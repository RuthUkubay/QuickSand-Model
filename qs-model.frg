#lang forge/temporal

option min_tracelength 5

---------- Definitions ----------

one sig T {
    var time: one Int
}

sig Machine {
    var total_mem: one Int,
    var free_mem: one Int,
    var total_compute: one Int,
    var free_compute: one Int,
    var proclets: set Proclet
}

abstract sig Run_State {}
sig Running, Finished, Not_Yet_Run extends Run_State {}

abstract sig Proclet {
    var location: lone Machine
}

sig Compute_Proclet extends Proclet {
    var compute: one Int, //amount of compute (decide on what this represents)
    var memory_procs: set Memory_Proclet, // set of memory proclets it needs to access data from
    var starttime: one Int, //represents state where proclet starts running
    var runtime: one Int, //number of states it is running for
    var runState: one Run_State
}

sig Memory_Proclet extends Proclet {
    var memory: one Int, // in MB
    var compute_procs: set Compute_Proclet
}

--------------------- State Invariants ------------------------

// Ensure free resources are valid (never negative)
pred validResources {
    all m: Machine | {
        m.free_mem >= 0
        m.free_compute >= 0
        m.total_compute > 0
        m.total_mem > 0
        m.free_mem <= m.total_mem
        m.free_compute <= m.total_compute
    }
}

// Ensure every proclet that has a location is in that machine's proclet set
pred validProcletLocation {
    all p: Proclet | {
        p.location != none implies p in p.location.proclets
        all m: Machine | p in m.proclets implies p.location = m
    }
}

// Ensure resources allocated to proclets match machine's used resources
pred resourcesMatchUsage {
    all m: Machine | {
        // Calculate memory usage
        let memoryProclets = m.proclets & Memory_Proclet |
            m.free_mem = subtract[m.total_mem, sum mp: memoryProclets | mp.memory]

        // Calculate compute usage
        let computeProclets = m.proclets & Compute_Proclet |
            m.free_compute = subtract[m.total_compute, sum cp: computeProclets | cp.compute]
    }
}

// Ensure memory and compute proclet relationships are consistent
pred validProcletRelationships {
    all mp: Memory_Proclet | all cp: Compute_Proclet | {
        mp in cp.memory_procs iff cp in mp.compute_procs
    }
}

// Ensure a valid state configuration (combines all state invariants)
pred validState {
    validResources
    validProcletLocation
    resourcesMatchUsage
    validProcletRelationships
}

 ------------------ Initial & Transition Predicates -------------------

pred init {
    all m: Machine | m.proclets = none
    all cp: Compute_Proclet | cp.runState = Not_Yet_Run
    all p: Proclet | p.location = none
    T.time = 0
}

pred final {
    all m: Machine | m.proclets = none
    all cp: Compute_Proclet | cp.runState = Finished
    all p: Proclet | p.location = none
}

// Helper predicate that checks that no machine has resources for the proclet
pred noHosts[cp: Compute_Proclet] {
    all m: Machine | {
        some mp: cp.memory_procs | all m1: Machine | m1.free_mem < mp.memory or
        m.free_compute < cp.compute
    }
}

//DOES NOT HANDLE SITUATION WHERE NOT PLACED AT STARTIME AND IS PLACED AFTER - BECAUSE THEN WON'T BE DONE RUNNING BY STARTIME PLUS RUNTIME
//ADD VARIABLE TO HANDLE THIS?? UGH
pred procletStateEvolves {
    all cp: Compute_Proclet |

        // Case 1: not start time yet or no machines with adequate resources to place the proclet
        (subtract[cp.starttime, 1] > T.time or noHosts[cp]) implies {
            cp.runState' = Not_Yet_Run
            cp.location' = none
            all mp: cp.memory_procs | {
                mp.location' = none
            }
        } and

        // Case 2: not placed and start time and room to place on a machine
        (cp.runState = Not_Yet_Run and subtract[cp.starttime, 1] <= T.time and not noHosts[cp]) implies {
            some m: Machine | {
                //place compute proclet and update state and machine
                m.free_compute >= cp.compute
                cp.runState' = Running
                cp.location' = m
                m.free_compute' = subtract[m.free_compute, cp.compute]
                m.proclets' = m.proclets + cp

                //place corresponding memory proclets and update states
                all mp: cp.memory_procs | {
                    some m1: Machine | {
                        m1.free_mem >= mp.memory
                        mp.location' = m1
                        m1.proclets' = m1.proclets + mp
                        m1.free_mem' = subtract[m1.free_mem, mp.memory]
                    }
                }
            }
        } and

        // Case 3: Running and not terminating yet
        (cp.runState = Running and subtract[add[cp.starttime, cp.runtime], 1] > T.time) implies {
            cp.runState' = Running
            cp.location' = cp.location
            all mp: cp.memory_procs | {
                mp.location' = mp.location
            }
        } and

        // Case 4: Running and Terminating on next time tick
        (cp.runState = Running and subtract[add[cp.starttime, cp.runtime], 1] <= T.time) implies {
            //remove compute proclet and update state and machine
            cp.runState' = Finished
            cp.location' = none
            cp.location.free_compute' = add[cp.location.free_compute, cp.compute]
            cp.location.proclets' = cp.location.proclets - cp

            //remove corresponding memory proclets and update states
            all mp: cp.memory_procs | {
                mp.location' = none
                mp.location.proclets' = mp.location.proclets - mp
                mp.location.free_mem' = add[mp.location.free_mem, mp.memory]
            }
        } and

        //Case 5: Terminated
        (cp.runState = Finished) implies {
            cp.runState' = Finished
            cp.location' = none
            all mp: cp.memory_procs | {
                mp.location' = none
            }
        }

}

pred timeEvolves {
    T.time' = add[T.time, 1]
}

pred traces {
    init
    always {
        validState
        timeEvolves
        procletStateEvolves
    }
    eventually final
}

run {
    traces
}