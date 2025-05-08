#lang forge/temporal

option min_tracelength 5

---------- Definitions ----------

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
    var runtime: one Int, //number of states it should run for
    var runState: one Run_State,
    var stepsRunning: one Int, // number of states it has been running for
    var stepsBeforeRun: one Int // number of states it has been waiting to run for
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
    all m: Machine | {
        // Ensure machines start with sufficient resources
        m.total_mem > 0
        m.total_compute > 0
        m.free_mem = m.total_mem
        m.free_compute = m.total_compute
        m.proclets = none
    }
    
    all cp: Compute_Proclet | {
        cp.runState = Not_Yet_Run
        cp.stepsRunning = 0
        cp.stepsBeforeRun = 0
        cp.compute > 0
        cp.runtime > 0
        cp.starttime >= 0
    }
    
    all mp: Memory_Proclet | {
        mp.memory > 0
    }
    
    all p: Proclet | p.location = none
    
    // at least one machine has enough resources for each proclet
    all cp: Compute_Proclet | {
        some m: Machine | m.total_compute >= cp.compute
        all mp: cp.memory_procs | some m: Machine | m.total_mem >= mp.memory
    }
}

pred final {
    all m: Machine | m.proclets = none
    all cp: Compute_Proclet | cp.runState = Finished
    all p: Proclet | p.location = none
}

// Helper predicate that checks that no machine has resources for the proclet
// pred noHosts[cp: Compute_Proclet] {
//     all m: Machine | {
//         some mp: cp.memory_procs | all m1: Machine | m1.free_mem < mp.memory or
//         m.free_compute < cp.compute
//     }
// }

// Helper predicate that checks if there are resources available for the proclet
pred canSchedule[cp: Compute_Proclet] {
    // Check if compute proclet can be placed
    some m: Machine | {
        m.free_compute >= cp.compute
        
        // Check if all memory proclets can be placed 
        all mp: cp.memory_procs | {
            some m1: Machine | m1.free_mem >= mp.memory
        }
    }
}

pred procletStateEvolves {
    all cp: Compute_Proclet | {

        // Case 1: not start time yet
        (cp.stepsBeforeRun < cp.starttime) implies {
            cp.runState' = Not_Yet_Run
            cp.location' = none
            all mp: cp.memory_procs | mp.location' = none
            cp.stepsBeforeRun' = add[cp.stepsBeforeRun, 1]
            cp.stepsRunning' = cp.stepsRunning
        } and

        // Case 2: eligible to start but no resources available yet
        (cp.runState = Not_Yet_Run and cp.stepsBeforeRun >= cp.starttime and not canSchedule[cp]) implies {
            cp.runState' = Not_Yet_Run
            cp.location' = none
            all mp: cp.memory_procs | mp.location' = none
            cp.stepsBeforeRun' = add[cp.stepsBeforeRun, 1]
            cp.stepsRunning' = cp.stepsRunning
        } and

        // Case 3: eligible to start and resources available
        (cp.runState = Not_Yet_Run and cp.stepsBeforeRun >= cp.starttime and canSchedule[cp]) implies {
            some m: Machine | {
                // Place compute proclet and update state and machine
                m.free_compute >= cp.compute
                cp.runState' = Running
                cp.location' = m
                m.free_compute' = subtract[m.free_compute, cp.compute]
                m.proclets' = m.proclets + cp
                cp.stepsRunning' = 0  // Reset counter as it just started
                cp.stepsBeforeRun' = cp.stepsBeforeRun

                // Place corresponding memory proclets and update states
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

        // Case 4: Running and not finishing yet
        (cp.runState = Running and cp.stepsRunning < subtract[cp.runtime, 1]) implies {
            cp.runState' = Running
            cp.location' = cp.location
            all mp: cp.memory_procs | mp.location' = mp.location
            cp.stepsRunning' = add[cp.stepsRunning, 1]
            cp.stepsBeforeRun' = cp.stepsBeforeRun
        } and

        // Case 5: Running and finishing on next time tick
        (cp.runState = Running and cp.stepsRunning >= subtract[cp.runtime, 1]) implies {
            // Remove compute proclet and update state and machine
            cp.runState' = Finished
            let oldLocation = cp.location | {
                cp.location' = none
                oldLocation.free_compute' = add[oldLocation.free_compute, cp.compute]
                oldLocation.proclets' = oldLocation.proclets - cp
            }
            cp.stepsRunning' = cp.stepsRunning
            cp.stepsBeforeRun' = cp.stepsBeforeRun

            // Remove corresponding memory proclets and update states
            all mp: cp.memory_procs | {
                let oldMemLocation = mp.location | {
                    mp.location' = none
                    oldMemLocation.proclets' = oldMemLocation.proclets - mp
                    oldMemLocation.free_mem' = add[oldMemLocation.free_mem, mp.memory]
                }
            }
        } and

        // Case 6: Already Finished
        (cp.runState = Finished) implies {
            cp.runState' = Finished
            cp.location' = none
            cp.stepsRunning' = cp.stepsRunning
            cp.stepsBeforeRun' = cp.stepsBeforeRun
            all mp: cp.memory_procs | mp.location' = none
        }
    }
    
    //  machines' total resources don't change
    all m: Machine | {
        m.total_mem' = m.total_mem
        m.total_compute' = m.total_compute
    }
}


pred traces {
    init
    always {
        validState
        procletStateEvolves
    }
    eventually final
}

// run {
//     traces
// } for exactly 3 Machine, exactly 10 Proclet, exactly 5 Compute_Proclet, exactly 5 Memory_Proclet

test suite for traces {
  eventuallyFinishes:
    assert {
      // “In every trace, every cp eventually reaches Finished.”
      always {
        all cp: Compute_Proclet |
          eventually (cp.runState = Finished)
      }
    }
    is necessary for traces
      for exactly 5 Int,
          exactly 3 Machine,
          exactly 3 Compute_Proclet,
          exactly 3 Memory_Proclet

    eventuallyStarts:
        assert {
            always {
                all cp: Compute_Proclet |
                (cp.runState = Not_Yet_Run
                and subtract[cp.starttime, 1] <= cp.stepsBeforeRun)
                implies eventually (cp.runState = Running)
            }
            }
            is necessary for traces
            for exactly 3 Machine,
                exactly 2 Compute_Proclet,
                exactly 2 Memory_Proclet,
                exactly 5 Int

}