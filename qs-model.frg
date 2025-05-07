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

// sig Hybrid_Proclet extends Proclet {
//     var h_compute: one Int,
//     var h_memory: one Int,
//     var h_starttime: one Int,
//     var h_runtime: one Int,
//     var h_runState: one Run_State
// }

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
        m.free_compute < cp.compute or
        some mp: cp.memory_procs | all m1: Machine | m1.free_mem < mp.memory
    }
}

pred procletStateEvolves {
    all cp: Compute_Proclet |
        // Case 1: not start time yet or no machines with adequate resources to place the proclet
        subtract[cp.starttime, 1] > T.time or noHosts[cp] implies {
            cp.runState' = Not_Yet_Run
            cp.location' = none
            all mp: cp.memory_procs | {
                mp.location' = none
            }
        }
        // Case 2: start time and room to place on machine
        //place compute and associated memory proclets
        subtract[cp.starttime, 1] <= T.time and

        // Case 3: start time and no room to place
        //same as case 1

        // Case 4: Running and not terminating yet

        // Case 5: Running and Terminating
        //remove proclet

        //Case 6: Terminated


}

pred timeEvolves {
    T.time' = add[T.time, 1]
}

pred traces {
    init
    always {
        validState
        timeEvolves
        procletStateEveolves
    }
    eventually final
}

run {
    traces
} for 3 Machine, 5 Compute_Proclet, 5 Memory_Proclet, 10 Int