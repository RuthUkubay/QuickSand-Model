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
    var compute: one Int, //% of a core it takes up on average during its runtime
    //(forge doesn't have floats so could just do 1-10 integers???)
    var memory_procs: set Memory_Proclet, // set of memory proclets it needs to access data from
    // ignore during simple model set up
    var starttime: one Int, // in seconds?
    var runtime: one Int,
    var runState: one Run_State
}

sig Memory_Proclet extends Proclet {
    var memory: one Int, // in MB
    var compute_procs: set Compute_Proclet // ignore during simple model set up
}

// I didn't mention this as much when explaining the system, but there are hybrid proclets - you can read more about them in the paper
// we could also choose not to include them, up to you two/how much time we have?
// sig Hybrid_Proclet extends Proclet {
//     var h_compute: one Int,
//     var h_memory: one Int,
//     var h_starttime: one Int,
//     var h_runtime: one Int,
//     var h_runState: one Run_State
// }

----------------- State Invariants ----------------- 

// Ensure free resources are valid (never negative)
pred validResources {
    all m: Machine | {
        m.free_mem >= 0
        m.free_compute >= 0
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
// pred resourcesMatchUsage {
//     all m: Machine | {
//         // Calculate memory usage
//         let memoryProclets = m.proclets & (Memory_Proclet + Hybrid_Proclet) | 
//             m.free_mem = subtract[m.total_mem, sum mp: memoryProclets | mp.memory]
        
//         // Calculate compute usage
//         let computeProclets = m.proclets & (Compute_Proclet + Hybrid_Proclet) | 
//             m.free_compute = subtract[m.total_compute, sum cp: computeProclets | cp.compute]
//     }
// }

// Ensure memory and compute proclet relationships are consistent
pred validProcletRelationships {
    all mp: Memory_Proclet | all cp: Compute_Proclet | {
        mp in cp.memory_procs iff cp in mp.compute_procs
    }
}

// Ensure a valid state configuration (combines all state invariants)
pred validState {
    always {
        validResources
        validProcletLocation
        // resourcesMatchUsage
        // validProcletRelationships
    }
}

run {validState}