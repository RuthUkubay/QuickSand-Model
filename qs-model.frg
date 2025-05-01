#lang forge/temporal

option min_tracelength 1

---------- Definitions ----------

sig Machine {
    var total_mem: one Int
    var free_mem: one Int
    var total_compute: one Int
    var free_compute: one Int
    var proclets: set Proclet
}

abstract sig Run_State {}
sig Running, Finished, Not_Yet_Run extends State {}

abstract sig Proclet {
    var location: lone Machine
}

sig Compute_Proclet extends Proclet {
    var compute: one Int //% of a core it takes up on average during its runtime
    //(forge doesn't have floats so could just do 1-10 integers???)
    var memory_procs: set Memory_Proclet // set of memory proclets it needs to access data from
    // ignore during simple model set up
    var starttime: one Int // in seconds?
    var runtime: one Int
    var state: one Run_State
}

sig Memory_Proclet extends Proclet {
    var memory: one Int // in MB
    var compute_procs: set Compute_Proclet // ignore during simple model set up
}

// I didn't mention this as much when explaining the system, but there are hybrid proclets - you can read more about them in the paper
// we could also choose not to include them, up to you two/how much time we have?
sig Hybrid_Proclet extends Proclet {
    var compute: one Int
    var memory: one Int
    var starttime: one Int
    var runtime: one Int
    var state: one Run_State
}
