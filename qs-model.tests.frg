#lang forge/temporal

open "qs-model.frg"

test suite for validResources {
    // Test 1: All valid resources
    test expect {
        validBasicResources: {
            some m: Machine | {
                m.total_mem = 7
                m.free_mem = 4
                m.total_compute = 6
                m.free_compute = 3
            }
            some cp: Compute_Proclet | {
                cp.compute = 2
                cp.starttime = 1
                cp.runtime = 3
                cp.stepsRunning = 0
                cp.stepsBeforeRun = 0
            }
            some mp: Memory_Proclet | {
                mp.memory = 4
            }
            validResources
        } is sat
    }

    // Test 2: Machine with negative free memory (should be unsat)
    test expect {
        invalidNegativeFreeMemory: {
            some m: Machine | {
                m.total_mem = 7
                m.free_mem = -1 // Invalid: negative free memory
                m.total_compute = 6
                m.free_compute = 3
            }
            validResources
        } is unsat
    }

    // Test 3: Machine with negative free compute (should be unsat)
    test expect {
        invalidNegativeFreeCompute: {
            some m: Machine | {
                m.total_mem = 7
                m.free_mem = 4
                m.total_compute = 6
                m.free_compute = -1 // Invalid: negative free compute
                validResources
            }
        } is unsat
    }

    // Test 4: Machine with zero total memory (should be unsat)
    test expect {
        invalidZeroTotalMemory: {
            some m: Machine | {
                m.total_mem = 0 // Invalid: total_mem must be > 0
                m.free_mem = 0
                m.total_compute = 6
                m.free_compute = 3
            }
            validResources
        } is unsat
    }

    // Test 5: Machine with zero total compute (should be unsat)
    test expect {
        invalidZeroTotalCompute: {
            some m: Machine | {
                m.total_mem = 7
                m.free_mem = 4
                m.total_compute = 0 // Invalid: total_compute must be > 0
                m.free_compute = 0
            }
            validResources
        } is unsat
    }

    // Test 6: Free memory exceeds total memory (should be unsat)
    test expect {
        invalidFreeMemExceedsTotal: {
            some m: Machine | {
                m.total_mem = 8
                m.free_mem = 10 // Invalid: free_mem > total_mem
                m.total_compute = 6
                m.free_compute = 3
            }
            validResources
        } for 5 Int is unsat
    }

     // Test 7: Free compute exceeds total compute (should be unsat)
    test expect {
        invalidFreeComputeExceedsTotal: {
            some m: Machine | {
                m.total_mem = 8
                m.free_mem = 4
                m.total_compute = 6
                m.free_compute = 8 // Invalid: free_compute > total_compute
            }
            validResources
        } for 5 Int is unsat
    }

    // Test 8: Compute Proclet with non-positive compute (should be unsat)
    test expect {
        invalidZeroCompute: {
            some cp: Compute_Proclet | {
                cp.compute = 0 // Invalid: compute must be > 0
                cp.starttime = 1
                cp.runtime = 3
                cp.stepsRunning = 0
                cp.stepsBeforeRun = 0
            }
            validResources
        } is unsat
    }

    // Test 9: Compute Proclet with non-positive starttime (should be unsat)
    test expect {
        invalidZeroStarttime: {
            some cp: Compute_Proclet | {
                cp.compute = 2
                cp.starttime = 0 // Invalid: starttime must be > 0
                cp.runtime = 3
                cp.stepsRunning = 0
                cp.stepsBeforeRun = 0
            }
            validResources
        } is unsat
    }

    // Test 10: Compute Proclet with non-positive runtime (should be unsat)
    test expect {
        invalidZeroRuntime: {
            some cp: Compute_Proclet | {
                cp.compute = 2
                cp.starttime = 1
                cp.runtime = 0 // Invalid: runtime must be > 0
                cp.stepsRunning = 0
                cp.stepsBeforeRun = 0
            }
            validResources
        } is unsat
    }

    // Test 11: Compute Proclet with negative stepsRunning (should be unsat)
    test expect {
        invalidNegativeStepsRunning: {
            some cp: Compute_Proclet | {
                cp.compute = 2
                cp.starttime = 1
                cp.runtime = 3
                cp.stepsRunning = -1 // Invalid: stepsRunning must be >= 0
                cp.stepsBeforeRun = 0
            }
            validResources
        } is unsat
    }

    // Test 12: Compute Proclet with negative stepsBeforeRun (should be unsat)
    test expect {
        invalidNegativeStepsBeforeRun: {
            some cp: Compute_Proclet | {
                cp.compute = 2
                cp.starttime = 1
                cp.runtime = 3
                cp.stepsRunning = 0
                cp.stepsBeforeRun = -1 // Invalid: stepsBeforeRun must be >= 0
            }
            validResources
        } is unsat
    }

    // Test 13: Memory Proclet with non-positive memory (should be unsat)
    test expect {
        invalidZeroMemory: {
            some mp: Memory_Proclet | {
                mp.memory = 0 // Invalid: memory must be > 0
            }
            validResources
        } is unsat
    }    
}

test suite for validProcletLocation {
    // Test 1: Valid case - proclet has location and is in that machine's proclet set
    test expect {
        validBasicLocation: {
            some m: Machine, p: Proclet | {
                p.location = m
                m.proclets = p
            }
            validProcletLocation
        } is sat
    }
    
    // Test 2: Valid case - multiple proclets on same machine
    test expect {
        validMultipleProclets: {
            some m: Machine | some disj p1, p2: Proclet | {
                p1.location = m
                p2.location = m
                m.proclets = {p1 + p2}
            }
            validProcletLocation
        } is sat
    }
    
    // Test 3: Valid case - proclet with no location (none)
    test expect {
        validNoLocation: {
            some m: Machine, p: Proclet | {
                p.location = none
                m.proclets = none
            }
            validProcletLocation
        } is sat
    }
    
    // Test 4: Invalid case - proclet has location but is not in machine's proclet set
    test expect {
        invalidNotInProcletSet: {
            some m: Machine, p: Proclet | {
                p.location = m
                m.proclets = none  // p is not in m.proclets
            }
            validProcletLocation
        } is unsat
    }
    
    // Test 5: Invalid case - proclet is in machine's proclet set but location doesn't match
    test expect {
        invalidLocationMismatch: {
            some disj m1, m2: Machine, p: Proclet | {
                p.location = m1
                m2.proclets = p  // p is in m2.proclets but p.location = m1
                m1.proclets = none
            }
            validProcletLocation
        } is unsat
    }
    
    // Test 6: Invalid case - proclet is in multiple machines' proclet sets
    test expect {
        invalidMultipleMachines: {
            some disj m1, m2: Machine, p: Proclet | {
                p.location = m1
                m1.proclets = p
                m2.proclets = p  // p can't be in two machines
            }
            validProcletLocation
        } is unsat
    }
    
    // Test 7: Invalid case - proclet has no location but is in a machine's proclet set
    test expect {
        invalidNoneLocationInSet: {
            some m: Machine, p: Proclet | {
                p.location = none
                m.proclets = p  // p is in m.proclets but has no location
            }
            validProcletLocation
        } is unsat
    }
    
    // Test 8: Invalid case - compute proclet location not matching its presence in machine
    test expect {
        invalidComputeProcletLocation: {
            some m: Machine, cp: Compute_Proclet | {
                cp.location = m
                m.proclets = none  // cp is not in m.proclets
            }
            validProcletLocation
        } is unsat
    }

}

test suite for resourcesMatchUsage {
    // Test 1: Valid case - Empty machine (no proclets)
    test expect {
        validEmptyMachineForResource: {
            some m: Machine | {
                m.total_mem = 8
                m.free_mem = 8  // All memory free
                m.total_compute = 6
                m.free_compute = 6  // All compute free
                m.proclets = none  // No proclets
            }
            resourcesMatchUsage
        } for 5 Int is sat
    }
    
    // Test 2: Valid case - Single memory proclet
    test expect {
        validSingleMemoryProclet: {
            some m: Machine, mp: Memory_Proclet | {
                m.total_mem = 8
                mp.memory = 3
                m.free_mem = 5  // 8 - 3 = 5
                m.total_compute = 6
                m.free_compute = 6  // No compute proclets
                m.proclets = mp
                mp.location = m
            }
            resourcesMatchUsage
        } for 5 Int is sat
    }
    
    // Test 3: Valid case - Single compute proclet
    test expect {
        validSingleComputeProclet: {
            some m: Machine, cp: Compute_Proclet | {
                m.total_mem = 8
                m.free_mem = 8  // No memory proclets
                m.total_compute = 6
                cp.compute = 2
                m.free_compute = 4  // 6 - 2 = 4
                m.proclets = cp
                cp.location = m
            }
            resourcesMatchUsage
        } for 5 Int is sat
    }
    
    // Test 4: Valid case - Full utilization (no free resources)
    test expect {
        validFullUtilization: {
            some m: Machine, cp: Compute_Proclet, mp: Memory_Proclet | {
                m.total_mem = 5
                mp.memory = 5
                m.free_mem = 0  // All memory used
                m.total_compute = 4
                cp.compute = 4
                m.free_compute = 0  // All compute used
                m.proclets = {cp + mp}
                cp.location = m
                mp.location = m
            }
            resourcesMatchUsage
        } is sat
    }
    
    // Test 5: Invalid case - Memory usage doesn't match
    test expect {
        invalidMemoryMismatch: {
            some m: Machine, mp: Memory_Proclet | {
                m.total_mem = 8
                mp.memory = 3
                m.free_mem = 4  // Should be 5 (8 - 3)
                m.total_compute = 6
                m.free_compute = 6
                m.proclets = mp
                mp.location = m
            }
            resourcesMatchUsage
        } for 5 Int is unsat
    }
    
    // Test 6: Invalid case - Compute usage doesn't match
    test expect {
        invalidComputeMismatch: {
            some m: Machine, cp: Compute_Proclet | {
                m.total_mem = 8
                m.free_mem = 8
                m.total_compute = 6
                cp.compute = 2
                m.free_compute = 3  // Should be 4 (6 - 2)
                m.proclets = cp
                cp.location = m
            }
            resourcesMatchUsage
        } for 5 Int is unsat
    }
    
    // Test 7: Valid case - Multiple machines with correct usage
    test expect {
        validMultipleMachinesResource: {
            some disj m1, m2: Machine, cp: Compute_Proclet, mp: Memory_Proclet | {
                // Machine 1
                m1.total_mem = 8
                m1.free_mem = 8  // No memory proclets
                m1.total_compute = 6
                cp.compute = 2
                m1.free_compute = 4  // 6 - 2 = 4
                m1.proclets = cp
                cp.location = m1
                
                // Machine 2
                m2.total_mem = 10
                mp.memory = 4
                m2.free_mem = 6  // 10 - 4 = 6
                m2.total_compute = 5
                m2.free_compute = 5  // No compute proclets
                m2.proclets = mp
                mp.location = m2
            }
            resourcesMatchUsage
        } for 5 Int is sat
    }
    
    // Test 8: Invalid case - Multiple machines with incorrect usage on one
    test expect {
        invalidMultipleMachinesResource: {
            some disj m1, m2: Machine, cp: Compute_Proclet, mp: Memory_Proclet | {
                // Machine 1 (correct)
                m1.total_mem = 8
                m1.free_mem = 8
                m1.total_compute = 6
                cp.compute = 2
                m1.free_compute = 4  // Correct: 6 - 2 = 4
                m1.proclets = cp
                cp.location = m1
                
                // Machine 2 (incorrect)
                m2.total_mem = 10
                mp.memory = 4
                m2.free_mem = 5  // Incorrect: should be 6 (10 - 4)
                m2.total_compute = 5
                m2.free_compute = 5
                m2.proclets = mp
                mp.location = m2
            }
            resourcesMatchUsage
        } for 5 Int is unsat
    }
}

test suite for validProcletRelationships {
    // Test 1: Valid basic relationship - bidirectional reference
    test expect {
        validBasicRelationship: {
            some mp: Memory_Proclet, cp: Compute_Proclet | {
                mp in cp.memory_procs
                cp in mp.compute_procs
            }
            validProcletRelationships
        } is sat
    }
    
    // Test 2: Invalid - One-way relationship (cp references mp but mp doesn't reference cp)
    test expect {
        invalidOneWayRelationship: {
            some mp: Memory_Proclet, cp: Compute_Proclet | {
                mp in cp.memory_procs
                cp not in mp.compute_procs
            }
            validProcletRelationships
        } is unsat
    }
    
    // Test 3: Invalid - Memory proclet with no compute proclet referencing it
    test expect {
        invalidMemoryProcletNoReferences: {
            some mp: Memory_Proclet | {
                all cp: Compute_Proclet | mp not in cp.memory_procs
                mp.compute_procs = none
            }
            validProcletRelationships
        } is unsat
    }
    
    // Test 4: Valid - Complex relationship with multiple proclets
    test expect {
        validComplexRelationship: {
            some disj mp1, mp2: Memory_Proclet | some disj cp1, cp2: Compute_Proclet | {
                // mp1 is referenced by both cp1 and cp2
                mp1 in cp1.memory_procs
                mp1 in cp2.memory_procs
                cp1 in mp1.compute_procs
                cp2 in mp1.compute_procs
                
                // mp2 is referenced only by cp2
                mp2 in cp2.memory_procs
                mp2 not in cp1.memory_procs
                cp2 in mp2.compute_procs
                cp1 not in mp2.compute_procs
            }
            validProcletRelationships
        } is sat
    }
}

test suite for validState {
    // Test 1: Valid basic state with all constraints satisfied
    // test expect {
    //     validBasicState: {
    //         // Create machine with resources
    //         some m: Machine | {
    //             m.total_mem = 10
    //             m.free_mem = 4
    //             m.total_compute = 8
    //             m.free_compute = 3
                
    //             // Create memory and compute proclets with valid relationships
    //             some mp: Memory_Proclet, cp: Compute_Proclet | {
    //                 // Resource requirements
    //                 mp.memory = 6             // Uses 6 memory
    //                 cp.compute = 5            // Uses 5 compute
                    
    //                 // Location assignments
    //                 mp.location = m
    //                 cp.location = m
    //                 m.proclets = {mp + cp}   // Both proclets assigned to machine
                    
    //                 // Proclet relationships
    //                 mp in cp.memory_procs
    //                 cp in mp.compute_procs
                    
    //                 // Valid state values
    //                 cp.starttime = 1
    //                 cp.runtime = 3
    //                 cp.stepsRunning = 2
    //                 cp.stepsBeforeRun = 0
    //                 cp.runState = Running
    //             }
    //         }
            
    //         // All individual predicates should be satisfied
    //         validResources
    //         validProcletLocation
    //         resourcesMatchUsage
    //         validProcletRelationships
    //         validState
    //     } for 5 Int is sat
    // }
    
    // Test 2: Valid complex state with multiple machines and proclets
    test expect {
        validComplexState: {
            // Create two machines
            some disj m1, m2: Machine | {
                // Machine 1 resources
                m1.total_mem = 8
                m1.free_mem = 2
                m1.total_compute = 6
                m1.free_compute = 1
                
                // Machine 2 resources
                m2.total_mem = 10
                m2.free_mem = 3
                m2.total_compute = 8
                m2.free_compute = 2
                
                // Create proclets with valid properties and relationships
                some disj mp1, mp2: Memory_Proclet | some disj cp1, cp2: Compute_Proclet | {
                    // Resource requirements
                    mp1.memory = 6
                    mp2.memory = 7
                    cp1.compute = 5
                    cp2.compute = 6
                    
                    // Location assignments
                    mp1.location = m1
                    cp1.location = m1
                    mp2.location = m2
                    cp2.location = m2
                    m1.proclets = {mp1 + cp1}
                    m2.proclets = {mp2 + cp2}
                    
                    // Proclet relationships - each memory proclet referenced by at least one compute proclet
                    mp1 in cp1.memory_procs
                    cp1 in mp1.compute_procs
                    mp2 in cp2.memory_procs
                    cp2 in mp2.compute_procs
                    
                    // Valid state values
                    cp1.starttime = 1
                    cp1.runtime = 3
                    cp1.stepsRunning = 1
                    cp1.stepsBeforeRun = 0
                    cp1.runState = Running
                    
                    cp2.starttime = 2
                    cp2.runtime = 4
                    cp2.stepsRunning = 2
                    cp2.stepsBeforeRun = 1
                    cp2.runState = Running
                }
            }
            
            validState
        } for 5 Int is sat
    }
    
    // Test 3: Invalid state due to resource mismatch
    test expect {
        invalidResourceMismatch: {
            some m: Machine | {
                m.total_mem = 10
                m.free_mem = 5          // Incorrect: should be 4 based on memory usage
                m.total_compute = 8
                m.free_compute = 3
                
                some mp: Memory_Proclet, cp: Compute_Proclet | {
                    // Resource requirements
                    mp.memory = 6       // Uses 6 memory
                    cp.compute = 5      // Uses 5 compute
                    
                    // Location assignments
                    mp.location = m
                    cp.location = m
                    m.proclets = {mp + cp}
                    
                    // Proclet relationships
                    mp in cp.memory_procs
                    cp in mp.compute_procs
                    
                    // Valid state values
                    cp.starttime = 1
                    cp.runtime = 3
                    cp.stepsRunning = 2
                    cp.stepsBeforeRun = 0
                    cp.runState = Running
                }
            }
            
            validState
        } is unsat
    }
}

test suite for init {

}

test suite for final {

}

test suite for noHosts {

}

test suite for procletStateEvolves {

}

test suite for traces {

}