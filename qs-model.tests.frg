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

test suite for validStateTimeRelationships {
    // Test 1: Valid Not_Yet_Run case
    test expect {
        validNotYetRunCase: {
            some cp: Compute_Proclet | {
                cp.starttime = 3
                cp.stepsBeforeRun = 2  // stepsBeforeRun < starttime
                cp.runState = Not_Yet_Run
                no cp.location
                cp.runtime = 5
                cp.stepsRunning = 0
            }
            validStateTimeRelationships
        } is sat
    }

    // Test 2: Valid Running case
    test expect {
        validRunningCase: {
            some m: Machine | some cp: Compute_Proclet | {
                cp.starttime = 3
                cp.stepsBeforeRun = 3  // stepsBeforeRun >= starttime
                cp.runState = Running
                cp.location = m
                cp.runtime = 5
                cp.stepsRunning = 2
            }
            validStateTimeRelationships
        } is sat
    }

    // Test 3: Valid Finished case
    test expect {
        validFinishedCase: {
            some cp: Compute_Proclet | {
                cp.starttime = 3
                cp.stepsBeforeRun = 3
                cp.runState = Finished
                no cp.location
                cp.runtime = 5
                cp.stepsRunning = 5  // stepsRunning = runtime
            }
            validStateTimeRelationships
        } is sat
    }

    // Test 4: Invalid Not_Yet_Run with location
    test expect {
        invalidNotYetRunWithLocation: {
            some m: Machine | some cp: Compute_Proclet | {
                cp.starttime = 3
                cp.stepsBeforeRun = 2
                cp.runState = Not_Yet_Run
                cp.location = m  // Not_Yet_Run shouldn't have location
            }
            validStateTimeRelationships
        } is unsat
    }

    // Test 5: Invalid Running without location
    test expect {
        invalidRunningNoLocation: {
            some cp: Compute_Proclet | {
                cp.runState = Running
                no cp.location  // Running must have location
            }
            validStateTimeRelationships
        } is unsat
    }

    // Test 6: Valid transition Not_Yet_Run -> Running
    test expect {
        validTransitionToRunning: {
            some m: Machine | some cp: Compute_Proclet | {
                cp.runState = Not_Yet_Run
                no cp.location
                cp.runState' = Running
                cp.location' = m
            }
            always {validStateTimeRelationships}
        } is sat
    }

    // Test 7: Invalid direct transition Not_Yet_Run -> Finished
    test expect {
        invalidDirectToFinished: {
            some cp: Compute_Proclet | {
                cp.runState = Not_Yet_Run
                cp.runState' = Finished  // Must go through Running first
            }
            always {validStateTimeRelationships}
        } is unsat
    }

    test expect {
        finishedStaysFinished: {
            some cp: Compute_Proclet | {
                cp.runState = Finished
                cp.runState' = Finished  // Must stay Finished
                no cp.location
                no cp.location'
                cp.stepsRunning = cp.runtime
                cp.stepsRunning' = cp.runtime
            }
            always {validStateTimeRelationships}
        } is sat

        invalidFinishedChanges: {
            some cp: Compute_Proclet | {
                cp.runState = Finished
                cp.runState' != Finished  // Should be impossible
            }
            always {validStateTimeRelationships}
        } is unsat
    }

}

test suite for validState {
    // Test 1: Basic valid state
    test expect {
        validBasicState: {
            some m: Machine | {
                m.total_mem = 10
                m.free_mem = 6
                m.total_compute = 8
                m.free_compute = 5
            }
            some cp: Compute_Proclet | {
                cp.compute = 3
                cp.starttime = 2
                cp.runtime = 5
                cp.stepsRunning = 0
                cp.stepsBeforeRun = 1
                cp.runState = Not_Yet_Run
                no cp.location
            }
            some mp: Memory_Proclet | {
                mp.memory = 4
                no mp.location
            }
            validState
        } for 6 Int is sat
    }

    // Test 2: Machine with allocated proclets
    test expect {
        validWithAllocations: {
            some m: Machine | {
                m.total_mem = 10
                m.total_compute = 8
                some cp: Compute_Proclet | {
                    cp.compute = 3
                    cp.location = m
                    cp.runState = Running
                    m.free_compute = 5  // 8 - 3 = 5
                }
                some mp: Memory_Proclet | {
                    mp.memory = 4
                    mp.location = m
                    m.free_mem = 6  // 10 - 4 = 6
                }
            }
            validState
        } for 6 Int is sat
    }

    // Test 3: Invalid - negative free memory
    test expect {
        invalidNegativeMemory: {
            some m: Machine | {
                m.total_mem = 10
                m.free_mem = -1  // Invalid
                m.total_compute = 8
                m.free_compute = 5
            }
            validState
        } for 6 Int is unsat
    }

    // Test 4: Invalid - proclet not in machine's proclets
    test expect {
        invalidProcletLocation: {
            some m: Machine, p: Proclet | {
                p.location = m
                p not in m.proclets  // Invalid location relationship
            }
            validState
        } is unsat
    }

    // Test 5: Invalid - compute proclet with zero runtime
    test expect {
        invalidZeroRuntimeState: {
            some cp: Compute_Proclet | {
                cp.runtime = 0  // Invalid
                cp.compute > 0
                cp.starttime > 0
            }
            validState
        } is unsat
    }

    // Test 6: Invalid - memory proclet with zero memory
    test expect {
        invalidZeroMemoryState: {
            some mp: Memory_Proclet | {
                mp.memory = 0  // Invalid
            }
            validState
        } is unsat
    }

    // Test 7: Invalid - resource usage mismatch
    test expect {
        invalidResourceUsage: {
            some m: Machine | {
                m.total_mem = 10
                m.total_compute = 8
                some mp: Memory_Proclet | {
                    mp.memory = 4
                    mp.location = m
                }
                m.free_mem = 7  // Should be 6 (10 - 4)
            }
            validState
        } for 6 Int is unsat
    }

    // Test 8: Invalid - inconsistent proclet relationships
    test expect {
        invalidProcletRelationships: {
            some mp: Memory_Proclet, cp: Compute_Proclet | {
                mp in cp.memory_procs
                cp not in mp.compute_procs  // Invalid relationship
            }
            validState
        } is unsat
    }

    // Test 9: Invalid - Running proclet with no location
    test expect {
        invalidRunningNoLocationState: {
            some cp: Compute_Proclet | {
                cp.runState = Running
                no cp.location  // Invalid
            }
            validState
        } is unsat
    }

    // Test 10: Valid temporal transition
    test expect {
        validStateTransition: {
            some m: Machine | some cp: Compute_Proclet | {
                // Initial state
                cp.runState = Not_Yet_Run
                no cp.location
                cp.stepsBeforeRun < cp.starttime
                
                // Next state
                cp.runState' = Running
                cp.location' = m
                m.proclets' = m.proclets + cp
                m.free_compute' = subtract[m.free_compute, cp.compute]
            }
            always {validState}
        } is sat
    }
}

test suite for init {
    test expect {
        validInitialState: {
            // At least one machine exists
            some m: Machine | {
                m.total_mem = 10
                m.free_mem = 10
                m.total_compute = 8
                m.free_compute = 8
                no m.proclets
            }
            
            // At least one compute proclet exists
            some cp: Compute_Proclet | {
                cp.runState = Not_Yet_Run
                cp.stepsRunning = 0
                cp.stepsBeforeRun = 0
                cp.compute = 3
                cp.runtime = 5
                cp.starttime = 2
                // Verify at least one machine can host it
                some m: Machine | m.total_compute >= cp.compute
                // Verify memory requirements can be met
                all mp: cp.memory_procs | some m: Machine | m.total_mem >= mp.memory
            }
            
            // At least one memory proclet exists
            some mp: Memory_Proclet | {
                mp.memory = 4
                no mp.location
            }
            
            // All proclets are unassigned
            all p: Proclet | no p.location
            
            init
        } for 5 Int is sat
        
        invalidInitialState: {
            // Machine starts with allocated proclets (should violate init)
            some m: Machine | some m.proclets
            init
        } is unsat
    }

}

test suite for final {
    // Test 1: Perfectly valid final state
    test expect {
        idealFinalState: {
            // Machines completely empty
            all m: Machine | {
                no m.proclets
                m.free_mem = m.total_mem  // Bonus: resources fully released
                m.free_compute = m.total_compute
            }
            
            // All compute proclets properly finished
            all cp: Compute_Proclet | {
                cp.runState = Finished
                no cp.location
                cp.stepsRunning = cp.runtime  // Completed full duration
            }
            
            // All memory proclets released
            all mp: Memory_Proclet | no mp.location
            
            final
        } is sat
    }

    // Test 2: Invalid if any compute proclet not finished
    test expect {
        unfinishedComputeProclets: {
            some cp: Compute_Proclet | cp.runState != Finished
            final
        } is unsat
    }
}

test suite for procletStateEvolves {

}

test suite for traces {
  eventuallyFinishes:
    assert {
      // In every trace, every cp eventually reaches Finished.
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

    // Test that memory proclets are correctly co-located with their compute proclets
    // memoryProcletPlacement:
    //     assert {
    //         // Memory proclets are properly placed when their compute proclet runs
    //         always {
    //             all cp: Compute_Proclet | all mp: cp.memory_procs | 
    //             (cp.runState = Running implies some mp.location)
    //         }
    //     }
    //     is necessary for traces
    //     for exactly 5 Int,
    //         exactly 2 Machine, 
    //         exactly 2 Compute_Proclet,
    //         exactly 3 Memory_Proclet
    // Test that resource constraints are never violated
    resourceConstraintsHold:
        assert {
            // Free resources never go negative
            always {
                all m: Machine | {
                m.free_mem >= 0
                m.free_compute >= 0
                }
            }
            }
            is necessary for traces
            for exactly 5 Int,
                exactly 2 Machine,
                exactly 3 Compute_Proclet,
                exactly 4 Memory_Proclet
    
    // Test that when a proclet finishes, resources are properly released
    // resourcesProperlyReleased:
    //     assert {
    //     // When a proclet changes from Running to Finished, resources are released
    //         always {
    //             all cp: Compute_Proclet | {
    //             (cp.runState = Running and cp.runState' = Finished) implies {
    //                 // Compute resources are released
    //                 all m: Machine | m = cp.location implies 
    //                 m.free_compute' = add[m.free_compute, cp.compute]
                    
    //                 // Memory resources are released
    //                 all mp: cp.memory_procs | all m: Machine | m = mp.location implies
    //                 m.free_mem' = add[m.free_mem, mp.memory]
    //             }
    //             }
    //         }
    //         }
    //         is necessary for traces
    //         for exactly 5 Int,
    //             exactly 2 Machine,
    //             exactly 2 Compute_Proclet,
    //             exactly 2 Memory_Proclet

    // Test that proclets follow their state transitions correctly
    validStateTransitions:
        assert {
            // State transitions follow the specified pattern
            always {
                all cp: Compute_Proclet | {
                // Not_Yet_Run can only transition to Running or stay Not_Yet_Run
                cp.runState = Not_Yet_Run implies cp.runState' in (Not_Yet_Run + Running)
                
                // Running can only transition to Finished or stay Running
                cp.runState = Running implies cp.runState' in (Running + Finished)
                
                // Finished must stay Finished
                cp.runState = Finished implies cp.runState' = Finished
                }
            }
            }
            is necessary for traces
            for exactly 5 Int,
                exactly 2 Machine,
                exactly 3 Compute_Proclet,
                exactly 2 Memory_Proclet
    
    // Test for scheduling fairness - proclets that can run eventually do run
    validStateTransitionsForTraces:
        assert {
        // If resources are available and a proclet is ready, it eventually runs
        always {
            all cp: Compute_Proclet | {
            (cp.runState = Not_Yet_Run and 
            cp.stepsBeforeRun >= cp.starttime and
            canSchedule[cp]) implies eventually (cp.runState = Running)
            }
        }
        }
        is necessary for traces
        for exactly 5 Int,
            exactly 2 Machine,
            exactly 2 Compute_Proclet,
            exactly 2 Memory_Proclet
    
    // Test that memory and compute proclet relationships remain consistent
    consistentRelationships:
        assert {
            // Memory and compute proclet relationships are bidirectional
            always {
                all mp: Memory_Proclet | all cp: Compute_Proclet | {
                mp in cp.memory_procs iff cp in mp.compute_procs
                }
            }
            }
            is necessary for traces
            for exactly 5 Int,
                exactly 1 Machine,
                exactly 2 Compute_Proclet,
                exactly 2 Memory_Proclet
    
    // Test that compute proclets run for exactly their specified runtime
    correctRuntimeBehavior:
        assert {
            // Proclets run for exactly their specified runtime
            always {
                all cp: Compute_Proclet | {
                (cp.runState = Running and cp.stepsRunning = subtract[cp.runtime, 1]) implies
                    cp.runState' = Finished
                }
            }
            }
            is necessary for traces
            for exactly 5 Int,
                exactly 1 Machine,
                exactly 1 Compute_Proclet,
                exactly 1 Memory_Proclet
}

// Test with limited resources to verify scheduling behavior
run {
  traces
  
  // Define a small machine with limited resources
  all m: Machine | {
    m.total_mem = 12
    m.total_compute = 5
  }
  
  // Define proclets that collectively need more resources than available
  all cp: Compute_Proclet | {
    cp.compute = 3
    cp.runtime = 2
  }
  
  all mp: Memory_Proclet | {
    mp.memory = 6
  }
} for exactly 7 Int, exactly 1 Machine, exactly 2 Compute_Proclet, exactly 2 Memory_Proclet