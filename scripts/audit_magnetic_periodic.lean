import NavierStokes.MagneticPeriodicSolution

-- Run with: lake env lean scripts/audit_magnetic_periodic.lean
-- Audit construction, geometry, gluing, and the final existential result.
#print axioms NavierStokes.MagneticPeriodicCoefficient.ofPeriodicSlab
#print axioms NavierStokes.MagneticPeriodicCoefficient.actualOnSlab
#print axioms NavierStokes.MagneticPeriodicCoefficient.actual_divergence
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.Phi_hasDerivAt
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.F_eq_evolution
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.F_initial
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.F_hasDerivAt
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.F_det_one
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.magnetic_continuousOn
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.magnetic_contDiffAt
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.magnetic_spatial_smooth
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.magnetic_induction
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.magnetic_divergence_free
#print axioms NavierStokes.MagneticPeriodicFlow.actual_finite_slab
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.Phi_overlap
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.F_overlap
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.Y_overlap
#print axioms NavierStokes.MagneticPeriodicFlow.Slab.magnetic_overlap
#print axioms NavierStokes.MagneticPeriodicSolution.Data.endpoints_spec
#print axioms NavierStokes.MagneticPeriodicSolution.Data.magnetic_eq_slab
#print axioms NavierStokes.MagneticPeriodicSolution.Data.magnetic_initial
#print axioms NavierStokes.MagneticPeriodicSolution.Data.magnetic_continuousOn
#print axioms NavierStokes.MagneticPeriodicSolution.Data.magnetic_contDiffAt
#print axioms NavierStokes.MagneticPeriodicSolution.Data.magnetic_spatial_smooth
#print axioms NavierStokes.MagneticPeriodicSolution.Data.magnetic_periodic
#print axioms NavierStokes.MagneticPeriodicSolution.Data.magnetic_divergence_free
#print axioms NavierStokes.MagneticPeriodicSolution.Data.magnetic_induction
#print axioms NavierStokes.MagneticPeriodicSolution.exists_actual_solution
#print axioms NavierStokes.MagneticPeriodicSolution.exists_actual_amplifying_solution
