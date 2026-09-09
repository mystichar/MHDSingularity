import NavierStokes.MagneticPeriodicMain

-- Run with: lake env lean scripts/audit_magnetic_main.lean
#print axioms NavierStokes.MagneticPeriodicMain.naturalSolution
#print axioms NavierStokes.MagneticPeriodicNorms.slab_bound
#print axioms NavierStokes.MagneticPeriodicNorms.supNorm_bounds
#print axioms NavierStokes.MagneticPeriodicNorms.energy_bound
#print axioms NavierStokes.MagneticPeriodicNorms.slab_norm_energy_bound
#print axioms NavierStokes.MagneticPeriodicNorms.supNorm_tendsto
#print axioms NavierStokes.MagneticPeriodicMain.constructed_conclusions
#print axioms NavierStokes.MagneticPeriodicMain.periodic_main
#print axioms NavierStokes.MagneticPeriodicMain.arbitrarily_small_seed
