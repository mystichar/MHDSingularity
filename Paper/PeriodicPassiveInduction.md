# Periodic passive magnetic induction in the actual forced Navier–Stokes velocity

This document describes the formal theorem and its proof. It makes no claim
of novelty or publication readiness; no literature comparison has been made.

## The closed statement

`NavierStokes.MagneticPeriodicMain.periodic_main` has no construction
hypotheses. It chooses a schedule `scales`, a forcing `forcing`, and a time
`0<a<1`. Its velocity is exactly

```
MagneticAxisTransfer.actualPeriodicVelocity
  ActualCandidateConstruction.selectedBudget
  ActualCandidateConstruction.selectedThreshold
  ActualCandidateConstruction.selectedThreshold_geometry
  scales
```

Its pressure is the activated periodization of the pressure sum from the
same schedule and the same actual pressure stages. It proves
`CandidateProperties velocity pressure forcing`, global smoothness of the
forcing, and the existing `CandidateConsequences.Consequences` for those
same three fields. In particular the velocity solves the forced
viscosity-one Navier–Stokes equation, is divergence free and periodic,
has zero initial velocity, and becomes unbounded as physical time tends to
one. The pressure and forcing have the regularity, periodicity, and forcing
time-support properties specified by `CandidateProperties`.

For **every** real constant `Bz0`, it then constructs **one** field B on
`[a,1)` with:

- periodicity, divergence freedom, and stretching-form ideal induction for
  that velocity;
- initial data `B(a,x)=Bz0 e₂` at every spatial point;
- joint continuity on `[a,1) × R³` and joint C1 regularity in its interior;
- spatial smoothness at every preterminal time;
- the exact formula
  `B(t,gamma(t))=Bz0*((1-a)/(1-t))^K e₂` for `a≤t<1`;
- if `Bz0≠0`, divergence of both `norm(B(t,gamma(t)))` and the global
  spatial supremum norm as `t→1-`;
- uniform finite supremum and cell-energy bounds on every fixed `[a,b]`,
  `a≤b<1`.

Here `gamma` is the existing distinguished trajectory and
`K=MagneticCoreAmplification.axialExponent ActualPrimary.nominal.axis.small`.
The earlier exact exponent computation, including `3.9999995<K<4`, is reused.
There is no time or viscosity rescaling in the exported magnetic formula.

## Why the upstream parameters match

The schedule comes from `ActualCandidateAssembly.selected_witness`.
Its selected budget, geometric threshold, potential stages, direct stages,
and pressure stages are used unchanged. The same returned witness supplies
Navier–Stokes properties and the schedule used to construct B.

The natural solution is not chosen independently by another existence
invocation. It is the already constructed proof

```
CorrectionInitialization.ActualPrimary.nominal.axis.natural.profile.family.natural
```

retained in the actual nominal profile. This is the natural-profile output
selected by the upstream axis preparation/entrance construction, with exactly
its `h`, `j`, outgoing pressure datum, scale, and normalization. The theorem
`MagneticPeriodicMain.naturalSolution` exposes that retained proof. There is
no unresolved schedule/profile compatibility assumption in `periodic_main`.
The more reusable `constructed_conclusions` retains a selected schedule and
a reference time after its proved late threshold; the closed theorem
instantiates both.

## Proof outline

1. Use the existing finite-slab induction construction: the flow `Phi`,
   inverse `Y`, and actual spatial Jacobian `F=D_x Phi` give
   `B(t,x)=Bz0 F(t,Y(t,x))e₂`. The variational ODE proves induction;
   `det F=1` and the Hessian/determinant identity prove divergence freedom.
2. Reuse compatibility and cofinal gluing to get one preterminal field.
   Export its already proved spatial smoothness, without asserting joint
   C-infinity regularity.
3. Use the retained natural solution to obtain the existing late axial
   transfer interval. Choose `a=(max(lateStart,0)+1)/2` and apply the
   existing exact amplification and pathwise norm-divergence theorems.
4. For each compact time slab, continuity on the product with the compact
   unit cube gives a uniform pointwise bound `C`. Periodicity and reduction
   to fractional coordinates extend this bound to every spatial point.
5. Define `supNorm B t = sup_x norm(B(t,x))`. Boundedness justifies the
   conditional-completeness lemmas for this real supremum and proves
   `norm(B(t,gamma(t))) ≤ supNorm B t`. Comparison gives divergence of the
   global uniform norm. The theorem uses an actual supremum, not an
   essential supremum; it does not use an unjustified pointwise lower bound
   for an essential supremum.
6. Define cell energy by the nonnegative Lebesgue integral
   `cellEnergy B t = (1/2) * integral_cell norm(B(t,x))² dx`, represented in
   Lean by an `ENNReal` lintegral. If the slab bound is C, monotonicity gives
   `cellEnergy B t ≤ (1/2)*C²*volume(cell) < infinity`. The closed unit cube
   has finite measure by compactness. Spatial smoothness ensures the energy
   density is continuous. This proves finiteness and a uniform upper bound
   on the chosen slab, with no assertion uniform in b as b tends to one.
7. For any `epsilon>0`, take `Bz0=epsilon/2`. The velocity, forcing, and
   reference time were chosen first. `arbitrarily_small_seed` gives this
   small positive seed, its constructed field, and supremum-norm divergence.

## Limits of the result

This is passive, ideal induction in a prescribed forced Navier–Stokes
velocity. The forcing is the one in the existing NS construction, not an
external assumption about an arbitrary NS field. B does not act on the
velocity. No resistivity, Lorentz backreaction, arbitrary-direction
amplification transfer, whole-space compact-seed transport, finite-volume
energy growth, or magnetic-energy blow-up is proved. Pointwise and supremum
norm divergence do not establish energy divergence. No fusion-performance
claim is made.

## Reproduction

```
lake build NavierStokes.MagneticPeriodicMain
lake build
lake env lean scripts/audit_magnetic_main.lean
lake env lean scripts/audit_magnetic_periodic.lean
```

See `MHD_PROGRESS.md` for the recorded build and axiom-audit results.
