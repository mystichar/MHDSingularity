# Compact-seed passive induction in the actual whole-space NS velocity

This is a statement and proof outline for the formal result, not a claim of
novelty or publication readiness. The completed periodic proofs are unchanged.

## Closed main theorem

`NavierStokes.MagneticCompactMain.whole_space_main` has no construction
hypotheses. It selects one schedule `scales`, a smooth forcing, and a late
regular time `0<a<1`. Its velocity is exactly

```
MagneticAxisTransfer.actualCompactVelocity
  ActualCandidateConstruction.selectedBudget
  ActualCandidateConstruction.selectedThreshold
  ActualCandidateConstruction.selectedThreshold_geometry
  scales
```

The pressure is `R3CompactCandidate.pressure` of the actual pressure sum with
that same schedule. The forcing is the already established
`R3CompactCandidate.compactForce` of the forcing from `selected_witness`.
`R3CompactCandidate.Properties` proves the viscosity-one forced NS equation,
spatial incompressibility, velocity/pressure/forcing regularity and compact
support, zero initial velocity, forcing time support, and velocity blow-up.
The main theorem also retains global smoothness of the forcing.

For every real amplitude `Bz0`, it constructs one field B on `[a,1)` with:

- smooth compactly supported divergence-free initial data `B_a`, equal to
  `Bz0 e2` on a neighborhood of `gamma(a)`;
- joint continuity on `[a,1) × R³`, joint C1 regularity in the interior,
  and spatial smoothness at every preterminal time;
- stretching-form ideal induction for the exact velocity above and magnetic
  divergence freedom;
- uniform compact spatial support on every fixed preterminal slab `[a,b]`;
- uniform finite global supremum and whole-space magnetic-energy bounds on
  that fixed slab;
- exact amplification
  `B(t,gamma(t)) = Bz0*((1-a)/(1-t))^K e2` for `a≤t<1`;
- when `Bz0≠0`, pathwise norm divergence and global spatial supremum-norm
  divergence as `t→1-`.

The same B is used for every time. The velocity, forcing, and reference time
are chosen before the seed amplitude. Neither the velocity nor its existing
localization is altered. Physical time remains viscosity-one time with
singular time one; the exponent is the existing `axialExponent`.

## Compact axial seed

With `c=gamma(a)` and the existing smooth cutoff `chi(x)=spatialCutoff(x-c)`,
set

```
A_a(x) = (Bz0/2) chi(x) (-(x-c)_1 e0 + (x-c)_0 e1)
B_a(x) = SpatialCurl.curl A_a(x).
```

This is `(1/2) chi(x) [Bz0 e2 cross (x-c)]` in the project's curl convention.
`MagneticCompactSeed.curl_linear` checks the sign and normalization exactly.
`seed_eq_on_plateau` and `seed_local_constant` prove the constant-field
identity where the translated cutoff is identically one. `seed_smooth`,
`seed_compact`, and `seed_divergence` prove the remaining seed properties.
The closed support lies in the translate of the existing support cylinder.

## Transport, divergence, and support

`MagneticCompactFlow.Slab` supplies physical-time adapters to the existing
Euler flow machinery. `SmoothTimeField.ofContDiffOnCompactSupport` supplies
the coefficient path and all uniformly bounded spatial jets on `[0,b-a]`.
`actualData` discharges its support requirement using the existing
`R3CompactCandidate.velocity_supported` and its smoothness using the selected
schedule. `coefficient_apply` and `data_velocity` identify its coefficient
with the actual velocity at physical time `a+s`. The Lipschitz bound is
finite-slab dependent; there is no bound assumed through time one.

The Picard flow, its inverse, spatial smoothness, actual Jacobian
identification, and determinant theorem are the existing Euler results.
The physical-time wrappers follow the established periodic adapter. For a
smooth spatially varying seed W, the transported field is literally

```
B(t,x) = F(t,Y(t,x)) (W(Y(t,x))),  F(t,xi)=D_x Phi(t,xi).
```

Differentiating `B(t,Phi(t,xi))=F(t,xi)W(xi)` with xi fixed proves induction
using the variational ODE. `F_det_one` and the existing
`EulerPacketVolumeDivergence.divergence_pushforward` preserve divergence.
That theorem uses second spatial derivatives of Phi and the determinant
identity; no unjustified temporal or second-derivative regularity of B is
introduced.

`Slab.transported_support` proves

```
tsupport(B(t,·)) ⊆ Phi(t,·) '' tsupport(W).
```

For `t in [a,b]`, these supports lie in the compact image of
`[a,b] × tsupport(W)` under the continuous flow. `compact_slab_bounds`
uses continuity on this tube to obtain a uniform pointwise bound C.
Outside the tube the field is zero. Hence the global supremum norm is finite
and uniformly bounded there. The nonnegative whole-space energy integral
satisfies

```
energy B t = (1/2) integral_R3 |B(t,x)|² dx
           ≤ (1/2) C² volume(tube) < infinity.
```

Lean represents energy by an `ENNReal` lintegral. The proof bounds the energy
density by an indicator of the compact tube; it does not bound a nonzero
constant over all of R³. All estimates are for the fixed upper endpoint b.

## One preterminal field and matching upstream witnesses

`Slab.Phi_overlap`, `F_overlap`, `Y_overlap`, and `magnetic_overlap` reuse the
flow-uniqueness argument for equal velocities and initial times, now with the
same varying seed. `MagneticCompactSolution.Data` glues a strictly increasing
cofinal family of upper endpoints. `magnetic_eq_slab` proves compatibility,
transferring regularity, induction, divergence freedom, and support bounds
to one preterminal field. `Data.transported_support` retains the exact
flow-image containment on each finite restriction.

The main theorem invokes `ActualCandidateAssembly.selected_witness` once.
`R3CompactCandidate.of_localized_fields` transfers its NS properties to the
existing compact candidate. The natural solution is the one already retained
in `ActualPrimary.nominal.axis.natural.profile.family.natural`, as exposed by
`MagneticPeriodicMain.naturalSolution`. No independent profile or scale is
chosen. Thus the constructed field satisfies the hypotheses of the existing
compact amplification and norm-divergence theorems for this very velocity.
Global supremum divergence follows by comparison with the path value. The
norm used is an actual spatial supremum, not an essential supremum.

## Scope

There are no unresolved upstream assumptions in `whole_space_main`. Generic
transport lemmas retain their stated smoothness, support, and divergence
hypotheses; all are discharged in the closed theorem. Joint C-infinity
regularity is not claimed. The transported field need not remain axial away
from the distinguished trajectory.

This is passive ideal induction in a prescribed forced NS velocity. There is
no actual terminal magnetic-energy blow-up theorem, arbitrary-direction
amplification, resistive amplification, Lorentz backreaction, or coupled MHD
result. The finite-energy upper bounds alone do not imply an energy-growth
lower bound. The subsequent extension below proves quantitative fixed-time
region and energy lower bounds.

## Reproduction

```
lake build NavierStokes.MagneticCompactMain
lake build
lake env lean scripts/audit_magnetic_compact.lean
lake env lean scripts/audit_magnetic_main.lean
lake env lean scripts/audit_magnetic_periodic.lean
```

Recorded validation results are in `MHD_PROGRESS.md`.


## Subsequent quantitative-region extension

The original existence and amplification proofs above are preserved. See
[MagneticRegions.md](MagneticRegions.md) for amplitude homogeneity, arbitrarily
small positive initial total energy with supremum divergence, the actual
material-flow bridge, positive-volume high-field regions, and quantitative
energy lower bounds. The terminal energy-divergence criterion there is
conditional on an unproved late bound for the actual label derivative;
actual magnetic-energy blow-up is not asserted.
