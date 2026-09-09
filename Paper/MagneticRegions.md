# Compact-seed high-field regions and energy lower bounds

This extends the whole-space construction at commit `3c5badb`. The periodic
and whole-space existence proofs are unchanged. The magnetic field remains
passive in the same prescribed, forced viscosity-one Navier–Stokes velocity.

## Small initial total energy

`MagneticCompactSeed.seed_homogeneous` proves
`seed center (c*z) = c • seed center z`, with the right side interpreted
pointwise. `Data.magnetic_smul` proves the same homogeneity for the actual
constructed transport. `Data.initial_energy_scaling` gives

```
E[D.magnetic (seed center c)](a)
  = ENNReal.ofReal(c^2) * E[D.magnetic (seed center 1)](a).
```

The unit seed has strictly positive initial energy, by its constant plateau
and a positive-volume ball, and finite energy, by the existing compact-slab
bound. Continuity of the scalar multiplier at zero gives arbitrarily small
positive initial energy. `MagneticCompactMain.small_initial_energy_main`
chooses the selected schedule, actual compact pressure/forcing, and late
reference time **before** quantifying over the energy tolerance. For every
real epsilon > 0 it supplies an amplitude c > 0 whose constructed field has
`0 < E(a) < ofReal epsilon` and spatial supremum tending to infinity.
The field retains the original construction's regularity, divergence freedom,
initial data, and induction equation. No smallness of the prescribed velocity
is required or deduced.

## The actual material representation

The namespace `MagneticCompactSolution.Data` exports `Phi`, `F`, and `Q`:

```
F(t,xi) = fderiv R (Phi t) xi
Q(t,xi) = F(t,xi)(W(xi))
D.magnetic W (t,Phi(t,xi)) = Q(t,xi).
```

`Phi_eq_slab` and `Q_eq_slab` identify these with every compatible finite-slab
construction, using nonlinear flow uniqueness and the existing overlap
proof. `Phi_eq_trajectory` proves trajectory identification. In particular,
`MagneticCompactMain.constructed_label_amplification` gives, for the same
`D = actualData ...`, `W = seed (gamma a) Bz0`, and `a <= t < 1`,

```
Phi(t,gamma(a)) = gamma(t)
||Q(t,gamma(a))|| = M(t) = |Bz0| * ((1-a)/(1-t))^K.
```

Here K is the existing exact exponent; it is neither redefined nor rederived.
This bridge concerns `Data.magnetic W`, not an arbitrary witness of
`MagneticConclusions`. Parameters are the existing selected schedule, its
actual compact NS pressure and force, `0 <= a < 1`, and `lateStart < a` for
the same existing natural solution. The prior closed construction supplies
these compatible data. The small-energy main theorem instantiates them.

## Deliverable A: a derivative-bound neighborhood

`MagneticAmplificationRegion.radius_bounds` and `high_field_ball` work for
maps between real normed spaces. Assume r0 > 0, M > 0, H >= 0, differentiability
at every point of `closedBall xi_star r0`, derivative norm <= H there, and
`||Q(xi_star)|| = M`. Define

```
r = r0*M / (2*(M+r0*H)).
```

Then `0 < r`, `r <= r0/2`, `H*r <= M/2`, and `||Q(xi)|| >= M/2`
on the open ball of radius r. The convex mean-value inequality and the reverse
triangle inequality prove the last statement. The denominator is positive;
there is no division by H, so H=0 is included.

## Deliverable B: an actual finite bound

`Slab.qPath_smooth` expresses the transported label field as a smooth map
into continuous time paths. `extendedDQ_continuous` then proves joint
continuity of its label derivative, including the finite-slab endpoints.
Compactness of a time slab times a closed label ball gives
`Slab.exists_uniform_DQ_bound`. This does not rely on inferring joint
regularity from separate spatial smoothness.

`Data.derivativeBound W xi_star r0 t` is the real supremum of
`||fderiv R (D.Q W t) xi||` on the fixed closed ball. `derivativeBound_spec`
proves nonnegativity and the derivative inequality at each preterminal time;
`derivativeBound_uniform` proves a finite uniform upper bound on every fixed
`[a,b]`, b < 1. All these bounds are for the actual constructed field.

`Slab.Q_fderiv_apply` proves the exact product rule

```
DQ[v] = (DF[v]) W + F(DW[v]).
```

`Q_fderiv_plateau` removes the second term on the compact seed's constant
plateau. A smaller fixed label ball may be chosen inside this open plateau;
the neighborhood and compactness theorems also allow any positive r0.

## Physical volume and energy

For `U_t = Phi(t, ball(xi_star,r(t)))`, `Slab.region_open` proves openness via
the actual flow homeomorphism. `Phi_measurePreserving` uses
`EulerSmoothBanachFlow.forward_measurePreserving` and incompressibility.
`region_volume` applies its measurable-preimage identity to the open image,
then uses flow injectivity to cancel preimage/image. Thus this is an actual
image-volume proof, not merely a determinant calculation.

The existing definition is retained:

```
E_B(t) = (2 : ENNReal)^(-1) * lintegral_x ofReal(||B(t,x)||^2).
```

`energy_of_region` proves `ofReal(M^2/8) * volume(U_t) <= E_B(t)` by
monotonicity of the nonnegative integral. No extra integrability assumption
is used. With `c3 = 4*pi/3`, the Euclidean ball formula gives

```
volume(U_t) = ofReal(c3*r(t)^3)
ofReal((c3/8)*M(t)^2*r(t)^3) <= E_B(t).
```

`unit_ball_finite_positive` verifies finiteness and positivity of c3's volume.
`MagneticCompactMain.constructed_quantitative_region` combines the actual
field, its exact central value, its constructed derivative supremum, open
image, positive volume, high-field inequality, and energy lower bound.
Its only amplitude restriction is `Bz0 != 0`; it assumes no bound on H.

## Deliverable C: a conditional terminal criterion

Write `m = |Bz0|*(1-a)^K > 0` and `q = max(p-K,0)`. If there are fixed
C > 0 and p >= 0 such that, sufficiently late,

```
H(t) <= C*(1-t)^(-p),
```

then `power_lower` and `eventual_power_lower` give

```
E_B(t) >= ofReal(c*(1-t)^(-2*K+3*q)),
d = r0/(2*(1+r0*C/m)),
c = (c3/8)*m^2*d^3 > 0.
```

The argument first bounds `r(t) >= d*(1-t)^q`. The theorem
`energy_exponent_negative` checks that `p < 5*K/3` makes the exponent
negative, considering the two cases defining max. The energy then tends to
`nhds top` in ENNReal. `conditional_energy_divergence` proves this abstract
criterion; `constructed_eventual_energy_lower` exports the actual field’s
eventual lower bound, and `constructed_conditional_energy_divergence` specializes divergence to the
actual compact field and actual derivative supremum. **Its late H-bound is
an explicit, uninstantiated assumption.**

## Deformation estimate audit and remaining obligation

The current flow path-space APIs establish smooth dependence on labels,
continuous derivative paths, and finite bounds on compact slabs. The
`EulerSmoothPathTimeJets.jetFamily_hasDerivWithinAt` API differentiates
spatial jets in time. These qualitative results do not bound the constants
as b approaches 1. The ordinary flow acceleration is a time derivative,
not a bound for the second derivative with respect to labels.

`EulerSmoothFlowGevrey.displacement_positive_bound` supplies an explicit
conditional estimate

```
||D^n(Phi_t-id)|| <= B*t*(4*R)^n*(n!)^2
```

but assumes all coefficient jets satisfy `||A.jet n|| <= B*R^n*(n!)^2`
and `B*R*T <= 1/8`. No matching terminal dependence of these constants is
supplied for the actual assembled compact coefficient on the relevant
material neighborhood. Compact-support smoothness supplies finite jet bounds
on each fixed slab, not the required uniform Gevrey or terminal power bounds.

There are also Eulerian profile estimates, which should not be confused
with label-derivative estimates. `ActualBaseVelocityBounds.velocity_rate`
bounds order-m jets of `FinalSlowBase.velocity` on the open-past endpoint
filter by a power of `PhysicalWaveSum.physicalQ`, with loss
`heatLoss m = (4*m+2)*(m+2)` (18 at m=1 and 40 at m=2).
These concern the actual slow base, not an identified full assembled
velocity jet along every label in the material ball. They do not directly
bound D_xi^2 Phi or H. `DiagonalJetBounds.tsum_jet_identity` identifies actual
sum derivatives using local finiteness; its quantitative tail estimates
require stage-jet hypotheses and prefixes depending on derivative order and
decay power. The numerical schedule alone is not a terminal bound for the
material derivative. No material-tube containment or full derivative transfer
needed to turn these Eulerian rates into the required H-rate is asserted.

The precise missing sufficient estimate is a bound for
`sup_closedBall ||D_xi(F(t,xi) W(xi))|| <= C*(1-t)^(-p)` with `p < 5*K/3`.
On the plateau this reduces to the action of the second label derivative of
Phi on the seed. A possible route is to estimate the second variational
identity `d_t D^2 Phi = D^2 u[F,F] + Du D^2 Phi` on the actual material tube.
The expanded second variational equation and a terminal quantitative estimate
are not added as declarations here. In particular, the available axial-column
transfer does not identify the full assembled gradient or its second spatial
derivatives with those of the natural core. The Eulerian core radius is not
substituted for a magnetic variation scale.

Only A and B are unconditional consequences for the constructed field.
Failure to discharge this sufficient C-bound does not show that energy stays
bounded. Actual terminal magnetic-energy divergence remains open.

## Logical scope

There are positive-volume high-field regions at each fixed time, with a
quantitative, time-dependent lower bound for their volumes. The label radius
may shrink to zero. No one fixed material set is shown to amplify indefinitely,
and no fixed-volume robustness, attraction, or stability under perturbations
is proved. A continuity neighborhood alone would not establish any such
claim. This work asserts neither resistivity/reconnection nor backreaction,
coupled MHD, stagnation attraction, or fusion performance. No novelty claim
is made.


## Validation and reproduction

```
lake build NavierStokes.MagneticSeedScaling
lake build
lake env lean scripts/audit_magnetic_regions.lean
lake env lean scripts/audit_magnetic_compact.lean
lake env lean scripts/audit_magnetic_main.lean
lake env lean scripts/audit_magnetic_periodic.lean
```

The targeted build and full build pass (11,277 full-build jobs). All 47 new
and 104 previous magnetic theorem audits use only `propext`,
`Classical.choice`, and `Quot.sound`. No new axioms or incomplete proofs were
added. Four pre-existing `ComparatorChallenges` sorry warnings remain outside
these magnetic dependency audits. Existing periodic and whole-space Lean
files are unchanged.
