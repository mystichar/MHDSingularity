# MHDSingularity handoff: exact natural-core magnetic amplification

## Current milestone

The natural-core amplification milestone is proved in
`NavierStokes/MagneticCoreAmplification.lean`. Existing
`MagneticSimilarityGradient.lean` proofs have been preserved.
The separate minimal assembled-flow audit is proved in
`NavierStokes/MagneticAxisTransfer.lean`.

### Exact exponent and bounds

Use the existing `NaturalAxisData.A`, `D`, `d`, and `L`, and set
`eta0 = MagneticSimilarityTrajectory.distinguishedEta p`. The only new exponent
definition is `MagneticCoreAmplification.axialExponent p`:

```text
K = (4*d(eta0)^2 + 2*A(h)*D(h)*eta0^2)/L(h,eta0).
```

With `p : SmallParameters h j` (`0<h≤1/1000`, `0<j≤1/1000`), Lean proves:

- `axialExponent_pos`: `0 < K`.
- `axialExponent_defect`:
  `4-K = eta0^2*(15/2 - 8*h + 2*h^2 - 4*eta0^2)/(1-2*h*eta0^2)`.
- `axialExponent_defect_bounds`: `0 < 4-K ∧ 4-K < j^2/2`.
- `axialExponent_bounds`: `7999999/2000000 < K ∧ K < 4`.
- `axialStrain_eq_exponent`: for a supplied
  `NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr` and `t<1`,
  `axialStrain h eta0 V t = K/(1-t)`.
- `spatialDerivative_core_axial`:
  `spatialDerivative (coreVelocity h f V) t (trajectory h eta0 t) e₂
   = (K/(1-t)) • e₂`.

The identities were checked algebraically in Lean. The root bound
`-j/4 < eta0 < -j/5` supplies `0<eta0²<j²/16`. The defect factor divided by
`L` lies strictly between zero and eight. No value of `K` is assumed to equal
four, and the swirl datum does not enter this exponent.

### Exact transport statements and hypotheses

Let `γ = trajectory h eta0` and `g(t)=((1-a)/(1-t))^K`.
`pure_axial_seed_transport` assumes:

1. `p : SmallParameters h j` and
   `hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr`.
2. `a≤b`, `b<1`, and a supplied `B : MagneticField`.
3. `IdealInductionOn (Ioo a b) (coreVelocity h f V) B`.
4. `ContinuousOn (fun t => B(t,γ(t))) (Icc a b)`.
5. `∀t∈Ioo a b, DifferentiableAt ℝ B (t,γ(t))`.
6. `B(a,γ(a)) = Bz0 • e₂`.

It concludes, for every `t∈Icc a b`:

```text
B(t,γ(t)) = (Bz0 * ((1-a)/(1-t))^K) • e₂.
```

`axial_component_transport` drops assumption 6 and concludes

```text
B(t,γ(t)) 2 = B(a,γ(a)) 2 * ((1-a)/(1-t))^K.
```

No nonzero seed is required for these equality statements. The separate
`amplificationFactor_gt_one` shows the factor exceeds one for `a<t<1`;
`amplificationFactor_pos` proves positivity whenever `a<1` and `t<1`.
The power-law derivative proof establishes positive numerator, denominator,
and ratio before using the real-power identities.

`pure_axial_transport_of_directional_gradient` is the reusable generic theorem:
it assumes a supplied Lagrangian trajectory, the same magnetic regularity and
induction hypotheses, continuity of the velocity Jacobian on the closed path,
and only `Dₓu(t,γ(t)) e₂ = (K/(1-t))e₂` at interior times. Its conclusion is
the same pure-seed formula. Full Jacobian equality to a model is unnecessary.
The core specialization proves Jacobian continuity rather than imposing an
extra hypothesis on the natural solution. Both transport proofs reuse the
material chain rule and `linearODE_eq_zero_on_interval`; neither solves the
full rotating deformation matrix.

These are conditional transport results for a supplied induction solution.
There is no claim of global magnetic PDE existence, divergence propagation,
finite-volume amplification, or an assembled Navier–Stokes magnetic result.
The stretching-form induction predicate keeps divergence conditions separate;
a supplied `IncompressibleInductionOn` provides its `.induction` hypothesis.

### Separate minimal assembled-velocity audit: proved

The exact viscosity-one fields from an explicit common schedule `a` are named
`actualPeriodicVelocity B N0 hN a` and `actualCompactVelocity B N0 hN a` in
`MagneticAxisTransfer`. They are the same formulas retained by the periodic
witness and whole-space extraction:

```text
ASum = potentialSum (fun j => (a j : real)) (physicalQ h) potentialStages
BSum = potentialSum (fun j => (a j : real)) (physicalQ h) directStages
u_periodic = activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum)
u_compact  = R3CompactCandidate.velocity ASum BSum
           = activatedVelocity (fun w => cutVelocity ASum w + cutPotential BSum w).
```

`slowBase_axis` proves the exact identity, for every `t<1` and every real `z`:

```text
FinalSlowBase.velocity H v upper B (t,z*e₂)
  = physicalQ(h,t,0,z)^(-A(h)) * U(j,physicalEta(h,t,0,z)) * e₂.
```

`slowBase_axis_eq_core` identifies this with any supplied natural solution
using the same `h` and `j`. `axial_derivative_of_line_germ` explicitly requires
differentiability and equality on a LINE NEIGHBORHOOD. It proves equality of
only the axial Jacobian column. Applying it gives `slowBase_axial_derivative`.
No derivative is inferred from equality at one point or merely along the
spacetime trajectory.

`actual_raw_eq_slowBase_germ`, `actual_periodic_eq_slowBase_germ`, and
`actual_compact_eq_slowBase_germ` instantiate the actual potential and direct
sequences. `minimal_transfer_of_slowBase_germ` combines their retained germ
with the slow-base line calculation. `actual_minimal_transfer_eventually`
proves the two required conditions sufficiently late for both final fields.

`selected_schedule_minimal_transfer_late_interval` has the exact quantified
form: for any `B,N0,hN,a`, with `hN : geometricThreshold≤N0`, the actual
`SelectedSchedule ... a`, and a supplied natural solution using
`CorrectionInitialization.ActualPrimary.h` and `nominal.axis.j`, there exists
`T<1` such that for every `T<t<1` and each of the two final velocities:

```text
HasDerivAt γ (u_final(t,γ(t))) t
spatialDerivative u_final t (γ(t)) e₂ = (K/(1-t)) • e₂.
```

The chosen `γ` and `K` use `nominal.axis.small`. `selected_witness` supplies
such a schedule at the selected budget and threshold. Every compact interval
`[aTime,bTime]` with `T<aTime≤bTime<1` lies within this proved interval.
This is a minimal-condition audit, kept separate from the magnetic transport
specialization. It asserts no full natural-core neighborhood or gradient
agreement and no magnetic solution for either final field.

### Correction-by-correction value and axial derivative

All entries refer to velocity contributions at the path. For potentials, the
contribution means their spatial curl, not the undifferentiated potential.
A zero spacetime germ implies zero value and zero axial Jacobian column via
`zero_germ_value_and_axial_derivative`; curl locality first applies this to
potential corrections.

| Term | Velocity value on the path | Axial directional derivative | Exact reason/conditions |
| --- | --- | --- | --- |
| Leading slow meridional field | `q^(-A)*U(j,eta0)*e₂ = γ′` | `(K/(1-t))*e₂` | Prescribed leading axial data and differentiation of the full axial-line identity |
| Positive slow Borel meridional terms, including their Borel cutoffs | Zero | Zero | Positive axial coefficient values vanish for every axial eta; radial averages agree with axial values. `slowSum_eq_leading_of_positive_zero` preserves the identity for the actual sum. No cutoff-derivative estimate is used. |
| Slow-base swirl, leading and positive orders | Zero | Zero | Axisymmetric swirl velocity vanishes on the entire spatial axis; differentiating that line identity gives zero axial derivative. Transverse swirl derivatives can be nonzero and are not identified. |
| Tail gauge subtraction from the base potential | Zero curl contribution | Zero | `finalPotential_sameCurl` holds throughout the open preterminal region. The gauge potential itself need not vanish. |
| Initial potential (initial physical wave plus initial stream mean) | Zero | Zero | `initialPotential_axisZeroOn`; spatial-curl locality, within `localDomain` |
| Positive particular potentials | Zero | Zero | `particular_axisZeroOn`; spatial-curl locality |
| Signed-copy potentials | Zero | Zero | `signed_axisZeroOn`; spatial-curl locality |
| Positive stream-mean potentials | Zero | Zero | `stream_axisZeroOn`; combined in `positivePotential_axisZeroOn` |
| Direct angular stages and their sum, including the initial direct stage | Zero | Zero | `LocalAngularDiagonal.angularSupport`, `directDiagonal_zero_germ`, and schedule local finiteness; the proof uses germs, not small amplitude |
| Zeroth diagonal cutoff of the retained base | No change | No change | Strict plateau `abs((a 0)*q)<1/2`; its derivatives vanish locally |
| Spatial potential/direct cutoffs | No change | No change | `γ(t)` in `SpatialLocalization.plateau`; includes all curl cutoff derivatives |
| Periodization | No change | No change | `MixedPeriodicAssembly.periodicVelocity_eventuallyEq`; other copies do not change the local germ |
| Time activation | No change for `t>3/4` | No change for `t>3/4` | Time switch equals one locally. Earlier it multiplies both spatial value and axial derivative; unrestricted early-time transfer is not asserted. |
| Pressure and force stages | Not a velocity contribution | Not a velocity contribution | They do not enter the two kinematic transfer conditions |

`path_eventually_in_plateaus` proves the required common late-time conditions:
`t<1`, `q(t)<qbig`, `abs((a 0)*q(t))<1/2`, `3/4<t`, and spatial plateau
membership. It uses `q(t)→0` and `γ(t)→0` as `t→1-`, with `D(h)>0`.
Thus the finite chosen schedule value is fixed before selecting the late
interval. No small-amplitude-to-small-derivative inference is made.

### Validation and remaining scope

- Full `lake build`: passed, 11,258 jobs.
- A separate Lean audit imported `MagneticSimilarityGradient`,
  `MagneticCoreAmplification`, and `MagneticAxisTransfer`, then ran
  `#print axioms` for all 40 theorem declarations (11 preserved gradient,
  15 amplification, 14 transfer). Every theorem depends only on `propext`,
  `Classical.choice`, and `Quot.sound`; none depends on `sorryAx`.
- Neither new module contains `sorry` or a new axiom declaration.
- The full build reports four inherited `sorry` warnings in
  `ComparatorChallenges/Euler.lean` and `ComparatorChallenges/NavierStokes.lean`.
- `git diff --check` passed. The existing gradient module was preserved.
- All task changes, including the previously staged gradient and handoff files,
  are included in the milestone commit on `main`; no push is requested.

Remaining work, if requested: specialize the generic magnetic transport theorem
to a supplied induction solution for one of the assembled fields; prove any
additional magnetic PDE existence or solenoidality statements separately.
Full transverse gradient/swirl transfer remains unproved and is unnecessary
for this pure-axial milestone. Resistivity, backreaction, global flow
identification, and finite-volume amplification remain outside this task.

## Historical sessions (superseded by the milestone above)

The rest of this file preserves earlier handoff notes. Statements below about
unfinished compilation or unresolved minimal transfer describe those earlier
sessions, not the current proof status.

## Historical pause state

The sections below, until “Resumed implementation”, record the earlier pause.
The unfinished-compilation statements in this historical section are superseded
by the current status above.

This note records the state when the user paused implementation and requested
that the active prompt and progress be documented. No further Lean changes were
made while writing this note. The new gradient module is unfinished and does
not currently compile. Do not treat its final coefficient theorem as verified.

## Active user request

Continue MHDSingularity from the current local state. Do not implement resistive
MHD, curl form, backreaction, or magnetic amplification.

1. Inspect the final assembled OpenAI Navier–Stokes velocity: locate natural-core
   insertion, all cutoffs/localizations, actual neighborhood agreement with the
   distinguished trajectory, and existing agreement lemmas.
2. If justified by the construction, prove
   `assembled_agrees_with_naturalCore_near_distinguishedTrajectory` on compact
   intervals `[a,b]`, `b < 1`, preferably as genuine neighborhood equality.
3. From genuine local equality prove
   `distinguished_trajectory_isLagrangian_for_assembled` and
   `spatialDerivative_assembled_eq_naturalCore_on_distinguishedTrajectory` at
   interior times. Never infer derivative equality from pointwise equality.
4. In `NavierStokes/MagneticSimilarityGradient.lean`, derive the exact continuous
   linear map `spatialDerivative u_core t (gamma_* t)` in a basis-friendly form.
5. Expose transverse isotropic strain, axial strain, xy rotation/swirl, and all
   axial/transverse coupling entries in terms of `h`, `j`, `eta_0`, `q`, and
   existing profile quantities.
6. Prove the trace of the strain part is zero.
7. Keep the axial coefficient exact. Do not claim `kappa = 4` or `B_z ~ q^-4`.
8. Run `lake build`.
9. Report the exact final velocity, local-agreement status, gradient matrix and
   block structure, remaining profile quantities, theorem names, assumptions,
   and any `sorry` or axioms.

The latest instruction supersedes further implementation for this turn:
“Ok simply document your current prompt and progress so far in markdown document
in the repo currently”.

## Previously completed baseline

The existing modules are:

- `NavierStokes/MagneticInduction.lean`: `MagneticField` aliases the existing
  time-first `VelocityField`. Solenoidality and stretching-form induction are
  separate predicates.
- `NavierStokes/MagneticTrajectory.lean`: endpoint-continuous trajectories with
  interior derivatives, and the material chain rule.
- `NavierStokes/MagneticCauchy.lean`: deformation existence and uniqueness and
  trajectory-level Cauchy transport, reusing `NavierStokes.TangentODE` and
  `Euler.ComparatorBridge.linearODE_eq_zero`.
- `NavierStokes/MagneticSimilarityTrajectory.lean`: the constant-eta natural-core
  trajectory, selected from the inherited unique root of `NaturalAxisData.H`.

Write

```text
D(h) = 1/2 - h
A(h) = 1/2 + h
d(eta) = 1 - eta^2
L(h,eta) = 1 - 2*h*eta^2
U(j,eta) = 4*eta + j
H(h,j,eta) = D(h)*eta + d(eta)*U(j,eta).
```

For the selected root `eta_0`, the proved core path is

```text
q(t) = (1-t)/d(eta_0)
gamma_*(t) = q(t)^D(h) * eta_0 * e_2.
```

The principal existing theorem is
`NavierStokes.MagneticSimilarityTrajectory.distinguished_trajectory_isLagrangian`.
It assumes `NaturalAxisData.SmallParameters h j`, a
`NaturalProfile.IsNaturalSolution`, and `a <= b < 1`. Its `_of_agrees` variant
requires explicit velocity agreement along the path; that hypothesis has not
been discharged for the assembled solution.

The last full baseline build succeeded with 11,255 jobs. The baseline trajectory
theorems were audited and use only `propext`, `Classical.choice`, and `Quot.sound`.
There are inherited comparator challenge `sorry` warnings, independent of those
proofs. The unrelated npm files were removed in the preceding work, and README
was updated. The Lake name `NavierStokesAndEuler` was deliberately retained to
match `lakefile.toml`.

## Construction inspection: established findings

### Exact final witness expression

`NavierStokes/ComparatorTheorem.lean` obtains its candidate from
`ActualCandidateAssembly.selected_candidate`.

In `NavierStokes/ActualCandidateAssembly.lean`:

- `Witness` (around line 1121) existentially supplies a selected schedule
  `a : ℕ → ℕ`, the extensions, forcing, and candidate properties.
- `selected_witness` specializes it to the selected budget and threshold.
- `selected_candidate` unpacks that witness; there is no single exported named
  selected velocity definition here.
- The exact viscosity-one periodic candidate velocity in that witness is

```lean
TimeLocalization.activatedVelocity
  (MixedPeriodicAssembly.periodicVelocity ASum BSum)
```

where `ASum` and `BSum` are `SolenoidalDiagonal.potentialSum`s, using scales
`fun j => (a j : ℝ)`, `PhysicalWaveSum.physicalQ h`, and the selected potential
and direct stage sequences. The raw velocity is

```lean
MixedPeriodicAssembly.velocity ASum BSum
-- spatialCurl ASum + BSum
```

The whole-space comparator route was not fully traced in this session. Do not
silently conflate its candidate or viscosity rescaling with the periodic
viscosity-one witness above.

### Cutoffs and neighborhoods

- `TimeLocalization.activatedVelocity u z = timeSwitch z.1 • u z`.
- `TimeLocalization.activatedVelocity_zero_early`: zero when `|t| <= 3/8`.
- `TimeLocalization.activatedVelocity_eq_late`: equals `u` for `3/4 <= t`.
- `TimeLocalization.activatedVelocity_eventuallyEq_late`: full spacetime germ
  equality for `3/4 < t`.
- `SpatialLocalization.spatialCutoff` uses
  `cutoff (16 * radialSquare x) * cutoff (4 * x 2)` and acts on potentials (and
  on the direct field separately). All curl derivatives of the cutoff are kept.
- `MixedPeriodicAssembly.periodicVelocity` periodizes the localized potential
  curl and the localized direct field separately.
- `MixedPeriodicAssembly.periodicVelocity_eventuallyEq` gives full spacetime
  neighborhood equality to the raw mixed velocity when the spatial point is
  in `SpatialLocalization.plateau`.
- `GermCandidateAssembly.potentialSum_eq_base_germ` uses local finiteness,
  zero germs of initialization/stage corrections, and the strict zeroth-cutoff
  condition `|scales 0 * q w| < 1/2`.
- `MixedAxisPreservation.mixedDiagonal_eq_base_germ` gives a true neighborhood
  equality to the **base curl**, under its axis/domain/support/scale conditions.
- `SolenoidalDiagonal.spatialCurl_eventuallyEq` transfers potential germs to
  velocity germs.
- `ResidualRegularity.space_fderiv_congr` transfers full spacetime germs to
  ordinary spatial Fréchet derivatives. It requires no differentiability
  assumption because it uses locality of `fderiv`.

### Important obstruction: natural core versus slow base

The actual inserted base is
`TailGaugePotential.finalPotential H v upper bandFloor`, whose curl is related by
`TailGaugePotential.finalPotential_sameCurl` to
`FinalSlowBase.velocity H v upper bandFloor`.

`FinalSlowBase.velocity` is a `SlowBorelBase.baseVelocity` constructed from a
Borel sum of slow profiles. It is not definitionally
`NaturalCore.coreVelocity`. The natural profiles enter its leading coefficients
through the nominal/aligned/modulated hierarchy, including:

- `AssembledSlowBase.nominalHierarchy_base`
- `AssembledSlowBase.nominalCoefficients_zero_fields`
- `EntranceAlignedBase.modulated_zero_fields`
- `EntranceAlignedBase.modulated_leading_axis`
- `EntranceAlignedBase.modulated_positive_axis`

The last lemma proves positive-order `phi`, `axial`, and `pressure` values vanish
**on the axis**. It does not prove they vanish in a neighborhood.

`GlobalSlowProfiles.profiles_inner_eq` says the positive profiles agree in an
inner region with the original local slow hierarchy. That hierarchy solves
inhomogeneous equations involving preceding diffusion:
`SlowRecursion.sequence_positive_order`.

Do not misread `EntranceAlignedBase.positive_coefficients_zero`: its conclusion
is about `SlowExpansionResidual.angularCoefficient` and `axialCoefficient`
(residual coefficients), not about the velocity profiles vanishing.

Consequences:

1. The requested unrestricted agreement on every `[a,b]` with `b < 1` is false
   for the activated candidate: it is zero at early times whereas the
   distinguished natural-core axial velocity is nonzero.
2. Even late, inspected lemmas supply neighborhood agreement with the **slow
   base**, not with the natural core. No late neighborhood equality theorem
   between the assembled velocity and natural core was proved.
3. This inspection does not prove that such late equality is impossible for
   every particular constructed profile; it establishes that it cannot be
   inferred from the cited axis-value lemmas.
4. A promising alternative is an actual axis-jet calculation: in an
   axisymmetric smooth velocity, the first Cartesian derivative only uses
   axial derivatives of axis meridional data and axis swirl data. Those may
   agree exactly even if whole neighborhoods of the fields differ. This must
   be proved using structure and derivative identities, not inferred from
   equality along a curve. This alternative has not yet been implemented for
   the assembled slow base.

No new assembled-velocity definition or agreement/transfer theorem has been
written in this interrupted session.

## Current new file and exact calculation

The only new Lean file in the working tree at the pause is
`NavierStokes/MagneticSimilarityGradient.lean` (untracked at the time of writing).
Its namespace is `NavierStokes.MagneticSimilarityGradient`.

The proposed exact core matrix is

```text
          [ -alpha/2   -rot       0 ]
Du_core = [  rot       -alpha/2   0 ]
          [  0          0      alpha ]
```

This is encoded as a continuous linear map `axisOperator alpha rot`, not merely
as a matrix abbreviation. Its transverse strain is `-alpha/2`, its axial strain
is `alpha`, and the four axial/transverse couplings vanish. Positive `rot` means
counterclockwise rotation, hence the negative `(0,1)` entry. The trace is zero.

The generic axis-gradient theorem starts with the existing formulas in
`AxisymmetricFields.velocity_zero`, `velocity_one`, and `velocity_two`, proves
local equality to their Cartesian expression using `C²` profile regularity,
and differentiates that expression. It does not infer a derivative from a
single point's value.

The coefficient definitions and intended exact formulas are

```text
alpha = partialZ (NaturalCore.meridionalPotential h V) (t,0,pathZ h eta t)
rot   = -partialS (NaturalCore.swirlPotential h f) (t,0,pathZ h eta t)

axialCoefficientExact(h,j,eta)
  = [4*d(eta) - 2*A(h)*eta*U(j,eta)] / L(h,eta)

alpha = q(t)^(-1) * axialCoefficientExact(h,j,eta)
rot   = q(t)^(-h) / q(t) * a0(eta).
```

These formulas concern the velocity gradient. `axialCoefficientExact` is **not**
defined as a magnetic exponent. No amplification, `kappa = 4`, or asymptotic
claim has been introduced. The swirl still contains the prescribed axis datum
`a0(eta)`. The axial formula has no remaining unknown radial profile quantity.
The closed axial formula is mathematically derived but its final Lean algebra
step remains unfinished, as detailed below.

Declarations currently written:

- `axisOperator`
- `axisOperator_apply`
- `axisOperator_matrix`
- `axisOperator_trace`
- `spatialDerivative_velocity_on_axis`
- `axialStrain`
- `swirlRate`
- `spatialDerivative_naturalCore_on_trajectory`
- `axialCoefficientExact`
- `swirlRate_eq`
- `meridionalPotential_axis`
- `axialStrain_eq` — unfinished compilation

The last Lean invocation reported only the final `axialStrain_eq` algebra error.
Earlier declarations elaborated without reported errors in that invocation,
but the module as a whole has not passed, has no successful new build, and has
not received a final axiom audit.

## Exact unfinished proof state

Last command:

```sh
lake env lean NavierStokes/MagneticSimilarityGradient.lean
```

It exited with code 1. The remaining error is near line 206, the first `calc`
step at the end of `axialStrain_eq`, using `by ring`.

The proof already establishes:

```text
q^(1-D) * q^(-A-1) = q^(-1)             -- hp1
q^(-A) / q^D = q^(-1)                  -- hp2
```

It obtains the axial derivative by differentiating the meridional potential
identity on the entire spatial axis, using the inherited coordinate derivative
lemmas. After substitution at the path, the remaining regrouping involves

```text
1 / (q^D * L)   versus   (1/q^D) * (1/L).
```

`ring` treats the inverse of the product as a separate atom and does not close
the equality. A likely next fix is to normalize product inverses/division
before `ring` (for example `simp only [div_eq_mul_inv, mul_inv_rev]` with the
applicable real-field lemma), or use `field_simp` with proved nonzero `q^D`
and `L`. This suggestion has not been tried. Avoid altering the mathematics
or adding assumptions merely to make the algebra tactic succeed.

Other Lean details already resolved:

- The imported scope reserves `ω`; the file uses the name `rot` instead.
- `HasFDerivAt` has `mul_const`, not the attempted `div_const`; division by two
  was handled as multiplication by `1/2`.
- Give profile-direction derivatives explicit types to avoid metavariables.
- Pull eventual smoothness back using `ContinuousAt.eventually`.
- The field-level axis-operator proof uses actual local equality and
  `EventuallyEq.fderiv_eq (𝕜 := ℝ)`.
- `mem_setOf_eq` was replaced by `mem_ofPred_eq` to avoid deprecation warnings.

## Regularity and parameter assumptions in the new file

- Generic Cartesian axis-gradient theorem: `ContDiffAt ℝ 2` for both scalar
  potentials at the profile point, and `x 0 = x 1 = 0`.
- Natural-core specialization and coefficient formulas: `0 < h < 1/2`,
  `NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr`, `eta^2 < 1`, `t < 1`.
- The gradient formulas work for any such constant eta; they do not need the
  root condition. Specialize to the distinguished eta with
  `distinguishedEta_sq_lt_one` and the existing small-parameter bounds.
- The existing `IsNaturalSolution` packages more regularity/PDE data than the
  isolated gradient calculation minimally needs. It is used to reuse the
  established smoothness and prescribed axis values.

No literal `sorry` or new axiom declaration was intentionally added. Since the
new module does not compile, do not claim it is fully verified or axiom-audited.

## Next actions after resuming implementation

1. Resolve the last rational-algebra normalization in `axialStrain_eq`.
2. Add a concise combined closed-form operator/matrix theorem if useful.
3. Decide the correct assembled-flow theorem: restrict to sufficiently late
   times and distinguish true local equality to the slow base from a separate
   first-axis-jet comparison to the natural core. Do not insert a hypothetical
   natural-core germ as if it were discharged by the construction.
4. Trace the chosen schedule, local domain, zeroth cutoff, direct-field zero
   germs, spatial plateau, and time-switch plateau for the distinguished path.
5. Prove the valid assembled trajectory/gradient connection, or precisely
   document remaining mathematical obligations without asserting agreement.
6. Run `lake build`, then audit all new principal theorems with `#print axioms`.
7. Report all assumptions and any remaining limitations. Keep amplification,
   resistivity, curl form, global flow derivatives, and backreaction deferred.

## Environment and working-tree notes

- Repository: `/mnt/ssd/homedirs/harpe-svc/MHDSingularity`.
- Tools run through bash. The ordinary filesystem sandbox has repeatedly failed
  to initialize (`bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted`).
  Inspection and edits have therefore used explicit escalated command calls.
- At the pause, `git status --short` showed only
  `?? NavierStokes/MagneticSimilarityGradient.lean`; writing this note also adds
  `MHD_PROGRESS.md`.
- No commit or push was performed in this session.


## Resumed implementation

### Completed proofs and validation

The last `axialStrain_eq` step now normalizes division and inverses of products
with `simp only [div_eq_mul_inv, mul_inv_rev]` before `ring`. No mathematical
assumption was added. The following combined results were added:

- `spatialDerivative_naturalCore_on_trajectory_exact`: the full continuous
  linear map with both coefficients substituted.
- `spatialDerivative_naturalCore_on_distinguishedTrajectory`: specializes that
  map to `distinguishedEta p`, under `SmallParameters h j`, the natural-solution
  predicate, and `t < 1`.
- `axisOperator_strain_trace`: zero trace of `axisOperator alpha 0`.

Together with `axisOperator_matrix`, these give precisely the matrix in the
calculation section. Its symmetric part is `diag(-alpha/2,-alpha/2,alpha)`;
its skew part is the xy rotation with entries `-rot` and `rot`. The four
axial/transverse couplings are zero. The general calculation assumes `0<h<1/2`,
`eta^2<1`, `t<1`, and `NaturalProfile.IsNaturalSolution`; the root condition is
only needed to identify the curve as Lagrangian. The only remaining prescribed
profile datum in the coefficients is `a0(eta)`.

Validation: `lake build` succeeded with 11,256 jobs. A separate Lean file imported
the built module and printed axioms for all eleven theorem declarations; every
result listed only `propext`, `Classical.choice`, and `Quot.sound`. No magnetic
amplification or exponent claim was introduced.

### Whole-space candidate traced

`ComparatorR3Theorem.navier_stokes_breakdown_R3` extracts
`R3CompactCandidate.selected_compact_candidate`. In `R3ActualCandidate.lean`,
this extracts the same `ActualCandidateAssembly.selected_witness` sums and
applies `R3CompactCandidate.of_localized_fields`. Its exact viscosity-one
velocity is:

```lean
R3CompactCandidate.velocity ASum BSum
-- TimeLocalization.activatedVelocity
--   (fun z => SpatialLocalization.cutVelocity ASum z +
--             SpatialLocalization.cutPotential BSum z)
```

Thus the whole-space field retains the spatial cutoff and its curl derivatives,
but has no periodization. Its force is `R3CompactCandidate.compactForce forcing`.
The periodic velocity remains the activated `MixedPeriodicAssembly.periodicVelocity`
from the earlier section. The comparator adapters rescale the force to
`nu^2 • forcing (nu*t,x)` and argue by normalization of hypothetical solutions;
the exact gradient proved here is for the unrescaled natural core.

### Precise remaining assembled-flow obligations

Let `eta = distinguishedEta p`, `d = 1-eta^2 > 0`,
`q(t) = (1-t)/d`, `z(t) = eta*q(t)^D(h)`, and let `a` be a schedule supplied by
`selected_witness`. `MixedCandidateWitness.SelectedSchedule` supplies `1 ≤ a 0`,
positivity, doubling, strict monotonicity, divergence of the real scales, and
`1/(a j : real) < qbig`. The following are sufficient geometric conditions for
using the inspected germ lemmas at `(t, trajectory h eta t)`:

1. `t < 1` and `q(t) < qbig`, putting the point in `localDomain`.
2. `(a 0 : real)*q(t) < 1/2`, the strict zeroth-cutoff plateau.
3. `|eta|*q(t)^D(h) < 1/8`, the spatial plateau; radial square is zero.
4. `3/4 < t`, the open time-activation plateau.

For `t<1`, the first two bounds follow respectively from
`t > 1-d*qbig` and `t > 1-d/(2*(a 0 : real))`. Since `D(h)>0`, the third also
holds sufficiently late. These threshold deductions and their uniform use on
compact intervals `[aTime,bTime]` lying after a common threshold have not yet
been packaged as Lean theorems for the selected witness. They do not establish
agreement on arbitrary early intervals.

At such points, `initialPotential_axisZeroOn` and
`positivePotential_axisZeroOn` supply the actual potential correction germs;
`GermCandidateAssembly.potentialSum_eq_base_germ` then identifies the potential
sum germ with `TailGaugePotential.finalPotential`. To obtain the full mixed
velocity germ, also instantiate the direct-series zero-germ/local-finiteness
argument with `LocalAngularDiagonal.rawSeries` and its angular supports.
The existing actual-candidate origin proof uses the direct field's axis VALUE
identity, so that proof alone does not supply this derivative-level step.
Compose the potential curl germ, direct zero germ, spatial plateau, and time
plateau, and use `TailGaugePotential.finalPotential_sameCurl` on the open
preterminal region. The resulting comparison is to `FinalSlowBase.velocity`.

The decisive additional mathematical obligation is then to compute the first
Cartesian axis derivative of that Borel-summed slow base. This requires:

- Axis identities for the actual summed meridional data on an axial interval,
  including all Borel cutoff factors, so their axial derivative can be computed.
- The radial derivative of the actual summed swirl potential on the axis.
  Positive-order `phi` values being zero is insufficient by itself to identify
  that derivative.
- Identification of the leading profile and swirl normalization with the
  particular natural solution used in the gradient theorem.

`modulated_leading_axis` identifies the zeroth axial coefficient with
`4*eta+j`; `modulated_positive_axis` makes positive `phi`, axial, and pressure
VALUES vanish on the axis. Neither is a neighborhood identity of velocities.
The new generic `spatialDerivative_velocity_on_axis` can be used once the
actual slow-base potentials, their regularity, and those two derivative data
are identified. A proved axis-value identity would suffice for the Lagrangian
transfer; the gradient transfer additionally needs the independently proved
axis derivative identities or a genuine neighborhood equality.

No theorem named `assembled_agrees_with_naturalCore_near_distinguishedTrajectory`,
`distinguished_trajectory_isLagrangian_for_assembled`, or
`spatialDerivative_assembled_eq_naturalCore_on_distinguishedTrajectory` is claimed
by this work. The unresolved identification is explicit rather than hidden in a
new hypothesis advertised as a construction theorem.
