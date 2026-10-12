import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import ChallengeDeps
import Submission.Work.ChiSmall
import Submission.Work.SlidingSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The coordinatewise bad-band (g2) statement for the cosine-M cutoffs

At the dℓ-scale layer the small-box cutoff is the two-factor product
`chiSmallB M ℓ d u x = χ_M(x/ℓ)·χ_M(x/(ℓd) − u)` (`Submission.Work.ChiSmall`).
FS's bad band `ℐ` (`final_v2.tex`, thm:aprioriHLambda proof) is
**coordinatewise**: with `A := ½ℓ(1+d)` and `w := (ℓd)•u`,

    ℐ := {u | (∃ j, A − 2μ^{-1/3} ≤ |w_j|) ∧ (∀ j, |w_j| ≤ A)}

(where the second conjunct is automatic on the support of `χ_{B(u)}`).
This module states that band (replacing the Euclidean-norm typeset
`SlidingSum.chiB_badband_volume_bound`, which is a loose transcription — see
SmallBoxDesignNote.md Session-175) and proves its first analytic containment:
**on the bad band the cutoff vanishes to order `2M` in `μ^{-1/3}/ℓ`**
(combination of `chiSmallB_band_support_slab` — u-band ⟹ x-face-slab — and
`chiSmallB_slab_decay`).  The subsequent integral assembly over
`SlidingSum.band_u_measure_le` is the next layer.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology ContDiff

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- the coordinatewise `μ ↦ 4μ` bad band: some face-coordinate of
`w := (ℓd)•u` reaches `≥ A − 2μ^{-1/3}` (`A := ½ℓ(1+d)`), all coordinates
`≤ A`. -/
def chiSmallBadBand (ℓ d μ : ℝ) : Set ℝ³ :=
  {u : ℝ³ |
    (∃ j : Fin 3,
      (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤ |((ℓ * d) • u).ofLp j|)
      ∧ (∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d))}

lemma chiSmallB_nonneg (M : ℕ) (ℓ d : ℝ) (u x : ℝ³) : 0 ≤ chiSmallB M ℓ d u x := by
  dsimp [chiSmallB]
  exact mul_nonneg (chiScale_nonneg ℓ x) (chiSmall_nonneg M _)

/-- **First containment of the bad band: sup-decay of the cutoff.**  For
`u` on the coordinatewise bad band, every value of the two-factor cutoff
vanishes to order `2M` in `μ^{-1/3}/ℓ`:

    ∀ x,  (χ_{B(u)}(x))² ≤ chiSmallBandDecay M d · (2μ^{-1/3}/ℓ)^{2M} .

At the repointed cutoff (`chiScale` at the `ℓ`-scale) the `M`-th-power smallness comes from the
*`ℓd`-scale* factor: `chiSmallB_band_support_slab` puts `(ℓd)u` near the outer face, whence the
small-box coordinate `(x − (ℓd)u)_j` is within `2μ^{-1/3}` of the small-box face
`|(x−(ℓd)u)_j| = (ℓd)/2`, and `chiSmallB_slab_decay` delivers
`|χ_B(x)| ≤ chiSupAbs·chiSmallDecay M·(2μ^{-1/3}/(ℓd))^M`.  For `x` with `χ_{B(u)}(x) = 0`
the bound is trivial. -/
lemma chiSmallB_badband_sup_decay {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (hμ : 0 < μ) {u x : ℝ³} (hu : u ∈ chiSmallBadBand ℓ d μ) :
    (chiSmallB M ℓ d u x) ^ 2 ≤ chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) := by
  have hδ0 : 0 ≤ 2 * μ ^ (-1 / 3 : ℝ) :=
    mul_nonneg (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hμ _))
  by_cases hx0 : chiSmallB M ℓ d u x = 0
  · rw [hx0]
    have h2 : 0 ≤ (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) :=
      pow_nonneg (div_nonneg hδ0 (le_of_lt hℓ)) _
    simpa using mul_nonneg (chiSmallBandDecay_nonneg M hd) h2
  · obtain ⟨j, hj⟩ := hu.1
    have hbig : |x.ofLp j| ≤ ℓ / 2 := chiSmallB_support_big_box hM hℓ hx0 j
    have hsm : |((x - (ℓ * d) • u).ofLp j)| ≤ ℓ * d / 2 :=
      chiSmallB_support_small_box_dist hM hℓ hd hx0 j
    have htri : |((ℓ * d) • u).ofLp j| - |x.ofLp j| ≤ |((x - (ℓ * d) • u)).ofLp j| := by
      have h1 : |((ℓ * d) • u).ofLp j| - |x.ofLp j|
          ≤ |((ℓ * d) • u).ofLp j - x.ofLp j| := abs_sub_abs_le_abs_sub _ _
      have h2 : ((ℓ * d) • u).ofLp j - x.ofLp j = -((x - (ℓ * d) • u).ofLp j) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      rwa [h2, abs_neg] at h1
    -- the small-box face distance is at most 2μ^{-1/3}
    have hface : max (ℓ * d / 2 - |(x - (ℓ * d) • u).ofLp j|) 0 ≤ 2 * μ ^ (-1 / 3 : ℝ) := by
      refine max_le ?_ hδ0
      linarith
    have hpos : 0 < ℓ * d := mul_pos hℓ hd
    have hp : (max (ℓ * d / 2 - |(x - (ℓ * d) • u).ofLp j|) 0 / (ℓ * d)) ^ M
        ≤ (2 * μ ^ (-1 / 3 : ℝ) / (ℓ * d)) ^ M :=
      pow_le_pow_left₀ (div_nonneg (le_max_right _ _) (le_of_lt hpos))
        (div_le_div_of_nonneg_right hface (le_of_lt hpos)) M
    have hb : |chiSmallB M ℓ d u x|
        ≤ chiSupAbs * chiSmallDecay M * (2 * μ ^ (-1 / 3 : ℝ) / (ℓ * d)) ^ M :=
      le_trans (chiSmallB_slab_decay hM hℓ hd u x j)
        (mul_le_mul_of_nonneg_left hp (mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)))
    have hsplit : (2 * μ ^ (-1 / 3 : ℝ) / (ℓ * d)) ^ (2 * M)
        = (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) * (d⁻¹) ^ (2 * M) := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc
      (chiSmallB M ℓ d u x) ^ 2 = |chiSmallB M ℓ d u x| ^ 2 := by rw [sq_abs]
      _ ≤ (chiSupAbs * chiSmallDecay M * (2 * μ ^ (-1 / 3 : ℝ) / (ℓ * d)) ^ M) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = chiSupAbs ^ 2 * (chiSmallDecay M) ^ 2
            * ((2 * μ ^ (-1 / 3 : ℝ) / (ℓ * d)) ^ M) ^ 2 := by
          rw [mul_pow, mul_pow]
      _ = chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) := by
          rw [chiSmallBandDecay, ← pow_mul, Nat.mul_comm M 2, hsplit]
          ring

-- ============ measure of the x-support cube (assembly infrastructure) ============

lemma eucl_cube_measurable {c : ℝ} : MeasurableSet {x : ℝ³ | ∀ j : Fin 3, |x.ofLp j| ≤ c} := by
  have hset : {x : ℝ³ | ∀ j : Fin 3, |x.ofLp j| ≤ c} =
      (fun x : ℝ³ => x.ofLp) ⁻¹' {f : Fin 3 → ℝ | ∀ j : Fin 3, |f j| ≤ c} := by
    ext x
    change (∀ j : Fin 3, |x.ofLp j| ≤ c) ↔ ∀ j : Fin 3, |(x.ofLp) j| ≤ c
    exact Iff.rfl
  rw [hset]
  refine (PiLp.volume_preserving_ofLp (Fin 3)).measurable ?_
  have hcube : {f : Fin 3 → ℝ | ∀ j : Fin 3, |f j| ≤ c} =
      Set.univ.pi (fun _ : Fin 3 => Set.Icc (-c) c) := by
    ext f
    change (∀ j : Fin 3, |f j| ≤ c) ↔
      ∀ j : Fin 3, j ∈ (Set.univ : Set (Fin 3)) → f j ∈ Set.Icc (-c) c
    constructor
    · intro h j hj
      exact abs_le.mp (h j)
    · intro h j
      rw [abs_le]
      exact h j (by simp)
  rw [hcube]
  exact MeasurableSet.pi (s := (Set.univ : Set (Fin 3))) (t := fun _ : Fin 3 => Set.Icc (-c) c)
    Set.countable_univ (by intro i hi; exact measurableSet_Icc)

/-- volume of the coordinate cube `{|x_j| ≤ c for all j}` in `EuclideanSpace`
is `(2c)³` (transferred from the function cube via the volume-preserving
`ofLp`; `coordCube_volume`). -/
lemma eucl_cube_volume {c : ℝ} (hc : 0 ≤ c) :
    (volume : Measure ℝ³) {x : ℝ³ | ∀ j : Fin 3, |x.ofLp j| ≤ c} = ENNReal.ofReal ((2 * c) ^ 3) := by
  have hset : {x : ℝ³ | ∀ j : Fin 3, |x.ofLp j| ≤ c} =
      (fun x : ℝ³ => x.ofLp) ⁻¹' {f : Fin 3 → ℝ | ∀ j : Fin 3, |f j| ≤ c} := by
    ext x
    change (∀ j : Fin 3, |x.ofLp j| ≤ c) ↔ ∀ j : Fin 3, |(x.ofLp) j| ≤ c
    exact Iff.rfl
  rw [hset]
  have hfc : MeasurableSet {f : Fin 3 → ℝ | ∀ j : Fin 3, |f j| ≤ c} := by
    have hcube : {f : Fin 3 → ℝ | ∀ j : Fin 3, |f j| ≤ c} =
        Set.univ.pi (fun _ : Fin 3 => Set.Icc (-c) c) := by
      ext f
      change (∀ j : Fin 3, |f j| ≤ c) ↔
        ∀ j : Fin 3, j ∈ (Set.univ : Set (Fin 3)) → f j ∈ Set.Icc (-c) c
      constructor
      · intro h j hj
        exact abs_le.mp (h j)
      · intro h j
        rw [abs_le]
        exact h j (by simp)
    rw [hcube]
    exact MeasurableSet.pi (s := (Set.univ : Set (Fin 3))) (t := fun _ : Fin 3 => Set.Icc (-c) c)
      Set.countable_univ (by intro i hi; exact measurableSet_Icc)
  have hpre := MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin 3))
    hfc.nullMeasurableSet
  rw [hpre]
  exact coordCube_volume hc

/-- volume of a translate of the coordinate cube (translation preserves
measure): `vol {x | |(x − a)_j| ≤ c ∀ j} = (2c)³`. -/
lemma eucl_cube_translate_volume {c : ℝ} (hc : 0 ≤ c) (a : ℝ³) :
    (volume : Measure ℝ³) {x : ℝ³ | ∀ j : Fin 3, |((x - a).ofLp j)| ≤ c} =
      ENNReal.ofReal ((2 * c) ^ 3) := by
  let R : ℝ³ → ℝ³ := fun x => -a + x
  have hR : (fun x : ℝ³ => x - a) = R := by
    funext x
    dsimp [R]
    rw [sub_eq_add_neg, add_comm]
  have hmp : MeasurePreserving R volume volume := by
    dsimp [R]
    exact measurePreserving_add_left (volume : Measure ℝ³) (-a)
  have hset : {x : ℝ³ | ∀ j : Fin 3, |((x - a).ofLp j)| ≤ c} = R ⁻¹' {y : ℝ³ | ∀ j : Fin 3, |y.ofLp j| ≤ c} := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_preimage]
      change ∀ j : Fin 3, |((-a + x).ofLp j)| ≤ c
      intro j
      simpa [add_comm, sub_eq_add_neg] using hx j
    · intro hx j
      rw [Set.mem_preimage] at hx
      have hx' : ∀ j : Fin 3, |((-a + x).ofLp j)| ≤ c := by
        simpa [R] using hx
      simpa [add_comm, sub_eq_add_neg] using hx' j
  rw [hset]
  have hcubemeas : MeasurableSet {y : ℝ³ | ∀ j : Fin 3, |y.ofLp j| ≤ c} := eucl_cube_measurable
  have hpre := MeasurePreserving.measure_preimage hmp hcubemeas.nullMeasurableSet
  rw [hpre]
  exact eucl_cube_volume hc

/-- the `x`-support of the two-factor cutoff lies in the `(ℓd)`-cube centred
at `w := (ℓd)•u` (coordinatewise `|(x − w)_j| ≤ (ℓd)/2`), from the small-box
support containment. -/
lemma chiSmallB_x_support_subset_cube {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : ℝ³) :
    {x : ℝ³ | chiSmallB M ℓ d u x ≠ 0}
      ⊆ {x : ℝ³ | ∀ j : Fin 3, |((x - (ℓ * d) • u).ofLp j)| ≤ (ℓ * d) / 2} := by
  intro x hx
  have hx' : chiSmallB M ℓ d u x ≠ 0 := by simpa using hx
  intro j
  exact chiSmallB_support_small_box_dist hM hℓ hd hx' j

/-- **x-support volume**: for every `u`, the measure of `{x | χ_{B(u)}(x) ≠ 0}`
is at most `(ℓd)³` (the cutoff's support is inside the small `(ℓd)`-cube). -/
lemma chiSmallB_x_support_measure_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : ℝ³) :
    (volume : Measure ℝ³) {x : ℝ³ | chiSmallB M ℓ d u x ≠ 0} ≤ ENNReal.ofReal ((ℓ * d) ^ 3) := by
  have hsub := chiSmallB_x_support_subset_cube hM hℓ hd u
  have hc : 0 ≤ (ℓ * d) / 2 := div_nonneg (mul_nonneg (le_of_lt hℓ) (le_of_lt hd)) (by norm_num)
  have hcube := eucl_cube_translate_volume (c := (ℓ * d) / 2) hc ((ℓ * d) • u)
  have hmono : (volume : Measure ℝ³) {x : ℝ³ | chiSmallB M ℓ d u x ≠ 0}
        ≤ (volume : Measure ℝ³) {x : ℝ³ | ∀ j : Fin 3, |((x - (ℓ * d) • u).ofLp j)| ≤ (ℓ * d) / 2} :=
      measure_mono (μ := (volume : Measure ℝ³)) hsub
  rw [hcube] at hmono
  rwa [show (2 * ((ℓ * d) / 2)) ^ 3 = (ℓ * d) ^ 3 by ring] at hmono


-- ============ step (i): the per-u real integral bound ============

/-- `x ↦ χ_{B(u)}(x)` is continuous (both factors: `χ_M` continuous, composed
with the affine `x ↦ c⁻¹•x − u` maps). -/
lemma chiSmallB_continuous {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : ℝ³) : Continuous (fun x : ℝ³ => chiSmallB M ℓ d u x) := by
  have hlin1 : Continuous (fun x : ℝ³ => ℓ⁻¹ • x) := by fun_prop
  have hlin2 : Continuous (fun x : ℝ³ => (ℓ * d)⁻¹ • x - u) := by fun_prop
  have h1 : Continuous (fun x : ℝ³ => chiScale ℓ x) := by
    have hc : Continuous (fun x : ℝ³ => chi (ℓ⁻¹ • x)) := chi_continuous.comp hlin1
    simpa [chiScale] using hc
  have h2 : Continuous (fun x : ℝ³ => chiSmall M ((ℓ * d)⁻¹ • x - u)) := (chiSmall_continuous hM).comp hlin2
  have hgoal : (fun x : ℝ³ => chiSmallB M ℓ d u x)
      = fun x : ℝ³ => chiScale ℓ x * chiSmall M ((ℓ * d)⁻¹ • x - u) := rfl
  rw [hgoal]
  exact h1.mul h2

/-- `x ↦ χ_{B(u)}(x)` has compact support (contained in the big-box cube,
which lies in a closed ball). -/
lemma chiSmallB_hasCompactSupport {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (u : ℝ³) : HasCompactSupport (fun x : ℝ³ => chiSmallB M ℓ d u x) := by
  change IsCompact (tsupport (fun x : ℝ³ => chiSmallB M ℓ d u x))
  change IsCompact (closure (Function.support (fun x : ℝ³ => chiSmallB M ℓ d u x)))
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ³) (Real.sqrt 3 * (ℓ / 2)))
    isClosed_closure ?_
  calc
    closure (Function.support (fun x : ℝ³ => chiSmallB M ℓ d u x))
        ⊆ closure (closedBall (0 : ℝ³) (Real.sqrt 3 * (ℓ / 2))) := by
          apply closure_mono
          intro x hx
          have hx' : chiSmallB M ℓ d u x ≠ 0 := Function.mem_support.mp hx
          have hcube : ∀ j : Fin 3, |x.ofLp j| ≤ ℓ / 2 := chiSmallB_support_big_box hM hℓ hx'
          have hball_mem : x ∈ {w : ℝ³ | ‖w‖ ≤ Real.sqrt 3 * (ℓ / 2)} :=
            (coord_box_subset_eucl_ball (A := ℓ / 2) (by positivity : 0 ≤ ℓ / 2)) (by
              change ∀ j : Fin 3, |x.ofLp j| ≤ ℓ / 2
              exact hcube)
          have hball : ‖x‖ ≤ Real.sqrt 3 * (ℓ / 2) := by simpa using hball_mem
          simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg] using hball
    _ = closedBall (0 : ℝ³) (Real.sqrt 3 * (ℓ / 2)) := closure_closedBall


/-- **Step (i) of the (g2) assembly — the per-`u` real integral bound**: for
`u` on the coordinatewise bad band,

    ∫ x : ℝ³, χ_{B(u)}(x)² ≤ (chiSmallDecay M)⁴ · (2μ^{-1/3}/ℓ)^{2M} · (ℓd)³ .

Proof: pointwise bound `f ≤ C'` everywhere (sup decay where `χ ≠ 0`, trivial
elsewhere); `∫ f = ∫_{support f} f` (`setIntegral_support`);
`setIntegral_mono` gives `∫_s f ≤ ∫_s C'`; `∫_s C' = C'·(vol s).toReal`
(`setIntegral_const`); `vol s ≤ (ℓd)³` (`chiSmallB_x_support_measure_le`).
No Fubini is needed. -/
lemma chiSmallB_x_integral_sq_le {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hμ : 0 < μ) {u : ℝ³} (hu : u ∈ chiSmallBadBand ℓ d μ) :
    (∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2)
      ≤ chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) * (ℓ * d) ^ 3 := by
  let f : ℝ³ → ℝ := fun x => (chiSmallB M ℓ d u x) ^ 2
  let s : Set ℝ³ := {x : ℝ³ | chiSmallB M ℓ d u x ≠ 0}
  let C' : ℝ := chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M)
  have hδ0 : 0 ≤ 2 * μ ^ (-1 / 3 : ℝ) / ℓ := by
    exact div_nonneg (mul_nonneg (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hμ _))) (le_of_lt hℓ)
  have hC'0 : 0 ≤ C' := by
    dsimp [C']
    exact mul_nonneg (chiSmallBandDecay_nonneg M hd) (pow_nonneg hδ0 (2 * M))
  have hsq : Function.support f = s := by
    ext x
    change (chiSmallB M ℓ d u x) ^ 2 ≠ 0 ↔ chiSmallB M ℓ d u x ≠ 0
    constructor
    · intro h hb
      exact h (by simp [hb])
    · intro h
      exact pow_ne_zero 2 h
  -- pointwise bound f ≤ C' everywhere
  have hpt : ∀ x : ℝ³, f x ≤ C' := by
    intro x
    dsimp [f]
    by_cases hx : chiSmallB M ℓ d u x = 0
    · rw [hx]
      simpa using hC'0
    · have hdec := chiSmallB_badband_sup_decay hM hℓ hd hμ (u := u) (x := x) hu
      simpa [C'] using hdec
  have hcont : Continuous (fun x : ℝ³ => chiSmallB M ℓ d u x) := chiSmallB_continuous hM hℓ hd u
  have hcs : HasCompactSupport (fun x : ℝ³ => chiSmallB M ℓ d u x) := chiSmallB_hasCompactSupport hM hℓ u
  have hf_cont : Continuous f := by
    change Continuous (fun x : ℝ³ => (chiSmallB M ℓ d u x) ^ 2)
    fun_prop
  have hcs_sq : HasCompactSupport f := by
    have hmon : Function.support f ⊆ Function.support (fun x : ℝ³ => chiSmallB M ℓ d u x) := by
      intro x hx
      change chiSmallB M ℓ d u x ≠ 0
      intro hb
      exact hx (by simp [f, hb])
    exact HasCompactSupport.mono hcs hmon
  have hf_int : Integrable f (volume : Measure ℝ³) :=
    hf_cont.integrable_of_hasCompactSupport hcs_sq
  have hs_fin : (volume : Measure ℝ³) s ≠ (∞ : ℝ≥0∞) := by
    have hle : (volume : Measure ℝ³) {x : ℝ³ | chiSmallB M ℓ d u x ≠ 0} ≤ ENNReal.ofReal ((ℓ * d) ^ 3) :=
      chiSmallB_x_support_measure_le hM hℓ hd u
    have hs : (volume : Measure ℝ³) s ≤ ENNReal.ofReal ((ℓ * d) ^ 3) := by
      simpa [s] using hle
    exact ne_of_lt (lt_of_le_of_lt hs ENNReal.ofReal_lt_top)
  have hm : (∫ x in s, f x) ≤ (∫ x in s, (fun _ : ℝ³ => C') x) := by
    refine MeasureTheory.setIntegral_mono ?_ ?_ ?_
    · exact hf_int.integrableOn
    · exact MeasureTheory.integrableOn_const (μ := volume) (s := s) hs_fin
    · intro x
      exact hpt x
  have hconst : (∫ x in s, (fun _ : ℝ³ => C') x) = C' * (volume : Measure ℝ³).real s := by
    have hc := MeasureTheory.setIntegral_const (μ := volume) (s := s) (c := C')
    simpa [smul_eq_mul, mul_comm] using hc
  have hvol : (volume : Measure ℝ³).real s ≤ (ℓ * d) ^ 3 := by
    have hle : (volume : Measure ℝ³) {x : ℝ³ | chiSmallB M ℓ d u x ≠ 0} ≤ ENNReal.ofReal ((ℓ * d) ^ 3) :=
      chiSmallB_x_support_measure_le hM hℓ hd u
    have hs : (volume : Measure ℝ³) s ≤ ENNReal.ofReal ((ℓ * d) ^ 3) := by
      simpa [s] using hle
    have hnn : 0 ≤ (ℓ * d) ^ 3 := pow_nonneg (mul_nonneg (le_of_lt hℓ) (le_of_lt hd)) 3
    have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
    have htr' : (volume : Measure ℝ³).real s ≤ (ℓ * d) ^ 3 := by
      rw [MeasureTheory.measureReal_def]
      simpa [ENNReal.toReal_ofReal hnn] using htr
    exact htr'
  calc
    (∫ x : ℝ³, f x) = ∫ x in Function.support f, f x := by
        exact (MeasureTheory.setIntegral_support (ν := (volume : Measure ℝ³)) (F := f)).symm
    _ = ∫ x in s, f x := by rw [hsq]
    _ ≤ ∫ x in s, (fun _ : ℝ³ => C') x := hm
    _ = C' * (volume : Measure ℝ³).real s := hconst
    _ ≤ C' * (ℓ * d) ^ 3 := mul_le_mul_of_nonneg_left hvol hC'0


-- ============ step (ii) infrastructure: the bad band as a measurable, finite set ============

/-- the coordinatewise bad band is measurable (finite union/intersection of
closed conditions in the continuous coordinate maps). -/
lemma chiSmallBadBand_measurable {ℓ d μ : ℝ} : MeasurableSet (chiSmallBadBand ℓ d μ) := by
  have hlower (j : Fin 3) :
      MeasurableSet {u : ℝ³ | (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤
        |((ℓ * d) • u).ofLp j|} := by
    have hcont : Continuous (fun u : ℝ³ => |((ℓ * d) • u).ofLp j|) := by
      fun_prop
    exact hcont.measurable measurableSet_Ici
  have hupper (j : Fin 3) :
      MeasurableSet {u : ℝ³ | |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d)} := by
    have hcont : Continuous (fun u : ℝ³ => |((ℓ * d) • u).ofLp j|) := by
      fun_prop
    exact hcont.measurable measurableSet_Iic
  dsimp [chiSmallBadBand]
  rw [Set.setOf_and]
  have hunion : MeasurableSet ({u : ℝ³ | ∃ j : Fin 3,
        (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤ |((ℓ * d) • u).ofLp j|}) := by
    rw [show {u : ℝ³ | ∃ j : Fin 3,
          (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤ |((ℓ * d) • u).ofLp j|}
        = ⋃ j : Fin 3, {u : ℝ³ | (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤
            |((ℓ * d) • u).ofLp j|} by ext u; simp]
    exact MeasurableSet.iUnion (fun j : Fin 3 => hlower j)
  have hinter : MeasurableSet {u : ℝ³ | ∀ j : Fin 3,
        |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d)} := by
    rw [show {u : ℝ³ | ∀ j : Fin 3,
          |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d)}
        = ⋂ j : Fin 3, {u : ℝ³ | |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d)} by
          ext u; simp]
    exact MeasurableSet.iInter (fun j : Fin 3 => hupper j)
  simpa using hunion.inter hinter
/-- the bad band is exactly the coordinate shell of `band_u_measure_le`
(`A := ½ℓ(1+d)`, `δ := 2μ^{-1/3}`), so its measure is bounded by the shell
volume. -/
lemma chiSmallBadBand_measure_le {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)) :
    (volume : Measure ℝ³) (chiSmallBadBand ℓ d μ)
      ≤ ENNReal.ofReal (((ℓ * d) ^ 3)⁻¹ *
          ((2 * ((1 / 2) * ℓ * (1 + d))) ^ 3 -
            (2 * (((1 / 2) * ℓ * (1 + d)) - 2 * μ ^ (-1 / 3 : ℝ))) ^ 3)) := by
  have hμδ : 0 ≤ 2 * μ ^ (-1 / 3 : ℝ) :=
    mul_nonneg (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hμ _))
  have hA : 0 ≤ (1 / 2) * ℓ * (1 + d) := by positivity
  have hset : chiSmallBadBand ℓ d μ = {u : ℝ³ |
      (∃ j : Fin 3, (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤ |((ℓ * d) • u).ofLp j|)
        ∧ (∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d))} := by
    rfl
  rw [hset]
  exact band_u_measure_le (ℓ := ℓ) (d := d) (A := (1 / 2) * ℓ * (1 + d))
    (δ := 2 * μ ^ (-1 / 3 : ℝ)) hℓ hd hA hμδ hAδ

/-- the bad band has finite `u`-measure (in the physically relevant regime
`2μ^{-1/3} ≤ ½ℓ(1+d)`). -/
lemma chiSmallBadBand_measure_lt_top {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)) :
    (volume : Measure ℝ³) (chiSmallBadBand ℓ d μ) < (∞ : ℝ≥0∞) := by
  exact lt_of_le_of_lt (chiSmallBadBand_measure_le hℓ hd hμ hAδ) ENNReal.ofReal_lt_top


-- ============ step (ii) atom: strong measurability / continuity of the partial integral ============

/-- the big-box cube `{|x_j| ≤ ℓ/2 ∀j}` is compact (closed subset of the
closed ball of radius `√3·ℓ/2`). -/
lemma bigBox_cube_compact {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsCompact {x : ℝ³ | ∀ j : Fin 3, |x.ofLp j| ≤ ℓ / 2} := by
  have hclosed : IsClosed {x : ℝ³ | ∀ j : Fin 3, |x.ofLp j| ≤ ℓ / 2} := by
    have hc (j : Fin 3) : IsClosed {x : ℝ³ | |x.ofLp j| ≤ ℓ / 2} := by
      have hset : {x : ℝ³ | |x.ofLp j| ≤ ℓ / 2}
          = {x : ℝ³ | -(ℓ / 2) ≤ x.ofLp j ∧ x.ofLp j ≤ ℓ / 2} := by
        ext x
        change |x.ofLp j| ≤ ℓ / 2 ↔ -(ℓ / 2) ≤ x.ofLp j ∧ x.ofLp j ≤ ℓ / 2
        rw [abs_le]
      rw [hset]
      have hlower : IsClosed {x : ℝ³ | -(ℓ / 2) ≤ x.ofLp j} := by
        rw [show {x : ℝ³ | -(ℓ / 2) ≤ x.ofLp j} =
            (fun x : ℝ³ => x.ofLp j) ⁻¹' Set.Ici (-(ℓ / 2)) by
          ext x
          simp]
        exact isClosed_Ici.preimage (coord_continuous j)
      have hupper : IsClosed {x : ℝ³ | x.ofLp j ≤ ℓ / 2} := by
        rw [show {x : ℝ³ | x.ofLp j ≤ ℓ / 2} =
            (fun x : ℝ³ => x.ofLp j) ⁻¹' Set.Iic (ℓ / 2) by
          ext x
          simp]
        exact isClosed_Iic.preimage (coord_continuous j)
      rw [show {x : ℝ³ | -(ℓ / 2) ≤ x.ofLp j ∧ x.ofLp j ≤ ℓ / 2}
          = {x : ℝ³ | -(ℓ / 2) ≤ x.ofLp j} ∩ {x : ℝ³ | x.ofLp j ≤ ℓ / 2} by
        ext x
        simp]
      exact hlower.inter hupper
    rw [show {x : ℝ³ | ∀ j : Fin 3, |x.ofLp j| ≤ ℓ / 2}
        = ⋂ j : Fin 3, {x : ℝ³ | |x.ofLp j| ≤ ℓ / 2} by
      ext x
      simp]
    exact isClosed_iInter (fun j : Fin 3 => hc j)
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ³) (Real.sqrt 3 * (ℓ / 2)))
    hclosed ?_
  calc
    {x : ℝ³ | ∀ j : Fin 3, |x.ofLp j| ≤ ℓ / 2}
        ⊆ {x : ℝ³ | ‖x‖ ≤ Real.sqrt 3 * (ℓ / 2)} :=
          coord_box_subset_eucl_ball (A := ℓ / 2) (by positivity)
    _ = closedBall (0 : ℝ³) (Real.sqrt 3 * (ℓ / 2)) := by
        ext x
        simp [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg]

/-- **The step-(ii) atom**: the partial-integral map
`u ↦ ∫_x χ_{B(u)}(x)² dx` is continuous.  Instantiation of Mathlib's
`continuous_parametric_integral_of_continuous` (Bochner/Set.lean): the
integrand `(u,x) ↦ χ_{B(u)}(x)²` is jointly continuous and the `x`-support
lies in the fixed compact big-box cube, so the parametric integral over that
cube is continuous; since the integrand vanishes outside the cube, the full
`∫_x` equals the cube-restricted integral. -/
lemma chiSmallB_partial_integral_continuous {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) :
    Continuous (fun u : ℝ³ => ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2) := by
  let K : Set ℝ³ := {x : ℝ³ | ∀ j : Fin 3, |x.ofLp j| ≤ ℓ / 2}
  have hKcompact : IsCompact K := by
    simpa [K] using (bigBox_cube_compact hℓ)
  have hKmeas : MeasurableSet K := by
    simpa [K] using (eucl_cube_measurable (c := ℓ / 2))
  have hjoint : Continuous (fun p : ℝ³ × ℝ³ => (chiSmallB M ℓ d p.1 p.2) ^ 2) := by
    have h1 : Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ p.2) := by
      have hc : Continuous (fun p : ℝ³ × ℝ³ => chi (ℓ⁻¹ • p.2)) :=
        chi_continuous.comp (by fun_prop)
      simpa [chiScale] using hc
    have h2 : Continuous (fun p : ℝ³ × ℝ³ => chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
      (chiSmall_continuous hM).comp (by fun_prop)
    have hgoal : (fun p : ℝ³ × ℝ³ => (chiSmallB M ℓ d p.1 p.2) ^ 2)
        = fun p : ℝ³ × ℝ³ => (chiScale ℓ p.2 * chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) ^ 2 := rfl
    rw [hgoal]
    exact (h1.mul h2).pow 2
  -- the parametric integral over the compact cube K is continuous (Mathlib)
  have hcontK : Continuous (fun u : ℝ³ => ∫ x in K, (chiSmallB M ℓ d u x) ^ 2) := by
    simpa [K] using (continuous_parametric_integral_of_continuous
      (X := ℝ³) (Y := ℝ³) (E := ℝ) (μ := (volume : Measure ℝ³))
      (f := fun (u : ℝ³) (x : ℝ³) => (chiSmallB M ℓ d u x) ^ 2) hjoint (s := K) hKcompact)
  -- full-space integral equals the K-integral (the integrand vanishes off K)
  have hfull : ∀ u : ℝ³, (∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2)
      = ∫ x in K, (chiSmallB M ℓ d u x) ^ 2 := by
    intro u
    let g : ℝ³ → ℝ := fun x => (chiSmallB M ℓ d u x) ^ 2
    have hg : ∀ x : ℝ³, g x = g x * (K.indicator (fun _ : ℝ³ => (1 : ℝ))) x := by
      intro x
      by_cases hx : x ∈ K
      · simp [g, hx]
      · have hz : chiSmallB M ℓ d u x = 0 := by
          by_contra hnz
          have hne : ∃ j : Fin 3, ¬ |x.ofLp j| ≤ ℓ / 2 := by
            simpa [K] using hx
          rcases hne with ⟨j, hj⟩
          have hle := chiSmallB_support_big_box hM hℓ hnz j
          linarith
        simp [g, hz, hx]
    have h2 : ∀ x : ℝ³, g x * (K.indicator (fun _ : ℝ³ => (1 : ℝ))) x = (K.indicator g) x := by
      intro x
      by_cases hx : x ∈ K
      · simp [g, hx]
      · simp [g, hx]
    calc
      (∫ x : ℝ³, g x) = ∫ x : ℝ³, g x * (K.indicator (fun _ : ℝ³ => (1 : ℝ))) x := by
          apply integral_congr_ae
          exact ae_of_all _ hg
      _ = ∫ x : ℝ³, (K.indicator g) x := by
          apply integral_congr_ae
          exact ae_of_all _ h2
      _ = ∫ x in K, g x := by
          rw [integral_indicator hKmeas]
  have hfun_eq : (fun u : ℝ³ => ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2)
      = fun u : ℝ³ => ∫ x in K, (chiSmallB M ℓ d u x) ^ 2 := by
    funext u
    exact hfull u
  rw [hfun_eq]
  exact hcontK


/-- **Strong measurability of the partial-integral map** (the step-(ii)
atom, in its literal form): `u ↦ ∫_x χ_{B(u)}(x)² dx` is `AEStronglyMeasurable`
— indeed continuous (`chiSmallB_partial_integral_continuous`). -/
lemma chiSmallB_partial_integral_aestronglyMeasurable {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) :
    AEStronglyMeasurable (fun u : ℝ³ => ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2)
      (volume : Measure ℝ³) :=
  (chiSmallB_partial_integral_continuous hM hℓ hd).aestronglyMeasurable


-- ============ step (ii): band-integrated (g2) bound ============

/-- `F : u ↦ ∫_x χ_{B(u)}²` is integrable over the bad band: it is strongly
measurable (continuous) and bounded by the constant `C'·(ℓd)³` on the band,
whose measure is finite. -/
lemma chiSmallB_partial_integral_integrableOn {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (hμ : 0 < μ) (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)) :
    IntegrableOn (fun u : ℝ³ => ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2)
      (chiSmallBadBand ℓ d μ) (volume : Measure ℝ³) := by
  let band : Set ℝ³ := chiSmallBadBand ℓ d μ
  let F : ℝ³ → ℝ := fun u => ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2
  let C'' : ℝ := chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) * (ℓ * d) ^ 3
  change Integrable F (volume.restrict band)
  have hcont : Continuous F := by
    dsimp [F]
    exact chiSmallB_partial_integral_continuous hM hℓ hd
  have hstrong : AEStronglyMeasurable F (volume.restrict band) := by
    exact hcont.aestronglyMeasurable.restrict
  have hC''0 : 0 ≤ C'' := by
    dsimp [C'']
    exact mul_nonneg (mul_nonneg (chiSmallBandDecay_nonneg M hd)
      (pow_nonneg (div_nonneg (mul_nonneg (by norm_num)
        (le_of_lt (Real.rpow_pos_of_pos hμ _))) (le_of_lt hℓ)) (2 * M)))
      (pow_nonneg (mul_nonneg (le_of_lt hℓ) (le_of_lt hd)) 3)
  have hpt : ∀ u : ℝ³, u ∈ band → |F u| ≤ C'' := by
    intro u hu
    have h1 := chiSmallB_x_integral_sq_le hM hℓ hd hμ hu
    have hF0 : 0 ≤ F u := by
      dsimp [F]
      exact integral_nonneg (by intro x; exact sq_nonneg (chiSmallB M ℓ d u x))
    have hFle : F u ≤ C'' := by
      dsimp [C'', F] at h1 ⊢
      exact h1
    calc
      |F u| = F u := abs_of_nonneg hF0
      _ ≤ C'' := hFle
  have hg : Integrable (fun _ : ℝ³ => C'') (volume.restrict band) := by
    have hfin : (volume : Measure ℝ³) band ≠ (∞ : ℝ≥0∞) := by
      have hlt := chiSmallBadBand_measure_lt_top hℓ hd hμ hAδ
      exact ne_of_lt (by simpa [band] using hlt)
    exact MeasureTheory.integrableOn_const (μ := volume) (s := band) hfin
  have hdom : ∀ᵐ u ∂(volume.restrict band), ‖F u‖ ≤ ‖(fun _ : ℝ³ => C'') u‖ := by
    rw [ae_restrict_iff' (chiSmallBadBand_measurable (ℓ := ℓ) (d := d) (μ := μ))]
    exact ae_of_all _ (by
      intro u hu
      have h := hpt u (by simpa [band] using hu)
      have hC'' : 0 ≤ C'' := hC''0
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC'']
      exact h)
  exact Integrable.mono hg hstrong hdom


/-- **Step (ii) of the (g2) assembly — the band-integrated bound**: for the
coordinatewise bad band `ℐ` (`A := ½ℓ(1+d)`, `δ := 2μ^{-1/3}`),

    ∫_{u ∈ ℐ} ∫_x χ_{B(u)}(x)² dx du
        ≤ (chiSmallDecay M)⁴ · (2μ^{-1/3}/ℓ)^{2M}
            · ( (2A)³ − (2(A−δ))³ ) ,

i.e. the per-`u` bound of step (i) (`≤ C'·(ℓd)³`) integrated over the band
(`vol ℐ ≤ ((ℓd)³)⁻¹·((2A)³−(2(A−δ))³)`, `band_u_measure_le`): the `(ℓd)³`
cancels. -/
lemma chiSmallB_badband_integral_le {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (hμ : 0 < μ) (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)) :
    (∫ u in chiSmallBadBand ℓ d μ,
        (∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2))
      ≤ chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) *
          ((2 * ((1 / 2) * ℓ * (1 + d))) ^ 3 -
            (2 * (((1 / 2) * ℓ * (1 + d)) - 2 * μ ^ (-1 / 3 : ℝ))) ^ 3) := by
  let band : Set ℝ³ := chiSmallBadBand ℓ d μ
  let F : ℝ³ → ℝ := fun u => ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2
  let C' : ℝ := chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M)
  let C'' : ℝ := C' * (ℓ * d) ^ 3
  let shell : ℝ := (2 * ((1 / 2) * ℓ * (1 + d))) ^ 3 -
      (2 * (((1 / 2) * ℓ * (1 + d)) - 2 * μ ^ (-1 / 3 : ℝ))) ^ 3
  have hμδ : 0 ≤ 2 * μ ^ (-1 / 3 : ℝ) :=
    mul_nonneg (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hμ _))
  have hC'0 : 0 ≤ C' := by
    dsimp [C']
    exact mul_nonneg (chiSmallBandDecay_nonneg M hd)
      (pow_nonneg (div_nonneg hμδ (le_of_lt hℓ)) (2 * M))
  have hC''0 : 0 ≤ C'' := by
    dsimp [C'']
    exact mul_nonneg hC'0 (pow_nonneg (mul_nonneg (le_of_lt hℓ) (le_of_lt hd)) 3)
  -- F ≤ C'' pointwise on the band (step (i))
  have hpt : ∀ u : ℝ³, u ∈ band → F u ≤ C'' := by
    intro u hu
    have h1 := chiSmallB_x_integral_sq_le hM hℓ hd hμ (by simpa [band] using hu)
    dsimp [C'', F] at h1 ⊢
    exact h1
  -- integrability of F and of the constant over the band
  have hF_on : IntegrableOn F band (volume : Measure ℝ³) := by
    dsimp [F, band]
    exact chiSmallB_partial_integral_integrableOn hM hℓ hd hμ hAδ
  have hconst_on : IntegrableOn (fun _ : ℝ³ => C'') band (volume : Measure ℝ³) := by
    have hfin : (volume : Measure ℝ³) band ≠ (∞ : ℝ≥0∞) := by
      have hlt := chiSmallBadBand_measure_lt_top hℓ hd hμ hAδ
      exact ne_of_lt (by simpa [band] using hlt)
    exact MeasureTheory.integrableOn_const (μ := volume) (s := band) hfin
  have hmeas : MeasurableSet band := by
    dsimp [band]
    exact chiSmallBadBand_measurable
  -- monotonicity over the band
  have hm : (∫ u in band, F u) ≤ (∫ u in band, (fun _ : ℝ³ => C'') u) := by
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ hmeas ?_
    · exact hF_on
    · exact hconst_on
    · intro u hu
      exact hpt u hu
  -- value of the constant restricted integral
  have hval : (∫ u in band, (fun _ : ℝ³ => C'') u) = C'' * (volume : Measure ℝ³).real band := by
    have hc := MeasureTheory.setIntegral_const (μ := volume) (s := band) (c := C'')
    simpa [smul_eq_mul, mul_comm] using hc
  -- measure of the band, toReal
  have hshell0 : 0 ≤ shell := by
    dsimp [shell]
    have hle : 2 * (((1 / 2) * ℓ * (1 + d)) - 2 * μ ^ (-1 / 3 : ℝ)) ≤ 2 * ((1 / 2) * ℓ * (1 + d)) := by
      nlinarith [hμδ]
    have hpos0 : 0 ≤ 2 * (((1 / 2) * ℓ * (1 + d)) - 2 * μ ^ (-1 / 3 : ℝ)) := by nlinarith [hAδ]
    have hpos1 : 0 ≤ 2 * ((1 / 2) * ℓ * (1 + d)) := by positivity
    have hp := pow_le_pow_left₀ hpos0 hle 3
    nlinarith
  have hvol : (volume : Measure ℝ³).real band ≤ ((ℓ * d) ^ 3)⁻¹ * shell := by
    have hle := chiSmallBadBand_measure_le hℓ hd hμ hAδ
    have hs : (volume : Measure ℝ³) band ≤ ENNReal.ofReal (((ℓ * d) ^ 3)⁻¹ * shell) := by
      simpa [band, shell] using hle
    have hnn : 0 ≤ ((ℓ * d) ^ 3)⁻¹ * shell :=
      mul_nonneg (inv_nonneg.mpr (pow_nonneg (mul_nonneg (le_of_lt hℓ) (le_of_lt hd)) 3)) hshell0
    have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
    have htr' : (volume : Measure ℝ³).real band ≤ ((ℓ * d) ^ 3)⁻¹ * shell := by
      rw [MeasureTheory.measureReal_def]
      simpa [ENNReal.toReal_ofReal hnn] using htr
    exact htr'
  -- cancellation of (ℓd)³
  have hcancel : C'' * (((ℓ * d) ^ 3)⁻¹ * shell) = C' * shell := by
    have hne : (ℓ * d) ^ 3 ≠ 0 := pow_ne_zero 3 (mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hd))
    dsimp [C'']
    calc
      C' * (ℓ * d) ^ 3 * (((ℓ * d) ^ 3)⁻¹ * shell) = C' * (((ℓ * d) ^ 3) * ((ℓ * d) ^ 3)⁻¹) * shell := by ring
      _ = C' * 1 * shell := by rw [mul_inv_cancel₀ hne]
      _ = C' * shell := by ring
  calc
    (∫ u in band, F u) ≤ ∫ u in band, (fun _ : ℝ³ => C'') u := hm
    _ = C'' * (volume : Measure ℝ³).real band := hval
    _ ≤ C'' * (((ℓ * d) ^ 3)⁻¹ * shell) := mul_le_mul_of_nonneg_left hvol hC''0
    _ = C' * shell := hcancel


-- ============ parameter-law restatement (FS eq:Iintegral form) ============

/-- the bad-band shell volume in the band's own coordinates is bounded by the
slab estimate: with `A := ½ℓ(1+d)` and `δ := 2μ^{-1/3}` (`0 ≤ δ ≤ A`),

    (2A)³ − (2(A−δ))³ ≤ 12 · μ^{-1/3} · ℓ² · (1+d)² . -/
lemma chiSmallB_badband_shell_bound {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)) :
    (2 * ((1 / 2) * ℓ * (1 + d))) ^ 3 -
        (2 * (((1 / 2) * ℓ * (1 + d)) - 2 * μ ^ (-1 / 3 : ℝ))) ^ 3
      ≤ 12 * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2 * (1 + d) ^ 2 := by
  let A : ℝ := (1 / 2) * ℓ * (1 + d)
  let δ : ℝ := 2 * μ ^ (-1 / 3 : ℝ)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hδ0 : 0 ≤ δ := by dsimp [δ]; exact mul_nonneg (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hμ _))
  have hδA : δ ≤ A := by
    have h0 : 0 ≤ A - δ := by simpa [A, δ] using hAδ
    linarith
  have hAmδ0 : 0 ≤ A - δ := by linarith
  have hAmδ_le_A : A - δ ≤ A := by linarith
  have hfac : (2 * A) ^ 3 - (2 * (A - δ)) ^ 3 = 8 * (A ^ 3 - (A - δ) ^ 3) := by
    ring
  have hδ3 : A ^ 3 - (A - δ) ^ 3 = δ * (A ^ 2 + A * (A - δ) + (A - δ) ^ 2) := by
    ring
  have hterms : A ^ 2 + A * (A - δ) + (A - δ) ^ 2 ≤ 3 * A ^ 2 := by
    have h1 : A * (A - δ) ≤ A * A := mul_le_mul_of_nonneg_left hAmδ_le_A hA0
    have h2 : (A - δ) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hAmδ0 hAmδ_le_A 2
    nlinarith
  have hmain : (2 * A) ^ 3 - (2 * (A - δ)) ^ 3 ≤ 24 * δ * A ^ 2 := by
    calc
      (2 * A) ^ 3 - (2 * (A - δ)) ^ 3 = 8 * (A ^ 3 - (A - δ) ^ 3) := hfac
      _ = 8 * (δ * (A ^ 2 + A * (A - δ) + (A - δ) ^ 2)) := by rw [hδ3]
      _ ≤ 8 * (δ * (3 * A ^ 2)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hterms hδ0) (by norm_num)
      _ = 24 * δ * A ^ 2 := by ring
  have hA2 : A ^ 2 = ℓ ^ 2 * (1 + d) ^ 2 / 4 := by
    dsimp [A]
    rw [mul_pow, mul_pow]
    ring
  calc
    (2 * ((1 / 2) * ℓ * (1 + d))) ^ 3 -
        (2 * (((1 / 2) * ℓ * (1 + d)) - 2 * μ ^ (-1 / 3 : ℝ))) ^ 3
        = (2 * A) ^ 3 - (2 * (A - δ)) ^ 3 := by rfl
    _ ≤ 24 * δ * A ^ 2 := hmain
    _ = 24 * (2 * μ ^ (-1 / 3 : ℝ)) * A ^ 2 := by dsimp [δ]
    _ = 48 * μ ^ (-1 / 3 : ℝ) * (ℓ ^ 2 * (1 + d) ^ 2 / 4) := by
        rw [hA2]
        ring
    _ = 12 * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2 * (1 + d) ^ 2 := by ring


/-- **Parameter-law restatement (FS eq:Iintegral shape)**: in the dilute
regime — encoded by the law

    (2μ^{-1/3}/ℓ)^{2M} · μ^{-1/3} · ℓ² ≤ C₁ · (μa³)^{M/3} · ℓ³

(the `μ^{-1/3} ≤ C·ℓ·(μa³)^{1/6}`-type relation raised to the needed powers,
to be derived from the concrete parameter choices at the assembly layer) —
the band-integrated (g2) bound takes the eq:Iintegral form

    ∫_{u∈ℐ} ∫_x χ²_{B(u)} ≤ 12(1+d)²·(chiSmallDecay M)⁴·C₁·(μa³)^{M/3}·ℓ³

(the `12(1+d)²·(chiSmallDecay M)⁴·C₁` is folded into the universal constant
`C(M)` at the concrete parameter stage). -/
lemma chiSmallB_badband_integral_law {M : ℕ} (hM : 1 ≤ M) {ℓ d μ a C₁ : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (hμ : 0 < μ) (ha : 0 ≤ a)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ))
    (hC₁ : 0 ≤ C₁)
    (hEst : (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2
        ≤ C₁ * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3) :
    (∫ u in chiSmallBadBand ℓ d μ,
        (∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2))
      ≤ 12 * (1 + d) ^ 2 * chiSmallBandDecay M d * C₁
          * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3 := by
  have hD0 : 0 ≤ chiSmallBandDecay M d := chiSmallBandDecay_nonneg M hd
  have hμp : 0 ≤ μ ^ (-1 / 3 : ℝ) := le_of_lt (Real.rpow_pos_of_pos hμ _)
  have hbase0 : 0 ≤ 2 * μ ^ (-1 / 3 : ℝ) / ℓ :=
    div_nonneg (mul_nonneg (by norm_num) hμp) (le_of_lt hℓ)
  have hpow0 : 0 ≤ (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) := pow_nonneg hbase0 (2 * M)
  have hA0 : 0 ≤ chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) :=
    mul_nonneg hD0 hpow0
  have hmain := chiSmallB_badband_integral_le hM hℓ hd hμ hAδ
  have hshell := chiSmallB_badband_shell_bound hℓ hd hμ hAδ
  have h12 : 0 ≤ 12 * (1 + d) ^ 2 * chiSmallBandDecay M d :=
    mul_nonneg (by positivity) hD0
  calc
    (∫ u in chiSmallBadBand ℓ d μ,
        (∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2))
        ≤ chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) *
            ((2 * ((1 / 2) * ℓ * (1 + d))) ^ 3 -
              (2 * (((1 / 2) * ℓ * (1 + d)) - 2 * μ ^ (-1 / 3 : ℝ))) ^ 3) := hmain
    _ ≤ chiSmallBandDecay M d * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) *
          (12 * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2 * (1 + d) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hshell hA0
    _ = 12 * (1 + d) ^ 2 * chiSmallBandDecay M d *
          ((2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2) := by ring
    _ ≤ 12 * (1 + d) ^ 2 * chiSmallBandDecay M d *
          (C₁ * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3) := by
        exact mul_le_mul_of_nonneg_left hEst h12
    _ = 12 * (1 + d) ^ 2 * chiSmallBandDecay M d * C₁
          * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3 := by ring


-- ============ sliding-sum normalisation: u-partition and (g3) for chiSmallB ============

/-- per-`x` partition of unity for the two-factor cutoff (the (g1)-analogue
for the cosine-M bump): `∫_u χ_{B(u)}(x)² du = (χ(x/ℓ))²`. -/
lemma chiSmallB_partition_u {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (x : ℝ³) :
    (∫ u : ℝ³, (chiSmallB M ℓ d u x) ^ 2) = (chiScale ℓ x) ^ 2 := by
  let a : ℝ³ := (ℓ * d)⁻¹ • x
  have hfact : (∫ u : ℝ³, (chiScale ℓ x * chiSmall M (a - u)) ^ 2)
      = (chiScale ℓ x) ^ 2 * (∫ u : ℝ³, (chiSmall M (a - u)) ^ 2) := by
    have hpt : (fun u : ℝ³ => (chiScale ℓ x * chiSmall M (a - u)) ^ 2)
        = fun u : ℝ³ => (chiScale ℓ x) ^ 2 * (chiSmall M (a - u)) ^ 2 := by
      funext u
      ring
    rw [hpt]
    simpa using (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ³))
      (r := (chiScale ℓ x) ^ 2) (f := fun u : ℝ³ => (chiSmall M (a - u)) ^ 2))
  have hinner : (∫ u : ℝ³, (chiSmall M (a - u)) ^ 2) = 1 := by
    have hpt : (fun u : ℝ³ => (chiSmall M (a - u)) ^ 2) = fun u : ℝ³ => (chiSmall M (u - a)) ^ 2 := by
      funext u
      have h : a - u = -(u - a) := by abel
      rw [h, chiSmall_even hM (u - a)]
    rw [hpt]
    have htr : MeasurePreserving (fun u : ℝ³ => u - a) volume volume := by
      have hmp := MeasureTheory.measurePreserving_add_left (volume : Measure ℝ³) (-a)
      have heq : (fun u : ℝ³ => u - a) = fun u : ℝ³ => -a + u := by
        funext u
        rw [sub_eq_add_neg, add_comm]
      simpa [heq] using hmp
    have himp : (∫ u : ℝ³, (chiSmall M (u - a)) ^ 2) = (∫ w : ℝ³, (chiSmall M w) ^ 2) := by
      have hφ : AEMeasurable (fun u : ℝ³ => u - a) volume := htr.aemeasurable
      have hfm : AEStronglyMeasurable (fun w : ℝ³ => (chiSmall M w) ^ 2)
          (Measure.map (fun u : ℝ³ => u - a) volume) := by
        have hc : Continuous (fun w : ℝ³ => (chiSmall M w) ^ 2) := by
          have hc' := chiSmall_continuous hM
          fun_prop
        exact hc.aestronglyMeasurable
      have hm := MeasureTheory.integral_map (μ := volume) hφ
        (f := fun w : ℝ³ => (chiSmall M w) ^ 2) hfm
      rw [htr.map_eq] at hm
      exact hm.symm
    calc
      (∫ u : ℝ³, (chiSmall M (u - a)) ^ 2) = (∫ w : ℝ³, (chiSmall M w) ^ 2) := himp
      _ = 1 := chiSmall_L2 hM
  calc
    (∫ u : ℝ³, (chiSmallB M ℓ d u x) ^ 2)
        = (∫ u : ℝ³, (chiScale ℓ x * chiSmall M (a - u)) ^ 2) := by
            simp [chiSmallB, a]
    _ = (chiScale ℓ x) ^ 2 * (∫ u : ℝ³, (chiSmall M (a - u)) ^ 2) := hfact
    _ = (chiScale ℓ x) ^ 2 := by rw [hinner]; ring

/-- the (g3)-analogue: `∬χ_{B(u)}² dx du = ℓ³`.  At the repointed cutoff the per-`x`
partition gives `∫_u χ_{B(u)}(x)² du = (χ(x/ℓ))²`, whose `x`-integral is `ℓ³·∫χ² = ℓ³`
(`chi_L2`), so the statement is unchanged. -/
lemma chiSmallB_double_integral_u_sq {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) :
    (∫ x : ℝ³, ∫ u : ℝ³, (chiSmallB M ℓ d u x) ^ 2) = ℓ ^ 3 := by
  calc
    (∫ x : ℝ³, ∫ u : ℝ³, (chiSmallB M ℓ d u x) ^ 2)
        = (∫ x : ℝ³, (chiScale ℓ x) ^ 2) := by
            apply integral_congr_ae
            exact ae_of_all _ (fun x => chiSmallB_partition_u hM hℓ hd x)
    _ = ℓ ^ 3 := by
        have hsc := integral_comp_smul_right (g := fun x : ℝ³ => (chi (ℓ⁻¹ • x)) ^ 2) hℓ
        have h1 : (∫ x : ℝ³, (chiScale ℓ x) ^ 2)
            = ∫ x : ℝ³, (chi (ℓ⁻¹ • x)) ^ 2 := rfl
        rw [h1]
        calc
          (∫ x : ℝ³, (chi (ℓ⁻¹ • x)) ^ 2)
              = ℓ ^ 3 * (∫ s : ℝ³, (chi (ℓ⁻¹ • (ℓ • s))) ^ 2) := hsc
          _ = ℓ ^ 3 * (∫ s : ℝ³, (chi s) ^ 2) := by
              congr 1
              apply integral_congr_ae
              exact ae_of_all _ (fun s => by
                have hs : ℓ⁻¹ • (ℓ • s) = s := by
                  rw [smul_smul]
                  change (ℓ⁻¹ * ℓ) • s = s
                  rw [inv_mul_cancel₀ (ne_of_gt hℓ), one_smul]
                simpa [hs])
          _ = ℓ ^ 3 * 1 := by rw [chi_L2]
          _ = ℓ ^ 3 := by ring




end BoseGases

end Submission
