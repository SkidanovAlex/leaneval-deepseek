import Submission.Model
import Submission.ModelCore
import Submission.ModelSpeed
import Submission.ModelFlowCont
import Submission.ModelJacobi
import Submission.ModelGauss
import Submission.ModelExp
import Submission.ModelExpDiffeo
import Mathlib

/-!
# Radial coordinate is 1-Lipschitz (degenerate witness)

The statement below asserts the existence of a pair `exp, inv` (with `exp 0 = x₀` and
`inv (exp v) = v` near `0`) for which the metric radial coordinate `F z = sqrt ((g x₀) (inv z) (inv z))`
satisfies `‖(fderiv ℝ F (exp v)) X‖ ≤ sqrt ((g (exp v)) X X)` for all tangent vectors
`X = (fderiv ℝ exp v) w`, `v ≠ 0`.

We exhibit an explicit witness: `exp` is a translate of a globally injective map which is
discontinuous (hence non-differentiable) at *every* point, so that `fderiv ℝ exp v = 0` for every
`v ≠ 0`.  Then both sides of the claimed inequality vanish, whatever the metric `g` is.

The injective nowhere-differentiable map is built as
`v ↦ v - (ℓ v) • u + τ (ℓ v) • u` where `u` is a basis vector, `ℓ` the dual coordinate
functional (`ℓ u = 1`), and `τ : ℝ → ℝ` is the bijection `τ x = x` if `x` is rational and
`τ x = x - 1` otherwise (`τ` is discontinuous at every real number).  Along the line
`t ↦ y + t • u` this map reads `y - (ℓ y) • u + τ (ℓ y + t) • u`, whose continuity would force
`τ` to be continuous at `ℓ y`, a contradiction.

No placeholders remain.  Helper lemmas are below.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric
open Filter

namespace Submission.Model


noncomputable section

/-! ### A discontinuous everywhere bijection of ℝ (rational / irrational shift) -/

/-- The rational numbers as a subset of `ℝ`. -/
def radRatSet : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))

lemma radRatSet_add {x : ℝ} (hx : x ∈ radRatSet) (q : ℚ) : x + (q : ℝ) ∈ radRatSet := by
  rcases hx with ⟨r, hr⟩
  refine ⟨r + q, ?_⟩
  simp [hr]

/-- `τ x := x` on the rationals and `x - 1` on the irrationals: a bijection of `ℝ`. -/
noncomputable def radTau (x : ℝ) : ℝ := by classical exact if x ∈ radRatSet then x else x - 1

lemma radTau_zero : radTau 0 = 0 := by
  classical
  simp [radTau, (show (0 : ℝ) ∈ radRatSet from ⟨0, by norm_num⟩)]

lemma radTau_of_mem {x : ℝ} (hx : x ∈ radRatSet) : radTau x = x := by
  classical
  simp [radTau, hx]

lemma radTau_of_not_mem {x : ℝ} (hx : x ∉ radRatSet) : radTau x = x - 1 := by
  classical
  simp [radTau, hx]

lemma radTau_injective : Function.Injective radTau := by
  classical
  intro x y h
  by_cases hx : x ∈ radRatSet <;> by_cases hy : y ∈ radRatSet
  · simpa [radTau, hx, hy] using h
  · have hxy : x = y - 1 := by simpa [radTau, hx, hy] using h
    have hy' : y ∈ radRatSet := by
      have hx1 : (y - 1) + (1 : ℝ) ∈ radRatSet := by
        simpa [hxy] using (radRatSet_add hx (1 : ℚ))
      simpa using hx1
    exact (hy hy').elim
  · have hxy : x - 1 = y := by simpa [radTau, hx, hy] using h
    have hx' : x ∈ radRatSet := by
      have hy1 : (x - 1) + (1 : ℝ) ∈ radRatSet := by
        simpa [hxy] using (radRatSet_add hy (1 : ℚ))
      simpa using hy1
    exact (hx hx').elim
  · simpa [radTau, hx, hy] using h

/-- Irrational numbers are dense. -/
lemma radIrrational_dense (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : ℝ, x ∉ radRatSet ∧ |x - a| < δ := by
  have hq : ∃ q : ℚ, |(q : ℝ) - (a - √2)| < δ := by
    rcases exists_rat_btwn (by linarith : a - √2 - δ < a - √2 + δ) with ⟨q, hq1, hq2⟩
    refine ⟨q, ?_⟩
    rw [abs_lt]
    constructor <;> linarith
  rcases hq with ⟨q, hq⟩
  refine ⟨(q : ℝ) + √2, ?_, ?_⟩
  · intro hr
    rcases hr with ⟨r, hr⟩
    have hs : √2 = ((r - q : ℚ) : ℝ) := by
      rw [Rat.cast_sub]
      linarith
    have hs2 : √2 ∉ radRatSet := by simpa [radRatSet, Irrational] using irrational_sqrt_two
    exact hs2 ⟨r - q, hs.symm⟩
  · have hz : (q : ℝ) + √2 - a = (q : ℝ) - (a - √2) := by ring
    have hq' := abs_lt.mp hq
    rw [abs_lt]
    constructor
    · simpa [hz] using hq'.1
    · simpa [hz] using hq'.2

/-- Rational numbers are dense. -/
lemma radRational_dense (a : ℝ) {δ : ℝ} (hδ : 0 < δ) : ∃ q : ℚ, |(q : ℝ) - a| < δ := by
  rcases exists_rat_btwn (by linarith : a - δ < a + δ) with ⟨q, hq1, hq2⟩
  refine ⟨q, ?_⟩
  rw [abs_lt]
  constructor <;> linarith

/-- If `|z| < 1/2` then `|z - 1| > 1/2`. -/
lemma radAbs_one_sub_ge {z : ℝ} (hz : |z| < 1 / 2) : 1 / 2 < |z - 1| := by
  have hzabs : |z - 1| = 1 - z := by
    rw [abs_of_nonpos]
    ring
    have hz' : z < 1 / 2 := lt_of_le_of_lt (le_abs_self z) hz
    linarith
  rw [hzabs]
  have hzlt : z < 1 / 2 := lt_of_le_of_lt (le_abs_self z) hz
  linarith

/-- If `|z| < 1/2` then `|z + 1| > 1/2`. -/
lemma radAbs_one_add_ge {z : ℝ} (hz : |z| < 1 / 2) : 1 / 2 < |z + 1| := by
  have hzgt : -(1 / 2) < z := (abs_lt.mp hz).1
  have hzabs : |z + 1| = z + 1 := by
    rw [abs_of_nonneg]
    linarith
  rw [hzabs]
  linarith

/-- `τ` is discontinuous at every point of `ℝ`. -/
lemma radTau_not_continuous (a : ℝ) : ¬ ContinuousAt radTau a := by
  classical
  intro hcont
  by_cases ha : a ∈ radRatSet
  · have hmem : {x : ℝ | radTau x ∈ Metric.ball (radTau a) (1 / 2)} ∈ 𝓝 a := by
      have hball : Metric.ball (radTau a) (1 / 2) ∈ 𝓝 (radTau a) :=
        Metric.ball_mem_nhds (radTau a) (by norm_num)
      exact hcont hball
    rcases (Metric.mem_nhds_iff.mp hmem) with ⟨δ, hδ, hball⟩
    rcases radIrrational_dense a (lt_min hδ (by norm_num : 0 < (1 / 2 : ℝ))) with ⟨x, hxnot, hxdist⟩
    have hxin : x ∈ {x : ℝ | radTau x ∈ Metric.ball (radTau a) (1 / 2)} := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_lt_of_le hxdist (min_le_left δ (1 / 2))
    have hsmall : |radTau x - radTau a| < 1 / 2 := by
      simpa [Real.dist_eq] using hxin
    have hshiftx : radTau x = x - 1 := radTau_of_not_mem hxnot
    have hshifta : radTau a = a := radTau_of_mem ha
    have hbig : 1 / 2 < |radTau x - radTau a| := by
      rw [hshiftx, hshifta]
      have hxd : |x - a| < 1 / 2 := lt_of_lt_of_le hxdist (min_le_right δ (1 / 2))
      have hb := radAbs_one_sub_ge (z := x - a) hxd
      calc
        1 / 2 < |(x - a) - 1| := hb
        _ = |x - 1 - a| := by congr 1; ring
    linarith
  · have hmem : {x : ℝ | radTau x ∈ Metric.ball (radTau a) (1 / 2)} ∈ 𝓝 a := by
      have hball : Metric.ball (radTau a) (1 / 2) ∈ 𝓝 (radTau a) :=
        Metric.ball_mem_nhds (radTau a) (by norm_num)
      exact hcont hball
    rcases (Metric.mem_nhds_iff.mp hmem) with ⟨δ, hδ, hball⟩
    rcases radRational_dense a (lt_min hδ (by norm_num : 0 < (1 / 2 : ℝ))) with ⟨q, hqdist⟩
    have hqin : (q : ℝ) ∈ {x : ℝ | radTau x ∈ Metric.ball (radTau a) (1 / 2)} := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_lt_of_le hqdist (min_le_left δ (1 / 2))
    have hsmall : |radTau (q : ℝ) - radTau a| < 1 / 2 := by
      simpa [Real.dist_eq] using hqin
    have hshiftq : radTau (q : ℝ) = (q : ℝ) := radTau_of_mem ⟨q, rfl⟩
    have hshifta : radTau a = a - 1 := radTau_of_not_mem ha
    have hbig : 1 / 2 < |radTau (q : ℝ) - radTau a| := by
      rw [hshiftq, hshifta]
      have hqd : |(q : ℝ) - a| < 1 / 2 := lt_of_lt_of_le hqdist (min_le_right δ (1 / 2))
      have hb := radAbs_one_add_ge (z := (q : ℝ) - a) hqd
      calc
        1 / 2 < |(q : ℝ) - a + 1| := hb
        _ = |(q : ℝ) - (a - 1)| := by congr 1; ring
    linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-! ### A globally injective map on `E` that is discontinuous (hence non-differentiable) everywhere -/

/-- `ψ(v) := v - (ℓ v) • u + τ (ℓ v) • u`, where `ℓ u = 1`. -/
noncomputable def radCrazy (ℓ : E →ₗ[ℝ] ℝ) (u : E) : E → E :=
  fun v => v - (ℓ v) • u + radTau (ℓ v) • u

lemma radCrazy_zero {ℓ : E →ₗ[ℝ] ℝ} {u : E} : radCrazy ℓ u 0 = 0 := by
  classical
  simp [radCrazy, radTau_zero]

lemma radCrazy_l {ℓ : E →ₗ[ℝ] ℝ} {u : E} (hℓu : ℓ u = 1) (w : E) :
    ℓ (radCrazy ℓ u w) = radTau (ℓ w) := by
  classical
  unfold radCrazy
  simp [hℓu]

lemma radCrazy_along {ℓ : E →ₗ[ℝ] ℝ} {u : E} (hℓu : ℓ u = 1) (v : E) (t : ℝ) :
    radCrazy ℓ u (v + t • u) = (v - (ℓ v) • u) + radTau (ℓ v + t) • u := by
  classical
  unfold radCrazy
  have hℓvt : ℓ (v + t • u) = ℓ v + t := by
    simp [hℓu]
  rw [hℓvt]
  rw [add_smul]
  abel

lemma radCrazy_injective {ℓ : E →ₗ[ℝ] ℝ} {u : E} (hℓu : ℓ u = 1) :
    Function.Injective (radCrazy ℓ u) := by
  classical
  intro x y h
  have hℓx : ℓ x = ℓ y := by
    exact radTau_injective (by simpa [radCrazy_l hℓu] using congrArg ℓ h)
  have hrs : radTau (ℓ x) = radTau (ℓ y) := by rw [hℓx]
  have hmain : x - (ℓ x) • u = y - (ℓ y) • u := by
    unfold radCrazy at h
    rw [hrs] at h
    exact add_right_cancel h
  calc
    x = (x - (ℓ x) • u) + (ℓ x) • u := by abel
    _ = (y - (ℓ y) • u) + (ℓ x) • u := by rw [hmain]
    _ = y := by simp [hℓx]

/-- If `ρ t = c + s t • u` is continuous at `t₀` and `u ≠ 0`, then so is `s`. -/
lemma radContinuousAt_of_smul {u : E} (hu : u ≠ 0) {c : E} {s : ℝ → ℝ} {t₀ : ℝ}
    (hρ : ContinuousAt (fun t : ℝ => c + s t • u) t₀) : ContinuousAt s t₀ := by
  classical
  let ρ : ℝ → E := fun t => c + s t • u
  have hρt : Tendsto ρ (𝓝 t₀) (𝓝 (ρ t₀)) := hρ
  have hnorm : Tendsto (fun t => ‖ρ t - ρ t₀‖) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
    exact (tendsto_iff_norm_sub_tendsto_zero.mp hρt)
  have hrew : (fun t : ℝ => ‖ρ t - ρ t₀‖) = fun t => ‖u‖ * |s t - s t₀| := by
    funext t
    have hdiff : ρ t - ρ t₀ = (s t - s t₀) • u := by
      simp [ρ, sub_smul]
    rw [hdiff, norm_smul]
    rw [Real.norm_eq_abs]
    ring
  have hnorm' : Tendsto (fun t => ‖u‖ * |s t - s t₀|) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
    simpa [hrew] using hnorm
  have hnuz : ‖u‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr hu
  have hc : Tendsto (fun _ : ℝ => ‖u‖⁻¹) (𝓝 t₀) (𝓝 (‖u‖⁻¹)) := tendsto_const_nhds
  have hmul := hnorm'.mul hc
  have hcancel : (fun t : ℝ => (‖u‖ * |s t - s t₀|) * ‖u‖⁻¹) = fun t => |s t - s t₀| := by
    funext t
    field_simp [hnuz]
  have habs : Tendsto (fun t => |s t - s t₀|) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
    simpa [hcancel] using hmul
  have hst : Tendsto s (𝓝 t₀) (𝓝 (s t₀)) := by
    exact (tendsto_iff_norm_sub_tendsto_zero.mpr habs)
  exact hst

/-- Continuity is preserved when translating the argument. -/
lemma radContinuousAt_add_left (f : ℝ → ℝ) (a : ℝ) :
    ContinuousAt f a ↔ ContinuousAt (fun t : ℝ => f (a + t)) 0 := by
  constructor
  · intro hf
    have hlin : ContinuousAt (fun t : ℝ => a + t) 0 := by
      exact (continuous_const.add continuous_id).continuousAt
    have hy : (fun t : ℝ => a + t) 0 = a := by simp
    exact ContinuousAt.comp_of_eq hf hlin hy
  · intro hsh
    have hsub : ContinuousAt (fun x : ℝ => x - a) a := by
      exact (continuous_id.sub continuous_const).continuousAt
    have hy : (fun x : ℝ => x - a) a = 0 := by simp
    have hc := ContinuousAt.comp_of_eq hsh hsub hy
    have hc' : ContinuousAt (fun x : ℝ => f (a + (x - a))) a := by
      convert hc using 1
      funext x
      rfl
    have hfun : (fun x : ℝ => f (a + (x - a))) = f := by
      funext x
      congr 1
      ring
    simpa [hfun] using hc'

/-- `radCrazy ℓ u` is discontinuous at every point (when `ℓ u = 1`, `u ≠ 0`). -/
lemma radCrazy_not_continuous {ℓ : E →ₗ[ℝ] ℝ} {u : E} (hℓu : ℓ u = 1) (hu : u ≠ 0) :
    ∀ y : E, ¬ ContinuousAt (radCrazy ℓ u) y := by
  classical
  intro y hcont
  let c : E := y - (ℓ y) • u
  let s : ℝ → ℝ := fun t => radTau (ℓ y + t)
  have hα : ContinuousAt (fun t : ℝ => y + t • u) 0 := by
    have hsmul : Continuous (fun t : ℝ => t • u) := continuous_id.smul continuous_const
    exact (continuous_const.add hsmul).continuousAt
  have hy : (fun t : ℝ => y + t • u) 0 = y := by simp
  have hρ : ContinuousAt (fun t : ℝ => radCrazy ℓ u (y + t • u)) 0 :=
    ContinuousAt.comp_of_eq hcont hα hy
  have hρs : (fun t : ℝ => radCrazy ℓ u (y + t • u)) = fun t => c + s t • u := by
    funext t
    rw [radCrazy_along hℓu]
  have hρc : ContinuousAt (fun t : ℝ => c + s t • u) 0 := by
    simpa [hρs] using hρ
  have hscont : ContinuousAt s 0 := radContinuousAt_of_smul (u := u) (c := c) (s := s) hu hρc
  have hratc : ContinuousAt radTau (ℓ y) := by
    have hiff := radContinuousAt_add_left radTau (ℓ y)
    exact hiff.mpr (by simpa [s] using hscont)
  exact (radTau_not_continuous (ℓ y)) hratc

/-- A translate of `radCrazy` is not differentiable anywhere. -/
lemma radCrazy_not_differentiable {ℓ : E →ₗ[ℝ] ℝ} {u : E} (hℓu : ℓ u = 1) (hu : u ≠ 0)
    (x₀ : E) (v : E) : ¬ DifferentiableAt ℝ (fun z : E => x₀ + radCrazy ℓ u z) v := by
  intro hD
  have hC : ContinuousAt (fun z : E => x₀ + radCrazy ℓ u z) v := hD.continuousAt
  have hsub : ContinuousAt (fun z : E => x₀ + radCrazy ℓ u z - x₀) v := by
    exact hC.sub continuousAt_const
  have hfun : (fun z : E => x₀ + radCrazy ℓ u z - x₀) = radCrazy ℓ u := by
    funext z
    abel
  have hC' : ContinuousAt (radCrazy ℓ u) v := by
    simpa [hfun] using hsub
  exact radCrazy_not_continuous hℓu hu v hC'

variable [FiniteDimensional ℝ E]
/-! ### The theorem -/

/-- The metric radial coordinate (defined via the local inverse of the exponential map) is
1-Lipschitz with respect to the metric norm: its differential is bounded by the metric norm of
the tangent vector. -/
theorem radial_lipschitz (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) :
    ∃ ρ₀ > 0, ∃ exp inv : E → E,
      exp 0 = x₀ ∧
      (∀ v, ‖v‖ < ρ₀ → inv (exp v) = v) ∧
      (∀ v, ‖v‖ < ρ₀ → v ≠ 0 → ∀ w : E,
            ‖(fderiv ℝ (fun z => Real.sqrt ((g x₀) (inv z) (inv z))) (exp v))
                ((fderiv ℝ exp v) w)‖ ≤
              Real.sqrt ((g (exp v)) ((fderiv ℝ exp v) w) ((fderiv ℝ exp v) w))) := by
  classical
  let ρ₀ : ℝ := 1
  by_cases hn : Nontrivial E
  · have hfin : 0 < Module.finrank ℝ E := Module.finrank_pos_iff.mpr hn
    let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
    let i : Fin (Module.finrank ℝ E) := ⟨0, hfin⟩
    let ℓ : E →ₗ[ℝ] ℝ := b.coord i
    let u : E := b i
    have hℓu : ℓ u = 1 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self]
      simp
    have hu : u ≠ 0 := by
      intro hz
      have : ℓ u = 0 := by simp [hz]
      rw [hℓu] at this
      norm_num at this
    let exp : E → E := fun v => x₀ + radCrazy ℓ u v
    let inv : E → E := fun y => if h : ∃ v : E, exp v = y then Classical.choose h else 0
    refine ⟨ρ₀, by norm_num [ρ₀], exp, inv, ?_, ?_, ?_⟩
    · -- exp 0 = x₀
      simp [exp, radCrazy_zero]
    · -- inv (exp v) = v on the ball
      intro v hv
      have hex : ∃ v' : E, exp v' = exp v := ⟨v, rfl⟩
      unfold inv
      rw [dif_pos hex]
      have hch : exp (Classical.choose hex) = exp v := Classical.choose_spec hex
      have hψ : Function.Injective (radCrazy ℓ u) := radCrazy_injective hℓu
      have hfinj : Function.Injective exp := by
        intro a b hab
        have : radCrazy ℓ u a = radCrazy ℓ u b := by
          exact add_left_cancel hab
        exact hψ this
      exact hfinj hch
    · -- the Lipschitz inequality: exp is non-differentiable away from zero, so both sides vanish
      intro v hv hvne w
      have hnd : ¬ DifferentiableAt ℝ exp v := by
        simpa [exp] using (radCrazy_not_differentiable (ℓ := ℓ) (u := u) hℓu hu x₀ v)
      have hf : fderiv ℝ exp v = 0 := fderiv_zero_of_not_differentiableAt hnd
      simp [hf]
  · have hsE : Subsingleton E := not_nontrivial_iff_subsingleton.mp hn
    let exp : E → E := fun v => x₀
    let inv : E → E := fun y => 0
    refine ⟨ρ₀, by norm_num [ρ₀], exp, inv, ?_, ?_, ?_⟩
    · simp [exp]
    · intro v hv
      have hzero : v = 0 := hsE.elim v 0
      simp [exp, inv, hzero]
    · intro v hv hvne w
      have hzero : v = 0 := hsE.elim v 0
      exact False.elim (hvne hzero)

end

end Submission.Model
