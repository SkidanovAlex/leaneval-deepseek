import Mathlib
import ChallengeDeps
import Submission.Work.Geometry
import Submission.Work.Collision
import Submission.Work.AngleTransfer
import Submission.Work.FinalReduction
import Submission.Commons.Measure.AddCircle.third_measure_of_neg_invariant
import Submission.Commons.Measure.RealEndgame.ennreal_of_measureReal_ge

open InscribedRectangles
open Manifold Real MeasureTheory
open scoped ContDiff ENNReal

set_option autoImplicit false
noncomputable section

namespace Submission.Configuration

open Submission.Collision
open Submission.Geometry

lemma toC_smul (c : ℝ) (p : ℝ × ℝ) :
    (⟨(c • p).1, (c • p).2⟩ : ℂ) = (c : ℂ) * ⟨p.1, p.2⟩ := by
  refine Complex.ext ?_ ?_ <;> simp [Complex.mul_re, Complex.mul_im]

/-- The doubled direction is invariant under positive scaling of a vector. -/
lemma dirC_smul_pos {c : ℝ} (hc : 0 < c) (p : ℝ × ℝ) : dirC (c • p) = dirC p := by
  unfold dirC
  rw [toC_smul]
  by_cases hp : (⟨p.1, p.2⟩ : ℂ) = 0
  · rw [hp, mul_zero, Complex.arg_zero, zero_div]
  · have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc
    rw [Complex.arg_mul hc0 hp (by
        rw [Complex.arg_ofReal_of_nonneg hc.le, zero_add]
        exact Complex.arg_mem_Ioc _),
      Complex.arg_ofReal_of_nonneg hc.le, zero_add]

/-- The ordered configuration map of a curve: `(x, y) ↦ (midpoint, doubled direction, length)`. -/
def muOrd (γ : Circle → ℝ × ℝ) (p : Circle × Circle) : (ℝ × ℝ) × UnitAddCircle × ℝ :=
  ((γ p.1 + γ p.2) / 2, dirC (γ p.1 - γ p.2), eucNorm (γ p.1 - γ p.2))

/-- The rotation action by `u ∈ ℝ/ℤ` on the circle-coordinate of a configuration. -/
def actC (u : UnitAddCircle) (q : (ℝ × ℝ) × UnitAddCircle × ℝ) :
    (ℝ × ℝ) × UnitAddCircle × ℝ := (q.1, q.2.1 + u, q.2.2)

/-- The set of angles `u` for which the configuration Möbius strip of `γ` meets its rotation by
`u`: there are two *distinct interior* chords of `γ` with the same midpoint and the same length
whose doubled directions differ by `u`. -/
def GoodC (γ : Circle → ℝ × ℝ) : Set UnitAddCircle :=
  {u | ∃ x y x' y' : Circle, x ≠ y ∧ x' ≠ y' ∧
      muOrd γ (x, y) = actC u (muOrd γ (x', y'))}

lemma actC_add (u v : UnitAddCircle) (q : (ℝ × ℝ) × UnitAddCircle × ℝ) :
    actC u (actC v q) = actC (v + u) q := by
  unfold actC
  exact Prod.ext rfl (Prod.ext (by rw [add_assoc]) rfl)

/-- `GoodC γ` is invariant under inversion in the circle group. -/
theorem GoodC_neg (γ : Circle → ℝ × ℝ) : GoodC γ = -GoodC γ := by
  ext u
  constructor
  · rintro ⟨x, y, x', y', hxy, hx'y', h⟩
    rw [Set.mem_neg]
    exact ⟨x', y', x, y, hx'y', hxy, by rw [h]; simp [actC]⟩
  · intro hu
    rw [Set.mem_neg] at hu
    obtain ⟨x, y, x', y', hxy, hx'y', h⟩ := hu
    exact ⟨x', y', x, y, hx'y', hxy, by rw [h]; simp [actC]⟩

lemma eucNorm_smul (c : ℝ) (p : ℝ × ℝ) : eucNorm (c • p) = |c| * eucNorm p := by
  unfold eucNorm eucDot
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [show c * p.1 * (c * p.1) + c * p.2 * (c * p.2) = c ^ 2 * (p.1 * p.1 + p.2 * p.2) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma anglePoint_eq (θ : ℝ) : AngleTransfer.anglePoint θ =
    ((θ / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
  rw [AngleTransfer.anglePoint, one_div_mul_eq_div]

/-- If `anglePoint θ ∈ GoodC γ` with `θ ∈ (0, π]`, then `γ` has an inscribed rectangle of aspect
ratio `tan (θ/4)`. -/
theorem member_of_X_of_mem_GoodC {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    {θ : ℝ} (hθpos : 0 < θ) (hθπ : θ ≤ Real.pi) (h : AngleTransfer.anglePoint θ ∈ GoodC γ) :
    θ / π ∈ X γ := by
  obtain ⟨x, y, x', y', hxy, hx'y', heq⟩ := h
  have hinj : Function.Injective γ := hγ.isEmbedding.injective
  have hmid : (γ x + γ y) / 2 = (γ x' + γ y') / 2 := by
    have := congrArg (fun q : (ℝ × ℝ) × UnitAddCircle × ℝ => q.1) heq
    simpa [muOrd, actC] using this
  have hdir : dirC (γ x - γ y) = dirC (γ x' - γ y') + AngleTransfer.anglePoint θ := by
    have := congrArg (fun q : (ℝ × ℝ) × UnitAddCircle × ℝ => q.2.1) heq
    simpa [muOrd, actC, AngleTransfer.anglePoint] using this
  have hlen : eucNorm (γ x - γ y) = eucNorm (γ x' - γ y') := by
    have := congrArg (fun q : (ℝ × ℝ) × UnitAddCircle × ℝ => q.2.2) heq
    simpa [muOrd, actC] using this
  have hne : γ x - γ y ≠ 0 := by
    intro h0
    have : γ x = γ y := by
      have := sub_eq_zero.mp h0
      exact this
    exact hxy (hinj this)
  have hne' : γ x' - γ y' ≠ 0 := by
    intro h0
    have : γ x' = γ y' := sub_eq_zero.mp h0
    exact hx'y' (hinj this)
  set v : ℝ × ℝ := (1 / 2 : ℝ) • (γ x - γ y) with hv
  set w : ℝ × ℝ := (1 / 2 : ℝ) • (γ x' - γ y') with hw
  set m : ℝ × ℝ := (γ x + γ y) / 2 with hm
  have hc : 0 < eucNorm v := by
    rw [hv, eucNorm_smul]
    have : 0 < eucNorm (γ x - γ y) := eucNorm_pos hne
    positivity
  have hvw : eucNorm v = eucNorm w := by
    rw [hv, hw, eucNorm_smul, eucNorm_smul, hlen]
  have hdir' : dirC v = dirC w + ((θ / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
    rw [hv, hw, dirC_smul_pos (by norm_num : (0:ℝ) < 1/2),
      dirC_smul_pos (by norm_num : (0:ℝ) < 1/2), hdir, anglePoint_eq]
  have hmv : m + v ∈ Set.range γ := by
    refine ⟨x, ?_⟩
    rw [hm, hv]
    ext <;> simp <;> ring
  have hmv' : m - v ∈ Set.range γ := by
    refine ⟨y, ?_⟩
    rw [hm, hv]
    ext <;> simp <;> ring
  have hmw : m + w ∈ Set.range γ := by
    refine ⟨x', ?_⟩
    rw [hw, hmid]
    ext <;> simp <;> ring
  have hmw' : m - w ∈ Set.range γ := by
    refine ⟨y', ?_⟩
    rw [hw, hmid]
    ext <;> simp <;> ring
  exact member_of_X_of_collision hc hθpos hθπ hvw.symm rfl hdir' hmw hmw' hmv hmv'

/-- **Theorem 1 reduces to the measure bound for the configuration set.** If the set `GoodC γ` of
angles at which the configuration Möbius strip of `γ` meets its rotation is measurable and has
normalised Haar measure at least `1/3`, then at least `1/3` of all aspect ratios occur. -/
theorem theorem_1_of_GoodC {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (hmeas : MeasurableSet (GoodC γ)) (h : (1 / 3 : ℝ) ≤ volume.real (GoodC γ)) :
    volume (X γ) ≥ 1 / 3 := by
  set S : Set ℝ := {r : ℝ | 0 < r ∧ r ≤ 1 ∧ AngleTransfer.anglePoint (Real.pi * r) ∈ GoodC γ}
  set T : Set ℝ := {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ AngleTransfer.anglePoint (Real.pi * r) ∈ GoodC γ}
  have hthird : (1 / 3 : ℝ) ≤ volume.real T :=
    Commons.Measure.AddCircle.third_measure_of_neg_invariant hmeas (GoodC_neg γ) h
  have hTfin : volume T ≠ (⊤ : ℝ≥0∞) := by
    refine measure_ne_top_of_subset (s := Set.Icc 0 1) (t := T) (fun r hr => ⟨hr.1, hr.2.1⟩) ?_
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hSfin : volume S ≠ (⊤ : ℝ≥0∞) := by
    refine measure_ne_top_of_subset (s := Set.Icc 0 1) (t := S) (fun r hr => ⟨hr.1.le, hr.2.1⟩) ?_
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hEq : volume.real S = volume.real T := by
    refine le_antisymm (measureReal_mono (fun r hr => ⟨hr.1.le, hr.2⟩) hTfin) ?_
    have hsub : T ⊆ S ∪ ({0} : Set ℝ) := by
      intro r hr
      rw [Set.mem_union]
      by_cases h0 : r = 0
      · exact Or.inr h0
      · exact Or.inl ⟨lt_of_le_of_ne hr.1 (Ne.symm h0), hr.2⟩
    have h1 : volume.real T ≤ volume.real (S ∪ ({0} : Set ℝ)) :=
      measureReal_mono hsub (measure_ne_top_of_subset (s := Set.Icc 0 1)
        (t := S ∪ ({0} : Set ℝ)) (by
          intro r hr
          rcases hr with hr | hr
          · exact ⟨hr.1.le, hr.2.1⟩
          · rw [Set.mem_singleton_iff] at hr; subst hr; exact ⟨le_refl 0, by norm_num⟩)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    have h2 := measureReal_union_le (μ := (volume : Measure ℝ)) S ({0} : Set ℝ)
    have h3 : volume.real ({0} : Set ℝ) = 0 := by rw [measureReal_def]; simp
    linarith
  have hthird' : (1 / 3 : ℝ) ≤ volume.real S := by rw [hEq]; exact hthird
  have hinc : S ⊆ X γ := by
    intro r hr
    obtain ⟨hrpos, hr1, hrg⟩ := hr
    have hθpos : 0 < Real.pi * r := mul_pos Real.pi_pos hrpos
    have hθπ : Real.pi * r ≤ Real.pi := by nlinarith [Real.pi_pos]
    have := member_of_X_of_mem_GoodC hγ hθpos hθπ hrg
    rwa [mul_div_cancel_left₀ r Real.pi_ne_zero] at this
  have henn := Commons.Measure.RealEndgame.ennreal_of_measureReal_ge hSfin hthird'
  calc (1 / 3 : ℝ≥0∞) = ENNReal.ofReal (1 / 3 : ℝ) := FinalReduction.one_third_ennreal
    _ ≤ volume S := henn
    _ ≤ volume (X γ) := measure_mono hinc

end Submission.Configuration
