import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.cosine_transform_even_smooth_homogeneous

/-!
# `even_smooth_cosine_decompose`

Assembly of the analytic core `cosine_transform_even_smooth_homogeneous`
(commons, Funk--Hecke / cosine transform) with the support-function
plumbing for a smooth origin-symmetric convex body.

## Route
Let `h u := sSup {⟨u,x⟩ | x ∈ X}` be the support function.
* `h` is even (`X = -X`), positively homogeneous of degree 1, and `C^∞`
  away from the origin (hypothesis); hence the commons core
  `cosine_transform_even_smooth_homogeneous` supplies a *signed* even
  continuous compactly supported density `f` with `h u = ∫ |⟨u,x⟩| f x`.
* `f = f₁ - f₂` with `f₁ := max f 0`, `f₂ := max (-f) 0` gives the two
  nonnegative even continuous compactly supported densities requested.
-/

namespace Commons.Geometry.Convex.Hadwiger

open Filter Metric Set MeasureTheory
open scoped Topology BigOperators Pointwise

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- support function -/
private def hsup (X : ConvexBody V) (u : V) : ℝ :=
  sSup ((fun x : V => inner ℝ u x) '' (X : Set V))

/-- image of a set under negation equals its negative. -/
private lemma neg_image (s : Set V) : (fun x : V => -x) '' s = -s := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact Set.mem_neg.mpr (by simpa using hz)
  · intro hy
    refine ⟨-y, ?_, by simp⟩
    exact Set.mem_neg.mp hy

/-- Evenness of the support function of a symmetric convex body. -/
private lemma support_neg (X : ConvexBody V) (hSym : (X : Set V) = -(X : Set V)) (u : V) :
    hsup X (-u) = hsup X u := by
  unfold hsup
  congr 1
  calc
    (fun x : V => inner ℝ (-u) x) '' (X : Set V)
        = ((fun x : V => inner ℝ u x) ∘ (fun x : V => -x)) '' (X : Set V) := by
          apply congrArg (fun f : V → ℝ => f '' (X : Set V))
          funext x
          change inner ℝ (-u) x = inner ℝ u (-x)
          simp [inner_neg_left, inner_neg_right]
    _ = (fun x : V => inner ℝ u x) '' ((fun x : V => -x) '' (X : Set V)) := by
          rw [Set.image_comp]
    _ = (fun x : V => inner ℝ u x) '' (X : Set V) := by
          congr 1
          rw [neg_image]
          exact hSym.symm

/-- Positive homogeneity of the support function of a convex body. -/
private lemma support_smul (X : ConvexBody V) {a : ℝ} (ha : 0 ≤ a) (u : V) :
    hsup X (a • u) = a * hsup X u := by
  unfold hsup
  have him : (fun x : V => inner ℝ (a • u) x) '' (X : Set V)
        = a • ((fun x : V => inner ℝ u x) '' (X : Set V)) := by
    ext z
    rw [mem_smul_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨inner ℝ u x, ⟨x, hx, rfl⟩, ?_⟩
      simpa [inner_smul_left, smul_eq_mul, mul_comm]
    · rintro ⟨t, ⟨x, hx, ht⟩, htz⟩
      refine ⟨x, hx, ?_⟩
      rw [← htz, ← ht]
      simpa [inner_smul_left, smul_eq_mul, mul_comm]
  rw [him, Real.sSup_smul_of_nonneg ha]
  simp

/-- A convex body is bounded in norm. -/
private lemma exists_norm_bound (X : ConvexBody V) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ X, ‖x‖ ≤ R := by
  have hb : Bornology.IsBounded (X : Set V) := X.isCompact.isBounded
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  refine ⟨max R 0, by positivity, ?_⟩
  intro x hx
  exact le_trans (hR x hx) (le_max_left R 0)

private lemma one_sided (X : ConvexBody V) {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x ∈ X, ‖x‖ ≤ R)
    (u v : V) : hsup X u ≤ hsup X v + R * ‖u - v‖ := by
  unfold hsup
  apply csSup_le ?_ ?_
  · exact (ConvexBody.nonempty X).image _
  · rintro y ⟨x, hx, rfl⟩
    calc
      inner ℝ u x ≤ inner ℝ v x + |inner ℝ (u - v) x| := by
        have hu : inner ℝ u x = inner ℝ v x + inner ℝ (u - v) x := by
          rw [← inner_add_left]
          congr 1
          abel
        rw [hu]
        linarith [le_abs_self (inner ℝ (u - v) x)]
      _ ≤ sSup ((fun x : V => inner ℝ v x) '' (X : Set V)) + R * ‖u - v‖ := by
        have h1 : inner ℝ v x ≤ sSup ((fun x : V => inner ℝ v x) '' (X : Set V)) := by
          refine le_csSup ?_ ⟨x, hx, rfl⟩
          refine ⟨‖v‖ * R, ?_⟩
          rintro y ⟨z, hz, rfl⟩
          calc
            inner ℝ v z ≤ ‖v‖ * ‖z‖ := real_inner_le_norm v z
            _ ≤ ‖v‖ * R := by gcongr; exact hR z hz
        have h2 : |inner ℝ (u - v) x| ≤ R * ‖u - v‖ := by
          calc
            |inner ℝ (u - v) x| ≤ ‖u - v‖ * ‖x‖ := by simpa [mul_comm] using abs_real_inner_le_norm (u - v) x
            _ ≤ ‖u - v‖ * R := by gcongr; exact hR x hx
            _ = R * ‖u - v‖ := by ring
        nlinarith

private lemma h_lipschitz (X : ConvexBody V) {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x ∈ X, ‖x‖ ≤ R)
    (u v : V) : |hsup X u - hsup X v| ≤ R * ‖u - v‖ := by
  have hvub : hsup X v ≤ hsup X u + R * ‖u - v‖ := by
    have hb' := one_sided X hR0 hR v u
    rwa [show R * ‖v - u‖ = R * ‖u - v‖ by congr 1; rw [← neg_sub, norm_neg]] at hb'
  rw [abs_sub_le_iff]
  constructor
  · linarith [one_sided X hR0 hR u v]
  · linarith

/-- Continuity of the support function. -/
private lemma support_continuous (X : ConvexBody V) : Continuous (hsup X) := by
  obtain ⟨R, hR0, hR⟩ := exists_norm_bound X
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε / (R + 1), by positivity, ?_⟩
  intro y hy
  have hy' : ‖y - x‖ < ε / (R + 1) := by simpa [dist_eq_norm] using hy
  have hle : |hsup X y - hsup X x| ≤ R * ‖y - x‖ := h_lipschitz X hR0 hR y x
  have hlt : R * ‖y - x‖ < ε := by
    have hRδ : R * (ε / (R + 1)) < ε := by
      by_cases hR : R = 0
      · simp [hR]
        exact hε
      · have hRp : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hR)
        calc
          R * (ε / (R + 1)) = (R / (R + 1)) * ε := by ring
          _ < 1 * ε := by
            exact mul_lt_mul_of_pos_right (by
              rw [div_lt_one]
              · linarith
              · positivity) hε
          _ = ε := by ring
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hy'.le hR0) hRδ
  rw [dist_eq_norm]
  simpa using lt_of_le_of_lt hle hlt

/-- `f = max f 0 - max (-f) 0` pointwise. -/
private lemma max_split {f : V → ℝ} (x : V) : f x = max (f x) 0 - max (-f x) 0 := by
  by_cases hx : 0 ≤ f x
  · have h1 : max (f x) 0 = f x := max_eq_left hx
    have h2 : max (-f x) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2]
    ring
  · have hx' : f x ≤ 0 := le_of_not_ge hx
    have h1 : max (f x) 0 = 0 := max_eq_right hx'
    have h2 : max (-f x) 0 = -f x := max_eq_left (by linarith)
    rw [h1, h2]
    ring

private lemma nonneg_max (t : ℝ) : 0 ≤ max t 0 := le_max_right (a := t) (b := 0)

/-- A function with values vanishing outside a bounded set has compact support. -/
private lemma hasCompactSupport_of_norm_bound {f : V → ℝ}
    (hfsR : ∃ R : ℝ, ∀ x : V, f x ≠ 0 → ‖x‖ ≤ R) : HasCompactSupport f := by
  rcases hfsR with ⟨R, hR⟩
  refine HasCompactSupport.of_support_subset_isCompact (K := closedBall 0 R) ?_ ?_
  · exact isCompact_closedBall 0 R
  · intro x hx
    simpa [Metric.mem_closedBall, dist_zero_right] using hR x (Function.mem_support.mp hx)

private lemma inner_left_continuous (u : V) : Continuous (fun x : V => inner ℝ u x) :=
  continuous_inner.comp (continuous_const.prodMk continuous_id)

/-- integrability of `|⟨u,·⟩| * f` for continuous compactly supported `f`. -/
private lemma integrable_inner_mul_of_bounded (u : V) {f : V → ℝ} (hfc : Continuous f)
    (hfsR : ∃ R : ℝ, ∀ x : V, f x ≠ 0 → ‖x‖ ≤ R) :
    Integrable (fun x : V => |inner ℝ u x| * f x) := by
  rcases hfsR with ⟨R, hR⟩
  have hcs : HasCompactSupport (fun x : V => |inner ℝ u x| * f x) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := closedBall 0 R) ?_ ?_
    · exact isCompact_closedBall 0 R
    · intro x hx
      have hfx : f x ≠ 0 := by
        intro hf0
        apply hx
        simp [hf0]
      simpa [Metric.mem_closedBall, dist_zero_right] using hR x hfx
  exact ((inner_left_continuous u).abs.mul hfc).integrable_of_hasCompactSupport hcs

/-- Continuity of the nonnegative part of a continuous function. -/
private lemma continuous_pos_part {f : V → ℝ} (hfc : Continuous f) :
    Continuous (fun x : V => max (f x) 0) := hfc.max continuous_const

private lemma continuous_neg_part {f : V → ℝ} (hfc : Continuous f) :
    Continuous (fun x : V => max (-f x) 0) := hfc.neg.max continuous_const

end

theorem even_smooth_cosine_decompose
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (X : ConvexBody V)
    (hSym : (X : Set V) = -(X : Set V))
    (hSmooth : ContDiffOn ℝ ⊤ (fun u : V => sSup ((fun x : V => inner ℝ u x) '' (X : Set V)))
      {u : V | u ≠ 0}) :
    ∃ (f₁ f₂ : V → ℝ),
      (∀ x : V, 0 ≤ f₁ x) ∧ (∀ x : V, 0 ≤ f₂ x) ∧
      (∀ x : V, f₁ (-x) = f₁ x) ∧ (∀ x : V, f₂ (-x) = f₂ x) ∧
      Continuous f₁ ∧ Continuous f₂ ∧
      (∃ R₁ : ℝ, ∀ x : V, f₁ x ≠ 0 → ‖x‖ ≤ R₁) ∧
      (∃ R₂ : ℝ, ∀ x : V, f₂ x ≠ 0 → ‖x‖ ≤ R₂) ∧
      (∀ u : V,
        sSup ((fun x : V => inner ℝ u x) '' (X : Set V)) =
          (∫ x : V, |inner ℝ u x| * f₁ x) - (∫ x : V, |inner ℝ u x| * f₂ x)) := by
  classical
  borelize V
  rcases cosine_transform_even_smooth_homogeneous V (hsup X)
      (fun x => support_neg X hSym x)
      (fun a x ha => support_smul X ha x)
      (support_continuous X)
      hSmooth with ⟨f, hfc, hfe, hfs, hfeq⟩
  rcases hfs with ⟨R, hfsR⟩
  let f₁ : V → ℝ := fun x => max (f x) 0
  let f₂ : V → ℝ := fun x => max (-f x) 0
  refine ⟨f₁, f₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa [f₁] using nonneg_max (f x)
  · intro x
    simpa [f₂] using nonneg_max (-f x)
  · intro x
    have hx : f (-x) = f x := hfe x
    simp [f₁, hx]
  · intro x
    have hx : f (-x) = f x := hfe x
    simp [f₂, hx]
  · simpa [f₁] using continuous_pos_part hfc
  · simpa [f₂] using continuous_neg_part hfc
  · refine ⟨R, ?_⟩
    intro x hx
    apply hfsR x
    intro hf0
    apply hx
    simp [f₁, hf0]
  · refine ⟨R, ?_⟩
    intro x hx
    apply hfsR x
    intro hf0
    apply hx
    simp [f₂, hf0]
  · intro u
    change hsup X u = (∫ x : V, |inner ℝ u x| * f₁ x) - (∫ x : V, |inner ℝ u x| * f₂ x)
    have hfun : (fun x : V => |inner ℝ u x| * f x)
        = (fun x : V => |inner ℝ u x| * f₁ x - |inner ℝ u x| * f₂ x) := by
      funext x
      have hs := max_split (f := f) x
      calc
        |inner ℝ u x| * f x = |inner ℝ u x| * (max (f x) 0 - max (-f x) 0) := by
          exact congrArg (fun t : ℝ => |inner ℝ u x| * t) hs
        _ = |inner ℝ u x| * max (f x) 0 - |inner ℝ u x| * max (-f x) 0 := by ring
        _ = |inner ℝ u x| * f₁ x - |inner ℝ u x| * f₂ x := by simp [f₁, f₂]
    calc
      hsup X u = ∫ x : V, |inner ℝ u x| * f x := hfeq u
      _ = ∫ x : V, (|inner ℝ u x| * f₁ x - |inner ℝ u x| * f₂ x) := by
            rw [hfun]
      _ = (∫ x : V, |inner ℝ u x| * f₁ x) - (∫ x : V, |inner ℝ u x| * f₂ x) := by
            have hI1 : Integrable (fun x : V => |inner ℝ u x| * f₁ x) := by
              refine integrable_inner_mul_of_bounded u (continuous_pos_part hfc) ⟨R, ?_⟩
              intro x hx
              apply hfsR x
              intro hf0
              apply hx
              simp [f₁, hf0]
            have hI2 : Integrable (fun x : V => |inner ℝ u x| * f₂ x) := by
              refine integrable_inner_mul_of_bounded u (continuous_neg_part hfc) ⟨R, ?_⟩
              intro x hx
              apply hfsR x
              intro hf0
              apply hx
              simp [f₂, hf0]
            exact integral_sub hI1 hI2

end Commons.Geometry.Convex.Hadwiger
