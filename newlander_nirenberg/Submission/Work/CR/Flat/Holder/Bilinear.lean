/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# `C^{k,α}` norms for maps into an arbitrary normed space
-/
import Mathlib
import Submission.Work.CR.Flat.Holder

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.CR.Flat.Holder

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Supremum over `Ω` of the operator norm of the `i`-th iterated derivative of `f`,
for `f` taking values in an arbitrary normed space. -/
noncomputable def iDN {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (i : ℕ) (f : X → A)
    (Ω : Set X) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω x‖

/-- Hölder seminorm of order `α` of the `i`-th iterated derivative of `f`,
for `f` taking values in an arbitrary normed space. -/
noncomputable def hSN {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (i : ℕ) (α : ℝ)
    (f : X → A) (Ω : Set X) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y),
    ENNReal.ofReal
      (‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖ / ‖x - y‖ ^ α)

@[simp] lemma iDN_complex_eq (i : ℕ) (f : X → ℂ) (Ω : Set X) :
    iDN i f Ω = iterDerivNorm i f Ω := rfl

@[simp] lemma hSN_complex_eq (i : ℕ) (α : ℝ) (f : X → ℂ) (Ω : Set X) :
    hSN i α f Ω = holderSeminorm i α f Ω := rfl

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma le_iDN (i : ℕ) {f : X → A} {Ω : Set X} {x : X} (hx : x ∈ Ω) :
    ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω x‖ ≤ iDN i f Ω :=
  le_iSup₂_of_le x hx le_rfl

/-- The `0`-th iterated derivative does not change the norm of a difference. -/
lemma norm_iteratedFDerivWithin_zero_sub (φ : X → A) (Ω : Set X) (x y : X) :
    ‖iteratedFDerivWithin ℝ 0 φ Ω x - iteratedFDerivWithin ℝ 0 φ Ω y‖ = ‖φ x - φ y‖ := by
  simp only [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map]

lemma le_hSN (i : ℕ) (α : ℝ) {f : X → A} {Ω : Set X} {x y : X}
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ENNReal.ofReal
        (‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖ / ‖x - y‖ ^ α)
      ≤ hSN i α f Ω :=
  le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

/-- `iDN` depends only on the values on `Ω`. -/
lemma iDN_congr {i : ℕ} {f g : X → A} {Ω : Set X} (h : ∀ x ∈ Ω, f x = g x) :
    iDN i f Ω = iDN i g Ω := by
  have H : ∀ x ∈ Ω, iteratedFDerivWithin ℝ i f Ω x = iteratedFDerivWithin ℝ i g Ω x :=
    fun x hx => iteratedFDerivWithin_congr (fun z hz => h z hz) hx i
  unfold iDN
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => ?_
    rw [H x hx]
    exact le_iSup₂_of_le x hx le_rfl
  · refine iSup₂_le fun x hx => ?_
    rw [← H x hx]
    exact le_iSup₂_of_le x hx le_rfl

/-- `hSN` depends only on the values on `Ω`. -/
lemma hSN_congr {i : ℕ} {α : ℝ} {f g : X → A} {Ω : Set X} (h : ∀ x ∈ Ω, f x = g x) :
    hSN i α f Ω = hSN i α g Ω := by
  have H : ∀ x ∈ Ω, iteratedFDerivWithin ℝ i f Ω x = iteratedFDerivWithin ℝ i g Ω x :=
    fun x hx => iteratedFDerivWithin_congr (fun z hz => h z hz) hx i
  unfold hSN
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [H x hx, H y hy]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [← H x hx, ← H y hy]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

@[simp] lemma iDN_zero_fun (i : ℕ) (Ω : Set X) :
    iDN i (0 : X → A) Ω = 0 := by
  refine le_antisymm ?_ bot_le
  refine iSup₂_le fun x _ => ?_
  rw [iteratedFDerivWithin_zero]
  simp

@[simp] lemma hSN_zero_fun (i : ℕ) (α : ℝ) (Ω : Set X) :
    hSN i α (0 : X → A) Ω = 0 := by
  refine le_antisymm ?_ bot_le
  refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun _ => ?_
  rw [iteratedFDerivWithin_zero]
  simp

@[simp] lemma iDN_zero_deriv (Ω : Set X) (f : X → A) :
    iDN 0 f Ω = ⨆ x ∈ Ω, ENNReal.ofReal ‖f x‖ := by
  unfold iDN
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => ?_
    rw [norm_iteratedFDerivWithin_zero]
    exact le_iSup₂_of_le x hx le_rfl
  · refine iSup₂_le fun x hx => ?_
    refine le_iSup₂_of_le x hx ?_
    rw [norm_iteratedFDerivWithin_zero]

@[simp] lemma hSN_zero_deriv (α : ℝ) (Ω : Set X) (f : X → A) :
    hSN 0 α f Ω =
      ⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y), ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α) := by
  unfold hSN
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [norm_iteratedFDerivWithin_zero_sub]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    refine le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy ?_))
    rw [norm_iteratedFDerivWithin_zero_sub]


/-! ### Derivatives of `fderivWithin` -/

lemma iDN_fderivWithin (i : ℕ) (f : X → A) (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω) :
    iDN i (fun z => fderivWithin ℝ f Ω z) Ω = iDN (i + 1) f Ω := by
  unfold iDN
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => ?_
    rw [norm_iteratedFDerivWithin_fderivWithin hΩ hx]
    exact le_iSup₂_of_le x hx le_rfl
  · refine iSup₂_le fun x hx => ?_
    refine le_iSup₂_of_le x hx ?_
    rw [norm_iteratedFDerivWithin_fderivWithin hΩ hx]

lemma hSN_fderivWithin (i : ℕ) (α : ℝ) (f : X → A) (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω) :
    hSN i α (fun z => fderivWithin ℝ f Ω z) Ω = hSN (i + 1) α f Ω := by
  have key : ∀ x ∈ Ω, ∀ y ∈ Ω,
      ‖iteratedFDerivWithin ℝ i (fun z => fderivWithin ℝ f Ω z) Ω x
        - iteratedFDerivWithin ℝ i (fun z => fderivWithin ℝ f Ω z) Ω y‖
      = ‖iteratedFDerivWithin ℝ (i + 1) f Ω x
        - iteratedFDerivWithin ℝ (i + 1) f Ω y‖ := by
    intro x hx y hy
    rw [iteratedFDerivWithin_succ_eq_comp_right hΩ hx,
      iteratedFDerivWithin_succ_eq_comp_right hΩ hy]
    simp only [Function.comp_apply]
    rw [← LinearIsometryEquiv.map_sub (continuousMultilinearCurryRightEquiv' ℝ i X A).symm _ _,
      LinearIsometryEquiv.norm_map]
  unfold hSN
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [key x hx y hy]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    refine le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy ?_))
    rw [key x hx y hy]

/-! ### Subadditivity of `hSN` -/

lemma hSN_add_le (i : ℕ) (α : ℝ) {φ ψ : X → A} {Ω : Set X}
    (hφ : ContDiffOn ℝ i φ Ω) (hψ : ContDiffOn ℝ i ψ Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    hSN i α (φ + ψ) Ω ≤ hSN i α φ Ω + hSN i α ψ Ω := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [iteratedFDerivWithin_add_apply (hφ.contDiffWithinAt hx) (hψ.contDiffWithinAt hx) hΩ hx,
    iteratedFDerivWithin_add_apply (hφ.contDiffWithinAt hy) (hψ.contDiffWithinAt hy) hΩ hy]
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hrewrite : (iteratedFDerivWithin ℝ i φ Ω x + iteratedFDerivWithin ℝ i ψ Ω x)
      - (iteratedFDerivWithin ℝ i φ Ω y + iteratedFDerivWithin ℝ i ψ Ω y)
      = (iteratedFDerivWithin ℝ i φ Ω x - iteratedFDerivWithin ℝ i φ Ω y)
        + (iteratedFDerivWithin ℝ i ψ Ω x - iteratedFDerivWithin ℝ i ψ Ω y) := by abel
  rw [hrewrite]
  calc ENNReal.ofReal
        (‖(iteratedFDerivWithin ℝ i φ Ω x - iteratedFDerivWithin ℝ i φ Ω y)
          + (iteratedFDerivWithin ℝ i ψ Ω x - iteratedFDerivWithin ℝ i ψ Ω y)‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal
          ((‖iteratedFDerivWithin ℝ i φ Ω x - iteratedFDerivWithin ℝ i φ Ω y‖
            + ‖iteratedFDerivWithin ℝ i ψ Ω x - iteratedFDerivWithin ℝ i ψ Ω y‖)
              / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (norm_add_le _ _) hd)
    _ = ENNReal.ofReal
          (‖iteratedFDerivWithin ℝ i φ Ω x - iteratedFDerivWithin ℝ i φ Ω y‖ / ‖x - y‖ ^ α
            + ‖iteratedFDerivWithin ℝ i ψ Ω x - iteratedFDerivWithin ℝ i ψ Ω y‖
              / ‖x - y‖ ^ α) := by
        rw [add_div]
    _ = ENNReal.ofReal
          (‖iteratedFDerivWithin ℝ i φ Ω x - iteratedFDerivWithin ℝ i φ Ω y‖ / ‖x - y‖ ^ α)
        + ENNReal.ofReal
          (‖iteratedFDerivWithin ℝ i ψ Ω x - iteratedFDerivWithin ℝ i ψ Ω y‖
            / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_add (div_nonneg (norm_nonneg _) hd) (div_nonneg (norm_nonneg _) hd)
    _ ≤ hSN i α φ Ω + hSN i α ψ Ω :=
        add_le_add (le_hSN i α hx hy hxy) (le_hSN i α hx hy hxy)

/-! ### The bilinear sup-norm bound -/

lemma iDN_bilinear_le (B : E →L[ℝ] F →L[ℝ] G) (i : ℕ) {f : X → E} {g : X → F} {Ω : Set X}
    (hf : ContDiffOn ℝ i f Ω) (hg : ContDiffOn ℝ i g Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    iDN i (fun x => B (f x) (g x)) Ω
      ≤ ENNReal.ofReal ‖B‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (iDN j f Ω * iDN (i - j) g Ω) := by
  refine iSup₂_le fun x hx => ?_
  have hb := B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hΩ hx le_rfl
  have hsum : (0:ℝ) ≤ ∑ j ∈ Finset.range (i + 1),
      (i.choose j : ℝ) * ‖iteratedFDerivWithin ℝ j f Ω x‖ *
        ‖iteratedFDerivWithin ℝ (i - j) g Ω x‖ := by positivity
  calc ENNReal.ofReal ‖iteratedFDerivWithin ℝ i (fun x => (B (f x)) (g x)) Ω x‖
      ≤ ENNReal.ofReal (‖B‖ * ∑ j ∈ Finset.range (i + 1),
          (i.choose j : ℝ) * ‖iteratedFDerivWithin ℝ j f Ω x‖ *
            ‖iteratedFDerivWithin ℝ (i - j) g Ω x‖) :=
        ENNReal.ofReal_le_ofReal hb
    _ = ENNReal.ofReal ‖B‖ * ENNReal.ofReal (∑ j ∈ Finset.range (i + 1),
          (i.choose j : ℝ) * ‖iteratedFDerivWithin ℝ j f Ω x‖ *
            ‖iteratedFDerivWithin ℝ (i - j) g Ω x‖) :=
        ENNReal.ofReal_mul (norm_nonneg B)
    _ = ENNReal.ofReal ‖B‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (ENNReal.ofReal ‖iteratedFDerivWithin ℝ j f Ω x‖ *
            ENNReal.ofReal ‖iteratedFDerivWithin ℝ (i - j) g Ω x‖) := by
        congr 1
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
        apply Finset.sum_congr rfl
        intro j hj
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ENNReal.ofReal ‖B‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (iDN j f Ω * iDN (i - j) g Ω) := by
        gcongr with j hj
        · exact le_iDN j hx
        · exact le_iDN (i - j) hx

end Work.CR.Flat.Holder
