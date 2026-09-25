import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.NN.Core

open Set

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Scalar multiplication of the *target* commutes with the iterated (within) derivative:
`D^i (c • f) = c • D^i f`, with no differentiability hypothesis on `f`.
This is the key pointwise input for the homogeneity of the Hölder norms. -/
private lemma iteratedFDerivWithin_const_smul_aux {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [Module ℂ Y] [SMulCommClass ℝ ℂ Y] [ContinuousConstSMul ℂ Y]
    {Ω : Set X} (hΩ : UniqueDiffOn ℝ Ω) (c : ℂ) (h : X → Y) :
    ∀ (n : ℕ) (x : X), x ∈ Ω →
      iteratedFDerivWithin ℝ n (fun y => c • h y) Ω x = c • iteratedFDerivWithin ℝ n h Ω x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      ext m
      simp [smul_apply]
  | succ n ih =>
      intro x hx
      ext m
      rw [smul_apply, iteratedFDerivWithin_succ_apply_left]
      have hfd : fderivWithin ℝ (iteratedFDerivWithin ℝ n (fun z => c • h z) Ω) Ω x
          = c • fderivWithin ℝ (iteratedFDerivWithin ℝ n h Ω) Ω x := by
        have h1 : fderivWithin ℝ (iteratedFDerivWithin ℝ n (fun z => c • h z) Ω) Ω x
            = fderivWithin ℝ (fun y => c • iteratedFDerivWithin ℝ n h Ω y) Ω x :=
          fderivWithin_congr (f := fun y => c • iteratedFDerivWithin ℝ n h Ω y)
            (fun y hy => ih y hy) (ih x hx)
        have h2 : fderivWithin ℝ (fun y => c • iteratedFDerivWithin ℝ n h Ω y) Ω x
            = c • fderivWithin ℝ (iteratedFDerivWithin ℝ n h Ω) Ω x :=
          fderivWithin_const_smul_field (𝕜 := ℝ) (R := ℂ)
            (f := iteratedFDerivWithin ℝ n h Ω) c (hΩ x hx)
        exact h1.trans h2
      rw [hfd, smul_apply, iteratedFDerivWithin_succ_apply_left, smul_apply]

lemma iteratedFDerivWithin_const_smul_uniqueDiff {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [Module ℂ Y] [SMulCommClass ℝ ℂ Y] [ContinuousConstSMul ℂ Y]
    {Ω : Set X} (hΩ : UniqueDiffOn ℝ Ω) (c : ℂ) (h : X → Y) (n : ℕ) {x : X} (hx : x ∈ Ω) :
    iteratedFDerivWithin ℝ n (fun y => c • h y) Ω x = c • iteratedFDerivWithin ℝ n h Ω x :=
  iteratedFDerivWithin_const_smul_aux hΩ c h n x hx

/-- The `i`-th iterated derivative norm is homogeneous under scalar multiplication
of the target. -/
lemma iterDerivNorm_const_smul_le {Ω : Set X} (hΩ : UniqueDiffOn ℝ Ω) (c : ℂ) (f : X → ℂ)
    (i : ℕ) :
    Work.CR.Flat.iterDerivNorm i (fun x => c • f x) Ω
      ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.iterDerivNorm i f Ω := by
  refine iSup₂_le fun x hx => ?_
  rw [iteratedFDerivWithin_const_smul_uniqueDiff hΩ c f i hx, norm_smul,
    ENNReal.ofReal_mul (norm_nonneg c)]
  exact mul_le_mul_of_nonneg_left (Work.CR.Flat.le_iterDerivNorm i f Ω hx) (zero_le)

/-- The `i`-th Hölder seminorm is homogeneous under scalar multiplication of the target. -/
lemma holderSeminorm_const_smul_le {Ω : Set X} (hΩ : UniqueDiffOn ℝ Ω) (c : ℂ) (f : X → ℂ)
    (i : ℕ) (α : ℝ) :
    Work.CR.Flat.holderSeminorm i α (fun x => c • f x) Ω
      ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.holderSeminorm i α f Ω := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [iteratedFDerivWithin_const_smul_uniqueDiff hΩ c f i hx,
    iteratedFDerivWithin_const_smul_uniqueDiff hΩ c f i hy, ← smul_sub, norm_smul,
    mul_div_assoc, ENNReal.ofReal_mul (norm_nonneg c)]
  exact mul_le_mul_of_nonneg_left
    (Work.CR.Flat.le_holderSeminorm i α f Ω hx hy hxy) (zero_le)

end

lemma holderNorm_const_mul_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {α : ℝ} {Ω : Set X} (hΩ : UniqueDiffOn ℝ Ω) (c : ℂ) (f : X → ℂ) :
    Work.CR.Flat.holderNorm k α (fun x => c * f x) Ω
      ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.holderNorm k α f Ω := by
  have hfun : (fun x => c * f x) = fun x => c • f x := by
    funext x
    exact smul_eq_mul c (f x)
  rw [hfun]
  simp only [Work.CR.Flat.holderNorm]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_add]
  exact add_le_add (iterDerivNorm_const_smul_le hΩ c f i) (holderSeminorm_const_smul_le hΩ c f i α)

end Work.NN.Core
