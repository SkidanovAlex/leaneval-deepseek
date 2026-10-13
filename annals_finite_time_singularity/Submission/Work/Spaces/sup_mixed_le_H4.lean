import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Linf_H2_of_decay
import Submission.Work.Spaces.HkSq_mixed_le
import Submission.Work.Spaces.HkMem_mixed_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- `VanishTheta` is preserved by iterated `D_z`-derivatives: the slice `θ ↦ DzIter n f z θ`
is identically zero at the two angular boundaries as soon as `f` is. -/
private lemma DzIter_vanish {f : ℝ → ℝ → ℝ} (h : VanishTheta f) (n : ℕ) :
    VanishTheta (DzIter n f) := by
  induction n with
  | zero => exact h
  | succ m ih =>
      constructor
      · intro z
        have hfun : (fun z' => DzIter m f z' 0) = fun _ => (0 : ℝ) := funext ih.1
        simp [DzIter_succ, Dz, pz, hfun]
      · intro z
        have hfun : (fun z' => DzIter m f z' (π / 2)) = fun _ => (0 : ℝ) := funext ih.2
        simp [DzIter_succ, Dz, pz, hfun]

/-- Any positive iterate of `D_θ` already vanishes on the two angular boundaries
(`D_θ` carries the factor `sin(2θ)`). -/
private lemma DthIter_vanish_of_pos (f : ℝ → ℝ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    VanishTheta (DthIter a f) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  constructor
  · intro z
    show Real.sin (2 * 0) * pth (DthIter a' f) z 0 = 0
    simp
  · intro z
    show Real.sin (2 * (π / 2)) * pth (DthIter a' f) z (π / 2) = 0
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi, zero_mul]

/-- `VanishTheta` is preserved by mixed `D`-derivatives `D_z^b D_θ^a`. -/
private lemma VanishTheta_mixed {f : ℝ → ℝ → ℝ} (h : VanishTheta f) (b a : ℕ) :
    VanishTheta (mixed b a f) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simpa [mixed] using DzIter_vanish h b
  · have h1 : VanishTheta (DthIter a f) := DthIter_vanish_of_pos f ha
    simpa [mixed] using DzIter_vanish h1 b

theorem sup_mixed_le_H4 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hvt : Work.Spaces.VanishTheta g)
    (hdec : Work.Spaces.DecayMixed 2 g) (hmem : Work.Spaces.HkMem α 4 g)
    (b a : ℕ) (hab : a + b ≤ 2) :
    Work.Spaces.supAbs (Work.Spaces.mixed b a g) ≤ 100 / Real.sqrt (Work.Spaces.gam α - 1)
      * Work.Spaces.HkNorm α 4 g := by
  have hsm' : SmoothNbhd (mixed b a g) := SmoothNbhd.DzIter (SmoothNbhd.DthIter hsm a) b
  have hvt' : VanishTheta (mixed b a g) := VanishTheta_mixed hvt b a
  have hmem' : HkMem α 2 (mixed b a g) := HkMem_mixed_le α hα hα1 g hsm hmem b a hab
  have hdec' : ∀ θ ∈ Iθ, Tendsto (fun z => mixed b a g z θ) atTop (𝓝 0) :=
    fun θ hθ => hdec a b hab θ hθ
  have h1 : supAbs (mixed b a g)
      ≤ 100 / Real.sqrt (gam α - 1) * HkNorm α 2 (mixed b a g) :=
    Linf_H2_of_decay α hα hα1 (mixed b a g) hsm' hvt' hdec' hmem'
  have h2 : HkNorm α 2 (mixed b a g) ≤ HkNorm α 4 g := by
    rw [HkNorm, HkNorm]
    exact Real.sqrt_le_sqrt (HkSq_mixed_le α hα hα1 g hsm hmem b a hab)
  have hcoef : 0 ≤ 100 / Real.sqrt (gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc supAbs (mixed b a g)
      ≤ 100 / Real.sqrt (gam α - 1) * HkNorm α 2 (mixed b a g) := h1
    _ ≤ 100 / Real.sqrt (gam α - 1) * HkNorm α 4 g :=
        mul_le_mul_of_nonneg_left h2 hcoef

end Work.Spaces
