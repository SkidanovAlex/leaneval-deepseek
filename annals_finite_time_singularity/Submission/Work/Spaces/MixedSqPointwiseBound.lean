/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise bound on the squared mixed derivative by `H⁴`

The `L^∞` bound of the paper's Corollary *Linfty* controls a function pointwise by its
`H²`-norm.  Applying it to the mixed derivative `D_z^b D_θ^a g` (`a + b ≤ 2`) and using
that the `H²`-integrand of `D_z^b D_θ^a g` is pointwise dominated by the `H⁴`-integrand
of `g` gives, for every point of the domain,

`(D_z^b D_θ^a g(z,θ))² ≤ (100/(γ-1)) · |g|²_{H⁴}`.

All the ingredients already live in the workspace:
* `HPwH2` is the pointwise `H²` estimate `(h z θ)² ≤ (100/(γ-1)) · HkSq α 2 h`;
* `HkMem_mixed_le` and `HkSq_mixed_le` transfer `HkMem`/`HkSq` from `g` to `D_z^b D_θ^a g`;
* `SmoothNbhd.DzIter`/`SmoothNbhd.DthIter` transfer smoothness;
* `bt_DzIter_vanish` (plus the trivial `Dth` statement below) transfers `VanishTheta`;
* `DecayMixed 2 g` supplies the slice-decay hypothesis for `D_z^b D_θ^a g`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.HkMem_mixed_le
import Submission.Work.Spaces.HkSq_mixed_le
import Submission.Work.Spaces.Linf_H2_of_decay
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HardyTheta
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.HPwH2
import Submission.Work.Spaces.bt_aux

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
set_option maxHeartbeats 1000000

/-- `D_θ g = sin(2θ) ∂_θ g` vanishes on both angular boundaries, because `sin(2θ)`
does.  Hence `VanishTheta` is preserved by any *positive* iterate of `D_θ` regardless of
the behaviour of `g`. -/
private theorem Dth_vanish (g : ℝ → ℝ → ℝ) : VanishTheta (Dth g) := by
  constructor
  · intro z
    show Real.sin (2 * 0) * pth g z 0 = 0
    simp
  · intro z
    show Real.sin (2 * (π / 2)) * pth g z (π / 2) = 0
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi, zero_mul]

/-- Any positive iterate of `D_θ` vanishes on the two angular boundaries. -/
private theorem DthIter_vanish_of_pos (f : ℝ → ℝ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    VanishTheta (DthIter a f) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [DthIter_succ]
  exact Dth_vanish (DthIter a' f)

/-- `VanishTheta` is preserved by mixed `D`-derivatives `D_z^b D_θ^a`. -/
private theorem VanishTheta_mixed_of_vanish {f : ℝ → ℝ → ℝ} (h : VanishTheta f) (b a : ℕ) :
    VanishTheta (mixed b a f) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [mixed_zero_right]
    obtain ⟨h1, h2⟩ := bt_DzIter_vanish h b
    exact ⟨h1, h2⟩
  · have h1 : VanishTheta (DthIter a f) := DthIter_vanish_of_pos f ha
    obtain ⟨h1a, h1b⟩ := bt_DzIter_vanish h1 b
    exact ⟨h1a, h1b⟩

/-- **Elgindi, `H⁴` pointwise bound on mixed derivatives.**  For `a + b ≤ 2`, the square
of `D_z^b D_θ^a g` at any point of the closed quadrant is bounded by
`(100/(γ-1)) · |g|²_{H⁴}`. -/
theorem MixedSqPointwiseBound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hvt : Work.Spaces.VanishTheta g)
    (hdec : Work.Spaces.DecayMixed 2 g) (hmem : Work.Spaces.HkMem α 4 g)
    (b a : ℕ) (hab : a + b ≤ 2) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ (100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 g := by
  have hsm' : SmoothNbhd (mixed b a g) := SmoothNbhd.DzIter (SmoothNbhd.DthIter hsm a) b
  have hvt' : VanishTheta (mixed b a g) := VanishTheta_mixed_of_vanish hvt b a
  have hmem' : HkMem α 2 (mixed b a g) := HkMem_mixed_le α hα hα1 g hsm hmem b a hab
  have hdec' : ∀ θ ∈ Iθ, Tendsto (fun z => mixed b a g z θ) atTop (𝓝 0) :=
    fun θ hθ => hdec a b hab θ hθ
  have hcoef : 0 ≤ 100 / (gam α - 1) := by
    have hgam1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
    exact div_nonneg (by norm_num) hgam1.le
  have hSq : HkSq α 2 (mixed b a g) ≤ HkSq α 4 g :=
    HkSq_mixed_le α hα hα1 g hsm hmem b a hab
  intro z hz θ hθ
  calc (mixed b a g z θ) ^ 2
      ≤ 100 / (gam α - 1) * HkSq α 2 (mixed b a g) :=
        HPwH2 α hα hα1 (mixed b a g) hsm' hvt' hdec' hmem' z hz θ hθ
    _ ≤ 100 / (gam α - 1) * HkSq α 4 g := mul_le_mul_of_nonneg_left hSq hcoef

end Work.Spaces
