import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots

/-!
## Factorisation of the mixed jets of `Θ = (1/(4α)) sin(2θ) L₁₂(F)`

The function `Θ α F` depends on `F` only through the radial function `L₁₂ F` and splits as a
product `(z,θ) ↦ B θ · A z` of a function of `θ` alone and a function of `z` alone.  Since
`D_z` acts only on `z` and `D_θ` only on `θ`, every mixed jet of `Θ` factors as the product of
the `θ`-jet of `B` and the `z`-jet of `A`:

  `D_z^j D_θ^i (B ⊗ A) = (Lop^i B) ⊗ (Zop^j A)`.

The only point needing care is that `deriv` in Lean is totalised, so the "constant multiple"
rules `deriv (c · f) = c · deriv f`, `deriv (f · c) = deriv f · c` must be used in their
*unconditional* forms `deriv_const_mul_field`, `deriv_mul_const_field`; no differentiability
hypothesis on `F` is available (and none is needed).
-/

/-- `D_θ^i` applied to a product of a `z`-function and a `θ`-function. -/
private lemma theta_mixed_DthIter_sep (i : ℕ) (A B : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => A z * B θ) = fun z θ => A z * (Work.Spaces.Lop^[i] B) θ := by
  induction i with
  | zero =>
      funext z θ
      rfl
  | succ i ih =>
      rw [show Work.Spaces.DthIter (i + 1) (fun z θ => A z * B θ)
            = Work.Spaces.Dth (Work.Spaces.DthIter i (fun z θ => A z * B θ)) from rfl, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => A z * (Work.Spaces.Lop^[i] B) θ') θ
          = A z * (Work.Spaces.Lop^[i + 1] B) θ
      rw [deriv_const_mul_field (x := θ) (v := Work.Spaces.Lop^[i] B) (A z)]
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      ring

/-- `D_z^j` applied to a product of a `z`-function and a `θ`-function. -/
private lemma theta_mixed_DzIter_sep (j : ℕ) (A C : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => A z * C θ) = fun z θ => (Work.Spaces.Zop^[j] A z) * C θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [show Work.Spaces.DzIter (j + 1) (fun z θ => A z * C θ)
            = Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => A z * C θ)) from rfl, ih]
      funext z θ
      show z * deriv (fun z' => Work.Spaces.Zop^[j] A z' * C θ) z
          = (Work.Spaces.Zop^[j + 1] A z) * C θ
      rw [deriv_mul_const_field (v := C θ) (u := Work.Spaces.Zop^[j] A) (x := z)]
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Zop]
      ring

/-- The hypothesis of the theorem is about `DzIter` at `θ = 0`; for a `θ`-independent function
this is the same as `Zop^[j]` evaluated at `z`. -/
private lemma theta_mixed_Zop_eq_DzIter (j : ℕ) (A : ℝ → ℝ) (z : ℝ) :
    Work.Spaces.Zop^[j] A z = Work.Spaces.DzIter j (fun z _ => A z) z 0 := by
  have h := congrFun (Work.Spaces.Zop_slice j (fun z _ => A z) 0) z
  exact h.symm

/-- Every mixed jet of a product `A z · B θ` is the product of the `θ`-jet of `B` and the
`z`-jet of `A` (in the `DzIter` form that occurs in the hypothesis). -/
private lemma theta_mixed_sep (j i : ℕ) (A B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => A z * B θ) z θ
      = (Work.Spaces.Lop^[i] B) θ * Work.Spaces.DzIter j (fun z _ => A z) z 0 := by
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => A z * B θ)) z θ = _
  rw [theta_mixed_DthIter_sep i A B, theta_mixed_DzIter_sep j A (Work.Spaces.Lop^[i] B)]
  show Work.Spaces.Zop^[j] A z * (Work.Spaces.Lop^[i] B) θ = _
  rw [theta_mixed_Zop_eq_DzIter j A z]
  ring

/-- The same factorisation with the two factors in the order in which `Theta` presents them. -/
private lemma theta_mixed_sep' (j i : ℕ) (A B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => B θ * A z) z θ
      = (Work.Spaces.Lop^[i] B) θ * Work.Spaces.DzIter j (fun z _ => A z) z 0 := by
  have hfun : (fun z θ => B θ * A z) = (fun z θ => A z * B θ) := by
    funext z θ
    exact mul_comm _ _
  rw [hfun]
  exact theta_mixed_sep j i A B z θ

theorem v2_thetaJetsTendsto {α : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hL12 : ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun n : ℕ =>
          Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 (F n) z) z 0)
        Filter.atTop
        (nhds (Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 G z) z 0))) :
    ∀ (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Work.Construction.Theta α (F n)) z θ)
        Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.Construction.Theta α G) z θ)) := by
  intro j i hji z θ hz hθ hθ2
  have hj : j ≤ 3 := by omega
  -- `Θ α H = B ⊗ L₁₂(H)` with `B θ = (1/(4α)) sin(2θ)`.
  set B : ℝ → ℝ := fun θ => (1 / (4 * α)) * Real.sin (2 * θ) with hB
  have hkey : ∀ H : ℝ → ℝ → ℝ,
      Work.Spaces.mixed j i (Work.Construction.Theta α H) z θ
        = (Work.Spaces.Lop^[i] B) θ
            * Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 H z) z 0 := by
    intro H
    rw [show Work.Construction.Theta α H
          = fun z θ => B θ * Work.Construction.L12 H z from rfl]
    exact theta_mixed_sep' j i (Work.Construction.L12 H) B z θ
  rw [show (fun n : ℕ => Work.Spaces.mixed j i (Work.Construction.Theta α (F n)) z θ)
        = (fun n : ℕ => (Work.Spaces.Lop^[i] B) θ
            * Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 (F n) z) z 0)
        from funext (fun n => hkey (F n)), hkey G]
  exact (hL12 j hj z hz).const_mul ((Work.Spaces.Lop^[i] B) θ)

end Work.FTS_RegExport.RXT.Slots
