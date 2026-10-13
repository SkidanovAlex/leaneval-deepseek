import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces

/-! ## Splitting a separated product under the mixed operator

If the first factor of a product depends only on `z` and the second only on `θ`,
then the two operators `D_θ = sin(2θ)∂_θ` and `D_z = z∂_z` act on their own
factor:

`D_θ^a (F · G) = F · D_θ^a G`   (when `F` is constant in `θ`),
`D_z^b (F · H) = D_z^b F · H`   (when `H` is constant in `z`).

Both are iterated forms of the elementary fact that the derivative of a product
one of whose factors is *constant in the differentiation variable* is the
derivative of the other factor times that constant
(`deriv_const_mul_field` / `deriv_mul_const_field`), and in particular no
smoothness hypothesis at all is needed. -/

/-- `D_θ^a` of a product whose first factor depends only on `z`. -/
private theorem DthIter_mul_z_only (f : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (a : ℕ) :
    Work.Spaces.DthIter a (fun z θ => f z * H z θ)
      = fun z θ => f z * Work.Spaces.DthIter a H z θ := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field (f z)]
      ring

/-- `D_z^b` of a product whose second factor does not depend on `z`. -/
private theorem DzIter_mul_zIndep {Φ : ℝ → ℝ → ℝ} (hΦ : ∀ z z' θ, Φ z θ = Φ z' θ)
    (H : ℝ → ℝ → ℝ) (b : ℕ) :
    Work.Spaces.DzIter b (fun z θ => H z θ * Φ z θ)
      = fun z θ => Work.Spaces.DzIter b H z θ * Φ z θ := by
  induction b with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      have hφc : ∀ z' : ℝ, Φ z' θ = Φ z θ := fun z' => hΦ z' z θ
      have hfun : (fun z' => Work.Spaces.DzIter n H z' θ * Φ z' θ)
          = fun z' => Work.Spaces.DzIter n H z' θ * Φ z θ := by
        funext z'
        rw [hφc z']
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [hfun, deriv_mul_const_field]
      ring

/-- `D_θ^a` preserves independence of `z`. -/
private theorem DthIter_zIndep {G : ℝ → ℝ → ℝ} (hG : ∀ z z' θ, G z θ = G z' θ) (a : ℕ) :
    ∀ z z' θ, Work.Spaces.DthIter a G z θ = Work.Spaces.DthIter a G z' θ := by
  induction a with
  | zero => exact hG
  | succ n ih =>
      intro z z' θ
      rw [Work.Spaces.DthIter_succ]
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [show (fun θ' => Work.Spaces.DthIter n G z θ')
            = fun θ' => Work.Spaces.DthIter n G z' θ' from funext fun θ' => ih z z' θ']

theorem mixed_sep_product (b a : ℕ) (f g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed b a (fun z θ : ℝ => f z * g θ) z θ
      = Work.Spaces.DzIter b (fun z _ : ℝ => f z) z θ
        * Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ := by
  have hA : Work.Spaces.DthIter a (fun z θ : ℝ => f z * g θ)
      = fun z θ => f z * Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ :=
    DthIter_mul_z_only f (fun _ θ : ℝ => g θ) a
  have hΦ : ∀ z z' θ, Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ
      = Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z' θ :=
    DthIter_zIndep (fun z z' θ => rfl) a
  have hB : Work.Spaces.DzIter b
        (fun z θ => f z * Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ)
      = fun z θ => Work.Spaces.DzIter b (fun z _ : ℝ => f z) z θ
          * Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ :=
    DzIter_mul_zIndep hΦ (fun z _ : ℝ => f z) b
  show Work.Spaces.DzIter b (Work.Spaces.DthIter a (fun z θ : ℝ => f z * g θ)) z θ
      = Work.Spaces.DzIter b (fun z _ : ℝ => f z) z θ
        * Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ
  simp only [hA, hB]

end Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces
