import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.Elliptic.division_by_z

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-! ## Leibniz for `D_z^j D_θ^i` on a product with a `z`-only factor

`D_θ = sin(2θ) ∂_θ` differentiates only in the angle, so a factor `Φ z` which depends on the
radius alone passes through every iterate `D_θ^i`:

`D_θ^i (Φ z · G z θ) = Φ z · D_θ^i G z θ`.

This is the unconditional `deriv_const_mul` recursion (`deriv_const_mul_field`), so no
smoothness is needed here.  Feeding it into the Leibniz rule for `D_z^j` on the product
`Φ z · (D_θ^i G z θ)` (`Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz`, which needs the two
factors to be `C^∞` on the open quadrant) gives the identity
`D_z^j D_θ^i (Φ·G) = ∑_b C(j,b) D_z^b Φ · D_z^{j-b} D_θ^i G`. -/

/-- A `z`-only factor factors out of every iterate of the angular operator `D_θ`. -/
private theorem DthIter_zOnly_mul (Φ : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => Φ z * H z θ)
      = fun z θ => Φ z * Work.Spaces.DthIter i H z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [deriv_const_mul_field]
    ring

theorem divz_mixed_leibniz (Φ : ℝ → ℝ) (G : ℝ → ℝ → ℝ) (j i : ℕ)
    (hΦ : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Φ z))
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i (fun z θ => Φ z * G z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
            (Work.Spaces.DzIter b (fun z _ => Φ z) z θ
              * Work.Spaces.mixed (j - b) i G z θ) := by
  intro z θ hz hθ0 hθ1
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => Φ z * G z θ)) z θ = _
  rw [DthIter_zOnly_mul Φ G i]
  rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz j (fun z _ => Φ z)
    (Work.Spaces.DthIter i G) hΦ (hG.DthIter i) z θ hz hθ0 hθ1]
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [Work.Spaces.mixed]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
