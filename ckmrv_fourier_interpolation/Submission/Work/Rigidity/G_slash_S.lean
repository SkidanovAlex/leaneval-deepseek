import Mathlib
import Submission.Work.Rigidity.AnnPlusWeightFourPDefs

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm

namespace Work.Rigidity

/-- At even weight the element `-1` of `SL(2, ℤ)` acts trivially on functions on `ℍ`:
`-1` acts on `ℍ` by the identity, with automorphy factor `-1`, and `(-1) ^ (-4) = 1`. -/
lemma slash_neg_one_four (F : ℍ → ℂ) : F ∣[(4 : ℤ)] (-1 : SL(2, ℤ)) = F := by
  funext τ
  rw [ModularForm.SL_slash_apply]
  have h1 : ((-1 : SL(2, ℤ)) • τ : ℍ) = τ := by
    apply UpperHalfPlane.ext
    simp
  have h2 : UpperHalfPlane.denom (Work.Kernels.glOf (-1 : SL(2, ℤ))) (τ : ℂ) = -1 := by
    rw [show UpperHalfPlane.denom (Work.Kernels.glOf (-1 : SL(2, ℤ))) (τ : ℂ)
        = (Work.Kernels.glOf (-1 : SL(2, ℤ))) 1 0 * (τ : ℂ)
          + (Work.Kernels.glOf (-1 : SL(2, ℤ))) 1 1 from rfl]
    rw [Work.Kernels.glOf_apply, Work.Kernels.glOf_apply]
    simp
  rw [h1, h2]
  norm_num

/-- **The `S`-action relations for `g_0` and `g_2`.**  Let `f : ℍ → ℂ` satisfy `f ∣[4] S = -f`
(written `SlashAction.map (4 : ℤ) ModularGroup.S f = -f`, to avoid notation), and put
`g_0 = f ∣[4] T - f`, `g_2 = f ∣[4] (T S) + f` (the definitions `G0` and `G2` of
`Submission.Work.Rigidity.AnnPlusWeightFourPDefs`).  Then `g_0 ∣[4] S = g_2` and
`g_2 ∣[4] S = g_0`.

Sketch (weight `4` throughout; `S * S = -1` in `SL(2,ℤ)`, but `-1` acts trivially at even
weight: `F ∣[k] (-1) = F` for even `k`).  First relation:
`(g_0 ∣[4] S) = ((f ∣[4] T) - f) ∣[4] S = f ∣[4] (T S) - f ∣[4] S = f ∣[4] (T S) + f = g_2`
(using `SlashAction.slash_mul`, `SlashAction.add_slash`, `SlashAction.neg_slash` and `hS`).
Second relation: `(g_2 ∣[4] S) = (f ∣[4] (T S) + f) ∣[4] S = f ∣[4] ((T S) S) + f ∣[4] S`, and
`(T S) S = T * (S*S) = T * (-1) = -T`; since `f ∣[4] (-T) = f ∣[4] T`, this is
`f ∣[4] T - f = g_0`. -/
theorem G_slash_S {f : UpperHalfPlane → ℂ}
    (hS : SlashAction.map (4 : ℤ) ModularGroup.S f = -f) :
    SlashAction.map (4 : ℤ) ModularGroup.S (G0 f) = G2 f ∧
      SlashAction.map (4 : ℤ) ModularGroup.S (G2 f) = G0 f := by
  have hTSS : ModularGroup.T * ModularGroup.S * ModularGroup.S = -ModularGroup.T := by decide
  have hneg : f ∣[(4 : ℤ)] (-ModularGroup.T) = f ∣[(4 : ℤ)] ModularGroup.T := by
    rw [neg_eq_neg_one_mul, SlashAction.slash_mul, slash_neg_one_four]
  constructor
  · rw [G0, G2, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
      ← SlashAction.slash_mul, hS, neg_neg]
  · rw [G2, G0, SlashAction.add_slash, ← SlashAction.slash_mul, hTSS, hneg, hS,
      ← sub_eq_add_neg]

end Work.Rigidity
