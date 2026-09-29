import Mathlib
import Submission.Work.C17.Bsubst_deps

/-!
# `B5_pullback`: the pullback of the differential relation of `B₅` along `y = x²/(x−1)`

The paper's relation for `B₅` (`Work.Pure.b5_rel`)

`2·X·(4−X)·B₅'(X) = (4−X)·B₅(X) − 2·B₂(X) + 4·X`

is pushed forward along the substitution `X ↦ y = Work.C7.yps` (a series of order `1`, so
substitution is legitimate: `Work.C7.yps` has zero constant coefficient).  Since substitution is a
`ℚ`-algebra homomorphism and `d/dx (f ∘ y) = (f' ∘ y)·y'`, the relation becomes the `x`-side
identity

`2·y·(4−y)·(B₅∘y)'(x) = ((4−y)·(B₅∘y) − 2·(B₂∘y) + 4·y)·y'(x)`,

i.e. the statement `Work.C17.B5_pullback`.
-/

namespace Work.C17

open PowerSeries

theorem B5_pullback :
    2 * Work.C7.yps * (4 - Work.C7.yps) * PowerSeries.derivative (R := ℚ) (Work.C7.g 4)
      = ((4 - Work.C7.yps) * (Work.C7.g 4) - 2 * (Work.C7.g 1) + 4 * Work.C7.yps)
        * PowerSeries.derivative (R := ℚ) Work.C7.yps := by
  have hy : PowerSeries.HasSubst Work.C7.yps := Submission.CDT.sympY_hasSubst
  -- the subst pullbacks defining `g`
  have hg4 : Work.C7.g 4 = Submission.CDTPlan.B5.subst Work.C7.yps := by
    simp [Work.C7.g, Submission.CDTPlan.pureB, Fin.isValue]
  have hg1 : Work.C7.g 1 = Submission.CDTPlan.B2.subst Work.C7.yps := by
    simp [Work.C7.g, Submission.CDTPlan.pureB, Fin.isValue]
  -- `Work.Pure.b5_rel` after substituting `X ↦ y`
  have hb5 : 2 * Work.C7.yps * (4 - Work.C7.yps)
        * (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B5).subst Work.C7.yps
      = (4 - Work.C7.yps) * (Submission.CDTPlan.B5.subst Work.C7.yps)
        - 2 * (Submission.CDTPlan.B2.subst Work.C7.yps) + 4 * Work.C7.yps := by
    have h := congrArg (fun f : PowerSeries ℚ => f.subst Work.C7.yps) Work.Pure.b5_rel
    rw [← PowerSeries.coe_substAlgHom hy] at h
    simp only [map_mul, map_sub, map_add, PowerSeries.substAlgHom_X hy] at h
    simp only [map_ofNat] at h
    simpa only [PowerSeries.coe_substAlgHom] using h
  -- `(B₅∘y)' = (B₅'∘y)·y'`
  have hdy : PowerSeries.derivative (R := ℚ) (Work.C7.g 4)
      = (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B5).subst Work.C7.yps
        * PowerSeries.derivative (R := ℚ) Work.C7.yps := by
    rw [hg4, PowerSeries.derivative_subst hy]
  calc 2 * Work.C7.yps * (4 - Work.C7.yps) * PowerSeries.derivative (R := ℚ) (Work.C7.g 4)
      = 2 * Work.C7.yps * (4 - Work.C7.yps)
          * ((PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B5).subst Work.C7.yps
              * PowerSeries.derivative (R := ℚ) Work.C7.yps) := by rw [hdy]
    _ = (2 * Work.C7.yps * (4 - Work.C7.yps)
          * (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B5).subst Work.C7.yps)
          * PowerSeries.derivative (R := ℚ) Work.C7.yps := by ring
    _ = ((4 - Work.C7.yps) * (Submission.CDTPlan.B5.subst Work.C7.yps)
          - 2 * (Submission.CDTPlan.B2.subst Work.C7.yps) + 4 * Work.C7.yps)
          * PowerSeries.derivative (R := ℚ) Work.C7.yps := by rw [hb5]
    _ = ((4 - Work.C7.yps) * (Work.C7.g 4) - 2 * (Work.C7.g 1) + 4 * Work.C7.yps)
          * PowerSeries.derivative (R := ℚ) Work.C7.yps := by rw [hg4, hg1]

end Work.C17
