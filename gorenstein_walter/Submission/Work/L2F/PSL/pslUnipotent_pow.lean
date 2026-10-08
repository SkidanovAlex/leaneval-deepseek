import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.PSL

/-- Every element of `pslUnipotent F` has order dividing `p` when `CharP F p`:
its image is `pslMap (unipotent b)` and `(unipotent b) ^ p = 1` because
`(1 + b N)^p = 1 + (bN)^p = 1` for `N` the nilpotent matrix `!![0,1;0,0]` with `N ^ 2 = 0`. -/
theorem pslUnipotent_pow (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] (hchar : CharP F p)
    (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (hx : x ∈ Work.L2F.pslUnipotent F) :
    x ^ p = 1 := by
  -- `x` is the image of `unipotent b` under `pslMap`, i.e. `unipotentHom F (ofAdd b)`.
  rw [Work.L2F.pslUnipotent, Work.L2F.unipotentSubgroup, Work.PSL2.unipotentSubgroup] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := hy
  -- Pass `^ p` through `pslMap`, then through `unipotentHom`; the additive group of `F`
  -- has exponent `p` since `p • b = (p : F) * b = 0`.
  rw [← map_pow]
  have h : (Work.PSL2.unipotentHom F m) ^ p = 1 := by
    rw [← ofAdd_toAdd m, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero F p,
      zero_mul, ofAdd_zero, map_one]
  rw [h, map_one]

end Work.L2F.PSL
