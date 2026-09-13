import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

namespace Commons.LinearAlgebra.Matrix

theorem rank_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n] {K : Type*} [Field K]
    (A : Matrix m n K) : A.rank = 0 ↔ A = 0 := by
  classical
  constructor
  · intro h
    rw [Matrix.rank] at h
    have hbot : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
    have h0 : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hbot
    ext i j
    have hc := congrArg (fun f : (n → K) →ₗ[K] (m → K) => f (Pi.single j 1) i) h0
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at hc
    simpa using hc
  · rintro rfl
    exact Matrix.rank_zero

end Commons.LinearAlgebra.Matrix