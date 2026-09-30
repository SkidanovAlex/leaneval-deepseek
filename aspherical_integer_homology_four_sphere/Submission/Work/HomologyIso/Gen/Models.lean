/-
# `HomologyIso/`: the generated data against the models

The generated modules of `Submission/Work/HomologyIso/Gen/` (produced by
`Submission/Work/HomologyIso/scripts/gen_sdr_data.py`) give, for each Ratcliffe–Tschantz cell
complex, the isomorphism `H_k(C) ≅ ℤ^{(b k)}` of `Work.Certificates.SDR.sound`.  This module
identifies the generated ranks `b` with the models of `Work.HomologyIso.Algebra`:

| complex | generated `b` | model rank | meaning |
|---|---|---|---|
| `mbar` | `(1,5,10,4,0)` | `rankA` | `H_k(M̄) = H_k(A)` |
| `cusp1` … `cusp5` | `(1,3,3,1)` | `rankT` | `H_k(T³_v) = H_k(A ∩ B)` per cusp |
| `prodTorus` | `(1,3,3,1)` | `rankT` | the same group, the other side of the torus bridge |
| `t2` | `(1,2,1)` | `rankT2` | `H_k(T²_v)`, the second summand of `H_k(B)` |

so that the homology of every generated complex is *literally* one of the models of the
Mayer–Vietoris computation.
-/
import Submission.Work.HomologyIso.Gen.Mbar
import Submission.Work.HomologyIso.Gen.Cusps
import Submission.Work.HomologyIso.Gen.ProdTorus
import Submission.Work.HomologyIso.Gen.T2
import Submission.Work.HomologyIso.Algebra

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open CategoryTheory

namespace Work.HomologyIso.Gen

open Work.Certificates

/-! ## §1  The ranks -/

/-- The generated rank of `H_k(M̄)` is `rankA`. -/
theorem mbarB_eq_rankA (k : ℕ) : mbarB k = rankA (k : ℤ) := by
  by_cases h : k < 5
  · interval_cases k <;> decide
  · rw [mbarB_eq_zero k (by omega),
      rankA_eq_zero _ (by omega) (by omega) (by omega) (by omega)]

/-- The generated rank of `H_k(T³_v)` is `rankT`, for each of the five cusps. -/
theorem cuspB_eq_rankT (k : ℕ) :
    cusp1B k = rankT (k : ℤ) ∧ cusp2B k = rankT (k : ℤ) ∧ cusp3B k = rankT (k : ℤ) ∧
      cusp4B k = rankT (k : ℤ) ∧ cusp5B k = rankT (k : ℤ) := by
  by_cases h : k < 4
  · interval_cases k <;> refine ⟨by decide, by decide, by decide, by decide, by decide⟩
  · have hz : rankT (k : ℤ) = 0 :=
      rankT_eq_zero _ (by omega) (by omega) (by omega) (by omega)
    rw [hz]
    exact ⟨cusp1B_eq_zero k (by omega), cusp2B_eq_zero k (by omega), cusp3B_eq_zero k (by omega),
      cusp4B_eq_zero k (by omega), cusp5B_eq_zero k (by omega)⟩

/-- The generated rank of `H_k(S¹_u × T²)` is `rankT` as well. -/
theorem prodTorusB_eq_rankT (k : ℕ) : prodTorusB k = rankT (k : ℤ) := by
  by_cases h : k < 4
  · interval_cases k <;> decide
  · rw [prodTorusB_eq_zero k (by omega),
      rankT_eq_zero _ (by omega) (by omega) (by omega) (by omega)]

/-- The generated rank of `H_k(T²)` is `rankT2`. -/
theorem t2B_eq_rankT2 (k : ℕ) : t2B k = rankT2 (k : ℤ) := by
  by_cases h : k < 3
  · interval_cases k <;> decide
  · rw [t2B_eq_zero k (by omega), rankT2_eq_zero _ (by omega) (by omega) (by omega)]

/-! ## §2  The homology of the generated complexes, as the models -/

/-- **`H_k(M̄) ≅ ℤ^{rankA k}`** — the generated computation, in the model of the area. -/
theorem mbarCx_homology_modelA (k : ℕ) :
    Nonempty (mbarCx.homology k ≅ ModelA (k : ℤ)) :=
  (mbarCx_homology k).map fun e => e ≪≫ freeModCast (mbarB_eq_rankA k)

/-- **`H_k(T³_v) ≅ ℤ^{rankT k}`** for the five cusp complexes. -/
theorem cuspCx_homology_modelT (k : ℕ) :
    Nonempty (cusp1Cx.homology k ≅ ModelT (k : ℤ)) ∧
      Nonempty (cusp2Cx.homology k ≅ ModelT (k : ℤ)) ∧
      Nonempty (cusp3Cx.homology k ≅ ModelT (k : ℤ)) ∧
      Nonempty (cusp4Cx.homology k ≅ ModelT (k : ℤ)) ∧
      Nonempty (cusp5Cx.homology k ≅ ModelT (k : ℤ)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cuspB_eq_rankT k
  exact ⟨(cusp1Cx_homology k).map (fun e => e ≪≫ freeModCast h1),
    (cusp2Cx_homology k).map (fun e => e ≪≫ freeModCast h2),
    (cusp3Cx_homology k).map (fun e => e ≪≫ freeModCast h3),
    (cusp4Cx_homology k).map (fun e => e ≪≫ freeModCast h4),
    (cusp5Cx_homology k).map (fun e => e ≪≫ freeModCast h5)⟩

/-- **`H_k(S¹_u × T²) ≅ ℤ^{rankT k}`** — the product side of the torus bridge. -/
theorem prodTorusCx_homology_modelT (k : ℕ) :
    Nonempty (prodTorusCx.homology k ≅ ModelT (k : ℤ)) :=
  (prodTorusCx_homology k).map fun e => e ≪≫ freeModCast (prodTorusB_eq_rankT k)

/-- **`H_k(T²) ≅ ℤ^{rankT2 k}`** — the filling torus. -/
theorem t2Cx_homology_modelT2 (k : ℕ) :
    Nonempty (t2Cx.homology k ≅ ModelT2 (k : ℤ)) :=
  (t2Cx_homology k).map fun e => e ≪≫ freeModCast (t2B_eq_rankT2 k)

end Work.HomologyIso.Gen
