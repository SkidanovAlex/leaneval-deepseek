import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.IdeleClassGroup

namespace NK.GlobalCFTdeep.SecondInequality

-- Module `Submission.NK.GlobalCFTdeep.SecondInequality.index_normClassSubgroup_eq_card_rayClassGroup`,
-- namespace `NK.GlobalCFTdeep.SecondInequality`, importing
-- `Submission.NK.GlobalCFT.NormGroup` (for `NK.GlobalCFT.Idele.normClassSubgroup`,
-- `normImage`) and `Submission.NK.GlobalCFT.IdeleClassGroup` (for
-- `NK.GlobalCFT.IdeleClassGroup.rayClassGroup`, `IdeleClassGroup.mk`).
--
-- MATHEMATICS.  By definition `NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U` is the quotient
-- `𝕀 K ⧸ (Kˣ ⊔ U)`, and `NK.GlobalCFT.Idele.normClassSubgroup K L` is the image of the norm
-- subgroup `normImage K L` in `C K = 𝕀 K ⧸ Kˣ`.  Noether's third isomorphism theorem
-- (`QuotientGroup.quotientQuotientEquivQuotient`, or directly the surjection
-- `rayClassGroupMk K U : C K →* rayClassGroup K U` with kernel `rayClassGroupMk`-kernel
-- `U.map (mk K)`, combined with `Subgroup.index_eq_card`) identifies the index of
-- `normClassSubgroup K L` in `C K` with the cardinality of the ray class group of `K` modulo the
-- norm subgroup.
--
-- This is the bridge between the `Subgroup.index` form of the second inequality
-- (`NK.GlobalCFT.TwoInequalities`) and the `Nat.card` form in which the analytic argument
-- (Milne VI.4.9) produces it.
theorem index_normClassSubgroup_eq_card_rayClassGroup {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index =
      Nat.card (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K (NK.GlobalCFT.Idele.normImage K L)) := by
  -- `Subgroup.index` *is* `Nat.card` of the quotient, and `normClassSubgroup K L` is by definition
  -- the kernel of the canonical surjection `C K →* rayClassGroup K (normImage K L)`.
  have hker : NK.GlobalCFT.Idele.normClassSubgroup K L =
      (NK.GlobalCFT.IdeleClassGroup.rayClassGroupMk K
        (NK.GlobalCFT.Idele.normImage K L)).ker :=
    (NK.GlobalCFT.IdeleClassGroup.ker_rayClassGroupMk _).symm
  rw [Subgroup.index_eq_card, hker]
  -- Noether's first isomorphism theorem turns the surjection into an equivalence of the quotient
  -- by its kernel with the ray class group.
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (NK.GlobalCFT.IdeleClassGroup.rayClassGroupMk_surjective _)).toEquiv

end NK.GlobalCFTdeep.SecondInequality
