import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.mem_borel
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff
import Submission.Work.L2F.PSL.pslUnipotent_card
import Submission.Work.L2F.PSL.pslMap_mem_normalizer_iff_mem_borel
import Submission.Work.L2F.PSL.natCard_borel

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-! ## Auxiliary computations

The order of the normalizer of `pslUnipotent F` in `PSL(2,F)` is assembled from three facts:

* `N(pslUnipotent F) = pslBorel F` (the image of the upper triangular subgroup `borel F`);
* the kernel of `pslMap F` meets `borel F` in `{1, -1}`, a group of order `2`;
* `|borel F| = q(q-1)`, `q = Nat.card F` (`natCard_borel`).

The second and third combine (via the index formula `Subgroup.relIndex_mul_card`) into
`2 * |pslBorel F| = |borel F| = q(q-1)`. -/

/-- The kernel of the quotient map `SL(2,F) → PSL(2,F)` meets the upper triangular subgroup in
`{1, -1} = zpowers (-1)`, a group of order `2`: by `pslMap_eq_one_iff` an element of the kernel is
`1` or `-1`, both of which are upper triangular, and `1 ≠ -1` because `(2 : F) ≠ 0`. -/
private lemma natCard_pslMap_ker_inf_borel (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    Nat.card ((Work.PSL2.pslMap F).ker ⊓ Work.L2F.borel F :
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) = 2 := by
  have hne : Work.L2F.negOne F ≠ 1 := by
    intro h
    have hmat : (((1 : SL(2, F)) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
      rw [← h]
      rfl
    have h00 : (1 : F) = -1 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hmat
      simpa using this
    have h' : (1 : F) + 1 = 0 := by
      have h'' : (1 : F) - (-1) = 0 := sub_eq_zero.mpr h00
      simpa using h''
    rw [one_add_one_eq_two] at h'
    exact h2 h'
  have hsq : (Work.L2F.negOne F) ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    change (((Work.L2F.negOne F * Work.L2F.negOne F : SL(2, F))) :
        Matrix (Fin 2) (Fin 2) F) = ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    rw [show ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
    rw [neg_mul_neg, one_mul]
  have hset : (Work.PSL2.pslMap F).ker ⊓ Work.L2F.borel F =
      Subgroup.zpowers (Work.L2F.negOne F) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf, MonoidHom.mem_ker] at hx
      rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 x).mp hx.1 with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [MonoidHom.mem_ker]
        exact (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)
      · rw [Work.L2F.Conic.mem_borel]
        simp [Work.L2F.negOne]
  rw [hset, Nat.card_zpowers]
  exact orderOf_eq_prime hsq hne

/-- The normalizer of `pslUnipotent F = π(U)` in `PSL(2,F)` is the image `π(B)` of the upper
triangular subgroup.  `⊇` is `pslMap_mem_normalizer_pslUnipotent`; for `⊆`, lift an element of the
normalizer to `A ∈ SL(2,F)` and apply `pslMap_mem_normalizer_iff_mem_borel`. -/
private lemma normalizer_pslUnipotent_eq_pslBorel (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    Subgroup.normalizer (Work.L2F.pslUnipotent F :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = Work.L2F.pslBorel F := by
  apply le_antisymm
  · intro g hg
    obtain ⟨A, hA⟩ : ∃ A : SL(2, F), Work.PSL2.pslMap F A = g :=
      QuotientGroup.mk'_surjective (Subgroup.center (SL(2, F))) g
    rw [← hA] at hg
    rw [Work.L2F.pslBorel, Subgroup.mem_map]
    exact ⟨A, (pslMap_mem_normalizer_iff_mem_borel F h2 A).mp hg, hA⟩
  · intro g hg
    rw [Work.L2F.pslBorel, Subgroup.mem_map] at hg
    obtain ⟨A, hA, rfl⟩ := hg
    exact (pslMap_mem_normalizer_iff_mem_borel F h2 A).mpr hA

/-- `2 * |π(B)| = |B| = q(q-1)`: the map `B → PSL(2,F)` is `2`-to-`1` because its kernel on `B` is
`{1, -1}` (`natCard_pslMap_ker_inf_borel`); this is the index formula
`Subgroup.relIndex_mul_card` for `H = (pslMap F).ker` and `K = borel F`. -/
private lemma two_mul_natCard_pslBorel (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    2 * Nat.card (Work.L2F.pslBorel F) = Nat.card (Work.L2F.borel F) := by
  have h1 : (Work.PSL2.pslMap F).ker.relIndex (Work.L2F.borel F) =
      Nat.card ((Work.L2F.borel F).map (Work.PSL2.pslMap F)) :=
    Subgroup.relIndex_ker (K := Work.L2F.borel F) (Work.PSL2.pslMap F)
  have h2' : (Work.PSL2.pslMap F).ker.relIndex (Work.L2F.borel F) *
      Nat.card ((Work.PSL2.pslMap F).ker ⊓ Work.L2F.borel F :
        Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
        Nat.card (Work.L2F.borel F) :=
    Subgroup.relIndex_mul_card (H := (Work.PSL2.pslMap F).ker) (K := Work.L2F.borel F)
  rw [h1, natCard_pslMap_ker_inf_borel F h2] at h2'
  rw [Work.L2F.pslBorel, mul_comm]
  exact h2'

/-- The normalizer of `pslUnipotent F` in `PSL(2,F)` has `q(q-1)/2` elements, i.e.
`2 * Nat.card (normalizer (pslUnipotent F)) = q * (q-1)`.  Proof: `N_{SL}(U) = B` (the upper
triangular subgroup, since a matrix conjugating `!![1,1;0,1]` into `U` is upper triangular), and
`N_{PSL}(π(U)) = π(N_{SL}(U·{±1})) = π(B)`; `|B| = q(q-1)` and `B ⊓ {±1} = {±1}`, so the image has
`q(q-1)/2` elements. -/
theorem normalizer_pslUnipotent_card (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) :
    2 * Nat.card (Subgroup.normalizer (Work.L2F.pslUnipotent F :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) =
      Nat.card F * (Nat.card F - 1) := by
  rw [normalizer_pslUnipotent_eq_pslBorel F h2, two_mul_natCard_pslBorel F h2, natCard_borel F]

end Work.L2F.PSL
