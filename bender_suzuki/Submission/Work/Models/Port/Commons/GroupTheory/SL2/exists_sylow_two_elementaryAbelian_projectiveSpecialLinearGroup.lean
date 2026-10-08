import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Commutator.Finite
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_stabilizer_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.Nat.factorization_mul_odd
import Submission.Work.Models.Port.Commons.Nat.factorization_two_pow
import Submission.Work.Models.Port.Commons.Nat.odd_two_pow_sub_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A Sylow `2`-subgroup of `PSL(2, K)`, `K` of characteristic two

For a finite field `K` of characteristic two, the projective special linear group
`PSL(2, K)` has a Sylow `2`-subgroup `U` of order `|K|`, namely the image of the subgroup
of unipotent (upper unitriangular) matrices
`{!![1, c; 0, 1] | c : K} ⊆ SL(2, K)`.

Since `K` has characteristic two, the determinant-one matrix `!![1, c; 0, 1]` satisfies
`!![1, c; 0, 1]^2 = !![[1, 2c; 0, 1]] = 1`, so every element of `U` is an involution; in
particular `U` is elementary abelian of order `|K|`.  Because the centre of `SL(2, K)` is
trivial in characteristic two, the natural surjection `SL(2, K) → PSL(2, K)` is injective,
so `U` sits inside `PSL(2, K)` with the same order.  Finally
`|PSL(2, K)| = |K| (|K|² - 1)` with `|K|` a power of two and `|K|² - 1` odd, so `|K|` is
exactly the `2`-part of `|PSL(2, K)|`; hence `U` is a Sylow `2`-subgroup.
-/

set_option linter.style.haveILetI false

open Matrix

namespace Commons.GroupTheory.SL2

/-- The unipotent (upper unitriangular) matrix `!![1, c; 0, 1]` as an element of `SL(2, K)`. -/
noncomputable def transvectionSL (K : Type*) [Field K] (c : K) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨Matrix.transvection (0 : Fin 2) (1 : Fin 2) c, by
    simp [Matrix.det_transvection_of_ne]⟩

/-- The unipotent matrices are closed under multiplication, with the parameters adding. -/
lemma transvectionSL_add {K : Type*} [Field K] (c d : K) :
    transvectionSL K (c + d) = transvectionSL K c * transvectionSL K d := by
  apply Subtype.ext
  show Matrix.transvection (0 : Fin 2) (1 : Fin 2) (c + d) =
    Matrix.transvection (0 : Fin 2) (1 : Fin 2) c * Matrix.transvection (0 : Fin 2) (1 : Fin 2) d
  exact (Matrix.transvection_mul_transvection_same (0 : Fin 2) (1 : Fin 2) (by decide) c d).symm

/-- The unipotent matrix with parameter `0` is the identity. -/
lemma transvectionSL_zero {K : Type*} [Field K] :
    transvectionSL K (0 : K) = 1 := by
  apply Subtype.ext
  show Matrix.transvection (0 : Fin 2) (1 : Fin 2) (0 : K) = 1
  rw [Matrix.transvection_zero]

/-- The parameter of a unipotent matrix is recovered from its upper-right entry. -/
lemma transvectionSL_injective (K : Type*) [Field K] :
    Function.Injective (transvectionSL K) := by
  intro c d h
  have h01 : transvectionSL K c 0 1 = transvectionSL K d 0 1 := by rw [h]
  simpa [transvectionSL, Matrix.transvection] using h01

/-- The additive group `K` embedded in `SL(2, K)` through the unipotent matrices. -/
noncomputable def unipotentHom (K : Type*) [Field K] :
    Multiplicative K →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun x := transvectionSL K (Multiplicative.toAdd x)
  map_one' := by simp [transvectionSL_zero]
  map_mul' x y := by rw [toAdd_mul, transvectionSL_add]

/-- The unipotent embedding into `SL(2, K)` is injective. -/
lemma unipotentHom_injective (K : Type*) [Field K] :
    Function.Injective (unipotentHom K) := by
  intro x y h
  have h' : transvectionSL K (Multiplicative.toAdd x) =
      transvectionSL K (Multiplicative.toAdd y) := h
  exact Multiplicative.toAdd.injective (transvectionSL_injective K h')

/-- The unipotent group inside `PSL(2, K)` = `SL(2, K) / Z(SL(2, K))`. -/
noncomputable def unipotentPSLHom (K : Type*) [Field K] :
    Multiplicative K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).comp
    (unipotentHom K)

/-- In characteristic two the natural map `SL(2, K) → PSL(2, K)` is injective, since the
centre of `SL(2, K)` is trivial. -/
lemma unipotentPSLHom_injective {K : Type*} [Field K] (hchar : CharP K 2) :
    Function.Injective (unipotentPSLHom K) := by
  have hker : (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).ker = ⊥ := by
    rw [QuotientGroup.ker_mk',
      Commons.GroupTheory.SL2.center_specialLinearGroup_two_eq_bot hchar]
  have hmk : Function.Injective
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  exact hmk.comp (unipotentHom_injective K)

/-- A Sylow `2`-subgroup of `PSL(2, K)` for `K` a finite field of characteristic two, of
order `|K|` and in which every element is an involution. -/
theorem exists_sylow_two_elementaryAbelian_projectiveSpecialLinearGroup {K : Type*} [Field K]
    [Fintype K] (hchar : CharP K 2) :
    ∃ S : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K),
      Nat.card ↥(S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) = Nat.card K ∧
        ∀ x : ↥(S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)), x ^ 2 = 1 := by
  haveI := hchar
  -- `K` is a finite field of characteristic two, hence `|K| = 2 ^ n`.
  obtain ⟨n, _, hK⟩ := FiniteField.card K 2
  have hn1 : 1 ≤ (n : ℕ) := n.2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hK]
  -- `|K|² - 1` is odd, so the `2`-part of `|K| (|K|² - 1)` is that of `|K|`.
  have hodd : Odd (Nat.card K ^ 2 - 1) := by
    rw [hKn]
    have hpow : (2 ^ (n : ℕ) : ℕ) ^ 2 - 1 = 2 ^ (2 * (n : ℕ)) - 1 := by
      rw [← pow_mul]; ring_nf
    rw [hpow]
    exact Commons.Nat.odd_two_pow_sub_one (2 * (n : ℕ)) (by omega)
  have hPSL : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) :=
    Commons.GroupTheory.SL2.card_projectiveSpecialLinearGroup hchar
  have hfac : (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).factorization 2 =
      (n : ℕ) := by
    rw [hPSL, Commons.Nat.factorization_mul_odd _ _ hodd, hKn,
      Commons.Nat.factorization_two_pow]
  -- The image of the unipotent group has order `|K|`.
  have hφinj : Function.Injective (unipotentPSLHom K) := unipotentPSLHom_injective hchar
  have hcardK : Nat.card ↥(unipotentPSLHom K).range = Nat.card K := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv,
        ← Nat.card_congr Multiplicative.ofAdd]
  have hcard2 : Nat.card ↥(unipotentPSLHom K).range =
      2 ^ (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).factorization 2 := by
    rw [hcardK, hfac, hKn]
  refine ⟨Sylow.ofCard (unipotentPSLHom K).range hcard2, ?_, ?_⟩
  · simp only [Sylow.coe_ofCard]
    exact hcardK
  · intro x
    -- Every element of `Multiplicative K` squares to one when `K` has characteristic two.
    have hy2 : ∀ y : Multiplicative K, y ^ 2 = 1 := by
      intro y
      rw [← ofAdd_toAdd y, pow_two, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero]
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp x.2
    refine Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [show (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) = unipotentPSLHom K y from
      hy.symm]
    rw [← map_pow, hy2 y, map_one]

end Commons.GroupTheory.SL2