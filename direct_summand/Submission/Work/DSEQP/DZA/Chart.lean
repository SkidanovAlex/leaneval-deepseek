/-
# Area DZA: the chart ring `Away 𝒜 (xS S)` as the degree-zero part of the chart localization

`Work.DSEQP.gf_degzero_away`: there is an `A`-linear isomorphism, natural in `S`, between
`(A[x₀,…,x_N][1/x_S])₀` and `Away (MvPolynomial.homogeneousSubmodule (Fin (N+1)) A) (xS S)`.
The map is the obvious one on the generating fractions `m / xS S ^ k` with `m ∈ 𝒜 (k · S.card)`.
-/
import Submission.Work.DSEQP.DZA.Arith

open MvPolynomial HomogeneousLocalization
open scoped BigOperators

namespace Work.DSEQP.DZA

universe a

variable {A : Type a} [CommRing A] {N : ℕ}

noncomputable section

/-! ## 4. Degree bookkeeping for products with `xS` -/

section Degrees

variable {S T : Finset (Fin (N + 1))}

lemma pow_mul_mem {k k' : ℕ} {m m' : MvPolynomial (Fin (N + 1)) A}
    (hm : m ∈ Work.DSCOH.homSub A (N + 1) (k * S.card))
    (hm' : m' ∈ Work.DSCOH.homSub A (N + 1) (k' * S.card)) :
    (Work.DSEQP.xS (A := A) S) ^ k' * m + (Work.DSEQP.xS (A := A) S) ^ k * m'
      ∈ Work.DSCOH.homSub A (N + 1) ((k + k') * S.card) := by
  have h1 : (Work.DSEQP.xS (A := A) S) ^ k' * m ∈
      Work.DSCOH.homSub A (N + 1) ((k + k') * S.card) := by
    have h := SetLike.mul_mem_graded
      (SetLike.pow_mem_graded k' (Work.DSEQP.xS_mem_homSub S)) hm
    rwa [show k' • (S.card) + k * (S.card) = (k + k') * S.card from by
      rw [show k' • (S.card) = k' * S.card from rfl]
      ring] at h
  have h2 : (Work.DSEQP.xS (A := A) S) ^ k * m' ∈
      Work.DSCOH.homSub A (N + 1) ((k + k') * S.card) := by
    have h := SetLike.mul_mem_graded
      (SetLike.pow_mem_graded k (Work.DSEQP.xS_mem_homSub S)) hm'
    rwa [show k • (S.card) + k' * (S.card) = (k + k') * S.card from by
      rw [show k • (S.card) = k * S.card from rfl]
      ring] at h
  exact add_mem h1 h2

lemma mul_pow_mem {k k' : ℕ} {m m' : MvPolynomial (Fin (N + 1)) A}
    (hm : m ∈ Work.DSCOH.homSub A (N + 1) (k * S.card))
    (hm' : m' ∈ Work.DSCOH.homSub A (N + 1) (k' * S.card)) :
    m * (Work.DSEQP.xS (A := A) S) ^ k' + m' * (Work.DSEQP.xS (A := A) S) ^ k
      ∈ Work.DSCOH.homSub A (N + 1) ((k + k') * S.card) := by
  have h1 : m * (Work.DSEQP.xS (A := A) S) ^ k' ∈
      Work.DSCOH.homSub A (N + 1) ((k + k') * S.card) := by
    have h := SetLike.mul_mem_graded hm
      (SetLike.pow_mem_graded k' (Work.DSEQP.xS_mem_homSub S))
    rwa [show k * (S.card) + k' • (S.card) = (k + k') * S.card from by
      rw [show k' • (S.card) = k' * S.card from rfl]
      ring] at h
  have h2 : m' * (Work.DSEQP.xS (A := A) S) ^ k ∈
      Work.DSCOH.homSub A (N + 1) ((k + k') * S.card) := by
    have h := SetLike.mul_mem_graded hm'
      (SetLike.pow_mem_graded k (Work.DSEQP.xS_mem_homSub S))
    rwa [show k' * (S.card) + k • (S.card) = (k + k') * S.card from by
      rw [show k • (S.card) = k * S.card from rfl]
      ring] at h
  exact add_mem h1 h2

/-- `(xS (T \ S)) ^ k * m` is homogeneous of degree `k * T.card` when `m` is homogeneous of
degree `k * S.card`. -/
lemma xS_sdiff_pow_mul_mem (hST : S ⊆ T) {k : ℕ} {m : MvPolynomial (Fin (N + 1)) A}
    (hm : m ∈ Work.DSCOH.homSub A (N + 1) (k * S.card)) :
    (Work.DSEQP.xS (A := A) (T \ S)) ^ k * m ∈
      Work.DSCOH.homSub A (N + 1) (k * T.card) := by
  have h1 : (Work.DSEQP.xS (A := A) (T \ S)) ^ k ∈
      Work.DSCOH.homSub A (N + 1) (k * (T \ S).card) :=
    SetLike.pow_mem_graded k (Work.DSEQP.xS_mem_homSub (T \ S))
  have h2 : (Work.DSEQP.xS (A := A) (T \ S)) ^ k * m ∈
      Work.DSCOH.homSub A (N + 1) (k * (T \ S).card + k * S.card) :=
    SetLike.mul_mem_graded h1 hm
  convert h2 using 1
  rw [← Finset.card_sdiff_add_card_eq_card hST, Nat.mul_add]

end Degrees


/-! ## 6. The `A`-module structure of the chart ring and `Away.mk` -/

section AtoAway

lemma val_AtoAway (S : Finset (Fin (N + 1))) (c : A) :
    (Work.DSEQP.AtoAway (A := A) (N := N) S c).val =
      algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization (Submonoid.powers (Work.DSEQP.xS (A := A) S))) (MvPolynomial.C c) := by
  rw [Work.DSEQP.AtoAway, RingHom.comp_apply, ← HomogeneousLocalization.algebraMap_eq]
  rw [← HomogeneousLocalization.algebraMap_apply (𝒜 := DSMap.PGr A N)
    (x := Submonoid.powers (Work.DSEQP.xS (A := A) S))]
  rw [← IsScalarTower.algebraMap_apply (↥(DSMap.PGr A N 0))
    (Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S))
    (Localization (Submonoid.powers (Work.DSEQP.xS (A := A) S)))
    (algebraMap A ↥(DSMap.PGr A N 0) c)]
  rw [IsScalarTower.algebraMap_apply (↥(DSMap.PGr A N 0)) (MvPolynomial (Fin (N + 1)) A)
    (Localization (Submonoid.powers (Work.DSEQP.xS (A := A) S)))
    (algebraMap A ↥(DSMap.PGr A N 0) c)]
  congr 1

/-- `Away.mk` at degree `0` of the constant polynomial `C c` is `AtoAway c`. -/
lemma away_mk_C (S : Finset (Fin (N + 1))) (c : A) :
    Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_mem_homSub S) 0 (MvPolynomial.C c)
        (by simpa using Submodule.zero_mem (Work.DSCOH.homSub A (N + 1) 0)) =
      Work.DSEQP.AtoAway (A := A) (N := N) S c := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (Work.DSEQP.xS (A := A) S))
  rw [HomogeneousLocalization.Away.val_mk, val_AtoAway]
  rw [Localization.mk_eq_mk']
  rw [show (⟨(Work.DSEQP.xS (A := A) S) ^ 0, by use 0⟩ :
      Submonoid.powers (Work.DSEQP.xS (A := A) S)) = 1 from Subtype.ext (pow_zero _)]
  rw [IsLocalization.mk'_one]

/-- Multiplication by the scalars of `Away`: `AtoAway c * z = c • z` for `z = a / xS^k`. -/
lemma AtoAway_mul_away_mk (S : Finset (Fin (N + 1))) (c : A) (k : ℕ)
    (a : MvPolynomial (Fin (N + 1)) A)
    (ha : a ∈ Work.DSCOH.homSub A (N + 1) (k • S.card))
    (ha' : c • a ∈ Work.DSCOH.homSub A (N + 1) (k • S.card)) :
    Work.DSEQP.AtoAway (A := A) (N := N) S c *
        Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_mem_homSub S) k a ha
      = Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_mem_homSub S) k (c • a) ha' := by
  have hsum : Work.DSEQP.AtoAway (A := A) (N := N) S c *
        Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_mem_homSub S) k a ha
      = Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_mem_homSub S) k (MvPolynomial.C c * a)
          (by simpa [smul_eq_C_mul] using ha') := by
    rw [← away_mk_C (A := A) (N := N) S c]
    rw [away_mk_mul (f := Work.DSEQP.xS (A := A) S) (d := S.card)
      (Work.DSEQP.xS_mem_homSub S) 0 k (MvPolynomial.C c) a
      (by simpa using Submodule.zero_mem (Work.DSCOH.homSub A (N + 1) 0)) ha
      (by simpa [smul_eq_C_mul] using ha')]
    exact away_mk_congr_idx (Work.DSEQP.xS_mem_homSub S) (Nat.zero_add k) _ _
  rw [hsum]
  exact away_mk_congr_num (f := Work.DSEQP.xS (A := A) S) (d := S.card)
    (Work.DSEQP.xS_mem_homSub S) k (by rw [MvPolynomial.smul_eq_C_mul]) _ _

end AtoAway

end

end Work.DSEQP.DZA
