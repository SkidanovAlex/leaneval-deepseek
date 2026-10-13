import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSEQP.vanishing_ideal_chart

/-!
# `Work.DSEQP.gf_sat_aux` — auxiliary lemmas for `Work.DSEQP.gf_sat`

Pieces of the proof of the chart-saturation statement `Work.DSEQP.chartJ_eq_ker`
(=`Work.DSEQP.gf_sat`):

* `Work.DSEQP.awayRes_away_mk` and `Work.DSEQP.mk_eq_mul_awayRes` — the algebra of the
  localisation map `awayRes` between the `{j}`-chart and the `S`-chart (`W.DSEQP.awayRes`),
  together with `Away.mk`-bookkeeping helpers.
-/

namespace Work.DSEQP

universe a u v

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry
open HomogeneousLocalization
open scoped BigOperators

variable {A : Type a} [CommRing A] {N : ℕ}

lemma away_mk_witness' {S : Type*} [CommRing S] {σ : Type*} [SetLike σ S] [AddSubgroupClass σ S]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] {f : S} {d₁ d₂ : ℕ} (hf₁ : f ∈ 𝒜 d₁) (hf₂ : f ∈ 𝒜 d₂)
    (n : ℕ) (a : S) (ha₁ : a ∈ 𝒜 (n • d₁)) (ha₂ : a ∈ 𝒜 (n • d₂)) :
    Away.mk 𝒜 hf₁ n a ha₁ = Away.mk 𝒜 hf₂ n a ha₂ := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, Away.val_mk]

/-- The cardinality identity for `S \ {j}` with `j ∈ S`. -/
lemma card_sdiff_singleton {S : Finset (Fin (N + 1))} {j : Fin (N + 1)} (hj : j ∈ S) :
    (S \ {j}).card = S.card - 1 := by
  rw [Finset.sdiff_singleton_eq_erase]
  exact Finset.card_erase_of_mem hj

lemma smul_card_sdiff {S : Finset (Fin (N + 1))} {j : Fin (N + 1)} (hj : j ∈ S) (k : ℕ) :
    k • S.card = k • 1 + k • (S \ {j}).card := by
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨j, hj⟩
  have h : S.card = 1 + (S \ {j}).card := by
    have := card_sdiff_singleton (N := N) hj
    omega
  rw [h, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_add]

/-- `awayRes` on a fraction at a singleton chart, in the `S`-chart. -/
lemma awayRes_away_mk (S : Finset (Fin (N + 1))) {j : Fin (N + 1)} (h : {j} ⊆ S)
    (k : ℕ) (f : MvPolynomial (Fin (N + 1)) A) (hf : f ∈ Work.DSCOH.homSub A (N + 1) k) :
    awayRes (A := A) (N := N) h
        (Away.mk (DSMap.PGr A N) (xS_singleton_mem (A := A) j) k f (by simpa using hf))
      = Away.mk (DSMap.PGr A N) (xS_mem_homSub (A := A) S) k
          (f * xS (A := A) (S \ {j}) ^ k) (by
            rw [smul_card_sdiff (N := N) (h (Finset.mem_singleton_self j)) k]
            exact SetLike.mul_mem_graded (by simpa using hf)
              (SetLike.pow_mem_graded k (xS_mem_homSub (A := A) (S \ {j})))) := by
  rw [awayRes, HomogeneousLocalization.awayMap_mk]
  exact away_mk_witness' _ _ _ _ _ _

/-- Key algebraic identity: the `S`-chart fraction is a multiple of the `j`-chart fraction. -/
lemma mk_eq_mul_awayRes (S : Finset (Fin (N + 1))) {j : Fin (N + 1)} (hj : j ∈ S)
    (d : ℕ) (f : MvPolynomial (Fin (N + 1)) A)
    (hf : f ∈ Work.DSCOH.homSub A (N + 1) (d * S.card)) :
    Away.mk (DSMap.PGr A N) (xS_mem_homSub (A := A) S) d f (by rw [smul_eq_mul]; exact hf)
      = Away.mk (DSMap.PGr A N) (xS_mem_homSub (A := A) S) d
          (MvPolynomial.X j ^ (d * S.card))
          (by simpa only [smul_eq_mul, mul_one] using
              SetLike.pow_mem_graded (d * S.card) (DSMap.Mix2.X_mem_PGr (A := A) (N := N) j))
        * awayRes (A := A) (N := N) (Finset.singleton_subset_iff.mpr hj)
            (Away.mk (DSMap.PGr A N) (xS_singleton_mem (A := A) j) (d * S.card) f
              (by rw [smul_eq_mul, mul_one]; exact hf)) := by
  rw [awayRes_away_mk (A := A) (N := N) S (Finset.singleton_subset_iff.mpr hj) (d * S.card) f hf]
  have hy : MvPolynomial.X j * xS (A := A) (S \ {j}) = xS (A := A) S := by
    rw [← xS_singleton (A := A) (j := j), xS_mul_diff (A := A) (N := N)
      (Finset.singleton_subset_iff.mpr hj)]
  rw [Work.DSEQP.away_mk_mul (𝒜 := DSMap.PGr A N) (f := xS (A := A) S) (d := S.card)
      (xS_mem_homSub (A := A) S) d (d * S.card)
      (MvPolynomial.X j ^ (d * S.card)) (f * xS (A := A) (S \ {j}) ^ (d * S.card)) _ _,
    Work.DSEQP.away_mk_pad (𝒜 := DSMap.PGr A N) (f := xS (A := A) S) (d := S.card)
      (xS_mem_homSub (A := A) S) d (d * S.card) f _]
  refine Work.DSEQP.away_mk_congr (xS_mem_homSub (A := A) S) rfl ?_ _ _
  rw [← hy, mul_pow]
  ring


end Work.DSEQP
