import Mathlib
import Submission.Vdw.IndexCount
import Submission.Vdw.CaseIIClasses
import Submission.Vdw.CaseISmallPrime
import Submission.Vdw.CaseIIIField
import Submission.Vdw.SharpFibre
import Submission.Vdw.PerFieldFibreAll

open Polynomial Filter Asymptotics
open scoped BigOperators NumberField Classical
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The index refinement: `FieldCountBound n (n/4 + ε)`

We assemble the per-discriminant count `IndexCount.goodVec_ncard_le` into the
field count.  For a fixed `H`, the field-isomorphism classes of the Case-II
region with `|Disc| ≤ Y` inject into the disjoint union of the sets
`GoodVec n D`, `D ≤ Y`.  Since every discriminant arising is *squarefull*
(the region is primitive with `|Gal| < n!`, `squarefull_classDisc`) and its
small-prime part is bounded by `S₀(n) = primorial n ^ (n + n log₂ n)`
(`discSmallPart_classDisc_le`), the per-discriminant bound

  `#GoodVec n D ≤ K·D^{(n+2)/4 + ε}/D_large = K·D^{(n+2)/4 - 1 + ε}·D_small`

sums over the `≪ √Y` squarefull `D ≤ Y` to `≪ Y^{n/4 + ε}`:

  **`fieldCountBound_index` : `FieldCountBound n (n/4 + ε)`.**

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## 1. Admissibility of the class discriminants -/

/-- The class discriminant of a member of the Case-II region is squarefull
(the region is primitive with `|Gal| < n!`, so Case-I squarefullness applies). -/
theorem squarefull_classDisc (n H : ℕ) (hn : 1 ≤ n) (hnn : 2 ≤ n)
    (q : Quotient (fieldIsoSetoid n H hn)) : Squarefull (classDisc n H hn q) := by
  obtain ⟨h, hprim, -⟩ := (Quotient.out q : ↥(SubcaseI_P2 n H)).2.1.2
  haveI : Fact (Irreducible ((((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])).map φℚ)) := ⟨h⟩
  rw [classDisc_out n H hn q]
  show Squarefull (fieldDisc (((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])))
  have hm : (((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])) ∈ SubcaseI_P2 n H :=
    (Quotient.out q : ↥(SubcaseI_P2 n H)).2
  have hbad : (((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])) ∈ IrreducibleBad n H := hm.1.1
  obtain ⟨hmonic, hdegree, -, hcard⟩ := hbad.1
  have hnd : ((((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])).map φℚ).natDegree = n := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero φℚ
      (by rw [hmonic.leadingCoeff]; simp)]
    exact Polynomial.natDegree_eq_of_degree_eq_some hdegree
  have hcard' : Nat.card (((((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])).map φℚ)).Gal
      < (((((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])).map φℚ).natDegree).factorial := by
    rw [hnd]
    exact hcard
  exact squarefull_fieldDisc_of_primitive_card_lt _ hmonic hprim hcard'

/-- The small-prime part of a class discriminant is bounded in terms of `n`
alone. -/
theorem discSmallPart_classDisc_le (n H : ℕ) (hn : 1 ≤ n) (hnn : 2 ≤ n)
    (q : Quotient (fieldIsoSetoid n H hn)) :
    discSmallPart n (classDisc n H hn q) ≤ primorial n ^ (n + n * Nat.log 2 n) := by
  obtain ⟨h, -, -⟩ := (Quotient.out q : ↥(SubcaseI_P2 n H)).2.1.2
  haveI : Fact (Irreducible ((((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])).map φℚ)) := ⟨h⟩
  rw [classDisc_out n H hn q]
  show discSmallPart n (fieldDisc (((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]))) ≤
    primorial n ^ (n + n * Nat.log 2 n)
  have hm : (((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])) ∈ SubcaseI_P2 n H :=
    (Quotient.out q : ↥(SubcaseI_P2 n H)).2
  have hbad : (((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])) ∈ IrreducibleBad n H := hm.1.1
  obtain ⟨hmonic, hdegree, -, -⟩ := hbad.1
  exact discSmallPart_fieldDisc_le _ hmonic n (Polynomial.natDegree_eq_of_degree_eq_some hdegree)

/-- The exponent at a prime `p > n` of a class discriminant is at most `n - 1`
(Lemma 24 through `GoodPoly_factorization_le`). -/
theorem factorization_classDisc_le (n H : ℕ) (hn : 1 ≤ n) (hnn : 2 ≤ n)
    (q : Quotient (fieldIsoSetoid n H hn)) {p : ℕ} (hp : Nat.Prime p)
    (hpn : n < p) (hpd : p ∣ classDisc n H hn q) :
    (classDisc n H hn q).factorization p ≤ n - 1 :=
  GoodPoly_factorization_le n _ (one_le_classDisc n H hn q) hn hp hpn hpd
    ⟨classPoly n H hn hnn q, classPoly_mem_goodPoly n H hn hnn q⟩

/-! ## 2. The per-class bound -/

/-- **The per-class bound**: the number of candidate coefficient vectors of a
class of discriminant `D` is `≪ D^{(n+2)/4 - 1 + ε}`. -/
theorem goodVec_ncard_le_classDisc (n : ℕ) (hn : 3 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (H : ℕ) (hn1 : 1 ≤ n) (q : Quotient (fieldIsoSetoid n H hn1)),
      ((GoodVec n (classDisc n H hn1 q)).ncard : ℝ)
        ≤ K * (classDisc n H hn1 q : ℝ) ^ (((n : ℝ) + 2) / 4 - 1 + ε) := by
  obtain ⟨K₀, hK₀, hbound⟩ := goodVec_ncard_le n hn ε hε
  set S : ℕ := primorial n ^ (n + n * Nat.log 2 n) with hS
  refine ⟨K₀ * S, by positivity, ?_⟩
  intro H hn1 q
  set D : ℕ := classDisc n H hn1 q with hD
  have hD1 : 1 ≤ D := by rw [hD]; exact one_le_classDisc n H hn1 q
  have hDne : D ≠ 0 := Nat.one_le_iff_ne_zero.mp hD1
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
  have hDspos : (0 : ℝ) < (discLargePart n D : ℝ) := by
    have h : 0 < discLargePart n D := discLargePart_pos n D
    exact_mod_cast h
  have hsq : ∀ p : ℕ, Nat.Prime p → p ∣ D → p ^ 2 ∣ D := by
    intro p hp hpd
    rw [hD] at hpd ⊢
    exact squarefull_classDisc n H hn1 (by omega) q p hp hpd
  have hv : ∀ p : ℕ, Nat.Prime p → n < p → p ∣ D → D.factorization p ≤ n - 1 := by
    intro p hp hpn hpd
    rw [hD] at hpd ⊢
    exact factorization_classDisc_le n H hn1 (by omega) q hp hpn hpd
  have hb := hbound D hD1 hv hsq
  have hsmall : discSmallPart n D ≤ S := by
    rw [hS, hD]; exact discSmallPart_classDisc_le n H hn1 (by omega) q
  have hsplit : (D : ℝ) = (discLargePart n D : ℝ) * (discSmallPart n D : ℝ) := by
    rw [← Nat.cast_mul, discSplit n D hDne]
  have hkey : (D : ℝ) ^ (((n : ℝ) + 2) / 4 + ε) / (discLargePart n D : ℝ)
      = (D : ℝ) ^ (((n : ℝ) + 2) / 4 - 1 + ε) * (discSmallPart n D : ℝ) := by
    have h1 : (D : ℝ) ^ (((n : ℝ) + 2) / 4 + ε)
        = (D : ℝ) ^ (((n : ℝ) + 2) / 4 - 1 + ε) * (D : ℝ) := by
      rw [show ((n : ℝ) + 2) / 4 + ε = (((n : ℝ) + 2) / 4 - 1 + ε) + 1 by ring,
        Real.rpow_add hDpos, Real.rpow_one]
    rw [h1, hsplit]
    have hne : (discLargePart n D : ℝ) ≠ 0 := ne_of_gt hDspos
    field_simp
  have hcastS : ((S : ℕ) : ℝ) = (S : ℝ) := rfl
  calc ((GoodVec n D).ncard : ℝ)
      ≤ K₀ * (D : ℝ) ^ (((n : ℝ) + 2) / 4 + ε) / (discLargePart n D : ℝ) := hb
    _ = K₀ * ((D : ℝ) ^ (((n : ℝ) + 2) / 4 - 1 + ε) * (discSmallPart n D : ℝ)) := by
        rw [mul_div_assoc, hkey]
    _ ≤ K₀ * ((D : ℝ) ^ (((n : ℝ) + 2) / 4 - 1 + ε) * (S : ℝ)) := by
        have hle : (discSmallPart n D : ℝ) ≤ (S : ℝ) := by exact_mod_cast hsmall
        have hnn : (0 : ℝ) ≤ (D : ℝ) ^ (((n : ℝ) + 2) / 4 - 1 + ε) := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hnn) hK₀
    _ = (K₀ * S) * (D : ℝ) ^ (((n : ℝ) + 2) / 4 - 1 + ε) := by ring

/-! ## 3. The field count -/

/-- **Freeze the initial segment.**  The quantifier over the exponent in the
target `(n : ℝ) / 4 + ε` and the coefficient bound are those of
`goodVec_ncard_le_classDisc`. -/
theorem fieldCountBound_index (n : ℕ) (hn1 : 1 ≤ n) (hn : 3 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    FieldCountBound n hn1 ((n : ℝ) / 4 + ε) := by
  classical
  obtain ⟨K, hK, hclass⟩ := goodVec_ncard_le_classDisc n hn ε hε
  obtain ⟨Cs, hCs, hsq⟩ := Commons.NumberTheory.Nat.ncard_squarefull_le_sqrt
  set S : ℕ := primorial n ^ (n + n * Nat.log 2 n) with hS
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by
    have hpos : 0 < primorial n := by
      rw [primorial]
      exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
    have hS1n : 1 ≤ S := by
      rw [hS]
      exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (pow_pos hpos _))
    exact_mod_cast hS1n
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set c : ℝ := ((n : ℝ) + 2) / 4 - 1 + ε with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  refine ⟨2 * Cs * (K * (S : ℝ)), by positivity, ?_⟩
  intro H Y hY
  haveI hFp : Fintype ↥(SubcaseI_P2 n H) :=
    ((box_finite n H).subset (subcaseI_P2_subset_Box n H)).fintype
  haveI hFq : Fintype (Quotient (fieldIsoSetoid n H hn1)) := Quotient.fintype _
  set Ts : Finset ℕ := (Finset.univ.image (classDisc n H hn1)).filter (fun D => D ≤ Y) with hTs
  have hmaps : Set.MapsTo (fun a : {q : Quotient (fieldIsoSetoid n H hn1) //
        classDisc n H hn1 q ≤ Y} => classDisc n H hn1 a.1)
      (↑(Finset.univ : Finset {q : Quotient (fieldIsoSetoid n H hn1) //
        classDisc n H hn1 q ≤ Y})) (↑Ts) := by
    intro a _
    rw [hTs]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨a.1, Finset.mem_univ _, rfl⟩, a.2⟩
  have hstep1 : ∀ D ∈ Ts,
      ((Finset.univ.filter (fun a : {q : Quotient (fieldIsoSetoid n H hn1) //
        classDisc n H hn1 q ≤ Y} => classDisc n H hn1 a.1 = D)).card : ℝ)
      ≤ K * (S : ℝ) * (D : ℝ) ^ c := by
    intro D hD
    have hDmem : D ∈ (Finset.univ.image (classDisc n H hn1)).filter (fun x => x ≤ Y) :=
      hTs ▸ hD
    obtain ⟨hDimg, hDY⟩ := Finset.mem_filter.mp hDmem
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hDimg
    have h1 : (Finset.univ.filter (fun a : {q : Quotient (fieldIsoSetoid n H hn1) //
          classDisc n H hn1 q ≤ Y} => classDisc n H hn1 a.1 = D)).card
        ≤ Nat.card {q : Quotient (fieldIsoSetoid n H hn1) // classDisc n H hn1 q = D} := by
      rw [← Fintype.card_subtype (fun a : {q : Quotient (fieldIsoSetoid n H hn1) //
          classDisc n H hn1 q ≤ Y} => classDisc n H hn1 a.1 = D)]
      rw [← Nat.card_eq_fintype_card]
      refine Nat.card_le_card_of_injective
        (fun a : {a : {q : Quotient (fieldIsoSetoid n H hn1) //
            classDisc n H hn1 q ≤ Y} // classDisc n H hn1 a.1 = D} =>
          (⟨a.1.1, a.2⟩ : {q : Quotient (fieldIsoSetoid n H hn1) //
            classDisc n H hn1 q = D})) ?_
      intro a b hab
      have h1 : a.1.1 = b.1.1 :=
        congrArg (fun x : {q : Quotient (fieldIsoSetoid n H hn1) //
          classDisc n H hn1 q = D} => (x : Quotient (fieldIsoSetoid n H hn1))) hab
      exact Subtype.ext (Subtype.ext h1)
    have h2 : Nat.card {q : Quotient (fieldIsoSetoid n H hn1) // classDisc n H hn1 q = D}
        ≤ (GoodVec n D).ncard := classCount_le_goodVec n H hn1 (by omega) D
    have h3 : ((GoodVec n D).ncard : ℝ) ≤ K * (D : ℝ) ^ c := by
      rw [hc, ← hq]
      exact hclass H hn1 q
    have hDc : (0 : ℝ) ≤ (D : ℝ) ^ c := by positivity
    have h4 : K * (D : ℝ) ^ c ≤ K * (S : ℝ) * (D : ℝ) ^ c := by
      have hKS : K ≤ K * (S : ℝ) := by
        calc K = K * 1 := by ring
          _ ≤ K * (S : ℝ) := mul_le_mul_of_nonneg_left hS1 hK
      exact mul_le_mul_of_nonneg_right hKS hDc
    calc ((Finset.univ.filter (fun a : {q : Quotient (fieldIsoSetoid n H hn1) //
          classDisc n H hn1 q ≤ Y} => classDisc n H hn1 a.1 = D)).card : ℝ)
        ≤ (Nat.card {q : Quotient (fieldIsoSetoid n H hn1) //
            classDisc n H hn1 q = D} : ℝ) := by exact_mod_cast h1
      _ ≤ ((GoodVec n D).ncard : ℝ) := by exact_mod_cast h2
      _ ≤ K * (D : ℝ) ^ c := h3
      _ ≤ K * (S : ℝ) * (D : ℝ) ^ c := h4
  have hTscard : (Ts.card : ℝ) ≤ Cs * (Real.sqrt (Y : ℝ) + 1) := by
    have hsub : (Ts : Set ℕ)
        ⊆ {N : ℕ | 1 ≤ N ∧ N ≤ Y ∧ ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N} := by
      intro N hN
      rw [hTs] at hN
      obtain ⟨hNimg, hNY⟩ := Finset.mem_filter.mp hN
      obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hNimg
      subst hq
      exact ⟨one_le_classDisc n H hn1 q, hNY,
        fun p hp hpd => squarefull_classDisc n H hn1 (by omega) q p hp hpd⟩
    have hfin : ({N : ℕ | 1 ≤ N ∧ N ≤ Y ∧ ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N} : Set ℕ).Finite :=
      (Set.finite_Iic Y).subset (fun N hN => hN.2.1)
    have h := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at h
    exact le_trans (by exact_mod_cast h) (hsq Y)
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hYpos : (0 : ℝ) < (Y : ℝ) := by linarith
  have hB : (Nat.card {q : Quotient (fieldIsoSetoid n H hn1) // classDisc n H hn1 q ≤ Y} : ℝ)
      ≤ (Ts.card : ℝ) * (K * (S : ℝ) * (Y : ℝ) ^ c) := by
    have h1 : ((Nat.card {q : Quotient (fieldIsoSetoid n H hn1) //
        classDisc n H hn1 q ≤ Y} : ℕ) : ℝ)
        ≤ ∑ D ∈ Ts, K * (S : ℝ) * (D : ℝ) ^ c := by
      rw [Nat.card_eq_fintype_card,
        ← Finset.card_univ (α := {q : Quotient (fieldIsoSetoid n H hn1) //
          classDisc n H hn1 q ≤ Y}),
        Finset.card_eq_sum_card_fiberwise hmaps]
      push_cast
      exact Finset.sum_le_sum hstep1
    have h2 : ∑ D ∈ Ts, K * (S : ℝ) * (D : ℝ) ^ c
        ≤ ∑ D ∈ Ts, K * (S : ℝ) * (Y : ℝ) ^ c := by
      refine Finset.sum_le_sum (fun D hD => ?_)
      have hDmem : D ∈ (Finset.univ.image (classDisc n H hn1)).filter (fun x => x ≤ Y) :=
        hTs ▸ hD
      have hDY : D ≤ Y := (Finset.mem_filter.mp hDmem).2
      have hDc : (D : ℝ) ^ c ≤ (Y : ℝ) ^ c :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hDY) (le_of_lt hc0)
      exact mul_le_mul_of_nonneg_left hDc (by positivity)
    have h3 : ∑ D ∈ Ts, K * (S : ℝ) * (Y : ℝ) ^ c
        = (Ts.card : ℝ) * (K * (S : ℝ) * (Y : ℝ) ^ c) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    linarith [h1, h2, h3]
  have hsqrt : (Real.sqrt (Y : ℝ) + 1) ≤ 2 * (Y : ℝ) ^ (1 / 2 : ℝ) := by
    have h1 : (1 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact (Real.one_le_sqrt).mpr hY1
    rw [Real.sqrt_eq_rpow]
    linarith
  have hsplit : (Y : ℝ) ^ (1 / 2 : ℝ) * (Y : ℝ) ^ c = (Y : ℝ) ^ ((n : ℝ) / 4 + ε) := by
    rw [← Real.rpow_add hYpos]
    congr 1
    rw [hc]
    ring
  have hmain : (Ts.card : ℝ) * (K * (S : ℝ) * (Y : ℝ) ^ c)
      ≤ (2 * Cs * (K * (S : ℝ))) * (Y : ℝ) ^ ((n : ℝ) / 4 + ε) := by
    have hCs0 : (0 : ℝ) ≤ Cs := le_of_lt hCs
    have h1 : (Ts.card : ℝ) ≤ Cs * (2 * (Y : ℝ) ^ (1 / 2 : ℝ)) :=
      le_trans hTscard (mul_le_mul_of_nonneg_left hsqrt hCs0)
    have h2 : (Cs * (2 * (Y : ℝ) ^ (1 / 2 : ℝ))) * (K * (S : ℝ) * (Y : ℝ) ^ c)
        = (2 * Cs * (K * (S : ℝ))) * ((Y : ℝ) ^ (1 / 2 : ℝ) * (Y : ℝ) ^ c) := by ring
    have h3 : (2 * Cs * (K * (S : ℝ))) * ((Y : ℝ) ^ (1 / 2 : ℝ) * (Y : ℝ) ^ c)
        = (2 * Cs * (K * (S : ℝ))) * (Y : ℝ) ^ ((n : ℝ) / 4 + ε) := by
      rw [hsplit]
    calc (Ts.card : ℝ) * (K * (S : ℝ) * (Y : ℝ) ^ c)
        ≤ (Cs * (2 * (Y : ℝ) ^ (1 / 2 : ℝ))) * (K * (S : ℝ) * (Y : ℝ) ^ c) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (2 * Cs * (K * (S : ℝ))) * ((Y : ℝ) ^ (1 / 2 : ℝ) * (Y : ℝ) ^ c) := h2
      _ = (2 * Cs * (K * (S : ℝ))) * (Y : ℝ) ^ ((n : ℝ) / 4 + ε) := h3
  exact le_trans hB hmain

/-! ## 4. The exponent conditions and the endpoint -/

lemma weylM_four : weylM 4 = 256 := by norm_num [weylM]

/-- The exponent condition for the index refinement with a slack `ε = 1/20`
and the paper's fibre exponent, `n ≥ 5`. -/
lemma exponent_index_refine_eps (n : ℕ) (hn : 5 ≤ n) :
    1 + (2 + 4 / (weylM n : ℝ)) * ((n : ℝ) / 4 + 1 / 20 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
      < (n : ℝ) - 1 := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hW : (128 : ℝ) ≤ (weylM n : ℝ) := by exact_mod_cast weylM_ge_128 n hn
  have hWpos : (0 : ℝ) < (weylM n : ℝ) := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hinv : 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 / 20 := by
    rw [div_le_div_iff₀ hn2 (by norm_num)]
    nlinarith
  have hcoef : (2 + 4 / (weylM n : ℝ)) ≤ 2 + 1 / 32 := by
    have h1 : 4 / (weylM n : ℝ) ≤ 1 / 32 := by
      rw [div_le_iff₀ hWpos]
      linarith
    linarith
  have hexpr : (n : ℝ) / 4 + 1 / 20 - 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ (n : ℝ) / 4 + 1 / 20 := by
    have h1 : (0 : ℝ) ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
    linarith
  have hnn : (0 : ℝ) ≤ (n : ℝ) / 4 + 1 / 20 - 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) / 4 := by linarith
    linarith
  have h1 : (2 + 4 / (weylM n : ℝ)) * ((n : ℝ) / 4 + 1 / 20 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ (2 + 1 / 32) * ((n : ℝ) / 4 + 1 / 20) := by
    calc (2 + 4 / (weylM n : ℝ)) * ((n : ℝ) / 4 + 1 / 20 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
        ≤ (2 + 1 / 32) * ((n : ℝ) / 4 + 1 / 20 - 1 / ((n : ℝ) * ((n : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_right hcoef hnn
      _ ≤ (2 + 1 / 32) * ((n : ℝ) / 4 + 1 / 20) :=
          mul_le_mul_of_nonneg_left hexpr (by norm_num)
  have h2 : (2 + 1 / 32) * ((n : ℝ) / 4 + 1 / 20) = (65 / 128) * (n : ℝ) + 65 / 640 := by ring
  have h3 : (65 / 128) * (n : ℝ) + 65 / 640 < (n : ℝ) - 2 := by nlinarith
  linarith

/-- The exponent condition in degree `4`. -/
lemma exponent_index_refine_eps_four :
    1 + (2 + 4 / (weylM 4 : ℝ)) * ((4 : ℝ) / 4 + 1 / 20 - 1 / ((4 : ℝ) * ((4 : ℝ) - 1)))
      < (4 : ℝ) - 1 := by
  rw [weylM_four]
  norm_num

/-- The exponent condition for `n = 4, 5` in a form uniform in `n`. -/
lemma exponent_index_refine_eps_four_five (n : ℕ) (hn : 4 ≤ n) (hn5 : n ≤ 5) :
    1 + (2 + 4 / (weylM n : ℝ)) * ((n : ℝ) / 4 + 1 / 20 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
      < (n : ℝ) - 1 := by
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    exact exponent_index_refine_eps_four
  · exact exponent_index_refine_eps n h

/-- The fibre exponent is below the refined field-count exponent for `n ≥ 4`. -/
lemma fibre_lt_index (n : ℕ) (hn : 4 ≤ n) :
    1 / ((n : ℝ) * ((n : ℝ) - 1)) < (n : ℝ) / 4 + 1 / 20 := by
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have h1 : 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 := by
    rw [div_le_one hn2]
    nlinarith
  have h2 : (1 : ℝ) ≤ (n : ℝ) / 4 + 1 / 20 := by linarith
  linarith

/-- **The challenge theorem from the index-refined field count** (plus the
imprimitive bound): for every `n ≥ 4` with an imprimitive bound of the required
strength. -/
theorem theorem_1_of_indexRefined (n : ℕ) (hn : 4 ≤ n)
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hfib : PerFieldFibreBoundExp n (by omega : 1 ≤ n)
      (1 / ((n : ℝ) * ((n : ℝ) - 1))) :=
    perFieldFibreBound_exp_classical n (by omega) (perFieldFibreBound_all n (by omega))
  have hSC : FieldCountBound n (by omega : 1 ≤ n) ((n : ℝ) / 4 + 1 / 20) :=
    fieldCountBound_index n (by omega) (by omega) (1 / 20) (by norm_num)
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    exact theorem_1_of_field_inputs_exp 4 (by omega) ((4 : ℝ) / 4 + 1 / 20)
      (1 / ((4 : ℝ) * ((4 : ℝ) - 1))) (by norm_num) exponent_index_refine_eps_four hfib hSC h4
  · exact theorem_1_of_field_inputs_exp n (by omega) ((n : ℝ) / 4 + 1 / 20)
      (1 / ((n : ℝ) * ((n : ℝ) - 1))) (fibre_lt_index n hn) (exponent_index_refine_eps n h)
      hfib hSC h4

/-- **The challenge theorem for `n = 4, 5` from the index refinement alone** —
neither Davenport–Heilbronn nor Bhargava is needed; the imprimitive input is
the machine-checked `ImprimitiveBad_four_isBigO` for `n = 4` and vacuous for
the prime `n = 5`. -/
theorem theorem_1_of_indexRefined_four_five (n : ℕ) (hn : 4 ≤ n) (hn5 : n ≤ 5) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    exact theorem_1_of_indexRefined 4 (by omega) (by simpa using ImprimitiveBad_four_isBigO)
  · have h5 : n = 5 := by omega
    subst h5
    exact theorem_1_of_indexRefined 5 (by omega) (ImprimitiveBad_isBigO_of_prime 5 (by norm_num))

/-- **The challenge theorem for prime `n ≥ 5`** from the index refinement (no
imprimitive input). -/
theorem theorem_1_of_indexRefined_prime (n : ℕ) (hn : 5 ≤ n) (hp : Nat.Prime n) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_indexRefined n (by omega) (ImprimitiveBad_isBigO_of_prime n hp)

/-- **The challenge theorem for composite `n ≥ 6`** from the index refinement
plus Widmer's imprimitive bound. -/
theorem theorem_1_of_indexRefined_widmer (n : ℕ) (hn : 6 ≤ n)
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_indexRefined n (by omega) (ImprimitiveBad_isBigO_of_widmer n hn hw)

end

end Submission.Vdw
