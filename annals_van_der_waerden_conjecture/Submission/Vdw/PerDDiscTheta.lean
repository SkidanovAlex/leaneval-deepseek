import Mathlib
import Submission.Vdw.FourierIndexBound
import Submission.Vdw.PerIrrTheta

open Polynomial Filter Asymptotics
open scoped BigOperators
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The per-discriminant bound from the `δ`-parametrised §4 input

`FourierIndexBound.perDDiscBound_of_perIrrBound_exp` converts the §4
index-condition input `PerIrrBound n c` (threshold `radical D ≤ H^{1+1/(2n)}`)
into the per-discriminant fibre bound.  Here the same proof is run with a
general threshold `δ`, starting from `PerIrrTheta.PerrIrrBoundTheta n δ c`
(the input supplied *unconditionally* at `δ = weylδ n` by
`PerIrrWeyl.perIrrBoundTheta_weyl`).

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw
noncomputable section

/-- **The per-discriminant bound with threshold `δ`** (paper §4, Corollary 33, in
the form used in Case I): the number of box polynomials with field discriminant
exactly `D` is at most `c^ω(D)·H^n/D` for a nonzero squarefull `D` with
`radical D ≤ H^{1+δ}`, all prime divisors `> n` dividing it with exponent `< n`,
and `D > H^{2+2δ}`. -/
def PerDDiscBoundTheta (n : ℕ) (δ : ℝ) (c : ℕ) : Prop :=
  ∀ H D : ℕ, D ≠ 0 → Squarefull D →
    (radical D : ℝ) ≤ (H : ℝ) ^ (1 + δ) →
    (∀ p ∈ D.primeFactors, n < p → D.factorization p < n) →
    (H : ℝ) ^ (2 + 2 * δ) < (D : ℝ) →
    ((Nat.card {f : ↥(Box n H) // ∃ h : Irreducible (f.1.map φℚ),
        fieldDiscExp f.1 h = D} : ℕ) : ℝ) ≤ (c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ)

/-- **The fiber form follows from the index form.**

The constant is `max (c·S₀+1) (S₀·(2S₀+1)^n)` with `S₀ = smallConst n`: the
second entry covers the degenerate regime in which the large-prime part of `D`
is `1` and only the trivial box bound is available. -/
theorem perDDiscBound_of_perIrrBoundTheta (n c : ℕ) (hn : 3 ≤ n) (hc : 1 ≤ c)
    (δ : ℝ) (hδ : -1 < δ) (e : ℝ) (he : 1 ≤ e) (h : PerIrrBoundTheta n δ c) :
    ∀ H D : ℕ, D ≠ 0 → Squarefull D →
      (radical D : ℝ) ≤ (H : ℝ) ^ (1 + δ) →
      (∀ p ∈ D.primeFactors, n < p → D.factorization p < n) →
      (H : ℝ) ^ e < (D : ℝ) →
      ((Nat.card {f : ↥(Box n H) // ∃ h : Irreducible (f.1.map φℚ),
          fieldDiscExp f.1 h = D} : ℕ) : ℝ)
        ≤ (((max (c * smallConst n + 1) (smallConst n * (2 * smallConst n + 1) ^ n) : ℕ) : ℝ))
            ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by
  classical
  intro H D hD0 hsq hrad hfac hlarge
  set c' : ℕ := max (c * smallConst n + 1) (smallConst n * (2 * smallConst n + 1) ^ n) with hc'
  have hcle : c * smallConst n + 1 ≤ c' := le_max_left _ _
  have hScle : smallConst n * (2 * smallConst n + 1) ^ n ≤ c' := le_max_right _ _
  have hsR : (1 : ℝ) ≤ (smallConst n : ℝ) := by exact_mod_cast smallConst_pos n
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  -- `H ≥ 1`: otherwise `H^(1+δ) = 0 < 1 ≤ radical D`
  have hHge1 : 1 ≤ H := by
    have hru : radical D ≠ 0 := by
      rw [radical_eq_prod_primeFactors]
      exact Finset.prod_ne_zero_iff.mpr
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
    have h1 : (1 : ℝ) ≤ (radical D : ℝ) := by
      have h2 : 1 ≤ radical D := Nat.one_le_iff_ne_zero.mpr hru
      exact_mod_cast h2
    have h3 : (1 : ℝ) ≤ (H : ℝ) ^ (1 + δ) := le_trans h1 hrad
    rcases Nat.eq_zero_or_pos H with h0 | hpos
    · exfalso
      rw [h0, Nat.cast_zero, Real.zero_rpow (by linarith : (1:ℝ) + δ ≠ 0)] at h3
      linarith
    · exact hpos
  by_cases homega : omega D = 0
  · -- impossible: `D = 1` contradicts `rad D ≤ H^(1+δ)` together with `H^(2+δ) < D`
    exfalso
    have hD1 : D = 1 := eq_one_of_omega_eq_zero hD0 homega
    subst hD1
    simp only [radical, Nat.primeFactors_one, Finset.prod_empty] at hrad
    rcases Nat.eq_zero_or_pos H with hH | hH
    · subst hH
      have hz : (((0 : ℕ) : ℝ) ^ (1 + δ)) = 0 := by
        rw [Nat.cast_zero]
        exact Real.zero_rpow (by linarith : (1:ℝ) + δ ≠ 0)
      rw [hz] at hrad
      norm_num at hrad
    · have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
      have h2 : (1 : ℝ) ≤ (H : ℝ) ^ e := by
        calc (1 : ℝ) = (1 : ℝ) ^ e := (Real.one_rpow _).symm
          _ ≤ (H : ℝ) ^ e :=
              Real.rpow_le_rpow (by norm_num) hHR (by linarith)
      simp only [Nat.cast_one] at hlarge
      linarith
  · have homega1 : 1 ≤ omega D := Nat.one_le_iff_ne_zero.mpr homega
    by_cases hsmall : discSmallPart n D ≤ smallConst n
    · set Ds : ℕ := discLargePart n D with hDs
      have hDs0 : Ds ≠ 0 := discLargePart_ne_zero n D hD0
      by_cases hDs2 : 2 ≤ Ds
      · -- main case: reduce to the large-prime part
        have hsqs : Squarefull Ds := squarefull_discLargePart n D hD0 hsq
        have hgt : ∀ p ∈ Ds.primeFactors, n < p :=
          fun p hp => (mem_primeFactors_discLargePart hD0 hp).1
        have hrads : (radical Ds : ℝ) ≤ (H : ℝ) ^ (1 + δ) := by
          have h1 : radical Ds ≤ radical D :=
            radical_le_of_dvd (discLargePart_dvd n D hD0) hD0
          exact le_trans (by exact_mod_cast h1) hrad
        have hfacs : ∀ p ∈ Ds.primeFactors, Ds.factorization p < n := by
          intro p hp
          have hpD := mem_primeFactors_discLargePart hD0 hp
          have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
          have hmem : p ∈ D.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpD.2, hD0⟩
          have h1 : D.factorization p < n := hfac p hmem hpD.1
          have h2 : Ds.factorization p = D.factorization p :=
            (factorization_discLargePart hD0 hp).symm
          rwa [h2]
        have hsieve := h H Ds hDs0 hsqs hDs2 hgt hrads hfacs
        -- the fiber is contained in the index-condition set of `Ds`
        have hpoint : ∀ f : ↥(Box n H), (∃ h : Irreducible (f.1.map φℚ),
              fieldDiscExp f.1 h = D) →
            (∀ p : Ds.primeFactors, indexClass (F := ZMod (p : ℕ)) n
              (Ds.factorization (p : ℕ)) (boxResidue n H (p : ℕ) f)) := by
          intro f hf p
          obtain ⟨hirr, hfeq⟩ := hf
          haveI : Fact (Irreducible (f.1.map φℚ)) := ⟨hirr⟩
          have hmon : f.1.Monic := f.2.1
          have hdeg : f.1.natDegree = n :=
            Polynomial.natDegree_eq_of_degree_eq_some f.2.2.1
          have hfeq' : fieldDisc f.1 = D := hfeq
          have hpD := mem_primeFactors_discLargePart hD0 p.2
          have hpp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
          haveI : Fact (Nat.Prime (p : ℕ)) := ⟨hpp⟩
          have h1 := restrictedSieve_entry f.1 hmon hdeg (show 1 ≤ n by omega) hpD.1
            (hfeq'.symm ▸ hpD.2)
          have h2 : (Ds.factorization (p : ℕ)) ≤ boxIndex (p : ℕ) n H f := by
            have hDse : Ds.factorization (p : ℕ) = D.factorization (p : ℕ) :=
              (factorization_discLargePart hD0 p.2).symm
            have hDfac : D.factorization (p : ℕ) = (fieldDisc f.1).factorization (p : ℕ) := by
              rw [hfeq']
            rw [hDse, hDfac]
            simpa [boxIndex, reductionPoly] using h1
          exact (boxIndex_iff_indexClass (p : ℕ) n H (Ds.factorization (p : ℕ)) f).mp h2
        have hcard : Nat.card {f : ↥(Box n H) //
              ∃ h : Irreducible (f.1.map φℚ), fieldDiscExp f.1 h = D}
            ≤ Nat.card {f : ↥(Box n H) // ∀ p : Ds.primeFactors,
                indexClass (F := ZMod (p : ℕ)) n (Ds.factorization (p : ℕ))
                  (boxResidue n H (p : ℕ) f)} :=
          Nat.card_le_card_of_injective
            (fun f : {f : ↥(Box n H) // ∃ h : Irreducible (f.1.map φℚ),
                  fieldDiscExp f.1 h = D} =>
              (⟨f.1, hpoint f.1 f.2⟩ :
                {f : ↥(Box n H) // ∀ p : Ds.primeFactors,
                    indexClass (F := ZMod (p : ℕ)) n (Ds.factorization (p : ℕ))
                      (boxResidue n H (p : ℕ) f)}))
            (fun f g hfg => by
              have h1 : (f : ↥(Box n H)) = (g : ↥(Box n H)) :=
                congrArg (fun x : {f : ↥(Box n H) // ∀ p : Ds.primeFactors,
                    indexClass (F := ZMod (p : ℕ)) n (Ds.factorization (p : ℕ))
                      (boxResidue n H (p : ℕ) f)} => (x : ↥(Box n H))) hfg
              exact Subtype.ext h1)
        -- constants: `Ds = D / discSmallPart n D`
        have hDspos : (0 : ℝ) < (Ds : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hDs0
        have hsmallpos : 0 < discSmallPart n D := by
          rw [show discSmallPart n D
              = ∏ p ∈ (Nat.primeFactors D).filter (fun p => p ≤ n), p ^ D.factorization p
              from rfl]
          exact Finset.prod_pos (fun p hp =>
            pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _)
        have hDsratio : ((H : ℝ) ^ n / (Ds : ℝ))
            ≤ (smallConst n : ℝ) * ((H : ℝ) ^ n / (D : ℝ)) := by
          have hDval : (D : ℝ) = (Ds : ℝ) * (discSmallPart n D : ℝ) := by
            exact_mod_cast (discSplit n D hD0).symm
          have hsne : (discSmallPart n D : ℝ) ≠ 0 := by
            exact_mod_cast hsmallpos.ne'
          have heq : (discSmallPart n D : ℝ) * ((H : ℝ) ^ n / (D : ℝ))
              = (H : ℝ) ^ n / (Ds : ℝ) := by
            rw [hDval]
            field_simp
          rw [← heq]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsmall)
            (div_nonneg (pow_nonneg (Nat.cast_nonneg H) _) hDpos.le)
        have hpow : (c : ℝ) ^ omega Ds ≤ (c : ℝ) ^ omega D := by
          have hsub : Ds.primeFactors ⊆ D.primeFactors :=
            primeFactors_subset_of_dvd (discLargePart_dvd n D hD0) hD0
          exact pow_le_pow_right₀ (by exact_mod_cast hc) (Finset.card_le_card hsub)
        have hconst : (c : ℝ) ^ omega D * (smallConst n : ℝ) ≤ (c' : ℝ) ^ omega D := by
          have h1 : (smallConst n : ℝ) ≤ (smallConst n : ℝ) ^ omega D :=
            le_self_pow₀ hsR (Nat.one_le_iff_ne_zero.mp homega1)
          calc (c : ℝ) ^ omega D * (smallConst n : ℝ)
              ≤ (c : ℝ) ^ omega D * (smallConst n : ℝ) ^ omega D :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = ((c : ℝ) * (smallConst n : ℝ)) ^ omega D := (mul_pow _ _ _).symm
            _ ≤ (c * smallConst n + 1 : ℕ) ^ omega D :=
                pow_le_pow_left₀ (by positivity) (by
                  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
                  linarith) (omega D)
            _ ≤ (c' : ℝ) ^ omega D :=
                pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcle) (omega D)
        have hbound : ((c : ℝ) ^ omega Ds * (H : ℝ) ^ n / (Ds : ℝ))
            ≤ (c' : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by
          calc (c : ℝ) ^ omega Ds * (H : ℝ) ^ n / (Ds : ℝ)
              = (c : ℝ) ^ omega Ds * ((H : ℝ) ^ n / (Ds : ℝ)) := by ring
            _ ≤ (c : ℝ) ^ omega D * ((smallConst n : ℝ) * ((H : ℝ) ^ n / (D : ℝ))) :=
                mul_le_mul hpow hDsratio
                  (div_nonneg (pow_nonneg (Nat.cast_nonneg H) _) hDspos.le)
                  (pow_nonneg (Nat.cast_nonneg c) _)
            _ = ((c : ℝ) ^ omega D * (smallConst n : ℝ)) * ((H : ℝ) ^ n / (D : ℝ)) := by ring
            _ ≤ (c' : ℝ) ^ omega D * ((H : ℝ) ^ n / (D : ℝ)) :=
                mul_le_mul_of_nonneg_right hconst (by positivity)
            _ = (c' : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by ring
        calc (((Nat.card {f : ↥(Box n H) // ∃ h : Irreducible (f.1.map φℚ),
                fieldDiscExp f.1 h = D} : ℕ) : ℝ))
            ≤ ((Nat.card {f : ↥(Box n H) // ∀ p : Ds.primeFactors,
                indexClass (F := ZMod (p : ℕ)) n (Ds.factorization (p : ℕ))
                  (boxResidue n H (p : ℕ) f)} : ℕ) : ℝ) := by exact_mod_cast hcard
          _ ≤ (c : ℝ) ^ omega Ds * (H : ℝ) ^ n / (Ds : ℝ) := hsieve
          _ ≤ (c' : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := hbound
      · -- degenerate case `Ds = 1`: `D ≤ S₀` and `H ≤ S₀`, so the trivial box
        -- bound suffices with the constant `S₀·(2S₀+1)^n`
        have hDs1 : Ds = 1 := by omega
        have hDle : D ≤ smallConst n := by
          have hsplit : Ds * discSmallPart n D = D := discSplit n D hD0
          rw [hDs1, one_mul] at hsplit
          omega
        have hHleS : H ≤ smallConst n := by
          have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHge1
          have h2 : (H : ℝ) ≤ (H : ℝ) ^ e := by
            calc (H : ℝ) = (H : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
              _ ≤ (H : ℝ) ^ e :=
                  Real.rpow_le_rpow_of_exponent_le hH1 he
          have h3 : (H : ℝ) < (smallConst n : ℝ) :=
            lt_of_le_of_lt h2 (lt_of_lt_of_le hlarge (by exact_mod_cast hDle))
          have h4 : H < smallConst n := by exact_mod_cast h3
          omega
        have hcount : Nat.card {f : ↥(Box n H) // ∃ h : Irreducible (f.1.map φℚ),
              fieldDiscExp f.1 h = D} ≤ (2 * smallConst n + 1) ^ n := by
          have h1 : Nat.card {f : ↥(Box n H) // ∃ h : Irreducible (f.1.map φℚ),
                fieldDiscExp f.1 h = D} ≤ Nat.card ↥(Box n H) :=
            Nat.card_le_card_of_injective (fun x => x.1) (fun a b hab => Subtype.ext hab)
          have h2 : Nat.card ↥(Box n H) = (2 * H + 1) ^ n := by
            rw [← Commons.Data.Set.ncard_eq_natCard (Box n H), Box_ncard_eq]
          have h3 : (2 * H + 1) ^ n ≤ (2 * smallConst n + 1) ^ n :=
            Nat.pow_le_pow_left (by omega) n
          omega
        have hc'ge2 : (smallConst n : ℝ) * (((2 * smallConst n + 1) ^ n : ℕ) : ℝ)
            ≤ (c' : ℝ) := by exact_mod_cast hScle
        have hc'1 : (1 : ℝ) ≤ (c' : ℝ) := by
          have h2 : (1 : ℝ) ≤ (((2 * smallConst n + 1) ^ n : ℕ) : ℝ) := by
            have h2n : (1 : ℕ) ≤ (2 * smallConst n + 1) ^ n :=
              one_le_pow₀ (by have := smallConst_pos n; omega)
            exact_mod_cast h2n
          nlinarith [hsR, h2, hc'ge2]
        have hSR : (0 : ℝ) < (smallConst n : ℝ) := by exact_mod_cast smallConst_pos n
        have h1 : (((2 * smallConst n + 1) ^ n : ℕ) : ℝ) ≤ (c' : ℝ) / (smallConst n : ℝ) := by
          rw [le_div_iff₀ hSR]
          linarith [hc'ge2]
        have h2 : (c' : ℝ) / (smallConst n : ℝ)
            ≤ (c' : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by
          have hp : (c' : ℝ) ≤ (c' : ℝ) ^ omega D :=
            le_self_pow₀ hc'1 (Nat.one_le_iff_ne_zero.mp homega1)
          have hHn : (1 : ℝ) ≤ (H : ℝ) ^ n := one_le_pow₀ (by exact_mod_cast hHge1)
          have hDleR : (D : ℝ) ≤ (smallConst n : ℝ) := by exact_mod_cast hDle
          have hc'nn : (0 : ℝ) ≤ (c' : ℝ) := le_trans zero_le_one hc'1
          rw [div_le_div_iff₀ hSR hDpos]
          calc (c' : ℝ) * (D : ℝ) ≤ (c' : ℝ) * (smallConst n : ℝ) :=
                mul_le_mul_of_nonneg_left hDleR hc'nn
            _ ≤ (c' : ℝ) ^ omega D * (smallConst n : ℝ) :=
                mul_le_mul_of_nonneg_right hp hSR.le
            _ ≤ (c' : ℝ) ^ omega D * (H : ℝ) ^ n * (smallConst n : ℝ) := by
                have h0 : (0 : ℝ) ≤ (c' : ℝ) ^ omega D := by positivity
                have h1 : (smallConst n : ℝ) ≤ (H : ℝ) ^ n * (smallConst n : ℝ) := by
                  nlinarith [hHn, hSR]
                calc (c' : ℝ) ^ omega D * (smallConst n : ℝ)
                    ≤ (c' : ℝ) ^ omega D * ((H : ℝ) ^ n * (smallConst n : ℝ)) :=
                      mul_le_mul_of_nonneg_left h1 h0
                  _ = (c' : ℝ) ^ omega D * (H : ℝ) ^ n * (smallConst n : ℝ) := by ring
        calc (((Nat.card {f : ↥(Box n H) // ∃ h : Irreducible (f.1.map φℚ),
                fieldDiscExp f.1 h = D} : ℕ) : ℝ))
            ≤ (((2 * smallConst n + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast hcount
          _ ≤ (c' : ℝ) / (smallConst n : ℝ) := h1
          _ ≤ (c' : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := h2
    · -- empty fiber: a real `D_f` has small part `≤ S₀`
      push_neg at hsmall
      have hemp : IsEmpty {f : ↥(Box n H) //
          ∃ h : Irreducible (f.1.map φℚ), fieldDiscExp f.1 h = D} := ⟨fun f => by
        obtain ⟨hirr, hfeq⟩ := f.2
        haveI : Fact (Irreducible ((f.1 : ℤ[X]).map φℚ)) := ⟨hirr⟩
        have hmon : (f.1 : ℤ[X]).Monic := f.1.2.1
        have hdeg : (f.1 : ℤ[X]).natDegree = n :=
          Polynomial.natDegree_eq_of_degree_eq_some f.1.2.2.1
        have h1 : discSmallPart n (fieldDisc (f.1 : ℤ[X])) ≤ smallConst n :=
          discSmallPart_fieldDisc_le (f.1 : ℤ[X]) hmon n hdeg
        have hfeq' : fieldDisc (f.1 : ℤ[X]) = D := hfeq
        rw [hfeq'] at h1
        omega⟩
      have hzero : Nat.card {f : ↥(Box n H) //
          ∃ h : Irreducible (f.1.map φℚ), fieldDiscExp f.1 h = D} = 0 := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_eq_zero
      rw [hzero]
      simp only [Nat.cast_zero]
      apply div_nonneg
      · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg c') _)
          (pow_nonneg (Nat.cast_nonneg H) _)
      · exact Nat.cast_nonneg D

/-- **The fiber form of the index-condition input at the paper's exponent**
(`2 + 2δ = 2 + 1/n`): `perDDiscBound_of_perIrrBound_exp` specialised to
`e = 2 + 1/n`. -/
theorem perDDiscBoundTheta_of_perIrrBoundTheta (n c : ℕ) (hn : 3 ≤ n) (hc : 1 ≤ c)
    (δ : ℝ) (hδ : -1 < δ) (hδ0 : 0 ≤ δ) (h : PerIrrBoundTheta n δ c) :
    PerDDiscBoundTheta n δ
      (max (c * smallConst n + 1) (smallConst n * (2 * smallConst n + 1) ^ n)) :=
  perDDiscBound_of_perIrrBoundTheta n c hn hc δ hδ (2 + 2 * δ)
    (by linarith)
    h


end
end Submission.Vdw
