import Mathlib
import Submission.Vdw.CaseIIClasses
import Submission.Vdw.FourierIndexBound
import Submission.Vdw.RadicalSq
import Submission.Vdw.CaseIFourier
import Submission.Vdw.CaseITail
import Submission.Vdw.CaseIRestricted
import Submission.Vdw.PrimitiveCase
import Submission.Vdw.FourierDequi
import Submission.Commons.Analysis.Sum.exists_sum_rpow_neg_le_of_card_le_fintype
import Submission.Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Case II at a *small* `D`-threshold: the paper's `δ` bookkeeping made explicit

The project's thresholds are those of the paper with `δ = 1/(2n)`.  The
Case-II computation (Schmidt + Lemke Oliver–Thorne + Abel summation) then
requires

    `1 + (2+2δ)·(β - 1/(n(n-1)))`  with  `2 + 2δ = 2 + 1/n`

to be `< n - 1`, which fails for `n = 4, 5` (with the exact-count exponent
`β = 1`) and for `n = 6` (`β = (n+2)/4 = 2`).  The paper's "say `δ = 1/(2n)`"
is a loose choice: the Case-I Fourier input only needs `δ < 1/(2n-1)`, so one
may take an *absolute* small `δ`, e.g. `δ' = 1/100` (`2 + 2δ' = 2.02`), and
then the Case-II computation succeeds for every `n ≥ 4`:

    `n = 4` (`β = 1`):    `1 + 2.02·(1 - 1/12) = 2.851 < 3`,
    `n = 5` (`β = 1`):    `1 + 2.02·(1 - 1/20) = 2.919 < 4`,
    `n = 6` (`β = 2`):    `1 + 2.02·(2 - 1/30) = 4.973 < 5`,
    `n ≥ 7`:               `1 + 2.02·((n+2)/4 - 1/(n(n-1))) < n - 1`.

This module implements that route.  The price is that the `D`-threshold drops
from `H^{2+1/n}` to `H^{2+ε}` (`ε = 2δ' = 1/50`), so the Case-II region is
enlarged and the *complement* `{H^{2+ε} < D_f ≤ H^{2+1/n}}` (the "slab") must be
handled separately — by the Fourier input `PerIrrBound` at the exponent
`e = 2 + ε` (`FourierIndexBound.perDDiscBound_of_perIrrBound_exp`) plus the
squarefull tail (`CaseITail.squarefull_tail_bound`), which loses exactly
`H^{ε/2}` — see `caseIIslab_isBigO` below.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **The Case-II region at the smaller threshold `H^{2+ε}`** (the paper's
Case II with the absolute small `δ' = ε/2`). -/
def SubcaseI_P2eps (n H : ℕ) (ε : ℝ) : Set ℤ[X] :=
  {f | f ∈ SubcaseI n H ∧ ∃ h : Irreducible (f.map φℚ),
      (fieldDiscExp f h : ℝ) ≤ (H : ℝ) ^ (2 + ε)}

/-- The smaller-threshold region sits inside the project's Case-II region
(equivalently: the class machinery of `CaseIIClasses` applies to it). -/
theorem subcaseI_P2eps_subset_P2 {n H : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hn : 1 ≤ n)
    (hε : ε ≤ 1 / (n : ℝ)) :
    SubcaseI_P2eps n H ε ⊆ SubcaseI_P2 n H := by
  intro f hf
  obtain ⟨h1, h, hle⟩ := hf
  refine ⟨h1, h, ?_⟩
  rcases Nat.eq_zero_or_pos H with hH | hH
  · subst hH
    have h1 : ((0 : ℕ) : ℝ) ^ (2 + ε) = 0 := by
      rw [Nat.cast_zero]
      exact Real.zero_rpow (by linarith)
    have h1' : (fieldDiscExp f h : ℝ) ≤ 0 := by
      rw [h1] at hle
      exact hle
    rw [Nat.cast_zero]
    have h2 : (0 : ℝ) ^ (2 + 1 / (n : ℝ)) = 0 := Real.zero_rpow (by positivity)
    rw [h2]
    exact h1'
  · have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hexp : 2 + ε ≤ 2 + 1 / (n : ℝ) := by
      have h1 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      linarith
    exact le_trans hle (Real.rpow_le_rpow_of_exponent_le hH1 hexp)

/-- `Finset`-cardinality of a decidable predicate as a `Nat.card` of the
corresponding subtype. -/
theorem card_filter_eq_natCard {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = Nat.card {x : α // P x} := by
  rw [← Fintype.card_subtype P]
  exact (Nat.card_eq_fintype_card).symm

/-- **Case II at the small threshold, from Schmidt + Lemke Oliver–Thorne**
(Abel-refined form, i.e. with the per-field weights `|Disc|^{-1/(n(n-1))}`
performing the summation). -/
theorem subcaseI_P2eps_isBigO (n : ℕ) (hn : 4 ≤ n) (hn1 : 1 ≤ n) (ε : ℝ) (hε0 : 0 < ε)
    (hεn : ε ≤ 1 / (n : ℝ))
    (β : ℝ) (hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < β)
    (hexp : 1 + (2 + ε) * (β - 1 / ((n : ℝ) * ((n : ℝ) - 1))) < (n : ℝ) - 1)
    (hLOT : PerFieldFibreBound n hn1)
    (hSC : FieldCountBound n hn1 β) :
    (fun H : ℕ => ((SubcaseI_P2eps n H ε).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  obtain ⟨C₁, hC₁, hLOTb⟩ := hLOT
  obtain ⟨c₂, hc₂, hSCb⟩ := hSC
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  obtain ⟨C₂, hC₂, hdyad⟩ :=
    Commons.Analysis.Sum.exists_sum_rpow_neg_le_of_card_le_fintype
      (1 / ((n : ℝ) * ((n : ℝ) - 1))) β hβ
  set γ : ℝ := β - 1 / ((n : ℝ) * ((n : ℝ) - 1)) with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  set κ : ℝ := 1 + (2 + ε) * γ with hκ
  have hκlt : κ < (n : ℝ) - 1 := by rw [hκ, hγ]; exact hexp
  set δ : ℝ := ((n : ℝ) - 1 - κ) / 2 with hδ
  have hδpos : 0 < δ := by
    have h1 := hδ
    linarith
  have hlog : ∀ᶠ H : ℕ in atTop,
      (Real.log (H : ℝ)) ^ (n - 1) ≤ (H : ℝ) ^ δ := by
    have h1 := Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow (n - 1) 1 δ hδpos
    filter_upwards [h1, eventually_ge_atTop (1 : ℕ)] with H hH hH1
    have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    have h2 : (Real.log (H : ℝ)) ^ (n - 1) ≤ (1 + Real.log (H : ℝ)) ^ (n - 1) :=
      pow_le_pow_left₀ (Real.log_nonneg hH1R) (by linarith) (n - 1)
    calc (Real.log (H : ℝ)) ^ (n - 1) ≤ (1 + Real.log (H : ℝ)) ^ (n - 1) := h2
      _ ≤ (H : ℝ) ^ δ := by simpa using hH
  have hpoint : ∀ᶠ H : ℕ in atTop,
      ((SubcaseI_P2eps n H ε).ncard : ℝ)
        ≤ C₁ * C₂ * c₂ * 2 ^ γ * (H : ℝ) ^ ((n : ℝ) - 1) := by
    filter_upwards [hlog, eventually_ge_atTop (1 : ℕ)] with H hlogH hH1
    have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hH1R
    haveI : Fintype ↥(SubcaseI_P2 n H) :=
      ((box_finite n H).subset (subcaseI_P2_subset_Box n H)).fintype
    haveI : Fintype (Quotient (fieldIsoSetoid n H hn1)) := Quotient.fintype _
    set s : Setoid ↥(SubcaseI_P2 n H) := fieldIsoSetoid n H hn1 with hs
    set X : ℕ := Nat.ceil ((H : ℝ) ^ (2 + ε)) with hX
    have hsub : SubcaseI_P2eps n H ε ⊆ SubcaseI_P2 n H :=
      subcaseI_P2eps_subset_P2 hε0 hn1 hεn
    haveI : Fintype ↥(SubcaseI_P2eps n H ε) :=
      ((box_finite n H).subset (fun f hf => subcaseI_P2_subset_Box n H (hsub hf))).fintype
    -- (1) the region's count is the sum of its own class fibres, which inject
    -- into the full fibres of the classes with `classDisc ≤ X`
    have hcard1 : Nat.card ↥(SubcaseI_P2eps n H ε)
        ≤ ∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X)),
            Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} := by
      have heq : Nat.card ↥(SubcaseI_P2eps n H ε)
          = ∑ q : Quotient s, Nat.card {f : ↥(SubcaseI_P2eps n H ε) //
              Quotient.mk s ⟨f.1, hsub f.2⟩ = q} := by
        have h2 := Nat.card_congr (Equiv.sigmaFiberEquiv
          (fun f : ↥(SubcaseI_P2eps n H ε) => Quotient.mk s ⟨f.1, hsub f.2⟩))
        rw [Nat.card_sigma] at h2
        exact h2.symm
      rw [heq]
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ)
        (fun q : Quotient s => classDisc n H hn1 q ≤ X)
        (fun q => Nat.card {f : ↥(SubcaseI_P2eps n H ε) //
              Quotient.mk s ⟨f.1, hsub f.2⟩ = q})]
      have hzero : ∑ q ∈ Finset.univ.filter (fun q : Quotient s => ¬ classDisc n H hn1 q ≤ X),
          Nat.card {f : ↥(SubcaseI_P2eps n H ε) // Quotient.mk s ⟨f.1, hsub f.2⟩ = q} = 0 := by
        refine Finset.sum_eq_zero (fun q hq => ?_)
        rw [Finset.mem_filter] at hq
        rw [Nat.card_eq_fintype_card]
        haveI : IsEmpty {f : ↥(SubcaseI_P2eps n H ε) //
            Quotient.mk s ⟨f.1, hsub f.2⟩ = q} :=
          ⟨fun f => by
            have hdisc : subcaseI_P2_disc n H ⟨f.1.1, hsub f.1.2⟩ ≤ X := by
              obtain ⟨h1, h, h2⟩ := f.1.2
              have h3 : subcaseI_P2_disc n H ⟨f.1.1, hsub f.1.2⟩ = fieldDiscExp f.1.1 h := rfl
              rw [h3, hX]
              exact_mod_cast le_trans h2 (Nat.le_ceil _)
            have hcls : classDisc n H hn1 q = subcaseI_P2_disc n H ⟨f.1.1, hsub f.1.2⟩ := by
              have h1 := congrArg (fun x => classDisc n H hn1 x) f.2
              rw [classDisc_mk n H hn1 ⟨f.1.1, hsub f.1.2⟩] at h1
              exact h1.symm
            omega⟩
        exact Fintype.card_eq_zero
      rw [hzero, add_zero]
      refine Finset.sum_le_sum (fun q _ => ?_)
      refine Nat.card_le_card_of_injective
        (fun f : {f : ↥(SubcaseI_P2eps n H ε) // Quotient.mk s ⟨f.1, hsub f.2⟩ = q} =>
          (⟨⟨f.1.1, hsub f.1.2⟩, f.2⟩ : {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q})) ?_
      intro a b hab
      exact Subtype.ext (Subtype.ext
        (congrArg (fun x => (x.1.1 : ℤ[X])) hab))
    -- (2) Lemke Oliver–Thorne for each class
    have hcard2 : (∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X)),
          ((Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} : ℕ) : ℝ))
        ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
            * (∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X)),
                (classDisc n H hn1 q : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1))))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun q _ => ?_)
      simpa only [mul_assoc] using hLOTb H q
    -- (3) the class sum by dyadic summation (Schmidt's count)
    let F : Finset (Quotient s) := Finset.univ.filter (fun q => classDisc n H hn1 q ≤ X)
    have hcount_nat : ∀ Y : ℕ,
        Nat.card {i : {q : Quotient s // q ∈ F} // classDisc n H hn1 i.1 ≤ Y}
          ≤ Nat.card {q : Quotient s // classDisc n H hn1 q ≤ Y} := by
      intro Y
      refine Nat.card_le_card_of_injective
        (fun i : {i : {q : Quotient s // q ∈ F} // classDisc n H hn1 i.1 ≤ Y} =>
          (⟨i.1.1, i.2⟩ : {q : Quotient s // classDisc n H hn1 q ≤ Y})) ?_
      intro a b hab
      have h1 : (a.1.1 : Quotient s) = b.1.1 :=
        congr_arg (fun x : {q : Quotient s // classDisc n H hn1 q ≤ Y} => (x : Quotient s)) hab
      exact Subtype.ext (Subtype.ext h1)
    have hcount : ∀ Y : ℕ, ((Finset.univ.filter (fun i : {q : Quotient s // q ∈ F} =>
          classDisc n H hn1 i.1 ≤ Y)).card : ℝ) ≤ c₂ * (Y : ℝ) ^ β := by
      intro Y
      rw [card_filter_eq_natCard]
      rcases Y with _ | Y
      · have hden : (0 : ℝ) < 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
          have hn2 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
          have h2 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
          positivity
        have hemp : Nat.card {i : {q : Quotient s // q ∈ F} // classDisc n H hn1 i.1 ≤ 0} = 0 := by
          rw [Nat.card_eq_fintype_card]
          haveI : IsEmpty {i : {q : Quotient s // q ∈ F} // classDisc n H hn1 i.1 ≤ 0} :=
            ⟨fun i => by
              have h3 := one_le_classDisc n H hn1 i.1.1
              have h4 := i.2
              omega⟩
          exact Fintype.card_eq_zero
        rw [hemp, Nat.cast_zero, Real.zero_rpow (ne_of_gt (lt_trans hden hβ)), mul_zero]
      · exact le_trans (by exact_mod_cast hcount_nat (Y + 1)) (hSCb H (Y + 1) (by omega))
    have hsum : (∑ i : {q : Quotient s // q ∈ F},
          (classDisc n H hn1 i.1 : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1)))))
        ≤ C₂ * c₂ * (X : ℝ) ^ γ := by
      have h1 := hdyad (fun i : {q : Quotient s // q ∈ F} => classDisc n H hn1 i.1) c₂ X
        hc₂ (by
          rw [hX]
          have h2 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + ε) :=
            Real.one_le_rpow hH1R (by positivity)
          exact le_trans h2 (Nat.le_ceil _))
        (fun i => one_le_classDisc n H hn1 i.1)
        (fun i => by
          have hmem : classDisc n H hn1 i.1 ≤ X := by
            have h2 : i.1 ∈ Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X) := i.2
            exact (Finset.mem_filter.mp h2).2
          exact_mod_cast hmem)
        hcount
      rwa [hγ] at h1
    -- (4) assemble
    have hattach : (∑ q ∈ F,
          (classDisc n H hn1 q : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1)))))
        = ∑ i : {q : Quotient s // q ∈ F},
          (classDisc n H hn1 i.1 : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1)))) :=
      (Finset.sum_attach _ _).symm
    have hXle : (X : ℝ) ≤ 2 * (H : ℝ) ^ (2 + ε) := by
      have h1 : (X : ℝ) < (H : ℝ) ^ (2 + ε) + 1 := by
        rw [hX]; exact Nat.ceil_lt_add_one (by positivity)
      have h2 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + ε) := Real.one_le_rpow hH1R (by positivity)
      linarith
    have hXpow : (X : ℝ) ^ γ ≤ 2 ^ γ * (H : ℝ) ^ ((2 + ε) * γ) := by
      calc (X : ℝ) ^ γ ≤ (2 * (H : ℝ) ^ (2 + ε)) ^ γ :=
            Real.rpow_le_rpow (by positivity) hXle hγ0.le
        _ = 2 ^ γ * ((H : ℝ) ^ (2 + ε)) ^ γ := Real.mul_rpow (by norm_num) (by positivity)
        _ = 2 ^ γ * (H : ℝ) ^ ((2 + ε) * γ) := by rw [Real.rpow_mul hHpos.le]
    have hrwadd : (H : ℝ) * (H : ℝ) ^ ((2 + ε) * γ) = (H : ℝ) ^ κ := by
      have h1 : (H : ℝ) * (H : ℝ) ^ ((2 + ε) * γ)
          = (H : ℝ) ^ (1 : ℝ) * (H : ℝ) ^ ((2 + ε) * γ) := by rw [Real.rpow_one]
      rw [h1, (Real.rpow_add hHpos 1 _).symm]
    have hexp2 : κ + δ ≤ (n : ℝ) - 1 := by
      have h1 := hδ
      linarith
    calc ((SubcaseI_P2eps n H ε).ncard : ℝ)
        ≤ ((∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X)),
            Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q}) : ℝ) := by
          exact_mod_cast hcard1
      _ = ∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X)),
            ((Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} : ℕ) : ℝ) := rfl
      _ ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
            * (∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X)),
                (classDisc n H hn1 q : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1))))) := hcard2
      _ = C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
            * (∑ i : {q : Quotient s // q ∈
                (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X))},
              (classDisc n H hn1 i.1 : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1))))) := by
          rw [hattach]
      _ ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (C₂ * c₂ * (X : ℝ) ^ γ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
            * (C₂ * c₂ * (2 ^ γ * (H : ℝ) ^ ((2 + ε) * γ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXpow (by positivity))
            (by positivity)
      _ = C₁ * C₂ * c₂ * 2 ^ γ * ((H : ℝ) * (H : ℝ) ^ ((2 + ε) * γ)
            * (Real.log (H : ℝ)) ^ (n - 1)) := by ring
      _ = C₁ * C₂ * c₂ * 2 ^ γ * ((H : ℝ) ^ κ * (Real.log (H : ℝ)) ^ (n - 1)) := by
          rw [hrwadd]
      _ ≤ C₁ * C₂ * c₂ * 2 ^ γ * ((H : ℝ) ^ κ * (H : ℝ) ^ δ) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogH (by positivity))
            (by positivity)
      _ = C₁ * C₂ * c₂ * 2 ^ γ * (H : ℝ) ^ (κ + δ) := by rw [← Real.rpow_add hHpos]
      _ ≤ C₁ * C₂ * c₂ * 2 ^ γ * (H : ℝ) ^ ((n : ℝ) - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hH1R hexp2
  refine IsBigO.of_bound (max (C₁ * C₂ * c₂ * 2 ^ γ) 0) ?_
  filter_upwards [hpoint] with H hH
  have hgoal : ((H : ℕ) ^ (n - 1) : ℝ) = (H : ℝ) ^ ((n : ℝ) - 1) := by
    rw [← Real.rpow_natCast (H : ℝ) (n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity), hgoal]
  refine le_trans hH ?_
  have : (0 : ℝ) ≤ C₁ * C₂ * c₂ * 2 ^ γ := by positivity
  rw [max_eq_left this]

def CaseIIslab (n H : ℕ) (ε : ℝ) : Set ℤ[X] :=
  {f | f ∈ SubcaseI_P2 n H ∧ ∃ h : Irreducible (f.map φℚ),
      (H : ℝ) ^ (2 + ε) < (fieldDiscExp f h : ℝ)}

/-- The candidate discriminants of the slab. -/
noncomputable def slabIndex (n H : ℕ) (ε : ℝ) : Finset ℕ :=
  (((Finset.Icc (Nat.floor ((H : ℝ) ^ (2 + ε)) + 1)
      (Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ))))).filter Squarefull).filter
    (fun D => ∀ p ∈ D.primeFactors, n < p → D.factorization p < n))

/-- The slab at the box level, with the irreducibility witness exposed. -/
def slabBox (n H : ℕ) (ε : ℝ) : Set ↥(Box n H) :=
  {f | ∃ h : Irreducible (f.1.map φℚ),
      Squarefull (fieldDiscExp f.1 h) ∧
      (H : ℝ) ^ (2 + ε) < (fieldDiscExp f.1 h : ℝ) ∧
      (fieldDiscExp f.1 h : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ))}

-- does proof irrelevance make the witnesses collapse?
example (f : ℤ[X]) (h1 h2 : Irreducible (f.map φℚ)) : fieldDiscExp f h1 = fieldDiscExp f h2 := rfl

/-- Region membership: a slab member's field discriminant lies in `slabIndex`. -/
theorem slabBox_subset_biUnion (n H : ℕ) (ε : ℝ) (hn : 1 ≤ n) :
    slabBox n H ε ⊆
      {f : ↥(Box n H) | ∃ D ∈ slabIndex n H ε, f ∈ fiberAt n H D} := by
  classical
  intro f hf
  obtain ⟨h, hsq, hgt, hle⟩ := hf
  refine ⟨fieldDiscExp f.1 h, ?_, h, rfl⟩
  haveI : Fact (Irreducible (f.1.map φℚ)) := ⟨h⟩
  have hmon : f.1.Monic := f.2.1
  have hdeg : f.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some f.2.2.1
  rw [slabIndex, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨⟨?_, ?_⟩, hsq⟩, ?_⟩
  · have hlt : Nat.floor ((H : ℝ) ^ (2 + ε)) < fieldDiscExp f.1 h := by
      have h1 : ((Nat.floor ((H : ℝ) ^ (2 + ε)) : ℕ) : ℝ) ≤ (H : ℝ) ^ (2 + ε) :=
        Nat.floor_le (by positivity)
      have h2 : ((Nat.floor ((H : ℝ) ^ (2 + ε)) : ℕ) : ℝ)
          < ((fieldDiscExp f.1 h : ℕ) : ℝ) := lt_of_le_of_lt h1 hgt
      exact_mod_cast h2
    omega
  · exact Nat.le_floor hle
  · intro p hp hpgt
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    haveI : Fact (Nat.Prime p) := ⟨hpp⟩
    have hpD : p ∣ fieldDisc f.1 := by
      simpa [fieldDiscExp] using (Nat.mem_primeFactors.mp hp).2.1
    have hlt := fieldDisc_factorization_lt_of_prime_gt n H hn f.1 hmon hdeg f.2 hpgt hpD
    simpa [fieldDiscExp] using hlt

open Classical in
/-- **The slab at the box level is counted by the per-discriminant sum.** -/
theorem slabBox_ncard_le_sum (n H c : ℕ) (hn : 3 ≤ n) (hc : 1 ≤ c) (ε : ℝ) (hε : 0 < ε)
    (hper : PerIrrBound n c) :
    ((slabBox n H ε).ncard : ℝ) ≤
      ∑ D ∈ slabIndex n H ε,
        (((max (c * smallConst n + 1) (smallConst n * (2 * smallConst n + 1) ^ n) : ℕ) : ℝ))
            ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by
  classical
  haveI : Finite ↥(Box n H) := box_finite n H
  have hfin : ({f : ↥(Box n H) | ∃ D ∈ slabIndex n H ε, f ∈ fiberAt n H D}).Finite :=
    Set.toFinite _
  have h1 : (slabBox n H ε).ncard ≤
      ({f : ↥(Box n H) | ∃ D ∈ slabIndex n H ε, f ∈ fiberAt n H D}).ncard :=
    Set.ncard_le_ncard (slabBox_subset_biUnion n H ε (by omega)) hfin
  have h2 := ncard_biUnion_finset_le (slabIndex n H ε) (fiberAt n H)
  have h3 : ∀ D ∈ slabIndex n H ε, ((fiberAt n H D).ncard : ℝ) ≤
      (((max (c * smallConst n + 1) (smallConst n * (2 * smallConst n + 1) ^ n) : ℕ) : ℝ))
        ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by
    intro D hD
    rw [slabIndex, Finset.mem_filter, Finset.mem_filter] at hD
    obtain ⟨⟨hDIcc, hDsq⟩, hDfac⟩ := hD
    have hD0 : D ≠ 0 := by
      have := (Finset.mem_Icc.mp hDIcc).1
      omega
    have hDle : D ≤ Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ))) := (Finset.mem_Icc.mp hDIcc).2
    -- the radical bound
    have hDrad : (radical D : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := by
      have hsqr : (radical D) ^ 2 ≤ D := radical_sq_le_of_squarefull D hD0 hDsq
      have h2 : ((radical D : ℝ)) ^ 2 ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
        have h3 : ((radical D : ℝ)) ^ 2 ≤ (D : ℝ) := by
          exact_mod_cast hsqr
        have h4a : (D : ℝ) ≤ ((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ))) : ℕ) : ℝ) := by
          exact_mod_cast hDle
        have h4b : ((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ))) : ℕ) : ℝ)
            ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) := Nat.floor_le (by positivity)
        linarith
      have h5 : (radical D : ℝ) ≤ Real.sqrt ((H : ℝ) ^ (2 + 1 / (n : ℝ))) :=
        (Real.le_sqrt (by positivity) (by positivity)).mpr h2
      have h6 : Real.sqrt ((H : ℝ) ^ (2 + 1 / (n : ℝ))) = (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg H)]
        congr 1
        field_simp
      rwa [h6] at h5
    -- the strict lower bound
    have hDgt : (H : ℝ) ^ (2 + ε) < (D : ℝ) := by
      have h1 : (H : ℝ) ^ (2 + ε) < (Nat.floor ((H : ℝ) ^ (2 + ε)) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h2 : (Nat.floor ((H : ℝ) ^ (2 + ε)) + 1 : ℕ) ≤ D := (Finset.mem_Icc.mp hDIcc).1
      have h3 : ((Nat.floor ((H : ℝ) ^ (2 + ε)) : ℕ) : ℝ) + 1 ≤ (D : ℝ) := by
        exact_mod_cast h2
      linarith
    have hcard : (fiberAt n H D).ncard = Nat.card {f : ↥(Box n H) //
        ∃ h : Irreducible (f.1.map φℚ), fieldDiscExp f.1 h = D} :=
      (Nat.card_coe_set_eq _).symm
    rw [hcard]
    exact perDDiscBound_of_perIrrBound_exp n c hn hc (2 + ε) (by linarith) hper
      H D hD0 hDsq hDrad hDfac hDgt
  have hcast : ((slabBox n H ε).ncard : ℝ) ≤
      ((∑ D ∈ slabIndex n H ε, (fiberAt n H D).ncard : ℕ) : ℝ) := by
    exact_mod_cast le_trans h1 h2
  calc ((slabBox n H ε).ncard : ℝ)
      ≤ ((∑ D ∈ slabIndex n H ε, (fiberAt n H D).ncard : ℕ) : ℝ) := hcast
    _ = ∑ D ∈ slabIndex n H ε, ((fiberAt n H D).ncard : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ D ∈ slabIndex n H ε,
          (((max (c * smallConst n + 1)
            (smallConst n * (2 * smallConst n + 1) ^ n) : ℕ) : ℝ))
            ^ omega D * (H : ℝ) ^ n / (D : ℝ) := Finset.sum_le_sum h3

open Classical in
/-- **The per-discriminant sum over `slabIndex` is bounded by the squarefull
tail.** -/
theorem slabIndex_sum_le_tail (n H : ℕ) (hn : 3 ≤ n) (c : ℕ) (hc : 1 ≤ c) (ε : ℝ)
    (hY1 : 1 ≤ Nat.floor ((H : ℝ) ^ (2 + ε)))
    (hYZ : Nat.floor ((H : ℝ) ^ (2 + ε))
      < Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) :
    ∑ D ∈ slabIndex n H ε, (c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) ≤
      (c : ℝ) * (H : ℝ) ^ n *
        ((1 + Real.log (((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) : ℝ)) ^ (2 * c) /
          (((Nat.floor ((H : ℝ) ^ (2 + ε)) : ℕ) : ℝ)) ^ ((1 : ℝ) / 2)) := by
  classical
  have htail := squarefull_tail_bound c hc ((1 : ℝ) / 2) (by norm_num) le_rfl
    (Nat.floor ((H : ℝ) ^ (2 + ε))) (Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) hY1 hYZ
  have hsub : slabIndex n H ε ⊆
      Finset.Icc (Nat.floor ((H : ℝ) ^ (2 + ε)) + 1)
        (Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) := by
    intro D hD
    rw [slabIndex, Finset.mem_filter, Finset.mem_filter] at hD
    exact hD.1.1
  have hsqmem : ∀ D ∈ slabIndex n H ε, Squarefull D := by
    intro D hD
    rw [slabIndex, Finset.mem_filter, Finset.mem_filter] at hD
    exact hD.1.2
  have hsum1 : ∑ D ∈ slabIndex n H ε, (c : ℝ) ^ omega D / (D : ℝ) ≤
      ∑ D ∈ Finset.Icc (Nat.floor ((H : ℝ) ^ (2 + ε)) + 1)
        (Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))),
        (if Squarefull D then (c : ℝ) ^ omega D / (D : ℝ) else 0) := by
    calc ∑ D ∈ slabIndex n H ε, (c : ℝ) ^ omega D / (D : ℝ)
        = ∑ D ∈ slabIndex n H ε,
            (if Squarefull D then (c : ℝ) ^ omega D / (D : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun D hD => ?_)
          simp [hsqmem D hD]
      _ ≤ ∑ D ∈ Finset.Icc (Nat.floor ((H : ℝ) ^ (2 + ε)) + 1)
            (Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))),
            (if Squarefull D then (c : ℝ) ^ omega D / (D : ℝ) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D hDt hDs => ?_)
          by_cases hsq : Squarefull D
          · simp only [hsq, if_true]
            have hD0 : (0 : ℝ) < (D : ℝ) := by
              have := (Finset.mem_Icc.mp hDt).1
              exact_mod_cast (by omega : 0 < D)
            positivity
          · simp [hsq]
  have hfactor : ∑ D ∈ slabIndex n H ε, ((c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ)) =
      (H : ℝ) ^ n * (∑ D ∈ slabIndex n H ε, (c : ℝ) ^ omega D / (D : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun D _ => by ring)
  rw [hfactor]
  refine le_trans (mul_le_mul_of_nonneg_left hsum1 (by positivity)) ?_
  refine le_trans (mul_le_mul_of_nonneg_left htail (by positivity)) ?_
  rw [mul_assoc]
  exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast hc)

open Classical in
/-- **Log absorption for the slab threshold** `Z = ⌊H^(2+1/n)⌋`. -/
lemma eventually_slab_log (n : ℕ) (hn : 3 ≤ n) (ε : ℝ) (hε0 : 0 < ε) (K : ℕ) :
    ∀ᶠ H : ℕ in atTop,
      (1 + Real.log (((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) : ℝ)) ^ K
        ≤ (H : ℝ) ^ (ε / 8) := by
  have hZm : ∀ᶠ H : ℕ in atTop,
      Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ))) ≤ caseICap n H := by
    have hcap : ∀ᶠ H : ℕ in atTop,
        (H : ℝ) ^ (2 + 1 / (n : ℝ)) ≤ (caseICap n H : ℝ) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH
      have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
      have hpow : (H : ℝ) ^ (2 + 1 / (n : ℝ))
          ≤ (H : ℝ) ^ (((2 * n - 1 : ℕ)) : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hH1 ?_
        have h2n : (((2 * n - 1 : ℕ)) : ℝ) = 2 * (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
          push_cast
          ring
        rw [h2n]
        have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
        have h1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hnpos]; linarith
        linarith
      have hnat : H ^ (2 * n - 1) ≤ caseICap n H := by
        simp only [caseICap]
        calc H ^ (2 * n - 1) ≤ (n * (H + 1)) ^ (2 * n - 1) :=
              Nat.pow_le_pow_left (by nlinarith [Nat.zero_le H]) _
          _ = 1 * (n * (H + 1)) ^ (2 * n - 1) := (one_mul _).symm
          _ ≤ (2 * n - 1).factorial * (n * (H + 1)) ^ (2 * n - 1) :=
              Nat.mul_le_mul_right _ (by have := Nat.factorial_pos (2 * n - 1); omega)
      have hcap2 : (H : ℝ) ^ (((2 * n - 1 : ℕ)) : ℝ) ≤ (caseICap n H : ℝ) := by
        rw [Real.rpow_natCast]
        exact_mod_cast hnat
      exact le_trans hpow hcap2
    filter_upwards [hcap] with H hH
    have h1 : ((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ))) : ℕ) : ℝ)
        ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) := Nat.floor_le (by positivity)
    exact_mod_cast le_trans h1 hH
  have hpow := Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow K 1 (ε / 16)
    (by linarith)
  have hconst : ∀ᶠ H : ℕ in atTop,
      (((4 * n ^ 2 : ℕ) : ℝ) + 1) ^ K ≤ (H : ℝ) ^ (ε / 16) :=
    Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by linarith)
  have hcap : ∀ᶠ H : ℕ in atTop, caseICap n H ≤ H ^ (4 * n ^ 2) := by
    filter_upwards [Commons.Data.Nat.eventually_heightCap_le_pow n (by omega)] with H hH
    simpa only [caseICap] using hH
  have hge1 : ∀ᶠ H : ℕ in atTop, (1 : ℝ) ≤ (H : ℝ) :=
    (eventually_ge_atTop (1 : ℕ)).mono (fun H h => by exact_mod_cast h)
  filter_upwards [hpow, hconst, hcap, hge1, hZm] with H hpow hconst hcap hge1 hZm
  have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hge1
  have hZ1 : 1 ≤ Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ))) := by
    refine Nat.le_floor ?_
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h : (1 : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) :=
      Real.one_le_rpow hge1 (by positivity : (0 : ℝ) ≤ 2 + 1 / (n : ℝ))
    simpa using h
  have hZpos : (0 : ℝ) < ((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℝ) := by
    exact_mod_cast (by omega : 0 < Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ))))
  have hcappos : (0 : ℝ) < (caseICap n H : ℝ) := by
    have hnat : 0 < caseICap n H := by
      simp only [caseICap]
      exact Nat.mul_pos (Nat.factorial_pos _)
        (pow_pos (Nat.mul_pos (by omega : 0 < n) (by omega : 0 < H + 1)) _)
    exact_mod_cast hnat
  have hlogZ : Real.log (((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) : ℝ)
      ≤ ((4 * n ^ 2 : ℕ) : ℝ) * Real.log (H : ℝ) := by
    have hpos : (0 : ℝ) < ((H : ℝ) ^ (4 * n ^ 2)) := by positivity
    calc Real.log (((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) : ℝ)
        ≤ Real.log (caseICap n H : ℝ) :=
          Real.log_le_log hZpos (by exact_mod_cast hZm)
      _ ≤ Real.log ((H : ℝ) ^ (4 * n ^ 2)) :=
          Real.log_le_log hcappos (by exact_mod_cast hcap)
      _ = ((4 * n ^ 2 : ℕ) : ℝ) * Real.log (H : ℝ) := Real.log_pow _ _
  have hlogH0 : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg hge1
  have hstep : 1 + Real.log (((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) : ℝ)
      ≤ (((4 * n ^ 2 : ℕ) : ℝ) + 1) * (1 + Real.log (H : ℝ)) := by
    have hc : (0 : ℝ) ≤ ((4 * n ^ 2 : ℕ) : ℝ) := by positivity
    nlinarith [hlogZ, hlogH0]
  have hpow' : (1 + Real.log ((H : ℝ) ^ 1)) ^ K ≤ (H : ℝ) ^ (ε / 16) := hpow
  rw [pow_one] at hpow'
  calc (1 + Real.log (((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) : ℝ)) ^ K
      ≤ ((((4 * n ^ 2 : ℕ) : ℝ) + 1) * (1 + Real.log (H : ℝ))) ^ K :=
        pow_le_pow_left₀ (by positivity) hstep _
    _ = (((4 * n ^ 2 : ℕ) : ℝ) + 1) ^ K * (1 + Real.log (H : ℝ)) ^ K := mul_pow _ _ _
    _ ≤ (H : ℝ) ^ (ε / 16) * (H : ℝ) ^ (ε / 16) :=
        mul_le_mul hconst hpow' (by positivity) (by positivity)
    _ = (H : ℝ) ^ (ε / 8) := by
        rw [← Real.rpow_add hHpos]
        congr 1
        ring

open Classical in
/-- **Counting inclusion**: the polynomial-level slab sits inside the box-level
slab `slabBox`. -/
theorem caseIIslab_ncard_le_slabBox (n H : ℕ) (ε : ℝ) (hn : 1 ≤ n) :
    (CaseIIslab n H ε).ncard ≤ (slabBox n H ε).ncard := by
  classical
  rw [(Nat.card_coe_set_eq (CaseIIslab n H ε)).symm,
    (Nat.card_coe_set_eq (slabBox n H ε)).symm]
  refine Nat.card_le_card_of_injective
    (fun f : {f : ℤ[X] // f ∈ CaseIIslab n H ε} => ?_) ?_
  · have hbox : f.1 ∈ Box n H := subcaseI_P2_subset_Box n H f.2.1
    have hprim : f.1 ∈ PrimitiveBad n H := SubcaseI_subset_PrimitiveBad n H f.2.1.1
    have h : Irreducible (f.1.map φℚ) :=
      (PrimitiveBad_exists_squarefull_fieldDisc n H f.1 hprim).choose
    have hsq : Squarefull (fieldDiscExp f.1 h) :=
      (Classical.choose_spec (PrimitiveBad_exists_squarefull_fieldDisc n H f.1 hprim)).2
    have hle : (fieldDiscExp f.1 h : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) :=
      Classical.choose_spec f.2.1.2
    have hgt : (H : ℝ) ^ (2 + ε) < (fieldDiscExp f.1 h : ℝ) := f.2.2.choose_spec
    exact ⟨⟨f.1, hbox⟩, h, hsq, hgt, hle⟩
  · intro a b hab
    have h1 : ((a.1 : ℤ[X])) = ((b.1 : ℤ[X])) := by
      have := congrArg (fun x : {g : ↥(Box n H) // g ∈ slabBox n H ε} =>
        ((x : ↥(Box n H)) : ℤ[X])) hab
      simpa using this
    exact Subtype.ext h1

open Classical in
/-- **The slab is `O(H^{n-1})` given the §4 Fourier input.** -/
theorem caseIIslab_bound_real (n : ℕ) (hn : 4 ≤ n) (ε : ℝ) (hε0 : 0 < ε)
    (hεn : ε ≤ 1 / (2 * (n : ℝ))) (c : ℕ) (hc : 1 ≤ c) (hper : PerIrrBound n c) :
    ∃ C : ℝ, ∀ᶠ H : ℕ in atTop, ((CaseIIslab n H ε).ncard : ℝ) ≤ C * (H : ℝ) ^ (n - 1) := by
  classical
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  set c' : ℕ := max (c * smallConst n + 1)
      (smallConst n * (2 * smallConst n + 1) ^ n) with hc'_def
  have hc' : 1 ≤ c' := by
    rw [hc'_def]
    have h1 : 1 ≤ c * smallConst n + 1 := Nat.le_add_left 1 _
    omega
  have hY1 : ∀ᶠ H : ℕ in atTop, 1 ≤ Nat.floor ((H : ℝ) ^ (2 + ε)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH
    refine Nat.le_floor ?_
    have h : (1 : ℝ) ≤ (H : ℝ) ^ (2 + ε) :=
      Real.one_le_rpow (by exact_mod_cast hH) (by linarith)
    simpa using h
  have hYZ : ∀ᶠ H : ℕ in atTop,
      Nat.floor ((H : ℝ) ^ (2 + ε)) < Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ))) := by
    have hbig : ∀ᶠ H : ℕ in atTop, (2 : ℝ) ≤ (H : ℝ) ^ (1 / (2 * (n : ℝ))) :=
      Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by positivity)
    filter_upwards [hbig, eventually_ge_atTop (1 : ℕ)] with H hbig hH
    have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hexp : 1 / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) - ε := by
      have : ε ≤ 1 / (2 * (n : ℝ)) := hεn
      have h2 : 1 / (2 * (n : ℝ)) = 1 / (n : ℝ) - 1 / (2 * (n : ℝ)) := by
        field_simp
        norm_num
      rw [h2] at this
      linarith
    have h1 : (H : ℝ) ^ (1 / (2 * (n : ℝ))) ≤ (H : ℝ) ^ (1 / (n : ℝ) - ε) :=
      Real.rpow_le_rpow_of_exponent_le hH1 hexp
    have h2 : (H : ℝ) ^ (2 + 1 / (n : ℝ))
        = (H : ℝ) ^ (2 + ε) * (H : ℝ) ^ (1 / (n : ℝ) - ε) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring
    have h3 : 2 * (H : ℝ) ^ (2 + ε) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
      rw [h2]
      calc 2 * (H : ℝ) ^ (2 + ε) = (H : ℝ) ^ (2 + ε) * 2 := by ring
        _ ≤ (H : ℝ) ^ (2 + ε) * (H : ℝ) ^ (1 / (n : ℝ) - ε) :=
            mul_le_mul_of_nonneg_left (le_trans hbig h1) (by positivity)
    have h4 : (H : ℝ) ^ (2 + ε) + 1 ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
      have h5 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + ε) :=
        Real.one_le_rpow hH1 (by linarith)
      linarith
    have h5 : (Nat.floor ((H : ℝ) ^ (2 + ε)) : ℝ) + 1
        ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
      have h6 : (Nat.floor ((H : ℝ) ^ (2 + ε)) : ℝ) ≤ (H : ℝ) ^ (2 + ε) :=
        Nat.floor_le (by positivity)
      linarith
    have h6 : Nat.floor ((H : ℝ) ^ (2 + ε)) + 1
        ≤ Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ))) := by
      refine Nat.le_floor ?_
      exact_mod_cast h5
    omega
  have hlog : ∀ᶠ H : ℕ in atTop,
      (1 + Real.log (((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) : ℝ)) ^ (2 * c')
        ≤ (H : ℝ) ^ (ε / 8) := eventually_slab_log n hn3 ε hε0 (2 * c')
  have hys : ∀ᶠ H : ℕ in atTop,
      (H : ℝ) ^ (1 + ε / 2) / Real.sqrt 2
        ≤ Real.sqrt (((Nat.floor ((H : ℝ) ^ (2 + ε))) : ℕ) : ℝ) := by
    have hbig : ∀ᶠ H : ℕ in atTop, (2 : ℝ) ≤ (H : ℝ) ^ (2 + ε) :=
      Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by linarith)
    filter_upwards [hbig] with H hbig
    have hfloor : (H : ℝ) ^ (2 + ε) / 2
        ≤ ((Nat.floor ((H : ℝ) ^ (2 + ε))) : ℕ) := by
      have h1 : (H : ℝ) ^ (2 + ε) < ((Nat.floor ((H : ℝ) ^ (2 + ε))) : ℕ) + 1 :=
        Nat.lt_floor_add_one _
      linarith
    have hsqrt : Real.sqrt ((H : ℝ) ^ (2 + ε) / 2)
        ≤ Real.sqrt (((Nat.floor ((H : ℝ) ^ (2 + ε))) : ℕ) : ℝ) := Real.sqrt_le_sqrt hfloor
    have hsqrtH : Real.sqrt ((H : ℝ) ^ (2 + ε)) = (H : ℝ) ^ (1 + ε / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg H)]
      congr 1
      ring
    have heq : Real.sqrt ((H : ℝ) ^ (2 + ε) / 2)
        = (H : ℝ) ^ (1 + ε / 2) / Real.sqrt 2 := by
      rw [Real.sqrt_div (by positivity), hsqrtH]
    rwa [heq] at hsqrt
  refine ⟨(c' : ℝ) * Real.sqrt 2, ?_⟩
  filter_upwards [hY1, hYZ, hlog, hys, eventually_ge_atTop (1 : ℕ)] with H hY1 hYZ hlog hys hH1
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have h3 : ((slabBox n H ε).ncard : ℝ) ≤
      (c' : ℝ) * (H : ℝ) ^ n *
        ((1 + Real.log (((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) : ℝ)) ^ (2 * c') /
          (((Nat.floor ((H : ℝ) ^ (2 + ε)) : ℕ) : ℝ)) ^ ((1 : ℝ) / 2)) :=
    le_trans (slabBox_ncard_le_sum n H c hn3 hc ε hε0 hper)
      (slabIndex_sum_le_tail n H hn3 c' hc' ε hY1 hYZ)
  have hbr : (1 + Real.log (((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) : ℝ)) ^ (2 * c') /
        (((Nat.floor ((H : ℝ) ^ (2 + ε)) : ℕ) : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ (H : ℝ) ^ (ε / 8) / ((H : ℝ) ^ (1 + ε / 2) / Real.sqrt 2) :=
    div_le_div₀ (by positivity) hlog (div_pos (by positivity) (by positivity))
      (by simpa [Real.sqrt_eq_rpow] using hys)
  have heq : (H : ℝ) ^ (ε / 8) / ((H : ℝ) ^ (1 + ε / 2) / Real.sqrt 2)
      = Real.sqrt 2 * (H : ℝ) ^ (-(1 + 3 * ε / 8)) := by
    have ha : (H : ℝ) ^ (1 + ε / 2) ≠ 0 := by positivity
    have hb : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have key : (H : ℝ) ^ (ε / 8) / ((H : ℝ) ^ (1 + ε / 2) / Real.sqrt 2)
        = Real.sqrt 2 * ((H : ℝ) ^ (ε / 8) / (H : ℝ) ^ (1 + ε / 2)) := by
      field_simp
    rw [key, ← Real.rpow_sub hHpos]
    congr 1
    ring_nf
  have hfin : (c' : ℝ) * (H : ℝ) ^ n *
        ((1 + Real.log (((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) : ℝ)) ^ (2 * c') /
          (((Nat.floor ((H : ℝ) ^ (2 + ε)) : ℕ) : ℝ)) ^ ((1 : ℝ) / 2))
      ≤ (c' : ℝ) * Real.sqrt 2 * (H : ℝ) ^ (n - 1) := by
    have hstep1 : (c' : ℝ) * (H : ℝ) ^ n * ((1 + Real.log
            (((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) : ℝ)) ^ (2 * c') /
          (((Nat.floor ((H : ℝ) ^ (2 + ε)) : ℕ) : ℝ)) ^ ((1 : ℝ) / 2))
        ≤ (c' : ℝ) * (H : ℝ) ^ n * (Real.sqrt 2 * (H : ℝ) ^ (-(1 + 3 * ε / 8))) :=
      mul_le_mul_of_nonneg_left (le_trans hbr (le_of_eq heq)) (by positivity)
    have hstep2 : (c' : ℝ) * (H : ℝ) ^ n * (Real.sqrt 2 * (H : ℝ) ^ (-(1 + 3 * ε / 8)))
        = (c' : ℝ) * Real.sqrt 2
          * ((H : ℝ) ^ (n : ℝ) * (H : ℝ) ^ (-(1 + 3 * ε / 8))) := by
      rw [← Real.rpow_natCast (H : ℝ) n]
      ring
    have hstep3 : (c' : ℝ) * Real.sqrt 2
          * ((H : ℝ) ^ (n : ℝ) * (H : ℝ) ^ (-(1 + 3 * ε / 8)))
        = (c' : ℝ) * Real.sqrt 2 * (H : ℝ) ^ ((n : ℝ) + (-(1 + 3 * ε / 8))) := by
      rw [Real.rpow_add hHpos]
    have hstep4 : (H : ℝ) ^ ((n : ℝ) + (-(1 + 3 * ε / 8))) ≤ (H : ℝ) ^ (n - 1) := by
      have hnat : (H : ℝ) ^ (n - 1) = (H : ℝ) ^ ((n : ℝ) - 1) := by
        rw [← Real.rpow_natCast (H : ℝ) (n - 1)]
        congr 1
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      rw [hnat]
      refine Real.rpow_le_rpow_of_exponent_le hH1R ?_
      have hε : (0 : ℝ) ≤ ε := le_of_lt hε0
      linarith
    calc (c' : ℝ) * (H : ℝ) ^ n * ((1 + Real.log
            (((Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) : ℝ)) ^ (2 * c') /
          (((Nat.floor ((H : ℝ) ^ (2 + ε)) : ℕ) : ℝ)) ^ ((1 : ℝ) / 2))
        ≤ (c' : ℝ) * (H : ℝ) ^ n * (Real.sqrt 2 * (H : ℝ) ^ (-(1 + 3 * ε / 8))) := hstep1
      _ = (c' : ℝ) * Real.sqrt 2
          * ((H : ℝ) ^ (n : ℝ) * (H : ℝ) ^ (-(1 + 3 * ε / 8))) := hstep2
      _ = (c' : ℝ) * Real.sqrt 2 * (H : ℝ) ^ ((n : ℝ) + (-(1 + 3 * ε / 8))) := hstep3
      _ ≤ (c' : ℝ) * Real.sqrt 2 * (H : ℝ) ^ (n - 1) :=
          mul_le_mul_of_nonneg_left hstep4 (by positivity)
  have h1 : ((CaseIIslab n H ε).ncard : ℝ) ≤ ((slabBox n H ε).ncard : ℝ) := by
    exact_mod_cast caseIIslab_ncard_le_slabBox n H ε hn1
  exact le_trans (le_trans h1 h3) hfin

open Classical in
/-- **The slab is `O(H^{n-1})` given the §4 Fourier input** (big-O form). -/
theorem caseIIslab_isBigO (n : ℕ) (hn : 4 ≤ n) (ε : ℝ) (hε0 : 0 < ε)
    (hεn : ε ≤ 1 / (2 * (n : ℝ))) (c : ℕ) (hc : 1 ≤ c) (hper : PerIrrBound n c) :
    (fun H : ℕ => ((CaseIIslab n H ε).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨C, hC⟩ := caseIIslab_bound_real n hn ε hε0 hεn c hc hper
  refine (Commons.Analysis.Asymptotics.isBigO_of_eventually_le _ _ ?_).trans
    (Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow (n - 1) (Nat.ceil C)
      (fun H => Nat.ceil C * H ^ (n - 1)) (Eventually.of_forall (fun H => le_rfl)))
  filter_upwards [hC] with H hH
  have h1 : ((CaseIIslab n H ε).ncard : ℝ) ≤ ((Nat.ceil C : ℕ) : ℝ) * (H : ℝ) ^ (n - 1) := by
    refine le_trans hH ?_
    have h2 : C ≤ ((Nat.ceil C : ℕ) : ℝ) := Nat.le_ceil C
    have h3 : (0 : ℝ) ≤ (H : ℝ) ^ (n - 1) := by positivity
    exact mul_le_mul_of_nonneg_right h2 h3
  have h4 : (((Nat.ceil C) * H ^ (n - 1) : ℕ) : ℝ)
      = ((Nat.ceil C : ℕ) : ℝ) * (H : ℝ) ^ (n - 1) := by
    push_cast
    ring
  rw [← h4] at h1
  exact_mod_cast h1

/-- **Cover of the Case-II region** by the small-threshold region and the slab
(the two thresholds `H^(2+ε)` and `H^(2+1/n)` with `ε ≤ 1/n`). -/
theorem SubcaseI_P2_subset_P2eps_union_slab (n H : ℕ) (ε : ℝ) :
    SubcaseI_P2 n H ⊆ SubcaseI_P2eps n H ε ∪ CaseIIslab n H ε := by
  intro f hf
  have hf' := hf
  obtain ⟨hsub, h, hD⟩ := hf
  by_cases hcase : (fieldDiscExp f h : ℝ) ≤ (H : ℝ) ^ (2 + ε)
  · exact Or.inl ⟨hsub, h, hcase⟩
  · push_neg at hcase
    exact Or.inr ⟨hf', h, hcase⟩

/-- **Case II at a small absolute threshold** from Schmidt + Lemke
Oliver–Thorne: whenever the two literature inputs hold at the exponent `β` and
`ε > 0` is small enough that `1 + (2+ε)(β - 1/(n(n-1))) < n - 1`, the Case-II
region is `O(H^(n-1))`. -/
theorem subcaseI_P2_isBigO_of_literature_eps (n : ℕ) (hn : 4 ≤ n) (ε : ℝ) (hε0 : 0 < ε)
    (hεn : ε ≤ 1 / (2 * (n : ℝ)))
    (β : ℝ) (hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < β)
    (hexp : 1 + (2 + ε) * (β - 1 / ((n : ℝ) * ((n : ℝ) - 1))) < (n : ℝ) - 1)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) β)
    (c : ℕ) (hc : 1 ≤ c) (hper : PerIrrBound n c) :
    (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hεn' : ε ≤ 1 / (n : ℝ) := by
    refine le_trans hεn ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hA := subcaseI_P2eps_isBigO n hn hn1 ε hε0 hεn' β hβ hexp hLOT hSC
  have hB := caseIIslab_isBigO n hn ε hε0 hεn c hc hper
  refine (isBigO_of_eventually_le_real (Eventually.of_forall (fun H => Nat.cast_nonneg _))
    (Eventually.of_forall (fun H => by positivity)) ?_).trans (hA.add hB)
  refine Eventually.of_forall (fun H => ?_)
  have hfin : (SubcaseI_P2eps n H ε ∪ CaseIIslab n H ε).Finite :=
    (box_finite n H).subset (fun f hf => hf.elim
      (fun h => Bad_subset_Box n H (irreducibleBad_subset_Bad n H
        (SubcaseI_subset_PrimitiveBad n H h.1).1))
      (fun h => subcaseI_P2_subset_Box n H h.1))
  have h1 := Set.ncard_le_ncard (SubcaseI_P2_subset_P2eps_union_slab n H ε) hfin
  have h2 := Set.ncard_union_le (SubcaseI_P2eps n H ε) (CaseIIslab n H ε)
  calc ((SubcaseI_P2 n H).ncard : ℝ)
      ≤ (((SubcaseI_P2eps n H ε ∪ CaseIIslab n H ε).ncard : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (((SubcaseI_P2eps n H ε).ncard + (CaseIIslab n H ε).ncard : ℕ) : ℝ) := by
        exact_mod_cast h2
    _ = ((SubcaseI_P2eps n H ε).ncard : ℝ) + ((CaseIIslab n H ε).ncard : ℝ) := by
        push_cast
        ring

/-- **Case II for `n = 4, 5`** (exact quartic/quintic field counts, `β = 1`) at
the absolute threshold `ε = 1/(10n)`. -/
theorem subcaseI_P2_isBigO_of_quartic_quintic (n : ℕ) (hn : 4 ≤ n) (hn5 : n ≤ 5)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) 1)
    (c : ℕ) (hc : 1 ≤ c) (hper : PerIrrBound n c) :
    (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  refine subcaseI_P2_isBigO_of_literature_eps n hn (1 / (10 * (n : ℝ)))
    (by positivity) ?_ 1 ?_ ?_ hLOT hSC c hc hper
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  · have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    rw [div_lt_one hden]
    nlinarith
  · have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn5R : (n : ℝ) ≤ 5 := by exact_mod_cast hn5
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    have hden20 : (n : ℝ) * ((n : ℝ) - 1) ≤ 20 := by nlinarith
    have hfrac : 1 / 20 ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) :=
      one_div_le_one_div_of_le hden hden20
    have hsub : 1 - 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 - 1 / 20 := by linarith
    have hN1 : (1 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    have hc0 : (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      rw [sub_nonneg]
      exact (div_le_one hden).mpr hN1
    have hb : 1 / (10 * (n : ℝ)) ≤ 1 / 40 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hprod : (2 + 1 / (10 * (n : ℝ))) * (1 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
        ≤ (2 + 1 / 40) * (1 - 1 / 20) :=
      mul_le_mul (by linarith) hsub hc0 (by norm_num)
    have hfinal : 1 + (2 + 1 / 40) * (1 - 1 / 20) < (n : ℝ) - 1 := by
      have h1 : (1 : ℝ) + (2 + 1 / 40) * (1 - 1 / 20) = 2339 / 800 := by norm_num
      rw [h1]
      linarith
    linarith

/-- **Case II for `n ≥ 6`** (Schmidt's exponent `β = (n+2)/4`) at the absolute
threshold `ε = 1/(10n)`. -/
theorem subcaseI_P2_isBigO_of_schmidt_eps (n : ℕ) (hn : 6 ≤ n)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) (((n : ℝ) + 2) / 4))
    (c : ℕ) (hc : 1 ≤ c) (hper : PerIrrBound n c) :
    (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  refine subcaseI_P2_isBigO_of_literature_eps n (by omega) (1 / (10 * (n : ℝ)))
    (by positivity) ?_ (((n : ℝ) + 2) / 4) ?_ ?_ hLOT hSC c hc hper
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  · have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    have h1 : 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 := by
      rw [div_le_one hden]
      nlinarith
    have h2 : (2 : ℝ) ≤ ((n : ℝ) + 2) / 4 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    linarith
  · rcases eq_or_lt_of_le hn with h6 | h7
    · subst h6
      norm_num
    · have hn7 : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h7
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hnpos hn1pos
      have hXle : ((n : ℝ) + 2) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ ((n : ℝ) + 2) / 4 := by
        have h : (0 : ℝ) ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
        linarith
      have hkey : 1 + (2 + 1 / (10 * (n : ℝ))) * (((n : ℝ) + 2) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
            - ((n : ℝ) - 1)
          ≤ 3 - (n : ℝ) / 2 + (1 / (10 * (n : ℝ))) * (((n : ℝ) + 2) / 4) := by
        have h1 : 1 + (2 + 1 / (10 * (n : ℝ))) * (((n : ℝ) + 2) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
              - ((n : ℝ) - 1)
            = 3 - (n : ℝ) / 2 - 2 / ((n : ℝ) * ((n : ℝ) - 1))
              + (1 / (10 * (n : ℝ))) * (((n : ℝ) + 2) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
          field_simp
          ring
        rw [h1]
        have h2 := mul_le_mul_of_nonneg_left hXle (by positivity : (0 : ℝ) ≤ 1 / (10 * (n : ℝ)))
        have h3 : (0 : ℝ) < 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
        linarith
      have h4 : (1 / (10 * (n : ℝ))) * (((n : ℝ) + 2) / 4) ≤ 9 / 280 := by
        have he : (1 / (10 * (n : ℝ))) * (((n : ℝ) + 2) / 4) = ((n : ℝ) + 2) / (40 * (n : ℝ)) := by
          field_simp
          ring
        rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hn7, hnpos]
      have h5 : 3 - (n : ℝ) / 2 + 9 / 280 < 0 := by linarith
      linarith

/-! ## Endpoints -/

/-- **The challenge theorem in degree 5**: from the §4 Fourier bound
(`DequiBound 5`), Lemke Oliver–Thorne's per-field fibre bound and the exact
quintic field count.  (`5` is prime, so the imprimitive input is vacuous.) -/
theorem theorem_1_of_dequi_caseII_five (h : DequiBound 5)
    (hLOT : PerFieldFibreBound 5 (by omega : 1 ≤ 5))
    (hSC : FieldCountBound 5 (by omega : 1 ≤ 5) 1) :
    (fun H : ℕ => (E 5 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (5 - 1) : ℝ)) := by
  obtain ⟨c, hc1, hc⟩ := perIrrBound_of_dequiBound 5 (by omega) h
  exact theorem_1_of_dequi_one_prime 5 (by omega) (by norm_num) h
    (subcaseI_P2_isBigO_of_quartic_quintic 5 (by omega) (by omega) hLOT hSC c hc1 hc)

/-- **The challenge theorem for `n ≥ 6`** from the §4 Fourier bound, Schmidt +
Lemke Oliver–Thorne (Case II) and Widmer's imprimitive bound. -/
theorem theorem_1_of_dequi_caseII_eps (n : ℕ) (hn : 6 ≤ n) (h : DequiBound n)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) (((n : ℝ) + 2) / 4))
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨c, hc1, hc⟩ := perIrrBound_of_dequiBound n (by omega) h
  exact theorem_1_of_dequi_three n (by omega) h
    (subcaseI_P2_isBigO_of_schmidt_eps n hn hLOT hSC c hc1 hc)
    (ImprimitiveBad_isBigO_of_widmer n (by omega) hw)

/-- **The challenge theorem in degree 4**, conditional on an `O(H^3)` bound for
the imprimitive slice (the `V₄, C₄, D₈` groups of degree `4`, where Widmer's
`O(H^(n/2+2)) = O(H^4)` is not enough). -/
theorem theorem_1_of_dequi_caseII_four (h : DequiBound 4)
    (hLOT : PerFieldFibreBound 4 (by omega : 1 ≤ 4))
    (hSC : FieldCountBound 4 (by omega : 1 ≤ 4) 1)
    (hw : (fun H : ℕ => ((ImprimitiveBad 4 H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (4 - 1) : ℝ))) :
    (fun H : ℕ => (E 4 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (4 - 1) : ℝ)) := by
  obtain ⟨c, hc1, hc⟩ := perIrrBound_of_dequiBound 4 (by omega) h
  refine theorem_1_of_residual 4 (by omega) ?_ ?_ ?_ hw
  · refine SubcaseI_P1resid_isBigO_of_perD 4
      (max (c * smallConst 4 + 1) (smallConst 4 * (2 * smallConst 4 + 1) ^ 4))
      (by omega) ?_ (perDDiscBound_of_perIrrBound 4 c (by omega) hc1 hc)
    exact le_trans (Nat.le_add_left 1 (c * smallConst 4)) (Nat.le_max_left _ _)
  · exact subcaseI_P2_isBigO_of_quartic_quintic 4 (by omega) (by omega) hLOT hSC c hc1 hc
  · exact SubcaseI_P3_isBigO_of_perIrrBound 4 c (by omega) hc1 hc

/-- **The Abel-refined Case-II input from the two literature inputs** (for every
`n ≥ 1`): Lemke Oliver–Thorne's per-field fibre bound plus the field-count
bound `#classes ≤ c·Y^β` give the cumulative estimate

    `#{f ∈ SubcaseI_P2 n H : |Disc K_f| ≤ X} ≤ C·H·(log H)^{n-1}·X^{β−1/(n(n−1))}`,

by decomposing the region into its field-isomorphism classes, applying the
per-field bound class-by-class (the weight `|Disc|^{-1/(n(n-1))}`), and summing
the weights against the cumulative field count
(`Commons.Analysis.Sum.exists_sum_rpow_neg_le_of_card_le_fintype`).  This is
the missing glue announced in the `CaseIIClasses` docstring. -/
theorem caseIICountBound_of_field_inputs (n : ℕ) (hn1 : 2 ≤ n) (β : ℝ)
    (hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < β)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) β) :
    CaseIICountBound n β := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hLOT' : PerFieldFibreBound n hn1 := hLOT
  have hSC' : FieldCountBound n hn1 β := hSC
  obtain ⟨C₁, hC₁, hLOTb⟩ := hLOT'
  obtain ⟨c₂, hc₂, hSCb⟩ := hSC'
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  obtain ⟨C₂, hC₂, hdyad⟩ :=
    Commons.Analysis.Sum.exists_sum_rpow_neg_le_of_card_le_fintype
      (1 / ((n : ℝ) * ((n : ℝ) - 1))) β hβ
  set γ : ℝ := β - 1 / ((n : ℝ) * ((n : ℝ) - 1)) with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  refine ⟨C₁ * C₂ * c₂, by positivity, ?_⟩
  intro H X hX
  haveI : Fintype ↥(SubcaseI_P2 n H) :=
    ((box_finite n H).subset (subcaseI_P2_subset_Box n H)).fintype
  haveI : Fintype (Quotient (fieldIsoSetoid n H hn1)) := Quotient.fintype _
  set s : Setoid ↥(SubcaseI_P2 n H) := fieldIsoSetoid n H hn1 with hs
  -- (1) the counted set is the sum of its class fibres
  have hcard1 : Nat.card {f : ↥(SubcaseI_P2 n H) //
        (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)}
      ≤ ∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X)),
          Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} := by
    have heq : Nat.card {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)}
        = ∑ q : Quotient s, Nat.card {f : {f : ↥(SubcaseI_P2 n H) //
            (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} // Quotient.mk s f.1 = q} := by
      have h2 := Nat.card_congr (Equiv.sigmaFiberEquiv
        (fun f : {f : ↥(SubcaseI_P2 n H) //
            (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} => Quotient.mk s f.1))
      rw [Nat.card_sigma] at h2
      exact h2.symm
    rw [heq]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ)
      (fun q : Quotient s => classDisc n H hn1 q ≤ X)
      (fun q => Nat.card {f : {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} // Quotient.mk s f.1 = q})]
    have hzero : ∑ q ∈ Finset.univ.filter (fun q : Quotient s => ¬ classDisc n H hn1 q ≤ X),
        Nat.card {f : {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} // Quotient.mk s f.1 = q} = 0 := by
      refine Finset.sum_eq_zero (fun q hq => ?_)
      rw [Finset.mem_filter] at hq
      rw [Nat.card_eq_fintype_card]
      haveI : IsEmpty {f : {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} // Quotient.mk s f.1 = q} :=
        ⟨fun f => by
          have hdisc : subcaseI_P2_disc n H f.1 ≤ X := Nat.cast_le.mp f.1.2
          have hcls : classDisc n H hn1 q = subcaseI_P2_disc n H f.1 := by
            have h1 := congrArg (fun x => classDisc n H hn1 x) f.2
            rw [classDisc_mk n H hn1 f.1] at h1
            exact h1.symm
          omega⟩
      exact Fintype.card_eq_zero
    rw [hzero, add_zero]
    refine Finset.sum_le_sum (fun q _ => ?_)
    refine Nat.card_le_card_of_injective
      (fun f : {f : {f : ↥(SubcaseI_P2 n H) //
            (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} // Quotient.mk s f.1 = q} =>
        (⟨f.1.1, f.2⟩ : {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q})) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext
      (congrArg (fun x : {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} => x.1) hab))
  -- (2) Lemke Oliver–Thorne class by class
  have hcard2 : (∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X)),
        ((Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} : ℕ) : ℝ))
      ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X)),
              (classDisc n H hn1 q : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1))))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun q _ => ?_)
    simpa only [mul_assoc] using hLOTb H q
  -- (3) the weighted class sum, from the cumulative field count
  let F : Finset (Quotient s) := Finset.univ.filter (fun q => classDisc n H hn1 q ≤ X)
  have hcount_nat : ∀ Y : ℕ,
      Nat.card {i : {q : Quotient s // q ∈ F} // classDisc n H hn1 i.1 ≤ Y}
        ≤ Nat.card {q : Quotient s // classDisc n H hn1 q ≤ Y} := by
    intro Y
    refine Nat.card_le_card_of_injective
      (fun i : {i : {q : Quotient s // q ∈ F} // classDisc n H hn1 i.1 ≤ Y} =>
        (⟨i.1.1, i.2⟩ : {q : Quotient s // classDisc n H hn1 q ≤ Y})) ?_
    intro a b hab
    have h1 : (a.1.1 : Quotient s) = b.1.1 :=
      congr_arg (fun x : {q : Quotient s // classDisc n H hn1 q ≤ Y} => (x : Quotient s)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hcount : ∀ Y : ℕ, ((Finset.univ.filter (fun i : {q : Quotient s // q ∈ F} =>
        classDisc n H hn1 i.1 ≤ Y)).card : ℝ) ≤ c₂ * (Y : ℝ) ^ β := by
    intro Y
    rw [card_filter_eq_natCard]
    rcases Y with _ | Y
    · have hden : (0 : ℝ) < 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
        have h2 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hnpos hn1pos
        positivity
      have hemp : Nat.card {i : {q : Quotient s // q ∈ F} // classDisc n H hn1 i.1 ≤ 0} = 0 := by
        rw [Nat.card_eq_fintype_card]
        haveI : IsEmpty {i : {q : Quotient s // q ∈ F} // classDisc n H hn1 i.1 ≤ 0} :=
          ⟨fun i => by
            have h3 := one_le_classDisc n H hn1 i.1.1
            have h4 := i.2
            omega⟩
        exact Fintype.card_eq_zero
      rw [hemp, Nat.cast_zero, Real.zero_rpow (ne_of_gt (lt_trans hden hβ)), mul_zero]
    · exact le_trans (by exact_mod_cast hcount_nat (Y + 1)) (hSCb H (Y + 1) (by omega))
  have hsum : (∑ i : {q : Quotient s // q ∈ F},
        (classDisc n H hn1 i.1 : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1)))))
      ≤ C₂ * c₂ * (X : ℝ) ^ γ := by
    have h1 := hdyad (fun i : {q : Quotient s // q ∈ F} => classDisc n H hn1 i.1) c₂ X
      hc₂ (by exact_mod_cast hX : (1 : ℝ) ≤ (X : ℝ))
      (fun i => one_le_classDisc n H hn1 i.1)
      (fun i => by
        have hmem : classDisc n H hn1 i.1 ≤ X := by
          have h2 : i.1 ∈ Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X) := i.2
          exact (Finset.mem_filter.mp h2).2
        exact_mod_cast hmem)
      hcount
    rwa [hγ] at h1
  have hattach : (∑ q ∈ F,
        (classDisc n H hn1 q : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1)))))
      = ∑ i : {q : Quotient s // q ∈ F},
        (classDisc n H hn1 i.1 : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1)))) :=
    (Finset.sum_attach _ _).symm
  calc ((Nat.card {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} : ℕ) : ℝ)
      ≤ ((∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X)),
          Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q}) : ℕ) := by
        exact Nat.cast_le.mpr hcard1
    _ = ∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X)),
          ((Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
    _ ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1 q ≤ X)),
              (classDisc n H hn1 q : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1))))) := hcard2
    _ ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (C₂ * c₂ * (X : ℝ) ^ γ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hattach]
        exact hsum
    _ = C₁ * C₂ * c₂ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ γ := by ring
    _ = C₁ * C₂ * c₂ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (X : ℝ) ^ (β - 1 / ((n : ℝ) * ((n : ℝ) - 1))) := by rw [hγ]

/-- **Case II in degree 3.**  In degree 3 the *bad* polynomials are exactly the
ones with cyclic Galois group (`|Gal| < 3! = 6` leaves only `C₃`), so the
field-isomorphism classes of the region are cyclic cubic fields, and

    `#{cyclic cubic fields with |Disc| ≤ Y} = O(√Y)`

— the classical parametrisation of cyclic cubic fields by the representations
`4f = u² + 27v²` (`u ≡ 1 mod 3`, `f` the conductor, `|Disc| = f²`) exhibits
each such field as one lattice point of the region `u² + 27v² ≤ 4√Y`, whose
side is `O(Y^{1/4})`, so the number of fields is `O(Y^{1/2})` (`a(C₃) = 1/2` in
the paper's notation).  Lemke Oliver–Thorne plus the Abel summation then gives
the cumulative bound with exponent
`1 + (2 + 1/3)·(1/2 − 1/6) = 16/9 < 2`, i.e. Case II is `O(H²)` in degree 3 —
with the project's *own* thresholds (`δ = 1/(2n)`), no small-`δ` adjustment
needed. -/
theorem subcaseI_P2_isBigO_three (hLOT : PerFieldFibreBound 3 (by omega : 1 ≤ 3))
    (hSC : FieldCountBound 3 (by omega : 1 ≤ 3) (1 / 2)) :
    (fun H : ℕ => ((SubcaseI_P2 3 H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) := by
  refine subcaseI_P2_isBigO_of_countBound 3 (by omega) (1 / 2) ?_ ?_
    (caseIICountBound_of_field_inputs 3 (by omega) (1 / 2) ?_ hLOT hSC)
  · norm_num
  · norm_num
  · norm_num

/-- **The challenge theorem in degree 3**: from the §4 Fourier bound, Lemke
Oliver–Thorne's per-field fibre bound and the count of cyclic cubic fields of
bounded discriminant. -/
theorem theorem_1_of_dequi_degree_three (h : DequiBound 3)
    (hLOT : PerFieldFibreBound 3 (by omega : 1 ≤ 3))
    (hSC : FieldCountBound 3 (by omega : 1 ≤ 3) (1 / 2)) :
    (fun H : ℕ => (E 3 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) :=
  theorem_1_of_dequi_one_prime 3 (by omega) (by norm_num) h
    (subcaseI_P2_isBigO_three hLOT hSC)

end




end Submission.Vdw
