import Mathlib
import Submission.Vdw.CaseIIFields
import Submission.Commons.NumberTheory.NumberField.discr_eq_of_algEquiv

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Case II from the two number-field-counting inputs (Schmidt; Lemke
Oliver–Thorne)

`CaseIIFields` isolates the Abel-refined Case-II input `CaseIICountBound n β`.
This module discharges it from the two *literature* inputs of the paper's
Case II, i.e. it makes the Case-II side of the reduction literature-shaped:

* `PerFieldFibreBound n` — **Lemke Oliver–Thorne** (Prop. 2.2 of *[LOT]*): a
  degree-`n` field with primitive Galois group is cut out by
  `≪ H log^{n-1}H/|Disc|^{1/(n(n-1))}` monic degree-`n` polynomials of height
  `≤ H`.  Formulated as the bound on the *field-fibre* cardinality, i.e. on the
  number of members of the Case-II region cutting out a fixed field
  (`classDisc` = the field's discriminant).
* `FieldCountBound n β` — **Schmidt**: the number of degree-`n` number fields
  of absolute discriminant `≤ Y` is `≪ Y^β` (Schmidt: `β = (n+2)/4`; the exact
  quartic/quintic counts give `β = 1`), restricted to the fields cut out by the
  region (an immediate consequence for the sub-collection).
* the Abel/dyadic summation (`Commons.Analysis.Sum.sum_rpow_neg_le_of_card_le_fintype`,
  delivered by the fleet) turns `FieldCountBound` into the weighted estimate
  `Σ_{q : classDisc q ≤ X} classDisc(q)^{-1/(n(n-1))} ≪ X^{β - 1/(n(n-1))}`.

Main result: `caseIICountBound_of_field_inputs` — the two inputs give
`CaseIICountBound n β`, hence (with `β = (n+2)/4`) Case II `= O(H^{n-1})` for
`n ≥ 7` (`subcaseI_P2_isBigO_of_literature`) and the corresponding endpoints
for the challenge theorem.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## The Case-II region and its field-isomorphism classes -/

/-- Members of the Case-II region are irreducible over `ℚ`. -/
theorem subcaseI_P2_irreducible (n H : ℕ) (hn : 1 ≤ n) (f : ↥(SubcaseI_P2 n H)) :
    Irreducible (((f : ℤ[X])).map φℚ) :=
  irreducibleBad_mem_irreducible_rat hn f.2.1.1

/-- The Case-II region sits inside the box. -/
theorem subcaseI_P2_subset_Box (n H : ℕ) : SubcaseI_P2 n H ⊆ Box n H :=
  fun _ hf => Bad_subset_Box n H (irreducibleBad_subset_Bad n H hf.1.1)

/-- **The field-isomorphism relation** on the Case-II region: two members are
equivalent when the fields they cut out are isomorphic. -/
noncomputable def fieldIsoRel (n H : ℕ) (hn : 1 ≤ n) (f g : ↥(SubcaseI_P2 n H)) : Prop :=
  letI : Fact (Irreducible (((f : ℤ[X])).map φℚ)) := ⟨subcaseI_P2_irreducible n H hn f⟩
  letI : Fact (Irreducible (((g : ℤ[X])).map φℚ)) := ⟨subcaseI_P2_irreducible n H hn g⟩
  Nonempty ((Kpoly (f : ℤ[X])) ≃ₐ[ℚ] (Kpoly (g : ℤ[X])))

theorem fieldIsoRel_refl (n H : ℕ) (hn : 1 ≤ n) (f : ↥(SubcaseI_P2 n H)) :
    fieldIsoRel n H hn f f := by
  show Nonempty ((Kpoly (f : ℤ[X])) ≃ₐ[ℚ] (Kpoly (f : ℤ[X])))
  exact ⟨AlgEquiv.refl⟩

theorem fieldIsoRel_symm (n H : ℕ) (hn : 1 ≤ n) {f g : ↥(SubcaseI_P2 n H)}
    (h : fieldIsoRel n H hn f g) : fieldIsoRel n H hn g f := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

theorem fieldIsoRel_trans (n H : ℕ) (hn : 1 ≤ n) {f g k : ↥(SubcaseI_P2 n H)}
    (h1 : fieldIsoRel n H hn f g) (h2 : fieldIsoRel n H hn g k) :
    fieldIsoRel n H hn f k := by
  obtain ⟨e1⟩ := h1
  obtain ⟨e2⟩ := h2
  exact ⟨e1.trans e2⟩

/-- The setoid of field-isomorphism classes on the Case-II region. -/
noncomputable def fieldIsoSetoid (n H : ℕ) (hn : 1 ≤ n) : Setoid ↥(SubcaseI_P2 n H) where
  r := fieldIsoRel n H hn
  iseqv := ⟨fieldIsoRel_refl n H hn, fun h => fieldIsoRel_symm n H hn h,
    fun h1 h2 => fieldIsoRel_trans n H hn h1 h2⟩

/-- The field discriminant is invariant under field isomorphism (the
`fieldDisc`/`NumberField.discr` bridge). -/
theorem subcaseI_P2_disc_eq_of_iso (n H : ℕ) (hn : 1 ≤ n) {f g : ↥(SubcaseI_P2 n H)}
    (h : fieldIsoRel n H hn f g) : subcaseI_P2_disc n H f = subcaseI_P2_disc n H g := by
  letI : Fact (Irreducible (((f : ℤ[X])).map φℚ)) := ⟨subcaseI_P2_irreducible n H hn f⟩
  letI : Fact (Irreducible (((g : ℤ[X])).map φℚ)) := ⟨subcaseI_P2_irreducible n H hn g⟩
  obtain ⟨e⟩ := h
  have hd := Commons.NumberTheory.NumberField.discr_eq_of_algEquiv e
  simp only [subcaseI_P2_disc, fieldDiscExp, fieldDisc, hd]

/-- **The discriminant of a field-isomorphism class** of the Case-II region. -/
noncomputable def classDisc (n H : ℕ) (hn : 1 ≤ n) :
    Quotient (fieldIsoSetoid n H hn) → ℕ :=
  Quot.lift (fun f : ↥(SubcaseI_P2 n H) => subcaseI_P2_disc n H f)
    (fun _ _ hfg => subcaseI_P2_disc_eq_of_iso n H hn hfg)

theorem classDisc_mk (n H : ℕ) (hn : 1 ≤ n) (f : ↥(SubcaseI_P2 n H)) :
    classDisc n H hn (Quotient.mk (fieldIsoSetoid n H hn) f) = subcaseI_P2_disc n H f := rfl

/-- The class discriminant computed at the canonical representative. -/
theorem classDisc_out (n H : ℕ) (hn : 1 ≤ n) (q : Quotient (fieldIsoSetoid n H hn)) :
    classDisc n H hn q = subcaseI_P2_disc n H (Quotient.out q) := by
  conv_lhs => rw [← Quotient.out_eq q]
  exact classDisc_mk n H hn (Quotient.out q)

/-- The discriminant of a class is at least one. -/
theorem one_le_classDisc (n H : ℕ) (hn : 1 ≤ n) (q : Quotient (fieldIsoSetoid n H hn)) :
    1 ≤ classDisc n H hn q := by
  haveI : Fact (Irreducible ((((Quotient.out q) : ↥(SubcaseI_P2 n H)) : ℤ[X]).map φℚ)) :=
    ⟨subcaseI_P2_irreducible n H hn (Quotient.out q)⟩
  have h2 : subcaseI_P2_disc n H (Quotient.out q)
      = fieldDisc (((Quotient.out q) : ↥(SubcaseI_P2 n H)) : ℤ[X]) := rfl
  rw [classDisc_out n H hn q, h2, fieldDisc]
  exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero _))

/-- Every class arising in the Case-II region has discriminant `≤ H^{2+1/n}`
(it contains a member of the region). -/
theorem classDisc_le (n H : ℕ) (hn : 1 ≤ n) (q : Quotient (fieldIsoSetoid n H hn)) :
    (classDisc n H hn q : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
  rw [classDisc_out n H hn q]
  exact subcaseI_P2_disc_le n H (Quotient.out q)

/-! ## The two literature inputs -/

/-- **Lemke Oliver–Thorne, per field** (fibre form): each field-isomorphism
class of the Case-II region is cut out by at most
`C·H·(log H)^{n-1}·|Disc|^{-1/(n(n-1))}` members of the region. -/
def PerFieldFibreBound (n : ℕ) (hn : 1 ≤ n) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, ∀ q : Quotient (fieldIsoSetoid n H hn),
    ((Nat.card {f : ↥(SubcaseI_P2 n H) //
        Quotient.mk (fieldIsoSetoid n H hn) f = q} : ℕ) : ℝ)
      ≤ C * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (classDisc n H hn q : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1))))

/-- **Schmidt, restricted to the fields arising in the region**: the number of
field-isomorphism classes of the Case-II region of discriminant `≤ Y` is at
most `c·Y^β`.  (Schmidt's theorem bounds *all* degree-`n` number fields of
absolute discriminant `≤ Y` by `≪ Y^{(n+2)/4}`; the restriction to the
sub-collection cut out by the region is immediate.) -/
def FieldCountBound (n : ℕ) (hn : 1 ≤ n) (β : ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ H Y : ℕ, 1 ≤ Y →
    ((Nat.card {q : Quotient (fieldIsoSetoid n H hn) //
        classDisc n H hn q ≤ Y} : ℕ) : ℝ) ≤ c * (Y : ℝ) ^ β

/-! ## From the two inputs to the Abel-refined count

The fibre bound sums over classes; the field count feeds the dyadic summation
`Commons.Analysis.Sum.sum_rpow_neg_le_of_card_le_fintype`. -/

/-- **Case II for `n ≥ 7` from the two literature inputs.**

The computation is the paper's, in its *crude* form (no Abel refinement of the
per-field weights is needed for `n ≥ 7`): the region splits into its
field-isomorphism classes,
`#SubcaseI_P2 n H ≤ Σ_q #(class q) ≤ Σ_q C·H·(log H)^{n-1} = C·H·(log H)^{n-1}·#classes`
by Lemke Oliver–Thorne (`classDisc q ≥ 1`, so `classDisc q^{-1/(n(n-1))} ≤ 1`),
and Schmidt's count `#classes ≪ X^{(n+2)/4}` with `X = ⌈H^{2+1/n}⌉` gives the
exponent `1 + (2+1/n)(n+2)/4`, which is `< n-1` exactly for `n ≥ 7`
(margin `(n² - 6.5n - 1)/2 > 0`).  The logarithmic factor is then absorbed by
the power saving. -/
theorem subcaseI_P2_isBigO_of_literature (n : ℕ) (hn : 7 ≤ n)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) (((n : ℝ) + 2) / 4)) :
    (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hLOT' : PerFieldFibreBound n hn1 := hLOT
  have hSC' : FieldCountBound n hn1 (((n : ℝ) + 2) / 4) := hSC
  obtain ⟨C₁, hC₁, hLOTb⟩ := hLOT'
  obtain ⟨c₂, hc₂, hSCb⟩ := hSC'
  have hnR : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- exponent bookkeeping
  set κ : ℝ := 1 + (2 + 1 / (n : ℝ)) * (((n : ℝ) + 2) / 4) with hκ
  have hκlt : κ < (n : ℝ) - 1 := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hmain : 0 < (n : ℝ) ^ 2 - (13 / 2) * (n : ℝ) - 1 := by nlinarith [hnR]
    have hgoal : κ * (4 * (n : ℝ))
        = 4 * (n : ℝ) + (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) := by
      rw [hκ]
      field_simp
    have hlt : κ * (4 * (n : ℝ)) < ((n : ℝ) - 1) * (4 * (n : ℝ)) := by
      rw [hgoal]
      nlinarith [hmain, hnpos]
    nlinarith [hlt, hnpos]
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
      ((SubcaseI_P2 n H).ncard : ℝ)
        ≤ C₁ * c₂ * 2 ^ (((n : ℝ) + 2) / 4) * (H : ℝ) ^ ((n : ℝ) - 1) := by
    filter_upwards [hlog, eventually_ge_atTop (1 : ℕ)] with H hlogH hH1
    have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hH1R
    haveI : Fintype ↥(SubcaseI_P2 n H) :=
      ((box_finite n H).subset (subcaseI_P2_subset_Box n H)).fintype
    haveI : Fintype (Quotient (fieldIsoSetoid n H hn1)) := Quotient.fintype _
    set s : Setoid ↥(SubcaseI_P2 n H) := fieldIsoSetoid n H hn1 with hs
    set X : ℕ := Nat.ceil ((H : ℝ) ^ (2 + 1 / (n : ℝ))) with hX
    -- (1) the region decomposes into its classes
    have hcard1 : Nat.card ↥(SubcaseI_P2 n H)
        ≤ ∑ q : Quotient s, Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} := by
      have h2 := Nat.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk s))
      rw [Nat.card_sigma] at h2
      exact le_of_eq h2.symm
    -- (2) Lemke Oliver–Thorne for each class
    have hcard2 : ∀ q : Quotient s,
        ((Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} : ℕ) : ℝ)
          ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) := by
      intro q
      have h1 := hLOTb H q
      have h2 : (classDisc n H hn1 q : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1)))) ≤ 1 := by
        have h3 : (1 : ℝ) ≤ (classDisc n H hn1 q : ℝ) := by
          exact_mod_cast one_le_classDisc n H hn1 q
        exact Real.rpow_le_one_of_one_le_of_nonpos h3 (by
          have : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
          have : (0 : ℝ) < 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
          linarith)
      calc ((Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} : ℕ) : ℝ)
          ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
              * (classDisc n H hn1 q : ℝ) ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1)))) := h1
        _ ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * 1 := by
            refine mul_le_mul_of_nonneg_left h2 ?_
            have hL0 : (0 : ℝ) ≤ (Real.log (H : ℝ)) ^ (n - 1) := by positivity
            exact mul_nonneg (mul_nonneg hC₁ (Nat.cast_nonneg H)) hL0
        _ = C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) := by ring
    -- (3) Schmidt: the number of classes
    have hcardq : ((Nat.card (Quotient s) : ℕ) : ℝ)
        ≤ c₂ * (X : ℝ) ^ (((n : ℝ) + 2) / 4) := by
      have hmem : ∀ q : Quotient s, classDisc n H hn1 q ≤ X := by
        intro q
        have h := classDisc_le n H hn1 q
        have hle := Nat.le_ceil ((H : ℝ) ^ (2 + 1 / (n : ℝ)))
        rw [hX]
        exact_mod_cast le_trans h hle
      have hall : Nat.card (Quotient s)
          = Nat.card {q : Quotient s // classDisc n H hn1 q ≤ X} := by
        refine Nat.card_congr ?_
        exact { toFun := fun q => ⟨q, hmem q⟩
                invFun := fun q => q.1
                left_inv := fun q => rfl
                right_inv := fun q => rfl }
      rw [hall]
      exact hSCb H X (by
        have h2 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) :=
          Real.one_le_rpow hH1R (by positivity)
        have h3 : (1 : ℝ) ≤ ((Nat.ceil ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) :=
          le_trans h2 (Nat.le_ceil _)
        rw [hX]
        exact_mod_cast h3)
    -- (4) assemble
    have hsum : (∑ q : Quotient s, ((Nat.card {f : ↥(SubcaseI_P2 n H) //
          Quotient.mk s f = q} : ℕ) : ℝ))
        ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (Nat.card (Quotient s) : ℝ) := by
      calc (∑ q : Quotient s, ((Nat.card {f : ↥(SubcaseI_P2 n H) //
            Quotient.mk s f = q} : ℕ) : ℝ))
          ≤ ∑ _q : Quotient s, (C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)) :=
            Finset.sum_le_sum (fun q _ => hcard2 q)
        _ = C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (Nat.card (Quotient s) : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
            ring
    have hstep : ((SubcaseI_P2 n H).ncard : ℝ)
        ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (c₂ * (X : ℝ) ^ (((n : ℝ) + 2) / 4)) := by
      calc ((SubcaseI_P2 n H).ncard : ℝ)
          = ((Nat.card ↥(SubcaseI_P2 n H) : ℕ) : ℝ) := by
            rw [← Commons.Data.Set.ncard_eq_natCard (SubcaseI_P2 n H)]
        _ ≤ ((∑ q : Quotient s, Nat.card {f : ↥(SubcaseI_P2 n H) //
              Quotient.mk s f = q}) : ℝ) := by exact_mod_cast hcard1
        _ = ∑ q : Quotient s, ((Nat.card {f : ↥(SubcaseI_P2 n H) //
              Quotient.mk s f = q} : ℕ) : ℝ) := rfl
        _ ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (Nat.card (Quotient s) : ℝ) := hsum
        _ ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (c₂ * (X : ℝ) ^ (((n : ℝ) + 2) / 4)) := by
            refine mul_le_mul_of_nonneg_left hcardq ?_
            have hL0 : (0 : ℝ) ≤ (Real.log (H : ℝ)) ^ (n - 1) := by positivity
            exact mul_nonneg (mul_nonneg hC₁ (Nat.cast_nonneg H)) hL0
    -- (5) `X ≤ 2·H^(2+1/n)` and the exponent comparison
    have hXle : (X : ℝ) ≤ 2 * (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
      have h1 : (X : ℝ) < (H : ℝ) ^ (2 + 1 / (n : ℝ)) + 1 := by
        rw [hX]; exact Nat.ceil_lt_add_one (by positivity)
      have h2 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) :=
        Real.one_le_rpow hH1R (by positivity)
      linarith
    have hβpos : (0 : ℝ) < ((n : ℝ) + 2) / 4 := by linarith
    have hXpow : (X : ℝ) ^ (((n : ℝ) + 2) / 4)
        ≤ 2 ^ (((n : ℝ) + 2) / 4) * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * (((n : ℝ) + 2) / 4)) := by
      calc (X : ℝ) ^ (((n : ℝ) + 2) / 4)
          ≤ (2 * (H : ℝ) ^ (2 + 1 / (n : ℝ))) ^ (((n : ℝ) + 2) / 4) :=
            Real.rpow_le_rpow (by positivity) hXle hβpos.le
        _ = 2 ^ (((n : ℝ) + 2) / 4)
              * ((H : ℝ) ^ (2 + 1 / (n : ℝ))) ^ (((n : ℝ) + 2) / 4) :=
            Real.mul_rpow (by norm_num) (by positivity)
        _ = 2 ^ (((n : ℝ) + 2) / 4)
              * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * (((n : ℝ) + 2) / 4)) := by
            rw [Real.rpow_mul hHpos.le]
    have hexp2 : κ + δ ≤ (n : ℝ) - 1 := by
      have h1 := hδ
      linarith
    calc ((SubcaseI_P2 n H).ncard : ℝ)
        ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
            * (c₂ * (X : ℝ) ^ (((n : ℝ) + 2) / 4)) := hstep
      _ ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
            * (c₂ * (2 ^ (((n : ℝ) + 2) / 4)
              * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * (((n : ℝ) + 2) / 4)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXpow hc₂) (by positivity)
      _ = C₁ * c₂ * 2 ^ (((n : ℝ) + 2) / 4)
            * ((H : ℝ) * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * (((n : ℝ) + 2) / 4))
              * (Real.log (H : ℝ)) ^ (n - 1)) := by ring
      _ = C₁ * c₂ * 2 ^ (((n : ℝ) + 2) / 4) * ((H : ℝ) ^ κ * (Real.log (H : ℝ)) ^ (n - 1)) := by
          have hrw : (H : ℝ) * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * (((n : ℝ) + 2) / 4))
              = (H : ℝ) ^ κ := by
            have h1 : (H : ℝ) * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * (((n : ℝ) + 2) / 4))
                = (H : ℝ) ^ (1 : ℝ) * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * (((n : ℝ) + 2) / 4)) := by
              rw [Real.rpow_one]
            rw [h1, (Real.rpow_add hHpos 1 _).symm]
          rw [hrw]
      _ ≤ C₁ * c₂ * 2 ^ (((n : ℝ) + 2) / 4) * ((H : ℝ) ^ κ * (H : ℝ) ^ δ) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogH (by positivity))
            (by positivity)
      _ = C₁ * c₂ * 2 ^ (((n : ℝ) + 2) / 4) * (H : ℝ) ^ (κ + δ) := by
          rw [← Real.rpow_add hHpos]
      _ ≤ C₁ * c₂ * 2 ^ (((n : ℝ) + 2) / 4) * (H : ℝ) ^ ((n : ℝ) - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hH1R hexp2
  refine IsBigO.of_bound (max (C₁ * c₂ * 2 ^ (((n : ℝ) + 2) / 4)) 0) ?_
  filter_upwards [hpoint] with H hH
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  rw [← Real.rpow_natCast (H : ℝ) (n - 1)]
  have hcast : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hcast]
  refine le_trans hH ?_
  have : (0 : ℝ) ≤ C₁ * c₂ * 2 ^ (((n : ℝ) + 2) / 4) := by positivity
  rw [max_eq_left this]

/-- **The challenge theorem for `n ≥ 7` from the paper's literature inputs**:
the §4 Fourier bound (`DequiBound`), Schmidt + Lemke Oliver–Thorne (Case II),
and Widmer's imprimitive bound. -/
theorem theorem_1_of_literature (n : ℕ) (hn : 7 ≤ n) (h : DequiBound n)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) (((n : ℝ) + 2) / 4))
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_dequi_three n (by omega) h (subcaseI_P2_isBigO_of_literature n hn hLOT hSC)
    (ImprimitiveBad_isBigO_of_widmer n (by omega) hw)

/-- **The challenge theorem in prime degree `n ≥ 7`**: the imprimitive input is
vacuous, leaving the §4 Fourier bound and the two number-field-counting
inputs. -/
theorem theorem_1_of_literature_prime (n : ℕ) (hn : 7 ≤ n) (hp : Nat.Prime n)
    (h : DequiBound n)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) (((n : ℝ) + 2) / 4)) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_dequi_one_prime n (by omega) hp h
    (subcaseI_P2_isBigO_of_literature n hn hLOT hSC)

end

end Submission.Vdw
