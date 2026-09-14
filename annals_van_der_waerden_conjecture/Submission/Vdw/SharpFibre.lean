import Mathlib
import Submission.Vdw.CaseIIClasses
import Submission.Vdw.CaseIICountM
import Submission.Vdw.FinalAssemblyM
import Submission.Vdw.FinalEndpoints
import Submission.Vdw.SchmidtCount
import Submission.Vdw.QuarticSymmBound
import Submission.Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case II with a general per-field fibre exponent

The paper's Case-II analysis uses the Lemke Oliver–Thorne per-field fibre bound

  `#{f ∈ region : K_f ≅ K} ≪ H·(log H)^{n-1}·|Disc K|^{-1/(n(n-1))}`,

whose discriminant exponent `1/(n(n-1))` comes from the Ellenberg–Venkatesh
lower bound `house α ≥ |Disc K|^{1/(n(n-1))}/2` on the house of a generator.
The *sharp* exponent would be `1/2` (the covolume of `𝓞 K`), but **it is false**:
the fleet refuted it with five families of counterexamples (see the Roadmap,
Session-164) — `K = ℚ(ζ_p)` with `Y = 1`; `K = ℚ(∛m)` with `Y ≍ |Disc K|^{1/3}`
(and in the regimes `|Disc K| ≤ Y^2`, `Y^3`, `Y^{2+1/n}`); and, for the `+ 1`
form, the subfield cosets of `ℚ(√a, √b)`.  The true fibre exponent is no better
than `2/(n(n-1))`-ish, and the paper's `1/(n(n-1))` (the Ellenberg–Venkatesh
value) is what the project uses.  The sharp-exponent endpoints below are
therefore *conditional statements about a false hypothesis*: they are kept only
to record the `(β, α)` trade-off.  What the module is actually **used** for is
the general parameterisation together with `theorem_1_of_indexFieldCount`.

This module parameterises the whole Case-II chain by the fibre exponent `α`:

* `PerFieldFibreBoundExp n α` — the per-field fibre bound with exponent `α`
  (this is the paper's `PerFieldFibreBound` for `α = 1/(n(n-1))`, and the sharp
  input for `α = 1/2`);
* `CaseIICountBoundExp n β α` — the Abel-refined cumulative estimate
  `#{f ∈ SubcaseI_P2 n H : |Disc K_f| ≤ X} ≪ H (log H)^{n-1} X^{β-α}`;
* `caseIICountBoundExp_of_field_inputs` — the two inputs give the cumulative
  estimate (Abel summation over the field classes);
* `SubcaseIM_P2_isBigO_of_countBoundExp` — the Case-II slice at the Weyl
  threshold `2 + 4/M` is `O(H^{n-1})` as soon as
  `1 + (2 + 4/M)(β - α) < n - 1`;
* the endpoints.

With the sharp exponent `α = 1/2` the exponent condition becomes
`β - 1/2 < (n-2)/(2+4/M)`, which is satisfied by the *classical* field-count
values `β = 1/2` (`n = 3`, Cohn), `β = 1` (`n = 4`, Davenport–Heilbronn) and
`β = (n+2)/4` (`n ≥ 5`, Schmidt) — in particular **`n = 5` no longer needs the
exact quintic count**.  Compare the classical chain, where the condition
`β - 1/(n(n-1)) < (n-2)/(2+4/M)` forces the sharper values `β = 1`
(`n = 4, 5`).

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## The per-field fibre bound with exponent `α` -/

/-- **Per-field fibre bound with discriminant exponent `α`**: each
field-isomorphism class of the Case-II region is cut out by at most
`C·H·(log H)^{n-1}·|Disc|^{-α}` members of the region.  (`α = 1/(n(n-1))` is
the Lemke Oliver–Thorne value delivered by the Mahler-measure count; `α = 1/2`
is the sharp lattice-covolume value.) -/
def PerFieldFibreBoundExp (n : ℕ) (hn : 1 ≤ n) (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, ∀ q : Quotient (fieldIsoSetoid n H hn),
    ((Nat.card {f : ↥(SubcaseI_P2 n H) //
        Quotient.mk (fieldIsoSetoid n H hn) f = q} : ℕ) : ℝ)
      ≤ C * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (classDisc n H hn q : ℝ) ^ (-α)

/-- **Abel-refined Case-II count with fibre exponent `α`**:
`#{f ∈ SubcaseI_P2 n H : |Disc K_f| ≤ X} ≤ C·H·(log H)^{n-1}·X^{β-α}`. -/
def CaseIICountBoundExp (n : ℕ) (β α : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H X : ℕ, 1 ≤ X →
    ((Nat.card {f : ↥(SubcaseI_P2 n H) //
        (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} : ℕ) : ℝ)
      ≤ C * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (X : ℝ) ^ (β - α)

/-- The paper's fibre exponent `1/(n(n-1))` is a special case. -/
theorem perFieldFibreBound_exp_classical (n : ℕ) (hn : 1 ≤ n)
    (h : PerFieldFibreBound n hn) :
    PerFieldFibreBoundExp n hn (1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun H q => by simpa using hb H q⟩

/-! ## The Abel summation with a general fibre exponent -/

/-- **The Abel-refined cumulative Case-II count from the two inputs**, with the
fibre exponent `α` arbitrary (`α < β`). -/
theorem caseIICountBoundExp_of_field_inputs (n : ℕ) (hn1 : 2 ≤ n) (β α : ℝ)
    (hαβ : α < β)
    (hfib : PerFieldFibreBoundExp n (by omega : 1 ≤ n) α)
    (hSC : FieldCountBound n (by omega : 1 ≤ n) β) :
    CaseIICountBoundExp n β α := by
  classical
  have hn1' : 1 ≤ n := by omega
  have hfib' : PerFieldFibreBoundExp n hn1' α := hfib
  have hSC' : FieldCountBound n hn1' β := hSC
  obtain ⟨C₁, hC₁, hfibb⟩ := hfib'
  obtain ⟨c₂, hc₂, hSCb⟩ := hSC'
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  obtain ⟨C₂, hC₂, hdyad⟩ :=
    Commons.Analysis.Sum.exists_sum_rpow_neg_le_of_card_le_fintype α β hαβ
  set γ : ℝ := β - α with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  refine ⟨C₁ * C₂ * c₂, by positivity, ?_⟩
  intro H X hX
  haveI : Fintype ↥(SubcaseI_P2 n H) :=
    ((box_finite n H).subset (subcaseI_P2_subset_Box n H)).fintype
  haveI : Fintype (Quotient (fieldIsoSetoid n H hn1')) := Quotient.fintype _
  set s : Setoid ↥(SubcaseI_P2 n H) := fieldIsoSetoid n H hn1' with hs
  -- (1) decompose the counted set into its class fibres
  have hcard1 : Nat.card {f : ↥(SubcaseI_P2 n H) //
        (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)}
      ≤ ∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1' q ≤ X)),
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
      (fun q : Quotient s => classDisc n H hn1' q ≤ X)
      (fun q => Nat.card {f : {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} // Quotient.mk s f.1 = q})]
    have hzero : ∑ q ∈ Finset.univ.filter (fun q : Quotient s => ¬ classDisc n H hn1' q ≤ X),
        Nat.card {f : {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} // Quotient.mk s f.1 = q} = 0 := by
      refine Finset.sum_eq_zero (fun q hq => ?_)
      rw [Finset.mem_filter] at hq
      rw [Nat.card_eq_fintype_card]
      haveI : IsEmpty {f : {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} // Quotient.mk s f.1 = q} :=
        ⟨fun f => by
          have hdisc : subcaseI_P2_disc n H f.1 ≤ X := Nat.cast_le.mp f.1.2
          have hcls : classDisc n H hn1' q = subcaseI_P2_disc n H f.1 := by
            have h1 := congrArg (fun x => classDisc n H hn1' x) f.2
            rw [classDisc_mk n H hn1' f.1] at h1
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
  -- (2) the per-class fibre bound
  have hcard2 : (∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1' q ≤ X)),
        ((Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} : ℕ) : ℝ))
      ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1' q ≤ X)),
              (classDisc n H hn1' q : ℝ) ^ (-α)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun q _ => ?_)
    simpa only [mul_assoc] using hfibb H q
  -- (3) the weighted class sum from the cumulative field count
  let F : Finset (Quotient s) := Finset.univ.filter (fun q => classDisc n H hn1' q ≤ X)
  have hcount_nat : ∀ Y : ℕ,
      Nat.card {i : {q : Quotient s // q ∈ F} // classDisc n H hn1' i.1 ≤ Y}
        ≤ Nat.card {q : Quotient s // classDisc n H hn1' q ≤ Y} := by
    intro Y
    refine Nat.card_le_card_of_injective
      (fun i : {i : {q : Quotient s // q ∈ F} // classDisc n H hn1' i.1 ≤ Y} =>
        (⟨i.1.1, i.2⟩ : {q : Quotient s // classDisc n H hn1' q ≤ Y})) ?_
    intro a b hab
    have h1 : (a.1.1 : Quotient s) = b.1.1 :=
      congr_arg (fun x : {q : Quotient s // classDisc n H hn1' q ≤ Y} => (x : Quotient s)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hcount : ∀ Y : ℕ, ((Finset.univ.filter (fun i : {q : Quotient s // q ∈ F} =>
        classDisc n H hn1' i.1 ≤ Y)).card : ℝ) ≤ c₂ * (Y : ℝ) ^ β := by
    intro Y
    rw [card_filter_eq_natCard]
    rcases Y with _ | Y
    · have hemp : Nat.card {i : {q : Quotient s // q ∈ F} // classDisc n H hn1' i.1 ≤ 0} = 0 := by
        rw [Nat.card_eq_fintype_card]
        haveI : IsEmpty {i : {q : Quotient s // q ∈ F} // classDisc n H hn1' i.1 ≤ 0} :=
          ⟨fun i => by
            have h3 := one_le_classDisc n H hn1' i.1.1
            have h4 := i.2
            omega⟩
        exact Fintype.card_eq_zero
      rw [hemp, Nat.cast_zero]
      exact mul_nonneg hc₂ (Real.rpow_nonneg (le_refl 0) β)
    · exact le_trans (by exact_mod_cast hcount_nat (Y + 1)) (hSCb H (Y + 1) (by omega))
  have hsum : (∑ i : {q : Quotient s // q ∈ F}, (classDisc n H hn1' i.1 : ℝ) ^ (-α))
      ≤ C₂ * c₂ * (X : ℝ) ^ γ := by
    have h1 := hdyad (fun i : {q : Quotient s // q ∈ F} => classDisc n H hn1' i.1) c₂ X
      hc₂ (by exact_mod_cast hX : (1 : ℝ) ≤ (X : ℝ))
      (fun i => one_le_classDisc n H hn1' i.1)
      (fun i => by
        have hmem : classDisc n H hn1' i.1 ≤ X := by
          have h2 : i.1 ∈ Finset.univ.filter (fun q : Quotient s => classDisc n H hn1' q ≤ X) := i.2
          exact (Finset.mem_filter.mp h2).2
        exact_mod_cast hmem)
      hcount
    rwa [hγ] at h1
  have hattach : (∑ q ∈ F, (classDisc n H hn1' q : ℝ) ^ (-α))
      = ∑ i : {q : Quotient s // q ∈ F}, (classDisc n H hn1' i.1 : ℝ) ^ (-α) :=
    (Finset.sum_attach _ _).symm
  calc ((Nat.card {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} : ℕ) : ℝ)
      ≤ ((∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1' q ≤ X)),
          Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q}) : ℕ) := by
        exact Nat.cast_le.mpr hcard1
    _ = ∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1' q ≤ X)),
          ((Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
    _ ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1' q ≤ X)),
              (classDisc n H hn1' q : ℝ) ^ (-α)) := hcard2
    _ ≤ C₁ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (C₂ * c₂ * (X : ℝ) ^ γ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hattach]
        exact hsum
    _ = C₁ * C₂ * c₂ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ γ := by ring
    _ = C₁ * C₂ * c₂ * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (X : ℝ) ^ (β - α) := by rw [hγ]


/-! ## The Case-II slice at the Weyl threshold with a general fibre exponent -/

/-- **Case II at the threshold `2 + 4/M`, from the Abel-refined count bound with
fibre exponent `α`.**  The region `SubcaseIM_P2 n M H` sits inside the
`CaseIICountBoundExp`-region with discriminant at most `⌈H^(2+4/M)⌉`; the
cumulative bound evaluated at that modulus gives the exponent
`1 + (2 + 4/M)·(β − α)`, and the logarithmic factor is absorbed by the power
saving. -/
theorem SubcaseIM_P2_isBigO_of_countBoundExp (n M : ℕ) (β α : ℝ) (hn : 3 ≤ n)
    (hM4 : 4 * n ≤ M)
    (hβα : α < β)
    (hexp : 1 + (2 + 4 / (M : ℝ)) * (β - α) < (n : ℝ) - 1)
    (h : CaseIICountBoundExp n β α) :
    (fun H : ℕ => ((SubcaseIM_P2 n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  obtain ⟨C, hC, hCb⟩ := h
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  set γ : ℝ := β - α with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  set κ : ℝ := 1 + (2 + 4 / (M : ℝ)) * γ with hκdef
  have hκ : κ < (n : ℝ) - 1 := by rw [hκdef, hγdef]; exact hexp
  set δ : ℝ := ((n : ℝ) - 1 - κ) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hlog : ∀ᶠ H : ℕ in atTop,
      (1 + Real.log (H : ℝ)) ^ (n - 1) ≤ (H : ℝ) ^ δ := by
    have h1 := Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
      (n - 1) 1 δ hδ
    filter_upwards [h1] with H hH
    simpa using hH
  have hXpow : ∀ (H X : ℕ), 1 ≤ H → (X : ℝ) ≤ 2 * (H : ℝ) ^ (2 + 4 / (M : ℝ)) →
      (X : ℝ) ^ γ ≤ 2 ^ γ * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ) := by
    intro H X hH1 hXle
    have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hH1R
    calc (X : ℝ) ^ γ ≤ (2 * (H : ℝ) ^ (2 + 4 / (M : ℝ))) ^ γ :=
          Real.rpow_le_rpow (by positivity) hXle hγ.le
      _ = 2 ^ γ * ((H : ℝ) ^ (2 + 4 / (M : ℝ))) ^ γ :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ = 2 ^ γ * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ) := by
          rw [Real.rpow_mul hHpos.le]
  have hbound : ∀ᶠ H : ℕ in atTop,
      ((SubcaseIM_P2 n M H).ncard : ℝ) ≤ C * 2 ^ γ * (H : ℝ) ^ ((n : ℝ) - 1) := by
    filter_upwards [hlog, eventually_ge_atTop (1 : ℕ)] with H hlogH hH1
    have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hH1R
    set X : ℕ := Nat.ceil ((H : ℝ) ^ (2 + 4 / (M : ℝ))) with hX
    have hX1 : 1 ≤ X := by
      rw [hX]
      have h2 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + 4 / (M : ℝ)) :=
        Real.one_le_rpow hH1R (by positivity)
      have h3 : (1 : ℝ) ≤ ((Nat.ceil ((H : ℝ) ^ (2 + 4 / (M : ℝ)))) : ℕ) :=
        le_trans h2 (Nat.le_ceil _)
      exact_mod_cast h3
    have hsub : SubcaseIM_P2 n M H ⊆ SubcaseI_P2 n H :=
      SubcaseIM_P2_subset_SubcaseI_P2 n M H hn hM4 hH1
    have hmem_le : ∀ (f : ℤ[X]) (hf : f ∈ SubcaseIM_P2 n M H),
        (subcaseI_P2_disc n H ⟨f, hsub hf⟩ : ℝ) ≤ (X : ℝ) := by
      intro f hf
      have hfmem := hf
      obtain ⟨-, h, hD⟩ := hf
      have heq : subcaseI_P2_disc n H ⟨f, hsub hfmem⟩ = fieldDiscExp f h := rfl
      rw [heq]
      calc (fieldDiscExp f h : ℝ) ≤ (H : ℝ) ^ (2 + 4 / (M : ℝ)) := hD
        _ ≤ (X : ℝ) := by rw [hX]; exact Nat.le_ceil _
    haveI hfinI : Fintype ↥(SubcaseI_P2 n H) :=
      ((box_finite n H).subset (subcaseI_P2_subset_Box n H)).fintype
    have hcardle : (SubcaseIM_P2 n M H).ncard ≤
        Nat.card {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} := by
      rw [← Nat.card_coe_set_eq]
      refine Nat.card_le_card_of_injective
        (fun f : ↥(SubcaseIM_P2 n M H) =>
          (⟨⟨f.1, hsub f.2⟩, hmem_le f.1 f.2⟩ :
            {g : ↥(SubcaseI_P2 n H) // (subcaseI_P2_disc n H g : ℝ) ≤ (X : ℝ)})) ?_
      intro a b hab
      exact Subtype.ext (congrArg (fun x => x.1.1) hab)
    have hcast : ((SubcaseIM_P2 n M H).ncard : ℝ) ≤
        ((Nat.card {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} : ℕ) : ℝ) := by
      exact_mod_cast hcardle
    have happly := hCb H X hX1
    have hXle : (X : ℝ) ≤ 2 * (H : ℝ) ^ (2 + 4 / (M : ℝ)) := by
      have h1 : (X : ℝ) < (H : ℝ) ^ (2 + 4 / (M : ℝ)) + 1 := by
        rw [hX]; exact Nat.ceil_lt_add_one (by positivity)
      have h2 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + 4 / (M : ℝ)) :=
        Real.one_le_rpow hH1R (by positivity)
      linarith
    have hXp := hXpow H X hH1 hXle
    have hlogle : (Real.log (H : ℝ)) ^ (n - 1) ≤ (1 + Real.log (H : ℝ)) ^ (n - 1) :=
      pow_le_pow_left₀ (Real.log_nonneg hH1R) (by linarith) (n - 1)
    have hκδ : κ + δ ≤ (n : ℝ) - 1 := by rw [hδdef]; linarith
    calc ((SubcaseIM_P2 n M H).ncard : ℝ)
        ≤ C * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ γ :=
          le_trans hcast happly
      _ ≤ C * (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ γ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogle (by positivity))
            (by positivity)
      _ ≤ C * (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1)
            * (2 ^ γ * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ)) :=
          mul_le_mul_of_nonneg_left hXp (by positivity)
      _ = C * 2 ^ γ * ((H : ℝ) ^ κ * (1 + Real.log (H : ℝ)) ^ (n - 1)) := by
          have hrw1 : (H : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ) = (H : ℝ) ^ κ := by
            have h1 : (H : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ)
                = (H : ℝ) ^ (1 : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ) := by
              rw [Real.rpow_one]
            rw [h1, (Real.rpow_add hHpos 1 _).symm]
          have hstep : C * (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1)
                * (2 ^ γ * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ))
              = C * 2 ^ γ * ((H : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ))
                * (1 + Real.log (H : ℝ)) ^ (n - 1) := by ring
          calc C * (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1)
                * (2 ^ γ * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ))
              = C * 2 ^ γ * ((H : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * γ))
                * (1 + Real.log (H : ℝ)) ^ (n - 1) := hstep
            _ = C * 2 ^ γ * ((H : ℝ) ^ κ * (1 + Real.log (H : ℝ)) ^ (n - 1)) := by
                rw [hrw1]; ring
      _ ≤ C * 2 ^ γ * ((H : ℝ) ^ κ * (H : ℝ) ^ δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hlogH (by positivity)
      _ = C * 2 ^ γ * (H : ℝ) ^ (κ + δ) := by rw [← Real.rpow_add hHpos]
      _ ≤ C * 2 ^ γ * (H : ℝ) ^ ((n : ℝ) - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hH1R hκδ
  refine IsBigO.of_bound (C * 2 ^ γ) ?_
  filter_upwards [hbound] with H hH
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  rw [← Real.rpow_natCast (H : ℝ) (n - 1)]
  have hcast : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hcast]
  exact hH


/-! ## Monotonicity of the field-count input -/

/-- The field-count bound is monotone in the exponent (the discriminant is
`≥ 1`). -/
theorem FieldCountBound_mono (n : ℕ) (hn : 1 ≤ n) {β β' : ℝ} (h : β ≤ β')
    (hb : FieldCountBound n hn β) : FieldCountBound n hn β' := by
  obtain ⟨c, hc, hcb⟩ := hb
  refine ⟨c, hc, ?_⟩
  intro H Y hY
  refine (hcb H Y hY).trans ?_
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY1 h) hc

/-! ## The challenge theorem from the field-count input and a fibre exponent -/

/-- **The challenge theorem from `FieldCountBound n β` and the per-field fibre
bound with exponent `α`** (plus the imprimitive bound), whenever
`1 + (2 + 4/weylM n)(β − α) < n − 1`.  The §4 Fourier input, the region
analysis and the reducible half are unconditional. -/
theorem theorem_1_of_field_inputs_exp (n : ℕ) (hn : 3 ≤ n) (β α : ℝ)
    (hβα : α < β)
    (hexp : 1 + (2 + 4 / (weylM n : ℝ)) * (β - α) < (n : ℝ) - 1)
    (hfib : PerFieldFibreBoundExp n (by omega : 1 ≤ n) α)
    (hSC : FieldCountBound n (by omega : 1 ≤ n) β)
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨c, hc, hper⟩ := perIrrBoundTheta_weyl n hn
  have hper' : PerIrrBoundTheta n ((2 : ℝ) / (weylM n : ℝ)) c := by
    rw [two_div_weylM n hn]; exact hper
  have h2 : (fun H : ℕ => ((SubcaseIM_P2 n (weylM n) H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
    SubcaseIM_P2_isBigO_of_countBoundExp n (weylM n) β α hn (four_mul_le_weylM n) hβα hexp
      (caseIICountBoundExp_of_field_inputs n (by omega) β α hβα hfib hSC)
  exact theorem_1_of_M_P2M n (weylM n) c hn (one_le_weylM n hn) (le_weylM n)
    (four_mul_le_weylM n) (weylM_exponentM n hn) (weylM_exponentM2 n hn) hc hper' h2 h4

/-! ## The exponent conditions for the sharp fibre exponent `α = 1/2` -/

lemma weylM_ge_128 (n : ℕ) (hn : 5 ≤ n) : 128 ≤ weylM n := by
  simp only [weylM]
  have h2 : (32 : ℕ) ≤ 2 ^ n := by
    have h : (32 : ℕ) = 2 ^ 5 := by norm_num
    rw [h]
    exact pow_le_pow_right₀ (by norm_num) hn
  calc (128:ℕ) = (4 * 1) * 32 := by norm_num
    _ ≤ (4 * n) * 32 := Nat.mul_le_mul_right 32 (Nat.mul_le_mul_left 4 (by omega))
    _ ≤ (4 * n) * 2 ^ n := Nat.mul_le_mul_left (4 * n) h2

/-- With `α = 1/2` and Schmidt's `β = (n+2)/4`, the exponent condition of
`theorem_1_of_field_inputs_exp` holds for all `n ≥ 5`. -/
lemma exponent_schmidt_sharp (n : ℕ) (hn : 5 ≤ n) :
    1 + (2 + 4 / (weylM n : ℝ)) * (((n : ℝ) + 2) / 4 - 1 / 2) < (n : ℝ) - 1 := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hW : (128 : ℝ) ≤ (weylM n : ℝ) := by exact_mod_cast weylM_ge_128 n hn
  have hWpos : (0 : ℝ) < (weylM n : ℝ) := by linarith
  have hcoef : 4 / (weylM n : ℝ) ≤ 1 / 32 := by
    rw [div_le_iff₀ hWpos]
    nlinarith
  have hd : ((n : ℝ) + 2) / 4 - 1 / 2 = (n : ℝ) / 4 := by ring
  rw [hd]
  have hkey : (2 + 4 / (weylM n : ℝ)) * ((n : ℝ) / 4) ≤ (65 / 128) * (n : ℝ) := by
    have h1 : 2 + 4 / (weylM n : ℝ) ≤ 2 + 1 / 32 := by linarith
    have h2 : (0 : ℝ) ≤ (n : ℝ) / 4 := by linarith
    calc (2 + 4 / (weylM n : ℝ)) * ((n : ℝ) / 4) ≤ (2 + 1 / 32) * ((n : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = (65 / 128) * (n : ℝ) := by ring
  have hfin : (65 / 128) * (n : ℝ) < (n : ℝ) - 2 := by nlinarith
  linarith

/-- With `α = 1/2` and `β = 1` (the exact quartic count), the exponent
condition holds in degree `4`. -/
lemma exponent_quartic_sharp :
    1 + (2 + 4 / (weylM 4 : ℝ)) * ((1 : ℝ) - 1 / 2) < (4 : ℝ) - 1 := by
  norm_num [weylM]

/-- With `α = 1/2` and `β = 3/5` (which follows from Cohn's `β = 1/2` for
cyclic cubic fields), the exponent condition holds in degree `3`. -/
lemma exponent_cubic_sharp :
    1 + (2 + 4 / (weylM 3 : ℝ)) * ((3 / 5 : ℝ) - 1 / 2) < (3 : ℝ) - 1 := by
  norm_num [weylM]

/-! ## Degree-wise endpoints -/

/-- **Sharp fibre bound + Schmidt: the challenge theorem for `n ≥ 5`** (only the
imprimitive bound remains as an input). -/
theorem theorem_1_of_schmidt_sharp (n : ℕ) (hn : 5 ≤ n)
    (hfib : PerFieldFibreBoundExp n (by omega : 1 ≤ n) (1 / 2))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_field_inputs_exp n (by omega) (((n : ℝ) + 2) / 4) (1 / 2)
    (by have h5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith)
    (exponent_schmidt_sharp n hn) hfib
    (fieldCountBound_schmidt n (by omega)) h4

/-- **Sharp fibre bound + Schmidt, prime degree `n ≥ 5`**: unconditional apart
from the sharp per-field fibre bound (the imprimitive input is vacuous in prime
degree).  This removes the need for the exact quintic field count. -/
theorem theorem_1_of_schmidt_sharp_prime (n : ℕ) (hn : 5 ≤ n) (hp : Nat.Prime n)
    (hfib : PerFieldFibreBoundExp n (by omega : 1 ≤ n) (1 / 2)) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_schmidt_sharp n hn hfib (ImprimitiveBad_isBigO_of_prime n hp)

/-- **Sharp fibre bound + the exact quartic count: the challenge theorem in
degree `4`** (the imprimitive input is the machine-checked `O(H^3)` bound). -/
theorem theorem_1_of_quartic_sharp
    (hfib : PerFieldFibreBoundExp 4 (by omega : 1 ≤ 4) (1 / 2))
    (hSC : FieldCountBound 4 (by omega : 1 ≤ 4) 1) :
    (fun H : ℕ => (E 4 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (4 - 1) : ℝ)) :=
  theorem_1_of_field_inputs_exp 4 (by omega) 1 (1 / 2) (by norm_num)
    exponent_quartic_sharp hfib hSC
    (by simpa using ImprimitiveBad_four_isBigO)

/-- **Sharp fibre bound + Cohn's cyclic cubic count: the challenge theorem in
degree `3`.** -/
theorem theorem_1_of_cubic_sharp
    (hfib : PerFieldFibreBoundExp 3 (by omega : 1 ≤ 3) (1 / 2))
    (hSC : FieldCountBound 3 (by omega : 1 ≤ 3) (1 / 2)) :
    (fun H : ℕ => (E 3 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) :=
  theorem_1_of_field_inputs_exp 3 (by omega) (3 / 5) (1 / 2) (by norm_num)
    exponent_cubic_sharp hfib
    (FieldCountBound_mono 3 (by omega) (by norm_num) hSC)
    (ImprimitiveBad_isBigO_of_prime 3 (by norm_num))


/-- **Sharp fibre bound + Schmidt + Widmer: the challenge theorem for composite
`n ≥ 6`**. -/
theorem theorem_1_of_schmidt_widmer_sharp (n : ℕ) (hn : 6 ≤ n)
    (hfib : PerFieldFibreBoundExp n (by omega : 1 ≤ n) (1 / 2))
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_schmidt_sharp n (by omega) hfib (ImprimitiveBad_isBigO_of_widmer n hn hw)

/-- **Sharp fibre bound + the exact quartic/quintic counts: the challenge theorem
for `n = 4, 5`** (the imprimitive input for `n = 4` is the machine-checked
`O(H³)` bound, and `5` is prime). -/
theorem theorem_1_of_quartic_sharp' (n : ℕ) (hn : 4 ≤ n) (hn5 : n ≤ 5)
    (hfib : PerFieldFibreBoundExp n (by omega : 1 ≤ n) (1 / 2))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) 1) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  rcases eq_or_lt_of_le hn with h4 | h5
  · subst h4
    exact theorem_1_of_quartic_sharp hfib hSC
  · have hn5' : n = 5 := by omega
    subst hn5'
    exact theorem_1_of_schmidt_sharp_prime 5 (by omega) (by norm_num) hfib


/-! ## The `+ 1` (lattice-point-with-boundary) form of the fibre bound

The pure form `#{f : M(f) ≤ Y, K_f ≅ K} ≤ C^n Y (log Y)^{n-1}/√|Disc K|` is
**false** when `Y` is small relative to `√|Disc K|`: e.g. `K = ℚ(∛m)` contains
`α = ∛m − ⌊∛m⌋`, whose height is `≍ |Disc K|^{1/3}`, so the fibre is nonempty
while `Y(log Y)^{n-1}/√|Disc K| ≪ 1`.  The correct statement is the standard
lattice-point bound *with boundary error*,

  `#{f : M(f) ≤ Y, K_f ≅ K} ≤ C^n (1 + Y (log Y)^{n-1}/√|Disc K|)`.

This extra `+ 1` is harmless in the Case-II summation: it contributes the
number of field classes, which is itself `≪ X^β`. -/

/-- The per-field fibre bound in "lattice-point with boundary" form. -/
def PerFieldFibreBoundPlus (n : ℕ) (hn : 1 ≤ n) (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, ∀ q : Quotient (fieldIsoSetoid n H hn),
    ((Nat.card {f : ↥(SubcaseI_P2 n H) //
        Quotient.mk (fieldIsoSetoid n H hn) f = q} : ℕ) : ℝ)
      ≤ C * (1 + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (classDisc n H hn q : ℝ) ^ (-α))

/-- **Abel-refined Case-II count in the `+ 1` form**:
`#{f ∈ SubcaseI_P2 n H : |Disc| ≤ X} ≤ C·(X^β + H(log H)^{n-1}X^{β−α})`. -/
def CaseIICountBoundPlus (n : ℕ) (β α : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H X : ℕ, 1 ≤ X →
    ((Nat.card {f : ↥(SubcaseI_P2 n H) //
        (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} : ℕ) : ℝ)
      ≤ C * ((X : ℝ) ^ β + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α))

/-- **The `+ 1` form from the two inputs**: the boundary term contributes the
number of classes (`FieldCountBound`), the main term the Abel sum. -/
theorem caseIICountBoundPlus_of_field_inputs (n : ℕ) (hn1 : 2 ≤ n) (β α : ℝ)
    (hαβ : α < β)
    (hfib : PerFieldFibreBoundPlus n (by omega : 1 ≤ n) α)
    (hSC : FieldCountBound n (by omega : 1 ≤ n) β) :
    CaseIICountBoundPlus n β α := by
  classical
  have hn1' : 1 ≤ n := by omega
  have hfib' : PerFieldFibreBoundPlus n hn1' α := hfib
  have hSC' : FieldCountBound n hn1' β := hSC
  obtain ⟨C₁, hC₁, hfibb⟩ := hfib'
  obtain ⟨c₂, hc₂, hSCb⟩ := hSC'
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  obtain ⟨C₂, hC₂, hdyad⟩ :=
    Commons.Analysis.Sum.exists_sum_rpow_neg_le_of_card_le_fintype α β hαβ
  set γ : ℝ := β - α with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  refine ⟨C₁ * (c₂ + C₂ * c₂), by positivity, ?_⟩
  intro H X hX
  haveI : Fintype ↥(SubcaseI_P2 n H) :=
    ((box_finite n H).subset (subcaseI_P2_subset_Box n H)).fintype
  haveI : Fintype (Quotient (fieldIsoSetoid n H hn1')) := Quotient.fintype _
  set s : Setoid ↥(SubcaseI_P2 n H) := fieldIsoSetoid n H hn1' with hs
  let F : Finset (Quotient s) := Finset.univ.filter (fun q => classDisc n H hn1' q ≤ X)
  -- (1) the counted set is the union of its class fibres
  have hcard1' : Nat.card {f : ↥(SubcaseI_P2 n H) //
        (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)}
      ≤ ∑ q ∈ (Finset.univ.filter (fun q : Quotient s => classDisc n H hn1' q ≤ X)),
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
      (fun q : Quotient s => classDisc n H hn1' q ≤ X)
      (fun q => Nat.card {f : {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} // Quotient.mk s f.1 = q})]
    have hzero : ∑ q ∈ Finset.univ.filter (fun q : Quotient s => ¬ classDisc n H hn1' q ≤ X),
        Nat.card {f : {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} // Quotient.mk s f.1 = q} = 0 := by
      refine Finset.sum_eq_zero (fun q hq => ?_)
      rw [Finset.mem_filter] at hq
      rw [Nat.card_eq_fintype_card]
      haveI : IsEmpty {f : {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} // Quotient.mk s f.1 = q} :=
        ⟨fun f => by
          have hdisc : subcaseI_P2_disc n H f.1 ≤ X := Nat.cast_le.mp f.1.2
          have hcls : classDisc n H hn1' q = subcaseI_P2_disc n H f.1 := by
            have h1 := congrArg (fun x => classDisc n H hn1' x) f.2
            rw [classDisc_mk n H hn1' f.1] at h1
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
  have hcard1 : Nat.card {f : ↥(SubcaseI_P2 n H) //
        (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)}
      ≤ ∑ q ∈ F, Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} := hcard1'
  -- (2) the per-class `+1` fibre bound
  have hcard2 : (∑ q ∈ F, ((Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} : ℕ) : ℝ))
      ≤ C₁ * ((F.card : ℝ) + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (∑ q ∈ F, (classDisc n H hn1' q : ℝ) ^ (-α))) := by
    have h1 : ∀ q ∈ F, ((Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} : ℕ) : ℝ)
        ≤ C₁ * (1 + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
            * (classDisc n H hn1' q : ℝ) ^ (-α)) := fun q _ => hfibb H q
    calc (∑ q ∈ F, ((Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} : ℕ) : ℝ))
        ≤ ∑ q ∈ F, C₁ * (1 + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
            * (classDisc n H hn1' q : ℝ) ^ (-α)) := Finset.sum_le_sum h1
      _ = C₁ * ((F.card : ℝ) + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
            * (∑ q ∈ F, (classDisc n H hn1' q : ℝ) ^ (-α))) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
  -- (3) the number of classes
  have hclasses : (F.card : ℝ) ≤ c₂ * (X : ℝ) ^ β := by
    have hle : F.card ≤ Nat.card {q : Quotient s // classDisc n H hn1' q ≤ X} := by
      have h1 : F = Finset.univ.filter (fun q => classDisc n H hn1' q ≤ X) := rfl
      rw [h1, card_filter_eq_natCard]
    exact le_trans (by exact_mod_cast hle) (hSCb H X hX)
  -- (4) the Abel sum of the weights
  have hcount_nat : ∀ Y : ℕ,
      Nat.card {i : {q : Quotient s // q ∈ F} // classDisc n H hn1' i.1 ≤ Y}
        ≤ Nat.card {q : Quotient s // classDisc n H hn1' q ≤ Y} := by
    intro Y
    refine Nat.card_le_card_of_injective
      (fun i : {i : {q : Quotient s // q ∈ F} // classDisc n H hn1' i.1 ≤ Y} =>
        (⟨i.1.1, i.2⟩ : {q : Quotient s // classDisc n H hn1' q ≤ Y})) ?_
    intro a b hab
    have h1 : (a.1.1 : Quotient s) = b.1.1 :=
      congr_arg (fun x : {q : Quotient s // classDisc n H hn1' q ≤ Y} => (x : Quotient s)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hcount : ∀ Y : ℕ, ((Finset.univ.filter (fun i : {q : Quotient s // q ∈ F} =>
        classDisc n H hn1' i.1 ≤ Y)).card : ℝ) ≤ c₂ * (Y : ℝ) ^ β := by
    intro Y
    rw [card_filter_eq_natCard]
    rcases Y with _ | Y
    · have hemp : Nat.card {i : {q : Quotient s // q ∈ F} // classDisc n H hn1' i.1 ≤ 0} = 0 := by
        rw [Nat.card_eq_fintype_card]
        haveI : IsEmpty {i : {q : Quotient s // q ∈ F} // classDisc n H hn1' i.1 ≤ 0} :=
          ⟨fun i => by
            have h3 := one_le_classDisc n H hn1' i.1.1
            have h4 := i.2
            omega⟩
        exact Fintype.card_eq_zero
      rw [hemp, Nat.cast_zero]
      exact mul_nonneg hc₂ (Real.rpow_nonneg (le_refl 0) β)
    · exact le_trans (by exact_mod_cast hcount_nat (Y + 1)) (hSCb H (Y + 1) (by omega))
  have hw : (∑ q ∈ F, (classDisc n H hn1' q : ℝ) ^ (-α)) ≤ C₂ * c₂ * (X : ℝ) ^ γ := by
    have h1 := hdyad (fun i : {q : Quotient s // q ∈ F} => classDisc n H hn1' i.1) c₂ X
      hc₂ (by exact_mod_cast hX : (1 : ℝ) ≤ (X : ℝ))
      (fun i => one_le_classDisc n H hn1' i.1)
      (fun i => by
        have hmem : classDisc n H hn1' i.1 ≤ X := (Finset.mem_filter.mp i.2).2
        exact_mod_cast hmem)
      hcount
    have hatt : (∑ q ∈ F, (classDisc n H hn1' q : ℝ) ^ (-α))
        = ∑ i : {q : Quotient s // q ∈ F}, (classDisc n H hn1' i.1 : ℝ) ^ (-α) :=
      (Finset.sum_attach _ _).symm
    rw [hatt, hγ]
    exact h1
  -- (5) assemble
  calc ((Nat.card {f : ↥(SubcaseI_P2 n H) //
        (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} : ℕ) : ℝ)
      ≤ ((∑ q ∈ F, Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q}) : ℕ) :=
        Nat.cast_le.mpr hcard1
    _ = ∑ q ∈ F, ((Nat.card {f : ↥(SubcaseI_P2 n H) // Quotient.mk s f = q} : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
    _ ≤ C₁ * ((F.card : ℝ) + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (∑ q ∈ F, (classDisc n H hn1' q : ℝ) ^ (-α))) := hcard2
    _ ≤ C₁ * (c₂ * (X : ℝ) ^ β + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (C₂ * c₂ * (X : ℝ) ^ γ)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hclasses ?_) hC₁
        exact mul_le_mul_of_nonneg_left hw (by positivity)
    _ = C₁ * (c₂ * (X : ℝ) ^ β
          + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (C₂ * c₂ * (X : ℝ) ^ (β - α))) := by
        rw [hγ]
    _ ≤ C₁ * (c₂ + C₂ * c₂) * ((X : ℝ) ^ β
          + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α)) := by
        have hA : (0 : ℝ) ≤ (X : ℝ) ^ β := Real.rpow_nonneg (Nat.cast_nonneg X) _
        have hB : (0 : ℝ) ≤ (X : ℝ) ^ (β - α) := Real.rpow_nonneg (Nat.cast_nonneg X) _
        have hL0 : (0 : ℝ) ≤ (Real.log (H : ℝ)) ^ (n - 1) := by positivity
        have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
        have h3 : (0 : ℝ) ≤ C₂ * c₂ := mul_nonneg hC₂ hc₂
        have hT : (0 : ℝ) ≤ (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α) :=
          mul_nonneg (mul_nonneg hH0 hL0) hB
        have hle : c₂ * (X : ℝ) ^ β
              + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (C₂ * c₂ * (X : ℝ) ^ (β - α))
            ≤ (c₂ + C₂ * c₂) * ((X : ℝ) ^ β
              + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α)) := by
          have e1 : c₂ * (X : ℝ) ^ β ≤ (c₂ + C₂ * c₂) * (X : ℝ) ^ β :=
            mul_le_mul_of_nonneg_right (by linarith) hA
          have e2 : (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (C₂ * c₂ * (X : ℝ) ^ (β - α))
              ≤ (c₂ + C₂ * c₂) * ((H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α)) := by
            have hT' : (0 : ℝ) ≤ (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α) :=
              mul_nonneg (mul_nonneg hH0 hL0) hB
            calc (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (C₂ * c₂ * (X : ℝ) ^ (β - α))
                = ((H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α)) * (C₂ * c₂) := by
                  ring
              _ ≤ ((H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α)) * (c₂ + C₂ * c₂) :=
                  mul_le_mul_of_nonneg_left (by linarith) hT'
              _ = (c₂ + C₂ * c₂) * ((H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α)) := by
                  ring
          rw [mul_add]
          linarith [e1, e2]
        calc C₁ * (c₂ * (X : ℝ) ^ β
              + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (C₂ * c₂ * (X : ℝ) ^ (β - α)))
            ≤ C₁ * ((c₂ + C₂ * c₂) * ((X : ℝ) ^ β
              + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α))) :=
              mul_le_mul_of_nonneg_left hle hC₁
          _ = C₁ * (c₂ + C₂ * c₂) * ((X : ℝ) ^ β
              + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α)) := by ring

/-- **The Case-II slice at the Weyl threshold in the `+ 1` form**: the slice is
`O(H^{n-1})` whenever `(2 + 4/M)β < n − 1` and `1 + (2 + 4/M)(β − α) < n − 1`. -/
theorem SubcaseIM_P2_isBigO_of_countBoundPlus (n M : ℕ) (β α : ℝ) (hn : 3 ≤ n)
    (hM4 : 4 * n ≤ M)
    (hαβ : α < β) (hβ0 : 0 ≤ β)
    (hexp1 : (2 + 4 / (M : ℝ)) * β < (n : ℝ) - 1)
    (hexp2 : 1 + (2 + 4 / (M : ℝ)) * (β - α) < (n : ℝ) - 1)
    (h : CaseIICountBoundPlus n β α) :
    (fun H : ℕ => ((SubcaseIM_P2 n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  obtain ⟨C, hC, hCb⟩ := h
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  -- power-saving exponents for the two terms
  set δ₁ : ℝ := ((n : ℝ) - 1 - (2 + 4 / (M : ℝ)) * β) / 2 with hδ₁def
  have hδ₁ : 0 < δ₁ := by rw [hδ₁def]; linarith
  set δ : ℝ := ((n : ℝ) - 1 - (1 + (2 + 4 / (M : ℝ)) * (β - α))) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hlog1 : ∀ᶠ H : ℕ in atTop, (1 : ℝ) ≤ (H : ℝ) ^ δ₁ := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH1
    exact Real.one_le_rpow (by exact_mod_cast hH1) (le_of_lt hδ₁)
  have hlog : ∀ᶠ H : ℕ in atTop,
      (1 + Real.log (H : ℝ)) ^ (n - 1) ≤ (H : ℝ) ^ δ := by
    have h1 := Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
      (n - 1) 1 δ hδ
    filter_upwards [h1] with H hH
    simpa using hH
  have hbound : ∀ᶠ H : ℕ in atTop,
      ((SubcaseIM_P2 n M H).ncard : ℝ)
        ≤ (C * (2 ^ β + 2 ^ (β - α) + 1)) * (H : ℝ) ^ ((n : ℝ) - 1) := by
    filter_upwards [hlog, hlog1, eventually_ge_atTop (1 : ℕ)] with H hlogH hlogH1 hH1
    have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hH1R
    set X : ℕ := Nat.ceil ((H : ℝ) ^ (2 + 4 / (M : ℝ))) with hX
    have hX1 : 1 ≤ X := by
      rw [hX]
      have h2 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + 4 / (M : ℝ)) := Real.one_le_rpow hH1R (by positivity)
      have h3 : (1 : ℝ) ≤ ((Nat.ceil ((H : ℝ) ^ (2 + 4 / (M : ℝ)))) : ℕ) := le_trans h2 (Nat.le_ceil _)
      exact_mod_cast h3
    have hsub : SubcaseIM_P2 n M H ⊆ SubcaseI_P2 n H :=
      SubcaseIM_P2_subset_SubcaseI_P2 n M H hn hM4 hH1
    have hmem_le : ∀ (f : ℤ[X]) (hf : f ∈ SubcaseIM_P2 n M H),
        (subcaseI_P2_disc n H ⟨f, hsub hf⟩ : ℝ) ≤ (X : ℝ) := by
      intro f hf
      have hfmem := hf
      obtain ⟨-, h, hD⟩ := hf
      have heq : subcaseI_P2_disc n H ⟨f, hsub hfmem⟩ = fieldDiscExp f h := rfl
      rw [heq]
      calc (fieldDiscExp f h : ℝ) ≤ (H : ℝ) ^ (2 + 4 / (M : ℝ)) := hD
        _ ≤ (X : ℝ) := by rw [hX]; exact Nat.le_ceil _
    haveI hfinI : Fintype ↥(SubcaseI_P2 n H) :=
      ((box_finite n H).subset (subcaseI_P2_subset_Box n H)).fintype
    have hcardle : (SubcaseIM_P2 n M H).ncard ≤
        Nat.card {f : ↥(SubcaseI_P2 n H) // (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} := by
      rw [← Nat.card_coe_set_eq]
      refine Nat.card_le_card_of_injective
        (fun f : ↥(SubcaseIM_P2 n M H) =>
          (⟨⟨f.1, hsub f.2⟩, hmem_le f.1 f.2⟩ :
            {g : ↥(SubcaseI_P2 n H) // (subcaseI_P2_disc n H g : ℝ) ≤ (X : ℝ)})) ?_
      intro a b hab
      exact Subtype.ext (congrArg (fun x => x.1.1) hab)
    have hcast : ((SubcaseIM_P2 n M H).ncard : ℝ) ≤
        ((Nat.card {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} : ℕ) : ℝ) := by
      exact_mod_cast hcardle
    have happly := hCb H X hX1
    have hXle : (X : ℝ) ≤ 2 * (H : ℝ) ^ (2 + 4 / (M : ℝ)) := by
      have h1 : (X : ℝ) < (H : ℝ) ^ (2 + 4 / (M : ℝ)) + 1 := by
        rw [hX]; exact Nat.ceil_lt_add_one (by positivity)
      have h2 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + 4 / (M : ℝ)) := Real.one_le_rpow hH1R (by positivity)
      linarith
    have hp1 : (X : ℝ) ^ β ≤ 2 ^ β * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * β) := by
      calc (X : ℝ) ^ β ≤ (2 * (H : ℝ) ^ (2 + 4 / (M : ℝ))) ^ β :=
            Real.rpow_le_rpow (by positivity) hXle hβ0
        _ = 2 ^ β * ((H : ℝ) ^ (2 + 4 / (M : ℝ))) ^ β := Real.mul_rpow (by norm_num) (by positivity)
        _ = 2 ^ β * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * β) := by rw [Real.rpow_mul hHpos.le]
    have hp2 : (X : ℝ) ^ (β - α) ≤ 2 ^ (β - α) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * (β - α)) := by
      calc (X : ℝ) ^ (β - α) ≤ (2 * (H : ℝ) ^ (2 + 4 / (M : ℝ))) ^ (β - α) :=
            Real.rpow_le_rpow (by positivity) hXle (by linarith [hαβ])
        _ = 2 ^ (β - α) * ((H : ℝ) ^ (2 + 4 / (M : ℝ))) ^ (β - α) :=
            Real.mul_rpow (by norm_num) (by positivity)
        _ = 2 ^ (β - α) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * (β - α)) := by rw [Real.rpow_mul hHpos.le]
    have hδ₁eq : ((n : ℝ) - 1) - ((2 + 4 / (M : ℝ)) * β) = 2 * δ₁ := by rw [hδ₁def]; ring
    have hδeq : ((n : ℝ) - 1) - (1 + (2 + 4 / (M : ℝ)) * (β - α)) = 2 * δ := by rw [hδdef]; ring
    have hHδ₁ : (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * β) ≤ (H : ℝ) ^ ((n : ℝ) - 1) := by
      refine Real.rpow_le_rpow_of_exponent_le hH1R ?_
      linarith [hexp1]
    have hHδ : (H : ℝ) ^ (1 + (2 + 4 / (M : ℝ)) * (β - α)) ≤ (H : ℝ) ^ ((n : ℝ) - 1) := by
      refine Real.rpow_le_rpow_of_exponent_le hH1R ?_
      linarith [hexp2]
    have hlogle : (Real.log (H : ℝ)) ^ (n - 1) ≤ (1 + Real.log (H : ℝ)) ^ (n - 1) :=
      pow_le_pow_left₀ (Real.log_nonneg hH1R) (by linarith) (n - 1)
    have hkey : (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α)
        ≤ 2 ^ (β - α) * (H : ℝ) ^ (1 + (2 + 4 / (M : ℝ)) * (β - α) + δ) := by
      calc (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α)
          ≤ (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1)
              * (2 ^ (β - α) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * (β - α))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hlogle (Nat.cast_nonneg H)) hp2
              (by positivity) (by positivity)
        _ = 2 ^ (β - α) * ((H : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * (β - α))
              * (1 + Real.log (H : ℝ)) ^ (n - 1)) := by ring
        _ ≤ 2 ^ (β - α) * ((H : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * (β - α))
              * (H : ℝ) ^ δ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine mul_le_mul_of_nonneg_left hlogH (by positivity)
        _ = 2 ^ (β - α) * (H : ℝ) ^ (1 + (2 + 4 / (M : ℝ)) * (β - α) + δ) := by
            have h1 : (H : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * (β - α))
                = (H : ℝ) ^ (1 + (2 + 4 / (M : ℝ)) * (β - α)) := by
              have h2 : (H : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * (β - α))
                  = (H : ℝ) ^ (1 : ℝ) * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * (β - α)) := by
                rw [Real.rpow_one]
              rw [h2, ← Real.rpow_add hHpos]
            rw [h1, ← Real.rpow_add hHpos]
    have hmain : (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α)
        ≤ (2 ^ (β - α) * 1) * (H : ℝ) ^ ((n : ℝ) - 1) := by
      refine le_trans hkey ?_
      have hlt : 1 + (2 + 4 / (M : ℝ)) * (β - α) + δ ≤ (n : ℝ) - 1 := by
        have h2 : 1 + (2 + 4 / (M : ℝ)) * (β - α) < (n : ℝ) - 1 := hexp2
        rw [hδdef]
        linarith [h2]
      calc 2 ^ (β - α) * (H : ℝ) ^ (1 + (2 + 4 / (M : ℝ)) * (β - α) + δ)
          ≤ 2 ^ (β - α) * (H : ℝ) ^ ((n : ℝ) - 1) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hH1R hlt) (by positivity)
        _ = (2 ^ (β - α) * 1) * (H : ℝ) ^ ((n : ℝ) - 1) := by ring
    have hbase : (X : ℝ) ^ β ≤ (2 ^ β * 1) * (H : ℝ) ^ ((n : ℝ) - 1) := by
      refine le_trans hp1 ?_
      calc 2 ^ β * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * β)
          = 2 ^ β * (H : ℝ) ^ ((2 + 4 / (M : ℝ)) * β) := rfl
        _ ≤ 2 ^ β * (H : ℝ) ^ ((n : ℝ) - 1) :=
            mul_le_mul_of_nonneg_left hHδ₁ (by positivity)
        _ = (2 ^ β * 1) * (H : ℝ) ^ ((n : ℝ) - 1) := by ring
    calc ((SubcaseIM_P2 n M H).ncard : ℝ)
        ≤ C * ((X : ℝ) ^ β + (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ (β - α)) :=
          le_trans hcast happly
      _ ≤ C * ((2 ^ β * 1) * (H : ℝ) ^ ((n : ℝ) - 1)
            + (2 ^ (β - α) * 1) * (H : ℝ) ^ ((n : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left (add_le_add hbase hmain) hC
      _ ≤ (C * (2 ^ β + 2 ^ (β - α) + 1)) * (H : ℝ) ^ ((n : ℝ) - 1) := by
          have hT : (0 : ℝ) ≤ (H : ℝ) ^ ((n : ℝ) - 1) := Real.rpow_nonneg (Nat.cast_nonneg H) _
          have hstep : C * ((2 ^ β * 1) * (H : ℝ) ^ ((n : ℝ) - 1)
              + (2 ^ (β - α) * 1) * (H : ℝ) ^ ((n : ℝ) - 1))
              = C * (2 ^ β + 2 ^ (β - α)) * (H : ℝ) ^ ((n : ℝ) - 1) := by ring
          rw [hstep]
          have h1 : (0 : ℝ) ≤ C * (H : ℝ) ^ ((n : ℝ) - 1) := mul_nonneg hC hT
          nlinarith [h1]
  refine IsBigO.of_bound (C * (2 ^ β + 2 ^ (β - α) + 1)) ?_
  filter_upwards [hbound] with H hH
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  rw [← Real.rpow_natCast (H : ℝ) (n - 1)]
  have hcast : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hcast]
  exact hH


/-! ## The challenge theorem from the `+ 1` fibre bound

With the corrected (lattice-point-with-boundary) fibre bound there are **two**
exponent conditions: the boundary term contributes the number of classes,
giving `(2 + 4/M)·β < n − 1`, and the main term the Abel sum, giving
`1 + (2 + 4/M)(β − α) < n − 1`. -/

/-- **The challenge theorem from `FieldCountBound n β`, the `+ 1` per-field
fibre bound with exponent `α`, and the imprimitive bound.** -/
theorem theorem_1_of_field_inputs_plus (n : ℕ) (hn : 3 ≤ n) (β α : ℝ)
    (hαβ : α < β) (hβ0 : 0 ≤ β)
    (hexp1 : (2 + 4 / (weylM n : ℝ)) * β < (n : ℝ) - 1)
    (hexp2 : 1 + (2 + 4 / (weylM n : ℝ)) * (β - α) < (n : ℝ) - 1)
    (hfib : PerFieldFibreBoundPlus n (by omega : 1 ≤ n) α)
    (hSC : FieldCountBound n (by omega : 1 ≤ n) β)
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨c, hc, hper⟩ := perIrrBoundTheta_weyl n hn
  have hper' : PerIrrBoundTheta n ((2 : ℝ) / (weylM n : ℝ)) c := by
    rw [two_div_weylM n hn]; exact hper
  have h2 : (fun H : ℕ => ((SubcaseIM_P2 n (weylM n) H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
    SubcaseIM_P2_isBigO_of_countBoundPlus n (weylM n) β α hn (four_mul_le_weylM n) hαβ hβ0
      hexp1 hexp2
      (caseIICountBoundPlus_of_field_inputs n (by omega) β α hαβ hfib hSC)
  exact theorem_1_of_M_P2M n (weylM n) c hn (one_le_weylM n hn) (le_weylM n)
    (four_mul_le_weylM n) (weylM_exponentM n hn) (weylM_exponentM2 n hn) hc hper' h2 h4

/-- The first exponent condition for Schmidt's `β = (n+2)/4` and `α = 1/2`,
for `n ≥ 5`. -/
lemma exponent_schmidt_plus_one (n : ℕ) (hn : 5 ≤ n) :
    (2 + 4 / (weylM n : ℝ)) * (((n : ℝ) + 2) / 4) < (n : ℝ) - 1 := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hW : (128 : ℝ) ≤ (weylM n : ℝ) := by exact_mod_cast weylM_ge_128 n hn
  have hWpos : (0 : ℝ) < (weylM n : ℝ) := by linarith
  have hcoef : 4 / (weylM n : ℝ) ≤ 1 / 32 := by
    rw [div_le_iff₀ hWpos]; nlinarith
  have hkey : (2 + 4 / (weylM n : ℝ)) * (((n : ℝ) + 2) / 4) ≤ (65 / 128) * ((n : ℝ) + 2) := by
    have h1 : 2 + 4 / (weylM n : ℝ) ≤ 2 + 1 / 32 := by linarith
    have h2 : (0 : ℝ) ≤ ((n : ℝ) + 2) / 4 := by linarith
    calc (2 + 4 / (weylM n : ℝ)) * (((n : ℝ) + 2) / 4) ≤ (2 + 1 / 32) * (((n : ℝ) + 2) / 4) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = (65 / 128) * ((n : ℝ) + 2) := by ring
  have hfin : (65 / 128) * ((n : ℝ) + 2) < (n : ℝ) - 1 := by nlinarith
  linarith

/-- The first exponent condition in degree `4` (with `β = 1`). -/
lemma exponent_quartic_plus_one :
    (2 + 4 / (weylM 4 : ℝ)) * (1 : ℝ) < (4 : ℝ) - 1 := by
  norm_num [weylM]

/-- The first exponent condition in degree `3` (with `β = 3/5`). -/
lemma exponent_cubic_plus_one :
    (2 + 4 / (weylM 3 : ℝ)) * (3 / 5 : ℝ) < (3 : ℝ) - 1 := by
  norm_num [weylM]

/-- **`+ 1` fibre bound + Schmidt: the challenge theorem for `n ≥ 5`** (only
the imprimitive bound remains). -/
theorem theorem_1_of_schmidt_plus (n : ℕ) (hn : 5 ≤ n)
    (hfib : PerFieldFibreBoundPlus n (by omega : 1 ≤ n) (1 / 2))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_field_inputs_plus n (by omega) (((n : ℝ) + 2) / 4) (1 / 2)
    (by
      have h5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith)
    (by positivity) (exponent_schmidt_plus_one n hn) (exponent_schmidt_sharp n hn) hfib
    (fieldCountBound_schmidt n (by omega)) h4

/-- **`+ 1` fibre bound + Schmidt, prime degree `n ≥ 5`**: unconditional apart
from the `+ 1` per-field fibre bound, removing the need for the exact quintic
count. -/
theorem theorem_1_of_schmidt_plus_prime (n : ℕ) (hn : 5 ≤ n) (hp : Nat.Prime n)
    (hfib : PerFieldFibreBoundPlus n (by omega : 1 ≤ n) (1 / 2)) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_schmidt_plus n hn hfib (ImprimitiveBad_isBigO_of_prime n hp)

/-- **`+ 1` fibre bound + Schmidt + Widmer: composite `n ≥ 6`.** -/
theorem theorem_1_of_schmidt_widmer_plus (n : ℕ) (hn : 6 ≤ n)
    (hfib : PerFieldFibreBoundPlus n (by omega : 1 ≤ n) (1 / 2))
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_schmidt_plus n (by omega) hfib (ImprimitiveBad_isBigO_of_widmer n hn hw)

/-- **`+ 1` fibre bound + the exact quartic count: the challenge theorem in
degree `4`.** -/
theorem theorem_1_of_quartic_plus
    (hfib : PerFieldFibreBoundPlus 4 (by omega : 1 ≤ 4) (1 / 2))
    (hSC : FieldCountBound 4 (by omega : 1 ≤ 4) 1) :
    (fun H : ℕ => (E 4 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (4 - 1) : ℝ)) :=
  theorem_1_of_field_inputs_plus 4 (by omega) 1 (1 / 2) (by norm_num) (by norm_num)
    exponent_quartic_plus_one exponent_quartic_sharp hfib hSC
    (by simpa using ImprimitiveBad_four_isBigO)

/-- **`+ 1` fibre bound + Cohn's cyclic cubic count: the challenge theorem in
degree `3`.** -/
theorem theorem_1_of_cubic_plus
    (hfib : PerFieldFibreBoundPlus 3 (by omega : 1 ≤ 3) (1 / 2))
    (hSC : FieldCountBound 3 (by omega : 1 ≤ 3) (1 / 2)) :
    (fun H : ℕ => (E 3 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) :=
  theorem_1_of_field_inputs_plus 3 (by omega) (3 / 5) (1 / 2) (by norm_num) (by norm_num)
    exponent_cubic_plus_one exponent_cubic_sharp hfib
    (FieldCountBound_mono 3 (by omega) (by norm_num) hSC)
    (ImprimitiveBad_isBigO_of_prime 3 (by norm_num))


/-! ## The index-refinement endpoint (fibre exponent `1/(n(n-1))`, field count `n/4`)

The index refinement of Bhargava's Theorem 1.2 (available from the proved
`Commons.FieldTheory.Polynomial.ncard_index_ge_fixed_coeffs_le` together with
Lemma 24 and the CRT arithmetic) yields `FieldCountBound n (n/4 + ε)`.  With the
paper's per-field fibre exponent `α = 1/(n(n-1))` — which is *unconditional* in
every degree (`PerFieldFibreAll.perFieldFibreBound_all`) — the exponent
condition becomes

  `1 + (2 + 4/weylM n)·(n/4 − 1/(n(n−1))) < n − 1`,

true for every `n ≥ 4`.  Hence the index refinement closes `n = 4` and `n = 5`
(the exact quartic/quintic counts are then not needed), while `n = 3` still
requires Cohn's count (`n/4 = 3/4 > 0.657`). -/

/-- The exponent condition for the index refinement, `n ≥ 5`. -/
lemma exponent_index_refine (n : ℕ) (hn : 5 ≤ n) :
    1 + (2 + 4 / (weylM n : ℝ))
        * ((n : ℝ) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1))) < (n : ℝ) - 1 := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hW : (128 : ℝ) ≤ (weylM n : ℝ) := by exact_mod_cast weylM_ge_128 n hn
  have hWpos : (0 : ℝ) < (weylM n : ℝ) := by linarith
  have hcoef : 4 / (weylM n : ℝ) ≤ 1 / 32 := by
    rw [div_le_iff₀ hWpos]; nlinarith
  have hn2 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have h1 : (2 + 4 / (weylM n : ℝ)) * ((n : ℝ) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ (2 + 1 / 32) * ((n : ℝ) / 4) := by
    have hle : (n : ℝ) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ (n : ℝ) / 4 := by
      have : 0 ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
      linarith
    have h2 : (2 + 4 / (weylM n : ℝ)) ≤ 2 + 1 / 32 := by linarith
    have hnn : (0 : ℝ) ≤ (n : ℝ) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      have h3 : (1 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have h4 : 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 := by
        rw [div_le_one hn2]; exact h3
      nlinarith
    calc (2 + 4 / (weylM n : ℝ)) * ((n : ℝ) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
        ≤ (2 + 1 / 32) * ((n : ℝ) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_right h2 hnn
      _ ≤ (2 + 1 / 32) * ((n : ℝ) / 4) := mul_le_mul_of_nonneg_left hle (by norm_num)
  have h2 : (2 + 1 / 32) * ((n : ℝ) / 4) = (65 / 128) * (n : ℝ) := by ring
  have h3 : (65 / 128) * (n : ℝ) < (n : ℝ) - 2 := by nlinarith
  linarith

/-- **The challenge theorem from the index-refined field count, for `n ≥ 4`.** -/
theorem theorem_1_of_indexFieldCount (n : ℕ) (hn : 4 ≤ n)
    (hSC : FieldCountBound n (by omega : 1 ≤ n) ((n : ℝ) / 4))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hfib : PerFieldFibreBoundExp n (by omega : 1 ≤ n)
      (1 / ((n : ℝ) * ((n : ℝ) - 1))) :=
    perFieldFibreBound_exp_classical n (by omega)
      (perFieldFibreBound_all n (by omega))
  rcases eq_or_lt_of_le hn with h4' | h5
  · subst h4'
    have hexp : 1 + (2 + 4 / (weylM 4 : ℝ))
        * ((4 : ℝ) / 4 - 1 / ((4 : ℝ) * ((4 : ℝ) - 1))) < (4 : ℝ) - 1 := by
      norm_num [weylM]
    exact theorem_1_of_field_inputs_exp 4 (by omega) ((4:ℝ)/4)
      (1 / ((4 : ℝ) * ((4 : ℝ) - 1))) (by norm_num) hexp hfib hSC h4
  · have hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < (n : ℝ) / 4 := by
      have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h5
      have hn2 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      rw [div_lt_iff₀ hn2]
      nlinarith
    exact theorem_1_of_field_inputs_exp n (by omega) ((n : ℝ) / 4)
      (1 / ((n : ℝ) * ((n : ℝ) - 1))) hβ (exponent_index_refine n h5) hfib hSC h4

/-- **The challenge theorem for `n = 4, 5` from the index-refined field count
alone** — neither Davenport–Heilbronn nor Bhargava is needed. -/
theorem theorem_1_of_indexFieldCount_four_five (n : ℕ) (hn : 4 ≤ n) (hn5 : n ≤ 5)
    (hSC : FieldCountBound n (by omega : 1 ≤ n) ((n : ℝ) / 4)) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  rcases eq_or_lt_of_le hn with h4 | h5
  · subst h4
    exact theorem_1_of_indexFieldCount 4 (by omega) (by simpa using hSC)
      (by simpa using ImprimitiveBad_four_isBigO)
  · have h5' : n = 5 := by omega
    subst h5'
    exact theorem_1_of_indexFieldCount 5 (by omega) hSC
      (ImprimitiveBad_isBigO_of_prime 5 (by norm_num))

/-- **The challenge theorem from the index-refined field count in prime degree
`n ≥ 5`** (no imprimitive input is needed). -/
theorem theorem_1_of_indexFieldCount_prime (n : ℕ) (hn : 5 ≤ n) (hp : Nat.Prime n)
    (hSC : FieldCountBound n (by omega : 1 ≤ n) ((n : ℝ) / 4)) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_indexFieldCount n (by omega) hSC (ImprimitiveBad_isBigO_of_prime n hp)

/-- **The challenge theorem from the index-refined field count in composite
degree `n ≥ 6`**, from Widmer's imprimitive bound. -/
theorem theorem_1_of_indexFieldCount_widmer (n : ℕ) (hn : 6 ≤ n)
    (hSC : FieldCountBound n (by omega : 1 ≤ n) ((n : ℝ) / 4))
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_indexFieldCount n (by omega) hSC (ImprimitiveBad_isBigO_of_widmer n hn hw)
end

end Submission.Vdw
