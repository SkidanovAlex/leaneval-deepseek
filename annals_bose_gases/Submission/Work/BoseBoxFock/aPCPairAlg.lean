import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.XSpow_aeStronglyMeasurable_ae_bounded
import Submission.Work.BoseBoxFock.modeProd_XS_pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aPCPairAlg` — the elementary algebra of the slot means `aPC`

`aPC ℓ i` (`slotCountsComplex.lean`) is the complex slot mean,
`aPC ℓ i Ψ x = ℓ⁻³ ∫_{acube ℓ} Ψ (x[i ↦ y]) dy`, i.e. the orthogonal projection of `Ψ` onto
the functions that are constant in the `i`-th slot (for the box pairing `⟨f,g⟩ = ∫ conj f g`).
This module collects the *elementary* consequences of that reading which the pair-slot
computations need, so that the consumers can quote them:

* `setIntegral_const_acube` — the cube has volume `ℓ³`;
* `aPC_idem` — `aPC ℓ i` is idempotent;
* `aPC_aQC_eq_zero` — the complementary slot `aQC ℓ i Ψ = Ψ − aPC ℓ i Ψ` has vanishing slot
  mean (an immediate consequence of the proved `integral_aQC_update_eq_zero`), i.e. the two
  slots are orthogonal;
* `aPC_aPC_invariant` — the *double* slot mean `aPC ℓ i (aPC ℓ j Ψ)` is invariant in the `j`-th
  coordinate (for every `i`, including `i = j`);
* `aPC_of_invariant` — conversely, the slot mean of a function already constant in the `i`-th
  coordinate is the function itself;
* `integrableOn_of_aesm_bound`, `integrableOn_conj_mul_aPC_aPC_of_bound`,
  `integrableOn_aPC_mul_of_bound` — the `L¹`-bookkeeping on the box (`abox N ℓ` has finite
  volume, and `aPC` of an a.e. bounded, a.e. strongly measurable function is a.e. bounded by
  the same constant, `aPC_ae_bound_full`).

## 4. Design note: the per-pair projection identity

The *pair* identity `∫_box conj(Θ)·P_iP_jΘ = ↑(∫_box ‖P_iP_jΘ‖²)`, i.e.
`Work.BoseBoxFock.integral_conj_mul_aPC_aPC`, is the content of the row
`⟨Θ, (Σ_i uSlot_i)(Σ_j uSlot_j) Θ⟩ = cS1C + cS2C`, and is proved from the lemmas above as
follows (`Ξ := P_j Θ = aPC ℓ j Θ`, `Q_k F = aQC ℓ k F = F − P_k F`).

* *Integrability.* `integrableOn_conj_mul_aPC_aPC_of_bound` applies to `Θ` itself once
  `AEStronglyMeasurable Θ volume` and `∀ᵐ x, ‖Θ x‖ ≤ C` are extracted from `MemLp Θ ⊤ volume`
  (`MeasureTheory.MemLp.aestronglyMeasurable`, `exists_ae_bound_of_memLp_top_gen`).  The
  auxiliary states `Ξ`, `Q_j Θ`, `Q_i Ξ` have global a.e. bounds and global a.e. strong
  measurability by `aPC_ae_bound_full` / `aPC_aesm_full`, so the same lemma (and
  `integrableOn_aPC_mul_of_bound`, for the hypotheses of `aPC_sym_box`) covers every integrand.
* *The `Q_j Θ` term vanishes.*  `P_iP_jΘ = P_j(P_iP_jΘ)` by `aPC_aPC_invariant` (the double
  mean is constant in the `j`-th coordinate) together with `aPC_of_invariant`.  Hence, by the
  box symmetry `aPC_sym_box` read right-to-left with `Φ := conj(Q_jΘ)`, `Ψ := P_iP_jΘ`,
  `∫_box conj(Q_jΘ)·P_iP_jΘ = ∫_box P_j(conj(Q_jΘ))·(P_iP_jΘ)`, and
  `P_j(conj(Q_jΘ)) = conj(P_j(Q_jΘ)) = 0` by `aPC_conj` and `aPC_aQC_eq_zero`; the integral of
  `0` vanishes.
* *The `P_j Θ` term.*  Decompose `Ξ = P_iΞ + Q_iΞ` and use `integral_add`: the cross term is
  `∫_box conj(Q_iΞ)·P_iΞ = conj(∫_box conj(P_iΞ)·Q_iΞ) = conj 0 = 0` (root-level `integral_conj`,
  plus the single-state orthogonality `integral_conj_aPC_mul_aQC_eq_zero` for the state `Ξ`),
  while `∫_box conj(P_iΞ)·P_iΞ = ∫_box ↑‖P_iΞ‖² = ↑(∫_box ‖P_iΞ‖²)` (`Complex.conj_mul'`,
  `integral_complex_ofReal`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. The volume of the cube -/

/-- The integral of a constant over the centred cube `acube ℓ` is `ℓ³` times the constant. -/
theorem setIntegral_const_acube {ℓ : ℝ} (hℓ : 0 < ℓ) (C : ℂ) :
    (∫ y in Submission.BoseGases.acube ℓ, C) = ((ℓ ^ 3 : ℝ) : ℂ) * C := by
  rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real,
    Submission.BoseGases.acube_volume ℓ hℓ.le,
    ENNReal.toReal_ofReal (by positivity), Complex.real_smul]

/-- The normalisation `ℓ⁻³ · ℓ³ = 1`. -/
theorem aPC_coeff_smul {ℓ : ℝ} (hℓ : 0 < ℓ) (C : ℂ) :
    ((1 / ℓ ^ 3 : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ) : ℂ) * C) = C := by
  rw [← mul_assoc, ← Complex.ofReal_mul,
    show (1 / ℓ ^ 3 : ℝ) * ℓ ^ 3 = 1 from by
      rw [one_div, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ))],
    Complex.ofReal_one, one_mul]

/-! ## 1. Idempotence and orthogonality of the slot mean -/

/-- **The slot mean is idempotent**: `aPC ℓ i (aPC ℓ i Ψ) = aPC ℓ i Ψ`.

Indeed `aPC ℓ i Ψ` is constant in the `i`-th coordinate (`aPC_const_in_coord`), so its cube
average is itself. -/
theorem aPC_idem {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℂ} : aPC ℓ i (aPC ℓ i Ψ) = aPC ℓ i Ψ := by
  funext x
  have hcongr : (∫ y in Submission.BoseGases.acube ℓ, aPC ℓ i Ψ (Function.update x i y))
      = ∫ y in Submission.BoseGases.acube ℓ, aPC ℓ i Ψ x :=
    MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun y _ => aPC_const_in_coord ℓ i Ψ x y)
  calc aPC ℓ i (aPC ℓ i Ψ) x
      = ((1 / ℓ ^ 3 : ℝ) : ℂ)
          * (∫ y in Submission.BoseGases.acube ℓ, aPC ℓ i Ψ (Function.update x i y)) := rfl
    _ = ((1 / ℓ ^ 3 : ℝ) : ℂ)
          * (∫ y in Submission.BoseGases.acube ℓ, aPC ℓ i Ψ x) := by rw [hcongr]
    _ = ((1 / ℓ ^ 3 : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ) : ℂ) * aPC ℓ i Ψ x) := by
          rw [setIntegral_const_acube hℓ]
    _ = aPC ℓ i Ψ x := aPC_coeff_smul hℓ _

/-- **The complementary slot has vanishing slot mean**: `aPC ℓ i (aQC ℓ i Ψ) = 0`.

This is the identity `∫_{acube} aQC ℓ i Ψ (x[i↦y]) dy = 0` (`integral_aQC_update_eq_zero`),
which holds without any hypothesis on `Ψ` (the Bochner integral of a non-integrable function
is the junk value `0`, and the junk values are compatible). -/
theorem aPC_aQC_eq_zero {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℂ} : aPC ℓ i (aQC ℓ i Ψ) = fun _ => 0 := by
  funext x
  calc aPC ℓ i (aQC ℓ i Ψ) x
      = ((1 / ℓ ^ 3 : ℝ) : ℂ)
          * (∫ y in Submission.BoseGases.acube ℓ, aQC ℓ i Ψ (Function.update x i y)) := rfl
    _ = ((1 / ℓ ^ 3 : ℝ) : ℂ) * 0 := by rw [integral_aQC_update_eq_zero hℓ i Ψ x]
    _ = 0 := mul_zero _

/-! ## 2. Invariance of the double slot mean, and the converse -/

/-- **The slot mean of a function already constant in the `i`-th coordinate is the function
itself.** -/
theorem aPC_of_invariant {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℂ}
    (hΨ : ∀ x w, Ψ (Function.update x i w) = Ψ x) : aPC ℓ i Ψ = Ψ := by
  funext x
  have hcongr : (∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update x i y))
      = ∫ y in Submission.BoseGases.acube ℓ, Ψ x :=
    MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun y _ => hΨ x y)
  calc aPC ℓ i Ψ x
      = ((1 / ℓ ^ 3 : ℝ) : ℂ)
          * (∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update x i y)) := rfl
    _ = ((1 / ℓ ^ 3 : ℝ) : ℂ) * (∫ y in Submission.BoseGases.acube ℓ, Ψ x) := by rw [hcongr]
    _ = ((1 / ℓ ^ 3 : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ) : ℂ) * Ψ x) := by
          rw [setIntegral_const_acube hℓ]
    _ = Ψ x := aPC_coeff_smul hℓ _

/-- **The double slot mean `aPC ℓ i (aPC ℓ j Ψ)` is invariant in the `j`-th coordinate.**

For `i ≠ j` the two update operators commute (`Function.update_comm`) and `aPC ℓ j Ψ` is
constant in its own slot (`aPC_const_in_coord`); for `i = j` this is `aPC_idem`. -/
theorem aPC_aPC_invariant {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin N)
    {Ψ : Submission.BoseGases.X N → ℂ} (x : Submission.BoseGases.X N) (w : Sp) :
    aPC ℓ i (aPC ℓ j Ψ) (Function.update x j w) = aPC ℓ i (aPC ℓ j Ψ) x := by
  by_cases hij : i = j
  · subst hij
    rw [aPC_idem hℓ]
    exact aPC_const_in_coord ℓ i Ψ x w
  · have hstep : (∫ y in Submission.BoseGases.acube ℓ,
          aPC ℓ j Ψ (Function.update (Function.update x j w) i y))
        = ∫ y in Submission.BoseGases.acube ℓ, aPC ℓ j Ψ (Function.update x i y) := by
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
        (fun y _ => ?_)
      rw [Function.update_comm (a := j) (b := i) (Ne.symm hij)]
      exact aPC_const_in_coord ℓ j Ψ (Function.update x i y) w
    calc aPC ℓ i (aPC ℓ j Ψ) (Function.update x j w)
        = ((1 / ℓ ^ 3 : ℝ) : ℂ)
            * (∫ y in Submission.BoseGases.acube ℓ,
                aPC ℓ j Ψ (Function.update (Function.update x j w) i y)) := rfl
      _ = ((1 / ℓ ^ 3 : ℝ) : ℂ)
            * (∫ y in Submission.BoseGases.acube ℓ, aPC ℓ j Ψ (Function.update x i y)) := by
            rw [hstep]
      _ = aPC ℓ i (aPC ℓ j Ψ) x := rfl

/-! ## 3. Integrability on the box out of a global a.e. bound -/

/-- **A globally a.e. bounded, a.e. strongly measurable function is integrable on the box**
(the box has finite volume). -/
theorem integrableOn_of_aesm_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {G : Work.BoseDict.Xn N → ℂ} {C : ℝ}
    (hG : AEStronglyMeasurable G (volume : Measure (Work.BoseDict.Xn N)))
    (hGb : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn N)), ‖G x‖ ≤ C) :
    IntegrableOn G (Submission.BoseGases.abox N ℓ) volume :=
  MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le)
    hG.restrict C (MeasureTheory.ae_mono Measure.restrict_le_self hGb)

/-- **`conj Ψ · aPC ℓ i (aPC ℓ j Ψ)` is integrable on the box** for a globally a.e. bounded,
a.e. strongly measurable state `Ψ`. -/
theorem integrableOn_conj_mul_aPC_aPC_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Ψ : Work.BoseDict.Xn N → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hΨaesm : AEStronglyMeasurable Ψ (volume : Measure (Work.BoseDict.Xn N)))
    (hΨb : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn N)), ‖Ψ x‖ ≤ C) (i j : Fin N) :
    IntegrableOn (fun x => (starRingEnd ℂ) (Ψ x) * aPC ℓ i (aPC ℓ j Ψ) x)
      (Submission.BoseGases.abox N ℓ) volume := by
  have hPj : AEStronglyMeasurable (aPC ℓ j Ψ) (volume : Measure (Work.BoseDict.Xn N)) :=
    aPC_aesm_full ℓ j hΨaesm
  have hbPj : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn N)), ‖aPC ℓ j Ψ x‖ ≤ C :=
    aPC_ae_bound_full ℓ hℓ j hC hΨb
  have hPiPj : AEStronglyMeasurable (aPC ℓ i (aPC ℓ j Ψ))
      (volume : Measure (Work.BoseDict.Xn N)) := aPC_aesm_full ℓ i hPj
  have hbPiPj : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn N)),
      ‖aPC ℓ i (aPC ℓ j Ψ) x‖ ≤ C := aPC_ae_bound_full ℓ hℓ i hC hbPj
  refine integrableOn_of_aesm_bound (C := C * C) hℓ (hΨaesm.star.mul hPiPj) ?_
  filter_upwards [hΨb, hbPiPj] with x h1 h2
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul h1 h2 (norm_nonneg _) hC

/-- **The two products appearing in the box-symmetry `aPC_sym_box` are integrable** for
globally a.e. bounded, a.e. strongly measurable states. -/
theorem integrableOn_aPC_mul_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ Ψ : Work.BoseDict.Xn N → ℂ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hΦaesm : AEStronglyMeasurable Φ (volume : Measure (Work.BoseDict.Xn N)))
    (hΦb : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn N)), ‖Φ x‖ ≤ C₁)
    (hΨaesm : AEStronglyMeasurable Ψ (volume : Measure (Work.BoseDict.Xn N)))
    (hΨb : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn N)), ‖Ψ x‖ ≤ C₂) (i : Fin N) :
    IntegrableOn (fun x => aPC ℓ i Φ x * Ψ x) (Submission.BoseGases.abox N ℓ) volume
      ∧ IntegrableOn (fun x => Φ x * aPC ℓ i Ψ x) (Submission.BoseGases.abox N ℓ) volume := by
  have hPi : AEStronglyMeasurable (aPC ℓ i Φ) (volume : Measure (Work.BoseDict.Xn N)) :=
    aPC_aesm_full ℓ i hΦaesm
  have hbPi : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn N)), ‖aPC ℓ i Φ x‖ ≤ C₁ :=
    aPC_ae_bound_full ℓ hℓ i hC₁ hΦb
  have hPj : AEStronglyMeasurable (aPC ℓ i Ψ) (volume : Measure (Work.BoseDict.Xn N)) :=
    aPC_aesm_full ℓ i hΨaesm
  have hbPj : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn N)), ‖aPC ℓ i Ψ x‖ ≤ C₂ :=
    aPC_ae_bound_full ℓ hℓ i hC₂ hΨb
  constructor
  · refine integrableOn_of_aesm_bound (C := C₁ * C₂) hℓ (hPi.mul hΨaesm) ?_
    filter_upwards [hbPi, hΨb] with x h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) hC₁
  · refine integrableOn_of_aesm_bound (C := C₁ * C₂) hℓ (hΦaesm.mul hPj) ?_
    filter_upwards [hΦb, hbPj] with x h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) hC₁

/-! ## 4. The orthogonality of the complementary slot with the range of the slot mean -/

/-- **The bilinear orthogonality of the complementary slot.**  For a.e. bounded, a.e. strongly
measurable `F`, `G`,

    `∫_box conj (Q_i F) · P_i G = 0`,

where `Q_i = aQC ℓ i` and `P_i = aPC ℓ i`.  It follows from the box symmetry `aPC_sym_box`
applied to `Φ = conj (Q_i F)`, `Ψ = G`: the left side becomes
`∫_box P_i (conj (Q_i F)) · G = ∫_box conj (P_i (Q_i F)) · G = 0`, since `P_i Q_i = 0`
(`aPC_aQC_eq_zero`) and `P_i` commutes with conjugation (`aPC_conj`). -/
theorem integral_conj_aQC_mul_aPC_eq_zero {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {F G : Work.BoseDict.Xn N → ℂ} {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hFaesm : AEStronglyMeasurable F (volume : Measure (Work.BoseDict.Xn N)))
    (hFb : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn N)), ‖F x‖ ≤ C)
    (hGaesm : AEStronglyMeasurable G (volume : Measure (Work.BoseDict.Xn N)))
    (hGb : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn N)), ‖G x‖ ≤ C') (i : Fin N) :
    ∫ x in Submission.BoseGases.abox N ℓ,
      (starRingEnd ℂ) (aQC ℓ i F x) * aPC ℓ i G x = 0 := by
  have hPiaesm : AEStronglyMeasurable (aPC ℓ i F) (volume : Measure (Work.BoseDict.Xn N)) :=
    aPC_aesm_full ℓ i hFaesm
  have hbPi : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn N)), ‖aPC ℓ i F x‖ ≤ C :=
    aPC_ae_bound_full ℓ hℓ i hC hFb
  have hQaesm : AEStronglyMeasurable (fun x => (starRingEnd ℂ) (aQC ℓ i F x))
      (volume : Measure (Work.BoseDict.Xn N)) :=
    (hFaesm.sub hPiaesm).star
  have hQb : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn N)),
      ‖(starRingEnd ℂ) (aQC ℓ i F x)‖ ≤ C + C := by
    filter_upwards [hFb, hbPi] with x h1 h2
    rw [Complex.norm_conj, aQC_apply]
    calc ‖F x - aPC ℓ i F x‖ ≤ ‖F x‖ + ‖aPC ℓ i F x‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add h1 h2
  obtain ⟨h1, h2⟩ := integrableOn_aPC_mul_of_bound hℓ (C₁ := C + C) (C₂ := C')
    (by positivity) hC' hQaesm hQb hGaesm hGb i
  have hsym := aPC_sym_box (ℓ := ℓ) i
    (Φ := fun x => (starRingEnd ℂ) (aQC ℓ i F x)) (Ψ := G) h1 h2
  have hzero : ∀ x : Work.BoseDict.Xn N,
      aPC ℓ i (fun y => (starRingEnd ℂ) (aQC ℓ i F y)) x = 0 := by
    intro x
    rw [aPC_conj ℓ i (aQC ℓ i F), aPC_aQC_eq_zero hℓ i]
    simp
  calc (∫ x in Submission.BoseGases.abox N ℓ,
        (starRingEnd ℂ) (aQC ℓ i F x) * aPC ℓ i G x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          aPC ℓ i (fun y => (starRingEnd ℂ) (aQC ℓ i F y)) x * G x := hsym.symm
    _ = 0 := by
        have hcongr : (fun x => aPC ℓ i (fun y => (starRingEnd ℂ) (aQC ℓ i F y)) x * G x)
            = fun x => (0 : ℂ) * G x := by
          funext x
          rw [hzero x]
        rw [MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun x => congrFun hcongr x))]
        simp

/-- **The single-state orthogonality**, in the box form needed by the pair computations:
`∫_box conj (P_i F) · Q_i F = 0` for an a.e. bounded, a.e. strongly measurable `F`
(the companion of `integral_conj_aQC_mul_aPC_eq_zero` with `G = F`). -/
theorem integral_conj_aPC_mul_aQC_eq_zero_of_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {F : Work.BoseDict.Xn (n + 1) → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hFaesm : AEStronglyMeasurable F (volume : Measure (Work.BoseDict.Xn (n + 1))))
    (hFb : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn (n + 1))), ‖F x‖ ≤ C)
    (i : Fin (n + 1)) :
    ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
      (starRingEnd ℂ) (aPC ℓ i F x) * aQC ℓ i F x = 0 := by
  have hPiaesm : AEStronglyMeasurable (aPC ℓ i F)
      (volume : Measure (Work.BoseDict.Xn (n + 1))) := aPC_aesm_full ℓ i hFaesm
  have hbPi : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn (n + 1))), ‖aPC ℓ i F x‖ ≤ C :=
    aPC_ae_bound_full ℓ hℓ i hC hFb
  have hQb : ∀ᵐ x ∂(volume : Measure (Work.BoseDict.Xn (n + 1))), ‖aQC ℓ i F x‖ ≤ C + C := by
    filter_upwards [hFb, hbPi] with x h1 h2
    rw [aQC_apply]
    calc ‖F x - aPC ℓ i F x‖ ≤ ‖F x‖ + ‖aPC ℓ i F x‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add h1 h2
  have hInt : IntegrableOn
      (fun x => (starRingEnd ℂ) (aPC ℓ i F x) * (F x - aPC ℓ i F x))
      (Submission.BoseGases.abox (n + 1) ℓ) volume := by
    refine integrableOn_of_aesm_bound (C := C * (C + C)) hℓ
      ((hPiaesm.star).mul (hFaesm.sub hPiaesm)) ?_
    filter_upwards [hbPi, hQb] with x h1 h2
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul h1 h2 (norm_nonneg _) hC
  have hmain := integral_conj_aPC_mul_aQC_eq_zero (ℓ := ℓ) hℓ (Θ := F) i hInt
  have hgoal : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (starRingEnd ℂ) (aPC ℓ i F x) * (F x - aPC ℓ i F x))
      = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (starRingEnd ℂ) (aPC ℓ i F x) * aQC ℓ i F x := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [aQC_apply]
  rw [← hgoal]
  exact hmain

end Work.BoseBoxFock
