import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotPairRowsAux
import Submission.Work.BoseBoxFock.boxSlotSum_rankOnePairGen
import Submission.Work.BoseBoxFock.cIPn_boxSlotOf_two_slot_congr
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.potPairRows_cIPn_pinned_gen` — the `Q₂` row in pinned normal form

Holder: `Submission/Work/BoseBoxFock/PotPairRows_exists.lean`.

`potPairRows` (`PotGroupDefs.lean`) is the `Q₂` group of FS `lem:2ndQuand`: the
`(W₁+W₁ω)a₀†a_k†a_ka₀` row, the Bogoliubov row `½W₁(a₀†a₀†a_ka_{-k}+h.c.)` and the
`(L₀+L₁)∘Σ_ka_k†a_k` row, all built from compositions of the first-quantised slot sums
`B(T) = boxSlotSum e T`.

The mathematical content of this module is the **pinned normal form** of that row: after

* the slot (`pairSet`) decomposition of the two differences of compositions
  (`Work.BoseBoxFock.potPairRows_pairSet`) together with the refinement of the *third* block
  (which is not of the difference form) into its `pairSet` sum `Σ_{i≠j}` plus the diagonal
  `Σ_j` (the diagonal of the composed rank-one operator vanishes because `f k 0 = 0`), and
* the substitution of the four `η`-occurrences of each slot by their a.e. equal *pinned*
  representatives (`Work.BoseBoxFock.cIPn_boxSlotOf_two_slot_congr`, plus its one-slot twin
  below),

the row becomes an explicit sum, over the modes `k` and the ordered pairs `p` of distinct slots,
of **triple integrals of the state against the pinned functions** — exactly the shape to which
the frame/Poisson identity of the chapter applies.

The statement is the *general* (mode-family- and pinning-abstract) form; the honest
instantiation (`Fp k = (√ℓ³)⁻¹ • qVec ℓ (kmomLab ℓ N k)`, `Th = c • thetaFun ℓ`) follows from the
proved pinning lemmas (`Work.BoseBoxFock.qVec_eq_etaOf_of_pairing`,
`Work.BoseBoxFock.e0_prop_theta`).

The proof is `cIPn`-linearity (finite sums and real multiples move out of the Bochner integral,
the integrability side conditions being supplied by the measurable/bounded/box-supported slot
composites), exactly as in `Work.BoseBoxFock.potCubic_cIPn_pinned_gen`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "Ω" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## 0. Small `cIPn` linearity helpers -/

/-- `cIPn Θ (c • Ψ) = c • cIPn Θ Ψ` (unconditional: `integral_const_mul`). -/
private lemma cIPn_smul_loc {d : ℕ} (Theta : Xn d → ℂ) (c : ℝ) (Psi : Xn d → ℂ) :
    cIPn d Theta (c • Psi) = c • cIPn d Theta Psi := by
  simp only [cIPn, Pi.smul_apply, Complex.real_smul]
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun x => by ring))

/-- `cIPn Θ (Ψ + Χ) = cIPn Θ Ψ + cIPn Θ Χ`. -/
private lemma cIPn_add_loc {d : ℕ} (Theta Psi Chi : Xn d → ℂ)
    (hPsi : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * Psi x))
    (hChi : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * Chi x)) :
    cIPn d Theta (Psi + Chi) = cIPn d Theta Psi + cIPn d Theta Chi := by
  simp only [cIPn, Pi.add_apply, mul_add]
  rw [MeasureTheory.integral_add hPsi hChi]

/-- `cIPn Θ (Ψ − Χ) = cIPn Θ Ψ − cIPn Θ Χ`. -/
private lemma cIPn_sub_loc {d : ℕ} (Theta Psi Chi : Xn d → ℂ)
    (hPsi : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * Psi x))
    (hChi : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * Chi x)) :
    cIPn d Theta (Psi - Chi) = cIPn d Theta Psi - cIPn d Theta Chi := by
  simp only [cIPn, Pi.sub_apply, mul_sub]
  rw [MeasureTheory.integral_sub hPsi hChi]

/-- `cIPn Θ (Σ_{i∈s} Ψ i) = Σ_{i∈s} cIPn Θ (Ψ i)`. -/
private lemma cIPn_finset_sum_loc {d : ℕ} {ι : Type*} (s : Finset ι) (Theta : Xn d → ℂ)
    (Psi : ι → Xn d → ℂ)
    (h : ∀ i ∈ s, MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * Psi i x)) :
    cIPn d Theta (∑ i ∈ s, Psi i) = ∑ i ∈ s, cIPn d Theta (Psi i) := by
  simp only [cIPn, Finset.sum_apply, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum _ h]

/-- Integrability of a finite sum of integrable integrands. -/
private lemma integrable_finset_sum_loc {d : ℕ} {ι : Type*} (s : Finset ι) (Theta : Xn d → ℂ)
    (Psi : ι → Xn d → ℂ)
    (h : ∀ i ∈ s, MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * Psi i x)) :
    MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * (∑ i ∈ s, Psi i) x) := by
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact integrable_finsetSum s h

/-- Integrability of the sum of two integrable integrands (in the `conj Θ · (A + B)` shape). -/
private lemma integrable_add_loc {d : ℕ} (Theta : Xn d → ℂ) (A B : Xn d → ℂ)
    (hA : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * A x))
    (hB : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * B x)) :
    MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * (A + B) x) := by
  simp only [Pi.add_apply, mul_add]
  exact hA.add hB

/-- Integrability of the difference of two integrable integrands. -/
private lemma integrable_sub_loc {d : ℕ} (Theta : Xn d → ℂ) (A B : Xn d → ℂ)
    (hA : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * A x))
    (hB : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * B x)) :
    MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * (A - B) x) := by
  simp only [Pi.sub_apply, mul_sub]
  exact hA.sub hB

/-- Integrability of a scalar multiple. -/
private lemma integrable_smul_loc {d : ℕ} (Theta : Xn d → ℂ) (c : ℝ) (Psi : Xn d → ℂ)
    (h : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * Psi x)) :
    MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Theta x) * (c • Psi) x) := by
  refine (h.const_mul (c : ℂ)).congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Pi.smul_apply, Complex.real_smul]
  ring

/-! ## 1. Local integrability of the slot composites -/

private lemma boxSlotOf_pair_integrable_loc {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w₁ v₁ w₂ v₂ : Fin m → ℝ) (i j : Fin d)
    (Theta : Xn d → ℂ) (hΘm : Measurable Theta)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Theta x‖ ≤ C)
    (hΘs : Function.support Theta ⊆ Work.MB.boxPow d ℓ) :
    MeasureTheory.Integrable (fun x : Xn d =>
      (starRingEnd ℂ) (Theta x) * Work.BoseDict.boxSlotOf e w₁ v₁ i
        (Work.BoseDict.boxSlotOf e w₂ v₂ j Theta) x) := by
  obtain ⟨hC₁m, C₁, hC₁⟩ :=
    Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdd hsupp w₂ v₂ j Theta hΘm hΘb
  obtain ⟨hC₂m, C₂, hC₂⟩ :=
    Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdd hsupp w₁ v₁ i
      (Work.BoseDict.boxSlotOf e w₂ v₂ j Theta) hC₁m ⟨C₁, hC₁⟩
  obtain ⟨C₃, hC₃⟩ := hΘb
  refine Work.MB.integrable_of_bdd_of_support (C := max C₃ 0 * max C₂ 0)
    (μ := volume) (Work.MB.measurableSet_boxPow d ℓ) (Work.MB.volume_boxPow_lt_top d ℓ) ?_ ?_ ?_
  · exact ((Complex.continuous_conj.measurable.comp hΘm).mul hC₂m).aestronglyMeasurable
  · intro x
    rw [norm_mul]
    have h1 : ‖(starRingEnd ℂ) (Theta x)‖ ≤ max C₃ 0 :=
      le_trans (by rw [Complex.norm_conj]; exact hC₃ x) (le_max_left _ _)
    have h2 : ‖Work.BoseDict.boxSlotOf e w₁ v₁ i (Work.BoseDict.boxSlotOf e w₂ v₂ j Theta) x‖
        ≤ max C₂ 0 := le_trans (hC₂ x) (le_max_left _ _)
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)
  · intro x hx
    have h0 : Theta x = 0 := by
      by_contra hne
      exact hx (hΘs (Function.mem_support.mpr hne))
    simp [h0]

private lemma boxSlotOf_oneSlot_integrable_loc {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d)
    (Theta : Xn d → ℂ) (hΘm : Measurable Theta)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Theta x‖ ≤ C)
    (hΘs : Function.support Theta ⊆ Work.MB.boxPow d ℓ) :
    MeasureTheory.Integrable (fun x : Xn d =>
      (starRingEnd ℂ) (Theta x) * Work.BoseDict.boxSlotOf e w v j Theta x) := by
  obtain ⟨hCm, C, hC⟩ :=
    Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdd hsupp w v j Theta hΘm hΘb
  obtain ⟨C₀, hC₀⟩ := hΘb
  refine Work.MB.integrable_of_bdd_of_support (C := max C₀ 0 * max C 0)
    (μ := volume) (Work.MB.measurableSet_boxPow d ℓ) (Work.MB.volume_boxPow_lt_top d ℓ) ?_ ?_ ?_
  · exact ((Complex.continuous_conj.measurable.comp hΘm).mul hCm).aestronglyMeasurable
  · intro x
    rw [norm_mul]
    have h1 : ‖(starRingEnd ℂ) (Theta x)‖ ≤ max C₀ 0 :=
      le_trans (by rw [Complex.norm_conj]; exact hC₀ x) (le_max_left _ _)
    have h2 : ‖Work.BoseDict.boxSlotOf e w v j Theta x‖ ≤ max C 0 :=
      le_trans (hC x) (le_max_left _ _)
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)
  · intro x hx
    have h0 : Theta x = 0 := by
      by_contra hne
      exact hx (hΘs (Function.mem_support.mpr hne))
    simp [h0]

/-! ## 2. The a.e. pinning of a single slot -/

/-- A.e. statements about the one-particle variable pull back along a coordinate of a finite
product. -/
private theorem ae_eval_volume_pi {N : ℕ} (i : Fin N) {P : Ω → Prop}
    (h : ∀ᵐ a ∂(volume : Measure Ω), P a) :
    ∀ᵐ x ∂(volume : Measure (Fin N → Ω)), P (x i) := by
  rw [MeasureTheory.volume_pi]
  exact (Measure.quasiMeasurePreserving_eval (μ := fun _ : Fin N => (volume : Measure Ω)) i).ae h

/-- **One slot, pinned.**  `cIPn Θ (boxSlotOf e w v j Θ)` with the two `η`-occurrences replaced
by their a.e. equal representatives. -/
private lemma cIPn_boxSlotOf_oneSlot_congr {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (w v : Fin m → ℝ) (W V : Ω → ℂ) (j : Fin d) (Theta : Xn d → ℂ)
    (hW : Work.BoseDict.etaOf e w =ᵐ[volume] W)
    (hV : Work.BoseDict.etaOf e v =ᵐ[volume] V) :
    cIPn d Theta (Work.BoseDict.boxSlotOf e w v j Theta)
      = ∫ x : Xn d, ∫ y : Ω,
          (starRingEnd ℂ) (Theta x) * W (x j) * (starRingEnd ℂ) (V y)
            * Theta (Function.update x j y) := by
  have hpt : ∀ x : Xn d,
      (starRingEnd ℂ) (Theta x) * Work.BoseDict.boxSlotOf e w v j Theta x
        = ∫ y : Ω, (starRingEnd ℂ) (Theta x) * Work.BoseDict.etaOf e w (x j)
            * (starRingEnd ℂ) (Work.BoseDict.etaOf e v y) * Theta (Function.update x j y) := by
    intro x
    simp only [Work.BoseDict.boxSlotOf]
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
  simp only [cIPn, hpt]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_eval_volume_pi j hW] with x hx
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hV] with y hy
  rw [hx, hy]

/-! ## 3. The row, with the third block refined into its `pairSet` and diagonal parts -/

/-- The rank-one composition `|evec0⟩⟨evec0| ∘ |f k⟩⟨f k|` vanishes when `f k 0 = 0`. -/
private lemma rankOnePair_evec0_comp_eq_zero {m : ℕ} [NeZero m] (hk : Fin m → ℝ)
    (h0 : hk 0 = 0) :
    (rankOnePair (evec0 m) (evec0 m)).comp (rankOnePair hk hk) = 0 := by
  rw [rankOnePair_comp]
  have hsum : (∑ l : Fin m, (evec0 m) l * hk l) = 0 := by
    have h : (∑ l : Fin m, (evec0 m) l * hk l) = hk 0 := by
      simp only [evec0, Work.BoseB4.evec, Pi.single_apply]
      rw [Finset.sum_eq_single (0 : Fin m)]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ (0 : Fin m)) h
    rw [h, h0]
  rw [hsum, zero_smul]

private lemma boxSlotSum_zeroOp {m d : ℕ} {e : Fin m → Ω → ℂ} (Theta : Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e (0 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) Theta = 0 := by
  simp only [Work.BoseDict.boxSlotSum, LinearMap.zero_apply, Pi.zero_apply, zero_smul,
    Finset.sum_const_zero]

/-- **The `Q₂` row with the third block fully decomposed.**  Same as
`Work.BoseBoxFock.potPairRows_pairSet`, except that the third block — which is *not* of the
difference form — is split into its off-diagonal `pairSet` sum and its diagonal `Σ_j`, the
diagonal of the composed rank-one operator `|evec0⟩⟨evec0| ∘ |f k⟩⟨f k|` vanishing because
`⟨f k, evec0⟩ = f k 0 = 0`. -/
theorem potPairRows_pairSet_flat {m n : ℕ} [NeZero m] {Mode : Type*}
    [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode] {ℓ : ℝ}
    (e : Fin m → Ω → ℂ)
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (f : Mode → Fin m → ℝ) (hf0 : ∀ k, f k 0 = 0) (E : Work.BoseB7.Q3Env Mode)
    (Theta : Xn n → ℂ) (hΘm : Measurable Theta)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Theta x‖ ≤ C) :
    potPairRows (fun T => boxSlotSum e T) f E Theta
      = (E.ell ^ (-(3 : ℝ))) • (∑ k : Mode, (E.W1 k + E.W1omega k) •
            (∑ p ∈ Submission.BoseGases.pairSet n,
              boxSlotOf e (evec0 m) (f k) p.1 (boxSlotOf e (f k) (evec0 m) p.2 Theta)))
        + ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ))) • (∑ k : Mode, E.W1 k •
            ((∑ p ∈ Submission.BoseGases.pairSet n,
                boxSlotOf e (evec0 m) (f k) p.1
                  (boxSlotOf e (evec0 m) (f (-k)) p.2 Theta))
              + (∑ p ∈ Submission.BoseGases.pairSet n,
                boxSlotOf e (f k) (evec0 m) p.1
                  (boxSlotOf e (f (-k)) (evec0 m) p.2 Theta))))
        + (∑ k : Mode,
            ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
                (∑ p ∈ Submission.BoseGases.pairSet n,
                  boxSlotOf e (evec0 m) (evec0 m) p.1
                    (boxSlotOf e (f k) (f k) p.2 Theta))
              - (E.mu * E.W1 0) •
                (∑ j : Fin n, boxSlotOf e (f k) (f k) j Theta))) := by
  rw [potPairRows_pairSet e hmeas hbdd hsupp horth f E Theta hΘm hΘb]
  have hC : (∑ k : Mode,
        ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
            (boxSlotSum e (rankOnePair (evec0 m) (evec0 m))
              (boxSlotSum e (rankOnePair (f k) (f k)) Theta))
          - (E.mu * E.W1 0) • (boxSlotSum e (rankOnePair (f k) (f k)) Theta)))
      = (∑ k : Mode,
          ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
              (∑ p ∈ Submission.BoseGases.pairSet n,
                boxSlotOf e (evec0 m) (evec0 m) p.1
                  (boxSlotOf e (f k) (f k) p.2 Theta))
            - (E.mu * E.W1 0) • (∑ j : Fin n, boxSlotOf e (f k) (f k) j Theta))) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hpd := pairDecompPairSetGen hmeas hbdd hsupp horth (evec0 m) (evec0 m)
      (f k) (f k) Theta hΘm hΘb
    rw [sub_eq_iff_eq_add] at hpd
    rw [hpd, rankOnePair_evec0_comp_eq_zero (f k) (hf0 k), boxSlotSum_zeroOp,
      boxSlotSum_rankOnePairGen hmeas hbdd hsupp (f k) (f k) Theta hΘm hΘb]
    simp
  rw [hC]

/-! ## 4. The pinned normal form of the `Q₂` row -/

/-- **The `Q₂` row in pinned normal form.**

With `B(T) = boxSlotSum e T`, the pairing of the box state `Theta` against the `Q₂` row is the sum
of the three blocks, each written as a `pairSet` sum of **triple integrals of the state against the
pinned functions** `Th` (the condensate) and `Fp k` (the `k`-th localised wave):

* the `(W₁+W₁ω)`-block (weight `ℓ⁻³(W₁ k + W₁ω k)`, slots `(evec0, f k)`, `(f k, evec0)`);
* the Bogoliubov block (weight `½ℓ⁻³W₁ k`, slots `(evec0, f k)`, `(evec0, f (−k))` and
  `(f k, evec0)`, `(f (−k), evec0)`);
* the `(L₀+L₁)` block (weight `ℓ⁻³W₁(0) + ℓ⁻³W₁ω(0)`), whose `Σ_{i≠j}` part carries the slots
  `(evec0, evec0)`, `(f k, f k)` and whose diagonal part is the single-slot sum over `j`. -/
theorem potPairRows_cIPn_pinned_gen {m : ℕ} [NeZero m] {n : ℕ} {ℓ : ℝ} {Mode : Type*}
    [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode] {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (f : Mode → Fin m → ℝ) (hf0 : ∀ k, f k 0 = 0)
    (E : Work.BoseB7.Q3Env Mode)
    (Fp : Mode → Ω → ℂ) (Th : Ω → ℂ)
    (hF : ∀ k, Work.BoseDict.etaOf e (f k) =ᵐ[volume] Fp k)
    (hTh : Work.BoseDict.etaOf e (evec0 m) =ᵐ[volume] Th)
    (Theta : Xn n → ℂ) (hΘm : Measurable Theta)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Theta x‖ ≤ C)
    (hΘs : Function.support Theta ⊆ Work.MB.boxPow n ℓ) :
    cIPn n Theta (potPairRows (fun T => boxSlotSum e T) f E Theta)
      = (E.ell ^ (-(3 : ℝ))) •
          (∑ k : Mode, (E.W1 k + E.W1omega k) •
            (∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
                (starRingEnd ℂ) (Theta x) * Th (x p.1)
                  * (starRingEnd ℂ) (Fp k y) * Fp k (x p.2)
                  * (starRingEnd ℂ) (Th u)
                  * Theta (Function.update (Function.update x p.1 y) p.2 u)))
        + ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ))) •
          (∑ k : Mode, E.W1 k •
            ((∑ p ∈ Submission.BoseGases.pairSet n,
                ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
                  (starRingEnd ℂ) (Theta x) * Th (x p.1)
                    * (starRingEnd ℂ) (Fp k y) * Th (x p.2)
                    * (starRingEnd ℂ) (Fp (-k) u)
                    * Theta (Function.update (Function.update x p.1 y) p.2 u))
              + (∑ p ∈ Submission.BoseGases.pairSet n,
                ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
                  (starRingEnd ℂ) (Theta x) * Fp k (x p.1)
                    * (starRingEnd ℂ) (Th y) * Fp (-k) (x p.2)
                    * (starRingEnd ℂ) (Th u)
                    * Theta (Function.update (Function.update x p.1 y) p.2 u))))
        + (∑ k : Mode,
            ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
                (∑ p ∈ Submission.BoseGases.pairSet n,
                  ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
                    (starRingEnd ℂ) (Theta x) * Th (x p.1)
                      * (starRingEnd ℂ) (Th y) * Fp k (x p.2)
                      * (starRingEnd ℂ) (Fp k u)
                      * Theta (Function.update (Function.update x p.1 y) p.2 u))
              - (E.mu * E.W1 0) •
                (∑ j : Fin n,
                  ∫ x : Xn n, ∫ y : Ω,
                    (starRingEnd ℂ) (Theta x) * Fp k (x j)
                      * (starRingEnd ℂ) (Fp k y) * Theta (Function.update x j y)))) := by
  classical
  -- ## 0. the atom evaluations
  have atomI : ∀ (k : Mode) (i j : Fin n), i ≠ j →
      cIPn n Theta
          (boxSlotOf e (evec0 m) (f k) i (boxSlotOf e (f k) (evec0 m) j Theta))
        = ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
            (starRingEnd ℂ) (Theta x) * Th (x i) * (starRingEnd ℂ) (Fp k y)
              * Fp k (x j) * (starRingEnd ℂ) (Th u)
              * Theta (Function.update (Function.update x i y) j u) :=
    fun k i j hij =>
      cIPn_boxSlotOf_two_slot_congr (e := e) (evec0 m) (f k) (f k) (evec0 m)
        Th (Fp k) (Fp k) Th i j hij Theta hTh (hF k) (hF k) hTh hmeas hbdd hsupp hΘm hΘb
  have atomIIa : ∀ (k : Mode) (i j : Fin n), i ≠ j →
      cIPn n Theta
          (boxSlotOf e (evec0 m) (f k) i (boxSlotOf e (evec0 m) (f (-k)) j Theta))
        = ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
            (starRingEnd ℂ) (Theta x) * Th (x i) * (starRingEnd ℂ) (Fp k y)
              * Th (x j) * (starRingEnd ℂ) (Fp (-k) u)
              * Theta (Function.update (Function.update x i y) j u) :=
    fun k i j hij =>
      cIPn_boxSlotOf_two_slot_congr (e := e) (evec0 m) (f k) (evec0 m) (f (-k))
        Th (Fp k) Th (Fp (-k)) i j hij Theta hTh (hF k) hTh (hF (-k)) hmeas hbdd hsupp hΘm hΘb
  have atomIIb : ∀ (k : Mode) (i j : Fin n), i ≠ j →
      cIPn n Theta
          (boxSlotOf e (f k) (evec0 m) i (boxSlotOf e (f (-k)) (evec0 m) j Theta))
        = ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
            (starRingEnd ℂ) (Theta x) * Fp k (x i) * (starRingEnd ℂ) (Th y)
              * Fp (-k) (x j) * (starRingEnd ℂ) (Th u)
              * Theta (Function.update (Function.update x i y) j u) :=
    fun k i j hij =>
      cIPn_boxSlotOf_two_slot_congr (e := e) (f k) (evec0 m) (f (-k)) (evec0 m)
        (Fp k) Th (Fp (-k)) Th i j hij Theta (hF k) hTh (hF (-k)) hTh hmeas hbdd hsupp hΘm hΘb
  have atomIII : ∀ (k : Mode) (i j : Fin n), i ≠ j →
      cIPn n Theta
          (boxSlotOf e (evec0 m) (evec0 m) i (boxSlotOf e (f k) (f k) j Theta))
        = ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
            (starRingEnd ℂ) (Theta x) * Th (x i) * (starRingEnd ℂ) (Th y)
              * Fp k (x j) * (starRingEnd ℂ) (Fp k u)
              * Theta (Function.update (Function.update x i y) j u) :=
    fun k i j hij =>
      cIPn_boxSlotOf_two_slot_congr (e := e) (evec0 m) (evec0 m) (f k) (f k)
        Th Th (Fp k) (Fp k) i j hij Theta hTh hTh (hF k) (hF k) hmeas hbdd hsupp hΘm hΘb
  have atomE : ∀ (k : Mode) (j : Fin n),
      cIPn n Theta (boxSlotOf e (f k) (f k) j Theta)
        = ∫ x : Xn n, ∫ y : Ω,
            (starRingEnd ℂ) (Theta x) * Fp k (x j) * (starRingEnd ℂ) (Fp k y)
              * Theta (Function.update x j y) :=
    fun k j =>
      cIPn_boxSlotOf_oneSlot_congr (ℓ := ℓ) (f k) (f k) (Fp k) (Fp k) j Theta (hF k) (hF k)
  -- ## 1. integrability
  have hIntI : ∀ (k : Mode) (i j : Fin n),
      MeasureTheory.Integrable (fun x : Xn n =>
        (starRingEnd ℂ) (Theta x) *
          boxSlotOf e (evec0 m) (f k) i (boxSlotOf e (f k) (evec0 m) j Theta) x) :=
    fun k i j =>
      boxSlotOf_pair_integrable_loc hmeas hbdd hsupp _ _ _ _ i j Theta hΘm hΘb hΘs
  have hIntIIa : ∀ (k : Mode) (i j : Fin n),
      MeasureTheory.Integrable (fun x : Xn n =>
        (starRingEnd ℂ) (Theta x) *
          boxSlotOf e (evec0 m) (f k) i (boxSlotOf e (evec0 m) (f (-k)) j Theta) x) :=
    fun k i j =>
      boxSlotOf_pair_integrable_loc hmeas hbdd hsupp _ _ _ _ i j Theta hΘm hΘb hΘs
  have hIntIIb : ∀ (k : Mode) (i j : Fin n),
      MeasureTheory.Integrable (fun x : Xn n =>
        (starRingEnd ℂ) (Theta x) *
          boxSlotOf e (f k) (evec0 m) i (boxSlotOf e (f (-k)) (evec0 m) j Theta) x) :=
    fun k i j =>
      boxSlotOf_pair_integrable_loc hmeas hbdd hsupp _ _ _ _ i j Theta hΘm hΘb hΘs
  have hIntIII : ∀ (k : Mode) (i j : Fin n),
      MeasureTheory.Integrable (fun x : Xn n =>
        (starRingEnd ℂ) (Theta x) *
          boxSlotOf e (evec0 m) (evec0 m) i (boxSlotOf e (f k) (f k) j Theta) x) :=
    fun k i j =>
      boxSlotOf_pair_integrable_loc hmeas hbdd hsupp _ _ _ _ i j Theta hΘm hΘb hΘs
  have hIntE : ∀ (k : Mode) (j : Fin n),
      MeasureTheory.Integrable (fun x : Xn n =>
        (starRingEnd ℂ) (Theta x) * boxSlotOf e (f k) (f k) j Theta x) :=
    fun k j => boxSlotOf_oneSlot_integrable_loc hmeas hbdd hsupp _ _ j Theta hΘm hΘb hΘs
  -- the sums over the `pairSet`s
  have hIntSumI : ∀ k : Mode,
      MeasureTheory.Integrable (fun x : Xn n =>
        (starRingEnd ℂ) (Theta x) *
          (∑ p ∈ Submission.BoseGases.pairSet n,
            boxSlotOf e (evec0 m) (f k) p.1 (boxSlotOf e (f k) (evec0 m) p.2 Theta)) x) :=
    fun k => integrable_finset_sum_loc _ _ _ (fun p _ => hIntI k p.1 p.2)
  have hIntSumIIa : ∀ k : Mode,
      MeasureTheory.Integrable (fun x : Xn n =>
        (starRingEnd ℂ) (Theta x) *
          (∑ p ∈ Submission.BoseGases.pairSet n,
            boxSlotOf e (evec0 m) (f k) p.1 (boxSlotOf e (evec0 m) (f (-k)) p.2 Theta)) x) :=
    fun k => integrable_finset_sum_loc _ _ _ (fun p _ => hIntIIa k p.1 p.2)
  have hIntSumIIb : ∀ k : Mode,
      MeasureTheory.Integrable (fun x : Xn n =>
        (starRingEnd ℂ) (Theta x) *
          (∑ p ∈ Submission.BoseGases.pairSet n,
            boxSlotOf e (f k) (evec0 m) p.1 (boxSlotOf e (f (-k)) (evec0 m) p.2 Theta)) x) :=
    fun k => integrable_finset_sum_loc _ _ _ (fun p _ => hIntIIb k p.1 p.2)
  have hIntSumIII : ∀ k : Mode,
      MeasureTheory.Integrable (fun x : Xn n =>
        (starRingEnd ℂ) (Theta x) *
          (∑ p ∈ Submission.BoseGases.pairSet n,
            boxSlotOf e (evec0 m) (evec0 m) p.1 (boxSlotOf e (f k) (f k) p.2 Theta)) x) :=
    fun k => integrable_finset_sum_loc _ _ _ (fun p _ => hIntIII k p.1 p.2)
  have hIntSumE : ∀ k : Mode,
      MeasureTheory.Integrable (fun x : Xn n =>
        (starRingEnd ℂ) (Theta x) *
          (∑ j : Fin n, boxSlotOf e (f k) (f k) j Theta) x) :=
    fun k => integrable_finset_sum_loc _ _ _ (fun j _ => hIntE k j)  -- ## 2. the rewriting
  have hIntS1 := integrable_finset_sum_loc (Finset.univ : Finset Mode) Theta
      (fun k : Mode => (E.W1 k + E.W1omega k) •
        (∑ p ∈ Submission.BoseGases.pairSet n,
          boxSlotOf e (evec0 m) (f k) p.1 (boxSlotOf e (f k) (evec0 m) p.2 Theta)))
      (fun k _ => integrable_smul_loc Theta _ _ (hIntSumI k))
  have hIntS2 := integrable_finset_sum_loc (Finset.univ : Finset Mode) Theta
      (fun k : Mode => E.W1 k •
        ((∑ p ∈ Submission.BoseGases.pairSet n,
            boxSlotOf e (evec0 m) (f k) p.1
              (boxSlotOf e (evec0 m) (f (-k)) p.2 Theta))
          + (∑ p ∈ Submission.BoseGases.pairSet n,
            boxSlotOf e (f k) (evec0 m) p.1
              (boxSlotOf e (f (-k)) (evec0 m) p.2 Theta))))
      (fun k _ => integrable_smul_loc Theta _ _
        (integrable_add_loc Theta _ _ (hIntSumIIa k) (hIntSumIIb k)))
  have hIntS3 := integrable_finset_sum_loc (Finset.univ : Finset Mode) Theta
      (fun k : Mode =>
        ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
            (∑ p ∈ Submission.BoseGases.pairSet n,
              boxSlotOf e (evec0 m) (evec0 m) p.1
                (boxSlotOf e (f k) (f k) p.2 Theta))
          - (E.mu * E.W1 0) • (∑ j : Fin n, boxSlotOf e (f k) (f k) j Theta)))
      (fun k _ => integrable_sub_loc Theta _ _
        (integrable_smul_loc Theta _ _ (hIntSumIII k))
        (integrable_smul_loc Theta _ _ (hIntSumE k)))
  have hIntA := integrable_smul_loc (d := n) Theta (E.ell ^ (-(3 : ℝ)))
      (∑ k : Mode, (E.W1 k + E.W1omega k) •
        (∑ p ∈ Submission.BoseGases.pairSet n,
          boxSlotOf e (evec0 m) (f k) p.1 (boxSlotOf e (f k) (evec0 m) p.2 Theta)))
      hIntS1
  have hIntB := integrable_smul_loc (d := n) Theta ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ)))
      (∑ k : Mode, E.W1 k •
        ((∑ p ∈ Submission.BoseGases.pairSet n,
            boxSlotOf e (evec0 m) (f k) p.1
              (boxSlotOf e (evec0 m) (f (-k)) p.2 Theta))
          + (∑ p ∈ Submission.BoseGases.pairSet n,
            boxSlotOf e (f k) (evec0 m) p.1
              (boxSlotOf e (f (-k)) (evec0 m) p.2 Theta))))
      hIntS2
  have hIntC := hIntS3
  have hIntAB := integrable_add_loc Theta _ _ hIntA hIntB
  rw [potPairRows_pairSet_flat e hmeas hbdd hsupp horth f hf0 E Theta hΘm hΘb]
  rw [cIPn_add_loc Theta _ _ hIntAB hIntC]
  rw [cIPn_add_loc Theta _ _ hIntA hIntB]
  congr 1
  · congr 1
    · -- block I
      rw [cIPn_smul_loc]
      congr 1
      rw [cIPn_finset_sum_loc Finset.univ _ _
        (fun k _ => integrable_smul_loc Theta _ _ (hIntSumI k))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [cIPn_smul_loc]
      congr 1
      rw [cIPn_finset_sum_loc (Submission.BoseGases.pairSet n) _ _
        (fun p _ => hIntI k p.1 p.2)]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      exact atomI k p.1 p.2 ((Finset.mem_filter.mp hp).2)
    · -- block II
      rw [cIPn_smul_loc]
      congr 1
      rw [cIPn_finset_sum_loc Finset.univ _ _
        (fun k _ => integrable_smul_loc Theta _ _
          (integrable_add_loc Theta _ _ (hIntSumIIa k) (hIntSumIIb k)))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [cIPn_smul_loc]
      congr 1
      rw [cIPn_add_loc _ _ _ (hIntSumIIa k) (hIntSumIIb k)]
      congr 1
      · rw [cIPn_finset_sum_loc (Submission.BoseGases.pairSet n) _ _
          (fun p _ => hIntIIa k p.1 p.2)]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        exact atomIIa k p.1 p.2 ((Finset.mem_filter.mp hp).2)
      · rw [cIPn_finset_sum_loc (Submission.BoseGases.pairSet n) _ _
          (fun p _ => hIntIIb k p.1 p.2)]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        exact atomIIb k p.1 p.2 ((Finset.mem_filter.mp hp).2)
  · -- block III
    rw [cIPn_finset_sum_loc Finset.univ _ _
      (fun k _ => integrable_sub_loc Theta _ _
        (integrable_smul_loc Theta _ _ (hIntSumIII k))
        (integrable_smul_loc Theta _ _ (hIntSumE k)))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [cIPn_sub_loc _ _ _ (integrable_smul_loc Theta _ _ (hIntSumIII k))
        (integrable_smul_loc Theta _ _ (hIntSumE k))]
    congr 1
    · rw [cIPn_smul_loc]
      congr 1
      rw [cIPn_finset_sum_loc (Submission.BoseGases.pairSet n) _ _
        (fun p _ => hIntIII k p.1 p.2)]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      exact atomIII k p.1 p.2 ((Finset.mem_filter.mp hp).2)
    · rw [cIPn_smul_loc]
      congr 1
      rw [cIPn_finset_sum_loc Finset.univ _ _ (fun j _ => hIntE k j)]
      exact Finset.sum_congr rfl (fun j _ => atomE k j)

end Work.BoseBoxFock
