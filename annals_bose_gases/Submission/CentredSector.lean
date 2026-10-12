import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.Q0Value
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — sector counts on the centred analysis box

The condensate/excited sector counts on the centred box `abox N ℓ`
(geometry decision (A)):

    S₁  = Σ_i  ‖PᵢΦ‖²      (condensed-particle count)
    n₊  = Σ_i  ‖QᵢΦ‖²      (excited-particle count)
    S₂  = Σ_{i≠j} ‖PᵢPⱼΦ‖² (pair-condensate sum used by `q0_expect`)

Per-particle Parseval `‖Φ‖² = ‖PᵢΦ‖² + ‖QᵢΦ‖²` (from `aQ_ortho_box`,
`aP_sym_box`, `aP_idem`) gives the counting identity

    n₊ + S₁ = N·‖Φ‖² ,                                          (sector_parseval)

and the contraction `‖PᵢΨ‖² ≤ ‖Ψ‖²` (`aP_sq_le`) gives

    ‖PᵢPⱼΦ‖² ≤ ‖PⱼΦ‖²        (pair contraction)  and  S₂ ≤ (N−1)·S₁ .

These are the corpus-native (first-quantized, no symmetry needed) versions of
the FS sector-count bounds (`eq:Densities`, `thm:aprioribounds` `eq:apriorinn+`),
used in the a-priori bounds and the Q1/Q2/potapp estimates on the analysis box.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Condensed-particle count: `S₁ = Σ_i ‖PᵢΦ‖²` (box L² norms over `abox N ℓ`). -/
noncomputable def cS1 (ℓ : ℝ) {N : ℕ} (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2

/-- Pair-condensate sum: `S₂ = Σ_{i≠j} ‖PᵢPⱼΦ‖²`. -/
noncomputable def cS2 (ℓ : ℝ) {N : ℕ} (Φ : X N → ℝ) : ℝ :=
  ∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2

/-- Excited-particle count: `n₊ = Σ_i ‖QᵢΦ‖²`. -/
noncomputable def cnPlus (ℓ : ℝ) {N : ℕ} (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2

/-- Per-particle Parseval: `‖Φ‖² = ‖PᵢΦ‖² + ‖QᵢΦ‖²`. -/
lemma sq_norm_decomp {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, (Φ x) ^ 2) =
      (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) +
      (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
  have hInt_ΦP : IntegrableOn (fun x : X N => Φ x * aP ℓ i Φ x) (abox N ℓ) volume :=
    integrableOn_mul_aP hℓ i hΦc hΦc
  have hInt_P2 : IntegrableOn (fun x : X N => (aP ℓ i Φ x) ^ 2) (abox N ℓ) volume :=
    integrableOn_sq_aP hℓ i hΦc
  have hInt_Q2 : IntegrableOn (fun x : X N => (aQ ℓ i Φ x) ^ 2) (abox N ℓ) volume :=
    integrableOn_sq_aQ hℓ i hΦc
  have hInt_Φ2 : IntegrableOn (fun x : X N => (Φ x) ^ 2) (abox N ℓ) volume :=
    integrableOn_abox_of_continuous hℓ (hΦc.pow 2)
  have hIntPΦ : IntegrableOn (fun x : X N => aP ℓ i Φ x * Φ x) (abox N ℓ) volume := by
    simpa [mul_comm] using hInt_ΦP
  -- orthogonality: `∫(PᵢΦ)·Φ = ∫(PᵢΦ)²`
  have hortho : (∫ x in abox N ℓ, aP ℓ i Φ x * Φ x)
      = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
    have hsub : (∫ x in abox N ℓ, aP ℓ i Φ x * Φ x) - (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) = 0 := by
      calc
        (∫ x in abox N ℓ, aP ℓ i Φ x * Φ x) - (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)
            = ∫ x in abox N ℓ, (aP ℓ i Φ x * Φ x - (aP ℓ i Φ x) ^ 2) := by
                rw [← integral_sub hIntPΦ hInt_P2]
        _ = ∫ x in abox N ℓ, aP ℓ i Φ x * aQ ℓ i Φ x := by
                apply integral_congr_ae
                filter_upwards with x
                unfold aQ
                ring
        _ = 0 := aQ_ortho_box hℓ i hΦc
    linarith
  -- commuted version `∫Φ·(PᵢΦ) = ∫(PᵢΦ)²`
  have hΦP : (∫ x in abox N ℓ, Φ x * aP ℓ i Φ x)
      = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
    calc
      (∫ x in abox N ℓ, Φ x * aP ℓ i Φ x)
          = (∫ x in abox N ℓ, aP ℓ i Φ x * Φ x) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [mul_comm]
      _ = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := hortho
  -- integrability of `Φ·(QᵢΦ)` and `(PᵢΦ)·(QᵢΦ)`, as combinations of known pieces
  have hInt_ΦQ : IntegrableOn (fun x : X N => Φ x * aQ ℓ i Φ x) (abox N ℓ) volume := by
    have h := hInt_Φ2.sub hInt_ΦP
    have hEq : ((fun x : X N => (Φ x) ^ 2) - fun x : X N => Φ x * aP ℓ i Φ x)
        = (fun x : X N => Φ x * aQ ℓ i Φ x) := by
      funext x
      change (Φ x) ^ 2 - Φ x * aP ℓ i Φ x = Φ x * aQ ℓ i Φ x
      unfold aQ
      ring
    rwa [hEq] at h
  have hInt_PQ : IntegrableOn (fun x : X N => aP ℓ i Φ x * aQ ℓ i Φ x) (abox N ℓ) volume := by
    have h := hIntPΦ.sub hInt_P2
    have hEq : ((fun x : X N => aP ℓ i Φ x * Φ x) - fun x : X N => (aP ℓ i Φ x) ^ 2)
        = (fun x : X N => aP ℓ i Φ x * aQ ℓ i Φ x) := by
      funext x
      change aP ℓ i Φ x * Φ x - (aP ℓ i Φ x) ^ 2 = aP ℓ i Φ x * aQ ℓ i Φ x
      unfold aQ
      ring
    rwa [hEq] at h
  -- `(QᵢΦ)² = Φ·(QᵢΦ) − (PᵢΦ)·(QᵢΦ)` pointwise; by orthogonality the second term vanishes
  have hQ2a : (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
      = (∫ x in abox N ℓ, Φ x * aQ ℓ i Φ x) := by
    calc
      (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
          = ∫ x in abox N ℓ, (Φ x * aQ ℓ i Φ x - aP ℓ i Φ x * aQ ℓ i Φ x) := by
              apply integral_congr_ae
              filter_upwards with x
              unfold aQ
              ring
      _ = (∫ x in abox N ℓ, Φ x * aQ ℓ i Φ x) - (∫ x in abox N ℓ, aP ℓ i Φ x * aQ ℓ i Φ x) := by
              rw [← integral_sub hInt_ΦQ hInt_PQ]
      _ = (∫ x in abox N ℓ, Φ x * aQ ℓ i Φ x) := by
              rw [aQ_ortho_box hℓ i hΦc]
              ring
  -- `Φ·(QᵢΦ) = Φ² − Φ·(PᵢΦ)`, and `∫Φ·(PᵢΦ) = ∫(PᵢΦ)²`
  have hQ2 : (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
      = (∫ x in abox N ℓ, (Φ x) ^ 2) - (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
    calc
      (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
          = (∫ x in abox N ℓ, Φ x * aQ ℓ i Φ x) := hQ2a
      _ = ∫ x in abox N ℓ, ((Φ x) ^ 2 - Φ x * aP ℓ i Φ x) := by
              apply integral_congr_ae
              filter_upwards with x
              unfold aQ
              ring
      _ = (∫ x in abox N ℓ, (Φ x) ^ 2) - (∫ x in abox N ℓ, Φ x * aP ℓ i Φ x) := by
              rw [← integral_sub hInt_Φ2 hInt_ΦP]
      _ = (∫ x in abox N ℓ, (Φ x) ^ 2) - (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
              rw [hΦP]
  -- finish
  calc
    (∫ x in abox N ℓ, (Φ x) ^ 2)
        = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)
            + ((∫ x in abox N ℓ, (Φ x) ^ 2) - (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)) := by
            ring
    _ = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)
            + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
            rw [hQ2]

/-- Sector Parseval: `n₊ + S₁ = N·‖Φ‖²`. -/
lemma cnPlus_add_cS1 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    cnPlus ℓ Φ + cS1 ℓ Φ = (N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  unfold cnPlus cS1
  calc
    (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
        + (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)
        = ∑ i : Fin N, ((∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
            + (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)) := by
            rw [← Finset.sum_add_distrib]
    _ = ∑ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [add_comm]
            exact (sq_norm_decomp hℓ i hΦc).symm
    _ = (N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
            rw [Finset.sum_const]
            simp [nsmul_eq_mul]

/-- The condensed count is nonnegative. -/
lemma cS1_nonneg {N : ℕ} {ℓ : ℝ} {Φ : X N → ℝ} : 0 ≤ cS1 ℓ Φ := by
  unfold cS1
  exact Finset.sum_nonneg (fun i hi =>
    integral_nonneg (μ := (volume : Measure (X N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg _))

/-- The excited count is nonnegative. -/
lemma cnPlus_nonneg {N : ℕ} {ℓ : ℝ} {Φ : X N → ℝ} : 0 ≤ cnPlus ℓ Φ := by
  unfold cnPlus
  exact Finset.sum_nonneg (fun i hi =>
    integral_nonneg (μ := (volume : Measure (X N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg _))

/-- The pair-condensate sum is nonnegative. -/
lemma cS2_nonneg {N : ℕ} {ℓ : ℝ} {Φ : X N → ℝ} : 0 ≤ cS2 ℓ Φ := by
  unfold cS2
  exact Finset.sum_nonneg (fun p hp =>
    integral_nonneg (μ := (volume : Measure (X N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg _))

/-- Condensed count bounded by `N·‖Φ‖²`. -/
lemma cS1_le_norm_sq {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    cS1 ℓ Φ ≤ (N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  unfold cS1
  calc
    (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)
        ≤ ∑ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2) := by
          exact Finset.sum_le_sum (fun i hi => aP_sq_le hℓ i hΦc)
    _ = (N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]

/-- Excited count bounded by `N·‖Φ‖²`. -/
lemma cnPlus_le_norm_sq {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    cnPlus ℓ Φ ≤ (N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  have h := cnPlus_add_cS1 hℓ hΦc
  have h1 : 0 ≤ cS1 ℓ Φ := cS1_nonneg
  linarith

/-- Pair contraction: `‖PᵢPⱼΦ‖² ≤ ‖PⱼΦ‖²` for `i ≠ j`. -/
lemma pair_contract {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2) ≤
      (∫ x in abox N ℓ, (aP ℓ j Φ x) ^ 2) := by
  exact aP_sq_le hℓ i (aP_continuous hℓ j hΦc)

/-- Counting: the sum over distinct ordered pairs of a function of the second
coordinate equals `(N−1)` times the sum over all coordinates. -/
lemma sum_pairSet_second_eq (N : ℕ) (g : Fin N → ℝ) :
    (∑ p ∈ pairSet N, g p.2) = ((N : ℝ) - 1) * (∑ i : Fin N, g i) := by
  let univNN : Finset (Fin N × Fin N) := Finset.univ
  let univN : Finset (Fin N) := Finset.univ
  -- diagonal sum equals ∑ g i
  have hdiag : (∑ p ∈ univNN.filter (fun p => ¬ p.1 ≠ p.2), g p.2)
      = (∑ i : Fin N, g i) := by
    refine Finset.sum_bij (s := univNN.filter (fun p => ¬ p.1 ≠ p.2))
      (t := univN)
      (f := fun p : Fin N × Fin N => g p.2) (g := g)
      (i := fun p hp => p.2) ?hi ?inj ?surj ?hv
    · intro p hp
      simp [univN]
    · intro p₁ hp₁ p₂ hp₂ h
      apply Prod.ext
      · have hp1 : ¬ p₁.1 ≠ p₁.2 := (Finset.mem_filter.mp hp₁).2
        have hp2 : ¬ p₂.1 ≠ p₂.2 := (Finset.mem_filter.mp hp₂).2
        have h₁ : p₁.1 = p₁.2 := by by_contra hc; exact hp1 hc
        have h₂ : p₂.1 = p₂.2 := by by_contra hc; exact hp2 hc
        calc p₁.1 = p₁.2 := h₁
             _ = p₂.2 := h
             _ = p₂.1 := h₂.symm
      · exact h
    · intro b hb
      refine ⟨(b, b), ?_, ?_⟩
      · simp [univNN, Finset.mem_filter]
      · rfl
    · intro p hp
      rfl
  -- total sum equals N * ∑ g i
  have htotal : (∑ p ∈ univNN, g p.2)
      = (N : ℝ) * (∑ i : Fin N, g i) := by
    calc
      (∑ p ∈ univNN, g p.2)
          = (∑ p ∈ univN ×ˢ univN, g p.2) := by
              change (∑ p : Fin N × Fin N, g p.2) = ∑ p : Fin N × Fin N, g p.2
              simp [univNN, univN]
      _ = ∑ a ∈ univN, ∑ b ∈ univN, g b := by
              rw [Finset.sum_product]
      _ = (N : ℝ) * (∑ i : Fin N, g i) := by
              rw [Finset.sum_const]
              simp [nsmul_eq_mul, univN]
  -- split: off-diagonal + diagonal = total
  have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := univNN)
      (p := fun p : Fin N × Fin N => p.1 ≠ p.2) (f := fun p : Fin N × Fin N => g p.2)
  have hmain : (∑ p ∈ pairSet N, g p.2) + (∑ i : Fin N, g i)
      = (N : ℝ) * (∑ i : Fin N, g i) := by
    calc
      (∑ p ∈ pairSet N, g p.2) + (∑ i : Fin N, g i)
          = (∑ p ∈ univNN.filter (fun p : Fin N × Fin N => p.1 ≠ p.2), g p.2)
              + (∑ i : Fin N, g i) := by
              simp [pairSet, univNN]
      _ = (∑ p ∈ univNN.filter (fun p : Fin N × Fin N => p.1 ≠ p.2), g p.2)
              + (∑ p ∈ univNN.filter (fun p => ¬ p.1 ≠ p.2), g p.2) := by
              rw [hdiag]
      _ = (∑ p ∈ univNN, g p.2) := hsplit
      _ = (N : ℝ) * (∑ i : Fin N, g i) := htotal
  have h : (∑ p ∈ pairSet N, g p.2) = (N : ℝ) * (∑ i : Fin N, g i) - (∑ i : Fin N, g i) := by
    linarith
  calc
    (∑ p ∈ pairSet N, g p.2) = (N : ℝ) * (∑ i : Fin N, g i) - (∑ i : Fin N, g i) := h
    _ = ((N : ℝ) - 1) * (∑ i : Fin N, g i) := by ring

/-- Pair-condensate sum bounded by `(N−1)·S₁`. -/
lemma cS2_le_mul_cS1 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    cS2 ℓ Φ ≤ ((N : ℝ) - 1) * cS1 ℓ Φ := by
  unfold cS2 cS1
  let g : Fin N → ℝ := fun i => ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
        ≤ ∑ p ∈ pairSet N, g p.2 := by
          exact Finset.sum_le_sum (fun p hp => by
            have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
            simpa [g] using pair_contract hℓ hne hΦc)
    _ = ((N : ℝ) - 1) * (∑ i : Fin N, g i) := sum_pairSet_second_eq N g
    _ = ((N : ℝ) - 1) * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
          simp [g]

/-- Weaker but `N`-free version: `S₂ ≤ N·S₁`. -/
lemma cS2_le_n_mul_cS1 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    cS2 ℓ Φ ≤ (N : ℝ) * cS1 ℓ Φ := by
  have h1 := cS2_le_mul_cS1 hℓ hΦc
  have h2 : 0 ≤ cS1 ℓ Φ := cS1_nonneg
  have h3 : (N : ℝ) - 1 ≤ (N : ℝ) := by linarith
  exact le_trans h1 (mul_le_mul_of_nonneg_right h3 h2)

end BoseGases

end Submission
