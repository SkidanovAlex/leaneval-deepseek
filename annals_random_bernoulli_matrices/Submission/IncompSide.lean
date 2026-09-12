import Mathlib
import Submission.CompressCentered
import Submission.IncompReduction
import Submission.GeoBridge

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Submission.IncompSide

open Matrix MeasureTheory ProbabilityTheory Measure Filter unitInterval
open scoped ENNReal BigOperators

noncomputable section

universe u

open Submission.GeoBridge (E actSqFullFn exists_measurable_clamped_matrix measureReal_matrix_event_eq_of_ae)
open Submission.IncompReduction (shiftMatrix shiftMatrix_apply incEvent normalLe lastFin nVec swapLast incompressible_bound)
open Submission.CompressCentered

/-!
# Incompressible side of Theorem A: σ_min bound in the random-normal form

Combining the compress-side decomposition (`sigma_min_decomp_law_only_any_s`)
with the incompressible reduction (`IncompReduction.incompressible_bound`)
gives, for a law-only Bernoulli(p) matrix family `B` and every shift `s`,
`P{σ_min(Bω+sJ) ≤ u} ≤ (1−p+ε)^n + (2/(ν²δ))·P{|⟨col_last(Mω), Y(Mω)⟩| ≤ 2u√n/ν}`,
where `Mω := Bω + sJ` and `Y` is the measurable unit normal of the first
`n−1` columns.  This is the paper's eq. (comp-incomp) in the fully law-only
setting, ready for the threshold/ε-net machinery of the last layer.
-/

/-- Set identity: the decomp's `∃ f`-event equals `incEvent` applied to the
shifted matrix. -/
lemma raw_event_eq_incEvent {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) {δ ν u : ℝ} :
    (∃ f : Fin n → ℝ, Commons.LinearAlgebra.Net.sqNorm f = 1 ∧
      ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => B i j + s) f ≤ u ^ 2)
    ↔ incEvent (shiftMatrix s B) δ ν u := by
  unfold incEvent
  apply exists_congr
  intro f
  apply and_congr_right
  intro hf1
  apply and_congr_right
  intro hnot
  have hfn : (fun i j : Fin n => (shiftMatrix s B) i j) = fun i j : Fin n => B i j + s := by
    funext i j
    rw [shiftMatrix_apply]
  constructor
  · intro hfimg
    rwa [hfn]
  · intro hfimg
    rwa [← hfn]

/-- `σ_min`-decomposition combined with the incompressible reduction: the
random-normal form of the incompressible side (law-only hypotheses). -/
theorem sigma_min_le_normal_bound {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ) (h2n : 2 ≤ n), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
        (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P),
        ∀ s : ℝ, ∀ u : ℝ, 0 < u →
          u ≤ γ₀ * Real.sqrt (n : ℝ) →
          P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
            ≤ (1 - (p : ℝ) + ε) ^ n
              + (2 / (ν ^ 2 * δ)) *
                  P.real {ω : Ω | normalLe (le_trans (by norm_num : (1 : ℕ) ≤ 2) h2n) (shiftMatrix s (B ω))
                      (2 * u * Real.sqrt (n : ℝ) / ν)} := by
  classical
  rcases sigma_min_decomp_law_only_any_s hp₀ hp₁ hε₀ with
    ⟨n₀, hn₀2, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, hdec⟩
  refine ⟨n₀, hn₀2, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, ?_⟩
  intro n h2n hn Ω mΩ P hP B hBind hBlaw s u hu0 hule
  have hn2 : 2 ≤ n := h2n
  -- decomp
  have hdecB := hdec n hn (Ω := Ω) P B hBind hBlaw s u hu0 hule
  -- measurable clamped version
  rcases exists_measurable_clamped_matrix (P := P) B hBind hBlaw with
    ⟨Bc, hcm, hcind, hclaw, hcpt, hcae⟩
  let Ei : Set Ω := {ω : Ω | incEvent (shiftMatrix s (B ω)) δ ν u}
  let EiC : Set Ω := {ω : Ω | incEvent (shiftMatrix s (Bc ω)) δ ν u}
  have hEi_eq_raw : {ω : Ω | ∃ f : Fin n → ℝ, Commons.LinearAlgebra.Net.sqNorm f = 1 ∧
        ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
        actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} = Ei := by
    ext ω
    exact (raw_event_eq_incEvent (B ω) s (δ := δ) (ν := ν) (u := u)).symm
  -- apply the incompressible bound to the clamped family
  have hbndC : P.real EiC ≤ (2 / (ν ^ 2 * δ)) *
      P.real {ω : Ω | normalLe (le_trans (by norm_num : (1 : ℕ) ≤ 2) h2n) (shiftMatrix s (Bc ω))
          (2 * u * Real.sqrt (n : ℝ) / ν)} := by
    dsimp [EiC]
    exact incompressible_bound hn2 P (B := fun ω => Bc ω) hcm hcind hclaw s hδ0 hν0 (le_of_lt hu0)
  -- Ei event for B equals EiC by ae entry-equality transfer
  have hae' : ∀ i j : Fin n, (fun ω => B ω i j) =ᵐ[P] (fun ω => Bc ω i j) := by
    intro i j
    exact (hcae i j).symm
  have htrEi : P.real Ei = P.real EiC := by
    let S : Set (Matrix (Fin n) (Fin n) ℝ) :=
      {M : Matrix (Fin n) (Fin n) ℝ | incEvent (shiftMatrix s M) δ ν u}
    have h1 : Ei = {ω : Ω | B ω ∈ S} := by rfl
    have h2 : EiC = {ω : Ω | Bc ω ∈ S} := by rfl
    rw [h1, h2]
    exact measureReal_matrix_event_eq_of_ae P B Bc hae' S
  -- transfer of the normal event
  have htrN : P.real {ω : Ω | normalLe (le_trans (by norm_num : (1 : ℕ) ≤ 2) h2n) (shiftMatrix s (Bc ω))
          (2 * u * Real.sqrt (n : ℝ) / ν)} =
      P.real {ω : Ω | normalLe (le_trans (by norm_num : (1 : ℕ) ≤ 2) h2n) (shiftMatrix s (B ω))
          (2 * u * Real.sqrt (n : ℝ) / ν)} := by
    let S : Set (Matrix (Fin n) (Fin n) ℝ) :=
      {M : Matrix (Fin n) (Fin n) ℝ | normalLe (le_trans (by norm_num : (1 : ℕ) ≤ 2) h2n) M
          (2 * u * Real.sqrt (n : ℝ) / ν)}
    have hae2 : ∀ i j : Fin n, (fun ω => shiftMatrix s (B ω) i j) =ᵐ[P]
        (fun ω => shiftMatrix s (Bc ω) i j) := by
      intro i j
      have h := hae' i j
      filter_upwards [h] with ω hω
      rw [shiftMatrix_apply, shiftMatrix_apply]
      rw [hω]
    have heq := measureReal_matrix_event_eq_of_ae P (fun ω => shiftMatrix s (B ω))
      (fun ω => shiftMatrix s (Bc ω)) hae2 S
    have hs1 : {ω : Ω | shiftMatrix s (Bc ω) ∈ S} =
        {ω : Ω | normalLe (le_trans (by norm_num : (1 : ℕ) ≤ 2) h2n) (shiftMatrix s (Bc ω))
            (2 * u * Real.sqrt (n : ℝ) / ν)} := by rfl
    have hs2 : {ω : Ω | shiftMatrix s (B ω) ∈ S} =
        {ω : Ω | normalLe (le_trans (by norm_num : (1 : ℕ) ≤ 2) h2n) (shiftMatrix s (B ω))
            (2 * u * Real.sqrt (n : ℝ) / ν)} := by rfl
    rw [hs2, hs1] at heq
    exact heq.symm
  -- put it together
  calc
    P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
        ≤ (1 - (p : ℝ) + ε) ^ n
            + P.real {ω : Ω | ∃ f : Fin n → ℝ, Commons.LinearAlgebra.Net.sqNorm f = 1 ∧
                ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
                actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} := hdecB
    _ = (1 - (p : ℝ) + ε) ^ n + P.real Ei := by
            rw [hEi_eq_raw]
    _ ≤ (1 - (p : ℝ) + ε) ^ n + (2 / (ν ^ 2 * δ)) *
          P.real {ω : Ω | normalLe (le_trans (by norm_num : (1 : ℕ) ≤ 2) h2n) (shiftMatrix s (Bc ω))
              (2 * u * Real.sqrt (n : ℝ) / ν)} := by
            rw [htrEi]
            linarith [hbndC]
    _ = (1 - (p : ℝ) + ε) ^ n + (2 / (ν ^ 2 * δ)) *
          P.real {ω : Ω | normalLe (le_trans (by norm_num : (1 : ℕ) ≤ 2) h2n) (shiftMatrix s (B ω))
              (2 * u * Real.sqrt (n : ℝ) / ν)} := by
            rw [htrN]

end

end Submission.IncompSide
