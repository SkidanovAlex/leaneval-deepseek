import Mathlib
import Submission.Work.FIArea4.UnitsFlat.wdyad1123_units
import Submission.Work.FIArea4.Wdyad_le_trivial
import Submission.Work.FIArea4.Vflip.Wdyad_symm
import Submission.Work.FIArea4.Vflip.normSq_gammaF
import Submission.Work.FIArea4.prop_11_1_defs

/-!
# FI (11.24): the unit-class form of the dyadic dual variance

This module proves `Work.FIArea4.Wdyad_units`: the dual variance

`Wdyad D R S β = ∑_{R<r≤2R} ∑_{S<s≤2S} |∑_{D<d≤2D} ∑_{a<d} β a d · M((d,a),(r,s))|²`

for coefficient matrices `β` supported on the **reduced** classes `(a,d) = 1` is bounded by the
bracket

`D^{-1/2}·R·S + (R·S^{3/4} + S·R^{3/4} + D·√(RS) + D·min(R,S))·(RS)^ε`

times the energy `∑_{d,a} |β a d|²` — i.e. the `DR` term of (11.23) has been replaced by
`D·min(R,S)`, which is what the `r ↔ s` symmetry of the dyadic dual variance buys.

The proof is a two-case reduction to the two estimates that are already formalised:

* (11.23), `Work.FIArea4.Wdyad_le_1123`:
  `Wdyad D R S γ ≤ C₁·(D^{-1/2}RS + (S·R^{3/4} + D·R + D·√(RS))·(DR)^ε)·‖γ‖²`,
  usable when `D ≤ S` (then `(DR)^ε ≤ (RS)^ε`) — and its asymmetric `D·R` term is exactly the
  `D·min(R,S)` term of the target under the ordering `R ≤ S`;
* the trivial bound, `Work.FIArea4.Wdyad_le_trivial`:
  `Wdyad D R S γ ≤ C₂·(RS + D·min(R,S) + D)·‖γ‖²`, usable when `S ≤ D` (then `RS ≤ D·min(R,S)`);

the ordering `R ≤ S` is imposed by `Work.FIArea4.Vflip.Wdyad_symm` (`Wdyad D R S β =
Wdyad D S R (gammaF β)`) whose transform `gammaF` preserves both the support hypothesis and the
energy `∑_{d,a}|β a d|²` (`Work.FIArea4.Vflip.normSq_gammaF`).
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The bracket of the target estimate (FI (11.24)). -/
noncomputable def WTb (D R S : ℕ) (ε : ℝ) : ℝ :=
  (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
    + ((R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) + (D : ℝ) * (min R S : ℝ))
      * (((R : ℝ) * (S : ℝ)) ^ ε)

/-- The energy `∑_{D<d≤2D} ∑_{a<d} ‖β a d‖²` of a coefficient matrix. -/
noncomputable def WE (D : ℕ) (β : ℕ → ℕ → ℂ) : ℝ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (β a d)

/-- The bracket of FI (11.23). -/
noncomputable def B1123 (D R S : ℕ) (ε : ℝ) : ℝ :=
  (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
    + ((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε)

/-- The bracket of the trivial bound. -/
noncomputable def Btriv (D R S : ℕ) : ℝ :=
  (R : ℝ) * (S : ℝ) + (D : ℝ) * (min R S : ℝ) + (D : ℝ)

/-- The target bracket is symmetric in `R` and `S`, as it must be. -/
lemma WTb_swap (D R S : ℕ) (ε : ℝ) : WTb D S R ε = WTb D R S ε := by
  have hs : Real.sqrt ((S : ℝ) * (R : ℝ)) = Real.sqrt ((R : ℝ) * (S : ℝ)) := by rw [mul_comm]
  have he : ((S : ℝ) * (R : ℝ)) ^ ε = ((R : ℝ) * (S : ℝ)) ^ ε := by rw [mul_comm]
  have hm : (min S R : ℝ) = (min R S : ℝ) := by rw [min_comm]
  simp only [WTb]
  rw [hs, he, hm]
  ring

/-- **The `D ≤ S` comparison of brackets.**  When `D ≤ S` (and `R ≤ S`) the bracket of (11.23)
is dominated by the target bracket: `(DR)^ε ≤ (RS)^ε` and `D·R = D·min(R,S)`. -/
lemma bracket_A {ε : ℝ} (hε : 0 < ε) {D R S : ℕ} (hDS : D ≤ S) (hRS : R ≤ S) :
    B1123 D R S ε ≤ WTb D R S ε := by
  have hDRS : (D : ℝ) * (R : ℝ) ≤ (R : ℝ) * (S : ℝ) := by
    have h1 : (D : ℝ) ≤ (S : ℝ) := by exact_mod_cast hDS
    have h2 : (0 : ℝ) ≤ (R : ℝ) := by positivity
    nlinarith
  have hpow : ((D : ℝ) * (R : ℝ)) ^ ε ≤ ((R : ℝ) * (S : ℝ)) ^ ε :=
    Real.rpow_le_rpow (by positivity) hDRS hε.le
  have hmin : (min R S : ℝ) = (R : ℝ) := by
    have h : (R : ℝ) ≤ (S : ℝ) := by exact_mod_cast hRS
    exact min_eq_left h
  have hv0 : (0 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := Real.rpow_nonneg (by positivity) _
  have hbr : (0 : ℝ) ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
      + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) := by positivity
  have h1 : ((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε)
      ≤ ((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((R : ℝ) * (S : ℝ)) ^ ε) :=
    mul_le_mul_of_nonneg_left hpow hbr
  have h2 : ((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((R : ℝ) * (S : ℝ)) ^ ε)
      ≤ ((R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) + (D : ℝ) * (R : ℝ))
        * (((R : ℝ) * (S : ℝ)) ^ ε) := by
    refine mul_le_mul_of_nonneg_right ?_ hv0
    have h0 : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    linarith
  have hthis : WTb D R S ε = (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
      + ((R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) + (D : ℝ) * (min R S : ℝ))
        * (((R : ℝ) * (S : ℝ)) ^ ε) := rfl
  have hthis2 : B1123 D R S ε = (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
      + ((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε) := rfl
  rw [hthis, hthis2, hmin]
  linarith

/-- **The `S ≤ D` comparison of brackets.**  When `S ≤ D` (and `R ≤ S`) the trivial bracket is
dominated by three times the target bracket, because then `RS ≤ D·min(R,S) ≥ D`. -/
lemma bracket_B {ε : ℝ} (hε : 0 < ε) {D R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRS : R ≤ S)
    (hDS : S ≤ D) :
    Btriv D R S ≤ 3 * WTb D R S ε := by
  have hmin : (min R S : ℝ) = (R : ℝ) := min_eq_left (by exact_mod_cast hRS)
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hSR : (S : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDS
  have hv1 : (1 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := Real.one_le_rpow (by nlinarith) hε.le
  have hDRnn : (0 : ℝ) ≤ (D : ℝ) * (R : ℝ) := by positivity
  have hv0 : (0 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := by positivity
  have hkey1 : (R : ℝ) * (S : ℝ) ≤ (D : ℝ) * (R : ℝ) := by nlinarith
  have hkey2 : (D : ℝ) ≤ (D : ℝ) * (R : ℝ) := by nlinarith
  have hbracket : (D : ℝ) * (R : ℝ)
      ≤ (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) + (D : ℝ) * (min R S : ℝ) := by
    rw [hmin]
    have h0 : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    have h0' : (0 : ℝ) ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    have h0'' : (0 : ℝ) ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) := by positivity
    linarith
  have hb : (D : ℝ) * (R : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε) ≤ WTb D R S ε := by
    have hstep := mul_le_mul_of_nonneg_right hbracket hv0
    unfold WTb
    have h0 : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) := by positivity
    linarith [hstep]
  have hB : Btriv D R S = (R : ℝ) * (S : ℝ) + (D : ℝ) * (R : ℝ) + (D : ℝ) := by
    unfold Btriv; rw [hmin]
  calc Btriv D R S = (R : ℝ) * (S : ℝ) + (D : ℝ) * (R : ℝ) + (D : ℝ) := hB
    _ ≤ 3 * ((D : ℝ) * (R : ℝ)) := by linarith
    _ ≤ 3 * ((D : ℝ) * (R : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)) := by nlinarith [hDRnn, hv1]
    _ ≤ 3 * WTb D R S ε := by linarith [hb]

/-- **FI (11.24)** for coefficient matrices supported on the reduced classes `(a,d) = 1`. -/
theorem Wdyad_units (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (β : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      (∀ a d, β a d ≠ 0 → Nat.Coprime a d) →
      Work.FIArea4.Wdyad D R S β ≤ C * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
          + ((R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)
              + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
              + (D : ℝ) * (min R S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε))
        * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (β a d)) := by
  obtain ⟨C₁, hC₁pos, hC₁'⟩ := UnitsFlat.Wdyad_le_1123_units ε hε
  obtain ⟨C₂, hC₂pos, hC₂'⟩ := Wdyad_le_trivial
  have hC₁ : ∀ (D R S : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      Wdyad D R S γ ≤ C₁ * B1123 D R S ε * WE D γ := by
    intro D R S γ hD hR hS
    simpa only [B1123, WE] using hC₁' D R S γ hD hR hS
  have hC₂ : ∀ (D R S : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      Wdyad D R S γ ≤ C₂ * Btriv D R S * WE D γ := by
    intro D R S γ hD hR hS
    simpa only [Btriv, WE] using hC₂' D R S γ hD hR hS
  refine ⟨C₁ + 3 * C₂, by linarith, ?_⟩
  intro D R S β hD hR hS hβ
  have step : ∀ {D R S : ℕ}, 1 ≤ D → 1 ≤ R → 1 ≤ S → R ≤ S → ∀ γ : ℕ → ℕ → ℂ,
      Wdyad D R S γ ≤ (C₁ + 3 * C₂) * WTb D R S ε * WE D γ := by
    intro D R S hD hR hS hRS γ
    have hEnn : 0 ≤ WE D γ := by
      unfold WE
      exact Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
    have hTnn : 0 ≤ WTb D R S ε := by unfold WTb; positivity
    by_cases hDS : D ≤ S
    · have hb := hC₁ D R S γ hD hR hS
      have hbr := bracket_A hε hDS hRS
      have h1 : C₁ * B1123 D R S ε ≤ (C₁ + 3 * C₂) * WTb D R S ε := by
        have h2 : C₁ * B1123 D R S ε ≤ C₁ * WTb D R S ε := mul_le_mul_of_nonneg_left hbr hC₁pos.le
        have h3 : C₁ * WTb D R S ε ≤ (C₁ + 3 * C₂) * WTb D R S ε :=
          mul_le_mul_of_nonneg_right (by linarith) hTnn
        linarith
      calc Wdyad D R S γ ≤ C₁ * B1123 D R S ε * WE D γ := hb
        _ = (C₁ * B1123 D R S ε) * WE D γ := by ring
        _ ≤ ((C₁ + 3 * C₂) * WTb D R S ε) * WE D γ := mul_le_mul_of_nonneg_right h1 hEnn
        _ = (C₁ + 3 * C₂) * WTb D R S ε * WE D γ := by ring
    · have hSD : S < D := not_le.mp hDS
      have hb := hC₂ D R S γ hD hR hS
      have hbr := bracket_B hε hR hS hRS hSD.le
      have h1 : C₂ * Btriv D R S ≤ (C₁ + 3 * C₂) * WTb D R S ε := by
        have h2 : C₂ * Btriv D R S ≤ C₂ * (3 * WTb D R S ε) :=
          mul_le_mul_of_nonneg_left hbr hC₂pos.le
        have h3 : C₂ * (3 * WTb D R S ε) ≤ (C₁ + 3 * C₂) * WTb D R S ε := by
          have h4 : C₂ * 3 ≤ C₁ + 3 * C₂ := by linarith
          calc C₂ * (3 * WTb D R S ε) = (C₂ * 3) * WTb D R S ε := by ring
            _ ≤ (C₁ + 3 * C₂) * WTb D R S ε := mul_le_mul_of_nonneg_right h4 hTnn
        linarith
      calc Wdyad D R S γ ≤ C₂ * Btriv D R S * WE D γ := hb
        _ = (C₂ * Btriv D R S) * WE D γ := by ring
        _ ≤ ((C₁ + 3 * C₂) * WTb D R S ε) * WE D γ := mul_le_mul_of_nonneg_right h1 hEnn
        _ = (C₁ + 3 * C₂) * WTb D R S ε * WE D γ := by ring
  by_cases hRS : R ≤ S
  · show Wdyad D R S β ≤ (C₁ + 3 * C₂) * WTb D R S ε * WE D β
    exact step hD hR hS hRS β
  · have hSR : S ≤ R := le_of_lt (not_le.mp hRS)
    have hsym : Wdyad D R S β = Wdyad D S R (Vflip.gammaF β) :=
      Vflip.Wdyad_symm D R S β hβ
    have hg : ∀ a d, Vflip.gammaF β a d ≠ 0 → Nat.Coprime a d := by
      intro a d h
      by_contra hc
      simp only [Vflip.gammaF] at h
      rw [if_neg hc] at h
      exact h rfl
    have hnorm : WE D (Vflip.gammaF β) = WE D β := Vflip.normSq_gammaF D β hβ
    have hkey := step hD hS hR hSR (Vflip.gammaF β)
    show Wdyad D R S β ≤ (C₁ + 3 * C₂) * WTb D R S ε * WE D β
    calc Wdyad D R S β = Wdyad D S R (Vflip.gammaF β) := hsym
      _ ≤ (C₁ + 3 * C₂) * WTb D S R ε * WE D (Vflip.gammaF β) := hkey
      _ = (C₁ + 3 * C₂) * WTb D R S ε * WE D β := by rw [WTb_swap D R S ε, hnorm]

end

end Work.FIArea4
