import Mathlib
import Submission.Work.FIArea4.Vflip.Wdyad_diff_part_le_gen
import Submission.Work.FIArea4.Vflip.Wloc_bound_fresh
import Submission.Work.FIArea4.lemma_11_4

set_option maxHeartbeats 1000000

/-!
# Uniform (in `S` and `F`) form of the non-flat (`♦`) part bound

`Work.FIArea4.Vflip.Wdyad_diff_part_le_gen` bounds the non-flat part of the dyadic dual form by
`C · (S R^{3/4} + D R + D√(RS)) (DR)^ε · Σ_d Σ_{a<d} |γ(a,d)|²` for a kernel `F` with
`‖F ξ‖ ≤ C₀ S (1 + S|ξ|)⁻²`, but its constant `C` is produced *after* `S` and `F` are fixed.

The constant that the proof actually constructs,
`√(C₁ C₀² 4^{ε/2} (2 C₂ (2^{3/2}+1) + 1)) + 1` with `C₁ = C₁(ε/4)` from
`Wloc_bound_fresh` and `C₂ = C₂(ε/4)` from Lemma 11.4, depends only on `ε` and `C₀`; neither
`S` nor `F` occurs in it.  Here we make that explicit by re-running the argument with the
existential over `C` outside the quantifiers on `S`, `hS`, `F`, `hdec`.  This is exactly the
form in which the estimate is consumed by `Work.FIArea4.bump_majorant_uniform`, where the bump
majorant `F` is manufactured from `S`.
-/

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

noncomputable section

theorem Wdyad_diff_part_le_gen_unif (ε : ℝ) (hε : 0 < ε) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : ℕ) (hS : 1 ≤ S) (F : ℝ → ℂ)
        (hdec : ∀ ξ : ℝ, ‖F ξ‖ ≤ C₀ * (S : ℝ) * (1 + (S : ℝ) * |ξ|) ^ (-(2 : ℝ)))
        (D R : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R →
        ‖∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ (Finset.Ioc D (2 * D)).filter
            (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                        ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          ∑ a ∈ Finset.range (Nat.lcm d1 d2),
            γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
              Work.FIArea4.KK F R d1 d2 a‖
        ≤ C * (((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * R
                + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε))
            * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Wloc_bound_fresh (ε/4) (by linarith)
  have hC₀pos : (0:ℝ) < C₀ := hC₀
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FIArea4.lemma_11_4 (ε/4) (by linarith)
  have hC1n : (0:ℝ) ≤ C1 := hC1pos.le
  have hC₀n : (0:ℝ) ≤ C₀ := hC₀pos.le
  have hC2n : (0:ℝ) ≤ C2 := hC2pos.le
  set C3 : ℝ := C1 * C₀^2 * (4:ℝ)^(ε/2) * (2 * C2 * ((2:ℝ)^((3:ℝ)/2) + 1) + 1) with hC3def
  refine ⟨Real.sqrt C3 + 1, by positivity, ?_⟩
  intro S hS F hdec D R γ hD hR
  have hε4 : (0:ℝ) < ε/4 := by linarith
  have hε0 : (0:ℝ) ≤ ε := hε.le
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  have hD0 : (0:ℝ) < (D:ℝ) := by linarith
  have hR0 : (0:ℝ) < (R:ℝ) := by linarith
  have hS0 : (0:ℝ) < (S:ℝ) := by linarith
  have hC3n : (0:ℝ) ≤ C3 := by rw [hC3def]; positivity
  have hCS := wdg_cs_nonflat F D R γ
  have hEnergy : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
      ≤ (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d))
        * (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
    have h := Work.FIArea4.sigma_gamma_le D γ
    simpa [pow_two] using h
  have hN0 : (0:ℝ) ≤ ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d) :=
    Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
  have hsqrtE : Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
      ≤ ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d) := by
    rw [Real.sqrt_le_iff]
    exact ⟨hN0, by rw [pow_two]; exact hEnergy⟩
  -- per-pair local variance bound with a uniform lcm-power
  have hpair : ∀ d1 d2 : ℕ, d1 ∈ Finset.Ioc D (2*D) → d2 ∈ Finset.Ioc D (2*D) →
      Wloc (F) R d1 d2
        ≤ C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
            ((S:ℝ)^2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)) := by
    intro d1 d2 hd1 hd2
    have hd1' : 1 ≤ d1 := by
      have h := (Finset.mem_Ioc.mp hd1).1; omega
    have hd2' : 1 ≤ d2 := by
      have h := (Finset.mem_Ioc.mp hd2).1; omega
    have hp := hC1 (S:ℝ) hS1 F C₀ hC₀pos hdec R hR d1 d2 hd1' hd2'
    have hqle : (((Nat.lcm d1 d2 : ℕ)) : ℝ) ≤ 4 * (D:ℝ)^2 := by
      have h1 : Nat.lcm d1 d2 ≤ d1 * d2 := by
        have hpos : 0 < d1 * d2 :=
          Nat.mul_pos (by have a := (Finset.mem_Ioc.mp hd1).1; omega)
                      (by have b := (Finset.mem_Ioc.mp hd2).1; omega)
        exact Nat.le_of_dvd hpos (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
      have h2 : ((d1:ℕ):ℝ) ≤ 2 * (D:ℝ) := by
        have := (Finset.mem_Ioc.mp hd1).2
        exact_mod_cast this
      have h3 : ((d2:ℕ):ℝ) ≤ 2 * (D:ℝ) := by
        have := (Finset.mem_Ioc.mp hd2).2
        exact_mod_cast this
      have h4 : ((Nat.lcm d1 d2 : ℕ) : ℝ) ≤ (d1:ℝ) * (d2:ℝ) := by exact_mod_cast h1
      have h5 : ((d1:ℕ):ℝ) * ((d2:ℕ):ℝ) ≤ (2 * (D:ℝ)) * (2 * (D:ℝ)) :=
        mul_le_mul h2 h3 (Nat.cast_nonneg d2) (by positivity)
      nlinarith [h4, h5, hD0.le]
    have hpow : (((Nat.lcm d1 d2 : ℕ) : ℝ) * (R:ℝ))^(ε/4) ≤ (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [hqle, hR0.le]) hε4.le
    have hbase0 : (0:ℝ) ≤ ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (S:ℝ)^2 * wdg_CSsumIoc d1 d2 R
        + ((R:ℝ) + (S:ℝ)) * (R:ℝ) := by
      have h1 : (0:ℝ) ≤ ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
      have h2 : (0:ℝ) ≤ wdg_CSsumIoc d1 d2 R := Complex.normSq_nonneg _
      have h3 : (0:ℝ) ≤ ((R:ℝ) + (S:ℝ)) * (R:ℝ) := by positivity
      have h4 : (0:ℝ) ≤ (S:ℝ)^2 := sq_nonneg _
      nlinarith [h1, h2, h3, h4, mul_nonneg (mul_nonneg h1 h4) h2]
    have hp' : Wloc (F) R d1 d2
        ≤ C1 * C₀^2 * ((((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (S:ℝ)^2 * wdg_CSsumIoc d1 d2 R
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)) * (((Nat.lcm d1 d2 : ℕ) : ℝ) * (R:ℝ))^(ε/4)) := by
      refine hp.trans (le_of_eq ?_)
      rw [wdg_CSsumIoc]
      ring
    calc Wloc (F) R d1 d2
        ≤ C1 * C₀^2 * ((((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (S:ℝ)^2 * wdg_CSsumIoc d1 d2 R
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)) * (((Nat.lcm d1 d2 : ℕ) : ℝ) * (R:ℝ))^(ε/4)) := hp'
      _ ≤ C1 * C₀^2 * ((((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (S:ℝ)^2 * wdg_CSsumIoc d1 d2 R
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)) * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hbase0)
            (mul_nonneg hC1n (sq_nonneg C₀))
      _ = C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
            ((S:ℝ)^2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)) := by ring
  have hW1 : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter
        (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                    ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
      ≤ ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter
        (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                    ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
            ((S:ℝ)^2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)) := by
    refine Finset.sum_le_sum (fun d1 hd1 => Finset.sum_le_sum (fun d2 hd2 => ?_))
    exact hpair d1 d2 hd1 (Finset.mem_filter.mp hd2).1
  have hW2 : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter
        (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                    ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
            ((S:ℝ)^2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)))
      = C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
          ((S:ℝ)^2 * (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter
                (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                            ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
            + (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter
                (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                            ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                ((R:ℝ) + (S:ℝ)) * (R:ℝ))) := by
    have step1 : ∀ d1, (∑ d2 ∈ (Finset.Ioc D (2*D)).filter
          (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                      ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
              ((S:ℝ)^2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
                + ((R:ℝ) + (S:ℝ)) * (R:ℝ)))
        = C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
            ((S:ℝ)^2 * (∑ d2 ∈ (Finset.Ioc D (2*D)).filter
                  (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                              ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                  ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
              + (∑ d2 ∈ (Finset.Ioc D (2*D)).filter
                  (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                              ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                  ((R:ℝ) + (S:ℝ)) * (R:ℝ))) := by
      intro d1
      exact wdg_sum_const_mul_add _ _ _ _ _
    rw [Finset.sum_congr rfl (fun d1 _ => step1 d1)]
    exact wdg_sum_const_mul_add _ _ _ _ _

  have hSump : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
      ≤ 2 * C2 * ((2:ℝ)^((3:ℝ)/2) + 1) * (R:ℝ)^((3:ℝ)/2) * (4 * (D:ℝ) * (R:ℝ))^(ε/4) := by
    have step1 : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
        ≤ (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (wdg_CSsum d1 d2 (2*R) + wdg_CSsum d1 d2 R))) := by
      apply Finset.sum_le_sum; intro d1 _
      apply Finset.sum_le_sum; intro d2 _
      have h := wdg_CSsumIoc_le R d1 d2
      have hl : (0:ℝ) ≤ ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
      calc ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R
          ≤ ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (2 * (wdg_CSsum d1 d2 (2*R) + wdg_CSsum d1 d2 R)) :=
            mul_le_mul_of_nonneg_left h hl
        _ = 2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (wdg_CSsum d1 d2 (2*R) + wdg_CSsum d1 d2 R)) := by ring
    refine step1.trans ?_
    have hsplit : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (wdg_CSsum d1 d2 (2*R) + wdg_CSsum d1 d2 R)))
        = 2 * ((∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                  ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 (2*R))
              + (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                  ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R)) :=
      wdg_sum_two_mul_add _ _ (fun d1 d2 => ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹)
        (fun d1 d2 => wdg_CSsum d1 d2 (2*R)) (fun d1 d2 => wdg_CSsum d1 d2 R)
    rw [hsplit]
    have henl : ∀ R' : ℕ, (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R')
        ≤ ∑ d1 ∈ Finset.Icc 1 (2*D), ∑ d2 ∈ (Finset.Icc 1 (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R' := by
      intro R'
      have stepA : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R')
          ≤ ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Icc 1 (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R' := by
        apply Finset.sum_le_sum; intro d1 _
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d2 _ _ => ?_)
        · intro d2 hd2
          rw [Finset.mem_filter] at hd2 ⊢
          obtain ⟨hd2', hp⟩ := hd2
          have h1 := (Finset.mem_Ioc.mp hd2').1
          have h2 := (Finset.mem_Ioc.mp hd2').2
          exact ⟨by rw [Finset.mem_Icc]; omega, hp⟩
        · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Complex.normSq_nonneg _)
      have stepB : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Icc 1 (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R')
          ≤ ∑ d1 ∈ Finset.Icc 1 (2*D), ∑ d2 ∈ (Finset.Icc 1 (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R' := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d1 _ _ => ?_)
        · intro d1 hd1
          rw [Finset.mem_Icc]
          have h1 := (Finset.mem_Ioc.mp hd1).1
          have h2 := (Finset.mem_Ioc.mp hd1).2
          omega
        · exact Finset.sum_nonneg (fun d2 _ =>
            mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Complex.normSq_nonneg _))
      exact stepA.trans stepB
    have h11a := hC2 (2*D) (2*R) (by omega) (by omega)
    have h11b := hC2 (2*D) R (by omega) hR
    have hB1 : (∑ d1 ∈ Finset.Icc 1 (2*D), ∑ d2 ∈ (Finset.Icc 1 (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 (2*R))
        ≤ C2 * (2:ℝ)^((3:ℝ)/2) * (R:ℝ)^((3:ℝ)/2) * (4 * (D:ℝ) * (R:ℝ))^(ε/4) := by
      refine h11a.trans (le_of_eq ?_)
      rw [show (((2*D : ℕ) : ℝ) * ((2*R : ℕ) : ℝ)) = 4 * (D:ℝ) * (R:ℝ) by
            push_cast; ring]
      rw [show (((2*R : ℕ) : ℝ)) = 2 * (R:ℝ) by push_cast; ring]
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hR0.le]
      ring
    have hB2 : (∑ d1 ∈ Finset.Icc 1 (2*D), ∑ d2 ∈ (Finset.Icc 1 (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R)
        ≤ C2 * (R:ℝ)^((3:ℝ)/2) * (4 * (D:ℝ) * (R:ℝ))^(ε/4) := by
      refine h11b.trans ?_
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC2n (Real.rpow_nonneg hR0.le _))
      rw [show (((2*D : ℕ) : ℝ) * ((R : ℕ) : ℝ)) = 2 * (D:ℝ) * (R:ℝ) by push_cast; ring,
          show (2 * (D:ℝ) * (R:ℝ)) = 2 * ((D:ℝ)*(R:ℝ)) by ring,
          show (4 * (D:ℝ) * (R:ℝ)) = 4 * ((D:ℝ)*(R:ℝ)) by ring]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith [hD1, hR1]) hε4.le
    have h1 := (henl (2*R)).trans hB1
    have h2 := (henl R).trans hB2
    nlinarith [h1, h2, hC2n, hR0.le, Real.rpow_nonneg hR0.le ((3:ℝ)/2),
      Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 4 * (D:ℝ) * (R:ℝ)) (ε/4),
      Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) ((3:ℝ)/2)]
  have hSumY : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        ((R:ℝ) + (S:ℝ)) * (R:ℝ)) ≤ (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ) := by
    have h1 : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          ((R:ℝ) + (S:ℝ)) * (R:ℝ))
        ≤ ∑ d1 ∈ Finset.Ioc D (2*D), ∑ _d2 ∈ Finset.Ioc D (2*D), ((R:ℝ) + (S:ℝ)) * (R:ℝ) := by
      apply Finset.sum_le_sum; intro d1 _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d2 _ _ => by positivity)
    refine h1.trans (le_of_eq ?_)
    have hc : ((Finset.Ioc D (2*D)).card : ℝ) = (D:ℝ) := by
      rw [Nat.card_Ioc]
      have : 2*D - D = D := by omega
      rw [this]
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hc]
    ring
  have hWle : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
      ≤ C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
          ((S:ℝ)^2 * (2 * C2 * ((2:ℝ)^((3:ℝ)/2) + 1) * (R:ℝ)^((3:ℝ)/2)
              * (4 * (D:ℝ) * (R:ℝ))^(ε/4))
            + (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ)) := by
    refine hW1.trans ?_
    rw [hW2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine add_le_add ?_ hSumY
    exact mul_le_mul_of_nonneg_left hSump (by positivity)
  have hWfin : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
      ≤ C3 * ((S:ℝ)^2 * (R:ℝ)^((3:ℝ)/2)
          + (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ)) * ((D:ℝ)*(R:ℝ))^ε := by
    refine hWle.trans ?_
    rw [hC3def]
    convert wdg_combine_step C1 C₀ C2 ε hC1n hC₀n hC2n hε D R S hD hR using 2 <;> ring
  have hb0 : (0:ℝ) ≤ (S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) := by positivity
  have hW3 : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
      ≤ C3 * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2 * ((D:ℝ)*(R:ℝ))^ε) := by
    have h := wdg_sq_le_bracket_sq D R S hD hR
    have h2 : C3 * ((S:ℝ)^2 * (R:ℝ)^((3:ℝ)/2) + (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ))
        ≤ C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2 := mul_le_mul_of_nonneg_left h hC3n
    have hTnn : (0:ℝ) ≤ ((D:ℝ)*(R:ℝ))^ε := Real.rpow_nonneg (by positivity) _
    have h3 := mul_le_mul_of_nonneg_right h2 hTnn
    refine hWfin.trans ?_
    calc C3 * ((S:ℝ)^2 * (R:ℝ)^((3:ℝ)/2) + (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ))
            * ((D:ℝ)*(R:ℝ))^ε
        = (C3 * ((S:ℝ)^2 * (R:ℝ)^((3:ℝ)/2) + (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ)))
            * ((D:ℝ)*(R:ℝ))^ε := by ring
      _ ≤ (C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2) * ((D:ℝ)*(R:ℝ))^ε := h3
      _ = C3 * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2 * ((D:ℝ)*(R:ℝ))^ε) := by ring
  have hsqrtW : Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
      ≤ Real.sqrt C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^(ε/2) := by
    calc Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
        ≤ Real.sqrt (C3 * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2 * ((D:ℝ)*(R:ℝ))^ε)) := Real.sqrt_le_sqrt hW3
      _ = Real.sqrt C3 * (Real.sqrt (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2) * Real.sqrt (((D:ℝ)*(R:ℝ))^ε)) := by
          rw [Real.sqrt_mul hC3n, Real.sqrt_mul (sq_nonneg _)]
      _ = Real.sqrt C3 * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * Real.sqrt (((D:ℝ)*(R:ℝ))^ε)) := by
          rw [Real.sqrt_sq hb0]
      _ = Real.sqrt C3 * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^(ε/2)) := by
          have hs : Real.sqrt (((D:ℝ)*(R:ℝ))^ε) = ((D:ℝ)*(R:ℝ))^(ε/2) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (D:ℝ)*(R:ℝ)),
                show ε * (1/2) = ε/2 by ring]
          rw [hs]
      _ = Real.sqrt C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^(ε/2) := by ring
  have hT : ((D:ℝ)*(R:ℝ))^(ε/2) ≤ ((D:ℝ)*(R:ℝ))^ε :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [hD1, hR1]) (by linarith)
  calc ‖∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
            KK (F) R d1 d2 a‖
      ≤ Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D),
              ∑ a ∈ Finset.range (Nat.lcm d1 d2),
                Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
          * Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2) := hCS
    _ ≤ (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) * Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2) :=
        mul_le_mul_of_nonneg_right hsqrtE (Real.sqrt_nonneg _)
    _ ≤ (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) * (Real.sqrt C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^(ε/2)) :=
        mul_le_mul_of_nonneg_left hsqrtW hN0
    _ ≤ (Real.sqrt C3 + 1) * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^ε) * (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
        have hTnn : (0:ℝ) ≤ ((D:ℝ)*(R:ℝ))^ε := Real.rpow_nonneg (by positivity) _
        have h1 : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) * (Real.sqrt C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^(ε/2))
            ≤ (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) * (Real.sqrt C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^ε) := by
          apply mul_le_mul_of_nonneg_left _ hN0
          exact mul_le_mul_of_nonneg_left hT (mul_nonneg (Real.sqrt_nonneg C3) hb0)
        have h2 : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) * (Real.sqrt C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^ε)
            ≤ (Real.sqrt C3 + 1) * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^ε) * (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
          nlinarith [hTnn, hN0, hb0, Real.sqrt_nonneg C3,
            mul_nonneg hN0 (mul_nonneg hb0 hTnn), mul_nonneg (mul_nonneg hb0 hTnn) hN0]
        exact h1.trans h2

end

end Work.FIArea4.Vflip

namespace Work.FIArea4

theorem Wdyad_diff_part_le_unif (ε : ℝ) (hε : 0 < ε) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ℕ) (hS : 1 ≤ S) (F : ℝ → ℂ)
      (hdec : ∀ ξ : ℝ, ‖F ξ‖ ≤ C₀ * (S : ℝ) * (1 + (S : ℝ) * |ξ|) ^ (-(2 : ℝ)))
      (D R : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R →
      ‖∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ (Finset.Ioc D (2 * D)).filter
          (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                      ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
            Work.FIArea4.KK F R d1 d2 a‖
      ≤ C * (((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * R
              + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε))
          * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) :=
  Work.FIArea4.Vflip.Wdyad_diff_part_le_gen_unif ε hε C₀ hC₀

end Work.FIArea4
