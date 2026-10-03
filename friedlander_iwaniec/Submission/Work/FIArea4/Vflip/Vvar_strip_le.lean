import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.PairSumCommon
import Submission.Work.FIArea4.pair_sum_le_Evar
import Submission.Work.FIArea4.Evar_le_trivial
import Submission.Work.FIArea4.Vflip.VflipAux
import Submission.Work.FIArea4.sum_Ioc_Evar_le_braceV_support_r_one
import Submission.Work.FIArea4.sum_Ioc_Evar_le_braceV_support_s_one

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

lemma p14L2_nonneg_aux (R S : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ Work.FIArea4.p14L2 R S α := by
  rw [Work.FIArea4.p14L2]
  exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))

lemma normSq_add_le_two_mul (z w : ℂ) :
    Complex.normSq (z + w) ≤ 2 * (Complex.normSq z + Complex.normSq w) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [norm_add_le z w, norm_nonneg z, norm_nonneg w, sq_nonneg (‖z‖ - ‖w‖),
    norm_nonneg (z + w)]

lemma sum_Ioc_div_add_one_le (D : ℕ) (hD : 1 ≤ D) (c : ℝ) (hc : 0 ≤ c) :
    ∑ d ∈ Finset.Ioc D (2 * D), (c / (d : ℝ) + 1) ≤ (D : ℝ) + c := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hterm : ∀ d ∈ Finset.Ioc D (2 * D), c / (d : ℝ) + 1 ≤ c / (D : ℝ) + 1 := by
    intro d hdmem
    have hDd : (D : ℝ) ≤ (d : ℝ) := by
      have h' := (Finset.mem_Ioc.mp hdmem).1
      exact_mod_cast le_of_lt h'
    have := div_le_div_of_nonneg_left hc hDpos hDd
    linarith
  calc ∑ d ∈ Finset.Ioc D (2 * D), (c / (d : ℝ) + 1)
      ≤ ∑ d ∈ Finset.Ioc D (2 * D), (c / (D : ℝ) + 1) := Finset.sum_le_sum hterm
    _ = ((Finset.Ioc D (2 * D)).card : ℝ) * (c / (D : ℝ) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (D : ℝ) * (c / (D : ℝ) + 1) := by
          rw [Nat.card_Ioc, show 2 * D - D = D by omega]
    _ = (D : ℝ) + c := by
          field_simp
          ring

/-- **Subadditivity of the local variance** under an additive decomposition `β = β₁ + β₂`. -/
lemma Evar_add_le_two (R S d : ℕ) (β β₁ β₂ : ℕ → ℕ → ℂ)
    (h : ∀ r s, β r s = β₁ r s + β₂ r s) :
    Work.FIPlan.Evar R S d β
      ≤ 2 * Work.FIPlan.Evar R S d β₁ + 2 * Work.FIPlan.Evar R S d β₂ := by
  have hcls : ∀ a, Work.FIArea4.clsSum R S d β a
      = Work.FIArea4.clsSum R S d β₁ a + Work.FIArea4.clsSum R S d β₂ a := by
    intro a
    rw [Work.FIArea4.clsSum, Work.FIArea4.clsSum, Work.FIArea4.clsSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [h p.1 p.2]
    ring
  rw [Work.FIArea4.Evar_eq_sum_normSq_clsSum R S d β,
      Work.FIArea4.Evar_eq_sum_normSq_clsSum R S d β₁,
      Work.FIArea4.Evar_eq_sum_normSq_clsSum R S d β₂]
  calc ∑ a ∈ Finset.range d, Complex.normSq (Work.FIArea4.clsSum R S d β a)
      = ∑ a ∈ Finset.range d, Complex.normSq (Work.FIArea4.clsSum R S d β₁ a
          + Work.FIArea4.clsSum R S d β₂ a) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [hcls a]
    _ ≤ ∑ a ∈ Finset.range d, (2 * Complex.normSq (Work.FIArea4.clsSum R S d β₁ a)
          + 2 * Complex.normSq (Work.FIArea4.clsSum R S d β₂ a)) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        have := normSq_add_le_two_mul (Work.FIArea4.clsSum R S d β₁ a)
          (Work.FIArea4.clsSum R S d β₂ a)
        linarith
    _ = (∑ a ∈ Finset.range d, 2 * Complex.normSq (Work.FIArea4.clsSum R S d β₁ a))
          + ∑ a ∈ Finset.range d, 2 * Complex.normSq (Work.FIArea4.clsSum R S d β₂ a) := by
        rw [Finset.sum_add_distrib]
    _ = 2 * (∑ a ∈ Finset.range d, Complex.normSq (Work.FIArea4.clsSum R S d β₁ a))
          + 2 * ∑ a ∈ Finset.range d, Complex.normSq (Work.FIArea4.clsSum R S d β₂ a) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- **Subadditivity of the global variance** under an additive decomposition `β = β₁ + β₂`. -/
lemma Vvar_add_le_two (R S D : ℕ) (β β₁ β₂ : ℕ → ℕ → ℂ)
    (h : ∀ r s, β r s = β₁ r s + β₂ r s) :
    Work.FIPlan.Vvar R S D β
      ≤ 2 * Work.FIPlan.Vvar R S D β₁ + 2 * Work.FIPlan.Vvar R S D β₂ := by
  rw [Work.FIPlan.Vvar, Work.FIPlan.Vvar, Work.FIPlan.Vvar]
  calc ∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d β
      ≤ ∑ d ∈ Finset.Ioc D (2 * D),
          (2 * Work.FIPlan.Evar R S d β₁ + 2 * Work.FIPlan.Evar R S d β₂) :=
        Finset.sum_le_sum (fun d _ => Evar_add_le_two R S d β β₁ β₂ h)
    _ = (∑ d ∈ Finset.Ioc D (2 * D), 2 * Work.FIPlan.Evar R S d β₁)
          + ∑ d ∈ Finset.Ioc D (2 * D), 2 * Work.FIPlan.Evar R S d β₂ := by
        rw [Finset.sum_add_distrib]
    _ = 2 * (∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d β₁)
          + 2 * ∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d β₂ := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]

theorem Vvar_strip_le (D R S : ℕ) (β : ℕ → ℕ → ℂ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hsupp : ∀ r s, β r s ≠ 0 → r = 1 ∨ s = 1) :
    Work.FIPlan.Vvar R S D β
      ≤ (16 * ((R : ℝ) + (S : ℝ) + (D : ℝ))) * Work.FIArea4.p14L2 R S β := by
  have hL2nn : 0 ≤ Work.FIArea4.p14L2 R S β := p14L2_nonneg_aux R S β
  -- split `β` into its `r = 1` part and its `s = 1` part
  set βR : ℕ → ℕ → ℂ := fun r s => if r = 1 then β r s else 0 with hβR
  set βS : ℕ → ℕ → ℂ := fun r s => if s = 1 ∧ r ≠ 1 then β r s else 0 with hβS
  have hsuppR : ∀ r s, βR r s ≠ 0 → r = 1 := by
    intro r s hrs
    simp only [hβR] at hrs
    by_cases hr : r = 1
    · exact hr
    · rw [if_neg hr] at hrs
      exact absurd rfl hrs
  have hsuppS : ∀ r s, βS r s ≠ 0 → s = 1 := by
    intro r s hrs
    simp only [hβS] at hrs
    by_cases h : s = 1 ∧ r ≠ 1
    · exact h.1
    · rw [if_neg h] at hrs
      exact absurd rfl hrs
  have hpoint : ∀ r s, β r s = βR r s + βS r s := by
    intro r s
    simp only [hβR, hβS]
    by_cases hr : r = 1
    · simp [hr]
    · by_cases hs : s = 1
      · simp [hr, hs]
      · have hz : β r s = 0 := by
          by_contra hne
          rcases hsupp r s hne with h | h
          · exact hr h
          · exact hs h
        simp [hr, hs, hz]
  -- the `r = 1` half
  have hboundR : Work.FIPlan.Vvar R S D βR ≤ ((D : ℝ) + 2 * (S : ℝ)) * Work.FIArea4.p14L2 R S β := by
    rw [Work.FIPlan.Vvar]
    have heq : (∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (βR 1 s))
        = ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (β 1 s) := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp [hβR]
    have hsingle : ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (β 1 s)
        ≤ Work.FIArea4.p14L2 R S β := by
      rw [Work.FIArea4.p14L2]
      refine Finset.single_le_sum
        (f := fun r => ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (β r s))
        (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _)) ?_
      rw [Finset.mem_Icc]
      omega
    have hper : ∀ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d βR
        ≤ (2 * (S : ℝ) / (d : ℝ) + 1) * Work.FIArea4.p14L2 R S β := by
      intro d hdmem
      have hdpos : 0 < d := by
        have h' := (Finset.mem_Ioc.mp hdmem).1
        omega
      calc Work.FIPlan.Evar R S d βR
          ≤ (2 * (S : ℝ) / (d : ℝ) + 1)
              * ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (βR 1 s) :=
            Work.FIArea4.Evar_le_reduced_r_one R S d βR hR hdpos hsuppR
        _ = (2 * (S : ℝ) / (d : ℝ) + 1)
              * ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (β 1 s) := by rw [heq]
        _ ≤ (2 * (S : ℝ) / (d : ℝ) + 1) * Work.FIArea4.p14L2 R S β :=
            mul_le_mul_of_nonneg_left hsingle (by positivity)
    calc ∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d βR
        ≤ ∑ d ∈ Finset.Ioc D (2 * D),
            (2 * (S : ℝ) / (d : ℝ) + 1) * Work.FIArea4.p14L2 R S β :=
          Finset.sum_le_sum hper
      _ = (∑ d ∈ Finset.Ioc D (2 * D), (2 * (S : ℝ) / (d : ℝ) + 1))
            * Work.FIArea4.p14L2 R S β := by rw [Finset.sum_mul]
      _ ≤ ((D : ℝ) + 2 * (S : ℝ)) * Work.FIArea4.p14L2 R S β :=
          mul_le_mul_of_nonneg_right
            (sum_Ioc_div_add_one_le D hD (2 * (S : ℝ)) (by positivity)) hL2nn
  -- the `s = 1` half
  have hboundS : Work.FIPlan.Vvar R S D βS ≤ ((D : ℝ) + 2 * (R : ℝ)) * Work.FIArea4.p14L2 R S β := by
    rw [Work.FIPlan.Vvar]
    have hL2S : Work.FIArea4.p14L2 R S βS ≤ Work.FIArea4.p14L2 R S β := by
      rw [Work.FIArea4.p14L2, Work.FIArea4.p14L2]
      refine Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun s _ => ?_))
      by_cases h : s = 1 ∧ r ≠ 1
      · have : βS r s = β r s := by rw [hβS]; simp [h]
        rw [this]
      · have : βS r s = 0 := by rw [hβS]; simp [h]
        rw [this, Complex.normSq_zero]
        exact Complex.normSq_nonneg _
    have hper : ∀ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d βS
        ≤ (2 * (R : ℝ) / (d : ℝ) + 1) * Work.FIArea4.p14L2 R S β := by
      intro d hdmem
      have hdpos : 0 < d := by
        have h' := (Finset.mem_Ioc.mp hdmem).1
        omega
      refine le_trans (Work.FIArea4.Evar_le_of_support_s_one R S d βS hS hdpos hsuppS) ?_
      exact mul_le_mul_of_nonneg_left hL2S (by positivity)
    calc ∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d βS
        ≤ ∑ d ∈ Finset.Ioc D (2 * D),
            (2 * (R : ℝ) / (d : ℝ) + 1) * Work.FIArea4.p14L2 R S β :=
          Finset.sum_le_sum hper
      _ = (∑ d ∈ Finset.Ioc D (2 * D), (2 * (R : ℝ) / (d : ℝ) + 1))
            * Work.FIArea4.p14L2 R S β := by rw [Finset.sum_mul]
      _ ≤ ((D : ℝ) + 2 * (R : ℝ)) * Work.FIArea4.p14L2 R S β :=
          mul_le_mul_of_nonneg_right
            (sum_Ioc_div_add_one_le D hD (2 * (R : ℝ)) (by positivity)) hL2nn
  have hcs : Work.FIPlan.Vvar R S D β
      ≤ 2 * Work.FIPlan.Vvar R S D βR + 2 * Work.FIPlan.Vvar R S D βS :=
    Vvar_add_le_two R S D β βR βS hpoint
  calc Work.FIPlan.Vvar R S D β
      ≤ 2 * Work.FIPlan.Vvar R S D βR + 2 * Work.FIPlan.Vvar R S D βS := hcs
    _ ≤ 2 * (((D : ℝ) + 2 * (S : ℝ)) * Work.FIArea4.p14L2 R S β)
          + 2 * (((D : ℝ) + 2 * (R : ℝ)) * Work.FIArea4.p14L2 R S β) := by
        have h1 := mul_le_mul_of_nonneg_left hboundR (by norm_num : (0 : ℝ) ≤ 2)
        have h2 := mul_le_mul_of_nonneg_left hboundS (by norm_num : (0 : ℝ) ≤ 2)
        linarith
    _ = (4 * ((R : ℝ) + (S : ℝ) + (D : ℝ))) * Work.FIArea4.p14L2 R S β := by ring
    _ ≤ (16 * ((R : ℝ) + (S : ℝ) + (D : ℝ))) * Work.FIArea4.p14L2 R S β := by
        refine mul_le_mul_of_nonneg_right ?_ hL2nn
        have : (0 : ℝ) ≤ (R : ℝ) + (S : ℝ) + (D : ℝ) := by positivity
        linarith

end

end Work.FIArea4.Vflip
