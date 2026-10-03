import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.farPre
import Submission.Work.FIArea4.Vflip.Vfd.farGadgets
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs
import Submission.Work.FIArea4.Vflip.Vfd.dyadic_far_sum
import Submission.Work.FIArea4.Vflip.Vfd.farInner_eq_zero_of_range
import Submission.Work.FIArea4.Vflip.Vfd.farInner_eq_zero_of_large_cD
import Submission.Work.FIArea4.Vflip.Vfd.mcLog_bound
import Submission.Work.FIArea4.Vflip.Vfd.p14T11_le_mcInner
import Submission.Work.FIArea4.Vflip.Vfd.McDefs
import Submission.Work.FIArea4.A4varbounds

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem farInner_mc_bound
    (Cd ε : ℝ) (hCd : 0 < Cd) (hε : 0 < ε)
    (hdy : ∀ (D R S m c Q : ℕ) (a b H : ℝ) (α : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → 1 ≤ m → 1 ≤ c → m ∣ c →
      D ≤ R * S → R * S < D * D →
      H = ((R:ℝ)*(S:ℝ)/(D:ℝ))^((1:ℝ)/3) →
      a = 2*(S:ℝ)/(H*(R:ℝ)) → b = 2*(S:ℝ)/(R:ℝ) →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
      ((1 ≤ Q → ‖Work.FIArea4.Vflip.Vfd.farInner D R S a b α m c Q (2 * Q)‖
            ≤ Cd * (Real.log (2 + b / a) + 1) ^ 2 * (Real.log (2 * (Work.FIArea4.Vflip.Vfd.cR c R : ℝ)) + 1)
                * Work.FIArea4.p14T11 (m * Q) (Work.FIArea4.Vflip.Vfd.cR c R) S (ε / 4)
                * Work.FIArea4.p14L2 (Work.FIArea4.Vflip.Vfd.cR c R) S (Work.FIArea4.Vflip.Vfd.redA c α))
        ∧ (‖Work.FIArea4.Vflip.Vfd.farInner D R S a b α m c 0 1‖
            ≤ Cd * (Real.log (2 + b / a) + 1) ^ 2 * (Real.log (2 * (Work.FIArea4.Vflip.Vfd.cR c R : ℝ)) + 1)
                * Work.FIArea4.p14T11 m (Work.FIArea4.Vflip.Vfd.cR c R) S (ε / 4)
                * Work.FIArea4.p14L2 (Work.FIArea4.Vflip.Vfd.cR c R) S (Work.FIArea4.Vflip.Vfd.redA c α)))) :
    ∀ (D R S m c : ℕ) (a b H : ℝ) (α : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → 1 ≤ m → 1 ≤ c → m ∣ c →
      D ≤ R * S → R * S < D * D →
      H = ((R:ℝ)*(S:ℝ)/(D:ℝ))^((1:ℝ)/3) →
      a = 2*(S:ℝ)/(H*(R:ℝ)) → b = 2*(S:ℝ)/(R:ℝ) →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
      (∑ j ∈ Finset.range (4*R*S),
          ‖Work.FIArea4.Vflip.Vfd.farInner D R S a b α m c (2^j) (2^(j+1))‖)
        + ‖Work.FIArea4.Vflip.Vfd.farInner D R S a b α m c 0 1‖
      ≤ (100 * Cd)
          * ((Real.log (2*H)+1)^2 * (Real.log (2*(Work.FIArea4.Vflip.Vfd.cR c R : ℝ))+1)
              * ( (m * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))))^(-(1:ℝ)/2) * ((Work.FIArea4.Vflip.Vfd.cR c R:ℝ)*(S:ℝ))
                  + ((R:ℝ)*(S:ℝ))^(ε/4)
                    * ( m * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
                          * Real.sqrt ((Work.FIArea4.Vflip.Vfd.cR c R:ℝ)*(S:ℝ))
                        + (Real.log (160*H)+1)
                          * ( (Work.FIArea4.Vflip.Vfd.cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4))
                              + (S:ℝ)*((Work.FIArea4.Vflip.Vfd.cR c R:ℝ)^((3:ℝ)/4)) ) ) ))
          * Work.FIArea4.p14L2 (Work.FIArea4.Vflip.Vfd.cR c R) S (Work.FIArea4.Vflip.Vfd.redA c α) := by
  intro D R S m c a b H α h1D h1R h1S h1m h1c hmc hDRS hRSDD hH ha hb hcop hbox
  -- ===== basic positivity and parameter facts =====
  have hD0 : 0 < D := by omega
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD0
  have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast (show 0 < R by omega)
  have hSpos : (0:ℝ) < (S:ℝ) := by exact_mod_cast (show 0 < S by omega)
  have hcpos : (0:ℝ) < (c:ℝ) := by exact_mod_cast (show 0 < c by omega)
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hHpos : 0 < H := far_H_pos h1R h1S h1D hH
  have hbase : (1:ℝ) ≤ (R:ℝ)*(S:ℝ)/(D:ℝ) := by
    rw [le_div_iff₀ hDpos, one_mul]
    exact_mod_cast hDRS
  have hHge : 1 ≤ H := by rw [hH]; exact Real.one_le_rpow hbase (by norm_num)
  have hapos : 0 < a := far_a_pos h1R h1S hHpos ha
  have hbpos : 0 < b := far_b_pos h1R h1S hb
  have hba : b / a = H := far_b_div_a h1R h1S h1D hH ha hb
  have hab : a ≤ b := far_a_le_b h1R h1S h1D hDRS hH ha hb
  have haH : a * H * (R:ℝ) = 2*(S:ℝ) := by rw [ha]; field_simp
  have hRSnn : (0:ℝ) ≤ (R:ℝ)*(S:ℝ) := by positivity
  have hSRnn : (0:ℝ) ≤ (S:ℝ)*(R:ℝ) := by positivity
  -- ===== abbreviations =====
  set CL : ℝ := Cd * (Real.log (2 + H) + 1)^2 * (Real.log (2*(cR c R : ℝ)) + 1)
      * Work.FIArea4.p14L2 (cR c R) S (redA c α) with hCL
  set Sf : Finset ℕ := (Finset.range (4*R*S)).filter
      (fun j => (2:ℝ)^j * 2 > (S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))
        ∧ (2:ℝ)^j < 16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) with hSf
  -- ===== auxiliary numeric facts =====
  have hRle_nat : cR c R ≤ R := by
    rw [cR, Nat.div_le_iff_le_mul_add_pred (by omega : 0 < c)]
    have h : R ≤ c * R := Nat.le_mul_of_pos_left R (by omega : 0 < c)
    omega
  have hRle : (cR c R : ℝ) ≤ (R:ℝ) := by exact_mod_cast hRle_nat
  have hL2nn : (0:ℝ) ≤ Work.FIArea4.p14L2 (cR c R) S (redA c α) := by
    rw [Work.FIArea4.p14L2]
    refine Finset.sum_nonneg (fun r hr => Finset.sum_nonneg (fun s hs => ?_))
    exact Complex.normSq_nonneg _
  have hPnn : (0:ℝ) ≤ Real.log (2*(cR c R : ℝ)) + 1 := by
    have h1 : (1:ℝ) ≤ 2*(cR c R : ℝ) := by
      have : (1:ℝ) ≤ (cR c R : ℝ) := by exact_mod_cast cR_pos h1c h1R
      linarith
    have := Real.log_nonneg h1
    linarith
  have hCLnn : (0:ℝ) ≤ CL := by
    rw [hCL]
    have hA : (0:ℝ) ≤ (Real.log (2 + H) + 1)^2 := sq_nonneg _
    have hCdnn : (0:ℝ) ≤ Cd := hCd.le
    positivity
  have hMnn : (0:ℝ) ≤ mcInner D R S m c H ε := by
    rw [mcInner]
    refine add_nonneg ?_ ?_
    · refine mul_nonneg ?_ (by positivity)
      exact Real.rpow_nonneg (by positivity) _
    · refine mul_nonneg ?_ ?_
      · exact Real.rpow_nonneg (by positivity) _
      · refine add_nonneg ?_ ?_
        · refine mul_nonneg (by positivity) ?_
          exact Real.sqrt_nonneg _
        · refine mul_nonneg ?_ (by positivity)
          have : (0:ℝ) ≤ Real.log (160*H) := Real.log_nonneg (by linarith)
          linarith
  -- ===== (1) per-dyadic bound from `hdy` =====
  have hper : ∀ j : ℕ, ‖farInner D R S a b α m c (2^j) (2^(j+1))‖
      ≤ CL * Work.FIArea4.p14T11 (m * 2^j) (cR c R) S (ε/4) := by
    intro j
    have h1 : 1 ≤ (2:ℕ)^j := Nat.one_le_pow j 2 (by norm_num)
    have hb1 := (hdy D R S m c (2^j) a b H α h1D h1R h1S h1m h1c hmc hDRS hRSDD hH ha hb hcop hbox).1 h1
    rw [hba] at hb1
    have h2 : (2:ℕ)^(j+1) = 2 * 2^j := by rw [pow_succ]; ring
    rw [h2]
    calc ‖farInner D R S a b α m c (2^j) (2 * 2^j)‖
        ≤ Cd * (Real.log (2 + H) + 1) ^ 2 * (Real.log (2 * (cR c R : ℝ)) + 1)
            * Work.FIArea4.p14T11 (m * 2^j) (cR c R) S (ε / 4)
            * Work.FIArea4.p14L2 (cR c R) S (redA c α) := hb1
      _ = CL * Work.FIArea4.p14T11 (m * 2^j) (cR c R) S (ε/4) := by rw [hCL]; ring
  -- ===== (2) vanishing of the pieces outside the window =====
  have hvan : ∀ j ∈ Finset.range (4*R*S), j ∉ Sf →
      farInner D R S a b α m c (2^j) (2^(j+1)) = 0 := by
    intro j hj hjn
    have hfez := farInner_eq_zero_of_range (D := D) (R := R) (S := S) (m := m) (c := c)
        (Q1 := 2^j) (Q2 := 2^(j+1)) (a := a) (b := b) (H := H) (α := α)
        hD0 hHpos hapos haH
    obtain ⟨h1, h2⟩ := hfez
    have hnot : ¬ ((2:ℝ)^j * 2 > (S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))
        ∧ (2:ℝ)^j < 16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) := by
      intro hcon
      exact hjn (by rw [hSf, Finset.mem_filter]; exact ⟨hj, hcon⟩)
    have hcases : (2:ℝ)^j * 2 ≤ (S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))
        ∨ 16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)) ≤ (2:ℝ)^j := by
      by_cases hA : (2:ℝ)^j * 2 > (S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))
      · exact Or.inr (not_lt.mp (fun hB => hnot ⟨hA, hB⟩))
      · exact Or.inl (not_lt.mp hA)
    rcases hcases with hle | hge
    · apply h1
      push_cast
      rw [pow_succ]
      have h5 : (0:ℝ) < 5*H*(c:ℝ)*(D:ℝ) := by positivity
      have hstep : ((2:ℝ)^j * 2) * (5*H*(c:ℝ)*(D:ℝ)) ≤ (S:ℝ)*(R:ℝ) := by
        calc ((2:ℝ)^j * 2) * (5*H*(c:ℝ)*(D:ℝ))
            ≤ ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))) * (5*H*(c:ℝ)*(D:ℝ)) :=
              mul_le_mul_of_nonneg_right hle h5.le
          _ = (S:ℝ)*(R:ℝ) := div_mul_cancel₀ _ (ne_of_gt h5)
      linarith only [hstep, hSRnn]
    · apply h2
      push_cast
      have h6 : (0:ℝ) < (c:ℝ)*(D:ℝ) := by positivity
      have hstep : 16*(R:ℝ)*(S:ℝ) ≤ (2:ℝ)^j * ((c:ℝ)*(D:ℝ)) := by
        calc 16*(R:ℝ)*(S:ℝ)
            = (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) * ((c:ℝ)*(D:ℝ)) :=
              (div_mul_cancel₀ _ (ne_of_gt h6)).symm
          _ ≤ (2:ℝ)^j * ((c:ℝ)*(D:ℝ)) := mul_le_mul_of_nonneg_right hge h6.le
      linarith only [hstep, hRSnn]
  -- ===== (3) reduce the sum to the window =====
  have hsum_eq : (∑ j ∈ Finset.range (4*R*S), ‖farInner D R S a b α m c (2^j) (2^(j+1))‖)
      = ∑ j ∈ Sf, ‖farInner D R S a b α m c (2^j) (2^(j+1))‖ := by
    have hsub : Sf ⊆ Finset.range (4*R*S) := by rw [hSf]; exact Finset.filter_subset _ _
    refine (Finset.sum_subset hsub (fun j hj hjn => ?_)).symm
    rw [hvan j hj hjn]; simp
  have hsum_le : ∑ j ∈ Sf, ‖farInner D R S a b α m c (2^j) (2^(j+1))‖
      ≤ CL * ∑ j ∈ Sf, Work.FIArea4.p14T11 (m * 2^j) (cR c R) S (ε/4) := by
    calc ∑ j ∈ Sf, ‖farInner D R S a b α m c (2^j) (2^(j+1))‖
        ≤ ∑ j ∈ Sf, CL * Work.FIArea4.p14T11 (m * 2^j) (cR c R) S (ε/4) :=
          Finset.sum_le_sum (fun j _ => hper j)
      _ = CL * ∑ j ∈ Sf, Work.FIArea4.p14T11 (m * 2^j) (cR c R) S (ε/4) := by
          rw [Finset.mul_sum]
  -- ===== (4) unfold p14T11 into the dyadic sum pieces =====
  have hT11_eq : ∑ j ∈ Sf, Work.FIArea4.p14T11 (m * 2^j) (cR c R) S (ε/4)
      = ∑ j ∈ Sf, (((m:ℝ)*(2:ℝ)^j)^(-(1:ℝ)/2) * ((cR c R:ℝ)*(S:ℝ))
          + (m:ℝ)*(2:ℝ)^j * (Real.sqrt ((cR c R:ℝ)*(S:ℝ)) * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))
          + (((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))
              * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Work.FIArea4.p14T11]
    push_cast
    ring
  -- ===== (5) the dyadic sum estimate =====
  have hQminpos : (0:ℝ) < (S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ)) := by positivity
  have hQmaxpos : (0:ℝ) < 16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)) := by positivity
  have hratio_eq : (80*H) * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ)))
      = 16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)) := by
    field_simp
    ring
  have hC01 : (1:ℝ) ≤ 80*H := by linarith
  have hdf := dyadic_far_sum (m := (m:ℝ))
    (Qmin := (S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ)))
    (Qmax := 16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
    (A := (cR c R:ℝ)*(S:ℝ))
    (B := Real.sqrt ((cR c R:ℝ)*(S:ℝ)) * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))
    (Cc := ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))
      * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))
    (C0 := 80*H) (J := 4*R*S)
    hmpos hQminpos hQmaxpos (by positivity) (by positivity) (by positivity) hC01 (le_of_eq hratio_eq.symm)
  rw [show (2:ℝ)*(80*H) = 160*H by ring] at hdf
  -- ===== (6) the bracket is dominated by `mcInner` =====
  have hcore : ((m:ℝ) * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))))^(-(1:ℝ)/2) * ((cR c R:ℝ)*(S:ℝ))
      + (m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
          * (Real.sqrt ((cR c R:ℝ)*(S:ℝ)) * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))
      + (Real.log (160*H)+1)
          * (((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))
              * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))
      ≤ mcInner D R S m c H ε := by
    have hAeps : (((cR c R:ℝ)*(S:ℝ))^(ε/4)) ≤ (((R:ℝ)*(S:ℝ))^(ε/4)) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      nlinarith only [hRle, hSpos]
    have hlg : (0:ℝ) ≤ Real.log (160*H)+1 := by
      have : (0:ℝ) ≤ Real.log (160*H) := Real.log_nonneg (by linarith)
      linarith
    have hcb : (0:ℝ) ≤ (cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)) :=
      add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    have h1 : (m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
          * (Real.sqrt ((cR c R:ℝ)*(S:ℝ)) * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))
        ≤ (((R:ℝ)*(S:ℝ))^(ε/4))
          * ((m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
              * Real.sqrt ((cR c R:ℝ)*(S:ℝ))) := by
      have h0 : (0:ℝ) ≤ (m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
          * Real.sqrt ((cR c R:ℝ)*(S:ℝ)) :=
        mul_nonneg (by positivity) (Real.sqrt_nonneg _)
      calc (m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
            * (Real.sqrt ((cR c R:ℝ)*(S:ℝ)) * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))
          = ((m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
              * Real.sqrt ((cR c R:ℝ)*(S:ℝ))) * (((cR c R:ℝ)*(S:ℝ))^(ε/4)) := by ring
        _ ≤ ((m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
              * Real.sqrt ((cR c R:ℝ)*(S:ℝ))) * (((R:ℝ)*(S:ℝ))^(ε/4)) :=
              mul_le_mul_of_nonneg_left hAeps h0
        _ = (((R:ℝ)*(S:ℝ))^(ε/4))
              * ((m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
                  * Real.sqrt ((cR c R:ℝ)*(S:ℝ))) := by ring
    have h2 : (Real.log (160*H)+1)
          * (((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))
              * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))
        ≤ (((R:ℝ)*(S:ℝ))^(ε/4))
          * ((Real.log (160*H)+1)
              * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))) := by
      have h0 : (0:ℝ) ≤ (Real.log (160*H)+1)
          * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4))) :=
        mul_nonneg hlg hcb
      calc (Real.log (160*H)+1)
            * (((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))
                * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))
          = ((Real.log (160*H)+1)
              * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4))))
              * (((cR c R:ℝ)*(S:ℝ))^(ε/4)) := by ring
        _ ≤ ((Real.log (160*H)+1)
              * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4))))
              * (((R:ℝ)*(S:ℝ))^(ε/4)) := mul_le_mul_of_nonneg_left hAeps h0
        _ = (((R:ℝ)*(S:ℝ))^(ε/4))
              * ((Real.log (160*H)+1)
                  * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))) := by ring
    unfold mcInner
    calc ((m:ℝ) * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))))^(-(1:ℝ)/2) * ((cR c R:ℝ)*(S:ℝ))
          + (m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
              * (Real.sqrt ((cR c R:ℝ)*(S:ℝ)) * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))
          + (Real.log (160*H)+1)
              * (((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))
                  * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))
        = ((m:ℝ) * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))))^(-(1:ℝ)/2) * ((cR c R:ℝ)*(S:ℝ))
          + ((m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
              * (Real.sqrt ((cR c R:ℝ)*(S:ℝ)) * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))
            + (Real.log (160*H)+1)
              * (((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))
                  * (((cR c R:ℝ)*(S:ℝ))^(ε/4)))) := by ring
      _ ≤ ((m:ℝ) * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))))^(-(1:ℝ)/2) * ((cR c R:ℝ)*(S:ℝ))
          + ((((R:ℝ)*(S:ℝ))^(ε/4))
              * ((m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
                  * Real.sqrt ((cR c R:ℝ)*(S:ℝ)))
            + (((R:ℝ)*(S:ℝ))^(ε/4))
              * ((Real.log (160*H)+1)
                  * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4))))) :=
          add_le_add le_rfl (add_le_add h1 h2)
      _ = ((m:ℝ) * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))))^(-(1:ℝ)/2) * ((cR c R:ℝ)*(S:ℝ))
          + (((R:ℝ)*(S:ℝ))^(ε/4))
              * ((m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)))
                  * Real.sqrt ((cR c R:ℝ)*(S:ℝ))
                + (Real.log (160*H)+1)
                  * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))) := by ring
  have hT11 : ∑ j ∈ Sf, Work.FIArea4.p14T11 (m * 2^j) (cR c R) S (ε/4)
      ≤ 10 * mcInner D R S m c H ε := by
    rw [hT11_eq, hSf]
    exact le_trans hdf (mul_le_mul_of_nonneg_left hcore (by norm_num))
  -- ===== (7) assembly: the dyadic sum =====
  have hA1 : (∑ j ∈ Finset.range (4*R*S), ‖farInner D R S a b α m c (2^j) (2^(j+1))‖)
      ≤ CL * (10 * mcInner D R S m c H ε) := by
    rw [hsum_eq]
    exact le_trans hsum_le (mul_le_mul_of_nonneg_left hT11 hCLnn)
  -- ===== (8) assembly: the q'=1 piece =====
  have hA2 : ‖farInner D R S a b α m c 0 1‖ ≤ CL * mcInner D R S m c H ε := by
    have hb2 := (hdy D R S m c 0 a b H α h1D h1R h1S h1m h1c hmc hDRS hRSDD hH ha hb hcop hbox).2
    rw [hba] at hb2
    by_cases hcase : (S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ)) < 1/2
      ∧ (c:ℝ)*(D:ℝ) ≤ 8*(R:ℝ)*(S:ℝ)
    · have hT11m : Work.FIArea4.p14T11 m (cR c R) S (ε/4) ≤ mcInner D R S m c H ε :=
        p14T11_le_mcInner h1D h1c hHge hε hcase.1 hcase.2 hRle h1m
      calc ‖farInner D R S a b α m c 0 1‖
          ≤ Cd * (Real.log (2 + H) + 1) ^ 2 * (Real.log (2 * (cR c R : ℝ)) + 1)
              * Work.FIArea4.p14T11 m (cR c R) S (ε / 4)
              * Work.FIArea4.p14L2 (cR c R) S (redA c α) := hb2
        _ ≤ Cd * (Real.log (2 + H) + 1) ^ 2 * (Real.log (2 * (cR c R : ℝ)) + 1)
              * mcInner D R S m c H ε
              * Work.FIArea4.p14L2 (cR c R) S (redA c α) := by
              nlinarith only [hT11m, hCLnn]
        _ = CL * mcInner D R S m c H ε := by rw [hCL]; ring
    · have hzero : farInner D R S a b α m c 0 1 = 0 := by
        by_cases hq : (S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ)) < 1/2
        · have hbig : 8*(R:ℝ)*(S:ℝ) < (c:ℝ)*(D:ℝ) := by
            by_contra hcon
            exact hcase ⟨hq, not_lt.mp hcon⟩
          exact farInner_eq_zero_of_large_cD hD0 hHpos hapos haH hbig
        · apply (farInner_eq_zero_of_range (D := D) (R := R) (S := S) (m := m) (c := c)
            (Q1 := 0) (Q2 := 1) (a := a) (b := b) (H := H) (α := α)
            hD0 hHpos hapos haH).1
          have h5 : (0:ℝ) < 5*H*(c:ℝ)*(D:ℝ) := by positivity
          have hge := not_lt.mp hq
          have hmul : (1/2) * (5*H*(c:ℝ)*(D:ℝ))
              ≤ ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))) * (5*H*(c:ℝ)*(D:ℝ)) :=
            mul_le_mul_of_nonneg_right hge h5.le
          rw [div_mul_cancel₀ _ (ne_of_gt h5)] at hmul
          have hg : 5 * H * (c:ℝ) * (D:ℝ) ≤ 2 * (S:ℝ) * (R:ℝ) := by linarith only [hmul]
          simpa using hg
      rw [hzero, norm_zero]
      exact mul_nonneg hCLnn hMnn
  -- ===== (9) final numeric assembly =====
  refine le_trans (add_le_add hA1 hA2) ?_
  have hCL_le : CL ≤ 4 * (Cd * (Real.log (2*H)+1)^2 * (Real.log (2*(cR c R : ℝ))+1)
      * Work.FIArea4.p14L2 (cR c R) S (redA c α)) := by
    rw [hCL]
    have hlog := mcLog_bound hHge
    have hnl : (0:ℝ) ≤ Cd * (Real.log (2*(cR c R : ℝ))+1)
        * Work.FIArea4.p14L2 (cR c R) S (redA c α) :=
      mul_nonneg (mul_nonneg hCd.le hPnn) hL2nn
    nlinarith only [hlog, hnl]
  have hstep : CL * (10 * mcInner D R S m c H ε) + CL * mcInner D R S m c H ε
      ≤ (100 * Cd) * ((Real.log (2*H)+1)^2 * (Real.log (2*(cR c R : ℝ))+1)
          * mcInner D R S m c H ε)
        * Work.FIArea4.p14L2 (cR c R) S (redA c α) := by
    have hAnn : (0:ℝ) ≤ (Real.log (2*H)+1)^2 := sq_nonneg _
    have hnl : (0:ℝ) ≤ Cd * (Real.log (2*H)+1)^2 * (Real.log (2*(cR c R : ℝ))+1)
        * mcInner D R S m c H ε * Work.FIArea4.p14L2 (cR c R) S (redA c α) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCd.le hAnn) hPnn) hMnn) hL2nn
    nlinarith only [hCL_le, hMnn, hnl]
  exact hstep

end

end Work.FIArea4.Vflip.Vfd
