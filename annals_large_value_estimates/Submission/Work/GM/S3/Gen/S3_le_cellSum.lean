import Mathlib
import Submission.Work.GM.S3.gen_defs
import Submission.Work.GM.S3.norm_Iterm_le_Rtilde_of_domain
import Submission.Work.GM.S3.s3_tail_noclash
import Submission.Work.GM.S3.Iterm_transpose
import Submission.Work.GM.S3.Iterm_cyclic
import Submission.Work.GM.S3.Gen.cs_defs
import Submission.Work.GM.S3.Gen.cs_decay_bound
import Submission.Work.GM.S3.Gen.cs_cell_bound
import Submission.Work.GM.S3.Gen.cs_cover
import Submission.Work.GM.S3.Gen.csLHS_eq_csNzBox
import Submission.Work.GM.S3.Gen.csNzBox_le_three_maxBox
import Submission.Work.GM.S3.Gen.cs_log_cube_le

namespace Work.GM.S3.Gen

open Finset
open scoped BigOperators

open Submission.GM (Iterm Separated)
open Submission.LargeValues (M)

set_option maxHeartbeats 4000000

theorem cs_cellSum_nonneg {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) (W : Finset ℝ) (J : ℕ)
    (ψ₁ ψ₂ : ℝ → ℝ) :
    0 ≤ cellSum N W δ (δ / 2) J ψ₁ ψ₂ := by
  classical
  unfold cellSum
  refine Finset.sum_nonneg fun p hp => mul_nonneg (div_nonneg (by positivity) ?_) (S30g_nonneg ..)
  exact le_of_lt (Bdy_pos hN (csKlev_pos hN δ))

theorem cs_idx1_card_le {M : ℝ} (hM : 0 ≤ M) : (idx1 M).card ≤ 4 * M + 1 := by
  have h1 : (idx1 M).card ≤ (Finset.Icc (-⌊2 * M⌋) ⌊2 * M⌋).card := by
    refine Finset.card_le_card fun m hm => ?_
    simp only [idx1, Finset.mem_filter] at hm
    exact hm.1
  rw [Int.card_Icc] at h1
  have h2 : (((⌊2 * M⌋ + 1 - -⌊2 * M⌋).toNat : ℤ) : ℝ) = ((2 * ⌊2 * M⌋ + 1 : ℤ) : ℝ) := by
    have heq : ⌊2 * M⌋ + 1 - -⌊2 * M⌋ = 2 * ⌊2 * M⌋ + 1 := by ring
    rw [heq]
    have hnn : (0 : ℤ) ≤ 2 * ⌊2 * M⌋ + 1 := by
      have := Int.floor_nonneg.mpr (by linarith : (0:ℝ) ≤ 2 * M)
      omega
    rw [Int.toNat_of_nonneg hnn]
  have h3 : ((2 * ⌊2 * M⌋ + 1 : ℤ) : ℝ) ≤ 4 * M + 1 := by
    have hle := Int.floor_le (2 * M)
    push_cast at hle ⊢
    linarith
  calc ((idx1 M).card : ℝ) ≤ (((⌊2 * M⌋ + 1 - -⌊2 * M⌋).toNat : ℤ) : ℝ) := by
        exact_mod_cast h1
    _ = ((2 * ⌊2 * M⌋ + 1 : ℤ) : ℝ) := h2
    _ ≤ 4 * M + 1 := h3

theorem cs_Mdy_le_Klev {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) (i : ℕ) : Mdy N δ i ≤ Klev N δ := by
  have hK : (0 : ℝ) ≤ Klev N δ := le_of_lt (csKlev_pos hN δ)
  have h1 : (1 : ℝ) ≤ 2 ^ i := by
    exact_mod_cast Nat.one_le_pow i 2 (by norm_num)
  rw [Mdy, div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ i)]
  nlinarith [hK, h1]

theorem cs_cell_card_le {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) (i j k : ℕ) :
    ((csCell N δ i j k).card : ℝ) ≤ (4 * Klev N δ + 1) ^ 3 := by
  have hKi : (0 : ℝ) ≤ Mdy N δ i := le_of_lt (csMdy_pos hN δ i)
  have hKj : (0 : ℝ) ≤ Mdy N δ j := le_of_lt (csMdy_pos hN δ j)
  have hKk : (0 : ℝ) ≤ Mdy N δ k := le_of_lt (csMdy_pos hN δ k)
  have h1 : ((idx1 (Mdy N δ i)).card : ℝ) ≤ 4 * Klev N δ + 1 :=
    le_trans (cs_idx1_card_le hKi) (by linarith [cs_Mdy_le_Klev hN δ i])
  have h2 : ((idxM (Mdy N δ j)).card : ℝ) ≤ 4 * Klev N δ + 1 :=
    le_trans (cs_idx1_card_le hKj) (by linarith [cs_Mdy_le_Klev hN δ j])
  have h3 : ((idxM (Mdy N δ k)).card : ℝ) ≤ 4 * Klev N δ + 1 :=
    le_trans (cs_idx1_card_le hKk) (by linarith [cs_Mdy_le_Klev hN δ k])
  have h0 : (0 : ℝ) ≤ 4 * Klev N δ + 1 := by
    have := le_of_lt (csKlev_pos hN δ); linarith
  have hcard : ((csCell N δ i j k).card : ℝ)
      = ((idx1 (Mdy N δ i)).card : ℝ) * ((idxM (Mdy N δ j)).card : ℝ) *
        ((idxM (Mdy N δ k)).card : ℝ) := by
    rw [csCell, Finset.product_eq_sprod, Finset.product_eq_sprod]
    rw [Finset.card_product, Finset.card_product]
    push_cast
    ring
  have ha : (0 : ℝ) ≤ ((idxM (Mdy N δ k)).card : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ ((idxM (Mdy N δ j)).card : ℝ) := by positivity
  rw [hcard]
  calc ((idx1 (Mdy N δ i)).card : ℝ) * ((idxM (Mdy N δ j)).card : ℝ) * ((idxM (Mdy N δ k)).card : ℝ)
      ≤ (4 * Klev N δ + 1) * (4 * Klev N δ + 1) * (4 * Klev N δ + 1) := by
        exact mul_le_mul (mul_le_mul h1 h2 hb h0) h3 ha (by nlinarith [h0])
    _ = (4 * Klev N δ + 1) ^ 3 := by ring


theorem S3_le_cellSum :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∀ (ψ₁ ψ₂ : ℝ → ℝ), Work.GM.S3.IsBumpAtZero ψ₁ 4 → Work.GM.S3.IsBumpAtOne ψ₂ 4 →
      (∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x) → (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x) →
    (∑ m₁ ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋,
      ∑ m₂ ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋,
      ∑ m₃ ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋,
        if (m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0) then ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ else 0) ≤
      C * (N : ℝ) ^ δ * Work.GM.S3.Gen.cellSum N W δ (δ / 2) (Work.GM.S3.Gen.cellJ N δ) ψ₁ ψ₂ +
        C * (N : ℝ) ^ δ * (Submission.LargeValues.M N) ^ (3 * (δ / 2)) * (W.card : ℝ) ^ 3 +
        C * (N : ℝ) ^ (-10 : ℤ) := by
  intro ε δ hε hδ
  by_cases hA : (3:ℝ)/2 ≤ δ
  · -- ============ Case A: δ ≥ 3/2, the elementary decay bound ============
    obtain ⟨Cd, hCdpos, hdec⟩ := cs_decay_bound
    obtain ⟨N₀l, hlogb⟩ := cs_log_cube_le (Cd * (1 + δ) ^ 3) (by positivity)
    refine ⟨1, one_pos, max N₀l 2, ?_⟩
    intro N hN W hW hsep ψ₁ ψ₂ hb1 hb2 hp1 hp2
    have hNl : N₀l ≤ N := le_trans (le_max_left _ _) hN
    have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
    have hN1 : 1 ≤ N := by omega
    have hNpos : (0:ℝ) < (N:ℝ) := by positivity
    have hNgt : (1:ℝ) < (N:ℝ) := by exact_mod_cast hN2
    have hlog := hlogb N hNl
    have hdec' := hdec N δ hδ hN1 W hW
    have hcs : 0 ≤ cellSum N W δ (δ / 2) (cellJ N δ) ψ₁ ψ₂ := cs_cellSum_nonneg hN1 δ W _ ψ₁ ψ₂
    have hMdef : Submission.LargeValues.M N = (N:ℝ)^((6:ℝ)/5) := rfl
    have hLHS_eq : (Submission.LargeValues.M N)^3 * (N:ℝ)^(0.3:ℝ) = (N:ℝ)^(3.9:ℝ) := by
      rw [hMdef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
      norm_num
    have hRHS_eq : (N:ℝ)^δ * (Submission.LargeValues.M N)^(3*(δ/2)) = (N:ℝ)^(2.8*δ) := by
      rw [hMdef, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
      ring_nf
    have hmono : (N:ℝ)^(3.9:ℝ) ≤ (N:ℝ)^(2.8*δ) := by
      rw [Real.rpow_le_rpow_left_iff hNgt]
      linarith
    have hkey : Cd * (W.card:ℝ)^3 * (Submission.LargeValues.M N)^3 *
        (1 + Real.log (N:ℝ))^3 * (1+δ)^3 ≤
        (N:ℝ)^δ * (Submission.LargeValues.M N)^(3*(δ/2)) * (W.card:ℝ)^3 := by
      have hw : (0:ℝ) ≤ (W.card:ℝ)^3 := by positivity
      have h1 : Cd * (1+δ)^3 * (1 + Real.log (N:ℝ))^3 ≤ (N:ℝ)^(0.3:ℝ) := by
        have hh := hlog; linarith [hh]
      have hMw : (0:ℝ) ≤ Submission.LargeValues.M N := by
        have := Submission.LargeValues.M_ge_one hN1; linarith
      have hT3nn : (0:ℝ) ≤ (Submission.LargeValues.M N)^3 := pow_nonneg hMw 3
      calc Cd * (W.card:ℝ)^3 * (Submission.LargeValues.M N)^3 *
            (1 + Real.log (N:ℝ))^3 * (1+δ)^3
          = (W.card:ℝ)^3 * ((Submission.LargeValues.M N)^3 * (Cd * (1+δ)^3 *
              (1 + Real.log (N:ℝ))^3)) := by ring
        _ ≤ (W.card:ℝ)^3 * ((Submission.LargeValues.M N)^3 * (N:ℝ)^(0.3:ℝ)) := by
              refine mul_le_mul_of_nonneg_left ?_ hw
              exact mul_le_mul_of_nonneg_left h1 hT3nn
        _ ≤ (W.card:ℝ)^3 * ((N:ℝ)^δ * (Submission.LargeValues.M N)^(3*(δ/2))) := by
              refine mul_le_mul_of_nonneg_left ?_ hw
              rw [hLHS_eq, hRHS_eq]
              exact hmono
        _ = (N:ℝ)^δ * (Submission.LargeValues.M N)^(3*(δ/2)) * (W.card:ℝ)^3 := by ring
    have hMw : (0:ℝ) ≤ Submission.LargeValues.M N := by
      have := Submission.LargeValues.M_ge_one hN1; linarith
    have hmid : (0:ℝ) ≤ (N:ℝ)^δ * (Submission.LargeValues.M N)^(3*(δ/2)) * (W.card:ℝ)^3 := by
      refine mul_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt hNpos) _)
        (Real.rpow_nonneg hMw _)) (by positivity)
    have hlast : (0:ℝ) ≤ (N:ℝ)^(-10:ℤ) := zpow_nonneg (le_of_lt hNpos) _
    have hcs2 : (0:ℝ) ≤ (N:ℝ)^δ * cellSum N W δ (δ / 2) (cellJ N δ) ψ₁ ψ₂ :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hNpos) _) hcs
    rw [show (∑ m₁ ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋,
        ∑ m₂ ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋,
        ∑ m₃ ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋,
          if (m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0) then ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ else 0)
        = csLHS N δ W from rfl]
    linarith [hdec', hkey, hcs2, hmid, hlast]
  · -- ============ Case B: δ < 3/2, the cell decomposition ============
    have hδ15 : δ ≤ 3 / 2 := by linarith [not_le.mp hA]
    obtain ⟨Cb, hCbpos, N₀b, hcell⟩ := cs_cell_bound ε δ hε hδ
    obtain ⟨N₀c, hcover⟩ := cs_cover δ hδ hδ15
    refine ⟨max 1 (3 * Cb), lt_of_lt_of_le one_pos (le_max_left _ _),
      max (max N₀b N₀c) (2^40), ?_⟩
    intro N hN W hW hsep ψ₁ ψ₂ hb1 hb2 hp1 hp2
    have hNb : N₀b ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hNc : N₀c ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hNbig : 2^40 ≤ N := le_trans (le_max_right _ _) hN
    have hN1 : 1 ≤ N := le_trans (by norm_num : 1 ≤ 2^40) hNbig
    have hN2 : 2 ≤ N := le_trans (by norm_num : 2 ≤ 2^40) hNbig
    have h328 : (328:ℝ)^3 * 125 ≤ N := by
      have h2 : (2:ℝ)^40 ≤ N := by exact_mod_cast hNbig
      norm_num at h2 ⊢
      linarith
    have hNpos : (0:ℝ) < (N:ℝ) := by positivity
    have hNgt : (1:ℝ) < (N:ℝ) := by exact_mod_cast hN2
    have hcs : 0 ≤ cellSum N W δ (δ / 2) (cellJ N δ) ψ₁ ψ₂ := cs_cellSum_nonneg hN1 δ W _ ψ₁ ψ₂
    have hLHS_eq : csLHS N δ W = ∑ u ∈ csNzBox (Klev N δ), ‖Iterm N W u‖ :=
      csLHS_eq_csNzBox N δ W
    have hmax : (∑ u ∈ csNzBox (Klev N δ), ‖Iterm N W u‖) ≤
        3 * ∑ u ∈ csMaxBox (Klev N δ), ‖Iterm N W u‖ :=
      csNzBox_le_three_maxBox (Klev N δ) N W
    have hbox_bound : ∀ (m : ℤ), m ∈ Finset.Icc (-⌊Klev N δ⌋) ⌊Klev N δ⌋ → |(m:ℝ)| ≤ Klev N δ := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h1 : ((-(Klev N δ)) : ℝ) ≤ ((-⌊Klev N δ⌋ : ℤ) : ℝ) := by
          have := Int.floor_le (Klev N δ); push_cast; linarith
        have h2 : ((-⌊Klev N δ⌋ : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
        linarith
      · have h2 : (m : ℝ) ≤ (⌊Klev N δ⌋ : ℝ) := by exact_mod_cast hm.2
        have := Int.floor_le (Klev N δ); linarith
    have hmem : ∀ u ∈ csMaxBox (Klev N δ),
        u.1 ≠ 0 ∧ u.2.1 ≠ 0 ∧ u.2.2 ≠ 0 ∧ |(u.1:ℝ)| ≤ Klev N δ ∧
          |(u.2.1:ℝ)| ≤ Klev N δ ∧ |(u.2.2:ℝ)| ≤ Klev N δ ∧
          |(u.1:ℝ)| ≤ |(u.2.1:ℝ)| ∧ |(u.2.2:ℝ)| ≤ |(u.2.1:ℝ)| := by
      intro u hu
      rw [csMaxBox, Finset.mem_filter] at hu
      obtain ⟨hu1, hu2a, hu2b⟩ := hu
      rw [mem_csNzBox] at hu1
      obtain ⟨hm1, hm2, hm3⟩ := hu1
      exact ⟨hm1.2, hm2.2, hm3.2, hbox_bound _ hm1.1, hbox_bound _ hm2.1, hbox_bound _ hm3.1,
        hu2a, hu2b⟩
    have hmap : ∀ u ∈ csMaxBox (Klev N δ), csGcell N δ u ∈ cellFam N δ (δ / 2) (cellJ N δ) := by
      intro u hu
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hmem u hu
      exact (hcover N hNc u h1 h2 h3 h4 h5 h6 h7 h8).1
    have hfw := Finset.sum_fiberwise_of_maps_to hmap (fun u => ‖Iterm N W u‖)
    have hcells : (∑ u ∈ csMaxBox (Klev N δ), ‖Iterm N W u‖) ≤
        ∑ p ∈ cellFam N δ (δ / 2) (cellJ N δ),
          ∑ u ∈ csCell N δ p.1 p.2.1 p.2.2, ‖Iterm N W u‖ := by
      rw [← hfw]
      refine Finset.sum_le_sum fun p hp => ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨hux, hgu⟩ := hu
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hmem u hux
        have hconj := (hcover N hNc u h1 h2 h3 h4 h5 h6 h7 h8).2
        rwa [hgu] at hconj
      · intro u hu hnu; positivity
    have hpercell : (∑ p ∈ cellFam N δ (δ / 2) (cellJ N δ),
          ∑ u ∈ csCell N δ p.1 p.2.1 p.2.2, ‖Iterm N W u‖) ≤
        ∑ p ∈ cellFam N δ (δ / 2) (cellJ N δ),
          (Cb * ((N:ℝ)^2 / Bdy N δ (δ/2) p.2.1) *
              S30g N W (Bdy N δ (δ/2) p.2.1) (Mdy N δ p.1) (Mdy N δ p.2.1) (Mdy N δ p.2.2)
                ψ₁ ψ₂
            + Cb * (N:ℝ)^(-20:ℤ) * ((csCell N δ p.1 p.2.1 p.2.2).card : ℝ)) := by
      refine Finset.sum_le_sum fun p hp => ?_
      exact hcell N hNb W hW hsep ψ₁ ψ₂ hb1 hb2 hp1 hp2 p.1 p.2.1 p.2.2
    have hsplit : (∑ p ∈ cellFam N δ (δ / 2) (cellJ N δ),
          (Cb * ((N:ℝ)^2 / Bdy N δ (δ/2) p.2.1) *
              S30g N W (Bdy N δ (δ/2) p.2.1) (Mdy N δ p.1) (Mdy N δ p.2.1) (Mdy N δ p.2.2)
                ψ₁ ψ₂
            + Cb * (N:ℝ)^(-20:ℤ) * ((csCell N δ p.1 p.2.1 p.2.2).card : ℝ))) =
        Cb * cellSum N W δ (δ/2) (cellJ N δ) ψ₁ ψ₂
          + Cb * (N:ℝ)^(-20:ℤ) *
            (∑ p ∈ cellFam N δ (δ/2) (cellJ N δ), ((csCell N δ p.1 p.2.1 p.2.2).card : ℝ)) := by
      have h1 : (∑ p ∈ cellFam N δ (δ / 2) (cellJ N δ),
            Cb * ((N:ℝ)^2 / Bdy N δ (δ/2) p.2.1) *
              S30g N W (Bdy N δ (δ/2) p.2.1) (Mdy N δ p.1) (Mdy N δ p.2.1) (Mdy N δ p.2.2)
                ψ₁ ψ₂) = Cb * cellSum N W δ (δ/2) (cellJ N δ) ψ₁ ψ₂ := by
        rw [show cellSum N W δ (δ/2) (cellJ N δ) ψ₁ ψ₂ =
          ∑ p ∈ cellFam N δ (δ/2) (cellJ N δ), ((N:ℝ)^2 / Bdy N δ (δ/2) p.2.1) *
            S30g N W (Bdy N δ (δ/2) p.2.1) (Mdy N δ p.1) (Mdy N δ p.2.1) (Mdy N δ p.2.2)
              ψ₁ ψ₂ from rfl]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p hp => by ring
      have h2 : (∑ p ∈ cellFam N δ (δ / 2) (cellJ N δ),
            Cb * (N:ℝ)^(-20:ℤ) * ((csCell N δ p.1 p.2.1 p.2.2).card : ℝ)) =
          Cb * (N:ℝ)^(-20:ℤ) *
            (∑ p ∈ cellFam N δ (δ/2) (cellJ N δ), ((csCell N δ p.1 p.2.1 p.2.2).card : ℝ)) := by
        rw [Finset.mul_sum]
      rw [Finset.sum_add_distrib, h1, h2]
    have hcardsum : (∑ p ∈ cellFam N δ (δ/2) (cellJ N δ), ((csCell N δ p.1 p.2.1 p.2.2).card : ℝ))
        ≤ (cellJ N δ : ℝ)^3 * (4 * Klev N δ + 1)^3 := by
      refine le_trans (Finset.sum_le_sum fun p hp => cs_cell_card_le hN1 δ p.1 p.2.1 p.2.2) ?_
      rw [Finset.sum_const]
      rw [nsmul_eq_mul]
      have h1 : ((cellFam N δ (δ/2) (cellJ N δ)).card : ℝ) ≤ (cellJ N δ : ℝ)^3 := by
        have h2 : (cellFam N δ (δ/2) (cellJ N δ)).card ≤ (cellJ N δ)^3 := by
          refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
          rw [Finset.card_product, Finset.card_product]
          simp only [Finset.card_range]
          exact le_of_eq (by ring)
        exact_mod_cast h2
      have h0 : (0:ℝ) ≤ (4 * Klev N δ + 1)^3 := by
        have := csKlev_pos hN1 δ; positivity
      exact mul_le_mul_of_nonneg_right h1 h0
    have hK2 : Klev N δ ≤ (N:ℝ)^2 := by
      have hexp : (6:ℝ)/5 * (1 + δ) - 1 ≤ 2 := by linarith [hδ15]
      have heq : Klev N δ = (N:ℝ)^((6:ℝ)/5 * (1+δ) - 1) := by
        have h1 : (N:ℝ)^((6:ℝ)/5 * (1+δ) - 1) = (N:ℝ)^((6:ℝ)/5 * (1+δ)) / N := by
          rw [Real.rpow_sub hNpos, Real.rpow_one]
        rw [Klev, (show Submission.LargeValues.M N = (N:ℝ)^((6:ℝ)/5) from rfl),
          ← Real.rpow_mul hNpos.le, ← h1]
      calc Klev N δ = (N:ℝ)^((6:ℝ)/5 * (1+δ) - 1) := heq
        _ ≤ (N:ℝ)^(((2:ℕ)):ℝ) := by
            rw [Real.rpow_le_rpow_left_iff hNgt]; push_cast; exact hexp
        _ = (N:ℝ)^2 := Real.rpow_natCast (N:ℝ) 2
    have hJ : (cellJ N δ : ℝ) ≤ 328 * N := by
      have hlog : Nat.log 2 N ≤ N := Nat.log_le_self 2 N
      have hceil : Nat.ceil δ ≤ 2 := Nat.ceil_le.mpr (by push_cast; linarith [hδ15])
      have hlog' : ((Nat.log 2 N : ℕ) : ℝ) ≤ N := by exact_mod_cast hlog
      have hceil' : ((Nat.ceil δ : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hceil
      have hN1r : (1:ℝ) ≤ N := by exact_mod_cast hN1
      have hJnum : ((8 * Nat.ceil δ * (Nat.log 2 N + 1) + 256 : ℕ) : ℝ) ≤ 328 * N := by
        push_cast
        nlinarith [hlog', hceil', hN1r]
      simpa only [cellJ] using hJnum
    have hNδ1 : (1:ℝ) ≤ (N:ℝ)^δ := Real.one_le_rpow (by exact_mod_cast hN1) (le_of_lt hδ)
    have hKw : (0:ℝ) ≤ Klev N δ := le_of_lt (csKlev_pos hN1 δ)
    have hMw : (0:ℝ) ≤ Submission.LargeValues.M N := by
      have := Submission.LargeValues.M_ge_one hN1; linarith
    have hcardN : (∑ p ∈ cellFam N δ (δ/2) (cellJ N δ), ((csCell N δ p.1 p.2.1 p.2.2).card : ℝ))
        ≤ (N:ℝ)^10 := by
      refine le_trans hcardsum ?_
      have hNsq : (1:ℝ) ≤ (N:ℝ)^2 := by
        have hN1r : (1:ℝ) ≤ N := by exact_mod_cast hN1
        nlinarith [hN1r]
      have h1 : (4*Klev N δ + 1) ≤ 5 * (N:ℝ)^2 := by linarith [hK2, hNsq]
      have h4 : (cellJ N δ : ℝ)^3 ≤ (328*N)^3 := pow_le_pow_left₀ (by positivity) hJ 3
      have h5 : (328*N)^3 * (5*(N:ℝ)^2)^3 ≤ (N:ℝ)^10 := by
        have h9 : (0:ℝ) ≤ (N:ℝ)^9 := by positivity
        calc (328*N)^3 * (5*(N:ℝ)^2)^3 = (328^3 * 125) * (N:ℝ)^9 := by ring
          _ ≤ N * (N:ℝ)^9 := mul_le_mul_of_nonneg_right h328 h9
          _ = (N:ℝ)^10 := by ring
      have h2 : (4*Klev N δ + 1)^3 ≤ 125 * (N:ℝ)^6 :=
        le_trans (pow_le_pow_left₀ (by linarith [hKw]) h1 3) (le_of_eq (by ring))
      calc (cellJ N δ : ℝ)^3 * (4*Klev N δ + 1)^3
          ≤ (328*N)^3 * (125 * (N:ℝ)^6) := mul_le_mul h4 h2 (by positivity) (by positivity)
        _ = (328*N)^3 * (5*(N:ℝ)^2)^3 := by ring
        _ ≤ (N:ℝ)^10 := h5
    have hcardbound : 3 * Cb * (N:ℝ)^(-20:ℤ) *
        (∑ p ∈ cellFam N δ (δ/2) (cellJ N δ), ((csCell N δ p.1 p.2.1 p.2.2).card : ℝ)) ≤
        max 1 (3*Cb) * (N:ℝ)^(-10:ℤ) := by
      have h3c : (0:ℝ) ≤ 3 * Cb := by linarith
      have hN10 : (N:ℝ)^(-20:ℤ) * (N:ℝ)^10 = (N:ℝ)^(-10:ℤ) := by
        rw [← zpow_natCast, ← zpow_add₀ (ne_of_gt hNpos)]
        norm_num
      calc 3 * Cb * (N:ℝ)^(-20:ℤ) *
            (∑ p ∈ cellFam N δ (δ/2) (cellJ N δ), ((csCell N δ p.1 p.2.1 p.2.2).card : ℝ))
          = (3*Cb) * ((N:ℝ)^(-20:ℤ) * (∑ p ∈ cellFam N δ (δ/2) (cellJ N δ),
              ((csCell N δ p.1 p.2.1 p.2.2).card : ℝ))) := by ring
        _ ≤ (3*Cb) * ((N:ℝ)^(-20:ℤ) * (N:ℝ)^10) := by
            refine mul_le_mul_of_nonneg_left ?_ h3c
            exact mul_le_mul_of_nonneg_left hcardN (zpow_nonneg (le_of_lt hNpos) _)
        _ = (3*Cb) * (N:ℝ)^(-10:ℤ) := by rw [hN10]
        _ ≤ max 1 (3*Cb) * (N:ℝ)^(-10:ℤ) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (zpow_nonneg (le_of_lt hNpos) _)
    have hcellsum_bound : 3 * Cb * cellSum N W δ (δ/2) (cellJ N δ) ψ₁ ψ₂ ≤
        max 1 (3*Cb) * (N:ℝ)^δ * cellSum N W δ (δ/2) (cellJ N δ) ψ₁ ψ₂ := by
      calc 3 * Cb * cellSum N W δ (δ/2) (cellJ N δ) ψ₁ ψ₂
          = (3*Cb) * cellSum N W δ (δ/2) (cellJ N δ) ψ₁ ψ₂ := by ring
        _ ≤ (3*Cb) * ((N:ℝ)^δ * cellSum N W δ (δ/2) (cellJ N δ) ψ₁ ψ₂) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            simpa using mul_le_mul_of_nonneg_right hNδ1 hcs
        _ ≤ max 1 (3*Cb) * ((N:ℝ)^δ * cellSum N W δ (δ/2) (cellJ N δ) ψ₁ ψ₂) := by
            refine mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ = max 1 (3*Cb) * (N:ℝ)^δ * cellSum N W δ (δ/2) (cellJ N δ) ψ₁ ψ₂ := by ring
    have hmid : (0:ℝ) ≤ max 1 (3*Cb) * (N:ℝ)^δ * (Submission.LargeValues.M N)^(3*(δ/2)) *
        (W.card:ℝ)^3 := by
      refine mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt (lt_of_lt_of_le one_pos (le_max_left _ _)))
        (Real.rpow_nonneg (le_of_lt hNpos) _)) (Real.rpow_nonneg hMw _)) (by positivity)
    have hlast : (0:ℝ) ≤ max 1 (3*Cb) * (N:ℝ)^(-10:ℤ) :=
      mul_nonneg (le_of_lt (lt_of_lt_of_le one_pos (le_max_left _ _)))
        (zpow_nonneg (le_of_lt hNpos) _)
    rw [show (∑ m₁ ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋,
        ∑ m₂ ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋,
        ∑ m₃ ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋,
          if (m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0) then ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ else 0)
        = csLHS N δ W from rfl]
    linarith [hLHS_eq.le, hmax, hcells, hpercell, hsplit.le, hcellsum_bound, hcardbound, hmid, hlast]

end Work.GM.S3.Gen
