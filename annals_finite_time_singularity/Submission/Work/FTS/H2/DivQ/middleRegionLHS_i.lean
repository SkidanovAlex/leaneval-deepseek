import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.FTS.H2.DivQ.middleRegionLHS
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The middle-region bound, with the data hypothesis at the level actually needed.**

This is `middleRegionLHS` with its hypothesis `∀ m ∈ Finset.Icc 1 4, IntegrableOn (Denγ m)`
*wakened* to `∀ m ∈ Finset.Icc 1 i` (the right-hand side already sums only over `m ≤ i`, and the
proof only ever uses the data at levels `m < i`).  The weakening is what makes the result applicable
to the slices `h_b = fun θ => DzIter b Φ z θ` with `b ≥ 1`, for which `HkMem α 4 (pth Φ)` certifies
the data only when `m + b ≤ 4`, while the assembly needs the bound at level `i ≤ 4 - b`.
The proof body of `middleRegionLHS` carries over verbatim: its only use of the data hypothesis is
inside its `hBm`, at levels `1 ≤ m ≤ i`, and the `m = 0` term uses the unchanged `η`-weighted
hypothesis. -/
theorem middleRegionLHS_i :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 →
        (∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
        (∫ θ in (Real.pi / 8)..(3 * Real.pi / 8),
            (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  obtain ⟨K, hKpos, hKb⟩ := divSinIterMidBound
  obtain ⟨C₁, hC₁pos, hC₁b⟩ := honestPoincarePoint
  refine ⟨100 * K * (C₁ + 1) + 1, by positivity, ?_⟩
  intro α h hα hα1 hsm ht0 ht1 hIntη i hi hIntγ
  let γ : ℝ := Work.Spaces.gam α
  let V : ℝ → ℝ := fun θ => h θ / Real.sin (2 * θ)
  let w : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-γ)
  let wη : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  let Un : ℕ → ℝ → ℝ := fun m θ => Work.Elliptic.Dth1Iter m (deriv h) θ
  let Denη : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * wη θ
  let Dens : ℝ := ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hi4 : i ≤ 4 := (Finset.mem_Icc.mp hi).2
  have hγdef : γ = Work.Spaces.gam α := rfl
  have hγpos : 0 < γ := by rw [hγdef, Work.Spaces.gam]; linarith
  have hγeta : Work.Spaces.eta ≤ γ := by
    rw [hγdef, Work.Spaces.gam, Work.Spaces.eta]; linarith
  have hγle : γ ≤ 1.1 := by rw [hγdef, Work.Spaces.gam]; linarith
  have h2γle : (2 : ℝ) ^ γ ≤ 4 := by
    have h1 : (2 : ℝ) ^ γ ≤ (2 : ℝ) ^ (2 : ℝ) :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by linarith)
    have h2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    linarith [h1, h2]
  have h2γ1 : (1 : ℝ) ≤ 2 ^ γ := Real.one_le_rpow (by norm_num) hγpos.le
  have h2γ_nn : (0 : ℝ) ≤ 2 ^ γ := le_trans zero_le_one h2γ1
  have hDenη_nn : 0 ≤ Denη :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _))
  have hDens_nn : 0 ≤ Dens :=
    Finset.sum_nonneg (fun m _ =>
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _)))
  show (∫ θ in midA..midB, (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ)
      ≤ (100 * K * (C₁ + 1) + 1) * (Denη + Dens)
  rw [intervalIntegral.integral_of_le midA_lt_midB.le]
  -- ## integrability on the middle interval
  have hIc : ∀ m ∈ Finset.range i,
      IntegrableOn (fun θ => (Un m θ) ^ 2 * w θ) (Set.Ioc midA midB) := by
    intro m _
    exact (ContinuousOn.integrableOn_compact isCompact_Icc
      (((continuousOn_Dth1Iter_deriv hsm m).pow 2).mul
        (continuousOn_rpow_neg_sin_two γ))).mono_set Set.Ioc_subset_Icc_self
  have hIa : IntegrableOn (fun θ => (V θ) ^ 2 * w θ) (Set.Ioc midA midB) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (((continuousOn_div_sin_two hsm).pow 2).mul
        (continuousOn_rpow_neg_sin_two γ))).mono_set Set.Ioc_subset_Icc_self
  have hIb : IntegrableOn (fun θ => ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ)
      (Set.Ioc midA midB) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_finsetSum (Finset.range i) (fun m _ =>
        ((continuousOn_Dth1Iter_deriv hsm m).pow 2).mul
          (continuousOn_rpow_neg_sin_two γ)))).mono_set Set.Ioc_subset_Icc_self
  have hFint : IntegrableOn (fun θ => (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ)
      (Set.Ioc midA midB) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (((continuousOn_Dth1Iter_div hsm i).pow 2).mul
        (continuousOn_rpow_neg_sin_two γ))).mono_set Set.Ioc_subset_Icc_self
  have hΨint : IntegrableOn
      (fun θ => K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ))
      (Set.Ioc midA midB) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_const.mul ((((continuousOn_div_sin_two hsm).pow 2).mul
        (continuousOn_rpow_neg_sin_two γ)).add
        (continuousOn_finsetSum (Finset.range i) (fun m _ =>
          ((continuousOn_Dth1Iter_deriv hsm m).pow 2).mul
            (continuousOn_rpow_neg_sin_two γ)))))).mono_set Set.Ioc_subset_Icc_self
  -- ## the pointwise iterate bound
  have hpt : ∀ θ ∈ Set.Ioc midA midB,
      (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ
        ≤ K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ) := by
    intro θ hθ
    have hm : θ ∈ midSet := ⟨le_of_lt hθ.1, hθ.2⟩
    have hw : 0 ≤ w θ :=
      Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ (midSet_subset_Iθ hm)) _
    have h1 := hKb h hsm i hi θ hm
    calc (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ
        ≤ (K * ((V θ) ^ 2 + ∑ m ∈ Finset.range i, (Un m θ) ^ 2)) * w θ :=
          mul_le_mul_of_nonneg_right h1 hw
      _ = K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ) := by
          rw [← Finset.sum_mul]; ring
  -- ## evaluation of `∫ Ψ`
  have hΨeq : (∫ θ in Set.Ioc midA midB,
        K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ))
      = K * ((∫ θ in Set.Ioc midA midB, (V θ) ^ 2 * w θ)
          + ∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_add hIa hIb, MeasureTheory.integral_finsetSum _ hIc]
  -- ## the `V`-term
  have hBV : (∫ θ in Set.Ioc midA midB, (V θ) ^ 2 * w θ) ≤ 16 * C₁ * Denη := by
    have hptV : ∀ θ ∈ Set.Ioc midA midB, (V θ) ^ 2 * w θ ≤ 16 * C₁ * Denη := by
      intro θ hθ
      have hm : θ ∈ midSet := ⟨le_of_lt hθ.1, hθ.2⟩
      have hhalf := half_le_sin_two_of_mem_mid hm
      have hC := hC₁b h hsm ht0 hIntη θ (midSet_subset_Ioo hm)
      have hw := rpow_neg_sin_two_le_mid hγpos.le hm
      have hV2 : (V θ) ^ 2 ≤ 4 * (h θ) ^ 2 := by
        have hs2 : (1 : ℝ) / 4 ≤ (Real.sin (2 * θ)) ^ 2 := by nlinarith [hhalf]
        rw [show V θ = h θ / Real.sin (2 * θ) from rfl, div_pow,
          div_le_iff₀ (by positivity : (0 : ℝ) < (Real.sin (2 * θ)) ^ 2)]
        nlinarith [hs2, sq_nonneg (h θ)]
      have h2 : (V θ) ^ 2 ≤ 4 * (C₁ * Denη) := by
        have := hV2; nlinarith [hC, hC₁pos.le, hDenη_nn]
      have h4 : (0 : ℝ) ≤ 4 * (C₁ * Denη) := by
        have := hC₁pos.le; nlinarith [hDenη_nn]
      calc (V θ) ^ 2 * w θ ≤ (4 * (C₁ * Denη)) * 2 ^ γ :=
            mul_le_mul h2 hw (Real.rpow_nonneg
              (Work.FTS.H2.sin_two_nonneg_Iθ (midSet_subset_Iθ hm)) _) h4
        _ ≤ (4 * (C₁ * Denη)) * 4 := mul_le_mul_of_nonneg_left h2γle h4
        _ = 16 * C₁ * Denη := by ring
    have hInt2 : IntegrableOn (fun _ : ℝ => 16 * C₁ * Denη) (Set.Ioc midA midB) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have haux := MeasureTheory.setIntegral_mono_on hIa hInt2 measurableSet_Ioc hptV
    rw [MeasureTheory.setIntegral_const, volume_real_Ioc_mid, smul_eq_mul] at haux
    refine haux.trans ?_
    have hnn : (0 : ℝ) ≤ 16 * C₁ * Denη := by have := hC₁pos.le; nlinarith [hDenη_nn]
    nlinarith [Real.pi_le_four, hnn]
  -- ## the `m = 0` term
  have hB0 : (∫ θ in Set.Ioc midA midB, (Un 0 θ) ^ 2 * w θ) ≤ 2 ^ γ * Denη := by
    have hpt0 : ∀ θ ∈ Set.Ioc midA midB,
        (Un 0 θ) ^ 2 * w θ ≤ 2 ^ γ * ((deriv h θ) ^ 2 * wη θ) := by
      intro θ hθ
      have hm : θ ∈ midSet := ⟨le_of_lt hθ.1, hθ.2⟩
      have hle := rpow_neg_sin_two_le_mid_eta hγeta hm
      calc (Un 0 θ) ^ 2 * w θ = (deriv h θ) ^ 2 * w θ := rfl
        _ ≤ (deriv h θ) ^ 2 * (2 ^ γ * wη θ) :=
            mul_le_mul_of_nonneg_left hle (sq_nonneg _)
        _ = 2 ^ γ * ((deriv h θ) ^ 2 * wη θ) := by ring
    have hInt3 : IntegrableOn (fun θ => 2 ^ γ * ((deriv h θ) ^ 2 * wη θ))
        (Set.Ioc midA midB) :=
      (ContinuousOn.integrableOn_compact isCompact_Icc
        (continuousOn_const.mul (((continuousOn_deriv_slice hsm).pow 2).mul
          (continuousOn_rpow_neg_sin_two (Work.Spaces.eta))))).mono_set Set.Ioc_subset_Icc_self
    have h0mem : (0 : ℕ) ∈ Finset.range i := Finset.mem_range.mpr hi1
    have haux := MeasureTheory.setIntegral_mono_on (hIc 0 h0mem) hInt3 measurableSet_Ioc hpt0
    refine haux.trans ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ h2γ_nn
    have hmono : (∫ θ in Set.Ioc midA midB, (deriv h θ) ^ 2 * wη θ)
        ≤ (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * wη θ) :=
      MeasureTheory.setIntegral_mono_set hIntη
        ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall
          (fun θ hθ => mul_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _))))
        (Filter.Eventually.of_forall (fun θ (hθ : θ ∈ Set.Ioc midA midB) => midSet_subset_Iθ ⟨le_of_lt hθ.1, hθ.2⟩))
    exact hmono
  -- ## the `m ≥ 1` terms
  have hBm : ∀ m : ℕ, 1 ≤ m → m ≤ i →
      (∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ := by
    intro m hm1 hmi
    have hmI : m ∈ Finset.Icc 1 i := Finset.mem_Icc.mpr ⟨hm1, hmi⟩
    exact MeasureTheory.setIntegral_mono_set (hIntγ m hmI)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _))))
      (Filter.Eventually.of_forall (fun θ (hθ : θ ∈ Set.Ioc midA midB) => midSet_subset_Iθ ⟨le_of_lt hθ.1, hθ.2⟩))
  -- ## the sum
  have hSum : (∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ)
      ≤ (i : ℝ) * (2 ^ γ * (Denη + Dens)) := by
    have hterm : ∀ m ∈ Finset.range i,
        (∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ) ≤ 2 ^ γ * (Denη + Dens) := by
      intro m hm
      have hlt : m < i := Finset.mem_range.mp hm
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        calc (∫ θ in Set.Ioc midA midB, (Un 0 θ) ^ 2 * w θ) ≤ 2 ^ γ * Denη := hB0
          _ ≤ 2 ^ γ * (Denη + Dens) := by
              apply mul_le_mul_of_nonneg_left _ h2γ_nn
              linarith [hDens_nn]
      · have hmIcc : m ∈ Finset.Icc 1 i := Finset.mem_Icc.mpr ⟨hpos, le_of_lt hlt⟩
        have hsingle : (∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ) ≤ Dens := by
          show (∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ) ≤
            ∑ a ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ, (Un a θ) ^ 2 * w θ)
          exact Finset.single_le_sum (fun a _ => MeasureTheory.setIntegral_nonneg
            measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _)
              (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _))) hmIcc
        have hb := hBm m hpos (le_of_lt hlt)
        have hS_nn : 0 ≤ Denη + Dens := by linarith
        have hfin : Dens ≤ 2 ^ γ * (Denη + Dens) := by
          have h1 := mul_le_mul_of_nonneg_right h2γ1 hS_nn
          nlinarith [h1, hDens_nn]
        calc (∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ)
            ≤ ∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ := hb
          _ ≤ Dens := hsingle
          _ ≤ 2 ^ γ * (Denη + Dens) := hfin
    calc (∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ)
        ≤ ∑ m ∈ Finset.range i, (2 ^ γ * (Denη + Dens)) := Finset.sum_le_sum hterm
      _ = (Finset.range i).card • (2 ^ γ * (Denη + Dens)) := Finset.sum_const _
      _ = (i : ℝ) * (2 ^ γ * (Denη + Dens)) := by
          rw [Finset.card_range, nsmul_eq_mul]
  -- ## assembly
  calc (∫ θ in Set.Ioc midA midB, (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ)
      ≤ ∫ θ in Set.Ioc midA midB,
          K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ) :=
        MeasureTheory.setIntegral_mono_on hFint hΨint measurableSet_Ioc hpt
    _ = K * ((∫ θ in Set.Ioc midA midB, (V θ) ^ 2 * w θ)
          + ∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ) := hΨeq
    _ ≤ (100 * K * (C₁ + 1) + 1) * (Denη + Dens) := by
        have hS_nn : (0 : ℝ) ≤ Denη + Dens := by linarith
        have hsum : (∫ θ in Set.Ioc midA midB, (V θ) ^ 2 * w θ)
              + ∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ
            ≤ 16 * C₁ * Denη + 16 * (Denη + Dens) := by
          have h1 : (i : ℝ) * (2 ^ γ * (Denη + Dens)) ≤ 16 * (Denη + Dens) := by
            have hi4R : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
            have h3 : 2 ^ γ * (Denη + Dens) ≤ 4 * (Denη + Dens) := by
              nlinarith [h2γle, hS_nn]
            have := mul_le_mul hi4R h3 (mul_nonneg h2γ_nn hS_nn) (by norm_num)
            nlinarith [this]
          linarith [hBV, hSum, h1]
        have hbig : K * (16 * C₁ * Denη + 16 * (Denη + Dens))
            ≤ (100 * K * (C₁ + 1) + 1) * (Denη + Dens) := by
          have hC1n : (0 : ℝ) ≤ C₁ + 1 := by linarith [hC₁pos.le]
          have h16 : 16 * C₁ * Denη + 16 * (Denη + Dens) ≤ 16 * (C₁ + 1) * (Denη + Dens) := by
            nlinarith [hC₁pos.le, hDenη_nn, hDens_nn, hS_nn]
          have h100 : 16 * (C₁ + 1) * (Denη + Dens) ≤ 100 * (C₁ + 1) * (Denη + Dens) := by
            have h16le : (16 : ℝ) ≤ 100 := by norm_num
            have hprod : 0 ≤ (C₁ + 1) * (Denη + Dens) := mul_nonneg hC1n hS_nn
            nlinarith [h16le, hprod]
          calc K * (16 * C₁ * Denη + 16 * (Denη + Dens))
              ≤ K * (16 * (C₁ + 1) * (Denη + Dens)) := mul_le_mul_of_nonneg_left h16 hKpos.le
            _ ≤ K * (100 * (C₁ + 1) * (Denη + Dens)) := mul_le_mul_of_nonneg_left h100 hKpos.le
            _ ≤ (100 * K * (C₁ + 1) + 1) * (Denη + Dens) := by
                have h1 : K * (100 * (C₁ + 1) * (Denη + Dens))
                    = 100 * K * (C₁ + 1) * (Denη + Dens) := by ring
                rw [h1]
                nlinarith [hS_nn, hKpos.le, hC1n]
        exact (mul_le_mul_of_nonneg_left hsum hKpos.le).trans hbig

end Work.FTS.H2.DivQ
