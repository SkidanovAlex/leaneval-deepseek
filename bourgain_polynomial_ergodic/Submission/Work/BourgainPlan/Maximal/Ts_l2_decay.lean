import Mathlib
import Submission.Work.BourgainPlan.Maximal.Ts_prelude

/-!
# `L²` decay of the dyadic Littlewood–Paley block `T_s` (target theorem)

The statement and the whole supporting development live here; the prelude
`Submission.Work.BourgainPlan.Maximal.Ts_prelude` carries the symbol bounds, the
curve-average multiplier identity and the `L²` multiplier calculus.
-/

open MeasureTheory MeasureTheory.Measure FourierTransform Filter
open scoped ENNReal BigOperators Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.BourgainPlan.Maximal

noncomputable section

/-- A pointwise equality of `L²` classes gives an a.e. equality of their coercions. -/
private lemma lpCoeFn_eq_of_eq {X Y : Lp ℂ 2 (volume : Measure ℝ)} (h : X = Y) :
    (X : ℝ → ℂ) =ᵐ[volume] (Y : ℝ → ℂ) := by rw [h]

theorem Ts_l2_decay (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (ε : ℕ → ℂ), (∀ k : ℕ, ‖ε k‖ ≤ 1) → ∀ (s : ℤ) (h : ℝ → ℂ), MeasureTheory.MemLp h 2 MeasureTheory.volume → MeasureTheory.eLpNorm (fun x : ℝ => ∑ k ∈ Finset.range K, Work.BourgainPlan.Maximal.dyadicProj Work.BourgainPlan.Maximal.dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s) (fun y : ℝ => ε k * Work.BourgainPlan.Maximal.dyadicProj Work.BourgainPlan.Maximal.dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (Work.BourgainPlan.Maximal.dyadD P k h) y) x) 2 MeasureTheory.volume ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-(|((s : ℤ) : ℝ)|) / (P.natDegree : ℝ))) * MeasureTheory.eLpNorm h 2 MeasureTheory.volume := by
  obtain ⟨C₀, hC₀pos, hsymb⟩ := Ts_symbol_bound P hdeg
  refine ⟨C₀, hC₀pos, ?_⟩
  intro K ε hε s h hh
  classical
  obtain ⟨Bψ, hBψ0, hBψ⟩ := dyadPsi_abs_bound
  obtain ⟨Bt, hBt0, hBt⟩ := dyadTilde_abs_bound
  let L : ℕ → ℤ := fun k => (P.natDegree : ℤ) * (k : ℤ) + s
  let mS : ℕ → ℝ → ℂ := fun k ξ => (dyadPsi ((2:ℝ)^(L k) * ξ) : ℂ)
  let mT : ℕ → ℝ → ℂ := fun k ξ => (dyadTilde ((2:ℝ)^(L k) * ξ) : ℂ)
  let mu : ℕ → ℝ → ℂ := fun k => muSym P k
  let H : Lp ℂ 2 (volume : Measure ℝ) := hh.toLp
  let G : ℕ → ℝ → ℂ := fun k => fun y => ε k * dyadicProj dyadPsi (L k) (dyadD P k h) y
  -- (A) structural facts
  have hψd : HasCompactSupport dyadPsi := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-2:ℝ)) (b := 2)) ?_
    intro ξ hξ
    obtain ⟨h1, h2⟩ := dyadPsi_support hξ
    exact ⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩
  have htd : HasCompactSupport dyadTilde := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-4:ℝ)) (b := 4)) ?_
    intro ξ hξ
    have hξ' : ¬ (4 ≤ |ξ|) := fun hh4 => hξ (dyadTilde_zero hh4)
    exact ⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩
  have hψC : HasCompactSupport (fun η : ℝ => (dyadPsi η : ℂ)) :=
    hψd.comp_left (g := fun η : ℝ => (η : ℂ)) (by simp)
  have htC : HasCompactSupport (fun η : ℝ => (dyadTilde η : ℂ)) :=
    htd.comp_left (g := fun η : ℝ => (η : ℂ)) (by simp)
  have hS_cont : ∀ k, Continuous (mS k) := fun k =>
    Complex.continuous_ofReal.comp (continuous_dyadPsi.comp (continuous_const.mul continuous_id))
  have hT_cont : ∀ k, Continuous (mT k) := fun k =>
    Complex.continuous_ofReal.comp
      ((dyadTheta_spec.1.continuous.comp (continuous_id.div_const 2)).comp (continuous_const.mul continuous_id))
  have hS_memLp : ∀ k, MemLp (mS k) ⊤ (volume : Measure ℝ) := fun k =>
    memLp_top_of_bound' (hS_cont k).aestronglyMeasurable Bψ (fun ξ => by
      change ‖(dyadPsi ((2:ℝ)^(L k) * ξ) : ℂ)‖ ≤ Bψ
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hBψ _)
  have hT_memLp : ∀ k, MemLp (mT k) ⊤ (volume : Measure ℝ) := fun k =>
    memLp_top_of_bound' (hT_cont k).aestronglyMeasurable Bt (fun ξ => by
      change ‖(dyadTilde ((2:ℝ)^(L k) * ξ) : ℂ)‖ ≤ Bt
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hBt _)
  have hS_supp : ∀ k, HasCompactSupport (mS k) := fun k =>
    hasCompactSupport_comp_mul_left' hψC (zpow_ne_zero (L k) (by norm_num : (2:ℝ) ≠ 0))
  have hT_supp : ∀ k, HasCompactSupport (mT k) := fun k =>
    hasCompactSupport_comp_mul_left' htC (zpow_ne_zero (L k) (by norm_num : (2:ℝ) ≠ 0))
  have hS_int : ∀ k, Integrable (mS k) (volume : Measure ℝ) := fun k =>
    (hS_cont k).integrable_of_hasCompactSupport (hS_supp k)
  have hT_int : ∀ k, Integrable (mT k) (volume : Measure ℝ) := fun k =>
    (hT_cont k).integrable_of_hasCompactSupport (hT_supp k)
  have hMu_memLp : ∀ k, MemLp (mu k) ⊤ (volume : Measure ℝ) := fun k =>
    (memLp_star_polyProfile P (2^k)).sub (memLp_star_polyProfile P (2^(k+1)))
  have hD_memLp : ∀ k, MemLp (dyadD P k h) 2 (volume : Measure ℝ) := fun k =>
    ((curveSigma_eq_multiplier P (2^k) h hh).2).sub ((curveSigma_eq_multiplier P (2^(k+1)) h hh).2)
  -- (B) G ∈ L²
  have hG_memLp : ∀ k, MemLp (G k) 2 (volume : Measure ℝ) := by
    intro k
    by_cases hD1 : Integrable (dyadD P k h) (volume : Measure ℝ)
    · have hd := (dyadicProj_dichotomy (mS k) (hS_int k) (hS_memLp k) (dyadD P k h) (hD_memLp k)).2 hD1
      have hGae : G k =ᵐ[volume]
          (ε k • (Commons.Analysis.Fourier.BoundaryLayer.multiplier (mS k) (hS_memLp k)
            (MemLp.toLp (dyadD P k h) (hD_memLp k))) : ℝ → ℂ) := by
        show (fun y : ℝ => ε k * dyadicProj dyadPsi (L k) (dyadD P k h) y) =ᵐ[volume]
          (fun y : ℝ => ε k * ((Commons.Analysis.Fourier.BoundaryLayer.multiplier (mS k) (hS_memLp k)
            (MemLp.toLp (dyadD P k h) (hD_memLp k)) : ℝ → ℂ) y))
        exact (Filter.EventuallyEq.of_eq
          (rfl : (fun _ : ℝ => ε k) = (fun _ : ℝ => ε k))).mul hd
      exact MemLp.ae_eq hGae.symm ((Lp.memLp _).const_smul (ε k))
    · have hd := (dyadicProj_dichotomy (mS k) (hS_int k) (hS_memLp k) (dyadD P k h) (hD_memLp k)).1 hD1
      have h0 : ∀ y : ℝ, dyadicProj dyadPsi (L k) (dyadD P k h) y = 0 := fun y => congrFun hd y
      refine MemLp.ae_eq (Filter.Eventually.of_forall (fun y => ?_))
        (MeasureTheory.MemLp.zero : MemLp (fun _ : ℝ => (0:ℂ)) 2 (volume : Measure ℝ))
      show (0:ℂ) = G k y
      show (0:ℂ) = ε k * dyadicProj dyadPsi (L k) (dyadD P k h) y
      rw [h0 y, mul_zero]
  -- (C) hDmu
  have hDmu : ∀ k, MemLp.toLp (dyadD P k h) (hD_memLp k)
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier (mu k) (hMu_memLp k) H := by
    intro k
    obtain ⟨hmA, hAae⟩ := (curveSigma_eq_multiplier P (2^k) h hh).1
    obtain ⟨hmB, hBae⟩ := (curveSigma_eq_multiplier P (2^(k+1)) h hh).1
    have hAB : (curveSigma P (2^k) h - curveSigma P (2^(k+1)) h : ℝ → ℂ) =ᵐ[volume]
        ((Commons.Analysis.Fourier.BoundaryLayer.multiplier
            (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^k) ξ)) hmA H)
          - (Commons.Analysis.Fourier.BoundaryLayer.multiplier
            (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) hmB H) : ℝ → ℂ) :=
      hAae.sub hBae
    have hsub := multiplier_sub_sym (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^k) ξ))
      (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) hmA hmB (hMu_memLp k) H
    have hAB1 : dyadD P k h =ᵐ[volume]
        (Commons.Analysis.Fourier.BoundaryLayer.multiplier (mu k) (hMu_memLp k) H : ℝ → ℂ) := by
      refine hAB.trans ?_
      refine (Lp.coeFn_sub _ _).symm.trans ?_
      rw [← hsub]
      exact Filter.EventuallyEq.rfl
    apply Lp.ext (p := 2) (μ := (volume : Measure ℝ))
    filter_upwards [MemLp.coeFn_toLp (hD_memLp k), hAB1] with x e1 e2
    rw [e1, e2]
  -- (D) the good set, the symbol σ
  let good : ℕ → Prop := fun k => Integrable (dyadD P k h) (volume : Measure ℝ)
    ∧ Integrable (G k) (volume : Measure ℝ)
  let σ : ℕ → ℝ → ℂ := fun k ξ => if good k then ε k * (mS k ξ * mu k ξ) else 0
  have hSmu : ∀ k, MemLp (fun ξ : ℝ => mS k ξ * mu k ξ) ⊤ (volume : Measure ℝ) := fun k =>
    (hS_memLp k).mul (hMu_memLp k)
  have hσc : ∀ k, MemLp (fun ξ : ℝ => ε k * (mS k ξ * mu k ξ)) ⊤ (volume : Measure ℝ) := fun k =>
    (hSmu k).const_smul (ε k)
  have hσ : ∀ k, MemLp (σ k) ⊤ (volume : Measure ℝ) := by
    intro k
    by_cases hk : good k
    · have : σ k = fun ξ : ℝ => ε k * (mS k ξ * mu k ξ) := by
        funext ξ
        show (if good k then ε k * (mS k ξ * mu k ξ) else 0) = ε k * (mS k ξ * mu k ξ)
        rw [if_pos hk]
      rw [this]; exact hσc k
    · have : σ k = fun _ : ℝ => (0:ℂ) := by
        funext ξ
        show (if good k then ε k * (mS k ξ * mu k ξ) else 0) = 0
        rw [if_neg hk]
      rw [this]; exact memLp_zero_fun
  have hTS : ∀ k, MemLp (fun ξ : ℝ => mT k ξ * σ k ξ) ⊤ (volume : Measure ℝ) := fun k =>
    (hT_memLp k).mul (hσ k)
  -- (E) the block identity
  have hBlock : ∀ k, (fun x : ℝ => dyadicProj dyadTilde (L k) (G k) x) =ᵐ[volume]
      (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H : ℝ → ℂ) := by
    intro k
    by_cases hk : good k
    · have hD1 : Integrable (dyadD P k h) (volume : Measure ℝ) := hk.1
      have hG1 : Integrable (G k) (volume : Measure ℝ) := hk.2
      have hinner := (dyadicProj_dichotomy (mS k) (hS_int k) (hS_memLp k) (dyadD P k h) (hD_memLp k)).2 hD1
      have hGtoLp : MemLp.toLp (G k) (hG_memLp k)
          = ε k • (Commons.Analysis.Fourier.BoundaryLayer.multiplier (mS k) (hS_memLp k)
              (MemLp.toLp (dyadD P k h) (hD_memLp k))) := by
        have hae : G k =ᵐ[volume]
            (ε k • (Commons.Analysis.Fourier.BoundaryLayer.multiplier (mS k) (hS_memLp k)
              (MemLp.toLp (dyadD P k h) (hD_memLp k))) : ℝ → ℂ) := by
          show (fun y : ℝ => ε k * dyadicProj dyadPsi (L k) (dyadD P k h) y) =ᵐ[volume]
            (fun y : ℝ => ε k * ((Commons.Analysis.Fourier.BoundaryLayer.multiplier (mS k) (hS_memLp k)
              (MemLp.toLp (dyadD P k h) (hD_memLp k)) : ℝ → ℂ) y))
          exact (Filter.EventuallyEq.of_eq
            (rfl : (fun _ : ℝ => ε k) = (fun _ : ℝ => ε k))).mul hinner
        calc MemLp.toLp (G k) (hG_memLp k)
            = MemLp.toLp (ε k • (Commons.Analysis.Fourier.BoundaryLayer.multiplier (mS k) (hS_memLp k)
                (MemLp.toLp (dyadD P k h) (hD_memLp k)) : ℝ → ℂ))
                ((Lp.memLp _).const_smul (ε k)) :=
              MemLp.toLp_congr (hG_memLp k) ((Lp.memLp _).const_smul (ε k)) hae
          _ = ε k • MemLp.toLp (Commons.Analysis.Fourier.BoundaryLayer.multiplier (mS k) (hS_memLp k)
                (MemLp.toLp (dyadD P k h) (hD_memLp k)) : ℝ → ℂ) (Lp.memLp _) :=
              MemLp.toLp_const_smul (ε k) (Lp.memLp _)
          _ = ε k • (Commons.Analysis.Fourier.BoundaryLayer.multiplier (mS k) (hS_memLp k)
                (MemLp.toLp (dyadD P k h) (hD_memLp k))) := by rw [Lp.toLp_coeFn]
      have hGchain : MemLp.toLp (G k) (hG_memLp k)
          = Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H := by
        rw [hGtoLp, hDmu k]
        rw [multiplier_mul (mS k) (mu k) (hS_memLp k) (hMu_memLp k) (hSmu k) H]
        rw [(multiplier_const_smul (ε k) (fun ξ : ℝ => mS k ξ * mu k ξ) (hSmu k) (hσc k) H).symm]
        exact multiplier_congr (by
          funext ξ
          show ε k * (mS k ξ * mu k ξ) = (if good k then ε k * (mS k ξ * mu k ξ) else 0)
          rw [if_pos hk]) (hσc k) (hσ k) H
      have houter := (dyadicProj_dichotomy (mT k) (hT_int k) (hT_memLp k) (G k) (hG_memLp k)).2 hG1
      have hstep1 : Commons.Analysis.Fourier.BoundaryLayer.multiplier (mT k) (hT_memLp k)
            (MemLp.toLp (G k) (hG_memLp k))
          = Commons.Analysis.Fourier.BoundaryLayer.multiplier (mT k) (hT_memLp k)
            (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H) := by rw [hGchain]
      have hstep2 : Commons.Analysis.Fourier.BoundaryLayer.multiplier (mT k) (hT_memLp k)
            (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H)
          = Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun ξ : ℝ => mT k ξ * σ k ξ) (hTS k) H :=
        multiplier_mul (mT k) (σ k) (hT_memLp k) (hσ k) (hTS k) H
      have hstep3 : Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun ξ : ℝ => mT k ξ * σ k ξ) (hTS k) H
          = Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H := by
        refine multiplier_congr ?_ (hTS k) (hσ k) H
        funext ξ
        by_cases hk' : good k
        · have hσξ : σ k ξ = ε k * (mS k ξ * mu k ξ) := by
            show (if good k then ε k * (mS k ξ * mu k ξ) else 0) = ε k * (mS k ξ * mu k ξ)
            rw [if_pos hk']
          rw [hσξ]
          have hmTξ : mT k ξ = 1 ∨ mS k ξ = 0 := by
            by_cases hz : mS k ξ = 0
            · exact Or.inr hz
            · refine Or.inl ?_
              have hψne : dyadPsi ((2:ℝ)^(L k) * ξ) ≠ 0 := fun h => hz (by
                show (dyadPsi ((2:ℝ)^(L k) * ξ) : ℂ) = 0; rw [h]; simp)
              have habs := (dyadPsi_support hψne).2
              show (dyadTilde ((2:ℝ)^(L k) * ξ) : ℂ) = 1
              rw [dyadTilde_one habs]; simp
          rcases hmTξ with h1 | h0
          · rw [h1, one_mul]
          · rw [h0]; ring
        · have hσξ : σ k ξ = 0 := by
            show (if good k then ε k * (mS k ξ * mu k ξ) else 0) = 0
            rw [if_neg hk']
          rw [hσξ, mul_zero]
      exact (Filter.EventuallyEq.of_eq (show (fun x : ℝ => dyadicProj dyadTilde (L k) (G k) x)
          = (fun x : ℝ => 𝓕⁻ (fun ξ : ℝ => mT k ξ * 𝓕 (G k) ξ) x) from rfl)).trans
        (houter.trans (lpCoeFn_eq_of_eq (hstep1.trans (hstep2.trans hstep3))))
    · have hσ0 : σ k = fun _ : ℝ => (0:ℂ) := by
        funext ξ
        show (if good k then ε k * (mS k ξ * mu k ξ) else 0) = 0
        rw [if_neg hk]
      have hmult0 : Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H = 0 := by
        rw [multiplier_congr hσ0 (hσ k) memLp_zero_fun H]
        exact multiplier_zero H
      have hLHS0 : (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H : ℝ → ℂ)
          =ᵐ[volume] fun _ : ℝ => (0:ℂ) := by
        rw [hmult0]
        exact Lp.coeFn_zero ℂ (p := 2) (μ := (volume : Measure ℝ))
      have hRHS0 : (fun x : ℝ => dyadicProj dyadTilde (L k) (G k) x) =ᵐ[volume] fun _ : ℝ => (0:ℂ) := by
        by_cases hG1 : Integrable (G k) (volume : Measure ℝ)
        · have hD1 : ¬ Integrable (dyadD P k h) (volume : Measure ℝ) := fun hD1 => hk ⟨hD1, hG1⟩
          have hinner0 := (dyadicProj_dichotomy (mS k) (hS_int k) (hS_memLp k) (dyadD P k h) (hD_memLp k)).1 hD1
          have hG0 : G k = fun _ : ℝ => (0:ℂ) := by
            funext y
            show ε k * dyadicProj dyadPsi (L k) (dyadD P k h) y = 0
            rw [show dyadicProj dyadPsi (L k) (dyadD P k h) y = 0 from congrFun hinner0 y]
            simp
          have hGtoLp0 : MemLp.toLp (G k) (hG_memLp k) = 0 := by
            apply Lp.ext (p := 2) (μ := (volume : Measure ℝ))
            filter_upwards [MemLp.coeFn_toLp (hG_memLp k),
              Lp.coeFn_zero ℂ (p := 2) (μ := (volume : Measure ℝ))] with x e1 e2
            rw [e1, e2]
            exact congrFun hG0 x
          have houter := (dyadicProj_dichotomy (mT k) (hT_int k) (hT_memLp k) (G k) (hG_memLp k)).2 hG1
          rw [hGtoLp0, multiplier_Lpzero] at houter
          exact houter.trans (Lp.coeFn_zero ℂ (p := 2) (μ := (volume : Measure ℝ)))
        · have houter := (dyadicProj_dichotomy (mT k) (hT_int k) (hT_memLp k) (G k) (hG_memLp k)).1 hG1
          exact Filter.EventuallyEq.of_eq houter
      exact hRHS0.trans hLHS0.symm
  -- (F) assembly
  have hSumAe : (fun x : ℝ => ∑ k ∈ Finset.range K, dyadicProj dyadTilde (L k) (G k) x) =ᵐ[volume]
      (Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (fun ξ : ℝ => ∑ k ∈ Finset.range K, σ k ξ) (memLpSum_top (Finset.range K) σ hσ) H : ℝ → ℂ) := by
    have h1 : (fun x : ℝ => ∑ k ∈ Finset.range K, dyadicProj dyadTilde (L k) (G k) x)
        = (∑ k ∈ Finset.range K, (fun x : ℝ => dyadicProj dyadTilde (L k) (G k) x)) := by
      funext x
      exact (Finset.sum_apply x (Finset.range K)
        (fun k => fun x => dyadicProj dyadTilde (L k) (G k) x)).symm
    rw [h1]
    refine (ae_eq_finset_sum (Finset.range K)
        (fun k => fun x : ℝ => dyadicProj dyadTilde (L k) (G k) x)
        (fun k => (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H : ℝ → ℂ))
        (fun k _ => hBlock k)).trans ?_
    rw [← multiplier_sum (Finset.range K) σ hσ H]
    have h2 : (∑ i ∈ Finset.range K,
          (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ i) (hσ i) H : ℝ → ℂ))
        = (fun x => ∑ i ∈ Finset.range K,
          (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ i) (hσ i) H : ℝ → ℂ) x) := by
      funext x
      exact (Finset.sum_apply x (Finset.range K)
        (fun i => (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ i) (hσ i) H : ℝ → ℂ)))
    rw [h2]
    exact (Lp.coeFn_fun_finsetSum (Finset.range K)
      (fun k => Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H)).symm
  have hsym : ∀ ξ : ℝ, ‖∑ k ∈ Finset.range K, σ k ξ‖
      ≤ C₀ * (2:ℝ) ^ (-(|((s:ℤ):ℝ)|) / (P.natDegree:ℝ)) := by
    intro ξ
    have h := hsymb K (fun k => if good k then ε k else 0) (fun k => by
      by_cases hk : good k
      · rw [if_pos hk]; exact hε k
      · rw [if_neg hk]; simp) s ξ
    have hsum_eq : ∑ k ∈ Finset.range K, σ k ξ = ∑ k ∈ Finset.range K,
        (if good k then ε k else (0:ℂ)) * (dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) : ℂ)
          * (starRingEnd ℂ (polyProfile P (2^k) ξ) - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hg : good k
      · have hσξ : σ k ξ = ε k * (mS k ξ * mu k ξ) := by
          show (if good k then ε k * (mS k ξ * mu k ξ) else 0) = ε k * (mS k ξ * mu k ξ)
          rw [if_pos hg]
        rw [hσξ, if_pos hg,
          show mS k ξ = (dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) : ℂ) from rfl,
          show mu k ξ = starRingEnd ℂ (polyProfile P (2^k) ξ)
            - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ) from rfl]
        ring
      · have hσξ : σ k ξ = 0 := by
          show (if good k then ε k * (mS k ξ * mu k ξ) else 0) = 0
          rw [if_neg hg]
        rw [hσξ, if_neg hg]
        ring
    rw [hsum_eq]
    exact h
  show MeasureTheory.eLpNorm (fun x : ℝ => ∑ k ∈ Finset.range K, dyadicProj dyadTilde (L k) (G k) x) 2 MeasureTheory.volume
      ≤ ENNReal.ofReal (C₀ * (2 : ℝ) ^ (-(|((s : ℤ) : ℝ)|) / (P.natDegree : ℝ))) * MeasureTheory.eLpNorm h 2 MeasureTheory.volume
  calc MeasureTheory.eLpNorm (fun x : ℝ => ∑ k ∈ Finset.range K, dyadicProj dyadTilde (L k) (G k) x) 2 MeasureTheory.volume
      = MeasureTheory.eLpNorm (Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (fun ξ : ℝ => ∑ k ∈ Finset.range K, σ k ξ) (memLpSum_top (Finset.range K) σ hσ) H) 2 MeasureTheory.volume :=
        eLpNorm_congr_ae hSumAe
    _ ≤ ENNReal.ofReal (C₀ * (2 : ℝ) ^ (-(|((s : ℤ) : ℝ)|) / (P.natDegree : ℝ)))
          * MeasureTheory.eLpNorm H 2 MeasureTheory.volume :=
        eLpNorm_multiplier_le (fun ξ : ℝ => ∑ k ∈ Finset.range K, σ k ξ)
          (memLpSum_top (Finset.range K) σ hσ)
          (C₀ * (2 : ℝ) ^ (-(|((s : ℤ) : ℝ)|) / (P.natDegree : ℝ))) hsym H
    _ = ENNReal.ofReal (C₀ * (2 : ℝ) ^ (-(|((s : ℤ) : ℝ)|) / (P.natDegree : ℝ)))
          * MeasureTheory.eLpNorm h 2 MeasureTheory.volume := by
        rw [show MeasureTheory.eLpNorm H 2 (volume : Measure ℝ)
            = MeasureTheory.eLpNorm h 2 (volume : Measure ℝ) from eLpNorm_congr_ae hh.coeFn_toLp]


end

end Work.BourgainPlan.Maximal
