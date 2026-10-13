import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.CmodeDecay
import Submission.Work.FTS.PhiStar.FlatWAux.eFamSupBound
import Submission.Work.FTS.PhiStar.FlatWAux.QmDerivBound
import Submission.Work.FTS.PhiStar.FlatW_psiDiv
import Submission.Work.FTS.PhiStar.FlatWAux.AngDeriv
import Submission.Work.FTS.PhiStar.FlatWAux.Linv_lop
import Submission.Work.FTS.PhiStar.FlatWAux.PsiExpansion
import Submission.Work.FTS.PhiStar.FlatWAux.WtBound
import Submission.Work.FTS.PhiStar.FlatWAux.ChiaBasic
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.BmodeExpansionSelf
import Submission.Work.FTS.PhiStar.LinvFlat.LinvBaseBound
import Submission.Work.FTS.PhiStar.LinvFlat.LinvLopAux
import Submission.Work.FTS.PhiStar.LinvFlat.Linv_contDiffOn_hasDerivAt
import Submission.Work.FTS.PhiStar.LinvFlat.Lop_iter_sin_cos_bound
import Submission.Work.FTS.PhiStar.AngU.WtBoundU
import Submission.Work.FTS.PhiStar.AngU.chia_base_boundU
import Submission.Work.FTS.PhiStar.AngU.Linv_iter_uniform
import Submission.Work.FTS.PhiStar.AngU.Wt_differentiableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open scoped Real Topology BigOperators ContDiff
open MeasureTheory Set Filter

set_option maxHeartbeats 3200000

/-- `sin (2θ) ≠ 0` on the open angular interval. -/
lemma s2_ne_zero_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.s2 θ ≠ 0 := by
  have h : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  simpa [Work.Construction.s2] using ne_of_gt h

/-- The angular model is `C^n` on the open interval for every `n`. -/
lemma angModel_contDiffOn {α : ℝ} {ψ : ℝ → ℝ} (h : Work.FTS.PhiStar.AngModel α ψ) (n : ℕ) :
    ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)) :=
  h.smooth.of_le (by
    rw [show Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞) from rfl]
    exact_mod_cast le_top)

/-- A global bound for the `Lop`-iterates of `sin (2θ)` up to order `6`. -/
lemma lopIter_s2_global : ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℕ, r ≤ 6 →
    ∀ θ : ℝ, |(Work.Spaces.Lop^[r]) Work.Construction.s2 θ| ≤ M := by
  have hTP : ∀ r : ℕ, Work.FTS.PhiStar.LinvFlat.LopTrig.TP
      ((Work.Spaces.Lop^[r]) (fun θ : ℝ => Real.sin (2 * θ))) := by
    intro r
    induction r with
    | zero => simpa using Work.FTS.PhiStar.LinvFlat.LopTrig.TP.sin2
    | succ r ih =>
        rw [Function.iterate_succ_apply']
        exact Work.FTS.PhiStar.LinvFlat.LopTrig.TP_lop ih
  choose B hB using fun r => Work.FTS.PhiStar.LinvFlat.LopTrig.TP_bdd (hTP r)
  refine ⟨∑ r ∈ Finset.range 7, B r, Finset.sum_nonneg (fun r _ => (hB r).1), ?_⟩
  intro r hr θ
  have h1 : |(Work.Spaces.Lop^[r]) (fun θ : ℝ => Real.sin (2 * θ)) θ| ≤ B r := (hB r).2 θ
  have h2 : B r ≤ ∑ s ∈ Finset.range 7, B s :=
    Finset.single_le_sum (fun i _ => (hB i).1) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  exact le_trans h1 h2

/-- Unpacking `FlatW 7` for a `θ`-only function: bounds on the function and on the
`Lop`-iterates of its derivative. -/
lemma flatW_zindep_unpack {g : ℝ → ℝ} {C : ℝ}
    (hf : Work.FTS.VocabO2.FlatW 7 (fun _ θ => g θ) C) :
    (∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |g θ| ≤ C) ∧
    (∀ i : ℕ, i ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |(Work.Spaces.Lop^[i]) (deriv g) θ| ≤ C) := by
  constructor
  · intro θ hθ
    have h := (hf 1 θ one_pos hθ.1 hθ.2).1 0 (by norm_num)
    simpa using h
  · intro i hi θ hθ
    have h := (hf 1 θ one_pos hθ.1 hθ.2).2 0 i (by omega)
    simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero] at h
    have h2 : (Work.Spaces.DthIter i (Work.Spaces.pth (fun _ θ' => g θ'))) 1 θ
        = (Work.Spaces.Lop^[i]) (deriv g) θ :=
      congrFun (Work.Spaces.DthIter_eq_iterate_Lop i
        (Work.Spaces.pth (fun _ θ' => g θ')) 1) θ
    rwa [h2] at h

theorem AngBoundU : ∃ Kw : ℕ → ℝ, ∃ Kc : ℕ → ℕ → ℝ,
    (∀ j : ℕ, 0 ≤ Kw j) ∧ (∀ j i : ℕ, 0 ≤ Kc j i) ∧
    (∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ →
      (∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J → ∀ θ : ℝ,
        θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.FlatWAux.Wt ψ j θ| ≤ Kw j) ∧
      (∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J → ∀ i : ℕ, i ≤ 6 → ∀ θ : ℝ,
        θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ| ≤ Kc j i)) := by
  -- ########################################################################
  -- ### 1. the universal data (independent of `α` and of `ψ`)
  -- ########################################################################
  obtain ⟨Cd, hCd, hdecAll⟩ := Work.FTS.PhiStar.Series.CmodeDecay
  obtain ⟨Cg, hCg, hgrAll⟩ := eFamSupBound
  obtain ⟨CQ, hCQnn, hQAll⟩ := QmDerivBound
  obtain ⟨Cf, hCf, hflatAll⟩ := FlatW_psiDiv
  obtain ⟨Ms, hMs0, hMsGlob⟩ := lopIter_s2_global
  obtain ⟨Kw, hKw0, hKwU⟩ := AngU.WtBoundU Cd (CQ 0) Cf hCd.le (hCQnn 0) hCf.le
  obtain ⟨B0, hB00, hB0U⟩ := AngU.chia_base_boundU Cf Ms hCf.le hMs0
  obtain ⟨CL, hCL0, hLinvU⟩ := AngU.Linv_iter_uniform
  -- ########################################################################
  -- ### 2. the recursion defining the angular constants `A j i` (`Kc = A`)
  -- ########################################################################
  let Wbd : (ℕ → ℝ) → ℕ → ℝ := fun prev d =>
    ∑ b ∈ Finset.range (d + 1), (d.choose b : ℝ) * Ms *
      (CL (d - b) * (4 * ∑ n ∈ Finset.range 7, |prev n|))
  let stepF : ℕ → (ℕ → ℝ) → ℕ → ℝ := fun j prev i =>
    ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) * Ms *
      (if i - a = 0 then Kw (j + 1) else Wbd prev (i - a - 1))
  let A : ℕ → ℕ → ℝ := fun j => Nat.rec B0 (fun j prev => stepF j prev) j
  have A_zero : A 0 = B0 := rfl
  have A_succ : ∀ j : ℕ, A (j + 1) = stepF j (A j) := fun j => rfl
  have hWbd0 : ∀ (prev : ℕ → ℝ) (d : ℕ), 0 ≤ Wbd prev d := by
    intro prev d
    dsimp only [Wbd]
    refine Finset.sum_nonneg (fun b _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hMs0) ?_
    exact mul_nonneg (hCL0 _) (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun n _ => abs_nonneg _)))
  have hA0 : ∀ j i : ℕ, 0 ≤ A j i := by
    intro j
    induction j with
    | zero => intro i; rw [A_zero]; exact hB00 i
    | succ j _ =>
        intro i
        rw [A_succ]
        dsimp only [stepF]
        refine Finset.sum_nonneg (fun a _ => ?_)
        refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hMs0) ?_
        by_cases h : i - a = 0
        · rw [if_pos h]; exact hKw0 (j + 1)
        · rw [if_neg h]; exact hWbd0 (A j) (i - a - 1)
  -- ########################################################################
  -- ### 3. the induction on the level `j`
  -- ########################################################################
  have master : ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 →
      Work.FTS.PhiStar.AngModel α ψ →
      ∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J →
        ((∀ i : ℕ, i ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
            |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ| ≤ A j i) ∧
          ContDiffOn ℝ 9 (Work.FTS.PhiStar.FlatWAux.chia ψ j) (Set.Ioo 0 (Real.pi / 2))) := by
    intro α ψ hα hα5 hang
    -- the angular-model data
    have hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)) :=
      angModel_contDiffOn hang
    have hcontIoo : ContinuousOn ψ (Set.Ioo 0 (Real.pi / 2)) := (hsm 0).continuousOn
    have hbddψ : ∃ M : ℝ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ| ≤ M := by
      obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hang.cont
      exact ⟨M, fun θ hθ => by
        have h := hM θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
        simpa [Real.norm_eq_abs] using h⟩
    have hdecψ : ∀ m : ℕ, 1 ≤ m → |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
      intro m hm
      rw [Work.FTS.PhiStar.Series.bmode_eq_cmode m ψ 0]
      exact hdecAll α ψ hα hα5 hang m hm
    have hflatψ : Work.FTS.VocabO2.FlatW 7 (fun z θ => ψ θ / Work.Construction.s2 θ) Cf :=
      hflatAll α ψ hα (by linarith) hang
    have hWb : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |ψ θ / Work.Construction.s2 θ| ≤ Cf := (flatW_zindep_unpack hflatψ).1
    have hWb' : ∀ d : ℕ, d ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[d]) (deriv (fun θ' => ψ θ' / Work.Construction.s2 θ')) θ| ≤ Cf :=
      (flatW_zindep_unpack hflatψ).2
    have hQ0ψ : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ θ : ℝ,
        θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.FlatWAux.Qm m θ| ≤ C * (2 * (m : ℝ) + 1) ^ 2 := by
      refine ⟨CQ 0 + 1, by linarith [hCQnn 0], fun m hm θ hθ => ?_⟩
      have h := hQAll m hm 0 (by norm_num) θ hθ
      rw [iteratedDeriv_zero] at h
      have h2 : (2 * (m : ℝ) + 1) ^ (2 * 0 + 2) = (2 * (m : ℝ) + 1) ^ 2 := by norm_num
      rw [h2] at h
      have hnn : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 2 := by positivity
      calc |Work.FTS.PhiStar.FlatWAux.Qm m θ| ≤ CQ 0 * (2 * (m : ℝ) + 1) ^ 2 := h
        _ ≤ (CQ 0 + 1) * (2 * (m : ℝ) + 1) ^ 2 := by nlinarith [hnn]
    have hQ0ψ' : ∀ m : ℕ, 1 ≤ m → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.FlatWAux.Qm m θ| ≤ CQ 0 * (2 * (m : ℝ) + 1) ^ 2 := by
      intro m hm θ hθ
      have h := hQAll m hm 0 (by norm_num) θ hθ
      rw [iteratedDeriv_zero] at h
      have h2 : (2 * (m : ℝ) + 1) ^ (2 * 0 + 2) = (2 * (m : ℝ) + 1) ^ 2 := by norm_num
      rwa [h2] at h
    have hL : ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.Linv (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ') y|
        ≤ K * (Work.FTS.PhiStar.Gegenbauer.lam m * (2 * (m : ℝ) + 1)) :=
      exists_linv_lam_eFam_bound ⟨Cg, hCg, hgrAll⟩
    have hexp : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ :=
      MomentChiaAux.BmodeExpansionSelf ψ ⟨Cd, hCd, hdecψ⟩ ⟨Cg, hCg, hgrAll⟩ hcontIoo hbddψ
        hang.moment
    have hIntψ : MeasureTheory.IntegrableOn (fun θ : ℝ => ψ θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ := by
      have hc : ContinuousOn (fun θ : ℝ => ψ θ * Work.Elliptic.sinCos2 θ)
          (Set.Icc 0 (Real.pi / 2)) :=
        hang.cont.mul (by
          show ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
            (Set.Icc 0 (Real.pi / 2))
          fun_prop)
      exact hc.integrableOn_Icc
    have hchia0_eq : Set.EqOn (Work.FTS.PhiStar.FlatWAux.chia ψ 0) ψ Work.Spaces.Iθ := by
      intro θ hθ
      have hIcc : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hθ
      rcases eq_or_lt_of_le hIcc.1 with h0 | h0
      · subst h0
        have hs : Work.Construction.s2 0 = 0 := by
          rw [Work.Construction.s2_eq]
          norm_num
        simp only [Work.FTS.PhiStar.FlatWAux.chia, Work.FTS.PhiStar.FlatWAux.Wt_zero]
        rw [hs]
        simp [hang.bdry0]
      rcases eq_or_lt_of_le hIcc.2 with h2 | h2
      · subst h2
        have hs : Work.Construction.s2 (Real.pi / 2) = 0 := by
          rw [Work.Construction.s2_eq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        simp only [Work.FTS.PhiStar.FlatWAux.chia, Work.FTS.PhiStar.FlatWAux.Wt_zero]
        rw [hs]
        simp [hang.bdry1]
      · exact chia_zero (s2_ne_zero_of_mem_Ioo ⟨h0, h2⟩)
    have hCB := ChiaBasic ψ ⟨Cd, hCd, hdecψ⟩ ⟨Cg, hCg, hgrAll⟩ ⟨CQ, hCQnn, hQAll⟩
    -- the induction on the level
    have key : ∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J →
        ((∀ i : ℕ, i ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
            |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ| ≤ A j i) ∧
          ContDiffOn ℝ 9 (Work.FTS.PhiStar.FlatWAux.chia ψ j) (Set.Ioo 0 (Real.pi / 2))) := by
      intro j
      induction j with
      | zero =>
          intro _
          refine ⟨?_, ?_⟩
          · intro i hi θ hθ
            have h := hB0U ψ hsm hWb hWb' hMsGlob i hi θ hθ
            rwa [A_zero]
          · exact (hsm 9).congr (fun θ hθ => chia_zero (s2_ne_zero_of_mem_Ioo hθ))
      | succ j ih =>
          intro hj
          obtain ⟨ihb, ihs⟩ := ih (by omega)
          -- integrability and the vanishing moment of `chia ψ j`
          have hintj : MeasureTheory.IntegrableOn
              (fun θ : ℝ => Work.FTS.PhiStar.FlatWAux.chia ψ j θ * Work.Elliptic.sinCos2 θ)
              Work.Spaces.Iθ := by
            rcases Nat.eq_zero_or_pos j with h0 | h0
            · subst h0
              refine hIntψ.congr_fun (fun θ hθ => by rw [hchia0_eq (x := θ) hθ]) measurableSet_Icc
            · exact hCB.2.2.1 j h0 (by omega)
          have hmomj : (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.FlatWAux.chia ψ j θ * Work.Elliptic.sinCos2 θ) = 0 := by
            rcases Nat.eq_zero_or_pos j with h0 | h0
            · subst h0
              show (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
                  Work.FTS.PhiStar.FlatWAux.chia ψ 0 θ * Work.Elliptic.sinCos2 θ) = 0
              rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc
                (fun θ hθ => by rw [hchia0_eq (x := θ) hθ])]
              exact hang.moment
            · exact hCB.2.2.2 j h0 (by omega)
          -- the explicit bound `Dj` on `chia ψ j` and its iterates
          let Dj : ℝ := ∑ n ∈ Finset.range 7, |A j n|
          have hDj0 : 0 ≤ Dj := by
            show (0 : ℝ) ≤ ∑ n ∈ Finset.range 7, |A j n|
            exact Finset.sum_nonneg (fun n _ => abs_nonneg _)
          have hbDj : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
              |Work.FTS.PhiStar.FlatWAux.chia ψ j θ| ≤ Dj := by
            intro θ hθ
            have h0 := ihb 0 (by norm_num) θ hθ
            simp only [Function.iterate_zero_apply] at h0
            have hA0j : (0 : ℝ) ≤ A j 0 := hA0 j 0
            show |Work.FTS.PhiStar.FlatWAux.chia ψ j θ| ≤ ∑ n ∈ Finset.range 7, |A j n|
            calc |Work.FTS.PhiStar.FlatWAux.chia ψ j θ| ≤ A j 0 := h0
              _ = |A j 0| := (abs_of_nonneg hA0j).symm
              _ ≤ ∑ n ∈ Finset.range 7, |A j n| :=
                  Finset.single_le_sum (f := fun n => |A j n|) (fun n _ => abs_nonneg _)
                    (Finset.mem_range.mpr (by norm_num))
          have hiterDj : ∀ a : ℕ, a ≤ 4 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
              |(Work.Spaces.Lop^[a]) (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ| ≤ 4 * Dj := by
            intro a ha θ hθ
            have h := ihb a (by omega) θ hθ
            have h1 : A j a ≤ ∑ n ∈ Finset.range 7, |A j n| :=
              le_trans (le_abs_self _) (Finset.single_le_sum (f := fun n => |A j n|)
                (fun n _ => abs_nonneg _) (Finset.mem_range.mpr (by omega)))
            linarith
          have hLinvDj : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
              |Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ| ≤ 4 * Dj :=
            Work.FTS.PhiStar.LinvFlat.LI_lc_abs_le _ Dj hDj0 hbDj hintj hmomj
          -- the smoothness chain for the level `j+1`
          have hWtdiff : DifferentiableOn ℝ (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1))
              (Set.Ioo 0 (Real.pi / 2)) :=
            AngU.Wt_differentiableOn ψ (j + 1) (by omega) ⟨Cd, hCd, hdecψ⟩
              ⟨Cg, hCg, hgrAll⟩ hQ0ψ hL
          have hLinv9 : ContDiffOn ℝ 9
              (Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j))
              (Set.Ioo 0 (Real.pi / 2)) :=
            (Work.FTS.PhiStar.LinvFlat.Linv_contDiffOn_hasDerivAt
              (h := Work.FTS.PhiStar.FlatWAux.chia ψ j) (n := 9) (by norm_num) ihs hintj).1
          have hderivWt : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
              deriv (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1)) θ
                = Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ :=
            fun θ hθ => AngDeriv ψ ⟨Cd, hCd, hdecψ⟩ ⟨Cg, hCg, hgrAll⟩ ⟨CQ, hCQnn, hQAll⟩
              hcontIoo hbddψ hang.moment hexp (j + 1) (by omega) (by omega) θ hθ
          have hWt9 : ContDiffOn ℝ 9 (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1))
              (Set.Ioo 0 (Real.pi / 2)) := by
            have hcast : (((9 : ℕ)) : ℕ∞ω) + 1 = (10 : ℕ∞ω) := by norm_num
            have hmain : ContDiffOn ℝ ((((9 : ℕ)) : ℕ∞ω) + 1)
                (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1)) (Set.Ioo 0 (Real.pi / 2)) :=
              (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
                (f := Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1))
                (s := Set.Ioo 0 (Real.pi / 2)) (n := (((9 : ℕ)) : ℕ∞ω)) isOpen_Ioo).mpr
                ⟨hWtdiff, (fun hc => absurd hc WithTop.coe_ne_top),
                  hLinv9.congr (fun θ hθ => hderivWt θ hθ)⟩
            rw [hcast] at hmain
            exact hmain.of_le (by exact_mod_cast (by norm_num : (9 : ℕ) ≤ 10))
          have hchia9 : ContDiffOn ℝ 9 (Work.FTS.PhiStar.FlatWAux.chia ψ (j + 1))
              (Set.Ioo 0 (Real.pi / 2)) := by
            have h := (by fun_prop : ContDiffOn ℝ 9 (fun θ : ℝ => Real.sin (2 * θ))
                (Set.Ioo 0 (Real.pi / 2))).mul hWt9
            show ContDiffOn ℝ 9 (fun θ : ℝ => Work.Construction.s2 θ
              * Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1) θ) (Set.Ioo 0 (Real.pi / 2))
            exact h
          -- the bounds at the level `j+1`
          have hWtbd : ∀ e : ℕ, e ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
              |(Work.Spaces.Lop^[e]) (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1)) θ|
                ≤ (if e = 0 then Kw (j + 1) else Wbd (A j) (e - 1)) := by
            intro e he θ hθ
            rcases Nat.eq_zero_or_pos e with h0 | h0
            · subst h0
              rw [if_pos rfl]
              exact hKwU ψ hdecψ hQ0ψ' hflatψ (j + 1) (by omega) θ hθ
            · rw [if_neg (by omega)]
              -- `Lop (Wt ψ (j+1)) = s2 · Linv (chia ψ j)` on the interval
              have heq : Set.EqOn (Work.Spaces.Lop (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1)))
                  (fun θ' : ℝ => Work.Construction.s2 θ'
                    * Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ')
                  (Set.Ioo 0 (Real.pi / 2)) := by
                intro θ' hθ'
                show Real.sin (2 * θ') * deriv (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1)) θ'
                  = Work.Construction.s2 θ'
                    * Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ'
                rw [hderivWt θ' hθ']
                rfl
              have hstep : (Work.Spaces.Lop^[e]) (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1)) θ
                  = (Work.Spaces.Lop^[e - 1])
                      (fun θ' : ℝ => Work.Construction.s2 θ'
                        * Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ') θ := by
                rw [show e = (e - 1) + 1 by omega, Function.iterate_succ_apply]
                exact Work.FTS.PhiStar.LinvFlat.LI_Lop_iter_congr_eqOn isOpen_Ioo (e - 1) heq hθ
              have hleib2 : (Work.Spaces.Lop^[e - 1])
                    (fun θ' : ℝ => Work.Construction.s2 θ'
                      * Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j) θ') θ
                  = ∑ b ∈ Finset.range ((e - 1) + 1), ((e - 1).choose b : ℝ) *
                      ((Work.Spaces.Lop^[b]) (fun θ' : ℝ => Real.sin (2 * θ')) θ *
                        (Work.Spaces.Lop^[e - 1 - b])
                          (Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j)) θ) :=
                (Work.FTS.PhiStar.LinvFlat.LI_Lop_iter_mul_eqOn_9
                  (u := fun θ' : ℝ => Real.sin (2 * θ'))
                  (v := Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j))
                  isOpen_Ioo (by fun_prop) hLinv9 (e - 1) (by omega)) hθ
              rw [hstep, hleib2]
              have hbd : ∀ b ∈ Finset.range ((e - 1) + 1),
                  |((e - 1).choose b : ℝ) *
                    ((Work.Spaces.Lop^[b]) (fun θ' : ℝ => Real.sin (2 * θ')) θ *
                      (Work.Spaces.Lop^[e - 1 - b])
                        (Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j)) θ)|
                  ≤ ((e - 1).choose b : ℝ) * Ms * (CL (e - 1 - b) * (4 * Dj)) := by
                intro b hb
                have hb' : b ≤ e - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
                have hMsa : |(Work.Spaces.Lop^[b]) (fun θ' : ℝ => Real.sin (2 * θ')) θ| ≤ Ms :=
                  hMsGlob b (by omega) θ
                have hLv := hLinvU (Work.FTS.PhiStar.FlatWAux.chia ψ j) (4 * Dj)
                  (by linarith [hDj0]) hiterDj hLinvDj ihs hintj hmomj (e - 1 - b) (by omega) θ hθ
                rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
                have h1 : |(Work.Spaces.Lop^[b]) (fun θ' : ℝ => Real.sin (2 * θ')) θ|
                      * |(Work.Spaces.Lop^[e - 1 - b])
                          (Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j)) θ|
                    ≤ Ms * (CL (e - 1 - b) * (4 * Dj)) :=
                  mul_le_mul hMsa hLv (abs_nonneg _) hMs0
                calc ((e - 1).choose b : ℝ) *
                      (|(Work.Spaces.Lop^[b]) (fun θ' : ℝ => Real.sin (2 * θ')) θ|
                        * |(Work.Spaces.Lop^[e - 1 - b])
                            (Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j)) θ|)
                    ≤ ((e - 1).choose b : ℝ) * (Ms * (CL (e - 1 - b) * (4 * Dj))) :=
                      mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
                  _ = ((e - 1).choose b : ℝ) * Ms * (CL (e - 1 - b) * (4 * Dj)) := by ring
              show |∑ b ∈ Finset.range ((e - 1) + 1), ((e - 1).choose b : ℝ) *
                    ((Work.Spaces.Lop^[b]) (fun θ' : ℝ => Real.sin (2 * θ')) θ *
                      (Work.Spaces.Lop^[e - 1 - b])
                        (Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ j)) θ)|
                  ≤ Wbd (A j) (e - 1)
              rw [show Wbd (A j) (e - 1) = ∑ b ∈ Finset.range ((e - 1) + 1),
                    ((e - 1).choose b : ℝ) * Ms * (CL (e - 1 - b) * (4 * Dj)) from rfl]
              exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hbd)
          have hmain : ∀ i : ℕ, i ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
              |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.FlatWAux.chia ψ (j + 1)) θ|
                ≤ A (j + 1) i := by
            intro i hi θ hθ
            have hleib : (Work.Spaces.Lop^[i]) ((fun θ' : ℝ => Real.sin (2 * θ'))
                  * (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1))) θ
                = ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
                    ((Work.Spaces.Lop^[a]) (fun θ' : ℝ => Real.sin (2 * θ')) θ *
                      (Work.Spaces.Lop^[i - a]) (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1)) θ) :=
              (Work.FTS.PhiStar.LinvFlat.LI_Lop_iter_mul_eqOn_9 isOpen_Ioo (by fun_prop) hWt9 i
                (by omega)) hθ
            have hLsum : (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.FlatWAux.chia ψ (j + 1)) θ
                = ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
                    ((Work.Spaces.Lop^[a]) (fun θ' : ℝ => Real.sin (2 * θ')) θ *
                      (Work.Spaces.Lop^[i - a]) (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1)) θ) :=
              hleib
            rw [hLsum]
            have hle : ∀ a ∈ Finset.range (i + 1),
                |(i.choose a : ℝ) * ((Work.Spaces.Lop^[a]) (fun θ' : ℝ => Real.sin (2 * θ')) θ *
                    (Work.Spaces.Lop^[i - a]) (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1)) θ)|
                ≤ (i.choose a : ℝ) * Ms *
                    (if i - a = 0 then Kw (j + 1) else Wbd (A j) (i - a - 1)) := by
              intro a ha
              have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
              have hMsa : |(Work.Spaces.Lop^[a]) (fun θ' : ℝ => Real.sin (2 * θ')) θ| ≤ Ms :=
                hMsGlob a (by omega) θ
              have hWa := hWtbd (i - a) (by omega) θ hθ
              rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
              have h1 : |(Work.Spaces.Lop^[a]) (fun θ' : ℝ => Real.sin (2 * θ')) θ|
                    * |(Work.Spaces.Lop^[i - a]) (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1)) θ|
                  ≤ Ms * (if i - a = 0 then Kw (j + 1) else Wbd (A j) (i - a - 1)) :=
                mul_le_mul hMsa hWa (abs_nonneg _) hMs0
              calc (i.choose a : ℝ) *
                    (|(Work.Spaces.Lop^[a]) (fun θ' : ℝ => Real.sin (2 * θ')) θ|
                      * |(Work.Spaces.Lop^[i - a]) (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1)) θ|)
                  ≤ (i.choose a : ℝ) *
                      (Ms * (if i - a = 0 then Kw (j + 1)
                        else Wbd (A j) (i - a - 1))) :=
                    mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
                _ = (i.choose a : ℝ) * Ms *
                      (if i - a = 0 then Kw (j + 1) else Wbd (A j) (i - a - 1)) := by ring
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            calc ∑ a ∈ Finset.range (i + 1),
                  |(i.choose a : ℝ) * ((Work.Spaces.Lop^[a]) (fun θ' : ℝ => Real.sin (2 * θ')) θ *
                    (Work.Spaces.Lop^[i - a]) (Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1)) θ)|
                ≤ ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) * Ms *
                    (if i - a = 0 then Kw (j + 1)
                      else Wbd (A j) (i - a - 1)) := Finset.sum_le_sum hle
              _ = A (j + 1) i := by rw [A_succ]
          exact ⟨hmain, hchia9⟩
    exact key
  -- ########################################################################
  -- ### 4. assembly
  -- ########################################################################
  refine ⟨Kw, A, hKw0, hA0, ?_⟩
  intro α ψ hα hα5 hang
  refine ⟨?_, ?_⟩
  · intro j hj θ hθ
    exact hKwU ψ
      (fun m hm => by
        rw [Work.FTS.PhiStar.Series.bmode_eq_cmode m ψ 0]
        exact hdecAll α ψ hα hα5 hang m hm)
      (fun m hm θ' hθ' => by
        have h := hQAll m hm 0 (by norm_num) θ' hθ'
        rw [iteratedDeriv_zero] at h
        have h2 : (2 * (m : ℝ) + 1) ^ (2 * 0 + 2) = (2 * (m : ℝ) + 1) ^ 2 := by norm_num
        rwa [h2] at h)
      (hflatAll α ψ hα (by linarith) hang) j hj θ hθ
  · intro j hj i hi θ hθ
    exact (master α ψ hα hα5 hang j hj).1 i hi θ hθ

end Work.FTS.PhiStar.FlatWAux
