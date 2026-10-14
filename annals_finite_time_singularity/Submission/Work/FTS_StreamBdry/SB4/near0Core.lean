import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS_LocDatum3a.Basic
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.THL.L.DzDthG_tau_mod
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont
import Submission.Work.FTS_StreamBdry.Inputs.ftau_cont
import Submission.Work.FTS_StreamBdry.SB4.l12_zero_plainE
import Submission.Work.FTS_StreamBdry.SB4.near0Aux
import Submission.Work.FTS_StreamBdry.SB4.slice_L12_c2
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.FTS_StreamBdry.sb5_barrier_proved
import Submission.Work.Spaces.one_le_mul_w
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.lamDyn_tendsto_of_mu =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

theorem lamDyn_tendsto_of_mu {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ}
    (hmu : Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)))
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hXn : ∀ n : ℕ, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2) :
    (|Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s| ≤ 1 / 2) ∧
    Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)) := by
  -- `muDyn` sees a family only through its `s`-slice, so `MuLamOK` — which is stated at the
  -- *constant* families built from a class-`C` profile of size `≤ C₀α²` and at time `0` — applies
  -- verbatim to each member of the sequence.
  have hbnd : ∀ n : ℕ, |Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s| ≤ 1 / 2 := by
    intro n
    obtain ⟨h1, _⟩ := hml
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) (hC n) (hXn n)
    have key : Work.FTS.Galerkin.muDyn α
        (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ =>
          Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s z θ))
        (fun z θ _ => Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s z θ) 0
        = Work.FTS.Galerkin.muDyn α
          (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s := rfl
    rwa [key] at h1
  -- the bound passes to the limit
  have hle : Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s ≤ 1 / 2 :=
    le_of_tendsto hmu (Filter.Eventually.of_forall fun n => (abs_le.mp (hbnd n)).2)
  have hge : -(1 / 2) ≤ Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s :=
    ge_of_tendsto hmu (Filter.Eventually.of_forall fun n => (abs_le.mp (hbnd n)).1)
  refine ⟨abs_le.mpr ⟨hge, hle⟩, ?_⟩
  -- `lamfun μ = -2μ/(1+μ)` is continuous at the limit, whose distance to `-1` is `≥ 1/2`
  have hden : (1 + Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s) ≠ 0 := by
    intro h
    linarith
  have hcomp : Filter.Tendsto (fun n : ℕ => Work.Construction.lamfun
      (Work.FTS.Galerkin.muDyn α
        (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) Filter.atTop
      (nhds (Work.Construction.lamfun
        (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s))) := by
    have hcont : ContinuousAt (fun μ : ℝ => Work.Construction.lamfun μ)
        (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s) := by
      show ContinuousAt (fun μ : ℝ => -2 * μ / (1 + μ)) _
      exact (continuousAt_const.mul continuousAt_id).div
        (continuousAt_const.add continuousAt_id) hden
    exact hcont.tendsto.comp hmu
  simpa only [Work.FTS.Galerkin.lamDyn] using hcomp

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.MubarCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS_RegExport.RXR5L

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp gSlice)
open Work.FTS_MuLipC

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `|a - b| ≤ |a| + |b|`. -/
private theorem abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

theorem mubarData_of_Tfacts {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Work.FTS.Galerkin.Fam}
    (hSol : Work.FTS.FinalV2.Sol (pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hTfacts : ∃ M : ℝ, 0 ≤ M ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) S,
        |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
          (gSlice g τ) z θ / (1 + z)) 0| ≤ M) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
        |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
            (gSlice g τ) z θ / (1 + z)) 0
          - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
            (gSlice g τ') z θ / (1 + z)) 0| ≤ M * |τ - τ'|)) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S,
      |Work.Construction.mubar
        (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α)
          (Work.FTS_RegExport.RXR5.SG α g) τ)
          (gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
        (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α)
          (Work.FTS_RegExport.RXR5.SG α g) τ)
          (gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ))| ≤ M) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |Work.Construction.mubar
          (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α)
            (Work.FTS_RegExport.RXR5.SG α g) τ)
            (gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
          (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α)
            (Work.FTS_RegExport.RXR5.SG α g) τ)
            (gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ))
        - Work.Construction.mubar
          (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α)
            (Work.FTS_RegExport.RXR5.SG α g) τ')
            (gSlice (Work.FTS_RegExport.RXR5.SG α g) τ'))
          (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α)
            (Work.FTS_RegExport.RXR5.SG α g) τ')
            (gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ'))|
        ≤ M * |τ - τ'| ^ α) := by
  have hβ : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- ## the three difference rows at the profile exponent (no smallness needed)
  obtain ⟨K0, hK00, hrow0⟩ := diffRow0_noSmall (α := pExp α) (C₀ := C₀) hβ hβ1
  obtain ⟨K1, hK10, hrow1⟩ := diffRow1_noSmall (α := pExp α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    hβ hβ1 (fun a b => map_sub E a b) (fun c a => map_smul E c a) hStar
    (fun u hu => (hEll u hu).1)
  obtain ⟨K2, hK20, hrow2⟩ := Work.FTS_MuLipC.RowT.diffRow2 (α := pExp α) (C₀ := C₀) hβ hβ1
  -- ## the transport `τ`-facts at the limit family
  obtain ⟨MT, hMT0, hMTb, hMTh⟩ := hTfacts
  -- ## the horizon
  set T : ℝ := max S 1 with hTdef
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right S 1)
  have hST : ∀ τ ∈ Set.Icc (0 : ℝ) S, τ ∈ Set.Icc (0 : ℝ) T := fun τ hτ =>
    ⟨hτ.1, le_trans hτ.2 (le_max_left S 1)⟩
  -- ## the approximating families of `LimApprox`
  obtain ⟨gn, B, L, hC, hLip, hjet, hmu⟩ := hOK.2 T hT
  have hC₀0 : 0 ≤ C₀ := by
    have hX0 : Work.FTS.Nonlin.Xn (pExp α) (slice (gn 0) 0) ≤ C₀ * (pExp α) ^ 2 :=
      (hC 0 0 ⟨le_rfl, hT.le⟩).2.1
    have h0 : 0 ≤ Work.FTS.Nonlin.Xn (pExp α) (slice (gn 0) 0) :=
      Work.Spaces.HkNorm_nonneg _ _ _
    have hpos : 0 < (pExp α) ^ 2 := pow_pos hβ 2
    nlinarith [hX0, h0, hpos]
  -- ## the envelope and the constants
  set EnvB : ℝ := Env (pExp α) (C₀ * (pExp α) ^ 2) with hEnvB
  have hEnvB0 : 0 ≤ EnvB := by
    rw [hEnvB]
    exact Env_nonneg hβ.le (mul_nonneg hC₀0 (sq_nonneg _))
  set MubB : ℝ := (Work.FTS_MuLamOK.KMu0 + Work.FTS_MuLamOK.KMu1 Ce Cs) * EnvB with hMubB
  have hMubB0 : 0 ≤ MubB := mul_nonneg (add_nonneg (le_of_lt (Work.FTS_MuLamOK.KMu0_pos))
    (le_of_lt (Work.FTS_MuLamOK.KMu1_pos Ce Cs))) hEnvB0
  set TB : ℝ := Work.FTS_MuLamOK.KMu2 * (C₀ * (pExp α) ^ 2) with hTB
  have hTB0 : 0 ≤ TB := mul_nonneg (le_of_lt Work.FTS_MuLamOK.KMu2_pos)
    (mul_nonneg hC₀0 (sq_nonneg _))
  set Mmu : ℝ := (MubB + TB) / (2 * pExp α) with hMmu
  have hMmu0 : 0 ≤ Mmu := div_nonneg (add_nonneg hMubB0 hTB0) (by positivity)
  set Lr : ℝ := max L 0 with hLr
  have hLr0 : 0 ≤ Lr := le_max_right _ _
  set Lmu : ℝ := ((K0 + K1) * Lr + K2 * Lr) / (2 * pExp α) with hLmu
  have hLmu0 : 0 ≤ Lmu := div_nonneg (add_nonneg (mul_nonneg (add_nonneg hK00.le hK10.le) hLr0)
    (mul_nonneg hK20.le hLr0)) (by positivity)
  -- ## the per-approximant value bounds
  have hbound0 : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      |Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0|
        ≤ Work.FTS_MuLamOK.KMu0 * EnvB := by
    intro n τ hτ
    have hw : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ) := (hC n τ hτ).1
    have hX : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ) ≤ C₀ * (pExp α) ^ 2 :=
      (hC n τ hτ).2.1
    have h1 := Work.FTS_MuLamOK.KMu0_row hβ hβ1 hw.reg (Work.FTS.ClassC.classC_hkMem_four hw)
    have h2 : Env (pExp α) (Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ)) ≤ EnvB := by
      rw [hEnvB]
      exact Env_mono hβ.le (Work.Spaces.HkNorm_nonneg _ _ _) hX
    simp only [Sn0] at h1 ⊢
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt Work.FTS_MuLamOK.KMu0_pos))
  have hbound1 : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      |Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0|
        ≤ Work.FTS_MuLamOK.KMu1 Ce Cs * EnvB := by
    intro n τ hτ
    have hw : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ) := (hC n τ hτ).1
    have hX : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ) ≤ C₀ * (pExp α) ^ 2 :=
      (hC n τ hτ).2.1
    have h1 := Work.FTS_MuLamOK.KMu1_row Ce Cs hβ hβ1 hw.reg
      (Work.FTS.ClassC.classC_hkMem_four hw) hStar.toStarPkgo ((hEll _ hw).1)
    have h2 : Env (pExp α) (Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ)) ≤ EnvB := by
      rw [hEnvB]
      exact Env_mono hβ.le (Work.Spaces.HkNorm_nonneg _ _ _) hX
    simp only [Sn] at h1 ⊢
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt (Work.FTS_MuLamOK.KMu1_pos Ce Cs)))
  have hbound2 : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      |Work.Construction.L12 (Tf (gSlice (gn n) τ)) 0| ≤ TB := by
    intro n τ hτ
    have hw : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ) := (hC n τ hτ).1
    have hX : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ) ≤ C₀ * (pExp α) ^ 2 :=
      (hC n τ hτ).2.1
    have h1 := Work.FTS_MuLamOK.KMu2_row hβ hβ1 hw.reg (Work.FTS.ClassC.classC_hkMem_four hw)
    rw [hTB]
    exact le_trans h1 (mul_le_mul_of_nonneg_left hX (le_of_lt Work.FTS_MuLamOK.KMu2_pos))
  -- ## the per-approximant `τ`-moduli
  have hdiff0 : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      ∀ (τ' : ℝ), τ' ∈ Set.Icc (0 : ℝ) T →
      |Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0
        - Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ')) 0|
        ≤ K0 * (Lr * |τ - τ'|) := by
    intro n τ hτ τ' hτ'
    have hf : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ) := (hC n τ hτ).1
    have hf' : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ') := (hC n τ' hτ').1
    have hX : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ) ≤ C₀ * (pExp α) ^ 2 :=
      (hC n τ hτ).2.1
    have hX' : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ') ≤ C₀ * (pExp α) ^ 2 :=
      (hC n τ' hτ').2.1
    have h1 := hrow0 _ _ hf hf' hX hX'
    have h2 : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ - slice (gn n) τ')
        ≤ Lr * |τ - τ'| := by
      refine le_trans (hLip n τ hτ τ' hτ') ?_
      exact mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _)
    simp only [Sn0] at h1 ⊢
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hK00.le)
  have hdiff1 : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      ∀ (τ' : ℝ), τ' ∈ Set.Icc (0 : ℝ) T →
      |Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0
        - Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ')) 0|
        ≤ K1 * (Lr * |τ - τ'|) := by
    intro n τ hτ τ' hτ'
    have hf : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ) := (hC n τ hτ).1
    have hf' : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ') := (hC n τ' hτ').1
    have hX : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ) ≤ C₀ * (pExp α) ^ 2 :=
      (hC n τ hτ).2.1
    have hX' : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ') ≤ C₀ * (pExp α) ^ 2 :=
      (hC n τ' hτ').2.1
    have h1 := hrow1 _ _ hf hf' hX hX'
    have h2 : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ - slice (gn n) τ')
        ≤ Lr * |τ - τ'| := by
      refine le_trans (hLip n τ hτ τ' hτ') ?_
      exact mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _)
    simp only [Sn] at h1 ⊢
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hK10.le)
  have hdiff2 : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      ∀ (τ' : ℝ), τ' ∈ Set.Icc (0 : ℝ) T →
      |Work.Construction.L12 (Tf (gSlice (gn n) τ)) 0
        - Work.Construction.L12 (Tf (gSlice (gn n) τ')) 0| ≤ K2 * (Lr * |τ - τ'|) := by
    intro n τ hτ τ' hτ'
    have hf : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ) := (hC n τ hτ).1
    have hf' : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ') := (hC n τ' hτ').1
    have hX : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ) ≤ C₀ * (pExp α) ^ 2 :=
      (hC n τ hτ).2.1
    have hX' : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ') ≤ C₀ * (pExp α) ^ 2 :=
      (hC n τ' hτ').2.1
    have h1 := hrow2 _ _ hf hf' hX hX'
    have h2 : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ - slice (gn n) τ')
        ≤ Lr * |τ - τ'| := by
      refine le_trans (hLip n τ hτ τ' hτ') ?_
      exact mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _)
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hK20.le)
  -- ## the `μ` of the approximants: bound
  have hmu_n_bd : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      |Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs (⇑E) (gn n)) (gn n) τ|
        ≤ Mmu := by
    intro n τ hτ
    have hmuid : Work.FTS.Galerkin.muDyn (pExp α)
          (Work.FTS.Nonlin.PsiCan Φs (⇑E) (gn n)) (gn n) τ
        = Work.FTS.Galerkin.muDyn (pExp α)
            (Work.FTS.Nonlin.PsiCan Φs (⇑E) (Work.FTS.FinalV2.cst (gSlice (gn n) τ)))
            (Work.FTS.FinalV2.cst (gSlice (gn n) τ)) 0 := rfl
    rw [hmuid, Work.FTS_MuLipC.muDyn_const_eq]
    have ha := hbound0 n τ hτ
    have hb := hbound1 n τ hτ
    have hc := hbound2 n τ hτ
    have hsum : |Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0
        + Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0| ≤ MubB := by
      rw [hMubB]
      calc |Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0
            + Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0|
          ≤ |Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0|
            + |Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0| :=
            abs_add_le _ _
        _ ≤ Work.FTS_MuLamOK.KMu0 * EnvB + Work.FTS_MuLamOK.KMu1 Ce Cs * EnvB :=
            add_le_add ha hb
        _ = (Work.FTS_MuLamOK.KMu0 + Work.FTS_MuLamOK.KMu1 Ce Cs) * EnvB := by ring
    rw [hMmu]
    have htri : |(Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0
              + Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0)
            + Work.Construction.L12 (Tf (gSlice (gn n) τ)) 0| ≤ MubB + TB :=
      le_trans (abs_add_le _ _) (add_le_add hsum hc)
    have hfac : 1 / (2 * (pExp α))
            * (Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0
              + Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0)
          + 1 / (2 * (pExp α)) * Work.Construction.L12 (Tf (gSlice (gn n) τ)) 0
        = (1 / (2 * (pExp α))) * ((Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0
              + Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0)
            + Work.Construction.L12 (Tf (gSlice (gn n) τ)) 0) := by ring
    rw [hfac, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * (pExp α)))]
    calc 1 / (2 * (pExp α)) * |(Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0
              + Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0)
            + Work.Construction.L12 (Tf (gSlice (gn n) τ)) 0|
        ≤ 1 / (2 * (pExp α)) * (MubB + TB) :=
          mul_le_mul_of_nonneg_left htri (by positivity)
      _ = (MubB + TB) / (2 * (pExp α)) := by ring
  -- ## the `μ` of the approximants: `τ`-modulus
  have hmu_n_ho : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      ∀ (τ' : ℝ), τ' ∈ Set.Icc (0 : ℝ) T →
      |Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs (⇑E) (gn n)) (gn n) τ
        - Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs (⇑E) (gn n)) (gn n) τ'|
        ≤ Lmu * |τ - τ'| := by
    intro n τ hτ τ' hτ'
    have hmuid : ∀ s : ℝ, Work.FTS.Galerkin.muDyn (pExp α)
          (Work.FTS.Nonlin.PsiCan Φs (⇑E) (gn n)) (gn n) s
        = Work.FTS.Galerkin.muDyn (pExp α)
            (Work.FTS.Nonlin.PsiCan Φs (⇑E) (Work.FTS.FinalV2.cst (gSlice (gn n) s)))
            (Work.FTS.FinalV2.cst (gSlice (gn n) s)) 0 := fun s => rfl
    rw [hmuid τ, hmuid τ', Work.FTS_MuLipC.muDyn_const_eq, Work.FTS_MuLipC.muDyn_const_eq]
    have ha := hdiff0 n τ hτ τ' hτ'
    have hb := hdiff1 n τ hτ τ' hτ'
    have hc := hdiff2 n τ hτ τ' hτ'
    have hfac : (1 / (2 * (pExp α))
            * (Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0
              + Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0)
          + 1 / (2 * (pExp α)) * Work.Construction.L12 (Tf (gSlice (gn n) τ)) 0)
        - (1 / (2 * (pExp α))
            * (Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ')) 0
              + Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ')) 0)
          + 1 / (2 * (pExp α)) * Work.Construction.L12 (Tf (gSlice (gn n) τ')) 0)
        = (1 / (2 * (pExp α)))
            * ((Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0
                - Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ')) 0)
              + (Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0
                - Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ')) 0)
              + (Work.Construction.L12 (Tf (gSlice (gn n) τ)) 0
                - Work.Construction.L12 (Tf (gSlice (gn n) τ')) 0)) := by ring
    rw [hfac, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * (pExp α)))]
    have htri : |(Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0
              - Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ')) 0)
            + (Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0
              - Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ')) 0)
            + (Work.Construction.L12 (Tf (gSlice (gn n) τ)) 0
              - Work.Construction.L12 (Tf (gSlice (gn n) τ')) 0)|
        ≤ (K0 * (Lr * |τ - τ'|) + K1 * (Lr * |τ - τ'|)) + K2 * (Lr * |τ - τ'|) := by
      refine le_trans (abs_add_le _ _) (add_le_add (le_trans (abs_add_le _ _)
        (add_le_add ha hb)) hc)
    have h1 : (K0 * (Lr * |τ - τ'|) + K1 * (Lr * |τ - τ'|)) + K2 * (Lr * |τ - τ'|)
        = ((K0 + K1) * Lr + K2 * Lr) * |τ - τ'| := by ring
    rw [hLmu]
    calc 1 / (2 * (pExp α)) * |(Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ)) 0
              - Work.Construction.L12 (Sn0 (pExp α) (gSlice (gn n) τ')) 0)
            + (Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ)) 0
              - Work.Construction.L12 (Sn (pExp α) Φs (⇑E) (gSlice (gn n) τ')) 0)
            + (Work.Construction.L12 (Tf (gSlice (gn n) τ)) 0
              - Work.Construction.L12 (Tf (gSlice (gn n) τ')) 0)|
        ≤ 1 / (2 * (pExp α)) * (((K0 + K1) * Lr + K2 * Lr) * |τ - τ'|) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← h1]
          exact htri
      _ = ((K0 + K1) * Lr + K2 * Lr) / (2 * (pExp α)) * |τ - τ'| := by ring
  -- ## pass to the limit
  have hmu_bd : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      |Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ| ≤ Mmu := by
    intro τ hτ
    exact le_of_tendsto ((hmu τ (hST τ hτ)).abs)
      (Filter.Eventually.of_forall fun n => hmu_n_bd n τ (hST τ hτ))
  have hmu_ho : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ
        - Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ'|
        ≤ Lmu * |τ - τ'| := by
    intro τ hτ τ' hτ'
    exact le_of_tendsto (((hmu τ (hST τ hτ)).sub (hmu τ' (hST τ' hτ'))).abs)
      (Filter.Eventually.of_forall fun n => hmu_n_ho n τ (hST τ hτ) τ' (hST τ' hτ'))
  -- ## the Hölder modulus of the reference `mubar`
  have hLipTot : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |Work.Construction.mubar
          (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α)
            (Work.FTS_RegExport.RXR5.SG α g) τ)
            (gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
          (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α)
            (Work.FTS_RegExport.RXR5.SG α g) τ)
            (gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ))
        - Work.Construction.mubar
          (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α)
            (Work.FTS_RegExport.RXR5.SG α g) τ')
            (gSlice (Work.FTS_RegExport.RXR5.SG α g) τ'))
          (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α)
            (Work.FTS_RegExport.RXR5.SG α g) τ')
            (gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ'))|
        ≤ ((K0 + K1) * Lr + K2 * Lr + MT) * |τ - τ'| := by
    intro τ hτ τ' hτ'
    rw [mubar_sanitized_eq (α := α) (Φs := Φs) (E := E) (g := g) (τ := τ) hτ.1,
      mubar_sanitized_eq (α := α) (Φs := Φs) (E := E) (g := g) (τ := τ') hτ'.1,
      mubar_ref_eq hα (Φs := Φs) (E := E) (g := g) (τ := τ),
      mubar_ref_eq hα (Φs := Φs) (E := E) (g := g) (τ := τ')]
    have h2 := hmu_ho τ hτ τ' hτ'
    have h3 := hMTh τ hτ τ' hτ'
    have h4 : 2 * (pExp α) * Lmu = (K0 + K1) * Lr + K2 * Lr := by
      rw [hLmu]; field_simp
    calc |2 * (pExp α) * Work.FTS.Galerkin.muDyn (pExp α)
              (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ
          - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ) z θ / (1 + z)) 0
          - (2 * (pExp α) * Work.FTS.Galerkin.muDyn (pExp α)
                (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ'
            - Work.Construction.L12
                (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ') z θ / (1 + z)) 0)|
        = |2 * (pExp α) * (Work.FTS.Galerkin.muDyn (pExp α)
                (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ
              - Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ')
            - (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ) z θ / (1 + z)) 0
              - Work.Construction.L12
                  (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ') z θ / (1 + z)) 0)| := by
          congr 1; ring
      _ ≤ 2 * (pExp α) * |Work.FTS.Galerkin.muDyn (pExp α)
              (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ
            - Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ'|
          + |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ) z θ / (1 + z)) 0
            - Work.Construction.L12
                (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ') z θ / (1 + z)) 0| := by
          have h := abs_sub_le_abs_add (2 * (pExp α) * (Work.FTS.Galerkin.muDyn (pExp α)
                (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ
              - Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ'))
            (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ) z θ / (1 + z)) 0
              - Work.Construction.L12
                  (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ') z θ / (1 + z)) 0)
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (pExp α))] at h
          exact h
      _ ≤ 2 * (pExp α) * (Lmu * |τ - τ'|) + MT * |τ - τ'| :=
          add_le_add (mul_le_mul_of_nonneg_left h2 (by positivity)) h3
      _ = ((K0 + K1) * Lr + K2 * Lr + MT) * |τ - τ'| := by rw [← h4]; ring
  -- ## the two conclusions
  refine ⟨⟨MubB + TB + MT, by positivity, ?_⟩,
    ⟨((K0 + K1) * Lr + K2 * Lr + MT) * S ^ (1 - α), by positivity, ?_⟩⟩
  · intro τ hτ
    rw [mubar_sanitized_eq (α := α) (Φs := Φs) (E := E) (g := g) (τ := τ) hτ.1,
      mubar_ref_eq hα (Φs := Φs) (E := E) (g := g) (τ := τ)]
    have ha := hmu_bd τ hτ
    have hb := hMTb τ hτ
    have h4 : 2 * (pExp α) * Mmu = MubB + TB := by rw [hMmu]; field_simp
    calc |2 * (pExp α) * Work.FTS.Galerkin.muDyn (pExp α)
              (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ
          - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ) z θ / (1 + z)) 0|
        ≤ 2 * (pExp α) * |Work.FTS.Galerkin.muDyn (pExp α)
              (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ|
          + |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ) z θ / (1 + z)) 0| := by
          have h := abs_sub_le_abs_add (2 * (pExp α) * Work.FTS.Galerkin.muDyn (pExp α)
                (Work.FTS.Nonlin.PsiCan Φs (⇑E) g) g τ)
            (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth (gSlice g τ) z θ / (1 + z)) 0)
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (pExp α))] at h
          exact h
      _ ≤ 2 * (pExp α) * Mmu + MT :=
          add_le_add (mul_le_mul_of_nonneg_left ha (by positivity)) hb
      _ = MubB + TB + MT := by rw [h4]
  · intro τ hτ τ' hτ'
    have hk := hLipTot τ hτ τ' hτ'
    have hle : |τ - τ'| ≤ S := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [hτ.1, hτ.2, hτ'.1, hτ'.2],
        by linarith [hτ.1, hτ.2, hτ'.1, hτ'.2]⟩
    have h2 : |τ - τ'| ^ (1 - α) ≤ S ^ (1 - α) :=
      Real.rpow_le_rpow (abs_nonneg _) hle (by linarith)
    have h3 : |τ - τ'| ≤ S ^ (1 - α) * |τ - τ'| ^ α := by
      rcases eq_or_lt_of_le (abs_nonneg (τ - τ')) with h0 | hpos
      · rw [h0.symm, Real.zero_rpow (ne_of_gt hα), mul_zero]
      · have h1 : |τ - τ'| = |τ - τ'| ^ (1 - α) * |τ - τ'| ^ α := by
          rw [← Real.rpow_add hpos (1 - α) α]
          norm_num
        calc |τ - τ'| = |τ - τ'| ^ (1 - α) * |τ - τ'| ^ α := h1
          _ ≤ S ^ (1 - α) * |τ - τ'| ^ α :=
              mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (abs_nonneg _) _)
    calc |Work.Construction.mubar
            (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α)
              (Work.FTS_RegExport.RXR5.SG α g) τ)
              (gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
            (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α)
              (Work.FTS_RegExport.RXR5.SG α g) τ)
              (gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ))
          - Work.Construction.mubar
            (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α)
              (Work.FTS_RegExport.RXR5.SG α g) τ')
              (gSlice (Work.FTS_RegExport.RXR5.SG α g) τ'))
            (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α)
              (Work.FTS_RegExport.RXR5.SG α g) τ')
              (gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ'))|
        ≤ ((K0 + K1) * Lr + K2 * Lr + MT) * |τ - τ'| := hk
      _ ≤ ((K0 + K1) * Lr + K2 * Lr + MT) * (S ^ (1 - α) * |τ - τ'| ^ α) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ((K0 + K1) * Lr + K2 * Lr + MT) * S ^ (1 - α) * |τ - τ'| ^ α := by ring


end Work.FTS_RegExport.RXR5L
end
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.L.DzDthSG_C1JetP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.THL.L


end Work.FTS_RegExport.THL.L
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.slice_inputs_of_slot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS_StreamBdry.Inputs


end Work.FTS_StreamBdry.Inputs
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB4.near0Core =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB4.near0Core` — the SB4 assembly for one slice

`near0_core`: from the `D_z`-bounds of the elliptic summand `PhiTil αG f (E f)` and of `Theta αG f`
(`hφ3`, `hφ4`), the `C²`-regularity of `L12` on the slice (`hL12`) and the star package, the SB4
bound `|D_z psiP αG Ψ| ≤ K·z·sin 2θ` holds for the canonical slice `Ψ = slice (PsiCan Φs E g) τ`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB4

set_option maxHeartbeats 800000

/-! ## §5 The assembly for one slice -/

/-- **The core assembly**: from the `D_z`-bounds of the elliptic and `Θ(f)` summands and the
`C²`-regularity of `L12` on the slice, the SB4 bound holds for the canonical slice at `τ`. -/
theorem near0_core {a C₀ Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs)
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hL12 : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) w)
        (-(Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ) z)) z ∧
      DifferentiableAt ℝ (fun w => Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ) w) z)
    (hφ3 : ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      z ≤ 1 →
      |Work.Spaces.Dz (fun z θ => Work.FTS.StreamBdryIface.Uprime (Work.FTS.Regularity.pExp a)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp a) (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ))) z θ) z θ| ≤ K * z)
    (hφ4 : ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      z ≤ 1 →
      |Work.Spaces.Dz (fun z θ => Work.FTS.StreamBdryIface.Uprime (Work.FTS.Regularity.pExp a)
        (Work.Construction.Theta (Work.FTS.Regularity.pExp a) (Work.FTS.Galerkin.slice g τ))
          z θ) z θ| ≤ K * z) :
    ∀ τ, 0 ≤ τ → ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP (Work.FTS.Regularity.pExp a)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) z θ|
        ≤ K * z * Work.Construction.s2 θ := by
  intro τ hτ
  set αG := Work.FTS.Regularity.pExp a with hαGdef
  have hαG : 0 < αG := by rw [hαGdef]; show (0 : ℝ) < 3 * a; linarith
  have hαG1 : αG ≤ 1 := by rw [hαGdef]; show (3 : ℝ) * a ≤ 1; linarith
  -- abbreviations
  set f : ℝ → ℝ → ℝ := Work.FTS.Galerkin.slice g τ with hfdef
  set Ψ : ℝ → ℝ → ℝ := Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ with hΨdef
  -- the star summand is smooth
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs αG Φs) :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs hαG hαG1 hStar.smooth).1
  -- the elliptic summand is `C³`
  obtain ⟨gn, B, L, hC, hLc, hjet, hmu⟩ := hOK.2 (τ + 1) (by linarith)
  have hCτ : ∀ n, Work.FTS.ClassC.ClassC αG (Work.FTS.Galerkin.slice (gn n) τ) :=
    fun n => (hC n τ ⟨hτ, by linarith⟩).1
  have hBτ : ∀ n, Work.FTS.StrongGlobal.Xn6 αG (Work.FTS.Galerkin.slice (gn n) τ) ≤ B :=
    fun n => (hC n τ ⟨hτ, by linarith⟩).2.2
  have hf4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0 := hOK.1.1.c4 τ hτ
  have hjetτ : ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ)
        Filter.atTop (𝓝 (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ)) :=
    fun j i hji z θ hzθ => hjet τ ⟨hτ, by linarith⟩ j i hji z θ hzθ
  obtain ⟨-, hEf3, -⟩ := hEL (fun n => Work.FTS.Galerkin.slice (gn n) τ)
    (Work.FTS.Galerkin.slice g τ) B hCτ hBτ hf4 hjetτ
  -- radial differentiability of the two elementary summands of `ΦTil αG f (E f)`
  have hEf_diff : ∀ w θ : ℝ, (w, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun w' => E (Work.FTS.Galerkin.slice g τ) w' θ) w := by
    intro w θ hwθ
    have hslice : ContDiffOn ℝ 3 (fun w' => E (Work.FTS.Galerkin.slice g τ) w' θ) (Set.Ioi 0) :=
      Work.FTS.StrongEps.EComparison.contDiffOn_slice_z
        ⟨hwθ.2.1, hwθ.2.2⟩ hEf3
    exact (hslice.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hwθ.1)
  have hEf_pz_diff : ∀ w θ : ℝ, (w, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun w' => Work.Spaces.pz (E (Work.FTS.Galerkin.slice g τ)) w' θ) w :=
    fun w θ hwθ => near0_diff_pz_of_joint ⟨hwθ.2.1, hwθ.2.2⟩ hwθ.1 hEf3
  have hTh_diff : ∀ w θ : ℝ, (w, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun w' => Work.Construction.Theta αG
        (Work.FTS.Galerkin.slice g τ) w' θ) w :=
    fun w θ hwθ =>
      (near0_hasDerivAt_Theta (αG := αG) ((hL12 τ hτ w hwθ.1).1.differentiableAt)).differentiableAt
  have hTh_pz_diff : ∀ w θ : ℝ, (w, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun w' => Work.Spaces.pz (Work.Construction.Theta αG
        (Work.FTS.Galerkin.slice g τ)) w' θ) w :=
    fun w θ hwθ => near0_diff_pz_Theta hwθ.1 (fun w' hw' => (hL12 τ hτ w' hw').1)
      (fun w' hw' => (hL12 τ hτ w' hw').2)
  -- radial differentiability of the `U`-slot of the elliptic summand
  have hdiff3 : ∀ w θ : ℝ, (w, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun w' => Work.FTS.StreamBdryIface.Uprime αG
        (Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ))) w' θ) w := by
    intro w θ hwθ
    have hdPhi : DifferentiableAt ℝ (fun w' => Work.Construction.PhiTil αG
        (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)) w' θ) w := by
      have h := (hEf_diff w θ hwθ).sub (hTh_diff w θ hwθ)
      have hfun : ((fun w' => E (Work.FTS.Galerkin.slice g τ) w' θ)
            - fun w' => Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) w' θ)
          = (fun w' => Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) w' θ) := by
        funext w'; simp only [Pi.sub_apply, Work.Construction.PhiTil]
      rw [hfun] at h
      exact h
    have hpzPhi : DifferentiableAt ℝ (fun w' => Work.Spaces.pz (Work.Construction.PhiTil αG
        (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) w' θ) w := by
      have hev : (fun w' => Work.Spaces.pz (Work.Construction.PhiTil αG
            (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) w' θ)
          =ᶠ[𝓝 w] (fun w' => Work.Spaces.pz (E (Work.FTS.Galerkin.slice g τ)) w' θ
            - Work.Spaces.pz (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) w' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hwθ.1] with w' hw'
        simp only [Work.Spaces.pz, Work.Construction.PhiTil]
        have hfun : (fun z' => E (Work.FTS.Galerkin.slice g τ) z' θ
              - Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) z' θ)
            = (fun z' => E (Work.FTS.Galerkin.slice g τ) z' θ)
              - fun z' => Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) z' θ := by
          funext z'; simp only [Pi.sub_apply]
        rw [hfun, deriv_sub (hEf_diff w' θ ⟨hw', hwθ.2.1, hwθ.2.2⟩)
          (hTh_diff w' θ ⟨hw', hwθ.2.1, hwθ.2.2⟩)]
      exact (hev.differentiableAt_iff).mpr ((hEf_pz_diff w θ hwθ).sub (hTh_pz_diff w θ hwθ))
    have hA : DifferentiableAt ℝ (fun w' : ℝ => αG * w') w :=
      differentiableAt_id.const_mul αG
    have h3 : DifferentiableAt ℝ (fun w' : ℝ => -3 * Work.Construction.PhiTil αG
        (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)) w' θ
        - αG * w' * Work.Spaces.pz (Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ))) w' θ) w :=
      (hdPhi.const_mul (-3)).sub (hA.mul hpzPhi)
    simpa only [Work.FTS.StreamBdryIface.Uprime, Work.Construction.Uop] using
      h3.div_const (Work.Construction.s2 θ)
  -- the four Lipschitz constants
  obtain ⟨C1, hC1nn, hC1⟩ := near0_lip_star ha ha13 hStar
  obtain ⟨C3, hC3nn, hC3⟩ := hφ3 τ hτ
  obtain ⟨C4, hC4nn, hC4⟩ := hφ4 τ hτ
  have hC3' : ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.FTS.StreamBdryIface.Uprime αG (Work.Construction.PhiTil αG
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ
        - Work.FTS.StreamBdryIface.Uprime αG (Work.Construction.PhiTil αG
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z' θ|
        ≤ C3 * |z - z'| :=
    near0_lip_of_dz_bound hC3nn hdiff3 fun w θ hwθ hwle => hC3 w θ hwθ hwle
  have hC4' : ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z θ
        - Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z' θ|
        ≤ C4 * |z - z'| :=
    near0_lip_of_dz_bound hC4nn (fun w θ hwθ => by
        have hA : DifferentiableAt ℝ (fun w' : ℝ => αG * w') w :=
          differentiableAt_id.const_mul αG
        have h3 : DifferentiableAt ℝ (fun w' : ℝ => -3 * Work.Construction.Theta αG
            (Work.FTS.Galerkin.slice g τ) w' θ
            - αG * w' * Work.Spaces.pz (Work.Construction.Theta αG
              (Work.FTS.Galerkin.slice g τ)) w' θ) w :=
          ((hTh_diff w θ hwθ).const_mul (-3)).sub (hA.mul (hTh_pz_diff w θ hwθ))
        simpa only [Work.FTS.StreamBdryIface.Uprime, Work.Construction.Uop] using
          h3.div_const (Work.Construction.s2 θ))
      fun w θ hwθ hwle => hC4 w θ hwθ hwle
  -- the constant of the `Θ(F_*)` summand
  have hC2 := near0_lip_theta_fstar hαG hαG1
  -- additivity of the `U`-slot over the four summands
  have hLstar : ∀ z : ℝ, 0 < z → DifferentiableAt ℝ
      (fun w => Work.Construction.L12 (Work.Construction.Fstar αG) w) z := by
    intro z hz
    have hev : (fun w => Work.Construction.L12 (Work.Construction.Fstar αG) w)
        =ᶠ[𝓝 z] (fun w => 2 * αG / (1 + w)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact Work.Construction.L12_Fstar_eq hαG hαG1 hw.le
    have hd : DifferentiableAt ℝ (fun w : ℝ => 2 * αG / (1 + w)) z :=
      (differentiableAt_const (2 * αG)).div (differentiableAt_const 1 |>.add differentiableAt_id)
        (by positivity)
    exact (hev.differentiableAt_iff).mpr hd
  have hadd : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Galerkin.slice
          (Work.FTS.Nonlin.PsiCan Φs E g) τ) z θ
        = Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z θ
          + Work.FTS.StreamBdryIface.Uprime αG
              (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
          + Work.FTS.StreamBdryIface.Uprime αG (Work.Construction.PhiTil αG
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ
          + Work.FTS.StreamBdryIface.Uprime αG
              (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z θ := by
    intro z θ hzθ
    have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hzθ.2.1, hzθ.2.2⟩
    have hd1 : HasDerivAt (fun w => Work.FTS.Nonlin.PhiTs αG Φs w θ)
        (Work.Spaces.pz (Work.FTS.Nonlin.PhiTs αG Φs) z θ) z :=
      hsm1.hasDerivAt_slice hθm hzθ.1
    have hd2 : HasDerivAt (fun w => Work.Construction.Theta αG
        (Work.Construction.Fstar αG) w θ)
        (Work.Spaces.pz (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ) z :=
      near0_hasDerivAt_Theta (hLstar z hzθ.1)
    have hd3 : HasDerivAt (fun w => Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
        (E (Work.FTS.Galerkin.slice g τ)) w θ)
        (Work.Spaces.pz (Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ))) z θ) z := by
      have hsub := (hEf_diff z θ hzθ).hasDerivAt.sub (hTh_diff z θ hzθ).hasDerivAt
      have hval : Work.Spaces.pz (Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
            (E (Work.FTS.Galerkin.slice g τ))) z θ
          = Work.Spaces.pz (E (Work.FTS.Galerkin.slice g τ)) z θ
            - Work.Spaces.pz (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z θ := by
        simp only [Work.Spaces.pz, Work.Construction.PhiTil]
        have hfun : (fun z' => E (Work.FTS.Galerkin.slice g τ) z' θ
              - Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) z' θ)
            = (fun z' => E (Work.FTS.Galerkin.slice g τ) z' θ)
              - fun z' => Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) z' θ := by
          funext z'; simp only [Pi.sub_apply]
        rw [hfun, deriv_sub (hEf_diff z θ hzθ) (hTh_diff z θ hzθ)]
      rw [hval]
      have hfun : ((fun w' => E (Work.FTS.Galerkin.slice g τ) w' θ)
            - fun w' => Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) w' θ)
          = (fun w' => Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) w' θ) := by
        funext w'; simp only [Pi.sub_apply, Work.Construction.PhiTil]
      rw [hfun] at hsub
      exact hsub
    have hd4 : HasDerivAt (fun w => Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) w θ)
        (Work.Spaces.pz (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z θ) z :=
      near0_hasDerivAt_Theta ((hL12 τ hτ z hzθ.1).1.differentiableAt)
    have hderiv : deriv (fun w => Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ w θ) z
        = Work.Spaces.pz (Work.FTS.Nonlin.PhiTs αG Φs) z θ
          + Work.Spaces.pz (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
          + Work.Spaces.pz (Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ))) z θ
          + Work.Spaces.pz (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z θ := by
      have hfun : (fun w => Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ w θ)
          = (((fun w => Work.FTS.Nonlin.PhiTs αG Φs w θ)
              + fun w => Work.Construction.Theta αG (Work.Construction.Fstar αG) w θ)
              + fun w => Work.Construction.PhiTil αG (Work.FTS.Galerkin.slice g τ)
                  (E (Work.FTS.Galerkin.slice g τ)) w θ)
              + fun w => Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ) w θ := by
        funext w
        simp only [Pi.add_apply, Work.FTS.Galerkin.slice, Work.FTS.Nonlin.PsiCan,
          Work.FTS.Nonlin.PhiTs, Work.Construction.PhiTil]
        ring
      rw [hfun, (((hd1.add hd2).add hd3).add hd4).deriv]
    rw [Work.FTS.StreamBdryIface.Uprime, Work.Construction.Uop, Work.Spaces.pz, hderiv]
    simp only [Work.FTS.Galerkin.slice, Work.FTS.Nonlin.PsiCan, Work.FTS.Nonlin.PhiTs,
      Work.Construction.PhiTil, Work.Construction.Theta, Work.FTS.StreamBdryIface.Uprime,
      Work.Construction.Uop, Work.Spaces.pz]
    ring
  -- the Lipschitz bound of `U'(Ψ)`
  have hU : ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.StreamBdryIface.Uprime αG Ψ z θ - Work.FTS.StreamBdryIface.Uprime αG Ψ z' θ|
        ≤ ((C1 + 2) + C3 + C4) * |z - z'| := by
    intro z hz z' hz' θ hθ
    have hCtot : (0 : ℝ) ≤ ((C1 + 2) + C3 + C4) := by linarith
    rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hθ.2 with hθ2 | hθ2
      · have hzq : (z, θ) ∈ Work.Construction.Qd := ⟨hz.1, hθ0, hθ2⟩
        have hzq' : (z', θ) ∈ Work.Construction.Qd := ⟨hz'.1, hθ0, hθ2⟩
        have h1 := hadd z θ hzq
        have h2 := hadd z' θ hzq'
        rw [h1, h2]
        set a1 := Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z θ with ha1
        set b1 := Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z' θ with hb1
        set a2 := Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ with ha2
        set b2 := Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z' θ with hb2
        set a3 := Work.FTS.StreamBdryIface.Uprime αG (Work.Construction.PhiTil αG
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ with ha3
        set b3 := Work.FTS.StreamBdryIface.Uprime αG (Work.Construction.PhiTil αG
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z' θ with hb3
        set a4 := Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z θ with ha4
        set b4 := Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.FTS.Galerkin.slice g τ)) z' θ with hb4
        have e1 : |a1 - b1| ≤ C1 * |z - z'| := hC1 z hz z' hz' θ hθ
        have e2 : |a2 - b2| ≤ 2 * |z - z'| := hC2 z hz z' hz' θ hθ
        have e3 : |a3 - b3| ≤ C3 * |z - z'| := hC3' z hz z' hz' θ ⟨hθ0, hθ2⟩
        have e4 : |a4 - b4| ≤ C4 * |z - z'| := hC4' z hz z' hz' θ ⟨hθ0, hθ2⟩
        have hzznn : (0:ℝ) ≤ |z - z'| := abs_nonneg _
        calc |(a1 + a2 + a3 + a4) - (b1 + b2 + b3 + b4)|
            = |(a1 - b1) + (a2 - b2) + (a3 - b3) + (a4 - b4)| := by ring_nf
          _ ≤ |a1 - b1| + |a2 - b2| + |a3 - b3| + |a4 - b4| := by
              have h := abs_add_le ((a1 - b1) + (a2 - b2) + (a3 - b3)) (a4 - b4)
              have h' := abs_add_le ((a1 - b1) + (a2 - b2)) (a3 - b3)
              have h'' := abs_add_le (a1 - b1) (a2 - b2)
              linarith
          _ ≤ ((C1 + 2) + C3 + C4) * |z - z'| := by linarith
      · have h0 : Work.Construction.s2 θ = 0 := by
          rw [Work.Construction.s2_eq, hθ2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        simp only [Work.FTS.StreamBdryIface.Uprime, h0, div_zero, sub_zero, abs_zero]
        exact mul_nonneg hCtot (abs_nonneg _)
    · have h0 : Work.Construction.s2 θ = 0 := by
        rw [← hθ0, Work.Construction.s2_eq, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
      simp only [Work.FTS.StreamBdryIface.Uprime, h0, div_zero, sub_zero, abs_zero]
      exact mul_nonneg hCtot (abs_nonneg _)
  -- the `psiP`-Lipschitz bound and the derivative bound
  have hCtot : (0 : ℝ) ≤ (C1 + 2) + C3 + C4 := by linarith
  obtain ⟨K, hK⟩ := psiP_lipschitz hαG hCtot hU
  refine ⟨((C1 + 2) + C3 + C4) / (3 + αG), ?_⟩
  intro z θ hzθ hz1
  have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hzθ.2.1, le_of_lt hzθ.2.2⟩
  obtain ⟨hKval, hKlip⟩ := hK θ hθ
  have habs := abs_deriv_le_of_lipschitzOn_Ioc hKlip z ⟨hzθ.1, hz1⟩
  rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz, hΨdef]
  rw [abs_mul, abs_of_pos hzθ.1]
  have hs2nn : 0 ≤ Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_nonneg_of_Iθ hθ
  rw [hKval] at habs
  have : z * |deriv (fun z' => Work.FTS.StreamBdryIface.psiP αG
      (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) z' θ) z|
      ≤ z * (Work.Construction.s2 θ * ((C1 + 2) + C3 + C4) / (3 + αG)) :=
    mul_le_mul_of_nonneg_left habs hzθ.1.le
  refine le_trans this (le_of_eq ?_)
  ring


end Work.FTS_StreamBdry.SB4
end
end
