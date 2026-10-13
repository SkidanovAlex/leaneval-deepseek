/-
# `MubarCore` — the assembly of `mubarData` (conditional on the transport `τ`-facts)

`mubarData_of_Tfacts` proves the two `mubar` clauses of the leaf statement from the two
`τ`-facts of the transport term `L₁₂(3 D_θ(slice g τ)/(1+z))(0)`; the leaf file supplies them
through `Work.FTS_RegExport.RXR5L.aux.Tlim_bounds`.

See `MubarAssemblyAux.lean` for the structural lemmas and the module docstring of
`mubarData.lean` for the route.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXR5L.MubarAssemblyAux
import Submission.Work.FTS_RegExport.RXR5L.MubarRows
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_MuLipC.RowT.diffRow2

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
