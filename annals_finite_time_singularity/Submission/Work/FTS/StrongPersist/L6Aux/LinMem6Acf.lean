/-
# `Work.FTS.StrongPersist.L6Aux.LinMem6Acf` — the nonlocal summand `Acoef α · Mf f`

The separated coefficient `Acoef α = acoef(z)·gamCoef(α,θ)` multiplied by the radial tail
integral `Mf f = fun z _ => L₁₂(f)(z)`.  The finite-smoothness multiplier estimate
`zmul_finite6` (with `g = gamCoef α · L₁₂ f`) reduces the `ℋ⁶`-integrand to that of `g`; the
level-six separation lemma `L6Aux.HkIntegrandSepLeGen` factorises the latter into the angular
majorant `Mth6 α` and the radial slot sum `SlotSum (L₁₂ f)`, both integrable
(`Mth6_integrable`, the delegated `L6Aux.L12SlotSum6`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.L3_lin_mem
import Submission.Work.FTS.StrongPersist.HkAddFin
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Aux.GamJetBounds
import Submission.Work.FTS.LocData.HkIntegrand_neg
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.PthIter2VftsAux
import Submission.Work.Coercivity.dthIterAng_sq_integrable
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm HkIntegrand Dz Dth mixed)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §4 The nonlocal summand `Acoef α · Mf f` -/


/-- Lowering the order of a `C^n`-statement on the open half-line. -/
theorem linMem_le_of_le {B : ℝ → ℝ} {n m : ℕ}
    (h : ContDiffOn ℝ n B (Set.Ioi (0 : ℝ))) (hmn : m ≤ n) :
    ContDiffOn ℝ m B (Set.Ioi (0 : ℝ)) :=
  h.of_le (by exact_mod_cast hmn)

/-- `gamCoef α = Γ(θ)/c(α)` is `C^n` on the open angular interval, for every `n`. -/
theorem contDiffOn_gamCoef (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (gamCoef α) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hbase : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.contDiff_sin.contDiffOn).mul ((Real.contDiff_cos.contDiffOn).pow 2)
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hgam : ContDiffOn ℝ ⊤ (fun θ : ℝ => Work.Spaces.Gam α θ)
      (Set.Ioo (0 : ℝ) (π / 2)) := hbase.rpow_const_of_ne hne
  have hgc : ContDiffOn ℝ ⊤ (gamCoef α) (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine (hgam.div_const (Work.Spaces.c α)).congr (fun θ _ => ?_)
    rw [gamCoef]
  exact hgc.of_le le_top

/-- Joint `C^n`-smoothness of a separated product `(z,θ) ↦ gamCoef α θ · B z`. -/
theorem linMem_sep_mul {n : ℕ} {B : ℝ → ℝ} {α : ℝ}
    (hB : ContDiffOn ℝ n B (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => gamCoef α θ * B z))
      Work.FTS.EllipticEst.Q0 := by
  have hθ : ContDiffOn ℝ n (fun p : ℝ × ℝ => gamCoef α p.2) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_gamCoef α n).comp contDiffOn_snd
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  have hz : ContDiffOn ℝ n (fun p : ℝ × ℝ => B p.1) Work.FTS.EllipticEst.Q0 :=
    hB.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hfun : Function.uncurry (fun z θ => gamCoef α θ * B z)
      = fun p : ℝ × ℝ => gamCoef α p.2 * B p.1 := rfl
  rw [hfun]
  exact hθ.mul hz

/-- The radial factor `acoef` is `C^n` on the open half-line. -/
theorem linMem_acoef (n : ℕ) :
    ContDiffOn ℝ n acoef (Set.Ioi (0 : ℝ)) := by
  refine (Work.FTS.StrongPersist.L3Aux.contDiffOn_two_z_div.mono ?_).of_le le_top
  intro z hz
  simp only [Set.mem_Ioi] at hz ⊢
  linarith


/-- `C⁶`-smoothness of `L₁₂ f` on the open half-line, from `ℋ⁷`-honesty of `f`. -/
theorem contDiffOn6_L12_of {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) := by
  have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 7 f hsm hmem7
    (by norm_num)).1
  rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
  exact h

/-- **`C⁶`-smoothness of the nonlocal summand on the open quadrant**, from `C⁶`-smoothness of
`L₁₂ f` on the open half-line. -/
theorem contDiffOn6_Acf {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h12 : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ 6 (Function.uncurry (fun z θ => Acoef α z θ * Mf f z θ))
      Work.FTS.EllipticEst.Q0 := by
  have hgz : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => gamCoef α θ * Work.Construction.L12 f z))
      Work.FTS.EllipticEst.Q0 := linMem_sep_mul h12
  have h1 : ContDiffOn ℝ 6 (Function.uncurry
      (fun z θ => acoef z * (gamCoef α θ * Work.Construction.L12 f z)))
      Work.FTS.EllipticEst.Q0 :=
    linMem_zmul_joint (n := 6) (linMem_acoef 6) hgz
  refine h1.congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  show Acoef α z θ * Mf f z θ = acoef z * (gamCoef α θ * Work.Construction.L12 f z)
  rw [Acoef_eq_mul]
  have hMf : Mf f z θ = Work.Construction.L12 f z := rfl
  rw [hMf]
  ring

/-- **The nonlocal summand is in `ℋ⁶`.**  The multiplier step (`zmul_finite6`, with
`φ = acoef` and `g = gamCoef α · L₁₂ f`) reduces the `ℋ⁶`-integrand to that of `g`, which the
separation lemma factorises into the angular majorant `Mth6 α` and the radial slot sum of
`L₁₂ f`; both factors are integrable (`Mth6_integrable`, `hslot`).

The hypothesis `hsep` is the level-six separation lemma for `k = 6`
(`L6Aux.HkIntegrandSepLeGen`), stated in the `Mth6`/`SlotSum` vocabulary. -/
theorem Acf_mem6_of {α : ℝ} {f : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    {K C₁ : ℝ} (hK : 0 ≤ K)
    (hzb : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] acoef z| ≤ K)
    (hslot : MeasureTheory.IntegrableOn (SlotSum (fun z => Work.Construction.L12 f z))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, SlotSum (fun z => Work.Construction.L12 f z) z)
        ≤ C₁ * Work.Spaces.HkSq α 6 f)
    (hsep : ∀ {z θ : ℝ}, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 6
          (fun z' θ' => gamCoef α θ' * Work.Construction.L12 f z') z θ
        ≤ Mth6 α θ * SlotSum (fun z => Work.Construction.L12 f z) z)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f)
    (h0 : Work.Construction.L12 f 0 = 0) :
    Work.Spaces.HkMem α 6 (fun z θ => Acoef α z θ * Mf f z θ) := by
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have h12 : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn6_L12_of hsm hmem7
  set g : ℝ → ℝ → ℝ := fun z θ => gamCoef α θ * Work.Construction.L12 f z with hgdef
  have hgz : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 := by
    rw [hgdef]
    exact linMem_sep_mul h12
  have hgsm : ∀ (i : ℕ), i ≤ 6 → ∀ θ : ℝ,
      ContDiffOn ℝ i (fun z => g z θ) (Set.Ioi (0 : ℝ)) := by
    intro i hi θ
    rw [hgdef]
    exact (contDiffOn_const (c := gamCoef α θ)).mul (linMem_le_of_le (n := 6) (m := i) h12 hi)
  have hgθsm : ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 6 → ∀ θ : ℝ,
      ContDiffOn ℝ j (fun z => Work.Spaces.DthIter i g z θ) (Set.Ioi (0 : ℝ)) := by
    intro j i hi hij θ
    have hdec : (fun z => Work.Spaces.DthIter i g z θ)
        = fun z => Work.Spaces.dthU^[i] (gamCoef α) θ * Work.Construction.L12 f z := by
      funext z
      rw [hgdef]
      exact Work.Spaces.DthIter_decomp i (gamCoef α) (fun z => Work.Construction.L12 f z) z θ
    rw [hdec]
    exact (contDiffOn_const (c := Work.Spaces.dthU^[i] (gamCoef α) θ)).mul
      (linMem_le_of_le (n := 6) (m := j) h12 (by omega))
  have hZnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2 :=
    mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos 6).le (sq_nonneg _)
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => acoef z * g z θ) z θ
        ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2)
            * (Mth6 α θ * SlotSum (fun z => Work.Construction.L12 f z) z) := by
    intro z hz θ hθ
    have h1 := zmul_finite6 α acoef g hK hzb (fun b _ => linMem_acoef b) hgsm hgθsm z hz θ hθ
    have h2 : Work.Spaces.HkIntegrand α 6 g z θ
        ≤ Mth6 α θ * SlotSum (fun z => Work.Construction.L12 f z) z := by
      rw [hgdef]
      exact hsep hθ
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hZnn)
  have hAcf : (fun z θ => Acoef α z θ * Mf f z θ) = fun z θ => acoef z * g z θ := by
    funext z θ
    rw [hgdef, Acoef_eq_mul]
    have hMf : Mf f z θ = Work.Construction.L12 f z := rfl
    rw [hMf]
    ring
  rw [hAcf]
  refine Work.FTS.LocData.HkMem_of_majorant α 6
    (f := fun z θ => acoef z * g z θ)
    (M := fun z θ => (Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2)
      * (Mth6 α θ * SlotSum (fun z => Work.Construction.L12 f z) z)) ?_ ?_ ?_ ?_
  · exact Work.FTS.EllipticEst.Cores.DiagEstEllT.continuousOn_HkIntegrand_of_contDiffOn
      (linMem_zmul_joint (n := 6) (linMem_acoef 6) hgz) α
  · intro z hz
    exact (((Mth6_integrable hα hα1).mul_const
      (SlotSum (fun z => Work.Construction.L12 f z) z)).const_mul _)
  · have h1 : (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2)
            * (Mth6 α θ * SlotSum (fun z => Work.Construction.L12 f z) z))
        = fun z => (Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2)
            * ((∫ θ in Work.Spaces.Iθ, Mth6 α θ)
              * SlotSum (fun z => Work.Construction.L12 f z) z) := by
      funext z
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
    rw [h1]
    exact (hslot.1.const_mul (∫ θ in Work.Spaces.Iθ, Mth6 α θ)).const_mul _
  · exact hpt


end Work.FTS.StrongPersist
