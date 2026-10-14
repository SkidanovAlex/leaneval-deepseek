import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.HkMem_mul_pth_flat
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row25
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.OpenPkg.wrad_field
import Submission.Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_LocDatum3a.L12_Jeps_interchange_mine
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow22 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Row 22 of the §8 table, in the `Ctx` packaging used by `NonlinRows`

`Work.FTS.Nonlin.N4sg α g = -(1/2)·FK(F_*)·D_θ g` is the slot of the transport estimate in which
the coefficient `-(1/2)·FK(F_*)` is a function of `z` alone and the derivative
`D_θ g = sin(2θ)·∂_θ g` falls on the test function.  The relevant clause of the primed interface
`Work.FTS.OpenPkg.N4Extra'` is `t4`,

  `|IP α (f·D_θ g) g| ≤ Ct·α^{-1/2}·WDp 4 f·|g|²_ℋ⁴`,

so everything reduces to the open-quadrant `D`-sup norm of the radial coefficient.  The two facts
needed about it:

* `FK (F_*(α)) z = α·(2z/(1+z)²) = α·2·hKer z` (`FstarPkg.FK_Fstar`), so the coefficient is
  `-α·hKer`, a constant multiple of the radial profile `hKer z = z/(1+z)²`;
* `WDp 4 (c·hKer) ≤ 200·C_W·|c|` (`RNP.hKerConstWlInf` for the `𝒲^{4,∞}`-membership and
  `OpenPkg.WDp_le_WlInf` for the comparison `WDp ≤ C_W·WlInf`).

The loss `α^{-1/2}·α = √α` is what produces the `√α` of the stated bound, with the constant
`K = Ct·(C_W·200) + 1`, positive because `Ct > 0`.

### The `ℋ⁴`-honesty conjunct

`N₄^{sg} = (-α·hKer)·D_θ g` is a `𝒲^{4,∞}`-coefficient times `D_θ g`, so the mixed product rule
`N4Norm'.wprod` applies, once `D_θ g ∈ ℋ⁴` — which follows from `RegQ α 5 g` by
`CoercivityFix.QuadPorts.RegQ_dth` (the Galerkin class supplies `RegQ α 6 g`).

The hypotheses `StarPkgo α Cs Φs` and `EllPkgGo α Ce g Φg` are not needed for this row;
`GalClass α g` is used only through `galClass_regQ4` and the `RegQ α 5 g` slice of its
`RegQ α 6`-membership. -/

/-- `(z,θ) ↦ c·z/(1+z)²` is `C^∞` on the open quadrant. -/
theorem hKerConst_smoothOpen (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => c * Work.Spaces.hKer z) := by
  refine smoothOpen_radial (r := fun z => c * Work.Spaces.hKer z) ?_
  intro n
  have hker : ContDiffOn ℝ n (fun z : ℝ => Work.Spaces.hKer z) (Set.Ioi 0) := by
    simp only [Work.Spaces.hKer_apply]
    refine ContDiffOn.div (n := (n : WithTop ℕ∞)) (s := Set.Ioi 0)
      (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))
      (((contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi 0)).add
        (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))).pow 2) ?_
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    exact pow_ne_zero 2 (by linarith)
  exact ContDiffOn.const_smul c hker


end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.N4NormExists =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Nonnegativity of the `ℒ^∞`-type norms of the right-hand sides -/

/-- The closed-quadrant supremum of `|g|` is nonnegative (`Spaces.supAbs` is Lean's junk value
`0` for unbounded functions, so this holds unconditionally). -/
theorem supAbs_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.supAbs g := by
  rw [Work.Spaces.supAbs]
  by_cases h : BddAbove {y : ℝ | ∃ z ∈ Work.Spaces.Iz, ∃ θ ∈ Work.Spaces.Iθ, y = |g z θ|}
  · have hmem : |g 0 0| ∈ {y : ℝ | ∃ z ∈ Work.Spaces.Iz, ∃ θ ∈ Work.Spaces.Iθ,
        y = |g z θ|} :=
      ⟨0, Set.mem_Ici.mpr le_rfl, 0, ⟨le_rfl, by linarith [Real.pi_pos]⟩, rfl⟩
    exact le_trans (abs_nonneg (g 0 0)) (le_csSup h hmem)
  · rw [csSup_of_not_bddAbove h, Real.sSup_empty]

/-- The `𝒲^{l,∞}`-norm is nonnegative. -/
theorem WlInf_nonneg (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.WlInf α l f := by
  rw [Work.Spaces.WlInf]
  refine add_nonneg (Finset.sum_nonneg fun k _ => supAbs_nonneg _) ?_
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  split_ifs with h
  · exact supAbs_nonneg _
  · exact le_rfl

/-! ## Relaxing the constant of a two-factor product bound -/

/-- `A ≤ C·g → C ≤ Ci → 0 ≤ g → A ≤ Ci·g`. -/
theorem relax1 {A C Ci g : ℝ} (hle : C ≤ Ci) (hg : 0 ≤ g) (h : A ≤ C * g) : A ≤ Ci * g :=
  le_trans h (mul_le_mul_of_nonneg_right hle hg)

/-- `A ≤ C·p·g → C ≤ Ci → 0 ≤ p → 0 ≤ g → A ≤ Ci·p·g` (the products associate to the left). -/
theorem relax2 {A C Ci p g : ℝ} (hle : C ≤ Ci) (hp : 0 ≤ p) (hg : 0 ≤ g)
    (h : A ≤ C * p * g) : A ≤ Ci * p * g := by
  refine le_trans h ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hle hp) hg

/-- `A ≤ C·p·f·g → … → A ≤ Ci·p·f·g`. -/
theorem relax3 {A C Ci p f g : ℝ} (hle : C ≤ Ci) (hp : 0 ≤ p) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (h : A ≤ C * p * f * g) : A ≤ Ci * p * f * g := by
  refine le_trans h ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hp) hf) hg

/-! ## The inhabitation -/

/-- **`N4Norm'` is inhabited**, from its twelve field lemmas in the `∃ C` form. -/
theorem N4Norm'_exists {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1)
    (prod : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Xn α (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g)
    (wprod : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f → HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Xn α (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Xn α g)
    (wtoh : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Fn,
      Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) →
      Xn α f ≤ C * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ))
    (l12H : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : Fn,
      HQo α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
      Xn α (fun z θ => Work.Construction.L12 g z) ≤ C * Xn α g)
    (l12zero : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Fn, HQo α 4 f →
      |Work.Construction.L12 f 0| ≤ C * Xn α f)
    (fkH : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : Fn,
      HQo α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
      Xn α (fun z _ => Work.Construction.FK g z) ≤ C * Xn α g)
    (l12diff : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : Fn, HQo α 4 g → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z)
    (radialMul : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (r : ℝ → ℝ) (g : Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 4 (fun z _ => r z) → Work.Spaces.HkMem α 4 g →
      (∀ b : ℕ, b ≤ 4 → Filter.Tendsto
        (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => r z) z 0) Filter.atTop (nhds 0)) →
      (∀ b : ℕ, b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b g z θ) Filter.atTop (nhds 0)) →
      Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) ∧
      Xn α (fun z θ => r z * g z θ) ≤ C * Xn α (fun z _ => r z) * Xn α g)
    (angmul : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
      ∀ (a : ℝ → ℝ) (f : Fn) (Ca : ℝ),
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ca) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ca * Real.sin (2 * θ)) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) ∧
      Xn α (fun z θ => a θ * f z θ) ≤ C * Ca * Xn α f)
    (wang : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
      ∀ (a : ℝ → ℝ) (h : Fn) (Ca : ℝ),
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      Work.FTS.EllipticEst.SmoothOpen h →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ca) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ca * Real.sin (2 * θ)) →
      WDMem 4 h →
      WDMem 4 (fun z θ => a θ * h z θ) ∧
      WDp 4 (fun z θ => a θ * h z θ) ≤ C * Ca * WDp 4 h)
    (wrad : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (φ : ℝ → ℝ) (h : Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ => φ z) →
      Work.FTS.EllipticEst.SmoothOpen h →
      WDMem 4 (fun z _ => φ z) → WDMem 4 h →
      WDMem 4 (fun z θ => φ z * h z θ) ∧
      WDp 4 (fun z θ => φ z * h z θ) ≤ C * WDp 4 (fun z _ => φ z) * WDp 4 h)
    (wmul : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      WDMem 4 f → WDMem 4 g →
      (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ,
        Work.Spaces.pzIter k g z 0 = 0 ∧ Work.Spaces.pzIter k g z (π / 2) = 0) →
      WDMem 4 (fun z θ => f z θ * g z θ) ∧
      WDp 4 (fun z θ => f z θ * g z θ) ≤ C * WDp 4 f * WDp 4 g) :
    ∃ Ci : ℝ, 0 < Ci ∧ N4Norm' Ci α₂ := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ := prod
  obtain ⟨C₂, hC₂, h₂⟩ := wprod
  obtain ⟨C₃, hC₃, h₃⟩ := wtoh
  obtain ⟨C₄, hC₄, h₄⟩ := l12H
  obtain ⟨C₅, hC₅, h₅⟩ := l12zero
  obtain ⟨C₆, hC₆, h₆⟩ := fkH
  obtain ⟨C₇, hC₇, h₇⟩ := radialMul
  obtain ⟨C₈, hC₈, h₈⟩ := angmul
  obtain ⟨C₉, hC₉, h₉⟩ := wang
  obtain ⟨C₁₀, hC₁₀, h₁₀⟩ := wrad
  obtain ⟨C₁₁, hC₁₁, h₁₁⟩ := wmul
  set Ci : ℝ := 1 + C₁ + C₂ + C₃ + C₄ + C₅ + C₆ + C₇ + C₈ + C₉ + C₁₀ + C₁₁ with hCidef
  have hCipos : 0 < Ci := by rw [hCidef]; positivity
  have h1le : C₁ ≤ Ci := by rw [hCidef]; linarith
  have h2le : C₂ ≤ Ci := by rw [hCidef]; linarith
  have h3le : C₃ ≤ Ci := by rw [hCidef]; linarith
  have h4le : C₄ ≤ Ci := by rw [hCidef]; linarith
  have h5le : C₅ ≤ Ci := by rw [hCidef]; linarith
  have h6le : C₆ ≤ Ci := by rw [hCidef]; linarith
  have h7le : C₇ ≤ Ci := by rw [hCidef]; linarith
  have h8le : C₈ ≤ Ci := by rw [hCidef]; linarith
  have h9le : C₉ ≤ Ci := by rw [hCidef]; linarith
  have h10le : C₁₀ ≤ Ci := by rw [hCidef]; linarith
  have h11le : C₁₁ ≤ Ci := by rw [hCidef]; linarith
  refine ⟨Ci, hCipos, N4Norm'_of_fields hα₂ hCipos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · -- `prod`
    intro α hα f g hf hg
    obtain ⟨hm, hb⟩ := h₁ α hα.1 (le_trans hα.2 hα₂1) f g hf hg
    exact ⟨hm, relax3 h1le (Real.rpow_nonneg hα.1.le _)
      (Work.Spaces.HkNorm_nonneg α 4 f) (Work.Spaces.HkNorm_nonneg α 4 g) hb⟩
  · -- `wprod`
    intro α hα f g hf hW hg
    obtain ⟨hm, hb⟩ := h₂ α hα.1 (le_trans hα.2 hα₂1) f g hf hW hg
    exact ⟨hm, relax3 h2le (Real.rpow_nonneg hα.1.le _)
      (WlInf_nonneg α 4 f) (Work.Spaces.HkNorm_nonneg α 4 g) hb⟩
  · -- `wtoh`
    intro α hα f hf hW
    exact relax1 h3le (WlInf_nonneg α 4 _)
      (h₃ α hα.1 (le_trans hα.2 hα₂1) f hf hW)
  · -- `l12H`
    intro α hα g hg h0
    obtain ⟨hm, hb⟩ := h₄ α hα.1 (le_trans hα.2 hα₂1) g hg h0
    exact ⟨hm, relax1 h4le (Work.Spaces.HkNorm_nonneg α 4 g) hb⟩
  · -- `l12zero`
    intro α hα f hf
    exact relax1 h5le (Work.Spaces.HkNorm_nonneg α 4 f)
      (h₅ α hα.1 (le_trans hα.2 hα₂1) f hf)
  · -- `fkH`
    intro α hα g hg h0
    obtain ⟨hm, hb⟩ := h₆ α hα.1 (le_trans hα.2 hα₂1) g hg h0
    exact ⟨hm, relax1 h6le (Work.Spaces.HkNorm_nonneg α 4 g) hb⟩
  · -- `l12diff`
    intro α hα g hg z hz
    exact l12diff α hα.1 (le_trans hα.2 hα₂1) g hg z hz
  · -- `radialMul`
    intro α hα r g hr hg hmr hmg hdr hdg
    obtain ⟨hm, hb⟩ := h₇ α hα.1 (le_trans hα.2 hα₂1) r g hr hg hmr hmg hdr hdg
    exact ⟨hm, relax2 h7le (Work.Spaces.HkNorm_nonneg α 4 (fun z _ => r z))
      (Work.Spaces.HkNorm_nonneg α 4 g) hb⟩
  · -- `angmul`
    intro α hα a f hsm ha hda hf hmem
    obtain ⟨hm, hb⟩ := h₈ α hα.1 (le_trans hα.2 hα₂1) a f Ci hsm ha hda hf hmem
    exact ⟨hm, relax2 h8le hCipos.le (Work.Spaces.HkNorm_nonneg α 4 f) hb⟩
  · -- `wang`
    intro α hα a h hsm hhsm ha hda hW
    obtain ⟨hm, hb⟩ := h₉ α hα.1 (le_trans hα.2 hα₂1) a h Ci hsm hhsm ha hda hW
    exact ⟨hm, relax2 h9le hCipos.le (WDp_nonneg 4 h) hb⟩
  · -- `wrad`
    intro α hα φ h hsm hhsm hW hWh
    obtain ⟨hm, hb⟩ := h₁₀ α hα.1 (le_trans hα.2 hα₂1) φ h hsm hhsm hW hWh
    exact ⟨hm, relax2 h10le (WDp_nonneg 4 (fun z _ => φ z)) (WDp_nonneg 4 h) hb⟩
  · -- `wmul`
    intro α hα f g hf hg hWf hWg hv
    obtain ⟨hm, hb⟩ := h₁₁ α hα.1 (le_trans hα.2 hα₂1) f g hf hg hWf hWg hv
    exact ⟨hm, relax2 h11le (WDp_nonneg 4 f) (WDp_nonneg 4 g) hb⟩

/-- **`N4Norm'` is inhabited from the delivered field lemmas.**  The ten field lemmas proved in
this directory are plugged in; only `wang_field` and `wrad_field` remain as hypotheses. -/
theorem N4Norm'_exists_of_proved {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1)
    (wang : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
      ∀ (a : ℝ → ℝ) (h : Fn) (Ca : ℝ),
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      Work.FTS.EllipticEst.SmoothOpen h →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ca) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ca * Real.sin (2 * θ)) →
      WDMem 4 h →
      WDMem 4 (fun z θ => a θ * h z θ) ∧
      WDp 4 (fun z θ => a θ * h z θ) ≤ C * Ca * WDp 4 h)
    (wrad : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (φ : ℝ → ℝ) (h : Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ => φ z) →
      Work.FTS.EllipticEst.SmoothOpen h →
      WDMem 4 (fun z _ => φ z) → WDMem 4 h →
      WDMem 4 (fun z θ => φ z * h z θ) ∧
      WDp 4 (fun z θ => φ z * h z θ) ≤ C * WDp 4 (fun z _ => φ z) * WDp 4 h) :
    ∃ Ci : ℝ, 0 < Ci ∧ N4Norm' Ci α₂ :=
  N4Norm'_exists hα₂ hα₂1 prod_field wprod_field_winf wtoh_field_winf l12H_field
    l12zero_field fkH_field
    (fun α hα hα1 g hg z hz => l12diff_field α g hα hα1 hg z hz)
    radialMul_field angmul_field wang wrad wmul_field

/-- **`N4Norm'` is inhabited** — all twelve field lemmas of this directory plugged in. -/
theorem N4Norm'_exists_of_all_fields {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) :
    ∃ Ci : ℝ, 0 < Ci ∧ N4Norm' Ci α₂ :=
  N4Norm'_exists_of_proved hα₂ hα₂1 wang_field wrad_field

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.BdryTraces_Jeps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Elementary tools for the boundary-trace transfer

`J_ε` is a weighted average of the shifted values of the profile (`abs_Jeps_le_sup`), so the
boundary traces of `J_ε g` follow from those of `g` as soon as the two weights `z · w z ^ 2` and
`sin (2θ) ^ e` can be compared with their shifted values.  Those comparisons are the content of
`Traces/wtZ_shift_mul_le.lean`, `Traces/sin_rpow_thShift_le.lean` and
`Traces/eventually_thShift_{lt,gt}.lean`; the two `zShift` facts are proved here. -/

/-- A real function which is eventually nonnegative and eventually `≤ ε` for every `ε > 0` tends
to `0`. -/
theorem tendsto_nhds_zero_of_eventually_le {l : Filter ℝ} {F : ℝ → ℝ}
    (hnn : ∀ᶠ x in l, 0 ≤ F x) (h : ∀ ε' > 0, ∀ᶠ x in l, F x ≤ ε') :
    Tendsto F l (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hnn] with x hx using lt_of_lt_of_le ha hx
  · have h2 : 0 < b / 2 := by linarith
    filter_upwards [h (b / 2) h2] with x hx using lt_of_le_of_lt hx (by linarith)

/-- The radial weight is positive on `z > 0`. -/
theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

/-- The `z`-shift `z ↦ z e^{-p}` is eventually `< δ` near `z = 0`, uniformly in `|p| ≤ ε`. -/
theorem eventually_zShift_lt (ε δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ z in 𝓝[>] (0 : ℝ), ∀ p : ℝ, |p| ≤ ε → zShift z p < δ := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ * Real.exp (-ε) by positivity)] with z hz
  intro p hp
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  calc zShift z p = z * Real.exp (-p) := rfl
    _ ≤ z * Real.exp ε :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hz1.le
    _ < δ * Real.exp (-ε) * Real.exp ε := mul_lt_mul_of_pos_right hz2 (Real.exp_pos _)
    _ = δ := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

/-- The `z`-shift `z ↦ z e^{-p}` is eventually `> Z` near `z = ∞`, uniformly in `|p| ≤ ε`. -/
theorem eventually_zShift_gt (ε Z : ℝ) :
    ∀ᶠ z in atTop, 0 < z ∧ ∀ p : ℝ, |p| ≤ ε → Z < zShift z p := by
  filter_upwards [eventually_gt_atTop (max (Z * Real.exp ε) 0)] with z hz
  have hz1 : 0 < z := lt_of_le_of_lt (le_max_right _ _) hz
  have hz2 : Z * Real.exp ε < z := lt_of_le_of_lt (le_max_left _ _) hz
  refine ⟨hz1, fun p hp => ?_⟩
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  have h1 : Real.exp (-ε) ≤ Real.exp (-p) := Real.exp_le_exp.mpr (by linarith)
  calc Z = Z * Real.exp ε * Real.exp (-ε) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ < z * Real.exp (-ε) := mul_lt_mul_of_pos_right hz2 (Real.exp_pos _)
    _ ≤ z * Real.exp (-p) := mul_le_mul_of_nonneg_left h1 hz1.le
    _ = zShift z p := rfl

theorem BdryTraces_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {α : ℝ} {k : ℕ} {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hbdd : ∀ a b : ℕ, a + b ≤ k → ∃ M : ℝ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed b a f z θ| ≤ M)
    (hz0 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
        z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2 ≤ ε')
    (hzin : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ Z : ℝ, ∀ z : ℝ, Z < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
        z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2 ≤ ε')
    (ht0 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε')
    (ht1 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < π / 2 → π / 2 - δ < θ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε') :
    Work.FTS.Nonlin.BdryTraces α k (Jeps ρ ε f) := by
  intro a b hab
  set g : ℝ → ℝ → ℝ := Work.Spaces.mixed b a f with hg
  have hcm : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.mixed b a (Jeps ρ ε f) z θ = Jeps ρ ε g z θ :=
    fun z θ hz hθ => mixed_Jeps ρ hρ.moll hε hsm hz hθ b a
  have hIθ : Set.Ioo 0 (π / 2) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)
  have hIθ' : Set.Ioo 0 (π / 2) ∈ 𝓝[<] (π / 2) :=
    Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)
  have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := self_mem_nhdsWithin
  refine ⟨fun θ hθ => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩⟩
  · -- ### `z → 0⁺`
    have hlim : Tendsto (fun z : ℝ => z * (Jeps ρ ε g z θ * Work.Spaces.w z) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_nhds_zero_of_eventually_le ?_ ?_
      · filter_upwards [hIoi] with z hz using mul_nonneg hz.le (sq_nonneg _)
      · intro ε' hε'
        obtain ⟨δ, hδpos, hδ⟩ :=
          hz0 a b hab (ε' / Real.exp (3 * ε)) (div_pos hε' (Real.exp_pos _))
        have hzs : ∀ᶠ z in 𝓝[>] (0 : ℝ), ∀ p : ℝ, |p| ≤ ε → zShift z p < δ :=
          eventually_zShift_lt ε δ hδpos
        filter_upwards [hIoi, hzs] with z hz hzs
        have hzw : 0 < z * Work.Spaces.w z ^ 2 := mul_pos hz (pow_pos (w_pos_of_pos hz) 2)
        set M : ℝ := Real.sqrt (ε' / (z * Work.Spaces.w z ^ 2)) with hMdef
        have hMn : 0 ≤ M := Real.sqrt_nonneg _
        have hMsq : M ^ 2 = ε' / (z * Work.Spaces.w z ^ 2) :=
          Real.sq_sqrt (div_nonneg hε'.le hzw.le)
        have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
            |g (zShift z p.1) (thShift θ p.2)| ≤ M := by
          intro p hp1 hp2
          have hz1 : 0 < zShift z p.1 := zShift_pos hz
          have hzδ : zShift z p.1 < δ := hzs p.1 hp1
          have hth : thShift θ p.2 ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
          have hhyp := hδ (zShift z p.1) hz1 hzδ (thShift θ p.2) hth
          have hwt := Traces.wtZ_shift_mul_le z p.1 ε hz hε.le hp1
          have hsq : (g (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ M ^ 2 := by
            rw [hMsq, le_div_iff₀ hzw]
            have hhyp' : (zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)
                * (g (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ ε' / Real.exp (3 * ε) := by
              have h := hhyp
              rw [mul_pow] at h
              calc (zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)
                    * (g (zShift z p.1) (thShift θ p.2)) ^ 2
                  = zShift z p.1 * ((g (zShift z p.1) (thShift θ p.2)) ^ 2
                      * Work.Spaces.w (zShift z p.1) ^ 2) := by ring
                _ ≤ ε' / Real.exp (3 * ε) := h
            calc (g (zShift z p.1) (thShift θ p.2)) ^ 2 * (z * Work.Spaces.w z ^ 2)
                ≤ (g (zShift z p.1) (thShift θ p.2)) ^ 2
                    * (Real.exp (3 * ε)
                        * (zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)) :=
                  mul_le_mul_of_nonneg_left hwt (sq_nonneg _)
              _ = Real.exp (3 * ε) * ((zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)
                    * (g (zShift z p.1) (thShift θ p.2)) ^ 2) := by ring
              _ ≤ Real.exp (3 * ε) * (ε' / Real.exp (3 * ε)) :=
                  mul_le_mul_of_nonneg_left hhyp' (Real.exp_pos _).le
              _ = ε' := by rw [mul_div_cancel₀ _ (Real.exp_pos _).ne']
          have hsq' : |g (zShift z p.1) (thShift θ p.2)| ≤ |M| := sq_le_sq.mp hsq
          rwa [abs_of_nonneg hMn] at hsq'
        have hjep : |Jeps ρ ε g z θ| ≤ M := abs_Jeps_le_sup ρ hρ.moll hε hz hθ hMb hMn
        have hjsq : (Jeps ρ ε g z θ) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hjep 2
        calc z * (Jeps ρ ε g z θ * Work.Spaces.w z) ^ 2
            = z * Work.Spaces.w z ^ 2 * (Jeps ρ ε g z θ) ^ 2 := by ring
          _ ≤ z * Work.Spaces.w z ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hjsq hzw.le
          _ = z * Work.Spaces.w z ^ 2 * (ε' / (z * Work.Spaces.w z ^ 2)) := by rw [hMsq]
          _ = ε' := by rw [mul_div_cancel₀ _ hzw.ne']
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hIoi] with z hz
    rw [hcm z θ hz hθ]
  · -- ### `z → ∞`
    have hlim : Tendsto (fun z : ℝ => z * (Jeps ρ ε g z θ * Work.Spaces.w z) ^ 2)
        atTop (𝓝 0) := by
      refine tendsto_nhds_zero_of_eventually_le ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz using
          mul_nonneg hz.le (sq_nonneg _)
      · intro ε' hε'
        obtain ⟨Z, hZ⟩ := hzin a b hab (ε' / Real.exp (3 * ε)) (div_pos hε' (Real.exp_pos _))
        have hzs : ∀ᶠ z in atTop, 0 < z ∧ ∀ p : ℝ, |p| ≤ ε → Z < zShift z p :=
          eventually_zShift_gt ε Z
        filter_upwards [hzs] with z hz
        obtain ⟨hzpos, hzs⟩ := hz
        have hzw : 0 < z * Work.Spaces.w z ^ 2 := mul_pos hzpos (pow_pos (w_pos_of_pos hzpos) 2)
        set M : ℝ := Real.sqrt (ε' / (z * Work.Spaces.w z ^ 2)) with hMdef
        have hMn : 0 ≤ M := Real.sqrt_nonneg _
        have hMsq : M ^ 2 = ε' / (z * Work.Spaces.w z ^ 2) :=
          Real.sq_sqrt (div_nonneg hε'.le hzw.le)
        have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
            |g (zShift z p.1) (thShift θ p.2)| ≤ M := by
          intro p hp1 hp2
          have hz1 : 0 < zShift z p.1 := zShift_pos hzpos
          have hzZ : Z < zShift z p.1 := hzs p.1 hp1
          have hth : thShift θ p.2 ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
          have hhyp := hZ (zShift z p.1) hzZ (thShift θ p.2) hth
          have hwt := Traces.wtZ_shift_mul_le z p.1 ε hzpos hε.le hp1
          have hsq : (g (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ M ^ 2 := by
            rw [hMsq, le_div_iff₀ hzw]
            have hhyp' : (zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)
                * (g (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ ε' / Real.exp (3 * ε) := by
              have h := hhyp
              rw [mul_pow] at h
              calc (zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)
                    * (g (zShift z p.1) (thShift θ p.2)) ^ 2
                  = zShift z p.1 * ((g (zShift z p.1) (thShift θ p.2)) ^ 2
                      * Work.Spaces.w (zShift z p.1) ^ 2) := by ring
                _ ≤ ε' / Real.exp (3 * ε) := h
            calc (g (zShift z p.1) (thShift θ p.2)) ^ 2 * (z * Work.Spaces.w z ^ 2)
                ≤ (g (zShift z p.1) (thShift θ p.2)) ^ 2
                    * (Real.exp (3 * ε)
                        * (zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)) :=
                  mul_le_mul_of_nonneg_left hwt (sq_nonneg _)
              _ = Real.exp (3 * ε) * ((zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)
                    * (g (zShift z p.1) (thShift θ p.2)) ^ 2) := by ring
              _ ≤ Real.exp (3 * ε) * (ε' / Real.exp (3 * ε)) :=
                  mul_le_mul_of_nonneg_left hhyp' (Real.exp_pos _).le
              _ = ε' := by rw [mul_div_cancel₀ _ (Real.exp_pos _).ne']
          have hsq' : |g (zShift z p.1) (thShift θ p.2)| ≤ |M| := sq_le_sq.mp hsq
          rwa [abs_of_nonneg hMn] at hsq'
        have hjep : |Jeps ρ ε g z θ| ≤ M := abs_Jeps_le_sup ρ hρ.moll hε hzpos hθ hMb hMn
        have hjsq : (Jeps ρ ε g z θ) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hjep 2
        calc z * (Jeps ρ ε g z θ * Work.Spaces.w z) ^ 2
            = z * Work.Spaces.w z ^ 2 * (Jeps ρ ε g z θ) ^ 2 := by ring
          _ ≤ z * Work.Spaces.w z ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hjsq hzw.le
          _ = z * Work.Spaces.w z ^ 2 * (ε' / (z * Work.Spaces.w z ^ 2)) := by rw [hMsq]
          _ = ε' := by rw [mul_div_cancel₀ _ hzw.ne']
    refine Tendsto.congr' ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    rw [hcm z θ hz hθ]
  · -- ### `θ → 0⁺`
    have hlim : Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Jeps ρ ε g z θ) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_nhds_zero_of_eventually_le ?_ ?_
      · filter_upwards [hIθ] with θ hθ using
          mul_nonneg (Real.rpow_nonneg (sin_two_nonneg ⟨hθ.1.le, by linarith [hθ.2]⟩) _)
            (sq_nonneg _)
      · intro ε' hε'
        obtain ⟨δ, hδpos, hδ⟩ := ht0 a b hab (ε' / Real.exp (ε * |(1 - Work.Spaces.gam α)|))
          (div_pos hε' (Real.exp_pos _))
        have hθs : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ p : ℝ, |p| ≤ ε → thShift θ p < δ :=
          Traces.eventually_thShift_lt ε δ hδpos
        filter_upwards [hIθ, hθs] with θ hθ hθs
        have hsEpos : 0 < Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_pos_of_pos (sin_two_pos hθ) _
        set M : ℝ := Real.sqrt (ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) with hMdef
        have hMn : 0 ≤ M := Real.sqrt_nonneg _
        have hMsq : M ^ 2 = ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.sq_sqrt (div_nonneg hε'.le hsEpos.le)
        have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
            |g (zShift z p.1) (thShift θ p.2)| ≤ M := by
          intro p hp1 hp2
          have hz1 : 0 < zShift z p.1 := zShift_pos hz
          have hth : thShift θ p.2 ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
          have hthδ : thShift θ p.2 < δ := hθs p.2 hp2
          have hhyp := hδ (thShift θ p.2) hth.1 hthδ (zShift z p.1) hz1
          have hcmp := Traces.sin_rpow_thShift_le θ p.2 ε (1 - Work.Spaces.gam α) hθ hε.le hp2
          have hsq : (g (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ M ^ 2 := by
            rw [hMsq, le_div_iff₀ hsEpos]
            calc (g (zShift z p.1) (thShift θ p.2)) ^ 2
                  * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                ≤ (g (zShift z p.1) (thShift θ p.2)) ^ 2
                    * (Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                        * Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)) :=
                  mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
              _ = Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                    * (Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)
                        * (g (zShift z p.1) (thShift θ p.2)) ^ 2) := by ring
              _ ≤ Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                    * (ε' / Real.exp (ε * |(1 - Work.Spaces.gam α)|)) :=
                  mul_le_mul_of_nonneg_left hhyp (Real.exp_pos _).le
              _ = ε' := by rw [mul_div_cancel₀ _ (Real.exp_pos _).ne']
          have hsq' : |g (zShift z p.1) (thShift θ p.2)| ≤ |M| := sq_le_sq.mp hsq
          rwa [abs_of_nonneg hMn] at hsq'
        have hjep : |Jeps ρ ε g z θ| ≤ M := abs_Jeps_le_sup ρ hρ.moll hε hz hθ hMb hMn
        have hjsq : (Jeps ρ ε g z θ) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hjep 2
        calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Jeps ρ ε g z θ) ^ 2
            ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * M ^ 2 :=
              mul_le_mul_of_nonneg_left hjsq hsEpos.le
          _ = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                * (ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) := by rw [hMsq]
          _ = ε' := by rw [mul_div_cancel₀ _ hsEpos.ne']
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hIθ] with θ hθ
    rw [hcm z θ hz hθ]
  · -- ### `θ → (π/2)⁻`
    have hlim : Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Jeps ρ ε g z θ) ^ 2) (𝓝[<] (π / 2)) (𝓝 0) := by
      refine tendsto_nhds_zero_of_eventually_le ?_ ?_
      · filter_upwards [hIθ'] with θ hθ using
          mul_nonneg (Real.rpow_nonneg (sin_two_nonneg ⟨hθ.1.le, by linarith [hθ.2]⟩) _)
            (sq_nonneg _)
      · intro ε' hε'
        obtain ⟨δ, hδpos, hδ⟩ := ht1 a b hab (ε' / Real.exp (ε * |(1 - Work.Spaces.gam α)|))
          (div_pos hε' (Real.exp_pos _))
        have hθs : ∀ᶠ θ in 𝓝[<] (π / 2), ∀ p : ℝ, |p| ≤ ε → π / 2 - δ < thShift θ p :=
          Traces.eventually_thShift_gt ε δ hδpos
        filter_upwards [hIθ', hθs] with θ hθ hθs
        have hsEpos : 0 < Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_pos_of_pos (sin_two_pos hθ) _
        set M : ℝ := Real.sqrt (ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) with hMdef
        have hMn : 0 ≤ M := Real.sqrt_nonneg _
        have hMsq : M ^ 2 = ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.sq_sqrt (div_nonneg hε'.le hsEpos.le)
        have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
            |g (zShift z p.1) (thShift θ p.2)| ≤ M := by
          intro p hp1 hp2
          have hz1 : 0 < zShift z p.1 := zShift_pos hz
          have hth : thShift θ p.2 ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
          have hthδ : π / 2 - δ < thShift θ p.2 := hθs p.2 hp2
          have hhyp := hδ (thShift θ p.2) hth.2 hthδ (zShift z p.1) hz1
          have hcmp := Traces.sin_rpow_thShift_le θ p.2 ε (1 - Work.Spaces.gam α) hθ hε.le hp2
          have hsq : (g (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ M ^ 2 := by
            rw [hMsq, le_div_iff₀ hsEpos]
            calc (g (zShift z p.1) (thShift θ p.2)) ^ 2
                  * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                ≤ (g (zShift z p.1) (thShift θ p.2)) ^ 2
                    * (Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                        * Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)) :=
                  mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
              _ = Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                    * (Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)
                        * (g (zShift z p.1) (thShift θ p.2)) ^ 2) := by ring
              _ ≤ Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                    * (ε' / Real.exp (ε * |(1 - Work.Spaces.gam α)|)) :=
                  mul_le_mul_of_nonneg_left hhyp (Real.exp_pos _).le
              _ = ε' := by rw [mul_div_cancel₀ _ (Real.exp_pos _).ne']
          have hsq' : |g (zShift z p.1) (thShift θ p.2)| ≤ |M| := sq_le_sq.mp hsq
          rwa [abs_of_nonneg hMn] at hsq'
        have hjep : |Jeps ρ ε g z θ| ≤ M := abs_Jeps_le_sup ρ hρ.moll hε hz hθ hMb hMn
        have hjsq : (Jeps ρ ε g z θ) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hjep 2
        calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Jeps ρ ε g z θ) ^ 2
            ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * M ^ 2 :=
              mul_le_mul_of_nonneg_left hjsq hsEpos.le
          _ = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                * (ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) := by rw [hMsq]
          _ = ε' := by rw [mul_div_cancel₀ _ hsEpos.ne']
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hIθ'] with θ hθ
    rw [hcm z θ hz hθ]

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.L12_Jeps_locG6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false

/-! ## `L₁₂` of a separable datum -/

/-- The angular density of a separable datum: `L₁₂dens(K)(R·G)(s) = (R(s)/s)·∫_θ K(θ)G(θ)`. -/
lemma L12dens_sep_mul (R G : ℝ → ℝ) (s : ℝ) :
    Work.FM.L12dens Work.Spaces.K (fun z θ => R z * G θ) s
      = (R s / s) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ) := by
  simp only [Work.FM.L12dens, Work.Spaces.Iθ]
  rw [show (∫ θ in Set.Icc (0 : ℝ) (π / 2), Work.Spaces.K θ * (R s * G θ) / s)
      = ∫ θ in Set.Icc (0 : ℝ) (π / 2), (R s / s) * (Work.Spaces.K θ * G θ) from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]

/-- **`L₁₂` of a separable datum**: `L₁₂(R·G)(0) = (∫_θ K G)·(∫_s R(s)/s)`. -/
lemma L12_sep_mul (R G : ℝ → ℝ) :
    Work.FM.L12 Work.Spaces.K (fun z θ => R z * G θ) 0
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ) * (∫ s in Set.Ioi (0 : ℝ), R s / s) := by
  simp only [Work.FM.L12]
  rw [show (∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K (fun z θ => R z * G θ) s)
      = ∫ s in Set.Ioi (0 : ℝ), (R s / s) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ) from
    setIntegral_congr_fun measurableSet_Ioi (fun s _ => L12dens_sep_mul R G s)]
  rw [MeasureTheory.integral_mul_const]
  exact mul_comm _ _

/-- The same computation for a datum already *shifted* in the log-coordinates:
`L₁₂ (z ↦ R(z e^{-p₁}) · G(thShift · p₂))(0) = (∫_s R(s)/s)·(∫_θ K(θ)G(thShift θ p₂))`.
The `z`-integral is invariant under `s ↦ c s` for `ds/s`
(`Work.FTS_LocDatum3a.integral_comp_mul_Ioi`). -/
lemma L12_sep_mul_shift (R G : ℝ → ℝ) (p₁ p₂ : ℝ) :
    Work.FM.L12 Work.Spaces.K
        (fun z θ => R (Work.FTS.StrongEps.zShift z p₁) * G (Work.FTS.StrongEps.thShift θ p₂)) 0
      = (∫ s in Set.Ioi (0 : ℝ), R s / s)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G (Work.FTS.StrongEps.thShift θ p₂)) := by
  have hc : (0 : ℝ) < Real.exp (-p₁) := Real.exp_pos _
  have hswap : (∫ s in Set.Ioi (0 : ℝ), R (Work.FTS.StrongEps.zShift s p₁) / s)
      = ∫ s in Set.Ioi (0 : ℝ), R s / s := by
    rw [show (∫ s in Set.Ioi (0 : ℝ), R (Work.FTS.StrongEps.zShift s p₁) / s)
        = ∫ s in Set.Ioi (0 : ℝ), R (Real.exp (-p₁) * s) / s from
      setIntegral_congr_fun measurableSet_Ioi
        (fun s _ => by rw [Work.FTS.StrongEps.zShift, mul_comm])]
    exact integral_comp_mul_Ioi hc R
  rw [L12_sep_mul (fun z => R (Work.FTS.StrongEps.zShift z p₁))
      (fun θ => G (Work.FTS.StrongEps.thShift θ p₂)), hswap]
  ring

/-- The normalisation constant `c(α)` with the factors in the order used by `L₁₂dens`. -/
lemma c_eq_int (α : ℝ) :
    Work.Spaces.c α = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ := by
  rw [Work.Spaces.c]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-! ## The angular factor `Γ(α)` -/

/-- `Γ(α)` is continuous (the exponent `α/3` is nonnegative). -/
lemma continuous_Gam (α : ℝ) (hα : 0 < α) : Continuous (Work.Spaces.Gam α) := by
  have h : Continuous fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 := by fun_prop
  exact h.rpow_const (fun θ => Or.inr (by positivity))

/-- `Γ(α)` is measurable. -/
lemma measurable_Gam (α : ℝ) (hα : 0 ≤ α) : Measurable (Work.Spaces.Gam α) := by
  have hbase : Measurable fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 :=
    Real.continuous_sin.measurable.mul
      (by fun_prop : Continuous fun θ : ℝ => Real.cos θ ^ 2).measurable
  have hrp : Measurable fun x : ℝ => x ^ (α / 3) :=
    (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ α / 3)).measurable
  rw [show Work.Spaces.Gam α = fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl]
  exact hrp.comp hbase

/-- `|Γ(α)| ≤ 1` everywhere. -/
lemma abs_Gam_le_one (α : ℝ) (hα : 0 < α) (θ : ℝ) : |Work.Spaces.Gam α θ| ≤ 1 := by
  have hy : (0 : ℝ) ≤ α / 3 := by positivity
  have habs : |Real.sin θ * Real.cos θ ^ 2| ≤ 1 := by
    have hs : |Real.sin θ| ≤ 1 := abs_le.mpr (Real.sin_mem_Icc θ)
    have hc : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have hc0 : 0 ≤ |Real.cos θ| := abs_nonneg _
    calc |Real.sin θ * Real.cos θ ^ 2| = |Real.sin θ| * |Real.cos θ| ^ 2 := by
          rw [abs_mul, abs_pow]
      _ ≤ 1 * 1 ^ 2 := by
          exact mul_le_mul hs (pow_le_pow_left₀ hc0 hc 2) (by positivity) (by norm_num)
      _ = 1 := by norm_num
  calc |Work.Spaces.Gam α θ| = |(Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)| := rfl
    _ ≤ |Real.sin θ * Real.cos θ ^ 2| ^ (α / 3) := Real.abs_rpow_le_abs_rpow _ _
    _ ≤ 1 ^ (α / 3) := Real.rpow_le_rpow (abs_nonneg _) habs hy
    _ = 1 := Real.one_rpow _

/-! ## The hypothesis `L₁₂(locG6)(0) = 0` is `∫ R(s)/s ds = 0` -/

/-- **The normalisation hypothesis in radial form**: if `L₁₂(locG6 α L β)(0) = 0` then the
radial factor satisfies `∫_0^∞ locR(s)/s ds = 0`. -/
lemma locR_Lambda_zero (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (h12 : Work.Construction.L12 (Work.FTS.LocData6.locG6 α L β) 0 = 0) :
    (∫ s in Set.Ioi (0 : ℝ), Work.FTS.LocDataExt.locR α L β s / s) = 0 := by
  have hfact : Work.FTS.LocData6.locG6 α L β
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ :=
    Work.FTS.LocDataExt.locG_eq_locR_Gam α L β
  have h1 : Work.Construction.L12 (Work.FTS.LocData6.locG6 α L β) 0
      = Work.Spaces.c α * (∫ s in Set.Ioi (0 : ℝ), Work.FTS.LocDataExt.locR α L β s / s) := by
    rw [show Work.Construction.L12 (Work.FTS.LocData6.locG6 α L β) 0
        = Work.FM.L12 Work.Spaces.K
            (fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ) 0 from by
      rw [hfact]
      rfl]
    rw [L12_sep_mul, c_eq_int]
  have hz : Work.Spaces.c α * (∫ s in Set.Ioi (0 : ℝ), Work.FTS.LocDataExt.locR α L β s / s)
      = 0 := by rw [← h1, h12]
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  exact (mul_eq_zero.mp hz).resolve_left hc

/-! ## The radial factor `locR`: measurability, vanishing near `0` and decay -/

/-- `|F_{*,rad}(z)| ≤ 2/(1+z)` for `z > 0`. -/
lemma abs_Fstar_le (z : ℝ) (hz : 0 < z) : |Work.FM.Fstar z| ≤ 2 / (1 + z) := by
  have hz1 : 0 < 1 + z := by linarith
  have hzle : z / (1 + z) ≤ 1 := by rw [div_le_one hz1]; linarith
  rw [Work.FM.Fstar, abs_div, abs_of_nonneg (sq_nonneg (1 + z)), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hz,
    show 2 * z / (1 + z) ^ 2 = (2 / (1 + z)) * (z / (1 + z)) from by field_simp]
  exact mul_le_of_le_one_right (by positivity) hzle

/-- `|zfarR L z| ≤ 2/(1+z)` for `z > 0`. -/
lemma abs_zfarR_le (L : ℝ) (z : ℝ) (hz : 0 < z) :
    |Work.FTS.LocDataExt.zfarR L z| ≤ 2 / (1 + z) := by
  rw [Work.FTS.LocDataExt.zfarR_apply, abs_mul]
  refine (mul_le_of_le_one_left (abs_nonneg _) ?_).trans (abs_Fstar_le z hz)
  rw [abs_le]
  exact ⟨by linarith [Work.Stability.chi_le_one (z / L)],
    by linarith [Work.Stability.chi_nonneg (z / L)]⟩

/-- `zfarR L` is measurable. -/
lemma measurable_zfarR (L : ℝ) : Measurable (Work.FTS.LocDataExt.zfarR L) := by
  have hchi : Measurable fun z : ℝ => Work.Stability.chi (z / L) :=
    Work.Stability.chi_continuous.measurable.comp (by fun_prop)
  have hF : Measurable fun z : ℝ => (2 * z) / (1 + z) ^ 2 := by measurability
  rw [show Work.FTS.LocDataExt.zfarR L
      = fun z : ℝ => (1 - Work.Stability.chi (z / L)) * ((2 * z) / (1 + z) ^ 2) from rfl]
  exact (measurable_const.sub hchi).mul hF

/-- `bumpZ` is measurable. -/
lemma measurable_bumpZ : Measurable Work.FTS.LocData.bumpZ := by
  rw [show Work.FTS.LocData.bumpZ
      = fun z : ℝ => Work.Stability.chi (4 * z - 5) from rfl]
  exact Work.Stability.chi_continuous.measurable.comp (by fun_prop)

/-- `locR α L β` is measurable. -/
lemma measurable_locR (α L β : ℝ) : Measurable (Work.FTS.LocDataExt.locR α L β) := by
  have hz := measurable_zfarR L
  have hb := measurable_bumpZ
  rw [show Work.FTS.LocDataExt.locR α L β
      = fun z : ℝ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z
          + β * Work.FTS.LocData.bumpZ z from rfl]
  exact (measurable_const.mul hz).add (measurable_const.mul hb)

/-- `locR α L β` vanishes on `(0, 3/4]` (the cut-off factors of both summands are `0` there). -/
lemma locR_vanish (α L β : ℝ) (hL : 1 ≤ L) :
    ∀ z, 0 < z → z ≤ 3 / 4 → Work.FTS.LocDataExt.locR α L β z = 0 := by
  intro z hz hz34
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [Work.FTS.LocDataExt.locR_apply,
    Work.FTS.LocDataExt.zfarR_eq_zero_of_le hLpos hz.le (by linarith),
    Work.FTS.LocDataExt.bumpZ_eq_zero_of_le hz34]
  ring

/-- The decay `|locR α L β z| ≤ C/(1+z)` for `z > 0`. -/
lemma locR_decay (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, 0 < z →
      |Work.FTS.LocDataExt.locR α L β z| ≤ C / (1 + z) := by
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hbump1 : ∀ z : ℝ, |Work.FTS.LocData.bumpZ z| ≤ 1 := by
    intro z
    rw [Work.FTS.LocData.bumpZ_apply]
    exact abs_le.mpr ⟨by linarith [Work.Stability.chi_nonneg (4 * z - 5)],
      Work.Stability.chi_le_one (4 * z - 5)⟩
  refine ⟨20 * α + 3 * |β| + 1, by positivity, fun z hz => ?_⟩
  have hz1 : 0 < 1 + z := by linarith
  have h1 : |-(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z| ≤ 20 * α / (1 + z) := by
    rw [abs_mul, abs_neg, abs_div, abs_of_pos hcpos, abs_of_pos hα]
    have h2 : α / Work.Spaces.c α ≤ 10 * α := by
      rw [div_le_iff₀ hcpos]
      have := mul_le_mul_of_nonneg_left hc hα.le
      nlinarith
    calc α / Work.Spaces.c α * |Work.FTS.LocDataExt.zfarR L z|
        ≤ 10 * α * (2 / (1 + z)) :=
          mul_le_mul h2 (abs_zfarR_le L z hz) (abs_nonneg _) (by positivity)
      _ = 20 * α / (1 + z) := by ring
  have h3 : |β * Work.FTS.LocData.bumpZ z| ≤ 3 * |β| / (1 + z) := by
    rw [abs_mul]
    by_cases hle : z ≤ 7 / 4
    · have h4 : (1 : ℝ) ≤ 3 / (1 + z) := by
        rw [le_div_iff₀ hz1]
        linarith
      calc |β| * |Work.FTS.LocData.bumpZ z| ≤ |β| * 1 :=
            mul_le_mul_of_nonneg_left (hbump1 z) (abs_nonneg β)
        _ = |β| := by ring
        _ ≤ |β| * (3 / (1 + z)) := le_mul_of_one_le_right (abs_nonneg β) h4
        _ = 3 * |β| / (1 + z) := by ring
    · have hz0 : Work.FTS.LocData.bumpZ z = 0 := by
        refine Work.FTS.LocData.bumpZ_eq_zero_of_notMem ?_
        simp only [Set.mem_Icc, not_and_or, not_le]
        exact Or.inr (by linarith)
      rw [hz0, abs_zero, mul_zero]
      positivity
  rw [Work.FTS.LocDataExt.locR_apply]
  calc |-(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z
          + β * Work.FTS.LocData.bumpZ z|
      ≤ |-(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z|
        + |β * Work.FTS.LocData.bumpZ z| := abs_add_le _ _
    _ ≤ 20 * α / (1 + z) + 3 * |β| / (1 + z) := add_le_add h1 h3
    _ ≤ (20 * α + 3 * |β| + 1) / (1 + z) := by
        rw [← add_div, div_le_div_iff_of_pos_right hz1]
        linarith

/-- Measurability of the separable datum `(z,θ) ↦ locR z · Γ(α)(θ)`. -/
lemma measurable_uncurry_locR_Gam (α L β : ℝ) (hα : 0 < α) :
    Measurable (Function.uncurry (fun z θ => Work.FTS.LocDataExt.locR α L β z
      * Work.Spaces.Gam α θ)) := by
  have hlocR := measurable_locR α L β
  have hGam := measurable_Gam α hα.le
  rw [show Function.uncurry (fun z θ => Work.FTS.LocDataExt.locR α L β z
      * Work.Spaces.Gam α θ)
      = fun x : ℝ × ℝ => Work.FTS.LocDataExt.locR α L β x.1 * Work.Spaces.Gam α x.2 from rfl]
  exact (hlocR.comp measurable_fst).mul (hGam.comp measurable_snd)

/-! ## The target -/

theorem L12_Jeps_locG6 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (h12 : Work.Construction.L12 (Work.FTS.LocData6.locG6 α L β) 0 = 0) :
    Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.LocData6.locG6 α L β)) 0 = 0 := by
  obtain ⟨C, hCpos, hCb⟩ := locR_decay α L β hα hα1
  have hΛ : (∫ s in Set.Ioi (0 : ℝ), Work.FTS.LocDataExt.locR α L β s / s) = 0 :=
    locR_Lambda_zero α L β hα hα1 h12
  have hFm : Measurable (Function.uncurry (fun z θ => Work.FTS.LocDataExt.locR α L β z
      * Work.Spaces.Gam α θ)) := measurable_uncurry_locR_Gam α L β hα
  have hF0 : ∀ z θ, 0 < z → z ≤ 3 / 4 →
      (fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ) z θ = 0 := by
    intro z θ hz hza
    show Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ = 0
    rw [locR_vanish α L β hL z hz hza, zero_mul]
  have hFg : ∀ z θ, 0 < z →
      |(fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ) z θ|
        ≤ C / (1 + z) := by
    intro z θ hz
    show |Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ| ≤ C / (1 + z)
    rw [abs_mul]
    calc |Work.FTS.LocDataExt.locR α L β z| * |Work.Spaces.Gam α θ|
        ≤ (C / (1 + z)) * 1 :=
          mul_le_mul (hCb z hz) (abs_Gam_le_one α hα θ) (abs_nonneg _) (by positivity)
      _ = C / (1 + z) := by ring
  have hkey := L12_Jeps_interchange_mine (ρ := ρ) hρ.moll hε
      (F := fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ)
      (a := 3 / 4) (C := C) (by norm_num) hFm hF0 hFg
  have hfact : Work.FTS.LocData6.locG6 α L β
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ :=
    Work.FTS.LocDataExt.locG_eq_locR_Gam α L β
  rw [show Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.LocData6.locG6 α L β)) 0
      = Work.FM.L12 Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε
          (fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ)) 0 from by
    rw [hfact]
    rfl]
  rw [hkey]
  have hshift : ∀ p : ℝ × ℝ, Work.FM.L12 Work.Spaces.K
      (fun z θ => (fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ)
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) 0
      = (∫ s in Set.Ioi (0 : ℝ), Work.FTS.LocDataExt.locR α L β s / s)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
            * Work.Spaces.Gam α (Work.FTS.StrongEps.thShift θ p.2)) :=
    fun p => L12_sep_mul_shift (Work.FTS.LocDataExt.locR α L β) (Work.Spaces.Gam α) p.1 p.2
  simp only [hshift]
  rw [hΛ]
  simp

end Work.FTS_LocDatum3a
end
end
