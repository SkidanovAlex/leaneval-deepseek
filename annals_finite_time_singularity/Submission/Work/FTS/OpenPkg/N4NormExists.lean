/-
# `OpenPkg/N4NormExists` — the inhabitation of `N4Norm'` (the migrated `n4norm_exists`)

`N4Norm'_exists` discharges the twelve fields of `Work.FTS.OpenPkg.N4Norm'` from the twelve field
lemmas of the table in `NormFields.lean`, in the exact `∃ C, 0 < C ∧ ∀ …` shape in which those
lemmas are stated, and produces `∃ Ci > 0, N4Norm' Ci α₂` for every `0 < α₂ ≤ 1`.

The proof is the constant bookkeeping: the twelve constants are chosen out of the existential
hypotheses (`Classical.choose`), `Ci` is taken to dominate them all, and each field is transferred
to `Ci` by monotonicity of multiplication (each right-hand side is nonnegative; for the two
`𝒲`-norm right-hand sides this is `supAbs_nonneg`/`WlInf_nonneg` below).

The ten field lemmas that are already proved plug in verbatim; the two which are still open
(`wang_field`, `wrad_field`) are hypotheses here, so this theorem is the exact reduction of the
`N4Norm'` inhabitation to those two statements. -/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.OpenPkg.NormFields
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.wprod_field_winf
import Submission.Work.FTS.OpenPkg.wtoh_field_winf
import Submission.Work.FTS.OpenPkg.l12H_field
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.OpenPkg.fkH_field
import Submission.Work.FTS.OpenPkg.l12diff_field
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.OpenPkg.angmul_field
import Submission.Work.FTS.OpenPkg.wmul_field
import Submission.Work.FTS.OpenPkg.wrad_field
import Submission.Work.FTS.OpenPkg.wang_field

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
