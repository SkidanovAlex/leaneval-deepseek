/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PTgadgets` — reusable pointwise input for `N0_N_Transport_pt_le`

The lemmas collected here decompose the hypotheses of
`Work.FTS.StrongEps.E5Aux2.N0_N_Transport_pt_le` into pointwise statements:

* `pt_EpsDecay_slots` — the seven slot bounds of the interface `EpsDecay`, normalised to
  `≤ 1` (the majorant is `≤ 1`);
* `pt_Fstar_pt_data` — the pointwise data of the reference profile `F_*`;
* `pt_F_slots` — the value of `F = F_* + W` and the two combinations `sin 2θ · ∂_θF`,
  `D_zF` that occur in `N₀` and `N`;
* `pt_Xi_slots` — the three slots of the residual stream function
  `PhiTil α (F_* + W) Φg` of `N`, obtained from the slots of `PhiTil α W Φg` (which is what
  `EpsDecay` bounds) by subtracting the explicit profile `sin 2θ/(2(1+z))`;
* `pt_FK_le` — the angular moment of `F = F_* + W`.

Axioms: `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.PhiStar.CoreAux.EVDefs
import Submission.Work.FTS.StrongEps.E5Aux2.Psivar0_slots_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- Triangle inequality for six signed terms. -/
theorem pt_abs_six_le (a b c d e f : ℝ) :
    |a - b + c + d - e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b, le_abs_self c,
      neg_abs_le c, le_abs_self d, neg_abs_le d, le_abs_self e, neg_abs_le e, le_abs_self f,
      neg_abs_le f]

/-- Triangle inequality for five signed terms. -/
theorem pt_abs_five_le (a b c d e : ℝ) :
    |a - b - c - d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b, le_abs_self c,
      neg_abs_le c, le_abs_self d, neg_abs_le d, le_abs_self e, neg_abs_le e]

/-- The angular coefficient `c2m θ = cos 2θ - sin²θ` is bounded by `2` in absolute value. -/
theorem pt_abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq]
  have h1 := Real.abs_cos_le_one (2 * θ)
  have h2 := Real.sin_sq_le_one θ
  have h3 : |Real.sin θ ^ 2| = Real.sin θ ^ 2 := abs_of_nonneg (sq_nonneg _)
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := abs_sub _ _
    _ = |Real.cos (2 * θ)| + Real.sin θ ^ 2 := by rw [h3]
    _ ≤ 1 + 1 := by linarith
    _ = 2 := by norm_num

/-- `z/(1+z)² ≤ 1` for `z ≥ 0`. -/
theorem pt_z_div_sq_le_one {z : ℝ} (hz : 0 ≤ z) : z / (1 + z) ^ 2 ≤ 1 := by
  have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  rw [div_le_one h1]
  nlinarith [sq_nonneg z]

/-- The sharp pointwise data of the reference profile `F_*` on the open quadrant: all five
quantities are `O(α)`, because the radial factor `z/(1+z)²` is `≤ 1`. -/
theorem pt_Fstar_pt_data {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |Work.Construction.Fstar α z θ| ≤ 100 * α ∧
      |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 100 * α ∧
      |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| ≤ 100 * α ∧
      |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ 2 * α ∧
      |Work.Construction.FK (Work.Construction.Fstar α) z| ≤ 2 * α := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hfrac : z / (1 + z) ^ 2 ≤ 1 := pt_z_div_sq_le_one hz.le
  have hα2 : α ^ 2 ≤ α := by nlinarith [hα.le, hα1]
  have hL : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
    Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 (by linarith)
  have hFK : Work.Construction.FK (Work.Construction.Fstar α) z = α * (2 * z / (1 + z) ^ 2) :=
    Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans (Work.FTS.NonlinRows.Rl1.Fstar_pt hα hα1 hz hθI) ?_
    have h2 : 20 * α * (z / (1 + z) ^ 2) ≤ 20 * α := by
      have := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ 20 * α)
      linarith [this]
    have h3 : 20 * α * z / (1 + z) ^ 2 = 20 * α * (z / (1 + z) ^ 2) := by ring
    linarith [h2]
  · refine le_trans (Work.FTS.NonlinRows.Rl1.DzFstar_pt hα hα1 hz hθI) ?_
    have h2 : 20 * α * (z / (1 + z) ^ 2) ≤ 20 * α := by
      have := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ 20 * α)
      linarith [this]
    have h3 : 20 * α * z / (1 + z) ^ 2 = 20 * α * (z / (1 + z) ^ 2) := by ring
    linarith [h2]
  · refine le_trans (Work.FTS.NonlinRows.Rl1.DthFstar_pt hα hα1 hz hθ.1 hθ.2) ?_
    have h2 : 80 / 3 * α ^ 2 * (z / (1 + z) ^ 2) ≤ 80 / 3 * α ^ 2 := by
      have := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ 80 / 3 * α ^ 2)
      linarith [this]
    have h3 : 80 / 3 * α ^ 2 * z / (1 + z) ^ 2 = 80 / 3 * α ^ 2 * (z / (1 + z) ^ 2) := by ring
    linarith [h2, hα2]
  · rw [hL, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + z),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * α)]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + z)]
    nlinarith [hα.le]
  · rw [hFK, abs_mul, abs_of_nonneg hα.le]
    have h2 : |2 * z / (1 + z) ^ 2| ≤ 2 := by
      have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hz.le,
        abs_of_pos h1, div_le_iff₀ h1]
      nlinarith [sq_nonneg z]
    calc α * |2 * z / (1 + z) ^ 2| ≤ α * 2 := mul_le_mul_of_nonneg_left h2 hα.le
      _ ≤ 2 * α := by linarith

/-! ## The slot bounds of the interface -/

/-- The seven slot bounds of the interface `EpsDecay`, normalised to `≤ 1` (the majorant is
bounded by `1`, and `SlotMaj 0` is the case `j = i = 0` of a slot bound). -/
theorem pt_EpsDecay_slots {α : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε τ : ℝ}
    {g : Work.FTS.Galerkin.Fam} {Maj : ℝ → ℝ}
    (hDec : Work.FTS.StrongEps.EpsDecay α ρ Φs E ε τ g Maj) :
    (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, ∀ j i : ℕ, j + i ≤ 1 →
        |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            z θ| ≤ 1) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ,
        |Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ z θ| ≤ 1) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ,
        |Work.Spaces.Dz (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) z θ| ≤ 1) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ,
        |Work.Spaces.Dth (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) z θ| ≤ 1) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ ε g)) τ)) z θ| ≤ 3) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ ε g)) τ)) z θ
          / Work.Construction.s2 θ| ≤ 3) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ ε g)) τ)) z θ| ≤ 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz θ j i hji
    exact le_trans (hDec.2.2.2.1 z hz θ j i hji) (hDec.2.1 z)
  · intro z hz θ
    have h := le_trans (hDec.2.2.2.1 z hz θ 0 0 (by norm_num)) (hDec.2.1 z)
    simpa [Work.Spaces.mixed, Work.Spaces.DzIter, Work.Spaces.DthIter] using h
  · intro z hz θ
    have h := le_trans (hDec.2.2.2.1 z hz θ 1 0 (by norm_num)) (hDec.2.1 z)
    simpa [Work.Spaces.mixed, Work.Spaces.DzIter, Work.Spaces.DthIter] using h
  · intro z hz θ
    have h := le_trans (hDec.2.2.2.1 z hz θ 0 1 (by norm_num)) (hDec.2.1 z)
    simpa [Work.Spaces.mixed, Work.Spaces.DzIter, Work.Spaces.DthIter] using h
  · intro z hz θ hθ
    exact (hDec.2.2.2.2 z θ hz hθ).1
  · intro z hz θ hθ
    exact (hDec.2.2.2.2 z θ hz hθ).2.1
  · intro z hz θ hθ
    exact (hDec.2.2.2.2 z θ hz hθ).2.2

/-! ## The slots of the full profile `F = F_* + W` -/

/-- The value of `F = F_* + W`, and the two combinations `sin 2θ·∂_θF`, `D_zF` occurring in
`N₀` and `N`. -/
theorem pt_F_slots {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W F : ℝ → ℝ → ℝ}
    (hWS : Work.FTS.EllipticEst.SmoothOpen W)
    (hFeq : F = fun z θ => Work.Construction.Fstar α z θ + W z θ)
    (hWval : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |W z θ| ≤ 1)
    (hWDz : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dz W z θ| ≤ 1)
    (hWDth : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dth W z θ| ≤ 1) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |F z θ| ≤ 101 ∧
        |Work.Construction.s2 θ * Work.Spaces.pth F z θ| ≤ 101 ∧
        |Work.Spaces.Dz F z θ| ≤ 101 := by
  have hFS : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hpth : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth F z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth W z θ := by
    intro z θ hz h1 h2
    have hpt : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
        F z' θ' = Work.Construction.Fstar α z' θ' + W z' θ' := by
      intro z' θ' hz' h1' h2'
      rw [hFeq]
    rw [Work.FTS.PhiStar.CoreAux.pth_congr_Q0 hpt z θ hz h1 h2]
    exact Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hFS hWS z θ hz h1 h2
  have hpz : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pz F z θ
        = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz W z θ := by
    intro z θ hz h1 h2
    have hpt : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
        F z' θ' = Work.Construction.Fstar α z' θ' + W z' θ' := by
      intro z' θ' hz' h1' h2'
      rw [hFeq]
    rw [Work.FTS.GalFields.RHS.Sharp.pz_congr_Q0 hpt z θ hz h1 h2]
    exact Work.FTS.GalFields.RHS.Sharp.pz_add_Q0 hFS hWS z θ hz h1 h2
  intro z hz θ hθ
  obtain ⟨hFstar, hDzFstar, hDthFstar, -, -⟩ := pt_Fstar_pt_data hα hα1 hz hθ
  have h2 : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      = Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ := rfl
  have h3 : Work.Spaces.Dth W z θ = Work.Construction.s2 θ * Work.Spaces.pth W z θ := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hFeq]
    have h1 := abs_add_le (Work.Construction.Fstar α z θ) (W z θ)
    nlinarith [h1, hFstar, hWval z hz θ, hα.le, hα1]
  · have hdist : Work.Construction.s2 θ
        * (Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth W z θ)
        = Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth W z θ := by
      simp only [Work.Construction.s2, Work.Spaces.Dth]
      ring_nf
    rw [hpth z θ hz hθ.1 hθ.2, hdist]
    have h1 := abs_add_le (Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      (Work.Spaces.Dth W z θ)
    nlinarith [h1, hDthFstar, hWDth z hz θ, hα.le, hα1]
  · have h1 := abs_add_le (Work.Spaces.Dz (Work.Construction.Fstar α) z θ) (Work.Spaces.Dz W z θ)
    have h2' : Work.Spaces.Dz F z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz W z θ := by
      rw [Work.Spaces.Dz, hpz z θ hz hθ.1 hθ.2, Work.Spaces.Dz, Work.Spaces.Dz]
      ring
    rw [h2']
    nlinarith [h1, hDzFstar, hWDz z hz θ, hα.le, hα1]

/-! ## The slots of the residual stream function -/

/-- The three slots of `PhiTil α (F_* + W) Φg`, from the slots of `PhiTil α W Φg` (the
profile whose slots the interface bounds) and the explicit `Theta`-difference
`sin 2θ/(2(1+z))`. -/
theorem pt_Xi_slots {α : ℝ} (hαι : α ∈ Set.Ioc 0 1) {W Φg : ℝ → ℝ → ℝ}
    (hWS : Work.FTS.EllipticEst.SmoothOpen W)
    (hWC4 : Work.Spaces.HkMem α 4 W)
    (hSlotR : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Rop α (Work.Construction.PhiTil α W Φg) z θ| ≤ 3)
    (hSlotU : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Uop α (Work.Construction.PhiTil α W Φg) z θ
        / Work.Construction.s2 θ| ≤ 3)
    (hSlotV : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Vop (Work.Construction.PhiTil α W Φg) z θ| ≤ 3) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Rop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg)
          z θ| ≤ 13 ∧
        |Work.Construction.Uop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg)
          z θ / Work.Construction.s2 θ| ≤ 13 ∧
        |Work.Construction.Vop
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg)
          z θ| ≤ 13 := by
  have hα0 : 0 < α := hαι.1
  have hα1 : α ≤ 1 := hαι.2
  -- the explicit difference of the two `Theta`-parts
  have hΘ : ∀ z θ : ℝ, 0 < z →
      Work.Construction.Theta α W z θ
        - Work.Construction.Theta α (fun z θ => Work.Construction.Fstar α z θ + W z θ) z θ
        = -Real.sin (2 * θ) / (2 * (1 + z)) := by
    intro z θ hz
    have hLadd : Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + W z θ) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 W z :=
      Work.FTS.StrongEps.blocks.L12_Fstar_add_open hα0 hα1 hWS hWC4 hz.le
    have hLstar : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
      Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα0 hα1 (by linarith)
    simp only [Work.Construction.Theta, Work.Construction.s2]
    rw [hLadd, hLstar]
    have hαne : α ≠ 0 := ne_of_gt hα0
    have h1z : (1 : ℝ) + z ≠ 0 := by linarith
    field_simp
    ring
  have hΞid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg z θ
        = Work.Construction.PhiTil α W Φg z θ - Real.sin (2 * θ) / (2 * (1 + z)) := by
    intro z θ hz h1 h2
    have h := hΘ z θ hz
    simp only [Work.Construction.PhiTil] at h ⊢
    ring_nf at h ⊢
    linarith
  have hlocR : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Construction.Rop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg)
          z θ
        = Work.Construction.Rop α (fun z θ =>
            Work.Construction.PhiTil α W Φg z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ :=
    fun z θ hz h1 h2 =>
      Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0 (fun z θ hz' h1' h2' => hΞid z θ hz' h1' h2')
        z θ hz h1 h2
  have hlocU : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Construction.Uop α
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg)
          z θ
        = Work.Construction.Uop α (fun z θ =>
            Work.Construction.PhiTil α W Φg z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ :=
    fun z θ hz h1 h2 =>
      Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0 (fun z θ hz' h1' h2' => hΞid z θ hz' h1' h2')
        z θ hz h1 h2
  have hlocV : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Construction.Vop
          (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg)
          z θ
        = Work.Construction.Vop (fun z θ =>
            Work.Construction.PhiTil α W Φg z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ :=
    fun z θ hz h1 h2 =>
      Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0 (fun z θ hz' h1' h2' => hΞid z θ hz' h1' h2')
        z θ hz h1 h2
  intro z hz θ hθ
  refine ⟨?_, ?_, ?_⟩
  · rw [hlocR z θ hz hθ.1 hθ.2]
    have h := (Psivar0_slots_sub hαι hz hθ (Ψ1 := Work.Construction.PhiTil α W Φg)).1
    linarith [hSlotR z hz θ hθ]
  · rw [hlocU z θ hz hθ.1 hθ.2]
    have h := (Psivar0_slots_sub hαι hz hθ (Ψ1 := Work.Construction.PhiTil α W Φg)).2.1
    linarith [hSlotU z hz θ hθ]
  · rw [hlocV z θ hz hθ.1 hθ.2]
    have h := (Psivar0_slots_sub hαι hz hθ (Ψ1 := Work.Construction.PhiTil α W Φg)).2.2
    linarith [hSlotV z hz θ hθ]

/-! ## The angular moment of `F = F_* + W` -/

/-- `FK (F_* + W) = FK F_* + FK W` and the resulting bound. -/
theorem pt_FK_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W F : ℝ → ℝ → ℝ}
    (hWS : Work.FTS.EllipticEst.SmoothOpen W)
    (hWC4 : Work.Spaces.HkMem α 4 W)
    (hFeq : F = fun z θ => Work.Construction.Fstar α z θ + W z θ)
    {C7 B : ℝ} (hC7nn : 0 ≤ C7) (hB0 : 0 ≤ B)
    (hFKW : ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Construction.FK W z| ≤ C7 * B) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.FK F z| ≤ (100 + C7) * (1 + B) := by
  intro z hz
  obtain ⟨-, -, -, -, hFKstar⟩ :=
    pt_Fstar_pt_data (θ := 1) hα hα1 hz ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hadd : Work.Construction.FK F z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK W z := by
    rw [hFeq]
    exact Work.FTS.GalFields.RHS.FK_add_of_slices hz0
      (Work.Stability.integrableOn_slice_Fstar α hα z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hWS hWC4 hz)
  rw [hadd]
  have h1 := abs_add_le (Work.Construction.FK (Work.Construction.Fstar α) z)
    (Work.Construction.FK W z)
  have h2 := hFKW z hz
  have h3 : |Work.Construction.FK (Work.Construction.Fstar α) z| ≤ 100 := by
    nlinarith [hFKstar, hα.le, hα1]
  have h4 : |Work.Construction.FK W z| ≤ C7 * (1 + B) := by
    nlinarith [h2, hC7nn, hB0]
  nlinarith [h1, h3, h4, hB0, hC7nn]

end Work.FTS.StrongEps.E5Aux2
