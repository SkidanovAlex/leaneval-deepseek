import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row11Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.wtoHQ_of_pointwise
import Submission.Work.FTS.Nonlinear.Pieces.RNP.Bv_WlInf
import Submission.Work.FTS.Nonlinear.Pieces.RNP.Rv_smooth
import Submission.Work.FTS.Nonlinear.Pieces.RNP.N1ss_smoothQuad
import Submission.Work.FTS.H2.Q.WtoH_Radial_Q
import Submission.Work.FTS.H2.Q.WtoH_Mixed_Q
import Submission.Work.FTS.H2.prodW_interior_bound
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNPV2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Row 11 of the `N4` table

The piece is `N₁^{**} = 2 ℛ(Φ̃_*) F_*` (`Work.FTS.Nonlin.N1ss`) and the claim is
`|N₁^{**}|_{ℋ⁴} ≤ K α²`.

The design's route (`FTS/N45_DESIGN_LEAD.md` §3.4, row 11) splits `N₁^{**}` as the product of an
*angular* factor and a *radial* factor:

* `F_*(z,θ) = Bv(θ)·z/(1+z)²` with `Bv(θ) = 2αΓ(θ)/c(α)`, so
  `N₁^{**} = (2 Bv(θ)) · (ℛ(Φ̃_*) z/(1+z)²)`;
* the angular factor is controlled by the explicit estimates of `Bv_WlInf` (`|Bv| ≤ 20α`,
  `|D_θ^j Bv| ≤ 20α tBound(j-1)0 · sin(2θ)^{-α/5}/(α+sin 2θ)`);
* the radial factor carries the whole `𝒲^{4,∞}`-content: `((z+1)³/z²)·(ℛ(Φ̃_*)z/(1+z)²) = ℛ̃(Φ̃_*)`
  is exactly the *weighted* coefficient of the star package, whose `𝒲^{4,∞}`-norm is `≤ Cs α`.

The passage from `𝒲^{4,∞}`-control of the radial factor to the pointwise bounds needed by
`wtoHQ_of_pointwise` is `WtoH_Radial_Q`/`WtoH_Mixed_Q`, and the product with the angular factor
is handled by the pointwise Leibniz rules of the interior class `SmoothQuad`
(`sqm_pz_DthIter_mul_le_4`).  Both factors are `SmoothQuad`, so every Leibniz expansion used
below is an identity — none of the (false) *global* product rules for `𝒲^{4,∞}` is needed. -/

/-! ## The two factors -/

/-- The angular factor `2 Bv(θ)` of row 11 — a function of `θ` alone. -/
def angF (α : ℝ) : ℝ → ℝ := fun θ => 2 * Work.FTS.Nonlinear.Pieces.RNP.Bv α θ

/-- The angular factor, viewed as a function of `(z,θ)`. -/
def angB (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => angF α θ

/-- The radial factor `ℛ(Φ̃_*) · z/(1+z)²` of row 11. -/
def radA (α : ℝ) (Φs : Fn) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * z / (1 + z) ^ 2

@[simp] theorem angF_apply (α θ : ℝ) :
    angF α θ = 2 * Work.FTS.Nonlinear.Pieces.RNP.Bv α θ := rfl

@[simp] theorem angB_apply (α z θ : ℝ) : angB α z θ = angF α θ := rfl

@[simp] theorem radA_apply (α : ℝ) (Φs : Fn) (z θ : ℝ) :
    radA α Φs z θ
      = Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * z / (1 + z) ^ 2 := rfl

/-- **The factorisation of row 11**: `N₁^{**} = (2 Bv(θ))·(ℛ(Φ̃_*) z/(1+z)²)`. -/
theorem N1ss_eq_angB_mul_radA (α : ℝ) (Φs : Fn) :
    Work.FTS.Nonlin.N1ss α Φs = fun z θ => angB α z θ * radA α Φs z θ := by
  funext z θ
  simp only [Work.FTS.Nonlin.N1ss, angB, angF, radA, Work.Construction.Fstar,
    Work.FM.Fstar, Work.FTS.Nonlinear.Pieces.RNP.Bv]
  ring_nf

/-- The weighted radial factor is the weighted coefficient of the star package. -/
theorem weighted_eq_Rv (α : ℝ) (Φs : Fn) :
    (fun z θ => (z + 1) ^ 3 / z ^ 2 * radA α Φs z θ)
      = Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs := by
  funext z θ
  rcases eq_or_ne z 0 with hz | hz
  · subst hz; simp [radA, Work.FTS.Nonlinear.Pieces.RNP.Rv]
  · rcases eq_or_ne z (-1) with hz1 | hz1
    · subst hz1; simp [radA, Work.FTS.Nonlinear.Pieces.RNP.Rv]
    · have h1 : (1 + z : ℝ) ≠ 0 := by intro hh; exact hz1 (by linarith)
      simp only [radA, Work.FTS.Nonlinear.Pieces.RNP.Rv, Work.FTS.Nonlin.PhiTs]
      rw [div_mul_div_comm,
        show (z + 1) ^ 3 * (Work.Construction.Rop α
              (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ * z)
            = ((1 + z) * (1 + z) ^ 2) * (Work.Construction.Rop α
              (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ * z) by ring,
        show z ^ 2 * (1 + z) ^ 2 = (z * (1 + z) ^ 2) * z by ring]
      field_simp
      ring

/-- `∂_z^k` of a product with a factor depending on `θ` alone: the factor comes out.  (The
`z`-derivative is blind to the `θ`-dependence of the constant.) -/
theorem pzIter_theta_mul (k : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter k (fun z θ => a θ * f z θ)
      = fun z θ => a θ * Work.Spaces.pzIter k f z θ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]
      funext z θ
      exact Work.FTS.Nonlinear.Pieces.RNP.deriv_const_mul_loc (a θ)
        (fun z' => Work.Spaces.pzIter k f z' θ) z

/-! ## Smoothness of the two factors -/

/-- `Bv(α,·)` is `C^∞` on the open interval `(0,π/2)`. -/
theorem contDiffOn_Bv (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.FTS.Nonlinear.Pieces.RNP.Bv α θ) (Set.Ioo 0 (π / 2)) := by
  rw [Work.FTS.Nonlinear.Pieces.RNP.Bv_eq_const_mul α]
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo 0 (π / 2)) :=
    Real.contDiff_sin.contDiffOn.mul (Real.contDiff_cos.contDiffOn.pow 2)
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have hs : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hGam : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Work.Spaces.Gam α θ)
      (Set.Ioo 0 (π / 2)) := hbase.rpow_const_of_ne hne
  exact contDiffOn_const.mul hGam

/-- The angular factor is `C^∞` on the open quadrant. -/
theorem smoothQuad_angF (α : ℝ) :
    Work.FTS.LocData.SmoothQuad (fun z θ => angF α θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => angF α θ)) Work.Spaces.quadU
  have hsnd : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.2)
      Work.Spaces.quadU := contDiffOn_snd
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => angF α θ)
      (Set.Ioo 0 (π / 2)) := contDiffOn_const.mul (contDiffOn_Bv α)
  have h := h2.comp hsnd (fun p hp => hp.2)
  refine h.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  rfl

/-- The angular factor is `C^∞` on the open quadrant. -/
theorem smoothQuad_angB (α : ℝ) : Work.FTS.LocData.SmoothQuad (angB α) :=
  smoothQuad_angF α

/-- The radial factor is `C^∞` on the open quadrant. -/
theorem smoothQuad_radA {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : Work.FTS.Nonlin.StarPkg α Cs Φs) : Work.FTS.LocData.SmoothQuad (radA α Φs) := by
  have hTheta : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    Work.FTS.Nonlinear.Pieces.RNP.smoothQuad_Theta_Fstar hα hα1
  have hPhi : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) := by
    show Work.FTS.LocData.SmoothQuad
      (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
    exact Work.FTS.LocData.smoothQuad_sub h.smooth hTheta
  have hR : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.Nonlinear.Pieces.RNP.smoothQuad_Rop hPhi
  have hrat : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => z / (1 + z) ^ 2) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ : ℝ => z / (1 + z) ^ 2)) Work.Spaces.quadU
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
        Work.Spaces.quadU := contDiffOn_fst
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (1 + p.1) ^ 2)
        Work.Spaces.quadU := (contDiffOn_const.add contDiffOn_fst).pow 2
    have hne : ∀ p ∈ Work.Spaces.quadU, (1 + p.1) ^ 2 ≠ 0 := by
      intro p hp
      have : 0 < 1 + p.1 := by linarith [Set.mem_Ioi.mp hp.1]
      positivity
    refine (hnum.div hden hne).congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    rfl
  have hmain : Work.FTS.LocData.SmoothQuad
      (fun z θ => Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * (z / (1 + z) ^ 2)) := Work.FTS.LocData.smoothQuad_mul hR hrat
  refine hmain.congr (fun z θ => ?_)
  simp only [Function.uncurry, radA_apply]
  ring

/-! ## The angular weight and the pointwise bounds for the angular factor -/

/-- The angular weight `Φ(θ) = (α + sin 2θ)·sin(2θ)^{α/5}` of the `𝒲^{4,∞}`-norm. -/
def Phi (α θ : ℝ) : ℝ := (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)

/-- A universal bound for the auxiliary constants `tBound j 0`, `j ≤ 3`. -/
def TBound : ℝ := (∑ j ∈ Finset.range 4, (Work.Spaces.tBound j 0 + 1)) + 1

theorem TBound_pos : 0 < TBound := by
  have hS : (0 : ℝ) ≤ ∑ j ∈ Finset.range 4, (Work.Spaces.tBound j 0 + 1) :=
    Finset.sum_nonneg (fun j _ => by linarith [Work.Spaces.tBound_nonneg j 0])
  rw [TBound]
  linarith

theorem tBound_le_TBound (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) :
    Work.Spaces.tBound (j - 1) 0 ≤ TBound := by
  have hmem : j - 1 ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
  have hsingle : Work.Spaces.tBound (j - 1) 0 + 1
      ≤ ∑ i ∈ Finset.range 4, (Work.Spaces.tBound i 0 + 1) :=
    Finset.single_le_sum (f := fun i : ℕ => Work.Spaces.tBound i 0 + 1)
      (fun i _ => by linarith [Work.Spaces.tBound_nonneg i 0]) hmem
  rw [TBound]
  linarith

theorem Phi_nonneg (α : ℝ) (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Phi α θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  exact mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)

theorem Phi_le_two (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Phi α θ ≤ 2 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hr : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
    Real.rpow_le_one hs0 hs1 (by positivity)
  have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
  calc Phi α θ = (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := rfl
    _ ≤ 2 * 1 := mul_le_mul h1 hr (Real.rpow_nonneg hs0 _) (by norm_num)
    _ = 2 := by norm_num

/-- The angular factor is bounded by `40α`. -/
theorem angF_abs_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : |angF α θ| ≤ 40 * α := by
  have h := Work.FTS.Nonlinear.Pieces.RNP.Bv_abs_le α hα hα1 hθ
  rw [angF_apply, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

/-- The angular derivatives of the angular factor carry the weight `Φ`. -/
theorem dthU_angF_weight_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (j : ℕ) (hj : 1 ≤ j)
    (hj4 : j ≤ 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.dthU^[j] (angF α) θ| ≤ 40 * α * TBound * Phi α θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hd0 : 0 < α + Real.sin (2 * θ) := by linarith
  have hdne : α + Real.sin (2 * θ) ≠ 0 := ne_of_gt hd0
  have hw0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    div_nonneg (Real.rpow_nonneg (le_of_lt hs0) _) (le_of_lt hd0)
  have hss : (Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (-(α / 5)) = 1 := by
    rw [mul_comm, ← Real.rpow_add hs0, neg_add_cancel, Real.rpow_zero]
  have hprod : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (le_of_lt hd0) (Real.rpow_nonneg (le_of_lt hs0) _)
  have hid : (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) = 1 := by
    rw [div_mul_eq_mul_div, mul_comm ((Real.sin (2 * θ)) ^ (-(α / 5)))
        ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)),
      mul_assoc, hss, mul_one, div_self hdne]
  have hB := Work.FTS.Nonlinear.Pieces.RNP.Bv_dthIter_weight_le α hα hα1 j hj hθI
  have hB' : |Work.Spaces.dthU^[j] (Work.FTS.Nonlinear.Pieces.RNP.Bv α) θ|
      * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ 20 * α * Work.Spaces.tBound (j - 1) 0 := by
    rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hs0) _),
      abs_of_nonneg (le_of_lt hd0), mul_div_assoc] at hB
    exact hB
  have hkey : |Work.Spaces.dthU^[j] (Work.FTS.Nonlinear.Pieces.RNP.Bv α) θ|
      ≤ 20 * α * Work.Spaces.tBound (j - 1) 0
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    calc |Work.Spaces.dthU^[j] (Work.FTS.Nonlinear.Pieces.RNP.Bv α) θ|
        = |Work.Spaces.dthU^[j] (Work.FTS.Nonlinear.Pieces.RNP.Bv α) θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
          rw [hid, mul_one]
      _ = (|Work.Spaces.dthU^[j] (Work.FTS.Nonlinear.Pieces.RNP.Bv α) θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
      _ ≤ (20 * α * Work.Spaces.tBound (j - 1) 0)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_le_mul_of_nonneg_right hB' hprod
  have hfun : angF α = fun t => 2 * Work.FTS.Nonlinear.Pieces.RNP.Bv α t := rfl
  rw [hfun, Work.Spaces.dthU_iter_const_mul,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hTB := tBound_le_TBound j hj hj4
  have hΦ0 := Phi_nonneg α hα hθI
  have hstep : 20 * α * Work.Spaces.tBound (j - 1) 0
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      ≤ 20 * α * TBound * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    have h1 : 20 * α * Work.Spaces.tBound (j - 1) 0 ≤ 20 * α * TBound :=
      mul_le_mul_of_nonneg_left hTB (by positivity)
    exact mul_le_mul_of_nonneg_right h1 hprod
  simp only [Phi]
  calc 2 * |Work.Spaces.dthU^[j] (Work.FTS.Nonlinear.Pieces.RNP.Bv α) θ|
      ≤ 2 * (20 * α * Work.Spaces.tBound (j - 1) 0
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_left hkey (by norm_num)
    _ ≤ 2 * (20 * α * TBound * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 40 * α * TBound * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring

/-- The angular derivatives of the angular factor, without weight. -/
theorem dthU_angF_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (j : ℕ) (hj : 1 ≤ j)
    (hj4 : j ≤ 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.dthU^[j] (angF α) θ| ≤ 80 * α * TBound := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hw := dthU_angF_weight_le hα hα1 j hj hj4 hθ
  have hΦ := Phi_le_two α hα hα1 hθI
  calc |Work.Spaces.dthU^[j] (angF α) θ|
      ≤ 40 * α * TBound * Phi α θ := hw
    _ ≤ 40 * α * TBound * 2 := by
        have hT0 : (0 : ℝ) < TBound := TBound_pos
        have : (0 : ℝ) ≤ 40 * α * TBound := by positivity
        exact mul_le_mul_of_nonneg_left hΦ this
    _ = 80 * α * TBound := by ring

/-- The constant `Ca` dominating all the angular bounds of row 11. -/
def Ca : ℝ := 100 * TBound + 100

theorem Ca_pos : 0 < Ca := by
  have := TBound_pos
  rw [Ca]; linarith

theorem Ca_ge_40 : 40 ≤ Ca := by
  have := TBound_pos
  rw [Ca]; linarith

theorem Ca_ge_80 : 80 * TBound ≤ Ca := by
  have := TBound_pos
  rw [Ca]; linarith

theorem Ca_ge_40TB : 40 * TBound ≤ Ca := by
  have := TBound_pos
  rw [Ca]; linarith

/-! ## The collapse of the double Leibniz sum -/

/-- When the first factor of a product depends on `θ` alone, the double Leibniz sum of
`∂_z^l D_θ^i` collapses: only the `c = 0` terms survive. -/
theorem mixed_sum_collapse (l i : ℕ) (a2 : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z (θ' : ℝ) => a2 θ')) z θ|
          * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) F) z θ|)
      = ∑ a ∈ Finset.range (i + 1),
          |Work.Spaces.dthU^[a] a2 θ| * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) F) z θ| := by
  have hDthfun : ∀ a : ℕ, Work.Spaces.DthIter a (fun z (θ' : ℝ) => a2 θ')
      = fun _ (θ' : ℝ) => Work.Spaces.dthU^[a] a2 θ' := by
    intro a
    funext z' θ'
    exact Work.FTS.Nonlinear.Pieces.RNP.DthIter_z_indep a2 a z' θ'
  rw [Finset.sum_eq_single (0 : ℕ)]
  · refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Work.Spaces.pzIter_zero, hDthfun a, Nat.sub_zero]
  · intro c hc hcne
    refine Finset.sum_eq_zero (fun a ha => ?_)
    rw [hDthfun a, Work.FTS.Nonlinear.Pieces.RNP.pzIter_z_indep_ne_zero
      (Work.Spaces.dthU^[a] a2) c hcne]
    simp
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos l)) h0

/-! ## Row 11 -/

theorem row11 {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ K * α ^ 2 := by
  obtain ⟨Cw, hCw, hwto⟩ := Work.FTS.Nonlinear.Pieces.RNP.wtoHQ_of_pointwise
  refine ⟨1 + Cw * (10 ^ 6 * Ca) * max Cs 0, ?_, ?_⟩
  · have h1 : 0 ≤ Cw * (10 ^ 6 * Ca) * max Cs 0 :=
      mul_nonneg (mul_nonneg hCw.le (mul_nonneg (by norm_num) (le_of_lt Ca_pos)))
        (le_max_right _ _)
    linarith
  · intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
    have hCa0 : 0 ≤ Ca := le_of_lt Ca_pos
    set WA : ℝ := Work.Spaces.WlInf α 4 (Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs) with hWA
    have hWA0 : 0 ≤ WA := by
      rw [hWA]
      exact Work.FTS.H2.sqm_WlInf_nonneg α 4 _ hstar.R.1
    have hWAle : WA ≤ max Cs 0 * α := by
      rw [hWA]
      exact hstar.R.2.trans (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
    have hmemG : Work.Spaces.WlInfMem α 4
        (fun z θ => (z + 1) ^ 3 / z ^ 2 * radA α Φs z θ) := by
      rw [weighted_eq_Rv]
      exact hstar.R.1
    have hWAeq : Work.Spaces.WlInf α 4
        (fun z θ => (z + 1) ^ 3 / z ^ 2 * radA α Φs z θ) = WA := by
      rw [weighted_eq_Rv, hWA]
    -- the two pointwise estimates for the two factors
    have hrad : ∀ m ≤ 4, ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m (radA α Φs) z θ|
          ≤ 200000 * WA := by
      intro m hm z hz θ hθ
      have h := Work.FTS.H2.Q.WtoH_Radial_Q hα hα1 (smoothQuad_radA hα hα1 hstar) hmemG
        m hm z hz θ hθ
      rwa [hWAeq] at h
    have hmix : ∀ i l, 1 ≤ i → l + i ≤ 4 → ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ l
            * Work.Spaces.pzIter l (Work.Spaces.DthIter i (radA α Φs)) z θ|
          ≤ 200000 * (WA * Phi α θ) := by
      intro i l hi hli z hz θ hθ
      have h := Work.FTS.H2.Q.WtoH_Mixed_Q hα hα1 (smoothQuad_radA hα hα1 hstar) hmemG
        i l hi hli z hz θ hθ
      rwa [hWAeq] at h
    set W : ℝ := 10 ^ 6 * Ca * (α * WA) with hW
    have hW0 : 0 ≤ W := by
      rw [hW]
      exact mul_nonneg (mul_nonneg (by norm_num) hCa0) (mul_nonneg hα.le hWA0)
    -- the pointwise hypotheses of `wtoHQ_of_pointwise`
    have hboundA : ∀ m ≤ 4, ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ m
            * Work.Spaces.pzIter m (Work.FTS.Nonlin.N1ss α Φs) z θ|
          ≤ 200000 * W := by
      intro m hm z hz θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hfac : Work.Spaces.pzIter m (Work.FTS.Nonlin.N1ss α Φs) z θ
          = angF α θ * Work.Spaces.pzIter m (radA α Φs) z θ := by
        rw [N1ss_eq_angB_mul_radA]
        simp only [angB]
        rw [pzIter_theta_mul m (angF α) (radA α Φs)]
      rw [hfac]
      have habs : |(1 + z) * Work.Spaces.w z * z ^ m
            * (angF α θ * Work.Spaces.pzIter m (radA α Φs) z θ)|
          = |angF α θ| * |(1 + z) * Work.Spaces.w z * z ^ m
              * Work.Spaces.pzIter m (radA α Φs) z θ| := by
        rw [show (1 + z) * Work.Spaces.w z * z ^ m
              * (angF α θ * Work.Spaces.pzIter m (radA α Φs) z θ)
            = angF α θ * ((1 + z) * Work.Spaces.w z * z ^ m
              * Work.Spaces.pzIter m (radA α Φs) z θ) by ring, abs_mul]
      rw [habs]
      have h1 := angF_abs_le hα hα1 hθI
      have h2 := hrad m hm z hz θ hθ
      have h40 : (40 : ℝ) ≤ 10 ^ 6 * Ca := by
        have h := Ca_ge_40
        nlinarith [hCa0]
      have harith : 40 * α * (200000 * WA) ≤ 200000 * W := by
        rw [hW]
        calc 40 * α * (200000 * WA) ≤ (10 ^ 6 * Ca) * α * (200000 * WA) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_right h40 hα.le
          _ = 200000 * (10 ^ 6 * Ca * (α * WA)) := by ring
      calc |angF α θ| * |(1 + z) * Work.Spaces.w z * z ^ m
              * Work.Spaces.pzIter m (radA α Φs) z θ|
          ≤ (40 * α) * (200000 * WA) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ 200000 * W := harith
    have hboundB : ∀ i l, 1 ≤ i → l + i ≤ 4 → ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
            (Work.Spaces.DthIter i (Work.FTS.Nonlin.N1ss α Φs)) z θ|
          ≤ 200000 * (W * Phi α θ) := by
      intro i l hi hli z hz θ hθ
      have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hl4 : l ≤ 4 := by omega
      have hi4 : i ≤ 4 := by omega
      have hΦ0 : 0 ≤ Phi α θ := Phi_nonneg α hα hθI
      have hρ : 0 ≤ (1 + z) * Work.Spaces.w z * z ^ l := by
        have hw0 : 0 ≤ Work.Spaces.w z := by
          rw [Work.Spaces.w]; positivity
        exact mul_nonneg (mul_nonneg (by linarith) hw0) (pow_nonneg (le_of_lt hz) l)
      have hfun : Work.Spaces.DthIter i (Work.FTS.Nonlin.N1ss α Φs)
          = Work.Spaces.DthIter i (fun z θ => angF α θ * radA α Φs z θ) := by
        rw [N1ss_eq_angB_mul_radA]
        simp only [angB]
      rw [hfun]
      -- the Leibniz bound, with the sum collapsed
      have hleib := Work.FTS.H2.sqm_pz_DthIter_mul_le_4 l i hl4 hi4
        (fun z θ => angF α θ) (radA α Φs) (smoothQuad_angF α)
        (smoothQuad_radA hα hα1 hstar) z hzI θ hθ
      have hsum : |Work.Spaces.pzIter l
            (Work.Spaces.DthIter i (fun z θ => angF α θ * radA α Φs z θ)) z θ|
          ≤ 257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (angF α) θ|
                * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ|) :=
        hleib.trans (le_of_eq (by rw [mixed_sum_collapse l i (angF α) (radA α Φs) z θ]))
      -- the per-`a` estimate
      have hterm : ∀ a ∈ Finset.range (i + 1),
          |Work.Spaces.dthU^[a] (angF α) θ|
            * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ|
            * ((1 + z) * Work.Spaces.w z * z ^ l)
          ≤ 200000 * (Ca * α * WA * Phi α θ) := by
        intro a ha
        have hai : a ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
        have heq : |Work.Spaces.dthU^[a] (angF α) θ|
              * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ|
              * ((1 + z) * Work.Spaces.w z * z ^ l)
            = |Work.Spaces.dthU^[a] (angF α) θ|
              * |(1 + z) * Work.Spaces.w z * z ^ l
                  * Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ| := by
          rw [abs_mul, abs_of_nonneg hρ]
          ring
        rw [heq]
        rcases lt_or_eq_of_le hai with hlt | heq2
        · -- `a < i`: the mixed estimate for the radial factor
          have h1 : 1 ≤ i - a := by omega
          have h2 : l + (i - a) ≤ 4 := by omega
          have hR := hmix (i - a) l h1 h2 z hz θ hθ
          have hD : |Work.Spaces.dthU^[a] (angF α) θ| ≤ Ca * α := by
            rcases eq_or_lt_of_le (Nat.zero_le a) with h0 | hpos
            · subst h0
              show |angF α θ| ≤ Ca * α
              have hf := angF_abs_le hα hα1 hθI
              have h40 : 40 * α ≤ Ca * α := mul_le_mul_of_nonneg_right Ca_ge_40 hα.le
              linarith
            · have ha4 : a ≤ 4 := by omega
              have hf := dthU_angF_le hα hα1 a hpos ha4 hθ
              have h80 : 80 * TBound * α ≤ Ca * α :=
                mul_le_mul_of_nonneg_right Ca_ge_80 hα.le
              linarith
          have hR0 : 0 ≤ Ca * α := mul_nonneg hCa0 hα.le
          calc |Work.Spaces.dthU^[a] (angF α) θ|
                * |(1 + z) * Work.Spaces.w z * z ^ l
                    * Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ|
              ≤ (Ca * α) * (200000 * (WA * Phi α θ)) :=
                mul_le_mul hD hR (abs_nonneg _) hR0
            _ = 200000 * (Ca * α * WA * Phi α θ) := by ring
        · -- `a = i`: the radial estimate for the radial factor
          have hia : i - a = 0 := by omega
          rw [hia, Work.Spaces.DthIter_zero]
          have ha1 : 1 ≤ a := by omega
          have ha4 : a ≤ 4 := by omega
          have hR := hrad l hl4 z hz θ hθ
          have hD := dthU_angF_weight_le hα hα1 a ha1 ha4 hθ
          have hD' : |Work.Spaces.dthU^[a] (angF α) θ| ≤ Ca * α * Phi α θ := by
            have h40 : 40 * α * TBound ≤ Ca * α := by
              have h := mul_le_mul_of_nonneg_right Ca_ge_40TB hα.le
              linarith
            calc |Work.Spaces.dthU^[a] (angF α) θ| ≤ 40 * α * TBound * Phi α θ := hD
              _ ≤ Ca * α * Phi α θ := mul_le_mul_of_nonneg_right h40 hΦ0
          have hR0 : 0 ≤ Ca * α * Phi α θ :=
            mul_nonneg (mul_nonneg hCa0 hα.le) hΦ0
          calc |Work.Spaces.dthU^[a] (angF α) θ|
                * |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l (radA α Φs) z θ|
              ≤ (Ca * α * Phi α θ) * (200000 * WA) :=
                mul_le_mul hD' hR (abs_nonneg _) hR0
            _ = 200000 * (Ca * α * WA * Phi α θ) := by ring
      -- assemble
      have hρ2 : |(1 + z) * Work.Spaces.w z * z ^ l
            * Work.Spaces.pzIter l (Work.Spaces.DthIter i
                (fun z θ => angF α θ * radA α Φs z θ)) z θ|
          = ((1 + z) * Work.Spaces.w z * z ^ l)
            * |Work.Spaces.pzIter l (Work.Spaces.DthIter i
                (fun z θ => angF α θ * radA α Φs z θ)) z θ| := by
        rw [abs_mul, abs_of_nonneg hρ]
      rw [hρ2]
      have hnn : 0 ≤ 200000 * (Ca * α * WA * Phi α θ) :=
        mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg hCa0 hα.le) hWA0) hΦ0)
      have hi5 : ((i + 1 : ℕ) : ℝ) ≤ 5 := by
        have : i + 1 ≤ 5 := by omega
        exact_mod_cast this
      have hstep1 : ((1 + z) * Work.Spaces.w z * z ^ l)
            * |Work.Spaces.pzIter l (Work.Spaces.DthIter i
                (fun z θ => angF α θ * radA α Φs z θ)) z θ|
          ≤ ((1 + z) * Work.Spaces.w z * z ^ l) * (257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (angF α) θ|
                * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ|)) :=
        mul_le_mul_of_nonneg_left hsum hρ
      have hstep2 : ((1 + z) * Work.Spaces.w z * z ^ l)
            * (257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (angF α) θ|
                * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ|))
          = 257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (angF α) θ|
                * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ|
                * ((1 + z) * Work.Spaces.w z * z ^ l)) := by
        have h1 : ((1 + z) * Work.Spaces.w z * z ^ l) * (257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (angF α) θ|
                * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ|))
            = 257 * (((1 + z) * Work.Spaces.w z * z ^ l) * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (angF α) θ|
                * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ|)) := by
          ring
        rw [h1, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun a ha => by ring)
      have hstep3 : 257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (angF α) θ|
                * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ|
                * ((1 + z) * Work.Spaces.w z * z ^ l))
          ≤ 257 * (∑ _a ∈ Finset.range (i + 1), 200000 * (Ca * α * WA * Phi α θ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num)
      have hstep4 : 257 * (∑ _a ∈ Finset.range (i + 1), 200000 * (Ca * α * WA * Phi α θ))
          = 257 * (((i + 1 : ℕ) : ℝ) * (200000 * (Ca * α * WA * Phi α θ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hstep5 : 257 * (((i + 1 : ℕ) : ℝ) * (200000 * (Ca * α * WA * Phi α θ)))
          ≤ 200000 * (W * Phi α θ) := by
        rw [hW]
        calc 257 * (((i + 1 : ℕ) : ℝ) * (200000 * (Ca * α * WA * Phi α θ)))
            = (257 * ((i + 1 : ℕ) : ℝ)) * (200000 * (Ca * α * WA * Phi α θ)) := by ring
          _ ≤ (257 * 5) * (200000 * (Ca * α * WA * Phi α θ)) := by
              apply mul_le_mul_of_nonneg_right _ hnn
              exact mul_le_mul_of_nonneg_left hi5 (by norm_num)
          _ ≤ 10 ^ 6 * (200000 * (Ca * α * WA * Phi α θ)) := by
              apply mul_le_mul_of_nonneg_right _ hnn
              norm_num
          _ = 200000 * (10 ^ 6 * Ca * (α * WA) * Phi α θ) := by ring
      calc ((1 + z) * Work.Spaces.w z * z ^ l)
            * |Work.Spaces.pzIter l (Work.Spaces.DthIter i
                (fun z θ => angF α θ * radA α Φs z θ)) z θ|
          ≤ ((1 + z) * Work.Spaces.w z * z ^ l) * (257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (angF α) θ|
                * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ|)) :=
            hstep1
        _ = 257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (angF α) θ|
                * |Work.Spaces.pzIter l (Work.Spaces.DthIter (i - a) (radA α Φs)) z θ|
                * ((1 + z) * Work.Spaces.w z * z ^ l)) := hstep2
        _ ≤ 257 * (∑ _a ∈ Finset.range (i + 1), 200000 * (Ca * α * WA * Phi α θ)) := hstep3
        _ = 257 * (((i + 1 : ℕ) : ℝ) * (200000 * (Ca * α * WA * Phi α θ))) := hstep4
        _ ≤ 200000 * (W * Phi α θ) := hstep5
    -- the transfer
    have hmain := hwto α (Work.FTS.Nonlin.N1ss α Φs) W hα hα1 hW0
      (Work.FTS.Nonlinear.Pieces.RNP.N1ss_smoothQuad hα hα1 hstar) hboundA hboundB
    -- the final arithmetic
    have hWle : W ≤ 10 ^ 6 * Ca * (α * (max Cs 0 * α)) := by
      rw [hW]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hWAle hα.le)
        (mul_nonneg (by norm_num) hCa0)
    calc Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ Cw * W := hmain
      _ ≤ Cw * (10 ^ 6 * Ca * (α * (max Cs 0 * α))) :=
          mul_le_mul_of_nonneg_left hWle hCw.le
      _ = (Cw * (10 ^ 6 * Ca) * max Cs 0) * α ^ 2 := by ring
      _ ≤ (1 + Cw * (10 ^ 6 * Ca) * max Cs 0) * α ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg α)
          linarith

end Work.FTS.Nonlinear.Pieces.RNPV2

