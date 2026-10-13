import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Psi0_exists
import Submission.Work.FTS.EllipticEst.bslOp_sub
import Submission.Work.FTS.PhiStar.phiAj_smooth2
import Submission.Work.FTS.PhiStar.linv23_smooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-! ## Helpers for the telescoping identity

The three auxiliary facts below are the algebraic/regularity inputs of `telescoping`:

* `contDiffAt_uncurry_sep_mul`: a separable product `(z,θ) ↦ (c·A z)·v θ` is `C²` at `(z,θ)`
  as soon as `A` is `C²` at `z` and `v` is `C²` at `θ` (this is what `Work.Elliptic.bslOp_add`
  needs in order to split off a correction term);
* `bslOp_sep_const`: `bslOp` of a constant multiple of a separable product, obtained from the
  (unconditional) `Work.FTS.PhiStar.bslOp_sep` by pulling the constants
  `iteratedDeriv 2 (fun z => c * A z) = c · iteratedDeriv 2 A` and
  `deriv (fun z => c * A z) = c · deriv A` out of the operator;
* `telescoping_psi23_contDiffAt`: `C²`-regularity of the two telescoping iterates
  `ψ₂ = σ·LinvI ψ`, `ψ₃ = σ·LinvI ψ₂` (`σ = sin 2θ`) at interior points, deduced from the
  `Linv`-regularity `Work.FTS.PhiStar.linv23_smooth` by the product rule. -/

/-- `C²`-regularity of the uncurried form of a (scaled) separable product. -/
theorem contDiffAt_uncurry_sep_mul (c : ℝ) {A v : ℝ → ℝ} {z θ : ℝ} (hA : ContDiffAt ℝ 2 A z)
    (hv : ContDiffAt ℝ 2 v θ) :
    ContDiffAt ℝ 2 (Function.uncurry (fun z θ => (c * A z) * v θ)) (z, θ) := by
  have h1 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => A p.1) (z, θ) := by
    simpa [Function.comp_def] using hA.comp (z, θ) (contDiffAt_fst (p := (z, θ)))
  have h2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => v p.2) (z, θ) := by
    simpa [Function.comp_def] using hv.comp (z, θ) (contDiffAt_snd (p := (z, θ)))
  have h3 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (c * A p.1) * v p.2) (z, θ) :=
    ((contDiffAt_const (c := c)).mul h1).mul h2
  have hfun : Function.uncurry (fun z θ => (c * A z) * v θ)
      = fun p : ℝ × ℝ => (c * A p.1) * v p.2 := rfl
  rw [hfun]
  exact h3

/-- `bslOp` of a constant multiple of a separable product. -/
theorem bslOp_sep_const (c α : ℝ) (A : ℝ → ℝ) (v : ℝ → ℝ) (z θ : ℝ)
    (hA : ContDiffAt ℝ 2 A z) :
    Work.Elliptic.bslOp α (fun z θ => (c * A z) * v θ) z θ
      = c * (A z * Work.FTS.EllipticEst.Lzero1 v θ)
        - c * (α ^ 2 * z ^ 2 * iteratedDeriv 2 A z + α * (5 + α) * z * deriv A z) * v θ := by
  have h := bslOp_sep α (fun z => c * A z) v z θ
  rw [iteratedDeriv_const_mul c hA,
    deriv_const_mul c (hA.differentiableAt (by norm_num))] at h
  rw [h]
  ring

/-- `C²`-regularity of the two telescoping iterates `ψ₂ = σ·LinvI ψ`, `ψ₃ = σ·LinvI ψ₂` at
every interior point of the angular interval, for an angular model `ψ`.

Both are of the form `σ·(primitive of a smooth function)`: `Linv23_smooth` (`linv23_smooth`)
provides `C^∞`-regularity of `LinvI h` on `(0,π/2)` together with the local bounds on `LinvI h`
on `(0,t)`, `t < π/2`, as soon as `h` is `C^∞` on `(0,π/2)` and locally bounded at `0⁺`.
Applying it first to `ψ` (locally bounded by `hψ.cont` on the compact `[0,π/2]`) gives `ψ₂`, and
then to `ψ₂` (locally bounded because `|σ| ≤ 1`) gives `ψ₃`; the smooth factor `σ = sin 2θ` is
handled by the product rule. -/
theorem telescoping_psi23_contDiffAt {α : ℝ} {ψ : ℝ → ℝ} (hψ : Work.FTS.PhiStar.AngModel α ψ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ 2 (Work.FTS.PhiStar.Psi2 ψ) θ ∧
    ContDiffAt ℝ 2 (Work.FTS.PhiStar.Psi3 ψ) θ := by
  -- local boundedness of `ψ` on `(0,t)`, `t < π/2`
  have hbddψ : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      ∃ M : ℝ, ∀ x ∈ Set.Ioo 0 t, |ψ x| ≤ M := by
    intro t ht0 ht1
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := ψ) hψ.cont
    refine ⟨C, fun x hx => ?_⟩
    simpa only [Real.norm_eq_abs] using
      hC x ⟨le_of_lt hx.1, le_of_lt (lt_of_lt_of_le hx.2 (le_of_lt ht1))⟩
  obtain ⟨-, hLIsm, -, hLIbdd⟩ := linv23_smooth hψ.smooth hbddψ
  have hs2sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Construction.s2 θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Work.Construction.s2 θ) := by
      rw [show (fun θ : ℝ => Work.Construction.s2 θ) = fun θ => Real.sin (2 * θ) from rfl]
      exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
    exact h.contDiffOn
  have hpsi2sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Work.FTS.PhiStar.Psi2 ψ) (Set.Ioo 0 (Real.pi / 2)) := by
    rw [show Work.FTS.PhiStar.Psi2 ψ
      = fun θ => Work.Construction.s2 θ * Work.FTS.PhiStar.LinvI ψ θ from rfl]
    exact hs2sm.mul hLIsm
  have hbddψ2 : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      ∃ M : ℝ, ∀ x ∈ Set.Ioo 0 t, |Work.FTS.PhiStar.Psi2 ψ x| ≤ M := by
    intro t ht0 ht1
    obtain ⟨M, hM⟩ := hLIbdd t ht0 ht1
    refine ⟨max M 0, fun x hx => ?_⟩
    have h1 : |Work.FTS.PhiStar.LinvI ψ x| ≤ max M 0 :=
      le_trans (hM x hx) (le_max_left _ _)
    have h2 : |Work.Construction.s2 x| ≤ 1 := by
      rw [show Work.Construction.s2 x = Real.sin (2 * x) from rfl]
      exact Real.abs_sin_le_one _
    rw [show Work.FTS.PhiStar.Psi2 ψ x
      = Work.Construction.s2 x * Work.FTS.PhiStar.LinvI ψ x from rfl, abs_mul]
    calc |Work.Construction.s2 x| * |Work.FTS.PhiStar.LinvI ψ x|
        ≤ 1 * max M 0 := mul_le_mul h2 h1 (abs_nonneg _) (by norm_num)
      _ = max M 0 := one_mul _
  obtain ⟨-, hLI2sm, -, -⟩ := linv23_smooth hpsi2sm hbddψ2
  have hpsi3sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Work.FTS.PhiStar.Psi3 ψ) (Set.Ioo 0 (Real.pi / 2)) := by
    rw [show Work.FTS.PhiStar.Psi3 ψ
      = fun θ => Work.Construction.s2 θ * Work.FTS.PhiStar.LinvI (Work.FTS.PhiStar.Psi2 ψ) θ
      from rfl]
    exact hs2sm.mul hLI2sm
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  exact ⟨(hpsi2sm.contDiffAt hmem).of_le (m := 2) (by norm_num),
    (hpsi3sm.contDiffAt hmem).of_le (m := 2) (by norm_num)⟩

theorem telescoping {α : ℝ} (hα : 0 < α) {ψ : ℝ → ℝ} (hψ : Work.FTS.PhiStar.AngModel α ψ) {R : Work.FTS.Galerkin.Fn}
    (hR : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α R z θ = Work.FTS.PhiStar.RemSource α ψ z θ)
    (hL2 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.FTS.EllipticEst.Lzero1
        (fun θ' => Work.Construction.s2 θ' * Work.FTS.PhiStar.LinvI ψ θ') θ = ψ θ)
    (hL3 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.FTS.EllipticEst.Lzero1
        (fun θ' => Work.Construction.s2 θ'
          * Work.FTS.PhiStar.LinvI (Work.FTS.PhiStar.Psi2 ψ) θ') θ
        = Work.FTS.PhiStar.Psi2 ψ θ)
    (hC2R : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (Function.uncurry R) (z, θ)) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α (fun z θ => R z θ
        - (α ^ 2 * Work.FTS.VocabO.phiA α z * Work.FTS.PhiStar.Psi2 ψ θ
           + α ^ 3 * Work.FTS.PhiStar.phiAj 2 α z * Work.FTS.PhiStar.Psi3 ψ θ)) z θ
      = α ^ 4 * Work.FTS.PhiStar.phiAj 3 α z * Work.FTS.PhiStar.Psi3 ψ θ := by
  have hαpos : 0 < α := hα
  intro z hz θ hθ0 hθ1
  have hmem : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  -- regularity of the coefficients `𝒜φ = phiAj 1`, `𝒜²φ = phiAj 2`, and of `ψ₂`, `ψ₃`
  obtain ⟨hphi2, hphiAj2⟩ := phiAj_smooth2 (α := α) hz
  obtain ⟨hpsi2, hpsi3⟩ := telescoping_psi23_contDiffAt (α := α) hψ hmem
  have hC1 : ContDiffAt ℝ 2 (Function.uncurry
      (fun z θ => (α ^ 2 * Work.FTS.VocabO.phiA α z) * Work.FTS.PhiStar.Psi2 ψ θ)) (z, θ) :=
    contDiffAt_uncurry_sep_mul (α ^ 2) (A := Work.FTS.VocabO.phiA α)
      (v := Work.FTS.PhiStar.Psi2 ψ) hphi2 hpsi2
  have hC2 : ContDiffAt ℝ 2 (Function.uncurry
      (fun z θ => (α ^ 3 * Work.FTS.PhiStar.phiAj 2 α z) * Work.FTS.PhiStar.Psi3 ψ θ))
      (z, θ) :=
    contDiffAt_uncurry_sep_mul (α ^ 3) (A := Work.FTS.PhiStar.phiAj 2 α)
      (v := Work.FTS.PhiStar.Psi3 ψ) hphiAj2 hpsi3
  have hC12 : ContDiffAt ℝ 2 (Function.uncurry
      (fun z θ => (α ^ 2 * Work.FTS.VocabO.phiA α z) * Work.FTS.PhiStar.Psi2 ψ θ
        + (α ^ 3 * Work.FTS.PhiStar.phiAj 2 α z) * Work.FTS.PhiStar.Psi3 ψ θ)) (z, θ) := by
    have hfun : Function.uncurry
        (fun z θ => (α ^ 2 * Work.FTS.VocabO.phiA α z) * Work.FTS.PhiStar.Psi2 ψ θ
          + (α ^ 3 * Work.FTS.PhiStar.phiAj 2 α z) * Work.FTS.PhiStar.Psi3 ψ θ)
        = fun p : ℝ × ℝ =>
            Function.uncurry (fun z θ => (α ^ 2 * Work.FTS.VocabO.phiA α z)
              * Work.FTS.PhiStar.Psi2 ψ θ) p
            + Function.uncurry (fun z θ => (α ^ 3 * Work.FTS.PhiStar.phiAj 2 α z)
              * Work.FTS.PhiStar.Psi3 ψ θ) p := rfl
    rw [hfun]
    exact hC1.add hC2
  -- linearity of `bslOp`, and the two separable pieces
  have hsub := Work.FTS.EllipticEst.bslOp_sub α R
    (fun z θ => (α ^ 2 * Work.FTS.VocabO.phiA α z) * Work.FTS.PhiStar.Psi2 ψ θ
      + (α ^ 3 * Work.FTS.PhiStar.phiAj 2 α z) * Work.FTS.PhiStar.Psi3 ψ θ) z θ hcos
    (hC2R z θ hz hθ0 hθ1) hC12
  have hadd := Work.Elliptic.bslOp_add α
    (fun z θ => (α ^ 2 * Work.FTS.VocabO.phiA α z) * Work.FTS.PhiStar.Psi2 ψ θ)
    (fun z θ => (α ^ 3 * Work.FTS.PhiStar.phiAj 2 α z) * Work.FTS.PhiStar.Psi3 ψ θ)
    z θ hcos hC1 hC2
  have hL2' : Work.FTS.EllipticEst.Lzero1 (Work.FTS.PhiStar.Psi2 ψ) θ = ψ θ :=
    hL2 θ hmem
  have hL3' : Work.FTS.EllipticEst.Lzero1 (Work.FTS.PhiStar.Psi3 ψ) θ
      = Work.FTS.PhiStar.Psi2 ψ θ := hL3 θ hmem
  have e1 : Work.Elliptic.bslOp α
      (fun z θ => (α ^ 2 * Work.FTS.VocabO.phiA α z) * Work.FTS.PhiStar.Psi2 ψ θ) z θ
      = α ^ 2 * Work.FTS.VocabO.phiA α z * ψ θ
        - α ^ 3 * Work.FTS.PhiStar.phiAj 2 α z * Work.FTS.PhiStar.Psi2 ψ θ := by
    have h := bslOp_sep_const (c := α ^ 2) α (Work.FTS.VocabO.phiA α)
      (Work.FTS.PhiStar.Psi2 ψ) z θ hphi2
    rw [h, hL2']
    have hphiaj : Work.FTS.PhiStar.phiAj 2 α z
        = α * z ^ 2 * iteratedDeriv 2 (Work.FTS.VocabO.phiA α) z
          + (5 + α) * z * deriv (Work.FTS.VocabO.phiA α) z := rfl
    rw [hphiaj]
    ring
  have e2 : Work.Elliptic.bslOp α
      (fun z θ => (α ^ 3 * Work.FTS.PhiStar.phiAj 2 α z) * Work.FTS.PhiStar.Psi3 ψ θ) z θ
      = α ^ 3 * Work.FTS.PhiStar.phiAj 2 α z * Work.FTS.PhiStar.Psi2 ψ θ
        - α ^ 4 * Work.FTS.PhiStar.phiAj 3 α z * Work.FTS.PhiStar.Psi3 ψ θ := by
    have h := bslOp_sep_const (c := α ^ 3) α (Work.FTS.PhiStar.phiAj 2 α)
      (Work.FTS.PhiStar.Psi3 ψ) z θ hphiAj2
    rw [h, hL3']
    have hphiaj3 : Work.FTS.PhiStar.phiAj 3 α z
        = α * z ^ 2 * iteratedDeriv 2 (Work.FTS.PhiStar.phiAj 2 α) z
          + (5 + α) * z * deriv (Work.FTS.PhiStar.phiAj 2 α) z := rfl
    rw [hphiaj3]
    ring
  have hR' : Work.Elliptic.bslOp α R z θ = α ^ 2 * Work.FTS.VocabO.phiA α z * ψ θ := by
    have h := hR z hz θ hθ0 hθ1
    rw [Work.FTS.PhiStar.RemSource] at h
    exact h
  rw [hsub, hadd, e1, e2, hR']
  ring

end Work.FTS.PhiStar
