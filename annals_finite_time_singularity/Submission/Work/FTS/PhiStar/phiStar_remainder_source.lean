import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.PhiStar

/-- **The telescoping identity `P2` of the `Φ_*` node.**

With `φ = phiR = 2z/(1+z)²`, `𝒜φ = phiA = αz²φ'' + (5+α)zφ'`, `Γ̄ = GamBar = Γ/c − (5/4)sin 2θ`,
`ψ` solving `L₀ψ = Γ̄` in the interior, and `Gz` solving the radial model
`−(α²z²Gz'') − α(5+α)zGz' = (5α/4)φ`,

`bslOp α (Gz·sin 2θ + α·φ·ψ) = F_* − α²·(𝒜φ)·ψ`  on the open quadrant.

Proof: `bslOp` is additive (`bslOp_add`), the first piece is a radial multiple of `sin 2θ`
(`bslOp_radial` + the model equation for `Gz`) and contributes `(5α/4)φ sin 2θ`, the second is a
separable product (`bslOp_sep`) and contributes `α φ (Γ̄ + (5/4)sin 2θ) − α²(𝒜φ)ψ`.  The
`(5α/4)φ sin 2θ` terms cancel and `Γ̄ + (5/4)sin 2θ = Γ/c`, which gives `F_* = α(Γ/c)φ`. -/
theorem phiStar_remainder_source (α : ℝ) (hα : 0 < α) (ψ : ℝ → ℝ) (Gz : ℝ → ℝ)
    (hψ : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (π / 2)))
    (hψeq : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.FTS.EllipticEst.Lzero1 ψ θ = Work.FTS.VocabO.GamBar α θ)
    (hG : ∀ z, 0 < z → -(α ^ 2 * z ^ 2 * iteratedDeriv 2 Gz z) - α * (5 + α) * z * deriv Gz z
        = (5 * α / 4) * Work.FTS.VocabO.phiR z)
    (hGd : ContDiffOn ℝ 2 Gz (Set.Ioi 0)) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α
        (fun z' θ' => Gz z' * Real.sin (2 * θ') + α * Work.FTS.VocabO.phiR z' * ψ θ') z θ
      = Work.Construction.Fstar α z θ - α ^ 2 * Work.FTS.VocabO.phiA α z * ψ θ := by
  intro z hz θ hθ0 hθ1
  have hmem : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  have hcos : Real.cos θ ≠ 0 := by
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, hθ1⟩)
    linarith [Real.pi_pos]
  -- `phiR` is `C²` at `z > 0` (`2z/(1+z)²` is a quotient with nonvanishing denominator there)
  have hphi : ContDiffAt ℝ 2 Work.FTS.VocabO.phiR z := by
    change ContDiffAt ℝ 2 (fun z : ℝ => 2 * z / (1 + z) ^ 2) z
    exact ContDiffAt.div ((contDiffAt_const (c := (2 : ℝ))).mul contDiffAt_id)
      ((contDiffAt_const.add contDiffAt_id).pow 2)
      (by have h1z : (1 + z) ≠ 0 := by intro h; linarith [hz]
          exact pow_ne_zero 2 h1z)
  -- joint `C²` regularity of the two summands, as required by `bslOp_add`
  have hCd1 : ContDiffAt ℝ 2
      (Function.uncurry (fun z' θ' => Gz z' * Real.sin (2 * θ'))) (z, θ) := by
    have h1 : ContDiffAt ℝ 2 Gz z := hGd.contDiffAt (isOpen_Ioi.mem_nhds hz)
    have hfst : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Gz p.1) (z, θ) := by
      simpa [Function.comp_def] using h1.comp (z, θ) (contDiffAt_fst (p := (z, θ)))
    have hsnd : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) (z, θ) := by
      have h2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => 2 * p.2) (z, θ) := by
        simpa [Function.comp_def] using
          (contDiffAt_const (c := (2 : ℝ))).mul (contDiffAt_snd (p := (z, θ)))
      simpa [Function.comp_def] using (Real.contDiff_sin.contDiffAt).comp (z, θ) h2
    change ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Gz p.1 * Real.sin (2 * p.2)) (z, θ)
    exact hfst.mul hsnd
  have hCd2 : ContDiffAt ℝ 2
      (Function.uncurry (fun z' θ' => α * Work.FTS.VocabO.phiR z' * ψ θ')) (z, θ) := by
    have h1 : ContDiffAt ℝ 2 (fun z' => α * Work.FTS.VocabO.phiR z') z :=
      (contDiffAt_const (c := α)).mul hphi
    have h2 : ContDiffAt ℝ 2 ψ θ := hψ.contDiffAt (isOpen_Ioo.mem_nhds hmem)
    have hfst : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => α * Work.FTS.VocabO.phiR p.1) (z, θ) := by
      simpa [Function.comp_def] using h1.comp (z, θ) (contDiffAt_fst (p := (z, θ)))
    have hsnd : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.2) (z, θ) := by
      simpa [Function.comp_def] using h2.comp (z, θ) (contDiffAt_snd (p := (z, θ)))
    change ContDiffAt ℝ 2 (fun p : ℝ × ℝ => α * Work.FTS.VocabO.phiR p.1 * ψ p.2) (z, θ)
    exact hfst.mul hsnd
  -- the radial piece: `bslOp α (Gz · sin 2θ) = (5α/4)φ · sin 2θ`
  have hrad : Work.Elliptic.bslOp α (fun z' θ' => Gz z' * Real.sin (2 * θ')) z θ
      = (5 * α / 4) * Work.FTS.VocabO.phiR z * Real.sin (2 * θ) := by
    rw [bslOp_radial α Gz z θ hcos,
      show -(α ^ 2 * z ^ 2 * iteratedDeriv 2 Gz z + α * (5 + α) * z * deriv Gz z)
        = (5 * α / 4) * Work.FTS.VocabO.phiR z by linarith [hG z hz]]
  -- the separable piece: `bslOp α (α φ ψ) = α φ Γ̄ − α²(𝒜φ) ψ`
  have hsep : Work.Elliptic.bslOp α (fun z' θ' => α * Work.FTS.VocabO.phiR z' * ψ θ') z θ
      = α * Work.FTS.VocabO.phiR z * Work.FTS.VocabO.GamBar α θ
        - α ^ 2 * Work.FTS.VocabO.phiA α z * ψ θ := by
    rw [bslOp_sep α (fun z' => α * Work.FTS.VocabO.phiR z') ψ z θ, hψeq θ hmem]
    have hd1 : deriv (fun z' => α * Work.FTS.VocabO.phiR z') z
        = α * deriv Work.FTS.VocabO.phiR z :=
      deriv_const_mul α (hphi.differentiableAt (by norm_num))
    have hd2 : iteratedDeriv 2 (fun z' => α * Work.FTS.VocabO.phiR z') z
        = α * iteratedDeriv 2 Work.FTS.VocabO.phiR z :=
      iteratedDeriv_const_mul α hphi
    have hcoef : α ^ 2 * z ^ 2 * (α * iteratedDeriv 2 Work.FTS.VocabO.phiR z)
        + α * (5 + α) * z * (α * deriv Work.FTS.VocabO.phiR z)
        = α ^ 2 * Work.FTS.VocabO.phiA α z := by
      rw [Work.FTS.VocabO.phiA]; ring
    rw [hd1, hd2, hcoef]
  rw [Work.Elliptic.bslOp_add α (fun z' θ' => Gz z' * Real.sin (2 * θ'))
        (fun z' θ' => α * Work.FTS.VocabO.phiR z' * ψ θ') z θ hcos hCd1 hCd2]
  rw [hrad, hsep]
  simp only [Work.Construction.Fstar, Work.FTS.VocabO.GamBar, Work.FTS.VocabO.phiR, Work.FM.Fstar]
  ring

end Work.FTS.PhiStar
