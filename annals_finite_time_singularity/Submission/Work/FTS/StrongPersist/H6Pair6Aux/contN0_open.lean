import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.OpenPkg.l12diff_field

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option maxHeartbeats 800000

/-- **Joint continuity of `N₀ α (F_*+g) g` on the open quadrant**, in the *open* datum class
`SmoothOpen g` + `HkMem α 4 g`.

`N₀` is a sum of six terms, each a product of the angular factors `sin(2θ)`, `cos 2θ - sin²θ`,
the radial factors `z ↦ L₁₂(g)(z)` (`Work.Construction.L12 g`) and `z ↦ L₁₂(F_*)(z)`, and the
fields `g`, `∂_θg`, `z∂_zg`, `∂_θ(F_*+g)`, `z∂_z(F_*+g)`.  Every factor is continuous on the
open quadrant:

* `g` and its `∂_θ`/`z∂_z` derivatives, because `SmoothOpen` is preserved by `pz`/`pth`/`Dz`
  (`EllipticEst.SmoothOpen.pz`, `.pth`, `.Dz`) and a `C^∞` function is continuous;
* `F_*` and its derivatives, from `LocData.Fstar_smoothQuad` (the open quadrant `Q0` sits inside
  the strip `quadU = (-1,∞) × (0,π/2)`), and hence the same for `F_* + g`;
* `L₁₂(F_*)(z) = 2α/(1+z)` (`continuousOn_L12_Fstar`);
* `z ↦ L₁₂(g)(z)`, by `OpenPkg.l12diff_field` (`Construction.L12` is *definitionally*
  `Elliptic.L12`, hence differentiable on `(0,∞)` for a `SmoothOpen` honest `ℋ⁴` datum, by
  `UopHk.contDiffOn_L12_of_smoothOpen_Hk`).

The assembly is the one of `Work.FTS.Nonlinear.Pieces.continuousOn_uncurry_N0` (the
stronger-class sibling of this statement), with the `SmoothQuad`-hypotheses replaced by the
`SmoothOpen` API. -/
theorem contN0_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ContinuousOn (Function.uncurry (Work.Construction.N0 α (Work.Construction.Ftot α g) g))
      (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  -- smoothness of the explicit profile `F_*` on the open quadrant
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    (Work.FTS.LocData.Fstar_smoothQuad α).mono (by
      intro p hp
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ⟨by show (-1 : ℝ) < p.1; linarith, hθ0, hθ1⟩)
  -- smoothness of the full profile `F = F_* + g`
  have hT : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Ftot α g) :=
    hF.add hso
  -- `z ↦ L₁₂(g)(z)` on `(0,∞)`, from the differentiability delivered by `l12diff_field`
  have hLg : ContinuousOn (fun z : ℝ => Work.Construction.L12 g z) (Set.Ioi 0) :=
    DifferentiableOn.continuousOn (fun z hz =>
      (Work.FTS.OpenPkg.l12diff_field α g hα hα1 ⟨hso, hmem⟩ z hz).differentiableWithinAt)
  -- `z ↦ L₁₂(F_*)(z) = 2α/(1+z)` on `(0,∞)`
  have hLF : ContinuousOn (fun z : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (Set.Ioi 0) := Work.FTS.Nonlinear.Pieces.continuousOn_L12_Fstar hα hα1
  have hpthg : ContinuousOn (Function.uncurry (Work.Spaces.pth g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hso.pth.continuousOn
  have hpzg : ContinuousOn (Function.uncurry (Work.Spaces.pz g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hso.pz.continuousOn
  have hpthF : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Construction.Fstar α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hF.pth.continuousOn
  have hpzF : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Construction.Fstar α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hF.pz.continuousOn
  have hpthT : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Construction.Ftot α g)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hT.pth.continuousOn
  have hpzT : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Construction.Ftot α g)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hT.pz.continuousOn
  have hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hso.continuousOn
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.s2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    simp only [Work.Construction.s2]
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hc2m : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    simp only [Work.Construction.c2m]
    exact (((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).sub
      ((Real.continuous_sin.comp continuous_snd).pow 2))).continuousOn
  have hLg' : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.L12 g p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hLg.comp continuousOn_fst (fun p hp => hp.1)
  have hLF' : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.L12 (Work.Construction.Fstar α) p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hLF.comp continuousOn_fst (fun p hp => hp.1)
  have h1 : ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * Work.Construction.s2 p.2
        * Work.Construction.L12 (Work.Construction.Fstar α) p.1
        * Work.Spaces.pth (Work.Construction.Fstar α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (3 / (2 * α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).mul hsin).mul hLF').mul hpthF).congr ?_
    intro p hp; simp only [Function.uncurry, Pi.mul_apply]
  have h2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Construction.L12 (Work.Construction.Fstar α) p.1
        * Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((hc2m.mul hLF').mul (continuousOn_fst.mul hpzF)).congr ?_
    intro p hp; simp only [Function.uncurry, Work.Spaces.Dz, Pi.mul_apply]
  have h3 : ContinuousOn (fun p : ℝ × ℝ =>
      (1 / α) * Work.Construction.L12 g p.1 * g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine (((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (1 / α))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).mul hLg').mul hg).congr ?_
    intro p hp; simp only [Function.uncurry, Pi.mul_apply]
  have h4 : ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * Work.Construction.s2 p.2 * Work.Construction.L12 g p.1
        * Work.Spaces.pth (Work.Construction.Ftot α g) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (3 / (2 * α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).mul hsin).mul hLg').mul hpthT).congr ?_
    intro p hp; simp only [Function.uncurry, Pi.mul_apply]
  have h5 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Construction.L12 g p.1
        * Work.Spaces.Dz (Work.Construction.Ftot α g) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((hc2m.mul hLg').mul (continuousOn_fst.mul hpzT)).congr ?_
    intro p hp; simp only [Function.uncurry, Work.Spaces.Dz, Pi.mul_apply]
  have h6 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Construction.L12 (Work.Construction.Fstar α) p.1
        * Work.Spaces.Dz g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((hc2m.mul hLF').mul (continuousOn_fst.mul hpzg)).congr ?_
    intro p hp; simp only [Function.uncurry, Work.Spaces.Dz, Pi.mul_apply]
  have key : ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * Work.Construction.s2 p.2
          * Work.Construction.L12 (Work.Construction.Fstar α) p.1
          * Work.Spaces.pth (Work.Construction.Fstar α) p.1 p.2
        - Work.Construction.c2m p.2 * Work.Construction.L12 (Work.Construction.Fstar α) p.1
          * Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2
        + (1 / α) * Work.Construction.L12 g p.1 * g p.1 p.2
        + (3 / (2 * α)) * Work.Construction.s2 p.2 * Work.Construction.L12 g p.1
          * Work.Spaces.pth (Work.Construction.Ftot α g) p.1 p.2
        - Work.Construction.c2m p.2 * Work.Construction.L12 g p.1
          * Work.Spaces.Dz (Work.Construction.Ftot α g) p.1 p.2
        - Work.Construction.c2m p.2 * Work.Construction.L12 (Work.Construction.Fstar α) p.1
          * Work.Spaces.Dz g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((((h1.sub h2).add h3).add h4).sub h5).sub h6 |>.congr ?_
    intro p hp
    simp only [Pi.sub_apply, Pi.add_apply]
  refine key.congr ?_
  intro p hp
  simp only [Function.uncurry, Work.Construction.N0]

end Work.FTS.StrongPersist.H6Pair6Aux
