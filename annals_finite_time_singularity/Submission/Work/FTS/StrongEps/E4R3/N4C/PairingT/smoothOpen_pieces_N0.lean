/-
# `E4R3/N4C/PairingT/smoothOpen_pieces_N0`

The seven pieces of the `N₀`-block of the §8 split,

  `N0fix α`, `N03g α g`, `N04aF α g`, `N04bF α g`, `N05aF α g`, `N05bF α g`, `N06F α g`,

are `C^∞` on the *open* quadrant `(0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.SmoothOpen`) as soon as the honest context of the level-four row is
available: `ClassC α g` (giving `SmoothOpen g` and the all-order smoothness of the radial
function `z ↦ L₁₂(g)(z)`, via the two open-quadrant elliptic packages and the atoms of
`PairingT.Atoms`), plus the two packages `EllPkgGo α Ce g Φg` and `StarPkgo2 α Cs Φs` (only
used to produce the atom `SmoothOpen (z ↦ L₁₂(g)(z))`, through
`Work.FTS.NonlinRows.smoothOpen_L12_radial`).

The proof is a term-by-term assembly: every one of the seven pieces is a finite sum of products
of the atoms

* `g`, `∂_θg`, `D_zg` and `F_*`, `∂_θF_*`, `D_zF_*` — `SmoothOpen` by hypothesis /
  `Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar` and the closure of `SmoothOpen` under
  `pth`, `Dz`,
* the angular factors `s2 θ = sin 2θ` and `c2m θ = cos 2θ - sin²θ` — smooth on `ℝ`,
* the radial factors `z ↦ L₁₂(g)(z)` and `z ↦ L₁₂(F_*)(z)`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.Atoms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.PairingT

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.StrongEps.E4R3.N4C
open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Negation preserves `SmoothOpen`.  (The library's `so_const_mul (-1)` produces
`fun z θ => -1 * f z θ`, which is only propositionally equal to `fun z θ => -f z θ`, and the
product rule below needs the latter shape.) -/
theorem so_neg {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    SmoothOpen (fun z θ => -f z θ) :=
  SmoothOpen.congr (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (-1) hf)
    (fun z θ _ _ _ => by ring)

theorem smoothOpen_pieces_N0 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Cs Ce : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hg : Work.FTS.ClassC.ClassC α g) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N03g α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04aF α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04bF α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05aF α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05bF α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N06F α g) := by
  -- the twelve smoothness atoms of the §8 assembly
  have hA := atomsO_of_ctx hα hα1 hg hell hstar
  -- the angular factors
  have hs2 : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.s2 θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_s2
  have hc2m : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m
  -- the derivatives of the two profiles
  have hpF : SmoothOpen (Work.Spaces.pth (Work.Construction.Fstar α)) :=
    SmoothOpen.pth hA.sFs
  have hDzF : SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
    SmoothOpen.Dz hA.sFs
  have hpg : SmoothOpen (Work.Spaces.pth g) := SmoothOpen.pth hA.sg
  have hDzg : SmoothOpen (Work.Spaces.Dz g) := SmoothOpen.Dz hA.sg
  -- the negated angular factor, in the `-c2m` shape
  have hnc2m : SmoothOpen (fun z (θ : ℝ) => -Work.Construction.c2m θ) := so_neg hc2m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `N0fix α = I^{N₀}_1 + I^{N₀}_2`
    refine SmoothOpen.congr (f := fun z θ =>
        (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        + (-Work.Construction.c2m θ) * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_add
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
          (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
            (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hs2) hA.sLFs)
          hpF)
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
          (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hnc2m hA.sLFs) hDzF)
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N0fix, Work.Construction.N01, Work.Construction.N02]
  · -- `N03g α g = I^{N₀}_3 = (1/α) L₁₂(g) g`
    refine SmoothOpen.congr (f := fun z θ =>
        (1 / α) * Work.Construction.L12 g z * g z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (1 / α) hA.sLg) hA.sg
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
  · -- `N04aF α g = (3/(2α)) sin 2θ L₁₂(g) ∂_θF_*`
    refine SmoothOpen.congr (f := fun z θ => (3 / (2 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 g z * Work.Spaces.pth (Work.Construction.Fstar α) z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
          (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hs2) hA.sLg) hpF
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a]
  · -- `N04bF α g = (3/(2α)) sin 2θ L₁₂(g) ∂_θg`
    refine SmoothOpen.congr (f := fun z θ => (3 / (2 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 g z * Work.Spaces.pth g z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
          (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hs2) hA.sLg) hpg
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b]
  · -- `N05aF α g = -c2m(θ) L₁₂(g) D_zF_*`
    refine SmoothOpen.congr (f := fun z θ => (-Work.Construction.c2m θ)
        * Work.Construction.L12 g z * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hnc2m hA.sLg) hDzF
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
  · -- `N05bF α g = -c2m(θ) L₁₂(g) D_zg`
    refine SmoothOpen.congr (f := fun z θ => (-Work.Construction.c2m θ)
        * Work.Construction.L12 g z * Work.Spaces.Dz g z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hnc2m hA.sLg) hDzg
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
  · -- `N06F α g = -c2m(θ) L₁₂(F_*) D_zg`
    refine SmoothOpen.congr (f := fun z θ => (-Work.Construction.c2m θ)
        * Work.Construction.L12 (Work.Construction.Fstar α) z
        * Work.Spaces.Dz g z θ) ?_ ?_
    · exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hnc2m hA.sLFs) hDzg
    · intro z θ hz hθ hθ2
      simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]

end Work.FTS.StrongEps.E4R3.N4C.PairingT
