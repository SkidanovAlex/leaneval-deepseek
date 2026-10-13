/-
Copyright: work module for the Elgindi finite-time singularity project.

# A.e. strong measurability of the `θ`-slice integrals of `Hhard` and of the `D_z`-pairing

This module proves `Work.FTS.H2.AesmSlicesQ`: for `SmoothQuad` data `f`, `g` (genuine `C^∞`
on the open quadrant `(-1,∞) × (0,π/2)`, the class of the localisation chapter, which a
cut-off can satisfy) the radial functions

* `z ↦ ∫_θ Hhard α f g z θ`                     (the "hard" part of `(f D_z g, g)_{ℋ⁴}`), and
* `z ↦ ∫_θ H4PairInt α (f · D_z g) g z θ`       (the full pairing integrand)

are a.e. strongly measurable on `Iz = [0,∞)`.

The route is the one used throughout `Submission/Work/Spaces` and in `T2Aesm` (its
`SmoothNbhd`-analogue):

* every ingredient of `Hhard` and of `H4PairInt α (f·D_z g) g` is a product of weighted
  derivatives `D_z^j D_θ^i` of `f` and `g` (`SmoothQuad` is preserved by `D_z`, `D_θ` and
  their iterates, and by products, `Work.FTS.LocData.SmoothChain`) with the continuous
  weights `w(z) = (1+z)²/z²`, `sin(2θ)^{-η/2}` and `sin(2θ)^{-γ/2}`, plus the factor `z`.
  Hence both integrands are *continuous on the open square* `Qd = (0,∞) × (0,π/2)`;
* continuity on `Qd` upgrades to a.e. strong measurability for
  `(volume.restrict Iz).prod (volume.restrict Iθ)`, because `Qd` exhausts `Iz × Iθ` up to
  the null union of the three segments `{0} × Iθ`, `Iz × {0}`, `Iz × {π/2}`
  (`Work.Spaces.aesm_of_continuousOn_Qd`);
* Fubini for a.e. measurable integrands (`AEStronglyMeasurable.integral_prod_right'`) then
  gives a.e. strong measurability of the partial integral `z ↦ ∫_θ · z θ`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.Qd
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.T2Qaux.SupAux
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.H2.T1Q.T1HardAesmQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.LocData (Qd SmoothQuad)

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Continuity of the mixed derivatives of a `SmoothQuad` function -/

private lemma continuousOn_DzIter_smoothQuad {F : ℝ → ℝ → ℝ} (hF : SmoothQuad F) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2) Qd :=
  ((Work.FTS.LocData.contDiffOn_DzIter Work.FTS.LocData.isOpen_quadU hF i).continuousOn).mono
    Qd_subset_quadU

private lemma continuousOn_mixed_smoothQuad {F : ℝ → ℝ → ℝ} (hF : SmoothQuad F) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2) Qd :=
  ((Work.FTS.LocData.contDiffOn_mixed Work.FTS.LocData.isOpen_quadU hF j i).continuousOn).mono
    Qd_subset_quadU

private lemma continuousOn_of_smoothQuad {F : ℝ → ℝ → ℝ} (hF : SmoothQuad F) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) Qd :=
  (hF.continuousOn).mono Qd_subset_quadU

private lemma continuousOn_pz_mixed_smoothQuad {F : ℝ → ℝ → ℝ} (hF : SmoothQuad F) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.mixed j i F) p.1 p.2) Qd :=
  ((Work.FTS.LocData.contDiffOn_pz Work.FTS.LocData.isOpen_quadU
      (Work.FTS.LocData.contDiffOn_mixed Work.FTS.LocData.isOpen_quadU hF j i)).continuousOn).mono
    Qd_subset_quadU

/-- `D_z` of a `SmoothQuad` function is `SmoothQuad`. -/
private lemma smoothQuad_Dz {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) :
    SmoothQuad (Work.Spaces.Dz G) :=
  Work.FTS.LocData.contDiffOn_Dz Work.FTS.LocData.isOpen_quadU hG

/-! ## Joint continuity of `H4PairInt` on the open square -/

private lemma continuousOn_H4PairInt_smoothQuad (α : ℝ) {u v : ℝ → ℝ → ℝ}
    (hu : SmoothQuad u) (hv : SmoothQuad v) :
    ContinuousOn (fun p : ℝ × ℝ => H4PairInt α u v p.1 p.2) Qd := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 5,
      (Work.Spaces.DzIter i u p.1 p.2 * Whz p.1 p.2)
        * (Work.Spaces.DzIter i v p.1 p.2 * Whz p.1 p.2)) Qd :=
    continuousOn_finsetSum _ fun i _ =>
      ((continuousOn_DzIter_smoothQuad hu i).mul continuousOn_Whz_Qd).mul
        ((continuousOn_DzIter_smoothQuad hv i).mul continuousOn_Whz_Qd)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 then
        (Work.Spaces.mixed j i u p.1 p.2 * Wm α p.1 p.2)
          * (Work.Spaces.mixed j i v p.1 p.2 * Wm α p.1 p.2) else 0)) Qd :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => by
      split_ifs with h
      · exact ((continuousOn_mixed_smoothQuad hu j i).mul (continuousOn_Wm_Qd α)).mul
          ((continuousOn_mixed_smoothQuad hv j i).mul (continuousOn_Wm_Qd α))
      · exact continuousOn_const
  have key : (fun p : ℝ × ℝ => H4PairInt α u v p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i u p.1 p.2 * Whz p.1 p.2)
              * (Work.Spaces.DzIter i v p.1 p.2 * Whz p.1 p.2))
            + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
                (if 1 ≤ i ∧ i + j ≤ 4 then
                  (Work.Spaces.mixed j i u p.1 p.2 * Wm α p.1 p.2)
                    * (Work.Spaces.mixed j i v p.1 p.2 * Wm α p.1 p.2) else 0) := by
    funext p
    rfl
  rw [key]
  exact h1.add h2

/-! ## Joint continuity of `Hhard` on the open square -/

private lemma continuousOn_Thard_smoothQuad {g : ℝ → ℝ → ℝ} (hg : SmoothQuad g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Thard g k p.1 p.2) Qd := by
  fin_cases k
  · simpa only [Thard] using continuousOn_mixed_smoothQuad hg 4 0
  · simpa only [Thard] using continuousOn_mixed_smoothQuad hg 3 1
  · simpa only [Thard] using continuousOn_mixed_smoothQuad hg 2 2
  · simpa only [Thard] using continuousOn_mixed_smoothQuad hg 1 3
  · simpa only [Thard] using continuousOn_mixed_smoothQuad hg 0 4

private lemma continuousOn_pzThard_smoothQuad {g : ℝ → ℝ → ℝ} (hg : SmoothQuad g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Thard g k) p.1 p.2) Qd := by
  fin_cases k
  · simpa only [Thard] using continuousOn_pz_mixed_smoothQuad hg 4 0
  · simpa only [Thard] using continuousOn_pz_mixed_smoothQuad hg 3 1
  · simpa only [Thard] using continuousOn_pz_mixed_smoothQuad hg 2 2
  · simpa only [Thard] using continuousOn_pz_mixed_smoothQuad hg 1 3
  · simpa only [Thard] using continuousOn_pz_mixed_smoothQuad hg 0 4

private lemma continuousOn_Hhard_smoothQuad (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : SmoothQuad f) (hg : SmoothQuad g) :
    ContinuousOn (fun p : ℝ × ℝ => Hhard α f g p.1 p.2) Qd := by
  have hsum : ContinuousOn (fun p : ℝ × ℝ => ∑ k : Fin 5,
      Work.Spaces.pz (Thard g k) p.1 p.2 * Thard g k p.1 p.2
        * (Work.Spaces.w p.1) ^ 2 * sghard α k p.2) Qd :=
    continuousOn_finsetSum _ fun k _ =>
      (((continuousOn_pzThard_smoothQuad hg k).mul (continuousOn_Thard_smoothQuad hg k)).mul
        (continuousOn_w_Qd.pow 2)).mul (continuousOn_sghard α k)
  have key : (fun p : ℝ × ℝ => Hhard α f g p.1 p.2)
      = fun p : ℝ × ℝ => f p.1 p.2 * p.1 * (∑ k : Fin 5,
          Work.Spaces.pz (Thard g k) p.1 p.2 * Thard g k p.1 p.2
            * (Work.Spaces.w p.1) ^ 2 * sghard α k p.2) := by
    funext p
    rfl
  rw [key]
  exact ((continuousOn_of_smoothQuad hf).mul continuousOn_fst).mul hsum

/-! ## The a.e. strong measurability statements -/

theorem AesmSlicesQ : ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α →
    Work.FTS.LocData.SmoothQuad f → Work.FTS.LocData.SmoothQuad g →
    MeasureTheory.AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Hhard α f g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  intro α f g _hα hf hg
  have hu : SmoothQuad (fun z θ => f z θ * Work.Spaces.Dz g z θ) :=
    Work.FTS.LocData.smoothQuad_mul hf (smoothQuad_Dz hg)
  constructor
  · exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_Hhard_smoothQuad α hf hg))
  · exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_H4PairInt_smoothQuad α hu hg))

end Work.FTS.H2
