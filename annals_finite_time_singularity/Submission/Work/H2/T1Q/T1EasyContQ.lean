/-
# `Work.H2.T1Q.T1EasyContQ` — continuity and a.e. strong measurability of `T1Easy`

`Work.FTS.H2.T1Easy α f g = H4PairInt α (f · D_θg) g - T1Hard α f g` is a finite sum of products of
the slots `D_z^i` and `D_z^jD_θ^i` of `f`, `g` (and of the factor `f · D_θ g`) with the two weights
`Whz = w/sin(2θ)^{η/2}` and `Wm = w·sin(2θ)^{-γ/2}`, all of which are continuous on the open
quadrant `quadQ = (0,∞) × (0,π/2)` when `f`, `g` are of class `SmoothQuad`.  Hence `T1Easy α f g`
is continuous on `quadQ` (`continuousOn_T1Easy_qd`), and therefore a.e. strongly measurable for the
product measure `pm` (`aesm_T1Easy_qd`).

The two `D_θ`-slots `D_θ(D_z^j u)` and `D_θ(D_z^jD_θ^i u)` are handled by expressing them as the
mixed slots `D_z^jD_θ u` resp. `D_z^jD_θ^{i+1} u` (the commutation
`Work.H2.WPQ.Dth_DzIter_comm_smoothQuad`), and the products are discharged by `fun_prop`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Submission.Work.FTS.H2.T2Aesm
import Submission.Work.FTS.H2.T1EasyBound
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.H2.WPQ.Dth_DzIter_comm_smoothQuad
import Submission.Work.H2.T1Q.SlotOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.H2

/-- Continuity of the `i`-th pure `D_z`-slot on the open quadrant. -/
theorem continuousOn_dzIter_qd (u : ℝ → ℝ → ℝ) (hu : Work.FTS.LocData.SmoothQuad u) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i u p.1 p.2) Work.FTS.H2.HQ.quadQ :=
  ((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hu i).continuousOn.mono
    Work.FTS.H2.HQ.quadQ_subset_quadU)

/-- Continuity of the `(j,i)`-th mixed slot on the open quadrant. -/
theorem continuousOn_mixed_qd (u : ℝ → ℝ → ℝ) (hu : Work.FTS.LocData.SmoothQuad u) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i u p.1 p.2) Work.FTS.H2.HQ.quadQ :=
  ((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hu j i).continuousOn.mono
    Work.FTS.H2.HQ.quadQ_subset_quadU)

/-- Continuity of `D_θ(D_z^j u)` on the open quadrant (it equals the mixed slot `D_z^jD_θ u`). -/
theorem continuousOn_Dth_dzIter_qd (u : ℝ → ℝ → ℝ) (hu : Work.FTS.LocData.SmoothQuad u) (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth (Work.Spaces.DzIter j u) p.1 p.2)
      Work.FTS.H2.HQ.quadQ :=
  ContinuousOn.congr (continuousOn_mixed_qd u hu j 1) (fun p hp =>
    Work.H2.WPQ.Dth_DzIter_comm_smoothQuad hu j (Set.mem_Ici.mpr (le_of_lt hp.1)) hp.2)

/-- Continuity of `D_θ(mixed j i u)` on the open quadrant (it equals `mixed j (i+1) u`). -/
theorem continuousOn_Dth_mixed_qd (u : ℝ → ℝ → ℝ) (hu : Work.FTS.LocData.SmoothQuad u)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth (Work.Spaces.mixed j i u) p.1 p.2)
      Work.FTS.H2.HQ.quadQ :=
  ContinuousOn.congr (continuousOn_mixed_qd u hu j (i + 1)) (fun p hp => by
    have h := Work.H2.WPQ.Dth_DzIter_comm_smoothQuad (hu.DthIter i) j
      (Set.mem_Ici.mpr (le_of_lt hp.1)) hp.2
    simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_add_right, Nat.one_add] using h)

/-- Continuity of `H4PairInt α u g` on the open quadrant for `SmoothQuad` data. -/
theorem continuousOn_H4PairInt_qd (α : ℝ) (u g : ℝ → ℝ → ℝ)
    (hu : Work.FTS.LocData.SmoothQuad u) (hg : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (fun p : ℝ × ℝ => H4PairInt α u g p.1 p.2) Work.FTS.H2.HQ.quadQ := by
  have hDz : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i u p.1 p.2)
      Work.FTS.H2.HQ.quadQ := fun i => continuousOn_dzIter_qd u hu i
  have hDz' : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i g p.1 p.2)
      Work.FTS.H2.HQ.quadQ := fun i => continuousOn_dzIter_qd g hg i
  have hMx : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i u p.1 p.2)
      Work.FTS.H2.HQ.quadQ := fun j i => continuousOn_mixed_qd u hu j i
  have hMx' : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2)
      Work.FTS.H2.HQ.quadQ := fun j i => continuousOn_mixed_qd g hg j i
  have hWhz : ContinuousOn (fun p : ℝ × ℝ => Whz p.1 p.2) Work.FTS.H2.HQ.quadQ :=
    continuousOn_Whz_quad
  have hWm : ContinuousOn (fun p : ℝ × ℝ => Wm α p.1 p.2) Work.FTS.H2.HQ.quadQ :=
    continuousOn_Wm_quad α
  have hterm : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.DzIter i u p.1 p.2 * Whz p.1 p.2
        * (Work.Spaces.DzIter i g p.1 p.2 * Whz p.1 p.2)) Work.FTS.H2.HQ.quadQ := by
    intro i
    fun_prop
  have hmixed : ∀ i j : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.mixed j i u p.1 p.2 * Wm α p.1 p.2
        * (Work.Spaces.mixed j i g p.1 p.2 * Wm α p.1 p.2)) Work.FTS.H2.HQ.quadQ := by
    intro i j
    fun_prop
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (∑ i ∈ Finset.range 5, Work.Spaces.DzIter i u p.1 p.2 * Whz p.1 p.2
          * (Work.Spaces.DzIter i g p.1 p.2 * Whz p.1 p.2))
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then Work.Spaces.mixed j i u p.1 p.2 * Wm α p.1 p.2
              * (Work.Spaces.mixed j i g p.1 p.2 * Wm α p.1 p.2) else 0))
      Work.FTS.H2.HQ.quadQ := by
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_finsetSum _ fun i _ => hterm i
    · refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · simpa only [if_pos hc] using hmixed i j
      · simpa only [if_neg hc] using continuousOn_const
  exact ContinuousOn.congr hcont (fun p _ => by simp only [H4PairInt])

/-- Continuity of `T1Hard α f g` on the open quadrant for `SmoothQuad` data. -/
theorem continuousOn_T1Hard_qd (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (fun p : ℝ × ℝ => T1Hard α f g p.1 p.2) Work.FTS.H2.HQ.quadQ := by
  have hf0 : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.H2.HQ.quadQ :=
    hf.continuousOn.mono Work.FTS.H2.HQ.quadQ_subset_quadU
  have hw2 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) Work.FTS.H2.HQ.quadQ :=
    (Work.FTS.H2.continuousOn_w_Qd).pow 2
  have hDz : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i g p.1 p.2)
      Work.FTS.H2.HQ.quadQ := fun i => continuousOn_dzIter_qd g hg i
  have hMx : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2)
      Work.FTS.H2.HQ.quadQ := fun j i => continuousOn_mixed_qd g hg j i
  have hDthDz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth (Work.Spaces.DzIter 4 g) p.1 p.2)
      Work.FTS.H2.HQ.quadQ := continuousOn_Dth_dzIter_qd g hg 4
  have hDthMx : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dth (Work.Spaces.mixed j i g) p.1 p.2) Work.FTS.H2.HQ.quadQ :=
    fun j i => continuousOn_Dth_mixed_qd g hg j i
  have hsinη : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta))
      Work.FTS.H2.HQ.quadQ := Work.FTS.H2.continuousOn_sin_rpow_Qd (-Work.Spaces.eta)
  have hsinγ : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))
      Work.FTS.H2.HQ.quadQ := Work.FTS.H2.continuousOn_sin_rpow_Qd (-(Work.Spaces.gam α))
  have hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * (Work.Spaces.w p.1) ^ 2 *
      (Work.Spaces.Dth (Work.Spaces.DzIter 4 g) p.1 p.2 * Work.Spaces.DzIter 4 g p.1 p.2
          * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta)
        + (Work.Spaces.Dth (Work.Spaces.mixed 3 1 g) p.1 p.2 * Work.Spaces.mixed 3 1 g p.1 p.2
            + Work.Spaces.Dth (Work.Spaces.mixed 2 2 g) p.1 p.2 * Work.Spaces.mixed 2 2 g p.1 p.2
            + Work.Spaces.Dth (Work.Spaces.mixed 1 3 g) p.1 p.2 * Work.Spaces.mixed 1 3 g p.1 p.2
            + Work.Spaces.Dth (Work.Spaces.mixed 0 4 g) p.1 p.2 * Work.Spaces.mixed 0 4 g p.1 p.2)
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))) Work.FTS.H2.HQ.quadQ := by
    fun_prop
  exact ContinuousOn.congr hcont (fun p _ => by simp only [T1Hard])

/-- Continuity of `T1Easy α f g` on the open quadrant. -/
theorem continuousOn_T1Easy_qd (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (Function.uncurry (T1Easy α f g)) Work.FTS.H2.HQ.quadQ := by
  have hu : Work.FTS.LocData.SmoothQuad (fun z θ => f z θ * Work.Spaces.Dth g z θ) :=
    Work.FTS.LocData.smoothQuad_mul hf (hg.DthIter 1)
  have hH := continuousOn_H4PairInt_qd α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g hu hg
  have hT := continuousOn_T1Hard_qd α f g hf hg
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      H4PairInt α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g p.1 p.2 - T1Hard α f g p.1 p.2)
      Work.FTS.H2.HQ.quadQ := hH.sub hT
  exact ContinuousOn.congr hcont (fun p _ => by simp only [Function.uncurry, T1Easy])

/-- Almost-everywhere strong measurability of `T1Easy α f g` for `pm`. -/
theorem aesm_T1Easy_qd (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    AEStronglyMeasurable (Function.uncurry (T1Easy α f g)) pm :=
  Work.FTS.H2.aesm_of_Qd (continuousOn_T1Easy_qd α f g hf hg)

/-- Almost-everywhere strong measurability of `|T1Easy α f g|` for `pm`. -/
theorem aesm_abs_T1Easy_qd (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => |T1Easy α f g z θ|)) pm :=
  (aesm_T1Easy_qd α f g hf hg).norm.congr
    (Eventually.of_forall (fun p => by simp only [Function.uncurry, Real.norm_eq_abs]))

end Work.H2.T1Q
