/-
Copyright: work module for the Elgindi finite-time singularity project.

# The open-quadrant smoothness class `SmoothOpen` and its basic API

The estimates of §'Elliptic Regularity Estimates' of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021)

are stated for a source `F` which is `C^∞` on the *open* quadrant `(0,∞) × (0,π/2)` and
honestly in the weighted space `ℋ^k` (`Work.Spaces.HkMem`).  The older hypothesis
`Work.Spaces.SmoothNbhd` (of the delivered module `Fstar_Hk_le`) asks for *analyticity* on a
neighbourhood of the *closed* quadrant, which is far too strong (a cut-off is `C^∞` but never
analytic, cf. `Work.FTS.LocData`).

This module fixes the vocabulary of the open-quadrant version:

* `Q0` is the open quadrant `(0,∞) × (0,π/2)`;
* `SmoothOpen F` is `C^∞` (all finite orders, i.e. `Work.Stability.smoothOrder`) of the
  uncurried `F` on `Q0`; it is *equivalent* to the raw shape
  `∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2))` of the
  statements (`smoothOpen_iff_forall`).

The API collected here is what the deferred lemmas of the chapter
(`moment_relation`, `PsiInt_sq_mul_w_le_open`, …) and the main estimate
`Work.FTS.EllipticEst.Fstar_Hk_le_open` need:

* `SmoothOpen.DzIter`, `SmoothOpen.mixed`, `SmoothOpen.pz`, … : the iterated operators
  preserve `C^∞` on the open quadrant (from the generic `Work.FTS.LocData` lemmas);
* `SmoothOpen.curry_z`, `SmoothOpen.curry_θ`, `SmoothOpen.hasDerivAt_slice`,
  `SmoothOpen.hasDerivAt_slice_pzIter` : the slices and their differentiability;
* `SmoothOpen.continuousOn_summand`, `SmoothOpen.aesm_slice_summand` : continuity of the
  weighted `D_z`-summand on the open quadrant and the a.e. strong measurability of its
  angular slices (via `Work.Spaces.aesm_slice_of_continuousOn_Qd`);
* `integrableOn_zSummand` : a single weighted `D_z`-summand of `HkIntegrand` is integrable on
  the angular slice, for every `z ∈ Iz`, as soon as `F ∈ ℋ^k`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.EllipticEst.FstarHkAux
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

variable {F G : ℝ → ℝ → ℝ}

/-! ## The open quadrant and the smoothness class -/

/-- The open quadrant `(0,∞) × (0,π/2)` of the elliptic estimates. -/
def Q0 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_Q0 : IsOpen Q0 := isOpen_Ioi.prod isOpen_Ioo

theorem mem_Q0 {z θ : ℝ} : (z, θ) ∈ Q0 ↔ 0 < z ∧ 0 < θ ∧ θ < π / 2 := by
  simp only [Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

/-- **The smoothness class of the open-quadrant statements**: the uncurried `F` is `C^∞` on
the open quadrant `(0,∞) × (0,π/2)`. -/
def SmoothOpen (F : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry F) Q0

/-- `SmoothOpen` is exactly the raw hypothesis shape used by the statements of the chapter. -/
theorem smoothOpen_iff_forall (F : ℝ → ℝ → ℝ) :
    SmoothOpen F ↔ ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Q0 := by
  constructor
  · intro h n
    exact contDiffOn_iff_forall_nat_le.mp h n le_top
  · intro h
    exact contDiffOn_iff_forall_nat_le.mpr (fun m _ => h m)

theorem smoothOpen_of_forall {F : ℝ → ℝ → ℝ}
    (h : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Q0) : SmoothOpen F :=
  (smoothOpen_iff_forall F).mpr h

theorem SmoothOpen.forall (hF : SmoothOpen F) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry F) Q0 :=
  (smoothOpen_iff_forall F).mp hF n

/-! ## The bridge from the re-scoped strong class

`EllHyp.smooth` is `Work.Spaces.SmoothInt Ψ` (`C^∞` on the open strip `(-1,∞) × (0,π/2)` plus
`C^∞` `z`-slices), so a consumer that used `EllHyp.smooth` only for *open-quadrant* facts can
switch to these two lemmas instead of demanding `SmoothNbhd`.  (The boundary `θ`-facts — e.g.
`SmoothNbhd (∂_θΨ)` at `θ = 0, π/2` — are *not* consequences of `SmoothInt`; those consumers are
the class-B residue.) -/

/-- The open-quadrant smoothness component of `SmoothInt`: this is the replacement for
`SmoothNbhd_smoothOpen`/`smoothOpen_of_smoothNbhd` at the (re-scoped) field `EllHyp.smooth`. -/
theorem smoothOpen_of_smoothInt {F : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothInt F) : SmoothOpen F := by
  refine (smoothOpen_iff_forall F).mpr fun n => ?_
  have hsub : Q0 ⊆ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    intro p hp
    have hp' : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := hp
    have hp1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp').1
    have hp2 : p.2 ∈ Set.Ioo (0 : ℝ) (π / 2) := (Set.mem_prod.mp hp').2
    exact Set.mem_prod.mpr ⟨show (-1 : ℝ) < p.1 from by linarith, hp2⟩
  exact ((h.1.of_le le_top).mono hsub).of_le le_top

/-- Continuity of the (uncurried) datum on the open quadrant, from `SmoothInt`. -/
theorem continuousOn_uncurry_of_smoothInt {F : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothInt F) :
    ContinuousOn (Function.uncurry F) Q0 :=
  (smoothOpen_of_smoothInt h).continuousOn

/-! ## The iterated operators preserve `C^∞` on the open quadrant -/

theorem SmoothOpen.pz (hF : SmoothOpen F) : SmoothOpen (Work.Spaces.pz F) :=
  Work.FTS.LocData.contDiffOn_pz isOpen_Q0 hF

theorem SmoothOpen.pth (hF : SmoothOpen F) : SmoothOpen (Work.Spaces.pth F) :=
  Work.FTS.LocData.contDiffOn_pth isOpen_Q0 hF

theorem SmoothOpen.Dz (hF : SmoothOpen F) : SmoothOpen (Work.Spaces.Dz F) :=
  Work.FTS.LocData.contDiffOn_Dz isOpen_Q0 hF

theorem SmoothOpen.Dth (hF : SmoothOpen F) : SmoothOpen (Work.Spaces.Dth F) :=
  Work.FTS.LocData.contDiffOn_Dth isOpen_Q0 hF

theorem SmoothOpen.pzIter (hF : SmoothOpen F) (i : ℕ) : SmoothOpen (Work.Spaces.pzIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pzIter_succ]; exact ih.pz

theorem SmoothOpen.DzIter (hF : SmoothOpen F) (i : ℕ) : SmoothOpen (Work.Spaces.DzIter i F) :=
  Work.FTS.LocData.contDiffOn_DzIter isOpen_Q0 hF i

theorem SmoothOpen.DthIter (hF : SmoothOpen F) (i : ℕ) : SmoothOpen (Work.Spaces.DthIter i F) :=
  Work.FTS.LocData.contDiffOn_DthIter isOpen_Q0 hF i

theorem SmoothOpen.mixed (hF : SmoothOpen F) (j i : ℕ) : SmoothOpen (Work.Spaces.mixed j i F) :=
  Work.FTS.LocData.contDiffOn_mixed isOpen_Q0 hF j i

/-! ## Slices -/

/-- The `z`-slice of a function `C^∞` on the open quadrant, at an interior angle. -/
theorem SmoothOpen.curry_z (hF : SmoothOpen F) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => F z θ) (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z hF hθ

/-- The `θ`-slice of a function `C^∞` on the open quadrant, at a positive radius. -/
theorem SmoothOpen.curry_θ (hF : SmoothOpen F) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => F z θ) (Set.Ioo 0 (π / 2)) :=
  Work.FTS.LocData.contDiffOn_slice_θ hF hz

/-- **The `z`-derivative of the slice.**  For `θ` interior, the slice `z ↦ F z θ` is
differentiable at every `z > 0`, with derivative `Work.Spaces.pz F z θ`. -/
theorem SmoothOpen.hasDerivAt_slice (hF : SmoothOpen F) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => F z' θ) (Work.Spaces.pz F z θ) z :=
  ((hF.curry_z hθ).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioi.mem_nhds hz) |>.hasDerivAt

/-- **The `z`-derivative of the slice of an iterated `∂_z`-derivative.** -/
theorem SmoothOpen.hasDerivAt_slice_pzIter (hF : SmoothOpen F) (i : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter i F z' θ)
      (Work.Spaces.pzIter (i + 1) F z θ) z := by
  have h := (hF.pzIter i).hasDerivAt_slice hθ hz
  simpa only [Work.Spaces.pzIter_succ] using h

/-- **The `z`-derivative of the slice of an iterated `D_z`-derivative.** -/
theorem SmoothOpen.hasDerivAt_slice_DzIter (hF : SmoothOpen F) (i : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => Work.Spaces.DzIter i F z' θ)
      (Work.Spaces.pz (Work.Spaces.DzIter i F) z θ) z :=
  (hF.DzIter i).hasDerivAt_slice hθ hz

/-! ## Continuity of the weighted derivatives on the open quadrant -/

/-- The weight `w z / sin(2θ)^{η/2}` is continuous on the open quadrant. -/
theorem continuousOn_wdivsin_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1
      / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1)
  have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Q0 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  exact hw.div hsin (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))

/-- The uncurried weighted `D_z`-summand is continuous on the open quadrant. -/
theorem SmoothOpen.continuousOn_summand (hF : SmoothOpen F) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) Q0 :=
  ((hF.DzIter i).continuousOn).mul continuousOn_wdivsin_Q0

/-- The uncurried `ℋ^k`-integrand is continuous on the open quadrant. -/
theorem SmoothOpen.continuousOn_HkIntegrand (hF : SmoothOpen F) (α : ℝ) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2) Q0 := by
  have hz : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2) Q0 :=
    fun i => (hF.DzIter i).continuousOn
  have hm : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2) Q0 :=
    fun j i => (hF.mixed j i).continuousOn
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
      have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
          = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
        funext p; rfl
      rw [hfun2]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1))
    refine hw.mul ?_
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i F p.1 p.2
                * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ => ?_)
    exact (((hz i).mul continuousOn_wdivsin_Q0)).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j _ => ?_))
    split_ifs with h
    · exact (((hm j i).mul hWt)).pow 2
    · exact continuousOn_const

/-! ## Measurability and integrability of the angular slices of a summard -/

/-- The angular slice of the weighted `D_z`-summand is a.e. strongly measurable. -/
theorem SmoothOpen.aesm_slice_summand (hF : SmoothOpen F) (i : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter i F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hF.continuousOn_summand i) hz

/-- The angular slice of the plain `∂_z`-iterate is a.e. strongly measurable. -/
theorem SmoothOpen.aesm_slice_pzIter (hF : SmoothOpen F) (i : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.pzIter i F z θ)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.pzIter i F p.1 p.2) (hF.pzIter i).continuousOn hz

/-- A single weighted `D_z`-summand of the `ℋ^k`-integrand is integrable on the angular slice,
for every `z ∈ Iz`, as soon as `F ∈ ℋ^k`.  (The open-quadrant analogue of
`Work.FTS.EllipticEst.integrableOn_zSummand`.) -/
theorem integrableOn_zSummand (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (i : ℕ) (hi : i ≤ k) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter i F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- at `z = 0` the radial weight vanishes and the summand is identically zero
    have hzero : ∀ θ : ℝ, (Work.Spaces.DzIter i F 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
      intro θ
      rw [Work.Spaces.w]
      norm_num
    rw [show (fun θ : ℝ => (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = fun _ : ℝ => (0 : ℝ) from by
      funext θ; rw [← hz0]; exact hzero θ]
    exact integrableOn_zero
  · refine Integrable.mono' (hmem.1 z hz) ((hF.aesm_slice_summand i hzpos).pow 2) ?_
    rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    exact Eventually.of_forall fun θ _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_z α k F z θ i hi

end Work.FTS.EllipticEst
