/-
Copyright: work module for the Elgindi finite-time singularity project.

# A.e. strong measurability of the "easy part" `Heasy` of the `D_z`-transport pairing

This module provides the measurability input of `T2EasyInt` (`Submission/Work/FTS/H2/T2EasyInt`)
and of `T2psiE`: the integrand `Heasy α f g z θ` of the easy part of the pairing
`(f D_z g, g)_{ℋ⁴}` is *jointly* a.e. strongly measurable for the product of the restricted
Lebesgue measures on `Iz = [0,∞)` and `Iθ = [0,π/2]`, and hence the radial partial integral
`z ↦ ∫_θ Heasy α f g z θ` is a.e. strongly measurable on `Iz`.

The route is the one used throughout `Submission/Work/Spaces`:

* `Heasy = H4PairInt α (f · D_z g) g − Hhard`, and every ingredient is a product of weighted
  derivatives `D_z^j D_θ^i` of `f`, `g` (`Spaces.SmoothNbhd` is preserved by `D_z`, `D_θ` and
  their iterates, `Spaces.mixed_comm`) with the continuous weights `w(z) = (1+z)²/z²` and
  `sin(2θ)^{-γ/2}`.  So `Heasy` is continuous on the open square `Qd = (0,∞) × (0,π/2)`;
* continuity on `Qd` upgrades to a.e. strong measurability for
  `(volume.restrict Iz).prod (volume.restrict Iθ)` because `Qd` exhausts `Iz × Iθ` up to the
  null union of the three segments `{0} × Iθ`, `Iz × {0}`, `Iz × {π/2}`
  (`Work.Spaces.aesm_of_continuousOn_Qd`);
* Fubini for a.e. measurable integrands (`AEStronglyMeasurable.integral_prod_right'`) then
  gives a.e. strong measurability of the partial integral.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.FTS.H2.Qd
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section


/-- A function `C^∞` on an open neighbourhood of the closed quadrant is continuous on the
open square. -/
theorem continuousOn_smoothNbhd {F : ℝ → ℝ → ℝ} (hF : Work.Spaces.SmoothNbhd F) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) Qd :=
  (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) Work.Spaces.nbhU).continuousOn.mono Qd_subset_nbhU

theorem continuousOn_DzIter_of_nbhd {F : ℝ → ℝ → ℝ} (hF : Work.Spaces.SmoothNbhd F)
    (i : ℕ) : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2) Qd :=
  (Work.Spaces.SmoothNbhd.DzIter hF i :
      ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter i F)) Work.Spaces.nbhU).continuousOn.mono
    Qd_subset_nbhU

theorem continuousOn_mixed_of_nbhd {F : ℝ → ℝ → ℝ} (hF : Work.Spaces.SmoothNbhd F)
    (j i : ℕ) : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2) Qd := by
  have h : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.mixed j i F)) Work.Spaces.nbhU :=
    Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hF i) j
  exact h.continuousOn.mono Qd_subset_nbhU

theorem continuousOn_pz_mixed_of_nbhd {F : ℝ → ℝ → ℝ} (hF : Work.Spaces.SmoothNbhd F)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.mixed j i F) p.1 p.2) Qd := by
  have hU : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.mixed j i F)) Work.Spaces.quadU := by
    have h : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.mixed j i F)) Work.Spaces.nbhU :=
      Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hF i) j
    exact h.mono quadU_subset_nbhU
  exact ((Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_quadU hU).continuousOn).mono
    Qd_subset_quadU

/-! ## Continuity of `H4PairInt`, `Hhard` and `Heasy` on the open square -/

theorem continuousOn_H4PairInt_Qd (α : ℝ) {u v : ℝ → ℝ → ℝ}
    (hu : Work.Spaces.SmoothNbhd u) (hv : Work.Spaces.SmoothNbhd v) :
    ContinuousOn (fun p : ℝ × ℝ => H4PairInt α u v p.1 p.2) Qd := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 5,
      (Work.Spaces.DzIter i u p.1 p.2 * Whz p.1 p.2)
        * (Work.Spaces.DzIter i v p.1 p.2 * Whz p.1 p.2)) Qd :=
    continuousOn_finsetSum _ fun i _ =>
      ((continuousOn_DzIter_of_nbhd hu i).mul continuousOn_Whz_Qd).mul
        ((continuousOn_DzIter_of_nbhd hv i).mul continuousOn_Whz_Qd)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 then
        (Work.Spaces.mixed j i u p.1 p.2 * Wm α p.1 p.2)
          * (Work.Spaces.mixed j i v p.1 p.2 * Wm α p.1 p.2) else 0)) Qd :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => by
      split_ifs with h
      · exact ((continuousOn_mixed_of_nbhd hu j i).mul (continuousOn_Wm_Qd α)).mul
          ((continuousOn_mixed_of_nbhd hv j i).mul (continuousOn_Wm_Qd α))
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

theorem continuousOn_Thard_of_nbhd {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g)
    (k : Fin 5) : ContinuousOn (fun p : ℝ × ℝ => Thard g k p.1 p.2) Qd := by
  fin_cases k
  · simpa only [Thard] using continuousOn_mixed_of_nbhd hg 4 0
  · simpa only [Thard] using continuousOn_mixed_of_nbhd hg 3 1
  · simpa only [Thard] using continuousOn_mixed_of_nbhd hg 2 2
  · simpa only [Thard] using continuousOn_mixed_of_nbhd hg 1 3
  · simpa only [Thard] using continuousOn_mixed_of_nbhd hg 0 4

theorem continuousOn_pzThard_of_nbhd {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g)
    (k : Fin 5) : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Thard g k) p.1 p.2) Qd := by
  fin_cases k
  · simpa only [Thard] using continuousOn_pz_mixed_of_nbhd hg 4 0
  · simpa only [Thard] using continuousOn_pz_mixed_of_nbhd hg 3 1
  · simpa only [Thard] using continuousOn_pz_mixed_of_nbhd hg 2 2
  · simpa only [Thard] using continuousOn_pz_mixed_of_nbhd hg 1 3
  · simpa only [Thard] using continuousOn_pz_mixed_of_nbhd hg 0 4

theorem continuousOn_sghard (α : ℝ) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => sghard α k p.2) Qd := by
  fin_cases k
  · simpa only [sghard] using continuousOn_sinpow_Qd (-(Work.Spaces.eta))
  · simpa only [sghard] using continuousOn_sinpow_Qd (-(Work.Spaces.gam α))
  · simpa only [sghard] using continuousOn_sinpow_Qd (-(Work.Spaces.gam α))
  · simpa only [sghard] using continuousOn_sinpow_Qd (-(Work.Spaces.gam α))
  · simpa only [sghard] using continuousOn_sinpow_Qd (-(Work.Spaces.gam α))

theorem continuousOn_Hhard_Qd (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (hg : Work.Spaces.SmoothNbhd g) :
    ContinuousOn (fun p : ℝ × ℝ => Hhard α f g p.1 p.2) Qd := by
  have hsum : ContinuousOn (fun p : ℝ × ℝ => ∑ k : Fin 5,
      Work.Spaces.pz (Thard g k) p.1 p.2 * Thard g k p.1 p.2
        * (Work.Spaces.w p.1) ^ 2 * sghard α k p.2) Qd :=
    continuousOn_finsetSum _ fun k _ =>
      (((continuousOn_pzThard_of_nbhd hg k).mul (continuousOn_Thard_of_nbhd hg k)).mul
        (continuousOn_w_Qd.pow 2)).mul (continuousOn_sghard α k)
  have key : (fun p : ℝ × ℝ => Hhard α f g p.1 p.2)
      = fun p : ℝ × ℝ => f p.1 p.2 * p.1 * (∑ k : Fin 5,
          Work.Spaces.pz (Thard g k) p.1 p.2 * Thard g k p.1 p.2
            * (Work.Spaces.w p.1) ^ 2 * sghard α k p.2) := by
    funext p
    rfl
  rw [key]
  exact ((continuousOn_smoothNbhd hf).mul continuousOn_fst).mul hsum

/-- `Heasy α f g` is continuous on the open square `(0,∞) × (0,π/2)` whenever `f` and `g`
are smooth on a neighbourhood of the closed quadrant. -/
theorem continuousOn_Heasy_Qd (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (hg : Work.Spaces.SmoothNbhd g) :
    ContinuousOn (fun p : ℝ × ℝ => Heasy α f g p.1 p.2) Qd := by
  have hu : Work.Spaces.SmoothNbhd (fun z θ => f z θ * Work.Spaces.Dz g z θ) :=
    (hf : ContDiffOn ℝ ⊤ (Function.uncurry f) Work.Spaces.nbhU).mul
      (Work.Spaces.SmoothNbhd.Dz hg :
        ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dz g)) Work.Spaces.nbhU)
  have h1 := continuousOn_H4PairInt_Qd α hu hg
  have h2 := continuousOn_Hhard_Qd α hf hg
  have key : (fun p : ℝ × ℝ => Heasy α f g p.1 p.2)
      = fun p : ℝ × ℝ =>
          H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g p.1 p.2
            - Hhard α f g p.1 p.2 := by
    funext p
    rfl
  rw [key]
  exact h1.sub h2

/-! ## The a.e. strong measurability statements -/

/-- Joint a.e. strong measurability of `Heasy α f g` for the product of the restricted
Lebesgue measures on `Iz` and `Iθ`. -/
theorem aesm_uncurry_Heasy (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (hg : Work.Spaces.SmoothNbhd g) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Heasy α f g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_Heasy_Qd α hf hg)

/-- At `z = 0` the whole integrand `Heasy` vanishes: both weights `Whz` and `Wm` are `0`
there (the radial weight `w` is `0` at the origin). -/
theorem Heasy_zero_z (α : ℝ) (f g : ℝ → ℝ → ℝ) (θ : ℝ) : Heasy α f g 0 θ = 0 := by
  simp [Heasy, Hhard, H4PairInt, Whz, Wm, Work.Spaces.w, Work.Spaces.Wt,
    Work.Spaces.wTheta]

/-- Angular slice a.e. strong measurability of `Heasy α f g`: for every `z ∈ Iz` the function
`θ ↦ Heasy α f g z θ` is a.e. strongly measurable on `Iθ`.  For `z > 0` this is the continuity
on the open square; for `z = 0` the slice vanishes identically. -/
theorem aesm_slice_Heasy (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (hg : Work.Spaces.SmoothNbhd g) :
    ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Heasy α f g z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
  · rw [← h]
    have hzero : (fun θ : ℝ => Heasy α f g 0 θ) = fun _ : ℝ => (0 : ℝ) :=
      funext fun θ => Heasy_zero_z α f g θ
    rw [hzero]
    exact aestronglyMeasurable_const
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
      (continuousOn_Heasy_Qd α hf hg) h

/-- A.e. strong measurability of the radial partial integral `z ↦ ∫_θ Heasy α f g z θ` on
`Iz`, obtained from `aesm_uncurry_Heasy` by Fubini. -/
theorem aesm_integral_Heasy (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (hg : Work.Spaces.SmoothNbhd g) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Heasy α f g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  MeasureTheory.AEStronglyMeasurable.integral_prod_right' (aesm_uncurry_Heasy α hf hg)

/-- Joint a.e. strong measurability of `|Heasy α f g|` (the absolute value of the easy part),
the version needed to apply Tonelli to the absolute value. -/
theorem aesm_uncurry_abs_Heasy (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (hg : Work.Spaces.SmoothNbhd g) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |Heasy α f g p.1 p.2|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  continuous_abs.comp_aestronglyMeasurable (aesm_uncurry_Heasy α hf hg)

/-- A.e. strong measurability of the radial partial integral of the absolute value,
`z ↦ ∫_θ |Heasy α f g z θ|` on `Iz`: this is the measurability half of `T2EasyInt`. -/
theorem aesm_integral_abs_Heasy (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (hg : Work.Spaces.SmoothNbhd g) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, |Heasy α f g z θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  MeasureTheory.AEStronglyMeasurable.integral_prod_right' (aesm_uncurry_abs_Heasy α hf hg)

end

end Work.FTS.H2
