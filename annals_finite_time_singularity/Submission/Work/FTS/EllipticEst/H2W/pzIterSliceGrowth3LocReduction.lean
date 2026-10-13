import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.FTS.EllipticEst.H2W.SliceB.lzeroGrowthQuantL1
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W/pzIterSliceGrowth3LocReduction` — the reduction of the locally uniform slice growth to a
source-mass bound

Target of the node `Work.FTS.EllipticEst.H2W.pzIterSliceGrowth3Loc`: for a datum
`WeakPos2 α F Ψ` (`0 < α ≤ 1/4`) and for almost every `z₀ > 0` there is `ε ∈ (0, z₀)` and a
*single* constant `C ≥ 0` with

  `|∂_z^j Ψ(z,θ)| ≤ C·(θ⁻¹ + (π/2-θ)⁻¹)`  for all `j ≤ 3`, all `z ∈ (z₀-ε, z₀+ε)`,
  all `θ ∈ (0, π/2)`.

This file proves the **reduction**: the target follows from the *locally uniform* bound on the
pole-weighted `L¹` **mass of the source of each of the four slices** together with the same
quantity's local boundedness at the reference angle `π/4` (`SliceSourceMassBound` below).

## What is genuinely new here

The sibling node `H2W/pzIterPoleBoundUpTo4` proves the *almost everywhere in `z`* version of the
same conclusion (for `m ≤ 4`) by extracting, for each `z` separately, a constant from the
one-variable theorem `WeakPureAux.lzeroSlicePoleBound`, whose conclusion is an `∃ C`.  That
extraction is *not* uniform in `z`: the constant of the one-variable theorem is a function of the
slice's source mass and of the slice's data at `π/4`, and the theorem does not record the
dependence.  For the *local* (uniform in `z`) form one needs the quantitative version

> `SliceB.lzeroGrowthQuantL1` — `|u θ| ≤ C·(K u + |u(π/4)| + |u'(π/4)|)·(θ⁻¹ + (π/2-θ)⁻¹)` with a
> *universal* `C` and `K u := ∫_{Iθ} sinθcos²θ·|Lzero1 u|`,

which this file consumes.  With it the reduction is mechanical:

* the slice `θ ↦ ∂_z^m Ψ(z,·)` is `C^∞` on `(0,π/2)` for every `z > 0` (the class is `C^∞` on the
  open quadrant), so the quantitative theorem applies to it;
* the source-mass term is bounded uniformly on the neighbourhood by the hypothesis;
* the *data* term `|∂_z^mΨ(z,π/4)| + |∂_θ∂_z^mΨ(z,π/4)|` is *continuous in `z`*, hence bounded on
  the compact interval `[z₀-ε, z₀+ε]` — this is what makes the constant uniform in `z`
  (`exists_sliceData_bound_single`), and it uses only the `C^∞` clause of the class.

## The remaining input

`SliceSourceMassBound Ψ` is *not* a consequence of `WeakPos2` by any argument available in the
tree: the source of the `m`-th slice is
`∂_z^m F + α²z²∂_z^{m+2}Ψ + (2α²m + α(5+α))z∂_z^{m+1}Ψ + (α²m(m-1) + α(5+α)m)∂_z^mΨ`
(see `H2W/pzIterPoleBoundUpTo4`), so its mass involves the slices at levels `m+1`, `m+2` and, at
the top level `m = 3`, the honesty of `∂_z³F`, which the class does not provide.  See
`NOTES_pzIterSliceGrowth3Loc_reduction.md` beside this file (the regress has no base case; the
statement is the chapter's level-`0` bottleneck in its locally uniform form).
-/

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## The `θ`-slices of the iterated `z`-derivatives are `C^∞` on the open angular interval -/

/-- The `θ`-slices `θ ↦ ∂_z^m Ψ(z,θ)` of a datum which is `C^∞` on the open quadrant are `C^∞`
on `(0, π/2)` at every `z > 0`, at every order. -/
theorem contDiffOn_slice_pzIter {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) (m : ℕ) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.pzIter m Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hQ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hcur := (hQ.pzIter m).curry_θ hz
  intro n
  exact (contDiffOn_iff_forall_nat_le.mp hcur) n le_top

/-! ## The data term at `θ = π/4` is locally bounded in `z` -/

/-- **The data term `|∂_z^mΨ(z,π/4)| + |∂_θ∂_z^mΨ(z,π/4)|` is bounded on a compact interval of
`z`'s, for `C^∞` data.**  Both summands are `ContinuousOn` (they are `z`-slices at the interior
angle `π/4`), so the bound is `IsCompact.exists_bound_of_continuousOn`. -/
theorem exists_sliceData_bound_single {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Set.Icc a b,
      |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
        + |Work.Spaces.pth (Work.Spaces.pzIter m Ψ) z (Real.pi / 4)| ≤ M := by
  have h4 : (Real.pi / 4 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hc1 : ContinuousOn (fun z : ℝ => Work.Spaces.pzIter m Ψ z (Real.pi / 4))
      (Set.Icc a b) := ((hsm.pzIter m).curry_z h4).continuousOn.mono hsub
  have hc2 : ContinuousOn (fun z : ℝ => Work.Spaces.pth (Work.Spaces.pzIter m Ψ) z (Real.pi / 4))
      (Set.Icc a b) := ((hsm.pzIter m).pth.curry_z h4).continuousOn.mono hsub
  have hc : ContinuousOn (fun z : ℝ => |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
      + |Work.Spaces.pth (Work.Spaces.pzIter m Ψ) z (Real.pi / 4)|) (Set.Icc a b) :=
    hc1.abs.add hc2.abs
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hmem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hval : ∀ z ∈ Set.Icc a b, ‖|Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
      + |Work.Spaces.pth (Work.Spaces.pzIter m Ψ) z (Real.pi / 4)|‖
      = |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
      + |Work.Spaces.pth (Work.Spaces.pzIter m Ψ) z (Real.pi / 4)| := by
    intro z _
    exact Real.norm_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨M, ?_, fun z hz => ?_⟩
  · have h0 : (0 : ℝ) ≤ |Work.Spaces.pzIter m Ψ a (Real.pi / 4)|
        + |Work.Spaces.pth (Work.Spaces.pzIter m Ψ) a (Real.pi / 4)| := by positivity
    have := hM a hmem
    rw [hval a hmem] at this
    linarith
  · have := hM z hz
    rw [hval z hz] at this
    exact this

/-! ## The source-mass hypothesis -/

/-- **The locally uniform source-mass hypothesis.**  For a.e. centre `z₀ > 0` there is a
neighbourhood on which, with a *single* constant `C`, for each of the four slices `∂_z^mΨ`
(`m ≤ 3`) the `Lzero1`-source is `sinθcos²θ`-integrable with the *integrated* quantity
`∫_θ (sinθcos²θ·|Lzero1(∂_z^mΨ(z,·))| + |∂_z^mΨ(z,π/4)| + |∂_θ∂_z^mΨ(z,π/4)|)` bounded by `C`.

This is the locally uniform form of the source-honesty input of `H2W/pzIterPoleBoundUpTo4`, in
exactly the shape in which the quantitative one-variable theorem consumes it; it is *not* a
consequence of `WeakPos2` (see the module docstring). -/
def SliceSourceMassBound (Ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
    ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε), ∀ m : ℕ, m ≤ 3 →
        MeasureTheory.IntegrableOn
            (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 *
              |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
            Work.Spaces.Iθ
          ∧ (∫ θ in Work.Spaces.Iθ,
                (Real.sin θ * Real.cos θ ^ 2 *
                    |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|
                  + |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
                  + |deriv (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') (Real.pi / 4)|))
              ≤ C

/-! ## The reduction -/

/-- **The reduction of `pzIterSliceGrowth3Loc` to the source-mass bound.**  For a datum of the
weak class `WeakPos2 α F Ψ` and a locally uniform bound on the pole-weighted `L¹` mass of the
sources of the four slices `∂_z^mΨ` (`m ≤ 3`), the locally uniform pole bound follows.

The quantitative one-variable theorem (`SliceB.lzeroGrowthQuantL1`) gives, for every `z` and `m`,
`|∂_z^mΨ(z,θ)| ≤ C·(K_m(z) + d_m(z))·(θ⁻¹ + (π/2-θ)⁻¹)` with `K_m(z)` the source mass and
`d_m(z)` the data term at `π/4`; both are bounded uniformly on the neighbourhood — `K_m` by
hypothesis and `d_m` by `exists_sliceData_bound_single` (compactness of `[z₀-ε, z₀+ε]` and
continuity at the interior angle `π/4`). -/
theorem pzIterSliceGrowth3Loc_of_massBound {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) (hmass : SliceSourceMassBound Ψ) :
    ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
          ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.Spaces.pzIter j Ψ z θ| ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  obtain ⟨Cq, hCq, hquant⟩ := Work.FTS.EllipticEst.H2W.SliceB.lzeroGrowthQuantL1
  have hsm_raw : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.2.2.2.2.2.2.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm_raw
  filter_upwards [hmass, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z₀ hm hz₀
  obtain ⟨ε, hεpos, hεz, CM, hCM, hbound⟩ := hm
  -- the four data bounds on the closed interval `[z₀ - ε, z₀ + ε]`
  obtain ⟨M0, hM0, hbd0⟩ :=
    exists_sliceData_bound_single hsm (a := z₀ - ε) (b := z₀ + ε) (by linarith) (by linarith) 0
  obtain ⟨M1, hM1, hbd1⟩ :=
    exists_sliceData_bound_single hsm (a := z₀ - ε) (b := z₀ + ε) (by linarith) (by linarith) 1
  obtain ⟨M2, hM2, hbd2⟩ :=
    exists_sliceData_bound_single hsm (a := z₀ - ε) (b := z₀ + ε) (by linarith) (by linarith) 2
  obtain ⟨M3, hM3, hbd3⟩ :=
    exists_sliceData_bound_single hsm (a := z₀ - ε) (b := z₀ + ε) (by linarith) (by linarith) 3
  refine ⟨ε, hεpos, hεz, Cq * CM, by positivity, fun j hj z hz θ hθ => ?_⟩
  have hzpos : 0 < z := by linarith [hz.1, hεz]
  obtain ⟨hint, hK⟩ := hbound z hz j hj
  have hslice := hquant (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ')
    (contDiffOn_slice_pzIter hsm_raw hzpos j) hint θ hθ
  have hdata : |Work.Spaces.pzIter j Ψ z (Real.pi / 4)|
      + |deriv (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') (Real.pi / 4)|
      ≤ M0 + M1 + M2 + M3 := by
    have hzI : z ∈ Set.Icc (z₀ - ε) (z₀ + ε) := ⟨hz.1.le, hz.2.le⟩
    interval_cases j
    · exact le_trans (hbd0 z hzI) (by linarith)
    · exact le_trans (hbd1 z hzI) (by linarith)
    · exact le_trans (hbd2 z hzI) (by linarith)
    · exact le_trans (hbd3 z hzI) (by linarith)
  have hρ : 0 ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ :=
    add_nonneg (inv_nonneg.mpr hθ.1.le) (inv_nonneg.mpr (by linarith [hθ.2]))
  have hK' : (∫ θ in Work.Spaces.Iθ,
        (Real.sin θ * Real.cos θ ^ 2 *
            |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') θ|
          + |Work.Spaces.pzIter j Ψ z (Real.pi / 4)|
          + |deriv (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') (Real.pi / 4)|)) ≤ CM := hK
  calc |Work.Spaces.pzIter j Ψ z θ|
      ≤ (Cq * (∫ s in Work.Spaces.Iθ,
            (Real.sin s * Real.cos s ^ 2 *
                |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') s|
              + |Work.Spaces.pzIter j Ψ z (Real.pi / 4)|
              + |deriv (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') (Real.pi / 4)|)))
          * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := hslice
    _ ≤ (Cq * CM) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK' hCq.le) hρ
    _ = Cq * CM * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by ring

end

end Work.FTS.EllipticEst.H2W
