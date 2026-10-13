/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# Slice calculus for `C²` functions on the open strip

`Work.FTS.EllSol.Trunc.window_mass_le` (the "window mass" estimate for the truncation of
`flat2DAgmon`) is proved from two ingredients:

* the per-angle slice estimate `window_slice_le` and
* the existence of an angle-independent "good slice" `exists_good_slice`.

Both are stated for a function `g` which is only `C²` on the **open** strip
`ℝ × (0,π/2)` (the hypotheses of `window_mass_le`), so `z`- and `θ`-slices of `g` and of its
first partials have to be produced from `ContDiffOn` on that strip.  This file collects that
elementary slice calculus, together with the angular weight `σ θ = sin(2θ)^{-η}` of the
zero-th slot.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.FTS.EllSol.slice_zero_slot_finite
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.Trunc

set_option autoImplicit false

/-! ## The strip and the angular weight -/

/-- The open strip `ℝ × (0,π/2)` on which the hypotheses of `window_mass_le` live. -/
def Strip : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- `g` is `C²` on the open strip `ℝ × (0,π/2)`. -/
def StripC2 (g : ℝ → ℝ → ℝ) : Prop := ContDiffOn ℝ 2 (Function.uncurry g) Strip

theorem isOpen_Strip : IsOpen Strip := isOpen_univ.prod isOpen_Ioo

/-- The angular weight `σ θ = sin(2θ)^{-η}` (`η = 99/100`) of the zero-th slot. -/
def Sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

theorem Sig_eq_sEta : Sig = Work.FTS.EllSol.sEta := rfl

theorem Sig_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Sig θ :=
  Work.FTS.EllSol.sEta_nonneg_of_mem_Iθ hθ

theorem Sig_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Sig θ :=
  Work.FTS.EllSol.sEta_pos_of_mem_Ioo hθ

theorem one_le_Sig_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ Sig θ :=
  Work.FTS.EllSol.one_le_sEta_of_mem_Ioo hθ

theorem Sig_integrableOn : IntegrableOn Sig Work.Spaces.Iθ :=
  Work.FTS.EllSol.sEta_integrableOn

/-! ## `z`-slices -/

/-- The `z`-slice of a `C²` function on the strip has derivative `pz g z θ`. -/
theorem hasDerivAt_zslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (z : ℝ) :
    HasDerivAt (fun z' => g z' θ) (Work.Spaces.pz g z θ) z := by
  have hmem : (z, θ) ∈ Strip := ⟨trivial, hθ⟩
  have hd : DifferentiableAt ℝ (Function.uncurry g) (z, θ) :=
    ((hg.differentiableOn (by norm_num)).differentiableAt (isOpen_Strip.mem_nhds hmem))
  have h1 : HasDerivAt (fun z' => Function.uncurry g (z', θ))
      ((fderiv ℝ (Function.uncurry g) (z, θ)) (1, 0)) z :=
    Work.Spaces.hasDerivAt_slice_fst hd.hasFDerivAt
  have h2 : (fderiv ℝ (Function.uncurry g) (z, θ)) (1, 0) = Work.Spaces.pz g z θ :=
    (Work.Spaces.pz_eq_fderiv hd).symm
  rw [h2] at h1
  simpa [Function.uncurry] using h1

/-- The `z`-slice of a `C²` function on the strip is `C²` on `ℝ`. -/
theorem contDiffOn_zslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : ContDiffOn ℝ 2 (fun z => g z θ) Set.univ := by
  have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) Set.univ Strip := fun _ _ => ⟨trivial, hθ⟩
  have h := hg.comp (contDiffOn_id.prodMk (contDiffOn_const (c := θ))) hmap
  simpa [Function.comp_def, Function.uncurry] using h

/-- The `z`-slice of a `C²` function on the strip is continuous. -/
theorem continuous_zslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Continuous (fun z => g z θ) :=
  continuousOn_univ.mp (contDiffOn_zslice hg hθ).continuousOn

/-- The `z`-slice of `pz g` is continuous. -/
theorem continuous_pz_zslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Continuous (fun z => Work.Spaces.pz g z θ) := by
  have hcd := contDiffOn_zslice hg hθ
  have h1 : ContinuousOn (derivWithin (fun z => g z θ) Set.univ) Set.univ :=
    hcd.continuousOn_derivWithin uniqueDiffOn_univ (by norm_num)
  rw [derivWithin_univ, continuousOn_univ] at h1
  have h2 : deriv (fun z => g z θ) = fun z => Work.Spaces.pz g z θ := by
    funext z
    exact (hasDerivAt_zslice hg hθ z).deriv
  rwa [← h2]

/-- The fundamental theorem of calculus for the `z`-slice: `∫_a^b ∂_z g(z,θ) dz = g b θ - g a θ`. -/
theorem integral_pz_eq_sub {g : ℝ → ℝ → ℝ} (hg : StripC2 g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) {a b : ℝ} :
    ∫ z in a..b, Work.Spaces.pz g z θ = g b θ - g a θ :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (E := ℝ)
    (f := fun z => g z θ) (f' := fun z => Work.Spaces.pz g z θ)
    (fun x _ => hasDerivAt_zslice hg hθ x)
    ((continuous_pz_zslice hg hθ).intervalIntegrable a b)

/-! ## `θ`-slices -/

/-- The `θ`-slice of a `C²` function on the strip is `C²` on `(0,π/2)`. -/
theorem contDiffOn_thslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) (t : ℝ) :
    ContDiffOn ℝ 2 (fun θ => g t θ) (Set.Ioo 0 (π / 2)) := by
  have hmap : Set.MapsTo (fun θ : ℝ => (t, θ)) (Set.Ioo 0 (π / 2)) Strip :=
    fun _ hθ => ⟨trivial, hθ⟩
  have h := hg.comp ((contDiffOn_const (c := t)).prodMk contDiffOn_id) hmap
  simpa [Function.comp_def, Function.uncurry] using h

/-- The `θ`-slice of a `C²` function on the strip has derivative `pth g t θ`. -/
theorem hasDerivAt_thslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (t : ℝ) :
    HasDerivAt (fun θ' => g t θ') (Work.Spaces.pth g t θ) θ := by
  have hmem : (t, θ) ∈ Strip := ⟨trivial, hθ⟩
  have hd : DifferentiableAt ℝ (Function.uncurry g) (t, θ) :=
    ((hg.differentiableOn (by norm_num)).differentiableAt (isOpen_Strip.mem_nhds hmem))
  have h1 : HasDerivAt (fun θ' => Function.uncurry g (t, θ'))
      ((fderiv ℝ (Function.uncurry g) (t, θ)) (0, 1)) θ :=
    Work.Spaces.hasDerivAt_slice_snd hd.hasFDerivAt
  have h2 : (fderiv ℝ (Function.uncurry g) (t, θ)) (0, 1) = Work.Spaces.pth g t θ :=
    (Work.Spaces.pth_eq_fderiv hd).symm
  rw [h2] at h1
  simpa [Function.uncurry] using h1

/-- The `θ`-slice of `pth g` is `C¹` on the strip. -/
theorem contDiffOn_uncurry_pth_two {g : ℝ → ℝ → ℝ} (hg : StripC2 g) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth g)) Strip := by
  have hfd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry g) p) Strip := by
    have h' := hg.fderivWithin (m := 1) isOpen_Strip.uniqueDiffOn (by norm_num)
    refine h'.congr (fun p hp => ?_)
    rw [fderivWithin_of_isOpen isOpen_Strip hp]
  have hcomp : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry g) p) (0, 1)) Strip :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  have hd : DifferentiableAt ℝ (Function.uncurry g) p :=
    (hg.differentiableOn (by norm_num)).differentiableAt (isOpen_Strip.mem_nhds hp)
  show Function.uncurry (Work.Spaces.pth g) p = (fderiv ℝ (Function.uncurry g) p) (0, 1)
  exact Work.Spaces.pth_eq_fderiv hd

/-- The `θ`-slice of `pth g` has derivative `pth (pth g) t θ`. -/
theorem hasDerivAt_pth_thslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (t : ℝ) :
    HasDerivAt (fun θ' => Work.Spaces.pth g t θ')
      (Work.Spaces.pth (Work.Spaces.pth g) t θ) θ := by
  have hmem : (t, θ) ∈ Strip := ⟨trivial, hθ⟩
  have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth g)) (t, θ) :=
    ((contDiffOn_uncurry_pth_two hg).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Strip.mem_nhds hmem)
  have h1 : HasDerivAt (fun θ' => Function.uncurry (Work.Spaces.pth g) (t, θ'))
      ((fderiv ℝ (Function.uncurry (Work.Spaces.pth g)) (t, θ)) (0, 1)) θ :=
    Work.Spaces.hasDerivAt_slice_snd hd.hasFDerivAt
  have h2 : Work.Spaces.pth (Work.Spaces.pth g) t θ
      = (fderiv ℝ (Function.uncurry (Work.Spaces.pth g)) (t, θ)) (0, 1) :=
    Work.Spaces.pth_eq_fderiv hd
  simpa [Function.uncurry, h2] using h1

/-- The `θ`-slice of `pth g` is continuous on `(0,π/2)`. -/
theorem continuousOn_pth_thslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) (t : ℝ) :
    ContinuousOn (fun θ => Work.Spaces.pth g t θ) (Set.Ioo 0 (π / 2)) := by
  have hmap : Set.MapsTo (fun θ : ℝ => (t, θ)) (Set.Ioo 0 (π / 2)) Strip :=
    fun _ hθ => ⟨trivial, hθ⟩
  have hcont : ContinuousOn (fun θ : ℝ => (t, θ)) (Set.Ioo 0 (π / 2)) :=
    continuousOn_const.prodMk continuousOn_id
  have h := (contDiffOn_uncurry_pth_two hg).continuousOn.comp hcont hmap
  simpa [Function.comp_def, Function.uncurry] using h

/-- The second `θ`-derivative of the slice is `pth (pth g)` (definitional). -/
theorem thslice_derivDeriv {g : ℝ → ℝ → ℝ} (t θ : ℝ) :
    deriv (deriv (fun θ' => g t θ')) θ = Work.Spaces.pth (Work.Spaces.pth g) t θ := rfl

end Work.FTS.EllSol.Trunc
