/-
Copyright: work module for the Elgindi finite-time singularity project.

# Measurability of the "easy" part of the `SpecialTransport` pairing

The three remainders `EZ`, `EM`, `EC` of the split `H4PairInt = EZ + EM + EC + HardF`
(`EasyId`) are pointwise bounded by `C·|∂_θ f|_{𝒲}·HkIntegrand α 4 g`, but to be able to
add their `θ`-integrals (`integral_add`) one needs their almost-everywhere strong
measurability.  This file provides it:

* the joint smoothness of the iterated operators `D_z^b`, `D_θ^a`, `D_z^b D_θ^a` for a
  `SmoothInt` function (`contDiffOn_uncurry_DzIter`, `…_mixed`);
* the transfer of almost-everywhere strong measurability from `(0,π/2)` to `Iθ`
  (`aestronglyMeasurable_of_restrict_of_null`, `aesm_slice_contDiffOn_Ioo`);
* the resulting measurability of the slices of `f`, of the `g`-blocks, and of `EZ`, `EM`,
  `EC`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.STEasyBnd
import Submission.Work.FTS.H2.EMBound
import Submission.Work.FTS.H2.ECBound
import Submission.Work.FTS.H2.HardIntegrable
import Submission.Work.FTS.H2.STHardBnd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Joint smoothness of the iterated operators for `SmoothInt` functions -/

theorem contDiffOn_uncurry_DzIter {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (b : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter b f)) V := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    have hpz := Work.Spaces.contDiffOn_uncurry_pz hV ih
    have hmul : ContDiffOn ℝ ⊤
        (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz (Work.Spaces.DzIter b f) p.1 p.2) V :=
      contDiffOn_fst.mul hpz
    have hfun : (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz (Work.Spaces.DzIter b f) p.1 p.2)
        = Function.uncurry (Work.Spaces.DzIter (b + 1) f) := rfl
    rwa [hfun] at hmul

theorem contDiffOn_uncurry_mixed {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (j i : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.mixed j i f)) V :=
  contDiffOn_uncurry_DzIter hV (contDiffOn_uncurry_DthIter hV h i) j

/-! ## Transfer of almost-everywhere measurability -/

/-- Almost-everywhere strong measurability is inherited from `(0,π/2)` to `Iθ` (the two
differ by the null set `{0,π/2}`). -/
theorem aestronglyMeasurable_of_restrict_of_null {u : ℝ → ℝ} {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hnull : volume (s \ t) = 0)
    (h : AEStronglyMeasurable u (volume.restrict t)) :
    AEStronglyMeasurable u (volume.restrict s) := by
  obtain ⟨g, hg, hfg⟩ := h
  refine ⟨g, hg, ?_⟩
  have h1 : ∀ᵐ x ∂(volume.restrict t), u x = g x := hfg.eventually
  rw [ae_restrict_iff' ht] at h1
  have h2 : ∀ᵐ x ∂volume, x ∉ s \ t := by
    rw [ae_iff]
    have hset : {x : ℝ | ¬ x ∉ s \ t} = s \ t := by ext x; simp
    rw [hset]; exact hnull
  have h3 : ∀ᵐ x ∂(volume.restrict s), u x = g x := by
    rw [ae_restrict_iff' hs]
    filter_upwards [h1, h2] with x hx1 hx2 hxs
    have hxt : x ∈ t := by
      by_contra hxt
      exact hx2 ⟨hxs, hxt⟩
    exact hx1 hxt
  exact h3

theorem volume_Icc_diff_Ioo : volume (Set.Icc (0 : ℝ) (π / 2) \ Set.Ioo 0 (π / 2)) = 0 := by
  have hsub : Set.Icc (0 : ℝ) (π / 2) \ Set.Ioo 0 (π / 2) ⊆ ({0} : Set ℝ) ∪ {π / 2} := by
    intro x hx
    rw [Set.mem_diff, Set.mem_Icc, Set.mem_Ioo] at hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_singleton_iff]
    by_cases h : x ≤ 0
    · left; linarith
    · right
      push_neg at h
      have hlt : ¬ (x < π / 2) := fun hlt => h3 ⟨h, hlt⟩
      linarith
  refine measure_mono_null hsub ?_
  rw [measure_union_null_iff]
  exact ⟨Real.volume_singleton, Real.volume_singleton⟩

/-- A function which is `C^∞` (in particular continuous) on the open interval `(0,π/2)` is
almost everywhere strongly measurable on `Iθ`. -/
theorem aesm_slice_contDiffOn_Ioo {u : ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable u (volume.restrict (Set.Ioo 0 (π / 2))) :=
    h.continuousOn.aestronglyMeasurable measurableSet_Ioo
  have h2 : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
  rw [h2]
  exact aestronglyMeasurable_of_restrict_of_null measurableSet_Icc measurableSet_Ioo
    volume_Icc_diff_Ioo h1

/-! ## Measurability of the individual blocks -/

/-- The `θ`-slice of a `SmoothNbhd` function is a.e. strongly measurable on `Iθ`. -/
theorem aesm_slice_of_smoothNbhd {G : ℝ → ℝ → ℝ} (hG : Work.Spaces.SmoothNbhd G)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ => G z θ) (volume.restrict Work.Spaces.Iθ) :=
  (continuousOn_slice_of_smoothNbhd hG hz).aestronglyMeasurable
    (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)

/-- The `θ`-slice of a `D_z`-iterate of a `SmoothInt` function. -/
theorem aesm_DzIter_slice {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothInt f) (b : ℕ) {z : ℝ}
    (hz : z ∈ Set.Ioi (-1)) :
    AEStronglyMeasurable (fun θ => Work.Spaces.DzIter b f z θ)
      (volume.restrict Work.Spaces.Iθ) :=
  aesm_slice_contDiffOn_Ioo
    (contDiffOn_thslice_of_uncurry isOpen_strp (contDiffOn_uncurry_DzIter isOpen_strp hsm.1 b)
      isOpen_Ioo (fun θ hθ => ⟨hz, hθ⟩))

/-- The `θ`-slice of a mixed derivative of a `SmoothInt` function. -/
theorem aesm_mixed_slice {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothInt f) (j i : ℕ) {z : ℝ}
    (hz : z ∈ Set.Ioi (-1)) :
    AEStronglyMeasurable (fun θ => Work.Spaces.mixed j i f z θ)
      (volume.restrict Work.Spaces.Iθ) :=
  aesm_slice_contDiffOn_Ioo
    (contDiffOn_thslice_of_uncurry isOpen_strp (contDiffOn_uncurry_mixed isOpen_strp hsm.1 j i)
      isOpen_Ioo (fun θ hθ => ⟨hz, hθ⟩))

/-- The `θ`-slice of `f` itself, under continuity on the closed quadrant. -/
theorem aesm_slice_of_continuousOn {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ => f z θ) (volume.restrict Work.Spaces.Iθ) := by
  have h1 : ContinuousOn (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ := by fun_prop
  have h2 := hcont.comp h1 (fun θ hθ => ⟨hz, hθ⟩)
  have h3 : ContinuousOn (fun θ : ℝ => f z θ) Work.Spaces.Iθ := by
    simpa [Function.comp_def, Function.uncurry] using h2
  exact h3.aestronglyMeasurable (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)

/-! ## Measurability of the slices of `EZ`, `EM`, `EC` -/

theorem aesm_sin_rpow (q : ℝ) :
    AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ q) (volume.restrict Work.Spaces.Iθ) :=
  ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const q).aestronglyMeasurable

theorem aesm_EZ_slice {f g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothInt f)
    (hg : Work.Spaces.SmoothNbhd g) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ => EZ f g z θ) (volume.restrict Work.Spaces.Iθ) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hzIoi : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  change AEStronglyMeasurable (fun θ : ℝ => (∑ m ∈ Finset.range 5,
      ∑ b ∈ Finset.range (m + 1),
      (if m = 4 ∧ b = 0 then (0 : ℝ) else (m.choose b : ℝ)) *
        (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (m - b) (Work.Spaces.pth g) z θ
          * Work.Spaces.DzIter m g z θ) * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) : ℝ)) (volume.restrict Work.Spaces.Iθ)
  refine Finset.aestronglyMeasurable_fun_sum (M := ℝ) (Finset.range 5) (fun m _ =>
    Finset.aestronglyMeasurable_fun_sum (M := ℝ) (Finset.range (m + 1)) (fun b _ => ?_))
  by_cases hcase : m = 4 ∧ b = 0
  · simp only [if_pos hcase]
    simp only [zero_mul]
    exact aestronglyMeasurable_const
  · simp only [if_neg hcase]
    have hA : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter b f z θ)
        (volume.restrict Work.Spaces.Iθ) := aesm_DzIter_slice hsm b hzIoi
    have hB : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter (m - b) (Work.Spaces.pth g) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      aesm_slice_of_smoothNbhd (Work.Spaces.smoothNbhd_DzIter (Work.Spaces.SmoothNbhd.pth hg)
        (m - b)) hz
    have hC : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter m g z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      aesm_slice_of_smoothNbhd (Work.Spaces.smoothNbhd_DzIter hg m) hz
    have hS := aesm_sin_rpow (-Work.Spaces.eta)
    exact (((aestronglyMeasurable_const.mul ((hA.mul hB).mul hC)).mul
      aestronglyMeasurable_const).mul hS)

theorem aesm_EM_slice {α : ℝ} {f g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothInt f)
    (hg : Work.Spaces.SmoothNbhd g) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ => EM α f g z θ) (volume.restrict Work.Spaces.Iθ) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hzIoi : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  change AEStronglyMeasurable (fun θ : ℝ => (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
      if 1 ≤ i ∧ i + j ≤ 4 then
        ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (if i + j = 4 ∧ a = 0 ∧ b = 0 then (0 : ℝ)
            else ((i.choose a : ℝ) * (j.choose b : ℝ))) *
            (Work.Spaces.mixed b a f z θ
              * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ
              * Work.Spaces.mixed j i g z θ) * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      else (0 : ℝ) : ℝ)) (volume.restrict Work.Spaces.Iθ)
  refine Finset.aestronglyMeasurable_fun_sum (M := ℝ) (Finset.range 5) (fun i _ =>
    Finset.aestronglyMeasurable_fun_sum (M := ℝ) (Finset.range 5) (fun j _ => ?_))
  by_cases hc : 1 ≤ i ∧ i + j ≤ 4
  · simp only [if_pos hc]
    refine Finset.aestronglyMeasurable_fun_sum (M := ℝ) (Finset.range (i + 1)) (fun a _ =>
      Finset.aestronglyMeasurable_fun_sum (M := ℝ) (Finset.range (j + 1)) (fun b _ => ?_))
    by_cases hc2 : i + j = 4 ∧ a = 0 ∧ b = 0
    · simp only [if_pos hc2]
      simp only [zero_mul]
      exact aestronglyMeasurable_const
    · simp only [if_neg hc2]
      have hA : AEStronglyMeasurable (fun θ => Work.Spaces.mixed b a f z θ)
          (volume.restrict Work.Spaces.Iθ) := aesm_mixed_slice hsm b a hzIoi
      have hB : AEStronglyMeasurable
          (fun θ => Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ)
          (volume.restrict Work.Spaces.Iθ) :=
        aesm_slice_of_smoothNbhd
          (Work.Spaces.smoothNbhd_mixed (Work.Spaces.SmoothNbhd.pth hg) (j - b) (i - a)) hz
      have hC : AEStronglyMeasurable (fun θ => Work.Spaces.mixed j i g z θ)
          (volume.restrict Work.Spaces.Iθ) :=
        aesm_slice_of_smoothNbhd (Work.Spaces.smoothNbhd_mixed hg j i) hz
      have hS := aesm_sin_rpow (-(Work.Spaces.gam α))
      exact (((aestronglyMeasurable_const.mul ((hA.mul hB).mul hC)).mul
        aestronglyMeasurable_const).mul hS)
  · simp only [if_neg hc]
    exact aestronglyMeasurable_const

theorem aesm_EC_slice {α : ℝ} {f g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hg : Work.Spaces.SmoothNbhd g) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ => EC α f g z θ) (volume.restrict Work.Spaces.Iθ) := by
  change AEStronglyMeasurable (fun θ : ℝ => (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
      if 1 ≤ i ∧ i + j = 4 then
        f z θ * ((Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
            - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ) * Work.Spaces.mixed j i g z θ)
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      else (0 : ℝ) : ℝ)) (volume.restrict Work.Spaces.Iθ)
  refine Finset.aestronglyMeasurable_fun_sum (M := ℝ) (Finset.range 5) (fun i _ =>
    Finset.aestronglyMeasurable_fun_sum (M := ℝ) (Finset.range 5) (fun j _ => ?_))
  by_cases hc : 1 ≤ i ∧ i + j = 4
  · simp only [if_pos hc]
    have hF : AEStronglyMeasurable (fun θ => f z θ) (volume.restrict Work.Spaces.Iθ) :=
      aesm_slice_of_continuousOn hcont hz
    have hA : AEStronglyMeasurable (fun θ => Work.Spaces.mixed j i (Work.Spaces.pth g) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      aesm_slice_of_smoothNbhd
        (Work.Spaces.smoothNbhd_mixed (Work.Spaces.SmoothNbhd.pth hg) j i) hz
    have hB : AEStronglyMeasurable (fun θ => Work.Spaces.pth (Work.Spaces.mixed j i g) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      aesm_slice_of_smoothNbhd (Work.Spaces.SmoothNbhd.pth
        (Work.Spaces.smoothNbhd_mixed hg j i)) hz
    have hC : AEStronglyMeasurable (fun θ => Work.Spaces.mixed j i g z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      aesm_slice_of_smoothNbhd (Work.Spaces.smoothNbhd_mixed hg j i) hz
    have hS := aesm_sin_rpow (-(Work.Spaces.gam α))
    exact (((hF.mul ((hA.sub hB).mul hC)).mul aestronglyMeasurable_const).mul hS)
  · simp only [if_neg hc]
    exact aestronglyMeasurable_const


/-! ## The pointwise bound on the easy part, and its integrability -/

/-- The sum of the three bounds `EZ_bound`, `EMBound`, `ECBound`. -/
theorem EasyBound {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hvt : Work.Spaces.VanishTheta f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hWl : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f))
    (hg : Work.Spaces.SmoothNbhd g) (hHk : Work.Spaces.HkMem α 4 g)
    {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |EZ f g z θ + EM α f g z θ + EC α f g z θ|
      ≤ 2000000000000000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  have h1 := EZ_bound hsm hcont hvt hα hα1 hWl hHk hz hθ
  have h2 := EMBound hsm hcont hvt hα hα1 hWl hg hHk hz hθ
  have h3 := ECBound hsm hcont hvt hα hα1 hWl hg hHk hz hθ
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := WlInf_nonneg hWl
  have hHkI : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hprod : (0 : ℝ) ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
      * Work.Spaces.HkIntegrand α 4 g z θ := mul_nonneg hWnn hHkI
  calc |EZ f g z θ + EM α f g z θ + EC α f g z θ|
      ≤ |EZ f g z θ + EM α f g z θ| + |EC α f g z θ| := abs_add_le _ _
    _ ≤ (|EZ f g z θ| + |EM α f g z θ|) + |EC α f g z θ| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (1500000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
            * Work.Spaces.HkIntegrand α 4 g z θ
          + 1000000000000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
            * Work.Spaces.HkIntegrand α 4 g z θ)
          + 4000000000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
            * Work.Spaces.HkIntegrand α 4 g z θ := by
        exact add_le_add (add_le_add h1 h2) h3
    _ ≤ 2000000000000000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
        * Work.Spaces.HkIntegrand α 4 g z θ := by nlinarith [hprod]

/-- Almost every `θ ∈ Iθ` lies in the open interval `(0,π/2)`. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  rw [ae_restrict_iff' hIθ, ae_iff]
  have hset : {a : ℝ | ¬(a ∈ Work.Spaces.Iθ → a ∈ Set.Ioo 0 (π / 2))}
      = Work.Spaces.Iθ \ Set.Ioo 0 (π / 2) := by
    ext a; simp only [Set.mem_setOf_eq, Set.mem_diff, not_imp]
  rw [hset, show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
  exact volume_Icc_diff_Ioo

/-- The easy part `EZ + EM + EC` is integrable on `Iθ`. -/
theorem integrableOn_easy {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hvt : Work.Spaces.VanishTheta f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hWl : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f))
    (hg : Work.Spaces.SmoothNbhd g) (hHk : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) :
    MeasureTheory.IntegrableOn
      (fun θ => EZ f g z θ + EM α f g z θ + EC α f g z θ) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := WlInf_nonneg hWl
  refine MeasureTheory.Integrable.mono'
    ((hHk.1 z hzI).const_mul (2000000000000000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)))
    (((aesm_EZ_slice hsm hg hzI).add (aesm_EM_slice hsm hg hzI)).add
      (aesm_EC_slice hsm hcont hg hzI)) ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  have hb := EasyBound hsm hcont hvt hα hα1 hWl hg hHk hz hθ
  have hc : (0 : ℝ) ≤ 2000000000000000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) :=
    mul_nonneg (by norm_num) hWnn
  have hHkI : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  rw [Real.norm_eq_abs]
  exact le_trans hb (le_of_eq (by ring))

end Work.FTS.H2
