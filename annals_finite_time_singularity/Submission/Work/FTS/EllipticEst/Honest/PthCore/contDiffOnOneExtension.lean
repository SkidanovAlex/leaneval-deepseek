import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.Honest.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Extending a `C¹` function on `(0, π/2)` with vanishing boundary values to `[0, π/2]`

`Work.FTS.EllipticEst.Honest.PthCore.contDiffOnOneExtension`: if `f` is `C¹` on the open
interval `(0, π/2)`, has vanishing one-sided limits at the two endpoints, and the one-sided
limits of `deriv f` at the endpoints exist, then `f` has a `C¹` extension `g` to
`[0, π/2]` with `g 0 = g (π/2) = 0`, agreeing with `f` (together with its derivative) on
the open interval.

The extension used is the *piecewise linear* one:

`pthOneExt A B f x = if x ≤ 0 then A * x else if x < π/2 then f x else B * (x - π/2)`,

with `A`, `B` the one-sided limits of `deriv f`.  It is `C¹` on the open neighbourhood
`(-1, π/2 + 1)` of `[0, π/2]`; at the two junction points the derivative is computed by
l'Hôpital's rule (`HasDerivAt.lhopital_zero_nhdsGT/LT`), which is the formal substitute for
the mean value theorem here.
-/

namespace Work.FTS.EllipticEst.Honest.PthCore

open Filter Set
open scoped Topology

/-- The extension of `f` from `(0, π/2)` to `ℝ`: linear with slope `A` to the left of `0`,
`f` itself on `(0, π/2)`, and linear with slope `B` to the right of `π/2`. -/
noncomputable def pthOneExt (A B : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then A * x else if x < Real.pi / 2 then f x else B * (x - Real.pi / 2)

/-- Candidate for the derivative of `pthOneExt A B f`: the slope `A` on `(-∞, 0]`, `deriv f`
on `(0, π/2)` and the slope `B` on `[π/2, ∞)`. -/
noncomputable def pthOneExtDeriv (A B : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then A else if x < Real.pi / 2 then deriv f x else B

lemma hpi_half_pos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]

variable {A B : ℝ} {f : ℝ → ℝ}

lemma pthOneExt_of_nonpos {x : ℝ} (hx : x ≤ 0) : pthOneExt A B f x = A * x := by
  simp only [pthOneExt, hx, ↓reduceIte]

lemma pthOneExt_of_mem {x : ℝ} (hx : x ∈ Ioo 0 (Real.pi / 2)) :
    pthOneExt A B f x = f x := by
  simp only [pthOneExt, not_le.mpr hx.1, hx.2, ↓reduceIte]

lemma pthOneExt_of_ge {x : ℝ} (hx : Real.pi / 2 ≤ x) :
    pthOneExt A B f x = B * (x - Real.pi / 2) := by
  simp only [pthOneExt, not_le.mpr (lt_of_lt_of_le hpi_half_pos hx), not_lt.mpr hx, ↓reduceIte]

lemma pthOneExt_zero : pthOneExt A B f 0 = 0 := by simp [pthOneExt]

lemma pthOneExt_pi_half : pthOneExt A B f (Real.pi / 2) = 0 := by
  rw [pthOneExt_of_ge le_rfl]; ring

lemma pthOneExt_hasDerivAt_of_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt (pthOneExt A B f) A x := by
  have hev : pthOneExt A B f =ᶠ[𝓝 x] (fun y : ℝ => A * y) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact pthOneExt_of_nonpos hy.le
  simpa using ((hasDerivAt_id x).const_mul A).congr_of_eventuallyEq hev

lemma pthOneExt_hasDerivAt_of_pi_half_lt {x : ℝ} (hx : Real.pi / 2 < x) :
    HasDerivAt (pthOneExt A B f) B x := by
  have hev : pthOneExt A B f =ᶠ[𝓝 x] (fun y : ℝ => B * (y - Real.pi / 2)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact pthOneExt_of_ge hy.le
  have h1 : HasDerivAt (fun y : ℝ => y - Real.pi / 2) 1 x := (hasDerivAt_id' x).sub_const _
  simpa using (h1.const_mul B).congr_of_eventuallyEq hev

lemma pthOneExt_hasDerivAt_of_mem {x : ℝ} (hx : x ∈ Ioo 0 (Real.pi / 2))
    (hdf : DifferentiableAt ℝ f x) : HasDerivAt (pthOneExt A B f) (deriv f x) x := by
  have hev : pthOneExt A B f =ᶠ[𝓝 x] f := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact pthOneExt_of_mem hy
  exact (hdf.hasDerivAt).congr_of_eventuallyEq hev

/-- The extension is differentiable at `0`, with derivative the (one-sided) limit `A` of
`deriv f`; l'Hôpital's rule supplies the right derivative, the left one is linear. -/
lemma pthOneExt_hasDerivAt_zero (hdf : DifferentiableOn ℝ f (Ioo 0 (Real.pi / 2)))
    (h0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0)) (hA : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) (𝓝 A)) :
    HasDerivAt (pthOneExt A B f) A 0 := by
  have hmem : Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hpi_half_pos
  have hder : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt (pthOneExt A B f) (deriv f x) x := by
    filter_upwards [hmem] with x hx
    exact pthOneExt_hasDerivAt_of_mem hx (hdf.differentiableAt (Ioo_mem_nhds hx.1 hx.2))
  have hone : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt (fun y : ℝ => y) (1 : ℝ) x :=
    Eventually.of_forall fun x => hasDerivAt_id' x
  have hne : ∀ᶠ x in 𝓝[>] (0 : ℝ), (1 : ℝ) ≠ 0 := Eventually.of_forall fun _ => one_ne_zero
  have hfa : Tendsto (pthOneExt A B f) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    h0.congr' (by
      filter_upwards [hmem] with x hx
      exact (pthOneExt_of_mem hx).symm)
  have hga : Tendsto (fun y : ℝ => y) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id'.mpr nhdsWithin_le_nhds
  have hdiv : Tendsto (fun x => deriv f x / (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    simpa using hA
  have hlhop := HasDerivAt.lhopital_zero_nhdsGT hder hone hne hfa hga hdiv
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  refine ⟨?_, ?_⟩
  · have hev : (fun _ : ℝ => A) =ᶠ[𝓝[<] (0 : ℝ)] slope (pthOneExt A B f) 0 := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hAy : A * y / y = A := by
        rw [mul_comm A y, mul_div_cancel_left₀ _ (ne_of_lt hy)]
      rw [slope_def_field, pthOneExt_of_nonpos hy.le, pthOneExt_zero, sub_zero, sub_zero, hAy]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => A) (𝓝[<] (0 : ℝ)) (𝓝 A)).congr' hev
  · refine hlhop.congr' ?_
    filter_upwards with x
    rw [slope_def_field, pthOneExt_zero, sub_zero, sub_zero]

/-- The extension is differentiable at `π/2`, with derivative the (one-sided) limit `B` of
`deriv f`. -/
lemma pthOneExt_hasDerivAt_pi_half (hdf : DifferentiableOn ℝ f (Ioo 0 (Real.pi / 2)))
    (h1 : Tendsto f (𝓝[<] (Real.pi / 2)) (𝓝 0))
    (hB : Tendsto (deriv f) (𝓝[<] (Real.pi / 2)) (𝓝 B)) :
    HasDerivAt (pthOneExt A B f) B (Real.pi / 2) := by
  have hmem : Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2) := Ioo_mem_nhdsLT hpi_half_pos
  have hder : ∀ᶠ x in 𝓝[<] (Real.pi / 2), HasDerivAt (pthOneExt A B f) (deriv f x) x := by
    filter_upwards [hmem] with x hx
    exact pthOneExt_hasDerivAt_of_mem hx (hdf.differentiableAt (Ioo_mem_nhds hx.1 hx.2))
  have hone : ∀ᶠ x in 𝓝[<] (Real.pi / 2), HasDerivAt (fun y : ℝ => y - Real.pi / 2) (1 : ℝ) x :=
    Eventually.of_forall fun x => (hasDerivAt_id' x).sub_const _
  have hne : ∀ᶠ x in 𝓝[<] (Real.pi / 2), (1 : ℝ) ≠ 0 := Eventually.of_forall fun _ => one_ne_zero
  have hfa : Tendsto (pthOneExt A B f) (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
    h1.congr' (by filter_upwards [hmem] with x hx; exact (pthOneExt_of_mem hx).symm)
  have hga : Tendsto (fun y : ℝ => y - Real.pi / 2) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have h0' : Tendsto (fun y : ℝ => y) (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
      tendsto_id'.mpr nhdsWithin_le_nhds
    have hc : Tendsto (fun _ : ℝ => Real.pi / 2) (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
      tendsto_const_nhds
    simpa using h0'.sub hc
  have hdiv : Tendsto (fun x => deriv f x / (1 : ℝ)) (𝓝[<] (Real.pi / 2)) (𝓝 B) := by
    simpa using hB
  have hlhop := HasDerivAt.lhopital_zero_nhdsLT hder hone hne hfa hga hdiv
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  refine ⟨?_, ?_⟩
  · refine hlhop.congr' ?_
    filter_upwards with x
    rw [slope_def_field, pthOneExt_pi_half, sub_zero]
  · have hev : (fun _ : ℝ => B) =ᶠ[𝓝[>] (Real.pi / 2)] slope (pthOneExt A B f) (Real.pi / 2) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hBy : B * (y - Real.pi / 2) / (y - Real.pi / 2) = B := by
        rw [mul_comm B (y - Real.pi / 2), mul_div_cancel_left₀ _ (sub_ne_zero.mpr (ne_of_gt hy))]
      rw [slope_def_field, pthOneExt_of_ge hy.le, pthOneExt_pi_half, sub_zero, hBy]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => B) (𝓝[>] (Real.pi / 2)) (𝓝 B)).congr' hev

lemma pthOneExt_deriv_of_neg {x : ℝ} (hx : x < 0) : deriv (pthOneExt A B f) x = A :=
  (pthOneExt_hasDerivAt_of_neg hx).deriv

lemma pthOneExt_deriv_of_mem {x : ℝ} (hx : x ∈ Ioo 0 (Real.pi / 2))
    (hdf : DifferentiableAt ℝ f x) : deriv (pthOneExt A B f) x = deriv f x :=
  (pthOneExt_hasDerivAt_of_mem hx hdf).deriv

lemma pthOneExt_deriv_of_pi_half_lt {x : ℝ} (hx : Real.pi / 2 < x) :
    deriv (pthOneExt A B f) x = B := (pthOneExt_hasDerivAt_of_pi_half_lt hx).deriv

/-- On the neighbourhood `(-1, π/2 + 1)` of `[0, π/2]` the derivative of the extension is the
explicit candidate `pthOneExtDeriv`. -/
lemma pthOneExt_deriv_eqOn (hdf : DifferentiableOn ℝ f (Ioo 0 (Real.pi / 2)))
    (h0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0)) (h1 : Tendsto f (𝓝[<] (Real.pi / 2)) (𝓝 0))
    (hA : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) (𝓝 A)) (hB : Tendsto (deriv f) (𝓝[<] (Real.pi / 2)) (𝓝 B)) :
    EqOn (deriv (pthOneExt A B f)) (pthOneExtDeriv A B f) (Ioo (-1) (Real.pi / 2 + 1)) := by
  intro x _
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · rw [pthOneExt_deriv_of_neg hlt]
    simp only [pthOneExtDeriv, hlt.le, ↓reduceIte]
  · subst heq
    rw [(pthOneExt_hasDerivAt_zero hdf h0 hA).deriv]
    simp only [pthOneExtDeriv, le_refl, ↓reduceIte]
  · rcases lt_trichotomy x (Real.pi / 2) with h2 | h2 | h2
    · rw [pthOneExt_deriv_of_mem ⟨hgt, h2⟩ (hdf.differentiableAt (Ioo_mem_nhds hgt h2))]
      simp only [pthOneExtDeriv, not_le.mpr hgt, h2, ↓reduceIte]
    · subst h2
      rw [(pthOneExt_hasDerivAt_pi_half hdf h1 hB).deriv]
      simp only [pthOneExtDeriv, not_le.mpr hpi_half_pos, lt_irrefl (Real.pi / 2), ↓reduceIte]
    · rw [pthOneExt_deriv_of_pi_half_lt h2]
      simp only [pthOneExtDeriv, not_le.mpr (lt_trans hpi_half_pos h2), not_lt.mpr h2.le, ↓reduceIte]

/-- `pthOneExtDeriv A B f` is continuous on the neighbourhood `(-1, π/2 + 1)`. -/
lemma continuousOn_pthOneExtDeriv (hderiv : ContinuousOn (deriv f) (Ioo 0 (Real.pi / 2)))
    (hA : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hB : Tendsto (deriv f) (𝓝[<] (Real.pi / 2)) (𝓝 B)) :
    ContinuousOn (pthOneExtDeriv A B f) (Ioo (-1) (Real.pi / 2 + 1)) := by
  intro x _
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · have hval : pthOneExtDeriv A B f x = A := by
      simp only [pthOneExtDeriv, hlt.le, ↓reduceIte]
    have hev : (fun _ : ℝ => A) =ᶠ[𝓝 x] pthOneExtDeriv A B f := by
      filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
      have hy' : y ≤ 0 := hy.le
      simp only [pthOneExtDeriv, hy', ↓reduceIte]
    exact ((continuousAt_const : ContinuousAt (fun _ : ℝ => A) x).congr hev).continuousWithinAt
  · subst heq
    have hval : pthOneExtDeriv A B f 0 = A := by
      simp only [pthOneExtDeriv, le_refl, ↓reduceIte]
    have hcont : ContinuousAt (pthOneExtDeriv A B f) 0 := by
      rw [continuousAt_iff_continuous_left'_right']
      refine ⟨?_, ?_⟩
      · have hev : (fun _ : ℝ => A) =ᶠ[𝓝[<] (0 : ℝ)] pthOneExtDeriv A B f := by
          filter_upwards [self_mem_nhdsWithin] with y hy
          have hy' : y ≤ 0 := hy.le
          simp only [pthOneExtDeriv, hy', ↓reduceIte]
        have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => A) (𝓝[<] (0 : ℝ)) (𝓝 A)).congr' hev
        unfold ContinuousWithinAt
        rw [hval]
        exact h
      · have hev : (fun x => deriv f x) =ᶠ[𝓝[>] (0 : ℝ)] pthOneExtDeriv A B f := by
          filter_upwards [Ioo_mem_nhdsGT hpi_half_pos] with y hy
          simp only [pthOneExtDeriv, not_le.mpr hy.1, hy.2, ↓reduceIte]
        have h := hA.congr' hev
        unfold ContinuousWithinAt
        rw [hval]
        exact h
    exact hcont.continuousWithinAt
  · rcases lt_trichotomy x (Real.pi / 2) with h2 | h2 | h2
    · have hev : (fun x => deriv f x) =ᶠ[𝓝 x] pthOneExtDeriv A B f := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨hgt, h2⟩] with y hy
        simp only [pthOneExtDeriv, not_le.mpr hy.1, hy.2, ↓reduceIte]
      exact ((hderiv.continuousAt (Ioo_mem_nhds hgt h2)).congr hev).continuousWithinAt
    · subst h2
      have hval : pthOneExtDeriv A B f (Real.pi / 2) = B := by
        simp only [pthOneExtDeriv, not_le.mpr hpi_half_pos, lt_irrefl (Real.pi / 2), ↓reduceIte]
      have hcont : ContinuousAt (pthOneExtDeriv A B f) (Real.pi / 2) := by
        rw [continuousAt_iff_continuous_left'_right']
        refine ⟨?_, ?_⟩
        · have hev : (fun x => deriv f x) =ᶠ[𝓝[<] (Real.pi / 2)] pthOneExtDeriv A B f := by
            filter_upwards [Ioo_mem_nhdsLT hpi_half_pos] with y hy
            simp only [pthOneExtDeriv, not_le.mpr hy.1, hy.2, ↓reduceIte]
          have h := hB.congr' hev
          unfold ContinuousWithinAt
          rw [hval]
          exact h
        · have hev : (fun _ : ℝ => B) =ᶠ[𝓝[>] (Real.pi / 2)] pthOneExtDeriv A B f := by
            filter_upwards [self_mem_nhdsWithin] with y hy
            have hy' : Real.pi / 2 ≤ y := hy.le
            simp only [pthOneExtDeriv, not_le.mpr (lt_trans hpi_half_pos hy), not_lt.mpr hy',
              ↓reduceIte]
          have h :=
            (tendsto_const_nhds : Tendsto (fun _ : ℝ => B) (𝓝[>] (Real.pi / 2)) (𝓝 B)).congr' hev
          unfold ContinuousWithinAt
          rw [hval]
          exact h
      exact hcont.continuousWithinAt
    · have hval : pthOneExtDeriv A B f x = B := by
        simp only [pthOneExtDeriv, not_le.mpr (lt_trans hpi_half_pos h2), not_lt.mpr h2.le,
          ↓reduceIte]
      have hev : (fun _ : ℝ => B) =ᶠ[𝓝 x] pthOneExtDeriv A B f := by
        filter_upwards [isOpen_Ioi.mem_nhds h2] with y hy
        have hy' : Real.pi / 2 ≤ y := hy.le
        simp only [pthOneExtDeriv, not_le.mpr (lt_trans hpi_half_pos hy), not_lt.mpr hy',
          ↓reduceIte]
      exact ((continuousAt_const (y := B) : ContinuousAt (fun _ : ℝ => B) x).congr
        hev).continuousWithinAt

/-- `pthOneExt A B f` is differentiable on the neighbourhood `(-1, π/2 + 1)`. -/
lemma differentiableOn_pthOneExt (hdf : DifferentiableOn ℝ f (Ioo 0 (Real.pi / 2)))
    (h0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0)) (h1 : Tendsto f (𝓝[<] (Real.pi / 2)) (𝓝 0))
    (hA : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hB : Tendsto (deriv f) (𝓝[<] (Real.pi / 2)) (𝓝 B)) :
    DifferentiableOn ℝ (pthOneExt A B f) (Ioo (-1) (Real.pi / 2 + 1)) := by
  intro x _
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · exact (pthOneExt_hasDerivAt_of_neg hlt).differentiableAt.differentiableWithinAt
  · subst heq
    exact (pthOneExt_hasDerivAt_zero hdf h0 hA).differentiableAt.differentiableWithinAt
  · rcases lt_trichotomy x (Real.pi / 2) with h2 | h2 | h2
    · exact (pthOneExt_hasDerivAt_of_mem ⟨hgt, h2⟩
        (hdf.differentiableAt (Ioo_mem_nhds hgt h2))).differentiableAt.differentiableWithinAt
    · subst h2
      exact (pthOneExt_hasDerivAt_pi_half hdf h1 hB).differentiableAt.differentiableWithinAt
    · exact (pthOneExt_hasDerivAt_of_pi_half_lt h2).differentiableAt.differentiableWithinAt

theorem contDiffOnOneExtension {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) (h1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) (h0' : ∃ L : ℝ, Filter.Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) (h1' : ∃ L : ℝ, Filter.Tendsto (deriv f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L)) : ∃ g : ℝ → ℝ, ContDiffOn ℝ 1 g (Set.Icc 0 (Real.pi / 2)) ∧ g 0 = 0 ∧ g (Real.pi / 2) = 0 ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = f θ ∧ deriv g θ = deriv f θ) := by
  obtain ⟨L0, hL0⟩ := h0'
  obtain ⟨L1, hL1⟩ := h1'
  have hdf : DifferentiableOn ℝ f (Ioo 0 (Real.pi / 2)) := hf.differentiableOn (by norm_num)
  have hderiv : ContinuousOn (deriv f) (Ioo 0 (Real.pi / 2)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  refine ⟨pthOneExt L0 L1 f, ?_, pthOneExt_zero, pthOneExt_pi_half, ?_⟩
  · have hU : ContDiffOn ℝ 1 (pthOneExt L0 L1 f) (Ioo (-1) (Real.pi / 2 + 1)) := by
      rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
        contDiffOn_succ_iff_deriv_of_isOpen (n := 0) isOpen_Ioo]
      refine ⟨differentiableOn_pthOneExt hdf h0 h1 hL0 hL1, fun h => by simp at h, ?_⟩
      rw [contDiffOn_zero]
      exact (continuousOn_pthOneExtDeriv hderiv hL0 hL1).congr
        (pthOneExt_deriv_eqOn hdf h0 h1 hL0 hL1)
    exact hU.mono fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro θ hθ
    refine ⟨pthOneExt_of_mem hθ, ?_⟩
    have hev : pthOneExt L0 L1 f =ᶠ[𝓝 θ] f := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
      exact pthOneExt_of_mem hy
    exact (hev.symm.deriv_eq).symm

end Work.FTS.EllipticEst.Honest.PthCore
