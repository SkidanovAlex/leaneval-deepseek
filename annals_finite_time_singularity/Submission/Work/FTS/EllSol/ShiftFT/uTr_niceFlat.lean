import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.EllSol.ShiftFT.uTr_niceFlat`

`uTr N b u = phiTr N · Gc N b u` is the truncated ("nice", i.e. uniformly compactly supported in
`t`) approximant of the shifted construction of `ShiftFT/ShiftPrimDefs.lean`.  The content of the
target theorem is that for `2 ≤ N` this approximant is again a `NiceFlat` datum, i.e. jointly `C²`
on the half-strip, with the two endpoint values `0` and uniformly compact support in `t`.

Everything is elementary except the `C²`-regularity of the variable lower endpoint primitive
`(t,θ) ↦ ∫ s in t..(2N), exp (-(b*s)) * deriv (chi N) s * u s θ`, which is the content of the
`ParamIntSelf` namespace below (a self-contained proof by two-level differentiation under the
integral sign; see also the sibling modules
`Submission/Work/FTS/EllSol/ShiftFT/contDiffOn_integral_variableLower.lean` and
`contDiffOn_intervalIntegral_param_two.lean` for the same statement required of the fleet).
-/

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## `C²`-regularity of parametric interval integrals

A self-contained proof (no import of the sibling delegated lemmas needed) that a jointly `C²` family
`K` has a `C²` parametric interval integral, both for fixed endpoints and for a variable lower
endpoint.  The route is the two-level induction on the order of differentiability:

* `contDiffOn_fderiv_slice_param'` — the slice derivative `(t,x) ↦ ∂₂K(t,x)` of a jointly `C^{n+1}`
  family is jointly `C^n`;
* `continuousOn_fderiv_slice_param'` — that slice derivative is continuous for `C¹` families;
* `continuousOn_intervalIntegral_param'` — dominated convergence for the parametric interval
  integral (general codomain);
* `hasFDerivAt_intervalIntegral_param'` — differentiation under the integral sign, from Mathlib's
  `hasFDerivAt_integral_of_dominated_of_fderiv_le''` and compactness of the tube;
* `contDiffOn_intervalIntegral_param_one'` — the `C¹` statement;
* `contDiffOn_intervalIntegral_param_two'` — the `C²` statement (with `E := X →L[ℝ] ℝ` for the
  derivative family);
* `contDiffOn_integral_variableLower'` — the variable lower endpoint version, from
  `∫ s in t..c = ∫ s in 0..c - ∫ s in 0..t` and the substitution `∫ s in 0..t = t ∫ v in 0..1, …(t*v)`. -/

namespace ParamIntSelf

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The partial derivative in the second variable of a jointly `C¹` family is the full Fréchet
derivative composed with `inr`. -/
theorem hasFDerivAt_slice_param' {K : ℝ → X → E} {u : Set ℝ} {s : Set X}
    (hu : IsOpen u) (hs : IsOpen s)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s))
    {t : ℝ} {x : X} (ht : t ∈ u) (hx : x ∈ s) :
    HasFDerivAt (fun y => K t y)
      ((fderiv ℝ (fun p : ℝ × X => K p.1 p.2) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ X)) x := by
  have hcd : ContDiffAt ℝ 1 (fun p : ℝ × X => K p.1 p.2) (t, x) :=
    (hK (t, x) ⟨ht, hx⟩).contDiffAt ((hu.prod hs).mem_nhds ⟨ht, hx⟩)
  have hfd : HasFDerivAt (fun p : ℝ × X => K p.1 p.2)
      (fderiv ℝ (fun p : ℝ × X => K p.1 p.2) (t, x)) (t, x) :=
    hcd.differentiableAt_one.hasFDerivAt
  have hpair : HasFDerivAt (fun y : X => (t, y)) (ContinuousLinearMap.inr ℝ ℝ X) x := by
    have h : HasFDerivAt (fun y : X => ContinuousLinearMap.inr ℝ ℝ X y)
        (ContinuousLinearMap.inr ℝ ℝ X) x :=
      ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inr ℝ ℝ X)
    have h' : HasFDerivAt (fun y : X => (t, (0 : X)) + ContinuousLinearMap.inr ℝ ℝ X y)
        (ContinuousLinearMap.inr ℝ ℝ X) x := h.const_add (t, (0 : X))
    simpa using h'
  simpa only [Function.comp_def] using hfd.comp x hpair

/-- The family `(t,x) ↦ ∂₂K(t,x)` is jointly `C^n` when `K` is jointly `C^{n+1}`. -/
theorem contDiffOn_fderiv_slice_param' {K : ℝ → X → E} {u : Set ℝ} {s : Set X}
    (hu : IsOpen u) (hs : IsOpen s) (n : ℕ)
    (hK : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ENat)
      (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContDiffOn ℝ (n : WithTop ENat)
      (fun p : ℝ × X => fderiv ℝ (fun y => K p.1 y) p.2) (u ×ˢ s) := by
  have hK1 : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s) :=
    hK.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have h1 : ContDiffOn ℝ (n : WithTop ENat)
      (fderiv ℝ (fun p : ℝ × X => K p.1 p.2)) (u ×ˢ s) :=
    hK.fderiv_of_isOpen (hu.prod hs) (by rw [Nat.cast_add, Nat.cast_one])
  have h2 : ContDiffOn ℝ (n : WithTop ENat)
      (fun p : ℝ × X => ((ContinuousLinearMap.compL ℝ X (ℝ × X) E).flip
        (ContinuousLinearMap.inr ℝ ℝ X)) (fderiv ℝ (fun p : ℝ × X => K p.1 p.2) p)) (u ×ˢ s) :=
    (((ContinuousLinearMap.compL ℝ X (ℝ × X) E).flip
      (ContinuousLinearMap.inr ℝ ℝ X))).contDiff.comp_contDiffOn h1
  exact h2.congr fun p hp => (hasFDerivAt_slice_param' hu hs hK1 hp.1 hp.2).fderiv

/-- The slice derivative of a jointly `C¹` family is continuous on the product of the open sets. -/
theorem continuousOn_fderiv_slice_param' {K : ℝ → X → E} {u : Set ℝ} {s : Set X}
    (hu : IsOpen u) (hs : IsOpen s)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContinuousOn (fun p : ℝ × X => fderiv ℝ (fun y => K p.1 y) p.2) (u ×ˢ s) := by
  have h1 : ContinuousOn (fun p : ℝ × X => fderiv ℝ (fun p : ℝ × X => K p.1 p.2) p) (u ×ˢ s) :=
    hK.continuousOn_fderiv_of_isOpen (hu.prod hs) le_rfl
  have h2 : Continuous fun L : (ℝ × X) →L[ℝ] E => L.comp (ContinuousLinearMap.inr ℝ ℝ X) :=
    (((ContinuousLinearMap.compL ℝ X (ℝ × X) E).flip
      (ContinuousLinearMap.inr ℝ ℝ X)) : ((ℝ × X) →L[ℝ] E) →L[ℝ] (X →L[ℝ] E)).continuous
  refine (h2.continuousOn.comp h1 (fun p _ => Set.mem_univ _)).congr fun p hp => ?_
  exact (hasFDerivAt_slice_param' hu hs hK hp.1 hp.2).fderiv

/-- **Continuity of a parametric interval integral** (general codomain). -/
theorem continuousOn_intervalIntegral_param' [ProperSpace X]
    {K : ℝ → X → E} {s : Set X} {u : Set ℝ} {a b : ℝ}
    (hs : IsOpen s) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ u)
    (hK : ContinuousOn (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContinuousOn (fun x => ∫ t in a..b, K t x) s := by
  have hIoc : Set.uIoc a b ⊆ Set.Icc a b := fun t ht => by
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hsubIoc : Set.uIoc a b ⊆ u := fun t ht => hsub (hIoc ht)
  intro x₀ hx₀
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  have hρ : 0 < δ / 2 := by positivity
  have hsubρ : Metric.closedBall x₀ (δ / 2) ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith)).trans hδs
  have hcont : ContinuousOn (fun p : ℝ × X => K p.1 p.2)
      (Set.Icc a b ×ˢ Metric.closedBall x₀ (δ / 2)) := hK.mono (Set.prod_mono hsub hsubρ)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall x₀ (δ / 2))).exists_bound_of_continuousOn hcont
  have hslice : ∀ x ∈ s, ContinuousOn (fun t : ℝ => K t x) (Set.Icc a b) := by
    intro x hx
    exact hK.comp (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨hsub ht, hx⟩)
  refine intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => C) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact ((hslice x hx).mono hIoc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x₀ hρ)] with x hx
    refine Eventually.of_forall fun t ht => ?_
    exact hC (t, x) ⟨hIoc ht, Metric.ball_subset_closedBall hx⟩
  · refine Eventually.of_forall fun t ht => ?_
    have htu : t ∈ u := hsubIoc ht
    have ht' : (t, x₀) ∈ u ×ˢ s := ⟨htu, hx₀⟩
    exact (hK.continuousWithinAt ht').comp
      (continuousWithinAt_const.prodMk continuousWithinAt_id) (fun x hx => ⟨htu, hx⟩)

/-- **Differentiation under the integral sign**, general codomain `E`, fixed endpoints. -/
theorem hasFDerivAt_intervalIntegral_param' [ProperSpace X]
    {K : ℝ → X → E} {u : Set ℝ} {s : Set X} {a b : ℝ}
    (hs : IsOpen s) (hu : IsOpen u) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ u)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) {x₀ : X} (hx₀ : x₀ ∈ s) :
    HasFDerivAt (fun x => ∫ t in a..b, K t x) (∫ t in a..b, fderiv ℝ (fun y => K t y) x₀) x₀ := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  have hε2 : 0 < ε / 2 := by positivity
  have hdie : Metric.closedBall x₀ (ε / 2) ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεs
  have hcont : ContinuousOn (fun p : ℝ × X => fderiv ℝ (fun y => K p.1 y) p.2)
      (Set.Icc a b ×ˢ Metric.closedBall x₀ (ε / 2)) :=
    (continuousOn_fderiv_slice_param' hu hs hK).mono (Set.prod_mono hsub hdie)
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall x₀ (ε / 2))).exists_bound_of_continuousOn hcont
  have hsubIoc : Set.uIoc a b ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hab]; exact Set.Ioc_subset_Icc_self
  have hslice (x : X) (hx : x ∈ s) : ContinuousOn (fun t : ℝ => K t x) (Set.Icc a b) :=
    hK.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨hsub ht, hx⟩)
  have hslice' : ContinuousOn (fun t : ℝ => fderiv ℝ (fun y => K t y) x₀) (Set.Icc a b) :=
    (continuousOn_fderiv_slice_param' hu hs hK).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨hsub ht, hx₀⟩)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume) (x₀ := x₀)
    (s := Metric.ball x₀ (ε / 2) ∩ s)
    (F := fun x t => K t x) (F' := fun x t => fderiv ℝ (fun y => K t y) x) (bound := fun _ => M)
    ?_ ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact inter_mem (Metric.ball_mem_nhds x₀ hε2) (hs.mem_nhds hx₀)
  · filter_upwards [hs.mem_nhds hx₀] with x hx
    exact ((hslice x hx).mono hsubIoc).aestronglyMeasurable measurableSet_uIoc
  · exact (hslice x₀ hx₀).intervalIntegrable_of_Icc hab
  · exact (hslice'.mono hsubIoc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    intro x hx
    exact hM (t, x) ⟨hsubIoc ht, Metric.ball_subset_closedBall hx.1⟩
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    intro x hx
    have h := hasFDerivAt_slice_param' hu hs hK (hsub (hsubIoc ht)) hx.2
    simpa only [h.fderiv] using h

/-- **`C¹` parametric interval integral**, general codomain `E`, fixed endpoints. -/
theorem contDiffOn_intervalIntegral_param_one' [ProperSpace X]
    {K : ℝ → X → E} {u : Set ℝ} {s : Set X} {a b : ℝ}
    (hu : IsOpen u) (hs : IsOpen s) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ u)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContDiffOn ℝ 1 (fun x => ∫ t in a..b, K t x) s := by
  have hderiv : ContinuousOn (fun x => ∫ t in a..b, fderiv ℝ (fun y => K t y) x) s :=
    continuousOn_intervalIntegral_param' hs hab hsub (continuousOn_fderiv_slice_param' hu hs hK)
  refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (s := s)
    (f := fun x => ∫ t in a..b, K t x) (n := (0 : WithTop ENat)) hs.uniqueDiffOn).2 ⟨?_, ?_⟩
  · intro h
    exact absurd h (by simp)
  · refine ⟨fun x => ∫ t in a..b, fderiv ℝ (fun y => K t y) x, (contDiffOn_zero).2 hderiv, ?_⟩
    intro x hx
    exact (hasFDerivAt_intervalIntegral_param' hs hu hab hsub hK hx).hasFDerivWithinAt

/-- **`C²` parametric interval integral**, fixed endpoints. -/
theorem contDiffOn_intervalIntegral_param_two' [ProperSpace X]
    {K : ℝ → X → ℝ} {u : Set ℝ} {s : Set X} {a b : ℝ}
    (hu : IsOpen u) (hs : IsOpen s) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ u)
    (hK : ContDiffOn ℝ 2 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContDiffOn ℝ 2 (fun x => ∫ t in a..b, K t x) s := by
  have hK1 : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s) := hK.of_le (by norm_num)
  have hf' : ContDiffOn ℝ 1 (fun x => ∫ t in a..b, fderiv ℝ (fun y => K t y) x) s :=
    contDiffOn_intervalIntegral_param_one' (E := X →L[ℝ] ℝ) hu hs hab hsub
      (contDiffOn_fderiv_slice_param' hu hs 1 hK)
  refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (s := s)
    (f := fun x => ∫ t in a..b, K t x) (n := (1 : WithTop ENat)) hs.uniqueDiffOn).2 ⟨?_, ?_⟩
  · intro h
    exact absurd h (by simp)
  · refine ⟨fun x => ∫ t in a..b, fderiv ℝ (fun y => K t y) x, hf', ?_⟩
    intro x hx
    exact (hasFDerivAt_intervalIntegral_param' hs hu hab hsub hK1 hx).hasFDerivWithinAt

/-- The slice `s ↦ F s θ` is continuous when `F` is jointly `C²` on `univ ×ˢ V` and `θ ∈ V`. -/
theorem continuous_slice_of_contDiffOn' {F : ℝ → ℝ → ℝ} {V : Set ℝ}
    (hF : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) (Set.univ ×ˢ V))
    {θ : ℝ} (hθ : θ ∈ V) : Continuous (fun s : ℝ => F s θ) := by
  have hcont : ContinuousOn (fun s : ℝ => F s θ) Set.univ :=
    hF.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s _ => ⟨trivial, hθ⟩)
  exact continuousOn_univ.mp hcont

/-- **The variable lower endpoint primitive of a jointly `C²` family is `C²`.** -/
theorem contDiffOn_integral_variableLower' (F : ℝ → ℝ → ℝ) {V : Set ℝ} (hV : IsOpen V) (c : ℝ)
    (hF : ContDiffOn ℝ 2 (Function.uncurry F) (Set.univ ×ˢ V)) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ∫ s in p.1..c, F s p.2) (Set.univ ×ˢ V) := by
  have hF' : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) (Set.univ ×ˢ V) := hF
  -- the `θ`-only piece
  have hA : ContDiffOn ℝ 2 (fun θ : ℝ => ∫ s in (0 : ℝ)..c, F s θ) V := by
    rcases le_or_gt (0 : ℝ) c with hc | hc
    · exact contDiffOn_intervalIntegral_param_two' (X := ℝ) (K := fun s θ => F s θ)
        (u := Set.univ) (s := V) (a := 0) (b := c) isOpen_univ hV hc (fun _ _ => trivial) hF'
    · have h2 := contDiffOn_intervalIntegral_param_two' (X := ℝ) (K := fun s θ => F s θ)
        (u := Set.univ) (s := V) (a := c) (b := 0) isOpen_univ hV (le_of_lt hc)
        (fun _ _ => trivial) hF'
      have heq : (fun θ : ℝ => ∫ s in (0 : ℝ)..c, F s θ) = fun θ => -∫ s in c..0, F s θ := by
        funext θ; rw [intervalIntegral.integral_symm]
      rw [heq]
      exact h2.neg
  -- the rescaled piece
  have hB : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ∫ v in (0 : ℝ)..1, F (p.1 * v) p.2)
      (Set.univ ×ˢ V) := by
    have hK : ContDiffOn ℝ 2 (fun q : ℝ × (ℝ × ℝ) => F (q.2.1 * q.1) q.2.2)
        (Set.univ ×ˢ (Set.univ ×ˢ V)) := by
      have hφ : ContDiffOn ℝ 2 (fun q : ℝ × (ℝ × ℝ) => (q.2.1 * q.1, q.2.2))
          (Set.univ ×ˢ (Set.univ ×ˢ V)) := by fun_prop
      exact hF'.comp hφ (fun q hq => ⟨trivial, hq.2.2⟩)
    exact contDiffOn_intervalIntegral_param_two' (X := ℝ × ℝ) (K := fun v p => F (p.1 * v) p.2)
      (u := Set.univ) (s := Set.univ ×ˢ V) (a := 0) (b := 1) isOpen_univ
      (isOpen_univ.prod hV) (by norm_num) (fun _ _ => trivial) hK
  have hAs : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ∫ s in (0 : ℝ)..c, F s p.2)
      (Set.univ ×ˢ V) :=
    hA.comp (contDiffOn_snd (s := Set.univ ×ˢ V)) (fun p hp => hp.2)
  refine (hAs.sub (contDiffOn_fst (s := Set.univ ×ˢ V) |>.mul hB)).congr fun p hp => ?_
  obtain ⟨t, θ⟩ := p
  have hslice : Continuous (fun s : ℝ => F s θ) := continuous_slice_of_contDiffOn' hF' hp.2
  have hsub : (∫ s in (0 : ℝ)..t, F s θ) = t * ∫ v in (0 : ℝ)..1, F (t * v) θ := by
    have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun v : ℝ => F v θ) t
    simpa [smul_eq_mul] using h.symm
  have hsplit : (∫ s in t..c, F s θ) = (∫ s in (0 : ℝ)..c, F s θ) - ∫ s in (0 : ℝ)..t, F s θ := by
    have h := intervalIntegral.integral_interval_sub_left (f := fun s : ℝ => F s θ)
      (hslice.intervalIntegrable (μ := volume) (0 : ℝ) c)
      (hslice.intervalIntegrable (μ := volume) (0 : ℝ) t)
    linarith [h]
  rw [hsplit, hsub]

end ParamIntSelf

/-! ## Auxiliary: `C^n`-regularity of `p ↦ g p.1` on a strip -/

private lemma contDiffOn_fst_comp {g : ℝ → ℝ} {n : WithTop ENat} (hg : ContDiff ℝ n g)
    (V : Set ℝ) : ContDiffOn ℝ n (fun p : ℝ × ℝ => g p.1) (Set.univ ×ˢ V) :=
  (hg.comp_contDiffOn contDiff_fst.contDiffOn).mono (Set.subset_univ _)

/-! ## The target -/

theorem uTr_niceFlat (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 2 ≤ N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (h1 : ∀ t : ℝ, u t (Real.pi / 2) = 0) :
    Work.FTS.EllSol.FlatFT.NiceFlat (Work.FTS.EllSol.ShiftFT.uTr N b u) := by
  have hV : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have huf : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ContDiffOn ℝ 2 (fun p : ℝ × ℝ => phiTr N p.1 * Gc N b u p.1 p.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
    have hphi : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => phiTr N p.1)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_fst_comp (phiTr_contDiff 2 N) _
    have hchi : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Trunc.chi N p.1)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_fst_comp (Trunc.chi_contDiff 2 N) _
    have hdchi : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => deriv (Trunc.chi N) p.1)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_fst_comp ((Trunc.chi_contDiff 3 N).deriv') _
    have hexp1 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.exp (-(b * p.1)))
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_fst_comp (((contDiff_const.mul contDiff_id).neg).exp) _
    have hexp2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.exp (b * p.1))
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_fst_comp ((contDiff_const.mul contDiff_id).exp) _
    have hH : ContDiffOn ℝ 2
        (Function.uncurry (fun s θ => Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ))
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      show ContDiffOn ℝ 2
        (fun p : ℝ × ℝ => Real.exp (-(b * p.1)) * deriv (Trunc.chi N) p.1 * u p.1 p.2) _
      exact (hexp1.mul hdchi).mul huf
    have hInt : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        ∫ s in p.1..(2 * N), Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s p.2)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ParamIntSelf.contDiffOn_integral_variableLower'
        (fun s θ => Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ) hV (2 * N) hH
    have hGc : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Gc N b u p.1 p.2)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hchi.mul huf).add (hexp2.mul hInt)
    exact hphi.mul hGc
  · intro t
    show phiTr N t * Gc N b u t 0 = 0
    have hz : Gc N b u t 0 = 0 := by
      show Trunc.chi N t * u t 0
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s 0 = 0
      simp [h0]
    rw [hz, mul_zero]
  · intro t
    show phiTr N t * Gc N b u t (Real.pi / 2) = 0
    have hz : Gc N b u t (Real.pi / 2) = 0 := by
      show Trunc.chi N t * u t (Real.pi / 2)
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s (Real.pi / 2) = 0
      simp [h1]
    rw [hz, mul_zero]
  · refine ⟨8192 * N, fun t θ ht => ?_⟩
    have hz : phiTr N t = 0 := by
      rw [phiTr_eq_chi]
      exact Trunc.chi_eq_zero (N := 4096 * N) (by linarith) (by linarith)
    show phiTr N t * Gc N b u t θ = 0
    rw [hz, zero_mul]

end

end Work.FTS.EllSol.ShiftFT
