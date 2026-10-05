import Mathlib

/-!
# Smoothness of a parametric interval integral

If `(s, x) ↦ f s x` is jointly `C^∞`, then `x ↦ ∫ s in a..b, f s x` is `C^∞`.

The proof is the classical induction: a parametric interval integral of a jointly `C^n` family is
`C^n`.  The inductive step is differentiation under the integral sign
(`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`): the derivative of
`x ↦ ∫ s in a..b, f s x` is `x ↦ ∫ s in a..b, ∂₂f (s, x)`, where `∂₂f` is the partial derivative
of `f` in the second variable.  The domination bound — the crucial input of the differentiation
lemma — is a *local uniform* bound on the continuous family `(s, x) ↦ ∂₂f (s, x)`, obtained from
compactness of the interval `[a, b]` together with continuity at `(s, x₀)`
(`exists_local_bound` below).

The induction is carried out for a codomain `E` whose universe is at least that of the parameter
space `X`, so that the space `X →L[ℝ] E` of derivatives stays in the same universe as `E`; this
is the reason for the hypothesis `E : Type (max u w)` in `paramIntegral_contDiff_aux`.  The
statement in arbitrary universes is then obtained by lifting `E` through `ULift`
(`paramIntegral_contDiff_ulift`).

The order `((⊤ : ℕ∞) : WithTop ℕ∞)` is the order `∞` of the `ContDiff` scope, i.e. `C^∞`.
-/

namespace Work.RPB.B2

open MeasureTheory Set Filter
open scoped Interval Topology ContDiff

universe u v w

/-! ### A local uniform bound for a jointly continuous family -/

/-- A jointly continuous family `(t, x) ↦ g t x : ℝ → X → F`, restricted to `t ∈ uIoc a b`, is
uniformly bounded near any `x₀ : X`.  This is the domination input for differentiating a
parametric integral.  Compactness of the interval supplies the uniformity in `t`. -/
private lemma exists_local_bound {X : Type u} [NormedAddCommGroup X] {F : Type*}
    [NormedAddCommGroup F] {g : ℝ → X → F}
    (hg : Continuous (fun z : ℝ × X => g z.1 z.2)) (x₀ : X) (a b : ℝ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ t ∈ Set.uIoc a b, ∀ x : X, dist x x₀ < δ → ‖g t x‖ ≤ C := by
  -- Near each `t` the family is bounded, uniformly for `t` close to `t` and `x` close to `x₀`.
  have hpt : ∀ u : ℝ, ∃ d C : ℝ, 0 < d ∧
      ∀ t : ℝ, dist t u < d → ∀ x : X, dist x x₀ < d → ‖g t x‖ ≤ C := by
    intro u
    have hcont : ContinuousAt (fun z : ℝ × X => ‖g z.1 z.2‖) (u, x₀) := hg.norm.continuousAt
    rcases Metric.continuousAt_iff.1 hcont 1 zero_lt_one with ⟨r, rpos, hr⟩
    refine ⟨r, ‖g u x₀‖ + 1, rpos, fun t ht x hx => ?_⟩
    have hd : dist (t, x) (u, x₀) < r := by
      rw [Prod.dist_eq]; exact max_lt ht hx
    have h1 := hr hd
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).2
    linarith
  choose d C hdpos hdC using hpt
  -- Compactness of `uIcc a b` turns the pointwise statement into a uniform one.
  have hcover : Set.uIcc a b ⊆ ⋃ u, Metric.ball u (d u) :=
    fun u _ => Set.mem_iUnion.mpr ⟨u, Metric.mem_ball_self (hdpos u)⟩
  obtain ⟨t, ht⟩ := isCompact_uIcc.elim_finite_subcover (fun u : ℝ => Metric.ball u (d u))
      (fun u => Metric.isOpen_ball) hcover
  have htne : t.Nonempty := by
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp (ht (left_mem_uIcc (a := a) (b := b)))
    obtain ⟨hv', -⟩ := Set.mem_iUnion.mp hv
    exact ⟨v, hv'⟩
  obtain ⟨δ, _, hδmin⟩ := t.exists_min_image d htne
  obtain ⟨c, _, hcmax⟩ := t.exists_max_image C htne
  refine ⟨d δ, hdpos δ, C c, fun t' ht' x hx => ?_⟩
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (ht (Set.uIoc_subset_uIcc ht'))
  obtain ⟨hst, hsv⟩ := Set.mem_iUnion.mp hs
  exact (hdC s t' (Metric.mem_ball.mp hsv) x (lt_of_lt_of_le hx (hδmin s hst))).trans
    (hcmax s hst)

/-! ### The induction -/

/-- **Auxiliary induction.**  If `(s, x) ↦ f s x` is jointly `C^k` then `x ↦ ∫ s in a..b, f s x`
is `C^k`.  Here the codomain `E` lives in a universe at least as large as that of `X`; this keeps
the space `X →L[ℝ] E` of derivatives in the same universe, so that the induction hypothesis is
applicable to the differentiated integrand. -/
private theorem paramIntegral_contDiff_aux {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type (max u w)} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (k : ℕ∞) (f : ℝ → X → E) (a b : ℝ)
    (hf : ContDiff ℝ (k : WithTop ℕ∞) (fun z : ℝ × X => f z.1 z.2)) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun x : X => ∫ s in a..b, f s x) := by
  induction k using ENat.nat_induction generalizing E f with
  | zero =>
      change ContDiff ℝ (0 : WithTop ℕ∞) (fun z : ℝ × X => f z.1 z.2) at hf
      change ContDiff ℝ (0 : WithTop ℕ∞) (fun x : X => ∫ s in a..b, f s x)
      rw [contDiff_zero] at hf ⊢
      -- `hf : Continuous (fun z : ℝ × X => f z.1 z.2)`; rewrite the goal as a parametric
      -- integral in the standard (parameter first) form.
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun x s => f s x) (hf.comp continuous_swap) a b
  | succ n ih =>
      push_cast at hf ⊢
      rw [contDiff_succ_iff_hasFDerivAt]
      let T : ((ℝ × X) →L[ℝ] E) →L[ℝ] (X →L[ℝ] E) :=
        ContinuousLinearMap.precomp E (ContinuousLinearMap.inr ℝ ℝ X)
      let f' : ℝ → X → (X →L[ℝ] E) :=
        fun s x => (fderiv ℝ (fun z : ℝ × X => f z.1 z.2) (s, x)).comp
          (ContinuousLinearMap.inr ℝ ℝ X)
      refine ⟨fun x => ∫ s in a..b, f' s x, ?_, ?_⟩
      · -- the derivative family is `C^n`, by the induction hypothesis
        apply ih (E := X →L[ℝ] E)
        have hfd : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞)
            (fderiv ℝ (fun z : ℝ × X => f z.1 z.2)) :=
          hf.fderiv_right (m := (n : ℕ∞)) le_rfl
        have hcomp : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞)
            (fun z : ℝ × X => T (fderiv ℝ (fun z : ℝ × X => f z.1 z.2) z)) :=
          T.contDiff.comp hfd
        exact hcomp
      · -- differentiation under the integral sign
        intro x₀
        have hGdiff : Differentiable ℝ (fun z : ℝ × X => f z.1 z.2) := by
          have hone : (1 : WithTop ℕ∞) ≤ (((n : ℕ∞)) : WithTop ℕ∞) + 1 := by
            push_cast; norm_num
          exact (hf.of_le hone).differentiable_one
        have hfdcont : Continuous (fderiv ℝ (fun z : ℝ × X => f z.1 z.2)) := by
          have hfd : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞)
              (fderiv ℝ (fun z : ℝ × X => f z.1 z.2)) :=
            hf.fderiv_right (m := (n : ℕ∞)) le_rfl
          exact hfd.continuous
        have hf'cont : Continuous (fun z : ℝ × X => f' z.1 z.2) := T.continuous.comp hfdcont
        obtain ⟨δ, hδpos, C, hC⟩ := exists_local_bound (g := fun s x => f' s x) hf'cont x₀ a b
        refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
          (μ := volume) (F := fun x s => f s x) (F' := fun x s => f' s x)
          (s := Metric.ball x₀ δ) (bound := fun _ => C)
          (Metric.ball_mem_nhds x₀ hδpos) ?_ ?_ ?_ ?_ ?_ ?_
        · exact Filter.Eventually.of_forall (fun x =>
            (hf.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
        · exact (hf.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
        · exact (hf'cont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
        · exact Filter.Eventually.of_forall (fun t ht x hx =>
            hC t ht x (Metric.mem_ball.mp hx))
        · exact intervalIntegrable_const
        · exact Filter.Eventually.of_forall (fun t _ht x _hx =>
            ((hGdiff (t, x)).hasFDerivAt).comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x))
  | top ih =>
      rw [contDiff_infty] at hf ⊢
      intro m
      exact ih m f (hf m)

/-! ### Arbitrary universes, via `ULift` -/

/-- The statement of `paramIntegral_contDiff_inf` for `E` and `X` in arbitrary (possibly
different) universes, obtained from `paramIntegral_contDiff_aux` by lifting the codomain `E` into
the common universe. -/
private theorem paramIntegral_contDiff_ulift {E : Type v} {X : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] (f : ℝ → X → E) (a b : ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × X => f z.1 z.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : X => ∫ s in a..b, f s x) := by
  -- `ULift.up` and `ULift.down` are `C^∞` linear isometries.
  have hup : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : E => (ULift.up y : ULift.{max u v} E)) :=
    (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := E)).symm.contDiff
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × X => (ULift.up (f z.1 z.2) : ULift.{max u v} E)) := hup.comp hf
  have hmain : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : X => ∫ s in a..b, (ULift.up (f s x) : ULift.{max u v} E)) :=
    paramIntegral_contDiff_aux (k := (⊤ : ℕ∞))
      (f := fun s x => (ULift.up (f s x) : ULift.{max u v} E)) a b hg
  -- `ULift.down` commutes with the interval integral.
  have hfun : (fun x : X => ∫ s in a..b, f s x)
      = fun x : X => ULift.down (∫ s in a..b, (ULift.up (f s x) : ULift.{max u v} E)) := by
    funext x
    have hint : IntervalIntegrable
        (fun s : ℝ => (ULift.up (f s x) : ULift.{max u v} E)) volume a b :=
      ((ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := E)).symm.continuous.comp
        (hf.continuous.comp (continuous_id.prodMk continuous_const))).intervalIntegrable a b
    exact ContinuousLinearMap.intervalIntegral_comp_comm (μ := volume)
      (L := (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := E) : ULift.{max u v} E →L[ℝ] E)) hint
  rw [hfun]
  exact (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := E)).contDiff.comp hmain

/-! ### The target statement -/

theorem paramIntegral_contDiff_inf {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup X] [NormedSpace ℝ X] (f : ℝ → X → E) (a b : ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × X => f z.1 z.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : X => ∫ s in a..b, f s x) := by
  exact paramIntegral_contDiff_ulift f a b hf

end Work.RPB.B2
