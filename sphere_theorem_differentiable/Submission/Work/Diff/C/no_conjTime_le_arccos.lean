import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.hess_dist_jacobi_shapeOp_mfderiv
import Submission.Work.Diff.C.JacobiLogDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

/-! ## Auxiliary lemmas for `no_conjTime_le_arccos`

The mathematical content of the target is the classical one-dimensional Sturm comparison: a
nonnegative function `f` on `(0,d)` with `f' ≥ 2 (cot t − ε₁ / sin t) f` cannot vanish at `d < π`
while being positive somewhere on `(0,d)`.  The comparison is proved here in the elementary form
`sturm_no_conj_aux` (with an integrating factor `t ↦ f t / sin²t · exp (C t)`), and is then applied
to `f t = ⟪J t, J t⟫` for the Jacobi field `J`, using the log-derivative identity
`Work.Diff.C.jml_hasDerivAt_inner_self` together with the bridge and shape hypotheses. -/

/-- Derivative of the integrating factor `t ↦ f t / (sin t)² · exp (C t)`:
`d/dt = exp (C t)/(sin t)² · (f' − 2 cot t · f + C f)`. -/
theorem psiExp_hasDerivAt {f f' : ℝ → ℝ} {C t : ℝ}
    (hder : HasDerivAt f (f' t) t) (hsin : Real.sin t ≠ 0) :
    HasDerivAt (fun s : ℝ => f s / (Real.sin s * Real.sin s) * Real.exp (C * s))
      (Real.exp (C * t) / (Real.sin t * Real.sin t)
        * (f' t - 2 * Real.cot t * f t + C * f t)) t := by
  have hsin2 := (Real.hasDerivAt_sin t).mul (Real.hasDerivAt_sin t)
  have hexp := (Real.hasDerivAt_exp (C * t)).comp t ((hasDerivAt_id t).const_mul C)
  have hdiv := hder.div hsin2 (mul_ne_zero hsin hsin)
  have hmul := hdiv.mul hexp
  refine hmul.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply]
  rw [Real.cot_eq_cos_div_sin]
  field_simp [hsin]
  ring_nf

/-- **Sturm comparison in the form needed for `no_conjTime_le_arccos`.**  Let `0 < s < d < π`,
`ε₁ ≥ 0` and let `f` be continuous on `[s,d]`, nonnegative on `(s,d)` and differentiable there with
`2 (cot t − ε₁ / sin t) f t ≤ f' t`.  Then `f` cannot satisfy both `f d = 0` and `f s > 0`.

Proof: with `M := min_{[s,d]} sin > 0` and `C := 2 ε₁ / M`, the function
`Ψ t = f t / sin²t · exp (C t)` has nonnegative derivative on `(s,d)`, hence is monotone on `[s,d]`;
but `Ψ d = 0 < Ψ s`. -/
theorem sturm_no_conj_aux {f f' : ℝ → ℝ} {ε₁ s d : ℝ}
    (hε₁ : 0 ≤ ε₁) (hs0 : 0 < s) (hsd : s < d) (hdπ : d < Real.pi)
    (hcont : ContinuousOn f (Set.Icc s d))
    (hnn : ∀ t ∈ Set.Ioo s d, 0 ≤ f t)
    (hder : ∀ t ∈ Set.Ioo s d, HasDerivAt f (f' t) t)
    (hineq : ∀ t ∈ Set.Ioo s d, 2 * (Real.cot t - ε₁ / Real.sin t) * f t ≤ f' t)
    (hfd : f d = 0) (hfs : 0 < f s) : False := by
  have hsinpos : ∀ t ∈ Set.Icc s d, 0 < Real.sin t := fun t ht =>
    Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hs0 ht.1) (lt_of_le_of_lt ht.2 hdπ)
  obtain ⟨c, hc, hcmin⟩ := isCompact_Icc.exists_isMinOn (f := Real.sin) (s := Set.Icc s d)
    ⟨s, ⟨le_refl s, le_of_lt hsd⟩⟩ Real.continuous_sin.continuousOn
  obtain ⟨M, hMpos, hMle⟩ : ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Set.Icc s d, M ≤ Real.sin t :=
    ⟨Real.sin c, hsinpos c hc, fun t ht => hcmin ht⟩
  set C : ℝ := 2 * ε₁ / M with hCdef
  have hCbound : ∀ t ∈ Set.Ioo s d, 2 * ε₁ / Real.sin t ≤ C := by
    intro t ht
    rw [hCdef]
    exact div_le_div_of_nonneg_left (by linarith) hMpos
      (hMle t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  set Ψ : ℝ → ℝ := fun t => f t / (Real.sin t * Real.sin t) * Real.exp (C * t) with hΨdef
  have hΨd : Ψ d = 0 := by
    simp [hΨdef, hfd]
  have hΨs : 0 < Ψ s := by
    rw [hΨdef]
    have hs : s ∈ Set.Icc s d := ⟨le_refl s, le_of_lt hsd⟩
    exact mul_pos (div_pos hfs (mul_pos (hsinpos s hs) (hsinpos s hs))) (Real.exp_pos _)
  have hcontΨ : ContinuousOn Ψ (Set.Icc s d) := by
    rw [hΨdef]
    refine ContinuousOn.mul ?_ ?_
    · exact hcont.div (Real.continuous_sin.continuousOn.mul Real.continuous_sin.continuousOn)
        (fun t ht => mul_ne_zero (ne_of_gt (hsinpos t ht)) (ne_of_gt (hsinpos t ht)))
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hdiffΨ : DifferentiableOn ℝ Ψ (interior (Set.Icc s d)) := by
    rw [hΨdef, interior_Icc]
    intro t ht
    exact ((psiExp_hasDerivAt (hder t ht)
      (ne_of_gt (hsinpos t ⟨le_of_lt ht.1, le_of_lt ht.2⟩))).differentiableAt).differentiableWithinAt
  have hderivΨ : ∀ t ∈ interior (Set.Icc s d), 0 ≤ deriv Ψ t := by
    rw [interior_Icc]
    intro t ht
    have htI : t ∈ Set.Icc s d := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hsin_ne : Real.sin t ≠ 0 := ne_of_gt (hsinpos t htI)
    rw [hΨdef, (psiExp_hasDerivAt (hder t ht) hsin_ne).deriv]
    have h1 := hineq t ht
    have h2 := hnn t ht
    have h3 := hCbound t ht
    have h4 : 0 ≤ f' t - 2 * (Real.cot t - ε₁ / Real.sin t) * f t := by linarith
    have h5 : 0 ≤ f t * (C - 2 * ε₁ / Real.sin t) := mul_nonneg h2 (by linarith)
    have h6 : 0 ≤ Real.exp (C * t) / (Real.sin t * Real.sin t) :=
      le_of_lt (div_pos (Real.exp_pos _) (mul_pos (hsinpos t htI) (hsinpos t htI)))
    have h7 : 0 ≤ f' t - 2 * Real.cot t * f t + C * f t := by
      have hsum : 0 ≤ (f' t - 2 * (Real.cot t - ε₁ / Real.sin t) * f t)
          + f t * (C - 2 * ε₁ / Real.sin t) := add_nonneg h4 h5
      have heq : (f' t - 2 * (Real.cot t - ε₁ / Real.sin t) * f t)
          + f t * (C - 2 * ε₁ / Real.sin t)
          = f' t - 2 * Real.cot t * f t + C * f t := by ring
      linarith [hsum, heq]
    exact mul_nonneg h6 h7
  have hmono : MonotoneOn Ψ (Set.Icc s d) :=
    monotoneOn_of_deriv_nonneg (convex_Icc s d) hcontΨ hdiffΨ hderivΨ
  have hle : Ψ s ≤ Ψ d :=
    hmono ⟨le_refl s, le_of_lt hsd⟩ ⟨le_of_lt hsd, le_refl d⟩ (le_of_lt hsd)
  linarith [hΨs, hΨd, hle]

open scoped Manifold ContDiff Bundle Topology in

/-- **No conjugate time at distance `≤ L < π` from a centre, given the two-sided shape-operator
bound.**  Along the unit-speed ray `γ t = GExp q (t • u)` (`‖u‖ = 1`), let `J` be a Jacobi field with
`J 0 = 0`, `J d = 0`, `0 < d ≤ L < π`, not identically zero on `(0,d)`, orthogonal to the radial
field `∇ (rdist q)`, and suppose the *bridge identity*
`⟪∇_{γ'} J (t), J t⟫ = rhess (rdist q) (γ t) (J t) (J t)` holds on `(0,d)` (this is supplied, for a
minimising ray, by `Work.Diff.C.hess_dist_jacobi_shapeOp_mfderiv`), together with the *lower*
shape-operator bound `rhess (rdist q) (γ t) (J t) (J t) ≥ (cot t - ε₁ / sin t) · ⟪J t, J t⟫`
(supplied by `Work.Diff.C.rhess_rdist_bound_of_hHess`).  Then `False`.

This is the classical Sturm comparison argument in the form in which it is used to exclude the
conjugate-point (tangential-merging) case of the cut locus at the level `fcos q = -1+c`:
`Work.Diff.C.jld_log_deriv_of_jacobi` gives `(½ log ⟪J,J⟫)' = ⟪∇_{γ'}J, J⟫ / ⟪J,J⟫`, the two
hypotheses bound it below by `cot t - ε₁/sin t` on `(0,t₀)` where `t₀` is the first zero of `J`, and
integrating this differential inequality from `t₀/2` to `t₀ - h` (where `sin ≥ sin (t₀/2) > 0`) gives
`‖J (t₀-h)‖ ≥ C > 0` for a constant `C` independent of `h`, contradicting `J t₀ = 0` as `h → 0`. -/
theorem no_conjTime_le_arccos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {ε₁ L : ℝ} (hε₁ : 0 ≤ ε₁) (hLπ : L < Real.pi)
    {q : M} {u : TangentSpace I q} (hu : ‖u‖ = 1) {d : ℝ} (hd0 : 0 < d) (hdL : d ≤ L)
    {J : (t : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))}
    (hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov
      (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) J t)
    (hJ0 : J 0 = 0) (hJd : J d = 0)
    (hne : ∃ s ∈ Set.Ioo (0 : ℝ) d, J s ≠ 0)
    (hperp : ∀ t ∈ Set.Ioo (0 : ℝ) d,
      Inner.inner ℝ (J t) (Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))) = 0)
    (hbridge : ∀ t ∈ Set.Ioo (0 : ℝ) d,
      Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t) (J t)
        = Work.Diff.C.rhess cov (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z)
            (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) (J t) (J t))
    (hshape : ∀ t ∈ Set.Ioo (0 : ℝ) d,
      (Real.cot t - ε₁ / Real.sin t) * Inner.inner ℝ (J t) (J t)
        ≤ Work.Diff.C.rhess cov (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z)
            (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) (J t) (J t)) :
    False := by
  have hu_ne : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    norm_num at hu
  set γ : ℝ → M := fun t : ℝ =>
    Submission.GlobalExp.GExp (cov := cov) hmet q (t • u) with hγdef
  have hγ : ContMDiff 𝓘(ℝ) I ∞ γ := by
    rw [hγdef]
    exact Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet q hu_ne
  have hvel : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0 := by
    intro t
    rw [hγdef]
    exact Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hu_ne t
  have hJac : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ J t := by
    intro t
    rw [hγdef]
    exact hJ t
  have hder : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Inner.inner ℝ (J s) (J s))
      (2 * Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t) (J t)) t :=
    fun t => jml_hasDerivAt_inner_self (I := I) (M := M) (cov := cov) hmet htor hγ hJac hvel t
  have hcont : Continuous (fun t : ℝ => Inner.inner ℝ (J t) (J t)) :=
    continuous_iff_continuousAt.mpr (fun t => (hder t).continuousAt)
  obtain ⟨s₀, hs₀, hs₀_ne⟩ := hne
  have hs₀0 : 0 < s₀ := hs₀.1
  have hs₀d : s₀ < d := hs₀.2
  have hdπ : d < Real.pi := lt_of_le_of_lt hdL hLπ
  refine sturm_no_conj_aux (f := fun t : ℝ => Inner.inner ℝ (J t) (J t))
    (f' := fun t : ℝ => 2 * Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t) (J t))
    hε₁ hs₀0 hs₀d hdπ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hcont.continuousOn
  · intro t ht
    rw [real_inner_self_eq_norm_sq]
    positivity
  · intro t ht
    exact hder t
  · intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) d := ⟨lt_trans hs₀0 ht.1, ht.2⟩
    have h1 := hshape t ht'
    rw [← hbridge t ht'] at h1
    linarith
  · rw [hJd, inner_zero_right]
  · rw [real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hs₀_ne) 2

end Work.Diff.C
