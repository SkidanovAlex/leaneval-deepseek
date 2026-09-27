import Mathlib
import Submission.Work.Drive.Neutral.StripDiskAux
import Submission.Work.Drive.Neutral.dataChordAux
import Submission.Work.Drive.exists_contDiff_smul_factor

namespace Work.Drive.Neutral

open Manifold MeasureTheory Filter
open scoped Manifold ContDiff Topology

/-! ## Joint smoothness of the chord data on `{x ≠ 0}` -/

/-- The chord vector is `C^∞` in `(x, s)` away from `x = 0`.  The two local arguments
`(Complex.log x).im` and `(Complex.log (-x)).im + π` cover `ℂ \ {0}` (`slitPlane_or_neg`);
on each of the two charts the chord is the smooth expression of `dataChord_eq_exp`. -/
theorem contDiffOn_dataChord_of_ne (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => dataChord γ p.1 p.2)
      {p : ℂ × ℝ | p.1 ≠ 0} := by
  refine contDiffOn_of_locally_contDiffOn (fun p hp => ?_)
  rcases slitPlane_or_neg p.1 hp with hsp | hsp
  · refine ⟨Complex.slitPlane ×ˢ Set.univ, ?_, ⟨hsp, trivial⟩, ?_⟩
    · exact Complex.isOpen_slitPlane.prod isOpen_univ
    · exact (contDiffOn_dataChord_slit γ hγ).mono Set.inter_subset_right
  · refine ⟨{q : ℂ × ℝ | -q.1 ∈ Complex.slitPlane}, ?_, hsp, ?_⟩
    · exact Complex.isOpen_slitPlane.preimage (continuous_neg.comp continuous_fst)
    · exact (contDiffOn_dataChord_negSlit γ hγ).mono Set.inter_subset_right

/-- The chord midpoint is `C^∞` in `(x, s)` away from `x = 0`. -/
theorem contDiffOn_dataMid_of_ne (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => dataMid γ p.1 p.2)
      {p : ℂ × ℝ | p.1 ≠ 0} := by
  refine contDiffOn_of_locally_contDiffOn (fun p hp => ?_)
  rcases slitPlane_or_neg p.1 hp with hsp | hsp
  · refine ⟨Complex.slitPlane ×ˢ Set.univ, ?_, ⟨hsp, trivial⟩, ?_⟩
    · exact Complex.isOpen_slitPlane.prod isOpen_univ
    · exact (contDiffOn_dataMid_slit γ hγ).mono Set.inter_subset_right
  · refine ⟨{q : ℂ × ℝ | -q.1 ∈ Complex.slitPlane}, ?_, hsp, ?_⟩
    · exact Complex.isOpen_slitPlane.preimage (continuous_neg.comp continuous_fst)
    · exact (contDiffOn_dataMid_negSlit γ hγ).mono Set.inter_subset_right

lemma symmC_zero : symmC (0 : ℝ × ℝ) = 0 := by
  refine Complex.ext ?_ ?_ <;> simp [symmC]

/-! ## The local argument in the complex variable -/

/-- The continuous argument of `x` relative to a base point `x₀ ≠ 0`,
`θ x = arg x₀ + (log (x / x₀)).im`, is smooth on the chart `{x | x / x₀ ∈ slitPlane}`. -/
lemma contDiffOn_localArgC (x₀ : ℂ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℂ => Complex.arg x₀ + (Complex.log (x / x₀)).im)
      {x : ℂ | x / x₀ ∈ Complex.slitPlane} := by
  have hdiv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℂ => x / x₀)
      {x : ℂ | x / x₀ ∈ Complex.slitPlane} := (contDiff_id.div_const x₀).contDiffOn
  have hlog := hlog_slit.comp hdiv (fun x hx => hx)
  have him : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℂ => (Complex.log (x / x₀)).im)
      {x : ℂ | x / x₀ ∈ Complex.slitPlane} := by
    have h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z.im) Set.univ :=
      Complex.imCLM.contDiff.contDiffOn
    exact h.comp hlog (fun x hx => trivial)
  exact contDiffOn_const.add him

/-- **The chord in the local argument.**  For `x / x₀` in the slit plane the chord vector is the
smooth expression in the continuous argument `arg x₀ + (log (x / x₀)).im`. -/
lemma dataChord_eq_localArg (γ : Circle → ℝ × ℝ) (x₀ : ℂ) (hx₀ : x₀ ≠ 0)
    {x : ℂ} (hx : x / x₀ ∈ Complex.slitPlane) (s : ℝ) :
    dataChord γ x s = symmC (curve γ (Complex.arg x₀ + (Complex.log (x / x₀)).im + sClamp s)
      - curve γ (Complex.arg x₀ + (Complex.log (x / x₀)).im - sClamp s)) := by
  have hne : x / x₀ ≠ 0 := ne_zero_of_mem_slitPlane hx
  have hxne : x ≠ 0 := fun h => hne (by rw [h, zero_div])
  have hcirc : Circle.exp (Complex.arg x₀ + (Complex.log (x / x₀)).im) = toCirc x hxne := by
    have h1 : Circle.exp (Complex.arg x₀ + (Complex.log (x / x₀)).im)
        = toCirc x₀ hx₀ * toCirc (x / x₀) hne := by
      rw [Circle.exp_add, toCirc_eq_exp_arg x₀ hx₀, Complex.log_im,
        ← toCirc_eq_exp_arg (x / x₀) hne]
    rw [h1, ← toCirc_mul x₀ (x / x₀) hx₀ hne]
    refine Subtype.ext ?_
    rw [toCirc_coe, toCirc_coe, mul_div_cancel₀ x hx₀]
  refine dataChord_eq_exp γ x hxne ?_ s
  rw [hcirc, toCirc_coe]

/-! ## Hadamard's identity for the second variable -/

/-- The fundamental theorem of calculus along the second variable, in divided form. -/
lemma smul_integral_fderiv (G : ℂ × ℝ → ℂ) (x : ℂ) (s : ℝ)
    (hG : ∀ t : ℝ, HasFDerivAt G (fderiv ℝ G (x, t)) (x, t))
    (hc : Continuous fun u : ℝ => (fderiv ℝ G (x, u)) ((0 : ℂ), (1 : ℝ))) :
    s • (∫ u in (0 : ℝ)..1, (fderiv ℝ G (x, u * s)) ((0 : ℂ), (1 : ℝ)))
      = G (x, s) - G (x, 0) := by
  have hderiv : ∀ u : ℝ, HasDerivAt (G ∘ fun v : ℝ => ((x : ℂ), v * s))
      (s • (fderiv ℝ G (x, u * s)) ((0 : ℂ), (1 : ℝ))) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => ((x : ℂ), v * s)) ((0 : ℂ), s) u := by
      simpa using (hasDerivAt_const u x).prodMk ((hasDerivAt_id u).mul_const s)
    have h2 := (hG (u * s)).comp_hasDerivAt u h1
    have h3 : (fderiv ℝ G (x, u * s)) ((0 : ℂ), s)
        = s • (fderiv ℝ G (x, u * s)) ((0 : ℂ), (1 : ℝ)) := by
      conv_lhs => rw [show ((0 : ℂ), s) = s • ((0 : ℂ), (1 : ℝ)) by simp]
      rw [ContinuousLinearMap.map_smul]
    rw [h3] at h2
    exact h2
  have hint : IntervalIntegrable (fun u : ℝ => s • (fderiv ℝ G (x, u * s)) ((0 : ℂ), (1 : ℝ)))
      volume (0 : ℝ) 1 :=
    ((hc.comp (continuous_id.mul continuous_const)).const_smul s).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_smul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) hint]
  simp only [Function.comp_apply, one_mul, zero_mul]

/-- The same identity, symmetrised in `s`, for an odd `G (x, ·)`: the average of the divided
differences at `s` and `-s` is again the divided difference. -/
lemma smul_integral_fderiv_symm (G : ℂ × ℝ → ℂ) (x : ℂ) (s : ℝ)
    (hG : ∀ t : ℝ, HasFDerivAt G (fderiv ℝ G (x, t)) (x, t))
    (hc : Continuous fun u : ℝ => (fderiv ℝ G (x, u)) ((0 : ℂ), (1 : ℝ)))
    (h0 : G (x, 0) = 0) (hodd : ∀ t : ℝ, G (x, -t) = -G (x, t)) :
    s • (∫ u in (0 : ℝ)..1, (1 / 2 : ℝ) • ((fderiv ℝ G (x, u * s)) ((0 : ℂ), (1 : ℝ))
      + (fderiv ℝ G (x, -(u * s))) ((0 : ℂ), (1 : ℝ)))) = G (x, s) := by
  set A : ℝ → ℂ := fun u => (fderiv ℝ G (x, u * s)) ((0 : ℂ), (1 : ℝ)) with hA
  set B : ℝ → ℂ := fun u => (fderiv ℝ G (x, -(u * s))) ((0 : ℂ), (1 : ℝ)) with hB
  have hAcont : Continuous A := hc.comp (continuous_id.mul continuous_const)
  have hBcont : Continuous B := hc.comp ((continuous_id.mul continuous_const).neg)
  have hAint : IntervalIntegrable A volume (0 : ℝ) 1 := hAcont.intervalIntegrable 0 1
  have hBint : IntervalIntegrable B volume (0 : ℝ) 1 := hBcont.intervalIntegrable 0 1
  have hArec : s • (∫ u in (0 : ℝ)..1, A u) = G (x, s) - G (x, 0) :=
    smul_integral_fderiv G x s hG hc
  have hBrec : s • (∫ u in (0 : ℝ)..1, B u) = G (x, 0) - G (x, -s) := by
    have hderiv : ∀ u : ℝ, HasDerivAt (G ∘ fun v : ℝ => ((x : ℂ), v * (-s)))
        (-(s • B u)) u := by
      intro u
      have h1 : HasDerivAt (fun v : ℝ => ((x : ℂ), v * (-s))) ((0 : ℂ), -s) u := by
        have h2 : HasDerivAt (fun v : ℝ => v * (-s)) (-s) u := by
          simpa using (hasDerivAt_id u).mul_const (-s)
        exact (hasDerivAt_const u x).prodMk h2
      have h2 := (hG (u * (-s))).comp_hasDerivAt u h1
      have h3 : (fderiv ℝ G (x, u * (-s))) ((0 : ℂ), -s) = -(s • B u) := by
        conv_lhs => rw [show ((0 : ℂ), -s) = -(s • ((0 : ℂ), (1 : ℝ))) by simp,
          show u * (-s) = -(u * s) by ring]
        rw [map_neg, ContinuousLinearMap.map_smul]
      rw [h3] at h2
      exact h2
    have hint : IntervalIntegrable (fun u : ℝ => -(s • B u)) volume (0 : ℝ) 1 :=
      (hBcont.const_smul s).neg.intervalIntegrable 0 1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) hint
    simp only [Function.comp_apply, one_mul, zero_mul] at hFTC
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_smul] at hFTC
    have h' := congrArg Neg.neg hFTC
    rw [neg_neg, neg_sub] at h'
    exact h'
  calc s • (∫ u in (0 : ℝ)..1, (1 / 2 : ℝ) • (A u + B u))
      = s • ((1 / 2 : ℝ) • ((∫ u in (0 : ℝ)..1, A u) + (∫ u in (0 : ℝ)..1, B u))) := by
        rw [intervalIntegral.integral_smul, intervalIntegral.integral_add hAint hBint]
    _ = (1 / 2 : ℝ) • (s • ((∫ u in (0 : ℝ)..1, A u) + (∫ u in (0 : ℝ)..1, B u))) :=
        smul_comm s (1 / 2) _
    _ = (1 / 2 : ℝ) • (s • (∫ u in (0 : ℝ)..1, A u) + s • (∫ u in (0 : ℝ)..1, B u)) := by
        rw [smul_add]
    _ = (1 / 2 : ℝ) • ((G (x, s) - G (x, 0)) + (G (x, 0) - G (x, -s))) := by rw [hArec, hBrec]
    _ = (1 / 2 : ℝ) • (G (x, s) - G (x, -s)) := by
        rw [show (G (x, s) - G (x, 0)) + (G (x, 0) - G (x, -s)) = G (x, s) - G (x, -s) by ring]
    _ = (1 / 2 : ℝ) • (G (x, s) + G (x, s)) := by rw [hodd s, sub_neg_eq_add]
    _ = G (x, s) := by rw [← two_smul ℝ (G (x, s)), smul_smul]; norm_num

/-- The parametric `fderiv`-integral of a globally smooth function is globally smooth. -/
lemma contDiff_integral_fderiv_symm (G : ℂ × ℝ → ℂ)
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ =>
      ∫ u in (0 : ℝ)..1, (1 / 2 : ℝ) • ((fderiv ℝ G (p.1, u * p.2)) ((0 : ℂ), (1 : ℝ))
        + (fderiv ℝ G (p.1, -(u * p.2))) ((0 : ℂ), (1 : ℝ)))) := by
  refine parametric_integral_contDiff_univ (P := ℂ × ℝ) (E := ℂ) (n := ⊤) ?_
  have hfam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun (_ : (ℂ × ℝ) × ℝ) (y : ℂ × ℝ) => G y)) := hG.comp contDiff_snd
  have hc1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℂ × ℝ) × ℝ => ((q.1.1, q.2 * q.1.2) : ℂ × ℝ)) :=
    (contDiff_fst.comp contDiff_fst).prodMk (contDiff_snd.mul (contDiff_snd.comp contDiff_fst))
  have hc2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℂ × ℝ) × ℝ => ((q.1.1, -(q.2 * q.1.2)) : ℂ × ℝ)) :=
    (contDiff_fst.comp contDiff_fst).prodMk
      ((contDiff_snd.mul (contDiff_snd.comp contDiff_fst)).neg)
  have hd1 := ContDiff.fderiv (𝕜 := ℝ)
    (f := fun (_ : (ℂ × ℝ) × ℝ) (y : ℂ × ℝ) => G y)
    (g := fun q : (ℂ × ℝ) × ℝ => ((q.1.1, q.2 * q.1.2) : ℂ × ℝ))
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hfam hc1 (by simp)
  have hd2 := ContDiff.fderiv (𝕜 := ℝ)
    (f := fun (_ : (ℂ × ℝ) × ℝ) (y : ℂ × ℝ) => G y)
    (g := fun q : (ℂ × ℝ) × ℝ => ((q.1.1, -(q.2 * q.1.2)) : ℂ × ℝ))
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hfam hc2 (by simp)
  have hsum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℂ × ℝ) × ℝ =>
      (fderiv ℝ G (q.1.1, q.2 * q.1.2)) ((0 : ℂ), (1 : ℝ))
        + (fderiv ℝ G (q.1.1, -(q.2 * q.1.2))) ((0 : ℂ), (1 : ℝ))) :=
    (hd1.clm_apply contDiff_const).add (hd2.clm_apply contDiff_const)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : (ℂ × ℝ) × ℝ => (1 / 2 : ℝ)) := contDiff_const
  have hfin := hc.smul hsum
  have hgoal : Function.uncurry (fun p : ℂ × ℝ => fun u : ℝ => (1 / 2 : ℝ) •
      ((fderiv ℝ G (p.1, u * p.2)) ((0 : ℂ), (1 : ℝ))
        + (fderiv ℝ G (p.1, -(u * p.2))) ((0 : ℂ), (1 : ℝ))))
      = fun q : (ℂ × ℝ) × ℝ => (1 / 2 : ℝ) •
        ((fderiv ℝ G (q.1.1, q.2 * q.1.2)) ((0 : ℂ), (1 : ℝ))
          + (fderiv ℝ G (q.1.1, -(q.2 * q.1.2))) ((0 : ℂ), (1 : ℝ))) := rfl
  rw [hgoal]
  exact hfin

/-! ## The halving of the chord vector -/

/-- The continuous argument of `x` relative to a base point `x₀`: a global formula, smooth on the
chart `{x | x / x₀ ∈ slitPlane}` (`contDiffOn_localArgC`). -/
noncomputable def dchTheta (x₀ x : ℂ) : ℝ := Complex.arg x₀ + (Complex.log (x / x₀)).im

/-- The chord expression in the local argument: a global formula equal to `dataChord` on the
chart (`dataChord_eq_localArg`). -/
noncomputable def dchGloc (γ : Circle → ℝ × ℝ) (x₀ : ℂ) (q : ℂ × ℝ) : ℂ :=
  symmC (curve γ (dchTheta x₀ q.1 + sClamp q.2) - curve γ (dchTheta x₀ q.1 - sClamp q.2))

lemma dchGloc_apply (γ : Circle → ℝ × ℝ) (x₀ x : ℂ) (s : ℝ) :
    dchGloc γ x₀ (x, s) = symmC (curve γ (Complex.arg x₀ + (Complex.log (x / x₀)).im + sClamp s)
      - curve γ (Complex.arg x₀ + (Complex.log (x / x₀)).im - sClamp s)) := rfl

/-- The parametrised Hadamard quotient: the `s`-derivative of `G` integrated against the
symmetrised opening. -/
noncomputable def dchMw (G : ℂ × ℝ → ℂ) (q : ℂ × ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..1, (1 / 2 : ℝ) • ((fderiv ℝ G (q.1, u * q.2)) ((0 : ℂ), (1 : ℝ))
    + (fderiv ℝ G (q.1, -(u * q.2))) ((0 : ℂ), (1 : ℝ)))

/-- The halving of the chord vector. -/
noncomputable def dchW (γ : Circle → ℝ × ℝ) : ℂ × ℝ → ℂ :=
  dchMw (fun q : ℂ × ℝ => dataChord γ q.1 q.2)

lemma dchMw_neg (G : ℂ × ℝ → ℂ) (x : ℂ) (s : ℝ) :
    dchMw G (x, -s) = dchMw G (x, s) := by
  rw [dchMw, dchMw]
  apply intervalIntegral.integral_congr
  intro u _
  beta_reduce
  rw [mul_neg, neg_neg, add_comm]

lemma dchW_neg (γ : Circle → ℝ × ℝ) (x : ℂ) (s : ℝ) : dchW γ (x, -s) = dchW γ (x, s) :=
  dchMw_neg _ x s

lemma dchMw_smul (G : ℂ × ℝ → ℂ) (x : ℂ) (s : ℝ)
    (hG : ∀ t : ℝ, HasFDerivAt G (fderiv ℝ G (x, t)) (x, t))
    (hc : Continuous fun u : ℝ => (fderiv ℝ G (x, u)) ((0 : ℂ), (1 : ℝ)))
    (h0 : G (x, 0) = 0) (hodd : ∀ t : ℝ, G (x, -t) = -G (x, t)) :
    s • dchMw G (x, s) = G (x, s) :=
  smul_integral_fderiv_symm G x s hG hc h0 hodd

lemma dchW_smul (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {x : ℂ} (hx : x ≠ 0) (s : ℝ) : s • dchW γ (x, s) = dataChord γ x s := by
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℂ × ℝ => dataChord γ q.1 q.2)
      {p : ℂ × ℝ | p.1 ≠ 0} := contDiffOn_dataChord_of_ne γ hγ
  have hmem : ∀ t : ℝ, {p : ℂ × ℝ | p.1 ≠ 0} ∈ 𝓝 (x, t) := fun t =>
    (isOpen_ne.preimage continuous_fst).mem_nhds hx
  have hdiff : ∀ t : ℝ, HasFDerivAt (fun q : ℂ × ℝ => dataChord γ q.1 q.2)
      (fderiv ℝ (fun q : ℂ × ℝ => dataChord γ q.1 q.2) (x, t)) (x, t) := fun t =>
    ((hf.contDiffAt (hmem t)).differentiableAt (by simp)).hasFDerivAt
  have hcont : Continuous (fun u : ℝ =>
      (fderiv ℝ (fun q : ℂ × ℝ => dataChord γ q.1 q.2) (x, u)) ((0 : ℂ), (1 : ℝ))) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (((hf.contDiffAt (hmem u)).continuousAt_fderiv (by simp)).comp
      (continuousAt_const.prodMk continuousAt_id)).clm_apply continuousAt_const
  have h0 : (fun q : ℂ × ℝ => dataChord γ q.1 q.2) (x, 0) = 0 := by
    simp only [dataChord, endPlus, endMinus, neg_zero, sub_self]
  have hodd : ∀ t : ℝ, (fun q : ℂ × ℝ => dataChord γ q.1 q.2) (x, -t)
      = -(fun q : ℂ × ℝ => dataChord γ q.1 q.2) (x, t) := by
    intro t
    simp only [dataChord, endPlus, endMinus, neg_neg]
    ring
  exact dchMw_smul (fun q : ℂ × ℝ => dataChord γ q.1 q.2) x s hdiff hcont h0 hodd

/-- The parametric `fderiv`-integral of a globally smooth function is globally smooth. -/
lemma contDiff_dchMw (G : ℂ × ℝ → ℂ) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dchMw G) := by
  refine parametric_integral_contDiff_univ (P := ℂ × ℝ) (E := ℂ) (n := ⊤) ?_
  have hfam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun (_ : (ℂ × ℝ) × ℝ) (y : ℂ × ℝ) => G y)) := hG.comp contDiff_snd
  have hc1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℂ × ℝ) × ℝ => ((q.1.1, q.2 * q.1.2) : ℂ × ℝ)) :=
    (contDiff_fst.comp contDiff_fst).prodMk (contDiff_snd.mul (contDiff_snd.comp contDiff_fst))
  have hc2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℂ × ℝ) × ℝ => ((q.1.1, -(q.2 * q.1.2)) : ℂ × ℝ)) :=
    (contDiff_fst.comp contDiff_fst).prodMk
      ((contDiff_snd.mul (contDiff_snd.comp contDiff_fst)).neg)
  have hd1 := ContDiff.fderiv (𝕜 := ℝ)
    (f := fun (_ : (ℂ × ℝ) × ℝ) (y : ℂ × ℝ) => G y)
    (g := fun q : (ℂ × ℝ) × ℝ => ((q.1.1, q.2 * q.1.2) : ℂ × ℝ))
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hfam hc1 (by simp)
  have hd2 := ContDiff.fderiv (𝕜 := ℝ)
    (f := fun (_ : (ℂ × ℝ) × ℝ) (y : ℂ × ℝ) => G y)
    (g := fun q : (ℂ × ℝ) × ℝ => ((q.1.1, -(q.2 * q.1.2)) : ℂ × ℝ))
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hfam hc2 (by simp)
  have hsum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℂ × ℝ) × ℝ =>
      (fderiv ℝ G (q.1.1, q.2 * q.1.2)) ((0 : ℂ), (1 : ℝ))
        + (fderiv ℝ G (q.1.1, -(q.2 * q.1.2))) ((0 : ℂ), (1 : ℝ))) :=
    (hd1.clm_apply contDiff_const).add (hd2.clm_apply contDiff_const)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : (ℂ × ℝ) × ℝ => (1 / 2 : ℝ)) := contDiff_const
  have hfin := hc.smul hsum
  have hgoal : (Function.uncurry fun p : ℂ × ℝ => fun u : ℝ => (1 / 2 : ℝ) •
      ((fderiv ℝ G (p.1, u * p.2)) ((0 : ℂ), (1 : ℝ))
        + (fderiv ℝ G (p.1, -(u * p.2))) ((0 : ℂ), (1 : ℝ))))
      = fun q : (ℂ × ℝ) × ℝ => (1 / 2 : ℝ) •
        ((fderiv ℝ G (q.1.1, q.2 * q.1.2)) ((0 : ℂ), (1 : ℝ))
          + (fderiv ℝ G (q.1.1, -(q.2 * q.1.2))) ((0 : ℂ), (1 : ℝ))) := rfl
  rw [hgoal]
  exact hfin

/-- The glued model `φ x • dchGloc γ x₀ x`: globally smooth when `φ` is smooth on the chart. -/
noncomputable def dchGhat (γ : Circle → ℝ × ℝ) (φ : ℂ → ℝ) (x₀ : ℂ) (q : ℂ × ℝ) : ℂ :=
  φ q.1 • dchGloc γ x₀ q

lemma dchGhat_apply (γ : Circle → ℝ × ℝ) (φ : ℂ → ℝ) (x₀ x : ℂ) (s : ℝ) :
    dchGhat γ φ x₀ (x, s) = φ x • dchGloc γ x₀ (x, s) := rfl

/-- The halving of the chord vector is `C^∞` on `{x ≠ 0}` (locally it is the Hadamard quotient of
a globally smooth model built from the local continuous argument). -/
theorem contDiffOn_dchW (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dchW γ) {p : ℂ × ℝ | p.1 ≠ 0} := by
  refine contDiffOn_of_locally_contDiffOn (fun p hp => ?_)
  obtain ⟨x₀, s₀⟩ := p
  have hx₀ : x₀ ≠ 0 := hp
  set V : Set ℂ := {x : ℂ | x / x₀ ∈ Complex.slitPlane} with hVdef
  have hVopen : IsOpen V := Complex.isOpen_slitPlane.preimage (continuous_id.div_const x₀)
  have hx₀V : x₀ ∈ V := by
    show x₀ / x₀ ∈ Complex.slitPlane
    rw [div_self hx₀]; exact Complex.one_mem_slitPlane
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hVopen x₀ hx₀V
  let χ : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hrOut : χ.rOut = ε / 2 := rfl
  have hrIn : χ.rIn = ε / 4 := rfl
  have hχε1 : ∀ x ∈ Metric.closedBall x₀ χ.rIn, (χ x : ℝ) = 1 := fun x hx => χ.one_of_mem_closedBall hx
  have hχsupp : Function.support (fun x : ℂ => (χ x : ℝ)) ⊆ Metric.closedBall x₀ χ.rOut := by
    intro x hx
    rw [Metric.mem_closedBall]
    by_contra h
    exact hx (χ.zero_of_le_dist (le_of_lt (not_le.mp h)))
  have htsupp : tsupport (fun x : ℂ => (χ x : ℝ)) ⊆ V := by
    refine (closure_minimal hχsupp Metric.isClosed_closedBall).trans ?_
    intro x hx
    exact hεV (Metric.closedBall_subset_ball (by rw [hrOut]; linarith [hε]) hx)
  -- `dchGloc` is smooth on the chart
  have hGloc_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dchGloc γ x₀) (V ×ˢ Set.univ) := by
    have hθf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℂ × ℝ => dchTheta x₀ q.1)
        (V ×ˢ Set.univ) :=
      (contDiffOn_localArgC x₀).comp contDiffOn_fst (fun q hq => hq.1)
    have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℂ × ℝ => sClamp q.2)
        (V ×ˢ Set.univ) := (contDiff_sClamp.comp contDiff_snd).contDiffOn
    have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => symmC (curve γ t)) :=
      contDiff_symmC.comp (contDiff_curve_top hγ)
    exact (hc.comp_contDiffOn (hθf.add hs)).sub (hc.comp_contDiffOn (hθf.sub hs))
  -- `dchGhat` is globally smooth
  have hGhat1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dchGhat γ (fun x => (χ x : ℝ)) x₀)
      (V ×ˢ Set.univ) := by
    have hχcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℂ × ℝ => (χ q.1 : ℝ))
        (V ×ˢ Set.univ) := (χ.contDiff.comp contDiff_fst).contDiffOn
    exact hχcd.smul hGloc_smooth
  have hGhat2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dchGhat γ (fun x => (χ x : ℝ)) x₀)
      {q : ℂ × ℝ | q.1 ∉ tsupport (fun x : ℂ => (χ x : ℝ))} := by
    refine ContDiffOn.congr (contDiffOn_const (c := (0 : ℂ))) (fun q hq => ?_)
    have h0 : (χ q.1 : ℝ) = 0 := by
      by_contra h
      exact hq (subset_tsupport _ (Function.mem_support.mpr h))
    rw [dchGhat_apply, h0, zero_smul]
  have hGhat_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dchGhat γ (fun x => (χ x : ℝ)) x₀) := by
    have hloc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dchGhat γ (fun x => (χ x : ℝ)) x₀) Set.univ := by
      refine contDiffOn_of_locally_contDiffOn (fun q _ => ?_)
      by_cases hq : q.1 ∈ tsupport (fun x : ℂ => (χ x : ℝ))
      · exact ⟨V ×ˢ Set.univ, hVopen.prod isOpen_univ, ⟨htsupp hq, trivial⟩,
          hGhat1.mono Set.inter_subset_right⟩
      · exact ⟨{q : ℂ × ℝ | q.1 ∉ tsupport (fun x : ℂ => (χ x : ℝ))},
          (isClosed_tsupport _).isOpen_compl.preimage continuous_fst, hq,
          hGhat2.mono Set.inter_subset_right⟩
    exact contDiffOn_univ.mp hloc
  have hGhat0 : ∀ x : ℂ, dchGhat γ (fun x => (χ x : ℝ)) x₀ (x, 0) = 0 := by
    intro x
    have hgl : dchGloc γ x₀ (x, 0) = 0 := by
      simp only [dchGloc, dchTheta, sClamp_zero, add_zero, sub_zero, sub_self, symmC_zero]
    rw [dchGhat_apply, hgl, smul_zero]
  have hGhatodd : ∀ x : ℂ, ∀ t : ℝ,
      dchGhat γ (fun x => (χ x : ℝ)) x₀ (x, -t) = -dchGhat γ (fun x => (χ x : ℝ)) x₀ (x, t) := by
    intro x t
    simp only [dchGhat_apply, dchGloc, dchTheta, sClamp_odd]
    rw [show Complex.arg x₀ + (Complex.log (x / x₀)).im + -sClamp t
        = Complex.arg x₀ + (Complex.log (x / x₀)).im - sClamp t by ring,
      show Complex.arg x₀ + (Complex.log (x / x₀)).im - -sClamp t
        = Complex.arg x₀ + (Complex.log (x / x₀)).im + sClamp t by ring]
    rw [symmC_sub, symmC_sub, Complex.real_smul, Complex.real_smul]
    ring
  -- the Hadamard quotient of the model
  have hMsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (dchMw (dchGhat γ (fun x => (χ x : ℝ)) x₀)) := contDiff_dchMw _ hGhat_smooth
  have hMsmul : ∀ x s, s • dchMw (dchGhat γ (fun x => (χ x : ℝ)) x₀) (x, s)
      = dchGhat γ (fun x => (χ x : ℝ)) x₀ (x, s) := by
    intro x s
    have hdiff : ∀ t : ℝ, HasFDerivAt (dchGhat γ (fun x => (χ x : ℝ)) x₀)
        (fderiv ℝ (dchGhat γ (fun x => (χ x : ℝ)) x₀) (x, t)) (x, t) := fun t =>
      ((hGhat_smooth.differentiable (by simp)).differentiableAt).hasFDerivAt
    have hcont : Continuous (fun u : ℝ =>
        (fderiv ℝ (dchGhat γ (fun x => (χ x : ℝ)) x₀) (x, u)) ((0 : ℂ), (1 : ℝ))) :=
      (hGhat_smooth.continuous_fderiv (by simp)).clm_apply continuous_const |>.comp
        (continuous_const.prodMk continuous_id)
    exact dchMw_smul _ x s hdiff hcont (hGhat0 x) (fun t => hGhatodd x t)
  -- the chord agrees with the model near `x₀`
  have hfeq : ∀ x ∈ Metric.ball x₀ χ.rIn, ∀ s : ℝ,
      (fun q : ℂ × ℝ => dataChord γ q.1 q.2) (x, s)
        = dchGhat γ (fun x => (χ x : ℝ)) x₀ (x, s) := by
    intro x hx s
    have hxcl : x ∈ Metric.closedBall x₀ χ.rIn := Metric.ball_subset_closedBall hx
    have hxV : x ∈ V := hεV (Metric.closedBall_subset_ball (by rw [hrOut]; linarith [hε])
      (Metric.closedBall_subset_closedBall χ.rIn_lt_rOut.le hxcl))
    have hθeq : ∀ y : ℂ, (y / x₀ ∈ Complex.slitPlane) →
        dchTheta x₀ y = Complex.arg x₀ + (Complex.log (y / x₀)).im := fun y _ => rfl
    have hgl : dchGloc γ x₀ (x, s) = dataChord γ x s := by
      rw [dchGloc_apply]
      exact (dataChord_eq_localArg γ x₀ hx₀ hxV s).symm
    rw [dchGhat_apply, hχε1 x hxcl, one_smul, hgl]
  have hfd : ∀ (x : ℂ) (t : ℝ), x ∈ Metric.ball x₀ χ.rIn →
      fderiv ℝ (fun q : ℂ × ℝ => dataChord γ q.1 q.2) (x, t)
        = fderiv ℝ (dchGhat γ (fun x => (χ x : ℝ)) x₀) (x, t) := by
    intro x t hx
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [(Metric.isOpen_ball.prod isOpen_univ).mem_nhds
      (show (x, t) ∈ Metric.ball x₀ χ.rIn ×ˢ Set.univ from ⟨hx, trivial⟩)] with q hq
    exact hfeq q.1 hq.1 q.2
  have hWM : ∀ (x : ℂ) (s : ℝ), x ∈ Metric.ball x₀ χ.rIn →
      dchW γ (x, s) = dchMw (dchGhat γ (fun x => (χ x : ℝ)) x₀) (x, s) := by
    intro x s hx
    rw [dchW, dchMw, dchMw]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [hfd x (u * s) hx, hfd x (-(u * s)) hx]
  -- conclude
  refine ⟨Metric.ball x₀ χ.rIn ×ˢ Set.univ, Metric.isOpen_ball.prod isOpen_univ,
    ⟨by show x₀ ∈ Metric.ball x₀ χ.rIn; rw [Metric.mem_ball, dist_self]; exact χ.rIn_pos,
      trivial⟩, ?_⟩
  exact ((hMsmooth.contDiffOn.congr (fun q hq => (hWM q.1 q.2 hq.1))).mono Set.inter_subset_right)

open Manifold in
open scoped Manifold ContDiff in
theorem dataChord_spec (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℂ × ℝ => dataChord γ p.1 p.2) {p : ℂ × ℝ | p.1 ≠ 0} ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℂ × ℝ => dataMid γ p.1 p.2) {p : ℂ × ℝ | p.1 ≠ 0} ∧
      (∀ x s, dataChord γ x (-s) = -dataChord γ x s) ∧
      (∀ x s, dataMid γ x (-s) = dataMid γ x s) ∧
      (∃ W : ℂ × ℝ → ℂ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W {p : ℂ × ℝ | p.1 ≠ 0} ∧
        (∀ x s, x ≠ 0 → dataChord γ x s = s • W (x, s)) ∧
        (∀ x s, W (x, -s) = W (x, s))) := by
  refine ⟨contDiffOn_dataChord_of_ne γ hγ, contDiffOn_dataMid_of_ne γ hγ, ?_, ?_, ?_⟩
  · intro x s
    simp only [dataChord, endPlus, endMinus, neg_neg]
    ring
  · intro x s
    simp only [dataMid, endPlus, endMinus, neg_neg]
    ring
  · exact ⟨dchW γ, contDiffOn_dchW γ hγ,
      fun x s hx => (dchW_smul γ hγ hx s).symm, fun x s => dchW_neg γ x s⟩

end Work.Drive.Neutral
