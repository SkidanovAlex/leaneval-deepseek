import Mathlib
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.stripConfigInterface
import Submission.Work.Drive.tendsto_stripData_diag
import Submission.Work.Drive.exists_continuous_chordDir
import Submission.Work.Drive.stripChartSmooth

/-!
# The seam circle of a plane chart lies in the configuration band

`Work.Drive.IsPlaneChart γ hγne Q` pins a `C^∞` disk model `Q : ℂ → CappingSpace` of the capped plane
of `γ` by three clauses:

* the **strip clause** on the half-open annulus `1/2 < ‖z‖ ≤ 1`, where `Q z` is the class of the chord
  `(γ (arg z - s), γ (arg z + s))`, `s = √(π²(‖z‖ - 1/2)/2)`;
* the **seam clause** `Q (-z) = Q z` on the outer circle `‖z‖ = 1`;
* the **cap clause** on the open disk `‖z‖ < 1/2`, where `Q z` is the class of a cap point.

The **inner** circle `‖z‖ = 1/2` is covered by *neither* the strip clause (stated with the strict
inequality `1/2 < ‖z‖`) nor the cap clause (strict `‖z‖ < 1/2`): its value is pinned only by the
continuity of `Q`, and this file computes it.  It is the *tangent* chord, i.e. the diagonal point of
the configuration strip:

> **`Work.Drive.isPlaneChart_seam_mem_stripImage`** — for every `z` with `‖z‖ = 1/2` the value `Q z` is
> the class of the diagonal configuration point `(γ x, tangentDirC γ x, 0)` with `x = Circle.exp
> (arg z)`, hence lies in the image `Work.Drive.stripImage μ` of the strip `μ` (whose diagonal value is
> `μ (x, x) = (γ x, tangentDirC γ x, 0)` by hypothesis).

## Why this is not a one-liner, and what the naive statement gets wrong

The naive reading "`Q z = stripChart γ hγne 0 (mk2 a a)` with `a = arg z`" — the strip chart
*evaluated* at the coincident parameters, i.e. the limit of the *formula* of the strip clause — is
**FALSE**: `stripChart γ hγne 0 w` is the class of `confOf (muOrd γ (exp (w 0), exp (w 1)))`, and at
`w 0 = w 1` the chord is degenerate, so `dirC 0 = 0`, whereas the honest limit of the *values* `Q z'`
as `z' → z` from the annulus is the chord direction of the secant `γ (exp (a+s)) - γ (exp (a-s))` as
`s → 0⁺`, which converges to the **tangent** direction (`Work.Drive.tendsto_stripData_diag`, which
computes `s ↦ stripData γ (mk2 (a+s) (a-s))` in the limit).  So the seam value is
`(‖γ x‖, γ x / ‖γ x‖, tangentDirC γ x)` — exactly the diagonal value of the (continuous extension of
the) configuration strip `μ`, and it is this coincidence that makes the statement true.

The proof therefore computes a limit (no shortcut through closedness of `stripImage μ`, which fails for
a non-continuous `μ`):

* along the radial path `s ↦ (1 + 4s²/π²) • z` (positive real scaling, so `arg` is constant) the value
  of `Q` is the strip chart at the parameter `mk2 (arg z + s) (arg z - s)`, whose *value* tends to the
  diagonal point of the strip (the parameter itself jumps to the diagonal, where the chart is
  discontinuous, but the values converge to the tangent chord);
* the two limits `Q z_s → Q z` (continuity of `Q`) and `Q z_s → M` (the computation) agree by
  Hausdorffness of `CappingSpace` (`Work.Drive.cappingSpaceHomeoProj`).

## Contents

* `Work.Drive.arg_mul_ofReal_pos` — `arg` of a positive real multiple;
* `Work.Drive.rotConfig_zero_seam`, `Work.Drive.seamConfPt`, `Work.Drive.stripChart_zero_eq_seam` — the
  strip chart at rotation zero as a configuration class;
* `Work.Drive.confOf_eq_diag`, `Work.Drive.confOf_pos_diag` — the capping coordinates of a degenerate
  chord, as `(eucNorm m, m/‖m‖, η)`;
* `Work.Drive.seamDiagCP` — the diagonal configuration point at a parameter `a`;
* `Work.Drive.tendsto_confOf_muOrd_diag`, `Work.Drive.tendsto_seamDiagCP_diag`,
  `Work.Drive.tendsto_stripChart_seamDiag` — the diagonal limit in capping coordinates, in the
  configuration piece, and in the capping space;
* **`Work.Drive.isPlaneChart_seam_mem_stripImage`** — the target.
-/

set_option autoImplicit false

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology
open Submission.Configuration (muOrd)
open Submission.Geometry (eucNorm)
open Submission.Collision (dirC)

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted

noncomputable section

variable {γ : Circle → ℝ × ℝ}

/-! ## 1. Elementary preliminaries -/

/-- **The argument of a positive real multiple.**  Scaling by a positive real number does not change
`Complex.arg`; this is what keeps the radial path of the proof below on a fixed ray, so that the strip
clause sees a *constant* `arg` while the opening `s` varies. -/
lemma arg_mul_ofReal_pos (c : ℝ) (hc : 0 < c) (z : ℂ) :
    Complex.arg (((c : ℝ) : ℂ) * z) = Complex.arg z := by
  rcases eq_or_ne z 0 with rfl | hzne
  · simp
  · rw [Complex.arg_mul (by exact_mod_cast ne_of_gt hc) hzne]
    · simp only [Complex.arg_ofReal_of_nonneg hc.le, zero_add]
    · refine ⟨?_, ?_⟩
      · simpa only [Complex.arg_ofReal_of_nonneg hc.le, zero_add] using Complex.neg_pi_lt_arg z
      · simpa only [Complex.arg_ofReal_of_nonneg hc.le, zero_add] using Complex.arg_le_pi z

/-- `rotConfig 0` is the identity on the configuration piece. -/
lemma rotConfig_zero_seam (p : ConfigPiece) : rotConfig 0 p = p := by
  refine Subtype.ext ?_
  show (p.1.1, p.1.2.1, p.1.2.2 + 0) = p.1
  refine Prod.ext rfl ?_
  refine Prod.ext rfl ?_
  simp

/-- The configuration point of the chord with parameters `w` (`= (w 0, w 1)`): the capping coordinates
of `muOrd γ`, packaged as an element of the configuration piece.  The two side conditions are the
proven `Work.Drive.stripData_pos` and `Work.Drive.confOf_snd_norm_le_one`. -/
def seamConfPt (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) : ConfigPiece :=
  confPiece (muOrd γ (Circle.exp (w 0), Circle.exp (w 1))) (stripData_pos hγne w)
    (confOf_snd_norm_le_one _)

@[simp] lemma seamConfPt_val (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    (seamConfPt γ hγne w : ℝ × ℂ × UnitAddCircle)
      = confOf (muOrd γ (Circle.exp (w 0), Circle.exp (w 1))) := rfl

/-- **The strip chart at rotation zero is the class of its configuration point.** -/
lemma stripChart_zero_eq_seam (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    stripChart γ hγne 0 w = Quotient.mk'' (Sum.inl (seamConfPt γ hγne w)) := by
  unfold stripChart seamConfPt
  rw [rotConfig_zero_seam]

/-- **The capping coordinates of a degenerate chord.**  At vanishing length the capping radius is the
Euclidean norm of the midpoint and the disk coordinate is the normalised midpoint, so the raw formula
`confOf` takes the form in which the limit `Work.Drive.tendsto_stripData_diag` can be read. -/
lemma confOf_eq_diag (m : ℝ × ℝ) (hm : m ≠ 0) (η : UnitAddCircle) :
    confOf (m, η, 0) = (eucNorm m, ((⟨m.1, m.2⟩ : ℂ)) / ((eucNorm m : ℝ) : ℂ), η) := by
  have hS : eucNorm m = Real.sqrt (m.1 ^ 2 + m.2 ^ 2) := by rw [eucNorm, Submission.Geometry.eucDot_self]
  rw [hS]
  have hm' : m.1 ≠ 0 ∨ m.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (Prod.ext h.1 h.2)
  have hpos : 0 < Real.sqrt (m.1 ^ 2 + m.2 ^ 2) := Real.sqrt_pos.mpr (by
    rcases hm' with h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg m.1, sq_nonneg m.2])
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · simp only [confOf, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  · simp only [confOf, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
    refine Complex.ext ?_ ?_
    · simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
      field_simp
      ring
    · simp only [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
      field_simp
      ring

/-- The capping radius of a degenerate chord is positive as soon as its midpoint is off the axis. -/
lemma confOf_pos_diag (m : ℝ × ℝ) (hm : m ≠ 0) (η : UnitAddCircle) :
    0 < (confOf (m, η, 0)).1 := by
  rw [confOf_eq_diag m hm η]
  exact Submission.Geometry.eucNorm_pos hm

/-! ## 2. The diagonal limit of the chord data -/

/-- **The diagonal limit of the capping coordinates of the chord family.**  As the opening `s → 0⁺` the
capping coordinates of the chord `(a - s, a + s)` tend to those of the *degenerate* chord at
`Circle.exp a`, with the **tangent** doubled direction.  This is `Work.Drive.tendsto_stripData_diag`
with the doubled tangent direction rewritten by `Work.Drive.tangentDirC_of_exp_eq`. -/
lemma tendsto_confOf_muOrd_diag
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (a : ℝ) :
    Tendsto (fun s : ℝ => confOf (muOrd γ (Circle.exp (a + s), Circle.exp (a - s))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (eucNorm (γ (Circle.exp a)),
        ((⟨(γ (Circle.exp a)).1, (γ (Circle.exp a)).2⟩ : ℂ)) /
          ((eucNorm (γ (Circle.exp a)) : ℝ) : ℂ), tangentDirC γ (Circle.exp a))) := by
  have h := tendsto_stripData_diag γ hγ a
  rw [show dirC (deriv (fun t : ℝ => γ (Circle.exp t)) a) = tangentDirC γ (Circle.exp a) from
    (tangentDirC_of_exp_eq γ hγ rfl).symm] at h
  simpa only [stripData, mk2_apply_zero, mk2_apply_one] using h

/-- **The diagonal configuration point of the curve at the parameter `a`**: the class of the degenerate
chord at `Circle.exp a` with the *tangent* doubled direction.  This is the value of the configuration
strip at its seam, and it is where the inner boundary circle of a plane chart lands. -/
def seamDiagCP (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0) (a : ℝ) : ConfigPiece :=
  confPiece (γ (Circle.exp a), tangentDirC γ (Circle.exp a), 0)
    (confOf_pos_diag (γ (Circle.exp a)) (hγne _) (tangentDirC γ (Circle.exp a)))
    (confOf_snd_norm_le_one _)

@[simp] lemma seamDiagCP_val (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0) (a : ℝ) :
    (seamDiagCP γ hγne a : ℝ × ℂ × UnitAddCircle)
      = confOf (γ (Circle.exp a), tangentDirC γ (Circle.exp a), 0) := rfl

/-- **The configuration points of the chord family tend to the diagonal point.** -/
lemma tendsto_seamDiagCP_diag
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {hγne : ∀ x : Circle, γ x ≠ 0} (a : ℝ) :
    Tendsto (fun s : ℝ => seamConfPt γ hγne (mk2 (a + s) (a - s))) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (seamDiagCP γ hγne a)) := by
  have hconf : Tendsto (fun s : ℝ => confOf (muOrd γ (Circle.exp (a + s), Circle.exp (a - s))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (confOf (γ (Circle.exp a), tangentDirC γ (Circle.exp a), 0))) := by
    rw [confOf_eq_diag (γ (Circle.exp a)) (hγne _) (tangentDirC γ (Circle.exp a))]
    exact tendsto_confOf_muOrd_diag hγ a
  rw [nhds_subtype {q : ℝ × ℂ × UnitAddCircle | 0 < q.1 ∧ ‖q.2.1‖ ≤ 1} (seamDiagCP γ hγne a)]
  exact Filter.tendsto_comap_iff.mpr (by
    simpa only [Function.comp_def, seamConfPt_val, seamDiagCP, confPiece_val, mk2_apply_zero,
      mk2_apply_one] using hconf)

/-- **The strip chart of the diagonal parameter tends to the diagonal point of the strip.**  This is
the comparison of the strip clause of `IsPlaneChart` with the diagonal value of the strip `μ`; note
that the *chart* is not continuous at the diagonal parameter, but its values are. -/
lemma tendsto_stripChart_seamDiag
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {hγne : ∀ x : Circle, γ x ≠ 0} (a : ℝ) :
    Tendsto (fun s : ℝ => stripChart γ hγne 0 (mk2 (a + s) (a - s))) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Quotient.mk'' (Sum.inl (seamDiagCP γ hγne a)))) := by
  have hcont : Continuous (fun p : ConfigPiece => (Quotient.mk'' (Sum.inl p) : CappingSpace)) :=
    continuous_cappingMk.comp continuous_inl
  have hcls : Tendsto
      (fun s : ℝ => (Quotient.mk'' (Sum.inl (seamConfPt γ hγne (mk2 (a + s) (a - s))))
        : CappingSpace))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Quotient.mk'' (Sum.inl (seamDiagCP γ hγne a)))) :=
    hcont.continuousAt.tendsto.comp (tendsto_seamDiagCP_diag hγ a)
  exact Tendsto.congr'
    (Eventually.of_forall (fun s => (stripChart_zero_eq_seam γ hγne (mk2 (a + s) (a - s))).symm))
    hcls

/-! ## 3. The seam circle of a plane chart -/

/-- **The inner boundary circle of a plane chart lies in the configuration band.**  At `‖z‖ = 1/2` the
value of a plane chart is the class of the *tangent* chord at `Circle.exp (arg z)` — the diagonal
configuration point with doubled direction the tangent direction — which is exactly the diagonal value
`μ (x, x) = (γ x, tangentDirC γ x, 0)` of the strip; hence `Q z ∈ stripImage μ`. -/
theorem isPlaneChart_seam_mem_stripImage {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, Work.Drive.tangentDirC γ x, 0))
    {z : ℂ} (hz : ‖z‖ = 1 / 2) :
    Q z ∈ Work.Drive.stripImage μ := by
  -- `CappingSpace` is Hausdorff (it is homeomorphic to `(0,∞) × ℝP³`), so the two limits below agree
  haveI : T2Space Work.Drive.CappingSpace := cappingSpaceHomeoProj.symm.t2Space
  -- the parameter of the seam point and the radial path
  set a : ℝ := Complex.arg z with ha
  have hnorm : ∀ s : ℝ, ‖(((1 + 4 * s ^ 2 / Real.pi ^ 2 : ℝ)) : ℂ) * z‖
      = 1 / 2 + 2 * s ^ 2 / Real.pi ^ 2 := by
    intro s
    rw [Complex.norm_mul, hz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    ring
  have harg : ∀ s : ℝ, Complex.arg ((((1 + 4 * s ^ 2 / Real.pi ^ 2 : ℝ)) : ℂ) * z) = a := by
    intro s
    rw [arg_mul_ofReal_pos _ (by positivity) z, ha]
  have hsqrt : ∀ s : ℝ, 0 ≤ s →
      Real.sqrt (Real.pi ^ 2 * ((1 / 2 + 2 * s ^ 2 / Real.pi ^ 2) - 1 / 2) / 2) = s := by
    intro s hs
    have h : Real.pi ^ 2 * ((1 / 2 + 2 * s ^ 2 / Real.pi ^ 2) - 1 / 2) / 2 = s ^ 2 := by
      field_simp
      ring
    rw [h, Real.sqrt_sq hs]
  -- the strip clause on the path, for `s ∈ (0, 1]`
  have hsmall : ∀ᶠ s : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), s ≤ 1 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs _
    exact hs
  have hstrip_eq : (fun s : ℝ => Q ((((1 + 4 * s ^ 2 / Real.pi ^ 2 : ℝ)) : ℂ) * z))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun s : ℝ => stripChart γ hγne 0 (mk2 (a + s) (a - s))) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hs1
    have hspos : 0 < s := hs
    have hle : ‖(((1 + 4 * s ^ 2 / Real.pi ^ 2 : ℝ)) : ℂ) * z‖ ≤ 1 := by
      rw [hnorm s]
      have hs2 : s ^ 2 ≤ 1 := by nlinarith
      have hpi : (2 : ℝ) ≤ Real.pi := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
      have hpi2 : 4 ≤ Real.pi ^ 2 := by nlinarith [hpi, Real.pi_pos]
      have hle2 : 2 * s ^ 2 / Real.pi ^ 2 ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 2)]
        nlinarith [hs2, hpi2]
      linarith
    have hlt : 1 / 2 < ‖(((1 + 4 * s ^ 2 / Real.pi ^ 2 : ℝ)) : ℂ) * z‖ := by
      rw [hnorm s]
      have : 0 < 2 * s ^ 2 / Real.pi ^ 2 := by positivity
      linarith
    rw [hQ.2.1 _ hlt hle, hnorm s, harg s, hsqrt s (le_of_lt hspos)]
  -- limit 1: continuity of `Q`
  have hcontQ : Continuous Q := hQ.1.continuous
  have hlim1 : Tendsto (fun s : ℝ => Q ((((1 + 4 * s ^ 2 / Real.pi ^ 2 : ℝ)) : ℂ) * z))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Q z)) := by
    refine hcontQ.continuousAt.tendsto.comp ?_
    have hc : Tendsto (fun s : ℝ => (((1 + 4 * s ^ 2 / Real.pi ^ 2 : ℝ)) : ℂ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℂ)) := by
      have hreal : Tendsto (fun s : ℝ => (1 + 4 * s ^ 2 / Real.pi ^ 2 : ℝ)) (nhds (0 : ℝ))
          (nhds (1 : ℝ)) := by
        have hc' : Continuous (fun s : ℝ => (1 + 4 * s ^ 2 / Real.pi ^ 2 : ℝ)) := by fun_prop
        simpa using hc'.continuousAt.tendsto (x := (0 : ℝ))
      exact (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp (hreal.mono_left nhdsWithin_le_nhds)
    simpa using hc.mul tendsto_const_nhds
  -- limit 2: the strip chart at the diagonal parameter
  have hlim2 : Tendsto (fun s : ℝ => Q ((((1 + 4 * s ^ 2 / Real.pi ^ 2 : ℝ)) : ℂ) * z))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Quotient.mk'' (Sum.inl (seamDiagCP γ hγne a)))) :=
    Tendsto.congr' hstrip_eq.symm (tendsto_stripChart_seamDiag hγ a)
  have hQz : Q z = Quotient.mk'' (Sum.inl (seamDiagCP γ hγne a)) :=
    tendsto_nhds_unique hlim1 hlim2
  -- the diagonal point of `μ` is the same configuration point
  have hμa := hμdiag (Circle.exp a)
  have hne : γ (Circle.exp a) ≠ 0 := hγne _
  have h1 : 0 < (confOf (μ (Circle.exp a, Circle.exp a))).1 := by
    rw [hμa]
    exact confOf_pos_diag _ hne _
  have h2 : ‖(confOf (μ (Circle.exp a, Circle.exp a))).2.1‖ ≤ 1 := confOf_snd_norm_le_one _
  have hW : confPiece (μ (Circle.exp a, Circle.exp a)) h1 h2 = seamDiagCP γ hγne a := by
    refine Subtype.ext ?_
    rw [confPiece_val, seamDiagCP_val, hμa]
  rw [mem_stripImage_iff]
  exact ⟨(Circle.exp a, Circle.exp a), h1, h2, by rw [hW]; exact hQz⟩

end

end Work.Drive
