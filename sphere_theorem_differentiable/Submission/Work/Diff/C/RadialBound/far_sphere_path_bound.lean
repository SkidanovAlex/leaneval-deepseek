import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.GExpSmooth
import Submission.Commons.Analysis.InnerProductSpace.great_circle_norm
import Submission.Commons.Analysis.InnerProductSpace.great_circle_orth_norm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.RadialBound

open Bundle MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

/-! ## The great-circle path in the unit sphere of a real inner product space

This is a (private) copy of the great-circle vocabulary that was used by
`Submission.Work.Diff.C.far_sphere_diameter`: the definitions there were replaced by a delegation to
the present lemma while this proof was being written, so the path and its elementary properties are
restated here (with distinct names) to keep the module self-contained.  The two ingredients are
`Commons.Analysis.InnerProductSpace.great_circle_norm` (the path stays on the unit sphere) and
`Commons.Analysis.InnerProductSpace.great_circle_orth_norm` (its speed is constant). -/

section GreatCircle

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The great-circle path in `F` between two vectors `P₁`, `P₂` at angle `Φ`
(`⟪P₁,P₂⟫ = cos Φ`), parametrised on `[0,1]`. -/
private noncomputable def gcPathL (P₁ P₂ : F) (Φ : ℝ) : ℝ → F :=
  fun s => (Real.sin ((1 - s) * Φ) / Real.sin Φ) • P₁
    + (Real.sin (s * Φ) / Real.sin Φ) • P₂

private lemma gcPathL_fun (P₁ P₂ : F) (Φ : ℝ) :
    gcPathL P₁ P₂ Φ = (fun t : ℝ => (Real.sin ((1 - t) * Φ) / Real.sin Φ) • P₁)
      + (fun t : ℝ => (Real.sin (t * Φ) / Real.sin Φ) • P₂) := rfl

private lemma gcPathL_zero (P₁ P₂ : F) {Φ : ℝ} (hΦ : Real.sin Φ ≠ 0) :
    gcPathL P₁ P₂ Φ 0 = P₁ := by
  have h : (1 - 0) * Φ = Φ := by ring
  simp only [gcPathL, h, zero_mul, Real.sin_zero, zero_div, zero_smul, add_zero]
  rw [div_self hΦ, one_smul]

private lemma gcPathL_one (P₁ P₂ : F) {Φ : ℝ} (hΦ : Real.sin Φ ≠ 0) :
    gcPathL P₁ P₂ Φ 1 = P₂ := by
  have h : (1 - 1) * Φ = 0 := by ring
  have h2 : 1 * Φ = Φ := by ring
  simp only [gcPathL, h, h2, Real.sin_zero, zero_div, zero_smul, zero_add]
  rw [div_self hΦ, one_smul]

private lemma gcPathL_norm (P₁ P₂ : F) {Φ : ℝ} (h1 : ‖P₁‖ = 1) (h2 : ‖P₂‖ = 1)
    (hΦ0 : 0 < Φ) (hΦπ : Φ < Real.pi) (hcos : Inner.inner ℝ P₁ P₂ = Real.cos Φ) (s : ℝ) :
    ‖gcPathL P₁ P₂ Φ s‖ = 1 :=
  Commons.Analysis.InnerProductSpace.great_circle_norm P₁ P₂ Φ s h1 h2 hΦ0 hΦπ hcos

private lemma gcPathL_hasDerivAt (P₁ P₂ : F) {Φ : ℝ} (s : ℝ) :
    HasDerivAt (gcPathL P₁ P₂ Φ)
      (((Real.cos ((1 - s) * Φ) * -Φ) / Real.sin Φ) • P₁
        + ((Real.cos (s * Φ) * Φ) / Real.sin Φ) • P₂) s := by
  have h1 : HasDerivAt (fun t : ℝ => (1 - t) * Φ) (-Φ) s := by
    have h := ((hasDerivAt_const (x := s) (c := (1 : ℝ))).sub (hasDerivAt_id s)).mul_const Φ
    simpa using h
  have h2 : HasDerivAt (fun t : ℝ => t * Φ) Φ s := by
    simpa using (hasDerivAt_id s).mul_const Φ
  have h3 : HasDerivAt (fun t : ℝ => Real.sin ((1 - t) * Φ))
      (Real.cos ((1 - s) * Φ) * -Φ) s := (Real.hasDerivAt_sin _).comp s h1
  have h4 : HasDerivAt (fun t : ℝ => Real.sin (t * Φ))
      (Real.cos (s * Φ) * Φ) s := (Real.hasDerivAt_sin _).comp s h2
  have h5 : HasDerivAt (fun t : ℝ => (Real.sin ((1 - t) * Φ) / Real.sin Φ) • P₁)
      (((Real.cos ((1 - s) * Φ) * -Φ) / Real.sin Φ) • P₁) s :=
    (h3.div_const (Real.sin Φ)).smul_const P₁
  have h6 : HasDerivAt (fun t : ℝ => (Real.sin (t * Φ) / Real.sin Φ) • P₂)
      (((Real.cos (s * Φ) * Φ) / Real.sin Φ) • P₂) s :=
    (h4.div_const (Real.sin Φ)).smul_const P₂
  rw [gcPathL_fun]
  exact h5.add h6

/-- **The great-circle path has constant speed `Φ`** (it is the unit-speed path in the sphere of
radius one, parametrised on `[0,1]`). -/
private lemma gcPathL_speed (P₁ P₂ : F) {Φ : ℝ} (h1 : ‖P₁‖ = 1) (h2 : ‖P₂‖ = 1)
    (hcos : Inner.inner ℝ P₁ P₂ = Real.cos Φ) (hΦ0 : 0 < Φ) (hΦπ : Φ < Real.pi) (s : ℝ) :
    ‖((Real.cos ((1 - s) * Φ) * -Φ) / Real.sin Φ) • P₁
        + ((Real.cos (s * Φ) * Φ) / Real.sin Φ) • P₂‖ = Φ := by
  have hsin : 0 < Real.sin Φ := Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ
  have horth := Commons.Analysis.InnerProductSpace.great_circle_orth_norm P₁ P₂ Φ s h1 h2 hcos
  have hvec : ((Real.cos ((1 - s) * Φ) * -Φ) / Real.sin Φ) • P₁
        + ((Real.cos (s * Φ) * Φ) / Real.sin Φ) • P₂
      = Φ • ((Real.sin Φ)⁻¹ •
        (((-Real.cos ((1 - s) * Φ)) • P₁) + ((Real.cos (s * Φ)) • P₂))) := by
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> field_simp <;> ring
  rw [hvec, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hsin), abs_of_pos hΦ0, horth, Real.norm_eq_abs, abs_of_pos hsin]
  field_simp

end GreatCircle

/-- The extended norm of a seminormed group is the `ofReal` of the norm. -/
private lemma enorm_eq_ofReal_norm' {F : Type*} [SeminormedAddCommGroup F] (x : F) :
    ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
  rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]
  simp

/-! ## Two elementary real-inner-product facts

The existence of a unit vector orthogonal to a given unit vector in dimension at least two (this is
the only place where the hypothesis `2 ≤ finrank ℝ E` of the target is used), and the equality cases
of Cauchy–Schwarz in the form `⟪u,u'⟫ = ±1` for unit vectors `u`, `u'`. -/

/-- **A unit vector orthogonal to a given unit vector exists in dimension at least two.**  The
orthogonal complement of `ℝ ∙ u` has dimension `finrank ℝ F - 1 ≥ 1`, so it contains a nonzero
vector, which can be normalised. -/
private theorem exists_unit_orthogonal {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (h2 : 2 ≤ Module.finrank ℝ F) {u : F} (hu : ‖u‖ = 1) :
    ∃ w : F, ‖w‖ = 1 ∧ Inner.inner ℝ u w = 0 := by
  have hune : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; exact one_ne_zero hu.symm
  have hfr : Module.finrank ℝ (↥(ℝ ∙ u)) + Module.finrank ℝ (↥(ℝ ∙ u)ᗮ) = Module.finrank ℝ F :=
    Submodule.finrank_add_finrank_orthogonal _
  have h1 : Module.finrank ℝ (↥(ℝ ∙ u)) = 1 := finrank_span_singleton hune
  have h3 : 0 < Module.finrank ℝ (↥(ℝ ∙ u)ᗮ) := by omega
  haveI : Nontrivial (↥(ℝ ∙ u)ᗮ) := Module.finrank_pos_iff.mp h3
  obtain ⟨v, hv0⟩ := exists_ne (0 : ↥(ℝ ∙ u)ᗮ)
  have hvne : (v : F) ≠ 0 := by
    intro h; exact hv0 (Subtype.ext h)
  refine ⟨‖(v : F)‖⁻¹ • (v : F), ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvne)]
  · rw [inner_smul_right]
    have h0 : Inner.inner ℝ u (v : F) = 0 :=
      (Submodule.mem_orthogonal (ℝ ∙ u) (v : F)).mp v.2 u (Submodule.mem_span_singleton_self u)
    rw [h0, mul_zero]

/-- The equality case `⟪u,u'⟫ = 1` for unit vectors: `u' = u`. -/
private theorem eq_of_inner_eq_one {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u u' : F} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (h : Inner.inner ℝ u u' = 1) : u' = u := by
  have h2 : Inner.inner ℝ u u' = ‖u‖ * ‖u'‖ := by rw [hu, hu', mul_one]; exact h
  have h3 := (inner_eq_norm_mul_iff_real.mp h2)
  rw [hu, hu', one_smul, one_smul] at h3
  exact h3.symm

/-- The equality case `⟪u,u'⟫ = -1` for unit vectors: `u' = -u`. -/
private theorem eq_neg_of_inner_eq_neg_one {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {u u' : F} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (h : Inner.inner ℝ u u' = -1) : u' = -u := by
  have h2 : Inner.inner ℝ u (-u') = ‖u‖ * ‖-u'‖ := by
    rw [inner_neg_right, norm_neg, hu, hu', h]
    ring
  have h3 := (inner_eq_norm_mul_iff_real.mp h2)
  rw [hu, norm_neg, hu', one_smul, one_smul] at h3
  exact neg_eq_iff_eq_neg.mp h3.symm

open Bundle in
/-- **The angle form of the far-sphere path bound.**  Under the hypotheses of the target, except
that the pair `(u,u')` is in the non-degenerate range `-1 < ⟪u,u'⟫ < 1`, the Riemannian distance of
the two points of the radius-`ρ` sphere is bounded by `C` times the angle `arccos ⟪u,u'⟫` between
them.

This is the form in which the bound is proved: the length of the great-circle path joining `u` to
`u'` is exactly `arccos ⟪u,u'⟫`, and the speed of `s ↦ Φ(σ s)` is at most `C` times the speed of
`σ`.  The antipodal case of the target then follows from two applications of this statement with a
half-way unit vector, and the triangle inequality. -/
private theorem far_sphere_path_bound_angle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {ρ C : ℝ} (hρ0 : 0 < ρ) (hC : 0 ≤ C)
    (hdiff : ∀ (u w : TangentSpace I q), ‖u‖ = 1 → Inner.inner ℝ u w = 0 →
      ‖(mfderiv (modelWithCornersSelf ℝ E) I
          (fun x : E => Submission.GlobalExp.GExp (cov := cov) hmet q
            (ρ • (show TangentSpace I q from x)))
          (show E from u)) (show E from w)‖ ≤ C * ‖w‖)
    {u u' : TangentSpace I q} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (hlt : Inner.inner ℝ u u' < 1) (hgt : -1 < Inner.inner ℝ u u') :
    Manifold.riemannianEDist I
        (Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u))
        (Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u'))
      ≤ ENNReal.ofReal (C * Real.arccos (Inner.inner ℝ u u')) := by
  have hle : Inner.inner ℝ u u' ≤ 1 := by
    have h := real_inner_le_norm u u'
    rw [hu, hu', mul_one] at h
    exact h
  have hge : -1 ≤ Inner.inner ℝ u u' := by
    have h := real_inner_le_norm (-u) u'
    rw [inner_neg_left, norm_neg, hu, hu', mul_one] at h
    linarith
  set Φ₀ : ℝ := Real.arccos (Inner.inner ℝ u u') with hΦ₀def
  have hcos : Inner.inner ℝ u u' = Real.cos Φ₀ := (Real.cos_arccos hge hle).symm
  have hΦ₀0 : 0 < Φ₀ := by
    have h : Φ₀ ≠ 0 := by
      intro h
      rw [hΦ₀def] at h
      exact absurd (Real.arccos_eq_zero.mp h) (not_le.mpr hlt)
    exact lt_of_le_of_ne (Real.arccos_nonneg _) (Ne.symm h)
  have hΦ₀π : Φ₀ < Real.pi := by
    have h : Φ₀ ≠ Real.pi := by
      intro h
      rw [hΦ₀def] at h
      exact absurd (Real.arccos_eq_pi.mp h) (not_le.mpr hgt)
    exact lt_of_le_of_ne (Real.arccos_le_pi _) h
  have hsin : 0 < Real.sin Φ₀ := Real.sin_pos_of_pos_of_lt_pi hΦ₀0 hΦ₀π
  have hsinne : Real.sin Φ₀ ≠ 0 := ne_of_gt hsin
  let σ : ℝ → TangentSpace I q := gcPathL u u' Φ₀
  have hσnorm : ∀ s : ℝ, ‖σ s‖ = 1 :=
    fun s => gcPathL_norm u u' hu hu' hΦ₀0 hΦ₀π hcos s
  let σd : ℝ → TangentSpace I q :=
    fun s => ((Real.cos ((1 - s) * Φ₀) * -Φ₀) / Real.sin Φ₀) • u
      + ((Real.cos (s * Φ₀) * Φ₀) / Real.sin Φ₀) • u'
  have hσspeed : ∀ s : ℝ, ‖σd s‖ = Φ₀ :=
    fun s => gcPathL_speed u u' hu hu' hcos hΦ₀0 hΦ₀π s
  have hσderiv : ∀ s : ℝ, HasDerivAt σ (σd s) s := fun s => gcPathL_hasDerivAt u u' s
  have hσ0 : σ 0 = u := gcPathL_zero u u' hsinne
  have hσ1 : σ 1 = u' := gcPathL_one u u' hsinne
  -- The great circle has unit norm, so its velocity is orthogonal to it.
  have hσorth : ∀ s : ℝ, Inner.inner ℝ (σ s) (σd s) = 0 := by
    intro s
    have hder : HasDerivAt (fun t : ℝ => Inner.inner ℝ (σ t) (σ t))
        (Inner.inner ℝ (σ s) (σd s) + Inner.inner ℝ (σd s) (σ s)) s :=
      HasDerivAt.inner ℝ (hσderiv s) (hσderiv s)
    have hconst : (fun t : ℝ => Inner.inner ℝ (σ t) (σ t)) = fun _ => (1 : ℝ) := by
      funext t
      rw [real_inner_self_eq_norm_sq, hσnorm t]
      norm_num
    have h0 : HasDerivAt (fun t : ℝ => Inner.inner ℝ (σ t) (σ t)) 0 s := by
      rw [hconst]
      exact hasDerivAt_const s 1
    have hz : Inner.inner ℝ (σ s) (σd s) + Inner.inner ℝ (σd s) (σ s) = 0 := hder.unique h0
    have hcomm : Inner.inner ℝ (σd s) (σ s) = Inner.inner ℝ (σ s) (σd s) := real_inner_comm _ _
    linarith
  -- The parametrisation `u ↦ GExp q (ρ • u)` of the sphere, and its smoothness.
  let Φ : E → M := fun x => Submission.GlobalExp.GExp (cov := cov) hmet q
    (ρ • (show TangentSpace I q from x))
  have hΦat : ∀ x : E, ContMDiffAt (modelWithCornersSelf ℝ E) I 1 Φ x := by
    intro x
    have hG : ContMDiffAt (modelWithCornersSelf ℝ E) I 1
        (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet q
          (show TangentSpace I q from w))
        (show E from (ρ • (show TangentSpace I q from x))) :=
      (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet q
        (ρ • (show TangentSpace I q from x))).of_le (by simp)
    have hlin : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) 1
        (fun y : E => ρ • y) x := by
      rw [contMDiffAt_iff_contDiffAt]
      fun_prop
    exact ContMDiffAt.comp x hG hlin
  have hΦmd : ∀ x : E, MDifferentiableAt (modelWithCornersSelf ℝ E) I Φ x :=
    fun x => (hΦat x).mdifferentiableAt (by norm_num)
  let fE : ℝ → E := fun s => (show E from σ s)
  have hfEsmooth : ContDiff ℝ 1 fE := by
    dsimp only [fE]
    simp only [σ, gcPathL]
    fun_prop
  let γ : ℝ → M := Φ ∘ fE
  have hfEderiv : ∀ t : ℝ, HasDerivAt fE (show E from σd t) t := by
    intro t
    have h := ((tangentSpaceCastModel I q).hasFDerivAt (x := σ t)).comp_hasDerivAt t (hσderiv t)
    exact h
  -- The pointwise bound on the speed of `Φ ∘ σ`.
  have hpt : ∀ t : ℝ, ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I γ t)
      (1 : TangentSpace (modelWithCornersSelf ℝ ℝ) t)‖ ≤ C * Φ₀ := by
    intro t
    have hfEmd : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E) fE t :=
      (mdifferentiableAt_iff_differentiableAt).mpr (hfEderiv t).differentiableAt
    have h1 : (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t)
          (1 : TangentSpace (modelWithCornersSelf ℝ ℝ) t)
        = (mfderiv (modelWithCornersSelf ℝ E) I Φ (show E from σ t)) (show E from σd t) := by
      have hcomp := mfderiv_comp_apply (g := Φ) (f := fE) t (hΦmd (show E from σ t)) hfEmd 1
      rw [hcomp]
      congr 1
      rw [mfderiv_eq_fderiv]
      show (fderiv ℝ fE t) (1 : ℝ) = (show E from σd t)
      rw [fderiv_apply_one_eq_deriv]
      exact (hfEderiv t).deriv
    rw [h1]
    calc ‖(mfderiv (modelWithCornersSelf ℝ E) I Φ (show E from σ t)) (show E from σd t)‖
        ≤ C * ‖σd t‖ := hdiff (σ t) (σd t) (hσnorm t) (hσorth t)
      _ = C * Φ₀ := by rw [hσspeed t]
  have hγsm : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc (0:ℝ) 1) := by
    have hΦsm : ContMDiff (modelWithCornersSelf ℝ E) I 1 Φ := hΦat
    have hfEsm : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E) 1 fE
        (Set.Icc (0:ℝ) 1) :=
      (contMDiffOn_iff_contDiffOn).mpr hfEsmooth.contDiffOn
    exact ContMDiffOn.comp (t := Set.univ) hΦsm.contMDiffOn hfEsm (by intro x hx; trivial)
  have hγ0 : γ 0 = Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u) := by
    have h0 : fE 0 = (show E from u) := by
      change (show E from σ 0) = (show E from u)
      rw [hσ0]
    change Φ (fE 0) = Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u)
    rw [h0]
  have hγ1 : γ 1 = Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u') := by
    have h0 : fE 1 = (show E from u') := by
      change (show E from σ 1) = (show E from u')
      rw [hσ1]
    change Φ (fE 1) = Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u')
    rw [h0]
  have hle1 : Manifold.riemannianEDist I (γ 0) (γ 1) ≤ Manifold.pathELength I γ 0 1 :=
    Manifold.riemannianEDist_le_pathELength (I := I) (γ := γ) hγsm rfl rfl (by norm_num)
  have hle2 : Manifold.pathELength I γ 0 1 ≤ ENNReal.ofReal (C * Φ₀) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    calc ∫⁻ t in Set.Icc (0:ℝ) 1, ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I γ t)
            (1 : TangentSpace (modelWithCornersSelf ℝ ℝ) t)‖ₑ
        ≤ ∫⁻ _t in Set.Icc (0:ℝ) 1, ENNReal.ofReal (C * Φ₀) := by
          apply setLIntegral_mono measurable_const
          intro t ht
          rw [enorm_eq_ofReal_norm']
          exact ENNReal.ofReal_le_ofReal (hpt t)
      _ = ENNReal.ofReal (C * Φ₀) := by
          rw [setLIntegral_const, Real.volume_Icc]
          norm_num
  have hfin : Manifold.riemannianEDist I (γ 0) (γ 1) ≤ ENNReal.ofReal (C * Φ₀) :=
    le_trans hle1 hle2
  rw [hγ0, hγ1] at hfin
  rw [hΦ₀def] at hfin
  exact hfin

open Bundle in
/-- **The far-sphere distance bound along the great circle** (dimension at least two).

Let `q : M`, `ρ > 0`, `2 ≤ finrank ℝ E`, and suppose (hypothesis `hdiff`, supplied in the application
by `Work.Diff.C.GExp_radius_mfderiv_bound`) that the differential of `Φ u = GExp q (ρ • u)` in the
unit-sphere directions is bounded by a constant `C ≥ 0`:

`‖ⅆΦ(u)[w]‖ ≤ C ‖w‖` for `‖u‖ = 1`, `w ⊥ u`.

Then for unit `u, u' : T_qM`

`rdist (GExp q (ρ • u)) (GExp q (ρ • u')) ≤ C · π`.

The hypothesis `2 ≤ finrank ℝ E` is necessary: in dimension one the unit sphere is `{±u}` (not
connected), the only orthogonal `w` is `0`, so `hdiff` is vacuous, while on a circle two antipodal
rays give `rdist = 2ρ > 0`.

Proof: the radius-`ρ` exponential map of a great circle.  Let `Φ₀ := arccos ⟪u,u'⟫ ∈ [0,π]`; for
`Φ₀ ∈ (0,π)` the path `σ s = (sin((1-s)Φ₀)/sin Φ₀) • u + (sin(s Φ₀)/sin Φ₀) • u'` of
`Work.Diff.C.gcPath` (in the module `Submission.Work.Diff.C.far_sphere_diameter`) stays on the unit
sphere (`Work.Diff.C.gcPath_norm`), joins `u` to `u'` (`gcPath_zero`, `gcPath_one`), has derivative
`gcPath_hasDerivAt` and constant speed `Φ₀` (`gcPath_speed`).  Since `‖σ s‖ = 1` forces `σ' s ⊥ σ s`,
the curve `s ↦ Φ(σ s)` has speed `≤ C Φ₀`, and
`rdist x x' ≤ pathELength = ∫ ‖(Φ ∘ σ)'‖ ≤ C Φ₀ ≤ C π`
(`Manifold.riemannianEDist_le_pathELength`, `Manifold.pathELength_eq_lintegral_mfderiv_Icc`).  The
cases `u = u'` (trivial) and `Φ₀ = π` (use a semicircle through any unit vector orthogonal to `u`,
which exists in dimension `≥ 2`, and the triangle inequality) are separate. -/
theorem far_sphere_path_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {q : M} {ρ C : ℝ} (hρ0 : 0 < ρ) (hC : 0 ≤ C)
    (hdiff : ∀ (u w : TangentSpace I q), ‖u‖ = 1 → Inner.inner ℝ u w = 0 →
      ‖(mfderiv (modelWithCornersSelf ℝ E) I
          (fun x : E => Submission.GlobalExp.GExp (cov := cov) hmet q
            (ρ • (show TangentSpace I q from x)))
          (show E from u)) (show E from w)‖ ≤ C * ‖w‖)
    {u u' : TangentSpace I q} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) :
    Work.Diff.C.rdist (I := I) (M := M)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u))
        (Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u'))
      ≤ C * Real.pi := by
  have hupper : Inner.inner ℝ u u' ≤ 1 := by
    have h := real_inner_le_norm u u'
    rw [hu, hu', mul_one] at h
    exact h
  have hlower : -1 ≤ Inner.inner ℝ u u' := by
    have h := real_inner_le_norm (-u) u'
    rw [inner_neg_left, norm_neg, hu, hu', mul_one] at h
    linarith
  by_cases h1 : Inner.inner ℝ u u' = 1
  · -- the coincident case: the two points are equal
    have huu : u' = u := eq_of_inner_eq_one hu hu' h1
    rw [huu]
    have h0 : Work.Diff.C.rdist (I := I) (M := M)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u))
        (Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u)) = 0 := by
      simp [Work.Diff.C.rdist, Manifold.riemannianEDist_self]
    rw [h0]
    exact mul_nonneg hC Real.pi_pos.le
  by_cases h2 : Inner.inner ℝ u u' = -1
  · -- the antipodal case: go through a unit vector orthogonal to `u`, and use the triangle inequality
    have huu : u' = -u := eq_neg_of_inner_eq_neg_one hu hu' h2
    haveI : Nontrivial (TangentSpace I q) := ‹Nontrivial E›
    have hfr : 2 ≤ Module.finrank ℝ (TangentSpace I q) := by
      rw [(tangentSpaceCastModel I q).toLinearEquiv.finrank_eq]
      exact hdim
    obtain ⟨w, hw1, hw0⟩ := exists_unit_orthogonal hfr hu
    have hwlt : Inner.inner ℝ u w < 1 := by rw [hw0]; norm_num
    have hwgt : -1 < Inner.inner ℝ u w := by rw [hw0]; norm_num
    have ha := far_sphere_path_bound_angle (E := E) (H := H) (I := I) (M := M)
      (cov := cov) hmet htor hρ0 hC hdiff hu hw1 hwlt hwgt
    rw [hw0, Real.arccos_zero] at ha
    have hw0' : Inner.inner ℝ w u' = 0 := by
      rw [huu, inner_neg_right, real_inner_comm u w, hw0, neg_zero]
    have hwlt' : Inner.inner ℝ w u' < 1 := by rw [hw0']; norm_num
    have hwgt' : -1 < Inner.inner ℝ w u' := by rw [hw0']; norm_num
    have hb := far_sphere_path_bound_angle (E := E) (H := H) (I := I) (M := M)
      (cov := cov) hmet htor hρ0 hC hdiff hw1 hu' hwlt' hwgt'
    rw [hw0', Real.arccos_zero] at hb
    have htri := Manifold.riemannianEDist_triangle (I := I)
      (x := Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u))
      (y := Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • w))
      (z := Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u'))
    have hsum : Manifold.riemannianEDist I
          (Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u))
          (Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u'))
        ≤ ENNReal.ofReal (C * (Real.pi / 2)) + ENNReal.ofReal (C * (Real.pi / 2)) :=
      le_trans htri (add_le_add ha hb)
    rw [← ENNReal.ofReal_add (mul_nonneg hC (by positivity)) (mul_nonneg hC (by positivity)),
      show C * (Real.pi / 2) + C * (Real.pi / 2) = C * Real.pi by ring] at hsum
    have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
    rw [ENNReal.toReal_ofReal (mul_nonneg hC Real.pi_pos.le)] at hto
    rw [Work.Diff.C.rdist]
    exact hto
  · -- the generic case: `Φ₀ ∈ (0,π)`
    have hlt : Inner.inner ℝ u u' < 1 := lt_of_le_of_ne hupper h1
    have hgt : -1 < Inner.inner ℝ u u' := lt_of_le_of_ne hlower (Ne.symm h2)
    have hangle := far_sphere_path_bound_angle (E := E) (H := H) (I := I) (M := M)
      (cov := cov) hmet htor hρ0 hC hdiff hu hu' hlt hgt
    have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hangle
    rw [ENNReal.toReal_ofReal (mul_nonneg hC (Real.arccos_nonneg _))] at hto
    rw [Work.Diff.C.rdist]
    exact le_trans hto (mul_le_mul_of_nonneg_left (Real.arccos_le_pi _) hC)

end Work.Diff.C.RadialBound
