import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs

set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

-- NOTE for the prover: Goal: the flow line `s ↦ Φ 0 s y` moves the `p`-distance at speed at most 1
-- when `‖V‖ ≤ 1`.  Route: `Manifold.riemannianEDist I (Φ 0 s y) (Φ 0 s' y) ≤
-- Manifold.pathELength I (fun u => Φ 0 (s + u * (s' - s)) y) 0 1`
-- (`Submission.EDist.riemannianEDist_le_pathELength`, see `Submission/HingeUniform.lean:438` for a
-- worked instance) plus `Manifold.pathELength_eq_lintegral_mfderiv_Icc` + `hΦderiv` + `hV1` to bound
-- that length by `ofReal |s - s'|`.
-- WARNING (both reviewers): do NOT cite `Work.Diff.C.rdist_lipschitz` — it needs
-- `Submission.HopfRinow.riemannianEDist_lt_top` (i.e. a `cov` with `hmet`/`htor`), which is absent
-- here.  Instead: from `riemannianEDist (Φ 0 s y) (Φ 0 s' y) ≤ ofReal |s - s'| < ⊤` deduce by the
-- (unconditional) triangle inequality that `riemannianEDist p (Φ 0 s y) = ⊤ ↔
-- riemannianEDist p (Φ 0 s' y) = ⊤`, and handle the two cases (`toReal` of `⊤` is `0`, and in the
-- finite case use `ENNReal.toReal_le_toReal` / `ENNReal.toReal_sub` on the two triangle inequalities).
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- **Distance bookkeeping for a pair of points at bounded Riemannian distance.**

If `a` and `b` are at extended Riemannian distance at most `ofReal c` (with `c ≥ 0`), then the real
`p`-distances of `a` and `b` differ by at most `c`.  The point is that `ENNReal.toReal` is *not*
monotone, so one first has to observe (from the unconditional triangle inequality) that
`riemannianEDist I p a = ⊤ ↔ riemannianEDist I p b = ⊤`; in the infinite case both `toReal` are
`0`, in the finite case monotonicity of `toReal` plus additivity on finite values applies. -/
private theorem edist_toReal_sub_le_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [(x : M) → ENorm (TangentSpace I x)] [(x : M) → ENormSMulClass ℝ (TangentSpace I x)]
    {p a b : M} {c : ℝ} (hc : 0 ≤ c)
    (h : Manifold.riemannianEDist I a b ≤ ENNReal.ofReal c) :
    |(Manifold.riemannianEDist I p a).toReal - (Manifold.riemannianEDist I p b).toReal| ≤ c := by
  have hDfin : Manifold.riemannianEDist I a b ≠ ⊤ :=
    (lt_of_le_of_lt h ENNReal.ofReal_lt_top).ne
  have htri1 : Manifold.riemannianEDist I p a ≤
      Manifold.riemannianEDist I p b + Manifold.riemannianEDist I a b := by
    calc Manifold.riemannianEDist I p a
        ≤ Manifold.riemannianEDist I p b + Manifold.riemannianEDist I b a :=
          Manifold.riemannianEDist_triangle
      _ = Manifold.riemannianEDist I p b + Manifold.riemannianEDist I a b := by
          rw [Manifold.riemannianEDist_comm (I := I) (x := b) (y := a)]
  have htri2 : Manifold.riemannianEDist I p b ≤
      Manifold.riemannianEDist I p a + Manifold.riemannianEDist I a b :=
    Manifold.riemannianEDist_triangle
  rcases eq_or_ne (Manifold.riemannianEDist I p a) ⊤ with hA | hA
  · have hB : Manifold.riemannianEDist I p b = ⊤ := by
      by_contra hBne
      have hlt : Manifold.riemannianEDist I p b + Manifold.riemannianEDist I a b < ⊤ :=
        ENNReal.add_lt_top.mpr
          ⟨lt_top_iff_ne_top.mpr hBne, lt_top_iff_ne_top.mpr hDfin⟩
      rw [hA] at htri1
      exact absurd (htri1.trans_lt hlt) (lt_irrefl _)
    rw [hA, hB, ENNReal.toReal_top]
    simpa using hc
  · have hAlt : Manifold.riemannianEDist I p a < ⊤ := lt_top_iff_ne_top.mpr hA
    have hDlt : Manifold.riemannianEDist I a b < ⊤ := lt_top_iff_ne_top.mpr hDfin
    have hBne : Manifold.riemannianEDist I p b ≠ ⊤ := by
      intro hBtop
      rw [hBtop] at htri2
      have hlt : Manifold.riemannianEDist I p a + Manifold.riemannianEDist I a b < ⊤ :=
        ENNReal.add_lt_top.mpr ⟨hAlt, hDlt⟩
      exact absurd (htri2.trans_lt hlt) (lt_irrefl _)
    have hBlt : Manifold.riemannianEDist I p b < ⊤ := lt_top_iff_ne_top.mpr hBne
    have e1 : (Manifold.riemannianEDist I p a).toReal ≤
        (Manifold.riemannianEDist I p b).toReal
          + (Manifold.riemannianEDist I a b).toReal := by
      have h2 := ENNReal.toReal_mono (ENNReal.add_lt_top.mpr ⟨hBlt, hDlt⟩).ne htri1
      rwa [ENNReal.toReal_add hBne hDfin] at h2
    have e2 : (Manifold.riemannianEDist I p b).toReal ≤
        (Manifold.riemannianEDist I p a).toReal
          + (Manifold.riemannianEDist I a b).toReal := by
      have h2 := ENNReal.toReal_mono (ENNReal.add_lt_top.mpr ⟨hAlt, hDlt⟩).ne htri2
      rwa [ENNReal.toReal_add hA hDfin] at h2
    have hDc : (Manifold.riemannianEDist I a b).toReal ≤ c :=
      ENNReal.toReal_le_of_le_ofReal hc h
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem flow_lip_f
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {p : M} {V : (x : M) → TangentSpace I x}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hV1 : ∀ y : M, ‖V y‖ ≤ 1)
    {Φ : ℝ → ℝ → M → M}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x)))) :
    ∀ y : M, ∀ s s' : ℝ,
      |Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s y)
        - Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s' y)| ≤ |s - s'| := by
  intro y s s'
  -- ## The flow line `G : t ↦ Φ 0 t y` is smooth
  have hGsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => Φ 0 t y) := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun t : ℝ => (((0 : ℝ), t) : ℝ × ℝ)) :=
      ContMDiff.prodMk (contMDiff_const (c := (0 : ℝ))) (contMDiff_id (I := 𝓘(ℝ, ℝ)))
    have h2 : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) ∞
        (fun t : ℝ => ((((0 : ℝ), t) : ℝ × ℝ), y)) :=
      ContMDiff.prodMk h1 (contMDiff_const (c := y))
    exact hΦsm.comp h2
  -- ## The reparametrised curve `γ u = Φ 0 (s + u (s' - s)) y` joining the two points
  set γ : ℝ → M := fun u : ℝ => Φ 0 (s + u * (s' - s)) y with hγ
  have hγsm : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc (0 : ℝ) 1) := by
    have haff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun u : ℝ => s + u * (s' - s)) :=
      contMDiff_const.add (contMDiff_id.mul contMDiff_const)
    exact (((hGsm.comp haff).contMDiffOn).mono (Set.subset_univ _)).of_le (by simp)
  have hγ0 : γ 0 = Φ 0 s y := by simp [hγ]
  have hγ1 : γ 1 = Φ 0 s' y := by simp [hγ]
  -- ## Length of the curve bounds the extended distance
  have hdist : Manifold.riemannianEDist I (Φ 0 s y) (Φ 0 s' y) ≤
      Manifold.pathELength I γ 0 1 :=
    Manifold.riemannianEDist_le_pathELength (I := I) (γ := γ) (x := Φ 0 s y) (y := Φ 0 s' y)
      (a := 0) (b := 1) hγsm hγ0 hγ1 zero_le_one
  -- ## The speed of `γ` is at most `|s - s'|`
  have hpoint : ∀ u : ℝ, ‖(mfderiv 𝓘(ℝ, ℝ) I γ u) (1 : ℝ)‖ₑ ≤ ENNReal.ofReal |s - s'| := by
    intro u
    have hgd : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t : ℝ => Φ 0 t y) (s + u * (s' - s))
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (s + u * (s' - s)) y))) := hΦderiv 0 _ y
    have hfd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun v : ℝ => s + v * (s' - s)) u
        (ContinuousLinearMap.toSpanSingleton ℝ (s' - s)) := by
      have hd : HasDerivAt (fun v : ℝ => s + v * (s' - s)) (s' - s) u := by
        have h := ((hasDerivAt_id u).mul_const (s' - s)).const_add s
        have h2 : (fun x : ℝ => s + id x * (s' - s)) = fun v : ℝ => s + v * (s' - s) := by
          funext v; simp
        rw [h2] at h
        simpa using h
      exact hd.hasFDerivAt.hasMFDerivAt
    have hcomp := hgd.comp u hfd
    have hmf : mfderiv 𝓘(ℝ, ℝ) I γ u
        = ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (s + u * (s' - s)) y))) ∘SL
          (ContinuousLinearMap.toSpanSingleton ℝ (s' - s)) := by
      rw [hγ]
      exact hcomp.mfderiv
    have hval : (mfderiv 𝓘(ℝ, ℝ) I γ u) (1 : ℝ)
        = (s' - s) • V (Φ 0 (s + u * (s' - s)) y) := by
      rw [hmf]
      show ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (s + u * (s' - s)) y)))
          ((ContinuousLinearMap.toSpanSingleton ℝ (s' - s)) (1 : ℝ))
        = (s' - s) • V (Φ 0 (s + u * (s' - s)) y)
      simp
    rw [hval, ← Real.enorm_eq_ofReal_abs (s - s'), enorm_le_iff_norm_le]
    rw [norm_smul, Real.norm_eq_abs, abs_sub_comm s' s]
    calc |s - s'| * ‖V (Φ 0 (s + u * (s' - s)) y)‖ ≤ |s - s'| * 1 :=
          mul_le_mul_of_nonneg_left (hV1 _) (abs_nonneg _)
      _ = |s - s'| := mul_one _
  -- ## Hence the path length is at most `|s - s'|`
  have hpl : Manifold.pathELength I γ 0 1 ≤ ENNReal.ofReal |s - s'| := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have h1 : ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(mfderiv 𝓘(ℝ, ℝ) I γ t) (1 : ℝ)‖ₑ
        ≤ ∫⁻ _t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal |s - s'| :=
      MeasureTheory.lintegral_mono_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with u _hu
        exact hpoint u)
    have h2 : ∫⁻ _t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal |s - s'|
        = ENNReal.ofReal |s - s'| := by
      rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
      norm_num
    exact h1.trans_eq h2
  -- ## Assemble
  refine edist_toReal_sub_le_aux (I := I) (M := M) (p := p) (a := Φ 0 s y) (b := Φ 0 s' y)
    (c := |s - s'|) (abs_nonneg _) ?_
  exact hdist.trans hpl

end Work.Diff.Dim2
