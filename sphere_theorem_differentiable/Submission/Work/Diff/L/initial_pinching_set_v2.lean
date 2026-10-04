import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.PinchUniform
import Submission.CurvatureVec
import Submission.CurvatureSym
import Submission.Curvature
import Submission.Pinch
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.L.secK_rmFrame_eq_inner
import Submission.Work.Diff.L.R4_rmFrame_initSMet_eq
import Submission.Work.Diff.L.lc_eq_cov
import Submission.Work.Diff.L.rmVec_lcOf_initSMet_eq_cov
import Submission.Work.Diff.GE.scal_lapl_basic
import Submission.Work.Diff.L.exists_curv4_norm_bound_v2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The initial pinching set for the Brendle–Schoen sphere theorem (assembly copy)

`Work.Diff.L.initial_pinching_set_v2`: for a compact manifold with a smooth torsion-free
metric-compatible connection `cov` which is strictly quarter-pinched (`1 < K ≤ 4`, i.e. Knill's
`QuarterPinched`), there is a Böhm–Wilking **pinching set** `F` containing the curvature of the
ambient (instance) metric in every orthonormal frame.

This is "step 0" of the Brendle–Schoen route (see `HANDOFF.md`):

* `cov` is the Levi-Civita connection of the instance metric (packaged as `initSMet`), so the
  curvature arrays `rmFrame (initSMet) x e` are the curvature arrays of `cov`
  (`Work.Diff.L.lc_eq_cov`, `Work.Diff.L.rmVec_lcOf_initSMet_eq_cov`);
* those arrays are algebraic curvature tensors (`Work.Diff.L.isAlgCurv_rmFrame_initSMet`) and,
  over all `x` and all orthonormal frames `e`, form a **bounded** set of tensors: their sectional
  curvatures on orthonormal pairs are `> 1` and `≤ 4` by `QuarterPinched` (transported through
  `Work.Diff.L.secK_rmFrame_eq_inner` and `curvVec`), and
  `Work.Diff.L.exists_curv4_norm_bound` turns that into a bound on the tensor norm;
* the closed set
  `K = {R | IsAlgCurv R, a ≤ secK R u v, secK R u v ≤ 4 on orthonormal pairs, ‖R‖ ≤ C}`
  (`a > 1` the *uniform strict* lower pinching constant of `Submission.PinchUniform`) is therefore
  compact and contains all curvature arrays; every `R ∈ K` is strictly quarter-pinched with the
  constant `c = 1`, so `QuarterToPIC2` gives `∃ ε > 0, InPIC2 (R - ε • Iso n)`;
* `PinchingSetExists` applied to `K` produces the pinching set `F ⊇ K`, and `CurvIn` follows
  because `K` contains all curvature arrays.

The strictness of `a` is what makes the closedness argument work: `a > 1` gives the *closed* pinching
condition `{a ≤ secK R u v}` a strict margin relative to `c = 1` in `QuarterToPIC2`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-! ## Elementary closedness lemmas for the tensor conditions -/

/-- The set of algebraic curvature tensors is closed. -/
private theorem isClosed_setOf_isAlgCurv (n : ℕ) : IsClosed {R : Curv4 n | IsAlgCurv R} := by
  have h1 : {R : Curv4 n | ∀ i j k l : Fin n, R j i k l = -R i j k l}
      = ⋂ i, ⋂ j, ⋂ k, ⋂ l, {R : Curv4 n | R j i k l = -R i j k l} := by
    ext R; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have h2 : {R : Curv4 n | ∀ i j k l : Fin n, R k l i j = R i j k l}
      = ⋂ i, ⋂ j, ⋂ k, ⋂ l, {R : Curv4 n | R k l i j = R i j k l} := by
    ext R; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have h3 : {R : Curv4 n | ∀ i j k l : Fin n, R i j k l + R j k i l + R k i j l = 0}
      = ⋂ i, ⋂ j, ⋂ k, ⋂ l, {R : Curv4 n | R i j k l + R j k i l + R k i j l = 0} := by
    ext R; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have h : {R : Curv4 n | IsAlgCurv R}
      = ({R : Curv4 n | ∀ i j k l : Fin n, R j i k l = -R i j k l}
          ∩ {R : Curv4 n | ∀ i j k l : Fin n, R k l i j = R i j k l})
        ∩ {R : Curv4 n | ∀ i j k l : Fin n, R i j k l + R j k i l + R k i j l = 0} := by
    ext R
    simp only [IsAlgCurv, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [h, h1, h2, h3]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_ <;>
    refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_iInter fun l => isClosed_eq ?_ ?_ <;> fun_prop

/-- The set of arrays whose sectional curvature on orthonormal pairs is bounded below by `c`. -/
private theorem isClosed_setOf_secK_ge (n : ℕ) (c : ℝ) :
    IsClosed {R : Curv4 n | ∀ u v : Fin n → ℝ, IsONPair u v → c ≤ secK R u v} := by
  rw [show {R : Curv4 n | ∀ u v : Fin n → ℝ, IsONPair u v → c ≤ secK R u v}
      = ⋂ u, ⋂ v, {R : Curv4 n | IsONPair u v → c ≤ secK R u v} from by
    ext R; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
  refine isClosed_iInter fun u => isClosed_iInter fun v => ?_
  by_cases huv : IsONPair u v
  · rw [show {R : Curv4 n | IsONPair u v → c ≤ secK R u v} = {R | c ≤ secK R u v} from by
      ext R; simp [huv]]
    exact isClosed_le continuous_const (by unfold secK R4; fun_prop)
  · rw [show {R : Curv4 n | IsONPair u v → c ≤ secK R u v} = Set.univ from by
      ext R; simp [huv]]
    exact isClosed_univ

/-- The set of arrays whose sectional curvature on orthonormal pairs is bounded above by `c`. -/
private theorem isClosed_setOf_secK_le (n : ℕ) (c : ℝ) :
    IsClosed {R : Curv4 n | ∀ u v : Fin n → ℝ, IsONPair u v → secK R u v ≤ c} := by
  rw [show {R : Curv4 n | ∀ u v : Fin n → ℝ, IsONPair u v → secK R u v ≤ c}
      = ⋂ u, ⋂ v, {R : Curv4 n | IsONPair u v → secK R u v ≤ c} from by
    ext R; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
  refine isClosed_iInter fun u => isClosed_iInter fun v => ?_
  by_cases huv : IsONPair u v
  · rw [show {R : Curv4 n | IsONPair u v → secK R u v ≤ c} = {R | secK R u v ≤ c} from by
      ext R; simp [huv]]
    exact isClosed_le (by unfold secK R4; fun_prop) continuous_const
  · rw [show {R : Curv4 n | IsONPair u v → secK R u v ≤ c} = Set.univ from by
      ext R; simp [huv]]
    exact isClosed_univ

/-! ## The coordinate pairing of an orthonormal frame -/

/-- The pairing of two combinations of an orthonormal frame is the `dot` pairing of the
coefficients. -/
private theorem inner_comb_comb (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : IsONFrame (initSMet (I := I) (M := M)) x e)
    (u v : Fin (Module.finrank ℝ E) → ℝ) :
    inner ℝ (∑ i, u i • e i) (∑ i, v i • e i) = dot u v := by
  have hframe : ∀ i j : Fin (Module.finrank ℝ E),
      inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have h := he i j
    rw [initSMet_inner] at h
    exact h
  have hexp : inner ℝ (∑ i, u i • e i) (∑ i, v i • e i)
      = ∑ i, ∑ j, v i * (u j * inner ℝ (e j) (e i)) := by
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [hexp]
  have hinner : ∀ i : Fin (Module.finrank ℝ E),
      (∑ j, v i * (u j * inner ℝ (e j) (e i))) = v i * u i := by
    intro i
    have hcongr : ∀ j, v i * (u j * inner ℝ (e j) (e i)) = (if j = i then v i * u i else 0) := by
      intro j
      rw [hframe j i]
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [Finset.sum_congr rfl (fun j _ => hcongr j), Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  simp only [dot]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ## The pointwise upper pinching bound for the curvature of `cov` -/

/-- `QuarterPinched` gives the upper bound `≤ 4` for the sectional curvatures of `curvVec` on
orthonormal pairs. -/
private theorem curvVec_secK_le_four (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (hpinch : QuarterPinched cov) (p : M) (u v : TangentSpace I p)
    (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0) :
    inner ℝ (Submission.CurvatureVec.curvVec cov p u v v) u ≤ 4 := by
  obtain ⟨X, hX, hXp⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYp⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  have hpin := (hpinch X Y hX hY p (by rw [hXp]; exact hu) (by rw [hYp]; exact hv)
    (by rw [hXp, hYp]; exact huv)).2
  rw [← Submission.CurvatureVec.curvVec_eq cov ‹ContMDiffCovariantDerivative cov ∞› hX hY hY
    hXp hYp hYp, hXp] at hpin
  exact hpin
/-! ## The main theorem -/

theorem initial_pinching_set_v2
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov)
    (hLC : LCSmooth I M) (hA0 : QuarterToPIC2 (Module.finrank ℝ E))
    (hA1 : PinchingSetExists (Module.finrank ℝ E)) :
    ∃ F : Set (Curv4 (Module.finrank ℝ E)), IsPinchingSet F ∧ CurvIn (initSMet (I := I) (M := M)) F
    := by
  classical
  set g₀ : SMet I M := initSMet (I := I) (M := M) with hg₀
  -- the smoothness instance for `lcOf g₀`, from the frozen contract `LCSmooth`
  obtain ⟨hconn₀, -, -⟩ := hLC g₀
  obtain ⟨hcov₀⟩ := hconn₀
  -- the uniform strict lower pinching constant for `cov`
  have hunif : ∃ a : ℝ, 1 < a ∧ ∀ (p : M) (u v : TangentSpace I p),
      inner ℝ u u = 1 → inner ℝ v v = 1 → inner ℝ u v = 0 →
      a < inner ℝ (Submission.CurvatureVec.curvVec cov p u v v) u := by
    by_cases hM : Nonempty M
    · haveI : Nonempty M := hM
      haveI : Nontrivial E :=
        Module.finrank_pos_iff.mp (Nat.lt_of_lt_of_le Nat.zero_lt_two hdim)
      exact Submission.PinchUniform.exists_uniform_lt_curvVec (cov := cov) hmet hpinch htor
    · refine ⟨2, by norm_num, fun p => absurd ⟨p⟩ hM⟩
  obtain ⟨a, ha1, halow⟩ := hunif
  -- the algebraic norm bound for algebraic curvature tensors with `|secK| ≤ 4`
  obtain ⟨C, hC⟩ := exists_curv4_norm_bound_v2 (n := Module.finrank ℝ E) 4
  -- the candidate compact set of curvature arrays
  set K : Set (Curv4 (Module.finrank ℝ E)) :=
    {R | IsAlgCurv R ∧ (∀ u v : Fin (Module.finrank ℝ E) → ℝ, IsONPair u v → a ≤ secK R u v)
      ∧ (∀ u v : Fin (Module.finrank ℝ E) → ℝ, IsONPair u v → secK R u v ≤ 4)
      ∧ ‖R‖ ≤ C} with hK
  have hKclosed : IsClosed K := by
    have hAlg : IsClosed {R : Curv4 (Module.finrank ℝ E) | IsAlgCurv R} :=
      isClosed_setOf_isAlgCurv _
    have hlow : IsClosed {R : Curv4 (Module.finrank ℝ E) |
        ∀ u v : Fin (Module.finrank ℝ E) → ℝ, IsONPair u v → a ≤ secK R u v} :=
      isClosed_setOf_secK_ge _ _
    have hup : IsClosed {R : Curv4 (Module.finrank ℝ E) |
        ∀ u v : Fin (Module.finrank ℝ E) → ℝ, IsONPair u v → secK R u v ≤ 4} :=
      isClosed_setOf_secK_le _ _
    have hnorm : IsClosed {R : Curv4 (Module.finrank ℝ E) | ‖R‖ ≤ C} :=
      isClosed_le continuous_norm continuous_const
    have hthis : K = ({R : Curv4 (Module.finrank ℝ E) | IsAlgCurv R}
        ∩ {R : Curv4 (Module.finrank ℝ E) |
            ∀ u v : Fin (Module.finrank ℝ E) → ℝ, IsONPair u v → a ≤ secK R u v})
        ∩ {R : Curv4 (Module.finrank ℝ E) |
            ∀ u v : Fin (Module.finrank ℝ E) → ℝ, IsONPair u v → secK R u v ≤ 4}
        ∩ {R : Curv4 (Module.finrank ℝ E) | ‖R‖ ≤ C} := by
      rw [hK]
      ext R
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      tauto
    rw [hthis]
    exact IsClosed.inter (IsClosed.inter (IsClosed.inter hAlg hlow) hup) hnorm
  have hKcompact : IsCompact K := by
    refine (isCompact_closedBall (0 : Curv4 (Module.finrank ℝ E)) C).of_isClosed_subset
      hKclosed ?_
    intro R hR
    rw [hK] at hR
    simpa [dist_eq_norm] using hR.2.2.2
  -- every element of `K` satisfies the hypothesis of `PinchingSetExists`
  have hKgood : ∀ R ∈ K, IsAlgCurv R ∧
      ∃ ε : ℝ, 0 < ε ∧ InPIC2 (R - ε • Iso (Module.finrank ℝ E)) := by
    intro R hR
    rw [hK] at hR
    refine ⟨hR.1, hA0 R hR.1 1 (by norm_num) fun u v huv => ⟨?_, ?_⟩⟩
    · have h := hR.2.1 u v huv
      linarith
    · have h := hR.2.2.1 u v huv
      linarith
  -- the curvature arrays of the ambient metric lie in `K`
  have hframes : ∀ (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x),
      IsONFrame g₀ x e → rmFrame g₀ x e ∈ K := by
    intro x e he
    -- combinations of `e` along an orthonormal pair are orthonormal
    have hcomb : ∀ u v : Fin (Module.finrank ℝ E) → ℝ, IsONPair u v →
        inner ℝ (∑ i, u i • e i) (∑ i, u i • e i) = 1 ∧
        inner ℝ (∑ i, v i • e i) (∑ i, v i • e i) = 1 ∧
        inner ℝ (∑ i, u i • e i) (∑ i, v i • e i) = 0 := by
      intro u v huv
      rw [inner_comb_comb x e he u u, inner_comb_comb x e he v v, inner_comb_comb x e he u v]
      exact ⟨huv.1, huv.2.1, huv.2.2⟩
    -- frame expansion of the curvature components, and identification of `cov` with `lcOf g₀`
    have htransfer : ∀ u v : Fin (Module.finrank ℝ E) → ℝ,
        secK (rmFrame g₀ x e) u v
          = inner ℝ (Submission.CurvatureVec.curvVec cov x (∑ i, u i • e i)
              (∑ i, v i • e i) (∑ i, v i • e i)) (∑ i, u i • e i) := by
      intro u v
      rw [secK_rmFrame_eq_inner g₀ x e hcov₀ u v]
      rw [show g₀.inner x (rmVec (lcOf g₀) x (∑ i, u i • e i) (∑ i, v i • e i)
            (∑ i, v i • e i)) (∑ i, u i • e i)
          = inner ℝ (rmVec (lcOf g₀) x (∑ i, u i • e i) (∑ i, v i • e i)
            (∑ i, v i • e i)) (∑ i, u i • e i) from rfl]
      rw [rmVec_lcOf_initSMet_eq_cov cov htor hmet hLC x (∑ i, u i • e i) (∑ i, v i • e i)
        (∑ i, v i • e i)]
      rw [Work.Diff.GE.rmVec_eq_curvVec cov ‹ContMDiffCovariantDerivative cov ∞› x
        (∑ i, u i • e i) (∑ i, v i • e i) (∑ i, v i • e i)]
    rw [hK]
    refine ⟨Work.Diff.GE.isAlgCurv_rmFrame_kit hLC g₀ x e, ?_, ?_, ?_⟩
    · intro u v huv
      obtain ⟨hu, hv, huv'⟩ := hcomb u v huv
      rw [htransfer u v]
      exact le_of_lt (halow x _ _ hu hv huv')
    · intro u v huv
      obtain ⟨hu, hv, huv'⟩ := hcomb u v huv
      rw [htransfer u v]
      exact curvVec_secK_le_four cov hpinch x _ _ hu hv huv'
    · refine hC (rmFrame g₀ x e) (Work.Diff.GE.isAlgCurv_rmFrame_kit hLC g₀ x e) fun u v huv => ?_
      obtain ⟨hu, hv, huv'⟩ := hcomb u v huv
      have h1 : a ≤ inner ℝ (Submission.CurvatureVec.curvVec cov x (∑ i, u i • e i)
          (∑ i, v i • e i) (∑ i, v i • e i)) (∑ i, u i • e i) :=
        le_of_lt (halow x _ _ hu hv huv')
      have h2 : inner ℝ (Submission.CurvatureVec.curvVec cov x (∑ i, u i • e i)
          (∑ i, v i • e i) (∑ i, v i • e i)) (∑ i, u i • e i) ≤ 4 :=
        curvVec_secK_le_four cov hpinch x _ _ hu hv huv'
      rw [htransfer u v, abs_of_nonneg (by linarith)]
      exact h2
  -- `PinchingSetExists` applied to `K`
  obtain ⟨F, hF, hKF⟩ := hA1 K hKcompact hKgood
  exact ⟨F, hF, fun x e he => hKF (hframes x e he)⟩

end Work.Diff.L
