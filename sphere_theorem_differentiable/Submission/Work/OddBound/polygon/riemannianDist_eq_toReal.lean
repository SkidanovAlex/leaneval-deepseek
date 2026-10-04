import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygon.polygon_energy_aux

set_option backward.isDefEq.respectTransparency.types false

/-!
# The Riemannian distance is the extended Riemannian distance

`Submission.Distance.riemannianDist I x y` is the infimum of the lengths of *piecewise* `C¹` paths
(finitely many globally `C¹` curves joined end to end), while Mathlib's
`Manifold.riemannianEDist I x y` is the infimum of the lengths of `C¹` paths.  On a
path-connected manifold the two agree:

`riemannianDist I x y = (riemannianEDist I x y).toReal`.

The ingredients:

* `pathELength_eq_ofReal_curveLength`: for a globally `C¹` curve, Mathlib's `pathELength` is the
  `ENNReal.ofReal` of the Riemannian length `curveLength` of this development;
* `riemannianEDist_le_sum_pathELength`: for a chain of `C¹` curves joined end to end the extended
  distance of the endpoints is at most the sum of the `pathELength`s of the pieces (the triangle
  inequality for `riemannianEDist`, iterated).  This gives `riemannianEDist ≤ ofReal p.length` for
  *every* piecewise smooth path `p`, with no conversion of a general `C¹` path into a piecewise one;
* `exists_contMDiff_curve_near`: near every point `p` there is a neighbourhood every point of which
  is joined to `p` by a globally `C¹` curve (chart construction, clamped in time by
  `Real.smoothTransition`);
* `PwLengthSet_nonempty`: the set of lengths of piecewise smooth paths is nonempty, obtained from
  `PathConnectedSpace M` by the argument that the set of reachable points is open and closed, hence
  everything.

Then `riemannianEDist ≤ ofReal (riemannianDist)` follows by approximating the infimum with globally
`C¹` curves (`Manifold.exists_lt_locally_constant_of_riemannianEDist_lt`), and
`(riemannianEDist).toReal ≤ riemannianDist` from `riemannianEDist ≤ ofReal p.length` for all `p`
together with `le_csInf`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Manifold Bundle BigOperators ENNReal Topology
open Bundle ContDiff Set MeasureTheory
open scoped Interval
open Submission.Distance

namespace Work.OddBound.polygon

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

noncomputable section

/-! ## 1. Manifold path length of a globally `C¹` curve -/

/-- **Manifold path length versus Riemannian length, for a globally `C¹` curve.**  For a curve
`γ : ℝ → M` that is `C¹` on the whole real line, Mathlib's `pathELength` over `[a,b]` is the
extended-norm image of the integral of the Riemannian speed. -/
lemma pathELength_eq_ofReal_curveLength [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    [PathConnectedSpace M] [RegularSpace M] {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ) I 1 γ) {a b : ℝ} (hab : a ≤ b) :
    Manifold.pathELength I γ a b
      = ENNReal.ofReal (Submission.Length.curveLength (I := I) γ a b) := by
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hcont : Continuous (fun t : ℝ => Submission.Length.curveSpeed (I := I) γ t) :=
    continuous_curveSpeed (I := I) hγ
  rw [Submission.Length.curveLength_def]
  refine Commons.Geometry.Manifold.pathELength_eq_ofReal_integral_of_enorm_eq_nonneg (I := I)
    (γ := γ) (a := a) (b := b) (f := fun t : ℝ => Submission.Length.curveSpeed (I := I) γ t)
    hab hcont.integrableOn_Icc
    (fun t _ => Submission.Length.curveSpeed_nonneg (I := I) γ t) ?_
  intro t ht
  show ‖(mfderiv 𝓘(ℝ) I γ t) (1 : ℝ)‖ₑ
      = ENNReal.ofReal (Submission.Length.curveSpeed (I := I) γ t)
  rw [Submission.Minimal.enorm_eq_ofReal_norm, Submission.GeodesicSpeed.curveSpeed_eq_norm,
    Submission.Geodesic.curveVelocity_apply]

/-! ## 2. The extended distance is bounded by a chain of path lengths -/

/-- **Chain bound for the extended distance**, with the endpoint of the chain as target.  For
finitely many globally `C¹` curves joined end to end, the Riemannian extended distance between the
first endpoint and the last endpoint `c N (b N)` is at most the sum of the manifold path lengths of
the pieces. -/
lemma riemannianEDist_le_sum_pathELength_aux {N : ℕ} {c : ℕ → ℝ → M} {a b : ℕ → ℝ} {x : M}
    (hsmooth : ∀ i, ContMDiff 𝓘(ℝ) I 1 (c i))
    (hab : ∀ i, a i ≤ b i)
    (hjoin : ∀ i, i < N → c i (b i) = c (i + 1) (a (i + 1)))
    (hx : c 0 (a 0) = x) :
    Manifold.riemannianEDist I x (c N (b N))
      ≤ ∑ i ∈ Finset.range (N + 1), Manifold.pathELength I (c i) (a i) (b i) := by
  induction N with
  | zero =>
    rw [Finset.range_one, Finset.sum_singleton, ← hx]
    exact Manifold.riemannianEDist_le_pathELength (hsmooth 0).contMDiffOn rfl rfl (hab 0)
  | succ N ih =>
    have hrec := ih (fun i hi => hjoin i (Nat.lt_succ_of_lt hi))
    calc Manifold.riemannianEDist I x (c (N + 1) (b (N + 1)))
        ≤ Manifold.riemannianEDist I x (c N (b N))
            + Manifold.riemannianEDist I (c N (b N)) (c (N + 1) (b (N + 1))) :=
          Manifold.riemannianEDist_triangle
      _ = Manifold.riemannianEDist I x (c N (b N))
            + Manifold.riemannianEDist I (c (N + 1) (a (N + 1))) (c (N + 1) (b (N + 1))) := by
          rw [hjoin N (Nat.lt_succ_self N)]
      _ ≤ (∑ i ∈ Finset.range (N + 1), Manifold.pathELength I (c i) (a i) (b i))
            + Manifold.pathELength I (c (N + 1)) (a (N + 1)) (b (N + 1)) :=
          add_le_add hrec
            (Manifold.riemannianEDist_le_pathELength (hsmooth (N + 1)).contMDiffOn rfl rfl
              (hab (N + 1)))
      _ = ∑ i ∈ Finset.range (N + 1 + 1), Manifold.pathELength I (c i) (a i) (b i) :=
          (Finset.sum_range_succ (fun i => Manifold.pathELength I (c i) (a i) (b i)) (N + 1)).symm

/-- **Chain bound for the extended distance.** -/
lemma riemannianEDist_le_sum_pathELength {N : ℕ} {c : ℕ → ℝ → M} {a b : ℕ → ℝ} {x y : M}
    (hsmooth : ∀ i, ContMDiff 𝓘(ℝ) I 1 (c i))
    (hab : ∀ i, a i ≤ b i)
    (hjoin : ∀ i, i < N → c i (b i) = c (i + 1) (a (i + 1)))
    (hx : c 0 (a 0) = x) (hy : c N (b N) = y) :
    Manifold.riemannianEDist I x y
      ≤ ∑ i ∈ Finset.range (N + 1), Manifold.pathELength I (c i) (a i) (b i) := by
  rw [← hy]
  exact riemannianEDist_le_sum_pathELength_aux hsmooth hab hjoin hx

/-! ## 3. A globally `C¹` curve joining nearby points -/

/-- **Nearby points are joined by a globally `C¹` curve.**  Around every point `p` of `M` there is
a neighbourhood `U` such that every `q ∈ U` is the endpoint at time `1` of a globally `C¹` curve
starting at `p`.  The construction is the coordinate straight line in the extended chart of `p`,
clamped in time by `Real.smoothTransition` so that it is defined on all of `ℝ`. -/
lemma exists_contMDiff_curve_near [I.Boundaryless] (p : M) :
    ∃ U : Set M, U ∈ 𝓝 p ∧ ∀ q ∈ U, ∃ c : ℝ → M,
      ContMDiff 𝓘(ℝ) I 1 c ∧ c 0 = p ∧ c 1 = q := by
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) p)
    ((extChartAt I p) p) ((extChartAt I p).map_source (mem_extChartAt_source (I := I) p))
  refine ⟨(extChartAt I p).source ∩ (extChartAt I p) ⁻¹' Metric.ball ((extChartAt I p) p) (ρ / 2),
    Filter.inter_mem (extChartAt_source_mem_nhds (I := I) p)
      ((continuousAt_extChartAt (I := I) p).preimage_mem_nhds
        (Metric.ball_mem_nhds _ (by linarith))), ?_⟩
  rintro q ⟨hqsrc, hqball⟩
  set u : E := (extChartAt I p) q with hu
  have hnorm : ‖u - (extChartAt I p) p‖ < ρ / 2 := by
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hqball
    simpa [hu] using hqball
  have hmem : ∀ s : ℝ,
      Real.smoothTransition s • (u - (extChartAt I p) p) + (extChartAt I p) p
        ∈ (extChartAt I p).target := by
    intro s
    refine hρ ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul,
      Real.norm_of_nonneg (Real.smoothTransition.nonneg s)]
    calc Real.smoothTransition s * ‖u - (extChartAt I p) p‖
        ≤ 1 * ‖u - (extChartAt I p) p‖ := by
          gcongr
          exact Real.smoothTransition.le_one s
      _ = ‖u - (extChartAt I p) p‖ := one_mul _
      _ < ρ / 2 := hnorm
      _ < ρ := by linarith
  refine ⟨fun s : ℝ => (extChartAt I p).symm
    (Real.smoothTransition s • (u - (extChartAt I p) p) + (extChartAt I p) p), ?_, ?_, ?_⟩
  · have hcd : ContDiff ℝ 1 (fun s : ℝ =>
        Real.smoothTransition s • (u - (extChartAt I p) p) + (extChartAt I p) p) :=
      ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).smul_const
        (u - (extChartAt I p) p)).add contDiff_const
    have hcomp : ContMDiffOn 𝓘(ℝ) I 1
        ((↑(extChartAt I p).symm) ∘ fun s : ℝ =>
          Real.smoothTransition s • (u - (extChartAt I p) p) + (extChartAt I p) p) Set.univ :=
      (contMDiffOn_extChartAt_symm (I := I) p).comp
        (contMDiffOn_univ.mpr (contMDiff_iff_contDiff.mpr hcd)) (fun s _ => hmem s)
    exact contMDiffOn_univ.mp hcomp
  · show (extChartAt I p).symm (Real.smoothTransition 0 • (u - (extChartAt I p) p)
      + (extChartAt I p) p) = p
    rw [Real.smoothTransition.zero_of_nonpos le_rfl, zero_smul, zero_add]
    exact (extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)
  · show (extChartAt I p).symm (Real.smoothTransition 1 • (u - (extChartAt I p) p)
      + (extChartAt I p) p) = q
    rw [Real.smoothTransition.eq_one_iff_one_le.mpr le_rfl, one_smul, sub_add_cancel]
    exact (extChartAt I p).left_inv hqsrc

/-! ## 4. Piecewise smooth paths exist -/

/-- The set of points reachable from `x` by a piecewise smooth path is open: append a curve to the
end of a path. -/
lemma isOpen_reachableSet [I.Boundaryless] (x : M) :
    IsOpen {z : M | ∃ _ : PwPath I x z, True} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨P, -⟩
  obtain ⟨U, hU, hUprop⟩ := exists_contMDiff_curve_near (I := I) y
  refine Filter.mem_of_superset hU (fun q hq => ?_)
  obtain ⟨c, hc, hc0, hc1⟩ := hUprop q hq
  exact ⟨P.trans (PwPath.ofCurve (I := I) c hc y q hc0 hc1), trivial⟩

/-- The complement of the reachable set is open: a point joined to an unreachable point is itself
unreachable, by reversing the joining curve. -/
lemma isOpen_compl_reachableSet [I.Boundaryless] (x : M) :
    IsOpen {z : M | ∃ _ : PwPath I x z, True}ᶜ := by
  rw [isOpen_iff_mem_nhds]
  rintro y hy
  obtain ⟨U, hU, hUprop⟩ := exists_contMDiff_curve_near (I := I) y
  refine Filter.mem_of_superset hU (fun q hq hqB => ?_)
  obtain ⟨P, -⟩ := hqB
  obtain ⟨c, hc, hc0, hc1⟩ := hUprop q hq
  have hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ) 1 (fun s : ℝ => 1 - s) :=
    (contMDiff_const (c := (1 : ℝ))).sub contMDiff_id
  have hc' : ContMDiff 𝓘(ℝ) I 1 (fun s : ℝ => c (1 - s)) := by
    have h := hc.comp hg
    simpa only [Function.comp_def] using h
  have h0 : (fun s : ℝ => c (1 - s)) 0 = q := by simpa using hc1
  have h1 : (fun s : ℝ => c (1 - s)) 1 = y := by simpa using hc0
  exact hy ⟨P.trans (PwPath.ofCurve (I := I) (fun s : ℝ => c (1 - s)) hc' q y h0 h1),
    trivial⟩

/-- **Piecewise smooth paths exist.**  On a path-connected manifold, any two points are joined by a
piecewise smooth path, so the set of lengths of such paths is nonempty. -/
lemma PwLengthSet_nonempty [I.Boundaryless] [PathConnectedSpace M] (x y : M) :
    (PwLengthSet (I := I) x y).Nonempty := by
  have hclopen : IsClopen {z : M | ∃ _ : PwPath I x z, True} :=
    ⟨isOpen_compl_iff.mp (isOpen_compl_reachableSet (I := I) x),
      isOpen_reachableSet (I := I) x⟩
  have huniv : {z : M | ∃ _ : PwPath I x z, True} = Set.univ :=
    IsClopen.eq_univ hclopen ⟨x, PwPath.refl (I := I) x, trivial⟩
  obtain ⟨P, -⟩ := show y ∈ {z : M | ∃ _ : PwPath I x z, True} from by
    rw [huniv]; exact Set.mem_univ y
  exact ⟨P.length, Set.mem_range_self P⟩

/-! ## 5. The comparison -/

/-- **The Riemannian distance is the extended Riemannian distance.** -/
theorem riemannianDist_eq_toReal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    [RegularSpace M] (x y : M) :
    Submission.Distance.riemannianDist (I := I) x y = (Manifold.riemannianEDist I x y).toReal := by
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- every piecewise smooth path bounds the extended distance from above
  have hFle : ∀ p : PwPath I x y,
      Manifold.riemannianEDist I x y ≤ ENNReal.ofReal p.length := by
    intro p
    refine (riemannianEDist_le_sum_pathELength (I := I) (N := p.N) (c := p.c) (a := p.a)
      (b := p.b) (x := x) (y := y) p.hsmooth p.hab p.hjoin p.hx p.hy).trans (le_of_eq ?_)
    have h1 : (∑ i ∈ Finset.range (p.N + 1), Manifold.pathELength I (p.c i) (p.a i) (p.b i))
        = ∑ i ∈ Finset.range (p.N + 1),
            ENNReal.ofReal (Submission.Length.curveLength (I := I) (p.c i) (p.a i) (p.b i)) :=
      Finset.sum_congr rfl fun i _ =>
        pathELength_eq_ofReal_curveLength (I := I) (p.hsmooth i) (p.hab i)
    have h2 : (∑ i ∈ Finset.range (p.N + 1),
            ENNReal.ofReal (Submission.Length.curveLength (I := I) (p.c i) (p.a i) (p.b i)))
        = ENNReal.ofReal (∑ i ∈ Finset.range (p.N + 1),
            Submission.Length.curveLength (I := I) (p.c i) (p.a i) (p.b i)) :=
      (ENNReal.ofReal_sum_of_nonneg fun i _ =>
        Submission.Length.curveLength_nonneg (I := I) (p.c i) (p.hab i)).symm
    rw [h1, h2]
    exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun i _ =>
      Submission.Length.curveLength_def (I := I) (p.c i) (p.a i) (p.b i))
  -- hence the extended distance is finite
  have hFne : Manifold.riemannianEDist I x y ≠ ⊤ := by
    obtain ⟨s, hs⟩ := PwLengthSet_nonempty (I := I) x y
    obtain ⟨p, rfl⟩ := hs
    exact ne_of_lt ((hFle p).trans_lt ENNReal.ofReal_lt_top)
  -- the distance is at most the extended distance: approximate the latter by `C¹` curves
  have hA : Submission.Distance.riemannianDist (I := I) x y
      ≤ (Manifold.riemannianEDist I x y).toReal := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    set r : ℝ≥0∞ := Manifold.riemannianEDist I x y + ENNReal.ofReal ε with hr
    have hrlt : Manifold.riemannianEDist I x y < r := by
      rw [hr]
      exact ENNReal.lt_add_right hFne (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
    obtain ⟨γ, hγ0, hγ1, hγsm, hγlen, -⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (I := I)
        (x := x) (y := y) (a := 0) (b := 1) hrlt zero_lt_one
    have hlen : ENNReal.ofReal (Submission.Length.curveLength (I := I) γ 0 1) < r := by
      rw [← pathELength_eq_ofReal_curveLength (I := I) hγsm zero_le_one]
      exact hγlen
    have hlt : Submission.Length.curveLength (I := I) γ 0 1
        < (Manifold.riemannianEDist I x y).toReal + ε := by
      have hr' : r = ENNReal.ofReal ((Manifold.riemannianEDist I x y).toReal + ε) := by
        rw [hr, ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le, ENNReal.ofReal_toReal hFne]
      rw [hr'] at hlen
      exact (ENNReal.ofReal_lt_ofReal_iff
        (by linarith [ENNReal.toReal_nonneg (a := Manifold.riemannianEDist I x y)])).mp hlen
    calc Submission.Distance.riemannianDist (I := I) x y
        ≤ (PwPath.ofCurve (I := I) γ hγsm x y hγ0 hγ1).length :=
          Submission.Distance.riemannianDist_le_length _
      _ = Submission.Length.curveLength (I := I) γ 0 1 :=
          PwPath.length_ofCurve (I := I) γ hγsm x y hγ0 hγ1
      _ ≤ (Manifold.riemannianEDist I x y).toReal + ε := hlt.le
  -- and the extended distance is at most the distance
  have hB : (Manifold.riemannianEDist I x y).toReal
      ≤ Submission.Distance.riemannianDist (I := I) x y := by
    rw [Submission.Distance.riemannianDist]
    refine le_csInf (PwLengthSet_nonempty (I := I) x y) (fun s hs => ?_)
    obtain ⟨p, rfl⟩ := hs
    calc (Manifold.riemannianEDist I x y).toReal
        ≤ (ENNReal.ofReal p.length).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hFle p)
      _ = p.length := ENNReal.toReal_ofReal (PwPath.length_nonneg p)
  exact le_antisymm hA hB

end

end Work.OddBound.polygon
