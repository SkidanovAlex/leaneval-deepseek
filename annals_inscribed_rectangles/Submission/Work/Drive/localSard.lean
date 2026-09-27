import Mathlib
import Submission.Work.Drive.exists_meet3Data_of_good_family
import Submission.Work.Drive.baseCover
import Submission.Work.Drive.localDensity
import Submission.Work.Drive.goodParamsOpen
import Submission.Work.Drive.nineBoxToMeet3
import Submission.Work.Drive.meet3Containment
import Submission.Work.Drive.TParity.finite_bK3
import Submission.Work.Drive.meet32_bordism_invariance

namespace Work.Drive

set_option maxHeartbeats 1600000

open Filter Metric Set
open scoped Topology

/-! ## Local helpers for the localized parametric Sard

The helper lemmas below are the cut-off machinery of
`Work.Drive.exists_meet3Data_of_good_family` (private there, hence reproduced here) together with the
two small metric-space facts that glue the finitely many open dense parameter sets of the pieces. -/

/-- The differentiability order `⊤` is not zero. -/
private lemma top_ne_zero_order : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- **A smooth function that is `1` on a compact set and supported in an open set containing it.** -/
private lemma exists_cutoff_tsupport_subset {n : ℕ} {K V : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      (∀ x ∈ K, f x = 1) ∧ tsupport f ⊆ V := by
  classical
  have hpt : ∀ x : K, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (x : EuclideanSpace ℝ (Fin n)) (2 * r) ⊆ V := by
    intro x
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (hKV x.2))
    refine ⟨r / 4, by linarith, ?_⟩
    intro z hz
    apply hrsub
    rw [Metric.mem_ball]
    have h := Metric.mem_closedBall.mp hz
    linarith
  choose r hrpos hrsub using hpt
  have hbump : ∀ x : K, ∃ b : ContDiffBump (x : EuclideanSpace ℝ (Fin n)),
      b.rIn = r x ∧ b.rOut = 2 * r x := fun x =>
    ⟨⟨r x, 2 * r x, hrpos x, by linarith [hrpos x]⟩, rfl, rfl⟩
  choose b hb1 hb2 using hbump
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball (x : EuclideanSpace ℝ (Fin n)) (r x))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hrpos ⟨x, hx⟩)⟩)
  refine ⟨fun y => 1 - ∏ x ∈ s, (1 - b x y), ?_, ?_, ?_⟩
  · have hcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin n) => ∏ x ∈ s, (1 - b x y)) :=
      contDiff_prod (𝕜 := ℝ) (𝔸' := ℝ)
        (fun x _ => contDiff_const.sub (b x).contDiff)
    exact contDiff_const.sub hcont
  · intro y hy
    obtain ⟨x, hxs, hxy⟩ := Set.mem_iUnion₂.mp (hs hy)
    have hbx : b x y = 1 := by
      refine (b x).one_of_mem_closedBall ?_
      rw [hb1 x, Metric.mem_closedBall]
      exact le_of_lt (Metric.mem_ball.mp hxy)
    have hz : (1 - b x y) = 0 := by rw [hbx]; ring
    show 1 - ∏ x ∈ s, (1 - b x y) = 1
    rw [Finset.prod_eq_zero hxs hz]
    ring
  · have hsupp : Function.support (fun y => 1 - ∏ x ∈ s, (1 - b x y)) ⊆
        ⋃ x ∈ s, tsupport (⇑(b x)) := by
      intro y hy
      by_contra hcon
      have h1 : (∏ x ∈ s, (1 - b x y)) = 1 :=
        Finset.prod_eq_one (fun x hx => by
          have hb0 : b x y = 0 := by
            by_contra hne
            exact hcon (Set.mem_iUnion₂.mpr ⟨x, hx, subset_tsupport _ hne⟩)
          rw [hb0]; ring)
      simp only [Function.mem_support, ne_eq] at hy
      exact hy (by rw [h1]; ring)
    have hclosed : IsClosed (⋃ x ∈ s, tsupport (⇑(b x))) :=
      isClosed_biUnion_finset (fun x _ => isClosed_tsupport _)
    calc tsupport (fun y => 1 - ∏ x ∈ s, (1 - b x y))
        = closure (Function.support (fun y => 1 - ∏ x ∈ s, (1 - b x y))) := rfl
      _ ⊆ closure (⋃ x ∈ s, tsupport (⇑(b x))) := closure_mono hsupp
      _ = ⋃ x ∈ s, tsupport (⇑(b x)) := hclosed.closure_eq
      _ ⊆ V := by
          rintro z hz
          obtain ⟨x, hxs, hxz⟩ := Set.mem_iUnion₂.mp hz
          exact hrsub x (by rw [(b x).tsupport_eq, hb2 x] at hxz; exact hxz)

/-- A point outside the topological support of `f` has a neighbourhood on which `f` vanishes. -/
private lemma eventually_eq_zero_of_notMem_tsupport {X Y : Type*} [TopologicalSpace X] [Zero Y]
    {f : X → Y} {x : X} (h : x ∉ tsupport f) : ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using h)) ?_
  intro y hy
  by_contra hne
  exact hy (subset_tsupport f hne)

/-- **Smoothness of the cut-off charted difference map.** -/
private lemma contDiff_cutoff_chartDiff3 (m : ℕ)
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    (p : M) {γ : EuclideanSpace ℝ (Fin m) → ℝ} (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {β : EuclideanSpace ℝ (Fin 9) → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    {U : Set (EuclideanSpace ℝ (Fin m))} {V : Set (EuclideanSpace ℝ (Fin 9))}
    (hUV : U ×ˢ V ⊆ {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
      ∀ k : Fin 3, G q.1 k (TParity.bPartC k q.2) ∈ (chr p).source})
    (hγsupp : tsupport γ ⊆ U) (hβsupp : tsupport β ⊆ V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (γ q.1 * β q.2) • TParity.chartDiff3 p (G q.1) q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  by_cases hγ0 : q₀.1 ∈ tsupport γ
  · by_cases hβ0 : q₀.2 ∈ tsupport β
    · have hreg : ∀ k : Fin 3, G q₀.1 k (TParity.bPartC k q₀.2) ∈ (chr p).source :=
        hUV ⟨hγsupp hγ0, hβsupp hβ0⟩
      have hχ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
            TParity.chartDiff3 p (G q.1) q.2) q₀ :=
        contDiffAt_chartDiff3_family_fin m G hG p q₀.1 hreg
      have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) => γ q.1 * β q.2) q₀ :=
        (hγ.contDiffAt.comp q₀ contDiffAt_fst).mul
          (hβ.contDiffAt.comp q₀ contDiffAt_snd)
      exact hg.smul hχ
    · refine (contDiffAt_const (c := (0 : Tgt 8))).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_snd.tendsto q₀).eventually
        (eventually_eq_zero_of_notMem_tsupport hβ0)] with q hq
      rw [hq, mul_zero, zero_smul]
  · refine (contDiffAt_const (c := (0 : Tgt 8))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto q₀).eventually
      (eventually_eq_zero_of_notMem_tsupport hγ0)] with q hq
    rw [hq, zero_mul, zero_smul]

/-- If `f` is injective and `f ∘ g` is surjective, then `g` is surjective. -/
private lemma surjective_of_comp_injective {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F →L[ℝ] G} (hf : Function.Injective f) {g : E →L[ℝ] F}
    (h : Function.Surjective (f.comp g)) : Function.Surjective g := by
  intro w
  obtain ⟨v, hv⟩ := h (f w)
  refine ⟨v, hf ?_⟩
  rw [ContinuousLinearMap.comp_apply] at hv
  exact hv

/-- Transporting face-restricted surjectivity across an equality of the linear maps and of the face
coordinate. -/
private lemma faceSurj_congr {A B : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 8)}
    (hAB : A = B) {j j' : Fin 9} (hj : j = j')
    (h : Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v j = 0} => A v.1)) :
    Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v j' = 0} => B v.1) := by
  cases hAB
  cases hj
  exact h

/-- **The derivative of the cut-off family at a box point.**  At a point `y` of the compact set on
which the space cut-off equals `1` and at a zero of the charted difference map, the derivative of
`z' ↦ (γ s * β z') • chartDiff3 p (G s) z'` is the derivative of `chartDiff3` itself: the
product-rule term involving `β` carries the factor `chartDiff3 p (G s) y = 0`. -/
private lemma fderiv_cutoff_eq (m : ℕ)
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {s : EuclideanSpace ℝ (Fin m)}
    {y : EuclideanSpace ℝ (Fin 9)}
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    (p : M) {γ : EuclideanSpace ℝ (Fin m) → ℝ} (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγv : γ s = 1)
    {β : EuclideanSpace ℝ (Fin 9) → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβv : β y = 1)
    (hreg : y ∈ TParity.region3 p (G s)) (hzy : TParity.chartDiff3 p (G s) y = 0) :
    fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        (γ s * β z') • TParity.chartDiff3 p (G s) z') y
      = fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G s) z') y := by
  have hχat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G q.1) q.2) (s, y) :=
    contDiffAt_chartDiff3_family_fin m G hG p s hreg
  have hχp : HasFDerivAt (fun z' : EuclideanSpace ℝ (Fin 9) =>
      TParity.chartDiff3 p (G s) z')
      (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G s) z') y) y :=
    (hχat.comp y (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
      top_ne_zero_order |>.hasFDerivAt
  have hγβp : HasFDerivAt (fun z' : EuclideanSpace ℝ (Fin 9) => γ s * β z')
      (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) => γ s * β z') y) y :=
    ((contDiffAt_const.mul hβ.contDiffAt).differentiableAt
      top_ne_zero_order).hasFDerivAt
  have hsmul := hγβp.smul hχp
  have h1 : (γ s * β y) • (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G s) z') y)
      + (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) => γ s * β z') y).smulRight
          (TParity.chartDiff3 p (G s) y)
      = fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G s) z') y := by
    rw [hγv, hβv, one_mul, hzy]
    simp
  rw [h1] at hsmul
  exact hsmul.fderiv

/-- **The good-parameter predicate of a cut-off charted system**: every zero in `K ∩ unitBox 8` is
regular, and every boundary zero in `K` lies on exactly one face, with the restriction of the
derivative to that coordinate hyperplane still surjective.  This is the predicate whose *openness* is
`Work.Drive.goodParamsOpen`. -/
private abbrev GoodSet (m : ℕ)
    (Ψ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8))
    (K : Set (EuclideanSpace ℝ (Fin 9))) (t : EuclideanSpace ℝ (Fin m)) : Prop :=
  (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → Ψ (t, y) = 0 →
    Function.Surjective (fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (t, y')) y)) ∧
  (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → Ψ (t, y) = 0 →
    y ∈ Submission.Drive.unitBoxBdry 8 →
    ∃ (k : Fin 3) (i : Fin 3),
      (y (Work.Drive.bIdx k i) = 0 ∨ y (Work.Drive.bIdx k i) = 1) ∧
      (∀ j : Fin 3, j ≠ i → y (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, y (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v (Work.Drive.bIdx k i) = 0} =>
        fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (t, y')) y v.1))

section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The intrinsic good-parameter predicate on a compact set of the nine-box**: transversality at
every triple point in `K` and the face condition at every boundary triple point in `K`.  This is
exactly the conclusion of `Work.Drive.localDensity` (and of
`Work.Drive.exists_meet3Data_of_good_family`). -/
private abbrev GoodChart (m : ℕ) (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (K : Set (EuclideanSpace ℝ (Fin 9))) (t : EuclideanSpace ℝ (Fin m)) : Prop :=
  (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 →
    Work.Drive.TParity.meet3 (G t) y →
    Work.Drive.TripleTransverse (Work.Drive.TParity.md3 (G t) 0 y)
      (Work.Drive.TParity.md3 (G t) 1 y) (Work.Drive.TParity.md3 (G t) 2 y)) ∧
  (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 →
    Work.Drive.TParity.meet3 (G t) y → y ∈ Submission.Drive.unitBoxBdry 8 →
    ∃ (k : Fin 3) (i : Fin 3),
      (y (Work.Drive.bIdx k i) = 0 ∨ y (Work.Drive.bIdx k i) = 1) ∧
      (∀ j : Fin 3, j ≠ i → y (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, y (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
      ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
        Work.Drive.TripleCommonDir (Work.Drive.TParity.md3 (G t) 0 y)
          (Work.Drive.TParity.md3 (G t) 1 y) (Work.Drive.TParity.md3 (G t) 2 y) v ∧
        (v k) i ≠ 0)

end

/-! ## Two metric-space facts -/

/-- A finite family of positive reals has a positive lower bound. -/
private lemma exists_pos_le_all {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, ρ ≤ f i := by
  classical
  by_cases h : (Finset.univ : Finset ι).Nonempty
  · refine ⟨(Finset.univ : Finset ι).inf' h f, ?_, fun i => Finset.inf'_le f (Finset.mem_univ i)⟩
    rw [Finset.lt_inf'_iff h]
    exact fun i _ => hf i
  · exact ⟨1, one_pos, fun i => absurd ⟨i, Finset.mem_univ i⟩ h⟩

/-- An open set containing the ball of radius `ρ` in its closure, together with another set
containing the ball in its closure, has its intersection doing the same. -/
private lemma ball_subset_closure_inter {E : Type*} [PseudoMetricSpace E] [Zero E]
    {A B : Set E} {ρ : ℝ} (hA : IsOpen A) (hdA : Metric.ball 0 ρ ⊆ closure A)
    (hdB : Metric.ball 0 ρ ⊆ closure B) : Metric.ball 0 ρ ⊆ closure (A ∩ B) := by
  intro x hx
  have hxρ : dist x 0 < ρ := by rwa [Metric.mem_ball] at hx
  have hdA' : ∀ ε > 0, ∃ y ∈ A, dist x y < ε := fun ε hε =>
    Metric.mem_closure_iff.mp (hdA hx) ε hε
  have hdB' : ∀ y : E, dist y 0 < ρ → ∀ ε > 0, ∃ z ∈ B, dist y z < ε := by
    intro y hy ε hε
    exact Metric.mem_closure_iff.mp (hdB (by rwa [Metric.mem_ball])) ε hε
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hρx : 0 < ρ - dist x 0 := by linarith
  obtain ⟨y, hyA, hxy⟩ := hdA' (min ε (ρ - dist x 0) / 4)
    (div_pos (lt_min hε hρx) (by norm_num))
  have hyρ : dist y 0 < ρ := by
    have h2 : dist y x < min ε (ρ - dist x 0) / 4 := by rwa [dist_comm] at hxy
    have h3 : min ε (ρ - dist x 0) / 4 < ρ - dist x 0 := by
      have := min_le_right ε (ρ - dist x 0); linarith
    calc dist y 0 ≤ dist y x + dist x 0 := dist_triangle _ _ _
      _ < ρ := by linarith
  obtain ⟨η, hηpos, hηsub⟩ := Metric.isOpen_iff.mp hA y hyA
  obtain ⟨z, hzB, hyz⟩ := hdB' y hyρ (min η (min ε (ρ - dist x 0) / 4))
    (lt_min hηpos (div_pos (lt_min hε hρx) (by norm_num)))
  refine ⟨z, ⟨?_, hzB⟩, ?_⟩
  · refine hηsub ?_
    rw [Metric.mem_ball, dist_comm]
    exact lt_of_lt_of_le hyz (min_le_left _ _)
  · have h1 : dist x y < min ε (ρ - dist x 0) / 4 := hxy
    have h2 : dist y z < min ε (ρ - dist x 0) / 4 := lt_of_lt_of_le hyz (min_le_right _ _)
    have h3 : min ε (ρ - dist x 0) ≤ ε := min_le_left _ _
    calc dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
      _ < ε := by linarith

/-- A finite intersection of open sets, each dense in the ball of radius `ρ`, is dense in that
ball. -/
private lemma dense_iInter_of_dense_ball {ι : Type*} [Fintype ι]
    {E : Type*} [PseudoMetricSpace E] [Zero E] (A : ι → Set E) (ρ : ℝ)
    (hA : ∀ i, IsOpen (A i)) (hd : ∀ i, Metric.ball 0 ρ ⊆ closure (A i)) :
    Metric.ball 0 ρ ⊆ closure (⋂ i, A i) := by
  classical
  have key : ∀ s : Finset ι, (∀ i ∈ s, IsOpen (A i)) →
      (∀ i ∈ s, Metric.ball 0 ρ ⊆ closure (A i)) →
      Metric.ball 0 ρ ⊆ closure (⋂ i ∈ s, A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ _; simp
    | insert a s ha ih =>
        intro h1 h2
        rw [Finset.set_biInter_insert]
        refine ball_subset_closure_inter (h1 a (Finset.mem_insert_self a s))
          (h2 a (Finset.mem_insert_self a s)) ?_
        exact ih (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
          (fun i hi => h2 i (Finset.mem_insert_of_mem hi))
  have := key Finset.univ (fun i _ => hA i) (fun i _ => hd i)
  simpa using this


/-- **One piece of the localized parametric Sard.**  For a chart `p`, a compact set `K` and a radius
`δ` on which the chart at `p` contains all three values, there is a globally smooth cut-off charted
system `Ψ` whose good parameters on `K` are (a) *dense* near `0` — by `Work.Drive.localDensity` — and
(b) *contained* in the intrinsic good parameters on `K` — by the cut-off derivative identity
`fderiv_cutoff_eq`, the chart-independence of the derivative (`chartDiff3_surj`,
`chartDiff3_tan3_surjective_iff`) and the face criterion (`exists_commonDir_of_faceSurjective`).

This is the per-piece input of `Work.Drive.localSard`: `ρ = δ/8` is the radius on which the parameter
cut-off equals `1`, and on it the cut-off system and `chartDiff3 p (G ·)` have the same zeros in `K`
and the same derivatives there. -/
private theorem piece_data
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {m : ℕ} (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    (hsmooth : ∀ (t : EuclideanSpace ℝ (Fin m)) (k : Fin 3),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (G t k))
    (hseam : ∀ (t : EuclideanSpace ℝ (Fin m)) (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Work.Drive.onSeam x → G t k x = G t k (Work.Drive.seamInv x))
    (p : M) (K : Set (EuclideanSpace ℝ (Fin 9))) (δ : ℝ) (hK : IsCompact K) (hδ : 0 < δ)
    (hres : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < δ → y ∈ K →
      ∀ k : Fin 3, G t k (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source)
    (hsurj : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < δ → y ∈ K →
      Work.Drive.TParity.chartDiff3 p (G t) y = 0 →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.TParity.chartDiff3 p (G t') y) t)) :
    ∃ (ρ : ℝ) (Ψ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) →
        EuclideanSpace ℝ (Fin 8)),
      0 < ρ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      IsOpen {t : EuclideanSpace ℝ (Fin m) | GoodSet m Ψ K t} ∧
      (∀ t : EuclideanSpace ℝ (Fin m), ‖t‖ < ρ → GoodSet m Ψ K t → GoodChart m G K t) ∧
      (∀ (t₀ : EuclideanSpace ℝ (Fin m)), ‖t₀‖ < ρ → ∀ ε : ℝ, 0 < ε →
        ∃ t : EuclideanSpace ℝ (Fin m), ‖t - t₀‖ < ε ∧ ‖t‖ < ρ ∧ GoodSet m Ψ K t) := by
  classical
  set ρ : ℝ := δ / 8 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρδ : ρ < δ := by rw [hρdef]; linarith
  -- ## Step 0: the chart containment region is open
  have hcontfam : ∀ k : Fin 3, Continuous
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        G q.1 k (TParity.bPartC k q.2)) := fun k =>
    (hG k).continuous.comp
      (continuous_fst.prodMk ((TParity.bPartC k).continuous.comp continuous_snd))
  set W : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9)) :=
    {q | ∀ k : Fin 3, G q.1 k (TParity.bPartC k q.2) ∈ (chr p).source} with hW
  have hWopen : IsOpen W := by
    have h : W = ⋂ k : Fin 3, {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
        G q.1 k (TParity.bPartC k q.2) ∈ (chr p).source} := by
      rw [hW]; ext q; simp
    rw [h]
    exact isOpen_iInter_of_finite fun k => (hcontfam k).isOpen_preimage _ (chr p).open_source
  have hWsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (δ / 4) ×ˢ K ⊆ W := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    refine hres t y ?_ hy
    have h := Metric.mem_closedBall.mp ht
    rw [dist_zero_right] at h
    linarith
  -- ## Step 1: the tube lemma separates the parameter and the space variable
  obtain ⟨U, V, hUopen, hVopen, hUsub, hVsub, hUV⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) (δ / 4))
      hK hWopen hWsub
  -- ## Step 2: the two cut-off functions
  obtain ⟨γ, hγsmooth, hγone, hγsupp⟩ :=
    exists_cutoff_tsupport_subset (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) (δ / 4))
      hUopen hUsub
  obtain ⟨β, hβsmooth, hβone, hβsupp⟩ := exists_cutoff_tsupport_subset hK hVopen hVsub
  -- ## Step 3: the cut-off system, globally smooth by construction
  set Ψ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8) :=
    fun q => (γ q.1 * β q.2) • TParity.chartDiff3 p (G q.1) q.2 with hΨdef
  have hfun : ∀ t : EuclideanSpace ℝ (Fin m),
      (fun z' : EuclideanSpace ℝ (Fin 9) => Ψ (t, z')) =
        (fun z' : EuclideanSpace ℝ (Fin 9) =>
          (γ t * β z') • TParity.chartDiff3 p (G t) z') := fun t => rfl
  have hΨsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ :=
    contDiff_cutoff_chartDiff3 m G hG p hγsmooth hβsmooth hUV hγsupp hβsupp
  have hΨopen : IsOpen {t : EuclideanSpace ℝ (Fin m) | GoodSet m Ψ K t} :=
    goodParamsOpen m Ψ hΨsm K hK
  refine ⟨ρ, Ψ, hρpos, hΨsm, hΨopen, ?_, ?_⟩
  · -- ## Transfer out: a good parameter of the cut-off system is an intrinsic good parameter
    intro t ht hgood
    have htδ : ‖t‖ < δ := lt_trans ht hρδ
    have hγv : γ t = 1 := hγone t (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)
    have hDt : ∀ k : Fin 3, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (G t k) :=
      hsmooth t
    constructor
    · intro y hyK hybox hmeet
      have hreg : y ∈ TParity.region3 p (G t) := hres t y htδ hyK
      have hzy : TParity.chartDiff3 p (G t) y = 0 := (TParity.chartDiff3_eq_zero_iff hreg).mpr hmeet
      have hβv : β y = 1 := hβone y hyK
      have hΨ0 : Ψ (t, y) = 0 := by
        show (γ t * β y) • TParity.chartDiff3 p (G t) y = 0
        rw [hγv, hβv, one_mul, hzy, smul_zero]
      have hgood1 : Function.Surjective (fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) =>
          Ψ (t, y')) y) := hgood.1 y hyK hybox hΨ0
      rw [hfun t] at hgood1
      rw [fderiv_cutoff_eq m G hG p hγsmooth hγv hβsmooth hβv hreg hzy] at hgood1
      have htan : Function.Surjective (TParity.tan3 p (G t) y) :=
        surjective_of_comp_injective TParity.chartDiff3_pUpCLM_injective (by
          rw [← (TParity.hasFDerivAt_chartDiff3 p (G t) hDt hreg).fderiv]
          exact hgood1)
      exact (TParity.chartDiff3_tan3_surjective_iff p (G t) hreg hmeet).mp htan
    · intro y hyK hybox hmeet hybdry
      have hreg : y ∈ TParity.region3 p (G t) := hres t y htδ hyK
      have hzy : TParity.chartDiff3 p (G t) y = 0 := (TParity.chartDiff3_eq_zero_iff hreg).mpr hmeet
      have hβv : β y = 1 := hβone y hyK
      have hΨ0 : Ψ (t, y) = 0 := by
        show (γ t * β y) • TParity.chartDiff3 p (G t) y = 0
        rw [hγv, hβv, one_mul, hzy, smul_zero]
      obtain ⟨k, i, hbi, hin, hin', h4⟩ := hgood.2 y hyK hybox hΨ0 hybdry
      have h4' : Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) //
          v (Work.Drive.bIdx k i) = 0} =>
          fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (t, y')) y v.1) := h4
      rw [hfun t] at h4'
      have h5 : Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) //
          v (Work.Drive.bIdx k i) = 0} =>
          fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
            TParity.chartDiff3 p (G t) z') y v.1) :=
        faceSurj_congr (fderiv_cutoff_eq m G hG p hγsmooth hγv hβsmooth hβv hreg hzy) rfl h4'
      have hsurjy : Function.Surjective (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
          TParity.chartDiff3 p (G t) z') y) := by
        intro w
        obtain ⟨v, hv⟩ := h5 w
        exact ⟨v.1, hv⟩
      obtain ⟨v, hv, hvi⟩ :=
        exists_commonDir_of_faceSurjective p (G t) hDt hreg hmeet hsurjy h5
      exact ⟨k, i, hbi, hin, hin', v, hv, hvi⟩
  · -- ## Density: `Work.Drive.localDensity` produces arbitrarily close good parameters
    intro t₀ ht₀ ε hε
    have hε₂pos : 0 < min ε (ρ - ‖t₀‖) / 2 :=
      div_pos (lt_min hε (by linarith)) (by norm_num)
    obtain ⟨t, htclose, htrans, hface⟩ :=
      localDensity G hG hsmooth hseam p K δ hK hδ hres hsurj (t₀ := t₀) (by linarith)
        (ε := min ε (ρ - ‖t₀‖) / 2) hε₂pos
    have htε : ‖t - t₀‖ < ε :=
      lt_of_lt_of_le htclose (by have := min_le_left ε (ρ - ‖t₀‖); linarith)
    have htρ : ‖t‖ < ρ := by
      have h1 : ‖t - t₀‖ < min ε (ρ - ‖t₀‖) / 2 := htclose
      have h2 : min ε (ρ - ‖t₀‖) / 2 ≤ (ρ - ‖t₀‖) / 2 := by
        have := min_le_right ε (ρ - ‖t₀‖); linarith
      have h3 : t₀ + (t - t₀) = t := by abel
      calc ‖t‖ = ‖t₀ + (t - t₀)‖ := by rw [h3]
        _ ≤ ‖t₀‖ + ‖t - t₀‖ := norm_add_le _ _
        _ < ρ := by linarith
    have htδ : ‖t‖ < δ := lt_trans htρ hρδ
    have hγv : γ t = 1 := hγone t (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)
    have hDt : ∀ k : Fin 3, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (G t k) :=
      hsmooth t
    refine ⟨t, htε, htρ, ?_⟩
    constructor
    · intro y hyK hybox hΨ0
      have hβv : β y = 1 := hβone y hyK
      have hzy : TParity.chartDiff3 p (G t) y = 0 := by
        have h : (γ t * β y) • TParity.chartDiff3 p (G t) y = 0 := by
          show Ψ (t, y) = 0
          exact hΨ0
        rwa [hγv, hβv, one_mul, one_smul] at h
      have hreg : y ∈ TParity.region3 p (G t) := hres t y htδ hyK
      have hmeet : TParity.meet3 (G t) y := (TParity.chartDiff3_eq_zero_iff hreg).mp hzy
      have hsurjy : Function.Surjective (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
          TParity.chartDiff3 p (G t) z') y) :=
        TParity.chartDiff3_surj (G t) hDt hreg hmeet (htrans y hyK hybox hmeet)
      have hgoal : Function.Surjective (fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) =>
          Ψ (t, y')) y) := by
        rw [hfun t, fderiv_cutoff_eq m G hG p hγsmooth hγv hβsmooth hβv hreg hzy]
        exact hsurjy
      exact hgoal
    · intro y hyK hybox hΨ0 hybdry
      have hβv : β y = 1 := hβone y hyK
      have hzy : TParity.chartDiff3 p (G t) y = 0 := by
        have h : (γ t * β y) • TParity.chartDiff3 p (G t) y = 0 := by
          show Ψ (t, y) = 0
          exact hΨ0
        rwa [hγv, hβv, one_mul, one_smul] at h
      have hreg : y ∈ TParity.region3 p (G t) := hres t y htδ hyK
      have hmeet : TParity.meet3 (G t) y := (TParity.chartDiff3_eq_zero_iff hreg).mp hzy
      obtain ⟨k, i, hbi, hin, hin', v, hv, hvi⟩ := hface y hyK hybox hmeet hybdry
      have hsurjy : Function.Surjective (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
          TParity.chartDiff3 p (G t) z') y) :=
        TParity.chartDiff3_surj (G t) hDt hreg hmeet (htrans y hyK hybox hmeet)
      have hfaceS : Function.Surjective (fun w : {w : EuclideanSpace ℝ (Fin 9) //
          w (Work.Drive.bIdx k i) = 0} =>
          fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
            TParity.chartDiff3 p (G t) z') y w.1) :=
        TParity.chartDiff3_domRestrict_surjective p (G t) hDt hreg hmeet hsurjy hv
          (by rw [TParity.mk3_bIdx]; exact hvi)
      have hgoal : Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) //
          v (Work.Drive.bIdx k i) = 0} =>
          fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (t, y')) y v.1) := by
        rw [hfun t]
        exact faceSurj_congr
          (fderiv_cutoff_eq m G hG p hγsmooth hγv hβsmooth hβv hreg hzy).symm rfl hfaceS
      exact ⟨k, i, hbi, hin, hin', hgoal⟩

/-- **The parametric Sard for a family of triples, without any *global* chart-residency hypothesis.**

`Work.Drive.exists_meet3Hyp_of_good_family` produces one parameter `t` at which the three charts
`G t k` satisfy `Meet3Hyp`, but it needs a chart whose source contains all the perturbed values (the
`hcontain` hypothesis), and no such chart is available for the capping space: the preferred chart of
`Work.Drive.cappingCharted` has an *opaque* source (`Submission/Work/Drive/CHART_SOURCE_OPACITY.md`).

This statement replaces the single global chart by the *localized* construction (route 2 of that note):
the chart is taken at each base point's own value (which is free by `mem_chart_source`, cf.
`Work.Drive.TParity.mem_region3_self`), and the pieces are patched.  The regularity input is the
*richness* of the family: for **every** chart `p`, compact `K` and radius `δ` on which that chart
contains the values, the parametrised system `t ↦ chartDiff3 p (G t) y` is surjective at every zero
`y ∈ K`, `‖t‖ < δ`.  (At a zero the three values coincide, so this condition is *chart-independent*: two
charts differ there by a smooth transition with invertible differential — the mechanism of
`Work.Drive.TParity.chartDiff3_tan3_surjective_iff`.)

Proof plan.  Use `Work.Drive.baseCover` for the finite chart-per-piece cover `(p i, K i, δ i)`,
`Work.Drive.localDensity` for the density of each piece's good parameter set, and the merged genericity
`Work.Drive.exists_forall_good_and_notMem_family_multi` (finitely many systems, one parameter) — with the
cut-off/globalization step of `Work.Drive.exists_meet3Data_of_good_family` performed per piece (a common
parameter cut-off `γ` and squeeze `σ`, one spatial cut-off `β i` per piece supported inside that piece's
residency region) — so that a single parameter makes every piece regular; then
`Work.Drive.eventually_meet3_subset_of_isOpen` puts every triple point of `G t` in `⋃ int (K i)`, and the
per-piece conclusions bundle into `Meeting3Hyp`'s clauses. -/
theorem localSard
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {m : ℕ} (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    (hsmooth : ∀ (t : EuclideanSpace ℝ (Fin m)) (k : Fin 3),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (G t k))
    (hseam : ∀ (t : EuclideanSpace ℝ (Fin m)) (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Work.Drive.onSeam x → G t k x = G t k (Work.Drive.seamInv x))
    (hsurj : ∀ (p : M) (K : Set (EuclideanSpace ℝ (Fin 9))) (δ : ℝ), IsCompact K → 0 < δ →
      (∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < δ → y ∈ K →
        ∀ k : Fin 3, G t k (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source) →
      ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < δ → y ∈ K →
        Work.Drive.TParity.chartDiff3 p (G t) y = 0 →
        Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          Work.Drive.TParity.chartDiff3 p (G t') y) t)) :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin m), ‖t‖ < ε' ∧
      Work.Drive.Meet3Hyp M (G t) := by
  intro ε' hε'
  classical
  have hcont : ∀ k : Fin 3, Continuous
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2) :=
    fun k => (hG k).continuous
  obtain ⟨ι, hιfin, K, δ, p, hK, hδ, hcover, hres⟩ := baseCover G hcont
  letI : Fintype ι := hιfin
  -- ## one global smooth system and one radius per piece of the cover
  choose ρ Ψ hρpos hΨsm hΨopen htrans hdense using fun i : ι =>
    piece_data G hG hsmooth hseam (p i) (K i) (δ i) (hK i) (hδ i)
      (fun t y ht hy k => hres i t y ht hy k)
      (hsurj (p i) (K i) (δ i) (hK i) (hδ i) (fun t y ht hy k => hres i t y ht hy k))
  -- ## the base locus, covered by the interiors of the pieces
  set Ubig : Set (EuclideanSpace ℝ (Fin 9)) := ⋃ i, interior (K i) with hUbigdef
  have hUbigopen : IsOpen Ubig := isOpen_iUnion fun i => isOpen_interior
  have hbase : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      TParity.meet3 (G 0) y → y ∈ Ubig := by
    intro y hy hm
    obtain ⟨i, hi⟩ := hcover y hy hm
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  -- ## the radius on which the perturbed triple locus stays inside the union of the pieces
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ t : EuclideanSpace ℝ (Fin m), ‖t‖ < δ₀ →
        ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
          TParity.meet3 (G t) y → y ∈ Ubig := by
    have hev := eventually_meet3_subset_of_isOpen G hcont (U := Ubig) hUbigopen hbase
    rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hev
    obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := hev
    refine ⟨δ₀, hδ₀pos, fun t ht y hy hm => hδ₀sub ?_ y hy hm⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact ht
  -- ## a positive radius inside all the pieces
  obtain ⟨ρ₀, hρ₀pos, hρ₀le⟩ := exists_pos_le_all ρ hρpos
  -- ## the per-piece good parameter sets
  set S : ι → Set (EuclideanSpace ℝ (Fin m)) :=
    fun i => {t | ‖t‖ < ρ i ∧ GoodSet m (Ψ i) (K i) t} with hSdef
  have hSopen : ∀ i, IsOpen (S i) := by
    intro i
    have h1 : IsOpen {t : EuclideanSpace ℝ (Fin m) | ‖t‖ < ρ i} :=
      isOpen_lt continuous_norm continuous_const
    exact h1.inter (hΨopen i)
  have hSdense : ∀ i, Metric.ball 0 (ρ i) ⊆ closure (S i) := by
    intro i x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hxρ : ‖x‖ < ρ i := by
      rw [Metric.mem_ball] at hx
      simpa [dist_eq_norm] using hx
    obtain ⟨t, htclose, htρ, hgood⟩ := hdense i x hxρ ε hε
    exact ⟨t, ⟨htρ, hgood⟩, by rw [dist_comm]; simpa [dist_eq_norm] using htclose⟩
  have hdenseint : Metric.ball 0 ρ₀ ⊆ closure (⋂ i, S i) :=
    dense_iInter_of_dense_ball S ρ₀ hSopen
      (fun i => (Metric.ball_subset_ball (hρ₀le i)).trans (hSdense i))
  -- ## the parameter
  set R : ℝ := min ε' (min ρ₀ δ₀) with hRdef
  have hRpos : 0 < R := by rw [hRdef]; exact lt_min hε' (lt_min hρ₀pos hδ₀pos)
  have hRε' : R ≤ ε' := by rw [hRdef]; exact min_le_left _ _
  have hRρ₀ : R ≤ ρ₀ := by rw [hRdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hRδ₀ : R ≤ δ₀ := by rw [hRdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have h0mem : (0 : EuclideanSpace ℝ (Fin m)) ∈ Metric.ball 0 ρ₀ := by
    rw [Metric.mem_ball, dist_self]; exact hρ₀pos
  obtain ⟨t, htint, htR⟩ := Metric.mem_closure_iff.mp (hdenseint h0mem) R hRpos
  have htR' : ‖t‖ < R := by simpa [dist_eq_norm] using htR
  have htε' : ‖t‖ < ε' := lt_of_lt_of_le htR' hRε'
  have htδ₀ : ‖t‖ < δ₀ := lt_of_lt_of_le htR' hRδ₀
  have htρ : ∀ i, ‖t‖ < ρ i := fun i => lt_of_lt_of_le htR' (le_trans hRρ₀ (hρ₀le i))
  have htS : ∀ i, t ∈ S i := fun i => Set.mem_iInter.mp htint i
  refine ⟨t, htε', ?_⟩
  -- ## every triple point of `G t` lies in one of the pieces
  have hKin : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      TParity.meet3 (G t) y → y ∈ ⋃ i, K i := by
    intro y hy hm
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hδ₀sub t htδ₀ y hy hm)
    exact Set.mem_iUnion.mpr ⟨i, interior_subset hi⟩
  exact Meet3Hyp.of_nineBox (G t) (hsmooth t)
    (TParity.transHyp_of_on_compact (G t) (⋃ i, K i) hKin (fun y hyK hybox hmeet => by
      obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyK
      exact (htrans i t (htρ i) (htS i).2).1 y hyi hybox hmeet))
    (TParity.faceHyp_of_on_compact (G t) (⋃ i, K i) hKin (fun y hyK hybox hmeet hbdry => by
      obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyK
      exact (htrans i t (htρ i) (htS i).2).2 y hyi hybox hmeet hbdry))
    (hseam t)


end Work.Drive
