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
set_option linter.style.haveILetI false

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

/-! ## The multi-family machinery

The family version of the localized parametric Sard of `Submission/Work/Drive/localSard.lean`.  The
finite chart-per-piece covers of all the families are merged into one finite index type `Σ j, ι j`, the
good-parameter sets are intersected over that finite type, and the single resulting parameter makes
every family satisfy `Meet3Hyp` at once.  The statement below is the *centred-at-`0`* form; the
prescribed open set and the prescribed centre of the public theorem are handled there by re-centring
every family at that centre. -/

/-- The derivative of `x' ↦ f (c + x')` at `x` is the derivative of `f` at `c + x` (the derivative of a
translation is the identity). -/
private lemma fderiv_comp_add_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {c x : E}
    (hf : DifferentiableAt ℝ f (c + x)) :
    fderiv ℝ (fun x' : E => f (c + x')) x = fderiv ℝ f (c + x) := by
  have hσ : HasFDerivAt (fun x' : E => c + x') (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_add c
  rw [show (fun x' : E => f (c + x')) = f ∘ (fun x' : E => c + x') from rfl]
  rw [fderiv_comp x hf hσ.differentiableAt, hσ.fderiv]
  exact ContinuousLinearMap.comp_id _

/-- **The multi-family localized parametric Sard, centred at `0`.**  For finitely many families of
parametrised triple chains (heterogeneous manifolds, one charted structure each) which are jointly rich
in parameters *near `0`*, there are arbitrarily small parameters `t` at which *every* family satisfies
`Meet3Hyp`.

This is the per-piece patched construction of `Work.Drive.localSard`, with the finitely many pieces of
the finitely many families merged into a single finite index type. -/
private theorem family_meet3Hyp {J : Type*} [Fintype J] (M : J → Type*)
    [∀ j, TopologicalSpace (M j)] [∀ j, T2Space (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin 4)) (M j)]
    [∀ j, IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (M j)]
    {m : ℕ} (G : ∀ j, EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M j)
    (hG : ∀ j k, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G j q.1 k q.2))
    (hsmooth : ∀ j (t : EuclideanSpace ℝ (Fin m)) (k : Fin 3),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (G j t k))
    (hseam : ∀ j (t : EuclideanSpace ℝ (Fin m)) (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Work.Drive.onSeam x → G j t k x = G j t k (Work.Drive.seamInv x))
    (hrich : ∀ j (p : M j) (K : Set (EuclideanSpace ℝ (Fin 9))) (δ : ℝ),
      IsCompact K → 0 < δ →
      (∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < δ → y ∈ K →
        ∀ k : Fin 3, G j t k (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source) →
      ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < δ → y ∈ K →
        Work.Drive.TParity.chartDiff3 p (G j t) y = 0 →
        Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          Work.Drive.TParity.chartDiff3 p (G j t') y) t)) :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin m), ‖t‖ < ε' ∧
      ∀ j, Work.Drive.Meet3Hyp (M j) (G j t) := by
  intro ε' hε'
  classical
  -- ## one finite chart-per-piece cover per family
  have hcont : ∀ j (k : Fin 3), Continuous
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G j q.1 k q.2) :=
    fun j k => (hG j k).continuous
  choose ι hιfin K δ p hK hδ hcover hres using fun j : J => baseCover (G j) (hcont j)
  haveI : ∀ j, Fintype (ι j) := hιfin
  -- ## one smooth cut-off system and one radius per piece of the merged cover
  choose ρ Ψ hρpos hΨsm hΨopen htrans hdense using fun ji : Sigma ι =>
    piece_data (G ji.1) (hG ji.1) (hsmooth ji.1) (hseam ji.1) (p ji.1 ji.2) (K ji.1 ji.2)
      (δ ji.1 ji.2) (hK ji.1 ji.2) (hδ ji.1 ji.2)
      (fun t y ht hy k => hres ji.1 ji.2 t y ht hy k)
      (hrich ji.1 (p ji.1 ji.2) (K ji.1 ji.2) (δ ji.1 ji.2) (hK ji.1 ji.2) (hδ ji.1 ji.2)
        (fun t y ht hy k => hres ji.1 ji.2 t y ht hy k))
  -- ## the base triple locus of each family is covered by the interiors of its own pieces
  have hUbigopen : ∀ j, IsOpen (⋃ i : ι j, interior (K j i)) :=
    fun j => isOpen_iUnion fun i => isOpen_interior
  have hbase : ∀ j, ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      Work.Drive.TParity.meet3 (G j 0) y → y ∈ ⋃ i : ι j, interior (K j i) := by
    intro j y hy hm
    obtain ⟨i, hi⟩ := hcover j y hy hm
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  -- ## a radius per family on which the perturbed triple locus stays inside its own pieces
  have hδ₀ex : ∀ j, ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ t : EuclideanSpace ℝ (Fin m), ‖t‖ < δ₀ →
        ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
          Work.Drive.TParity.meet3 (G j t) y → y ∈ ⋃ i : ι j, interior (K j i) := by
    intro j
    have hev := eventually_meet3_subset_of_isOpen (G j) (hcont j)
      (U := ⋃ i : ι j, interior (K j i)) (hUbigopen j) (hbase j)
    rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hev
    obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := hev
    exact ⟨δ₀, hδ₀pos,
      fun t ht y hy hm => hδ₀sub (by rwa [Metric.mem_ball, dist_zero_right]) y hy hm⟩
  choose δ₀ hδ₀pos hδ₀sub using hδ₀ex
  -- ## positive radii inside all the pieces and inside all the families' radii
  obtain ⟨ρ₀, hρ₀pos, hρ₀le⟩ := exists_pos_le_all ρ hρpos
  obtain ⟨δ₁, hδ₁pos, hδ₁le⟩ := exists_pos_le_all δ₀ hδ₀pos
  -- ## the per-piece good parameter sets
  set S : (Σ j, ι j) → Set (EuclideanSpace ℝ (Fin m)) :=
    fun ji => {t | ‖t‖ < ρ ji ∧ GoodSet m (Ψ ji) (K ji.1 ji.2) t} with hSdef
  have hSopen : ∀ ji, IsOpen (S ji) := by
    intro ji
    have h1 : IsOpen {t : EuclideanSpace ℝ (Fin m) | ‖t‖ < ρ ji} :=
      isOpen_lt continuous_norm continuous_const
    exact h1.inter (hΨopen ji)
  have hSdense : ∀ ji, Metric.ball 0 (ρ ji) ⊆ closure (S ji) := by
    intro ji x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hxρ : ‖x‖ < ρ ji := by
      rw [Metric.mem_ball] at hx
      simpa [dist_eq_norm] using hx
    obtain ⟨t, htclose, htρ, hgood⟩ := hdense ji x hxρ ε hε
    exact ⟨t, ⟨htρ, hgood⟩, by rw [dist_comm]; simpa [dist_eq_norm] using htclose⟩
  have hdenseint : Metric.ball 0 ρ₀ ⊆ closure (⋂ ji, S ji) :=
    dense_iInter_of_dense_ball S ρ₀ hSopen
      (fun ji => (Metric.ball_subset_ball (hρ₀le ji)).trans (hSdense ji))
  -- ## the parameter
  set R : ℝ := min ε' (min ρ₀ δ₁) with hRdef
  have hRpos : 0 < R := by rw [hRdef]; exact lt_min hε' (lt_min hρ₀pos hδ₁pos)
  have hRε' : R ≤ ε' := by rw [hRdef]; exact min_le_left _ _
  have hRρ₀ : R ≤ ρ₀ := by rw [hRdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hRδ₁ : R ≤ δ₁ := by rw [hRdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have h0mem : (0 : EuclideanSpace ℝ (Fin m)) ∈ Metric.ball 0 ρ₀ := by
    rw [Metric.mem_ball, dist_self]; exact hρ₀pos
  obtain ⟨t, htint, htR⟩ := Metric.mem_closure_iff.mp (hdenseint h0mem) R hRpos
  have htR' : ‖t‖ < R := by simpa [dist_eq_norm] using htR
  have htε' : ‖t‖ < ε' := lt_of_lt_of_le htR' hRε'
  have htδ₀ : ∀ j, ‖t‖ < δ₀ j := fun j => lt_of_lt_of_le htR' (le_trans hRδ₁ (hδ₁le j))
  have htρ : ∀ ji, ‖t‖ < ρ ji := fun ji => lt_of_lt_of_le htR' (le_trans hRρ₀ (hρ₀le ji))
  have htS : ∀ ji, t ∈ S ji := fun ji => Set.mem_iInter.mp htint ji
  refine ⟨t, htε', fun j => ?_⟩
  -- ## every triple point of `G j t` lies in one of that family's pieces
  have hKin : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      Work.Drive.TParity.meet3 (G j t) y → y ∈ ⋃ i : ι j, K j i := by
    intro y hy hm
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hδ₀sub j t (htδ₀ j) y hy hm)
    exact Set.mem_iUnion.mpr ⟨i, interior_subset hi⟩
  exact Meet3Hyp.of_nineBox (G j t) (hsmooth j t)
    (TParity.transHyp_of_on_compact (G j t) (⋃ i : ι j, K j i) hKin
      (fun y hyK hybox hmeet => by
        obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyK
        exact (htrans ⟨j, i⟩ t (htρ ⟨j, i⟩) (htS ⟨j, i⟩).2).1 y hyi hybox hmeet))
    (TParity.faceHyp_of_on_compact (G j t) (⋃ i : ι j, K j i) hKin
      (fun y hyK hybox hmeet hbdry => by
        obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyK
        exact (htrans ⟨j, i⟩ t (htρ ⟨j, i⟩) (htS ⟨j, i⟩).2).2 y hyi hybox hmeet hbdry))
    (hseam j t)


/-! # Guidance (H3 lane, from the project lead's `Drive/NOTES_LEAD_hloc_htube_hsurj.md` §3.2(iii)) —
localSard_family_in_open

This is the multi-family localised parametric Sard statement that H4 consumes in `exists_refTriple_joint`
(notes §3.2(v)): one parameter `t` near `0` inside a prescribed open set `O` such that **all** the
families in a finite family of manifolds satisfy `Meet3Hyp` simultaneously.

The single-family version is `Work.Drive.localSard` (`Submission/Work/Drive/localSard.lean`, proved,
sorry-free, axiom-clean) — **copy its proof as the template**.  Its shape: from the local chart-per-piece
cover `Work.Drive.baseCover` and the per-piece regular data `Work.Drive.piece_data`, build the finite
intersection of the open dense good-parameter sets over the pieces (`Work.Drive.dense_iInter_of_dense_ball`,
`Work.Drive.exists_pos_le_all`), pick a small parameter in it, and conclude `Meet3Hyp M (G t)` through
`Work.Drive.Meet3Hyp.of_nineBox` with the per-piece transversality/face data and
`Work.Drive.eventually_meet3_subset_of_isOpen` to keep the triple points inside the pieces.

The differences to implement here:

* the manifolds are *heterogeneous*: a finite type `ι` of indices, one manifold `M j` with its own chart
  structure and `IsManifold` instance per `j` (as instance binders), one parametrised chain family `G j`
  per `j`; the good sets are intersected over the finitely many pairs `(j, piece)` (both `ι` and the
  cover are finite), so the final `t` works for every `j` at once;
* the richness hypothesis `hrich` is *time-centred*: it holds for `‖t - t₀‖ < δ` at a prescribed centre
  `t₀`, not at `0`.  Follow the centring of the single-family statement: pick `t₀ ∈ O` small with a ball
  around it inside `O`, apply the machinery to the re-centred families `τ ↦ G j (t₀ + τ)`, and conclude
  with `t = t₀ + τ`;
* the conclusion additionally restricts `t` to the prescribed open set `O` (whose only other input is
  `hO0`: every ball around `0` meets `O`), i.e. `∃ t ∈ O, ‖t‖ < ε' ∧ ∀ j, Meet3Hyp (M j) (G j t)`.

Keep the statement generic in the manifolds: no `cappingCharted`, no `projTimesLineCharted`, no
`projCharted`.  State joint smoothness with `modelWithCornersSelf` on the *product normed space*
`EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)` (never `(𝓡 m).prod (𝓡 3)`, which would give
`ModelProd` charts).  If the internals of `localSard`'s proof (such as `piece_data`, `GoodSet`,
`exists_pos_le_all`, `dense_iInter_of_dense_ball`) are private, reproduce them here exactly as
`localSard.lean` itself reproduces the private machinery of `exists_meet3Data_of_good_family`.

Useful facts for the recentring step: `richness_sweepChartFam` (`hsurjCentred.lean:166`) is quantified
over *every* centre `t₀`; `Meet3Hyp` is a pure `Prop` about the family and the manifold, with no
dependence on the base locus at parameter `0`; `hO0` supplies the small centre inside `O`.-/
open scoped Manifold ContDiff Topology in
theorem localSard_family_in_open {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ j, TopologicalSpace (M j)] [∀ j, T2Space (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin 4)) (M j)]
    [∀ j, IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (M j)]
    {m : ℕ} (G : ∀ j, EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M j)
    (hG : ∀ j k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
       (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
       (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G j q.1 k q.2))
    (hsmooth : ∀ j t k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
       (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (G j t k))
    (hseam : ∀ j t k (x : EuclideanSpace ℝ (Fin 3)), Work.Drive.onSeam x →
       G j t k x = G j t k (Work.Drive.seamInv x))
    (hrich : ∀ j (p : M j) (K : Set (EuclideanSpace ℝ (Fin 9))) (t₀ : EuclideanSpace ℝ (Fin m)) (δ : ℝ),
       IsCompact K → 0 < δ →
       (∀ t y, ‖t - t₀‖ < δ → y ∈ K → ∀ k,
         G j t k (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source) →
       ∀ t y, ‖t - t₀‖ < δ → y ∈ K → Work.Drive.TParity.chartDiff3 p (G j t) y = 0 →
       Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
         Work.Drive.TParity.chartDiff3 p (G j t') y) t))
    (O : Set (EuclideanSpace ℝ (Fin m))) (hO : IsOpen O)
    (hO0 : ∀ ε' : ℝ, 0 < ε' → ∃ t ∈ O, ‖t‖ < ε') :
    ∀ ε' : ℝ, 0 < ε' → ∃ t ∈ O, ‖t‖ < ε' ∧ ∀ j, Work.Drive.Meet3Hyp (M j) (G j t) := by
  intro ε' hε'
  classical
  -- ## a small centre inside the prescribed open set, with a ball around it inside `O`
  obtain ⟨t₀, ht₀O, ht₀ε⟩ := hO0 (ε' / 2) (by linarith)
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds ht₀O)
  -- ## joint smoothness of the re-centred families
  have hG' : ∀ j k, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G j (t₀ + q.1) k q.2) := by
    intro j k
    have htrans : ContMDiff
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => (t₀ + q.1, q.2)) :=
      (contMDiff_iff_contDiff).mpr (by fun_prop)
    exact (hG j k).comp htrans
  have hsmooth' : ∀ j (τ : EuclideanSpace ℝ (Fin m)) (k : Fin 3),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (G j (t₀ + τ) k) :=
    fun j τ k => hsmooth j (t₀ + τ) k
  have hseam' : ∀ j (τ : EuclideanSpace ℝ (Fin m)) (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Work.Drive.onSeam x → G j (t₀ + τ) k x = G j (t₀ + τ) k (Work.Drive.seamInv x) :=
    fun j τ k x hx => hseam j (t₀ + τ) k x hx
  -- ## richness of the re-centred families at the centre `0`, from richness of `G` at `t₀`
  have hrich' : ∀ j (p : M j) (K : Set (EuclideanSpace ℝ (Fin 9))) (δ : ℝ),
      IsCompact K → 0 < δ →
      (∀ (τ : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ → y ∈ K →
        ∀ k : Fin 3, G j (t₀ + τ) k (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source) →
      ∀ (τ : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ → y ∈ K →
        Work.Drive.TParity.chartDiff3 p (G j (t₀ + τ)) y = 0 →
        Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin m) =>
          Work.Drive.TParity.chartDiff3 p (G j (t₀ + τ')) y) τ) := by
    intro j p K δ hK hδ hres τ y hτ hyK hzero
    have hres₀ : ∀ (t : EuclideanSpace ℝ (Fin m)) (y' : EuclideanSpace ℝ (Fin 9)),
        ‖t - t₀‖ < δ → y' ∈ K → ∀ k : Fin 3,
          G j t k (Work.Drive.TParity.bPartC k y') ∈ (Work.Drive.chr p).source := by
      intro t y' ht hy' k
      have ht' : t = t₀ + (t - t₀) := by abel
      rw [ht']
      exact hres (t - t₀) y' (by simpa using ht) hy' k
    have hsurj : Function.Surjective (fderiv ℝ (fun s : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.TParity.chartDiff3 p (G j s) y) (t₀ + τ)) := by
      refine hrich j p K t₀ δ hK hδ hres₀ (t₀ + τ) y ?_ hyK hzero
      simpa using hτ
    have hreg : ∀ k : Fin 3, G j (t₀ + τ) k (Work.Drive.TParity.bPartC k y) ∈
        (Work.Drive.chr p).source := hres τ y hτ hyK
    have hχ : DifferentiableAt ℝ (fun s : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.TParity.chartDiff3 p (G j s) y) (t₀ + τ) :=
      ((contDiffAt_chartDiff3_family_fin m (G j) (hG j) p (t₀ + τ) hreg).comp (t₀ + τ)
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt top_ne_zero_order
    rw [fderiv_comp_add_const (c := t₀) hχ]
    exact hsurj
  -- ## run the machinery on the re-centred families
  have hmin : 0 < min (ε' / 2) r := lt_min (by linarith) hrpos
  obtain ⟨τ, hτ, hτj⟩ := family_meet3Hyp M (fun j τ k x => G j (t₀ + τ) k x)
    hG' hsmooth' hseam' hrich' (min (ε' / 2) r) hmin
  -- ## conclusion: the parameter `t₀ + τ` lies in `O` and is small
  refine ⟨t₀ + τ, ?_, ?_, ?_⟩
  · refine hrsub ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : t₀ + τ - t₀ = τ := by abel
    rw [h1]
    exact lt_of_lt_of_le hτ (min_le_right _ _)
  · have h1 : ‖τ‖ < ε' / 2 := lt_of_lt_of_le hτ (min_le_left _ _)
    calc ‖t₀ + τ‖ ≤ ‖t₀‖ + ‖τ‖ := norm_add_le _ _
      _ < ε' / 2 + ε' / 2 := by linarith
      _ = ε' := by ring
  · intro j
    exact hτj j


end Work.Drive
