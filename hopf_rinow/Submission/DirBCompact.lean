import Submission.DirectionB
import Mathlib

open scoped Manifold ENNReal ContDiff Topology
open Set Metric Filter TopologicalSpace
open EMetric
open Bundle

namespace Submission
namespace DirectionB

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
set_option linter.deprecated false

open LeanEval.Geometry

lemma unitGeo_edist_le_abs {M : Type*} [EMetricSpace M] {γ : ℝ → M} (hγ : UnitGeo γ)
    {a b : ℝ} : edist (γ a) (γ b) ≤ ENNReal.ofReal |a - b| := by
  rcases le_total a b with hab | hba
  · have h1 := hγ.lipschitz_le hab
    have h : |a - b| = b - a := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
    rwa [h]
  · have h1 := hγ.lipschitz_le hba
    have h : |a - b| = a - b := by rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    rw [h]
    simpa [edist_comm] using h1


/-- A geodesic (locally linear with some speed everywhere) is continuous. -/

lemma isGeodesic_continuousAt {M : Type*} [EMetricSpace M] {γ : ℝ → M} (h : IsGeodesic γ)
    (t₀ : ℝ) : ContinuousAt γ t₀ := by
  rcases h with ⟨c, hc⟩
  have hll : Metric.IsLocLinear (t₀ - 1) (t₀ + 1) c γ := by
    intro t₁ ht₁
    rcases hc t₁ with ⟨δ, hδ, hwin⟩
    refine ⟨δ, hδ, ?_⟩
    intro s t hs ht
    have hsδ : |s - t₁| < δ := by
      have hslo : t₁ - δ < s := by
        have h1 : t₁ - δ ≤ max (t₀ - 1) (t₁ - δ) := le_max_right _ _
        exact lt_of_le_of_lt h1 hs.1
      have hshi : s < t₁ + δ := by
        have h1 : min (t₀ + 1) (t₁ + δ) ≤ t₁ + δ := min_le_right _ _
        exact lt_of_lt_of_le hs.2 h1
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have htδ : |t - t₁| < δ := by
      have htlo : t₁ - δ < t := by
        have h1 : t₁ - δ ≤ max (t₀ - 1) (t₁ - δ) := le_max_right _ _
        exact lt_of_le_of_lt h1 ht.1
      have hthi : t < t₁ + δ := by
        have h1 : min (t₀ + 1) (t₁ + δ) ≤ t₁ + δ := min_le_right _ _
        exact lt_of_lt_of_le ht.2 h1
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    exact hwin s t hsδ htδ
  exact Metric.IsLocLinear.continuousAt hll (by constructor <;> linarith)

/-- Boundary case of sup-closure: a sequence in the closed ball of radius s whose distances
to p tend to s has a convergent subsequence. -/

lemma dense_rat_time {s : ℝ} (hs : 0 < s) {t : ℝ} (ht0 : 0 < t) (hts : t < s) {η : ℝ}
    (hη : 0 < η) : ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < s ∧ |t - (q : ℝ)| < η := by
  let ε : ℝ := min (η / 2) ((s - t) / 2)
  have hε0 : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith) (by linarith)
  have hεη : ε < η := by
    have h1 : ε ≤ η / 2 := by dsimp [ε]; exact min_le_left _ _
    have h2 : η / 2 < η := by linarith
    exact lt_of_le_of_lt h1 h2
  have hlo : max 0 (t - ε) < min s (t + ε) := by
    have h1 : max 0 (t - ε) < t := by
      apply max_lt <;> linarith
    have h2 : t < min s (t + ε) := by
      apply lt_min <;> linarith
    exact lt_trans h1 h2
  rcases exists_rat_btwn hlo with ⟨q, hql, hqu⟩
  refine ⟨q, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left 0 (t - ε)) (le_of_lt hql)
  · exact lt_of_lt_of_le hqu (min_le_left s (t + ε))
  · have h1 : t - ε < (q : ℝ) := lt_of_le_of_lt (le_max_right 0 (t - ε)) hql
    have h2 : (q : ℝ) < t + ε := lt_of_lt_of_le hqu (min_le_right s (t + ε))
    have habs : |(q : ℝ) - t| < ε := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    rw [abs_sub_comm]
    exact lt_trans habs hεη

/-- A Cauchy sequence that is eventually inside a compact set converges. -/

lemma cauchy_tendsto_of_eventually_compact {M : Type*} [EMetricSpace M]
    {u : ℕ → M} (hu : CauchySeq u) {K : Set M} (hK : IsCompact K)
    (hEv : ∀ᶠ n in atTop, u n ∈ K) : ∃ a : M, Tendsto u atTop (𝓝 a) := by
  classical
  rcases eventually_atTop.1 hEv with ⟨N, hN⟩
  have hvK : ∀ m : ℕ, u (N + m) ∈ K := by intro m; exact hN (N + m) (by omega)
  have huC : CauchySeq (fun m : ℕ => u (N + m)) := by
    simpa [Nat.add_comm] using (cauchySeq_shift N).2 hu
  rcases hK.tendsto_subseq (x := fun m : ℕ => u (N + m)) hvK with ⟨a, _haK, φ, hφ, hφt⟩
  have hw : Tendsto (fun m : ℕ => u (N + m)) atTop (𝓝 a) :=
    tendsto_nhds_of_cauchySeq_of_subseq huC hφ.tendsto_atTop hφt
  have hw' : Tendsto (fun n : ℕ => u (n + N)) atTop (𝓝 a) := by
    simpa [Nat.add_comm] using hw
  exact ⟨a, (tendsto_add_atTop_iff_nat N).1 hw'⟩

/-- Diagonal extraction: a sequence of unit geodesics `g n` from `p`, with distances of the
endpoints `v n` tending to `s`, has a subsequence converging pointwise at every rational time
in `(0,s)`. -/

lemma geo_diag_subseq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hgc : IsGeodesicallyComplete M) (hnon : ∃ v : E, v ≠ 0) (p : M)
    {s : ℝ} (hs : 0 < s)
    (hall : ∀ t : ℝ, 0 ≤ t → t < s → IsCompact (closedBall p (ENNReal.ofReal t)))
    (v : ℕ → M) (hv : ∀ n, v n ∈ closedBall p (ENNReal.ofReal s))
    (hfin : ∀ n : ℕ, edist p (v n) < ⊤)
    (g : ℕ → ℝ → M) (hg_unit : ∀ n : ℕ, UnitGeo (g n))
    (hgd : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ (edist p (v n)).toReal →
      edist p (g n t) = ENNReal.ofReal t)
    (hτ : Tendsto (fun n : ℕ => (edist p (v n)).toReal) atTop (𝓝 s)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < s} → M,
      ∀ a : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < s},
        Tendsto (fun m : ℕ => g (φ m) (a.1 : ℝ)) atTop (𝓝 (Q a)) := by
  classical
  let α : Type := {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < s}
  haveI : Countable α := by infer_instance
  let D : α → ℝ := fun a => (a.1 : ℝ)
  have hKα : ∀ a : α, IsCompact (closedBall p (ENNReal.ofReal (D a))) := by
    intro a
    exact hall (D a) (le_of_lt a.2.1) a.2.2
  haveI : ∀ a : α, CompactSpace ((closedBall p (ENNReal.ofReal (D a)) : Set M)) := by
    intro a
    exact isCompact_iff_compactSpace.mp (hKα a)
  have hpmem : ∀ a : α, p ∈ (closedBall p (ENNReal.ofReal (D a)) : Set M) := by
    intro a
    exact EMetric.mem_closedBall.mpr (by simpa using (ENNReal.ofReal_nonneg : 0 ≤ ENNReal.ofReal (D a)))
  let W : ℕ → (a : α) → (closedBall p (ENNReal.ofReal (D a)) : Set M) :=
    fun m a => if h : g m (D a) ∈ (closedBall p (ENNReal.ofReal (D a)) : Set M) then ⟨g m (D a), h⟩
      else ⟨p, hpmem a⟩
  haveI : CompactSpace ((a : α) → (closedBall p (ENNReal.ofReal (D a)) : Set M)) := by infer_instance
  rcases (isCompact_univ : IsCompact (univ : Set ((a : α) → (closedBall p (ENNReal.ofReal (D a)) : Set M)))).tendsto_subseq
      (x := W) (by intro m; trivial) with ⟨Q0, _hQ, φ, hφ, hφt⟩
  refine ⟨φ, hφ, fun a => (Q0 a : (closedBall p (ENNReal.ofReal (D a)) : Set M)), ?_⟩
  intro a
  -- coordinate convergence
  have hcoord : Tendsto (fun m : ℕ => W (φ m) a) atTop (𝓝 (Q0 a)) := tendsto_pi_nhds.mp hφt a
  have hunder : Tendsto (fun m : ℕ => ((W (φ m) a : (closedBall p (ENNReal.ofReal (D a)) : Set M)) : M))
      atTop (𝓝 ((Q0 a : (closedBall p (ENNReal.ofReal (D a)) : Set M)) : M)) :=
    (continuous_subtype_val.tendsto (Q0 a)).comp hcoord
  -- eventually g (φ m) (D a) = W value: need D a ≤ (edist p (v (φ m))).toReal eventually
  have hconvτ : Tendsto (fun m : ℕ => (edist p (v (φ m))).toReal) atTop (𝓝 s) :=
    hτ.comp hφ.tendsto_atTop
  have hEvT : ∀ᶠ m : ℕ in atTop, D a ≤ (edist p (v (φ m))).toReal := by
    have h := (tendsto_order.mp hconvτ).1 (D a) a.2.2
    filter_upwards [h] with m hm
    exact le_of_lt hm
  have hEqEv : ∀ᶠ m : ℕ in atTop, g (φ m) (D a) = ((W (φ m) a : (closedBall p (ENNReal.ofReal (D a)) : Set M)) : M) := by
    filter_upwards [hEvT] with m hm
    unfold W
    have hmmem : g (φ m) (D a) ∈ (closedBall p (ENNReal.ofReal (D a)) : Set M) := by
      exact EMetric.mem_closedBall.mpr (by
        have hd : edist p (g (φ m) (D a)) = ENNReal.ofReal (D a) := hgd (φ m) (D a) (le_of_lt a.2.1) hm
        simpa [edist_comm] using (le_of_eq hd))
    simp [hmmem]
  have hEqEv' : ∀ᶠ m : ℕ in atTop, ((W (φ m) a : (closedBall p (ENNReal.ofReal (D a)) : Set M)) : M) =
      g (φ m) (D a) := by
    filter_upwards [hEqEv] with m hm
    exact hm.symm
  exact Tendsto.congr' hEqEv' hunder



lemma ball_compact_expand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M]
    (hgc : IsGeodesicallyComplete M) (hnon : ∃ v : E, v ≠ 0) (p : M)
    {s : ℝ} (hs0 : 0 ≤ s)
    (hK : IsCompact (closedBall p (ENNReal.ofReal s))) :
    ∃ ε : ℝ, 0 < ε ∧ IsCompact (closedBall p (ENNReal.ofReal (s + ε))) := by
  classical
  let K : Set M := closedBall p (ENNReal.ofReal s)
  have hKmem : p ∈ K := by
    dsimp [K]
    exact EMetric.mem_closedBall.mpr (by simpa using (ENNReal.ofReal_nonneg : 0 ≤ ENNReal.ofReal s))
  -- compact superset C with K ⊆ interior C
  rcases exists_compact_superset hK with ⟨C, hC, hKint⟩
  have hFclosed : IsClosed (interior C : Set M)ᶜ := isClosed_compl_iff.mpr isOpen_interior
  have hKF : Disjoint K (interior C : Set M)ᶜ := by
    exact Set.disjoint_left.2 (fun x hxK hxF => hxF (hKint hxK))
  rcases EMetric.exists_pos_forall_lt_edist (s := K) hK hFclosed hKF with ⟨r, hr0, hr⟩
  let ε : ℝ := (r : ℝ) / 2
  have hε0 : 0 < ε := by
    dsimp [ε]
    exact half_pos hr0
  refine ⟨ε, hε0, ?_⟩
  apply IsCompact.of_isClosed_subset hC
  · exact EMetric.isClosed_closedBall
  · intro y hy
    have hys : edist y p ≤ ENNReal.ofReal (s + ε) := (EMetric.mem_closedBall.mp hy)
    have hysp : edist p y ≤ ENNReal.ofReal (s + ε) := by simpa [edist_comm] using hys
    have hfinite : edist p y < ⊤ := lt_of_le_of_lt hysp ENNReal.ofReal_lt_top
    have hts : 0 ≤ s + ε := by linarith
    have ht_le : (edist p y).toReal ≤ s + ε := by
      have h1 := ENNReal.toReal_mono (ne_of_lt ENNReal.ofReal_lt_top) hysp
      rwa [ENNReal.toReal_ofReal hts] at h1
    by_cases hle : edist y p ≤ ENNReal.ofReal s
    · have hyK : y ∈ K := by
        dsimp [K]
        exact EMetric.mem_closedBall.mpr hle
      exact interior_subset (hKint hyK)
    · have hlt : ENNReal.ofReal s < edist y p := lt_of_not_ge hle
      have hs_t : s ≤ (edist p y).toReal := by
        have h1 : ENNReal.ofReal s ≤ edist p y := by simpa [edist_comm] using (le_of_lt hlt)
        have h2 := ENNReal.toReal_mono (ne_of_lt hfinite) h1
        rwa [ENNReal.toReal_ofReal hs0] at h2
      rcases reachable_dirB I M hgc hnon p y hfinite with ⟨γ, hγu, _hγ0, hγd, hγe⟩
      let x : M := γ s
      have hxK : x ∈ K := by
        dsimp [K]
        exact EMetric.mem_closedBall.mpr (by
          have hd := hγd s hs0 hs_t
          simpa [edist_comm] using (le_of_eq hd))
      have ht_y : γ ((edist p y).toReal) = y := by
        exact EMetricSpace.eq_of_edist_eq_zero (by simpa [edist_comm] using hγe)
      have hxy : edist x y ≤ ENNReal.ofReal ε := by
        have hle2 : edist (γ s) (γ ((edist p y).toReal)) ≤
            ENNReal.ofReal ((edist p y).toReal - s) := hγu.lipschitz_le hs_t
        have hsub2 : (edist p y).toReal - s ≤ ε := by linarith
        calc
          edist x y = edist (γ s) (γ ((edist p y).toReal)) := by
            dsimp [x]
            rw [ht_y]
          _ ≤ ENNReal.ofReal ((edist p y).toReal - s) := hle2
          _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hsub2
      by_contra hyC
      have hyF' : y ∈ (interior C : Set M)ᶜ := by
        exact fun h => hyC (interior_subset h)
      have hlt2 : (r : ℝ≥0∞) < edist x y := hr x hxK y hyF'
      have hεr : ENNReal.ofReal ε < (r : ℝ≥0∞) := by
        have hεr' : ε < (r : ℝ) := by dsimp [ε]; linarith
        have hεr'' : ENNReal.ofReal ε < ENNReal.ofReal (r : ℝ) :=
          (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hr0 : 0 < (r : ℝ))).mpr hεr'
        simpa [ENNReal.ofReal_coe_nnreal] using hεr''
      have hlt3 : edist x y < (r : ℝ≥0∞) := lt_of_le_of_lt hxy hεr
      exact (not_lt_of_ge (le_of_lt hlt2)) hlt3


lemma geo_seq_limit_at_boundary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hgc : IsGeodesicallyComplete M) (hnon : ∃ v : E, v ≠ 0) (p : M)
    {s : ℝ} (hs : 0 < s)
    (hball : ∀ t : ℝ, 0 ≤ t → t < s → IsCompact (closedBall p (ENNReal.ofReal t)))
    (v : ℕ → M) (hv : ∀ n, v n ∈ closedBall p (ENNReal.ofReal s))
    (hτ : Tendsto (fun n : ℕ => (edist p (v n)).toReal) atTop (𝓝 s)) :
    ∃ a : M, a ∈ closedBall p (ENNReal.ofReal s) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (v ∘ φ) atTop (𝓝 a) := by
  classical
  let τv : ℕ → ℝ := fun n => (edist p (v n)).toReal
  have hfin : ∀ n : ℕ, edist p (v n) < ⊤ := by
    intro n
    have hd : edist (v n) p ≤ ENNReal.ofReal s := EMetric.mem_closedBall.mp (hv n)
    exact lt_of_le_of_lt (by simpa [edist_comm] using hd) ENNReal.ofReal_lt_top
  let gspec : ∀ n : ℕ, (∃ γ : ℝ → M, UnitGeo γ ∧ γ 0 = p ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ (edist p (v n)).toReal → edist p (γ t) = ENNReal.ofReal t) ∧
      edist (γ ((edist p (v n)).toReal)) (v n) = 0) := fun n =>
        reachable_dirB I M hgc hnon p (v n) (hfin n)
  let g : ℕ → ℝ → M := fun n => (gspec n).choose
  have hg_unit : ∀ n : ℕ, UnitGeo (g n) := fun n => (gspec n).choose_spec.1
  have hg0 : ∀ n : ℕ, g n 0 = p := fun n => (gspec n).choose_spec.2.1
  have hgd : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ (edist p (v n)).toReal →
      edist p (g n t) = ENNReal.ofReal t := fun n => (gspec n).choose_spec.2.2.1
  have hgend : ∀ n : ℕ, g n ((edist p (v n)).toReal) = v n := by
    intro n
    exact EMetricSpace.eq_of_edist_eq_zero (by simpa [edist_comm] using (gspec n).choose_spec.2.2.2)
  rcases geo_diag_subseq I M hgc hnon p hs hball v hv hfin g hg_unit hgd hτ with ⟨φ, hφmono, Q, hQconv⟩
  have hconvτ : Tendsto (fun m : ℕ => τv (φ m)) atTop (𝓝 s) := hτ.comp hφmono.tendsto_atTop
  have hτ_ge {q : ℝ} (hq : q < s) : ∀ᶠ m : ℕ in atTop, q ≤ τv (φ m) := by
    have h := (tendsto_order.mp hconvτ).1 q hq
    filter_upwards [h] with m hm
    exact le_of_lt hm
  let β : Type := {t : ℝ // 0 < t ∧ t < s}
  have hlim : ∀ t0 : β, ∃ a : M, Tendsto (fun m : ℕ => g (φ m) (t0.1 : ℝ)) atTop (𝓝 a) := by
    intro t0
    let mid : ℝ := (t0.1 + s) / 2
    have hmid0 : 0 ≤ mid := by
      dsimp [mid]
      have hpos : 0 < t0.1 + s := add_pos t0.2.1 hs
      exact le_of_lt (div_pos hpos zero_lt_two)
    have hmid_lt : mid < s := by
      dsimp [mid]
      field_simp
      linarith [t0.2.2]
    have hmid_t : t0.1 < mid := by
      dsimp [mid]
      field_simp
      linarith [t0.2.2]
    have hCauchy : CauchySeq (fun m : ℕ => g (φ m) (t0.1 : ℝ)) := by
      rw [uniformity_basis_edist_nnreal.cauchySeq_iff']
      intro ε hε
      have hεpos : 0 < (ε : ℝ) := by exact_mod_cast hε
      let η : ℝ := min ((ε : ℝ) / 8) (t0.1 / 2)
      have hη0 : 0 < η := by
        dsimp [η]
        have h1 : 0 < (ε : ℝ) / 8 := div_pos hεpos (by norm_num)
        have h2 : 0 < t0.1 / 2 := div_pos t0.2.1 (by norm_num)
        exact lt_min h1 h2
      have hηε : η ≤ (ε : ℝ) / 8 := by dsimp [η]; exact min_le_left _ _
      have hηt : η ≤ t0.1 / 2 := by dsimp [η]; exact min_le_right _ _
      rcases dense_rat_time hs t0.2.1 t0.2.2 hη0 with ⟨q, hq0, hqs, hqt⟩
      have hqpos : 0 < (q : ℝ) := by
        have habs := abs_sub_lt_iff.mp hqt
        linarith
      let a : {q0 : ℚ // 0 < (q0 : ℝ) ∧ (q0 : ℝ) < s} := ⟨q, ⟨hqpos, hqs⟩⟩
      have hconvq := hQconv a
      have hbound_q : ∀ᶠ m : ℕ in atTop,
          edist (g (φ m) (q : ℝ)) (Q a) < ENNReal.ofReal ((ε : ℝ) / 8) := by
        exact EMetric.tendsto_nhds.mp hconvq (ENNReal.ofReal ((ε : ℝ) / 8)) (by positivity)
      rcases eventually_atTop.1 hbound_q with ⟨Nq, hNq⟩
      rcases eventually_atTop.1 (hτ_ge hqs) with ⟨Nτ, hNτ⟩
      let N : ℕ := max Nq Nτ
      refine ⟨N, fun n hn => ?_⟩
      have hnN : N ≤ n := hn
      have hEq : edist (g (φ n) (t0.1 : ℝ)) (g (φ N) (t0.1 : ℝ)) < (ε : ℝ≥0∞) := by
        have hnq : edist (g (φ n) (q : ℝ)) (Q a) < ENNReal.ofReal ((ε : ℝ) / 8) :=
          hNq n (le_trans (le_max_left Nq Nτ) hn)
        have hNq' : edist (Q a) (g (φ N) (q : ℝ)) < ENNReal.ofReal ((ε : ℝ) / 8) := by
          simpa [edist_comm] using (hNq N (le_max_left Nq Nτ))
        have hnτ : (q : ℝ) ≤ τv (φ n) := hNτ n (le_trans (le_max_right Nq Nτ) hn)
        have hNτ' : (q : ℝ) ≤ τv (φ N) := hNτ N (le_max_right Nq Nτ)
        have hle_n : edist (g (φ n) (t0.1 : ℝ)) (g (φ n) (q : ℝ)) < ENNReal.ofReal ((ε : ℝ) / 8) := by
          have h1 := unitGeo_edist_le_abs (hg_unit (φ n)) (a := (t0.1 : ℝ)) (b := (q : ℝ))
          have hleabs : |t0.1 - (q : ℝ)| < (ε : ℝ) / 8 := by linarith [hqt, hηε]
          exact lt_of_le_of_lt h1 ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hleabs)
        have hle_N : edist (g (φ N) (q : ℝ)) (g (φ N) (t0.1 : ℝ)) < ENNReal.ofReal ((ε : ℝ) / 8) := by
          have h1 := unitGeo_edist_le_abs (hg_unit (φ N)) (a := (t0.1 : ℝ)) (b := (q : ℝ))
          have hleabs : |t0.1 - (q : ℝ)| < (ε : ℝ) / 8 := by linarith [hqt, hηε]
          have hstrict : edist (g (φ N) (t0.1 : ℝ)) (g (φ N) (q : ℝ)) < ENNReal.ofReal ((ε : ℝ) / 8) :=
            lt_of_le_of_lt h1 ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hleabs)
          simpa [edist_comm] using hstrict
        have hmid : edist (g (φ n) (q : ℝ)) (g (φ N) (q : ℝ)) < ENNReal.ofReal ((ε : ℝ) / 4) := by
          have htri := edist_triangle (g (φ n) (q : ℝ)) (Q a) (g (φ N) (q : ℝ))
          have hsum : edist (g (φ n) (q : ℝ)) (Q a) + edist (Q a) (g (φ N) (q : ℝ)) <
              ENNReal.ofReal ((ε : ℝ) / 4) := by
            have h1 : ENNReal.ofReal ((ε : ℝ) / 8) + ENNReal.ofReal ((ε : ℝ) / 8) =
                ENNReal.ofReal ((ε : ℝ) / 4) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1
              ring
            rw [← h1]
            exact ENNReal.add_lt_add hnq hNq'
          exact lt_of_le_of_lt htri hsum
        have htri1 := edist_triangle (g (φ n) (t0.1 : ℝ)) (g (φ n) (q : ℝ)) (g (φ N) (q : ℝ))
        have htri2 := edist_triangle (g (φ n) (q : ℝ)) (g (φ N) (q : ℝ)) (g (φ N) (t0.1 : ℝ))
        have hthree : edist (g (φ n) (t0.1 : ℝ)) (g (φ n) (q : ℝ)) +
            edist (g (φ n) (q : ℝ)) (g (φ N) (q : ℝ)) +
            edist (g (φ N) (q : ℝ)) (g (φ N) (t0.1 : ℝ)) < ENNReal.ofReal ((ε : ℝ) / 2) := by
          have h1 : ENNReal.ofReal ((ε : ℝ) / 8) + ENNReal.ofReal ((ε : ℝ) / 4) +
              ENNReal.ofReal ((ε : ℝ) / 8) = ENNReal.ofReal ((ε : ℝ) / 2) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
          rw [← h1]
          exact ENNReal.add_lt_add (ENNReal.add_lt_add hle_n hmid) hle_N
        have hsum' : edist (g (φ n) (t0.1 : ℝ)) (g (φ N) (t0.1 : ℝ)) ≤
            edist (g (φ n) (t0.1 : ℝ)) (g (φ n) (q : ℝ)) +
            edist (g (φ n) (q : ℝ)) (g (φ N) (q : ℝ)) +
            edist (g (φ N) (q : ℝ)) (g (φ N) (t0.1 : ℝ)) := by
          calc
            edist (g (φ n) (t0.1 : ℝ)) (g (φ N) (t0.1 : ℝ)) ≤
                edist (g (φ n) (t0.1 : ℝ)) (g (φ n) (q : ℝ)) +
                edist (g (φ n) (q : ℝ)) (g (φ N) (t0.1 : ℝ)) := edist_triangle _ _ _
            _ ≤ edist (g (φ n) (t0.1 : ℝ)) (g (φ n) (q : ℝ)) +
                (edist (g (φ n) (q : ℝ)) (g (φ N) (q : ℝ)) +
                 edist (g (φ N) (q : ℝ)) (g (φ N) (t0.1 : ℝ))) := by
                exact add_le_add_right (edist_triangle (g (φ n) (q : ℝ)) (g (φ N) (q : ℝ)) (g (φ N) (t0.1 : ℝ)))
                  (edist (g (φ n) (t0.1 : ℝ)) (g (φ n) (q : ℝ)))
            _ = edist (g (φ n) (t0.1 : ℝ)) (g (φ n) (q : ℝ)) +
                edist (g (φ n) (q : ℝ)) (g (φ N) (q : ℝ)) +
                edist (g (φ N) (q : ℝ)) (g (φ N) (t0.1 : ℝ)) := by
                rw [← add_assoc]
        have hlt_half : ENNReal.ofReal ((ε : ℝ) / 2) < (ε : ℝ≥0∞) := by
          have h : (ε : ℝ≥0∞) = ENNReal.ofReal (ε : ℝ) := by rw [ENNReal.ofReal_coe_nnreal]
          rw [h]
          exact (ENNReal.ofReal_lt_ofReal_iff hεpos).mpr (by linarith)
        exact lt_trans (lt_of_le_of_lt hsum' hthree) hlt_half
      -- membership: n ↦ membership in the Cauchy definition is (u n, u N) ∈ {p | edist p.1 p.2 < ↑i}
      simpa [SetRel] using hEq
    have hEvC : ∀ᶠ m : ℕ in atTop, g (φ m) (t0.1 : ℝ) ∈ closedBall p (ENNReal.ofReal mid) := by
      rcases eventually_atTop.1 (hτ_ge hmid_lt) with ⟨N, hN⟩
      refine eventually_atTop.mpr ⟨N, fun m hm => ?_⟩
      exact EMetric.mem_closedBall.mpr (by
        have hd : edist p (g (φ m) (t0.1 : ℝ)) = ENNReal.ofReal (t0.1 : ℝ) :=
          hgd (φ m) (t0.1 : ℝ) (le_of_lt t0.2.1) (le_trans (le_of_lt hmid_t) (hN m hm))
        have hle : ENNReal.ofReal (t0.1 : ℝ) ≤ ENNReal.ofReal mid := ENNReal.ofReal_le_ofReal (le_of_lt hmid_t)
        simpa [edist_comm] using (le_trans (le_of_eq hd) hle))
    exact cauchy_tendsto_of_eventually_compact hCauchy (hball mid hmid0 hmid_lt) hEvC
  let γ : β → M := fun t0 => Classical.choose (hlim t0)
  have hγlim : ∀ t0 : β, Tendsto (fun m : ℕ => g (φ m) (t0.1 : ℝ)) atTop (𝓝 (γ t0)) :=
    fun t0 => Classical.choose_spec (hlim t0)
  have hγdist : ∀ t0 : β, edist p (γ t0) = ENNReal.ofReal (t0.1 : ℝ) := by
    intro t0
    have hconv := hγlim t0
    have hlimdist : Tendsto (fun m : ℕ => edist p (g (φ m) (t0.1 : ℝ))) atTop (𝓝 (edist p (γ t0))) := by
      have hcont : Continuous (fun x : M => edist p x) :=
        Continuous.edist (continuous_const : Continuous (fun _ : M => p)) continuous_id
      exact hcont.continuousAt.tendsto.comp hconv
    have hconst : ∀ᶠ m : ℕ in atTop, edist p (g (φ m) (t0.1 : ℝ)) = ENNReal.ofReal (t0.1 : ℝ) := by
      rcases eventually_atTop.1 (hτ_ge t0.2.2) with ⟨N, hN⟩
      refine eventually_atTop.mpr ⟨N, fun m hm => ?_⟩
      exact hgd (φ m) (t0.1 : ℝ) (le_of_lt t0.2.1) (hN m hm)
    have hlrev : (fun _ : ℕ => ENNReal.ofReal (t0.1 : ℝ)) =ᶠ[atTop]
        (fun m : ℕ => edist p (g (φ m) (t0.1 : ℝ))) := hconst.mono (fun m hm => hm.symm)
    have hlim2 : Tendsto (fun m : ℕ => edist p (g (φ m) (t0.1 : ℝ))) atTop (𝓝 (ENNReal.ofReal (t0.1 : ℝ))) :=
      Tendsto.congr' hlrev tendsto_const_nhds
    exact tendsto_nhds_unique hlimdist hlim2
  have hγlipschitz : ∀ a b : β, edist (γ a) (γ b) ≤ ENNReal.ofReal |a.1 - b.1| := by
    intro a b
    have hA := hγlim a
    have hB := hγlim b
    have hpair' : Tendsto (fun m : ℕ => (g (φ m) (a.1 : ℝ), g (φ m) (b.1 : ℝ))) atTop
        (𝓝 (γ a) ×ˢ 𝓝 (γ b)) := hA.prodMk hB
    have hpair : Tendsto (fun m : ℕ => (g (φ m) (a.1 : ℝ), g (φ m) (b.1 : ℝ))) atTop (𝓝 (γ a, γ b)) := by
      simpa [nhds_prod_eq] using hpair'
    have hEdist : Tendsto (fun m : ℕ => edist (g (φ m) (a.1 : ℝ)) (g (φ m) (b.1 : ℝ)))
        atTop (𝓝 (edist (γ a) (γ b))) := by
      exact continuous_edist.continuousAt.tendsto.comp hpair
    have hmem : ∀ᶠ m : ℕ in atTop,
        edist (g (φ m) (a.1 : ℝ)) (g (φ m) (b.1 : ℝ)) ∈ (Set.Iic (ENNReal.ofReal |a.1 - b.1|) : Set ℝ≥0∞) := by
      exact Eventually.of_forall (fun m => by
        simpa using unitGeo_edist_le_abs (hg_unit (φ m)) (a := (a.1 : ℝ)) (b := (b.1 : ℝ)))
    exact isClosed_Iic.mem_of_tendsto hEdist hmem
  -- 4. γ realises distance between parameter points
  have hγrealizes : ∀ a b : β, a.1 ≤ b.1 → edist (γ a) (γ b) = ENNReal.ofReal (b.1 - a.1) := by
    intro a b hab
    have hle' : edist (γ a) (γ b) ≤ ENNReal.ofReal (b.1 - a.1) := by
      have h1 := hγlipschitz a b
      have h : |a.1 - b.1| = b.1 - a.1 := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
      rwa [h] at h1
    have hge' : ENNReal.ofReal (b.1 - a.1) ≤ edist (γ a) (γ b) := by
      have htri := edist_triangle p (γ a) (γ b)
      have h1 : edist p (γ b) ≤ edist p (γ a) + edist (γ a) (γ b) := htri
      have h2 : edist p (γ b) - edist p (γ a) ≤ edist (γ a) (γ b) :=
        tsub_le_iff_right.mpr (by simpa [add_comm] using h1)
      have hd : edist p (γ b) - edist p (γ a) = ENNReal.ofReal (b.1 - a.1) := by
        rw [hγdist b, hγdist a]
        exact (ENNReal.ofReal_sub b.1 (show 0 ≤ a.1 by exact le_of_lt a.2.1)).symm
      have h2' : ENNReal.ofReal (b.1 - a.1) ≤ edist (γ a) (γ b) := by
        rwa [hd] at h2
      exact h2'
    exact le_antisymm hle' hge'
  -- 5. build the extension: locally linear on (0,s), then hgc extends it to ℝ
  let gammaHat : ℝ → M := fun t => if ht : 0 < t ∧ t < s then γ ⟨t, ht⟩ else γ ⟨s / 2, ⟨half_pos hs, by linarith⟩⟩
  have hgammaHat_agr : ∀ t : ℝ, ∀ (ht0 : 0 < t) (hts : t < s),
      gammaHat t = γ ⟨t, ⟨ht0, hts⟩⟩ := by
    intro t ht0 hts
    dsimp [gammaHat]
    rw [dif_pos ⟨ht0, hts⟩]
  have hgeo_prem : ∃ c : NNReal, ∀ t₀ ∈ Ioo (0 : ℝ) s, ∃ δ > 0,
      ∀ s' t' : ℝ, s' ∈ Ioo (max (0 : ℝ) (t₀ - δ)) (min s (t₀ + δ)) →
        t' ∈ Ioo (max (0 : ℝ) (t₀ - δ)) (min s (t₀ + δ)) →
        edist (gammaHat s') (gammaHat t') = (c : ℝ≥0∞) * ENNReal.ofReal |t' - s'| := by
    refine ⟨1, ?_⟩
    intro t₀ ht₀
    let δ : ℝ := min (t₀ / 2) ((s - t₀) / 2)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (div_pos ht₀.1 (by norm_num)) (div_pos (sub_pos.mpr ht₀.2) (by norm_num))
    refine ⟨δ, hδ, ?_⟩
    intro s' t' hs' ht'
    have hs'_pos : 0 < s' := lt_of_le_of_lt (le_max_left 0 (t₀ - δ)) hs'.1
    have hs'_lt : s' < s := lt_of_lt_of_le hs'.2 (min_le_left s (t₀ + δ))
    have ht'_pos : 0 < t' := lt_of_le_of_lt (le_max_left 0 (t₀ - δ)) ht'.1
    have ht'_lt : t' < s := lt_of_lt_of_le ht'.2 (min_le_left s (t₀ + δ))
    have hs'γ : gammaHat s' = γ ⟨s', ⟨hs'_pos, hs'_lt⟩⟩ := hgammaHat_agr s' hs'_pos hs'_lt
    have ht'γ : gammaHat t' = γ ⟨t', ⟨ht'_pos, ht'_lt⟩⟩ := hgammaHat_agr t' ht'_pos ht'_lt
    rw [hs'γ, ht'γ]
    rcases le_total s' t' with hst | hts'
    · have hE := hγrealizes ⟨s', ⟨hs'_pos, hs'_lt⟩⟩ ⟨t', ⟨ht'_pos, ht'_lt⟩⟩ hst
      have h : |t' - s'| = t' - s' := by rw [abs_of_nonneg (sub_nonneg.mpr hst)]
      rw [h]
      simpa using hE
    · have hE := hγrealizes ⟨t', ⟨ht'_pos, ht'_lt⟩⟩ ⟨s', ⟨hs'_pos, hs'_lt⟩⟩ hts'
      have hE' : edist (γ ⟨s', ⟨hs'_pos, hs'_lt⟩⟩) (γ ⟨t', ⟨ht'_pos, ht'_lt⟩⟩) =
          ENNReal.ofReal (s' - t') := by simpa [edist_comm] using hE
      have h : |t' - s'| = s' - t' := by rw [abs_of_nonpos (sub_nonpos.mpr hts')]; ring
      rw [h]
      simpa using hE'
  rcases hgc 0 s gammaHat hs hgeo_prem with ⟨γext, hγextgeo, hγextagr⟩
  let a0 : M := γext s
  have hγext_cont : ContinuousAt γext s := isGeodesic_continuousAt hγextgeo s
  -- γext restricted to times below s (staying positive) tends to a0
  let 𝓕 : Filter ℝ := 𝓝[Ioo (0 : ℝ) s] s
  have h𝓕ne : 𝓕.NeBot := by
    dsimp [𝓕]
    rw [nhdsWithin_neBot]
    intro t ht
    rcases Metric.mem_nhds_iff.mp ht with ⟨η, hη0, hball⟩
    let x : ℝ := s - min (η / 2) (s / 2)
    refine ⟨x, ?_, ?_⟩
    · exact hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        have hx : |x - s| = min (η / 2) (s / 2) := by
          dsimp [x]
          rw [abs_sub_comm]
          have hm : 0 ≤ min (η / 2) (s / 2) := by positivity
          rw [abs_of_nonneg]
          · ring
          · rw [show s - (s - min (η / 2) (s / 2)) = min (η / 2) (s / 2) by ring]
            exact hm
        rw [hx]
        have hle : min (η / 2) (s / 2) ≤ η / 2 := min_le_left _ _
        have hle2 : η / 2 < η := by linarith
        exact lt_of_le_of_lt hle hle2)
    · have hx0 : 0 < x := by
        dsimp [x]
        have hle : min (η / 2) (s / 2) ≤ s / 2 := min_le_right _ _
        have hlt : min (η / 2) (s / 2) < s := lt_of_le_of_lt hle (half_lt_self hs)
        linarith
      have hxs : x < s := by
        dsimp [x]
        have hpos : 0 < min (η / 2) (s / 2) := by positivity
        linarith
      exact ⟨hx0, hxs⟩
  haveI : 𝓕.NeBot := h𝓕ne
  have hγext_in_tendsto : Tendsto γext 𝓕 (𝓝 a0) := by
    exact hγext_cont.tendsto.mono_left nhdsWithin_le_nhds
  -- a0 lies in the closed ball of radius s (limit of points at distances < s)
  have ha0ball : a0 ∈ closedBall p (ENNReal.ofReal s) := by
    have hmem : {x : ℝ | γext x ∈ closedBall p (ENNReal.ofReal s)} ∈ 𝓕 := by
      refine mem_of_superset self_mem_nhdsWithin ?_
      intro x hx
      -- hx : x ∈ Ioo 0 s
      have hx0 : 0 < x := hx.1
      have hxs : x < s := hx.2
      have hγ : γext x = γ ⟨x, ⟨hx0, hxs⟩⟩ := by
        rw [hγextagr x hx]
        exact hgammaHat_agr x hx0 hxs
      have hd : edist p (γext x) = ENNReal.ofReal x := by
        rw [hγ]
        exact hγdist ⟨x, ⟨hx0, hxs⟩⟩
      exact EMetric.mem_closedBall.mpr (by
        have hle : ENNReal.ofReal x ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal (le_of_lt hxs)
        simpa [edist_comm] using (le_trans (le_of_eq hd) hle))
    exact EMetric.isClosed_closedBall.mem_of_tendsto hγext_in_tendsto hmem
  -- 6. the original sequence converges to a0
  have hv_tendsto : Tendsto (v ∘ φ) atTop (𝓝 a0) := by
    rw [EMetric.tendsto_nhds]
    intro ε hε
    by_cases hεtop : ε = ⊤
    · -- all relevant distances finite: from the explicit bounds below with ε := 1: handled by the finite case: pick any
      have hε1 : 0 < (1 : ℝ) := by norm_num
      -- reuse finite-case argument with ε' := 1 as NNReal-ish? easier: trivial since all values finite:
      rw [hεtop]
      refine eventually_atTop.mpr ⟨0, fun m hm => ?_⟩
      have hfin1 : edist (v (φ m)) p < ⊤ := by simpa [edist_comm] using hfin (φ m)
      have hfin2 : edist p a0 < ⊤ := by
        -- a0 ∈ closed ball of radius s gives ≤ ofReal s < ⊤: from ha0ball:
        exact lt_of_le_of_lt (by simpa [edist_comm] using (EMetric.mem_closedBall.mp ha0ball)) ENNReal.ofReal_lt_top
      exact lt_of_le_of_lt (edist_triangle (v (φ m)) p a0) (ENNReal.add_lt_top.mpr ⟨hfin1, hfin2⟩)
    · have hε0 : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) hεtop
      have hεeq : ENNReal.ofReal ε.toReal = ε := ENNReal.ofReal_toReal hεtop
      -- pick a control time t0 close below s (still positive)
      let t0 : β := ⟨s - min (ε.toReal / 32) (s / 2), by
        have hmin : 0 < min (ε.toReal / 32) (s / 2) := lt_min (by linarith) (by linarith)
        have hmins : min (ε.toReal / 32) (s / 2) < s := lt_of_le_of_lt (min_le_right _ _) (by linarith)
        exact ⟨by linarith [hmin, hmins], by linarith [hmin]⟩⟩
      have hdist_t0 : s - t0.1 ≤ ε.toReal / 32 := by
        dsimp [t0]
        have hle : min (ε.toReal / 32) (s / 2) ≤ ε.toReal / 32 := min_le_left _ _
        linarith
      have hdist_t0' : s - t0.1 < ε.toReal / 16 := by linarith
      -- third term: edist (γ t0) a0 bounded by ε/4 via a point x ∈ (t0, s) with γext x close to a0
      have hthird : edist (γ t0) a0 ≤ ENNReal.ofReal (ε.toReal / 4) := by
        have hsmall : ∀ᶠ x : ℝ in 𝓕, edist (γext x) a0 < ENNReal.ofReal (ε.toReal / 8) := by
          exact EMetric.tendsto_nhds.mp hγext_in_tendsto (ENNReal.ofReal (ε.toReal / 8)) (by positivity)
        have hset2 : {x : ℝ | t0.1 < x} ∈ 𝓕 := by
          apply mem_nhdsWithin_of_mem_nhds
          exact isOpen_Ioi.mem_nhds t0.2.2
        have hboth : ∀ᶠ x : ℝ in 𝓕,
            x ∈ Ioo (0 : ℝ) s ∧ edist (γext x) a0 < ENNReal.ofReal (ε.toReal / 8) ∧ t0.1 < x := by
          filter_upwards [self_mem_nhdsWithin, hsmall, hset2] with x hxmem hxsm hxt
          exact ⟨hxmem, hxsm, hxt⟩
        rcases hboth.exists with ⟨x, hx⟩
        have hx0 : 0 < x := hx.1.1
        have hxs : x < s := hx.1.2
        have hγx : γext x = γ ⟨x, ⟨hx0, hxs⟩⟩ := by
          rw [hγextagr x ⟨hx0, hxs⟩]
          exact hgammaHat_agr x hx0 hxs
        have hdist_γx : edist (γ t0) (γext x) ≤ ENNReal.ofReal (x - t0.1) := by
          have hE := hγrealizes t0 ⟨x, ⟨hx0, hxs⟩⟩ (le_of_lt hx.2.2)
          rw [hγx]
          simpa using (le_of_eq hE)
        have hle_x : x - t0.1 ≤ ε.toReal / 8 := by
          have h1 : x - t0.1 < s - t0.1 := by linarith
          have h2 : s - t0.1 ≤ ε.toReal / 32 := hdist_t0
          linarith
        calc
          edist (γ t0) a0 ≤ edist (γ t0) (γext x) + edist (γext x) a0 :=
            edist_triangle (γ t0) (γext x) a0
          _ ≤ ENNReal.ofReal (x - t0.1) + edist (γext x) a0 := by
            exact add_le_add_left hdist_γx (edist (γext x) a0)
          _ ≤ ENNReal.ofReal (x - t0.1) + ENNReal.ofReal (ε.toReal / 8) := by
            exact add_le_add_right (le_of_lt hx.2.1) (ENNReal.ofReal (x - t0.1))
          _ ≤ ENNReal.ofReal (ε.toReal / 8) + ENNReal.ofReal (ε.toReal / 8) := by
            exact add_le_add_left (ENNReal.ofReal_le_ofReal hle_x) (ENNReal.ofReal (ε.toReal / 8))
          _ = ENNReal.ofReal (ε.toReal / 4) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
      -- first term (1-Lipschitz in time) and middle term (convergence at t0) are eventually small
      have hmiddle : ∀ᶠ m : ℕ in atTop,
          edist (g (φ m) (t0.1 : ℝ)) (γ t0) < ENNReal.ofReal (ε.toReal / 8) := by
        exact EMetric.tendsto_nhds.mp (hγlim t0) (ENNReal.ofReal (ε.toReal / 8)) (by positivity)
      have hfirst : ∀ᶠ m : ℕ in atTop,
          edist (v (φ m)) (g (φ m) (t0.1 : ℝ)) < ENNReal.ofReal (ε.toReal / 8) := by
        have hconvτ : Tendsto (fun m : ℕ => τv (φ m)) atTop (𝓝 s) := hτ.comp hφmono.tendsto_atTop
        have hEvT : ∀ᶠ m : ℕ in atTop, τv (φ m) < s + ε.toReal / 16 := by
          exact (tendsto_order.mp hconvτ).2 (s + ε.toReal / 16) (by linarith)
        have hEvT0 : ∀ᶠ m : ℕ in atTop, t0.1 ≤ τv (φ m) := by
          have h := (tendsto_order.mp hconvτ).1 t0.1 t0.2.2
          filter_upwards [h] with m hm
          exact le_of_lt hm
        filter_upwards [hEvT, hEvT0] with m hmT hmT0
        have hgend' : v (φ m) = g (φ m) (τv (φ m)) := by
          dsimp [τv]
          exact (hgend (φ m)).symm
        rw [hgend', edist_comm]
        have hlip : edist (g (φ m) (t0.1 : ℝ)) (g (φ m) (τv (φ m))) ≤
            ENNReal.ofReal (τv (φ m) - t0.1) := (hg_unit (φ m)).lipschitz_le hmT0
        have hlt : τv (φ m) - t0.1 < ε.toReal / 8 := by
          have h1 : τv (φ m) - t0.1 < (s + ε.toReal / 16) - t0.1 := by linarith
          have h2 : (s + ε.toReal / 16) - t0.1 < ε.toReal / 8 := by
            have hd : s - t0.1 ≤ ε.toReal / 32 := hdist_t0
            linarith
          exact lt_trans h1 h2
        exact lt_of_le_of_lt hlip ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt)
      filter_upwards [hmiddle, hfirst] with m hm hf
      have htri := edist_triangle (v (φ m)) (g (φ m) (t0.1 : ℝ)) (γ t0)
      have htri2 := edist_triangle (v (φ m)) (γ t0) a0
      have hb : edist (v (φ m)) a0 < ENNReal.ofReal (ε.toReal / 2) := by
        have h1 : edist (v (φ m)) (γ t0) < ENNReal.ofReal (ε.toReal / 4) := by
          have hA : ENNReal.ofReal (ε.toReal / 8) + ENNReal.ofReal (ε.toReal / 8) =
              ENNReal.ofReal (ε.toReal / 4) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
          have hsum : edist (v (φ m)) (g (φ m) (t0.1 : ℝ)) + edist (g (φ m) (t0.1 : ℝ)) (γ t0) <
              ENNReal.ofReal (ε.toReal / 4) := by
            rw [← hA]
            exact ENNReal.add_lt_add hf hm
          exact lt_of_le_of_lt (edist_triangle (v (φ m)) (g (φ m) (t0.1 : ℝ)) (γ t0)) hsum
        have h2 : edist (v (φ m)) (γ t0) + edist (γ t0) a0 < ENNReal.ofReal (ε.toReal / 2) := by
          have hB : ENNReal.ofReal (ε.toReal / 4) + ENNReal.ofReal (ε.toReal / 4) =
              ENNReal.ofReal (ε.toReal / 2) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
          rw [add_comm (edist (v (φ m)) (γ t0)) (edist (γ t0) a0)]
          rw [← hB]
          have hne : edist (γ t0) a0 ≠ ⊤ :=
            ne_of_lt (lt_of_le_of_lt hthird ENNReal.ofReal_lt_top)
          exact ENNReal.add_lt_add_of_le_of_lt hne hthird h1
        exact lt_of_le_of_lt (edist_triangle (v (φ m)) (γ t0) a0) h2
      have hfinal : ENNReal.ofReal (ε.toReal / 2) < ε := by
        have h' : ENNReal.ofReal (ε.toReal / 2) < ENNReal.ofReal ε.toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hε0).mpr (half_lt_self hε0)
        simpa [hεeq] using h'
      exact lt_trans hb hfinal
  exact ⟨a0, ha0ball, φ, hφmono, hv_tendsto⟩






/-- Sup-closure: if every closed ball of radius < s around p is compact then so is the ball
of radius s. (sequential compactness: split into the "radii bounded away from s" case and
the boundary case). -/
lemma isCompact_closedBall_sup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (hgc : IsGeodesicallyComplete M) (hnon : ∃ v : E, v ≠ 0) (p : M)
    {s : ℝ} (hs0 : 0 ≤ s)
    (hball : ∀ t : ℝ, 0 ≤ t → t < s → IsCompact (closedBall p (ENNReal.ofReal t))) :
    IsCompact (closedBall p (ENNReal.ofReal s)) := by
  classical
  by_cases hsz : s = 0
  · subst s
    rw [isCompact_iff_isSeqCompact]
    intro u hu
    have hu0 : ∀ n : ℕ, u n = p := by
      intro n
      have hm : u n ∈ closedBall p (0 : ℝ≥0∞) := by simpa using hu n
      have hd : edist (u n) p ≤ (0 : ℝ≥0∞) := EMetric.mem_closedBall.mp hm
      have hd0 : edist p (u n) = 0 := by
        have hle : edist p (u n) ≤ (0 : ℝ≥0∞) := by simpa [edist_comm] using hd
        exact le_antisymm hle zero_le
      exact (EMetricSpace.eq_of_edist_eq_zero hd0).symm
    refine ⟨p, ?_, id, strictMono_id, ?_⟩
    · exact EMetric.mem_closedBall.mpr (by simp)
    · have hc : Tendsto (fun _ : ℕ => p) atTop (𝓝 p) := tendsto_const_nhds
      exact Tendsto.congr' (Eventually.of_forall (fun n => (hu0 n).symm)) hc
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsz)
    rw [isCompact_iff_isSeqCompact]
    intro u hu
    let τ : ℕ → ℝ := fun n => (edist p (u n)).toReal
    have hτIcc : ∀ n : ℕ, τ n ∈ Icc (0 : ℝ) s := by
      intro n
      have hd : edist (u n) p ≤ ENNReal.ofReal s := EMetric.mem_closedBall.mp (hu n)
      have hd' : edist p (u n) ≤ ENNReal.ofReal s := by simpa [edist_comm] using hd
      have hle : (edist p (u n)).toReal ≤ s := by
        have h1 := ENNReal.toReal_mono (ne_of_lt ENNReal.ofReal_lt_top) hd'
        rwa [ENNReal.toReal_ofReal hs0] at h1
      exact ⟨ENNReal.toReal_nonneg, by simpa [τ] using hle⟩
    rcases (isCompact_Icc : IsCompact (Icc (0 : ℝ) s : Set ℝ)).tendsto_subseq (x := τ) hτIcc with
      ⟨tlim, htlim, φ, hφ, hφt⟩
    have htlim0 : 0 ≤ tlim := htlim.1
    have htlims : tlim ≤ s := htlim.2
    by_cases ht_lt : tlim < s
    · let t' : ℝ := (tlim + s) / 2
      have ht'gt : tlim < t' := by dsimp [t']; linarith
      have ht'lt : t' < s := by dsimp [t']; linarith
      have ht'0 : 0 ≤ t' := by dsimp [t']; linarith
      have hconv : Tendsto (fun n : ℕ => τ (φ n)) atTop (𝓝 tlim) := hφt
      have hEv : ∀ᶠ n : ℕ in atTop, u (φ n) ∈ closedBall p (ENNReal.ofReal t') := by
        have hlt' : ∀ᶠ n : ℕ in atTop, τ (φ n) < t' := (tendsto_order.mp hconv).2 t' ht'gt
        filter_upwards [hlt'] with n hn
        have hfin : edist p (u (φ n)) < ⊤ :=
          lt_of_le_of_lt (by simpa [edist_comm] using (EMetric.mem_closedBall.mp (hu (φ n)))) ENNReal.ofReal_lt_top
        have hd : edist p (u (φ n)) = ENNReal.ofReal (τ (φ n)) := by
          dsimp [τ]
          exact (ENNReal.ofReal_toReal (ne_of_lt hfin)).symm
        have hmem : u (φ n) ∈ closedBall p (ENNReal.ofReal (τ (φ n))) :=
          EMetric.mem_closedBall.mpr (by simpa [edist_comm] using (le_of_eq hd))
        exact EMetric.closedBall_subset_closedBall (ENNReal.ofReal_le_ofReal (le_of_lt hn)) hmem
      rcases eventually_atTop.1 hEv with ⟨N, hN⟩
      have hw : ∀ m : ℕ, u (φ (m + N)) ∈ closedBall p (ENNReal.ofReal t') := by
        intro m
        exact hN (m + N) (by omega)
      have hseq : IsSeqCompact (closedBall p (ENNReal.ofReal t')) :=
        (isCompact_iff_isSeqCompact).mp (hball t' ht'0 ht'lt)
      rcases hseq (x := fun m : ℕ => u (φ (m + N))) hw with ⟨a, haball, ψ, hψ, hψt⟩
      have haS : a ∈ closedBall p (ENNReal.ofReal s) := by
        have hle : ENNReal.ofReal t' ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal (le_of_lt ht'lt)
        exact EMetric.mem_closedBall.mpr (le_trans (EMetric.mem_closedBall.mp haball) hle)
      have hψN : StrictMono (fun m : ℕ => ψ m + N) := by
        intro a b hab
        exact Nat.add_lt_add_right (hψ hab) N
      refine ⟨a, haS, φ ∘ (fun m : ℕ => ψ m + N), hφ.comp hψN, ?_⟩
      -- tendsto (u ∘ (φ ∘ ψN)): hψt : Tendsto (fun m => u (φ (m+N)))∘ψ hmm (u∘φ∘(+N))∘ψ = u∘φ∘ψN
      exact hψt
    · have ht_eq : tlim = s := le_antisymm htlims (le_of_not_gt ht_lt)
      have hv : ∀ n : ℕ, (u ∘ φ) n ∈ closedBall p (ENNReal.ofReal s) := fun n => hu (φ n)
      have hτv : Tendsto (fun n : ℕ => (edist p ((u ∘ φ) n)).toReal) atTop (𝓝 s) := by
        have h1 : Tendsto (fun n : ℕ => (edist p ((u ∘ φ) n)).toReal) atTop (𝓝 tlim) := by
          change Tendsto (fun n : ℕ => (edist p (u (φ n))).toReal) atTop (𝓝 tlim)
          exact hφt
        simpa [ht_eq] using h1
      rcases geo_seq_limit_at_boundary I M hgc hnon p hs hball (u ∘ φ) hv hτv with
        ⟨a, haS, ψ, hψ, hψt⟩
      exact ⟨a, haS, φ ∘ ψ, hφ.comp hψ, hψt⟩


/-- No nonzero tangent vector: the model space E is a subsingleton. -/
lemma subsingleton_of_no_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hnot : ¬ ∃ v : E, v ≠ 0) : Subsingleton E := by
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by by_contra ha; exact hnot ⟨a, ha⟩
  have hb : b = 0 := by by_contra hb; exact hnot ⟨b, hb⟩
  rw [ha, hb]

/-- A manifold modelled on a subsingleton model space has subsingleton model space `H`. -/
lemma subsingleton_model_of_subsingleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (hE : Subsingleton E) : Subsingleton H := by
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ I.source := by rw [I.source_eq]; trivial
  have hy : y ∈ I.source := by rw [I.source_eq]; trivial
  have hxy : I.toPartialEquiv x = I.toPartialEquiv y := Subsingleton.elim _ _
  have h1 : I.invFun (I.toPartialEquiv x) = x := I.left_inv' hx
  have h2 : I.invFun (I.toPartialEquiv y) = y := I.left_inv' hy
  calc
    x = I.invFun (I.toPartialEquiv x) := h1.symm
    _ = I.invFun (I.toPartialEquiv y) := congrArg I.invFun hxy
    _ = y := h2

/-- A connected manifold modelled on a subsingleton model space is a subsingleton. -/
lemma subsingleton_manifold_of_model {H : Type*} [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [ConnectedSpace M] (hH : Subsingleton H) : Subsingleton M := by
  haveI : Subsingleton H := hH
  have hsing_open : ∀ x : M, IsOpen ({x} : Set M) := by
    intro x
    let c : OpenPartialHomeomorph M H := chartAt H x
    have hxsrc : x ∈ c.source := mem_chart_source H x
    have hsrc_single : c.source = {x} := by
      apply Subset.antisymm
      · intro y hy
        have hycx : (c : M → H) y = (c : M → H) x := Subsingleton.elim _ _
        have hyx : y = x := c.injOn hy hxsrc hycx
        exact mem_singleton_iff.mpr hyx
      · intro y hy
        have hyx : y = x := mem_singleton_iff.mp hy
        rwa [hyx]
    rw [← hsrc_single]
    exact c.open_source
  refine ⟨fun a b => ?_⟩
  by_contra hab
  -- {a} is clopen, nonempty, proper: contradict PreconnectedSpace
  haveI : PreconnectedSpace M := by infer_instance
  have hcl_a : IsClosed ({a} : Set M) := by
    -- complement is the union of singletons of points ≠ a
    have hcomp : ({a} : Set M)ᶜ = ⋃ x : {x : M // x ≠ a}, ({x.1} : Set M) := by
      ext y
      simp
    have hopen_comp : IsOpen (({a} : Set M)ᶜ) := by
      rw [hcomp]
      exact isOpen_iUnion (fun x : {x : M // x ≠ a} => hsing_open x.1)
    exact (isOpen_compl_iff).mp hopen_comp
  have hclop_a : IsClopen ({a} : Set M) := ⟨hcl_a, hsing_open a⟩
  have huniv : ({a} : Set M) = univ := IsClopen.eq_univ hclop_a ⟨a, rfl⟩
  have hb' : b ∈ ({a} : Set M) := by
    rw [huniv]
    trivial
  exact hab (mem_singleton_iff.mp hb').symm

/-- Compactness of any closed ball in a subsingleton e-metric space. -/
lemma compact_closedBall_subsingleton {M : Type*} [EMetricSpace M] [Subsingleton M]
    (p : M) (R : ℝ≥0∞) : IsCompact (closedBall p R) := by
  haveI : Nonempty M := ⟨p⟩
  -- univ = {p}: compact
  have hsing : (univ : Set M) = {p} := by
    ext x
    simp
    exact Subsingleton.elim x p
  have hcpt : IsCompact (univ : Set M) := by
    rw [hsing]
    exact isCompact_singleton
  exact IsCompact.of_isClosed_subset hcpt EMetric.isClosed_closedBall (subset_univ _)


/-- Under geodesic completeness (and a nonzero tangent vector) every closed finite ball is
compact.  The interval of "good radii" is: nonempty at small radii (local normal-ball
compactness), closed under upward extension (local compactness + reachability), and closed
under suprema (sup-closure); hence it contains every finite radius. -/
theorem geoBallsCompact_hnon {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M]
    (hgc : IsGeodesicallyComplete M) (hnon : ∃ v : E, v ≠ 0) (p : M)
    (R : ℝ≥0∞) (hR : R < ⊤) : IsCompact (closedBall p R) := by
  classical
  let r : ℝ := R.toReal
  have hRto : R = ENNReal.ofReal r := (ENNReal.ofReal_toReal (ne_of_lt hR)).symm
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  rw [hRto]
  -- per-point local normal-ball compactness gives compactness up to a small radius ρ0
  let pk : PkgAt E M p := Classical.choice (pkg_at I M p)
  let ρ0 : ℝ := pk.ρ0 / 2
  have hρ0pos : 0 < ρ0 := by dsimp [ρ0]; exact half_pos pk.rho_pos
  have hρ0lt : ρ0 < pk.ρ0 := by dsimp [ρ0]; linarith [pk.rho_pos]
  have hsmall : ∀ t : ℝ, 0 ≤ t → t ≤ ρ0 → IsCompact (closedBall p (ENNReal.ofReal t)) := by
    intro t ht0 htl
    by_cases htz : t = 0
    · -- radius 0 ball = {p}
      subst t
      rw [isCompact_iff_isSeqCompact]
      intro u hu
      have hu0 : ∀ n : ℕ, u n = p := by
        intro n
        have hm : u n ∈ closedBall p (0 : ℝ≥0∞) := by simpa using hu n
        have hd : edist (u n) p ≤ (0 : ℝ≥0∞) := EMetric.mem_closedBall.mp hm
        have hd0 : edist p (u n) = 0 := by
          have hle : edist p (u n) ≤ (0 : ℝ≥0∞) := by simpa [edist_comm] using hd
          exact le_antisymm hle zero_le
        exact (EMetricSpace.eq_of_edist_eq_zero hd0).symm
      refine ⟨p, ?_, id, strictMono_id, ?_⟩
      · exact EMetric.mem_closedBall.mpr (by simp)
      · exact Tendsto.congr' (Eventually.of_forall (fun n => (hu0 n).symm)) tendsto_const_nhds
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htz)
      have htlt : t < pk.ρ0 := lt_of_le_of_lt htl hρ0lt
      exact pk.ball_comp t htpos htlt
  by_cases hr_le : r ≤ ρ0
  · exact hsmall r hr0 hr_le
  · have hρ0r : ρ0 ≤ r := le_of_not_ge hr_le
    let A : Set ℝ := {t : ℝ | 0 ≤ t ∧ t ≤ r ∧ IsCompact (closedBall p (ENNReal.ofReal t))}
    have hρ0inA : ρ0 ∈ A := ⟨hρ0pos.le, hρ0r, hsmall ρ0 hρ0pos.le le_rfl⟩
    have hAnon : A.Nonempty := ⟨ρ0, hρ0inA⟩
    have hAbdd : BddAbove A := ⟨r, fun t ht => ht.2.1⟩
    let T : ℝ := sSup A
    have hTle : T ≤ r := csSup_le hAnon (fun t ht => ht.2.1)
    have hT0 : 0 ≤ T := le_trans hρ0pos.le (le_csSup hAbdd hρ0inA)
    have hsupClosed : ∀ t : ℝ, 0 ≤ t → t < T → IsCompact (closedBall p (ENNReal.ofReal t)) := by
      intro t ht0 htl
      have hnot : ¬ ∀ a : ℝ, a ∈ A → a ≤ t := by
        intro hall
        have hsup_le : sSup A ≤ t := csSup_le hAnon (fun a ha => hall a ha)
        have htl' : t < sSup A := by
          change t < sSup A
          simpa [T] using htl
        linarith
      push_neg at hnot
      rcases hnot with ⟨a, haA, hat⟩
      have hta : ENNReal.ofReal t ≤ ENNReal.ofReal a := ENNReal.ofReal_le_ofReal (le_of_lt hat)
      exact IsCompact.of_isClosed_subset haA.2.2 EMetric.isClosed_closedBall
        (EMetric.closedBall_subset_closedBall hta)
    have hTgood : IsCompact (closedBall p (ENNReal.ofReal T)) :=
      isCompact_closedBall_sup I M hgc hnon p hT0 hsupClosed
    by_cases hTlt : T < r
    · rcases ball_compact_expand I M hgc hnon p hT0 hTgood with ⟨ε, hε0, hεc⟩
      have hε0' : 0 ≤ ε := le_of_lt hε0
      by_cases hεle : T + ε ≤ r
      · have hTεA : T + ε ∈ A := ⟨by linarith, hεle, hεc⟩
        have hleT : T + ε ≤ T := le_csSup hAbdd hTεA
        linarith
      · have hrlt : r < T + ε := lt_of_not_ge hεle
        have hsub : ENNReal.ofReal r ≤ ENNReal.ofReal (T + ε) := ENNReal.ofReal_le_ofReal (le_of_lt hrlt)
        have hc : IsCompact (closedBall p (ENNReal.ofReal r)) :=
          IsCompact.of_isClosed_subset hεc EMetric.isClosed_closedBall
            (EMetric.closedBall_subset_closedBall hsub)
        simpa [← hRto] using hc
    · have hrT : r = T := le_antisymm (le_of_not_gt hTlt) hTle
      simpa [← hRto, hrT] using hTgood


/-- Direction B conclusion: geodesic completeness implies compactness of all closed
finite-radius balls (split into the nonzero-tangent case handled by the engine and the
zero-dimensional case where the connected manifold is a point). -/
theorem geoBallsCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M]
    (hgc : IsGeodesicallyComplete M) (p : M) (R : ℝ≥0∞) (hR : R < ⊤) :
    IsCompact (closedBall p R) := by
  by_cases hnon : ∃ v : E, v ≠ 0
  · exact geoBallsCompact_hnon I M hgc hnon p R hR
  · haveI hsubE : Subsingleton E := subsingleton_of_no_tangent hnon
    haveI hsubH : Subsingleton H := subsingleton_model_of_subsingleton I hsubE
    haveI hsubM : Subsingleton M := subsingleton_manifold_of_model M hsubH
    exact compact_closedBall_subsingleton p R

end DirectionB
end Submission
