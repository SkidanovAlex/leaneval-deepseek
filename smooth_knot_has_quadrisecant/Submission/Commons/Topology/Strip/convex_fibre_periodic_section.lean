import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace Commons.Topology.Strip

open Set Metric

/-! ## Auxiliary material: the circle distance on `ℝ`

For a period `p`, `circleDist p t` is the distance from `t` to the lattice `pℤ ≤ ℝ`.  It is a
continuous `p`-periodic function, and `circleDist p t < r` means that some translate of `t` by a
multiple of `p` lies within `r` of `0`. -/

/-- Translation on `ℝ` is an isometry. -/
private lemma isometry_add_right_real (c : ℝ) : Isometry fun y : ℝ => y + c := by
  refine Isometry.of_dist_eq fun a b => ?_
  rw [Real.dist_eq, Real.dist_eq, add_sub_add_right_eq_sub]

/-- Distance of a real number to the lattice `pℤ`. -/
private noncomputable def circleDist (p t : ℝ) : ℝ :=
  Metric.infDist t (AddSubgroup.zmultiples p : Set ℝ)

private lemma mem_zmultiples_self (p : ℝ) :
    p ∈ (AddSubgroup.zmultiples p : Set ℝ) := by
  show p ∈ AddSubgroup.zmultiples p
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩

private lemma neg_mem_zmultiples_self (p : ℝ) :
    -p ∈ (AddSubgroup.zmultiples p : Set ℝ) := by
  show -p ∈ AddSubgroup.zmultiples p
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨-1, by simp⟩

private lemma zero_mem_zmultiples (p : ℝ) :
    (0 : ℝ) ∈ (AddSubgroup.zmultiples p : Set ℝ) := by
  show 0 ∈ AddSubgroup.zmultiples p
  exact AddSubgroup.zero_mem _

private lemma circleDist_periodic (p : ℝ) : Function.Periodic (circleDist p) p := by
  intro t
  have hZ : (fun y : ℝ => y + p) '' (AddSubgroup.zmultiples p : Set ℝ)
      = (AddSubgroup.zmultiples p : Set ℝ) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact AddSubgroup.add_mem _ hy (mem_zmultiples_self p)
    · intro hz
      refine ⟨z - p, ?_, by ring⟩
      have := AddSubgroup.add_mem _ hz (neg_mem_zmultiples_self p)
      simpa [sub_eq_add_neg] using this
  have h := Metric.infDist_image (Φ := fun y : ℝ => y + p)
    (t := (AddSubgroup.zmultiples p : Set ℝ)) (x := t) (isometry_add_right_real p)
  rw [hZ] at h
  exact h

private lemma continuous_circleDist (p : ℝ) : Continuous (circleDist p) := by
  change Continuous fun x : ℝ => Metric.infDist x (AddSubgroup.zmultiples p : Set ℝ)
  exact Metric.continuous_infDist_pt _

private lemma circleDist_nonneg (p t : ℝ) : 0 ≤ circleDist p t := Metric.infDist_nonneg

private lemma circleDist_le_abs (p t : ℝ) : circleDist p t ≤ |t| := by
  have h := Metric.infDist_le_dist_of_mem (x := t) (zero_mem_zmultiples p)
  simpa [circleDist, Real.dist_eq] using h

private lemma circleDist_lt_iff {p t r : ℝ} :
    circleDist p t < r ↔ ∃ m : ℤ, |t - m • p| < r := by
  rw [circleDist, Metric.infDist_lt_iff ⟨0, zero_mem_zmultiples p⟩]
  constructor
  · rintro ⟨y, hy, hd⟩
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (SetLike.mem_coe.mp hy)
    exact ⟨m, by simpa [Real.dist_eq, ← hm] using hd⟩
  · rintro ⟨m, hm⟩
    refine ⟨m • p, ?_, by simpa [Real.dist_eq] using hm⟩
    show m • p ∈ AddSubgroup.zmultiples p
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨m, rfl⟩

/-! ## Auxiliary material: weights attached to a periodized interval -/

/-- A continuous `p`-periodic weight which is positive exactly on the periodization of the ball
of radius `η i` around `i`. -/
private noncomputable def weight (p : ℝ) (η : ℝ → ℝ) (x i : ℝ) : ℝ :=
  max 0 (η i - circleDist p (x - i))

private lemma weight_nonneg (p : ℝ) (η : ℝ → ℝ) (x i : ℝ) : 0 ≤ weight p η x i :=
  le_max_left _ _

private lemma weight_pos_iff (p : ℝ) (η : ℝ → ℝ) (x i : ℝ) :
    0 < weight p η x i ↔ circleDist p (x - i) < η i := by
  rw [weight, lt_max_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (lt_irrefl 0)
    · linarith
  · intro h
    exact Or.inr (by linarith)

private lemma continuous_weight (p : ℝ) (η : ℝ → ℝ) (i : ℝ) :
    Continuous fun x : ℝ => weight p η x i := by
  have h1 : Continuous fun x : ℝ => η i - circleDist p (x - i) :=
    continuous_const.sub ((continuous_circleDist p).comp (continuous_id.sub continuous_const))
  simpa [weight] using continuous_const.max h1

private lemma weight_add_period (p : ℝ) (η : ℝ → ℝ) (x i : ℝ) :
    weight p η (x + p) i = weight p η x i := by
  have h : circleDist p ((x + p) - i) = circleDist p (x - i) := by
    rw [show (x + p) - i = (x - i) + p by ring]
    exact circleDist_periodic p (x - i)
  simp only [weight, h]

private lemma weight_sub_zsmul (p : ℝ) (η : ℝ → ℝ) (x i : ℝ) (m : ℤ) :
    weight p η (x - m • p) i = weight p η x i := by
  have h : circleDist p ((x - m • p) - i) = circleDist p (x - i) := by
    rw [show (x - m • p) - i = (x - i) - m • p by ring]
    exact (circleDist_periodic p).sub_zsmul_eq m
  simp only [weight, h]

/-! ## The main theorem -/

/-- If `G ⊆ ℝ × ℝ` is open, invariant under `T q = (q.1 + p, q.2)` for some `p > 0`, and every
vertical fibre `{y | (x, y) ∈ G}` is a nonempty convex set of reals, then there is a continuous
`p`-periodic `u : ℝ → ℝ` whose graph lies in `G`. -/
theorem convex_fibre_periodic_section {p : ℝ} (hp : 0 < p) {G : Set (ℝ × ℝ)} (hG : IsOpen G)
    (hper : ∀ q : ℝ × ℝ, q ∈ G ↔ (q.1 + p, q.2) ∈ G)
    (hconv : ∀ x : ℝ, Convex ℝ {y : ℝ | (x, y) ∈ G})
    (hne : ∀ x : ℝ, ∃ y : ℝ, (x, y) ∈ G) :
    ∃ u : ℝ → ℝ, Continuous u ∧ (∀ x : ℝ, u (x + p) = u x) ∧
      ∀ x : ℝ, (x, u x) ∈ G := by
  classical
  -- Step 1: locally constant sections.
  have hlocal : ∀ x : ℝ, ∃ y : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, |t - x| < η → (t, y) ∈ G := by
    intro x
    obtain ⟨y, hy⟩ := hne x
    obtain ⟨U, V, hUo, hVo, hxU, hyV, hUV⟩ := isOpen_prod_iff.mp hG x y hy
    obtain ⟨η, hη, hηsub⟩ := Metric.isOpen_iff.mp hUo x hxU
    exact ⟨y, η, hη, fun t ht =>
      hUV ⟨hηsub (Metric.mem_ball.mpr (by rwa [Real.dist_eq])), hyV⟩⟩
  choose yy rest using hlocal
  choose η hηpos hmem using rest
  -- Step 2: a finite subcover of `[0, p]`.
  obtain ⟨t, ht⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := p)).elim_finite_subcover
    (fun x : ℝ => ball x (η x)) (fun x => isOpen_ball)
    (fun z _ => mem_iUnion.mpr ⟨z, mem_ball_self (hηpos z)⟩)
  -- Step 3: invariance of `G` under translation by integer multiples of `p`.
  have hGper : Function.Periodic (fun x : ℝ => {y : ℝ | (x, y) ∈ G}) p := by
    intro x
    ext y
    exact (hper (x, y)).symm
  have hGmove : ∀ (m : ℤ) (a b : ℝ), (a + m • p, b) ∈ G ↔ (a, b) ∈ G := by
    intro m a b
    have h := (hGper.zsmul m) a
    have h2 := congrArg (fun s : Set ℝ => b ∈ s) h
    simpa using h2
  -- Step 4: the denominator is strictly positive.
  have hbox_pos : ∀ z ∈ Icc (0 : ℝ) p, 0 < ∑ i ∈ t, weight p η z i := by
    intro z hz
    obtain ⟨i, hit, hzi⟩ := mem_iUnion₂.mp (ht hz)
    have hlt : |z - i| < η i := by
      have := Metric.mem_ball.mp hzi
      rwa [Real.dist_eq] at this
    refine Finset.sum_pos' (fun j _ => weight_nonneg p η z j) ⟨i, hit, ?_⟩
    rw [weight_pos_iff]
    exact lt_of_le_of_lt (circleDist_le_abs p (z - i)) hlt
  have hdenom_pos : ∀ x : ℝ, 0 < ∑ i ∈ t, weight p η x i := by
    intro x
    obtain ⟨n, hn⟩ : ∃ n : ℤ, x - n • p ∈ Ico (0 : ℝ) p :=
      ⟨toIcoDiv hp 0 x, by simpa using sub_toIcoDiv_zsmul_mem_Ico hp (0 : ℝ) x⟩
    have hpos := hbox_pos (x - n • p) ⟨hn.1, le_of_lt hn.2⟩
    have hsum : (∑ i ∈ t, weight p η (x - n • p) i) = ∑ i ∈ t, weight p η x i :=
      Finset.sum_congr rfl fun i _ => weight_sub_zsmul p η x i n
    rwa [hsum] at hpos
  -- Step 5: assemble.
  refine ⟨fun x => (∑ i ∈ t, weight p η x i * yy i) / (∑ i ∈ t, weight p η x i),
    ?_, ?_, ?_⟩
  · refine Continuous.div ?_ ?_ fun x => ne_of_gt (hdenom_pos x)
    · exact continuous_finsetSum t fun i _ =>
        (continuous_weight p η i).mul continuous_const
    · exact continuous_finsetSum t fun i _ => continuous_weight p η i
  · intro x
    show (∑ i ∈ t, weight p η (x + p) i * yy i) / (∑ i ∈ t, weight p η (x + p) i)
        = (∑ i ∈ t, weight p η x i * yy i) / (∑ i ∈ t, weight p η x i)
    have h1 : (∑ i ∈ t, weight p η (x + p) i * yy i) = ∑ i ∈ t, weight p η x i * yy i :=
      Finset.sum_congr rfl fun i _ => by rw [weight_add_period p η x i]
    have h2 : (∑ i ∈ t, weight p η (x + p) i) = ∑ i ∈ t, weight p η x i :=
      Finset.sum_congr rfl fun i _ => weight_add_period p η x i
    rw [h1, h2]
  · intro x
    show (x, (∑ i ∈ t, weight p η x i * yy i) / (∑ i ∈ t, weight p η x i)) ∈ G
    set t' := t.filter (fun i => weight p η x i ≠ 0) with ht'
    have hvanish : ∀ i ∈ t, i ∉ t' → weight p η x i * yy i = 0 := by
      intro i hit hit'
      have hw : weight p η x i = 0 := by
        by_contra hne0
        exact hit' (Finset.mem_filter.mpr ⟨hit, hne0⟩)
      rw [hw, zero_mul]
    have hNab : (∑ i ∈ t, weight p η x i * yy i) = ∑ i ∈ t', weight p η x i * yy i := by
      rw [ht']
      exact (Finset.sum_subset (Finset.filter_subset _ _) hvanish).symm
    have hSab : (∑ i ∈ t, weight p η x i) = ∑ i ∈ t', weight p η x i := by
      rw [ht']
      exact (Finset.sum_subset (Finset.filter_subset _ _) (fun i hit hit' => by
        by_contra hne0
        exact hit' (Finset.mem_filter.mpr ⟨hit, hne0⟩))).symm
    have hS'pos : 0 < ∑ i ∈ t', weight p η x i := by
      rw [← hSab]
      exact hdenom_pos x
    have hmain : (∑ i ∈ t', (weight p η x i / (∑ j ∈ t', weight p η x j)) • yy i)
        ∈ {y : ℝ | (x, y) ∈ G} := by
      refine (hconv x).sum_mem ?_ ?_ ?_
      · intro i _
        exact div_nonneg (weight_nonneg p η x i) (le_of_lt hS'pos)
      · rw [← Finset.sum_div]
        exact div_self (ne_of_gt hS'pos)
      · intro i hi
        have hwne : weight p η x i ≠ 0 := (Finset.mem_filter.mp hi).2
        have hwpos : 0 < weight p η x i :=
          lt_of_le_of_ne' (weight_nonneg p η x i) hwne
        have hdlt : circleDist p (x - i) < η i := (weight_pos_iff p η x i).mp hwpos
        obtain ⟨m, hm⟩ := circleDist_lt_iff.mp hdlt
        have hmid : (x - m • p, yy i) ∈ G := by
          refine hmem i (x - m • p) ?_
          rwa [show (x - m • p) - i = (x - i) - m • p by ring]
        have htrans := hGmove m (x - m • p) (yy i)
        have hfin : (x - m • p + m • p, yy i) ∈ G := htrans.mpr hmid
        have hxx : x - m • p + m • p = x := sub_add_cancel x (m • p)
        rwa [hxx] at hfin
    have hu_eq : (∑ i ∈ t, weight p η x i * yy i) / (∑ i ∈ t, weight p η x i)
        = ∑ i ∈ t', (weight p η x i / (∑ j ∈ t', weight p η x j)) • yy i := by
      rw [hNab, hSab, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, div_mul_eq_mul_div]
    rw [hu_eq]
    exact hmain

end Commons.Topology.Strip