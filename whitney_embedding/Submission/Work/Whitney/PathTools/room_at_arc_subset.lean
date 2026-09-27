import Mathlib
import Submission.Work.Whitney.PathTools.slices_totallyDisconnected
import Submission.Work.Whitney.PathTools.isPreconnected_sdiff_of_local_room
import Submission.Work.Whitney.PathTools.RemovabilityGeneral
import Submission.Work.Whitney.PathTools.ball_sdiff_isCompact_totallyDisconnected_isPathConnected
import Submission.Work.Whitney.PathTools.sphere_sdiff_isCompact_totallyDisconnected_isPreconnected

/-!
# Room at a point of a one-dimensional compact set

Main lemma: `Work.Whitney.PathTools.room_at_arc_subset`.
-/

open Set Metric Topology Filter
open scoped Topology InnerProductSpace

namespace Work.Whitney.PathTools

variable {n : ℕ}

/-! ## The perpendicular bisector has empty interior -/

lemma inner_diff_eq (u v z : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (u - z) (v - u) - inner ℝ (v - z) (v - u) = -(‖v - u‖ ^ 2) := by
  rw [← inner_sub_left]
  have h4 : (u - z) - (v - z) = u - v := by abel
  rw [h4]
  have h5 : u - v = -(v - u) := by abel
  rw [h5, inner_neg_left, real_inner_self_eq_norm_sq]

lemma norm_key_identity (u v z : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    ‖u - (z + δ • (v - u))‖ ^ 2 - ‖v - (z + δ • (v - u))‖ ^ 2
      = (‖u - z‖ ^ 2 - ‖v - z‖ ^ 2) + 2 * δ * ‖v - u‖ ^ 2 := by
  have h1 : u - (z + δ • (v - u)) = (u - z) - δ • (v - u) := by abel
  have h2 : v - (z + δ • (v - u)) = (v - z) - δ • (v - u) := by abel
  have hu : ‖(u - z) - δ • (v - u)‖ ^ 2
      = ‖u - z‖ ^ 2 - 2 * inner ℝ (u - z) (δ • (v - u)) + ‖δ • (v - u)‖ ^ 2 :=
    norm_sub_sq_real _ _
  have hv : ‖(v - z) - δ • (v - u)‖ ^ 2
      = ‖v - z‖ ^ 2 - 2 * inner ℝ (v - z) (δ • (v - u)) + ‖δ • (v - u)‖ ^ 2 :=
    norm_sub_sq_real _ _
  have h3 : inner ℝ (u - z) (δ • (v - u)) - inner ℝ (v - z) (δ • (v - u))
      = -δ * ‖v - u‖ ^ 2 := by
    rw [real_inner_smul_right, real_inner_smul_right, ← mul_sub, inner_diff_eq]
    ring
  rw [h1, h2, hu, hv]
  linarith [h3]

/-- The set of points equidistant from two distinct points has empty interior. -/
lemma interior_setOf_dist_eq_empty {u v : EuclideanSpace ℝ (Fin n)} (huv : u ≠ v) :
    interior {y : EuclideanSpace ℝ (Fin n) | dist u y = dist v y} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  have hzS : z ∈ {y : EuclideanSpace ℝ (Fin n) | dist u y = dist v y} := interior_subset hz
  simp only [mem_setOf_eq] at hzS
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hz
  obtain ⟨ε, hε, hεsub⟩ := hz
  have hd : ‖u - z‖ ^ 2 - ‖v - z‖ ^ 2 = 0 := by
    rw [← dist_eq_norm, ← dist_eq_norm, hzS]; ring
  have hw : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have hwn : 0 < ‖v - u‖ := norm_pos_iff.mpr hw
  set t : ℝ := ε / (2 * (‖v - u‖ + 1)) with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have htsmall : t * ‖v - u‖ < ε := by
    rw [htdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (‖v - u‖ + 1))]
    nlinarith [hwn]
  set z' : EuclideanSpace ℝ (Fin n) := z + t • (v - u) with hz'def
  have hz'ball : z' ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm, hz'def, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg htpos.le]
    linarith
  have hz'S : dist u z' = dist v z' := hεsub hz'ball
  have hzero : ‖u - z'‖ ^ 2 - ‖v - z'‖ ^ 2 = 0 := by
    rw [← dist_eq_norm, ← dist_eq_norm, hz'S]; ring
  have hkey := norm_key_identity u v z t
  rw [hz'def] at hzero
  rw [hkey, hd, zero_add] at hzero
  have : 0 < 2 * t * ‖v - u‖ ^ 2 := by positivity
  linarith

/-! ## A generic centre for which no arc of `h '' K` lies on a sphere -/

/-- Indexing type of pairs of rationals whose closed interval lies in `K`. -/
def goodPairIdx (K : Set ℝ) : Type := {p : ℚ × ℚ // (p.1 : ℝ) < (p.2 : ℝ) ∧
  Set.Icc (p.1 : ℝ) (p.2 : ℝ) ⊆ K}

instance (K : Set ℝ) : Countable (goodPairIdx K) := by
  unfold goodPairIdx; infer_instance

/-- For each pair, the set of centres from which the two image points are equidistant. -/
def badCenter (K : Set ℝ) (h : ℝ → EuclideanSpace ℝ (Fin n)) (p : goodPairIdx K) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | dist (h (p.1.1 : ℝ)) y = dist (h (p.1.2 : ℝ)) y}

lemma isClosed_badCenter (K : Set ℝ) (h : ℝ → EuclideanSpace ℝ (Fin n))
    (p : goodPairIdx K) : IsClosed (badCenter K h p) :=
  isClosed_eq (continuous_const.dist continuous_id) (continuous_const.dist continuous_id)

lemma isNowhereDense_badCenter {K : Set ℝ} {h : ℝ → EuclideanSpace ℝ (Fin n)}
    (hinj : Set.InjOn h K) (p : goodPairIdx K) :
    IsNowhereDense (badCenter K h p) := by
  rw [IsClosed.isNowhereDense_iff (isClosed_badCenter K h p)]
  apply interior_setOf_dist_eq_empty
  intro hcon
  have hab : (p.1.1 : ℝ) ≠ (p.1.2 : ℝ) := ne_of_lt p.2.1
  have ha : (p.1.1 : ℝ) ∈ K := p.2.2 ⟨le_refl _, le_of_lt p.2.1⟩
  have hb : (p.1.2 : ℝ) ∈ K := p.2.2 ⟨le_of_lt p.2.1, le_refl _⟩
  exact hab (hinj ha hb hcon)

/-- Every ball in `EuclideanSpace ℝ (Fin n)` (`n ≥ 1`) contains a point `y` such that no
nondegenerate interval of `K` is mapped by `h` into a sphere centred at `y`. -/
theorem center_avoiding_spherical_arcs {n : ℕ} (hn : 1 ≤ n)
    {K : Set ℝ} (hK : IsCompact K) {h : ℝ → EuclideanSpace ℝ (Fin n)}
    (hh : ContinuousOn h K) (hinj : Set.InjOn h K)
    (x : EuclideanSpace ℝ (Fin n)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ y : EuclideanSpace ℝ (Fin n), dist y x < ρ ∧
      ∀ (a b : ℚ), (a:ℝ) < b → Set.Icc (a:ℝ) (b:ℝ) ⊆ K →
        ∃ s ∈ Set.Icc (a:ℝ) (b:ℝ), dist (h s) y ≠ dist (h (a:ℝ)) y := by
  have hmeag : IsMeagre (⋃ p : goodPairIdx K, badCenter K h p) :=
    isMeagre_iUnion fun p =>
      (isMeagre_iff_countable_union_isNowhereDense).mpr
        ⟨{badCenter K h p}, by
          rintro t rfl
          exact isNowhereDense_badCenter hinj p,
         Set.countable_singleton _,
         by intro y hy; exact ⟨badCenter K h p, rfl, hy⟩⟩
  have hball : ¬ IsMeagre (Metric.ball x ρ) := by
    apply not_isMeagre_of_isOpen isOpen_ball
    exact ⟨x, mem_ball_self hρ⟩
  by_contra hcon
  push_neg at hcon
  refine hball (IsMeagre.mono (fun y hy => ?_) hmeag)
  have hy' : dist y x < ρ := by rwa [Metric.mem_ball] at hy
  rcases hcon y hy' with ⟨a, b, hab, hsub, hne⟩
  refine mem_iUnion.mpr ⟨⟨(a, b), ⟨hab, hsub⟩⟩, ?_⟩
  simp only [badCenter]
  have hb : (b : ℝ) ∈ Set.Icc (a:ℝ) (b:ℝ) := ⟨le_of_lt hab, le_refl _⟩
  have h := hne (b : ℝ) hb
  exact h.symm
/-!
## The curve meets every sphere centred at a "good" point in a totally disconnected set
-/

/-- **A preconnected piece of the curve lying on a sphere is a single point.**  If `y` is a centre
as produced by `center_avoiding_spherical_arcs` (no nondegenerate sub-arc of `K` is mapped into a
sphere around `y`), then no preconnected subset of `h '' K` with more than one point lies on a
sphere centred at `y`. -/
theorem subsingleton_of_isPreconnected_const_dist {n : ℕ} {K : Set ℝ} (hK : IsCompact K)
    {h : ℝ → EuclideanSpace ℝ (Fin n)} (hh : ContinuousOn h K) (hinj : Set.InjOn h K)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : ∀ (a b : ℚ), (a:ℝ) < b → Set.Icc (a:ℝ) (b:ℝ) ⊆ K →
        ∃ s ∈ Set.Icc (a:ℝ) (b:ℝ), dist (h s) y ≠ dist (h (a:ℝ)) y)
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCA : C ⊆ h '' K) (hCpre : IsPreconnected C)
    {t : ℝ} (ht : ∀ z ∈ C, dist z y = t) : C.Subsingleton := by
  classical
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  -- the map from the parameter set
  have hgcont : Continuous fun s : ↥K => h s := hh.domRestrict
  have hginj : Function.Injective fun s : ↥K => h s :=
    fun a b hab => Subtype.ext (hinj a.2 b.2 hab)
  have hgind : Topology.IsInducing fun s : ↥K => h s :=
    (Continuous.isClosedEmbedding hgcont hginj).toIsEmbedding.toIsInducing
  -- the parameter set of `C`
  set D : Set ↥K := (fun s : ↥K => h s) ⁻¹' C with hDdef
  have hDpre : IsPreconnected D := by
    have h1 : (fun s : ↥K => h s) '' D = C := by
      refine Subset.antisymm ?_ ?_
      · rintro z ⟨s, hs, rfl⟩; exact hs
      · intro z hz
        obtain ⟨s, hsK, hsz⟩ := hCA hz
        exact ⟨⟨s, hsK⟩, by rw [hDdef, Set.mem_preimage, hsz]; exact hz, hsz⟩
    have h2 : IsPreconnected ((fun s : ↥K => h s) '' D) := by rw [h1]; exact hCpre
    exact (Topology.IsInducing.isPreconnected_image (f := fun s : ↥K => h s) (s := D)
      hgind).mp h2
  set Dℝ : Set ℝ := Subtype.val '' D with hDℝdef
  have hDℝpre : IsPreconnected Dℝ := by
    have h2 : IsPreconnected ((Subtype.val : ↥K → ℝ) '' D) :=
      (Topology.IsInducing.isPreconnected_image (f := (Subtype.val : ↥K → ℝ)) (s := D)
        Topology.IsInducing.subtypeVal).mpr hDpre
    rwa [hDℝdef]
  have hDℝK : Dℝ ⊆ K := by
    rintro x ⟨s, -, rfl⟩
    exact s.2
  have hmemDℝ : ∀ s : ↥K, s ∈ D ↔ (s : ℝ) ∈ Dℝ := by
    intro s
    constructor
    · intro hs; exact ⟨s, hs, rfl⟩
    · rintro ⟨t, ht, hts⟩
      have hst : t = s := Subtype.ext hts
      rwa [← hst]
  -- the image on `C`
  have hCt : ∀ s : ↥K, s ∈ D → dist (h (s : ℝ)) y = t := by
    intro s hs
    have h1 : h (s : ℝ) ∈ C := by
      have h2 := hs
      rw [hDdef, Set.mem_preimage] at h2
      simpa using h2
    exact ht _ h1
  intro z₁ hz₁ z₂ hz₂
  by_contra hne
  obtain ⟨s₁, hs₁K, hs₁⟩ := hCA hz₁
  obtain ⟨s₂, hs₂K, hs₂⟩ := hCA hz₂
  have hs₁D : (⟨s₁, hs₁K⟩ : ↥K) ∈ D := by
    rw [hDdef, Set.mem_preimage, hs₁]; exact hz₁
  have hs₂D : (⟨s₂, hs₂K⟩ : ↥K) ∈ D := by
    rw [hDdef, Set.mem_preimage, hs₂]; exact hz₂
  have hs₁ℝ : s₁ ∈ Dℝ := ⟨⟨s₁, hs₁K⟩, hs₁D, rfl⟩
  have hs₂ℝ : s₂ ∈ Dℝ := ⟨⟨s₂, hs₂K⟩, hs₂D, rfl⟩
  have hdiff : s₁ ≠ s₂ := by
    intro hcon
    exact hne (by rw [← hs₁, ← hs₂, hcon])
  -- the interval inside `K` and the contradiction with `hy`
  have key : ∀ u v : ℝ, u < v → u ∈ Dℝ → v ∈ Dℝ → False := by
    intro u v huv huD hvD
    have hint : Set.Icc u v ⊆ Dℝ := hDℝpre.ordConnected.out huD hvD
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn huv
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn ha2
    have hab : (a : ℝ) < (b : ℝ) := hb1
    have hKsub : Set.Icc (a : ℝ) (b : ℝ) ⊆ K := fun x hx =>
      hDℝK (hint ⟨le_trans (le_of_lt ha1) hx.1, le_of_lt (lt_of_le_of_lt hx.2 hb2)⟩)
    obtain ⟨s', hs'mem, hs'ne⟩ := hy a b hab hKsub
    have h1 : dist (h s') y = t := by
      have hmem : s' ∈ Dℝ :=
        hint ⟨le_trans (le_of_lt ha1) hs'mem.1, le_of_lt (lt_of_le_of_lt hs'mem.2 hb2)⟩
      obtain ⟨w, hwD, hws⟩ := hmem
      have h2 : h (w : ℝ) ∈ C := by
        have h3 := hwD
        rw [hDdef, Set.mem_preimage] at h3
        simpa using h3
      rw [← hws]
      exact ht _ h2
    have h2 : dist (h (a : ℝ)) y = t := by
      have hmem : (a : ℝ) ∈ Dℝ :=
        hint ⟨le_of_lt ha1, le_of_lt ha2⟩
      obtain ⟨w, hwD, hws⟩ := hmem
      have h3 : h (w : ℝ) ∈ C := by
        have h4 := hwD
        rw [hDdef, Set.mem_preimage] at h4
        simpa using h4
      rw [← hws]
      exact ht _ h3
    exact hs'ne (by rw [h1, h2])
  rcases lt_or_gt_of_ne hdiff with hlt | hlt
  · exact key s₁ s₂ hlt hs₁ℝ hs₂ℝ
  · exact key s₂ s₁ hlt hs₂ℝ hs₁ℝ
/-- **A cap of a sphere is not totally disconnected.**  Let `z` be a point of the sphere
`Metric.sphere c t` (`t > 0`) and let `t' > 0` be close to `t`.  Then the cap
`Metric.sphere c t' ∩ Metric.ball z ε` contains a point outside every totally disconnected subset of
the sphere `Metric.sphere c t'`: it contains a nondegenerate arc. -/
lemma exists_notMem_sphere_inter_ball {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hrank : 2 ≤ Module.finrank ℝ E)
    {c z : E} {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t') (hz : ‖z - c‖ = t)
    {ε : ℝ} (hε : 0 < ε) (hclose : |t' - t| < ε / 2)
    {T : Set E} (hTs : T ⊆ Metric.sphere c t') (hT : IsTotallyDisconnected T) :
    ∃ w ∈ Metric.sphere c t' ∩ Metric.ball z ε, w ∉ T := by
  classical
  -- a unit vector along `z - c` and a unit vector orthogonal to it
  set v : E := t⁻¹ • (z - c) with hvdef
  have hv : ‖v‖ = 1 := by
    rw [hvdef, norm_smul, Real.norm_of_nonneg (by positivity), hz]
    field_simp
  obtain ⟨u, hu1, hu2⟩ := exists_orthogonal_unit_vector_gen hrank hv
  have hzv : z - c = t • v := by
    rw [hvdef, smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul]
  have hzu : ⟪z - c, u⟫_ℝ = 0 := by
    rw [hzv, real_inner_smul_left, hu2, mul_zero]
  -- the radial point of the sphere `Metric.sphere c t'` on the ray through `z`
  set z' : E := c + (t' / t) • (z - c) with hz'def
  have hz' : ‖z' - c‖ = t' := by
    have h1 : z' - c = (t' / t) • (z - c) := by rw [hz'def]; module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < t' / t), hz,
      div_mul_cancel₀ _ (ne_of_gt ht)]
  have hz'u : ⟪z' - c, u⟫_ℝ = 0 := by
    have h1 : z' - c = (t' / t) • (z - c) := by rw [hz'def]; module
    rw [h1, real_inner_smul_left, hzu, mul_zero]
  have hzz' : ‖z' - z‖ = |t' - t| := by
    have h1 : z' - z = (t' / t - 1) • (z - c) := by rw [hz'def]; module
    rw [h1, norm_smul, Real.norm_eq_abs,
      show t' / t - 1 = (t' - t) / t by field_simp, abs_div, abs_of_pos ht, hz,
      div_mul_cancel₀ _ (ne_of_gt ht)]
  -- the parameter of the arc
  set η : ℝ := min (1 / 2) (ε / 4) with hηdef
  have hηpos : 0 < η := lt_min (by norm_num) (by positivity)
  have hηle : η ≤ ε / 4 := min_le_right _ _
  -- the arc, on the sphere `Metric.sphere c t'`
  set ζ : ℝ → E :=
    fun s => c + (t' / Real.sqrt (t' ^ 2 + s ^ 2)) • ((z' - c) + s • u) with hζdef
  have hζcont : Continuous ζ := by
    rw [hζdef]
    have h1 : Continuous fun s : ℝ => Real.sqrt (t' ^ 2 + s ^ 2) :=
      (continuous_const.add (continuous_id.pow 2)).sqrt
    have h2 : Continuous fun s : ℝ => t' / Real.sqrt (t' ^ 2 + s ^ 2) :=
      continuous_const.div₀ h1 fun s => ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    exact continuous_const.add (h2.smul (continuous_const.add (continuous_id.smul continuous_const)))
  have hζsphere : ∀ s : ℝ, ζ s ∈ Metric.sphere c t' := by
    intro s
    have hTpos : 0 < Real.sqrt (t' ^ 2 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
    rw [Metric.mem_sphere, dist_eq_norm]
    have h1 : ζ s - c = (t' / Real.sqrt (t' ^ 2 + s ^ 2)) • ((z' - c) + s • u) := by
      rw [hζdef]; module
    rw [h1, norm_smul, Real.norm_of_nonneg (by positivity)]
    have h2 : ‖(z' - c) + s • u‖ = Real.sqrt (t' ^ 2 + s ^ 2) := by
      have h3 : ‖(z' - c) + s • u‖ ^ 2 = t' ^ 2 + s ^ 2 := by
        rw [norm_add_sq_real]
        simp only [real_inner_smul_right, hz'u, mul_zero, add_zero, norm_smul, Real.norm_eq_abs,
          hu1, mul_one, sq_abs, hz']
      rw [← h3, Real.sqrt_sq (norm_nonneg _)]
    rw [h2, div_mul_cancel₀ _ (ne_of_gt hTpos)]
  have hζclose : ∀ s ∈ Set.Icc (0:ℝ) η, ‖ζ s - z'‖ ≤ s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hTpos : 0 < Real.sqrt (t' ^ 2 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hTsq : Real.sqrt (t' ^ 2 + s ^ 2) ^ 2 = t' ^ 2 + s ^ 2 := Real.sq_sqrt (by positivity)
    have hTge : t' ≤ Real.sqrt (t' ^ 2 + s ^ 2) := by
      have := hTsq
      nlinarith [this, hTpos, ht', sq_nonneg s]
    have h1 : ζ s - z' = ((t' / Real.sqrt (t' ^ 2 + s ^ 2)) - 1) • (z' - c) +
        ((t' * s) / Real.sqrt (t' ^ 2 + s ^ 2)) • u := by
      have h2 : (t' / Real.sqrt (t' ^ 2 + s ^ 2)) • s • u
          = ((t' * s) / Real.sqrt (t' ^ 2 + s ^ 2)) • u := by
        rw [smul_smul, div_mul_eq_mul_div]
      rw [hζdef]
      simp only [smul_add, h2]
      module
    rw [h1]
    have horth : ⟪((t' / Real.sqrt (t' ^ 2 + s ^ 2)) - 1) • (z' - c),
        ((t' * s) / Real.sqrt (t' ^ 2 + s ^ 2)) • u⟫_ℝ = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right, hz'u, mul_zero, mul_zero]
    have h2 : ‖((t' / Real.sqrt (t' ^ 2 + s ^ 2)) - 1) • (z' - c) +
        ((t' * s) / Real.sqrt (t' ^ 2 + s ^ 2)) • u‖ ^ 2 ≤ s ^ 2 := by
      have hkey : ‖((t' / Real.sqrt (t' ^ 2 + s ^ 2)) - 1) • (z' - c) +
          ((t' * s) / Real.sqrt (t' ^ 2 + s ^ 2)) • u‖ ^ 2
          = 2 * t' ^ 2 * (Real.sqrt (t' ^ 2 + s ^ 2) - t') / Real.sqrt (t' ^ 2 + s ^ 2) := by
        rw [norm_add_sq_real, horth, mul_zero, add_zero, norm_smul, norm_smul, Real.norm_eq_abs,
          Real.norm_eq_abs, hz', hu1, mul_one, mul_pow, sq_abs, sq_abs]
        field_simp
        nlinarith [hTsq]
      rw [hkey, div_le_iff₀ hTpos]
      have hA : 0 ≤ Real.sqrt (t' ^ 2 + s ^ 2) - t' := by linarith
      have hB : 0 ≤ (Real.sqrt (t' ^ 2 + s ^ 2) + t') * Real.sqrt (t' ^ 2 + s ^ 2)
          - 2 * t' ^ 2 := by nlinarith [hTge, hTpos, ht']
      have hprod := mul_nonneg hA hB
      nlinarith [hprod, hTsq, sq_nonneg s]
    nlinarith [h2, norm_nonneg (((t' / Real.sqrt (t' ^ 2 + s ^ 2)) - 1) • (z' - c) +
      ((t' * s) / Real.sqrt (t' ^ 2 + s ^ 2)) • u), hs0]
  -- the arc lies in the cap
  have hmem : ∀ s ∈ Set.Icc (0:ℝ) η, ζ s ∈ Metric.sphere c t' ∩ Metric.ball z ε := by
    intro s hs
    refine ⟨hζsphere s, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖ζ s - z‖ ≤ ‖ζ s - z'‖ + ‖z' - z‖ := by
      have := dist_triangle (ζ s) z' z
      simpa only [dist_eq_norm] using this
    have h2 := hζclose s hs
    rw [hzz'] at h1
    have h3 : s + |t' - t| ≤ η + ε / 2 := by
      have := hs.2
      linarith
    linarith [hηle, hclose]
  -- the arc is nondegenerate
  have hne : ζ η ≠ ζ 0 := by
    intro hcon
    have h1 : ⟪ζ η - c, u⟫_ℝ = t' * η / Real.sqrt (t' ^ 2 + η ^ 2) := by
      have h2 : ζ η - c = (t' / Real.sqrt (t' ^ 2 + η ^ 2)) • ((z' - c) + η • u) := by
        rw [hζdef]; module
      rw [h2, real_inner_smul_left]
      simp only [inner_add_left, hz'u, zero_add, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hu1]
      ring
    have h3 : ⟪ζ 0 - c, u⟫_ℝ = 0 := by
      have h4 : Real.sqrt (t' ^ 2 + (0:ℝ) ^ 2) = t' := by
        rw [show t' ^ 2 + (0:ℝ) ^ 2 = t' ^ 2 by ring, Real.sqrt_sq ht'.le]
      have h5 : ζ 0 = z' := by
        rw [hζdef]
        simp only [h4, div_self (ne_of_gt ht'), one_smul, zero_smul, add_zero]
        abel
      rw [h5, hz'u]
    have h4 : ζ η - c = ζ 0 - c := by rw [hcon]
    rw [h4, h3] at h1
    have h5 : 0 < t' * η / Real.sqrt (t' ^ 2 + η ^ 2) := by positivity
    linarith [h1, h5]
  -- conclude
  by_contra hcon
  push_neg at hcon
  have hsub : ζ '' Set.Icc (0:ℝ) η ⊆ T := by
    rintro w ⟨s, hs, rfl⟩
    exact hcon (ζ s) (hmem s hs)
  have hpre : IsPreconnected (ζ '' Set.Icc (0:ℝ) η) :=
    isPreconnected_Icc.image ζ hζcont.continuousOn
  have hsing : (ζ '' Set.Icc (0:ℝ) η).Subsingleton := hT _ hsub hpre
  exact hne (hsing ⟨η, ⟨hηpos.le, le_refl _⟩, rfl⟩ ⟨0, ⟨le_refl _, hηpos.le⟩, rfl⟩)

/-- The sphere `Metric.sphere c t` (`t > 0`, `n ≥ 1`) has at least two points. -/
lemma not_subsingleton_sphere {n : ℕ} (hn : 1 ≤ n) (c : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : 0 < t) : ¬ (Metric.sphere c t).Subsingleton := by
  intro hsingle
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin n), w ≠ 0 := by
    refine ⟨(WithLp.equiv 2 (Fin n → ℝ)).symm (Pi.single ⟨0, hn⟩ 1), ?_⟩
    intro hc
    have := congrFun (congrArg (WithLp.equiv 2 (Fin n → ℝ)) hc) ⟨0, hn⟩
    simp at this
  set u : EuclideanSpace ℝ (Fin n) := ‖w‖⁻¹ • w with hudef
  have hun : ‖u‖ = 1 := by
    rw [hudef, norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr hw))]
  have h1 : c + t • u ∈ Metric.sphere c t := by
    rw [Metric.mem_sphere, dist_eq_norm]
    have h2 : c + t • u - c = t • u := by abel
    rw [h2, norm_smul, Real.norm_of_nonneg ht.le, hun, mul_one]
  have h2 : c - t • u ∈ Metric.sphere c t := by
    rw [Metric.mem_sphere, dist_eq_norm]
    have h3 : c - t • u - c = -(t • u) := by abel
    rw [h3, norm_neg, norm_smul, Real.norm_of_nonneg ht.le, hun, mul_one]
  have hne : c + t • u ≠ c - t • u := by
    intro hcon
    have h3 : t • u = -(t • u) := by
      have h4 : (c + t • u) - c = (c - t • u) - c := by rw [hcon]
      simpa using h4
    have h5 : t • u + t • u = 0 := eq_neg_iff_add_eq_zero.mp h3
    have h6 : (2 : ℝ) • (t • u) = 0 := by rw [two_smul]; exact h5
    rcases smul_eq_zero.mp h6 with h7 | h7
    · norm_num at h7
    · exact absurd h7 (smul_ne_zero (ne_of_gt ht) (by
        intro h8
        rw [h8, norm_zero] at hun
        norm_num at hun))
  exact hne (hsingle h1 h2)

/-- **A ball minus a set is preconnected, from information about its shells.**  Let `A ⊆ E`, `y₁ ∈ E`
and `R > 0`.  Suppose that
* every sphere `Metric.sphere y₁ t` with `0 < t < R` meets the complement of `A` (`hne`),
* the part of every such sphere outside `A` is preconnected (`hpre`),
* for `z` outside `A` on such a sphere and every `δ > 0` the shells of nearby radii meet the ball
  `Metric.ball z δ` (`hcap`);
then the ball `Metric.ball y₁ R` minus `A` is preconnected. -/
lemma isPreconnected_ball_sdiff_of_shells {E : Type*} [NormedAddCommGroup E]
    {A : Set E} {y₁ : E} {R : ℝ} (hR : 0 < R)
    (hpre : ∀ t ∈ Set.Ioo (0:ℝ) R, IsPreconnected (Metric.sphere y₁ t \ A))
    (hne : ∀ t ∈ Set.Ioo (0:ℝ) R, (Metric.sphere y₁ t \ A).Nonempty)
    (hcap : ∀ t ∈ Set.Ioo (0:ℝ) R, ∀ z ∈ Metric.sphere y₁ t \ A, ∀ δ > 0,
      ∃ ν > 0, ∀ t' ∈ Set.Ioo (0:ℝ) R, |t' - t| < ν →
        ((Metric.sphere y₁ t' \ A) ∩ Metric.ball z δ).Nonempty) :
    IsPreconnected (Metric.ball y₁ R \ A) := by
  classical
  have hball : ∀ t ∈ Set.Ioo (0:ℝ) R,
      Metric.sphere y₁ t \ A ⊆ Metric.ball y₁ R \ A := by
    rintro t ht z hz
    refine ⟨?_, hz.2⟩
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (le_of_eq (Metric.mem_sphere.mp hz.1)) ht.2
  rw [isPreconnected_iff_subset_of_disjoint]
  intro U V hU hV hUV hUVdisj
  -- every shell lies entirely on one side of the separation
  have key : ∀ t ∈ Set.Ioo (0:ℝ) R,
      (Metric.sphere y₁ t \ A ⊆ U) ∨ (Metric.sphere y₁ t \ A ⊆ V) := by
    intro t ht
    have h1 : Metric.sphere y₁ t \ A ⊆ U ∪ V := fun z hz => hUV (hball t ht hz)
    have h2 : (Metric.sphere y₁ t \ A) ∩ (U ∩ V) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hz, hzUV⟩
      exact Set.eq_empty_iff_forall_notMem.mp hUVdisj z ⟨hball t ht hz, hzUV⟩
    exact isPreconnected_iff_subset_of_disjoint.mp (hpre t ht) U V hU hV h1 h2
  -- a shell contained in one side is disjoint from the other one
  have hdisjU : ∀ t ∈ Set.Ioo (0:ℝ) R, Metric.sphere y₁ t \ A ⊆ V →
      Disjoint (Metric.sphere y₁ t \ A) U := by
    intro t ht htV
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hw, hwU⟩
    exact Set.eq_empty_iff_forall_notMem.mp hUVdisj w ⟨hball t ht hw, hwU, htV hw⟩
  have hdisjV : ∀ t ∈ Set.Ioo (0:ℝ) R, Metric.sphere y₁ t \ A ⊆ U →
      Disjoint (Metric.sphere y₁ t \ A) V := by
    intro t ht htU
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hw, hwV⟩
    exact Set.eq_empty_iff_forall_notMem.mp hUVdisj w ⟨hball t ht hw, htU hw, hwV⟩
  -- the set of radii whose shells lie on a given side is open
  have hopen_of : ∀ W : Set E, IsOpen W →
      (∀ t ∈ Set.Ioo (0:ℝ) R,
        Metric.sphere y₁ t \ A ⊆ W ∨ Disjoint (Metric.sphere y₁ t \ A) W) →
      IsOpen {t : ℝ | t ∈ Set.Ioo (0:ℝ) R ∧ Metric.sphere y₁ t \ A ⊆ W} := by
    intro W hW hWor
    rw [Metric.isOpen_iff]
    rintro t ⟨ht, htW⟩
    obtain ⟨htpos, htR⟩ := ht
    obtain ⟨z, hzS, hzA⟩ := hne t ⟨htpos, htR⟩
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hW z (htW ⟨hzS, hzA⟩)
    obtain ⟨ν, hνpos, hν⟩ := hcap t ⟨htpos, htR⟩ z ⟨hzS, hzA⟩ δ hδpos
    set η : ℝ := min (δ / 2) (min (t / 2) ((R - t) / 2)) with hηdef
    have hηpos : 0 < η := by
      rw [hηdef]
      exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hηδ : η ≤ δ / 2 := by rw [hηdef]; exact min_le_left _ _
    have hηt : η ≤ t / 2 := by
      rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hηR : η ≤ (R - t) / 2 := by
      rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    refine ⟨min η ν, lt_min hηpos hνpos, ?_⟩
    intro t' ht'
    rw [Metric.mem_ball, Real.dist_eq] at ht'
    have ht'ν : |t' - t| < ν := lt_of_lt_of_le ht' (min_le_right _ _)
    have ht'η : |t' - t| < η := lt_of_lt_of_le ht' (min_le_left _ _)
    have ht'pos : 0 < t' := by
      have h := (abs_lt.mp (lt_of_lt_of_le ht'η hηt)).1
      linarith
    have ht'R : t' < R := by
      have h := (abs_lt.mp (lt_of_lt_of_le ht'η hηR)).2
      linarith
    obtain ⟨w, ⟨hwS, hwA⟩, hwbal⟩ := hν t' ⟨ht'pos, ht'R⟩ ht'ν
    have hwW : w ∈ W := hδsub (Metric.ball_subset_ball (by linarith) hwbal)
    rcases hWor t' ⟨ht'pos, ht'R⟩ with h | h
    · exact ⟨⟨ht'pos, ht'R⟩, h⟩
    · exact absurd hwW (Set.disjoint_left.mp h ⟨hwS, hwA⟩)
  have hopenU : IsOpen {t : ℝ | t ∈ Set.Ioo (0:ℝ) R ∧ Metric.sphere y₁ t \ A ⊆ U} :=
    hopen_of U hU (fun t ht => (key t ht).imp id (hdisjU t ht))
  have hopenV : IsOpen {t : ℝ | t ∈ Set.Ioo (0:ℝ) R ∧ Metric.sphere y₁ t \ A ⊆ V} :=
    hopen_of V hV (fun t ht => (key t ht).symm.imp id (hdisjV t ht))
  have hcov : Set.Ioo (0:ℝ) R ⊆
      {t : ℝ | t ∈ Set.Ioo (0:ℝ) R ∧ Metric.sphere y₁ t \ A ⊆ U} ∪
      {t : ℝ | t ∈ Set.Ioo (0:ℝ) R ∧ Metric.sphere y₁ t \ A ⊆ V} := by
    intro t ht
    rcases key t ht with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr ⟨ht, h⟩
  have hdis : Set.Ioo (0:ℝ) R ∩
      ({t : ℝ | t ∈ Set.Ioo (0:ℝ) R ∧ Metric.sphere y₁ t \ A ⊆ U} ∩
        {t : ℝ | t ∈ Set.Ioo (0:ℝ) R ∧ Metric.sphere y₁ t \ A ⊆ V}) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro t hmem
    have ht : t ∈ Set.Ioo (0:ℝ) R := hmem.1
    have htU : Metric.sphere y₁ t \ A ⊆ U := hmem.2.1.2
    have htV : Metric.sphere y₁ t \ A ⊆ V := hmem.2.2.2
    obtain ⟨z, hzS, hzA⟩ := hne t ht
    exact Set.eq_empty_iff_forall_notMem.mp hUVdisj z
      ⟨hball t ht ⟨hzS, hzA⟩, htU ⟨hzS, hzA⟩, htV ⟨hzS, hzA⟩⟩
  rcases isPreconnected_iff_subset_of_disjoint.mp isPreconnected_Ioo _ _ hopenU hopenV hcov hdis with
    hall | hall
  · left
    intro z hz
    rw [Set.mem_sdiff] at hz
    obtain ⟨hzball, hzA⟩ := hz
    by_cases hzy : z = y₁
    · -- the centre of the ball: reach it by a shell of very small radius
      by_contra hzU
      have hzV : z ∈ V := by
        rcases hUV ⟨hzball, hzA⟩ with h | h
        · exact absurd h hzU
        · exact h
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hV z hzV
      obtain ⟨t, htpos, htmin⟩ : ∃ t : ℝ, 0 < t ∧ t < min δ R :=
        ⟨min δ R / 2, by linarith [lt_min hδpos hR], by linarith [lt_min hδpos hR]⟩
      have htR : t < R := lt_of_lt_of_le htmin (min_le_right _ _)
      have htδ : t < δ := lt_of_lt_of_le htmin (min_le_left _ _)
      obtain ⟨w, hwS, hwA⟩ := hne t ⟨htpos, htR⟩
      have hwV : w ∈ V := by
        refine hδsub ?_
        rw [Metric.mem_ball, hzy, Metric.mem_sphere.mp hwS]
        exact htδ
      have hwU : w ∈ U := (hall ⟨htpos, htR⟩).2 ⟨hwS, hwA⟩
      exact Set.eq_empty_iff_forall_notMem.mp hUVdisj
        w ⟨hball t ⟨htpos, htR⟩ ⟨hwS, hwA⟩, hwU, hwV⟩
    · -- a point of the shell of radius `dist z y₁`
      have hmem : z ∈ Metric.sphere y₁ (dist z y₁) \ A := ⟨Metric.mem_sphere.mpr rfl, hzA⟩
      exact (hall ⟨dist_pos.mpr hzy, Metric.mem_ball.mp hzball⟩).2 hmem
  · right
    intro z hz
    rw [Set.mem_sdiff] at hz
    obtain ⟨hzball, hzA⟩ := hz
    by_cases hzy : z = y₁
    · by_contra hzV
      have hzU : z ∈ U := by
        rcases hUV ⟨hzball, hzA⟩ with h | h
        · exact h
        · exact absurd h hzV
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hU z hzU
      obtain ⟨t, htpos, htmin⟩ : ∃ t : ℝ, 0 < t ∧ t < min δ R :=
        ⟨min δ R / 2, by linarith [lt_min hδpos hR], by linarith [lt_min hδpos hR]⟩
      have htR : t < R := lt_of_lt_of_le htmin (min_le_right _ _)
      have htδ : t < δ := lt_of_lt_of_le htmin (min_le_left _ _)
      obtain ⟨w, hwS, hwA⟩ := hne t ⟨htpos, htR⟩
      have hwU : w ∈ U := by
        refine hδsub ?_
        rw [Metric.mem_ball, hzy, Metric.mem_sphere.mp hwS]
        exact htδ
      have hwV : w ∈ V := (hall ⟨htpos, htR⟩).2 ⟨hwS, hwA⟩
      exact Set.eq_empty_iff_forall_notMem.mp hUVdisj
        w ⟨hball t ⟨htpos, htR⟩ ⟨hwS, hwA⟩, hwU, hwV⟩
    · have hmem : z ∈ Metric.sphere y₁ (dist z y₁) \ A := ⟨Metric.mem_sphere.mpr rfl, hzA⟩
      exact (hall ⟨dist_pos.mpr hzy, Metric.mem_ball.mp hzball⟩).2 hmem

/-- **Local room.**  Around every point of `h '' K` (`K ⊆ ℝ` compact, `h` continuous and injective
on `K`, in dimension `n ≥ 3`) there are arbitrarily small open neighbourhoods whose complement of
`h '' K` is nonempty and preconnected. -/
theorem exists_local_room {n : ℕ} (hn : 3 ≤ n) {K : Set ℝ} (hK : IsCompact K)
    {h : ℝ → EuclideanSpace ℝ (Fin n)} (hh : ContinuousOn h K) (hinj : Set.InjOn h K)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ h '' K) {N : Set (EuclideanSpace ℝ (Fin n))}
    (hN : N ∈ 𝓝 y) :
    ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ y ∈ O ∧ O ⊆ N ∧
      (O \ h '' K).Nonempty ∧ IsPreconnected (O \ h '' K) := by
  classical
  set A : Set (EuclideanSpace ℝ (Fin n)) := h '' K with hA
  have hAcpt : IsCompact A := hK.image_of_continuousOn hh
  have hAcl : IsClosed A := hAcpt.isClosed
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hN
  obtain ⟨u, hu0, huslice⟩ := slices_totallyDisconnected (n := n) (by omega) hK hh hinj y
  obtain ⟨y₁, hy₁ρ, hy₁⟩ :=
    center_avoiding_spherical_arcs (n := n) (by omega) hK hh hinj y (ρ := ρ / 4) (by linarith)
  set R : ℝ := ρ / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hy_mem : y ∈ Metric.ball y₁ R := by
    rw [Metric.mem_ball, hRdef]
    linarith [dist_comm y₁ y]
  have hOsub : Metric.ball y₁ R ⊆ N := by
    intro z hz
    refine hρsub ?_
    rw [Metric.mem_ball] at hz ⊢
    calc dist z y ≤ dist z y₁ + dist y₁ y := dist_triangle z y₁ y
      _ < R + ρ / 4 := by rw [hRdef] at hz; linarith [dist_comm y₁ y, hy₁ρ]
      _ < ρ := by rw [hRdef]; linarith
  have htd_sphere : ∀ t : ℝ, IsTotallyDisconnected (A ∩ Metric.sphere y₁ t) := by
    intro t S hS hSpre
    refine subsingleton_of_isPreconnected_const_dist (t := t) hK hh hinj hy₁ ?_ hSpre ?_
    · intro z hz; exact (hS hz).1
    · intro z hz; exact Metric.mem_sphere.mp (hS hz).2
  have hshell : ∀ t : ℝ, 0 < t → t < R → IsPreconnected (Metric.sphere y₁ t \ A) ∧
      (Metric.sphere y₁ t \ A).Nonempty := by
    intro t htpos htR
    have hpre := sphere_sdiff_isCompact_totallyDisconnected_isPreconnected
      (E := EuclideanSpace ℝ (Fin n)) (by rw [finrank_euclideanSpace_fin]; omega)
      (c := y₁) (r := t) htpos (hAcpt.inter_right Metric.isClosed_sphere)
      Set.inter_subset_right (htd_sphere t)
    have heq : Metric.sphere y₁ t \ (A ∩ Metric.sphere y₁ t) = Metric.sphere y₁ t \ A := by
      ext z
      constructor
      · rintro ⟨hz, hzA⟩
        exact ⟨hz, fun hzmem => hzA ⟨hzmem, hz⟩⟩
      · rintro ⟨hz, hzA⟩
        exact ⟨hz, fun hzmem => hzA hzmem.1⟩
    refine ⟨?_, ?_⟩
    · rwa [heq] at hpre
    · by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      have hsub : Metric.sphere y₁ t ⊆ A ∩ Metric.sphere y₁ t := by
        intro z hz
        refine ⟨?_, hz⟩
        by_contra hzA
        have hnon : (Metric.sphere y₁ t \ A).Nonempty := ⟨z, hz, hzA⟩
        rw [hcon] at hnon
        obtain ⟨z', hz'⟩ := hnon
        exact hz'
      have hrank1 : (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
        rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
        exact_mod_cast (by omega : 1 < n)
      have hsingle : (Metric.sphere y₁ t).Subsingleton :=
        htd_sphere t _ hsub (isPreconnected_sphere hrank1 y₁ t)
      exact not_subsingleton_sphere (by omega) y₁ htpos hsingle
  -- the shell of radius `t'` of a nearby radius meets a small ball around any point of the shell
  have hcap : ∀ t ∈ Set.Ioo (0:ℝ) R, ∀ z ∈ Metric.sphere y₁ t \ A, ∀ δ > 0,
      ∃ ν > 0, ∀ t' ∈ Set.Ioo (0:ℝ) R, |t' - t| < ν →
        ((Metric.sphere y₁ t' \ A) ∩ Metric.ball z δ).Nonempty := by
    intro t ht z hz δ hδ
    have hzS : ‖z - y₁‖ = t := by
      rw [← dist_eq_norm]; exact Metric.mem_sphere.mp hz.1
    refine ⟨δ / 2, by linarith, ?_⟩
    intro t' ht' hclose
    obtain ⟨w, hw, hwT⟩ := exists_notMem_sphere_inter_ball
      (E := EuclideanSpace ℝ (Fin n)) (t := t) (t' := t') (ε := δ)
      (by rw [finrank_euclideanSpace_fin]; omega) ht.1 ht'.1 hzS hδ hclose
      Set.inter_subset_right (htd_sphere t')
    exact ⟨w, ⟨hw.1, fun hwA => hwT ⟨hwA, hw.1⟩⟩, hw.2⟩
  have hpreball : IsPreconnected (Metric.ball y₁ R \ A) :=
    isPreconnected_ball_sdiff_of_shells hRpos
      (fun t ht => (hshell t ht.1 ht.2).1) (fun t ht => (hshell t ht.1 ht.2).2) hcap
  refine ⟨Metric.ball y₁ R, Metric.isOpen_ball, hy_mem, hOsub, ?_, ?_⟩
  · obtain ⟨t, htpos, htR⟩ : ∃ t : ℝ, 0 < t ∧ t < R := ⟨R / 2, by linarith, by linarith⟩
    obtain ⟨w, hwS, hwA⟩ := (hshell t htpos htR).2
    refine ⟨w, ⟨?_, hA ▸ hwA⟩⟩
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (le_of_eq (Metric.mem_sphere.mp hwS)) htR
  · exact hA ▸ hpreball

/-- **Target lemma.** For `n ≥ 3`, a compact `K ⊆ ℝ` mapped by `h` continuous and injective on
`K`, and `p ∈ h '' K`, every neighbourhood of `p` contains a ball whose complement inside it,
minus the curve `h '' K`, is path connected. -/
theorem room_at_arc_subset {n : ℕ} (hn : 3 ≤ n) {K : Set ℝ} (hK : IsCompact K)
    {h : ℝ → EuclideanSpace ℝ (Fin n)} (hh : ContinuousOn h K) (hinj : Set.InjOn h K)
    {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ h '' K) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ IsPathConnected (Metric.ball p r \ h '' K) := by
  classical
  have hAcl : IsClosed (h '' K) := (hK.image_of_continuousOn hh).isClosed
  haveI : LocallyPathConnectedSpace (EuclideanSpace ℝ (Fin n)) := inferInstance
  have hloc : ∀ y ∈ h '' K, ∀ N ∈ 𝓝 y, ∃ O : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen O ∧ y ∈ O ∧ O ⊆ N ∧ (O \ h '' K).Nonempty ∧ IsPreconnected (O \ h '' K) :=
    fun y hy N hN => exists_local_room hn hK hh hinj hy hN
  -- a nearby point of the complement, used to see that the room is nonempty
  obtain ⟨O, hOopen, hpO, hOsub, ⟨z, hzO, hzY⟩, -⟩ :=
    hloc p hp (Metric.ball p (ε / 4)) (Metric.ball_mem_nhds p (by linarith))
  have hdz : dist z p < ε / 4 := Metric.mem_ball.mp (hOsub hzO)
  refine ⟨ε / 2, by linarith, by linarith, ?_⟩
  have hpre : IsPreconnected (Metric.ball p (ε / 2) \ h '' K) :=
    isPreconnected_sdiff_of_local_room Metric.isPreconnected_ball Metric.isOpen_ball hAcl hloc
  have hne : (Metric.ball p (ε / 2) \ h '' K).Nonempty :=
    ⟨z, Metric.mem_ball.mpr (by linarith), hzY⟩
  have hopen : IsOpen (Metric.ball p (ε / 2) \ h '' K) := Metric.isOpen_ball.sdiff hAcl
  exact (IsOpen.isConnected_iff_isPathConnected hopen).mp ⟨hne, hpre⟩

end Work.Whitney.PathTools
