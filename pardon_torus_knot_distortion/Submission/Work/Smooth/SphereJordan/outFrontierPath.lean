import Mathlib
import Submission.Work.Smooth.SphereJordan.farPointsSameComponent
import Submission.Work.BoxShrink.Pinch.borsuk_frontier_connectedComponentIn

/-!
# The outer boundary of a finite union of equal closed balls

For `S = ⋃_{w ∈ P} closedBall w r` (a finite union of equal closed discs) the "outer boundary" is the
frontier `ω = frontier U`, where `U` is the component of a far point `x` in `Sᶜ` (equivalently: the
unbounded complementary component).  This module provides the two structural facts behind the
frontier-loop connector:

* `escapeRay_mem_frontier_component`: a point of `S` out of which a straight ray escapes from `S`
  lies on `ω` (join it to a far point of its own ray inside `Sᶜ`);
* `frontier_component_isPreconnected`: `ω` is preconnected (Wilder/Brouwer), in the clash-free form
  `Work.BoxShrink.Pinch.borsuk_frontier_connectedComponentIn`.

The points carrying an escaping ray are exactly the support points and the one-sided limits of the
envelope trace, i.e. the endpoints of the connectors of `ballUnionFrontierLoop_NOTES.md` §C/§G.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- Two points of the same connected component of a set have the same component.  (Local copy under a
distinctive name: this module must not depend on `arcPtOuterBoundary.lean`.) -/
theorem compIn_eq_of_mem' {X : Set ℂ} {y z : ℂ} (hy : y ∈ X)
    (hz : z ∈ connectedComponentIn X y) :
    connectedComponentIn X z = connectedComponentIn X y := by
  have hzX : z ∈ X := connectedComponentIn_subset X y hz
  have hpre : IsPreconnected (connectedComponentIn X z ∪ connectedComponentIn X y) :=
    IsPreconnected.union z (mem_connectedComponentIn hzX) hz
      isPreconnected_connectedComponentIn isPreconnected_connectedComponentIn
  have hsub : connectedComponentIn X z ∪ connectedComponentIn X y ⊆ X := by
    intro u hu
    rcases hu with hu | hu
    · exact connectedComponentIn_subset X z hu
    · exact connectedComponentIn_subset X y hu
  refine le_antisymm ?_ ?_
  · exact fun u hu =>
      hpre.subset_connectedComponentIn (Or.inr (mem_connectedComponentIn hy)) hsub (Or.inl hu)
  · exact fun u hu =>
      hpre.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hzX)) hsub (Or.inr hu)

/-- **Step 1 engine (a):** the endpoint of a path in `K` lies in the connected component of the
starting point.  This replaces path concatenation in the clopen argument. -/
theorem connectedComponentIn_of_path {K : Set ℂ} {a b : ℂ} (ha : a ∈ K) {γ : C(unitInterval, ℂ)}
    (hγ : ∀ t, γ t ∈ K) (h0 : γ 0 = a) (h1 : γ 1 = b) :
    b ∈ connectedComponentIn K a := by
  have hpre : IsPreconnected (Set.range γ) := isPreconnected_range γ.continuous
  have hsub : Set.range γ ⊆ K := by
    rintro y ⟨t, rfl⟩
    exact hγ t
  exact hpre.subset_connectedComponentIn ⟨0, h0⟩ hsub ⟨1, h1⟩

/-- **Step 1 engine (b) (the transfer):** if `K` is locally path connected around `z` with radius
`ε` and `z` lies in the connected component of `p`, then every `K`-point within `ε` of `z` lies in
that same component.  No concatenation is used: the path is fed through
`connectedComponentIn_of_path` and `compIn_eq_of_mem'`. -/
theorem connectedComponentIn_transfer {K : Set ℂ} {p z y : ℂ} {ε : ℝ} (hpK : p ∈ K)
    (hzA : z ∈ connectedComponentIn K p) (hyK : y ∈ K) (hd : dist y z < ε)
    (hprop : ∃ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ K) ∧ γ 0 = z ∧ γ 1 = y) :
    y ∈ connectedComponentIn K p := by
  obtain ⟨γ, hγK, hγ0, hγ1⟩ := hprop
  have hzK : z ∈ K := connectedComponentIn_subset K p hzA
  have hyc : y ∈ connectedComponentIn K z :=
    connectedComponentIn_of_path hzK hγK hγ0 hγ1
  rwa [compIn_eq_of_mem' hpK hzA] at hyc

/-- **`A` is closed in `K`** (Step 1, closedness half): a connected component of a closed set is
closed.  No analysis is needed — this is the "free" half of the clopen argument (§N). -/
theorem isClosed_connectedComponentIn_closed {K : Set ℂ} (hK : IsClosed K) (p : ℂ) :
    IsClosed (connectedComponentIn K p) := by
  by_cases hpK : p ∈ K
  · rw [connectedComponentIn_eq_image hpK]
    exact (hK.isClosedEmbedding_subtypeVal).isClosedMap _ isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hpK]
    exact isClosed_empty

/-- **`A` is open in `K`** (Step 1, openness half): if `K` is locally path connected with the
pointwise radii `ε`, then every `K`-point within `ε z` of a point `z` of the component of `p` lies
in that component.  This is the only place where `ε` (and hence `hloc`) is used, one point at a
time; no global radius is needed (§N). -/
theorem connectedComponentIn_openIn {K : Set ℂ} {p : ℂ} (hpK : p ∈ K)
    (ε : ℂ → ℝ)
    (hloc : ∀ z ∈ K, ∀ y ∈ K, dist y z < ε z →
      ∃ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ K) ∧ γ 0 = z ∧ γ 1 = y) :
    ∀ z ∈ connectedComponentIn K p, ∀ y ∈ K, dist y z < ε z →
      y ∈ connectedComponentIn K p :=
  fun z hz y hyK hd =>
    connectedComponentIn_transfer hpK hz hyK hd (hloc z (connectedComponentIn_subset K p hz) y hyK hd)

/-- **§M step 4.**  Concatenation of two paths with matching endpoints: the single place where the
connector spends a path composition (everything else uses `connectedComponentIn_of_path`). -/
theorem exists_concat {a b c : ℂ} {γ₁ γ₂ : C(unitInterval, ℂ)}
    (h₁ : γ₁ 0 = a) (h₂ : γ₁ 1 = b) (h₃ : γ₂ 0 = b) (h₄ : γ₂ 1 = c) :
    ∃ γ : C(unitInterval, ℂ), γ 0 = a ∧ γ 1 = c ∧
      ∀ t, γ t ∈ Set.range γ₁ ∪ Set.range γ₂ := by
  set P₁ : Path a b := ⟨γ₁, h₁, h₂⟩ with hP₁
  set P₂ : Path b c := ⟨γ₂, h₃, h₄⟩ with hP₂
  refine ⟨(P₁.trans P₂).toContinuousMap, ?_, ?_, ?_⟩
  · simpa using (P₁.trans P₂).source
  · simpa using (P₁.trans P₂).target
  · intro t
    show (P₁.trans P₂) t ∈ Set.range γ₁ ∪ Set.range γ₂
    rw [Path.trans_apply]
    split_ifs with h
    · exact Or.inl ⟨⟨2 * (t : ℝ), ⟨by linarith [t.2.1, h], by linarith [t.2.2]⟩⟩, rfl⟩
    · exact Or.inr ⟨⟨2 * (t : ℝ) - 1,
        ⟨by linarith [not_le.mp h], by linarith [t.2.2]⟩⟩, rfl⟩

/-- **§Q, reversal.**  A path in `K` traversed backwards, in the in-`K` form needed for the
closedness half of §Q (no `Set.range` bookkeeping). -/
theorem exists_reverse {K : Set ℂ} {a b : ℂ} {γ : C(unitInterval, ℂ)}
    (hK : ∀ t, γ t ∈ K) (h₀ : γ 0 = a) (h₁ : γ 1 = b) :
    ∃ γ' : C(unitInterval, ℂ), (∀ t, γ' t ∈ K) ∧ γ' 0 = b ∧ γ' 1 = a := by
  have hcont : Continuous fun t : unitInterval =>
      (⟨1 - (t : ℝ), ⟨by linarith [t.2.2], by linarith [t.2.1]⟩⟩ : unitInterval) := by
    fun_prop
  set F : unitInterval → unitInterval :=
    fun t => ⟨1 - (t : ℝ), ⟨by linarith [t.2.2], by linarith [t.2.1]⟩⟩ with hF
  refine ⟨γ.comp ⟨F, ?_⟩, fun t => hK _, ?_, ?_⟩
  · rw [hF]; exact hcont
  · have hF0 : F 0 = 1 := by
      rw [hF]
      apply Subtype.ext
      norm_num
    show γ (F 0) = b
    rw [hF0]; exact h₁
  · have hF1 : F 1 = 0 := by
      rw [hF]
      apply Subtype.ext
      norm_num
    show γ (F 1) = a
    rw [hF1]; exact h₀

/-- **§Q, openness half.**  If `K` is locally path connected with radii `ε`, then the set of points
of `K` reachable from `p` by a path in `K` is open in `K`: concatenate the path to `z` with the local
path `z → y` (`exists_concat`). -/
theorem pathReach_openIn {K : Set ℂ} {p : ℂ} (ε : ℂ → ℝ)
    (hloc : ∀ z ∈ K, ∀ y ∈ K, dist y z < ε z →
      ∃ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ K) ∧ γ 0 = z ∧ γ 1 = y) :
    ∀ z ∈ K, (∃ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ K) ∧ γ 0 = p ∧ γ 1 = z) →
      ∀ y ∈ K, dist y z < ε z →
        ∃ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ K) ∧ γ 0 = p ∧ γ 1 = y := by
  intro z hzK hreach y hyK hd
  obtain ⟨γ₁, hγ₁K, hγ₁0, hγ₁1⟩ := hreach
  obtain ⟨γ₂, hγ₂K, hγ₂0, hγ₂1⟩ := hloc z hzK y hyK hd
  obtain ⟨γ, hγ0, hγ1, hγr⟩ := exists_concat hγ₁0 hγ₁1 hγ₂0 hγ₂1
  refine ⟨γ, fun t => ?_, hγ0, hγ1⟩
  have h := hγr t
  rw [Set.mem_union] at h
  rcases h with h | h
  · obtain ⟨s, hs⟩ := h; rw [← hs]; exact hγ₁K s
  · obtain ⟨s, hs⟩ := h; rw [← hs]; exact hγ₂K s

/-- **§Q, closedness half.**  With the radius `ε z` taken at the point `z` we are *at* (the §N move,
which is what makes the two radii cancel), a limit point of the reachable set is reachable:
`hloc z` gives `z → y`, `exists_reverse` turns it into `y → z`, and `exists_concat` composes it with
the reachable path `p → y`. -/
theorem pathReach_closedIn {K : Set ℂ} {p : ℂ} (ε : ℂ → ℝ) (hε : ∀ z ∈ K, 0 < ε z)
    (hloc : ∀ z ∈ K, ∀ y ∈ K, dist y z < ε z →
      ∃ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ K) ∧ γ 0 = z ∧ γ 1 = y) :
    ∀ z ∈ K, (∀ δ : ℝ, 0 < δ → ∃ y ∈ K, dist y z < δ ∧
        ∃ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ K) ∧ γ 0 = p ∧ γ 1 = y) →
      ∃ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ K) ∧ γ 0 = p ∧ γ 1 = z := by
  intro z hzK hcl
  obtain ⟨y, hyK, hyz, γ₁, hγ₁K, hγ₁0, hγ₁1⟩ := hcl (ε z) (hε z hzK)
  obtain ⟨γ₂, hγ₂K, hγ₂0, hγ₂1⟩ := hloc z hzK y hyK hyz
  obtain ⟨γ₃, hγ₃K, hγ₃0, hγ₃1⟩ := exists_reverse hγ₂K hγ₂0 hγ₂1
  obtain ⟨γ, hγ0, hγ1, hγr⟩ := exists_concat hγ₁0 hγ₁1 hγ₃0 hγ₃1
  refine ⟨γ, fun t => ?_, hγ0, hγ1⟩
  have h := hγr t
  rw [Set.mem_union] at h
  rcases h with h | h
  · obtain ⟨s, hs⟩ := h; rw [← hs]; exact hγ₁K s
  · obtain ⟨s, hs⟩ := h; rw [← hs]; exact hγ₃K s

/-- **§O move 1: `u` is closed in `↥ω`.**  The clopen set of the subtype argument is the
preimage of a connected component (closed in the ambient space by `isClosed_connectedComponentIn_closed
whenever `K` is closed) under the continuous coercion `↥ω → ℂ`. -/
theorem isClosed_subtype_connectedComponentIn {K ω : Set ℂ} (hK : IsClosed K) (p : ℂ) :
    IsClosed {z : ↥ω | (z : ℂ) ∈ connectedComponentIn K p} :=
  IsClosed.preimage continuous_subtype_val (isClosed_connectedComponentIn_closed hK p)

/-- **Step 0 of the connector** (`ballUnionFrontierLoop_NOTES.md` §K): the frontier of a
complementary component of a closed set lies in the frontier of the set. -/
theorem frontier_componentIn_subset {S : Set ℂ} (hS : IsClosed S) {x : ℂ} :
    frontier (connectedComponentIn Sᶜ x) ⊆ frontier S := by
  set U : Set ℂ := connectedComponentIn Sᶜ x with hU
  have hz' : ∀ {z : ℂ}, z ∈ frontier (connectedComponentIn Sᶜ x) → z ∈ frontier U := fun h => h
  have hUopen : IsOpen U := hS.isOpen_compl.connectedComponentIn
  have hUsub : U ⊆ Sᶜ := connectedComponentIn_subset Sᶜ x
  intro z hz
  have hzU := hz' hz
  have hzclU : z ∈ closure U := hzU.1
  have hznotU : z ∉ U := by
    have h2 : z ∉ interior U := hzU.2
    rwa [hUopen.interior_eq] at h2
  -- `z ∈ S = closure S`
  have hzS : z ∈ S := by
    by_contra hcon
    have h1 : z ∈ closure U ∩ Sᶜ := ⟨hzclU, hcon⟩
    have h2 := Work.BoxShrink.Pinch.closure_connectedComponentIn_inter_compl_subset_self
      (M := S) (y := x) h1
    exact hznotU h2
  -- `z ∉ interior S`
  have hznotint : z ∉ interior S := by
    have h1 : z ∈ closure Sᶜ := closure_mono hUsub hzclU
    rwa [closure_compl] at h1
  refine ⟨?_, hznotint⟩
  rwa [hS.closure_eq]

/-- **An escaping ray puts a point of the union on the outer boundary.**  If `p ∈ S` and the open ray
`{p + t·n : t > 0}` (`‖n‖ = 1`) misses `S = ⋃ w ∈ P, closedBall w r`, then `p` lies on the frontier
of the component of any far point `x` of `Sᶜ`. -/
theorem escapeRay_mem_frontier_component {P : Finset ℂ} {r M : ℝ} (hr : 0 < r)
    (hM : ∀ w ∈ P, ‖w‖ + r < M) {p n x : ℂ} (hn : ‖n‖ = 1) (hx : M < ‖x‖)
    (hpS : p ∈ ⋃ w ∈ P, Metric.closedBall w r)
    (hray : ∀ t : ℝ, 0 < t → p + (t : ℂ) * n ∉ ⋃ w ∈ P, Metric.closedBall w r) :
    p ∈ frontier (connectedComponentIn (⋃ w ∈ P, Metric.closedBall w r)ᶜ x) := by
  set S : Set ℂ := ⋃ w ∈ P, Metric.closedBall w r with hS
  set U : Set ℂ := connectedComponentIn Sᶜ x with hU
  set f : ℝ → ℂ := fun s => p + (s : ℂ) * n with hf
  -- `p ∈ S`, so `p` is not in the open component `U ⊆ Sᶜ`
  have hpU : p ∉ U := by
    intro h
    exact (connectedComponentIn_subset Sᶜ x h) (by rw [hS]; exact hpS)
  -- the far point `x` lies outside `S`
  have hxS : x ∈ Sᶜ := by
    rw [hS, Set.mem_compl_iff]
    intro hmem
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hmem
    rw [Metric.mem_closedBall, dist_eq_norm] at hxw
    have h1 : ‖x‖ - ‖w‖ ≤ ‖x - w‖ := norm_sub_norm_le x w
    linarith [hM w hw]
  -- the ray misses `S`
  have hrayS : ∀ t : ℝ, 0 < t → f t ∉ S := by
    intro t ht hmem
    exact hray t ht (by rw [hS] at hmem; exact hmem)
  -- a far point of the ray
  set T : ℝ := |M| + ‖p‖ + 1 with hTdef
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hTdef]; have := abs_nonneg M; have := norm_nonneg p; linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hval : f T = p + (T : ℂ) * n := by simp only [hf]
  have hTnorm : M < ‖f T‖ := by
    rw [hval]
    have h3 : ‖(T : ℂ) * n‖ = T := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos, hn, mul_one]
    have h1 : ‖(T : ℂ) * n‖ - ‖p‖ ≤ ‖(T : ℂ) * n - (-p)‖ := by
      simpa using norm_sub_norm_le ((T : ℂ) * n) (-p)
    have h2 : (T : ℂ) * n - (-p) = p + (T : ℂ) * n := by ring
    rw [h2, h3] at h1
    have h4 : T - ‖p‖ = |M| + 1 := by rw [hTdef]; ring
    have h5 : M ≤ |M| := le_abs_self M
    linarith
  have hTmem : f T ∈ U := by
    rw [hU]
    exact farPointsSameComponent P hr hM hx hTnorm
  -- the piece of the ray between `f 1` and `f T` misses `S`, hence lies in `U`
  have hsegsub : f '' Set.Icc (1 : ℝ) T ⊆ Sᶜ := by
    rintro y ⟨s, hs, rfl⟩
    exact hrayS s (by linarith [hs.1])
  have hsegpre : IsPreconnected (f '' Set.Icc (1 : ℝ) T) :=
    isPreconnected_Icc.image f (by rw [hf]; fun_prop)
  have h1mem : f 1 ∈ U := by
    have hcomp : f 1 ∈ connectedComponentIn Sᶜ (f T) :=
      hsegpre.subset_connectedComponentIn ⟨T, ⟨hT1, le_rfl⟩, rfl⟩ hsegsub
        ⟨1, ⟨le_rfl, hT1⟩, rfl⟩
    have heq : connectedComponentIn Sᶜ (f T) = U := by
      rw [hU]; exact compIn_eq_of_mem' hxS hTmem
    rwa [heq] at hcomp
  -- for small positive parameters the ray point is in `U` as well
  have hsmall : ∀ t : ℝ, 0 < t → t ≤ 1 → f t ∈ U := by
    intro t htpos ht1
    have hsub' : f '' Set.Icc t 1 ⊆ Sᶜ := by
      rintro y ⟨s, hs, rfl⟩
      exact hrayS s (by linarith [hs.1])
    have hpre' : IsPreconnected (f '' Set.Icc t 1) :=
      isPreconnected_Icc.image f (by rw [hf]; fun_prop)
    have hcomp : f t ∈ connectedComponentIn Sᶜ (f 1) :=
      hpre'.subset_connectedComponentIn ⟨1, ⟨ht1, le_rfl⟩, rfl⟩ hsub'
        ⟨t, ⟨le_rfl, ht1⟩, rfl⟩
    have heq : connectedComponentIn Sᶜ (f 1) = U := by
      rw [hU]; exact compIn_eq_of_mem' hxS h1mem
    rwa [heq] at hcomp
  -- hence `p` is a limit point of `U`
  have hcl : p ∈ closure U := by
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    set t : ℝ := min 1 ε / 2 with htdef
    have htpos : 0 < t := by rw [htdef]; positivity
    have ht1 : t ≤ 1 := by rw [htdef]; linarith [min_le_left (1 : ℝ) ε]
    have htε : t < ε := by rw [htdef]; linarith [min_le_right (1 : ℝ) ε]
    refine ⟨f t, hsmall t htpos ht1, ?_⟩
    have hft : f t - p = (t : ℂ) * n := by simp only [hf]; ring
    rw [dist_comm, dist_eq_norm, hft, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos, hn, mul_one]
    exact htε
  exact ⟨hcl, fun h => hpU (interior_subset h)⟩

/-- **The outer boundary is a continuum.**  For a preconnected finite union of equal closed discs,
the frontier of the component of any point `x` in the complement is preconnected (Wilder's theorem,
via the unicoherence of the plane). -/
theorem frontier_component_isPreconnected {P : Finset ℂ} {r : ℝ} (hr : 0 < r)
    (hpre : IsPreconnected (⋃ w ∈ P, Metric.closedBall w r)) (x : ℂ) :
    IsPreconnected (frontier (connectedComponentIn (⋃ w ∈ P, Metric.closedBall w r)ᶜ x)) := by
  have _ : (0 : ℝ) < r := hr
  exact Work.BoxShrink.Pinch.borsuk_frontier_connectedComponentIn
    (Set.Finite.isCompact_biUnion P.finite_toSet fun w _ => isCompact_closedBall w r) hpre x

end

end Work.Smooth.SphereJordan
