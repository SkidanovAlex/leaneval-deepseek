import Mathlib
import Submission.Work.BW.Minkowski2.section_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Section maps for a symmetric convex body

`Work.BW.Minkowski2.section_maps`: for a closed, bounded, symmetric convex body `K ⊆ ℝᵈ` with
nonempty interior, and each `i : Fin d`, there is a *measurable* map `c i` which keeps the
coordinates `m ≥ i`, depends only on those coordinates, maps `K` into `K` and its interior into
its interior.

For each suffix `s` one selects measurably a point of the section `{x ∈ K | suf i x = s}`, choosing
it inside a dilate `(1 - 1/(n+1)) • K` (hence in the interior of `K`) whenever the section meets
the interior.  The selection is obtained from a measurable selection theorem
(`exists_measurable_selection_aux`, a Kuratowski–Ryll-Nardzewski/Castaing-style greedy
construction) applied to a multifunction whose values are those sections.
-/

open Set Metric Filter
open scoped Topology Pointwise

namespace Work.BW.Minkowski2

variable {d : ℕ}

-- PLACEHOLDER (delegated)
theorem exists_measurable_selection_aux {α : Type*} [MeasurableSpace α] {E : Type*}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] [Nonempty E] [CompleteSpace E]
    (Φ : α → Set E) (hne : ∀ a, (Φ a).Nonempty) (hcl : ∀ a, IsClosed (Φ a))
    (hmeas : ∀ y : E, ∀ r : ℝ, 0 < r → MeasurableSet {a | ∃ x ∈ Φ a, dist x y < r}) :
    ∃ f : α → E, Measurable f ∧ ∀ a, f a ∈ Φ a := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : ℕ → E, DenseRange q :=
    ⟨TopologicalSpace.denseSeq E, TopologicalSpace.denseRange_denseSeq E⟩
  have hex : ∀ (g : α → E) (n : ℕ), (∀ a, ∃ x ∈ Φ a, dist (g a) x < (1 / 2 : ℝ) ^ n) →
      ∀ a, ∃ k : ℕ, (∃ x ∈ Φ a, dist x (q k) < (1 / 2 : ℝ) ^ (n + 1)) ∧
        dist (g a) (q k) < 2 * (1 / 2 : ℝ) ^ n := by
    intro g n hg a
    obtain ⟨x, hxΦ, hxg⟩ := hg a
    obtain ⟨k, hk⟩ := hq.exists_dist_lt x (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 1))
    refine ⟨k, ⟨x, hxΦ, hk⟩, ?_⟩
    have h2 : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n * (1 / 2) := by rw [pow_succ]
    calc dist (g a) (q k) ≤ dist (g a) x + dist x (q k) := dist_triangle _ _ _
      _ < (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ (n + 1) := add_lt_add_of_lt_of_lt hxg hk
      _ = (1 / 2 : ℝ) ^ n * (1 + 1 / 2) := by rw [h2]; ring
      _ ≤ 2 * (1 / 2 : ℝ) ^ n := by
            have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
            nlinarith
  let step (g : α → E) (n : ℕ) (hg : ∀ a, ∃ x ∈ Φ a, dist (g a) x < (1 / 2 : ℝ) ^ n) : α → E :=
    fun a => q (Nat.find (hex g n hg a))
  have step_approx (g : α → E) (n : ℕ) (hg : ∀ a, ∃ x ∈ Φ a, dist (g a) x < (1 / 2 : ℝ) ^ n) :
      ∀ a, ∃ x ∈ Φ a, dist (step g n hg a) x < (1 / 2 : ℝ) ^ (n + 1) := by
    intro a
    obtain ⟨⟨x, hxΦ, hk⟩, -⟩ := Nat.find_spec (hex g n hg a)
    exact ⟨x, hxΦ, by rw [dist_comm]; exact hk⟩
  have step_dist (g : α → E) (n : ℕ) (hg : ∀ a, ∃ x ∈ Φ a, dist (g a) x < (1 / 2 : ℝ) ^ n) :
      ∀ a, dist (step g n hg a) (g a) < 2 * (1 / 2 : ℝ) ^ n := by
    intro a
    have h := (Nat.find_spec (hex g n hg a)).2
    rw [dist_comm]; exact h
  have step_meas (g : α → E) (n : ℕ) (hg : ∀ a, ∃ x ∈ Φ a, dist (g a) x < (1 / 2 : ℝ) ^ n)
      (hgm : Measurable g) : Measurable (step g n hg) := by
    have hm : ∀ k : ℕ, MeasurableSet {a : α | (∃ x ∈ Φ a,
        dist x (q k) < (1 / 2 : ℝ) ^ (n + 1)) ∧ dist (g a) (q k) < 2 * (1 / 2 : ℝ) ^ n} := by
      intro k
      have hQ : MeasurableSet {a : α | dist (g a) (q k) < 2 * (1 / 2 : ℝ) ^ n} :=
        measurableSet_lt (hgm.dist measurable_const) measurable_const
      exact (hmeas (q k) ((1 / 2 : ℝ) ^ (n + 1)) (by positivity)).inter hQ
    exact Measurable.find (p := fun k (a : α) => (∃ x ∈ Φ a,
        dist x (q k) < (1 / 2 : ℝ) ^ (n + 1)) ∧ dist (g a) (q k) < 2 * (1 / 2 : ℝ) ^ n)
      (f := fun k (_ : α) => q k) (fun k => measurable_const) hm (hex g n hg)
  have hinit : ∀ a : α, ∃ k : ℕ, ∃ x ∈ Φ a, dist x (q k) < 1 := by
    intro a
    obtain ⟨x, hx⟩ := hne a
    obtain ⟨k, hk⟩ := hq.exists_dist_lt x (by norm_num : (0 : ℝ) < 1)
    exact ⟨k, x, hx, hk⟩
  let g0 : α → E := fun a => q (Nat.find (hinit a))
  have g0_approx : ∀ a, ∃ x ∈ Φ a, dist (g0 a) x < (1 / 2 : ℝ) ^ 0 := by
    intro a
    obtain ⟨x, hx, hk⟩ := Nat.find_spec (hinit a)
    exact ⟨x, hx, by rw [dist_comm]; simpa using hk⟩
  have g0_meas : Measurable g0 :=
    Measurable.find (p := fun k (a : α) => ∃ x ∈ Φ a, dist x (q k) < 1)
      (f := fun k (_ : α) => q k) (fun k => measurable_const)
      (fun k => by simpa using hmeas (q k) 1 (by norm_num)) hinit
  let S : ℕ → Sort _ := fun n =>
    { f : α → E // (∀ a, ∃ x ∈ Φ a, dist (f a) x < (1 / 2 : ℝ) ^ n) ∧ Measurable f }
  have hS0 : S 0 := ⟨g0, g0_approx, g0_meas⟩
  let hSsucc : ∀ n, S n → S (n + 1) := fun n g =>
    ⟨step g.1 n g.2.1, step_approx g.1 n g.2.1, step_meas g.1 n g.2.1 g.2.2⟩
  let F : ∀ n, S n := Nat.rec hS0 hSsucc
  let f : ℕ → α → E := fun n => (F n).1
  have hf_approx : ∀ n a, ∃ x ∈ Φ a, dist (f n a) x < (1 / 2 : ℝ) ^ n := fun n => (F n).2.1
  have hf_meas : ∀ n, Measurable (f n) := fun n => (F n).2.2
  have hFsucc : ∀ n, F (n + 1) = hSsucc n (F n) := fun n => rfl
  have hSsucc_apply : ∀ (n : ℕ) (g : S n), (hSsucc n g).1 = step g.1 n g.2.1 := by
    intro n g
    dsimp only [hSsucc]
  have hf_step : ∀ n a, dist (f n a) (f (n + 1) a) ≤ 2 * (1 / 2 : ℝ) ^ n := by
    intro n a
    have hfeq : f (n + 1) = step (f n) n (hf_approx n) := by
      show (F (n + 1)).1 = step ((F n).1) n ((F n).2.1)
      rw [hFsucc n, hSsucc_apply]
    rw [hfeq, dist_comm]
    exact le_of_lt (step_dist (f n) n (hf_approx n) a)
  have hcauchy : ∀ a, CauchySeq (fun n => f n a) := fun a =>
    cauchySeq_of_le_geometric (r := 1 / 2) (C := 2) (by norm_num) (f := fun n => f n a)
      (fun n => hf_step n a)
  choose L hL using fun a => cauchySeq_tendsto_of_complete (hcauchy a)
  refine ⟨L, ?_, ?_⟩
  · exact measurable_of_tendsto_metrizable hf_meas (tendsto_pi_nhds.mpr hL)
  · intro a
    rw [← (hcl a).closure_eq]
    refine Metric.mem_closure_iff.mpr ?_
    intro ε hε
    have hp : Tendsto (fun n : ℕ => 8 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (8 : ℝ)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 8 * (1 / 2 : ℝ) ^ n < ε :=
      (hp.eventually (Iio_mem_nhds hε)).exists
    obtain ⟨x, hxΦ, hfx⟩ := hf_approx n a
    refine ⟨x, hxΦ, ?_⟩
    have hbd : dist (f n a) (L a) ≤ 2 * (1 / 2 : ℝ) ^ n / (1 - 1 / 2) :=
      dist_le_of_le_geometric_of_tendsto (r := 1 / 2) (C := 2) (by norm_num)
        (f := fun n => f n a) (fun n => hf_step n a) (hL a) n
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    have hfive : dist (L a) x ≤ 2 * (1 / 2 : ℝ) ^ n / (1 - 1 / 2) + (1 / 2 : ℝ) ^ n := by
      calc dist (L a) x ≤ dist (L a) (f n a) + dist (f n a) x := dist_triangle _ _ _
        _ ≤ 2 * (1 / 2 : ℝ) ^ n / (1 - 1 / 2) + (1 / 2 : ℝ) ^ n :=
            add_le_add (by rwa [dist_comm] at hbd) (le_of_lt hfx)
    have hbound : 2 * (1 / 2 : ℝ) ^ n / (1 - 1 / 2) + (1 / 2 : ℝ) ^ n < ε := by
      have hone : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
      rw [hone]
      have hfour : 2 * (1 / 2 : ℝ) ^ n / (1 / 2) = 4 * (1 / 2 : ℝ) ^ n := by ring
      rw [hfour]
      nlinarith [hn, hpos]
    exact lt_of_le_of_lt hfive hbound

theorem section_set_measurable_aux {d : ℕ} (L : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (hL : Continuous ⇑L)
    {C : Set (Fin d → ℝ)} (hC : IsClosed C) (hB : Bornology.IsBounded C) (y : Fin d → ℝ)
    {r : ℝ} (hr : 0 < r) :
    MeasurableSet {s : Fin d → ℝ | ∃ x ∈ C, L x = s ∧ dist x y < r} := by
  have hset : {s : Fin d → ℝ | ∃ x ∈ C, L x = s ∧ dist x y < r}
      = ⋃ k : ℕ, ⇑L '' (C ∩ closedBall y (r - 1 / ((k : ℝ) + 1))) := by
    ext s
    constructor
    · rintro ⟨x, hxC, rfl, hxy⟩
      obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 / ((k : ℝ) + 1) < r - dist x y :=
        exists_nat_one_div_lt (by linarith)
      exact mem_iUnion.mpr ⟨k, mem_image_of_mem L
        ⟨hxC, by rw [mem_closedBall]; linarith⟩⟩
    · intro hs
      obtain ⟨k, x, hx, rfl⟩ := mem_iUnion.mp hs
      refine ⟨x, hx.1, rfl, ?_⟩
      have hk2 : dist x y ≤ r - 1 / ((k : ℝ) + 1) := hx.2
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hset]
  refine MeasurableSet.iUnion fun k => ?_
  exact (((Metric.isCompact_iff_isClosed_bounded).mpr
    ⟨hC.inter Metric.isClosed_closedBall, hB.subset Set.inter_subset_left⟩).image hL).isClosed.measurableSet

/-- Elementary geometry of a convex set containing `0` in its interior. -/
theorem interior_smul_geometry_aux {d : ℕ} {K : Set (Fin d → ℝ)} (hKc : Convex ℝ K)
    (h0 : (0 : Fin d → ℝ) ∈ interior K) :
    (∀ t : ℝ, 0 ≤ t → t < 1 → ∀ x ∈ K, t • x ∈ interior K) ∧
    (∀ x : Fin d → ℝ, x ∈ interior K → ∃ n : ℕ, ∃ y ∈ K,
      x = (1 - (1 : ℝ) / ((n : ℝ) + 1)) • y) ∧
    (∀ t : ℝ, 0 < t → t ≤ 1 → ∀ a ∈ K, ∀ b ∈ interior K,
      (1 - t) • a + t • b ∈ interior K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht0 ht1 x hx
    have h := hKc.combo_interior_self_mem_interior h0 hx (a := 1 - t) (b := t)
      (by linarith) ht0 (by ring)
    simpa using h
  · intro x hx
    obtain ⟨ε, hε, hεK⟩ : ∃ ε : ℝ, 0 < ε ∧ ball x ε ⊆ K := by
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
      exact ⟨ε, hε, hball.trans interior_subset⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 / ((k : ℝ) + 1) < ε / (‖x‖ + 1) :=
      exists_nat_one_div_lt (by positivity : (0 : ℝ) < ε / (‖x‖ + 1))
    refine ⟨k + 1, (1 + 1 / ((k : ℝ) + 1)) • x, ?_, ?_⟩
    · apply hεK
      rw [mem_ball]
      have hnorm : dist ((1 + 1 / ((k : ℝ) + 1)) • x) x = ‖x‖ / ((k : ℝ) + 1) := by
        have hsub : (1 + 1 / ((k : ℝ) + 1)) • x - (1 : ℝ) • x = (1 / ((k : ℝ) + 1)) • x := by
          rw [← sub_smul]
          congr 1
          ring
        rw [dist_eq_norm, show (1 + 1 / ((k : ℝ) + 1)) • x - x =
          (1 + 1 / ((k : ℝ) + 1)) • x - (1 : ℝ) • x from by rw [one_smul], hsub,
          norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        ring
      rw [hnorm]
      have h1 : ‖x‖ / ((k : ℝ) + 1) < ε := by
        rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
        · rw [← hx0]; simpa using hε
        · calc ‖x‖ / ((k : ℝ) + 1) = ‖x‖ * (1 / ((k : ℝ) + 1)) := by rw [mul_one_div]
            _ < ‖x‖ * (ε / (‖x‖ + 1)) := by
                rw [mul_lt_mul_iff_of_pos_left hx0]
                simpa [one_div] using hk
            _ < ε := by
                rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
                nlinarith
      exact h1
    · rw [smul_smul]
      have hscal : (1 - (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1)) * (1 + 1 / ((k : ℝ) + 1)) = 1 := by
        push_cast
        field_simp
        ring
      rw [hscal, one_smul]
  · intro t ht0 ht1 a ha b hb
    have h := hKc.combo_self_interior_mem_interior ha hb (a := 1 - t) (b := t)
      (by linarith) ht0 (by ring)
    simpa using h

/-- If `K` is convex, symmetric about `0` and has nonempty interior, then `0` is interior. -/
theorem zero_mem_interior_of_symm {d : ℕ} {K : Set (Fin d → ℝ)} (hKc : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hKi : (interior K).Nonempty) :
    (0 : Fin d → ℝ) ∈ interior K := by
  obtain ⟨u, hu⟩ := hKi
  have h := hKc.combo_interior_self_mem_interior hu (hsym u (interior_subset hu))
    (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hzero : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • (-u) = 0 := by
    rw [← smul_add, add_neg_cancel, smul_zero]
  rwa [hzero] at h

/-- Choose measurably a point with a prescribed suffix. -/
theorem exists_section_choice_aux {d : ℕ} (i : Fin d) {K : Set (Fin d → ℝ)} (hKc : Convex ℝ K)
    (hKcl : IsClosed K) (hKbd : Bornology.IsBounded K) (h0 : (0 : Fin d → ℝ) ∈ interior K) :
    ∃ g : (Fin d → ℝ) → (Fin d → ℝ), Measurable g ∧
      (∀ s ∈ suf i '' K, g s ∈ K ∧ suf i (g s) = s) ∧
      (∀ s ∈ suf i '' interior K, g s ∈ interior K) ∧
      (∀ s ∈ Set.range (suf i), suf i (g s) = s) := by
  classical
  have hgeom1 : ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ x ∈ K, t • x ∈ interior K :=
    (interior_smul_geometry_aux hKc h0).1
  have hgeom2 : ∀ x : Fin d → ℝ, x ∈ interior K → ∃ n : ℕ, ∃ y ∈ K,
      x = (1 - (1 : ℝ) / ((n : ℝ) + 1)) • y :=
    (interior_smul_geometry_aux hKc h0).2.1
  have hKcpt : IsCompact K := (Metric.isCompact_iff_isClosed_bounded).mpr ⟨hKcl, hKbd⟩
  have hdil_cl : ∀ n : ℕ, IsClosed ((1 - (1 : ℝ) / ((n : ℝ) + 1)) • K) := by
    intro n
    by_cases hc : (1 - (1 : ℝ) / ((n : ℝ) + 1)) = 0
    · rw [hc, zero_smul_set ⟨0, interior_subset h0⟩]
      exact isClosed_singleton
    · exact hKcl.smul_of_ne_zero hc
  have hdil_cpt : ∀ n : ℕ, IsCompact ((1 - (1 : ℝ) / ((n : ℝ) + 1)) • K) :=
    fun n => hKcpt.smul _
  have hdil_bd : ∀ n : ℕ, Bornology.IsBounded ((1 - (1 : ℝ) / ((n : ℝ) + 1)) • K) :=
    fun n => (hdil_cpt n).isBounded
  have hDsub : suf i '' interior K ⊆ suf i '' K := image_mono interior_subset
  have hEmeas : MeasurableSet (suf i '' K) :=
    (hKcpt.image (suf_continuous i)).isClosed.measurableSet
  have hDmeas : MeasurableSet (suf i '' interior K) := by
    have hker : suf i '' interior K = ⋃ n : ℕ, suf i '' ((1 - (1 : ℝ) / ((n : ℝ) + 1)) • K) := by
      have hinter : interior K = ⋃ n : ℕ, (1 - (1 : ℝ) / ((n : ℝ) + 1)) • K := by
        ext x
        constructor
        · intro hx
          obtain ⟨n, y, hy, hxy⟩ := hgeom2 x hx
          exact mem_iUnion.mpr ⟨n, by rw [Set.mem_smul_set]; exact ⟨y, hy, hxy.symm⟩⟩
        · intro hx
          obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
          obtain ⟨y, hy, hyx⟩ := hxn
          rw [← hyx]
          refine hgeom1 _ ?_ ?_ y hy
          · rw [sub_nonneg, div_le_one (by positivity)]
            have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
            linarith
          · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            linarith
      rw [hinter, Set.image_iUnion]
    rw [hker]
    exact MeasurableSet.iUnion fun n => (hdil_cpt n).image (suf_continuous i) |>.isClosed.measurableSet
  -- level function
  have hlev_exists : ∀ s : Fin d → ℝ, ∃ n : ℕ,
      (s ∈ suf i '' ((1 - (1 : ℝ) / ((n : ℝ) + 1)) • K)) ∨ (s ∉ suf i '' interior K) := by
    intro s
    by_cases hs : s ∈ suf i '' interior K
    · obtain ⟨x, hx, hxs⟩ := hs
      obtain ⟨n, y, hy, hxy⟩ := hgeom2 x hx
      refine ⟨n, Or.inl ⟨(1 - (1 : ℝ) / ((n : ℝ) + 1)) • y, ?_, ?_⟩⟩
      · exact smul_mem_smul_set hy
      · rw [← hxy]; exact hxs
    · exact ⟨0, Or.inr hs⟩
  have hlev_meas : ∀ n : ℕ, MeasurableSet {s : Fin d → ℝ |
      (s ∈ suf i '' ((1 - (1 : ℝ) / ((n : ℝ) + 1)) • K)) ∨ (s ∉ suf i '' interior K)} := by
    intro n
    have h2 : MeasurableSet (suf i '' ((1 - (1 : ℝ) / ((n : ℝ) + 1)) • K)) :=
      (hdil_cpt n).image (suf_continuous i) |>.isClosed.measurableSet
    exact h2.union hDmeas.compl
  let lvl : (Fin d → ℝ) → ℕ := fun s => Nat.find (hlev_exists s)
  have hlvl_meas : Measurable lvl := measurable_find hlev_exists hlev_meas
  have hlvl_D : ∀ s ∈ suf i '' interior K,
      s ∈ suf i '' ((1 - (1 : ℝ) / ((lvl s : ℝ) + 1)) • K) := by
    intro s hs
    rcases Nat.find_spec (hlev_exists s) with h | h
    · exact h
    · exact absurd hs h
  -- the multifunction
  let Φ : (Fin d → ℝ) → Set (Fin d → ℝ) := fun s =>
    if s ∈ suf i '' interior K then {x | x ∈ (1 - (1 : ℝ) / ((lvl s : ℝ) + 1)) • K ∧ suf i x = s}
    else if s ∈ suf i '' K then {x | x ∈ K ∧ suf i x = s}
    else {s}
  have hΦD : ∀ s, s ∈ suf i '' interior K →
      Φ s = {x | x ∈ (1 - (1 : ℝ) / ((lvl s : ℝ) + 1)) • K ∧ suf i x = s} := by
    intro s hs
    dsimp only [Φ]
    rw [if_pos hs]
  have hΦE : ∀ s, s ∉ suf i '' interior K → s ∈ suf i '' K →
      Φ s = {x | x ∈ K ∧ suf i x = s} := by
    intro s hs hsE
    dsimp only [Φ]
    rw [if_neg hs, if_pos hsE]
  have hΦN : ∀ s, s ∉ suf i '' K → Φ s = {s} := by
    intro s hs
    have hsD : s ∉ suf i '' interior K := fun h => hs (hDsub h)
    dsimp only [Φ]
    rw [if_neg hsD, if_neg hs]
  have hΦ_ne : ∀ s, (Φ s).Nonempty := by
    intro s
    by_cases hD : s ∈ suf i '' interior K
    · rw [hΦD s hD]
      obtain ⟨y, hy, hys⟩ := hlvl_D s hD
      exact ⟨y, hy, hys⟩
    · by_cases hE : s ∈ suf i '' K
      · rw [hΦE s hD hE]
        obtain ⟨x, hx, hxs⟩ := hE
        exact ⟨x, hx, hxs⟩
      · rw [hΦN s hE]
        exact ⟨s, rfl⟩
  have hΦ_cl : ∀ s, IsClosed (Φ s) := by
    intro s
    by_cases hD : s ∈ suf i '' interior K
    · rw [hΦD s hD]
      exact (hdil_cl (lvl s)).inter (isClosed_eq (suf_continuous i) continuous_const)
    · by_cases hE : s ∈ suf i '' K
      · rw [hΦE s hD hE]
        exact hKcl.inter (isClosed_eq (suf_continuous i) continuous_const)
      · rw [hΦN s hE]
        exact isClosed_singleton
  have hΦ_meas : ∀ y : Fin d → ℝ, ∀ r : ℝ, 0 < r →
      MeasurableSet {s : Fin d → ℝ | ∃ x ∈ Φ s, dist x y < r} := by
    intro y r hr
    have h₁ : MeasurableSet {s : Fin d → ℝ | s ∈ suf i '' interior K ∧
        ∃ x ∈ (1 - (1 : ℝ) / ((lvl s : ℝ) + 1)) • K, suf i x = s ∧ dist x y < r} := by
      rw [show {s : Fin d → ℝ | s ∈ suf i '' interior K ∧
          ∃ x ∈ (1 - (1 : ℝ) / ((lvl s : ℝ) + 1)) • K, suf i x = s ∧ dist x y < r}
          = (suf i '' interior K) ∩ (⋃ n : ℕ, ({s : Fin d → ℝ | lvl s = n} ∩
              {s : Fin d → ℝ | ∃ x ∈ (1 - (1 : ℝ) / ((n : ℝ) + 1)) • K,
                suf i x = s ∧ dist x y < r})) from by
        ext s
        rw [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion]
        constructor
        · rintro ⟨hsD, x, hx, hxs, hxy⟩
          exact ⟨hsD, lvl s, rfl, x, hx, hxs, hxy⟩
        · rintro ⟨hsD, n, hn, x, hx, hxs, hxy⟩
          rw [← hn] at hx
          exact ⟨hsD, x, hx, hxs, hxy⟩]
      exact hDmeas.inter (MeasurableSet.iUnion fun n =>
        (hlvl_meas (measurableSet_singleton n)).inter
          (section_set_measurable_aux (suf i) (suf_continuous i) (hdil_cl n) (hdil_bd n) y hr))
    have h₂ : MeasurableSet {s : Fin d → ℝ | s ∉ suf i '' interior K ∧
        ∃ x ∈ K, suf i x = s ∧ dist x y < r} :=
      hDmeas.compl.inter (section_set_measurable_aux (suf i) (suf_continuous i) hKcl hKbd y hr)
    have h₃ : MeasurableSet {s : Fin d → ℝ | s ∉ suf i '' K ∧ dist s y < r} :=
      hEmeas.compl.inter
        ((isOpen_lt (continuous_id.dist continuous_const) continuous_const).measurableSet)
    have hmain : {s : Fin d → ℝ | ∃ x ∈ Φ s, dist x y < r} =
        {s : Fin d → ℝ | s ∈ suf i '' interior K ∧
            ∃ x ∈ (1 - (1 : ℝ) / ((lvl s : ℝ) + 1)) • K, suf i x = s ∧ dist x y < r} ∪
        ({s : Fin d → ℝ | s ∉ suf i '' interior K ∧
            ∃ x ∈ K, suf i x = s ∧ dist x y < r} ∪
         {s : Fin d → ℝ | s ∉ suf i '' K ∧ dist s y < r}) := by
      ext s
      rw [Set.mem_setOf_eq]
      by_cases hD : s ∈ suf i '' interior K
      · rw [hΦD s hD]
        constructor
        · rintro ⟨x, hx, hxy⟩
          exact Or.inl ⟨hD, x, hx.1, hx.2, hxy⟩
        · rintro (⟨-, x, hx, hxs, hxy⟩ | ⟨h, -⟩ | ⟨h, -⟩)
          · exact ⟨x, ⟨hx, hxs⟩, hxy⟩
          · exact absurd hD h
          · exact absurd (hDsub hD) h
      · by_cases hE : s ∈ suf i '' K
        · rw [hΦE s hD hE]
          constructor
          · rintro ⟨x, hx, hxy⟩
            exact Or.inr (Or.inl ⟨hD, x, hx.1, hx.2, hxy⟩)
          · rintro (⟨h, -⟩ | ⟨-, x, hx, hxs, hxy⟩ | ⟨h, -⟩)
            · exact absurd h hD
            · exact ⟨x, ⟨hx, hxs⟩, hxy⟩
            · exact (h hE).elim
        · rw [hΦN s hE]
          constructor
          · rintro ⟨x, hx, hxy⟩
            rw [Set.mem_singleton_iff] at hx
            subst hx
            exact Or.inr (Or.inr ⟨hE, hxy⟩)
          · rintro (⟨h, -⟩ | ⟨-, x, hx, hxs, hxy⟩ | ⟨-, h⟩)
            · exact absurd h hD
            · exact (hE ⟨x, hx, hxs⟩).elim
            · exact ⟨s, rfl, h⟩
    rw [hmain]
    exact h₁.union (h₂.union h₃)
  obtain ⟨g, hgmeas, hgmem⟩ := exists_measurable_selection_aux Φ hΦ_ne hΦ_cl hΦ_meas
  have hgeD : ∀ s, s ∈ suf i '' interior K →
      g s ∈ {x | x ∈ (1 - (1 : ℝ) / ((lvl s : ℝ) + 1)) • K ∧ suf i x = s} := by
    intro s hs
    rw [← hΦD s hs]
    exact hgmem s
  have hgeE : ∀ s, s ∉ suf i '' interior K → s ∈ suf i '' K →
      g s ∈ {x | x ∈ K ∧ suf i x = s} := by
    intro s hs hsE
    rw [← hΦE s hs hsE]
    exact hgmem s
  have hgeN : ∀ s, s ∉ suf i '' K → g s ∈ ({s} : Set (Fin d → ℝ)) := by
    intro s hs
    rw [← hΦN s hs]
    exact hgmem s
  have ht0 : ∀ s : Fin d → ℝ, 0 ≤ 1 - (1 : ℝ) / ((lvl s : ℝ) + 1) := by
    intro s
    rw [sub_nonneg, div_le_one (by positivity)]
    have hn : (0 : ℝ) ≤ (lvl s : ℝ) := Nat.cast_nonneg _
    linarith
  have ht1 : ∀ s : Fin d → ℝ, 1 - (1 : ℝ) / ((lvl s : ℝ) + 1) < 1 := by
    intro s
    have hpos : (0 : ℝ) < 1 / ((lvl s : ℝ) + 1) := by positivity
    linarith
  refine ⟨g, hgmeas, ?_, ?_, ?_⟩
  · intro s hs
    by_cases hD : s ∈ suf i '' interior K
    · have hg := hgeD s hD
      obtain ⟨z, hz, hzg⟩ := hg.1
      refine ⟨?_, hg.2⟩
      rw [← hzg]
      exact hKc.smul_mem_of_zero_mem (interior_subset h0) hz ⟨ht0 s, le_of_lt (ht1 s)⟩
    · by_cases hE : s ∈ suf i '' K
      · exact (hgeE s hD hE)
      · exact absurd hs hE
  · intro s hs
    have hg := hgeD s hs
    obtain ⟨z, hz, hzg⟩ := hg.1
    rw [← hzg]
    exact hgeom1 _ (ht0 s) (ht1 s) z hz
  · intro s hs
    by_cases hD : s ∈ suf i '' interior K
    · exact (hgeD s hD).2
    · by_cases hE : s ∈ suf i '' K
      · exact (hgeE s hD hE).2
      · have hg := hgeN s hE
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact mem_range_suf hs
/-- **Section maps.** -/
theorem section_maps {d : ℕ} (K : Set (Fin d → ℝ)) (hKc : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hKcl : IsClosed K) (hKbd : Bornology.IsBounded K)
    (hKi : (interior K).Nonempty) :
    ∃ c : Fin d → (Fin d → ℝ) → (Fin d → ℝ),
      (∀ i, Measurable (c i)) ∧
      (∀ i x, x ∈ K → c i x ∈ K) ∧
      (∀ i x, x ∈ interior K → c i x ∈ interior K) ∧
      (∀ i x m, i ≤ m → c i x m = x m) ∧
      (∀ i x y, (∀ m, i ≤ m → x m = y m) → c i x = c i y) := by
  classical
  have h0 : (0 : Fin d → ℝ) ∈ interior K := zero_mem_interior_of_symm hKc hsym hKi
  have hchoice : ∀ i : Fin d, ∃ g : (Fin d → ℝ) → (Fin d → ℝ), Measurable g ∧
      (∀ s ∈ suf i '' K, g s ∈ K ∧ suf i (g s) = s) ∧
      (∀ s ∈ suf i '' interior K, g s ∈ interior K) ∧
      (∀ s ∈ Set.range (suf i), suf i (g s) = s) :=
    fun i => exists_section_choice_aux i hKc hKcl hKbd h0
  choose g hgmeas hgK hgD hgsuf using hchoice
  refine ⟨fun i x => g i (suf i x), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hgmeas i).comp (suf_measurable i)
  · intro i x hx
    exact (hgK i (suf i x) ⟨x, hx, rfl⟩).1
  · intro i x hx
    exact hgD i (suf i x) ⟨x, hx, rfl⟩
  · intro i x m hm
    have h1 : suf i (g i (suf i x)) = suf i x := hgsuf i (suf i x) ⟨x, rfl⟩
    calc (fun i x => g i (suf i x)) i x m = suf i (g i (suf i x)) m :=
          (suf_apply_of_le (x := g i (suf i x)) hm).symm
      _ = (suf i x) m := by rw [h1]
      _ = x m := suf_apply_of_le (x := x) hm
  · intro i x y hxy
    have hxy' : suf i x = suf i y := suf_eq_iff.mpr hxy
    simp only
    rw [hxy']

end Work.BW.Minkowski2
