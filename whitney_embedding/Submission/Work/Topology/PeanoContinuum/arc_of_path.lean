import Mathlib

/-!
# Extracting an arc from a path in a compact metric space

Given a continuous map `f : ℝ → X` into a compact metric space with `f 0 ≠ f 1`, there is a
continuous `γ : ℝ → X` which is injective on `[0,1]` and joins `f 0` to `f 1`.

This follows the classical argument of Nadler, *Continuum Theory*, 8.23 (see also T. Banakh's
Borel-measurable Hahn–Mazurkiewicz theorem).
-/

namespace Work.Topology.PeanoContinuum

open Set Metric Filter

variable {X : Type*}

/-- `Admissible f K`: `K ⊆ [0,1]` is nonempty and compact, contains `0` and `1`, and every pair of
*consecutive* points of `K` has the same `f`-value. -/
def Admissible [MetricSpace X] (f : ℝ → X) (K : Set ℝ) : Prop :=
  IsCompact K ∧ K ⊆ Set.Icc (0 : ℝ) 1 ∧ (0 : ℝ) ∈ K ∧ (1 : ℝ) ∈ K ∧
    ∀ s ∈ K, ∀ t ∈ K, s < t → (∀ u ∈ K, ¬ (s < u ∧ u < t)) → f s = f t

lemma admissible_Icc [MetricSpace X] (f : ℝ → X) : Admissible f (Set.Icc (0:ℝ) 1) := by
  refine ⟨isCompact_Icc, subset_rfl, ⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩, ?_⟩
  intro s hs t ht hst h
  exact absurd ⟨show s < (s + t) / 2 by linarith, show (s + t) / 2 < t by linarith⟩
    (h ((s + t) / 2) ⟨by linarith [hs.1], by linarith [ht.2]⟩)

/-- The intersection of a nonempty chain of admissible sets is admissible. -/
lemma admissible_sInter [MetricSpace X] (f : ℝ → X) (hf : Continuous f)
    {c : Set (Set ℝ)} (hcne : c.Nonempty) (hcc : ∀ A ∈ c, ∀ B ∈ c, A ⊆ B ∨ B ⊆ A)
    (hc : ∀ A ∈ c, Admissible f A) : Admissible f (⋂₀ c) := by
  classical
  have hclosed : ∀ A ∈ c, IsClosed A := fun A hA => (hc A hA).1.isClosed
  have hKc : IsCompact (⋂₀ c) :=
    ((hc hcne.choose hcne.choose_spec).1).of_isClosed_subset (isClosed_sInter hclosed)
      (Set.sInter_subset_of_mem hcne.choose_spec)
  refine ⟨hKc, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hc hcne.choose hcne.choose_spec).2.1 (Set.sInter_subset_of_mem hcne.choose_spec hx)
  · intro A hA; exact (hc A hA).2.2.1
  · intro A hA; exact (hc A hA).2.2.2.1
  · -- The `Γ`-condition passes to chain intersections (Banakh's δ-argument): if `(s,t)` is a
    -- consecutive pair of the intersection with `f s ≠ f t`, there is `δ > 0` with `s + δ < t - δ`
    -- such that the images of the `δ`-neighbourhoods of `s` and of `t` are disjoint; every member
    -- of the chain then meets `[s+δ, t-δ]`, and by the finite intersection property so does the
    -- intersection, contradicting that `(s,t)` is a gap.
    intro s hs t ht hst hconsec
    by_contra hne
    have h2pos : 0 < dist (f s) (f t) / 4 := by
      have := dist_pos.mpr hne; linarith
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuous_iff.mp hf s (dist (f s) (f t) / 4) h2pos
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.continuous_iff.mp hf t (dist (f s) (f t) / 4) h2pos
    obtain ⟨δ, hδpos, hδ₁lt, hδ₂lt, hδ3⟩ :
        ∃ δ : ℝ, 0 < δ ∧ δ < δ₁ ∧ δ < δ₂ ∧ 3 * δ < t - s :=
      ⟨min δ₁ (min δ₂ ((t - s) / 3)) / 2,
        by have h1 : 0 < min δ₁ (min δ₂ ((t - s) / 3)) :=
              lt_min hδ₁pos (lt_min hδ₂pos (by linarith))
           linarith,
        by have h1 : min δ₁ (min δ₂ ((t - s) / 3)) ≤ δ₁ := min_le_left _ _
           linarith,
        by have h1 : min δ₁ (min δ₂ ((t - s) / 3)) ≤ min δ₂ ((t - s) / 3) := min_le_right _ _
           have h2 : min δ₂ ((t - s) / 3) ≤ δ₂ := min_le_left _ _
           linarith,
        by have h1 : min δ₁ (min δ₂ ((t - s) / 3)) ≤ min δ₂ ((t - s) / 3) := min_le_right _ _
           have h2 : min δ₂ ((t - s) / 3) ≤ (t - s) / 3 := min_le_right _ _
           linarith⟩
    have hsδ : s + δ < t - δ := by linarith
    have hAmeet : ∀ A ∈ c, (A ∩ Set.Icc (s + δ) (t - δ)).Nonempty := by
      intro A hA
      have hs01 : 0 ≤ s ∧ s ≤ 1 := (hc A hA).2.1 (hs A hA)
      have ht01 : 0 ≤ t ∧ t ≤ 1 := (hc A hA).2.1 (ht A hA)
      by_contra hempty
      have h0 : (A ∩ Set.Icc (0:ℝ) (s + δ)).Nonempty :=
        ⟨0, (hc A hA).2.2.1, le_refl 0, by linarith [hs01.1, hδpos]⟩
      obtain ⟨u, hu : IsGreatest (A ∩ Set.Icc (0:ℝ) (s + δ)) u⟩ :=
        ((hc A hA).1.inter isCompact_Icc).exists_isGreatest h0
      have h1 : (A ∩ Set.Icc (t - δ) 1).Nonempty :=
        ⟨1, (hc A hA).2.2.2.1, by linarith [ht01.2, hδpos], le_refl 1⟩
      obtain ⟨v, hv : IsLeast (A ∩ Set.Icc (t - δ) 1) v⟩ :=
        ((hc A hA).1.inter isCompact_Icc).exists_isLeast h1
      have huA : u ∈ A := hu.1.1
      have hvA : v ∈ A := hv.1.1
      have hs_le_u : s ≤ u := hu.2 ⟨hs A hA, hs01.1, by linarith [hs01.2, hδpos]⟩
      have hv_le_t : v ≤ t := hv.2 ⟨ht A hA, by linarith [ht01.1, hδpos], ht01.2⟩
      have huv : u < v := by linarith [hu.1.2.2, hv.1.2.1, hsδ]
      have hgap : ∀ w ∈ A, ¬ (u < w ∧ w < v) := by
        intro w hw hlt
        have hw01 : 0 ≤ w ∧ w ≤ 1 := (hc A hA).2.1 hw
        by_cases hcase : w ≤ s + δ
        · have : w ≤ u := hu.2 ⟨hw, hw01.1, hcase⟩
          linarith [hlt.1]
        · have h2 : t - δ ≤ w := by
            by_contra hcon
            push Not at hcon
            exact hempty ⟨w, hw, le_of_lt (not_le.mp hcase), le_of_lt hcon⟩
          have : v ≤ w := hv.2 ⟨hw, h2, hw01.2⟩
          linarith [hlt.2]
      have hfuv : f u = f v := (hc A hA).2.2.2.2 u huA v hvA huv hgap
      have hu' : dist (f u) (f s) < dist (f s) (f t) / 4 :=
        hδ₁ u (by rw [Real.dist_eq]; exact abs_lt.mpr ⟨by linarith [hs_le_u, hδ₁pos],
          by linarith [hu.1.2.2, hδ₁lt]⟩)
      have hv' : dist (f v) (f t) < dist (f s) (f t) / 4 :=
        hδ₂ v (by rw [Real.dist_eq]; exact abs_lt.mpr ⟨by linarith [hv.1.2.1, hδ₂pos],
          by linarith [hv_le_t, hδ₂lt]⟩)
      have ha : dist (f s) (f v) < dist (f s) (f t) / 4 := by
        rw [dist_comm (f s) (f v)]; simpa [hfuv] using hu'
      have htri : dist (f s) (f t) ≤ dist (f s) (f v) + dist (f v) (f t) := dist_triangle _ _ _
      linarith
    have hdir : ∀ A ∈ c, ∀ B ∈ c, ∃ C ∈ c, C ⊆ A ∩ B := by
      intro A hA B hB
      rcases hcc A hA B hB with h | h
      · exact ⟨A, hA, Set.subset_inter subset_rfl h⟩
      · exact ⟨B, hB, Set.subset_inter h subset_rfl⟩
    haveI : Nonempty {A : Set ℝ // A ∈ c} := ⟨⟨hcne.choose, hcne.choose_spec⟩⟩
    obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun (A : {A : Set ℝ // A ∈ c}) => (A : Set ℝ) ∩ Set.Icc (s + δ) (t - δ))
      (by
        rintro ⟨A, hA⟩ ⟨B, hB⟩
        obtain ⟨C, hC, hCsub⟩ := hdir A hA B hB
        exact ⟨⟨C, hC⟩, fun x hx => ⟨(hCsub hx.1).1, hx.2⟩,
          fun x hx => ⟨(hCsub hx.1).2, hx.2⟩⟩)
      (by rintro ⟨A, hA⟩; exact hAmeet A hA)
      (by rintro ⟨A, hA⟩; exact (hc A hA).1.inter isCompact_Icc)
      (by rintro ⟨A, hA⟩; exact (hc A hA).1.isClosed.inter isClosed_Icc)
    have hzK : z ∈ ⋂₀ c := fun A hA => (Set.mem_iInter.mp hz ⟨A, hA⟩).1
    have hzI : z ∈ Set.Icc (s + δ) (t - δ) :=
      (Set.mem_iInter.mp hz ⟨hcne.choose, hcne.choose_spec⟩).2
    exact hconsec z hzK ⟨by linarith [hzI.1], by linarith [hzI.2]⟩

/-- **Minimal admissible set.** -/
theorem exists_minimal_admissible [MetricSpace X] (f : ℝ → X) (hf : Continuous f) :
    ∃ K : Set ℝ, Admissible f K ∧ ∀ K' : Set ℝ, Admissible f K' → K' ⊆ K → K = K' := by
  classical
  have hchain : ∀ c ⊆ {K : Set ℝ | Admissible f K}, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ lb ∈ {K : Set ℝ | Admissible f K}, ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hchain hcne
    refine ⟨⋂₀ c, admissible_sInter f hf hcne ?_ (fun A hA => hcS hA), ?_⟩
    · intro A hA B hB
      by_cases hAB : A = B
      · exact Or.inl (le_of_eq hAB)
      · exact hchain hA hB hAB
    · intro s hs; exact Set.sInter_subset_of_mem hs
  obtain ⟨K, hKsub, hmin⟩ := zorn_superset_nonempty {K : Set ℝ | Admissible f K} hchain
    (Set.Icc 0 1) (admissible_Icc f)
  exact ⟨K, hmin.1, fun K' hK' hK'sub => (subset_antisymm hK'sub (hmin.2 hK' hK'sub)).symm⟩


/-- **Loops are gaps.**  In a minimal admissible set `K`, if `a < b` are points of `K` with
`f a = f b`, then `K` has no point strictly between them: deleting the interior of `[a,b]` again
gives an admissible set, so minimality forces it to be all of `K`. -/
lemma loop_gap [MetricSpace X] (f : ℝ → X) {K : Set ℝ} (hK : Admissible f K)
    (hmin : ∀ K' : Set ℝ, Admissible f K' → K' ⊆ K → K = K')
    {a b : ℝ} (ha : a ∈ K) (hb : b ∈ K) (hab : a < b) (hf : f a = f b) :
    ∀ u ∈ K, ¬ (a < u ∧ u < b) := by
  intro u hu hu'
  have haK : a ∈ K \ Set.Ioo a b := ⟨ha, fun h => absurd h.1 (lt_irrefl a)⟩
  have hbK : b ∈ K \ Set.Ioo a b := ⟨hb, fun h => absurd h.2 (lt_irrefl b)⟩
  have hK₀ : Admissible f (K \ Set.Ioo a b) := by
    refine ⟨hK.1.diff isOpen_Ioo, fun x hx => hK.2.1 hx.1, ?_, ?_, ?_⟩
    · exact ⟨hK.2.2.1, fun h => absurd h.1 (not_lt.mpr (hK.2.1 ha).1)⟩
    · exact ⟨hK.2.2.2.1, fun h => absurd h.2 (not_lt.mpr (hK.2.1 hb).2)⟩
    · intro s hs t ht hst hgap'
      by_cases hpair : s = a ∧ t = b
      · rw [hpair.1, hpair.2]; exact hf
      · refine hK.2.2.2.2 s hs.1 t ht.1 hst ?_
        intro w hw hlt
        have hw0 : w ∈ Set.Ioo a b := by
          by_contra hcon
          exact hgap' w ⟨hw, hcon⟩ hlt
        have hs' : s ≤ a ∨ b ≤ s := by
          by_contra hcon
          push Not at hcon
          exact hs.2 ⟨hcon.1, hcon.2⟩
        rcases hs' with hs'a | hs'b
        · rcases lt_or_eq_of_le hs'a with hsa | hsa
          · exact hgap' a haK ⟨hsa, by linarith [hw0.1, hlt.2]⟩
          · have htb : t ≤ b := by
              by_contra hcon
              push Not at hcon
              exact hgap' b hbK ⟨show s < b from hsa ▸ hab, hcon⟩
            have hbt : b ≤ t := by
              by_contra hcon
              push Not at hcon
              exact ht.2 ⟨show a < t from hsa ▸ hst, hcon⟩
            exact hpair ⟨hsa, le_antisymm htb hbt⟩
        · exact absurd hw0.2 (not_lt.mpr (le_of_lt (lt_of_le_of_lt hs'b hlt.1)))
  have hEq : K = K \ Set.Ioo a b := hmin _ hK₀ Set.sdiff_subset
  have : u ∈ K \ Set.Ioo a b := by rw [← hEq]; exact hu
  exact this.2 ⟨hu'.1, hu'.2⟩


/-- The "collapse" map attached to an admissible set `K`: it sends `u` to `f` of the largest point
of `K ∩ [0,u]` (clamped at `0`).  It is `f` on `K`, constant on each complementary interval, and
continuous (using that gaps have equal `f`-values). -/
noncomputable def collapse [MetricSpace X] (f : ℝ → X) (K : Set ℝ) (u : ℝ) : X :=
  f (sSup (K ∩ Set.Icc (0:ℝ) (max u 0)))

lemma collapse_mem [MetricSpace X] (f : ℝ → X) {K : Set ℝ} (hK : Admissible f K) (u : ℝ) :
    collapse f K u ∈ f '' K := by
  have hne : (K ∩ Set.Icc (0:ℝ) (max u 0)).Nonempty :=
    ⟨0, hK.2.2.1, le_refl (0:ℝ), le_max_right _ _⟩
  have hc : IsCompact (K ∩ Set.Icc (0:ℝ) (max u 0)) := hK.1.inter isCompact_Icc
  exact ⟨_, (hc.sSup_mem hne).1, rfl⟩

lemma collapse_zero [MetricSpace X] (f : ℝ → X) {K : Set ℝ} (hK : Admissible f K) :
    collapse f K 0 = f 0 := by
  have h1 : K ∩ Set.Icc (0:ℝ) (max 0 0) = {0} := by
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      have hx0 : x ≤ (0:ℝ) := by simpa using hx'.2
      exact le_antisymm hx0 hx'.1
    · rintro rfl
      exact ⟨hK.2.2.1, le_refl (0:ℝ), le_max_right 0 0⟩
  rw [collapse, h1, csSup_singleton]

lemma collapse_one [MetricSpace X] (f : ℝ → X) {K : Set ℝ} (hK : Admissible f K) :
    collapse f K 1 = f 1 := by
  have h1 : K ∩ Set.Icc (0:ℝ) (max 1 0) = K := by
    refine Set.Subset.antisymm Set.inter_subset_left fun x hx => ⟨hx, ?_⟩
    exact ⟨(hK.2.1 hx).1, le_trans (hK.2.1 hx).2 (le_max_left 1 0)⟩
  rw [collapse, h1, IsGreatest.csSup_eq ⟨hK.2.2.2.1, fun y hy => (hK.2.1 hy).2⟩]


/-! ### Basic properties of the "previous point of `K`" map

Write `s u := sSup (K ∩ [0, max u 0])`.  Then `s u ∈ K`, `s u ≤ max u 0`, `s` is monotone, and
`s u = u` for `u ∈ K`, `u ≥ 0`.  These are the ingredients for the continuity of `collapse`. -/

lemma s_ne [MetricSpace X] (f : ℝ → X) {K : Set ℝ} (hK : Admissible f K) (u : ℝ) :
    (K ∩ Set.Icc (0:ℝ) (max u 0)).Nonempty :=
  ⟨0, hK.2.2.1, le_refl 0, le_max_right _ _⟩

lemma s_bdd [MetricSpace X] (f : ℝ → X) (K : Set ℝ) (u : ℝ) :
    BddAbove (K ∩ Set.Icc (0:ℝ) (max u 0)) := ⟨max u 0, fun x hx => hx.2.2⟩

lemma s_mem [MetricSpace X] (f : ℝ → X) {K : Set ℝ} (hK : Admissible f K) (u : ℝ) :
    sSup (K ∩ Set.Icc (0:ℝ) (max u 0)) ∈ K :=
  ((hK.1.inter isCompact_Icc).sSup_mem (s_ne f hK u)).1

lemma s_le [MetricSpace X] (f : ℝ → X) {K : Set ℝ} (hK : Admissible f K) (u : ℝ) :
    sSup (K ∩ Set.Icc (0:ℝ) (max u 0)) ≤ max u 0 :=
  csSup_le (s_ne f hK u) (fun x hx => hx.2.2)

lemma s_nonneg [MetricSpace X] (f : ℝ → X) {K : Set ℝ} (hK : Admissible f K) (u : ℝ) :
    0 ≤ sSup (K ∩ Set.Icc (0:ℝ) (max u 0)) := (hK.2.1 (s_mem f hK u)).1

lemma s_mono [MetricSpace X] (f : ℝ → X) {K : Set ℝ} (hK : Admissible f K) :
    Monotone (fun u => sSup (K ∩ Set.Icc (0:ℝ) (max u 0))) := by
  intro u v huv
  refine csSup_le_csSup (s_bdd f K v) (s_ne f hK u) ?_
  rintro x ⟨hx1, hx2, hx3⟩
  exact ⟨hx1, hx2, le_trans hx3 (max_le_max huv le_rfl)⟩

lemma s_of_mem [MetricSpace X] (f : ℝ → X) {K : Set ℝ} (hK : Admissible f K) {u : ℝ}
    (hu : u ∈ K) (h0 : 0 ≤ u) : sSup (K ∩ Set.Icc (0:ℝ) (max u 0)) = u := by
  refine le_antisymm ?_ ?_
  · refine csSup_le (s_ne f hK u) ?_
    rintro b ⟨hb1, hb2, hb3⟩
    rw [max_eq_left h0] at hb3
    exact hb3
  · refine le_csSup (s_bdd f K u) ?_
    exact ⟨hu, h0, by rw [max_eq_left h0]⟩


/-- The key locality statement: on the complement of `K` the "previous point of `K`" map is
locally constant, so `collapse` is locally constant there. -/
lemma s_eventuallyConst_of_notMem [MetricSpace X] (f : ℝ → X) {K : Set ℝ}
    (hK : Admissible f K) {u₀ : ℝ} (hu₀ : u₀ ∉ K) :
    ∀ᶠ u in nhds u₀, sSup (K ∩ Set.Icc (0:ℝ) (max u 0)) =
      sSup (K ∩ Set.Icc (0:ℝ) (max u₀ 0)) := by
  obtain ⟨γ, hγpos, hγ⟩ := Metric.mem_nhds_iff.mp (hK.1.isClosed.isOpen_compl.mem_nhds hu₀)
  have hγ' : ∀ x, dist x u₀ < γ → x ∉ K := fun x hx => hγ (by simpa [Metric.mem_ball] using hx)
  have key : ∀ t, u₀ - γ < t → t < u₀ + γ →
      K ∩ Set.Icc (0:ℝ) (max t 0) = K ∩ Set.Icc (0:ℝ) (max (u₀ - γ) 0) := by
    intro t ht1 ht2
    by_cases hpos : (0:ℝ) < u₀ + γ
    · ext x
      constructor
      · rintro ⟨hxK, hx1, hx2⟩
        refine ⟨hxK, hx1, ?_⟩
        by_contra hcon
        push Not at hcon
        have hxlt : x < u₀ + γ := lt_of_le_of_lt hx2 (max_lt ht2 hpos)
        have hxd : dist x u₀ < γ := by
          rw [Real.dist_eq]
          exact abs_lt.mpr ⟨by linarith [hcon, le_max_left (u₀ - γ) (0:ℝ)], by linarith [hxlt]⟩
        exact hγ' x hxd hxK
      · rintro ⟨hxK, hx1, hx2⟩
        exact ⟨hxK, hx1, le_trans hx2 (max_le_max (by linarith) le_rfl)⟩
    · have ht0 : max t 0 = 0 := max_eq_right (le_of_lt (lt_of_lt_of_le ht2 (not_lt.mp hpos)))
      have hd0 : max (u₀ - γ) 0 = 0 :=
        max_eq_right (le_of_lt (by linarith [ht1, lt_of_lt_of_le ht2 (not_lt.mp hpos)]))
      rw [ht0, hd0]
  refine Filter.mem_of_superset (Metric.ball_mem_nhds u₀ hγpos) fun u hu => ?_
  have hu' : dist u u₀ < γ := by simpa [Metric.mem_ball] using hu
  have hub : |u - u₀| < γ := by rwa [Real.dist_eq] at hu'
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hub
  have h1 : u₀ - γ < u := by linarith [hu1]
  have h2 : u < u₀ + γ := by linarith [hu2]
  have h3 : u₀ - γ < u₀ := by linarith [hγpos]
  have h4 : u₀ < u₀ + γ := by linarith [hγpos]
  exact (congrArg sSup (key u h1 h2)).trans (congrArg sSup (key u₀ h3 h4)).symm

/-- `collapse` is continuous at every point outside `K`. -/
lemma continuousAt_collapse_of_notMem [MetricSpace X] (f : ℝ → X) (hf : Continuous f)
    {K : Set ℝ} (hK : Admissible f K) {u₀ : ℝ} (hu₀ : u₀ ∉ K) :
    ContinuousAt (collapse f K) u₀ := by
  have hconst : (fun _ : ℝ => collapse f K u₀) =ᶠ[nhds u₀] collapse f K := by
    filter_upwards [s_eventuallyConst_of_notMem f hK hu₀] with u hu
    simp only [collapse]
    exact congrArg f hu.symm
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hconst] with u hu
  rw [hu]
  simpa using hε


/-- **Right-continuity of `collapse` on `K`.**  For `u ≥ u₀ ∈ K` the "previous point of `K`" lies
in `[u₀, u]` (`u₀ = s u₀ ≤ s u ≤ u`), so `s u → u₀` and continuity of `f` finishes. -/
lemma tendsto_collapse_nhdsGE [MetricSpace X] (f : ℝ → X) (hf : Continuous f) {K : Set ℝ}
    (hK : Admissible f K) {u₀ : ℝ} (hu₀ : u₀ ∈ K) :
    Tendsto (collapse f K) (nhdsWithin u₀ (Set.Ici u₀)) (nhds (collapse f K u₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hηpos, hη⟩ := Metric.continuous_iff.mp hf u₀ ε hε
  have hu0 : 0 ≤ u₀ := (hK.2.1 hu₀).1
  have hsu₀ : sSup (K ∩ Set.Icc (0:ℝ) (max u₀ 0)) = u₀ := s_of_mem f hK hu₀ hu0
  have hlt : u₀ < u₀ + η := by linarith
  have hIio : Set.Iio (u₀ + η) ∈ nhds u₀ := isOpen_Iio.mem_nhds hlt
  have hsub : Set.Ici u₀ ∩ Set.Iio (u₀ + η) ∈ nhdsWithin u₀ (Set.Ici u₀) :=
    Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds hIio)
  refine Filter.mem_of_superset hsub fun u hu => ?_
  obtain ⟨hu1, hu2⟩ := hu
  have hu2' : u < u₀ + η := hu2
  have hsu_ge : u₀ ≤ sSup (K ∩ Set.Icc (0:ℝ) (max u 0)) := by
    rw [← hsu₀]
    exact s_mono f hK hu1
  have hsu_le : sSup (K ∩ Set.Icc (0:ℝ) (max u 0)) ≤ u := by
    have h0 : max u 0 = u := max_eq_left (le_trans hu0 hu1)
    simpa only [h0] using s_le f hK u
  simp only [collapse]
  rw [hsu₀]
  refine hη _ ?_
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- **Left-continuity of `collapse` on `K`.**  Let `L := sSup (K ∩ (-∞,u₀))` be the "previous point
of `K` below `u₀`".  If `L = u₀` then `L` is a limit of points of `K` from the left and `s u → u₀`
as `u ↑ u₀`; if `L < u₀` then `L` and `u₀` are consecutive points of `K`, so `f L = f u₀` and
`f ∘ s` is constantly `f u₀` on `(L, u₀)`. -/
lemma tendsto_collapse_nhdsLT [MetricSpace X] (f : ℝ → X) (hf : Continuous f) {K : Set ℝ}
    (hK : Admissible f K) {u₀ : ℝ} (hu₀ : u₀ ∈ K) :
    Tendsto (collapse f K) (nhdsWithin u₀ (Set.Iio u₀)) (nhds (collapse f K u₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hu0 : 0 ≤ u₀ := (hK.2.1 hu₀).1
  rcases eq_or_lt_of_le hu0 with h0eq | h0pos
  · -- `u₀ = 0`: `collapse` is constantly `f 0` on `(-∞,0]`
    subst h0eq
    refine Filter.mem_of_superset self_mem_nhdsWithin fun u hu => ?_
    have hmax : max u 0 = 0 := max_eq_right (le_of_lt hu)
    have hsingle : K ∩ Set.Icc (0:ℝ) (max u 0) = {0} := by
      rw [hmax]
      ext x
      constructor
      · rintro ⟨-, hx1, hx2⟩
        exact le_antisymm (by simpa using hx2) hx1
      · rintro rfl
        exact ⟨hK.2.2.1, le_refl 0, le_refl 0⟩
    have hz : sSup (K ∩ Set.Icc (0:ℝ) (max 0 0)) = 0 := s_of_mem f hK hK.2.2.1 le_rfl
    show dist (collapse f K u) (collapse f K 0) < ε
    simp only [collapse, hsingle, hz, csSup_singleton]
    simpa using hε
  · have hne : (K ∩ Set.Iio u₀).Nonempty := ⟨0, hK.2.2.1, h0pos⟩
    have hbdd : BddAbove (K ∩ Set.Iio u₀) := ⟨u₀, fun x hx => le_of_lt hx.2⟩
    set L := sSup (K ∩ Set.Iio u₀) with hLdef
    have hL0 : 0 ≤ L := le_csSup hbdd ⟨hK.2.2.1, h0pos⟩
    have hLK : L ∈ K := by
      have hmem : L ∈ closure (K ∩ Set.Iio u₀) := csSup_mem_closure hne hbdd
      exact hK.1.isClosed.closure_subset (closure_mono Set.inter_subset_left hmem)
    have hLle : L ≤ u₀ := csSup_le hne fun x hx => le_of_lt hx.2
    by_cases hLeq : L = u₀
    · -- `u₀` is a limit of points of `K` from the left
      obtain ⟨η, hηpos, hη⟩ := Metric.continuous_iff.mp hf u₀ ε hε
      have hex : ∃ x ∈ K ∩ Set.Iio u₀, u₀ - η < x := by
        by_contra hcon
        push Not at hcon
        have hb : u₀ - η ≥ L := csSup_le hne fun x hx => hcon x hx
        linarith
      obtain ⟨x, hxK, hxgt⟩ := hex
      have hxlt : x < u₀ := hxK.2
      have hx0 : 0 ≤ x := (hK.2.1 hxK.1).1
      refine Filter.mem_of_superset
        (Filter.inter_mem (nhdsWithin_le_nhds (Ioi_mem_nhds hxlt)) self_mem_nhdsWithin)
        fun u hu => ?_
      obtain ⟨hux, hu0'⟩ := hu
      have hu0'' : u < u₀ := hu0'
      have hupos : 0 < u := lt_of_le_of_lt hx0 hux
      have hsu_ge : x ≤ sSup (K ∩ Set.Icc (0:ℝ) (max u 0)) :=
        le_csSup (s_bdd f K u) ⟨hxK.1, hx0, le_trans hux.le (le_max_left u 0)⟩
      have hsu_le : sSup (K ∩ Set.Icc (0:ℝ) (max u 0)) ≤ u := by
        simpa only [max_eq_left hupos.le] using s_le f hK u
      have hsu₀ : sSup (K ∩ Set.Icc (0:ℝ) (max u₀ 0)) = u₀ := s_of_mem f hK hu₀ hu0
      simp only [collapse]
      rw [hsu₀]
      refine hη _ ?_
      rw [Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · have hLlt : L < u₀ := lt_of_le_of_ne hLle hLeq
      have hgap : ∀ w ∈ K, ¬ (L < w ∧ w < u₀) := by
        rintro w hwK ⟨hwL, hwu⟩
        have hw : w ≤ L := le_csSup hbdd ⟨hwK, hwu⟩
        linarith
      have hfL : f L = f u₀ := hK.2.2.2.2 L hLK u₀ hu₀ hLlt hgap
      refine Filter.mem_of_superset
        (Filter.inter_mem (nhdsWithin_le_nhds (Ioi_mem_nhds hLlt)) self_mem_nhdsWithin)
        fun u hu => ?_
      obtain ⟨huL, hu0'⟩ := hu
      have hupos : 0 < u := lt_of_le_of_lt hL0 huL
      have hsu : sSup (K ∩ Set.Icc (0:ℝ) (max u 0)) = L := by
        refine le_antisymm ?_ ?_
        · refine csSup_le (s_ne f hK u) ?_
          rintro b ⟨hbK, -, hb2⟩
          have hbu : b ≤ u := by
            have h := hb2
            rwa [max_eq_left hupos.le] at h
          exact le_csSup hbdd ⟨hbK, lt_of_le_of_lt hbu hu0'⟩
        · refine le_csSup (s_bdd f K u) ⟨hLK, hL0, ?_⟩
          exact le_trans (le_of_lt huL) (le_max_left u 0)
      have hsu₀ : sSup (K ∩ Set.Icc (0:ℝ) (max u₀ 0)) = u₀ := s_of_mem f hK hu₀ hu0
      show dist (collapse f K u) (collapse f K u₀) < ε
      simp only [collapse]
      rw [hsu, hsu₀, hfL]
      simpa using hε

/-- `collapse f K` is continuous at every point of `K`. -/
lemma continuousAt_collapse_of_mem [MetricSpace X] (f : ℝ → X) (hf : Continuous f) {K : Set ℝ}
    (hK : Admissible f K) {u₀ : ℝ} (hu₀ : u₀ ∈ K) : ContinuousAt (collapse f K) u₀ := by
  have hnhds : nhds u₀ = nhdsWithin u₀ (Set.Iio u₀) ⊔ nhdsWithin u₀ (Set.Ici u₀) := by
    rw [← nhdsWithin_union, Set.Iio_union_Ici, nhdsWithin_univ]
  rw [ContinuousAt, hnhds, tendsto_sup]
  exact ⟨tendsto_collapse_nhdsLT f hf hK hu₀, tendsto_collapse_nhdsGE f hf hK hu₀⟩

/-- **`collapse f K` is continuous.** -/
lemma continuous_collapse [MetricSpace X] (f : ℝ → X) (hf : Continuous f) {K : Set ℝ}
    (hK : Admissible f K) : Continuous (collapse f K) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  by_cases h : u₀ ∈ K
  · exact continuousAt_collapse_of_mem f hf hK h
  · exact continuousAt_collapse_of_notMem f hf hK h

/-- **The fibres of `collapse` are intervals**, for a *minimal* admissible `K`. -/
lemma collapse_fibre_interval [MetricSpace X] (f : ℝ → X) (hf : Continuous f) {K : Set ℝ}
    (hK : Admissible f K) (hmin : ∀ K' : Set ℝ, Admissible f K' → K' ⊆ K → K = K')
    {s t u : ℝ} (hst : s ≤ t) (htu : t ≤ u) (hsu : collapse f K s = collapse f K u) :
    collapse f K t = collapse f K s := by
  have hat : sSup (K ∩ Set.Icc (0:ℝ) (max s 0)) ≤ sSup (K ∩ Set.Icc (0:ℝ) (max t 0)) :=
    csSup_le_csSup (s_bdd f K t) (s_ne f hK s)
      (Set.inter_subset_inter subset_rfl (Set.Icc_subset_Icc le_rfl (max_le_max hst le_rfl)))
  have htb : sSup (K ∩ Set.Icc (0:ℝ) (max t 0)) ≤ sSup (K ∩ Set.Icc (0:ℝ) (max u 0)) :=
    csSup_le_csSup (s_bdd f K u) (s_ne f hK t)
      (Set.inter_subset_inter subset_rfl (Set.Icc_subset_Icc le_rfl (max_le_max htu le_rfl)))
  have hfab : f (sSup (K ∩ Set.Icc (0:ℝ) (max s 0))) =
      f (sSup (K ∩ Set.Icc (0:ℝ) (max u 0))) := hsu
  have hmain : f (sSup (K ∩ Set.Icc (0:ℝ) (max t 0))) = f (sSup (K ∩ Set.Icc (0:ℝ) (max s 0))) := by
    rcases eq_or_lt_of_le hat with hEq | hlt
    · rw [← hEq]
    · rcases eq_or_lt_of_le htb with hEq2 | hlt2
      · rw [hEq2]; exact hfab.symm
      · exact absurd (⟨hlt, hlt2⟩ : sSup (K ∩ Set.Icc (0:ℝ) (max s 0)) <
          sSup (K ∩ Set.Icc (0:ℝ) (max t 0)) ∧
          sSup (K ∩ Set.Icc (0:ℝ) (max t 0)) < sSup (K ∩ Set.Icc (0:ℝ) (max u 0)))
          (loop_gap f hK hmin (s_mem f hK s) (s_mem f hK u) (lt_trans hlt hlt2) hfab
            (sSup (K ∩ Set.Icc (0:ℝ) (max t 0))) (s_mem f hK t))
  simp only [collapse]
  exact hmain

end Work.Topology.PeanoContinuum
