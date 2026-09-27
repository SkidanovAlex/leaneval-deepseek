import Mathlib

set_option linter.unusedVariables false

namespace Work.Whitney.PathTools

open Set Metric

/-- The plane. -/
private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private lemma one_lt_rank_plane : 1 < Module.rank ℝ Plane := by
  have hfin : Module.finrank ℝ Plane = 2 := by
    rw [finrank_euclideanSpace]
    simp
  rw [← Module.finrank_eq_rank', hfin]
  norm_num

/-- The complement of a closed ball in the plane is path connected. -/
private theorem isPathConnected_compl_closedBall_plane (a : Plane) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsPathConnected ((Metric.closedBall a ρ)ᶜ : Set Plane) := by
  have hI : IsPathConnected (Ioi ρ) := (convex_Ioi ρ).isPathConnected ⟨ρ + 1, by simp⟩
  have hS : IsPathConnected (sphere (0 : Plane) 1) :=
    isPathConnected_sphere one_lt_rank_plane 0 (by norm_num)
  have hprod : IsPathConnected ((Ioi ρ) ×ˢ (sphere (0 : Plane) 1)) := hI.prod hS
  have hcont : Continuous (fun p : ℝ × Plane => a + p.1 • p.2) :=
    continuous_const.add (continuous_fst.smul continuous_snd)
  have himg := hprod.image hcont
  have hset : (fun p : ℝ × Plane => a + p.1 • p.2) '' ((Ioi ρ) ×ˢ (sphere (0 : Plane) 1))
      = (Metric.closedBall a ρ)ᶜ := by
    ext z
    constructor
    · rintro ⟨⟨s, u⟩, ⟨hs, hu⟩, rfl⟩
      simp only [mem_Ioi] at hs
      simp only [mem_sphere, dist_eq_norm, sub_zero] at hu
      simp only [mem_compl_iff, mem_closedBall, dist_eq_norm]
      have : a + s • u - a = s • u := by abel
      rw [this, norm_smul, hu, mul_one, Real.norm_of_nonneg (le_of_lt (lt_of_le_of_lt hρ hs))]
      linarith
    · intro hz
      rw [mem_compl_iff, mem_closedBall, dist_eq_norm] at hz
      have hlt : ρ < ‖z - a‖ := lt_of_not_ge hz
      have hne : ‖z - a‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt hρ hlt)
      refine ⟨(‖z - a‖, (‖z - a‖)⁻¹ • (z - a)), ⟨hlt, ?_⟩, ?_⟩
      · simp only [mem_sphere, dist_eq_norm, sub_zero]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hne]
      · simp only
        rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
        abel
  rwa [hset] at himg

/-- The midpoint of an interval. -/
private noncomputable def mid (p : ℝ × ℝ) : ℝ := (p.1 + p.2) / 2

/-- `p = (a,b)` is a *separating* pair if `x` and `y` cannot be joined avoiding `γ '' Icc a b`. -/
private def sep (γ : ℝ → Plane) (x y : Plane) (p : ℝ × ℝ) : Prop :=
  ¬ JoinedIn ((γ '' Set.Icc p.1 p.2)ᶜ) x y

/-- One bisection step: replace `p` by its left half when that half separates, else by the
right half. -/
private noncomputable def bisectStep (γ : ℝ → Plane) (x y : Plane) (p : ℝ × ℝ) : ℝ × ℝ := by
  classical
  exact if sep γ x y (p.1, mid p) then (p.1, mid p) else (mid p, p.2)

/-- **A Jordan arc does not separate the plane** (the core bisection argument). -/
private theorem joinedIn_compl_arc
    (hT : ∀ {K L : Set Plane} (hK : IsCompact K) (hL : IsCompact L)
      {p : Plane}, K ∩ L = {p} → ∀ {x y : Plane},
      x ∉ K ∪ L → y ∉ K ∪ L → JoinedIn (Kᶜ) x y → JoinedIn (Lᶜ) x y →
      JoinedIn ((K ∪ L)ᶜ) x y)
    {γ : ℝ → Plane} (hcont : Continuous γ) (hinj : InjOn γ (Set.Icc (0:ℝ) 1))
    {x y : Plane} (hx : x ∉ γ '' Set.Icc (0:ℝ) 1) (hy : y ∉ γ '' Set.Icc (0:ℝ) 1) :
    JoinedIn ((γ '' Set.Icc (0:ℝ) 1)ᶜ) x y := by
  classical
  by_contra hsep
  have hstep : ∀ p : ℝ × ℝ, p.1 ≤ p.2 → 0 ≤ p.1 → p.2 ≤ 1 → sep γ x y p →
      (bisectStep γ x y p).1 ≤ (bisectStep γ x y p).2 ∧ sep γ x y (bisectStep γ x y p) ∧
      0 ≤ (bisectStep γ x y p).1 ∧ (bisectStep γ x y p).2 ≤ 1 ∧
      (bisectStep γ x y p).2 - (bisectStep γ x y p).1 = (p.2 - p.1) / 2 ∧
      p.1 ≤ (bisectStep γ x y p).1 ∧ (bisectStep γ x y p).2 ≤ p.2 := by
    intro p hle h0 h1 hsepp
    have hm1 : p.1 ≤ mid p := by simp only [mid]; linarith
    have hm2 : mid p ≤ p.2 := by simp only [mid]; linarith
    have hKc : IsCompact (γ '' Set.Icc p.1 (mid p)) := isCompact_Icc.image hcont
    have hLc : IsCompact (γ '' Set.Icc (mid p) p.2) := isCompact_Icc.image hcont
    have hKL : (γ '' Set.Icc p.1 (mid p)) ∩ (γ '' Set.Icc (mid p) p.2) = {γ (mid p)} := by
      refine subset_antisymm ?_ ?_
      · rintro z ⟨hz1, hz2⟩
        obtain ⟨s, hs, rfl⟩ := hz1
        obtain ⟨t, ht, hts⟩ := hz2
        have hs01 : s ∈ Set.Icc (0:ℝ) 1 :=
          ⟨le_trans h0 hs.1, le_trans hs.2 (le_trans hm2 h1)⟩
        have ht01 : t ∈ Set.Icc (0:ℝ) 1 :=
          ⟨le_trans h0 (le_trans hm1 ht.1), le_trans ht.2 h1⟩
        have hst : s = t := hinj hs01 ht01 hts.symm
        have hsm : s = mid p := le_antisymm hs.2 (hst ▸ ht.1)
        rw [hsm]
        exact mem_singleton _
      · intro z hz
        rw [mem_singleton_iff] at hz
        subst hz
        exact ⟨mem_image_of_mem _ ⟨hm1, le_rfl⟩, mem_image_of_mem _ ⟨le_rfl, hm2⟩⟩
    have hUn : (γ '' Set.Icc p.1 (mid p)) ∪ (γ '' Set.Icc (mid p) p.2)
        = γ '' Set.Icc p.1 p.2 := by
      rw [← Set.image_union, Set.Icc_union_Icc_eq_Icc hm1 hm2]
    have hsub : γ '' Set.Icc p.1 p.2 ⊆ γ '' Set.Icc (0:ℝ) 1 :=
      Set.image_mono (fun s hs => ⟨le_trans h0 hs.1, le_trans hs.2 h1⟩)
    have hxKL : x ∉ (γ '' Set.Icc p.1 (mid p)) ∪ (γ '' Set.Icc (mid p) p.2) :=
      fun h => hx (hsub (hUn ▸ h))
    have hyKL : y ∉ (γ '' Set.Icc p.1 (mid p)) ∪ (γ '' Set.Icc (mid p) p.2) :=
      fun h => hy (hsub (hUn ▸ h))
    have hnotboth : ¬ (JoinedIn ((γ '' Set.Icc p.1 (mid p))ᶜ) x y ∧
        JoinedIn ((γ '' Set.Icc (mid p) p.2)ᶜ) x y) := by
      rintro ⟨hL1, hL2⟩
      have hh := hT (K := γ '' Set.Icc p.1 (mid p)) (L := γ '' Set.Icc (mid p) p.2)
        (p := γ (mid p)) hKc hLc hKL hxKL hyKL hL1 hL2
      rw [hUn] at hh
      exact hsepp hh
    by_cases hl : sep γ x y (p.1, mid p)
    · have heq : bisectStep γ x y p = (p.1, mid p) := by
        simp only [bisectStep, if_pos hl]
      rw [heq]
      exact ⟨hm1, hl, h0, le_trans hm2 h1, by simp only [mid]; ring, le_rfl, hm2⟩
    · have hl' : ¬ ¬ JoinedIn ((γ '' Set.Icc p.1 (mid p))ᶜ) x y := hl
      have h2' : sep γ x y (mid p, p.2) := by
        rcases not_and_or.mp hnotboth with h | h
        · exact absurd h hl'
        · exact h
      have heq : bisectStep γ x y p = (mid p, p.2) := by
        simp only [bisectStep, if_neg hl]
      rw [heq]
      exact ⟨hm2, h2', le_trans h0 hm1, h1, by simp only [mid]; ring, hm1, le_rfl⟩
  let q : ℕ → ℝ × ℝ := fun n => (bisectStep γ x y)^[n] (0, 1)
  have hq0 : q 0 = (0, 1) := Function.iterate_zero_apply _ _
  have hqsucc : ∀ n, q (n + 1) = bisectStep γ x y (q n) := by
    intro n
    exact Function.iterate_succ_apply' _ n _
  have key : ∀ n, (q n).1 ≤ (q n).2 ∧ sep γ x y (q n) ∧ 0 ≤ (q n).1 ∧ (q n).2 ≤ 1 ∧
      (q n).2 - (q n).1 = (1/2 : ℝ)^n := by
    intro n
    induction n with
    | zero =>
      rw [hq0]
      refine ⟨by norm_num, ?_, by norm_num, by norm_num, by norm_num⟩
      simpa only [sep] using hsep
    | succ n ih =>
      obtain ⟨hle, hsp, h0, h1, hlen⟩ := ih
      have hs := hstep (q n) hle h0 h1 hsp
      rw [hqsucc n]
      refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
      rw [hs.2.2.2.2.1, hlen, pow_succ]
      ring
  have hmonoA : ∀ n, (q n).1 ≤ (q (n + 1)).1 := by
    intro n
    obtain ⟨hle, hsp, h0, h1, _⟩ := key n
    have hs := hstep (q n) hle h0 h1 hsp
    rw [hqsucc n]
    exact hs.2.2.2.2.2.1
  have hmonoB : ∀ n, (q (n + 1)).2 ≤ (q n).2 := by
    intro n
    obtain ⟨hle, hsp, h0, h1, _⟩ := key n
    have hs := hstep (q n) hle h0 h1 hsp
    rw [hqsucc n]
    exact hs.2.2.2.2.2.2
  have ha_mono : Monotone (fun n => (q n).1) := monotone_nat_of_le_succ hmonoA
  have hb_anti : Antitone (fun n => (q n).2) := antitone_nat_of_succ_le hmonoB
  have hbddA : BddAbove (Set.range (fun n => (q n).1)) := by
    refine ⟨1, ?_⟩
    rintro a ⟨n, rfl⟩
    exact le_trans (key n).1 (key n).2.2.2.1
  set t : ℝ := sSup (Set.range (fun n => (q n).1)) with htdef
  have hat : ∀ n, (q n).1 ≤ t := by
    intro n
    rw [htdef]
    exact le_csSup hbddA (Set.mem_range_self n)
  have htb : ∀ m, t ≤ (q m).2 := by
    intro m
    rw [htdef]
    refine csSup_le ⟨(q 0).1, Set.mem_range_self 0⟩ ?_
    rintro a ⟨n, rfl⟩
    rcases le_total n m with hnm | hmn
    · exact le_trans (ha_mono hnm) (key m).1
    · exact le_trans (key n).1 (hb_anti hmn)
  have ht_mem : ∀ m, t ∈ Set.Icc (q m).1 (q m).2 := fun m => ⟨hat m, htb m⟩
  have ht01 : t ∈ Set.Icc (0:ℝ) 1 := by
    have h := ht_mem 0
    rw [hq0] at h
    simpa using h
  have hgt : γ t ∈ γ '' Set.Icc (0:ℝ) 1 := ⟨t, ht01, rfl⟩
  have hxt : x ≠ γ t := by rintro h; exact hx (by rw [h]; exact hgt)
  have hyt : y ≠ γ t := by rintro h; exact hy (by rw [h]; exact hgt)
  have hdx : 0 < dist x (γ t) := dist_pos.mpr hxt
  have hdy : 0 < dist y (γ t) := dist_pos.mpr hyt
  set ε : ℝ := min (dist x (γ t)) (dist y (γ t)) / 2 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; have := lt_min hdx hdy; linarith
  have hxε : x ∉ Metric.closedBall (γ t) ε := by
    rw [Metric.mem_closedBall, not_le, hεdef]
    have h1 := min_le_left (dist x (γ t)) (dist y (γ t))
    have h2 := lt_min hdx hdy
    linarith
  have hyε : y ∉ Metric.closedBall (γ t) ε := by
    rw [Metric.mem_closedBall, not_le, hεdef]
    have h1 := min_le_right (dist x (γ t)) (dist y (γ t))
    have h2 := lt_min hdx hdy
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (hcont.continuousOn)) ε hεpos
  have huc : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ s' ∈ Set.Icc (0:ℝ) 1, |s - s'| < δ →
      ‖γ s - γ s'‖ < ε := by
    intro s hs s' hs' hss'
    have h1 : dist s s' < δ := by rwa [Real.dist_eq]
    have h2 := hδ s hs s' hs' h1
    rwa [dist_eq_norm] at h2
  obtain ⟨n, hnδ⟩ : ∃ n : ℕ, (1/2 : ℝ)^n < δ := by
    have hlim : Filter.Tendsto (fun n : ℕ => (1/2 : ℝ)^n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)
    exact (hlim.eventually (Iio_mem_nhds hδpos)).exists
  obtain ⟨hle_n, hsep_n, h0_n, h1_n, hlen_n⟩ := key n
  have hjoin : JoinedIn ((γ '' Set.Icc (q n).1 (q n).2)ᶜ) x y := by
    have hsub : γ '' Set.Icc (q n).1 (q n).2 ⊆ Metric.closedBall (γ t) ε := by
      rintro z ⟨s, hs, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hs01 : s ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans h0_n hs.1, le_trans hs.2 h1_n⟩
      have hst : |s - t| < δ := by
        have ht_in : t ∈ Set.Icc (q n).1 (q n).2 := ht_mem n
        have h1' : |s - t| ≤ (q n).2 - (q n).1 := by
          rw [abs_sub_le_iff]
          exact ⟨by linarith [hs.1, hs.2, ht_in.1, ht_in.2],
                 by linarith [hs.1, hs.2, ht_in.1, ht_in.2]⟩
        rw [hlen_n] at h1'
        exact lt_of_le_of_lt h1' hnδ
      exact le_of_lt (huc s hs01 t ht01 hst)
    have hcb : JoinedIn ((Metric.closedBall (γ t) ε)ᶜ) x y :=
      (isPathConnected_compl_closedBall_plane (γ t) (le_of_lt hεpos)).joinedIn x hxε y hyε
    exact hcb.mono (Set.compl_subset_compl.mpr hsub)
  exact hsep_n hjoin

/-- **A Jordan arc in the plane does not separate the plane**, reduced to the single-point
Janiszewski splitting principle `hT`: bisect the arc `γ '' [0,1]`; if the whole arc separated `x`
from `y`, then (contrapositive of `hT` applied to the two halves, which meet only in `γ (1/2)`)
one half would separate too; iterating produces nested subarcs of length `2⁻ⁿ`, all separating,
whose intersection is a single point `p = γ t`; since a single point does not separate the plane
the resulting path avoids `γ '' [aₙ, bₙ]` for all large `n`, a contradiction. -/
theorem arc_complement_interval_of_inter_singleton
    (hT : ∀ {K L : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) (hL : IsCompact L)
      {p : EuclideanSpace ℝ (Fin 2)}, K ∩ L = {p} → ∀ {x y : EuclideanSpace ℝ (Fin 2)},
      x ∉ K ∪ L → y ∉ K ∪ L → JoinedIn (Kᶜ) x y → JoinedIn (Lᶜ) x y →
      JoinedIn ((K ∪ L)ᶜ) x y)
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} (hcont : Continuous γ)
    (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1)) :
    IsPathConnected ((γ '' Set.Icc (0:ℝ) 1)ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
  classical
  have hcomp : IsCompact (γ '' Set.Icc (0:ℝ) 1) := isCompact_Icc.image hcont
  have hex : ∃ z : Plane, z ∈ (γ '' Set.Icc (0:ℝ) 1)ᶜ := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hcomp.isBounded
    obtain ⟨w, hw⟩ := exists_ne (0 : Plane)
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    refine ⟨((|R| + 1) / ‖w‖) • w, ?_⟩
    rw [Set.mem_compl_iff]
    intro hmem
    have h1 := hR hmem
    have h2 : ‖((|R| + 1) / ‖w‖) • w‖ = |R| + 1 := by
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg (by positivity) (norm_nonneg w))]
      exact div_mul_cancel₀ _ (ne_of_gt hwn)
    rw [Metric.mem_closedBall, dist_zero_right, h2] at h1
    have h3 := le_abs_self R
    linarith
  obtain ⟨z₀, hz₀⟩ := hex
  refine ⟨z₀, hz₀, ?_⟩
  intro y hy
  exact joinedIn_compl_arc hT hcont hinj hz₀ hy

end Work.Whitney.PathTools
