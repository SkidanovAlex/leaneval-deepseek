import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.Limit
import Submission.Work.Smooth.SphereJordan.LocalArc.Branch

/-!
# The two ends of an embedded arc in a compact locally-arc space

For an embedded arc `α : ℝ → X` in a compact Hausdorff space `X`:

* the closures of the tails `α '' Ici t` and `α '' Iic t` are the tails together with their limit
  points (`tail_closure_subset`, `tail_closure_subset_atBot`);
* the two ends `pPos = lim_{t→+∞} α`, `pNeg = lim_{t→-∞} α` exist, the tails converge to them and
  they are not in the range of `α` (`exists_end_atTop`, `exists_ends`);
* consequently `closure (range α) = range α ∪ {pPos, pNeg}` (`closure_range_eq`).
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter
open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- **Closure of a `+∞`-tail of a curve.** -/
theorem tail_closure_subset [T2Space X] {α : ℝ → X} {p : X} (hcont : Continuous α)
    (htend : Tendsto α atTop (𝓝 p)) (t : ℝ) :
    closure (α '' Set.Ici t) ⊆ α '' Set.Ici t ∪ {p} := by
  intro y hy
  by_contra hcon
  rw [mem_union, not_or] at hcon
  obtain ⟨hy1, hy2⟩ := hcon
  have hy2' : y ≠ p := by simpa using hy2
  obtain ⟨O, O', hO, hO', hOy, hO'p, hdisj⟩ := t2_separation hy2'
  obtain ⟨T0, hT0⟩ := Filter.mem_atTop_sets.mp (htend (hO'.mem_nhds hO'p))
  set T := max T0 t with hT
  have hy' : y ∈ α '' Set.Icc t T := by
    rw [← (isCompact_Icc.image hcont).isClosed.closure_eq]
    rw [mem_closure_iff]
    intro U hU hyU
    rw [mem_closure_iff] at hy
    obtain ⟨z, hzOU, hzT⟩ := hy (O ∩ U) (hO.inter hU) ⟨hOy, hyU⟩
    obtain ⟨s, hsI, hsz⟩ := hzT
    have hsO : α s ∈ O := by rw [hsz]; exact hzOU.1
    have hsU : α s ∈ U := by rw [hsz]; exact hzOU.2
    have hsT : s ≤ T := by
      by_contra hlt
      rw [not_le] at hlt
      exact Set.disjoint_left.mp hdisj hsO (hT0 s (le_trans (le_max_left _ _) hlt.le))
    exact ⟨α s, hsU, s, ⟨hsI, hsT⟩, rfl⟩
  obtain ⟨s, hs, hsy⟩ := hy'
  exact hy1 ⟨s, hs.1, hsy⟩

/-- **Closure of a `-∞`-tail of a curve.** -/
theorem tail_closure_subset_atBot [T2Space X] {α : ℝ → X} {p : X} (hcont : Continuous α)
    (htend : Tendsto α atBot (𝓝 p)) (t : ℝ) :
    closure (α '' Set.Iic t) ⊆ α '' Set.Iic t ∪ {p} := by
  intro y hy
  by_contra hcon
  rw [mem_union, not_or] at hcon
  obtain ⟨hy1, hy2⟩ := hcon
  have hy2' : y ≠ p := by simpa using hy2
  obtain ⟨O, O', hO, hO', hOy, hO'p, hdisj⟩ := t2_separation hy2'
  obtain ⟨T0, hT0⟩ := Filter.mem_atBot_sets.mp (htend (hO'.mem_nhds hO'p))
  have hy' : y ∈ α '' Set.Icc T0 t := by
    rw [← (isCompact_Icc.image hcont).isClosed.closure_eq]
    rw [mem_closure_iff]
    intro U hU hyU
    rw [mem_closure_iff] at hy
    obtain ⟨z, hzOU, hzT⟩ := hy (O ∩ U) (hO.inter hU) ⟨hOy, hyU⟩
    obtain ⟨s, hsI, hsz⟩ := hzT
    have hsO : α s ∈ O := by rw [hsz]; exact hzOU.1
    have hsU : α s ∈ U := by rw [hsz]; exact hzOU.2
    have hsT : T0 ≤ s := by
      by_contra hlt
      rw [not_le] at hlt
      exact Set.disjoint_left.mp hdisj hsO (hT0 s hlt.le)
    exact ⟨α s, hsU, s, ⟨hsT, hsI⟩, rfl⟩
  obtain ⟨s, hs, hsy⟩ := hy'
  exact hy1 ⟨s, hs.2, hsy⟩

/-- **The `+∞`-end of an embedded arc in a compact space.** -/
theorem exists_end_atTop [T2Space X] [CompactSpace X]
    (H : Work.Smooth.SphereJordan.IsLocallyArc X)
    {α : ℝ → X} (hcont : Continuous α) (hinj : Function.Injective α) :
    ∃ p : X, (∀ t : ℝ, p ∈ closure (α '' Set.Ici t)) ∧ Tendsto α atTop (𝓝 p) ∧
      p ∉ Set.range α := by
  have hnest : ∀ t u : ℝ, t ≤ u → closure (α '' Set.Ici u) ⊆ closure (α '' Set.Ici t) := by
    intro t u htu
    apply closure_mono
    apply image_mono
    intro s hs
    simp only [Set.mem_Ici] at hs ⊢
    exact le_trans htu hs
  have hfin : ∀ u : Finset ℕ,
      (Set.univ ∩ ⋂ n ∈ u, closure (α '' Set.Ici ((n:ℕ):ℝ))).Nonempty := by
    intro u
    set N : ℕ := u.sum (fun n => n) + 1 with hN
    have hle : ∀ n ∈ u, (n : ℝ) ≤ (N : ℝ) := by
      intro n hn
      have h1 : n ≤ u.sum (fun n => n) :=
        Finset.single_le_sum (f := fun n => n) (fun i _ => Nat.zero_le i) hn
      have h2 : n ≤ N := by simp only [hN]; omega
      exact_mod_cast h2
    refine ⟨α (N : ℝ), trivial, ?_⟩
    simp only [Set.mem_iInter]
    intro n hn
    exact hnest (n : ℝ) (N : ℝ) (hle n hn)
      (subset_closure (s := α '' Set.Ici ((N:ℕ):ℝ)) ⟨(N:ℝ), Set.mem_Ici.mpr (le_refl _), rfl⟩)
  obtain ⟨p, -, hp⟩ := IsCompact.inter_iInter_nonempty isCompact_univ
    (fun n : ℕ => closure (α '' Set.Ici ((n:ℕ):ℝ))) (fun n => isClosed_closure) hfin
  have hpn : ∀ n : ℕ, p ∈ closure (α '' Set.Ici ((n:ℕ):ℝ)) := by
    simpa only [Set.mem_iInter] using hp
  have hp' : ∀ t : ℝ, p ∈ closure (α '' Set.Ici t) := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact hnest t (n : ℝ) hn (hpn n)
  exact ⟨p, hp', localArc_tendsto_atTop (Work.Smooth.SphereJordan.chartOf H p) hcont hinj hp',
    fun hmem => by
      obtain ⟨t₀, ht₀⟩ := hmem
      exact no_self_limit hcont hinj (Work.Smooth.SphereJordan.chartOf H (α t₀))
        (fun s => by rw [ht₀]; exact hp' s)⟩

/-- **Existence of the two ends of an embedded arc in a compact space.** -/
theorem exists_ends [T2Space X] [CompactSpace X]
    (H : Work.Smooth.SphereJordan.IsLocallyArc X)
    {α : ℝ → X} (hcont : Continuous α) (hinj : Function.Injective α) :
    ∃ pPos pNeg : X,
      (∀ t : ℝ, pPos ∈ closure (α '' Set.Ici t)) ∧ (∀ t : ℝ, pNeg ∈ closure (α '' Set.Iic t)) ∧
      Tendsto α atTop (𝓝 pPos) ∧ Tendsto α atBot (𝓝 pNeg) ∧
      pPos ∉ Set.range α ∧ pNeg ∉ Set.range α := by
  obtain ⟨pPos, hp1, hp2, hp3⟩ := exists_end_atTop H hcont hinj
  obtain ⟨pNeg, hq1, hq2, hq3⟩ := exists_end_atTop H (hcont.comp continuous_neg)
    (fun a b h => by simpa using hinj h)
  refine ⟨pPos, pNeg, hp1, ?_, hp2, ?_, hp3, ?_⟩
  · intro t
    have h := hq1 (-t)
    have himg : (α ∘ fun u : ℝ => -u) '' Set.Ici (-t) = α '' Set.Iic t := by
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        have hu' : -t ≤ u := hu
        exact ⟨-u, show -u ≤ t from by linarith, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        have hu' : u ≤ t := hu
        exact ⟨-u, show -t ≤ -u from by linarith, by simp⟩
    rwa [himg] at h
  · rw [tendsto_def] at hq2 ⊢
    intro U hU
    obtain ⟨T, hT⟩ := Filter.mem_atTop_sets.mp (hq2 U hU)
    exact Filter.mem_atBot_sets.mpr ⟨-T, fun t ht => by
      have h1 : T ≤ -t := by linarith
      simpa using hT (-t) h1⟩
  · rintro ⟨y, hy⟩
    exact hq3 ⟨-y, by simpa using hy⟩

/-- **The closure of the range of an embedded arc is the range together with the two ends.** -/
theorem closure_range_eq [T2Space X] [CompactSpace X]
    (H : Work.Smooth.SphereJordan.IsLocallyArc X) {α : ℝ → X} (hcont : Continuous α)
    (hinj : Function.Injective α) {pPos pNeg : X}
    (hPos : ∀ t : ℝ, pPos ∈ closure (α '' Set.Ici t))
    (hNeg : ∀ t : ℝ, pNeg ∈ closure (α '' Set.Iic t))
    (htPos : Tendsto α atTop (𝓝 pPos)) (htNeg : Tendsto α atBot (𝓝 pNeg))
    (hpPos : pPos ∉ Set.range α) (hpNeg : pNeg ∉ Set.range α) :
    closure (Set.range α) = Set.range α ∪ {pPos, pNeg} := by
  have h1 : closure (α '' Set.Ici 0) = α '' Set.Ici 0 ∪ {pPos} := by
    refine subset_antisymm (tail_closure_subset hcont htPos 0) ?_
    intro z hz
    rcases hz with hz | hz
    · exact subset_closure hz
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hPos 0
  have h2 : closure (α '' Set.Iic 0) = α '' Set.Iic 0 ∪ {pNeg} := by
    refine subset_antisymm (tail_closure_subset_atBot hcont htNeg 0) ?_
    intro z hz
    rcases hz with hz | hz
    · exact subset_closure hz
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hNeg 0
  have hrange : Set.range α = α '' Set.Iic 0 ∪ α '' Set.Ici 0 := by
    rw [← Set.image_union, Set.Iic_union_Ici, Set.image_univ]
  rw [hrange, closure_union, h1, h2]
  ext z
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, hrange]
  tauto

end

end Work.Smooth.SphereJordan.LocalArc
