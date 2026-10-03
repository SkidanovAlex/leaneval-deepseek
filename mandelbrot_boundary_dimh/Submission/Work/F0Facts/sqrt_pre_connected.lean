import Mathlib

namespace Work.F0Facts

open Set Metric

/-- For an open connected subset `V ⊆ ℂ` containing `0`, the set of its square roots
`{x : ℂ | x ^ 2 ∈ V}` is connected. -/
theorem sqrt_pre_connected {V : Set ℂ} (hV : IsOpen V) (hc : IsConnected V) (h0 : (0 : ℂ) ∈ V) :
    IsConnected {x : ℂ | x ^ 2 ∈ V} := by
  have hsq_open : IsOpenMap (fun z : ℂ => z ^ 2) := (Complex.isOpenQuotientMap_pow 2).isOpenMap
  have hsq_surj : Function.Surjective (fun z : ℂ => z ^ 2) :=
    (Complex.isOpenQuotientMap_pow 2).surjective
  set S : Set ℂ := (fun z : ℂ => z ^ 2) ⁻¹' V with hSdef
  have hSopen : IsOpen S := hV.preimage (by fun_prop)
  have h0S : (0 : ℂ) ∈ S := by show (0 : ℂ) ^ 2 ∈ V; simpa using h0
  set A : Set ℂ := connectedComponentIn S 0 with hAdef
  have hApre : IsPreconnected A := by rw [hAdef]; exact isPreconnected_connectedComponentIn
  have hAsub : A ⊆ S := by rw [hAdef]; exact connectedComponentIn_subset S 0
  have h0A : (0 : ℂ) ∈ A := by rw [hAdef]; exact mem_connectedComponentIn h0S
  -- The component of `0` is open in `ℂ`.
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro x hxA
    have hcomp : connectedComponentIn S x = A := by
      rw [hAdef]
      exact (connectedComponentIn_eq hxA).symm
    obtain ⟨r, hr, hballS⟩ := Metric.mem_nhds_iff.mp (hSopen.mem_nhds (hAsub hxA))
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x hr) ?_
    intro z hz
    rw [← hcomp]
    exact IsPreconnected.subset_connectedComponentIn ((convex_ball x r).isPreconnected)
      (Metric.mem_ball_self hr) hballS hz
  -- The component of `0` is closed in `S`.
  have hAclosed : ∀ y ∈ S, y ∈ closure A → y ∈ A := by
    intro y hyS hycl
    have hpre : IsPreconnected (A ∪ {y}) :=
      hApre.subset_closure subset_union_left (by
        intro z hz
        rcases hz with hz | hz
        · exact subset_closure hz
        · rw [mem_singleton_iff] at hz; rw [hz]; exact hycl)
    have hsub : A ∪ {y} ⊆ A := hpre.subset_connectedComponentIn (Or.inl h0A) (by
      intro z hz
      rcases hz with hz | hz
      · exact hAsub hz
      · rw [mem_singleton_iff] at hz; rw [hz]; exact hyS)
    exact hsub (Or.inr rfl)
  -- `A` is invariant under negation.
  have hnegA : ∀ a ∈ A, -a ∈ A := by
    intro a ha
    have hpre : IsPreconnected ((fun z : ℂ => -z) '' A) :=
      hApre.image _ continuous_neg.continuousOn
    have hsub : (fun z : ℂ => -z) '' A ⊆ S := by
      rintro z ⟨b, hb, rfl⟩
      show (-b) ^ 2 ∈ V
      have hbb : (-b) ^ 2 = b ^ 2 := by ring
      rw [hbb]; exact hAsub hb
    have hmem : (0 : ℂ) ∈ (fun z : ℂ => -z) '' A := ⟨0, h0A, by simp⟩
    exact hpre.subset_connectedComponentIn hmem hsub ⟨a, ha, rfl⟩
  set qA : Set ℂ := (fun z : ℂ => z ^ 2) '' A with hqAdef
  have hqA_open : IsOpen qA := hsq_open A hAopen
  -- Every square root of a point of `qA` lies in `A`.
  have hqA_roots : ∀ w ∈ qA, ∀ x : ℂ, x ^ 2 = w → x ∈ A := by
    intro w hw x hx
    rcases hw with ⟨a, ha, hae⟩
    have hae' : a ^ 2 = w := hae
    have hxa : x * x = a * a := by rw [← pow_two, ← pow_two, hx, hae']
    rcases mul_self_eq_mul_self_iff.mp hxa with h | h
    · rw [h]; exact ha
    · rw [h]; exact hnegA a ha
  -- The complement of `qA` inside `V` is open.
  have hv_open : IsOpen (V \ qA) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨hwV, hwqA⟩
    obtain ⟨x, hx⟩ := hsq_surj w
    have hx' : x ^ 2 = w := hx
    have hxS : x ∈ S := by show x ^ 2 ∈ V; rw [hx']; exact hwV
    have hxA : x ∉ A := fun h => hwqA ⟨x, h, hx⟩
    have hxcl : x ∉ closure A := fun h => hxA (hAclosed x hxS h)
    have hex : ∃ o : Set ℂ, IsOpen o ∧ x ∈ o ∧ o ∩ A = ∅ := by
      by_contra hcon
      exact hxcl (_root_.mem_closure_iff.mpr fun o ho hxo =>
        Set.nonempty_iff_ne_empty.mpr fun hEmpty => hcon ⟨o, ho, hxo, hEmpty⟩)
    obtain ⟨o, hoopen, hxo, hoA⟩ := hex
    obtain ⟨r₁, hr₁, hb₁⟩ := Metric.mem_nhds_iff.mp (hSopen.mem_nhds hxS)
    obtain ⟨r₂, hr₂, hb₂⟩ := Metric.mem_nhds_iff.mp (hoopen.mem_nhds hxo)
    set r : ℝ := min r₁ r₂ with hrdef
    have hr : 0 < r := lt_min hr₁ hr₂
    have hballO : ball x r ⊆ o := (Metric.ball_subset_ball (min_le_right r₁ r₂)).trans hb₂
    have hballS : ball x r ⊆ S := (Metric.ball_subset_ball (min_le_left r₁ r₂)).trans hb₁
    have hdisj : ∀ z ∈ ball x r, z ∉ A := by
      intro z hz hzA
      have hzo : z ∈ o ∩ A := ⟨hballO hz, hzA⟩
      rw [hoA] at hzo
      exact hzo
    set U : Set ℂ := (fun z : ℂ => z ^ 2) '' ball x r with hUdef
    have hUopen : IsOpen U := hsq_open _ Metric.isOpen_ball
    have hxball : x ∈ ball x r := Metric.mem_ball_self hr
    have hwU : w ∈ U := ⟨x, hxball, hx⟩
    refine Filter.mem_of_superset (hUopen.mem_nhds hwU) ?_
    rintro w' hw'
    obtain ⟨y, hyball, hyw'⟩ := hw'
    have hyw'' : y ^ 2 = w' := hyw'
    constructor
    · rw [← hyw'']; exact hballS hyball
    · intro hwqA'
      rcases hwqA' with ⟨b, hb, hbe⟩
      have hbe' : b ^ 2 = w' := hbe
      have hby : b * b = y * y := by rw [← pow_two, ← pow_two, hbe', hyw'']
      rcases mul_self_eq_mul_self_iff.mp hby with h | h
      · exact hdisj y hyball (h ▸ hb)
      · have : y ∈ A := by
          have := hnegA (-y) (h ▸ hb)
          simpa using this
        exact hdisj y hyball this
  -- `qA` is clopen in `V`, hence all of `V`.
  have hVqA : V ⊆ qA := by
    have hd : Disjoint qA (V \ qA) := by
      rw [Set.disjoint_left]; intro z hz hz'; exact hz'.2 hz
    have hsub : V ⊆ qA ∪ (V \ qA) := by
      intro z hz
      by_cases h : z ∈ qA
      · exact Or.inl h
      · exact Or.inr ⟨hz, h⟩
    rcases hc.isPreconnected.subset_or_subset hqA_open hv_open hd hsub with h | h
    · exact h
    · exfalso
      exact (h h0).2 ⟨0, h0A, by simp⟩
  have hS_eq_A : S = A := by
    refine Subset.antisymm ?_ hAsub
    intro z hzS
    exact hqA_roots (z ^ 2) (hVqA hzS) z rfl
  change IsConnected S
  rw [hS_eq_A, hAdef]
  exact isConnected_connectedComponentIn_iff.mpr h0S

end Work.F0Facts
