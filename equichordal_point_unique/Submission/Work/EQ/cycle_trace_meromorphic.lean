import Mathlib
import Submission.Work.EQ.EndDefs
import Submission.Work.EQ.cycle_local_normal_form
import Submission.Work.EQ.meromorphicAt_rootSum
import Submission.Work.EQ.rootSet_ncard
import Submission.Work.EQ.exists_common_eventual_value

open Filter _root_.Topology
open scoped Topology BigOperators

namespace Work.EQ

/-- The `ψ₁`-fibre of the component of `p` over `u`. -/
noncomputable def FibOf (a : ℝ) (h : ℂ → ℂ) (p : ChainData) (u : ℂ) : Set ChainData :=
  {q | q ∈ connectedComponentIn (H0 a h) p ∧ q.2.1 = u}

/-- **Cardinality of the fibre under the chart description.** -/
theorem ncard_fibre_of_charts {S : Set ChainData} {m : ℕ} {k : Fin m → ℕ} {κ : Fin m → ℂ}
    {e : Fin m → ℂ → ChainData} {u₁ u : ℂ}
    (hk : ∀ i, 0 < k i ∧ κ i ≠ 0) (hu : u ≠ u₁)
    (hfib : {q | q ∈ S ∧ q.2.1 = u} =
      ⋃ i, e i '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ i * ζ ^ (k i) = u})
    (hinj : ∀ (i j : Fin m) (ζ ζ' : ℂ), ζ ≠ 0 → ζ' ≠ 0 →
      u₁ + κ i * ζ ^ (k i) = u → u₁ + κ j * ζ' ^ (k j) = u → e i ζ = e j ζ' →
      i = j ∧ ζ = ζ') :
    {q | q ∈ S ∧ q.2.1 = u}.ncard = ∑ i, k i := by
  set s : Fin m → Set ChainData :=
    fun i => e i '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ i * ζ ^ (k i) = u} with hsdef
  have hfin_i : ∀ i, (s i).Finite := by
    intro i
    refine Set.Finite.image _ (Set.finite_of_ncard_pos ?_)
    rw [rootSet_ncard (hk i).1 (hk i).2 hu]
    exact (hk i).1
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro i j hij
    change Disjoint (s i) (s j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨ζ, hζ, hζx⟩ := hxi
    obtain ⟨ζ', hζ', hζ'x⟩ := hxj
    have heq : e i ζ = e j ζ' := by rw [hζx, hζ'x]
    exact hij (hinj i j ζ ζ' hζ.1 hζ'.1 hζ.2 hζ'.2 heq).1
  rw [hfib]
  change (⋃ i, s i).ncard = ∑ i, k i
  rw [Set.ncard_iUnion_of_finite hfin_i hdisj, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Set.InjOn.ncard_image]
  · exact rootSet_ncard (hk i).1 (hk i).2 hu
  · intro ζ hζ ζ' hζ' h
    exact (hinj i i ζ ζ' hζ.1 hζ'.1 hζ.2 hζ'.2 h).2

/-- **The fibre sum of `W` is meromorphic at the centre of a chart system.** -/
theorem meromorphic_fibreSum_of_charts {S : Set ChainData} {m : ℕ} {k : Fin m → ℕ} {κ : Fin m → ℂ}
    {e : Fin m → ℂ → ChainData} {u₁ : ℂ} {ρ : ℝ} {a : ℝ}
    (hρ : 0 < ρ) (hk : ∀ i, 0 < k i ∧ κ i ≠ 0)
    (hmero : ∀ i n, MeromorphicAt (fun ζ => ((e i ζ).1 n).1) 0 ∧
      MeromorphicAt (fun ζ => ((e i ζ).1 n).2) 0)
    (hkey : ∀ u ∈ Metric.ball u₁ ρ, u ≠ u₁ →
      {q | q ∈ S ∧ q.2.1 = u} =
          ⋃ i, e i '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ i * ζ ^ (k i) = u} ∧
        ∀ (i j : Fin m) (ζ ζ' : ℂ), ζ ≠ 0 → ζ' ≠ 0 →
          u₁ + κ i * ζ ^ (k i) = u → u₁ + κ j * ζ' ^ (k j) = u → e i ζ = e j ζ' →
          i = j ∧ ζ = ζ') :
    MeromorphicAt (fun u => ∑ᶠ q ∈ {q | q ∈ S ∧ q.2.1 = u}, wNum 0 q / wDen a 0 q) u₁ := by
  have hg : ∀ i, MeromorphicAt (fun ζ => wNum 0 (e i ζ) / wDen a 0 (e i ζ)) 0 := by
    intro i
    have h1 : MeromorphicAt (fun ζ => ((e i ζ).1 0).1) 0 := (hmero i 0).1
    have h2 : MeromorphicAt (fun ζ => ((e i ζ).1 0).2) 0 := (hmero i 0).2
    have h3 : MeromorphicAt (fun ζ => ((e i ζ).1 0).1 - ((a / 2 : ℝ) : ℂ)) 0 :=
      h1.sub (MeromorphicAt.const _ 0)
    have h4 : MeromorphicAt
        (fun ζ => ((e i ζ).1 0).2 / (((e i ζ).1 0).1 - ((a / 2 : ℝ) : ℂ))) 0 :=
      h2.div h3
    simpa [wNum, wDen] using h4
  have hHmero : MeromorphicAt (∑ i : Fin m, fun u : ℂ =>
      ∑ᶠ ζ ∈ {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ i * ζ ^ (k i) = u},
        wNum 0 (e i ζ) / wDen a 0 (e i ζ)) u₁ := by
    refine MeromorphicAt.sum (s := Finset.univ) (fun i _ => ?_)
    exact meromorphicAt_rootSum (hg i) (hk i).1 (hk i).2 u₁
  have hpoint : ∀ u ∈ Metric.ball u₁ ρ, u ≠ u₁ →
      ∑ᶠ q ∈ {q | q ∈ S ∧ q.2.1 = u}, wNum 0 q / wDen a 0 q =
      ∑ i : Fin m, ∑ᶠ ζ ∈ {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ i * ζ ^ (k i) = u},
        wNum 0 (e i ζ) / wDen a 0 (e i ζ) := by
    intro u hu hune
    obtain ⟨hfibu, hinju⟩ := hkey u hu hune
    set s : Fin m → Set ChainData :=
      fun i => e i '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ i * ζ ^ (k i) = u} with hsdef
    have hfin_i : ∀ i, (s i).Finite := by
      intro i
      refine Set.Finite.image _ (Set.finite_of_ncard_pos ?_)
      rw [rootSet_ncard (hk i).1 (hk i).2 hune]
      exact (hk i).1
    have hdisj : Pairwise (Function.onFun Disjoint s) := by
      intro i j hij
      change Disjoint (s i) (s j)
      rw [Set.disjoint_left]
      intro x hxi hxj
      obtain ⟨ζ, hζ, hζx⟩ := hxi
      obtain ⟨ζ', hζ', hζ'x⟩ := hxj
      have heq : e i ζ = e j ζ' := by rw [hζx, hζ'x]
      exact hij (hinju i j ζ ζ' hζ.1 hζ'.1 hζ.2 hζ'.2 heq).1
    have hdisjI : (Set.univ : Set (Fin m)).PairwiseDisjoint s :=
      fun i _ j _ hij => hdisj hij
    rw [hfibu]
    change ∑ᶠ q ∈ (⋃ i, s i), wNum 0 q / wDen a 0 q = _
    rw [show (⋃ i, s i) = ⋃ i ∈ (Set.univ : Set (Fin m)), s i by simp]
    rw [finsum_mem_biUnion hdisjI Set.finite_univ (fun i _ => hfin_i i), finsum_mem_univ,
      finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finsum_mem_image (g := e i) (s := {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ i * ζ ^ (k i) = u})
      (f := fun q => wNum 0 q / wDen a 0 q)]
    intro ζ hζ ζ' hζ' h
    exact (hinju i i ζ ζ' hζ.1 hζ'.1 hζ.2 hζ'.2 h).2
  refine hHmero.congr ?_
  have hb : Metric.ball u₁ ρ ∈ 𝓝[≠] u₁ := nhdsWithin_le_nhds (Metric.ball_mem_nhds u₁ hρ)
  filter_upwards [hb, self_mem_nhdsWithin] with u hu hune
  rw [Finset.sum_apply]
  exact (hpoint u hu hune).symm

/-- **The trace of `W` over the `ψ₁`-fibres is meromorphic on `ℂ*`.** For the component `S` of `p`, proper modulo punctures over `ℂ*`, the `ψ₁`-fibres are finite and have a common size `n ≥ 1` off a discrete set (and at most `n` everywhere), and the fibre sum of `W = y/(x - a/2)` of the index-0 point is meromorphic at every `u₁ ≠ 0`. This is an interface of `Work.EQ.rational_of_compact_cycle` (route: `Submission/Work/EQ/DESIGN_CCM.md`, §2 D). -/
theorem cycle_trace_meromorphic {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {p : ChainData} (hp : p ∈ H0 a h)
    (hcpt2 : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K →
      ∃ C : Set ChainData, IsCompact C ∧ C ⊆ H0 a h ∧
        ∃ (m : ℕ) (e : Fin m → ℂ → ChainData) (u₀ : Fin m → ℂ) (k : Fin m → ℕ),
          (∀ i, IsPuncturedChart a h (e i) (u₀ i) (k i)) ∧
          connectedComponentIn (H0 a h) p ∩ {q | q.2.1 ∈ K} ⊆
            C ∪ ⋃ i, e i '' (Metric.ball (0 : ℂ) (1 / 2) \ {0})) :
    ∃ n : ℕ, 0 < n ∧
      (∀ u : ℂ, u ≠ 0 →
        {q | q ∈ connectedComponentIn (H0 a h) p ∧ q.2.1 = u}.Finite ∧
        {q | q ∈ connectedComponentIn (H0 a h) p ∧ q.2.1 = u}.ncard ≤ n) ∧
      (∀ u₁ : ℂ, u₁ ≠ 0 → ∀ᶠ u in 𝓝[≠] u₁,
        {q | q ∈ connectedComponentIn (H0 a h) p ∧ q.2.1 = u}.ncard = n) ∧
      ∀ u₁ : ℂ, u₁ ≠ 0 → MeromorphicAt (fun u =>
        ∑ᶠ q ∈ {q | q ∈ connectedComponentIn (H0 a h) p ∧ q.2.1 = u},
          wNum 0 q / wDen a 0 q) u₁ := by
  change ∃ n : ℕ, 0 < n ∧
      (∀ u : ℂ, u ≠ 0 → (FibOf a h p u).Finite ∧ (FibOf a h p u).ncard ≤ n) ∧
      (∀ u₁ : ℂ, u₁ ≠ 0 → ∀ᶠ u in 𝓝[≠] u₁, (FibOf a h p u).ncard = n) ∧
      ∀ u₁ : ℂ, u₁ ≠ 0 →
        MeromorphicAt (fun u => ∑ᶠ q ∈ FibOf a h p u, wNum 0 q / wDen a 0 q) u₁
  have hpψ : p.2.1 ≠ 0 := by
    obtain ⟨ε, hε, f, -, hf0, hf⟩ := hp
    have hch : IsChain a h (f p.2.1) := (hf p.2.1 (Metric.mem_ball_self hε)).1
    rw [hf0] at hch
    exact hch.2.1
  have hloc : ∀ u₁ : ℂ, u₁ ≠ 0 →
      ∃ (ρ : ℝ) (m : ℕ) (k : Fin m → ℕ) (κ : Fin m → ℂ) (e : Fin m → ℂ → ChainData),
        0 < ρ ∧ (∀ i, 0 < k i ∧ κ i ≠ 0) ∧
        (∀ i n, MeromorphicAt (fun ζ => ((e i ζ).1 n).1) 0 ∧
          MeromorphicAt (fun ζ => ((e i ζ).1 n).2) 0) ∧
        (FibOf a h p u₁).Finite ∧ (FibOf a h p u₁).ncard ≤ ∑ i, k i ∧
        ∀ u ∈ Metric.ball u₁ ρ, u ≠ u₁ →
          FibOf a h p u = ⋃ i, e i '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ i * ζ ^ (k i) = u} ∧
          ∀ (i j : Fin m) (ζ ζ' : ℂ), ζ ≠ 0 → ζ' ≠ 0 →
            u₁ + κ i * ζ ^ (k i) = u → u₁ + κ j * ζ' ^ (k j) = u →
            e i ζ = e j ζ' → i = j ∧ ζ = ζ' := by
    intro u₁ hu₁
    obtain ⟨ρ, m, k, κ, e, hρ, hk, hmero, hfin, hle, hkey⟩ :=
      cycle_local_normal_form ha0 ha1 hh hp hcpt2 hu₁
    exact ⟨ρ, m, k, κ, e, hρ, hk, hmero, hfin, hle, hkey⟩
  have hbase : ∀ u : ℂ, u ≠ 0 → ∃ N : ℕ, ∀ᶠ v in 𝓝[≠] u, (FibOf a h p v).ncard = N := by
    intro u hu
    obtain ⟨ρ, m, k, κ, e, hρ, hk, hmero, hfin, hle, hkey⟩ := hloc u hu
    refine ⟨∑ i, k i, ?_⟩
    have hb : Metric.ball u ρ ∈ 𝓝[≠] u := nhdsWithin_le_nhds (Metric.ball_mem_nhds u hρ)
    filter_upwards [hb, self_mem_nhdsWithin] with v hv hvu
    exact ncard_fibre_of_charts hk hvu (hkey v hv hvu).1 (hkey v hv hvu).2
  obtain ⟨n, hn⟩ := exists_common_eventual_value (P := fun u => (FibOf a h p u).ncard) hbase
  have hNu : ∀ (u₁ : ℂ) (hu₁ : u₁ ≠ 0) (N : ℕ),
      (∀ᶠ v in 𝓝[≠] u₁, (FibOf a h p v).ncard = N) → N = n := by
    intro u₁ hu₁ N hN
    obtain ⟨v, hvN, hvn⟩ := (hN.and (hn u₁ hu₁)).exists
    exact hvN.symm.trans hvn
  have hNsum : ∀ (u₁ : ℂ) (hu₁ : u₁ ≠ 0) {m : ℕ} {k : Fin m → ℕ} {κ : Fin m → ℂ}
      {e : Fin m → ℂ → ChainData} {ρ : ℝ}, 0 < ρ → (∀ i, 0 < k i ∧ κ i ≠ 0) →
      (∀ u ∈ Metric.ball u₁ ρ, u ≠ u₁ →
        FibOf a h p u = ⋃ i, e i '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ i * ζ ^ (k i) = u} ∧
        ∀ (i j : Fin m) (ζ ζ' : ℂ), ζ ≠ 0 → ζ' ≠ 0 →
          u₁ + κ i * ζ ^ (k i) = u → u₁ + κ j * ζ' ^ (k j) = u →
          e i ζ = e j ζ' → i = j ∧ ζ = ζ') → (∑ i, k i) = n := by
    intro u₁ hu₁ m k κ e ρ hρ hk hkey
    refine hNu u₁ hu₁ _ ?_
    have hb : Metric.ball u₁ ρ ∈ 𝓝[≠] u₁ := nhdsWithin_le_nhds (Metric.ball_mem_nhds u₁ hρ)
    filter_upwards [hb, self_mem_nhdsWithin] with v hv hvu
    exact ncard_fibre_of_charts hk hvu (hkey v hv hvu).1 (hkey v hv hvu).2
  have hnpos : 0 < n := by
    obtain ⟨ρ, m, k, κ, e, hρ, hk, hmero, hfin, hle, hkey⟩ := hloc p.2.1 hpψ
    have hN : (∑ i, k i) = n := hNsum p.2.1 hpψ hρ hk hkey
    have hmem : p ∈ FibOf a h p p.2.1 := ⟨mem_connectedComponentIn hp, rfl⟩
    have h1 : 0 < (FibOf a h p p.2.1).ncard := (Set.ncard_pos hfin).mpr ⟨p, hmem⟩
    have h2 : (FibOf a h p p.2.1).ncard ≤ n := by rw [← hN]; exact hle
    omega
  refine ⟨n, hnpos, ?_, hn, ?_⟩
  · intro u hu
    obtain ⟨ρ, m, k, κ, e, hρ, hk, hmero, hfin, hle, hkey⟩ := hloc u hu
    have hN : (∑ i, k i) = n := hNsum u hu hρ hk hkey
    exact ⟨hfin, by rw [← hN]; exact hle⟩
  · intro u₁ hu₁
    obtain ⟨ρ, m, k, κ, e, hρ, hk, hmero, hfin, hle, hkey⟩ := hloc u₁ hu₁
    exact meromorphic_fibreSum_of_charts hρ hk hmero hkey

end Work.EQ
