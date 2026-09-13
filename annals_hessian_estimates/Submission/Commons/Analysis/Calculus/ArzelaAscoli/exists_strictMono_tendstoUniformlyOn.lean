import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

open scoped Topology
open Filter Set Metric

namespace Commons.Analysis.Calculus.ArzelaAscoli

/-- **Arzelà–Ascoli, sequential Lipschitz form.**

Let `X` be a compact pseudo-metric space and `E` a `T2` pseudo-metric space.  Let
`F : ℕ → X → E` be a sequence of continuous functions which is
* equicontinuous with a uniform Lipschitz constant `K`, i.e. `∀ n, LipschitzWith K (F n)`, and
* whose values lie in a common compact set `s ⊆ E`.

Then there is a strictly monotone `φ : ℕ → ℕ` and a `K`-Lipschitz function `g : X → E`
such that `F (φ k)` converges to `g` uniformly on `X`. -/
theorem exists_strictMono_tendstoUniformlyOn_of_lipschitz
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {E : Type*} [PseudoMetricSpace E] [T2Space E]
    {K : NNReal} {s : Set E} (hs : IsCompact s)
    {F : ℕ → X → E} (hcont : ∀ n, Continuous (F n)) (hmem : ∀ n x, F n x ∈ s)
    (hlip : ∀ n, LipschitzWith K (F n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : X → E, LipschitzWith K g ∧
      TendstoUniformlyOn (fun k => F (φ k)) g atTop Set.univ := by
  classical
  -- Package the functions as bounded continuous functions.
  let G : ℕ → BoundedContinuousFunction X E := fun n =>
    BoundedContinuousFunction.mkOfCompact (ContinuousMap.mk (F n) (hcont n))
  have G_apply : ∀ n x, G n x = F n x := by
    intro n x
    rw [BoundedContinuousFunction.mkOfCompact_apply]
    rfl
  -- The family is equicontinuous, with the modulus of continuity `t ↦ K * t`.
  have heq : Equicontinuous ((↑) : Set.range G → X → E) := by
    refine Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => (K : ℝ) * t) ?_ _ ?_
    · have h : Tendsto (fun t : ℝ => (K : ℝ) * t) (𝓝 0) (𝓝 ((K : ℝ) * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using h
    · intro x y i
      obtain ⟨n, hn⟩ := i.2
      have hcoe : (i : X → E) = F n := by
        rw [← hn]
        funext z
        exact G_apply n z
      rw [hcoe]
      exact (hlip n).dist_le_mul x y
  -- Arzelà–Ascoli: the closure of the family is compact.
  have hcpt : IsCompact (closure (Set.range G)) :=
    BoundedContinuousFunction.arzela_ascoli s hs (Set.range G)
      (fun f x hf => by rcases hf with ⟨n, rfl⟩; exact hmem n x) heq
  -- Extract a uniformly convergent subsequence.
  obtain ⟨g, -, φ, hφ, hconv⟩ :=
    hcpt.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  have hunif : TendstoUniformly (fun k (x : X) => G (φ k) x) g atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hconv ε hε] with k hk
    intro x
    calc dist (g x) (G (φ k) x) ≤ dist g (G (φ k)) :=
          BoundedContinuousFunction.dist_coe_le_dist x
      _ = dist (G (φ k)) g := dist_comm _ _
      _ < ε := hk
  refine ⟨φ, hφ, g, ?_, ?_⟩
  · -- The limit is `K`-Lipschitz.
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have hx : Tendsto (fun k => G (φ k) x) atTop (𝓝 (g x)) := hunif.tendsto_at x
    have hy : Tendsto (fun k => G (φ k) y) atTop (𝓝 (g y)) := hunif.tendsto_at y
    refine le_of_tendsto (hx.dist hy) ?_
    filter_upwards with k
    rw [G_apply, G_apply]
    exact (hlip (φ k)).dist_le_mul x y
  · -- Uniform convergence of `F ∘ φ` on `X`.
    rw [tendstoUniformlyOn_univ]
    simpa only [G_apply] using hunif

open scoped Topology in
/-- **Arzelà–Ascoli for a uniformly bounded, uniformly Lipschitz sequence on `ℝ⁴`.**

Given a sequence `u n` of functions on `ℝ⁴` which are uniformly bounded by `A` and all
`K`-Lipschitz, and given `R ≥ 0`, there is a strictly monotone subsequence index `φ` and a
`K`-Lipschitz function `g` such that `u (φ k)` converges to `g` uniformly on the closed ball
of radius `R` around the origin. -/
theorem exists_strictMono_tendstoUniformlyOn {u : ℕ → EuclideanSpace ℝ (Fin 4) → ℝ} {A : ℝ}
    {K : NNReal} (hu : ∀ n x, |u n x| ≤ A) (hlip : ∀ n, LipschitzWith K (u n)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : EuclideanSpace ℝ (Fin 4) → ℝ,
      LipschitzWith K g ∧
        TendstoUniformlyOn (fun k => u (φ k)) g atTop (Metric.closedBall 0 R) := by
  classical
  have hA : 0 ≤ A := le_trans (abs_nonneg (u 0 0)) (hu 0 0)
  -- Work on the compact closed ball `s`.
  set s : Set (EuclideanSpace ℝ (Fin 4)) := Metric.closedBall 0 R with hs
  have hcptS : CompactSpace s := by
    rw [hs]
    exact isCompact_iff_compactSpace.mp (isCompact_closedBall 0 R)
  have hs_mem : (0 : EuclideanSpace ℝ (Fin 4)) ∈ s := by
    rw [hs, Metric.mem_closedBall, dist_self]
    exact hR
  let F : ℕ → s → ℝ := fun n x => u n x
  have hF_cont : ∀ n, Continuous (F n) := by
    intro n
    show Continuous fun x : s => u n x
    exact (hlip n).continuous.comp continuous_subtype_val
  have hF_lip : ∀ n, LipschitzWith K (F n) := by
    intro n
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    show dist (u n x) (u n y) ≤ (K : ℝ) * dist x y
    simpa only [Subtype.dist_eq] using
      (hlip n).dist_le_mul (x : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 4))
  have hF_mem : ∀ n x, F n x ∈ Metric.closedBall (0 : ℝ) (max A 0) := by
    intro n x
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact le_trans (hu n x) (le_max_left A 0)
  obtain ⟨φ, hφ, g₀, hg₀_lip, hg₀_unif⟩ :=
    exists_strictMono_tendstoUniformlyOn_of_lipschitz (K := K)
      (isCompact_closedBall (0 : ℝ) (max A 0)) hF_cont hF_mem hF_lip
  -- Extend the limit from `s` to all of `ℝ⁴`, keeping the Lipschitz constant.
  let f : EuclideanSpace ℝ (Fin 4) → ℝ := fun x => if hx : x ∈ s then g₀ ⟨x, hx⟩ else 0
  have hf_lip : LipschitzOnWith K f s := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hx' : f x = g₀ ⟨x, hx⟩ := dif_pos hx
    have hy' : f y = g₀ ⟨y, hy⟩ := dif_pos hy
    rw [hx', hy']
    have := hg₀_lip.dist_le_mul (⟨x, hx⟩ : s) (⟨y, hy⟩ : s)
    rwa [Subtype.dist_eq] at this
  obtain ⟨G, hG_lip, hG_eq⟩ := hf_lip.extend_real
  refine ⟨φ, hφ, G, hG_lip, ?_⟩
  have hunif : TendstoUniformly (fun k (x : s) => F (φ k) x) g₀ atTop :=
    tendstoUniformlyOn_univ.mp hg₀_unif
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hunif ε hε] with k hk
  intro x hx
  have hGx : G x = g₀ ⟨x, hx⟩ := by
    rw [← hG_eq hx]
    exact dif_pos hx
  rw [hGx]
  exact hk ⟨x, hx⟩

end Commons.Analysis.Calculus.ArzelaAscoli