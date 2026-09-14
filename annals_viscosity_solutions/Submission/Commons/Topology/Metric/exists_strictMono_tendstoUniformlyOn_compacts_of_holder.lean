import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Commons.Topology.ArzelaAscoli.exists_subseq_tendstoLocallyUniformlyOn_of_locallyBounded_equicontinuous

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.Topology.Metric

open Filter Set
open scoped _root_.Topology

/-- The limit of the constant sequence with value `a`, obtained as a pointwise limit of functions
all of which take the value `a` at the base point, is at distance `0` from `a`. -/
private lemma dist_of_const_tendsto {E : Type*} [PseudoMetricSpace E] {a c : E}
    {u : ℕ → E} (hu : Tendsto u atTop (nhds c)) (h : ∀ n, u n = a) : dist c a = 0 := by
  have h2 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (dist c a)) := by
    have hh := hu.dist (tendsto_const_nhds (x := a))
    simpa [h] using hh
  exact tendsto_nhds_unique h2 tendsto_const_nhds

/-- **Sequential Arzelà–Ascoli on a separable, locally compact pseudo-metric space.**

Let `X` be a separable locally compact pseudo-metric space and `F` a proper pseudo-metric space.
Let `v : ℕ → X → F` be a sequence of functions which is
* bounded on every compact set (uniformly in `n`), and
* equicontinuous on every compact set (one modulus of continuity per compact set, uniform in `n`).

Then there is a strictly monotone `φ : ℕ → ℕ` and a function `G : X → F` such that `v (φ k)`
converges to `G` locally uniformly. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_of_equicontinuous_bounded
    {X : Type*} [PseudoMetricSpace X] [LocallyCompactSpace X] [TopologicalSpace.SeparableSpace X]
    {F : Type*} [PseudoMetricSpace F] [ProperSpace F]
    {v : ℕ → X → F} {x₀ : F}
    (hbdd : ∀ K : Set X, IsCompact K → ∃ C : ℝ, ∀ n, ∀ x ∈ K, dist (v n x) x₀ ≤ C)
    (heq : ∀ K : Set X, IsCompact K → Equicontinuous (fun n : ℕ => fun x : K => v n x)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : X → F,
      TendstoLocallyUniformlyOn (fun n => v (φ n)) G Filter.atTop Set.univ := by
  classical
  obtain ⟨D, hDcount, hDense⟩ := TopologicalSpace.exists_countable_dense X
  haveI : Countable D := Set.countable_coe_iff.mpr hDcount
  choose C hC using fun d : D => hbdd ({↑d} : Set X) isCompact_singleton
  let Φ : ℕ → (d : D) → Metric.closedBall x₀ (C d) := fun n d =>
    ⟨v n (d : X), by
      rw [Metric.mem_closedBall]
      exact hC d n (d : X) (Set.mem_singleton (d : X))⟩
  obtain ⟨z, φ, hφmono, hΦtend⟩ := CompactSpace.tendsto_subseq Φ
  have hz : ∀ d : D, Tendsto (fun k => v (φ k) (d : X)) atTop
      (𝓝 ((z d : Metric.closedBall x₀ (C d)) : F)) := by
    intro d
    have h1 : Tendsto (fun k => (Φ ∘ φ) k d) atTop (𝓝 (z d)) := (tendsto_pi_nhds.mp hΦtend) d
    have h2 := tendsto_subtype_rng.mp h1
    simpa [Φ, Function.comp_def] using h2
  have hconv : ∀ d ∈ D, CauchySeq (fun k => v (φ k) d) := fun d hd => (hz ⟨d, hd⟩).cauchySeq
  have hUnifCau := Commons.Topology.ArzelaAscoli.uniform_cauchy_of_dense_cauchy hDense hconv heq
  have hcauchy : ∀ x : X, CauchySeq (fun k => v (φ k) x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hUnifCau {x} isCompact_singleton ε hε
    exact ⟨N, fun m hm n hn => hN m hm n hn x (Set.mem_singleton x)⟩
  let g : X → F := fun x => Classical.choose (cauchySeq_tendsto_of_complete (hcauchy x))
  have hg : ∀ x : X, Tendsto (fun k => v (φ k) x) atTop (𝓝 (g x)) := fun x =>
    Classical.choose_spec (cauchySeq_tendsto_of_complete (hcauchy x))
  refine ⟨φ, hφmono, g, ?_⟩
  rw [tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hUnifCau K hK (ε / 2) (by linarith)
  rw [eventually_atTop]
  refine ⟨N, fun k hk x hx => ?_⟩
  have htend : Tendsto (fun l => dist (v (φ l) x) (v (φ k) x)) atTop
      (𝓝 (dist (g x) (v (φ k) x))) := (hg x).dist tendsto_const_nhds
  have hle : dist (g x) (v (φ k) x) ≤ ε / 2 := by
    refine le_of_tendsto htend ?_
    rw [eventually_atTop]
    exact ⟨N, fun l hl => le_of_lt (hN l hl k hk x hx)⟩
  linarith

theorem exists_strictMono_tendstoUniformlyOn_compacts_of_holder {F : Type*} [PseudoMetricSpace F]
    [ProperSpace F] {u : ℕ → ℝ → F} {T : ℕ → ℝ} {M : ℕ → ℝ} {x₀ : F}
    (hTmono : Monotone T) (hTend : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hT0 : ∀ j, 0 ≤ T j) (hM : ∀ j, 0 ≤ M j) (h0 : ∀ n, u n 0 = x₀)
    (hcont : ∀ n, ContinuousOn (u n) (Set.Ici 0))
    (hholder : ∀ j n (s t : ℝ), s ∈ Set.Icc 0 (T j) → t ∈ Set.Icc 0 (T j) →
        dist (u n s) (u n t) ≤ M j * Real.sqrt |s - t|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℝ → F,
      (∀ j, TendstoUniformlyOn (fun k => u (φ k)) G Filter.atTop (Set.Icc 0 (T j))) ∧
      ContinuousOn G (Set.Ici 0) ∧ G 0 = x₀ := by
  classical
  -- Work on the half-line as a type.
  let X : Type := ↥(Set.Ici (0 : ℝ))
  haveI : LocallyCompactSpace X := isClosed_Ici.locallyCompactSpace
  haveI : TopologicalSpace.SeparableSpace X := inferInstance
  let f : ℕ → X → F := fun n x => u n (x : ℝ)
  -- Every compact subset of the half-line is contained in some `[0, T j]`.
  have hex : ∀ K : Set X, IsCompact K → ∃ j : ℕ, ∀ x ∈ K, (x : ℝ) ≤ T j := by
    intro K hK
    have hKbc : IsCompact ((Subtype.val '' K) : Set ℝ) := hK.image continuous_subtype_val
    obtain ⟨B, hB⟩ := hKbc.bddAbove
    obtain ⟨j, hj⟩ := Filter.eventually_atTop.mp (hTend.eventually (eventually_ge_atTop B))
    exact ⟨j, fun x hx => le_trans (hB ⟨x, hx, rfl⟩) (hj j le_rfl)⟩
  -- Boundedness on compact sets, uniformly in `n`.
  have hbdd : ∀ K : Set X, IsCompact K → ∃ C : ℝ, ∀ n, ∀ x ∈ K, dist (f n x) x₀ ≤ C := by
    intro K hK
    obtain ⟨j, hj⟩ := hex K hK
    refine ⟨M j * Real.sqrt (T j), fun n x hx => ?_⟩
    have hxIcc : (x : ℝ) ∈ Set.Icc 0 (T j) := ⟨Set.mem_Ici.mp x.2, hj x hx⟩
    have h0Icc : (0 : ℝ) ∈ Set.Icc 0 (T j) := ⟨le_refl 0, hT0 j⟩
    calc dist (f n x) x₀
        = dist (u n (x : ℝ)) (u n 0) := by rw [h0 n]
      _ ≤ M j * Real.sqrt |(x : ℝ) - 0| := hholder j n (x : ℝ) 0 hxIcc h0Icc
      _ = M j * Real.sqrt (x : ℝ) := by rw [sub_zero, abs_of_nonneg (Set.mem_Ici.mp x.2)]
      _ ≤ M j * Real.sqrt (T j) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hj x hx)) (hM j)
  -- Equicontinuity on compact sets.
  have heq : ∀ K : Set X, IsCompact K → Equicontinuous (fun n : ℕ => fun x : K => f n x) := by
    intro K hK
    obtain ⟨j, hj⟩ := hex K hK
    refine Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => M j * Real.sqrt t) ?_ _ ?_
    · have h1 : Tendsto (fun t : ℝ => Real.sqrt t) (𝓝 0) (𝓝 (Real.sqrt 0)) :=
        Real.continuous_sqrt.continuousAt (x := 0)
      have h2 : Tendsto (fun t : ℝ => M j * Real.sqrt t) (𝓝 0) (𝓝 (M j * Real.sqrt 0)) :=
        (tendsto_const_nhds (x := M j)).mul h1
      simpa [Real.sqrt_zero] using h2
    · intro x y i
      have hxy : dist x y = |((x : X) : ℝ) - ((y : X) : ℝ)| := by
        rw [Subtype.dist_eq (x := x) (y := y),
            Subtype.dist_eq (x := (x : X)) (y := (y : X)), Real.dist_eq]
      rw [hxy]
      exact hholder j i ((x : X) : ℝ) ((y : X) : ℝ)
        ⟨Set.mem_Ici.mp (x : X).2, hj (x : K) x.2⟩
        ⟨Set.mem_Ici.mp (y : X).2, hj (y : K) y.2⟩
  obtain ⟨φ, hφ, G', hTLU⟩ :=
    exists_strictMono_tendstoLocallyUniformlyOn_of_equicontinuous_bounded hbdd heq
  -- The limit is continuous.
  have hG'cont : Continuous G' := by
    have hcont' : ∀ n, ContinuousOn (fun x : X => f (φ n) x) Set.univ := fun n =>
      continuousOn_univ.mpr (continuousOn_iff_continuous_domRestrict.mp (hcont (φ n)))
    have hcc := hTLU.continuousOn (Eventually.of_forall hcont').frequently
    rwa [continuousOn_univ] at hcc
  -- The value at the base point.
  have hG'0 : dist (G' ⟨0, Set.mem_Ici.mpr le_rfl⟩) x₀ = 0 := by
    refine dist_of_const_tendsto (hTLU.tendsto_at (Set.mem_univ _)) (fun n => ?_)
    exact h0 (φ n)
  -- The function on `ℝ`, forced to equal `x₀` at `0`.
  let G : ℝ → F := fun t => if h : 0 < t then G' ⟨t, Set.mem_Ici.mpr (le_of_lt h)⟩ else x₀
  have hG0 : G 0 = x₀ := by
    simp only [G]
    exact dif_neg (lt_irrefl 0)
  have hGg : ∀ x : X, dist (G (x : ℝ)) (G' x) = 0 := by
    intro x
    by_cases hx : 0 < (x : ℝ)
    · have h1 : G (x : ℝ) = G' ⟨(x : ℝ), Set.mem_Ici.mpr (le_of_lt hx)⟩ := by
        simp only [G, dif_pos hx]
      have hsub : (⟨(x : ℝ), Set.mem_Ici.mpr (le_of_lt hx)⟩ : X) = x := Subtype.ext rfl
      rw [h1, hsub, dist_self]
    · have hx0 : (x : ℝ) = 0 := le_antisymm (not_lt.mp hx) (Set.mem_Ici.mp x.2)
      have hGx : G (x : ℝ) = x₀ := by simp only [G, dif_neg hx]
      have hxx : x = ⟨(0 : ℝ), Set.mem_Ici.mpr le_rfl⟩ := Subtype.ext hx0
      rw [hGx, hxx, dist_comm]
      exact hG'0
  refine ⟨φ, hφ, G, ?_, ?_, hG0⟩
  · -- Uniform convergence on each `Icc 0 (T j)`.
    intro j
    have hKcpt : IsCompact {x : X | (x : ℝ) ≤ T j} := by
      rw [Subtype.isCompact_iff]
      have himg : Subtype.val '' {x : X | (x : ℝ) ≤ T j} = Set.Icc (0 : ℝ) (T j) := by
        ext t
        constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨Set.mem_Ici.mp x.2, hx⟩
        · intro ht; exact ⟨⟨t, Set.mem_Ici.mpr ht.1⟩, ht.2, rfl⟩
      rw [himg]; exact isCompact_Icc
    have hUK : TendstoUniformlyOn (fun i => f (φ i)) G' atTop {x : X | (x : ℝ) ≤ T j} :=
      (tendstoLocallyUniformly_iff_forall_isCompact.mp
        (tendstoLocallyUniformlyOn_univ.mp hTLU)) _ hKcpt
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hmain := (Metric.tendstoUniformlyOn_iff.mp hUK) ε hε
    filter_upwards [hmain] with k hk
    intro x hx
    have hxK : (⟨x, hx.1⟩ : X) ∈ {x : X | (x : ℝ) ≤ T j} := hx.2
    have h1 : dist (G x) (G' ⟨x, hx.1⟩) = 0 := hGg ⟨x, hx.1⟩
    have h2 := hk ⟨x, hx.1⟩ hxK
    calc dist (G x) (u (φ k) x)
        = dist (G x) (f (φ k) ⟨x, hx.1⟩) := rfl
      _ ≤ dist (G x) (G' ⟨x, hx.1⟩) + dist (G' ⟨x, hx.1⟩) (f (φ k) ⟨x, hx.1⟩) :=
            dist_triangle _ _ _
      _ = dist (G' ⟨x, hx.1⟩) (f (φ k) ⟨x, hx.1⟩) := by rw [h1, zero_add]
      _ < ε := h2
  · -- Continuity of `G` on the half-line.
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hG'cont.continuousAt ε hε
    refine ⟨δ, hδpos, fun a ha hab => ?_⟩
    have h1 : dist (G a) (G' ⟨a, ha⟩) = 0 := hGg ⟨a, ha⟩
    have h2 : dist (G' ⟨b, hb⟩) (G b) = 0 := by rw [dist_comm]; exact hGg ⟨b, hb⟩
    have h3 : dist (G' ⟨a, ha⟩) (G' ⟨b, hb⟩) < ε := by
      apply hδ
      rw [Subtype.dist_eq]
      exact hab
    calc dist (G a) (G b)
        ≤ dist (G a) (G' ⟨a, ha⟩) + dist (G' ⟨a, ha⟩) (G b) := dist_triangle _ _ _
      _ ≤ dist (G a) (G' ⟨a, ha⟩)
            + (dist (G' ⟨a, ha⟩) (G' ⟨b, hb⟩) + dist (G' ⟨b, hb⟩) (G b)) := by
            gcongr; exact dist_triangle _ _ _
      _ = dist (G' ⟨a, ha⟩) (G' ⟨b, hb⟩) := by rw [h1, h2]; ring
      _ < ε := h3

end Commons.Topology.Metric