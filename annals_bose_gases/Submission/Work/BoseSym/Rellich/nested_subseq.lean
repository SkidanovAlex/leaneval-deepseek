import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Nested-subsequence extraction (`Work.BoseSym.Rellich.nested_subseq`)

This file proves the diagonal-extraction lemma used by the Rellich compactness
assembly (`Submission/Work/BoseSym/Rellich/rellich.lean`).

Given a pseudo-metric space `X`, a sequence `x : ℕ → X` approximated along the
index by a doubly indexed family `y : ℕ → ℕ → X`,
`dist (x n) (y k n) ≤ ε k` with `ε k → 0`, and the *compactness-type* hypothesis
that for every `k` and every strictly monotone `ρ` the sequence `m ↦ y k (ρ m)`
has a Cauchy subsequence, we must produce a strictly monotone `ψ` with
`CauchySeq (x ∘ ψ)`.

The proof is the classical nested-diagonal argument:

* starting from the identity and using `hsub` at stage `k` on the current
  subsequence `σ k`, build a nested chain `σ (k+1) = σ k ∘ θ k` such that
  `y k ∘ σ (k+1)` is Cauchy;
* consequently `x ∘ σ (k+1)` is Cauchy up to the constant error `2 * ε k`
  (triangle inequality);
* the diagonal `k ↦ σ k k` is strictly monotone, and any two of its terms with
  index `≥ max K N` lie beyond position `N` in the `K`-th chain, where the
  `K`-th chain is eventually Cauchy up to `2 * ε K + δ`; since `ε K → 0` we are
  done.
-/

namespace Work.BoseSym.Rellich

/-- Recursive construction of a nested chain of strictly monotone maps: the
`0`-th map is the identity and `chainRec step (k+1) = step k (chainRec step k)`.
Carrying the strict-monotonicity proof in the subtype makes the recursive
dependency legal. -/
noncomputable def chainRec
    (step : ℕ → {f : ℕ → ℕ // StrictMono f} → {f : ℕ → ℕ // StrictMono f}) :
    ℕ → {f : ℕ → ℕ // StrictMono f} :=
  Nat.rec ⟨id, strictMono_id⟩ step

/-- **Nesting.**  If `σ` is a nested chain of strictly monotone maps,
`σ (k+1) = σ k ∘ θ k`, then for `k ≤ j` the map `σ j` is `σ k` composed with a
strictly monotone map `Θ` which moreover satisfies `n ≤ Θ n`. -/
theorem exists_comp_of_le {σ : ℕ → {f : ℕ → ℕ // StrictMono f}}
    (hσ : ∀ k, ∃ θ : ℕ → ℕ, StrictMono θ ∧ (σ (k+1)).1 = (σ k).1 ∘ θ) :
    ∀ k j : ℕ, k ≤ j → ∃ Θ : ℕ → ℕ, StrictMono Θ ∧ (∀ n, n ≤ Θ n) ∧
      (σ j).1 = (σ k).1 ∘ Θ := by
  intro k j hk
  induction j with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      exact ⟨id, strictMono_id, fun n => le_refl n, by ext n; rfl⟩
  | succ j ih =>
      rcases Nat.lt_or_eq_of_le hk with hlt | heq
      · have hkj : k ≤ j := Nat.lt_succ_iff.mp hlt
        obtain ⟨Θ, hΘ, hΘle, hΘeq⟩ := ih hkj
        obtain ⟨θ, hθ, hσθ⟩ := hσ j
        refine ⟨Θ ∘ θ, hΘ.comp hθ, fun n => le_trans (hθ.id_le n) (hΘle (θ n)), ?_⟩
        rw [hσθ, hΘeq]
        ext n; rfl
      · subst heq
        exact ⟨id, strictMono_id, fun n => le_refl n, by ext n; rfl⟩

/-- **Monotonicity of the diagonal.**  The diagonal `k ↦ σ k k` of a nested
chain of strictly monotone maps is strictly monotone. -/
theorem diag_strictMono {σ : ℕ → {f : ℕ → ℕ // StrictMono f}}
    (hσ : ∀ k, ∃ θ : ℕ → ℕ, StrictMono θ ∧ (σ (k+1)).1 = (σ k).1 ∘ θ) :
    StrictMono fun k => (σ k).1 k := by
  apply strictMono_nat_of_lt_succ
  intro k
  obtain ⟨θ, hθ, hσθ⟩ := hσ k
  have h1 : (σ (k+1)).1 (k+1) = (σ k).1 (θ (k+1)) := by rw [hσθ]; rfl
  have h2 : k < θ (k+1) := lt_of_lt_of_le (Nat.lt_succ_self k) (hθ.id_le (k+1))
  rw [h1]
  exact (σ k).2 h2

/-- **Abstract diagonal extraction.**  If `u (k+1)` is a subsequence of `u k`
(coherently, through `θ k`) and each `u k` is eventually Cauchy up to the
constant error `c k`, with `c k → 0`, then `u 0` has a Cauchy subsequence. -/
theorem diagonal_of_nested {X : Type*} [PseudoMetricSpace X]
    {u : ℕ → ℕ → X} {c : ℕ → ℝ}
    (hc : Filter.Tendsto c Filter.atTop (nhds 0))
    (hsub : ∀ k, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ n, u (k+1) n = u k (θ n))
    (hC : ∀ k, ∀ δ > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u k m) (u k n) ≤ c k + δ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ CauchySeq (u 0 ∘ ψ) := by
  choose θ hθ hθeq using hsub
  let step : ℕ → {f : ℕ → ℕ // StrictMono f} → {f : ℕ → ℕ // StrictMono f} :=
    fun j p => ⟨p.1 ∘ θ j, p.2.comp (hθ j)⟩
  let σ : ℕ → {f : ℕ → ℕ // StrictMono f} := chainRec step
  have hσeq : ∀ k, (σ (k+1)).1 = (σ k).1 ∘ θ k := by
    intro k
    show (chainRec step (k+1)).1 = (chainRec step k).1 ∘ θ k
    rfl
  have hσ' : ∀ k, ∃ θ' : ℕ → ℕ, StrictMono θ' ∧ (σ (k+1)).1 = (σ k).1 ∘ θ' :=
    fun k => ⟨θ k, hθ k, hσeq k⟩
  have hu : ∀ k, u k = u 0 ∘ (σ k).1 := by
    intro k
    induction k with
    | zero =>
        show u 0 = u 0 ∘ (chainRec step 0).1
        rw [show (chainRec step 0).1 = id from rfl]
        ext n; rfl
    | succ k ih =>
        funext n
        calc u (k+1) n = u k (θ k n) := hθeq k n
          _ = u 0 ((σ k).1 (θ k n)) := by rw [ih]; rfl
          _ = u 0 ((σ (k+1)).1 n) := by rw [hσeq k]; rfl
  refine ⟨fun k => (σ k).1 k, diag_strictMono hσ', ?_⟩
  rw [Metric.cauchySeq_iff]
  intro δ hδ
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hc) (δ/2) (by linarith)
  have hcK : c K < δ/2 := by
    have h1 : dist (c K) 0 < δ/2 := hK K le_rfl
    have h2 : |c K| < δ/2 := by simpa using h1
    exact lt_of_le_of_lt (le_abs_self (c K)) h2
  obtain ⟨N, hN⟩ := hC K (δ/2) (by linarith)
  refine ⟨max K N, fun m hm n hn => ?_⟩
  obtain ⟨Θm, hΘm, hΘmle, hΘmeq⟩ := exists_comp_of_le hσ' K m (le_of_max_le_left hm)
  obtain ⟨Θn, hΘn, hΘnle, hΘneq⟩ := exists_comp_of_le hσ' K n (le_of_max_le_left hn)
  have hmN : N ≤ Θm m := le_trans (le_max_right K N) (le_trans hm (hΘmle m))
  have hnN : N ≤ Θn n := le_trans (le_max_right K N) (le_trans hn (hΘnle n))
  have hleft : (u 0 ∘ fun k => (σ k).1 k) m = u K (Θm m) := by
    show u 0 ((σ m).1 m) = u K (Θm m)
    have h1 : (σ m).1 m = (σ K).1 (Θm m) := by rw [hΘmeq]; rfl
    rw [h1]
    exact congrFun (hu K).symm (Θm m)
  have hright : (u 0 ∘ fun k => (σ k).1 k) n = u K (Θn n) := by
    show u 0 ((σ n).1 n) = u K (Θn n)
    have h1 : (σ n).1 n = (σ K).1 (Θn n) := by rw [hΘneq]; rfl
    rw [h1]
    exact congrFun (hu K).symm (Θn n)
  rw [hleft, hright]
  have := hN (Θm m) hmN (Θn n) hnN
  linarith

/-- Triangle-inequality estimate: along a subsequence on which `y k` is Cauchy,
the tracked sequence `x` is eventually Cauchy up to the constant error
`2 * ε k`. -/
theorem cauchy_along_approx {X : Type*} [PseudoMetricSpace X]
    {x : ℕ → X} {y : ℕ → ℕ → X} {ε : ℕ → ℝ}
    (happrox : ∀ k n, dist (x n) (y k n) ≤ ε k)
    (k : ℕ) (σ : ℕ → ℕ) (hc : CauchySeq fun m => y k (σ m)) :
    ∀ δ > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (x (σ m)) (x (σ n)) ≤ 2 * ε k + δ := by
  intro δ hδ
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc δ hδ
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 : dist (x (σ m)) (y k (σ m)) ≤ ε k := happrox k (σ m)
  have h2 : dist (y k (σ n)) (x (σ n)) ≤ ε k := by
    rw [dist_comm]; exact happrox k (σ n)
  have h3 : dist (y k (σ m)) (y k (σ n)) < δ := hN m hm n hn
  calc dist (x (σ m)) (x (σ n))
      ≤ dist (x (σ m)) (y k (σ m)) + dist (y k (σ m)) (x (σ n)) := dist_triangle ..
    _ ≤ dist (x (σ m)) (y k (σ m)) + (dist (y k (σ m)) (y k (σ n)) + dist (y k (σ n)) (x (σ n))) := by
        gcongr
        exact dist_triangle ..
    _ ≤ ε k + (δ + ε k) := by gcongr
    _ = 2 * ε k + δ := by ring

/-- **Nested-subsequence extraction.**  If `x` is approximated (along the
index) by `y k` up to `ε k → 0`, and every subsequence of every `y k` has a
Cauchy subsequence, then `x` has a Cauchy subsequence. -/
theorem nested_subseq {X : Type*} [PseudoMetricSpace X]
    {x : ℕ → X} {y : ℕ → ℕ → X} {ε : ℕ → ℝ}
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (happrox : ∀ k n, dist (x n) (y k n) ≤ ε k)
    (hsub : ∀ k, ∀ ρ : ℕ → ℕ, StrictMono ρ →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (fun m => y k (ρ (φ m)))) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ CauchySeq (fun m => x (ψ m)) := by
  -- Nested chain `σ` of subsequence maps, with `y k ∘ σ (k+1)` Cauchy.
  let step : ℕ → {f : ℕ → ℕ // StrictMono f} → {f : ℕ → ℕ // StrictMono f} :=
    fun k p => ⟨p.1 ∘ Classical.choose (hsub k p.1 p.2),
      p.2.comp (Classical.choose_spec (hsub k p.1 p.2)).1⟩
  let σ : ℕ → {f : ℕ → ℕ // StrictMono f} := chainRec step
  have hσeq : ∀ k, (σ (k+1)).1 =
      (σ k).1 ∘ Classical.choose (hsub k (σ k).1 (σ k).2) := by
    intro k
    show (chainRec step (k+1)).1 =
      (chainRec step k).1 ∘ Classical.choose (hsub k (chainRec step k).1 (chainRec step k).2)
    rfl
  have hσcau : ∀ k, CauchySeq (fun m => y k ((σ (k+1)).1 m)) := by
    intro k
    have h := (Classical.choose_spec (hsub k (σ k).1 (σ k).2)).2
    have hfun : (fun m => y k ((σ k).1 (Classical.choose (hsub k (σ k).1 (σ k).2) m)))
        = (fun m => y k ((σ (k+1)).1 m)) := by
      funext m
      rw [hσeq k]
      rfl
    rwa [hfun] at h
  have hc : Filter.Tendsto (fun k => 2 * ε k) Filter.atTop (nhds 0) := by
    have h := hε0.const_mul 2
    simpa using h
  have hu_sub : ∀ k, ∃ θ : ℕ → ℕ, StrictMono θ ∧
      ∀ n, x ((σ ((k+1)+1)).1 n) = x ((σ (k+1)).1 (θ n)) := by
    intro k
    refine ⟨Classical.choose (hsub (k+1) (σ (k+1)).1 (σ (k+1)).2),
      (Classical.choose_spec (hsub (k+1) (σ (k+1)).1 (σ (k+1)).2)).1, fun n => ?_⟩
    rw [hσeq (k+1)]
    rfl
  have hC : ∀ k, ∀ δ > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      dist (x ((σ (k+1)).1 m)) (x ((σ (k+1)).1 n)) ≤ 2 * ε k + δ :=
    fun k => cauchy_along_approx happrox k (σ (k+1)).1 (hσcau k)
  obtain ⟨ψ, hψ, hψcau⟩ := diagonal_of_nested
    (u := fun k m => x ((σ (k+1)).1 m)) (c := fun k => 2 * ε k) hc hu_sub hC
  exact ⟨(σ 1).1 ∘ ψ, (σ 1).2.comp hψ, hψcau⟩

end Work.BoseSym.Rellich
