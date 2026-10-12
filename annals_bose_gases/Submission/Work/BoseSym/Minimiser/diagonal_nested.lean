import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Minimiser

/-- Diagonal extraction argument.

Given a sequence `x` in a pseudo metric space that is `ε k`-close to a family of
auxiliary sequences `y k` (`dist (x n) (y k n) ≤ ε k`), where `ε k → 0` and where
each `y k` becomes Cauchy along the "level `k`" subsequence `ω k`, and where the
levels are nested (`ω (k+1) = ω k ∘ θ` for a strictly monotone `θ`), there is a
strictly increasing `ψ` such that `x ∘ ψ` is Cauchy.

Proof: take the diagonal `ψ m = ω m (u m)` where `u m ≥ N m` is chosen so large
that `ω m (u m) > ω (m-1) (u (m-1))`; the nestedness of the ranges of the `ω k`
shows that for `a, b ≥ m` both `ψ a` and `ψ b` lie in the range of `ω m` with
coordinates `≥ N m`, whence the bound `dist (x (ψ a)) (x (ψ b)) ≤ 2 ε m + 1/(m+1)`
which tends to `0`. -/
theorem diagonal_nested {X : Type*} [PseudoMetricSpace X]
    {x : ℕ → X} {y : ℕ → ℕ → X} {ε : ℕ → ℝ} {ω : ℕ → ℕ → ℕ}
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (happrox : ∀ k n, dist (x n) (y k n) ≤ ε k)
    (hωmono : ∀ k, StrictMono (ω k))
    (hωstep : ∀ k, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ω (k + 1) = ω k ∘ θ)
    (hcau : ∀ k, CauchySeq (fun m => y k (ω k m))) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ CauchySeq (fun m => x (ψ m)) := by
  -- (1) The ranges of the `ω k` are nested: `range (ω (k+1)) ⊆ range (ω k)`.
  have hstep : ∀ k, Set.range (ω (k + 1)) ⊆ Set.range (ω k) := by
    intro k
    obtain ⟨θ, _, hθ⟩ := hωstep k
    rintro w ⟨n, rfl⟩
    rw [hθ]
    exact ⟨θ n, rfl⟩
  have hnest : ∀ a b, a ≤ b → Set.range (ω b) ⊆ Set.range (ω a) := by
    intro a b hab
    refine Nat.le_induction (P := fun n _ => Set.range (ω n) ⊆ Set.range (ω a)) ?_ ?_ b hab
    · exact subset_rfl
    · intro n _ ih
      exact fun w hw => ih (hstep n hw)
  -- (2) Cauchy thresholds at each level.
  have hNex : ∀ m, ∃ N : ℕ, ∀ a b, N ≤ a → N ≤ b →
      dist (y m (ω m a)) (y m (ω m b)) < 1 / ((m : ℝ) + 1) := by
    intro m
    obtain ⟨M, hM⟩ := (Metric.cauchySeq_iff.mp (hcau m)) (1 / ((m : ℝ) + 1)) (by positivity)
    exact ⟨M, fun a b ha hb => hM a (ge_iff_le.mpr ha) b (ge_iff_le.mpr hb)⟩
  let N : ℕ → ℕ := fun m => Classical.choose (hNex m)
  have hNspec : ∀ m a b, N m ≤ a → N m ≤ b →
      dist (y m (ω m a)) (y m (ω m b)) < 1 / ((m : ℝ) + 1) :=
    fun m => Classical.choose_spec (hNex m)
  -- (3) Build the diagonal `ψ m = ω m (u m)`.
  let u : ℕ → ℕ := fun m => Nat.rec (N 0) (fun n un => max (N (n + 1)) (ω n un + 1)) m
  have hu0 : u 0 = N 0 := rfl
  have husucc : ∀ m, u (m + 1) = max (N (m + 1)) (ω m (u m) + 1) := fun m => rfl
  let ψ : ℕ → ℕ := fun m => ω m (u m)
  have huN : ∀ m, N m ≤ u m := by
    intro m
    induction m with
    | zero => rw [hu0]
    | succ m _ => rw [husucc m]; exact le_max_left _ _
  have hsucc : ∀ m, u (m + 1) ≤ ω (m + 1) (u (m + 1)) :=
    fun m => StrictMono.id_le (hωmono (m + 1)) (u (m + 1))
  have hψlt : ∀ m, ψ m < ψ (m + 1) := by
    intro m
    have h2 : ψ m + 1 ≤ u (m + 1) := by
      rw [husucc m]
      exact le_max_right _ _
    have h3 : ψ m + 1 ≤ ψ (m + 1) := le_trans h2 (hsucc m)
    exact Nat.lt_of_succ_le h3
  have hψmono : StrictMono ψ := strictMono_nat_of_lt_succ hψlt
  refine ⟨ψ, hψmono, ?_⟩
  -- (4) The key estimate: for `a, b ≥ m`, both `ψ a` and `ψ b` are in the range
  -- of `ω m` with coordinates at least `N m`.
  have hkey : ∀ m a b, m ≤ a → m ≤ b →
      dist (x (ψ a)) (x (ψ b)) ≤ 2 * ε m + 1 / ((m : ℝ) + 1) := by
    intro m a b ha hb
    obtain ⟨p, hp⟩ : ψ a ∈ Set.range (ω m) := hnest m a ha ⟨u a, rfl⟩
    obtain ⟨q, hq⟩ : ψ b ∈ Set.range (ω m) := hnest m b hb ⟨u b, rfl⟩
    have hpa : ψ m ≤ ψ a := hψmono.monotone ha
    have hpb : ψ m ≤ ψ b := hψmono.monotone hb
    have hpN : N m ≤ p := by
      have h : u m ≤ p := by
        apply (hωmono m).le_iff_le.mp
        rw [hp]
        exact hpa
      exact le_trans (huN m) h
    have hqN : N m ≤ q := by
      have h : u m ≤ q := by
        apply (hωmono m).le_iff_le.mp
        rw [hq]
        exact hpb
      exact le_trans (huN m) h
    have h1 : dist (x (ω m p)) (y m (ω m p)) ≤ ε m := happrox m (ω m p)
    have h2 : dist (y m (ω m p)) (y m (ω m q)) ≤ 1 / ((m : ℝ) + 1) :=
      le_of_lt (hNspec m p q hpN hqN)
    have h3 : dist (y m (ω m q)) (x (ω m q)) ≤ ε m := by
      rw [dist_comm]; exact happrox m (ω m q)
    calc dist (x (ψ a)) (x (ψ b))
        = dist (x (ω m p)) (x (ω m q)) := by rw [hp, hq]
      _ ≤ dist (x (ω m p)) (y m (ω m p)) + dist (y m (ω m p)) (y m (ω m q))
            + dist (y m (ω m q)) (x (ω m q)) := dist_triangle4 _ _ _ _
      _ ≤ ε m + 1 / ((m : ℝ) + 1) + ε m := by linarith
      _ = 2 * ε m + 1 / ((m : ℝ) + 1) := by ring
  -- (5) The bound tends to `0`, so `x ∘ ψ` is Cauchy.
  have hbnd : Filter.Tendsto (fun m : ℕ => 2 * ε m + 1 / ((m : ℝ) + 1)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun m : ℕ => 2 * ε m) Filter.atTop (nhds (2 * 0)) :=
      hε0.const_mul 2
    have hcast : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 1)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop (R := ℝ)) tendsto_const_nhds
    have h2 : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
      Filter.Tendsto.congr (fun m => by simp [Pi.inv_apply, one_div]) hcast.inv_tendsto_atTop
    have := h1.add h2
    simpa using this
  rw [Metric.cauchySeq_iff]
  intro δ hδ
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hbnd δ hδ
  refine ⟨M, ?_⟩
  intro a ha b hb
  have h1 := hkey M a b ha hb
  have h2 : dist (2 * ε M + 1 / ((M : ℝ) + 1)) 0 < δ := hM M le_rfl
  rw [Real.dist_eq, sub_zero] at h2
  have h3 : 2 * ε M + 1 / ((M : ℝ) + 1) < δ := lt_of_le_of_lt (le_abs_self _) h2
  linarith

end Work.BoseSym.Minimiser
