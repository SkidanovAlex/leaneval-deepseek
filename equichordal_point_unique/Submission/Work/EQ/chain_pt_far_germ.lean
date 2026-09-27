import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.germC_leaf
import Submission.Work.EQ.fan_ne_germC

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

/-! ## Pieces of the reduction to the fan separation

The reduction has two steps.

* *The word reading a chain strictly below its tail index ends in the non-principal letter.*
  Reading the chain `q` between the levels `n < N = tailIdx a h q` as a branch word `ε`
  (`q.1 n = fan a h ε (λⁿ ψ₁ q)`, the shifted form of `Work.EQ.chain_eq_fan`) we show
  `ε.getLast? = some false`: the letter of the *last* step `N-1 → N` is `invBranch a true` only
  if `q.1 (N-1) = germC a h (λ^{N-1} ψ₁)`, which is exactly the minimality of `N`
  (`Work.EQ.germC_leaf` identifies the principal branch).  The remaining letters are peeled off
  the head of the word, at each step using `Work.EQ.H0_invParam_ge_exists_invBranch` to read the
  branch of the regular pair `(q.1 n, q.1 (n+1))`.

* *Separation.*  `Work.EQ.fan_ne_germC` then bounds `fan a h ε v` away from `germC a h v` by
  `c ‖v‖` uniformly in the word, and it is applied at `v = λⁿ ψ₁ q`. -/

/-- The weight of one more factor `λ` is at most one: `‖λ^{n+1} z‖ ≤ ‖λ^n z‖` for `0 < a < 1`. -/
lemma norm_lam_succ_le (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) (z : ℂ) :
    ‖(eqLam a : ℂ) ^ (n + 1) * z‖ ≤ ‖(eqLam a : ℂ) ^ n * z‖ := by
  have hlam0 : (0 : ℝ) < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hsplit : (eqLam a : ℂ) ^ (n + 1) * z = (eqLam a : ℂ) * ((eqLam a : ℂ) ^ n * z) := by
    rw [pow_succ]; ring
  rw [hsplit, norm_mul]
  have hn : ‖((eqLam a : ℝ) : ℂ)‖ = eqLam a := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hlam0.le]
  rw [hn]
  exact mul_le_of_le_one_left (norm_nonneg _) hlam1.le

/-- **The branch of the last step below the tail index is the non-principal one.**  If `q` is a
chain, `q.1 (n+1)` lies on the principal leaf, `q.1 n` does not, and `λⁿ ψ₁ q` is small enough
for the principal branch to invert the germ, then `q.1 n = invBranch a false (q.1 (n+1))`. -/
lemma chain_step_branch_false {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {dl : ℝ}
    (hleaf : ∀ u : ℂ, ‖u‖ < dl →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    {q : ChainData} (hq : IsChain a h q) {n : ℕ}
    (hfun : q.1 ((n + 1 : ℕ) : ℤ) = germC a h ((eqLam a : ℂ) ^ (n + 1) * q.2.1))
    (hne : q.1 (n : ℤ) ≠ germC a h ((eqLam a : ℂ) ^ n * q.2.1))
    (hsmall : ‖(eqLam a : ℂ) ^ n * q.2.1‖ < dl) :
    q.1 (n : ℤ) = invBranch a false (q.1 ((n + 1 : ℕ) : ℤ)) := by
  have hreg : RegPair a (q.1 (n : ℤ)) (q.1 ((n : ℤ) + 1)) := hq.1 (n : ℤ)
  have hidx : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hidx] at hreg
  rcases H0_invParam_ge_exists_invBranch hreg.1 hreg.2.2 with h | h
  · exfalso
    have harg : (eqLam a : ℂ) ^ (n + 1) * q.2.1 =
        (eqLam a : ℂ) * ((eqLam a : ℂ) ^ n * q.2.1) := by rw [pow_succ]; ring
    rw [h, hfun, harg] at hne
    exact hne (hleaf _ hsmall)
  · exact h

/-- **A chain strictly below its tail index is a fan value of a word ending in `false`.**  For a
chain `q`, a level `n` and a tail level `N = n + k` from which `q` follows the principal leaf,
with `q.1 (N-1) ≠ germC a h (λ^{N-1} ψ₁)` (the minimality of the tail index), the word of the
`k` steps from `n` to `N` ends in the non-principal letter. -/
lemma chain_word_last_false {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {dl : ℝ}
    (hleaf : ∀ u : ℂ, ‖u‖ < dl →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    {q : ChainData} (hq : IsChain a h q) :
    ∀ k n N : ℕ, n + k = N → 0 < k → TailP a h q N →
      q.1 ((N - 1 : ℕ) : ℤ) ≠ germC a h ((eqLam a : ℂ) ^ (N - 1) * q.2.1) →
      ‖(eqLam a : ℂ) ^ n * q.2.1‖ < dl →
      ∃ ε : List Bool, ε.length = k ∧ q.1 (n : ℤ) = fan a h ε ((eqLam a : ℂ) ^ n * q.2.1) ∧
        ε.getLast? = some false := by
  intro k
  induction k with
  | zero =>
      intro n N _ hk _ _ _
      exact absurd hk (lt_irrefl 0)
  | succ k ih =>
      intro n N hnN hk htail hne hsmall
      have harg : (eqLam a : ℂ) ^ (n + 1) * q.2.1 =
          (eqLam a : ℂ) * ((eqLam a : ℂ) ^ n * q.2.1) := by rw [pow_succ]; ring
      by_cases hk0 : k = 0
      · -- the last step: the word is `[false]`
        have hN1 : N = n + 1 := by omega
        have hfun : q.1 ((n + 1 : ℕ) : ℤ) =
            germC a h ((eqLam a : ℂ) ^ (n + 1) * q.2.1) := htail (n + 1) (by omega)
        have hne' : q.1 (n : ℤ) ≠ germC a h ((eqLam a : ℂ) ^ n * q.2.1) := by
          have hidxN : N - 1 = n := by omega
          rwa [hidxN] at hne
        have hbr := chain_step_branch_false ha0 ha1 hh hleaf hq hfun hne' hsmall
        have hval : q.1 (n : ℤ) = fan a h [false] ((eqLam a : ℂ) ^ n * q.2.1) := by
          rw [hbr, hfun, harg]
          rfl
        refine ⟨[false], ?_, hval, ?_⟩
        · simp [hk0]
        · simp
      · -- peel off the head letter
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hsmall' : ‖(eqLam a : ℂ) ^ (n + 1) * q.2.1‖ < dl :=
          lt_of_le_of_lt (norm_lam_succ_le a ha0 ha1 n q.2.1) hsmall
        have hreg : RegPair a (q.1 (n : ℤ)) (q.1 ((n : ℤ) + 1)) := hq.1 (n : ℤ)
        have hidx : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [hidx] at hreg
        obtain ⟨ε', hlen, hval', hlast⟩ := ih (n + 1) N (by omega) hkpos htail hne hsmall'
        have hne' : ε' ≠ [] := by
          intro hc
          rw [hc] at hlen
          simp only [List.length_nil] at hlen
          omega
        rcases H0_invParam_ge_exists_invBranch hreg.1 hreg.2.2 with hb | hb
        · refine ⟨true :: ε', ?_, ?_, ?_⟩
          · simp [hlen]
          · rw [hb, hval', harg]; rfl
          · rw [List.getLast?_cons_of_ne_nil hne']; exact hlast
        · refine ⟨false :: ε', ?_, ?_, ?_⟩
          · simp [hlen]
          · rw [hb, hval', harg]; rfl
          · rw [List.getLast?_cons_of_ne_nil hne']; exact hlast

/-- **A chain strictly below its tail index is bounded away from the principal leaf.**  If `q` is
a chain whose forward tail is the germ from some index on (`IsChain`), `n` is strictly below the
tail index `tailIdx a h q`, and the parameter `λⁿ ψ₁ q` is small, then `q.1 n` differs from the
germ point `germC a h (λⁿ ψ₁ q)` by at least `c ‖λⁿ ψ₁ q‖` — uniformly in `q` and `n`.

Route.  Put `N := tailIdx a h q`, so `q.1 N = germC a h (λ^N ψ₁)` and, by minimality,
`q.1 (N-1) ≠ germC a h (λ^{N-1} ψ₁)`; since `IsChain` gives `RegPair` at every step, `q.1 (N-1)` is
one of the two backward branches `invBranch a s (germC a h (λ^N ψ₁))`, and the principal one is
`germC a h (λ^{N-1}ψ₁)` (`Work.EQ.germC_leaf` gives this near `0`; the hypothesis `‖λⁿ ψ₁ q‖ < δ`
makes `λ^{N-1}ψ₁` small too since `λ < 1` and `N - 1 ≥ n`), so `s = false`.  Reading the steps
backwards gives `q.1 n = fan a h ε (λⁿ ψ₁ q)` with `ε` the word of the branches
`n, …, N-1` (its *last* letter being `false`, `chain_eq_fan_len` in
`Submission.Work.EQ.exists_compact_regular_cycle` supplies the length); the separation statement
`Work.EQ.fan_ne_germC` (in `Submission.Work.EQ.fan_ne_germC`, same route as this file: a word
ending in `false` is uniformly separated from `germC a h v`) then applies with `v = λⁿ ψ₁ q`. -/
theorem chain_pt_far_germ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ {q : ChainData} {n : ℕ}, Work.EQ.IsChain a h q →
      n < Work.EQ.tailIdx a h q → ‖(Work.EQ.eqLam a : ℂ) ^ n * q.2.1‖ < δ →
      c * ‖(Work.EQ.eqLam a : ℂ) ^ n * q.2.1‖ ≤
        ‖q.1 (n : ℤ) - Work.EQ.germC a h ((Work.EQ.eqLam a : ℂ) ^ n * q.2.1)‖ := by
  obtain ⟨δf, cf, hδf0, hcf0, hsep⟩ := fan_ne_germC ha0 ha1 hh
  obtain ⟨δl, hδl0, hleaf⟩ := (germC_leaf ha0 ha1 hh).2.2.2
  have hleaf' : ∀ u : ℂ, ‖u‖ < δl →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u :=
    fun u hu => hleaf u (by rw [Metric.mem_ball, dist_zero_right]; exact hu)
  refine ⟨min δf δl, cf, lt_min hδf0 hδl0, hcf0, ?_⟩
  intro q n hq hn hsmall
  set N : ℕ := tailIdx a h q with hNdef
  have hex : ∃ N' : ℕ, TailP a h q N' := tailP_of_isChain hq
  have htail : TailP a h q N := TailP_of_isChain hq
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le n) hn
  have hne : q.1 ((N - 1 : ℕ) : ℤ) ≠ germC a h ((eqLam a : ℂ) ^ (N - 1) * q.2.1) := by
    intro heq
    have hcontra : TailP a h q (N - 1) := by
      intro m hm
      rcases eq_or_lt_of_le hm with h | h
      · rw [← h]; exact heq
      · exact htail m (by omega)
    have hle : tailIdx a h q ≤ N - 1 := tailIdx_le hex hcontra
    rw [hNdef] at hle
    omega
  have hready : n + (N - n) = N := by omega
  have hsmall' : ‖(eqLam a : ℂ) ^ n * q.2.1‖ < δl := lt_of_lt_of_le hsmall (min_le_right _ _)
  obtain ⟨ε, hlen, hval, hlast⟩ :=
    chain_word_last_false ha0 ha1 hh hleaf' hq (N - n) n N hready (by omega) htail hne hsmall'
  have hdiff := hsep ε hlast ((eqLam a : ℂ) ^ n * q.2.1) (lt_of_lt_of_le hsmall (min_le_left _ _))
  calc cf * ‖(eqLam a : ℂ) ^ n * q.2.1‖
      ≤ ‖fan a h ε ((eqLam a : ℂ) ^ n * q.2.1) - germC a h ((eqLam a : ℂ) ^ n * q.2.1)‖ := hdiff
    _ = ‖q.1 (n : ℤ) - germC a h ((eqLam a : ℂ) ^ n * q.2.1)‖ := by rw [hval]

end

end Work.EQ
