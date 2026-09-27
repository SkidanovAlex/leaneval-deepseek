import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.H0_fibre_defs
import Submission.Work.EQ.chain_eq_fan_word
import Submission.Work.EQ.chainWord_eventually_true_pos
import Submission.Work.EQ.chainWord_eventually_true_neg
import Submission.Work.EQ.countable_eventually_true_words

/-!
# The `ψ₁`-fibre of `H0` is countable

Every chain of `H0` is determined by its *branch word* `chainWord a p : ℤ → Bool` together with
its stable parameter `ψ₁` (`Work.EQ.H0_fibre_defs`): this file proves that the map
`p ↦ chainWord a p` is injective on each `ψ₁`-fibre of `H0`, and that the words that occur there
are eventually `true` in both directions, whence the fibre is caught by a countable set of words.

* `Work.EQ.isChain_of_mem_H0` (`Submission/Work/EQ/StableTailDefs.lean`): a member of `H0` is an
  `IsChain`.
* `exists_injOn_ugermC`: the unstable germ is injective near `0`.
* `Work.EQ.chain_eq_fan_word`: a chain is the fan read off its branch word.
* `Work.EQ.chainWord_eventually_true_pos`, `Work.EQ.chainWord_eventually_true_neg`: the branch
  word is eventually the principal one on each side.
* `Work.EQ.countable_eventually_true_words`: the set of such words is countable.
-/

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

/-- **The unstable germ is injective near the origin.**  `ugermC a h = eqMirror ∘ germC a h`, and
the `y`-coordinate of `germC` is a local coordinate (`germC_facts`). -/
theorem exists_injOn_ugermC {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ρ : ℝ, 0 < ρ ∧ Set.InjOn (ugermC a h) (Metric.ball (0 : ℂ) ρ) := by
  obtain ⟨ρ, hρ, -, -, -, hInjY, -⟩ := germC_facts ha0 ha1 hh
  refine ⟨ρ, hρ, fun x hx y hy hxy => ?_⟩
  have h2 : (germC a h x).2 = (germC a h y).2 := by
    have h := congrArg Prod.snd hxy
    simpa [ugermC, eqMirror] using h
  exact hInjY hx hy h2

/-- **The `ψ₁`-fibre of `H0` is countable.**  For fixed `u` there are only countably many chains
of `H0` with `ψ₁ = u`: a chain is determined by `u` together with its two "branch words"
(which branch is taken at each step, forward from index `0` and backward from index `0`), and both
words are eventually `true` because both tails of a chain are eventually the canonical germ tails.
This is what makes `H0` a countable spread over `ℂ*`, hence second countable, hence have only
countably many components, hence only countably many regular values (Rychlik's Thm 11 step (141)).

Route (no F3 needed):
* `Work.EQ.H0_invParam_ge_exists_invBranch`: for a `RegPair` the backward point is one of the two
  `invBranch` values; `Work.EQ.germC_facts` gives `RegPair a (germC u) (germC (λu))` and
  `invBranch a true (germC (λu)) = germC u` on a small ball, so along the (eventual) canonical
  tails the branch word is eventually `true` on both sides.
* A word `σ : ℕ → Bool` that is `true` for all `n ≥ N` is determined by `σ 0, …, σ (N-1)`, so the
  set of eventually-true words is countable (a countable union of finite images).
* An injection of the fibre into `(eventually true words) × (eventually true words)`: given the
  forward word, the signs determine `p.1 1, p.1 2, …` from `p.1 0` and the backward word determines
  `p.1 (-1), p.1 (-2), …` from `p.1 0`; hence the whole chain. -/
theorem H0_countable_fibre {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (u : ℂ) :
    ({p : ChainData | p ∈ H0 a h ∧ p.2.1 = u} : Set ChainData).Countable := by
  classical
  -- the countable set of words that are eventually `true` in both directions
  set W : Set (ℤ → Bool) := {σ : ℤ → Bool | ∃ M : ℕ, (∀ n : ℤ, (M : ℤ) ≤ n → σ n = true) ∧
      (∀ n : ℤ, n ≤ -((M : ℤ)) → σ n = true)} with hW
  have hWc : W.Countable := countable_eventually_true_words
  set F : Set ChainData := {p : ChainData | p ∈ H0 a h ∧ p.2.1 = u} with hF
  -- every branch word of the fibre lies in `W`
  have hmemW : ∀ p ∈ F, chainWord a p ∈ W := by
    intro p hp
    rw [hF] at hp
    obtain ⟨hp0, -⟩ := hp
    have hpc : IsChain a h p := isChain_of_mem_H0 hp0
    obtain ⟨N, hN⟩ := chainWord_eventually_true_pos ha0 ha1 hh hpc
    obtain ⟨M, hM⟩ := chainWord_eventually_true_neg ha0 ha1 hh hpc
    refine ⟨max N M, ?_, ?_⟩
    · intro n hn
      exact hN n (le_trans (by exact_mod_cast le_max_left N M) hn)
    · intro n hn
      exact hM n (le_trans hn (neg_le_neg (by exact_mod_cast le_max_right N M)))
  -- the branch word determines the chain inside the fibre
  have hinj : ∀ p ∈ F, ∀ q ∈ F, chainWord a p = chainWord a q → p = q := by
    intro p hp q hq hw
    rw [hF] at hp hq
    obtain ⟨hp0, hpu⟩ := hp
    obtain ⟨hq0, hqu⟩ := hq
    have hpc : IsChain a h p := isChain_of_mem_H0 hp0
    have hqc : IsChain a h q := isChain_of_mem_H0 hq0
    obtain ⟨Np, hNp⟩ := isChain_tail_fwd_z hpc
    obtain ⟨Nq, hNq⟩ := isChain_tail_fwd_z hqc
    set N : ℤ := max (Np : ℤ) (Nq : ℤ) with hNdef
    have hNp' : ∀ n : ℤ, N ≤ n → p.1 n = germC a h ((eqLam a : ℂ) ^ n * p.2.1) :=
      fun n hn => hNp n (le_trans (le_max_left _ _) hn)
    have hNq' : ∀ n : ℤ, N ≤ n → q.1 n = germC a h ((eqLam a : ℂ) ^ n * q.2.1) :=
      fun n hn => hNq n (le_trans (le_max_right _ _) hn)
    -- nonnegative indices: both are fan values with the same word and the same parameter
    have hpos : ∀ k : ℤ, 0 ≤ k → p.1 k = q.1 k := by
      intro k _hk
      obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = max N (k + 1) - k := by
        have hzero : (0 : ℤ) ≤ max N (k + 1) - k := by omega
        exact ⟨(max N (k + 1) - k).toNat, Int.toNat_of_nonneg hzero⟩
      have hEk : N ≤ k + (j : ℤ) := by omega
      have h1 : p.1 k = fan a h (fanWord (chainWord a p) k j) ((eqLam a : ℂ) ^ k * p.2.1) :=
        chain_eq_fan_word ha0 ha1 hpc hNp' j k hEk
      have h2 : q.1 k = fan a h (fanWord (chainWord a q) k j) ((eqLam a : ℂ) ^ k * q.2.1) :=
        chain_eq_fan_word ha0 ha1 hqc hNq' j k hEk
      rw [h1, h2, hw, hpu, hqu]
    -- negative indices: descend by the backward branch recursion
    have hneg : ∀ m : ℕ, p.1 (-(m : ℤ)) = q.1 (-(m : ℤ)) := by
      intro m
      induction m with
      | zero => simpa using hpos 0 le_rfl
      | succ m ih =>
        have h1 : p.1 (-(((m + 1 : ℕ)) : ℤ)) =
            invBranch a (chainWord a p (-(((m + 1 : ℕ)) : ℤ))) (p.1 (-((m : ℕ) : ℤ))) := by
          have h := chainWord_spec hpc (-(((m + 1 : ℕ)) : ℤ))
          rwa [show -(((m + 1 : ℕ)) : ℤ) + 1 = -((m : ℕ) : ℤ) by push_cast; ring] at h
        have h2 : q.1 (-(((m + 1 : ℕ)) : ℤ)) =
            invBranch a (chainWord a q (-(((m + 1 : ℕ)) : ℤ))) (q.1 (-((m : ℕ) : ℤ))) := by
          have h := chainWord_spec hqc (-(((m + 1 : ℕ)) : ℤ))
          rwa [show -(((m + 1 : ℕ)) : ℤ) + 1 = -((m : ℕ) : ℤ) by push_cast; ring] at h
        rw [h1, h2, hw, ih]
    have hfst : p.1 = q.1 := by
      funext n
      rcases le_total 0 n with hn | hn
      · exact hpos n hn
      · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := by
          have hnn : (0 : ℤ) ≤ -n := by omega
          exact ⟨(-n).toNat, by rw [Int.toNat_of_nonneg hnn]; ring⟩
        rw [hm]
        exact hneg m
    -- the backward parameters agree: compare the backward tails at a large index
    have hsnd : p.2.2 = q.2.2 := by
      have hlam0 : 0 < eqLam a := by rw [eqLam]; positivity
      have hlam1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
      obtain ⟨ρ, hρ, hinjU⟩ := exists_injOn_ugermC ha0 ha1 hh
      have htp : Tendsto (fun k : ℕ => eqLam a ^ k * ‖p.2.2‖) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const ‖p.2.2‖
      have htq : Tendsto (fun k : ℕ => eqLam a ^ k * ‖q.2.2‖) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const ‖q.2.2‖
      obtain ⟨Kp, hKp⟩ :=
        (htp.eventually (eventually_lt_nhds hρ)).exists
      obtain ⟨Kq, hKq⟩ :=
        (htq.eventually (eventually_lt_nhds hρ)).exists
      obtain ⟨Mp, hMp⟩ := eventually_atTop.1 hpc.2.2.2.2
      obtain ⟨Mq, hMq⟩ := eventually_atTop.1 hqc.2.2.2.2
      set k : ℕ := max (max (max Kp Kq) Mp) Mq with hk
      have hkKp : Kp ≤ k := by omega
      have hkKq : Kq ≤ k := by omega
      have hkMp : Mp ≤ k := by omega
      have hkMq : Mq ≤ k := by omega
      have hnormp : ‖(eqLam a : ℂ) ^ k * p.2.2‖ = eqLam a ^ k * ‖p.2.2‖ := by
        rw [norm_mul, norm_pow]
        simp [abs_of_pos hlam0]
      have hnormq : ‖(eqLam a : ℂ) ^ k * q.2.2‖ = eqLam a ^ k * ‖q.2.2‖ := by
        rw [norm_mul, norm_pow]
        simp [abs_of_pos hlam0]
      have hkp : ‖(eqLam a : ℂ) ^ k * p.2.2‖ < ρ := by
        rw [hnormp]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hlam0.le hlam1.le hkKp) (norm_nonneg _)) hKp
      have hkq : ‖(eqLam a : ℂ) ^ k * q.2.2‖ < ρ := by
        rw [hnormq]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hlam0.le hlam1.le hkKq) (norm_nonneg _)) hKq
      have h1 : p.1 (-(k : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ k * p.2.2) := hMp k hkMp
      have h2 : q.1 (-(k : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ k * q.2.2) := hMq k hkMq
      have h3 : ugermC a h ((eqLam a : ℂ) ^ k * p.2.2)
          = ugermC a h ((eqLam a : ℂ) ^ k * q.2.2) := by
        rw [← h1, ← h2, hfst]
      have h4 : (eqLam a : ℂ) ^ k * p.2.2 = (eqLam a : ℂ) ^ k * q.2.2 :=
        hinjU (by simpa [Metric.mem_ball, dist_eq_norm] using hkp)
          (by simpa [Metric.mem_ball, dist_eq_norm] using hkq) h3
      exact mul_left_cancel₀ (pow_ne_zero k (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0))) h4
    refine Prod.ext hfst ?_
    exact Prod.ext (hpu.trans hqu.symm) hsnd
  -- the fibre injects into the countable set of words
  have hFcount : F.Countable := by
    rw [← Set.countable_coe_iff]
    haveI : Countable ↥W := Set.countable_coe_iff.mpr hWc
    refine Function.Injective.countable
      (f := fun p : ↥F => (⟨chainWord a p.1, hmemW p.1 p.2⟩ : ↥W)) ?_
    intro p q hpq
    have hw : chainWord a p.1 = chainWord a q.1 := by
      have h := congrArg Subtype.val hpq
      simpa using h
    exact Subtype.ext (hinj p.1 p.2 q.1 q.2 hw)
  exact hFcount

end

end Work.EQ
