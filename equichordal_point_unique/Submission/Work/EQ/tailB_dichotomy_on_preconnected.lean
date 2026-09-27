import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.tail_uniform_of_isPreconnected

namespace Work.EQ

open Filter _root_.Topology Set
open scoped Topology

noncomputable section

set_option maxHeartbeats 3200000

/-- Norm of `λ^m · z`. -/
private lemma norm_eqLam_pow_mulB {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ) (z : ℂ) :
    ‖(eqLam a : ℂ) ^ m * z‖ = (eqLam a) ^ m * ‖z‖ := by
  rw [norm_mul, norm_pow, norm_eqLamC ha0 ha1]

/-- On a preconnected `T ⊆ H0` on which `‖ψ₂‖ ≤ B`, the property "the backward tail is the
principal unstable leaf from level `n` on" is, at every level `n` past a uniform floor `n₀(B)`,
either true at every point of `T` or false at every point of `T`. -/
theorem tailB_dichotomy_on_preconnected {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {B : ℝ} (hB : 0 ≤ B) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ T : Set ChainData, IsPreconnected T → T ⊆ H0 a h →
      (∀ q ∈ T, ‖q.2.2‖ ≤ B) →
      ((∀ q ∈ T, TailB a h q n) ∨ (∀ q ∈ T, ¬ TailB a h q n)) := by
  obtain ⟨ρ, hρ0, hAnC, hC0, hRP, hInjY, hderivY⟩ := germC_facts ha0 ha1 hh
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlam1le : eqLam a ≤ 1 := le_of_lt hlam1
  -- a level `n₀` with `λ^{n₀} B < ρ`
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, (eqLam a) ^ n * B < ρ := by
    rcases eq_or_lt_of_le hB with hB0 | hBpos
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul, hB0.symm]
      exact hρ0
    · have hB1 : 0 < B + 1 := by linarith
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hρ0 hB1) hlam1
      refine ⟨n, ?_⟩
      have h1 : (eqLam a) ^ n * B < (ρ / (B + 1)) * B :=
        mul_lt_mul_of_pos_right hn hBpos
      have h2 : (ρ / (B + 1)) * B ≤ ρ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hB1]
        nlinarith [hρ0]
      linarith
  refine ⟨n₀, ?_⟩
  intro n hn_n₀ T hTpre hTH hB₂
  have hpow_le : ∀ m : ℕ, n ≤ m → (eqLam a) ^ m ≤ (eqLam a) ^ n₀ :=
    fun m hm => pow_le_pow_of_le_one hlam0.le hlam1le (le_trans hn_n₀ hm)
  have hballgen : ∀ m : ℕ, n ≤ m → ∀ q : ChainData, ‖q.2.2‖ ≤ B →
      (eqLam a : ℂ) ^ m * q.2.2 ∈ Metric.ball (0 : ℂ) ρ := by
    intro m hm q hq
    rw [Metric.mem_ball, dist_zero_right, norm_eqLam_pow_mulB ha0 ha1 m]
    have h1 : (eqLam a) ^ m ≤ (eqLam a) ^ n₀ := hpow_le m hm
    have h2 : (eqLam a) ^ m * ‖q.2.2‖ ≤ (eqLam a) ^ n₀ * B :=
      mul_le_mul h1 hq (norm_nonneg _) (pow_nonneg hlam0.le _)
    linarith [hn₀]
  set A : Set ChainData := {q' | TailB a h q' n} with hAdef
  -- `A` is closed at points of `T`
  have hclosed : ∀ q ∈ T, q ∈ closure A → q ∈ A := by
    intro q hqT hqcl
    by_contra hqA
    have hnot : ¬ TailB a h q n := hqA
    rw [TailB] at hnot
    push_neg at hnot
    obtain ⟨m, hmn, hmne⟩ := hnot
    have hball : (eqLam a : ℂ) ^ m * q.2.2 ∈ Metric.ball (0 : ℂ) ρ :=
      hballgen m hmn q (hB₂ q hqT)
    have hcont : ContinuousAt (fun q' : ChainData =>
        q'.1 (-(m : ℤ)) - ugermC a h ((eqLam a : ℂ) ^ m * q'.2.2)) q :=
      (by fun_prop : ContinuousAt (fun q' : ChainData => q'.1 (-(m : ℤ))) q).sub
        (continuousAt_ugermC_psi2 hAnC hball)
    have hS : {q' : ChainData | q'.1 (-(m : ℤ)) - ugermC a h ((eqLam a : ℂ) ^ m * q'.2.2) ≠ 0}
        ∈ 𝓝 q := hcont.eventually_ne (sub_ne_zero.mpr hmne)
    obtain ⟨x, hxS, hxA⟩ := mem_closure_iff_nhds.mp hqcl _ hS
    have hxA' : TailB a h x n := hxA
    exact hxS (by rw [hxA' m hmn, sub_self])
  -- `A` is open at points of `T`
  have hopen : ∀ q : ChainData, q ∈ T ∩ A →
      ∃ W : Set ChainData, IsOpen W ∧ q ∈ W ∧ W ∩ T ⊆ A := by
    intro q hq
    obtain ⟨hqT, hTBn⟩ := hq
    obtain ⟨N₁, M₁, K, ε, hε, hN₁K, hM₁K, htail⟩ := H0_tail_bounded ha0 ha1 hh q (hTH hqT)
    -- the neighbourhood box of `H0_tail_bounded`
    have hbox : ∀ᶠ q' in 𝓝 q,
        (∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q'.1 k - q.1 k‖ < ε) ∧ ‖q'.2.1 - q.2.1‖ < ε
          ∧ ‖q'.2.2 - q.2.2‖ < ε := by
      have h1 : ∀ᶠ q' in 𝓝 q, ∀ k ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)),
          ‖q'.1 k - q.1 k‖ < ε := by
        rw [Finset.eventually_all]
        intro k hk
        exact ev_norm_sub_self_lt (f := fun q' : ChainData => q'.1 k) (by fun_prop) hε
      filter_upwards [h1,
        ev_norm_sub_self_lt (f := fun q' : ChainData => q'.2.1) (by fun_prop) hε,
        ev_norm_sub_self_lt (f := fun q' : ChainData => q'.2.2) (by fun_prop) hε]
        with q' h1' h2' h3'
      refine ⟨?_, h2', h3'⟩
      intro k hk
      exact h1' k (by rw [Finset.mem_Icc]; exact abs_le.mp hk)
    -- the separation conditions at the finitely many intermediate levels
    have hclB : ∀ᶠ q' in 𝓝 q, ∀ m ∈ Finset.Icc n M₁,
        ‖q'.1 (-(m : ℤ)) - ugermC a h ((eqLam a : ℂ) ^ m * q'.2.2)‖ < 1 / 2 := by
      rw [Finset.eventually_all]
      intro m hm
      have hmn : n ≤ m := (Finset.mem_Icc.mp hm).1
      have hball : (eqLam a : ℂ) ^ m * q.2.2 ∈ Metric.ball (0 : ℂ) ρ :=
        hballgen m hmn q (hB₂ q hqT)
      exact ev_norm_lt_of_eq_zero (f := fun q' : ChainData =>
          q'.1 (-(m : ℤ)) - ugermC a h ((eqLam a : ℂ) ^ m * q'.2.2))
        ((by fun_prop : ContinuousAt (fun q' : ChainData => q'.1 (-(m : ℤ))) q).sub
          (continuousAt_ugermC_psi2 hAnC hball))
        (sub_eq_zero.mpr (hTBn m hmn)) (by norm_num)
    have hgood : ∀ᶠ q' in 𝓝[T] q, TailB a h q' n := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hbox, hclB] with q' hbox' hclB' hq'T
      have hTB' : TailB a h q' M₁ := (htail q' (hTH hq'T) hbox'.1 hbox'.2.1 hbox'.2.2).2
      have hchain : IsChain a h q' := isChain_of_mem_H0 (hTH hq'T)
      have hdesc : ∀ m : ℕ, n ≤ m → m ≤ M₁ →
          q'.1 (-(m : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ m * q'.2.2) := by
        intro m hmn hmM₁
        refine Nat.decreasingInduction (motive := fun j _ => n ≤ j →
            q'.1 (-(j : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ j * q'.2.2)) ?_ ?_ hmM₁ hmn
        · intro k hk ih hnk
          have hk₁ : k ≤ M₁ := le_of_lt hk
          have hnext : q'.1 (-((k + 1 : ℕ) : ℤ))
              = ugermC a h ((eqLam a : ℂ) ^ (k + 1) * q'.2.2) := ih (Nat.le_succ_of_le hnk)
          have hcl : ‖q'.1 (-(k : ℤ)) - ugermC a h ((eqLam a : ℂ) ^ k * q'.2.2)‖ < 1 / 2 :=
            hclB' k (Finset.mem_Icc.mpr ⟨hnk, hk₁⟩)
          have hball : (eqLam a : ℂ) ^ k * q'.2.2 ∈ Metric.ball (0 : ℂ) ρ :=
            hballgen k hnk q' (hB₂ q' hq'T)
          exact step_bwd hRP hchain hnext hcl hball
        · intro _
          exact hTB' M₁ le_rfl
      intro m hmn
      by_cases hle : m ≤ M₁
      · exact hdesc m hmn hle
      · exact hTB' m (le_of_lt (lt_of_not_ge hle))
    have hS : {q' : ChainData | TailB a h q' n} ∈ 𝓝 q ⊓ 𝓟 T := hgood
    have hS' := Filter.mem_inf_principal.mp hS
    obtain ⟨W, hWsub, hWopen, hqW⟩ := mem_nhds_iff.mp hS'
    refine ⟨W, hWopen, hqW, ?_⟩
    intro q' hq'
    exact hWsub hq'.1 hq'.2
  -- dichotomy
  by_cases hne : (T ∩ A).Nonempty
  · left
    obtain ⟨q₀, hq₀T, hq₀A⟩ := hne
    choose W hW using hopen
    have huopen : IsOpen (⋃ (q : ChainData) (hq : q ∈ T ∩ A), W q hq) :=
      isOpen_iUnion fun q => isOpen_iUnion fun hq => (hW q hq).1
    have hq₀u : q₀ ∈ (⋃ (q : ChainData) (hq : q ∈ T ∩ A), W q hq) :=
      Set.mem_iUnion.mpr ⟨q₀, Set.mem_iUnion.mpr
        ⟨⟨hq₀T, hq₀A⟩, (hW q₀ ⟨hq₀T, hq₀A⟩).2.1⟩⟩
    have hTsubA : T ⊆ A := by
      intro q hq
      by_contra hqA
      have hqcl : q ∉ closure A := fun hc => hqA (hclosed q hq hc)
      have hsu : T ⊆ (⋃ (q : ChainData) (hq : q ∈ T ∩ A), W q hq) ∪ (closure A)ᶜ := by
        intro x hx
        by_cases hxA : x ∈ A
        · exact Or.inl (Set.mem_iUnion.mpr
            ⟨x, Set.mem_iUnion.mpr ⟨⟨hx, hxA⟩, (hW x ⟨hx, hxA⟩).2.1⟩⟩)
        · exact Or.inr (fun hc => hxA (hclosed x hx hc))
      have hne1 : (T ∩ (⋃ (q : ChainData) (hq : q ∈ T ∩ A), W q hq)).Nonempty :=
        ⟨q₀, hq₀T, hq₀u⟩
      have hnev : (T ∩ (closure A)ᶜ).Nonempty := ⟨q, hq, hqcl⟩
      obtain ⟨x, hxT, hxu, hxv⟩ :=
        hTpre _ _ huopen isClosed_closure.isOpen_compl hsu hne1 hnev
      obtain ⟨q', hxu2⟩ := Set.mem_iUnion.mp hxu
      obtain ⟨hq', hxq'⟩ := Set.mem_iUnion.mp hxu2
      exact hxv (subset_closure ((hW q' hq').2.2 ⟨hxq', hxT⟩))
    intro q hq
    exact hTsubA hq
  · right
    intro q hq hqA
    exact hne ⟨q, hq, hqA⟩

end

end Work.EQ
