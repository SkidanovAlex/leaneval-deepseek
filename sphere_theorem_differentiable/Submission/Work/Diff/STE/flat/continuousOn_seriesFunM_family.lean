import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.flat.tail_tsum_box_tendsto_zero
import Submission.Work.Diff.STE.flat.fourier_projBox_uniform_tendsto
import Submission.Work.Diff.STE.pd_seriesFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint continuity of a Fourier family on the flat torus

Let `c : ℝ → (Fin n → ℤ) → MatC n` be a family of matrix-valued Fourier coefficient families
whose coefficients

* decay faster than every polynomial in the frequency, **uniformly in the time** `t ∈ Ico 0 τ`
  (`hdec`), and
* are continuous in the time (`hcont`).

Then the corresponding Fourier series is **jointly continuous** on the slab
`Ico 0 τ × univ`:

  `(t, x) ↦ seriesFunM (c t) x`.

The proof splits the series into its finite box partial sums and their tail:

* each box partial sum `seriesFunM (projBox N (c t)) x` is a *finite* sum of products of the
  (jointly) continuous functions `(t,x) ↦ c t k a b` and `(t,x) ↦ fourierExp k x`, hence
  `ContinuousOn` on the slab;
* the decay hypothesis bounds the tail of the series by `C · Σ_{k ∉ box n N} ⟨k⟩^{-(n+1)}`,
  a quantity that is *independent of* `t` and `x` and tends to `0` as `N → ∞`
  (`tail_tsum_box_tendsto_zero`), so the box partial sums converge to the series uniformly on the
  slab (`tendstoUniformlyOn_seriesFunM_projBox_aux`).

A uniform limit of continuous functions is continuous (`TendstoUniformlyOn.continuousOn`), which
is the conclusion.

The two halves are independent: the continuity of the partial sums uses only `hcont`, the uniform
convergence only `hdec`.
-/

namespace Work.Diff.STE.flat

open Set Filter
open scoped BigOperators Topology

noncomputable section

variable {n : ℕ}

/-- **The box partial sum is the finite sum over the box.**  Since `projBox N w` is supported in
the finite set `box n N`, its Fourier series is the corresponding finite sum. -/
private lemma seriesFun_projBox_eq_finsetSum (w : (Fin n → ℤ) → ℂ) (N : ℕ) (x : Fin n → ℝ) :
    Work.Diff.STE.seriesFun (Work.Diff.STE.Flat.projBox N w) x
      = ∑ k ∈ Work.Diff.STE.Flat.box n N, w k * Work.Diff.STE.fourierExp k x := by
  rw [Work.Diff.STE.seriesFun]
  rw [tsum_eq_sum (s := Work.Diff.STE.Flat.box n N) ?_]
  · exact Finset.sum_congr rfl fun k hk => by
      rw [Work.Diff.STE.Flat.projBox_apply_of_mem N w hk]
  · intro k hk
    rw [Work.Diff.STE.Flat.projBox_apply_of_not_mem N w hk, zero_mul]

/-- **Joint continuity of the box partial sums, entry by entry.**  This uses only the continuity
of the coefficients in the time variable. -/
private lemma continuousOn_seriesFunM_projBox_entry {τ : ℝ}
    (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hcont : ∀ (k : Fin n → ℤ) (a b : Fin n),
      ContinuousOn (fun t : ℝ => c t k a b) (Set.Ico (0 : ℝ) τ))
    (N : ℕ) (a b : Fin n) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
        Work.Diff.STE.Flat.seriesFunM (Work.Diff.STE.Flat.projBox N (c p.1)) p.2 a b)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) := by
  -- rewrite the partial sum as a finite sum of products of continuous functions
  have hcongr : Set.EqOn
      (fun p : ℝ × (Fin n → ℝ) => ∑ k ∈ Work.Diff.STE.Flat.box n N,
        c p.1 k a b * Work.Diff.STE.fourierExp k p.2)
      (fun p : ℝ × (Fin n → ℝ) =>
        Work.Diff.STE.Flat.seriesFunM (Work.Diff.STE.Flat.projBox N (c p.1)) p.2 a b)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) := by
    intro p _
    show (∑ k ∈ Work.Diff.STE.Flat.box n N, c p.1 k a b * Work.Diff.STE.fourierExp k p.2)
      = Work.Diff.STE.Flat.seriesFunM (Work.Diff.STE.Flat.projBox N (c p.1)) p.2 a b
    rw [Work.Diff.STE.Flat.seriesFunM_apply]
    rw [show (fun m => Work.Diff.STE.Flat.projBox N (c p.1) m a b)
        = Work.Diff.STE.Flat.projBox N (fun k => c p.1 k a b) from by
      funext m
      by_cases hm : m ∈ Work.Diff.STE.Flat.box n N
      · rw [Work.Diff.STE.Flat.projBox_apply_of_mem N (c p.1) hm,
            Work.Diff.STE.Flat.projBox_apply_of_mem N (fun k => c p.1 k a b) hm]
      · rw [Work.Diff.STE.Flat.projBox_apply_of_not_mem N (c p.1) hm,
            Work.Diff.STE.Flat.projBox_apply_of_not_mem N (fun k => c p.1 k a b) hm]
        simp]
    rw [seriesFun_projBox_eq_finsetSum]
  refine (continuousOn_congr hcongr).mp ?_
  refine continuousOn_finsetSum _ fun k _ => ?_
  have h1 : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => c p.1 k a b)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) :=
    (hcont k a b).comp continuousOn_fst (fun p hp => hp.1)
  have h2 : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => Work.Diff.STE.fourierExp k p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) :=
    ((Work.Diff.STE.continuous_fourierExp k).continuousOn (s := Set.univ)).comp
      (continuousOn_snd (s := Set.Ico (0 : ℝ) τ ×ˢ Set.univ)) (fun _ _ => Set.mem_univ _)
  exact h1.mul h2

/-- **Continuity of the box partial sums, matrix-valued.** -/
private lemma continuousOn_seriesFunM_projBox {τ : ℝ}
    (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hcont : ∀ (k : Fin n → ℤ) (a b : Fin n),
      ContinuousOn (fun t : ℝ => c t k a b) (Set.Ico (0 : ℝ) τ)) (N : ℕ) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
        Work.Diff.STE.Flat.seriesFunM (Work.Diff.STE.Flat.projBox N (c p.1)) p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) := by
  rw [continuousOn_pi]
  intro a
  rw [continuousOn_pi]
  intro b
  exact continuousOn_seriesFunM_projBox_entry c hcont N a b

/-- **Uniform convergence of the box partial sums.**  This uses only the decay hypothesis `hdec`:
with `m = n + 1`, `2m > n`, so the weight `⟨k⟩^{-m}` is summable, and the box tails
`Σ_{k ∉ box n N} ⟨k⟩^{-m}` tend to `0`; the decay bound turns this into a bound on the difference
between the series and its `N`-th box partial sum that is independent of `t` and `x`. -/
lemma tendstoUniformlyOn_seriesFunM_projBox_aux {τ : ℝ}
    (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : Fin n → ℤ,
      ∀ a b : Fin n, ‖c t k a b‖ * (Work.Diff.STE.wt k) ^ M ≤ C) :
    TendstoUniformlyOn
      (fun N (p : ℝ × (Fin n → ℝ)) =>
        Work.Diff.STE.Flat.seriesFunM (Work.Diff.STE.Flat.projBox N (c p.1)) p.2)
      (fun p : ℝ × (Fin n → ℝ) => Work.Diff.STE.Flat.seriesFunM (c p.1) p.2)
      Filter.atTop (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) := by
  classical
  obtain ⟨C, hC0, hCb⟩ := hdec (n + 1)
  have hwtpos : ∀ k : Fin n → ℤ, (0 : ℝ) < Work.Diff.STE.wt k :=
    fun k => Work.Diff.STE.wt_pos k
  have hsumw : Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ (-(((n + 1 : ℕ)) : ℤ))) :=
    Work.Diff.STE.summable_wt_zpow (n + 1) (by rw [Fintype.card_fin]; omega)
  have htail : Filter.Tendsto
      (fun N : ℕ => ∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N},
        (Work.Diff.STE.wt k.1) ^ (-(((n + 1 : ℕ)) : ℤ))) Filter.atTop (nhds 0) :=
    Work.Diff.STE.flat.tail_tsum_box_tendsto_zero
      (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ (-(((n + 1 : ℕ)) : ℤ)))
  -- the decay bound, in the reciprocal form
  have hbnd : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : Fin n → ℤ, ∀ a b : Fin n,
      ‖c t k a b‖ ≤ C * (Work.Diff.STE.wt k) ^ (-(((n + 1 : ℕ)) : ℤ)) := by
    intro t ht k a b
    have h := hCb t ht k a b
    have hpos : 0 < (Work.Diff.STE.wt k) ^ (n + 1) := pow_pos (hwtpos k) (n + 1)
    rw [zpow_neg, zpow_natCast, le_mul_inv_iff₀ hpos]
    exact h
  -- the entrywise tail bound
  have hperentry : ∀ (N : ℕ) (p : ℝ × (Fin n → ℝ)), p.1 ∈ Set.Ico (0 : ℝ) τ →
      ∀ a b : Fin n,
      ‖Work.Diff.STE.Flat.seriesFunM (c p.1) p.2 a b
        - Work.Diff.STE.Flat.seriesFunM (Work.Diff.STE.Flat.projBox N (c p.1)) p.2 a b‖
        ≤ C * (∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N},
            (Work.Diff.STE.wt k.1) ^ (-(((n + 1 : ℕ)) : ℤ))) := by
    intro N p hp a b
    have hsumm : Summable (fun k : Fin n → ℤ => ‖c p.1 k a b‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hbnd p.1 hp k a b)
        (hsumw.mul_left C)
    have h1 : Work.Diff.STE.Flat.seriesFunM (c p.1) p.2 a b
        = Work.Diff.STE.seriesFun (fun k => c p.1 k a b) p.2 :=
      Work.Diff.STE.Flat.seriesFunM_apply (c p.1) p.2 a b
    have h2 : Work.Diff.STE.Flat.seriesFunM (Work.Diff.STE.Flat.projBox N (c p.1)) p.2 a b
        = Work.Diff.STE.seriesFun (Work.Diff.STE.Flat.projBox N (fun k => c p.1 k a b)) p.2 :=
      Work.Diff.STE.Flat.seriesFunM_apply (Work.Diff.STE.Flat.projBox N (c p.1)) p.2 a b |>.trans
        (by
          congr 1
          funext k
          by_cases hk : k ∈ Work.Diff.STE.Flat.box n N
          · rw [Work.Diff.STE.Flat.projBox_apply_of_mem N (c p.1) hk,
                Work.Diff.STE.Flat.projBox_apply_of_mem N (fun k => c p.1 k a b) hk]
          · rw [Work.Diff.STE.Flat.projBox_apply_of_not_mem N (c p.1) hk,
                Work.Diff.STE.Flat.projBox_apply_of_not_mem N (fun k => c p.1 k a b) hk]
            simp)
    rw [h1, h2, norm_sub_rev]
    refine (Work.Diff.STE.flat.seriesFun_projBox_sub_norm_le (fun k => c p.1 k a b) hsumm
      N p.2).trans ?_
    have hle : (∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N}, ‖c p.1 k.1 a b‖)
        ≤ ∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N},
            C * (Work.Diff.STE.wt k.1) ^ (-(((n + 1 : ℕ)) : ℤ)) :=
      Summable.tsum_le_tsum (fun k => hbnd p.1 hp k.1 a b) (hsumm.subtype _)
        ((hsumw.mul_left C).subtype _)
    exact hle.trans (le_of_eq (Summable.tsum_mul_left C (hsumw.subtype _)))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rw [Filter.eventually_atTop]
  have hlt : ∀ᶠ N : ℕ in Filter.atTop,
      C * (∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N},
        (Work.Diff.STE.wt k.1) ^ (-(((n + 1 : ℕ)) : ℤ))) < ε := by
    have h0 : Filter.Tendsto (fun N : ℕ =>
        C * (∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N},
          (Work.Diff.STE.wt k.1) ^ (-(((n + 1 : ℕ)) : ℤ)))) Filter.atTop (nhds (C * 0)) :=
      htail.const_mul C
    rw [mul_zero] at h0
    exact (tendsto_order.1 h0).2 ε hε
  rw [Filter.eventually_atTop] at hlt
  obtain ⟨N₀, hN₀⟩ := hlt
  refine ⟨N₀, fun N hN p hp => ?_⟩
  have htailnn : 0 ≤ (∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N},
      (Work.Diff.STE.wt k.1) ^ (-(((n + 1 : ℕ)) : ℤ))) :=
    tsum_nonneg fun k => zpow_nonneg (le_of_lt (hwtpos k.1)) _
  refine lt_of_le_of_lt ?_ (hN₀ N hN)
  rw [dist_pi_le_iff (mul_nonneg hC0 htailnn)]
  intro a
  rw [dist_pi_le_iff (mul_nonneg hC0 htailnn)]
  intro b
  rw [dist_eq_norm]
  exact hperentry N p hp.1 a b

set_option linter.unusedVariables false in
/-- **Joint continuity of a rapidly decaying Fourier family on the slab `[0, τ) × ℝⁿ`.**  The
hypothesis `hτ : 0 < τ` is part of the requested statement; it is not needed by the argument (for
`τ ≤ 0` the slab is empty). -/
theorem continuousOn_seriesFunM_family {n : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : Fin n → ℤ,
      ∀ a b : Fin n, ‖c t k a b‖ * (Work.Diff.STE.wt k) ^ M ≤ C)
    (hcont : ∀ (k : Fin n → ℤ) (a b : Fin n),
      ContinuousOn (fun t : ℝ => c t k a b) (Set.Ico (0 : ℝ) τ)) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) => Work.Diff.STE.Flat.seriesFunM (c p.1) p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) :=
  (tendstoUniformlyOn_seriesFunM_projBox_aux c hdec).continuousOn
    (Filter.Frequently.of_forall fun N => continuousOn_seriesFunM_projBox c hcont N)

end

end Work.Diff.STE.flat
