import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.BW

/-- A `finprod` of a family of reals with all values in `[0, 1]` is at most `1`.
(If the support is infinite, the `finprod` is the junk value `1` by definition.) -/
private lemma finprod_le_one_of_forall_le_one {α : Type*} {f : α → ℝ}
    (h0 : ∀ a, 0 ≤ f a) (h1 : ∀ a, f a ≤ 1) : ∏ᶠ a, f a ≤ 1 := by
  by_cases hf : Function.HasFiniteMulSupport f
  · rw [← finprod_mem_mulSupport f, ← finprod_set_coe_eq_finprod_mem]
    have : Fintype {a // a ∈ Function.mulSupport f} := hf.fintype
    rw [finprod_eq_prod_of_fintype]
    exact Finset.prod_le_one₀ (fun a _ => h0 a) fun a _ => h1 a
  · rw [finprod_of_not_hasFiniteMulSupport hf]

/-- The logarithmic height (in a number field `K`) of a tuple of rational integers bounded in
absolute value by `M` is at most `[K : ℚ] · log M`. -/
theorem logHeight_intTuple_le {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]
    (n : ι → ℤ) {M : ℝ} (hM : 1 ≤ M) (hn : ∀ i, |(n i : ℝ)| ≤ M) :
    Height.logHeight (fun i => ((n i : ℤ) : K)) ≤ (Module.finrank ℚ K : ℝ) * Real.log M := by
  set x : ι → K := fun i => ((n i : ℤ) : K)
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hMnn : 0 ≤ M := le_of_lt hMpos
  rcases eq_or_ne x 0 with hx0 | hx0
  · rw [hx0, Height.logHeight_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hM)
  · obtain ⟨i₀, -⟩ := Function.ne_iff.mp hx0
    haveI : Nonempty ι := ⟨i₀⟩
    have hnn : ∀ (v : NumberField.FinitePlace K), 0 ≤ (⨆ i, v (x i)) :=
      fun v => Real.iSup_nonneg fun i => v.1.nonneg _
    have hnn2 : ∀ (w : NumberField.InfinitePlace K), 0 ≤ (⨆ i, w (x i)) :=
      fun w => Real.iSup_nonneg fun i => w.1.nonneg _
    -- At a finite place, an integer is `≤ 1` in absolute value.
    have hfin : ∀ v : NumberField.FinitePlace K, (⨆ i, v (x i)) ≤ 1 := by
      intro v
      refine ciSup_le fun i => ?_
      have hna : IsNonarchimedean (fun y : K => v y) :=
        fun a b => NumberField.FinitePlace.add_le v a b
      exact hna.apply_intCast_le_one (map_zero_le v 1) (map_one v) (map_neg_eq_map v)
    -- At an infinite place, the value of `x i` is `|n i| ≤ M`.
    have hinf : ∀ w : NumberField.InfinitePlace K, (⨆ i, w (x i)) ≤ M := by
      intro w
      refine ciSup_le fun i => ?_
      have h1 : w (x i) = ‖((n i : ℤ) : ℂ)‖ := by
        rw [← NumberField.InfinitePlace.norm_embedding_eq w]
        congr 1
        exact map_intCast w.embedding (n i)
      rw [h1, Complex.norm_intCast]
      exact hn i
    have hB : (∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i)) ≤ 1 :=
      finprod_le_one_of_forall_le_one (fun v => hnn v) (fun v => hfin v)
    have hA : (∏ w : NumberField.InfinitePlace K, (⨆ i, w (x i)) ^ w.mult)
        ≤ M ^ (Module.finrank ℚ K) := by
      calc ∏ w : NumberField.InfinitePlace K, (⨆ i, w (x i)) ^ w.mult
          ≤ ∏ w : NumberField.InfinitePlace K, M ^ w.mult :=
            Finset.prod_le_prod₀ (fun w _ => pow_nonneg (hnn2 w) _)
              (fun w _ => pow_le_pow_left₀ (hnn2 w) (hinf w) _)
        _ = M ^ ∑ w : NumberField.InfinitePlace K, w.mult :=
            Finset.prod_pow_eq_pow_sum _ _ _
        _ = M ^ (Module.finrank ℚ K) := by rw [NumberField.InfinitePlace.sum_mult_eq]
    have hmul : Height.mulHeight x ≤ M ^ (Module.finrank ℚ K) := by
      rw [NumberField.mulHeight_eq hx0]
      calc (∏ w : NumberField.InfinitePlace K, (⨆ i, w (x i)) ^ w.mult) *
              (∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i))
          ≤ (∏ w : NumberField.InfinitePlace K, (⨆ i, w (x i)) ^ w.mult) * 1 :=
            mul_le_mul_of_nonneg_left hB (Finset.prod_nonneg fun w _ => pow_nonneg (hnn2 w) _)
        _ = _ := mul_one _
        _ ≤ M ^ (Module.finrank ℚ K) := hA
    rw [Height.logHeight_eq_log_mulHeight]
    calc Real.log (Height.mulHeight x) ≤ Real.log (M ^ (Module.finrank ℚ K)) :=
          Real.log_le_log (Height.mulHeight_pos x) hmul
      _ = (Module.finrank ℚ K : ℝ) * Real.log M := Real.log_pow M _

end Work.BW
