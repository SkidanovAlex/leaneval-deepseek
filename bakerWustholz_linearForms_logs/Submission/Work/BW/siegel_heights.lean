import Mathlib
import Submission.Work.BW.logHeight_intTuple_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- A `finprod` of reals in `[0,1]` is at most `1`.  (If the support is infinite the `finprod`
is the junk value `1` by definition.) -/
private lemma finprod_le_one_of_forall_le_one {α : Type*} {f : α → ℝ}
    (h0 : ∀ a, 0 ≤ f a) (h1 : ∀ a, f a ≤ 1) : ∏ᶠ a, f a ≤ 1 := by
  by_cases hf : Function.HasFiniteMulSupport f
  · rw [← finprod_mem_mulSupport f, ← finprod_set_coe_eq_finprod_mem]
    have : Fintype {a // a ∈ Function.mulSupport f} := hf.fintype
    rw [finprod_eq_prod_of_fintype]
    exact Finset.prod_le_one₀ (fun a _ => h0 a) fun a _ => h1 a
  · rw [finprod_of_not_hasFiniteMulSupport hf]

/-- **Height bound from a place bound.**  If `x : κ → 𝓞 F` satisfies `w (x j) ≤ r` at every
infinite place `w` (for a real number `r ≥ 1`), then the logarithmic height of the tuple is at
most `[F : ℚ] · log r`.  (The finite places contribute at most `1`, since the entries are
algebraic integers.) -/
theorem logHeight_le_of_place_le {F : Type*} [Field F] [NumberField F] {κ : Type*} [Fintype κ]
    (x : κ → NumberField.RingOfIntegers F) {r : ℝ} (hr : 1 ≤ r)
    (hx : ∀ j (w : NumberField.InfinitePlace F), w (x j : F) ≤ r) :
    Height.logHeight (fun j => (x j : F)) ≤ (Module.finrank ℚ F : ℝ) * Real.log r := by
  classical
  rcases eq_or_ne (fun j => (x j : F)) 0 with h0 | hyne
  · rw [h0, Height.logHeight_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hr)
  · obtain ⟨j₀, -⟩ := Function.ne_iff.mp hyne
    haveI : Nonempty κ := ⟨j₀⟩
    have hnn : ∀ v : NumberField.FinitePlace F, 0 ≤ (⨆ j, v ((x j : F))) :=
      fun v => Real.iSup_nonneg fun j => v.1.nonneg _
    have hnn2 : ∀ w : NumberField.InfinitePlace F, 0 ≤ (⨆ j, w ((x j : F))) :=
      fun w => Real.iSup_nonneg fun j => w.1.nonneg _
    -- at finite places an algebraic integer has absolute value at most `1`
    have hfin : ∀ v : NumberField.FinitePlace F, (⨆ j, v ((x j : F))) ≤ 1 := by
      intro v
      refine ciSup_le fun j => ?_
      have h1 : v ((x j : F)) = ‖NumberField.FinitePlace.embedding v.maximalIdeal ((x j : F))‖ :=
        (NumberField.FinitePlace.norm_embedding_eq v ((x j : F))).symm
      rw [h1]
      exact NumberField.FinitePlace.norm_le_one (K := F) (v := v.maximalIdeal) (x := x j)
    have hinf : ∀ w : NumberField.InfinitePlace F, (⨆ j, w ((x j : F))) ≤ r :=
      fun w => ciSup_le fun j => hx j w
    have hB : (∏ᶠ v : NumberField.FinitePlace F, ⨆ j, v ((x j : F))) ≤ 1 :=
      finprod_le_one_of_forall_le_one hnn hfin
    have hA : (∏ w : NumberField.InfinitePlace F, (⨆ j, w ((x j : F))) ^ w.mult)
        ≤ r ^ (Module.finrank ℚ F) := by
      calc ∏ w : NumberField.InfinitePlace F, (⨆ j, w ((x j : F))) ^ w.mult
          ≤ ∏ w : NumberField.InfinitePlace F, r ^ w.mult :=
            Finset.prod_le_prod₀ (fun w _ => pow_nonneg (hnn2 w) _)
              (fun w _ => pow_le_pow_left₀ (hnn2 w) (hinf w) _)
        _ = r ^ ∑ w : NumberField.InfinitePlace F, w.mult :=
            Finset.prod_pow_eq_pow_sum _ _ r
        _ = r ^ (Module.finrank ℚ F) := by rw [NumberField.InfinitePlace.sum_mult_eq]
    have hmul : Height.mulHeight (fun j => (x j : F)) ≤ r ^ (Module.finrank ℚ F) := by
      rw [NumberField.mulHeight_eq hyne]
      calc (∏ w : NumberField.InfinitePlace F, (⨆ j, w ((x j : F))) ^ w.mult) *
              (∏ᶠ v : NumberField.FinitePlace F, ⨆ j, v ((x j : F)))
          ≤ (∏ w : NumberField.InfinitePlace F, (⨆ j, w ((x j : F))) ^ w.mult) * 1 :=
            mul_le_mul_of_nonneg_left hB (Finset.prod_nonneg fun w _ => pow_nonneg (hnn2 w) _)
        _ = _ := mul_one _
        _ ≤ r ^ (Module.finrank ℚ F) := hA
    rw [Height.logHeight_eq_log_mulHeight]
    calc Real.log (Height.mulHeight (fun j => (x j : F))) ≤ Real.log (r ^ (Module.finrank ℚ F)) :=
          Real.log_le_log (Height.mulHeight_pos _) hmul
      _ = (Module.finrank ℚ F : ℝ) * Real.log r := Real.log_pow r _

end Work.BW

namespace Work.BW

/-- **Height bound from place-wise bounds.**  If `x : κ → 𝓞 F` satisfies `w (x j) ≤ f w` at every
infinite place `w`, where `f ≥ 1`, then the logarithmic height of the tuple is at most
`∑_w mult w · log (f w)`.  (At the finite places the entries are algebraic integers, so the
contribution is at most `1`.) -/
theorem logHeight_le_of_place_bound {F : Type*} [Field F] [NumberField F] {κ : Type*} [Fintype κ]
    (x : κ → NumberField.RingOfIntegers F) (f : NumberField.InfinitePlace F → ℝ)
    (hf : ∀ w, 1 ≤ f w) (hx : ∀ j (w : NumberField.InfinitePlace F), w (x j : F) ≤ f w) :
    Height.logHeight (fun j => (x j : F)) ≤
      ∑ w : NumberField.InfinitePlace F, (w.mult : ℝ) * Real.log (f w) := by
  classical
  rcases eq_or_ne (fun j => (x j : F)) 0 with h0 | hyne
  · rw [h0, Height.logHeight_zero]
    refine Finset.sum_nonneg fun w _ => ?_
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (hf w))
  · obtain ⟨j₀, -⟩ := Function.ne_iff.mp hyne
    haveI : Nonempty κ := ⟨j₀⟩
    have hnn : ∀ v : NumberField.FinitePlace F, 0 ≤ (⨆ j, v ((x j : F))) :=
      fun v => Real.iSup_nonneg fun j => v.1.nonneg _
    have hnn2 : ∀ w : NumberField.InfinitePlace F, 0 ≤ (⨆ j, w ((x j : F))) :=
      fun w => Real.iSup_nonneg fun j => w.1.nonneg _
    have hfin : ∀ v : NumberField.FinitePlace F, (⨆ j, v ((x j : F))) ≤ 1 := by
      intro v
      refine ciSup_le fun j => ?_
      have h1 : v ((x j : F)) = ‖NumberField.FinitePlace.embedding v.maximalIdeal ((x j : F))‖ :=
        (NumberField.FinitePlace.norm_embedding_eq v ((x j : F))).symm
      rw [h1]
      exact NumberField.FinitePlace.norm_le_one (K := F) (v := v.maximalIdeal) (x := x j)
    have hB : (∏ᶠ v : NumberField.FinitePlace F, ⨆ j, v ((x j : F))) ≤ 1 :=
      finprod_le_one_of_forall_le_one hnn hfin
    have hunit : ∀ w : NumberField.InfinitePlace F, (⨆ j, w ((x j : F))) ≤ f w :=
      fun w => ciSup_le fun j => hx j w
    have hprod : (∏ w : NumberField.InfinitePlace F, (⨆ j, w ((x j : F))) ^ w.mult)
        ≤ ∏ w : NumberField.InfinitePlace F, (f w) ^ w.mult :=
      Finset.prod_le_prod₀ (fun w _ => pow_nonneg (hnn2 w) _)
        (fun w _ => pow_le_pow_left₀ (hnn2 w) (hunit w) _)
    have hfp : (∏ w : NumberField.InfinitePlace F, (f w) ^ w.mult)
        = ∏ w : NumberField.InfinitePlace F, Real.exp ((w.mult : ℝ) * Real.log (f w)) := by
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [Real.exp_nat_mul, Real.exp_log (by linarith [hf w])]
    have hmul : Height.mulHeight (fun j => (x j : F)) ≤
        ∏ w : NumberField.InfinitePlace F, Real.exp ((w.mult : ℝ) * Real.log (f w)) := by
      rw [NumberField.mulHeight_eq hyne]
      calc (∏ w : NumberField.InfinitePlace F, (⨆ j, w ((x j : F))) ^ w.mult) *
              (∏ᶠ v : NumberField.FinitePlace F, ⨆ j, v ((x j : F)))
          ≤ (∏ w : NumberField.InfinitePlace F, (f w) ^ w.mult) * 1 :=
            mul_le_mul hprod hB (finprod_nonneg fun v => hnn v)
              (Finset.prod_nonneg fun w _ => pow_nonneg (by linarith [hf w]) _)
        _ = ∏ w : NumberField.InfinitePlace F, Real.exp ((w.mult : ℝ) * Real.log (f w)) := by
            rw [mul_one, hfp]
    have hexp : ∏ w : NumberField.InfinitePlace F, Real.exp ((w.mult : ℝ) * Real.log (f w))
        = Real.exp (∑ w : NumberField.InfinitePlace F, (w.mult : ℝ) * Real.log (f w)) := by
      rw [← Real.exp_sum]
    rw [Height.logHeight_eq_log_mulHeight]
    calc Real.log (Height.mulHeight (fun j => (x j : F)))
        ≤ Real.log (Real.exp (∑ w : NumberField.InfinitePlace F, (w.mult : ℝ) * Real.log (f w))) :=
          Real.log_le_log (Height.mulHeight_pos _) (hmul.trans_eq hexp)
      _ = ∑ w : NumberField.InfinitePlace F, (w.mult : ℝ) * Real.log (f w) := Real.log_exp _

end Work.BW

