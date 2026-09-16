import Mathlib
import Submission.KernelLimitK
import Submission.ZetaRatioPoleFamily

open scoped BigOperators Topology
open Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# P8 (41) for a *family* of moduli — the full `k`-coordinate kernel

`kernel_pole_asymptotic_fin` (`Submission.KernelLimitK`) proves the P8 (41)
kernel asymptotic for *fixed* coprime moduli `W, N` and a fixed truncation
parameter `w`.  The sieve applies the lemma with the growing modulus
`W(x) = ∏_{p ≤ w(x)} p` (`w(x) = logloglog x`) and a truncation window `w(x)`
that also grows with `x`; this module proves the same asymptotic uniformly in
the family.

The only genuinely new input is the growth hypothesis
`log(W(x)·N(x))/√(log x) → 0` (satisfied since `log W(x) ≍ w(x) ≪ loglog x`),
which is exactly what `zetaWN_ratio_pole_uniform_family`
(`Submission.ZetaRatioPoleFamily`) needs; the tail factor `exp(C/w(x)) - 1`
now vanishes because `w(x) → ∞`.

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **P8 (41) for `k` coordinates, family form.**  Let `W, N : ℕ → ℕ` be
nonzero with `(W x, N x) = 1` for all `x`, let `w : ℕ → ℕ` tend to infinity
with every prime `≤ w x` dividing `W x·N x`, and assume the growth hypothesis
`log(W x·N x)/√(log x) → 0`.  Then for every `k ≥ 1` the kernel limit `K` of
the `k`-coordinate product `∏_{p ∤ W(x)N(x)} K_p` satisfies, uniformly on the
cube `|ξ_j|, |ξ'_j| ≤ √(log x)`,

    ‖ K · ∏_j poleFactor_j − 1 ‖ ≤ ε(x) + 2·(exp(C/w(x)) − 1) ,

with `ε(x) → 0` and `w(x) → ∞`. -/
theorem kernel_pole_asymptotic_family (k : ℕ) (hk : 1 ≤ k)
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x → ∀ ξ ξ' : Fin k → ℝ,
        (∀ j, |ξ j| ≤ Real.sqrt (Real.log (x : ℝ))) →
        (∀ j, |ξ' j| ≤ Real.sqrt (Real.log (x : ℝ))) →
        ∃ L : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter ((W x) * (N x)) n,
            coordLocalK p (fun j => logZ (ξ j) x) (fun j => logZ (ξ' j) x)) atTop (𝓝 L) ∧
          ‖L * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x) - 1‖ ≤
            ε x + 2 * (Real.exp (C / ((w x : ℕ) : ℝ)) - 1) := by
  classical
  obtain ⟨C, hC0, hCbound⟩ := exists_coordK_ratio_bound k
  obtain ⟨x₀₁, ε₁, hε₁, hpole⟩ := zetaWN_ratio_pole_uniform_family W N hW hN hcop hlq
  have hε₂ : Tendsto (fun x : ℕ => |ε₁ x|) atTop (𝓝 0) := by
    simpa using hε₁.abs
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hε₂.eventually_lt_const (by positivity : (0 : ℝ) < 1 / (2 * (k : ℝ))))
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hw.eventually_ge_atTop 1)
  refine ⟨C, hC0, max (max x₀₁ N₀) (max N₁ 2), fun x => 2 * (k : ℝ) * |ε₁ x|, ?_, ?_⟩
  · simpa using hε₂.const_mul (2 * (k : ℝ))
  · intro x hx ξ ξ' hξ hξ'
    have hx₁ : x₀₁ ≤ x :=
      le_trans (le_trans (le_max_left x₀₁ N₀) (le_max_left _ _)) hx
    have hNx : N₀ ≤ x :=
      le_trans (le_trans (le_max_right x₀₁ N₀) (le_max_left _ _)) hx
    have hw1 : 1 ≤ w x := hN₁ x (le_trans (le_trans (le_max_left N₁ 2)
      (le_max_right (max x₀₁ N₀) (max N₁ 2))) hx)
    have hx2 : 2 ≤ x := le_trans (le_trans (le_max_right N₁ 2)
      (le_max_right (max x₀₁ N₀) (max N₁ 2))) hx
    have hkx : (k : ℝ) * |ε₁ x| ≤ 1 / 2 := by
      have h1 := hN₀ x hNx
      have h2 : (k : ℝ) * |ε₁ x| < (k : ℝ) * (1 / (2 * (k : ℝ))) :=
        mul_lt_mul_of_pos_left h1 (by exact_mod_cast hk)
      have h3 : (k : ℝ) * (1 / (2 * (k : ℝ))) = 1 / 2 := by field_simp
      linarith [h2, h3.le]
    have hq : W x * N x ≠ 0 := mul_ne_zero (hW x) (hN x)
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    set a : Fin k → ℂ := fun j => logZ (ξ j) x with ha'
    set b : Fin k → ℂ := fun j => logZ (ξ' j) x with hb'
    have hare : ∀ j, 0 < (a j).re := by
      intro j
      rw [ha']
      rw [logZ_re]
      positivity
    have hbre : ∀ j, 0 < (b j).re := by
      intro j
      rw [hb']
      rw [logZ_re]
      positivity
    -- the modified-zeta ratio limits Zf
    set Zf : Fin k → ℂ := fun j => zetaWN (W x * N x) (1 + a j + b j) /
        (zetaWN (W x * N x) (1 + a j) * zetaWN (W x * N x) (1 + b j)) with hZf
    have hpole' : ∀ j : Fin k, ‖Zf j * poleFactor (W x) (N x) (ξ j) (ξ' j) x - 1‖ ≤
        |ε₁ x| := by
      intro j
      have h := hpole x hx₁ (ξ j) (ξ' j) (hξ j) (hξ' j)
      rw [show (1 + (logZ (ξ j) x + logZ (ξ' j) x)) = (1 + a j + b j) from by
            simp only [ha', hb']
            ring] at h
      rw [hZf]
      exact h.trans (le_abs_self _)
    -- the ratio and R products converge
    obtain ⟨M, hM⟩ := exists_tendsto_prod_one_add_filter (W x * N x) (C := C) hC0.le
      (fun p hp2 => by
        simpa using hCbound p hp2 a b (fun j => (hare j).le) (fun j => (hbre j).le))
    have hratio_tend : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter (W x * N x) n,
        coordLocalK p a b / ∏ j : Fin k, locR p (a j) (b j)) atTop (𝓝 M) := by
      refine hM.congr' ?_
      filter_upwards with n
      refine Finset.prod_congr rfl (fun p _ => ?_)
      ring
    have hRlim : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter (W x * N x) n,
        ∏ j : Fin k, locR p (a j) (b j)) atTop (𝓝 (∏ j : Fin k, Zf j)) := by
      have hcomm : (fun n : ℕ => ∏ p ∈ Sfilter (W x * N x) n, ∏ j : Fin k, locR p (a j) (b j)) =
          fun n : ℕ => ∏ j : Fin k, ∏ p ∈ Sfilter (W x * N x) n, locR p (a j) (b j) := by
        funext n
        exact Finset.prod_comm
      rw [hcomm]
      refine tendsto_finset_prod_of _ (fun j _ => ?_)
      have hR := eulerRatioZetaWN (W x * N x) hq (hare j) (hbre j)
      have h1 : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter (W x * N x) n, locR p (a j) (b j)) atTop
          (𝓝 (zetaWN (W x * N x) (1 + a j + b j) /
            (zetaWN (W x * N x) (1 + a j) * zetaWN (W x * N x) (1 + b j)))) := by
        refine hR.congr' ?_
        filter_upwards with n
        refine Finset.prod_congr rfl (fun p _ => ?_)
        rw [locR, div_eq_mul_inv]
      rw [hZf]
      exact h1
    -- the kernel limit is (∏ Zf) · M
    have hKlim : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter (W x * N x) n, coordLocalK p a b) atTop
        (𝓝 ((∏ j : Fin k, Zf j) * M)) := by
      have hEq : (fun n : ℕ => ∏ p ∈ Sfilter (W x * N x) n, coordLocalK p a b) =
          fun n : ℕ => (∏ p ∈ Sfilter (W x * N x) n, ∏ j : Fin k, locR p (a j) (b j)) *
            (∏ p ∈ Sfilter (W x * N x) n,
              coordLocalK p a b / ∏ j : Fin k, locR p (a j) (b j)) := by
        funext n
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun p hp => ?_)
        have hp2 : 2 ≤ p := two_le_of_mem_Sfilter hp
        have hRnz : (∏ j : Fin k, locR p (a j) (b j)) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr (fun j _ => by
            intro hz
            have h := locR_norm_ge_sixth (a j) (b j) hp2 (hare j).le (hbre j).le
            rw [hz] at h
            norm_num at h)
        field_simp [hRnz]
      rw [hEq]
      exact hRlim.mul hratio_tend
    -- the tail bound on M
    have hMbound : ‖M - 1‖ ≤ Real.exp (C / ((w x : ℕ) : ℝ)) - 1 := by
      have hclosed : IsClosed {z : ℂ | ‖z - 1‖ ≤ Real.exp (C / ((w x : ℕ) : ℝ)) - 1} :=
        isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
      refine hclosed.mem_of_tendsto hM (Eventually.of_forall (fun n => ?_))
      exact tailProduct_norm_sub_one_le hC0.le hw1 (fun p hp => by
        by_contra hlt
        have hpn : p ∈ n.primesBelow := (Finset.mem_filter.mp hp).1
        have hnd : ¬ p ∣ W x * N x := (Finset.mem_filter.mp hp).2
        exact hnd (hsmall x p (Nat.prime_of_mem_primesBelow hpn) (by omega)))
        (fun p hp => by
          simpa using hCbound p (two_le_of_mem_Sfilter hp) a b
            (fun j => (hare j).le) (fun j => (hbre j).le))
    refine ⟨(∏ j : Fin k, Zf j) * M, hKlim, ?_⟩
    have hexpta : 0 ≤ Real.exp (C / ((w x : ℕ) : ℝ)) - 1 := by
      have hwx : (0 : ℝ) ≤ ((w x : ℕ) : ℝ) := by
        have : (0 : ℕ) < w x := by omega
        exact_mod_cast this.le
      have h : 0 ≤ C / ((w x : ℕ) : ℝ) := div_nonneg hC0.le hwx
      linarith [Real.one_le_exp h]
    have hprod_b : ‖(∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x) - 1‖ ≤
        Real.exp ((k : ℝ) * |ε₁ x|) - 1 := by
      rw [← Finset.prod_mul_distrib]
      exact norm_prod_sub_one_le_of (fun j => hpole' j)
    have hprod_n : ‖(∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x)‖ ≤
        Real.exp ((k : ℝ) * |ε₁ x|) := by
      rw [← Finset.prod_mul_distrib]
      exact norm_prod_exp_le_of (fun j => hpole' j)
    have hkabs0 : 0 ≤ (k : ℝ) * |ε₁ x| := mul_nonneg (by positivity) (abs_nonneg _)
    have hkabs1 : (k : ℝ) * |ε₁ x| ≤ 1 := by linarith [hkx]
    have hexp_le : Real.exp ((k : ℝ) * |ε₁ x|) ≤ 1 + 2 * ((k : ℝ) * |ε₁ x|) := by
      have h := exp_sub_one_le_two_mul hkabs0 hkabs1
      linarith
    have h2k1 : 2 * ((k : ℝ) * |ε₁ x|) ≤ 1 := by linarith [hkx]
    have hdecomp : ((∏ j : Fin k, Zf j) * M) * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x) - 1 =
        (((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x)) * M -
          ((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x))) +
        (((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x)) - 1) := by ring
    rw [hdecomp]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x)) * M -
        ((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x))‖ ≤
        (1 + 2 * ((k : ℝ) * |ε₁ x|)) * (Real.exp (C / ((w x : ℕ) : ℝ)) - 1) := by
      have hsub : ((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x)) * M -
          ((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x)) =
          ((∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x)) * (M - 1) := by
        ring
      rw [hsub, norm_mul]
      calc ‖(∏ j : Fin k, Zf j) * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x)‖ * ‖M - 1‖
          ≤ Real.exp ((k : ℝ) * |ε₁ x|) * ‖M - 1‖ :=
            mul_le_mul_of_nonneg_right hprod_n (norm_nonneg _)
        _ ≤ (1 + 2 * ((k : ℝ) * |ε₁ x|)) * ‖M - 1‖ :=
            mul_le_mul_of_nonneg_right hexp_le (norm_nonneg _)
        _ ≤ (1 + 2 * ((k : ℝ) * |ε₁ x|)) * (Real.exp (C / ((w x : ℕ) : ℝ)) - 1) :=
            mul_le_mul_of_nonneg_left hMbound (by linarith [h2k1])
    have hexp1 : Real.exp ((k : ℝ) * |ε₁ x|) - 1 ≤ 2 * ((k : ℝ) * |ε₁ x|) :=
      exp_sub_one_le_two_mul hkabs0 hkabs1
    nlinarith [h2, hprod_b, hexp1, h2k1, hexpta]

/-- **P8 (41), family form with a single vanishing error.**  The tail factor
`2·(exp(C/w(x)) − 1)` of `kernel_pole_asymptotic_family` itself vanishes because
`w(x) → ∞`, so the two-part bound can be absorbed into one `ε → 0`. -/
theorem kernel_pole_asymptotic_family_eps (k : ℕ) (hk : 1 ≤ k)
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x → ∀ ξ ξ' : Fin k → ℝ,
        (∀ j, |ξ j| ≤ Real.sqrt (Real.log (x : ℝ))) →
        (∀ j, |ξ' j| ≤ Real.sqrt (Real.log (x : ℝ))) →
        ∃ L : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter ((W x) * (N x)) n,
            coordLocalK p (fun j => logZ (ξ j) x) (fun j => logZ (ξ' j) x)) atTop (𝓝 L) ∧
          ‖L * (∏ j : Fin k, poleFactor (W x) (N x) (ξ j) (ξ' j) x) - 1‖ ≤ ε x := by
  obtain ⟨C, hC0, x₀, ε, hε, hbound⟩ :=
    kernel_pole_asymptotic_family k hk W N hW hN hcop w hw hsmall hlq
  have hwR : Tendsto (fun x : ℕ => ((w x : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hw
  have h1 : Tendsto (fun x : ℕ => C / ((w x : ℕ) : ℝ)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hwR
  have h2 : Tendsto (fun x : ℕ => Real.exp (C / ((w x : ℕ) : ℝ))) atTop (𝓝 1) := by
    have := (Real.continuous_exp.tendsto 0).comp h1
    simpa [Function.comp_def, Real.exp_zero] using this
  have h3 : Tendsto (fun x : ℕ => 2 * (Real.exp (C / ((w x : ℕ) : ℝ)) - 1)) atTop (𝓝 0) := by
    have := (h2.sub_const 1).const_mul 2
    simpa using this
  refine ⟨x₀, fun x => ε x + 2 * (Real.exp (C / ((w x : ℕ) : ℝ)) - 1), ?_, ?_⟩
  · simpa using hε.add h3
  · intro x hx ξ ξ' hξ hξ'
    obtain ⟨L, hL, hb⟩ := hbound x hx ξ ξ' hξ hξ'
    exact ⟨L, hL, hb⟩

end Commons.NumberTheory.MaynardSieve
