import Mathlib
import Submission.Work.FIArea4.Wloc_eq_classSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Parseval / large-sieve inequality for the additive characters mod `q`

For a summable sequence `c : ℤ → ℂ`, the additive Fourier coefficients
`S_a = ∑_m c_m e(ma/q)` (`a = 0, …, q-1`) satisfy

  `∑_{a < q} |S_a|² ≤ q · M · ∑_m |c_m|`,

whenever every residue-class fibre of `∑|c_m|` is bounded by `M`, i.e.
`∑_{m ≡ n (q)} |c_m| ≤ M` for every `n : ZMod q`.

This is the standard Plancherel identity combined with the trivial bound on each
residue class.  Writing `K_C = ∑_{m ≡ C (q)} c_m` for the class sums, the proof is

  `∑_a |S_a|² = ∑_a |∑_C K_C e(aC/q)|² = q ∑_C |K_C|² ≤ q ∑_C W_C² ≤ q M ∑_C W_C = q M ∑_m |c_m|`,

where `W_C = ∑_{m ≡ C (q)} |c_m| ≤ M` is the class norm sum and `∑_C W_C = ∑_m |c_m|`.
-/

namespace Work.FIArea4.Vflip

open scoped BigOperators

noncomputable section

/-- Summability of the residue-restricted `ℂ`-valued sequence `m ↦ 𝟙_{m ≡ C (q)} c_m * w`. -/
private lemma summable_ite_mul (q : ℕ) (C : ℕ) (c : ℤ → ℂ) (hc : Summable c) (a : ℕ) :
    Summable (fun m : ℤ =>
      if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then c m * Work.FIArea4.EE q ((a:ℤ)*C) else 0) := by
  refine Summable.of_norm_bounded hc.norm (fun m => ?_)
  by_cases h : m % (q:ℤ) = (C:ℤ) % (q:ℤ)
  · rw [if_pos h, norm_mul, Work.FIArea4.norm_EE, mul_one]
  · rw [if_neg h, norm_zero]; exact norm_nonneg _

/-- Summability of the residue-restricted norm sequence `m ↦ 𝟙_{m ≡ C (q)} ‖c_m‖`. -/
private lemma summable_ite_norm (q : ℕ) (C : ℕ) (c : ℤ → ℂ) (hc : Summable c) :
    Summable (fun m : ℤ => if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then ‖c m‖ else 0) := by
  refine Summable.of_norm_bounded hc.norm (fun m => ?_)
  by_cases h : m % (q:ℤ) = (C:ℤ) % (q:ℤ)
  · simp [h]
  · rw [if_neg h, norm_zero]; exact norm_nonneg _

/-- Summability of the residue-restricted sequence `m ↦ 𝟙_{m ≡ C (q)} c_m`. -/
private lemma summable_ite_c (q : ℕ) (C : ℕ) (c : ℤ → ℂ) (hc : Summable c) :
    Summable (fun m : ℤ => if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then c m else 0) := by
  refine Summable.of_norm_bounded hc.norm (fun m => ?_)
  by_cases h : m % (q:ℤ) = (C:ℤ) % (q:ℤ)
  · simp [h]
  · rw [if_neg h, norm_zero]; exact norm_nonneg _

theorem parseval_zmod_le (q : ℕ) (hq : 1 ≤ q) (c : ℤ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hc : Summable c)
    (hM : ∀ n : ZMod q, (∑' m : ℤ, if (m : ZMod q) = n then ‖c m‖ else 0) ≤ M) :
    (∑ a ∈ Finset.range q, Complex.normSq (∑' m : ℤ, c m * Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ))))
      ≤ (q:ℝ) * M * (∑' m : ℤ, ‖c m‖) := by
  have hq0 : q ≠ 0 := by omega
  have hq0Z : (q:ℤ) ≠ 0 := by exact_mod_cast hq0
  -- the exponential of the statement is `EE`
  have h_exp : ∀ (a : ℕ) (m : ℤ),
      Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ)) = Work.FIArea4.EE q ((a:ℤ)*m) := by
    intro a m
    unfold Work.FIArea4.EE
    congr 1
    push_cast
    ring
  -- the `%`-residue condition agrees with the `ZMod`-residue condition
  have hfiber : ∀ C : ℕ,
      (∑' m : ℤ, (if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then ‖c m‖ else 0))
        = (∑' m : ℤ, (if (m : ZMod q) = (C : ZMod q) then ‖c m‖ else 0)) := by
    intro C
    apply tsum_congr; intro m
    have hiff : (m % (q:ℤ) = (C:ℤ) % (q:ℤ)) ↔ ((m : ZMod q) = (C : ZMod q)) := by
      rw [show (C : ZMod q) = ((C:ℤ) : ZMod q) from by push_cast; rfl]
      exact (ZMod.intCast_eq_intCast_iff' m (C:ℤ) q).symm
    by_cases h : m % (q:ℤ) = (C:ℤ) % (q:ℤ)
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]
  -- the class sums `K` and the class norm sums `W`
  set K : ℕ → ℂ := fun C => ∑' m : ℤ, (if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then c m else 0) with hK
  set W : ℕ → ℝ := fun C => ∑' m : ℤ, (if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then ‖c m‖ else 0) with hW
  have hWM : ∀ C : ℕ, W C ≤ M := by
    intro C
    simp only [hW, hfiber C]
    exact hM (C : ZMod q)
  have hWnn : ∀ C : ℕ, 0 ≤ W C := by
    intro C
    rw [hW]
    exact tsum_nonneg (fun m => by by_cases h : m % (q:ℤ) = (C:ℤ) % (q:ℤ) <;> simp [h])
  -- Fourier expansion of the coefficients in terms of the class sums
  have hS : ∀ a : ℕ, (∑' m : ℤ, c m * Work.FIArea4.EE q ((a:ℤ)*m))
      = ∑ C ∈ Finset.range q, K C * Work.FIArea4.EE q ((a:ℤ)*C) := by
    intro a
    have hsumm : ∀ C ∈ Finset.range q, Summable (fun m : ℤ =>
        if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then c m * Work.FIArea4.EE q ((a:ℤ)*C) else 0) :=
      fun C _ => summable_ite_mul q C c hc a
    rw [eq_comm]
    calc ∑ C ∈ Finset.range q, K C * Work.FIArea4.EE q ((a:ℤ)*C)
        = ∑ C ∈ Finset.range q, ∑' m : ℤ,
            (if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then c m * Work.FIArea4.EE q ((a:ℤ)*C) else 0) := by
          apply Finset.sum_congr rfl; intro C _
          rw [hK, ← tsum_mul_right]
          exact tsum_congr (fun m => by by_cases h : m % (q:ℤ) = (C:ℤ) % (q:ℤ) <;> simp [h])
      _ = ∑' m : ℤ, ∑ C ∈ Finset.range q,
            (if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then c m * Work.FIArea4.EE q ((a:ℤ)*C) else 0) :=
          (Summable.tsum_finsetSum hsumm).symm
      _ = ∑' m : ℤ, c m * Work.FIArea4.EE q ((a:ℤ)*m) := by
          apply tsum_congr; intro m
          have hfac : (∑ C ∈ Finset.range q,
              (if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then c m * Work.FIArea4.EE q ((a:ℤ)*C) else 0))
              = c m * ∑ C ∈ Finset.range q,
                  (if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then Work.FIArea4.EE q ((a:ℤ)*C) else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro C _
            by_cases h : m % (q:ℤ) = (C:ℤ) % (q:ℤ) <;> simp [h]
          rw [hfac, Work.FIArea4.sum_ite_EE q hq0 a m]
  -- termwise bound on the class sums
  have hnormK : ∀ C : ℕ, Complex.normSq (K C) ≤ W C * M := by
    intro C
    have h1 : ‖K C‖ ≤ W C := by
      rw [hK, hW]
      refine le_trans (norm_tsum_le_tsum_norm (summable_ite_c q C c hc).norm)
        (le_of_eq (tsum_congr (fun m => ?_)))
      by_cases h : m % (q:ℤ) = (C:ℤ) % (q:ℤ) <;> simp [h]
    calc Complex.normSq (K C) = ‖K C‖ ^ 2 := Complex.normSq_eq_norm_sq _
      _ ≤ (W C) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = W C * W C := by ring
      _ ≤ W C * M := mul_le_mul_of_nonneg_left (hWM C) (hWnn C)
  -- the class norm sums add up to the total norm
  have hWsum : ∑ C ∈ Finset.range q, W C = ∑' m : ℤ, ‖c m‖ := by
    have hinner : ∀ m : ℤ, ∑ C ∈ Finset.range q,
        (if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then ‖c m‖ else 0) = ‖c m‖ := by
      intro m
      set r : ℕ := (m % (q:ℤ)).toNat with hr
      have hmnn : 0 ≤ m % (q:ℤ) := Int.emod_nonneg m hq0Z
      have hmlt : m % (q:ℤ) < (q:ℤ) :=
        Int.emod_lt_of_pos m (by exact_mod_cast Nat.pos_of_ne_zero hq0)
      have hrc : (r : ℤ) = m % (q:ℤ) := Int.toNat_of_nonneg hmnn
      have hrlt : r < q := by
        have : (r : ℤ) < (q:ℤ) := by rw [hrc]; exact hmlt
        exact_mod_cast this
      have hstep : ∀ C ∈ Finset.range q,
          (if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then ‖c m‖ else 0) = (if C = r then ‖c m‖ else 0) := by
        intro C hC
        have hCq : (C : ℤ) < (q:ℤ) := by exact_mod_cast Finset.mem_range.mp hC
        have hCmod : ((C:ℤ) % (q:ℤ)) = (C:ℤ) := Int.emod_eq_of_lt (Int.natCast_nonneg C) hCq
        rw [hCmod, ← hrc]
        have hiff : ((r:ℤ) = (C:ℤ)) ↔ (C = r) := by rw [Int.ofNat_inj, eq_comm]
        by_cases h : (r:ℤ) = (C:ℤ)
        · rw [if_pos h, if_pos (hiff.mp h)]
        · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
      rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hrlt)]
    calc ∑ C ∈ Finset.range q, W C
        = ∑ C ∈ Finset.range q, ∑' m : ℤ,
            (if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then ‖c m‖ else 0) :=
          Finset.sum_congr rfl (fun C _ => by rw [hW])
      _ = ∑' m : ℤ, ∑ C ∈ Finset.range q,
            (if m % (q:ℤ) = (C:ℤ) % (q:ℤ) then ‖c m‖ else 0) :=
          (Summable.tsum_finsetSum (fun C _ => summable_ite_norm q C c hc)).symm
      _ = ∑' m : ℤ, ‖c m‖ := tsum_congr hinner
  calc
    (∑ a ∈ Finset.range q,
        Complex.normSq (∑' m : ℤ, c m * Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ))))
        = ∑ a ∈ Finset.range q,
            Complex.normSq (∑' m : ℤ, c m * Work.FIArea4.EE q ((a:ℤ)*m)) := by
          apply Finset.sum_congr rfl; intro a _
          congr 1
          exact tsum_congr (fun m => by rw [h_exp a m])
      _ = ∑ a ∈ Finset.range q,
            Complex.normSq (∑ C ∈ Finset.range q, K C * Work.FIArea4.EE q ((a:ℤ)*C)) := by
          apply Finset.sum_congr rfl; intro a _
          rw [hS a]
      _ = (q:ℝ) * ∑ C ∈ Finset.range q, Complex.normSq (K C) :=
          Work.FIArea4.parseval_EE q hq0 K
      _ ≤ (q:ℝ) * (M * ∑' m : ℤ, ‖c m‖) := by
          apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast Nat.zero_le q)
          calc ∑ C ∈ Finset.range q, Complex.normSq (K C)
              ≤ ∑ C ∈ Finset.range q, W C * M := Finset.sum_le_sum (fun C _ => hnormK C)
            _ = (∑ C ∈ Finset.range q, W C) * M := by rw [Finset.sum_mul]
            _ = (∑' m : ℤ, ‖c m‖) * M := by rw [hWsum]
            _ = M * ∑' m : ℤ, ‖c m‖ := by ring
      _ = (q:ℝ) * M * (∑' m : ℤ, ‖c m‖) := by ring

end

end Work.FIArea4.Vflip
