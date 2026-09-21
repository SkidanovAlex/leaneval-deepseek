import Mathlib
import Submission.Work.OddVolterra.KernelExt.Defs

/-!
# Lipschitz-in-`t` bounds for the jets of the radicand `Zrad`

`Zrad h (s, σ, t) = line h σ t ^ 2 - line h s t ^ 2 = (σ t + h σ) ^ 2 - (s t + h s) ^ 2`
(`Work.OddVolterra.KernelExt.Defs`) is the radicand of the odd Abel kernel, viewed as a function
of its first argument `s`.  This file proves that all its `s`-jets up to order `n + 2` are
Lipschitz in `t` with a constant depending only on `n`, uniformly over `h` that is `C^∞` and whose
jets up to order `n + 2` are bounded by `1/100`, and over `σ, a ∈ [9/20, 1]`, `t, t' ∈ [-2, 2]`.

The proof is elementary.  Writing `c = t + t'`, the finite difference of the radicand is

`Zrad h (v,σ,t) - Zrad h (v,σ,t') = (t - t') · (σ (σ c + 2 h σ) - v (v c + 2 h v))`,

so (for `j ≥ 1`, when the constant term drops out) the difference of the two `j`-jets is `(t-t')`
times the `j`-jet of a *single* function `v ↦ v (v c + 2 h v)` of `v` alone.  That jet is bounded
by the Leibniz (product) rule for `iteratedDeriv` together with the Leibniz rule bounds on the
jets of `v ↦ v c + 2 h v`, which in turn are bounded by `|c| ≤ 4` and `|h^{(k)}| ≤ 1/100`.
-/

open scoped Topology ContDiff

namespace Work.OddVolterra.Window

noncomputable section

private lemma abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg] using abs_add_le x (-y)

/-- The jets of a linear function `v ↦ c * v`. -/
private lemma iteratedDeriv_linear_form (c a : ℝ) (k : ℕ) :
    iteratedDeriv k (fun v : ℝ => c * v) a = if k = 0 then c * a else if k = 1 then c else 0 := by
  rw [show (fun v : ℝ => c * v) = fun v => c * id v from rfl,
    iteratedDeriv_const_mul (c := c) (f := id) contDiffAt_id, iteratedDeriv_id]
  split_ifs <;> ring

/-- **Leibniz bound.**  If the jets of `f` and `g` at `a` up to order `N` are bounded by `A`
and `B`, then the jets of the product are bounded by `A * B * 2^N`. -/
private lemma jet_mul_le_aux {f g : ℝ → ℝ} {N : ℕ} {a A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ k ≤ N, |iteratedDeriv k f a| ≤ A) (hg : ∀ k ≤ N, |iteratedDeriv k g a| ≤ B)
    (hf' : ContDiffAt ℝ (N : ℕ) f a) (hg' : ContDiffAt ℝ (N : ℕ) g a) :
    ∀ j ≤ N, |iteratedDeriv j (f * g) a| ≤ A * B * 2 ^ N := by
  intro j hj
  rw [iteratedDeriv_mul (hf'.of_le (by exact_mod_cast hj)) (hg'.of_le (by exact_mod_cast hj))]
  have h1 : |∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * iteratedDeriv i f a * iteratedDeriv (j - i) g a|
      ≤ ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℝ) * A * B) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    have hiN : i ≤ N := by omega
    have hjiN : j - i ≤ N := by omega
    have hCi : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg hCi]
    calc (j.choose i : ℝ) * |iteratedDeriv i f a| * |iteratedDeriv (j - i) g a|
        ≤ (j.choose i : ℝ) * A * |iteratedDeriv (j - i) g a| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hf i hiN) hCi) (abs_nonneg _)
      _ ≤ (j.choose i : ℝ) * A * B :=
          mul_le_mul_of_nonneg_left (hg (j - i) hjiN) (mul_nonneg hCi hA)
  refine h1.trans ?_
  have hsum : ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℝ) * A * B)
      = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * (A * B) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi; ring
  rw [hsum]
  have hchoose : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  rw [hchoose]
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  calc (2 : ℝ) ^ j * (A * B) ≤ (2 : ℝ) ^ N * (A * B) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hAB
    _ = A * B * 2 ^ N := by ring

/-- `Zrad h (·, σ, t)` written out. -/
private lemma zrad_eq (h : ℝ → ℝ) (σ t : ℝ) :
    (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t))
      = fun v => (σ * t + h σ) ^ 2 - (t * v + h v) ^ 2 := by
  funext v
  simp only [Work.OddVolterra.KernelExt.Zrad, Work.OddVolterra.line]
  ring

/-- `Zrad h (·, σ, t)` is smooth at every point, at every finite order. -/
private lemma contDiffAt_zrad {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t a : ℝ) (m : ℕ) :
    ContDiffAt ℝ (m : ℕ) (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t)) a := by
  rw [zrad_eq h σ t]
  have h2 : ContDiffAt ℝ (m:ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have h1 : ContDiffAt ℝ (m : ℕ) (fun v : ℝ => t * v + h v) a := by
    have := (contDiffAt_const (c := t) : ContDiffAt ℝ (m:ℕ) (fun _ : ℝ => t) a).mul contDiffAt_id
    simpa using this.add h2
  exact contDiffAt_const.sub (h1.pow 2)

theorem TWU_zrad_jet_lipschitz (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ∀ σ ∈ Set.Icc (9 / 20 : ℝ) 1, ∀ a ∈ Set.Icc (9 / 20 : ℝ) 1,
      ∀ j : ℕ, j ≤ n + 2 → ∀ t ∈ Set.Icc (-2 : ℝ) 2, ∀ t' ∈ Set.Icc (-2 : ℝ) 2,
        |iteratedDeriv j (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t)) a -
         iteratedDeriv j (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t')) a|
          ≤ K * |t - t'| := by
  refine ⟨100 * 2 ^ (n + 2), by positivity, ?_⟩
  intro h hh hjet σ hσ a ha j hj t ht t' ht'
  have hpow1 : (1 : ℝ) ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
  have hσabs : |σ| ≤ 1 := abs_le.mpr ⟨by linarith [hσ.1], hσ.2⟩
  have haabs : |a| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1], ha.2⟩
  have htabs : |t| ≤ 2 := abs_le.mpr ⟨ht.1, ht.2⟩
  have ht'abs : |t'| ≤ 2 := abs_le.mpr ⟨ht'.1, ht'.2⟩
  have hc4 : |t + t'| ≤ 4 := by have := abs_add_le t t'; linarith
  have hh0s : |h σ| ≤ 1 / 100 := by simpa using hjet 0 (by omega) σ
  have hh0a : |h a| ≤ 1 / 100 := by simpa using hjet 0 (by omega) a
  have hhAt : ∀ (m : ℕ) (x : ℝ), ContDiffAt ℝ (m : ℕ) h x :=
    fun m x => hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  -- the finite difference of the two radicands is `(t - t')` times a function of `v` alone
  have hsub : iteratedDeriv j (fun v : ℝ => KernelExt.Zrad h (v, σ, t) - KernelExt.Zrad h (v, σ, t')) a
      = iteratedDeriv j (fun v : ℝ => KernelExt.Zrad h (v, σ, t)) a -
        iteratedDeriv j (fun v : ℝ => KernelExt.Zrad h (v, σ, t')) a :=
    iteratedDeriv_sub (contDiffAt_zrad hh σ t a j) (contDiffAt_zrad hh σ t' a j)
  have hdiff : (fun v : ℝ => KernelExt.Zrad h (v, σ, t) - KernelExt.Zrad h (v, σ, t'))
      = fun v => (t - t') * (σ * (σ * (t + t') + 2 * h σ) - v * (v * (t + t') + 2 * h v)) := by
    funext v
    simp only [Work.OddVolterra.KernelExt.Zrad, Work.OddVolterra.line]
    ring
  rw [← hsub, hdiff]
  have hWcd : ContDiffAt ℝ (j : ℕ)
      (fun v : ℝ => σ * (σ * (t + t') + 2 * h σ) - v * (v * (t + t') + 2 * h v)) a := by
    apply ContDiffAt.sub contDiffAt_const
    apply ContDiffAt.mul contDiffAt_id
    apply ContDiffAt.add
    · exact contDiffAt_id.mul (contDiffAt_const (c := t + t'))
    · exact (contDiffAt_const (c := (2 : ℝ))).mul (hhAt j a)
  rw [iteratedDeriv_const_mul (c := t - t')
    (f := fun v : ℝ => σ * (σ * (t + t') + 2 * h σ) - v * (v * (t + t') + 2 * h v)) hWcd, abs_mul]
  have hWbound : |iteratedDeriv j
      (fun v : ℝ => σ * (σ * (t + t') + 2 * h σ) - v * (v * (t + t') + 2 * h v)) a|
        ≤ 100 * 2 ^ (n + 2) := by
    by_cases hj0 : j = 0
    · -- the value itself: both quadratic terms are bounded by 5
      subst hj0
      rw [iteratedDeriv_zero]
      have hσb : |σ * (σ * (t + t') + 2 * h σ)| ≤ 5 := by
        rw [abs_mul]
        have hx : |σ * (t + t') + 2 * h σ| ≤ 5 := by
          have h3 : |σ * (t + t')| ≤ 4 := by
            rw [abs_mul]; nlinarith [hσabs, hc4, abs_nonneg σ, abs_nonneg (t + t')]
          have h4 : |2 * h σ| ≤ 1 := by
            rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
            linarith [hh0s]
          linarith [abs_add_le (σ * (t + t')) (2 * h σ)]
        nlinarith [hσabs, hx, abs_nonneg σ, abs_nonneg (σ * (t + t') + 2 * h σ)]
      have hab : |a * (a * (t + t') + 2 * h a)| ≤ 5 := by
        rw [abs_mul]
        have hx : |a * (t + t') + 2 * h a| ≤ 5 := by
          have h3 : |a * (t + t')| ≤ 4 := by
            rw [abs_mul]; nlinarith [haabs, hc4, abs_nonneg a, abs_nonneg (t + t')]
          have h4 : |2 * h a| ≤ 1 := by
            rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
            linarith [hh0a]
          linarith [abs_add_le (a * (t + t')) (2 * h a)]
        nlinarith [haabs, hx, abs_nonneg a, abs_nonneg (a * (t + t') + 2 * h a)]
      calc |σ * (σ * (t + t') + 2 * h σ) - a * (a * (t + t') + 2 * h a)|
          ≤ |σ * (σ * (t + t') + 2 * h σ)| + |a * (a * (t + t') + 2 * h a)| :=
            abs_sub_le_abs_add _ _
        _ ≤ 5 + 5 := add_le_add hσb hab
        _ ≤ 100 * 2 ^ (n + 2) := by nlinarith [hpow1]
    · -- `j ≥ 1`: the constant term differentiated away, and `v ↦ v * (v c + 2 h v)` is bounded
      have hj1 : 1 ≤ j := by omega
      have hUcd : ContDiffAt ℝ (j : ℕ) (fun v : ℝ => v * (t + t') + 2 * h v) a := by
        apply ContDiffAt.add
        · exact contDiffAt_id.mul (contDiffAt_const (c := t + t'))
        · exact (contDiffAt_const (c := (2 : ℝ))).mul (hhAt j a)
      have hUcdN : ContDiffAt ℝ ((n + 2 : ℕ) : ℕ)
          (fun v : ℝ => v * (t + t') + 2 * h v) a := by
        apply ContDiffAt.add
        · exact contDiffAt_id.mul (contDiffAt_const (c := t + t'))
        · exact (contDiffAt_const (c := (2 : ℝ))).mul (hhAt (n+2) a)
      have hvu : ContDiffAt ℝ (j : ℕ) (id * fun v : ℝ => v * (t + t') + 2 * h v) a :=
        contDiffAt_id.mul hUcd
      have hfeq : (fun v : ℝ => σ * (σ * (t + t') + 2 * h σ) - v * (v * (t + t') + 2 * h v))
          = (fun _ : ℝ => σ * (σ * (t + t') + 2 * h σ)) -
            (id * fun v : ℝ => v * (t + t') + 2 * h v) := by
        funext v; simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
      rw [hfeq, iteratedDeriv_sub contDiffAt_const hvu, iteratedDeriv_const, if_neg hj0,
        zero_sub, abs_neg]
      have hUj : ∀ k ≤ n + 2, |iteratedDeriv k (fun v : ℝ => v * (t + t') + 2 * h v) a| ≤ 5 := by
        intro k hk
        have hcd1 : ContDiffAt ℝ (k : ℕ) (fun v : ℝ => v * (t + t')) a :=
          contDiffAt_id.mul (contDiffAt_const (c := t + t'))
        have hcd2 : ContDiffAt ℝ (k : ℕ) (fun v : ℝ => (2 : ℝ) * h v) a :=
          (contDiffAt_const (c := (2 : ℝ))).mul (hhAt k a)
        rw [show (fun v : ℝ => v * (t + t') + 2 * h v)
              = (fun v : ℝ => v * (t + t')) + (fun v : ℝ => (2 : ℝ) * h v) from rfl,
          iteratedDeriv_add hcd1 hcd2,
          show (fun v : ℝ => v * (t + t')) = (fun v : ℝ => (t + t') * v) by funext v; ring,
          iteratedDeriv_linear_form (t + t') a k,
          iteratedDeriv_const_mul (2 : ℝ) (hhAt k a)]
        have hA : |(if k = 0 then (t + t') * a else if k = 1 then (t + t') else 0)| ≤ 4 := by
          split_ifs with h0 h1
          · rw [abs_mul]; nlinarith [hc4, haabs, abs_nonneg (t + t'), abs_nonneg a]
          · exact hc4
          · norm_num
        have hB : |2 * iteratedDeriv k h a| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
          linarith [hjet k hk a]
        calc |(if k = 0 then (t + t') * a else if k = 1 then (t + t') else 0) + 2 * iteratedDeriv k h a|
            ≤ |(if k = 0 then (t + t') * a else if k = 1 then (t + t') else 0)| +
              |2 * iteratedDeriv k h a| := abs_add_le _ _
          _ ≤ 4 + 1 := add_le_add hA hB
          _ ≤ 5 := by norm_num
      have hidj : ∀ k ≤ n + 2, |iteratedDeriv k id a| ≤ 1 := by
        intro k hk
        rw [iteratedDeriv_id]
        split_ifs
        · exact haabs
        · norm_num
        · norm_num
      have hmul := jet_mul_le_aux (f := id) (g := fun v : ℝ => v * (t + t') + 2 * h v)
        (N := n + 2) (a := a) (A := 1) (B := 5) (by norm_num) (by norm_num) hidj hUj
        contDiffAt_id hUcdN j hj
      calc |iteratedDeriv j (id * fun v : ℝ => v * (t + t') + 2 * h v) a|
          ≤ 1 * 5 * 2 ^ (n + 2) := hmul
        _ ≤ 100 * 2 ^ (n + 2) := by nlinarith [hpow1]
  calc |t - t'| * |iteratedDeriv j
        (fun v : ℝ => σ * (σ * (t + t') + 2 * h σ) - v * (v * (t + t') + 2 * h v)) a|
      ≤ |t - t'| * (100 * 2 ^ (n + 2)) := mul_le_mul_of_nonneg_left hWbound (abs_nonneg _)
    _ = 100 * 2 ^ (n + 2) * |t - t'| := by ring

end

end Work.OddVolterra.Window
