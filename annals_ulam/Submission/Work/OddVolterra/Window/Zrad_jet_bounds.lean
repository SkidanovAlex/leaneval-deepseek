import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs

/-!
# Jet bounds for the radicand `Zrad` on the transition window

`Zrad h (s,σ,t) = line h σ t ^ 2 - line h s t ^ 2 = (σ t + h σ) ^ 2 - (s t + h s) ^ 2`
(`Work.OddVolterra.KernelExt.Defs`), the radicand of the odd Abel kernel, viewed as a function
of its first argument `s` and its derivatives with respect to `s`.

`Zrad_jet_bounds` is the elementary Lipschitz-in-`h` estimate on the window
`σ ∈ [7/10,1]`, `|t| ≤ 2`, `a ∈ [9/20,1]`: the first `n+2` derivatives in `s` of
`Zrad h (·,σ,t)` are bounded by a constant `B = B(n)` depending only on how small `h` is in
`C^{n+2}`, and the difference from the corresponding derivatives of the unperturbed radicand
`Zrad 0 (·,σ,t) = (σt)^2 - (st)^2` is bounded by `B δ` when `h` is `δ`-small in `C^{n+2}`.

Everything here is a polynomial expression in `t`, `x` and the jet `(h^{(k)} x)_{k ≤ n+2}`,
so the argument is the Leibniz (product) rule for `iteratedDeriv` together with the crude
estimate `|h^{(k)}| ≤ δ ≤ 1`.  The bound `B = 100 · 2^{n+2}` is generous on purpose.
-/

open scoped Topology ContDiff

namespace Work.OddVolterra.Window

open Work.OddVolterra

noncomputable section

/-! ### Elementary jet estimates -/

/-- `|x - y| ≤ |x| + |y|`. -/
private lemma abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg] using abs_add_le x (-y)

/-- **Leibniz bound.**  If the jets of `f` and `g` at `a` up to order `N` are bounded by `A`
and `B`, then the jets of the product are bounded by `A * B * 2^N`. -/
private lemma jet_mul_le {f g : ℝ → ℝ} {N : ℕ} {a A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
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

/-- The Leibniz bound for a square. -/
private lemma jet_sq_le {u : ℝ → ℝ} {N : ℕ} {a A : ℝ} (hA : 0 ≤ A)
    (hu : ∀ k ≤ N, |iteratedDeriv k u a| ≤ A) (hu' : ContDiffAt ℝ (N : ℕ) u a) :
    ∀ j ≤ N, |iteratedDeriv j (fun v => u v ^ 2) a| ≤ A * A * 2 ^ N := by
  intro j hj
  have h := jet_mul_le hA hA hu hu hu' hu' j hj
  have he : (fun v : ℝ => u v ^ 2) = u * u := by funext v; simp only [Pi.mul_apply]; ring
  rwa [he]

/-- The jets of a linear function `v ↦ c * v`. -/
private lemma iteratedDeriv_linear_form (c a : ℝ) (k : ℕ) :
    iteratedDeriv k (fun v : ℝ => c * v) a = if k = 0 then c * a else if k = 1 then c else 0 := by
  rw [show (fun v : ℝ => c * v) = fun v => c * id v from rfl,
    iteratedDeriv_const_mul (c := c) (f := id) contDiffAt_id, iteratedDeriv_id]
  split_ifs <;> ring

/-- Jet bound for a linear function. -/
private lemma abs_iteratedDeriv_linear_le {c a R : ℝ} (hR : 0 ≤ R) (k : ℕ)
    (hc : |c| ≤ R) (hca : |c * a| ≤ R) :
    |iteratedDeriv k (fun v : ℝ => c * v) a| ≤ R := by
  rw [iteratedDeriv_linear_form]
  split_ifs
  · simpa using hca
  · simpa using hc
  · simpa using hR

/-- Smoothness of a linear function at any finite order. -/
private lemma contDiffAt_linear (c a : ℝ) (N : ℕ) :
    ContDiffAt ℝ (N : ℕ) (fun v : ℝ => c * v) a := by fun_prop

/-- Smoothness of `v ↦ c * v + h v` at any finite order. -/
private lemma contDiffAt_linear_add {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (c a : ℝ) (N : ℕ) :
    ContDiffAt ℝ (N : ℕ) (fun v : ℝ => c * v + h v) a := by
  have h1 : ContDiffAt ℝ (N : ℕ) (fun v : ℝ => c * v) a := contDiffAt_linear c a N
  have h2 : ContDiffAt ℝ (N : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  simpa using h1.add h2

/-- The jets of `v ↦ c * v + h v`. -/
private lemma iteratedDeriv_linear_add {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (c a : ℝ)
    (k : ℕ) :
    iteratedDeriv k (fun v : ℝ => c * v + h v) a
      = iteratedDeriv k (fun v : ℝ => c * v) a + iteratedDeriv k h a := by
  have h1 : ContDiffAt ℝ (k : ℕ) (fun v : ℝ => c * v) a := contDiffAt_linear c a k
  have h2 : ContDiffAt ℝ (k : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  change iteratedDeriv k ((fun v : ℝ => c * v) + h) a
      = iteratedDeriv k (fun v : ℝ => c * v) a + iteratedDeriv k h a
  rw [iteratedDeriv_add h1 h2]

/-- Jet bound for `v ↦ c * v + h v` in terms of the jets of `h`. -/
private lemma jet_bound_linear_add {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {c a δ C D : ℝ} (hC : 0 ≤ C) (hδ : δ ≤ D) (k : ℕ)
    (hc : |c| ≤ C) (hca : |c * a| ≤ C) (hj : |iteratedDeriv k h a| ≤ δ) :
    |iteratedDeriv k (fun v : ℝ => c * v + h v) a| ≤ C + D := by
  rw [iteratedDeriv_linear_add hh c a k]
  calc |iteratedDeriv k (fun v : ℝ => c * v) a + iteratedDeriv k h a|
      ≤ |iteratedDeriv k (fun v : ℝ => c * v) a| + |iteratedDeriv k h a| := abs_add_le _ _
    _ ≤ C + D := add_le_add (abs_iteratedDeriv_linear_le hC k hc hca) (le_trans hj hδ)

/-! ### The window bounds -/

theorem Zrad_jet_bounds (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ δ → δ ≤ 1 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1, ∀ t : ℝ, |t| ≤ 2 → ∀ a ∈ Set.Icc (9 / 20 : ℝ) 1,
        (∀ j : ℕ, j ≤ n + 2 →
          |iteratedDeriv j (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t)) a| ≤ B) ∧
        (∀ j : ℕ, j ≤ n + 2 →
          |iteratedDeriv j (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t)) a -
           iteratedDeriv j (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad 0 (v, σ, t)) a| ≤
             B * δ) := by
  refine ⟨(2 : ℝ) ^ (n + 2) * 100, by positivity, ?_⟩
  intro h δ hh hδ0 hδ1 hjet σ hσ t ht a ha
  have hpow : (4 : ℝ) ≤ 2 ^ (n + 2) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hσabs : |σ| ≤ 1 := abs_le.mpr ⟨by linarith [hσ.1], hσ.2⟩
  have haabs : |a| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1], ha.2⟩
  have hta : |t * a| ≤ 2 := by rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg a]
  have htσ : |t * σ| ≤ 2 := by rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg σ]
  have hha : ∀ k, k ≤ n + 2 → |iteratedDeriv k h a| ≤ δ := fun k hk => hjet k hk a
  have h2t : |2 * t| ≤ 4 := by
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith [abs_nonneg t, ht]
  have hlin : ∀ x : ℝ, |x| ≤ 1 → |2 * t * x + h x| ≤ 5 := by
    intro x hx
    have h2tx : |2 * t * x| ≤ 4 := by
      rw [abs_mul]; nlinarith [h2t, hx, abs_nonneg x]
    calc |2 * t * x + h x| ≤ |2 * t * x| + |h x| := abs_add_le _ _
      _ ≤ 4 + δ := add_le_add h2tx (hjet 0 (by omega) x)
      _ ≤ 5 := by linarith
  have hP3 : ∀ k ≤ n + 2, |iteratedDeriv k (fun v : ℝ => t * v + h v) a| ≤ 3 := by
    intro k hk
    have h := jet_bound_linear_add hh (c := t) (a := a) (δ := δ) (C := 2) (D := 1)
      (by norm_num) hδ1 k ht hta (hha k hk)
    linarith
  have hQ5 : ∀ k ≤ n + 2, |iteratedDeriv k (fun v : ℝ => 2 * t * v + h v) a| ≤ 5 := by
    intro k hk
    have h2ta : |2 * t * a| ≤ 4 := by
      rw [abs_mul]; nlinarith [h2t, haabs, abs_nonneg a]
    have h := jet_bound_linear_add hh (c := 2 * t) (a := a) (δ := δ) (C := 4) (D := 1)
      (by norm_num) hδ1 k h2t h2ta (hha k hk)
    linarith
  have hhA : ContDiffAt ℝ (n + 2 : ℕ) h a :=
    hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hFu : (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t))
      = fun v => (t * σ + h σ) ^ 2 - (t * v + h v) ^ 2 := by
    funext v
    simp only [Work.OddVolterra.KernelExt.Zrad, Work.OddVolterra.line]
    ring
  have hF0u : (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad 0 (v, σ, t))
      = fun v => (t * σ) ^ 2 - (t * v) ^ 2 := by
    funext v
    simp only [Work.OddVolterra.KernelExt.Zrad, Work.OddVolterra.line, Pi.zero_apply]
    ring
  have hDu : (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t))
        - (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad 0 (v, σ, t))
      = fun v => ((t * σ + h σ) ^ 2 - (t * σ) ^ 2) - h v * (2 * t * v + h v) := by
    funext v
    simp only [Pi.sub_apply, Work.OddVolterra.KernelExt.Zrad, Work.OddVolterra.line, Pi.zero_apply]
    ring
  constructor
  · intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      rw [hFu]
      simp only [iteratedDeriv_zero]
      have h1 : |t * σ + h σ| ≤ 3 := by
        calc |t * σ + h σ| ≤ |t * σ| + |h σ| := abs_add_le _ _
          _ ≤ 2 + δ := add_le_add htσ (hjet 0 (by omega) σ)
          _ ≤ 3 := by linarith
      have h2 : |t * a + h a| ≤ 3 := by
        calc |t * a + h a| ≤ |t * a| + |h a| := abs_add_le _ _
          _ ≤ 2 + δ := add_le_add hta (hha 0 (by omega))
          _ ≤ 3 := by linarith
      calc |(t * σ + h σ) ^ 2 - (t * a + h a) ^ 2|
          ≤ |(t * σ + h σ) ^ 2| + |(t * a + h a) ^ 2| := abs_sub_le_abs_add _ _
        _ = (t * σ + h σ) ^ 2 + (t * a + h a) ^ 2 := by
            rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
        _ ≤ 18 := by nlinarith [abs_le.mp h1, abs_le.mp h2]
        _ ≤ 2 ^ (n + 2) * 100 := by nlinarith [hpow]
    · have hj1 : 1 ≤ j := by omega
      rw [hFu]
      change |iteratedDeriv j ((fun _ : ℝ => (t * σ + h σ) ^ 2)
          - (fun v : ℝ => (t * v + h v) ^ 2)) a| ≤ 2 ^ (n + 2) * 100
      have hc2 : ContDiffAt ℝ (j : ℕ) (fun v : ℝ => (t * v + h v) ^ 2) a :=
        (contDiffAt_linear_add hh t a j).pow 2
      rw [iteratedDeriv_sub contDiffAt_const hc2, iteratedDeriv_const]
      simp only [if_neg hj0]
      rw [zero_sub, abs_neg]
      have hsq := jet_sq_le (u := fun v : ℝ => t * v + h v) (N := n + 2) (a := a) (A := 3)
        (by norm_num) hP3 (contDiffAt_linear_add hh t a (n + 2)) j hj
      calc |iteratedDeriv j (fun v : ℝ => (t * v + h v) ^ 2) a| ≤ 3 * 3 * 2 ^ (n + 2) := hsq
        _ ≤ 2 ^ (n + 2) * 100 := by nlinarith [hpow]
  · intro j hj
    have hhAt : ContDiffAt ℝ (j : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have hc1 : ContDiffAt ℝ (j : ℕ)
        (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t)) a := by
      rw [hFu]
      exact contDiffAt_const.sub ((contDiffAt_linear_add hh t a j).pow 2)
    have hc0 : ContDiffAt ℝ (j : ℕ)
        (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad 0 (v, σ, t)) a := by
      rw [hF0u]
      exact contDiffAt_const.sub ((contDiffAt_linear t a j).pow 2)
    have hsub := iteratedDeriv_sub hc1 hc0
    rw [← hsub, hDu]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [iteratedDeriv_zero]
      have h1 : |(t * σ + h σ) ^ 2 - (t * σ) ^ 2| ≤ 5 * δ := by
        have he : (t * σ + h σ) ^ 2 - (t * σ) ^ 2 = h σ * (2 * t * σ + h σ) := by ring
        rw [he, abs_mul]
        calc |h σ| * |2 * t * σ + h σ| ≤ δ * 5 :=
              mul_le_mul (hjet 0 (by omega) σ) (hlin σ hσabs) (abs_nonneg _) hδ0
          _ = 5 * δ := by ring
      have h2 : |h a * (2 * t * a + h a)| ≤ 5 * δ := by
        rw [abs_mul]
        calc |h a| * |2 * t * a + h a| ≤ δ * 5 :=
              mul_le_mul (hha 0 (by omega)) (hlin a haabs) (abs_nonneg _) hδ0
          _ = 5 * δ := by ring
      calc |((t * σ + h σ) ^ 2 - (t * σ) ^ 2) - h a * (2 * t * a + h a)|
          ≤ |(t * σ + h σ) ^ 2 - (t * σ) ^ 2| + |h a * (2 * t * a + h a)| :=
            abs_sub_le_abs_add _ _
        _ ≤ 5 * δ + 5 * δ := add_le_add h1 h2
        _ = 10 * δ := by ring
        _ ≤ 2 ^ (n + 2) * 100 * δ := by
            have h10 : (10 : ℝ) ≤ 2 ^ (n + 2) * 100 := by nlinarith [hpow]
            calc 10 * δ ≤ (2 ^ (n + 2) * 100) * δ := mul_le_mul_of_nonneg_right h10 hδ0
              _ = 2 ^ (n + 2) * 100 * δ := by ring
    · have hj1 : 1 ≤ j := by omega
      change |iteratedDeriv j ((fun _ : ℝ => ((t * σ + h σ) ^ 2 - (t * σ) ^ 2))
          - (h * fun v : ℝ => 2 * t * v + h v)) a| ≤ 2 ^ (n + 2) * 100 * δ
      have hg : ContDiffAt ℝ (j : ℕ) (h * fun v : ℝ => 2 * t * v + h v) a :=
        hhAt.mul (contDiffAt_linear_add hh (2 * t) a j)
      rw [iteratedDeriv_sub contDiffAt_const hg, iteratedDeriv_const]
      simp only [if_neg hj0]
      rw [zero_sub, abs_neg]
      have hmul := jet_mul_le (f := h) (g := fun v : ℝ => 2 * t * v + h v) (N := n + 2)
        (a := a) (A := δ) (B := 5) hδ0 (by norm_num) hha hQ5 hhA
        (contDiffAt_linear_add hh (2 * t) a (n + 2)) j hj
      calc |iteratedDeriv j (h * fun v : ℝ => 2 * t * v + h v) a| ≤ δ * 5 * 2 ^ (n + 2) := hmul
        _ ≤ 2 ^ (n + 2) * 100 * δ := by nlinarith [hpow, hδ0]

end

end Work.OddVolterra.Window
