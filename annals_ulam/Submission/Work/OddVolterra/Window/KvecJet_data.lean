import Mathlib
import Submission.Work.OddVolterra.Window.KvecDefs

/-!
# Bounds, smoothness and `O(δ)`-closeness of the jet curve `u ↦ KJet n h σ z u`

The jet curve `KJet` (`KvecDefs`) collects, at the point `u = a`, the two chord endpoints
`-z 0`, `z 1`, the two state components `z 2`, `z 3`, the two Abel radicands `krad h σ t a`, the
radicand jets `kjet h σ t a ·` up to order `n+1` (for `t = -z 0` and `t = z 1`) and the
derivatives `h' a, …, h^{(n+1)} a`.  This file proves that on the transition window
(`σ ∈ [7/10, 1]`, `a ∈ [9/20, σ]`, `|z i| ≤ 2`, `z 0, z 1 ≥ 1/5`, `h` supported in
`[1 - 2τ, 1 - τ]` and `δ`-small in `C^{n+2}` with `δ ≤ 1/100`)

* the jet takes its values in the compact box `KJbox n (KJbz n)` (the main theorem below);
* the jet curve `u ↦ KJet n h σ z u` is `C^∞` (`contDiff_KJet`), for `h` and for `h = 0`;
* the `u`-derivative of the jet curve is bounded by `KJbz n`, and the jet (and its derivative)
  of `h` is `KJbz n * δ`-close to the jet (resp. derivative) of the unperturbed `h = 0`.

Every component is estimated pointwise: the entries `aa`, `sg`, `t1`, `t2`, `c2`, `c3` are
constants or the point `a`; the two radicand entries are bounded by `1/100 ≤ krad ≤ 10` and
`O(δ)`-close by `kj_krad_data`; the radicand jets are the derivatives of `Zrad h (·,σ,t)`,
bounded by `KJbz n = 2^{n+2} · 100` and `O(δ)`-close by `kj_zrad_jet`; and the entries of the
last block `w` are derivatives of `h`, bounded by `δ` and `δ`-close to `0`.  This is exactly the
input the general jet-curve lemma `JetCurve_box` consumes in `Kvec_deriv_close`.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## Radicand jet bounds with an explicit constant -/

/-! The next block is `Zrad_jet_bounds` (`Window/Zrad_jet_bounds.lean`) with its private helpers,
copied here verbatim (and renamed) so that the constant `2 ^ (n+2) * 100 = KJbz n` is available
and is not hidden behind an existential. -/

/-- `|x - y| ≤ |x| + |y|`. -/
private lemma kj_abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg] using abs_add_le x (-y)

/-- **Leibniz bound.**  If the jets of `f` and `g` at `a` up to order `N` are bounded by `A`
and `B`, then the jets of the product are bounded by `A * B * 2^N`. -/
private lemma kj_jet_mul_le {f g : ℝ → ℝ} {N : ℕ} {a A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
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
private lemma kj_jet_sq_le {u : ℝ → ℝ} {N : ℕ} {a A : ℝ} (hA : 0 ≤ A)
    (hu : ∀ k ≤ N, |iteratedDeriv k u a| ≤ A) (hu' : ContDiffAt ℝ (N : ℕ) u a) :
    ∀ j ≤ N, |iteratedDeriv j (fun v => u v ^ 2) a| ≤ A * A * 2 ^ N := by
  intro j hj
  have h := kj_jet_mul_le hA hA hu hu hu' hu' j hj
  have he : (fun v : ℝ => u v ^ 2) = u * u := by funext v; simp only [Pi.mul_apply]; ring
  rwa [he]

/-- The jets of a linear function `v ↦ c * v`. -/
private lemma kj_iteratedDeriv_linear_form (c a : ℝ) (k : ℕ) :
    iteratedDeriv k (fun v : ℝ => c * v) a = if k = 0 then c * a else if k = 1 then c else 0 := by
  rw [show (fun v : ℝ => c * v) = fun v => c * id v from rfl,
    iteratedDeriv_const_mul (c := c) (f := id) contDiffAt_id, iteratedDeriv_id]
  split_ifs <;> ring

/-- Jet bound for a linear function. -/
private lemma kj_abs_iteratedDeriv_linear_le {c a R : ℝ} (hR : 0 ≤ R) (k : ℕ)
    (hc : |c| ≤ R) (hca : |c * a| ≤ R) :
    |iteratedDeriv k (fun v : ℝ => c * v) a| ≤ R := by
  rw [kj_iteratedDeriv_linear_form]
  split_ifs
  · simpa using hca
  · simpa using hc
  · simpa using hR

/-- Smoothness of a linear function at any finite order. -/
private lemma kj_contDiffAt_linear (c a : ℝ) (N : ℕ) :
    ContDiffAt ℝ (N : ℕ) (fun v : ℝ => c * v) a := by fun_prop

/-- Smoothness of `v ↦ c * v + h v` at any finite order. -/
private lemma kj_contDiffAt_linear_add {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (c a : ℝ) (N : ℕ) :
    ContDiffAt ℝ (N : ℕ) (fun v : ℝ => c * v + h v) a := by
  have h1 : ContDiffAt ℝ (N : ℕ) (fun v : ℝ => c * v) a := kj_contDiffAt_linear c a N
  have h2 : ContDiffAt ℝ (N : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  simpa using h1.add h2

/-- The jets of `v ↦ c * v + h v`. -/
private lemma kj_iteratedDeriv_linear_add {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (c a : ℝ)
    (k : ℕ) :
    iteratedDeriv k (fun v : ℝ => c * v + h v) a
      = iteratedDeriv k (fun v : ℝ => c * v) a + iteratedDeriv k h a := by
  have h1 : ContDiffAt ℝ (k : ℕ) (fun v : ℝ => c * v) a := kj_contDiffAt_linear c a k
  have h2 : ContDiffAt ℝ (k : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  change iteratedDeriv k ((fun v : ℝ => c * v) + h) a
      = iteratedDeriv k (fun v : ℝ => c * v) a + iteratedDeriv k h a
  rw [iteratedDeriv_add h1 h2]

/-- Jet bound for `v ↦ c * v + h v` in terms of the jets of `h`. -/
private lemma kj_jet_bound_linear_add {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {c a δ C D : ℝ} (hC : 0 ≤ C) (hδ : δ ≤ D) (k : ℕ)
    (hc : |c| ≤ C) (hca : |c * a| ≤ C) (hj : |iteratedDeriv k h a| ≤ δ) :
    |iteratedDeriv k (fun v : ℝ => c * v + h v) a| ≤ C + D := by
  rw [kj_iteratedDeriv_linear_add hh c a k]
  calc |iteratedDeriv k (fun v : ℝ => c * v) a + iteratedDeriv k h a|
      ≤ |iteratedDeriv k (fun v : ℝ => c * v) a| + |iteratedDeriv k h a| := abs_add_le _ _
    _ ≤ C + D := add_le_add (kj_abs_iteratedDeriv_linear_le hC k hc hca) (le_trans hj hδ)

/-- **Explicit radicand jet bound.**  This is `Zrad_jet_bounds` with its witness constant made
explicit (`2 ^ (n+2) * 100 = KJbz n`); the `∃`-form of that theorem cannot be used downstream
because the constant it hides has to be compared with `KJbz n`. -/
private theorem kj_zrad_jet (n : ℕ) :
    ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ δ → δ ≤ 1 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1, ∀ t : ℝ, |t| ≤ 2 → ∀ a ∈ Set.Icc (9 / 20 : ℝ) 1,
        (∀ j : ℕ, j ≤ n + 2 →
          |iteratedDeriv j (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t)) a| ≤
            (2 : ℝ) ^ (n + 2) * 100) ∧
        (∀ j : ℕ, j ≤ n + 2 →
          |iteratedDeriv j (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t)) a -
           iteratedDeriv j (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad 0 (v, σ, t)) a| ≤
             (2 : ℝ) ^ (n + 2) * 100 * δ) := by
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
    have h := kj_jet_bound_linear_add hh (c := t) (a := a) (δ := δ) (C := 2) (D := 1)
      (by norm_num) hδ1 k ht hta (hha k hk)
    linarith
  have hQ5 : ∀ k ≤ n + 2, |iteratedDeriv k (fun v : ℝ => 2 * t * v + h v) a| ≤ 5 := by
    intro k hk
    have h2ta : |2 * t * a| ≤ 4 := by
      rw [abs_mul]; nlinarith [h2t, haabs, abs_nonneg a]
    have h := kj_jet_bound_linear_add hh (c := 2 * t) (a := a) (δ := δ) (C := 4) (D := 1)
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
          ≤ |(t * σ + h σ) ^ 2| + |(t * a + h a) ^ 2| := kj_abs_sub_le_abs_add _ _
        _ = (t * σ + h σ) ^ 2 + (t * a + h a) ^ 2 := by
            rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
        _ ≤ 18 := by nlinarith [abs_le.mp h1, abs_le.mp h2]
        _ ≤ 2 ^ (n + 2) * 100 := by nlinarith [hpow]
    · have hj1 : 1 ≤ j := by omega
      rw [hFu]
      change |iteratedDeriv j ((fun _ : ℝ => (t * σ + h σ) ^ 2)
          - (fun v : ℝ => (t * v + h v) ^ 2)) a| ≤ 2 ^ (n + 2) * 100
      have hc2 : ContDiffAt ℝ (j : ℕ) (fun v : ℝ => (t * v + h v) ^ 2) a :=
        (kj_contDiffAt_linear_add hh t a j).pow 2
      rw [iteratedDeriv_sub contDiffAt_const hc2, iteratedDeriv_const]
      simp only [if_neg hj0]
      rw [zero_sub, abs_neg]
      have hsq := kj_jet_sq_le (u := fun v : ℝ => t * v + h v) (N := n + 2) (a := a) (A := 3)
        (by norm_num) hP3 (kj_contDiffAt_linear_add hh t a (n + 2)) j hj
      calc |iteratedDeriv j (fun v : ℝ => (t * v + h v) ^ 2) a| ≤ 3 * 3 * 2 ^ (n + 2) := hsq
        _ ≤ 2 ^ (n + 2) * 100 := by nlinarith [hpow]
  · intro j hj
    have hhAt : ContDiffAt ℝ (j : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have hc1 : ContDiffAt ℝ (j : ℕ)
        (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t)) a := by
      rw [hFu]
      exact contDiffAt_const.sub ((kj_contDiffAt_linear_add hh t a j).pow 2)
    have hc0 : ContDiffAt ℝ (j : ℕ)
        (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad 0 (v, σ, t)) a := by
      rw [hF0u]
      exact contDiffAt_const.sub ((kj_contDiffAt_linear t a j).pow 2)
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
            kj_abs_sub_le_abs_add _ _
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
        hhAt.mul (kj_contDiffAt_linear_add hh (2 * t) a j)
      rw [iteratedDeriv_sub contDiffAt_const hg, iteratedDeriv_const]
      simp only [if_neg hj0]
      rw [zero_sub, abs_neg]
      have hmul := kj_jet_mul_le (f := h) (g := fun v : ℝ => 2 * t * v + h v) (N := n + 2)
        (a := a) (A := δ) (B := 5) hδ0 (by norm_num) hha hQ5 hhA
        (kj_contDiffAt_linear_add hh (2 * t) a (n + 2)) j hj
      calc |iteratedDeriv j (h * fun v : ℝ => 2 * t * v + h v) a| ≤ δ * 5 * 2 ^ (n + 2) := hmul
        _ ≤ 2 ^ (n + 2) * 100 * δ := by nlinarith [hpow, hδ0]

/-! ## Elementary jet-of-`h` helpers -/

/-- The `m`-th derivative of the zero function is `0`. -/
private lemma iteratedDeriv_zero_fun (m : ℕ) (a : ℝ) :
    iteratedDeriv m (0 : ℝ → ℝ) a = 0 := by
  change iteratedDeriv m (fun _ : ℝ => (0 : ℝ)) a = 0
  rw [iteratedDeriv_const]
  split_ifs <;> simp

/-- The derivative of the `m`-th derivative of `f` is the `(m+1)`-st derivative of `f`. -/
private lemma deriv_iteratedDeriv_succ (f : ℝ → ℝ) (m : ℕ) (a : ℝ) :
    deriv (fun u : ℝ => iteratedDeriv m f u) a = iteratedDeriv (m + 1) f a := by
  rw [show (fun u : ℝ => iteratedDeriv m f u) = iteratedDeriv m f from rfl,
    ← iteratedDeriv_succ (n := m) (f := f)]

/-! ## Smoothness of the jet curve -/

/-- The jet curve `u ↦ KJet n h σ z u` is `C^∞` when `h` is. -/
private lemma contDiff_KJet (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) (z : St) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n h σ z u) := by
  rw [contDiff_pi]
  intro i
  cases i
  case aa =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => u)
    exact contDiff_id
  case sg =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => σ)
    exact contDiff_const
  case t1 =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => -(z 0))
    exact contDiff_const
  case t2 =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => z 1)
    exact contDiff_const
  case kd1 =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => krad h σ (-(z 0)) u)
    exact contDiff_krad hh σ (-(z 0))
  case kd2 =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => krad h σ (z 1) u)
    exact contDiff_krad hh σ (z 1)
  case c2 =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => z 2)
    exact contDiff_const
  case c3 =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => z 3)
    exact contDiff_const
  case Z1 k =>
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => (σ - v) * krad h σ (-(z 0)) v) :=
      (contDiff_const.sub contDiff_id).mul (contDiff_krad hh σ (-(z 0)))
    simpa [kjet, iteratedDeriv_eq_iterate] using hF.iterate_deriv k.1
  case Z2 k =>
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => (σ - v) * krad h σ (z 1) v) :=
      (contDiff_const.sub contDiff_id).mul (contDiff_krad hh σ (z 1))
    simpa [kjet, iteratedDeriv_eq_iterate] using hF.iterate_deriv k.1
  case w j =>
    simpa [iteratedDeriv_eq_iterate] using hh.iterate_deriv (j.1 + 1)


/-! ## The explicit `krad` data -/

/-! The next block is the proof of `krad_data` (`Window/krad_data.lean`) with its witnesses
`κ = 1/100`, `C = 10` made explicit (the existential form cannot be compared with `KJbz n`). -/

/-- **Explicit `krad` data.**  `krad_data` with its witnesses `(κ, C) = (1/100, 10)` made
explicit. -/
private lemma kj_krad_data {h : ℝ → ℝ} {δ σ t a : ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hbnd : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    (hσ : σ ∈ Set.Icc (7 / 10 : ℝ) 1) (ht1 : 1 / 5 ≤ |t|) (ht2 : |t| ≤ 2)
    (ha : a ∈ Set.Icc (9 / 20 : ℝ) σ) :
    1 / 100 ≤ krad h σ t a ∧ krad h σ t a ≤ 10 ∧
      |krad h σ t a - krad 0 σ t a| ≤ 10 * δ ∧
      |deriv (fun a' : ℝ => krad h σ t a') a| ≤ 10 ∧
      |deriv (fun a' : ℝ => krad h σ t a') a -
        deriv (fun a' : ℝ => krad 0 σ t a') a| ≤ 10 * δ := by
  have hσ1 : 7 / 10 ≤ σ := hσ.1
  have hσ2 : σ ≤ 1 := hσ.2
  have ha1 : 9 / 20 ≤ a := ha.1
  have ha2 : a ≤ σ := ha.2
  have h0 : ∀ x : ℝ, |h x| ≤ δ := fun x => by
    have hx := hbnd 0 (by norm_num) x
    rwa [iteratedDeriv_zero] at hx
  have h1 : ∀ x : ℝ, |deriv h x| ≤ δ := fun x => by
    have hx := hbnd 1 (by norm_num) x
    rwa [iteratedDeriv_one] at hx
  have h2 : ∀ x : ℝ, |deriv (deriv h) x| ≤ δ := fun x => by
    have hx := hbnd 2 (by norm_num) x
    rwa [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one] at hx
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
    simpa only [Function.iterate_one] using hh.iterate_deriv 1
  have hliph : ∀ x y : ℝ, |h x - h y| ≤ δ * |x - y| :=
    abs_sub_le_mul_of_deriv_bound (f := h) (C := δ)
      (fun x => hh.differentiable (by simp) x) h1
  have hlipd : ∀ x y : ℝ, |deriv h x - deriv h y| ≤ δ * |x - y| :=
    abs_sub_le_mul_of_deriv_bound (f := deriv h) (C := δ)
      (fun x => hd.differentiable (by simp) x) h2
  have hlipq : ∀ x y : ℝ, |hquot h x σ - hquot h y σ| ≤ δ * |x - y| :=
    abs_hquot_sub_le hδ0 hd.continuous hlipd
  obtain ⟨hpos, hub, hclose⟩ :=
    krad_pointwise_data (h := h) (δ := δ) (σ := σ) (t := t) (a := a)
      hδ0 hδ1 h0 h1 hσ1 hσ2 ht1 ht2 ha1 ha2
  obtain ⟨hlip1, hlip2⟩ :=
    krad_lipschitz_window (h := h) (δ := δ) (σ := σ) (t := t)
      hδ0 hδ1 h0 h1 hliph hlipq hσ1 hσ2 ht2
  have haS : a ∈ Set.Icc (3 / 8 : ℝ) (3 / 2) := ⟨by linarith, by linarith⟩
  have hmem : Set.Icc (3 / 8 : ℝ) (3 / 2) ∈ 𝓝 a := Icc_mem_nhds (by linarith) (by linarith)
  refine ⟨hpos, hub, hclose, ?_, ?_⟩
  · have hlip : ∀ᶠ x in 𝓝 a, ‖krad h σ t x - krad h σ t a‖ ≤ 5 * ‖x - a‖ := by
      filter_upwards [hmem] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact hlip1 x hx a haS
    have hd5 := norm_deriv_le_of_lip' (f := fun a' : ℝ => krad h σ t a') (C := 5)
      (by norm_num) hlip
    rw [Real.norm_eq_abs] at hd5
    linarith
  · have hdif1 : DifferentiableAt ℝ (fun a' : ℝ => krad h σ t a') a :=
      (contDiff_krad hh σ t).differentiable (by simp) a
    have hdif0 : DifferentiableAt ℝ (fun a' : ℝ => krad 0 σ t a') a :=
      (contDiff_krad (h := (0 : ℝ → ℝ)) contDiff_const σ t).differentiable (by simp) a
    rw [← deriv_sub hdif1 hdif0]
    have hlip : ∀ᶠ x in 𝓝 a,
        ‖(krad h σ t x - krad 0 σ t x) - (krad h σ t a - krad 0 σ t a)‖ ≤
          (10 * δ) * ‖x - a‖ := by
      filter_upwards [hmem] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact hlip2 x hx a haS
    have hd10 := norm_deriv_le_of_lip' (f := fun a' : ℝ => krad h σ t a' - krad 0 σ t a')
      (C := 10 * δ) (by linarith) hlip
    rw [Real.norm_eq_abs] at hd10
    exact hd10

/-! ## The main theorem -/

/-- **The jet of the transition-window data.**  On the window, the jet `KJet n h σ z a` lies in
the compact box `KJbox n (KJbz n)`, the jet curves of `h` and of `0` are `C^∞`, their `u`-derivatives
at `a` are bounded by `KJbz n`, and the jet of `h` and its derivative are `KJbz n * δ`-close to
those of `0`. -/
theorem KvecJet_data (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ σ : ℝ}
    {z : St} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hjet : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    (hσ : σ ∈ Set.Icc (7 / 10 : ℝ) 1)
    (hz0 : (1 / 5 : ℝ) ≤ z 0) (hz1 : (1 / 5 : ℝ) ≤ z 1) (hz : ∀ i : Fin 4, |z i| ≤ 2)
    (a : ℝ) (ha : a ∈ Set.Icc (9 / 20 : ℝ) σ) :
    KJet n h σ z a ∈ KJbox n (KJbz n) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n h σ z u) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n 0 σ z u) ∧
    ‖deriv (fun u : ℝ => KJet n h σ z u) a‖ ≤ KJbz n ∧
    ‖deriv (fun u : ℝ => KJet n 0 σ z u) a‖ ≤ KJbz n ∧
    ‖KJet n h σ z a - KJet n 0 σ z a‖ ≤ KJbz n * δ ∧
    ‖deriv (fun u : ℝ => KJet n h σ z u) a - deriv (fun u : ℝ => KJet n 0 σ z u) a‖
      ≤ KJbz n * δ := by
  -- ## elementary constants and window data
  have hδ1' : δ ≤ 1 := by linarith
  have hB0 : 0 ≤ KJbz n := KJbz_nonneg n
  have hB1 : 1 ≤ KJbz n := one_le_KJbz n
  have hB10 : 10 ≤ KJbz n := ten_le_KJbz n
  have hBδ : 0 ≤ KJbz n * δ := mul_nonneg hB0 hδ0
  have hδB : δ ≤ KJbz n * δ := by
    simpa using mul_le_mul_of_nonneg_right hB1 hδ0
  have h10δ : (10 : ℝ) * δ ≤ KJbz n * δ := mul_le_mul_of_nonneg_right hB10 hδ0
  have hconst_deriv : ∀ c : ℝ, |deriv (fun _ : ℝ => c) a| ≤ KJbz n := by
    intro c
    have h0 : deriv (fun _ : ℝ => c) a = 0 := by simp
    rw [h0, abs_zero]
    exact hB0
  have hσ1 : 7 / 10 ≤ σ := hσ.1
  have hσ2 : σ ≤ 1 := hσ.2
  have ha1 : 9 / 20 ≤ a := ha.1
  have ha2 : a ≤ σ := ha.2
  have haS : a ∈ Set.Icc (9 / 20 : ℝ) 1 := ⟨ha1, le_trans ha2 hσ2⟩
  have hle1 : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by norm_num
  have hh1 : ContDiff ℝ (1 : ℕ∞) h := hh.of_le hle1
  have hh01 : ContDiff ℝ (1 : ℕ∞) (0 : ℝ → ℝ) := by
    show ContDiff ℝ (1 : ℕ∞) (fun _ : ℝ => (0 : ℝ))
    exact contDiff_const
  -- ## the two chord endpoints
  have hzt1 : |-(z 0)| ≤ 2 := by rw [abs_neg]; exact hz 0
  have hzt1' : (1 / 5 : ℝ) ≤ |-(z 0)| := by
    rw [abs_neg]; exact le_trans hz0 (le_abs_self (z 0))
  have hzt2 : |z 1| ≤ 2 := hz 1
  have hzt2' : (1 / 5 : ℝ) ≤ |z 1| := le_trans hz1 (le_abs_self (z 1))
  -- ## jets of the zero perturbation
  have hjet0 : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ (0 : ℝ) := by
    intro k hk s
    rw [iteratedDeriv_zero_fun k s, abs_zero]
  have hbnd2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ :=
    fun k hk s => hjet k (by omega) s
  have hbnd20 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ (0 : ℝ) :=
    fun k hk s => hjet0 k (by omega) s
  -- ## radicand jet bounds (both perturbations, both endpoints)
  obtain ⟨hZ1, hZ1δ⟩ := kj_zrad_jet n h δ hh hδ0 hδ1' hjet σ hσ (-(z 0)) hzt1 a haS
  obtain ⟨hZ2, hZ2δ⟩ := kj_zrad_jet n h δ hh hδ0 hδ1' hjet σ hσ (z 1) hzt2 a haS
  obtain ⟨hZ10, hZ10δ⟩ :=
    kj_zrad_jet n 0 0 contDiff_const le_rfl (by norm_num) hjet0 σ hσ (-(z 0)) hzt1 a haS
  obtain ⟨hZ20, hZ20δ⟩ :=
    kj_zrad_jet n 0 0 contDiff_const le_rfl (by norm_num) hjet0 σ hσ (z 1) hzt2 a haS
  have hZb1 : ∀ k : ℕ, k ≤ n + 2 → |kjet h σ (-(z 0)) a k| ≤ KJbz n := by
    intro k hk
    rw [kjet_eq_Zrad hh1 σ (-(z 0)) a k]
    simpa only [KJbz] using hZ1 k hk
  have hZb2 : ∀ k : ℕ, k ≤ n + 2 → |kjet h σ (z 1) a k| ≤ KJbz n := by
    intro k hk
    rw [kjet_eq_Zrad hh1 σ (z 1) a k]
    simpa only [KJbz] using hZ2 k hk
  have hZb10 : ∀ k : ℕ, k ≤ n + 2 → |kjet 0 σ (-(z 0)) a k| ≤ KJbz n := by
    intro k hk
    rw [kjet_eq_Zrad hh01 σ (-(z 0)) a k]
    simpa only [KJbz] using hZ10 k hk
  have hZb20 : ∀ k : ℕ, k ≤ n + 2 → |kjet 0 σ (z 1) a k| ≤ KJbz n := by
    intro k hk
    rw [kjet_eq_Zrad hh01 σ (z 1) a k]
    simpa only [KJbz] using hZ20 k hk
  have hZc1 : ∀ k : ℕ, k ≤ n + 2 →
      |kjet h σ (-(z 0)) a k - kjet 0 σ (-(z 0)) a k| ≤ KJbz n * δ := by
    intro k hk
    rw [kjet_eq_Zrad hh1 σ (-(z 0)) a k, kjet_eq_Zrad hh01 σ (-(z 0)) a k]
    simpa only [KJbz] using hZ1δ k hk
  have hZc2 : ∀ k : ℕ, k ≤ n + 2 →
      |kjet h σ (z 1) a k - kjet 0 σ (z 1) a k| ≤ KJbz n * δ := by
    intro k hk
    rw [kjet_eq_Zrad hh1 σ (z 1) a k, kjet_eq_Zrad hh01 σ (z 1) a k]
    simpa only [KJbz] using hZ2δ k hk
  -- ## radicand (`krad`) data at both endpoints, for both perturbations
  obtain ⟨hk1pos, hk1ub, hk1cl, hk1d, hk1dd⟩ :=
    kj_krad_data (h := h) (δ := δ) (σ := σ) (t := -(z 0)) (a := a)
      hh hδ0 hδ1 hbnd2 hσ hzt1' hzt1 ha
  obtain ⟨hk2pos, hk2ub, hk2cl, hk2d, hk2dd⟩ :=
    kj_krad_data (h := h) (δ := δ) (σ := σ) (t := z 1) (a := a)
      hh hδ0 hδ1 hbnd2 hσ hzt2' hzt2 ha
  obtain ⟨hk10pos, hk10ub, _, hk10d, _⟩ :=
    kj_krad_data (h := (0 : ℝ → ℝ)) (δ := 0) (σ := σ) (t := -(z 0)) (a := a)
      contDiff_const le_rfl (by norm_num) hbnd20 hσ hzt1' hzt1 ha
  obtain ⟨hk20pos, hk20ub, _, hk20d, _⟩ :=
    kj_krad_data (h := (0 : ℝ → ℝ)) (δ := 0) (σ := σ) (t := z 1) (a := a)
      contDiff_const le_rfl (by norm_num) hbnd20 hσ hzt2' hzt2 ha
  -- ## smoothness of the two jet curves
  have hcd1 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n h σ z u) := contDiff_KJet n hh σ z
  have hcd0 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n 0 σ z u) :=
    contDiff_KJet n contDiff_const σ z
  have hd1 : ∀ i : KJIx n, DifferentiableAt ℝ (fun u : ℝ => KJet n h σ z u i) a :=
    fun i => (((contDiff_pi.mp hcd1) i).contDiffAt).differentiableAt (by simp)
  have hd0 : ∀ i : KJIx n, DifferentiableAt ℝ (fun u : ℝ => KJet n 0 σ z u i) a :=
    fun i => (((contDiff_pi.mp hcd0) i).contDiffAt).differentiableAt (by simp)
  -- ## the jet lies in the box
  have hmem : KJet n h σ z a ∈ KJbox n (KJbz n) := by
    refine ⟨?_, ?_⟩
    · intro i
      cases i
      case aa =>
        show (9 / 20 : ℝ) ≤ a
        exact ha1
      case sg =>
        show (7 / 10 : ℝ) ≤ σ
        exact hσ1
      case t1 =>
        show (-2 : ℝ) ≤ -(z 0)
        linarith [(abs_le.mp (hz 0)).2]
      case t2 =>
        show (1 / 5 : ℝ) ≤ z 1
        exact hz1
      case kd1 =>
        show (1 / 100 : ℝ) ≤ krad h σ (-(z 0)) a
        exact hk1pos
      case kd2 =>
        show (1 / 100 : ℝ) ≤ krad h σ (z 1) a
        exact hk2pos
      case c2 =>
        show (-2 : ℝ) ≤ z 2
        linarith [(abs_le.mp (hz 2)).1]
      case c3 =>
        show (-2 : ℝ) ≤ z 3
        linarith [(abs_le.mp (hz 3)).1]
      case Z1 k =>
        show -(KJbz n) ≤ kjet h σ (-(z 0)) a k.1
        linarith [neg_le_abs (kjet h σ (-(z 0)) a k.1), hZb1 k.1 (le_of_lt k.2)]
      case Z2 k =>
        show -(KJbz n) ≤ kjet h σ (z 1) a k.1
        linarith [neg_le_abs (kjet h σ (z 1) a k.1), hZb2 k.1 (le_of_lt k.2)]
      case w j =>
        rw [show KJLo n (KJbz n) (KJIx.w j) = (-1 / 100 : ℝ) from rfl,
          show KJet n h σ z a (KJIx.w j) = iteratedDeriv (j.1 + 1) h a from rfl]
        have hj := hjet (j.1 + 1) (by have := j.2; omega) a
        linarith [neg_le_abs (iteratedDeriv (j.1 + 1) h a), hj, hδ1]
    · intro i
      cases i
      case aa =>
        show a ≤ 1
        linarith
      case sg =>
        show σ ≤ 1
        exact hσ2
      case t1 =>
        show -(z 0) ≤ -(1 / 5)
        linarith [hz0]
      case t2 =>
        show z 1 ≤ 2
        linarith [(abs_le.mp (hz 1)).2]
      case kd1 =>
        show krad h σ (-(z 0)) a ≤ 10
        exact hk1ub
      case kd2 =>
        show krad h σ (z 1) a ≤ 10
        exact hk2ub
      case c2 =>
        show z 2 ≤ 2
        linarith [(abs_le.mp (hz 2)).2]
      case c3 =>
        show z 3 ≤ 2
        linarith [(abs_le.mp (hz 3)).2]
      case Z1 k =>
        show kjet h σ (-(z 0)) a k.1 ≤ KJbz n
        linarith [le_abs_self (kjet h σ (-(z 0)) a k.1), hZb1 k.1 (le_of_lt k.2)]
      case Z2 k =>
        show kjet h σ (z 1) a k.1 ≤ KJbz n
        linarith [le_abs_self (kjet h σ (z 1) a k.1), hZb2 k.1 (le_of_lt k.2)]
      case w j =>
        show iteratedDeriv (j.1 + 1) h a ≤ 1 / 100
        have hj := hjet (j.1 + 1) (by have := j.2; omega) a
        linarith [le_abs_self (iteratedDeriv (j.1 + 1) h a), hj, hδ1]
  -- ## coordinatewise bounds for the derivatives
  have hder1c : ∀ i : KJIx n, |deriv (fun u : ℝ => KJet n h σ z u i) a| ≤ KJbz n := by
    intro i
    cases i
    case aa =>
      show |deriv (fun u : ℝ => u) a| ≤ KJbz n
      have h1 : deriv (fun u : ℝ => u) a = 1 := by simp
      rw [h1, abs_one]
      exact hB1
    case sg =>
      show |deriv (fun _ : ℝ => σ) a| ≤ KJbz n
      exact hconst_deriv σ
    case t1 =>
      show |deriv (fun _ : ℝ => -(z 0)) a| ≤ KJbz n
      exact hconst_deriv (-(z 0))
    case t2 =>
      show |deriv (fun _ : ℝ => z 1) a| ≤ KJbz n
      exact hconst_deriv (z 1)
    case kd1 =>
      show |deriv (fun u : ℝ => krad h σ (-(z 0)) u) a| ≤ KJbz n
      linarith [hk1d, hB10]
    case kd2 =>
      show |deriv (fun u : ℝ => krad h σ (z 1) u) a| ≤ KJbz n
      linarith [hk2d, hB10]
    case c2 =>
      show |deriv (fun _ : ℝ => z 2) a| ≤ KJbz n
      exact hconst_deriv (z 2)
    case c3 =>
      show |deriv (fun _ : ℝ => z 3) a| ≤ KJbz n
      exact hconst_deriv (z 3)
    case Z1 k =>
      show |deriv (fun u : ℝ => kjet h σ (-(z 0)) u k.1) a| ≤ KJbz n
      rw [(kjet_succ h σ (-(z 0)) a k.1).symm]
      exact hZb1 (k.1 + 1) (by have := k.2; omega)
    case Z2 k =>
      show |deriv (fun u : ℝ => kjet h σ (z 1) u k.1) a| ≤ KJbz n
      rw [(kjet_succ h σ (z 1) a k.1).symm]
      exact hZb2 (k.1 + 1) (by have := k.2; omega)
    case w j =>
      show |deriv (fun u : ℝ => iteratedDeriv (j.1 + 1) h u) a| ≤ KJbz n
      rw [deriv_iteratedDeriv_succ h (j.1 + 1) a]
      show |iteratedDeriv (j.1 + 2) h a| ≤ KJbz n
      exact le_trans (le_trans (hjet (j.1 + 2) (by have := j.2; omega) a) hδ1') hB1
  have hder0c : ∀ i : KJIx n, |deriv (fun u : ℝ => KJet n 0 σ z u i) a| ≤ KJbz n := by
    intro i
    cases i
    case aa =>
      show |deriv (fun u : ℝ => u) a| ≤ KJbz n
      have h1 : deriv (fun u : ℝ => u) a = 1 := by simp
      rw [h1, abs_one]
      exact hB1
    case sg =>
      show |deriv (fun _ : ℝ => σ) a| ≤ KJbz n
      exact hconst_deriv σ
    case t1 =>
      show |deriv (fun _ : ℝ => -(z 0)) a| ≤ KJbz n
      exact hconst_deriv (-(z 0))
    case t2 =>
      show |deriv (fun _ : ℝ => z 1) a| ≤ KJbz n
      exact hconst_deriv (z 1)
    case kd1 =>
      show |deriv (fun u : ℝ => krad 0 σ (-(z 0)) u) a| ≤ KJbz n
      linarith [hk10d, hB10]
    case kd2 =>
      show |deriv (fun u : ℝ => krad 0 σ (z 1) u) a| ≤ KJbz n
      linarith [hk20d, hB10]
    case c2 =>
      show |deriv (fun _ : ℝ => z 2) a| ≤ KJbz n
      exact hconst_deriv (z 2)
    case c3 =>
      show |deriv (fun _ : ℝ => z 3) a| ≤ KJbz n
      exact hconst_deriv (z 3)
    case Z1 k =>
      show |deriv (fun u : ℝ => kjet 0 σ (-(z 0)) u k.1) a| ≤ KJbz n
      rw [(kjet_succ (0 : ℝ → ℝ) σ (-(z 0)) a k.1).symm]
      exact hZb10 (k.1 + 1) (by have := k.2; omega)
    case Z2 k =>
      show |deriv (fun u : ℝ => kjet 0 σ (z 1) u k.1) a| ≤ KJbz n
      rw [(kjet_succ (0 : ℝ → ℝ) σ (z 1) a k.1).symm]
      exact hZb20 (k.1 + 1) (by have := k.2; omega)
    case w j =>
      show |deriv (fun u : ℝ => iteratedDeriv (j.1 + 1) (0 : ℝ → ℝ) u) a| ≤ KJbz n
      rw [deriv_iteratedDeriv_succ (0 : ℝ → ℝ) (j.1 + 1) a,
        iteratedDeriv_zero_fun ((j.1 + 1) + 1) a, abs_zero]
      exact hB0
  have hder1 : ‖deriv (fun u : ℝ => KJet n h σ z u) a‖ ≤ KJbz n := by
    rw [pi_norm_le_iff_of_nonneg hB0]
    intro i
    have h1 : (deriv (fun u : ℝ => KJet n h σ z u) a) i
        = deriv (fun u : ℝ => KJet n h σ z u i) a := congrFun (deriv_pi hd1) i
    rw [h1, Real.norm_eq_abs]
    exact hder1c i
  have hder0 : ‖deriv (fun u : ℝ => KJet n 0 σ z u) a‖ ≤ KJbz n := by
    rw [pi_norm_le_iff_of_nonneg hB0]
    intro i
    have h1 : (deriv (fun u : ℝ => KJet n 0 σ z u) a) i
        = deriv (fun u : ℝ => KJet n 0 σ z u i) a := congrFun (deriv_pi hd0) i
    rw [h1, Real.norm_eq_abs]
    exact hder0c i
  -- ## coordinatewise closeness of the jets
  have hclc : ∀ i : KJIx n, |KJet n h σ z a i - KJet n 0 σ z a i| ≤ KJbz n * δ := by
    intro i
    cases i
    case aa =>
      show |a - a| ≤ KJbz n * δ
      rw [sub_self, abs_zero]
      exact hBδ
    case sg =>
      show |σ - σ| ≤ KJbz n * δ
      rw [sub_self, abs_zero]
      exact hBδ
    case t1 =>
      show |-(z 0) - -(z 0)| ≤ KJbz n * δ
      rw [sub_self, abs_zero]
      exact hBδ
    case t2 =>
      show |z 1 - z 1| ≤ KJbz n * δ
      rw [sub_self, abs_zero]
      exact hBδ
    case kd1 =>
      show |krad h σ (-(z 0)) a - krad 0 σ (-(z 0)) a| ≤ KJbz n * δ
      exact le_trans hk1cl h10δ
    case kd2 =>
      show |krad h σ (z 1) a - krad 0 σ (z 1) a| ≤ KJbz n * δ
      exact le_trans hk2cl h10δ
    case c2 =>
      show |z 2 - z 2| ≤ KJbz n * δ
      rw [sub_self, abs_zero]
      exact hBδ
    case c3 =>
      show |z 3 - z 3| ≤ KJbz n * δ
      rw [sub_self, abs_zero]
      exact hBδ
    case Z1 k =>
      show |kjet h σ (-(z 0)) a k.1 - kjet 0 σ (-(z 0)) a k.1| ≤ KJbz n * δ
      exact hZc1 k.1 (le_of_lt k.2)
    case Z2 k =>
      show |kjet h σ (z 1) a k.1 - kjet 0 σ (z 1) a k.1| ≤ KJbz n * δ
      exact hZc2 k.1 (le_of_lt k.2)
    case w j =>
      show |iteratedDeriv (j.1 + 1) h a - iteratedDeriv (j.1 + 1) (0 : ℝ → ℝ) a| ≤ KJbz n * δ
      rw [iteratedDeriv_zero_fun (j.1 + 1) a, sub_zero]
      exact le_trans (hjet (j.1 + 1) (by have := j.2; omega) a) hδB
  have hcl : ‖KJet n h σ z a - KJet n 0 σ z a‖ ≤ KJbz n * δ := by
    rw [pi_norm_le_iff_of_nonneg hBδ]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact hclc i
  -- ## coordinatewise closeness of the derivatives
  have hddc : ∀ i : KJIx n,
      |deriv (fun u : ℝ => KJet n h σ z u i) a - deriv (fun u : ℝ => KJet n 0 σ z u i) a|
        ≤ KJbz n * δ := by
    intro i
    cases i
    case aa =>
      show |deriv (fun u : ℝ => u) a - deriv (fun u : ℝ => u) a| ≤ KJbz n * δ
      rw [sub_self, abs_zero]
      exact hBδ
    case sg =>
      show |deriv (fun _ : ℝ => σ) a - deriv (fun _ : ℝ => σ) a| ≤ KJbz n * δ
      rw [sub_self, abs_zero]
      exact hBδ
    case t1 =>
      show |deriv (fun _ : ℝ => -(z 0)) a - deriv (fun _ : ℝ => -(z 0)) a| ≤ KJbz n * δ
      rw [sub_self, abs_zero]
      exact hBδ
    case t2 =>
      show |deriv (fun _ : ℝ => z 1) a - deriv (fun _ : ℝ => z 1) a| ≤ KJbz n * δ
      rw [sub_self, abs_zero]
      exact hBδ
    case kd1 =>
      show |deriv (fun u : ℝ => krad h σ (-(z 0)) u) a -
            deriv (fun u : ℝ => krad 0 σ (-(z 0)) u) a| ≤ KJbz n * δ
      exact le_trans hk1dd h10δ
    case kd2 =>
      show |deriv (fun u : ℝ => krad h σ (z 1) u) a -
            deriv (fun u : ℝ => krad 0 σ (z 1) u) a| ≤ KJbz n * δ
      exact le_trans hk2dd h10δ
    case c2 =>
      show |deriv (fun _ : ℝ => z 2) a - deriv (fun _ : ℝ => z 2) a| ≤ KJbz n * δ
      rw [sub_self, abs_zero]
      exact hBδ
    case c3 =>
      show |deriv (fun _ : ℝ => z 3) a - deriv (fun _ : ℝ => z 3) a| ≤ KJbz n * δ
      rw [sub_self, abs_zero]
      exact hBδ
    case Z1 k =>
      show |deriv (fun u : ℝ => kjet h σ (-(z 0)) u k.1) a -
            deriv (fun u : ℝ => kjet 0 σ (-(z 0)) u k.1) a| ≤ KJbz n * δ
      rw [(kjet_succ h σ (-(z 0)) a k.1).symm, (kjet_succ (0 : ℝ → ℝ) σ (-(z 0)) a k.1).symm]
      exact hZc1 (k.1 + 1) (by have := k.2; omega)
    case Z2 k =>
      show |deriv (fun u : ℝ => kjet h σ (z 1) u k.1) a -
            deriv (fun u : ℝ => kjet 0 σ (z 1) u k.1) a| ≤ KJbz n * δ
      rw [(kjet_succ h σ (z 1) a k.1).symm, (kjet_succ (0 : ℝ → ℝ) σ (z 1) a k.1).symm]
      exact hZc2 (k.1 + 1) (by have := k.2; omega)
    case w j =>
      show |deriv (fun u : ℝ => iteratedDeriv (j.1 + 1) h u) a -
            deriv (fun u : ℝ => iteratedDeriv (j.1 + 1) (0 : ℝ → ℝ) u) a| ≤ KJbz n * δ
      rw [deriv_iteratedDeriv_succ h (j.1 + 1) a,
        deriv_iteratedDeriv_succ (0 : ℝ → ℝ) (j.1 + 1) a,
        iteratedDeriv_zero_fun ((j.1 + 1) + 1) a, sub_zero]
      exact le_trans (hjet ((j.1 + 1) + 1) (by have := j.2; omega) a) hδB
  have hdd : ‖deriv (fun u : ℝ => KJet n h σ z u) a - deriv (fun u : ℝ => KJet n 0 σ z u) a‖
      ≤ KJbz n * δ := by
    rw [pi_norm_le_iff_of_nonneg hBδ]
    intro i
    have h1 : (deriv (fun u : ℝ => KJet n h σ z u) a) i
        = deriv (fun u : ℝ => KJet n h σ z u i) a := congrFun (deriv_pi hd1) i
    have h2 : (deriv (fun u : ℝ => KJet n 0 σ z u) a) i
        = deriv (fun u : ℝ => KJet n 0 σ z u i) a := congrFun (deriv_pi hd0) i
    rw [Pi.sub_apply, h1, h2, Real.norm_eq_abs]
    exact hddc i
  exact ⟨hmem, hcd1, hcd0, hder1, hder0, hcl, hdd⟩

end

end Work.OddVolterra.Window
