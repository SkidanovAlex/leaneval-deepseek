import Mathlib
import Submission.Work.OddVolterra.Window.KvecDefs
import Submission.Work.OddVolterra.Window.KvecJet_data
import Submission.Work.OddVolterra.Window.Zrad_jet_bounds

namespace Work.OddVolterra.Window

/-- `|x - y| ≤ |x| + |y|`. -/
private lemma kjm_abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg] using abs_add_le x (-y)

/-- **Leibniz bound.**  If the jets of `f` and `g` at `a` up to order `N` are bounded by `A`
and `B`, then the jets of the product are bounded by `A * B * 2^N`. -/
private lemma kjm_jet_mul_le {f g : ℝ → ℝ} {N : ℕ} {a A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
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
private lemma kjm_jet_sq_le {u : ℝ → ℝ} {N : ℕ} {a A : ℝ} (hA : 0 ≤ A)
    (hu : ∀ k ≤ N, |iteratedDeriv k u a| ≤ A) (hu' : ContDiffAt ℝ (N : ℕ) u a) :
    ∀ j ≤ N, |iteratedDeriv j (fun v => u v ^ 2) a| ≤ A * A * 2 ^ N := by
  intro j hj
  have h := kjm_jet_mul_le hA hA hu hu hu' hu' j hj
  have he : (fun v : ℝ => u v ^ 2) = u * u := by funext v; simp only [Pi.mul_apply]; ring
  rwa [he]

/-- The jets of a linear function `v ↦ c * v`. -/
private lemma kjm_iteratedDeriv_linear_form (c a : ℝ) (k : ℕ) :
    iteratedDeriv k (fun v : ℝ => c * v) a = if k = 0 then c * a else if k = 1 then c else 0 := by
  rw [show (fun v : ℝ => c * v) = fun v => c * id v from rfl,
    iteratedDeriv_const_mul (c := c) (f := id) contDiffAt_id, iteratedDeriv_id]
  split_ifs <;> ring

/-- Jet bound for a linear function. -/
private lemma kjm_abs_iteratedDeriv_linear_le {c a R : ℝ} (hR : 0 ≤ R) (k : ℕ)
    (hc : |c| ≤ R) (hca : |c * a| ≤ R) :
    |iteratedDeriv k (fun v : ℝ => c * v) a| ≤ R := by
  rw [kjm_iteratedDeriv_linear_form]
  split_ifs
  · simpa using hca
  · simpa using hc
  · simpa using hR

/-- Smoothness of a linear function at any finite order. -/
private lemma kjm_contDiffAt_linear (c a : ℝ) (N : ℕ) :
    ContDiffAt ℝ (N : ℕ) (fun v : ℝ => c * v) a := by fun_prop

/-- Smoothness of `v ↦ c * v + h v` at any finite order. -/
private lemma kjm_contDiffAt_linear_add {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (c a : ℝ) (N : ℕ) :
    ContDiffAt ℝ (N : ℕ) (fun v : ℝ => c * v + h v) a := by
  have h1 : ContDiffAt ℝ (N : ℕ) (fun v : ℝ => c * v) a := kjm_contDiffAt_linear c a N
  have h2 : ContDiffAt ℝ (N : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  simpa using h1.add h2

/-- The jets of `v ↦ c * v + h v`. -/
private lemma kjm_iteratedDeriv_linear_add {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (c a : ℝ)
    (k : ℕ) :
    iteratedDeriv k (fun v : ℝ => c * v + h v) a
      = iteratedDeriv k (fun v : ℝ => c * v) a + iteratedDeriv k h a := by
  have h1 : ContDiffAt ℝ (k : ℕ) (fun v : ℝ => c * v) a := kjm_contDiffAt_linear c a k
  have h2 : ContDiffAt ℝ (k : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  change iteratedDeriv k ((fun v : ℝ => c * v) + h) a
      = iteratedDeriv k (fun v : ℝ => c * v) a + iteratedDeriv k h a
  rw [iteratedDeriv_add h1 h2]

/-- Jet bound for `v ↦ c * v + h v` in terms of the jets of `h`. -/
private lemma kjm_jet_bound_linear_add {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {c a δ C D : ℝ} (hC : 0 ≤ C) (hδ : δ ≤ D) (k : ℕ)
    (hc : |c| ≤ C) (hca : |c * a| ≤ C) (hj : |iteratedDeriv k h a| ≤ δ) :
    |iteratedDeriv k (fun v : ℝ => c * v + h v) a| ≤ C + D := by
  rw [kjm_iteratedDeriv_linear_add hh c a k]
  calc |iteratedDeriv k (fun v : ℝ => c * v) a + iteratedDeriv k h a|
      ≤ |iteratedDeriv k (fun v : ℝ => c * v) a| + |iteratedDeriv k h a| := abs_add_le _ _
    _ ≤ C + D := add_le_add (kjm_abs_iteratedDeriv_linear_le hC k hc hca) (le_trans hj hδ)

/-- **Explicit radicand jet bound.**  This is `Zrad_jet_bounds` with its witness constant made
explicit (`2 ^ (n+2) * 100 = KJbz n`); the `∃`-form of that theorem cannot be used downstream
because the constant it hides has to be compared with `KJbz n`. -/
private theorem kjm_zrad_jet (n : ℕ) :
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
    have h := kjm_jet_bound_linear_add hh (c := t) (a := a) (δ := δ) (C := 2) (D := 1)
      (by norm_num) hδ1 k ht hta (hha k hk)
    linarith
  have hQ5 : ∀ k ≤ n + 2, |iteratedDeriv k (fun v : ℝ => 2 * t * v + h v) a| ≤ 5 := by
    intro k hk
    have h2ta : |2 * t * a| ≤ 4 := by
      rw [abs_mul]; nlinarith [h2t, haabs, abs_nonneg a]
    have h := kjm_jet_bound_linear_add hh (c := 2 * t) (a := a) (δ := δ) (C := 4) (D := 1)
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
          ≤ |(t * σ + h σ) ^ 2| + |(t * a + h a) ^ 2| := kjm_abs_sub_le_abs_add _ _
        _ = (t * σ + h σ) ^ 2 + (t * a + h a) ^ 2 := by
            rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
        _ ≤ 18 := by nlinarith [abs_le.mp h1, abs_le.mp h2]
        _ ≤ 2 ^ (n + 2) * 100 := by nlinarith [hpow]
    · have hj1 : 1 ≤ j := by omega
      rw [hFu]
      change |iteratedDeriv j ((fun _ : ℝ => (t * σ + h σ) ^ 2)
          - (fun v : ℝ => (t * v + h v) ^ 2)) a| ≤ 2 ^ (n + 2) * 100
      have hc2 : ContDiffAt ℝ (j : ℕ) (fun v : ℝ => (t * v + h v) ^ 2) a :=
        (kjm_contDiffAt_linear_add hh t a j).pow 2
      rw [iteratedDeriv_sub contDiffAt_const hc2, iteratedDeriv_const]
      simp only [if_neg hj0]
      rw [zero_sub, abs_neg]
      have hsq := kjm_jet_sq_le (u := fun v : ℝ => t * v + h v) (N := n + 2) (a := a) (A := 3)
        (by norm_num) hP3 (kjm_contDiffAt_linear_add hh t a (n + 2)) j hj
      calc |iteratedDeriv j (fun v : ℝ => (t * v + h v) ^ 2) a| ≤ 3 * 3 * 2 ^ (n + 2) := hsq
        _ ≤ 2 ^ (n + 2) * 100 := by nlinarith [hpow]
  · intro j hj
    have hhAt : ContDiffAt ℝ (j : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have hc1 : ContDiffAt ℝ (j : ℕ)
        (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t)) a := by
      rw [hFu]
      exact contDiffAt_const.sub ((kjm_contDiffAt_linear_add hh t a j).pow 2)
    have hc0 : ContDiffAt ℝ (j : ℕ)
        (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad 0 (v, σ, t)) a := by
      rw [hF0u]
      exact contDiffAt_const.sub ((kjm_contDiffAt_linear t a j).pow 2)
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
            kjm_abs_sub_le_abs_add _ _
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
        hhAt.mul (kjm_contDiffAt_linear_add hh (2 * t) a j)
      rw [iteratedDeriv_sub contDiffAt_const hg, iteratedDeriv_const]
      simp only [if_neg hj0]
      rw [zero_sub, abs_neg]
      have hmul := kjm_jet_mul_le (f := h) (g := fun v : ℝ => 2 * t * v + h v) (N := n + 2)
        (a := a) (A := δ) (B := 5) hδ0 (by norm_num) hha hQ5 hhA
        (kjm_contDiffAt_linear_add hh (2 * t) a (n + 2)) j hj
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
private lemma kjm_contDiff_KJet (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) (z : St) :
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
/-- Box membership and `u`-derivative bound for the jet curve `KJet`, with no order condition
between `a` and `σ`.

Route: copy the proof of `KvecJet_data` in `Submission/Work/OddVolterra/Window/KvecJet_data.lean`
(`hmem` and `hder1`), replacing its (private) `kj_zrad_jet` by a copy of the same explicit
constant lemma (the bound is `2 ^ (n+2) * 100 = KJbz n`), and using the given `krad` data instead
of `kj_krad_data`.  For the `.Z1`/`.Z2` entries of the derivative block use `kjet_succ` and the
`(k+1)`-st radicand-jet bound (`k + 1 ≤ n + 2` for `k : Fin (n+2)`); for `.w j` use
`deriv_iteratedDeriv_succ` and the jet hypothesis at order `j.1 + 2 ≤ n + 2`. -/
theorem KJet_mem_box_deriv (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hjet : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (7 / 10 : ℝ) (19 / 20)) {z : Work.OddVolterra.St}
    (hz0 : 1 / 4 ≤ z 0) (hz1 : 1 / 4 ≤ z 1) (hz : ∀ i : Fin 4, |z i| ≤ 2)
    {a : ℝ} (ha : a ∈ Set.Icc (7 / 10 : ℝ) (19 / 20))
    (hk1 : 1 / 100 ≤ Work.OddVolterra.krad h σ (-(z 0)) a)
    (hk1' : Work.OddVolterra.krad h σ (-(z 0)) a ≤ 10)
    (hk2 : 1 / 100 ≤ Work.OddVolterra.krad h σ (z 1) a)
    (hk2' : Work.OddVolterra.krad h σ (z 1) a ≤ 10)
    (hk1d : |deriv (fun a' : ℝ => Work.OddVolterra.krad h σ (-(z 0)) a') a| ≤ 5)
    (hk2d : |deriv (fun a' : ℝ => Work.OddVolterra.krad h σ (z 1) a') a| ≤ 5) :
    Work.OddVolterra.Window.KJet n h σ z a ∈ Work.OddVolterra.Window.KJbox n (Work.OddVolterra.Window.KJbz n) ∧
    ‖deriv (fun u : ℝ => Work.OddVolterra.Window.KJet n h σ z u) a‖ ≤ Work.OddVolterra.Window.KJbz n := by
  have hB0 : 0 ≤ KJbz n := KJbz_nonneg n
  have hB1 : 1 ≤ KJbz n := one_le_KJbz n
  have hB10 : 10 ≤ KJbz n := ten_le_KJbz n
  have hσ1 : 7 / 10 ≤ σ := hσ.1
  have hσ2 : σ ≤ 1 := by linarith [hσ.2]
  have ha1 : 9 / 20 ≤ a := by linarith [ha.1]
  have ha2 : a ≤ 1 := by linarith [ha.2]
  have hσS : σ ∈ Set.Icc (7 / 10 : ℝ) 1 := ⟨hσ1, hσ2⟩
  have haS : a ∈ Set.Icc (9 / 20 : ℝ) 1 := ⟨ha1, ha2⟩
  have hh1 : ContDiff ℝ (1 : ℕ∞) h := hh.of_le (by norm_num)
  have hzt1 : |-(z 0)| ≤ 2 := by rw [abs_neg]; exact hz 0
  have hzt2 : |z 1| ≤ 2 := hz 1
  have hδ0 : (0 : ℝ) ≤ 1 / 100 := by norm_num
  have hδ1 : (1 : ℝ) / 100 ≤ 1 := by norm_num
  obtain ⟨hZ1, -⟩ :=
    kjm_zrad_jet n h (1 / 100) hh hδ0 hδ1 hjet σ hσS (-(z 0)) hzt1 a haS
  obtain ⟨hZ2, -⟩ :=
    kjm_zrad_jet n h (1 / 100) hh hδ0 hδ1 hjet σ hσS (z 1) hzt2 a haS
  have hZb1 : ∀ k : ℕ, k ≤ n + 2 → |kjet h σ (-(z 0)) a k| ≤ KJbz n := by
    intro k hk
    rw [kjet_eq_Zrad hh1 σ (-(z 0)) a k]
    simpa only [KJbz] using hZ1 k hk
  have hZb2 : ∀ k : ℕ, k ≤ n + 2 → |kjet h σ (z 1) a k| ≤ KJbz n := by
    intro k hk
    rw [kjet_eq_Zrad hh1 σ (z 1) a k]
    simpa only [KJbz] using hZ2 k hk
  have hcd1 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n h σ z u) := kjm_contDiff_KJet n hh σ z
  have hd1 : ∀ i : KJIx n, DifferentiableAt ℝ (fun u : ℝ => KJet n h σ z u i) a :=
    fun i => (((contDiff_pi.mp hcd1) i).contDiffAt).differentiableAt (by simp)
  have hconst_deriv : ∀ c : ℝ, |deriv (fun _ : ℝ => c) a| ≤ KJbz n := by
    intro c
    have h0 : deriv (fun _ : ℝ => c) a = 0 := by simp
    rw [h0, abs_zero]
    exact hB0
  refine ⟨⟨?_, ?_⟩, ?_⟩
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
      linarith
    case kd1 =>
      show (1 / 100 : ℝ) ≤ krad h σ (-(z 0)) a
      exact hk1
    case kd2 =>
      show (1 / 100 : ℝ) ≤ krad h σ (z 1) a
      exact hk2
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
      linarith [neg_le_abs (iteratedDeriv (j.1 + 1) h a), hj]
  · intro i
    cases i
    case aa =>
      show a ≤ 1
      exact ha2
    case sg =>
      show σ ≤ 1
      exact hσ2
    case t1 =>
      show -(z 0) ≤ -(1 / 5)
      linarith
    case t2 =>
      show z 1 ≤ 2
      linarith [(abs_le.mp (hz 1)).2]
    case kd1 =>
      show krad h σ (-(z 0)) a ≤ 10
      exact hk1'
    case kd2 =>
      show krad h σ (z 1) a ≤ 10
      exact hk2'
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
      linarith [le_abs_self (iteratedDeriv (j.1 + 1) h a), hj]
  · have hder1c : ∀ i : KJIx n, |deriv (fun u : ℝ => KJet n h σ z u i) a| ≤ KJbz n := by
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
        exact le_trans (le_trans (hjet (j.1 + 2) (by have := j.2; omega) a) hδ1) hB1
    rw [pi_norm_le_iff_of_nonneg hB0]
    intro i
    have h1 : (deriv (fun u : ℝ => KJet n h σ z u) a) i
        = deriv (fun u : ℝ => KJet n h σ z u i) a := congrFun (deriv_pi hd1) i
    rw [h1, Real.norm_eq_abs]
    exact hder1c i


end Work.OddVolterra.Window
