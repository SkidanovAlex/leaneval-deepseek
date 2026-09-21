import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.Window.krad_data
import Submission.Work.OddExistence.Manifest.aw_toolkit
import Submission.Work.OddVolterra.Existence.iteratedDeriv_mul_abs_bound
import Submission.Work.OddVolterra.Window.hquot_deriv2_bound

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Second `a`-derivative of the Abel radicand

`krad h σ t a = (t + hquot h a σ) (line h σ t + line h a t)` is a product of the two
`a`-dependent factors `A a = t + hquot h a σ` and `B a = line h σ t + line h a t`.  Its second
`a`-derivative is bounded by the Leibniz rule; the three ingredients are

* `|A| ≤ 3`, `|A'| ≤ δ`, `|A''| ≤ δ` (the last is the new analytic input, proved in
  `Work.OddVolterra.Window.hquot_deriv2_bound` by differentiating twice under the integral sign),
* `|B| ≤ 6`, `|B'| ≤ 6`, `|B''| ≤ δ` on the window.

This gives `|∂_a² krad| ≤ 3 δ + 2·δ·6 + δ·6 = 21 δ ≤ 26 δ`.  The constants are chosen with a
comfortable margin; nothing here is sharp.
-/

/-- `iteratedDeriv 2 f` is `deriv (deriv f)`. -/
theorem krad2_iteratedDeriv_two_eq_deriv_deriv (f : ℝ → ℝ) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- **Leibniz bound for the second derivative of a pointwise product.**  If `|f| ≤ Bf`,
`|f'| ≤ Df`, `|f''| ≤ Ef` at `a` and similarly `|g| ≤ Bg`, `|g'| ≤ Dg`, `|g''| ≤ Eg`, then
`|(f g)'' (a)| ≤ Bf · Eg + 2 Df · Dg + Ef · Bg`. -/
lemma krad2_iteratedDeriv2_mul_bound {f g : ℝ → ℝ} {a Bf Df Ef : ℝ}
    (hf : ContDiffAt ℝ (2 : ℕ∞) f a) (hg : ContDiffAt ℝ (2 : ℕ∞) g a)
    (hBf : 0 ≤ Bf) (hDf : 0 ≤ Df) (hEf : 0 ≤ Ef)
    (hf0 : |f a| ≤ Bf) (hf1 : |iteratedDeriv 1 f a| ≤ Df) (hf2 : |iteratedDeriv 2 f a| ≤ Ef)
    {Bg Dg Eg : ℝ} (hg0 : |g a| ≤ Bg) (hg1 : |iteratedDeriv 1 g a| ≤ Dg)
    (hg2 : |iteratedDeriv 2 g a| ≤ Eg) :
    |iteratedDeriv 2 (f * g) a| ≤ Bf * Eg + 2 * Df * Dg + Ef * Bg := by
  rw [iteratedDeriv_mul hf hg]
  have hexp : (∑ i ∈ Finset.range (2 + 1),
        ((2 : ℕ).choose i : ℝ) * iteratedDeriv i f a * iteratedDeriv (2 - i) g a)
      = f a * iteratedDeriv 2 g a + 2 * iteratedDeriv 1 f a * iteratedDeriv 1 g a
        + iteratedDeriv 2 f a * g a := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, Nat.sub_zero, Nat.sub_self,
      Nat.cast_one, Nat.cast_ofNat, one_mul, zero_add, iteratedDeriv_zero]
  rw [hexp]
  have h1 := abs_add_le (f a * iteratedDeriv 2 g a + 2 * iteratedDeriv 1 f a * iteratedDeriv 1 g a)
      (iteratedDeriv 2 f a * g a)
  have h2 := abs_add_le (f a * iteratedDeriv 2 g a)
      (2 * iteratedDeriv 1 f a * iteratedDeriv 1 g a)
  have h3 : |f a * iteratedDeriv 2 g a| ≤ Bf * Eg := by
    rw [abs_mul]; exact mul_le_mul hf0 hg2 (abs_nonneg _) hBf
  have h4 : |2 * iteratedDeriv 1 f a * iteratedDeriv 1 g a| ≤ 2 * Df * Dg := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hf1 (by norm_num)) hg1 (abs_nonneg _)
      (mul_nonneg (by norm_num) hDf)
  have h5 : |iteratedDeriv 2 f a * g a| ≤ Ef * Bg := by
    rw [abs_mul]; exact mul_le_mul hf2 hg0 (abs_nonneg _) hEf
  linarith

/-- The second `a`-derivative of `a ↦ line h σ t + line h a t` is `iteratedDeriv 2 h`:
the constant `line h σ t` contributes nothing. -/
lemma krad2_line_add_iteratedDeriv_two {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (σ t a : ℝ) :
    iteratedDeriv 2 (fun a' : ℝ => line h σ t + line h a' t) a = iteratedDeriv 2 h a := by
  rw [iteratedDeriv_const_add (by norm_num : (0 : ℕ) < 2) (line h σ t)]
  rw [Work.OddExistence.Manifest.AW.iteratedDeriv_line_eq h hh t a 2]
  norm_num

/-- On the window, the factor `B a = line h σ t + line h a t` and its first two derivatives
are bounded by `6`; the third-derivative-order bound `δ` for `B''` is supplied separately. -/
lemma krad2_line_add_iteratedDeriv_bound {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {δ σ t a : ℝ} (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    (hσ1 : 7 / 10 ≤ σ) (hσ2 : σ ≤ 1) (ht2 : |t| ≤ 2)
    (ha1 : 9 / 20 ≤ a) (ha2 : a ≤ σ) :
    ∀ k : ℕ, k ≤ 2 → |iteratedDeriv k (fun a' : ℝ => line h σ t + line h a' t) a| ≤ 6 := by
  have h0 : ∀ s : ℝ, |h s| ≤ δ := fun s => by
    have := hjet 0 (by norm_num) s
    rwa [iteratedDeriv_zero] at this
  have h1 : ∀ s : ℝ, |deriv h s| ≤ δ := fun s => by
    have := hjet 1 (by norm_num) s
    rwa [iteratedDeriv_one] at this
  have ha_abs : |a| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hs_abs : |σ| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hline : ∀ x : ℝ, |x| ≤ 1 → |line h x t| ≤ 201 / 100 := by
    intro x hx
    simp only [line]
    calc |x * t + h x| ≤ |x * t| + |h x| := abs_add_le _ _
      _ = |x| * |t| + |h x| := by rw [abs_mul]
      _ ≤ 1 * 2 + δ := add_le_add (mul_le_mul hx ht2 (abs_nonneg _) (by norm_num)) (h0 x)
      _ ≤ 201 / 100 := by linarith
  intro k hk
  interval_cases k
  · rw [iteratedDeriv_zero]
    calc |line h σ t + line h a t| ≤ |line h σ t| + |line h a t| := abs_add_le _ _
      _ ≤ 201 / 100 + 201 / 100 := add_le_add (hline σ hs_abs) (hline a ha_abs)
      _ ≤ 6 := by norm_num
  · have he : iteratedDeriv 1 (fun a' : ℝ => line h σ t + line h a' t) a = t + deriv h a := by
      rw [iteratedDeriv_const_add (by norm_num : (0 : ℕ) < 1) (line h σ t)]
      rw [Work.OddExistence.Manifest.AW.iteratedDeriv_line_eq h hh t a 1]
      norm_num
    rw [he]
    calc |t + deriv h a| ≤ |t| + |deriv h a| := abs_add_le _ _
      _ ≤ 2 + δ := add_le_add ht2 (h1 a)
      _ ≤ 6 := by linarith
  · rw [krad2_line_add_iteratedDeriv_two hh σ t a]
    calc |iteratedDeriv 2 h a| ≤ δ := hjet 2 (by norm_num) a
      _ ≤ 6 := by linarith

/-- **Bound on the second `a`-derivative of `krad` on the transition window**, conditional on
the corresponding bound for the divided difference `hquot h · σ`. -/
lemma krad2_abs_deriv_deriv_krad_le {h : ℝ → ℝ} {δ σ t a : ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    (hσ1 : 7 / 10 ≤ σ) (hσ2 : σ ≤ 1) (ht2 : |t| ≤ 2)
    (ha1 : 9 / 20 ≤ a) (ha2 : a ≤ σ)
    (hH2 : |deriv (deriv (fun x : ℝ => hquot h x σ)) a| ≤ δ) :
    |deriv (deriv (fun a' : ℝ => krad h σ t a')) a| ≤ 26 * δ := by
  have h1 : ∀ s : ℝ, |deriv h s| ≤ δ := fun s => by
    have := hjet 1 (by norm_num) s
    rwa [iteratedDeriv_one] at this
  have h2 : ∀ s : ℝ, |iteratedDeriv 2 h s| ≤ δ := fun s => hjet 2 (by norm_num) s
  have hb := Work.OddExistence.Manifest.AW.hquot_deriv_bound hh hδ0 h1 h2 a σ
  have hAc0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun a' : ℝ => hquot h a' σ) a :=
    ((Work.OddVolterra.Existence.hquot_contDiff hh).comp (f := fun a' : ℝ => (a', σ))
      (by fun_prop)).contDiffAt
  have hAc : ContDiffAt ℝ (2 : ℕ∞) (fun a' : ℝ => hquot h a' σ) a :=
    hAc0.of_le (Work.OddExistence.Manifest.AW.natCast_le_top_enat 2)
  have hAcd : ContDiffAt ℝ (2 : ℕ∞) (fun a' : ℝ => t + hquot h a' σ) a :=
    (contDiffAt_const (c := t)).add hAc
  have hl0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun a' : ℝ => line h a' t) a :=
    ((line_contDiff hh).comp (f := fun a' : ℝ => (a', t)) (by fun_prop)).contDiffAt
  have hl : ContDiffAt ℝ (2 : ℕ∞) (fun a' : ℝ => line h a' t) a :=
    hl0.of_le (Work.OddExistence.Manifest.AW.natCast_le_top_enat 2)
  have hBcd : ContDiffAt ℝ (2 : ℕ∞) (fun a' : ℝ => line h σ t + line h a' t) a :=
    (contDiffAt_const (c := line h σ t)).add hl
  have hAf0 : |(fun a' : ℝ => t + hquot h a' σ) a| ≤ 3 := by
    show |t + hquot h a σ| ≤ 3
    calc |t + hquot h a σ| ≤ |t| + |hquot h a σ| := abs_add_le _ _
      _ ≤ 2 + δ := add_le_add ht2 hb.1
      _ ≤ 3 := by linarith
  have hAf1 : |iteratedDeriv 1 (fun a' : ℝ => t + hquot h a' σ) a| ≤ δ := by
    rw [iteratedDeriv_one, deriv_const_add]
    exact hb.2
  have hAf2 : |iteratedDeriv 2 (fun a' : ℝ => t + hquot h a' σ) a| ≤ δ := by
    rw [iteratedDeriv_const_add (by norm_num : (0 : ℕ) < 2) t, krad2_iteratedDeriv_two_eq_deriv_deriv]
    exact hH2
  have hgB := krad2_line_add_iteratedDeriv_bound hh hδ1 (fun k hk => hjet k (by omega))
    hσ1 hσ2 ht2 ha1 ha2
  have hB0 : |iteratedDeriv 0 (fun a' : ℝ => line h σ t + line h a' t) a| ≤ 6 :=
    hgB 0 (by norm_num)
  have hB1 : |iteratedDeriv 1 (fun a' : ℝ => line h σ t + line h a' t) a| ≤ 6 :=
    hgB 1 (by norm_num)
  have hB2 : |iteratedDeriv 2 (fun a' : ℝ => line h σ t + line h a' t) a| ≤ δ := by
    rw [krad2_line_add_iteratedDeriv_two hh σ t a]; exact h2 a
  have hmain : |iteratedDeriv 2
      ((fun a' : ℝ => t + hquot h a' σ) * (fun a' : ℝ => line h σ t + line h a' t)) a|
      ≤ 3 * δ + 2 * δ * 6 + δ * 6 :=
    krad2_iteratedDeriv2_mul_bound hAcd hBcd (by norm_num) hδ0 hδ0
      hAf0 hAf1 hAf2 hB0 hB1 hB2
  have hmul_fun : (fun a' : ℝ => krad h σ t a')
      = (fun a' : ℝ => t + hquot h a' σ) * (fun a' : ℝ => line h σ t + line h a' t) := by
    funext a'; rw [krad_apply]; rfl
  rw [← krad2_iteratedDeriv_two_eq_deriv_deriv (fun a' : ℝ => krad h σ t a'), hmul_fun]
  linarith [hmain, hδ0]

/-- The unperturbed radicand `krad 0 σ t a = t² (σ + a)` is affine in `a`, so its second
`a`-derivative vanishes. -/
lemma krad2_krad_zero_deriv2 (σ t a : ℝ) :
    deriv (deriv (fun a' : ℝ => krad (0 : ℝ → ℝ) σ t a')) a = 0 := by
  have hfun : (fun a' : ℝ => krad (0 : ℝ → ℝ) σ t a') = fun a' : ℝ => t^2 * (σ + a') := by
    funext a'
    rw [krad_apply, hquot_zero]
    simp only [line, Pi.zero_apply, add_zero]
    ring
  have hderiv : deriv (fun a' : ℝ => t^2 * (σ + a')) = fun _ : ℝ => t^2 := by
    funext x
    have hx : HasDerivAt (fun a' : ℝ => t^2 * (σ + a')) (t^2) x := by
      simpa using ((hasDerivAt_id x).const_add σ).const_mul (t^2)
    exact hx.deriv
  rw [hfun, hderiv]
  simp

/-- (`Work.OddVolterra.Window`, module `Submission.Work.OddVolterra.Window.krad_deriv2_data`.)
Second `a`-derivative of the Abel radicand `krad h σ t ·` on the transition window
`σ ∈ [7/10,1]`, `1/5 ≤ |t| ≤ 2`, `a ∈ [9/20, σ]`, for `h` with `|h^(k)| ≤ δ ≤ 1/100` for `k ≤ 3`.

Mathematically: `krad h σ t a = (t + hquot h a σ) * (line h σ t + line h a t)`
(`Work.OddVolterra.krad_apply`), so by the product rule
`d²krad = (d² hquot)·(line h σ t + line h a t) + 2·(d hquot)·(t + deriv h a)
+ (t + hquot)·(iteratedDeriv 2 h a)`, and each factor is bounded: `|hquot| ≤ δ`, `|d hquot| ≤ δ`
(both from `Work.OddExistence.Manifest.AW.hquot_deriv_bound`, whose hypotheses `|h'| ≤ δ`,
`|h''| ≤ δ` follow from the jet hypothesis with `k ≤ 3`), and the new ingredient
`|d² hquot| ≤ δ`, which follows from `hquot h a σ = ∫_0^1 deriv h (a + τ*(σ-a)) dτ` by
differentiating twice under the integral sign
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, applied twice), giving
`d² hquot a = ∫_0^1 (1-τ)^2 * iteratedDeriv 3 h (a + τ*(σ-a)) dτ`, hence `≤ δ`.  For `h = 0` the
same formula gives `d² krad 0 σ t a = 0` (indeed `krad 0 σ t a' = t^2 * (σ + a')` is affine in
`a'`), so the second conjunct is the same inequality as the first. -/
theorem krad_deriv2_data :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℝ → ℝ) (δ σ t a : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      σ ∈ Set.Icc (7 / 10 : ℝ) 1 → 1 / 5 ≤ |t| → |t| ≤ 2 → a ∈ Set.Icc (9 / 20 : ℝ) σ →
      |deriv (deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a')) a| ≤ K * δ ∧
      |deriv (deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a')) a -
       deriv (deriv (fun a' : ℝ => Work.OddVolterra.krad 0 σ t a')) a| ≤ K * δ := by
  refine ⟨26, by norm_num, ?_⟩
  intro h δ σ t a hh hδ0 hδ1 hjet hσ _ht1 ht2 ha
  have hH2 : |deriv (deriv (fun x : ℝ => hquot h x σ)) a| ≤ δ := by
    have h3 : ∀ s : ℝ, |iteratedDeriv 3 h s| ≤ δ := fun s => hjet 3 (by norm_num) s
    exact hquot_deriv2_bound hh hδ0 h3 σ a
  have hmain := krad2_abs_deriv_deriv_krad_le hh hδ0 hδ1 hjet hσ.1 hσ.2 ht2 ha.1 ha.2 hH2
  have hzero := krad2_krad_zero_deriv2 σ t a
  constructor
  · linarith
  · rw [hzero, sub_zero]; linarith

end

end Work.OddVolterra.Window
