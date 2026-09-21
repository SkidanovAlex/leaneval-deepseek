import Mathlib
import Submission.Work.Anchor.eng_jets
import Submission.Work.Anchor.eng_reg
import Submission.Work.OddExistence.Manifest.aw_toolkit

/-!
# `t`-difference (uniform in `h`) jet bounds for the Bell numerators `Rnu`

The engine constants of the localised odd anchor need `∂_a K1M`, `∂_a K2M` to be Lipschitz in the
chord parameter `t`, *uniformly in `h`*.  Since `K1M = J1M / Kden`, `J1M = Rnu (n+1/2) h 1 (n+1)`
and `Rnu` is the Bell recursion `R_{m+1} = Zrad · ∂_a R_m + (ν-m) · (∂_a Zrad) · R_m`, this reduces
to a bound on the `t`-difference of the `a`-jets of `Rnu`.

The observation making this cheap: the radicand
`Zrad h (a',σ,t) = (σ t + h σ)^2 - (a' t + h a')^2`
is **quadratic in `t`** with explicit coefficients (see `awZrad_quad`), so the `t`-difference of any
`a`-jet of `Zrad` at `a` is an explicit multiple of `t - t'`, bounded by the Leibniz rule and the
jet bounds of `h` alone.  Feeding those into the recursion exactly as `Anchor.Rnu_jet_bounds` feeds
the `h`-versus-`0` differences produces the constants `awTA` (values of the `a`-jets) and `awTD`
(`t`-differences of the `a`-jets), both uniform in `h`.  No mixed-partial (Schwarz) argument is
needed anywhere.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Existence

open Work.OddVolterra

noncomputable section

set_option maxHeartbeats 1600000

/-! ## The quadratic form of the radicand in `t` -/

/-- The coefficient of `t` in `Zrad h (a',σ,t)`. -/
def awZB (h : ℝ → ℝ) (a' σ : ℝ) : ℝ := 2 * σ * h σ - 2 * a' * h a'

/-- The coefficient of `t ^ 2` in `Zrad h (a',σ,t)`. -/
def awZC (a' σ : ℝ) : ℝ := σ ^ 2 - a' ^ 2

lemma awZrad_quad (h : ℝ → ℝ) (a' σ t : ℝ) :
    KernelExt.Zrad h (a', σ, t)
      = ((h σ) ^ 2 - (h a') ^ 2) + t * awZB h a' σ + t ^ 2 * awZC a' σ := by
  simp only [KernelExt.Zrad, line, awZB, awZC]; ring

lemma awZrad_t_sub (h : ℝ → ℝ) (a' σ t t' : ℝ) :
    KernelExt.Zrad h (a', σ, t) - KernelExt.Zrad h (a', σ, t')
      = (t - t') * (awZB h a' σ + (t + t') * awZC a' σ) := by
  rw [awZrad_quad h a' σ t, awZrad_quad h a' σ t']; ring

/-! ## Elementary jet bounds -/

/-- The jets of the identity on `[49/100, 1]`. -/
lemma aw_abs_iteratedDeriv_id_le {N : ℕ} {a : ℝ} (ha : a ∈ Set.Icc (49 / 100 : ℝ) 1)
    {k : ℕ} (hk : k ≤ N) : |iteratedDeriv k (fun x : ℝ => x) a| ≤ 1 := by
  rw [show (fun x : ℝ => x) = id from rfl, iteratedDeriv_id]
  split_ifs
  · exact abs_le.mpr ⟨by linarith [ha.1], ha.2⟩
  · norm_num
  · norm_num

lemma aw_abs_iteratedDeriv_const_le (c : ℝ) (i : ℕ) (a : ℝ) :
    |iteratedDeriv i (fun _ : ℝ => c) a| ≤ |c| := by
  rw [iteratedDeriv_const]; split_ifs <;> simp

lemma abs_iteratedDeriv_add_le {f g : ℝ → ℝ} {a A B : ℝ} {i : ℕ}
    (hf : ContDiffAt ℝ (i : ℕ∞) f a) (hg : ContDiffAt ℝ (i : ℕ∞) g a)
    (hfA : |iteratedDeriv i f a| ≤ A) (hgB : |iteratedDeriv i g a| ≤ B) :
    |iteratedDeriv i (fun x => f x + g x) a| ≤ A + B := by
  rw [show (fun x => f x + g x) = f + g from rfl, iteratedDeriv_add hf hg]
  exact le_trans (abs_add_le _ _) (add_le_add hfA hgB)

lemma abs_value_sub_le_abs_add_abs (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [le_abs_self x, neg_le_abs x, le_abs_self y, neg_le_abs y]

lemma abs_iteratedDeriv_sub_le {f g : ℝ → ℝ} {a A B : ℝ} {i : ℕ}
    (hf : ContDiffAt ℝ (i : ℕ∞) f a) (hg : ContDiffAt ℝ (i : ℕ∞) g a)
    (hfA : |iteratedDeriv i f a| ≤ A) (hgB : |iteratedDeriv i g a| ≤ B) :
    |iteratedDeriv i (fun x => f x - g x) a| ≤ A + B := by
  rw [show (fun x => f x - g x) = f - g from rfl, iteratedDeriv_sub hf hg]
  exact le_trans (abs_value_sub_le_abs_add_abs _ _) (add_le_add hfA hgB)

lemma abs_iteratedDeriv_const_mul_le {c : ℝ} {f : ℝ → ℝ} {i : ℕ} {a A : ℝ}
    (hf : ContDiffAt ℝ (i : ℕ∞) f a) (hA : |iteratedDeriv i f a| ≤ A) :
    |iteratedDeriv i (fun x => c * f x) a| ≤ |c| * A := by
  rw [iteratedDeriv_const_mul c hf, abs_mul]
  exact mul_le_mul_of_nonneg_left hA (abs_nonneg c)

/-- Leibniz jet bound for a product. -/
lemma aw_prod_jet_le {f g : ℝ → ℝ} {a A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {N : ℕ}
    (hf : ∀ k ≤ N, |iteratedDeriv k f a| ≤ A) (hg : ∀ k ≤ N, |iteratedDeriv k g a| ≤ B)
    (hf' : ContDiffAt ℝ N f a) (hg' : ContDiffAt ℝ N g a) {j : ℕ} (hj : j ≤ N) :
    |iteratedDeriv j (f * g) a| ≤ 2 ^ j * (A * B) := by
  rw [iteratedDeriv_mul (hf'.of_le (by exact_mod_cast hj)) (hg'.of_le (by exact_mod_cast hj))]
  calc |∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * iteratedDeriv i f a * iteratedDeriv (j - i) g a|
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (A * B) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        rw [Finset.mem_range] at hi
        have hi1 : |iteratedDeriv i f a| ≤ A := hf i (by omega)
        have hi2 : |iteratedDeriv (j - i) g a| ≤ B := hg (j - i) (by omega)
        have hCi : (0:ℝ) ≤ (j.choose i : ℝ) := by positivity
        rw [abs_mul, abs_mul, abs_of_nonneg hCi]
        calc (j.choose i : ℝ) * |iteratedDeriv i f a| * |iteratedDeriv (j - i) g a|
            ≤ (j.choose i : ℝ) * A * B :=
              mul_le_mul (mul_le_mul_of_nonneg_left hi1 hCi) hi2 (abs_nonneg _) (by positivity)
          _ = (j.choose i : ℝ) * (A * B) := by ring
    _ = 2 ^ j * (A * B) := by
        rw [← Finset.sum_mul]
        have h : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
          rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
        rw [h]

/-! ## The `t`-difference of the `a`-jets of `Zrad` -/

/-- **The `t`-difference of an `a`-jet of the radicand, in closed form.** -/
lemma ZJ_t_sub_eq (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (i : ℕ) (a σ t t' : ℝ) :
    Work.Anchor.ZJ h i a σ t - Work.Anchor.ZJ h i a σ t'
      = (t - t') * iteratedDeriv i (fun a' : ℝ => awZB h a' σ + (t + t') * awZC a' σ) a := by
  have hs1 : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => KernelExt.Zrad h (a', σ, t)) :=
    Work.OddExistence.Manifest.AW.contDiff_Zrad_section hh σ t
  have hs2 : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => KernelExt.Zrad h (a', σ, t')) :=
    Work.OddExistence.Manifest.AW.contDiff_Zrad_section hh σ t'
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => awZB h a' σ + (t + t') * awZC a' σ) := by
    unfold awZB awZC; fun_prop
  have hsplit : (fun a' : ℝ => KernelExt.Zrad h (a', σ, t))
      = (fun a' : ℝ => KernelExt.Zrad h (a', σ, t) - KernelExt.Zrad h (a', σ, t'))
        + (fun a' : ℝ => KernelExt.Zrad h (a', σ, t')) := by
    funext x; simp
  have hdiff : iteratedDeriv i (fun a' : ℝ => KernelExt.Zrad h (a', σ, t)) a
      - iteratedDeriv i (fun a' : ℝ => KernelExt.Zrad h (a', σ, t')) a
      = iteratedDeriv i
          (fun a' : ℝ => KernelExt.Zrad h (a', σ, t) - KernelExt.Zrad h (a', σ, t')) a := by
    rw [hsplit, iteratedDeriv_add ((hs1.sub hs2).contDiffAt.of_le
      (Work.OddExistence.Manifest.AW.natCast_le_top_enat i))
      (hs2.contDiffAt.of_le (Work.OddExistence.Manifest.AW.natCast_le_top_enat i))]
    ring
  rw [Work.Anchor.ZJ, Work.Anchor.ZJ, hdiff]
  have hfun : (fun a' : ℝ => KernelExt.Zrad h (a', σ, t) - KernelExt.Zrad h (a', σ, t'))
      = fun a' : ℝ => (t - t') * (awZB h a' σ + (t + t') * awZC a' σ) := by
    funext x; exact awZrad_t_sub h x σ t t'
  rw [hfun, iteratedDeriv_const_mul _ (hsm.contDiffAt.of_le
    (Work.OddExistence.Manifest.AW.natCast_le_top_enat i))]

/-- **Jet bound for the `t`-difference coefficient of the radicand.** -/
lemma abs_iteratedDeriv_awG_le {N : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ N → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ)
    {a : ℝ} (ha : a ∈ Set.Icc (49 / 100 : ℝ) 1) {t t' σ : ℝ} (ht : t ∈ Set.Icc (-2 : ℝ) 2)
    (ht' : t' ∈ Set.Icc (-2 : ℝ) 2) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (19 / 20)) {i : ℕ}
    (hi : i ≤ N) :
    |iteratedDeriv i (fun a' : ℝ => awZB h a' σ + (t + t') * awZC a' σ) a|
      ≤ 2 * δ + 4 + 2 ^ (i + 1) * δ + 4 * 2 ^ i := by
  have hσ1 : |σ| ≤ 1 := abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have htt : |t + t'| ≤ 4 := by
    have h1 : |t| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have h2 : |t'| ≤ 2 := abs_le.mpr ⟨by linarith [ht'.1], ht'.2⟩
    have h3 : |t + t'| ≤ |t| + |t'| := abs_add_le _ _
    linarith
  have hha : |h σ| ≤ δ := hjet 0 (Nat.zero_le N) σ
  have hidA : ∀ k ≤ N, |iteratedDeriv k (fun x : ℝ => x) a| ≤ (1 : ℝ) :=
    fun k hk => aw_abs_iteratedDeriv_id_le ha hk
  have hidC : ContDiffAt ℝ N (fun x : ℝ => x) a := contDiffAt_id
  have hhC : ContDiffAt ℝ N h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hiC : ContDiffAt ℝ (i : ℕ∞) (fun x : ℝ => x) a := contDiffAt_id
  have hhiC : ContDiffAt ℝ (i : ℕ∞) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have h2i0 : (0:ℝ) ≤ 2 ^ i := by positivity
  have hid2 : |(2:ℝ)| = 2 := by norm_num
  have hc : |2 * σ * h σ + (t + t') * σ ^ 2| ≤ 2 * δ + 4 := by
    have h3 : |2 * σ * h σ + (t + t') * σ ^ 2| ≤ |2 * σ * h σ| + |(t + t') * σ ^ 2| :=
      abs_add_le _ _
    have hA : |2 * σ * h σ| ≤ 2 * δ := by
      rw [abs_mul, abs_mul, hid2]
      refine mul_le_mul ?_ hha (abs_nonneg _) (by norm_num)
      linarith [hσ1, abs_nonneg σ]
    have hB : |(t + t') * σ ^ 2| ≤ 4 := by
      rw [abs_mul, abs_pow]
      have hsq : |σ| ^ 2 ≤ 1 := by nlinarith [hσ1, abs_nonneg σ]
      nlinarith [htt, hsq, abs_nonneg (t + t'), hsq]
    linarith
  have hpart1 : |iteratedDeriv i (fun _ : ℝ => 2 * σ * h σ + (t + t') * σ ^ 2) a| ≤ 2 * δ + 4 :=
    le_trans (aw_abs_iteratedDeriv_const_le (2 * σ * h σ + (t + t') * σ ^ 2) i a) hc
  have hprod : (fun a' : ℝ => 2 * (a' * h a') + (t + t') * (a' * a'))
      = (fun a' : ℝ => 2 * (a' * h a')) + (fun a' : ℝ => (t + t') * (a' * a')) := by
    funext x; simp
  have hpc1 : ContDiffAt ℝ (i : ℕ∞) (fun a' : ℝ => 2 * (a' * h a')) a :=
    (contDiffAt_const (c := (2:ℝ))).mul (hiC.mul hhiC)
  have hpc2 : ContDiffAt ℝ (i : ℕ∞) (fun a' : ℝ => (t + t') * (a' * a')) a :=
    (contDiffAt_const (c := t + t')).mul (hiC.mul hiC)
  have hA2 : |iteratedDeriv i (fun a' : ℝ => 2 * (a' * h a')) a| ≤ 2 * 2 ^ i * δ := by
    have h1 : |iteratedDeriv i (fun x : ℝ => x * h x) a| ≤ 2 ^ i * (1 * δ) :=
      aw_prod_jet_le (by norm_num) hδ0 (fun k hk => hidA k hk) (fun k hk => hjet k hk a) hidC hhC hi
    have h2 : (fun a' : ℝ => 2 * (a' * h a')) = (fun x : ℝ => (2:ℝ) * (x * h x)) := by
      funext x; ring
    rw [h2]
    have h3 := abs_iteratedDeriv_const_mul_le (c := (2:ℝ)) (f := fun x : ℝ => x * h x)
      (i := i) (a := a) (A := 2 ^ i * (1 * δ))
      (hiC.mul hhiC) h1
    have h4 : |(2:ℝ)| * (2 ^ i * (1 * δ)) = 2 * 2 ^ i * δ := by rw [hid2]; ring
    exact le_trans h3 (le_of_eq h4)
  have hB2 : |iteratedDeriv i (fun a' : ℝ => (t + t') * (a' * a')) a| ≤ 4 * 2 ^ i := by
    have h1 : |iteratedDeriv i (fun x : ℝ => x * x) a| ≤ 2 ^ i * (1 * 1) :=
      aw_prod_jet_le (by norm_num) (by norm_num) (fun k hk => hidA k hk)
        (fun k hk => hidA k hk) hidC hidC hi
    have h2 : (fun a' : ℝ => (t + t') * (a' * a')) = (fun x : ℝ => (t + t') * (x * x)) := by
      funext x; ring
    rw [h2]
    have h3 := abs_iteratedDeriv_const_mul_le (c := t + t') (f := fun x : ℝ => x * x)
      (i := i) (a := a) (A := 2 ^ i * (1 * 1)) (hiC.mul hiC) h1
    have h4 : |t + t'| * (2 ^ i * (1 * 1)) ≤ 4 * 2 ^ i := by nlinarith [htt, h2i0]
    exact le_trans h3 h4
  have hpart2 : |iteratedDeriv i (fun a' : ℝ => 2 * (a' * h a') + (t + t') * (a' * a')) a|
      ≤ 2 ^ (i + 1) * δ + 4 * 2 ^ i := by
    rw [hprod]
    have h5 := abs_iteratedDeriv_add_le hpc1 hpc2 hA2 hB2
    have h6 : 2 * 2 ^ i * δ + 4 * 2 ^ i = 2 ^ (i + 1) * δ + 4 * 2 ^ i := by ring
    exact le_trans h5 (le_of_eq h6)
  have hG : (fun a' : ℝ => awZB h a' σ + (t + t') * awZC a' σ)
      = (fun _ : ℝ => 2 * σ * h σ + (t + t') * σ ^ 2)
        - (fun a' : ℝ => 2 * (a' * h a') + (t + t') * (a' * a')) := by
    funext x; simp only [Pi.sub_apply, awZB, awZC]; ring
  rw [hG]
  have c1 : ContDiffAt ℝ (i : ℕ∞) (fun _ : ℝ => 2 * σ * h σ + (t + t') * σ ^ 2) a :=
    (contDiffAt_const (c := 2 * σ * h σ + (t + t') * σ ^ 2)).of_le
      (Work.OddExistence.Manifest.AW.natCast_le_top_enat i)
  have c2 : ContDiffAt ℝ (i : ℕ∞)
      (fun a' : ℝ => 2 * (a' * h a') + (t + t') * (a' * a')) a := by
    rw [hprod]
    exact hpc1.add hpc2
  have hfin := abs_iteratedDeriv_sub_le c1 c2 hpart1 hpart2
  have hsum : (2 * δ + 4) + (2 ^ (i + 1) * δ + 4 * 2 ^ i)
      = 2 * δ + 4 + 2 ^ (i + 1) * δ + 4 * 2 ^ i := by ring
  exact le_trans hfin (le_of_eq hsum)

/-- **Uniform-in-`h` `t`-difference bound for the `a`-jets of the radicand.** -/
lemma abs_ZJ_t_sub_le {N : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ N → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ)
    {a σ t t' : ℝ} (ha : a ∈ Set.Icc (49 / 100 : ℝ) 1) (ht : t ∈ Set.Icc (-2 : ℝ) 2)
    (ht' : t' ∈ Set.Icc (-2 : ℝ) 2) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (19 / 20)) {i : ℕ}
    (hi : i ≤ N) :
    |Work.Anchor.ZJ h i a σ t - Work.Anchor.ZJ h i a σ t'| ≤ (5 * 2 ^ N + 8) * |t - t'| := by
  have hstep : |Work.Anchor.ZJ h i a σ t - Work.Anchor.ZJ h i a σ t'|
      = |t - t'| * |iteratedDeriv i (fun a' : ℝ => awZB h a' σ + (t + t') * awZC a' σ) a| := by
    rw [ZJ_t_sub_eq h hh i a σ t t', abs_mul]
  rw [hstep]
  have hX := abs_iteratedDeriv_awG_le hh hδ0 hδ1 hjet ha ht ht' hσ hi
  have h2N : (1:ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have h2i : (0:ℝ) ≤ 2 ^ i := by positivity
  have h2iN : (2:ℝ) ^ (i + 1) ≤ 2 ^ (N + 1) :=
    pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
  have h2N1 : (2:ℝ) ^ (N + 1) = 2 * 2 ^ N := by ring
  have hA : 2 ^ (i + 1) * δ ≤ 2 ^ (N + 1) * (1 / 100) :=
    mul_le_mul h2iN hδ1 hδ0 (by positivity)
  have hB : (2:ℝ) ^ i ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
  have hM : 2 * δ + 4 + 2 ^ (i + 1) * δ + 4 * 2 ^ i ≤ 5 * 2 ^ N + 8 := by
    nlinarith [hA, hB, hδ1, hδ0, h2N, h2N1, pow_nonneg (by norm_num : (0:ℝ) ≤ 2) N]
  have h3 : |t - t'| * (2 * δ + 4 + 2 ^ (i + 1) * δ + 4 * 2 ^ i)
      ≤ |t - t'| * (5 * 2 ^ N + 8) := mul_le_mul_of_nonneg_left hM (abs_nonneg _)
  calc |t - t'| * |iteratedDeriv i (fun a' : ℝ => awZB h a' σ + (t + t') * awZC a' σ) a|
      ≤ |t - t'| * (2 * δ + 4 + 2 ^ (i + 1) * δ + 4 * 2 ^ i) :=
        mul_le_mul_of_nonneg_left hX (abs_nonneg _)
    _ ≤ |t - t'| * (5 * 2 ^ N + 8) := h3
    _ = (5 * 2 ^ N + 8) * |t - t'| := by ring

/-! ## The recursion constants -/

/-- The recursion constants of the `a`-jets of `Rnu`. -/
noncomputable def awTA (ν B I : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => I
  | (m + 1), j =>
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (B * awTA ν B I m (j - i + 1) + |ν - (m : ℝ)| * B * awTA ν B I m (j - i))

/-- The recursion constants of the `t`-differences of the `a`-jets of `Rnu`. -/
noncomputable def awTD (ν B B1 I I1 : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => I1
  | (m + 1), j =>
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (B1 * awTA ν B I m (j - i + 1) + B * awTD ν B B1 I I1 m (j - i + 1)
         + |ν - (m : ℝ)| * (B1 * awTA ν B I m (j - i) + B * awTD ν B B1 I I1 m (j - i)))

lemma awTA_nonneg (ν B I : ℝ) (hB : 0 ≤ B) (hI : 0 ≤ I) : ∀ m j, 0 ≤ awTA ν B I m j := by
  intro m
  induction m with
  | zero => intro j; exact hI
  | succ m ih =>
    intro j
    rw [awTA]
    refine Finset.sum_nonneg fun i _ => ?_
    exact mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (mul_nonneg hB (ih _))
        (mul_nonneg (mul_nonneg (abs_nonneg _) hB) (ih _)))

lemma awTD_nonneg (ν B B1 I I1 : ℝ) (hB : 0 ≤ B) (hB1 : 0 ≤ B1) (hI : 0 ≤ I) (hI1 : 0 ≤ I1) :
    ∀ m j, 0 ≤ awTD ν B B1 I I1 m j := by
  intro m
  induction m with
  | zero => intro j; exact hI1
  | succ m ih =>
    intro j
    rw [awTD]
    refine Finset.sum_nonneg fun i _ => ?_
    have h1 := awTA_nonneg ν B I hB hI m (j - i + 1)
    have h2 := awTA_nonneg ν B I hB hI m (j - i)
    have h3 := ih (j - i + 1)
    have h4 := ih (j - i)
    exact mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (add_nonneg (mul_nonneg hB1 h1) (mul_nonneg hB h3))
        (mul_nonneg (abs_nonneg _) (add_nonneg (mul_nonneg hB1 h2) (mul_nonneg hB h4))))

/-- Telescoping estimate for products with independent `t`-difference scales. -/
lemma abs_mul_sub_mul_le' {x1 x2 y1 y2 Bx Bx' By By' d : ℝ}
    (hx : |x1| ≤ Bx) (hxd : |x1 - x2| ≤ Bx' * d) (hy : |y2| ≤ By) (hyd : |y1 - y2| ≤ By' * d) :
    |x1 * y1 - x2 * y2| ≤ (Bx * By' + Bx' * By) * d := by
  have hkey : x1 * y1 - x2 * y2 = x1 * (y1 - y2) + (x1 - x2) * y2 := by ring
  rw [hkey]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_mul]
  have h1 : |x1| * |y1 - y2| ≤ Bx * (By' * d) :=
    mul_le_mul hx hyd (abs_nonneg _) (le_trans (abs_nonneg _) hx)
  have h2 : |x1 - x2| * |y2| ≤ (Bx' * d) * By :=
    mul_le_mul hxd hy (abs_nonneg _) (le_trans (abs_nonneg _) hxd)
  calc |x1| * |y1 - y2| + |x1 - x2| * |y2| ≤ Bx * (By' * d) + (Bx' * d) * By := add_le_add h1 h2
    _ = (Bx * By' + Bx' * By) * d := by ring

/-! ## The main recursion bound -/

/-- **Uniform-in-`h` bounds and `t`-difference bounds for the `a`-jets of `Rnu`.** -/
theorem aw_rjet_bounds (ν : ℝ) (N : ℕ) (B B1 I I1 : ℝ)
    (init : ℝ × ℝ × ℝ → ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hinit : ContDiff ℝ (⊤ : ℕ∞) init)
    (hB : 0 ≤ B) (hB1 : 0 ≤ B1) (hI : 0 ≤ I) (hI1 : 0 ≤ I1)
    (hZval : ∀ j, j ≤ N → ∀ a σ t, Work.Anchor.Reg a σ t → |Work.Anchor.ZJ h j a σ t| ≤ B)
    (hZdif : ∀ j, j ≤ N → ∀ a σ t t', Work.Anchor.Reg a σ t → Work.Anchor.Reg a σ t' →
      |Work.Anchor.ZJ h j a σ t - Work.Anchor.ZJ h j a σ t'| ≤ B1 * |t - t'|)
    (hIval : ∀ j, j ≤ N → ∀ a σ t, Work.Anchor.Reg a σ t →
      |iteratedDeriv j (fun a' : ℝ => init (a', σ, t)) a| ≤ I)
    (hIdif : ∀ j, j ≤ N → ∀ a σ t t', Work.Anchor.Reg a σ t → Work.Anchor.Reg a σ t' →
      |iteratedDeriv j (fun a' : ℝ => init (a', σ, t)) a
        - iteratedDeriv j (fun a' : ℝ => init (a', σ, t')) a| ≤ I1 * |t - t'|) :
    ∀ m j, j + m ≤ N → ∀ a σ t t', Work.Anchor.Reg a σ t → Work.Anchor.Reg a σ t' →
      |Work.Anchor.Rjet ν h init m j a σ t| ≤ awTA ν B I m j ∧
      |Work.Anchor.Rjet ν h init m j a σ t - Work.Anchor.Rjet ν h init m j a σ t'|
        ≤ awTD ν B B1 I I1 m j * |t - t'| := by
  intro m
  induction m with
  | zero =>
    intro j hj a σ t t' ht ht'
    have h0 : Work.Anchor.Rjet ν h init 0 j a σ t
        = iteratedDeriv j (fun a' : ℝ => init (a', σ, t)) a := rfl
    have h0' : Work.Anchor.Rjet ν h init 0 j a σ t'
        = iteratedDeriv j (fun a' : ℝ => init (a', σ, t')) a := rfl
    have hAb : awTA ν B I 0 j = I := rfl
    have hDb : awTD ν B B1 I I1 0 j = I1 := rfl
    rw [h0, h0', hAb, hDb]
    exact ⟨hIval j (by omega) a σ t ht, hIdif j (by omega) a σ t t' ht ht'⟩
  | succ m ih =>
    intro j hj a σ t t' ht ht'
    have hm1 : ∀ i, i ∈ Finset.range (j + 1) → (j - i + 1) + m ≤ N := by
      intro i hi; rw [Finset.mem_range] at hi; omega
    have hm0 : ∀ i, i ∈ Finset.range (j + 1) → (j - i) + m ≤ N := by
      intro i hi; rw [Finset.mem_range] at hi; omega
    have hiN : ∀ i, i ∈ Finset.range (j + 1) → i ≤ N := by
      intro i hi; rw [Finset.mem_range] at hi; omega
    have hi1N : ∀ i, i ∈ Finset.range (j + 1) → i + 1 ≤ N := by
      intro i hi; rw [Finset.mem_range] at hi; omega
    have hC : ∀ i, (0:ℝ) ≤ (j.choose i : ℝ) := fun i => Nat.cast_nonneg _
    constructor
    · -- the value bound
      rw [Work.Anchor.Rjet_succ ν hh hinit m j a σ t, awTA]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i hi => ?_)
      rw [abs_mul, abs_of_nonneg (hC i)]
      refine mul_le_mul_of_nonneg_left ?_ (hC i)
      have e1 : |Work.Anchor.ZJ h i a σ t * Work.Anchor.Rjet ν h init m (j - i + 1) a σ t|
          ≤ B * awTA ν B I m (j - i + 1) := by
        rw [abs_mul]
        exact mul_le_mul (hZval i (hiN i hi) a σ t ht)
          ((ih (j - i + 1) (hm1 i hi) a σ t t' ht ht').1) (abs_nonneg _) hB
      have e2 : |(ν - (m : ℝ)) *
            (Work.Anchor.ZJ h (i + 1) a σ t * Work.Anchor.Rjet ν h init m (j - i) a σ t)|
          ≤ |ν - (m : ℝ)| * (B * awTA ν B I m (j - i)) := by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_mul]
        exact mul_le_mul (hZval (i + 1) (hi1N i hi) a σ t ht)
          ((ih (j - i) (hm0 i hi) a σ t t' ht ht').1) (abs_nonneg _) hB
      have hsum := le_trans (abs_add_le _ _) (add_le_add e1 e2)
      exact le_trans hsum (le_of_eq (by ring))
    · -- the `t`-difference bound
      rw [Work.Anchor.Rjet_succ ν hh hinit m j a σ t,
        Work.Anchor.Rjet_succ ν hh hinit m j a σ t',
        ← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [awTD, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have h1 := hm1 i hi
      have h2 := hm0 i hi
      have hv1 : |Work.Anchor.Rjet ν h init m (j - i + 1) a σ t| ≤ awTA ν B I m (j - i + 1) :=
        (ih (j - i + 1) h1 a σ t t' ht ht').1
      have hv1' : |Work.Anchor.Rjet ν h init m (j - i + 1) a σ t'| ≤ awTA ν B I m (j - i + 1) :=
        (ih (j - i + 1) h1 a σ t' t ht' ht).1
      have hv2 : |Work.Anchor.Rjet ν h init m (j - i) a σ t| ≤ awTA ν B I m (j - i) :=
        (ih (j - i) h2 a σ t t' ht ht').1
      have hv2' : |Work.Anchor.Rjet ν h init m (j - i) a σ t'| ≤ awTA ν B I m (j - i) :=
        (ih (j - i) h2 a σ t' t ht' ht).1
      have hd1 : |Work.Anchor.Rjet ν h init m (j - i + 1) a σ t
          - Work.Anchor.Rjet ν h init m (j - i + 1) a σ t'|
          ≤ awTD ν B B1 I I1 m (j - i + 1) * |t - t'| :=
        (ih (j - i + 1) h1 a σ t t' ht ht').2
      have hd2 : |Work.Anchor.Rjet ν h init m (j - i) a σ t
          - Work.Anchor.Rjet ν h init m (j - i) a σ t'|
          ≤ awTD ν B B1 I I1 m (j - i) * |t - t'| :=
        (ih (j - i) h2 a σ t t' ht ht').2
      have hkey : (j.choose i : ℝ) *
            (Work.Anchor.ZJ h i a σ t * Work.Anchor.Rjet ν h init m (j - i + 1) a σ t
              + (ν - (m : ℝ)) *
                (Work.Anchor.ZJ h (i + 1) a σ t * Work.Anchor.Rjet ν h init m (j - i) a σ t))
          - (j.choose i : ℝ) *
            (Work.Anchor.ZJ h i a σ t' * Work.Anchor.Rjet ν h init m (j - i + 1) a σ t'
              + (ν - (m : ℝ)) *
                (Work.Anchor.ZJ h (i + 1) a σ t' * Work.Anchor.Rjet ν h init m (j - i) a σ t'))
          = (j.choose i : ℝ) *
            ((Work.Anchor.ZJ h i a σ t * Work.Anchor.Rjet ν h init m (j - i + 1) a σ t
                - Work.Anchor.ZJ h i a σ t' * Work.Anchor.Rjet ν h init m (j - i + 1) a σ t')
              + (ν - (m : ℝ)) *
                (Work.Anchor.ZJ h (i + 1) a σ t * Work.Anchor.Rjet ν h init m (j - i) a σ t
                  - Work.Anchor.ZJ h (i + 1) a σ t'
                    * Work.Anchor.Rjet ν h init m (j - i) a σ t')) := by ring
      rw [hkey, abs_mul, abs_of_nonneg (hC i), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (hC i)
      refine le_trans (abs_add_le _ _) ?_
      have f1 : |Work.Anchor.ZJ h i a σ t * Work.Anchor.Rjet ν h init m (j - i + 1) a σ t
            - Work.Anchor.ZJ h i a σ t' * Work.Anchor.Rjet ν h init m (j - i + 1) a σ t'|
          ≤ (B * awTD ν B B1 I I1 m (j - i + 1) + B1 * awTA ν B I m (j - i + 1)) * |t - t'| :=
        abs_mul_sub_mul_le' (hZval i (hiN i hi) a σ t ht)
          (hZdif i (hiN i hi) a σ t t' ht ht') hv1' hd1
      have f2 : |(ν - (m : ℝ)) *
            (Work.Anchor.ZJ h (i + 1) a σ t * Work.Anchor.Rjet ν h init m (j - i) a σ t
              - Work.Anchor.ZJ h (i + 1) a σ t'
                * Work.Anchor.Rjet ν h init m (j - i) a σ t')|
          ≤ |ν - (m : ℝ)| *
            ((B * awTD ν B B1 I I1 m (j - i) + B1 * awTA ν B I m (j - i)) * |t - t'|) := by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact abs_mul_sub_mul_le' (hZval (i + 1) (hi1N i hi) a σ t ht)
          (hZdif (i + 1) (hi1N i hi) a σ t t' ht ht') hv2' hd2
      refine le_trans (add_le_add f1 f2) (le_of_eq ?_)
      ring

end

end Work.OddVolterra.Existence
