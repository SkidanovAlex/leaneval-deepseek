import Submission.Vinogradov.Extension
import Submission.Commons.Analysis.Complex.norm_exp_mul_I_sub_le

noncomputable section
open MeasureTheory Complex
open scoped Real BigOperators Interval
open LeanEval.NumberTheory.VinogradovMeanValue

set_option autoImplicit false

namespace Submission.Vinogradov

/-!
# Affine rescaling of the moment curve (BDG §7)

The moment curve `γ(t) = (t, t², …, tᵏ)` is *affinely rigid*: up to a
translation of the phase, composing `t ↦ γ(t)` with an affine map
`t ↦ ρ·t + t₀` is the same as applying an invertible linear map to the
frequency vector `x`.  Precisely (all lemmas below are proved), for
`x ∈ E k = ℝᵏ`, `ρ, t₀, t ∈ ℝ`,

    `x·γ(ρ·t + t₀) = x·γ(t₀) + (A x)·γ(t)`,
    `A x = ((Σ_j x_j · C(j+1,l+1) · ρ^{l+1} · t₀^{j-l}))_{l<k}`,

i.e. `momChar k x (ρ·t + t₀) = momChar k x t₀ · momChar k (A x) t`
(`momPhase_affine`, `momChar_affine`); the matrix `A` is upper triangular with
diagonal `(ρ, ρ², …, ρᵏ)` (the `ρ = 1` case is the unipotent translation
matrix of the proof of BDG Lemma 7.3 / Lemma 7.5, whose "bounded distortion"
for `t₀ ∈ [0,1]` is the content of `sum_norm_affVec_one_le`).

The change of variables `s = ρ·u + t₀` for the extension operator
`E_J g(x) = ∫_J g(t) e(x·γ(t)) dt` is `extOp_affine`:

    `E_{[ρa+t₀, ρb+t₀]} g(x)
       = ρ · e(x·γ(t₀)) · E_{[a,b]}(g(ρ·+t₀))(A x)`

with the immediate norm consequence `extOp_affine_norm_le`.  These are the
elementary inputs of BDG's parabolic rescaling (BDG §7, Lemma 7.3) and of the
lower-dimensional decoupling lemma (BDG §8, Lemma `nl5`).

We also record the **local constancy** of the character in the frequency
variable `x` and the resulting Lipschitz bound for the extension operator
(`momChar_diff_le`, `extOp_lipschitz`): since the frequencies of `momChar`
live in `[-1,1]`, `E_J g` is essentially constant at scale `1/(2π k)`; this is
the "trivial" input of the Nikolskii-type comparison of `Lᵖ(w_B)` norms for
different `p` (BDG §7, Corollary 7.2).

Nothing here needs the deep decoupling theorem; all lemmas below are proved.
-/

/-- **The affine-imaged frequency vector.**  `affVec k ρ t₀ x` has
`l`-th coordinate `Σ_j x_j · C(j+1,l+1) · ρ^{l+1} · t₀^{j-l}`
(so that `x·γ(ρt+t₀) = x·γ(t₀) + (affVec k ρ t₀ x)·γ(t)`). -/
noncomputable def affVec (k : ℕ) (ρ t₀ : ℝ) (x : E k) : E k :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun l : Fin k =>
    ∑ j : Fin k, x j * ((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ)
      * ρ ^ (l.val + 1) * t₀ ^ (j.val - l.val))

/-- Defining equation of `affVec` (definitional unfolding). -/
lemma affVec_apply (k : ℕ) (ρ t₀ : ℝ) (x : E k) (l : Fin k) :
    affVec k ρ t₀ x l = ∑ j : Fin k, x j
      * ((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ) * ρ ^ (l.val + 1)
      * t₀ ^ (j.val - l.val) := rfl

/-- Binomial expansion of `(ρt + t₀)^n`, grouped by powers of `t`: the terms
beyond the `n`-th power of `t` vanish because `n.choose (l+1) = 0` there. -/
lemma pow_binom_expand (n : ℕ) (ρ t₀ t : ℝ) {k : ℕ} (hk : n ≤ k) :
    (ρ * t + t₀) ^ n
      = t₀ ^ n + ∑ l ∈ Finset.range k,
          ((n.choose (l + 1) : ℕ) : ℝ) * ρ ^ (l + 1) * t₀ ^ (n - (l + 1))
            * t ^ (l + 1) := by
  rw [add_pow]
  rw [Finset.sum_range_succ' (fun m => (ρ * t) ^ m * t₀ ^ (n - m) * ((n.choose m : ℕ) : ℝ)) n]
  simp only [pow_zero, one_mul, mul_one, tsub_zero, Nat.choose_zero_right, Nat.cast_one]
  have hsum1 : (∑ i ∈ Finset.range n,
        (ρ * t) ^ (i + 1) * t₀ ^ (n - (i + 1)) * ((n.choose (i + 1) : ℕ) : ℝ))
      = ∑ i ∈ Finset.range n,
        ((n.choose (i + 1) : ℕ) : ℝ) * ρ ^ (i + 1) * t₀ ^ (n - (i + 1)) * t ^ (i + 1) :=
    Finset.sum_congr rfl (fun i _ => by rw [mul_pow]; ring)
  rw [hsum1]
  have hsub : ∑ i ∈ Finset.range n,
        ((n.choose (i + 1) : ℕ) : ℝ) * ρ ^ (i + 1) * t₀ ^ (n - (i + 1)) * t ^ (i + 1)
      = ∑ l ∈ Finset.range k,
        ((n.choose (l + 1) : ℕ) : ℝ) * ρ ^ (l + 1) * t₀ ^ (n - (l + 1)) * t ^ (l + 1) := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr hk) ?_
    intro x hx hxn
    simp only [Finset.mem_range] at hx hxn
    have hlt : n < x + 1 := Nat.lt_succ_of_le (Nat.le_of_not_lt hxn)
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp
  rw [hsub]
  ring

/-- **Affine rigidity of the moment curve** (phase form): the phase of
`γ(ρt+t₀)` splits as the phase at `t₀` plus the phase of `affVec k ρ t₀ x`
at `t`. -/
lemma momPhase_affine (k : ℕ) (x : E k) (ρ t₀ t : ℝ) :
    momPhase k x (ρ * t + t₀) = momPhase k x t₀ + momPhase k (affVec k ρ t₀ x) t := by
  have hpow : ∀ j : Fin k, (ρ * t + t₀) ^ (j.val + 1)
      = t₀ ^ (j.val + 1) + ∑ l ∈ Finset.range k,
          ((Nat.choose (j.val + 1) (l + 1) : ℕ) : ℝ) * ρ ^ (l + 1)
            * t₀ ^ (j.val - l) * t ^ (l + 1) := by
    intro j
    rw [pow_binom_expand (k := k) (j.val + 1) ρ t₀ t (Nat.succ_le_of_lt j.isLt)]
    congr 1
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Nat.succ_sub_succ]
  have hA : (∑ j : Fin k, x j * (ρ * t + t₀) ^ (j.val + 1))
      = ∑ j : Fin k, x j * (t₀ ^ (j.val + 1) + ∑ l ∈ Finset.range k,
          ((Nat.choose (j.val + 1) (l + 1) : ℕ) : ℝ) * ρ ^ (l + 1)
            * t₀ ^ (j.val - l) * t ^ (l + 1)) :=
    Finset.sum_congr rfl (fun j _ => by rw [hpow j])
  have hB : (∑ j : Fin k, x j * (t₀ ^ (j.val + 1) + ∑ l ∈ Finset.range k,
          ((Nat.choose (j.val + 1) (l + 1) : ℕ) : ℝ) * ρ ^ (l + 1)
            * t₀ ^ (j.val - l) * t ^ (l + 1)))
      = (∑ j : Fin k, x j * t₀ ^ (j.val + 1))
        + ∑ j : Fin k, x j * (∑ l ∈ Finset.range k,
            ((Nat.choose (j.val + 1) (l + 1) : ℕ) : ℝ) * ρ ^ (l + 1)
              * t₀ ^ (j.val - l) * t ^ (l + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_add]
  have hC : (∑ j : Fin k, x j * (∑ l ∈ Finset.range k,
            ((Nat.choose (j.val + 1) (l + 1) : ℕ) : ℝ) * ρ ^ (l + 1)
              * t₀ ^ (j.val - l) * t ^ (l + 1)))
      = ∑ l ∈ Finset.range k, (∑ j : Fin k, x j *
            (((Nat.choose (j.val + 1) (l + 1) : ℕ) : ℝ) * ρ ^ (l + 1)
              * t₀ ^ (j.val - l) * t ^ (l + 1))) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hD : (∑ l ∈ Finset.range k, (∑ j : Fin k, x j *
            (((Nat.choose (j.val + 1) (l + 1) : ℕ) : ℝ) * ρ ^ (l + 1)
              * t₀ ^ (j.val - l) * t ^ (l + 1))))
      = ∑ l : Fin k, (affVec k ρ t₀ x) l * t ^ (l.val + 1) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [affVec_apply]
    rw [show (∑ j : Fin k, x j * (((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ)
              * ρ ^ (l.val + 1) * t₀ ^ (j.val - l.val) * t ^ (l.val + 1)))
          = ∑ j : Fin k, (x j * ((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ)
              * ρ ^ (l.val + 1) * t₀ ^ (j.val - l.val)) * t ^ (l.val + 1)
        from Finset.sum_congr rfl (fun j _ => by ring)]
    rw [Finset.sum_mul]
  unfold momPhase
  rw [hA, hB, hC, hD]

/-- **Affine rigidity of the moment curve** (character form). -/
lemma momChar_affine (k : ℕ) (x : E k) (ρ t₀ t : ℝ) :
    momChar k x (ρ * t + t₀) = momChar k x t₀ * momChar k (affVec k ρ t₀ x) t := by
  rw [momChar_eq_exp, momChar_eq_exp, momChar_eq_exp, momPhase_affine k x ρ t₀ t]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Change of variables for the extension operator** (BDG §7, Lemma 7.3 and
the proof of Lemma 7.5): substituting `s = ρ·u + t₀`,

    `E_{[ρa+t₀, ρb+t₀]} g(x) = ρ·e(x·γ(t₀))·E_{[a,b]}(g(ρ·+t₀))(affVec k ρ t₀ x)`. -/
lemma extOp_affine (k : ℕ) (g : ℝ → ℂ) {ρ t₀ a b : ℝ} (hρ : 0 < ρ) (x : E k) :
    extOp k g (ρ * a + t₀) (ρ * b + t₀) x
      = ((ρ : ℂ) * momChar k x t₀)
          * extOp k (fun u => g (ρ * u + t₀)) a b (affVec k ρ t₀ x) := by
  have hrev : (∫ s in (ρ * a + t₀)..(ρ * b + t₀), g s * momChar k x s)
      = ρ • ∫ u in a..b, g (ρ * u + t₀) * momChar k x (ρ * u + t₀) := by
    have h := intervalIntegral.integral_comp_mul_add
      (f := fun s => g s * momChar k x s) (a := a) (b := b) (c := ρ) hρ.ne' t₀
    have h2 := congrArg (fun z => ρ • z) h
    rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul] at h2
    exact h2.symm
  have hcongr : (∫ u in a..b, g (ρ * u + t₀) * momChar k x (ρ * u + t₀))
      = momChar k x t₀ * ∫ u in a..b, g (ρ * u + t₀) * momChar k (affVec k ρ t₀ x) u := by
    rw [show (fun u => g (ρ * u + t₀) * momChar k x (ρ * u + t₀))
          = (fun u => momChar k x t₀ * (g (ρ * u + t₀)
              * momChar k (affVec k ρ t₀ x) u)) from ?_]
    · rw [intervalIntegral.integral_const_mul]
    · funext u
      rw [momChar_affine k x ρ t₀ u]
      ring
  unfold extOp
  rw [hrev, hcongr]
  rw [Complex.real_smul]
  ring

/-- **Translation special case** (`ρ = 1`) of `extOp_affine`: the change of
variables `s = u + t₀` is implemented by the unipotent linear map
`affVec k 1 t₀`. -/
lemma extOp_translate (k : ℕ) (g : ℝ → ℂ) (t₀ a b : ℝ) (x : E k) :
    extOp k g (a + t₀) (b + t₀) x
      = momChar k x t₀ * extOp k (fun u => g (u + t₀)) a b (affVec k 1 t₀ x) := by
  have h := extOp_affine k g (ρ := 1) (t₀ := t₀) (a := a) (b := b) (by norm_num) x
  have h1 : (fun u : ℝ => g (1 * u + t₀)) = (fun u : ℝ => g (u + t₀)) := by
    funext u; rw [one_mul]
  rw [h1] at h
  simpa using h

/-- **Norm form of the change of variables**: the affine rescaling loses only
the factor `ρ`. -/
lemma extOp_affine_norm_le (k : ℕ) (g : ℝ → ℂ) {ρ t₀ a b : ℝ} (hρ : 0 < ρ)
    (hab : a ≤ b) (x : E k) :
    ‖extOp k g (ρ * a + t₀) (ρ * b + t₀) x‖ ≤ ρ * ∫ u in a..b, ‖g (ρ * u + t₀)‖ := by
  have hρnorm : ‖(ρ : ℂ)‖ = ρ := (RCLike.norm_ofReal ρ).trans (abs_of_pos hρ)
  rw [extOp_affine k g hρ x, norm_mul, norm_mul, hρnorm, momChar_norm_one, mul_one]
  have hb := extOp_norm_le k (fun u => g (ρ * u + t₀)) hab (affVec k ρ t₀ x)
  exact mul_le_mul_of_nonneg_left hb (le_of_lt hρ)

/-- **Bounded distortion of the translation matrix** (`ρ = 1`, `|t₀| ≤ 1`):
`Σ_l |(affVec k 1 t₀ x)_l| ≤ k·2ᵏ · Σ_j |x_j|` (each binomial coefficient
`C(j+1,l+1)` is at most `2^{j+1} ≤ 2ᵏ`, and `|t₀|^{j-l} ≤ 1`).  Constants
depending only on `k` are irrelevant for the applications.  The form
`|t₀| ≤ 1` applies to both the map `t ↦ t + t₀` and its inverse
`t ↦ t - t₀`. -/
lemma sum_norm_affVec_one_le (k : ℕ) {t₀ : ℝ} (ht : |t₀| ≤ 1) (x : E k) :
    ∑ l : Fin k, ‖affVec k 1 t₀ x l‖ ≤ (k : ℝ) * (2 : ℝ) ^ k * ∑ j : Fin k, ‖x j‖ := by
  have htle : ∀ n : ℕ, ‖t₀ ^ n‖ ≤ 1 := by
    intro n
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg t₀) ht
  have hC : ∀ j l : Fin k, ((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
    intro j l
    have h1 : Nat.choose (j.val + 1) (l.val + 1) ≤ 2 ^ (j.val + 1) := Nat.choose_le_two_pow _ _
    have h2 : (2 : ℕ) ^ (j.val + 1) ≤ (2 : ℕ) ^ k :=
      Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt j.isLt)
    calc ((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ)
        ≤ ((2 : ℕ) ^ (j.val + 1) : ℕ) := by exact_mod_cast h1
      _ ≤ ((2 : ℕ) ^ k : ℕ) := by exact_mod_cast h2
      _ = (2 : ℝ) ^ k := by push_cast; ring
  have hstep : ∀ l : Fin k, ‖affVec k 1 t₀ x l‖ ≤ ∑ j : Fin k, ‖x j‖ * (2 : ℝ) ^ k := by
    intro l
    rw [affVec_apply]
    calc ‖∑ j : Fin k, x j * ((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ)
            * (1 : ℝ) ^ (l.val + 1) * t₀ ^ (j.val - l.val)‖
        ≤ ∑ j : Fin k, ‖x j * ((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ)
            * (1 : ℝ) ^ (l.val + 1) * t₀ ^ (j.val - l.val)‖ := norm_sum_le _ _
      _ = ∑ j : Fin k, ‖x j‖ * ((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ)
            * ‖t₀ ^ (j.val - l.val)‖ := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have hCn : ‖((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ)‖
              = ((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
          simp only [norm_mul, one_pow, mul_one, hCn]
      _ ≤ ∑ j : Fin k, ‖x j‖ * (2 : ℝ) ^ k := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          calc ‖x j‖ * ((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ)
                * ‖t₀ ^ (j.val - l.val)‖
              ≤ ‖x j‖ * ((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ) * 1 := by
                apply mul_le_mul_of_nonneg_left (htle _)
                positivity
            _ = ‖x j‖ * ((Nat.choose (j.val + 1) (l.val + 1) : ℕ) : ℝ) := by ring
            _ ≤ ‖x j‖ * (2 : ℝ) ^ k := mul_le_mul_of_nonneg_left (hC j l) (norm_nonneg _)
  calc ∑ l : Fin k, ‖affVec k 1 t₀ x l‖
      ≤ ∑ l : Fin k, ∑ j : Fin k, ‖x j‖ * (2 : ℝ) ^ k :=
        Finset.sum_le_sum (fun l _ => hstep l)
    _ = ∑ j : Fin k, ∑ _l : Fin k, ‖x j‖ * (2 : ℝ) ^ k := Finset.sum_comm
    _ = ∑ j : Fin k, (k : ℕ) • (‖x j‖ * (2 : ℝ) ^ k) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    _ = ∑ j : Fin k, ((k : ℝ) * (2 : ℝ) ^ k) * ‖x j‖ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [nsmul_eq_mul]; ring
    _ = ((k : ℝ) * (2 : ℝ) ^ k) * ∑ j : Fin k, ‖x j‖ := by
        rw [Finset.mul_sum]

lemma momChar_diff_le (k : ℕ) (x y : E k) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖momChar k x t - momChar k y t‖ ≤ 2 * Real.pi * (∑ j : Fin k, ‖x j - y j‖) := by
  have hcast : ∀ a : ℝ, (((2 * Real.pi : ℂ) * Complex.I) * ((a : ℝ) : ℂ))
      = ((((2 * Real.pi * a : ℝ)) : ℂ)) * Complex.I := by
    intro a
    push_cast
    ring
  have hA : |momPhase k x t - momPhase k y t| ≤ ∑ j : Fin k, ‖x j - y j‖ := by
    have hterm : ∀ j : Fin k, |x j * t ^ (j.val + 1) - y j * t ^ (j.val + 1)|
        ≤ ‖x j - y j‖ := by
      intro j
      rw [← sub_mul, abs_mul, abs_pow, Real.norm_eq_abs]
      have htle : |t| ^ (j.val + 1) ≤ 1 := by
        rw [abs_of_nonneg ht0]
        exact pow_le_one₀ ht0 ht1
      calc |x j - y j| * |t| ^ (j.val + 1) ≤ |x j - y j| * 1 :=
            mul_le_mul_of_nonneg_left htle (abs_nonneg _)
        _ = |x j - y j| := by ring
    unfold momPhase
    rw [← Finset.sum_sub_distrib]
    calc |∑ j : Fin k, (x j * t ^ (j.val + 1) - y j * t ^ (j.val + 1))|
        ≤ ∑ j : Fin k, |x j * t ^ (j.val + 1) - y j * t ^ (j.val + 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin k, ‖x j - y j‖ := Finset.sum_le_sum (fun j _ => hterm j)
  calc ‖momChar k x t - momChar k y t‖
      = ‖Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((momPhase k x t : ℝ) : ℂ))
          - Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((momPhase k y t : ℝ) : ℂ))‖ := by
        rw [momChar_eq_exp, momChar_eq_exp]
    _ = ‖Complex.exp ((((2 * Real.pi * momPhase k x t : ℝ)) : ℂ) * Complex.I)
          - Complex.exp ((((2 * Real.pi * momPhase k y t : ℝ)) : ℂ) * Complex.I)‖ := by
        rw [hcast (momPhase k x t), hcast (momPhase k y t)]
    _ ≤ |2 * Real.pi * momPhase k x t - 2 * Real.pi * momPhase k y t| :=
        Commons.Analysis.Complex.norm_exp_mul_I_sub_le _ _
    _ = 2 * Real.pi * |momPhase k x t - momPhase k y t| := by
        rw [← mul_sub, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    _ ≤ 2 * Real.pi * (∑ j : Fin k, ‖x j - y j‖) :=
        mul_le_mul_of_nonneg_left hA (by positivity)

lemma extOp_lipschitz (k : ℕ) (g : ℝ → ℂ) (hg : Continuous g) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) (x y : E k) :
    ‖extOp k g a b x - extOp k g a b y‖
      ≤ 2 * Real.pi * (∑ j : Fin k, ‖x j - y j‖) * ∫ t in a..b, ‖g t‖ := by
  have hcx : IntervalIntegrable (fun t => g t * momChar k x t) volume a b :=
    (hg.mul (momChar_continuous_t k x)).intervalIntegrable a b
  have hcy : IntervalIntegrable (fun t => g t * momChar k y t) volume a b :=
    (hg.mul (momChar_continuous_t k y)).intervalIntegrable a b
  have hdiff : extOp k g a b x - extOp k g a b y
      = ∫ t in a..b, g t * (momChar k x t - momChar k y t) := by
    simp only [extOp]
    rw [← intervalIntegral.integral_sub hcx hcy]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  have hlb : ∀ t ∈ Set.Icc a b,
      ‖g t * (momChar k x t - momChar k y t)‖
        ≤ ‖g t‖ * (2 * Real.pi * (∑ j : Fin k, ‖x j - y j‖)) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans ha ht.1
    have ht1 : t ≤ 1 := le_trans ht.2 hb
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (momChar_diff_le k x y ht0 ht1) (norm_nonneg _)
  rw [hdiff]
  calc ‖∫ t in a..b, g t * (momChar k x t - momChar k y t)‖
      ≤ ∫ t in a..b, ‖g t * (momChar k x t - momChar k y t)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, ‖g t‖ * (2 * Real.pi * (∑ j : Fin k, ‖x j - y j‖)) := by
        refine intervalIntegral.integral_mono_on hab ?_ ?_ hlb
        · exact (hg.mul ((momChar_continuous_t k x).sub (momChar_continuous_t k y))).norm.intervalIntegrable _ _
        · exact ((continuous_norm.comp hg).mul_const _).intervalIntegrable _ _
    _ = (∫ t in a..b, ‖g t‖) * (2 * Real.pi * (∑ j : Fin k, ‖x j - y j‖)) :=
        intervalIntegral.integral_mul_const _ _
    _ = 2 * Real.pi * (∑ j : Fin k, ‖x j - y j‖) * ∫ t in a..b, ‖g t‖ := by ring

/-- **Operator norm bound for the translation matrix**: for `|t₀| ≤ 1` the map
`x ↦ affVec k 1 t₀ x` is bounded by a constant depending only on `k`
(`‖x‖ ≤ Σ_l ‖x_l‖ ≤ k‖x‖` together with `sum_norm_affVec_one_le`). -/
lemma norm_affVec_one_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (t₀ : ℝ), |t₀| ≤ 1 → ∀ x : E k,
    ‖affVec k 1 t₀ x‖ ≤ C * ‖x‖ := by
  refine ⟨(k : ℝ) ^ 2 * (2 : ℝ) ^ k + 1, by positivity, fun t₀ ht x => ?_⟩
  have h1 : ‖affVec k 1 t₀ x‖ ≤ ∑ l : Fin k, ‖affVec k 1 t₀ x l‖ := by
    rw [EuclideanSpace.norm_eq]
    have h : ∑ i, ‖affVec k 1 t₀ x i‖ ^ 2 ≤ (∑ i, ‖affVec k 1 t₀ x i‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
    calc √(∑ i, ‖affVec k 1 t₀ x i‖ ^ 2) ≤ √((∑ i, ‖affVec k 1 t₀ x i‖) ^ 2) :=
          Real.sqrt_le_sqrt h
      _ = ∑ i, ‖affVec k 1 t₀ x i‖ :=
          Real.sqrt_sq (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  have h2 : ∑ j : Fin k, ‖x j‖ ≤ (k : ℝ) * ‖x‖ := by
    calc ∑ j : Fin k, ‖x j‖ ≤ ∑ _j : Fin k, ‖x‖ := Finset.sum_le_sum (fun j _ => PiLp.norm_apply_le x j)
      _ = (k : ℝ) * ‖x‖ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h3 := sum_norm_affVec_one_le k ht x
  have hknn : (0 : ℝ) ≤ (k : ℝ) ^ 2 * (2 : ℝ) ^ k := by positivity
  calc ‖affVec k 1 t₀ x‖ ≤ ∑ l : Fin k, ‖affVec k 1 t₀ x l‖ := h1
    _ ≤ (k : ℝ) * (2 : ℝ) ^ k * ∑ j : Fin k, ‖x j‖ := h3
    _ ≤ (k : ℝ) * (2 : ℝ) ^ k * ((k : ℝ) * ‖x‖) := by
        apply mul_le_mul_of_nonneg_left h2; positivity
    _ = (k : ℝ) ^ 2 * (2 : ℝ) ^ k * ‖x‖ := by ring
    _ ≤ ((k : ℝ) ^ 2 * (2 : ℝ) ^ k + 1) * ‖x‖ := by
        have := norm_nonneg x; nlinarith [hknn, this]

end Submission.Vinogradov
