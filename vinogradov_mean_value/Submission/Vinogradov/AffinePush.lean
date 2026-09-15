import Submission.Vinogradov.Rescaling
import Submission.Vinogradov.AffineTransfer
import Submission.Commons.Analysis.InnerProductSpace.norm_le_sum_abs_coord

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Interval Topology
open LeanEval.NumberTheory.VinogradovMeanValue

set_option autoImplicit false

namespace Submission.Vinogradov

/-!
# The pushed-forward ball weight under an affine rescaling of the moment curve

BDG's parabolic-rescaling lemma (`ne31`, §7) decouples an interval
`I = [t₀, t₀+σ]` by rescaling `t = t₀ + σs`.  In the rescaled variable the
frequency vector is transformed by

    `A = affVec k σ t₀ = D_σ ∘ affVec k 1 t₀`,   `(D_σ y)_l = σ^{l+1} y_l`,

and the **ball weight pushes forward to the anisotropic weight**

    `pushWeight k σ t₀ c R y := ballWeight k c R (A⁻¹ y)`
      `= (1 + ‖A⁻¹(y − A c)‖/R)^{−100k}`,   `A⁻¹ = affVec k σ⁻¹ (−t₀/σ)`.

The singular values of `A` are `≍ σ, σ², …, σᵏ`, so `A⁻¹` distorts distances
by at most `≍ σ^{-k}`; consequently `pushWeight` is *essentially constant* on
balls of radius `R₀ := σᵏ R` (`pushWeight_local_const`).  In BDG's numerology
(`δ = 1/N`, `σ = δ^ρ`, `R = δ^{-n}` the scale of the rescaled problem is
`1/m` with `m = Nσ`, and `R₀ = σᵏR = mᵏ` is exactly the canonical radius of
that scale — so `pushWeight` only needs to be constant at the canonical scale,
which is what makes the parabolic rescaling lossless.

Contents (all proved, no sorries):

* `affVec_scale` — `affVec k ρ t₀ = D_ρ ∘ affVec k 1 t₀`;
* `norm_affVec_le` — `‖affVec k ρ t₀ x‖ ≤ C ρ ‖x‖` for `0 < ρ ≤ 1`, `|t₀| ≤ 1`
  (the upper bound on `A` used in the push-forward comparisons);
* **`affVec_inv`** — `affVec k σ⁻¹ (−t₀/σ) ∘ affVec k σ t₀ = id` (`σ > 0`),
  proved through the phase identities `momPhase_affine` (the adjoint of the
  substitution `s ↦ σs+t₀` is the inverse of the adjoint of `s ↦ s/σ − t₀/σ`)
  and `momPhase_injective`;
* `norm_affVec_inv_le`, `norm_affVec_inv_ge` — `‖A⁻¹ z‖ ≤ Cσ^{-k}‖z‖` and
  `‖A⁻¹ z‖ ≥ C⁻¹‖z‖` for `0 < σ ≤ 1`, `|t₀| ≤ 1`;
* `pushWeight` and **`pushWeight_local_const`** — the local constancy of the
  pushed weight at the canonical scale `σᵏR` (constant `(1+C₀)^{100k}`, with
  `C₀ = C₀(k)`), which is the geometric input of the "cover by `R₀`-balls"
  argument for BDG's `ne31`.

### Note (why not an isotropic comparison)

`pushWeight` is *not* comparable to a single isotropic ball weight with a
`σ`-independent constant: comparing it with `w_{B(c',σR)}` (the large radius)
and with `w_{B(c',σ^{k-1}R)}` (the small radius) costs a factor
`σ^{-100k(k-1)}` in one of the two directions.  The cover argument for `ne31`
therefore has to use the local constancy above (on balls of radius `σᵏR`, the
pushed weight is constant up to `C(k)`), together with Minkowski's inequality
in `ℓ^{p/2}` (`p ≥ 2`), which is what makes the passage from the ball weights
to the pushed weight lossless in `σ`.
-/

/-- `(D_ρ y)_l = ρ^{l+1} y_l`: the dilation part of `affVec k ρ t₀`. -/
def dilVec (k : ℕ) (ρ : ℝ) (y : E k) : E k :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun l : Fin k => ρ ^ (l.val + 1) * y l)

/-- Coordinates of `dilVec`. -/
lemma dilVec_apply (k : ℕ) (ρ : ℝ) (y : E k) (l : Fin k) :
    dilVec k ρ y l = ρ ^ (l.val + 1) * y l := rfl

/-- **The dilation decomposition of `affVec`**: `affVec k ρ t₀ = D_ρ ∘ affVec k 1 t₀`. -/
lemma affVec_scale (k : ℕ) (ρ t₀ : ℝ) (x : E k) :
    affVec k ρ t₀ x = dilVec k ρ (affVec k 1 t₀ x) := by
  ext l
  rw [dilVec_apply, affVec_apply, affVec_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `affVec k ρ t₀` is additive in its vector argument. -/
lemma affVec_sub_general (k : ℕ) (ρ t₀ : ℝ) (x c : E k) :
    affVec k ρ t₀ (x - c) = affVec k ρ t₀ x - affVec k ρ t₀ c := by
  ext l
  simp only [PiLp.sub_apply, affVec_apply, sub_mul]
  rw [Finset.sum_sub_distrib]

/-- Norm bound for the dilation: `‖D_ρ y‖ ≤ ρ‖y‖` for `0 ≤ ρ ≤ 1`. -/
lemma norm_dilVec_le (k : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (y : E k) :
    ‖dilVec k ρ y‖ ≤ ρ * ‖y‖ := by
  have h1 : ‖dilVec k ρ y‖ ^ 2 = ∑ l : Fin k, (ρ ^ (l.val + 1) * y l) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [dilVec_apply, Real.norm_eq_abs, sq_abs]
  have h2 : ‖y‖ ^ 2 = ∑ l : Fin k, (y l) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun l _ => by rw [Real.norm_eq_abs, sq_abs]
  have h3 : ∀ l : Fin k, (ρ ^ (l.val + 1) * y l) ^ 2 ≤ ρ ^ 2 * (y l) ^ 2 := by
    intro l
    have hpl : ρ ^ (l.val + 1) ≤ ρ := by
      cases l.val with
      | zero => simp
      | succ n => exact pow_le_of_le_one hρ0 hρ1 (by omega)
    have hpl0 : 0 ≤ ρ ^ (l.val + 1) := pow_nonneg hρ0 _
    calc (ρ ^ (l.val + 1) * y l) ^ 2 = (ρ ^ (l.val + 1)) ^ 2 * (y l) ^ 2 := by ring
      _ ≤ ρ ^ 2 * (y l) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact pow_le_pow_left₀ hpl0 hpl 2
  have hsq : ‖dilVec k ρ y‖ ^ 2 ≤ ρ ^ 2 * ‖y‖ ^ 2 := by
    rw [h1, h2, Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ => h3 l
  have hsqrt : √(ρ ^ 2 * ‖y‖ ^ 2) = ρ * ‖y‖ := by
    rw [Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ0, Real.sqrt_sq (norm_nonneg y)]
  calc ‖dilVec k ρ y‖ = √(‖dilVec k ρ y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(ρ ^ 2 * ‖y‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ρ * ‖y‖ := hsqrt

/-- **Norm form of the affine map**: there is `C > 0` (depending only on `k`)
with `‖affVec k ρ t₀ x‖ ≤ C ρ ‖x‖` for `0 < ρ ≤ 1`, `|t₀| ≤ 1`. -/
lemma norm_affVec_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (t₀ : ℝ), |t₀| ≤ 1 → ∀ x : E k,
      ‖affVec k ρ t₀ x‖ ≤ C * ρ * ‖x‖ := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := norm_affVec_one_le k
  refine ⟨C₀, hC₀pos, ?_⟩
  intro ρ hρ0 hρ1 t₀ ht x
  rw [affVec_scale]
  calc ‖dilVec k ρ (affVec k 1 t₀ x)‖ ≤ ρ * ‖affVec k 1 t₀ x‖ :=
        norm_dilVec_le k hρ0.le hρ1 _
    _ ≤ ρ * (C₀ * ‖x‖) := mul_le_mul_of_nonneg_left (hC₀ t₀ ht x) hρ0.le
    _ = C₀ * ρ * ‖x‖ := by ring

/-- **The inverse of the affine map** (BDG §7): for `σ > 0`,
`affVec k σ⁻¹ (−t₀/σ) ∘ affVec k σ t₀ = id`.  (The map `affVec k ρ t₀` is the
adjoint of the curve substitution `s ↦ ρs + t₀`; the adjoint of the inverse
substitution `s ↦ s/σ − t₀/σ` is therefore the inverse adjoint.) -/
lemma affVec_inv (k : ℕ) {σ : ℝ} (hσ : 0 < σ) (t₀ : ℝ) (x : E k) :
    affVec k (1 / σ) (-t₀ / σ) (affVec k σ t₀ x) = x := by
  refine momPhase_injective k _ _ fun u => ?_
  have h1 := momPhase_affine k (affVec k σ t₀ x) (1 / σ) (-t₀ / σ) u
  have h2 := momPhase_affine k x σ t₀ ((1 / σ) * u - t₀ / σ)
  have h3 := momPhase_affine k x σ t₀ (-t₀ / σ)
  have h2' : σ * ((1 / σ) * u - t₀ / σ) + t₀ = u := by field_simp; ring
  have h3' : σ * (-t₀ / σ) + t₀ = 0 := by field_simp; ring
  rw [h2'] at h2
  rw [h3'] at h3
  have h0 : momPhase k x 0 = 0 := by simp [momPhase]
  rw [h0] at h3
  have h1'' : momPhase k (affVec k σ t₀ x) ((1 / σ) * u - t₀ / σ)
      = momPhase k (affVec k σ t₀ x) (-t₀ / σ)
        + momPhase k (affVec k (1 / σ) (-t₀ / σ) (affVec k σ t₀ x)) u := by
    have h := h1
    rwa [show (1 / σ) * u + (-t₀ / σ) = (1 / σ) * u - t₀ / σ by ring] at h
  linarith

/-- The `ℓ¹` norm of the coordinates of a vector is dominated by
`√k` times its `ℓ²` norm. -/
lemma sum_abs_coord_le (k : ℕ) (z : E k) : ∑ j : Fin k, |z j| ≤ Real.sqrt k * ‖z‖ := by
  have h1 : (∑ j : Fin k, |z j|) ^ 2 ≤ (k : ℝ) * ∑ j : Fin k, |z j| ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : Fin k => |z j|))
  have h2 : ∑ j : Fin k, |z j| ^ 2 = ‖z‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun j _ => sq_abs (z j)
  have h3 : (0 : ℝ) ≤ ∑ j : Fin k, |z j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hs : (∑ j : Fin k, |z j|) ^ 2 ≤ (k : ℝ) * ‖z‖ ^ 2 := by
    rw [h2] at h1
    exact h1
  have h4 : (∑ j : Fin k, |z j|) ≤ Real.sqrt ((k : ℝ) * ‖z‖ ^ 2) := by
    calc (∑ j : Fin k, |z j|) = Real.sqrt ((∑ j : Fin k, |z j|) ^ 2) := (Real.sqrt_sq h3).symm
      _ ≤ Real.sqrt ((k : ℝ) * ‖z‖ ^ 2) := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq (norm_nonneg z)] at h4
  exact h4

/-- **Upper bound for the inverse map**: `σᵏ‖A⁻¹ z‖ ≤ C‖z‖` for `0 < σ ≤ 1`,
`|t₀| ≤ 1`, `C = 2ᵏ√k`.  (Direct coordinate estimate: the `(i,j)` entry of the
matrix of `affVec k σ⁻¹ (−t₀/σ)` is `C(j+1,i+1)(−t₀)^{j−i}σ^{-(j+1)}`, whose
absolute value is at most `C(j+1,i+1)σ^{-(j+1)} ≤ 2^{j+1}σ^{-(j+1)}`.) -/
lemma norm_affVec_inv_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), 0 < σ → σ ≤ 1 → ∀ (t₀ : ℝ), |t₀| ≤ 1 → ∀ z : E k,
      σ ^ k * ‖affVec k (1 / σ) (-t₀ / σ) z‖ ≤ C * ‖z‖ := by
  refine ⟨(k : ℝ) * (2 : ℝ) ^ k * Real.sqrt k + 1, by positivity, ?_⟩
  intro σ hσ0 hσ1 t₀ ht z
  set B : E k → E k := affVec k (1 / σ) (-t₀ / σ) with hB
  -- coordinate bound
  have hcoord : ∀ i : Fin k, |B z i|
      ≤ ∑ j : Fin k, |z j| * ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ) / σ ^ (j.val + 1) := by
    intro i
    have hBij : B z i = ∑ j : Fin k, z j * ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ)
        * (1 / σ) ^ (i.val + 1) * (-t₀ / σ) ^ (j.val - i.val) := rfl
    rw [hBij]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    by_cases hij : i.val ≤ j.val
    · have hC : (0 : ℝ) ≤ ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
      have h1 : |z j * ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ) * (1 / σ) ^ (i.val + 1)
          * (-t₀ / σ) ^ (j.val - i.val)|
          = |z j| * |((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ)| * |(1 / σ) ^ (i.val + 1)|
            * |(-t₀ / σ) ^ (j.val - i.val)| := by
        rw [abs_mul, abs_mul, abs_mul]
      rw [h1]
      have h2 : |((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ)|
          = ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ) := abs_of_nonneg hC
      have h3 : |(1 / σ) ^ (i.val + 1)| = (1 / σ) ^ (i.val + 1) :=
        abs_of_pos (pow_pos (by positivity) _)
      have h4 : |(-t₀ / σ) ^ (j.val - i.val)| = |t₀| ^ (j.val - i.val) / σ ^ (j.val - i.val) := by
        rw [abs_pow, abs_div, abs_neg, abs_of_pos hσ0, div_pow]
      rw [h2, h3, h4, one_div_pow]
      have ht0 : |t₀| ^ (j.val - i.val) ≤ 1 := pow_le_one₀ (abs_nonneg _) ht
      have hσ2 : 0 < σ ^ (j.val - i.val) := pow_pos hσ0 _
      have hprod : (1 / σ ^ (i.val + 1)) * (|t₀| ^ (j.val - i.val) / σ ^ (j.val - i.val))
          ≤ 1 / σ ^ (j.val + 1) := by
        have hexp : i.val + 1 + (j.val - i.val) = j.val + 1 := by omega
        have hb : (1 / σ ^ (i.val + 1)) * (1 / σ ^ (j.val - i.val)) = 1 / σ ^ (j.val + 1) := by
          rw [div_mul_div_comm, one_mul, ← pow_add, hexp]
        have ha : (1 / σ ^ (i.val + 1)) * (|t₀| ^ (j.val - i.val) / σ ^ (j.val - i.val))
            ≤ (1 / σ ^ (i.val + 1)) * (1 / σ ^ (j.val - i.val)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff_of_pos_right hσ2]
          exact ht0
        rwa [hb] at ha
      calc |z j| * ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ) * (1 / σ ^ (i.val + 1))
            * (|t₀| ^ (j.val - i.val) / σ ^ (j.val - i.val))
          = |z j| * ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ)
            * ((1 / σ ^ (i.val + 1)) * (|t₀| ^ (j.val - i.val) / σ ^ (j.val - i.val))) := by ring
        _ ≤ |z j| * ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ) * (1 / σ ^ (j.val + 1)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = |z j| * ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ) / σ ^ (j.val + 1) := by
            rw [mul_one_div]
    · rw [not_le] at hij
      have hzero : ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (by omega : j.val + 1 < i.val + 1)]
        norm_num
      rw [hzero]
      simp
  -- assemble
  have hnorm : ‖B z‖ ≤ ∑ i : Fin k, |B z i| :=
    Commons.Analysis.InnerProductSpace.norm_le_sum_abs_coord (B z)
  have hsum1 : ∑ i : Fin k, |B z i|
      ≤ ∑ i : Fin k, ∑ j : Fin k, |z j| * ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ)
          / σ ^ (j.val + 1) := Finset.sum_le_sum fun i _ => hcoord i
  have hswap : ∑ i : Fin k, ∑ j : Fin k, |z j| * ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ)
        / σ ^ (j.val + 1)
      = ∑ j : Fin k, (∑ i : Fin k, ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ))
          * (|z j| / σ ^ (j.val + 1)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hterm : ∀ i : Fin k, |z j| * ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ)
          / σ ^ (j.val + 1)
        = ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ) * (|z j| / σ ^ (j.val + 1)) :=
      fun i => by ring
    calc ∑ i : Fin k, |z j| * ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ) / σ ^ (j.val + 1)
        = ∑ i : Fin k, ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ)
            * (|z j| / σ ^ (j.val + 1)) := Finset.sum_congr rfl fun i _ => hterm i
      _ = (∑ i : Fin k, ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ))
            * (|z j| / σ ^ (j.val + 1)) := (Finset.sum_mul ..).symm
  have hchoose : ∀ j : Fin k, (∑ i : Fin k, ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ))
      ≤ (k : ℝ) * (2 : ℝ) ^ (j.val + 1) := by
    intro j
    calc ∑ i : Fin k, ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ)
        ≤ ∑ _i : Fin k, (2 : ℝ) ^ (j.val + 1) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hcl := Nat.choose_le_two_pow (j.val + 1) (i.val + 1)
          calc ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ) ≤ ((2 ^ (j.val + 1) : ℕ) : ℝ) := by
                exact_mod_cast hcl
            _ = (2 : ℝ) ^ (j.val + 1) := by push_cast; ring
      _ = (k : ℝ) * (2 : ℝ) ^ (j.val + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hstep2 : ∑ j : Fin k, σ ^ k * ((∑ i : Fin k, ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ))
        * (|z j| / σ ^ (j.val + 1))) ≤ ∑ j : Fin k, (k : ℝ) * (2 : ℝ) ^ k * |z j| := by
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : σ ^ k * ((∑ i : Fin k, ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ))
          * (|z j| / σ ^ (j.val + 1)))
        ≤ σ ^ k * (((k : ℝ) * (2 : ℝ) ^ (j.val + 1)) * (|z j| / σ ^ (j.val + 1))) := by
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hσ0.le _)
      exact mul_le_mul_of_nonneg_right (hchoose j) (by positivity)
    have h2 : σ ^ k * (((k : ℝ) * (2 : ℝ) ^ (j.val + 1)) * (|z j| / σ ^ (j.val + 1)))
        = (k : ℝ) * (2 : ℝ) ^ (j.val + 1) * |z j| * (σ ^ k / σ ^ (j.val + 1)) := by ring
    have h3 : σ ^ k / σ ^ (j.val + 1) = σ ^ (k - (j.val + 1)) :=
      (pow_sub₀ σ hσ0.ne' (by omega : j.val + 1 ≤ k)).symm
    have h4 : σ ^ (k - (j.val + 1)) ≤ 1 := pow_le_one₀ hσ0.le hσ1
    have h5 : (2 : ℝ) ^ (j.val + 1) ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc σ ^ k * ((∑ i : Fin k, ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ))
            * (|z j| / σ ^ (j.val + 1)))
        ≤ σ ^ k * (((k : ℝ) * (2 : ℝ) ^ (j.val + 1)) * (|z j| / σ ^ (j.val + 1))) := h1
      _ = (k : ℝ) * (2 : ℝ) ^ (j.val + 1) * |z j| * (σ ^ k / σ ^ (j.val + 1)) := h2
      _ = (k : ℝ) * (2 : ℝ) ^ (j.val + 1) * |z j| * σ ^ (k - (j.val + 1)) := by rw [h3]
      _ ≤ (k : ℝ) * (2 : ℝ) ^ (j.val + 1) * |z j| * 1 :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ (k : ℝ) * (2 : ℝ) ^ k * |z j| := by
          have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          have hz0 : (0 : ℝ) ≤ |z j| := abs_nonneg _
          calc (k : ℝ) * (2 : ℝ) ^ (j.val + 1) * |z j| * 1
              = (k : ℝ) * ((2 : ℝ) ^ (j.val + 1) * |z j|) := by ring
            _ ≤ (k : ℝ) * ((2 : ℝ) ^ k * |z j|) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h5 hz0) hk0
            _ = (k : ℝ) * (2 : ℝ) ^ k * |z j| := by ring
  calc σ ^ k * ‖B z‖
      ≤ σ ^ k * ∑ i : Fin k, |B z i| :=
        mul_le_mul_of_nonneg_left hnorm (pow_nonneg hσ0.le _)
    _ ≤ σ ^ k * ∑ i : Fin k, ∑ j : Fin k, |z j| * ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ)
          / σ ^ (j.val + 1) := mul_le_mul_of_nonneg_left hsum1 (pow_nonneg hσ0.le _)
    _ = ∑ j : Fin k, σ ^ k * ((∑ i : Fin k, ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ))
          * (|z j| / σ ^ (j.val + 1))) := by rw [hswap, Finset.mul_sum]
    _ ≤ ∑ j : Fin k, (k : ℝ) * (2 : ℝ) ^ k * |z j| := hstep2
    _ = ((k : ℝ) * (2 : ℝ) ^ k) * ∑ j : Fin k, |z j| := by
        rw [Finset.mul_sum]
    _ ≤ ((k : ℝ) * (2 : ℝ) ^ k) * (Real.sqrt k * ‖z‖) :=
        mul_le_mul_of_nonneg_left (sum_abs_coord_le k z) (by positivity)
    _ ≤ ((k : ℝ) * (2 : ℝ) ^ k * Real.sqrt k + 1) * ‖z‖ := by
        have h2k : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
        have hsk : (0 : ℝ) ≤ Real.sqrt k := Real.sqrt_nonneg _
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith [norm_nonneg z]

/-- **The dilation scales at least by `σᵏ`**: `σᵏ‖y‖ ≤ ‖D_σ y‖`. -/
lemma norm_dilVec_ge (k : ℕ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (y : E k) :
    σ ^ k * ‖y‖ ≤ ‖dilVec k σ y‖ := by
  have h1 : ‖dilVec k σ y‖ ^ 2 = ∑ l : Fin k, (σ ^ (l.val + 1) * y l) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [dilVec_apply, Real.norm_eq_abs, sq_abs]
  have h2 : ‖y‖ ^ 2 = ∑ l : Fin k, (y l) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun l _ => by rw [Real.norm_eq_abs, sq_abs]
  have h3 : (σ ^ k) ^ 2 * ‖y‖ ^ 2 ≤ ‖dilVec k σ y‖ ^ 2 := by
    rw [h1, h2, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    have h4 : σ ^ k ≤ σ ^ (l.val + 1) := pow_le_pow_of_le_one hσ0.le hσ1 (by omega)
    have h5 : (σ ^ k) ^ 2 * (y l) ^ 2 ≤ (σ ^ (l.val + 1)) ^ 2 * (y l) ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact pow_le_pow_left₀ (pow_nonneg hσ0.le _) h4 2
    calc (σ ^ k) ^ 2 * (y l) ^ 2 = ((σ ^ k) * (y l)) ^ 2 := by ring
      _ ≤ (σ ^ (l.val + 1) * y l) ^ 2 := by
          rw [mul_pow, mul_pow]
          exact h5
  have := Real.sqrt_le_sqrt h3
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hσ0.le _),
    Real.sqrt_sq (norm_nonneg y), Real.sqrt_sq (norm_nonneg _)] at this
  exact this

/-! ## The pushed-forward ball weight -/

/-- The **pushed-forward ball weight** under the affine rescaling `A = affVec k σ t₀`:
`pushWeight k σ t₀ c R y = ballWeight k c R (A⁻¹ y)` with the explicit
inverse `A⁻¹ = affVec k σ⁻¹ (−t₀/σ)` (`affVec_inv`). -/
def pushWeight (k : ℕ) (σ t₀ : ℝ) (c : E k) (R : ℝ) (y : E k) : ℝ :=
  ballWeight k c R (affVec k (1 / σ) (-t₀ / σ) y)

/-- The pushed-forward weight is positive. -/
lemma pushWeight_pos (k : ℕ) (σ t₀ : ℝ) (c : E k) {R : ℝ} (hR : 0 < R)
    (_σpos : 0 < σ) (y : E k) : 0 < pushWeight k σ t₀ c R y := by
  unfold pushWeight
  exact ballWeight_pos k c hR _

/-- `pushWeight` is the ball weight composed with the inverse affine map. -/
lemma pushWeight_apply (k : ℕ) (σ t₀ : ℝ) (c : E k) (R : ℝ) (y : E k) :
    pushWeight k σ t₀ c R y = ballWeight k c R (affVec k (1 / σ) (-t₀ / σ) y) := rfl

/-- **Local constancy of the pushed-forward weight at the canonical scale
`σᵏR`.**  Since `A⁻¹` distorts distances by at most `≍ σ^{-k}`, the pushed
weight is constant at scale `σᵏR` (and in BDG's numerology `σᵏR = mᵏ` is the
canonical radius of the rescaled problem). -/
lemma pushWeight_local_const (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (σ : ℝ), 0 < σ → σ ≤ 1 → ∀ (t₀ : ℝ), |t₀| ≤ 1 →
      ∀ (R : ℝ), 0 < R → ∀ (c y y₀ : E k), ‖y - y₀‖ ≤ σ ^ k * R →
        pushWeight k σ t₀ c R y ≤ C * pushWeight k σ t₀ c R y₀ := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := norm_affVec_inv_le k
  refine ⟨(1 + C₀) ^ (100 * k), one_le_pow₀ (by linarith), ?_⟩
  intro σ hσ0 hσ1 t₀ ht R hR c y y₀ hy
  have hC₀nn : (0 : ℝ) ≤ C₀ := hC₀pos.le
  -- `σ^{-k}σᵏ = 1`
  have hσkinv : σ ^ (-(k : ℝ)) * σ ^ k = 1 := by
    rw [← Real.rpow_natCast σ k, ← Real.rpow_add hσ0, neg_add_cancel, Real.rpow_zero]
  -- `‖A⁻¹(y−y₀)‖ ≤ C₀σ^{-k}‖y−y₀‖`
  have hBz : ‖affVec k (1 / σ) (-t₀ / σ) (y - y₀)‖ ≤ C₀ * σ ^ (-(k : ℝ)) * ‖y - y₀‖ := by
    have h := hC₀ σ hσ0 hσ1 t₀ ht (y - y₀)
    calc ‖affVec k (1 / σ) (-t₀ / σ) (y - y₀)‖
        = σ ^ (-(k : ℝ)) * (σ ^ k * ‖affVec k (1 / σ) (-t₀ / σ) (y - y₀)‖) := by
          rw [← mul_assoc]
          rw [hσkinv, one_mul]
      _ ≤ σ ^ (-(k : ℝ)) * (C₀ * ‖y - y₀‖) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hσ0.le _)
      _ = C₀ * σ ^ (-(k : ℝ)) * ‖y - y₀‖ := by ring
  have hBsub : ‖affVec k (1 / σ) (-t₀ / σ) y - affVec k (1 / σ) (-t₀ / σ) y₀‖
      ≤ C₀ * σ ^ (-(k : ℝ)) * ‖y - y₀‖ := by
    rw [← affVec_sub_general]
    exact hBz
  have hC₀R : C₀ * σ ^ (-(k : ℝ)) * ‖y - y₀‖ ≤ C₀ * R := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC₀nn
    calc σ ^ (-(k : ℝ)) * ‖y - y₀‖ ≤ σ ^ (-(k : ℝ)) * (σ ^ k * R) :=
          mul_le_mul_of_nonneg_left hy (Real.rpow_nonneg hσ0.le _)
      _ = (σ ^ (-(k : ℝ)) * σ ^ k) * R := by ring
      _ = R := by rw [hσkinv, one_mul]
  -- both arguments differ by at most `C₀R`
  have hkey : ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖
      ≤ ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ + C₀ * R := by
    have hsplit : affVec k (1 / σ) (-t₀ / σ) y₀ - c
        = (affVec k (1 / σ) (-t₀ / σ) y - c)
          + (affVec k (1 / σ) (-t₀ / σ) y₀ - affVec k (1 / σ) (-t₀ / σ) y) := by abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) (add_le_add le_rfl ?_)
    have hrev : ‖affVec k (1 / σ) (-t₀ / σ) y₀ - affVec k (1 / σ) (-t₀ / σ) y‖
        = ‖affVec k (1 / σ) (-t₀ / σ) y - affVec k (1 / σ) (-t₀ / σ) y₀‖ :=
      norm_sub_rev _ _
    rw [hrev]
    exact le_trans hBsub hC₀R
  -- the weight argument grows by at most the factor `(1+C₀)`
  have hle : 1 + ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖ / R
      ≤ (1 + C₀) * (1 + ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ / R) := by
    have h2 : ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖ / R
        ≤ ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ / R + C₀ := by
      calc ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖ / R
          ≤ (‖affVec k (1 / σ) (-t₀ / σ) y - c‖ + C₀ * R) / R :=
            div_le_div_of_nonneg_right hkey hR.le
        _ = ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ / R + C₀ := by field_simp
    nlinarith [norm_nonneg (affVec k (1 / σ) (-t₀ / σ) y - c), hC₀nn,
      div_nonneg (norm_nonneg (affVec k (1 / σ) (-t₀ / σ) y - c)) hR.le]
  -- conclude
  have hmain : (1 + ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖ / R) ^ (100 * k)
      ≤ (1 + C₀) ^ (100 * k) * (1 + ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ / R) ^ (100 * k) := by
    have h := pow_le_pow_left₀ (by positivity) hle (100 * k)
    rwa [mul_pow] at h
  unfold pushWeight ballWeight
  have hApos : (0 : ℝ) < (1 + ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ / R) ^ (100 * k) :=
    pow_pos (by positivity) _
  have hBpos : (0 : ℝ) < (1 + ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖ / R) ^ (100 * k) :=
    pow_pos (by positivity) _
  have h1 : (1 + ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖ / R) ^ (100 * k)
        / ((1 + ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ / R) ^ (100 * k)
          * (1 + ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖ / R) ^ (100 * k))
      ≤ (1 + C₀) ^ (100 * k) * (1 + ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ / R) ^ (100 * k)
        / ((1 + ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ / R) ^ (100 * k)
          * (1 + ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖ / R) ^ (100 * k)) :=
    div_le_div_of_nonneg_right hmain (by positivity)
  have h2 : (1 + ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖ / R) ^ (100 * k)
        / ((1 + ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ / R) ^ (100 * k)
          * (1 + ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖ / R) ^ (100 * k))
      = ((1 + ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ / R) ^ (100 * k))⁻¹ := by
    field_simp
  have h3 : (1 + C₀) ^ (100 * k) * (1 + ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ / R) ^ (100 * k)
        / ((1 + ‖affVec k (1 / σ) (-t₀ / σ) y - c‖ / R) ^ (100 * k)
          * (1 + ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖ / R) ^ (100 * k))
      = (1 + C₀) ^ (100 * k)
        * ((1 + ‖affVec k (1 / σ) (-t₀ / σ) y₀ - c‖ / R) ^ (100 * k))⁻¹ := by
    field_simp
  rwa [h2, h3] at h1

end Submission.Vinogradov
