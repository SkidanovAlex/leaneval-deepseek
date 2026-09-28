import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.evaldefs

namespace Work.HP.HP2

open Finset

/-!
# Sharp per-monomial Lipschitz bound

`Work.HP.HP2.veronese_lip_sharp`: a degree-`d` monomial in `n+1` variables is Lipschitz on the
Euclidean ball of radius `R ≥ 1` with constant `d * R^(d-1)` (one power of `R` better than the
trivial bound `d * R^d` of `Work.HP.HP2.mon_lip`).

The proof is an induction on the (finite) set of variables, in the sharp form

`|∏_{i∈s} xᵢ^{μᵢ} − ∏_{i∈s} yᵢ^{μᵢ}| ≤ (Σ_{i∈s} μᵢ) · R^{(Σ_{i∈s} μᵢ)−1} · Σ_{i∈s}|xᵢ − yᵢ|`.

Inserting a variable `k` splits the difference as
`x_k^{μ_k}·(A − B) + (x_k^{μ_k} − y_k^{μ_k})·B`, and the two summands cost
`R^{μ_k}·K·R^{K−1}·T` and `μ_k·R^{μ_k−1}·δ·R^K`; the total exponent of `R` is `μ_k + K − 1 = d − 1`.
The (only) delicate point is the arithmetic of `Nat`-truncated exponents when `K = 0` or `μ_k = 0`;
in both cases the offending term carries a zero factor, so the inequality survives.
-/

/-- The absolute value of a product of powers is bounded by `R` raised to the total degree. -/
lemma abs_prod_pow_le_s {ι : Type*} (s : Finset ι) (x : ι → ℝ) (μ : ι → ℕ) (R : ℝ)
    (hx : ∀ i ∈ s, |x i| ≤ R) : |∏ i ∈ s, x i ^ (μ i)| ≤ R ^ (∑ i ∈ s, μ i) := by
  rw [Finset.abs_prod]
  calc ∏ i ∈ s, |x i ^ (μ i)| ≤ ∏ i ∈ s, R ^ (μ i) := by
        refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i hi => ?_)
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx i hi) _
    _ = R ^ (∑ i ∈ s, μ i) := Finset.prod_pow_eq_pow_sum s μ R

/-- The arithmetic core of the induction step: replacing the two `Nat`-truncated exponents
`K - 1` and `μ - 1` by the common exponent `μ + K - 1` is legitimate, because the `K = 0` and
`μ = 0` cases come with a zero factor. -/
lemma step_bound {m K : ℕ} {R T δ : ℝ} (hR : 1 ≤ R) (hT : 0 ≤ T) (hδ : 0 ≤ δ) :
    R ^ m * ((K : ℝ) * R ^ (K - 1) * T) + ((m : ℝ) * R ^ (m - 1) * δ) * R ^ K
      ≤ ((m + K : ℕ) : ℝ) * R ^ (m + K - 1) * (δ + T) := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have h1 : R ^ m * ((K : ℝ) * R ^ (K - 1) * T) ≤ (K : ℝ) * R ^ (m + K - 1) * T := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp
    · have hm : m + (K - 1) = m + K - 1 := by omega
      calc R ^ m * ((K : ℝ) * R ^ (K - 1) * T)
          = (K : ℝ) * (R ^ m * R ^ (K - 1)) * T := by ring
        _ = (K : ℝ) * R ^ (m + (K - 1)) * T := by rw [pow_add]
        _ ≤ (K : ℝ) * R ^ (m + K - 1) * T := le_of_eq (by rw [hm])
  have h2 : ((m : ℝ) * R ^ (m - 1) * δ) * R ^ K ≤ (m : ℝ) * R ^ (m + K - 1) * δ := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have hk : (m - 1) + K = m + K - 1 := by omega
      calc ((m : ℝ) * R ^ (m - 1) * δ) * R ^ K
          = (m : ℝ) * (R ^ (m - 1) * R ^ K) * δ := by ring
        _ = (m : ℝ) * R ^ ((m - 1) + K) * δ := by rw [pow_add]
        _ ≤ (m : ℝ) * R ^ (m + K - 1) * δ := le_of_eq (by rw [hk])
  have h3 : (K : ℝ) * R ^ (m + K - 1) * T + (m : ℝ) * R ^ (m + K - 1) * δ
      ≤ ((m + K : ℕ) : ℝ) * R ^ (m + K - 1) * (δ + T) := by
    have hcast : ((m + K : ℕ) : ℝ) = (m : ℝ) + (K : ℝ) := by push_cast; ring
    rw [hcast]
    have hRk : 0 ≤ R ^ (m + K - 1) := pow_nonneg hR0 _
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    nlinarith [hRk, hT, hδ, hm0, hK0, mul_nonneg hRk hT, mul_nonneg hRk hδ,
      mul_nonneg hm0 hT, mul_nonneg hK0 hδ]
  linarith [h1, h2, h3]

/-- **Sharp Lipschitz bound for a monomial over an arbitrary finite set of variables.** -/
lemma lip_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (μ : ι → ℕ) (x y : ι → ℝ)
    (R : ℝ) (hR : 1 ≤ R) (hx : ∀ i ∈ s, |x i| ≤ R) (hy : ∀ i ∈ s, |y i| ≤ R) :
    |∏ i ∈ s, x i ^ (μ i) - ∏ i ∈ s, y i ^ (μ i)| ≤
      ((∑ i ∈ s, μ i : ℕ) : ℝ) * R ^ ((∑ i ∈ s, μ i) - 1) * (∑ i ∈ s, |x i - y i|) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert k s' hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.sum_insert hk, Finset.sum_insert hk]
    have hx' : ∀ i ∈ s', |x i| ≤ R := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hy' : ∀ i ∈ s', |y i| ≤ R := fun i hi => hy i (Finset.mem_insert_of_mem hi)
    have hxk : |x k| ≤ R := hx k (Finset.mem_insert_self k s')
    have hyk : |y k| ≤ R := hy k (Finset.mem_insert_self k s')
    have hR0 : 0 ≤ R := le_trans zero_le_one hR
    have hIH : |∏ i ∈ s', x i ^ (μ i) - ∏ i ∈ s', y i ^ (μ i)|
        ≤ ((∑ i ∈ s', μ i : ℕ) : ℝ) * R ^ ((∑ i ∈ s', μ i) - 1) * (∑ i ∈ s', |x i - y i|) :=
      ih hx' hy'
    have hPy : |∏ i ∈ s', y i ^ (μ i)| ≤ R ^ (∑ i ∈ s', μ i) := abs_prod_pow_le_s s' y μ R hy'
    have hxkm : |x k ^ (μ k)| ≤ R ^ (μ k) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hxk _
    have hδ : |x k ^ (μ k) - y k ^ (μ k)|
        ≤ (μ k : ℝ) * R ^ (μ k - 1) * |x k - y k| := by
      calc |x k ^ (μ k) - y k ^ (μ k)|
          ≤ |x k - y k| * (μ k : ℝ) * max |x k| |y k| ^ (μ k - 1) :=
            _root_.abs_pow_sub_pow_le _ _ _
        _ ≤ |x k - y k| * (μ k : ℝ) * R ^ (μ k - 1) := by
            gcongr
            exact max_le hxk hyk
        _ = (μ k : ℝ) * R ^ (μ k - 1) * |x k - y k| := by ring
    have hT0 : 0 ≤ ∑ i ∈ s', |x i - y i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hD0 : 0 ≤ |x k - y k| := abs_nonneg _
    have hsplit : |x k ^ (μ k) * (∏ i ∈ s', x i ^ (μ i)) - y k ^ (μ k) * (∏ i ∈ s', y i ^ (μ i))|
        ≤ |x k ^ (μ k)| * |(∏ i ∈ s', x i ^ (μ i)) - (∏ i ∈ s', y i ^ (μ i))|
          + |x k ^ (μ k) - y k ^ (μ k)| * |∏ i ∈ s', y i ^ (μ i)| := by
      calc |x k ^ (μ k) * (∏ i ∈ s', x i ^ (μ i)) - y k ^ (μ k) * (∏ i ∈ s', y i ^ (μ i))|
          = |x k ^ (μ k) * ((∏ i ∈ s', x i ^ (μ i)) - (∏ i ∈ s', y i ^ (μ i)))
              + (x k ^ (μ k) - y k ^ (μ k)) * (∏ i ∈ s', y i ^ (μ i))| := by ring_nf
        _ ≤ |x k ^ (μ k) * ((∏ i ∈ s', x i ^ (μ i)) - (∏ i ∈ s', y i ^ (μ i)))|
              + |(x k ^ (μ k) - y k ^ (μ k)) * (∏ i ∈ s', y i ^ (μ i))| := abs_add_le _ _
        _ = |x k ^ (μ k)| * |(∏ i ∈ s', x i ^ (μ i)) - (∏ i ∈ s', y i ^ (μ i))|
              + |x k ^ (μ k) - y k ^ (μ k)| * |∏ i ∈ s', y i ^ (μ i)| := by rw [abs_mul, abs_mul]
    have hterm1 : |x k ^ (μ k)| * |(∏ i ∈ s', x i ^ (μ i)) - (∏ i ∈ s', y i ^ (μ i))|
        ≤ R ^ (μ k) * (((∑ i ∈ s', μ i : ℕ) : ℝ) * R ^ ((∑ i ∈ s', μ i) - 1)
            * (∑ i ∈ s', |x i - y i|)) :=
      mul_le_mul hxkm hIH (abs_nonneg _) (pow_nonneg hR0 _)
    have hterm2 : |x k ^ (μ k) - y k ^ (μ k)| * |∏ i ∈ s', y i ^ (μ i)|
        ≤ ((μ k : ℝ) * R ^ (μ k - 1) * |x k - y k|) * R ^ (∑ i ∈ s', μ i) :=
      mul_le_mul hδ hPy (abs_nonneg _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hR0 _)) (abs_nonneg _))
    exact (hsplit.trans (add_le_add hterm1 hterm2)).trans (step_bound hR hT0 hD0)

/-- **Sharp per-monomial Lipschitz bound.**  For `rNorm x ≤ R`, `rNorm y ≤ R` (`1 ≤ R`) and an
exponent vector `μ` of total degree `d`, the monomial `veronese d n x μ` (`= ∏ i, x i ^ (μ.1 i)`)
differs from `veronese d n y μ` by at most `d · R^{d-1} · Σᵢ|xᵢ − yᵢ|`.

The exponent `d − 1` (NOT `d`) is the sharp homogeneous bound, and it is what makes
`|Q(x)² − Q(y)²| ≤ 2·N_{d,n}·d·‖a‖²·R^{2d-1}·Σᵢ|xᵢ−yᵢ|` possible for a degree-`d` form `Q`
(`Work.HP.HP2.mon_lip` gives only `d · R^d · Σᵢ|xᵢ−yᵢ|`, one power of `R` too many).

Route (telescoping with a moving intermediate product): write
`∏ᵢ yᵢ^{μᵢ} − ∏ᵢ xᵢ^{μᵢ} = Σᵢ (∏_{j<i} xⱼ^{μⱼ}) · (yᵢ^{μᵢ} − xᵢ^{μᵢ}) · (∏_{j>i} yⱼ^{μⱼ})`
(for the coordinate `j ∉ s`, the product over the remaining coordinates; any linear order on the
index set works), bound each factor by `R` raised to its total exponent and use the one-variable
bound `abs_pow_sub_pow_le : |a^m − b^m| ≤ |a − b| * m * max |a| |b| ^ (m - 1)` (Mathlib) to get
`|yᵢ^{μᵢ} − xᵢ^{μᵢ}| ≤ μᵢ · R^{μᵢ−1} · |xᵢ − yᵢ|`; the total exponent of `R` in each summand is
then `(d − μᵢ) + (μᵢ − 1) = d − 1`.  Equivalently, induce directly on the finset of coordinates
keeping the hypothesis in the sharp form
`|∏_{i∈s} xᵢ^{μᵢ} − ∏_{i∈s} yᵢ^{μᵢ}| ≤ (Σ_{i∈s} μᵢ) · R^{(Σ_{i∈s} μᵢ) − 1} · Σ_{i∈s}|xᵢ − yᵢ|`
(case split on whether `Σ_{i∈s} μᵢ = 0`; then both products are `1`).

Available facts: `abs_coord_le_rNorm : |x i| ≤ rNorm x` (`Submission/Work/HP/evaldefs.lean`),
`μ.2 : ∑ i, (μ.1 i : ℕ) = d`, and `veronese d n x μ` is definitionally `∏ i, x i ^ (μ.1 i : ℕ)`. -/
theorem veronese_lip_sharp (d n : ℕ) (μ : Mon d n) {R : ℝ} (hR : 1 ≤ R)
    {x y : Fin (n + 1) → ℝ} (hx : rNorm x ≤ R) (hy : rNorm y ≤ R) :
    |veronese d n x μ - veronese d n y μ| ≤ (d : ℝ) * R ^ (d - 1) * (∑ i, |x i - y i|) := by
  have h := lip_finset (Finset.univ : Finset (Fin (n + 1))) (fun i => (μ.1 i : ℕ)) x y R hR
    (fun i _ => le_trans (abs_coord_le_rNorm x i) hx)
    (fun i _ => le_trans (abs_coord_le_rNorm y i) hy)
  simpa [veronese, μ.2] using h

end Work.HP.HP2
