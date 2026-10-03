import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.ArcNumOrth
import Submission.Work.BourgainPlan.IonescuWainger.ZModArcs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The character sum over the torsion subgroup `Σ_{⊆ A}`

Tao's `Σ_{⊆ A} = 𝕋[Q_A]` is the `Q_A`-torsion subgroup of the circle (here realised, for
`sigmaSubAFinset A`, as the `Finset` of the points `a/Q_A`, `a = 0, …, Q_A - 1`).  The `m`-th
Fourier monomial `fourier m β = e(m β)` is a character of the circle, and summing it over the
torsion subgroup is a geometric series:

  `∑_{β ∈ Σ_{⊆ A}} conj (e(m β)) = Q_A` if `Q_A ∣ m`, and `0` otherwise.

This is the "denominator orthogonality" identity used to read off that the `Σ_{⊆ A}`-projection is
the periodisation-counting symbol at scale `Q_A` (Tao, arXiv:2008.05066, §4, Lemma `ortho`(ii)).

The proof reduces the `Finset` sum to the range sum `∑_{a < Q_A} z^a` with `z = fourier (-m) (1/Q_A)`,
which is a constant amount (`Q_A`) exactly when `z = 1`, i.e. when `Q_A ∣ m`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## Elementary properties of the Fourier monomials on the circle -/

/-- The monomials `fourier n` are additive in the point of the circle:
`fourier n (x + y) = fourier n x * fourier n y`. -/
private lemma fourier_add_arg {T : ℝ} (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

/-- `fourier n (a • x) = (fourier n x) ^ a`. -/
private lemma fourier_nsmul {T : ℝ} (n : ℤ) (x : AddCircle T) (a : ℕ) :
    fourier n (a • x) = (fourier n x) ^ a := by
  induction a with
  | zero => rw [zero_nsmul, fourier_eval_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, fourier_add_arg, ih, pow_succ]

/-- Complex conjugation of the monomial `fourier n` is `fourier (-n)`. -/
private lemma star_fourier {T : ℝ} (n : ℤ) (x : AddCircle T) :
    star (fourier n x) = fourier (-n) x := by
  rw [Complex.star_def]
  exact (fourier_neg (T := T) (n := n) (x := x)).symm

/-- `fourier n x = 1` exactly when `n • x = 0` on the circle. -/
private lemma fourier_eq_one_iff {T : ℝ} (hT : T ≠ 0) {n : ℤ} {x : AddCircle T} :
    fourier n x = 1 ↔ n • x = 0 := by
  rw [fourier_apply]
  constructor
  · intro h
    have h2 : (n • x).toCircle = (0 : AddCircle T).toCircle := by
      rw [Circle.coe_eq_one.mp h, AddCircle.toCircle_zero]
    exact AddCircle.injective_toCircle hT h2
  · intro h
    rw [h, AddCircle.toCircle_zero, Circle.coe_one]

/-! ## The arc points `a/Q` -/

/-- `arcPt Q a = a • arcPt Q 1` for natural `a`. -/
private lemma arcPt_nsmul (Q : ℕ) (a : ℕ) : arcPt Q (a : ℤ) = a • arcPt Q 1 := by
  rw [← natCast_zsmul (arcPt Q 1) a, zsmul_arcPt' (a : ℤ) Q 1, mul_one]

/-- The numerators `a ∈ [0, Q)` give pairwise distinct points `a/Q` of the circle. -/
private lemma arcPt_injOn_range {Q : ℕ} (hQ : Q ≠ 0) :
    Set.InjOn (fun a : ℕ => arcPt Q (a : ℤ)) ↑(Finset.range Q) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_range] at ha hb
  have hdvd : (Q : ℤ) ∣ ((a : ℤ) - (b : ℤ)) := (arcPt_eq_arcPt_iff_dvd hQ a b).mp hab
  have hlt : |((a : ℤ) - (b : ℤ))| < (Q : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have h0 : (a : ℤ) - (b : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  have hab' : (a : ℤ) = (b : ℤ) := by omega
  omega

/-- **The character sum over the torsion subgroup `Σ_{⊆ A} = 𝕋[Q_A]`.**  Summing the `m`-th
exponential over the `Finset` of the `Q_A`-torsion points of the circle gives `Q_A` when `Q_A ∣ m`
and `0` otherwise. -/
theorem charSum_sigmaSubAFinset (A : Finset ℕ) (m : ℤ) :
    ∑ β ∈ sigmaSubAFinset A, star (fourier m β)
      = if (QA A : ℤ) ∣ m then (QA A : ℂ) else 0 := by
  classical
  rcases eq_or_ne (QA A) 0 with hQ0 | hQ0
  · unfold sigmaSubAFinset
    rw [hQ0, Finset.range_zero, Finset.image_empty, Finset.sum_empty]
    split <;> simp
  · -- reduce the `Finset` sum to the sum over the numerators `a < Q_A`
    have hsum1 : ∑ β ∈ sigmaSubAFinset A, star (fourier m β)
        = ∑ a ∈ Finset.range (QA A), star (fourier m (arcPt (QA A) (a : ℤ))) := by
      unfold sigmaSubAFinset
      exact Finset.sum_image (arcPt_injOn_range hQ0)
    rw [hsum1]
    -- each summand is the `a`-th power of the single character `z = conj (e(m/Q_A))`
    set z : ℂ := fourier (-m) (arcPt (QA A) 1) with hz
    have hterm : ∀ a ∈ Finset.range (QA A),
        star (fourier m (arcPt (QA A) (a : ℤ))) = z ^ a := by
      intro a _
      rw [star_fourier, arcPt_nsmul, fourier_nsmul, ← hz]
    rw [Finset.sum_congr rfl hterm]
    -- `z` is a `Q_A`-th root of unity, since `Q_A · (1/Q_A) = 0`
    have hzQ : z ^ (QA A) = 1 := by
      have h1 : z ^ (QA A) = fourier (-m) (arcPt (QA A) ((QA A : ℕ) : ℤ)) := by
        rw [hz, arcPt_nsmul, fourier_nsmul]
      rw [h1, (arcPt_eq_zero_iff_dvd hQ0 ((QA A : ℕ) : ℤ)).mpr (dvd_refl _),
        fourier_eval_zero]
    -- hence the geometric series
    have hgeo : ∑ a ∈ Finset.range (QA A), z ^ a = if z = 1 then (QA A : ℂ) else 0 := by
      rcases eq_or_ne z 1 with hz1 | hz1
      · rw [if_pos hz1, hz1]; simp
      · rw [if_neg hz1]
        have hm := geom_sum_mul z (QA A)
        rw [hzQ, sub_self] at hm
        rcases mul_eq_zero.mp hm with h | h
        · exact h
        · exact absurd h (sub_ne_zero.mpr hz1)
    -- and `z = 1` exactly when `Q_A ∣ m`
    have hzcond : z = 1 ↔ (QA A : ℤ) ∣ m := by
      rw [hz, fourier_eq_one_iff (T := (1 : ℝ)) one_ne_zero, neg_zsmul, neg_eq_zero,
        zsmul_arcPt', mul_one]
      exact arcPt_eq_zero_iff_dvd hQ0 m
    rw [hgeo]
    by_cases h : (QA A : ℤ) ∣ m
    · rw [if_pos (hzcond.mpr h), if_pos h]
    · rw [if_neg (fun hz1 => h (hzcond.mp hz1)), if_neg h]

end Work.BourgainPlan.IonescuWainger
