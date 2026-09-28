import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.WedgeDefs

/-!
# The covolume of a pair after subtracting a multiple of the first vector

`WedgeDefs.wedgeR a b = √(‖a‖²‖b‖² - ⟨a,b⟩²)` is the covolume of a pair of real vectors,
and `Defs.wedgeNorm` is its integral companion.  The main lemma below is the elementary
"shear" computation: if `u ⊥ a` and `b = u - s·a`, then the covolume of the pair `(a, b)` is
the product `‖a‖·‖u‖` (a shear by a multiple of `a` does not change it).

The analytic input is the 2×2 Gram determinant identity
`‖a‖²‖u - s a‖² - ⟨a, u - s a⟩² = (‖a‖‖u‖)²`,
which follows from `⟨a,u⟩ = 0`, `⟨a, u - s a⟩ = -s‖a‖²` and `‖u - s a‖² = ‖u‖² + s²‖a‖²`;
since `‖a‖‖u‖ ≥ 0`, taking square roots gives the covolume `‖a‖‖u‖`.

Everything here is proved from the definitions in `Defs`/`WedgeDefs` and Mathlib only, so
that the file does not depend on the (frequently edited) shared Euclidean-norm API in
`Submission/Work/HP/tau_basic.lean`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.HP3

/-- `rNorm v ^ 2 = ∑ i, (v i) ^ 2` (local copy, to avoid depending on `tau_basic`). -/
lemma rNorm_sq_aux {ι : Type*} [Fintype ι] (v : ι → ℝ) : rNorm v ^ 2 = ∑ i, (v i) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))

/-- `0 ≤ rNorm v` (local copy, to avoid depending on `tau_basic`). -/
lemma rNorm_nonneg_aux {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ rNorm v :=
  Real.sqrt_nonneg _

/-- The Gram determinant identity for an orthogonal pair: if `u ⊥ a` and `s` is real, then the
squared covolume of the pair `(a, u - s • a)` is `(‖a‖‖u‖)²`. -/
lemma gram_det_orth_sub {ι : Type*} [Fintype ι] (a u : ι → ℝ) (s : ℝ) (h : dotR u a = 0) :
    rNorm a ^ 2 * rNorm (u - s • a) ^ 2 - (dotR a (u - s • a)) ^ 2
      = (rNorm a * rNorm u) ^ 2 := by
  have hsum0 : ∑ i, u i * a i = 0 := h
  -- the off-diagonal Gram entry
  have hAsum : ∑ i, a i * (u i - s * a i) = ∑ i, (a i * u i - s * a i ^ 2) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  have hswap : ∑ i, a i * u i = ∑ i, u i * a i :=
    Finset.sum_congr rfl (fun i _ => by ring)
  have hda : dotR a (u - s • a) = -s * rNorm a ^ 2 := by
    have hdot : dotR a (u - s • a) = ∑ i, a i * (u i - s * a i) := rfl
    rw [hdot, hAsum, Finset.sum_sub_distrib, hswap, hsum0, ← Finset.mul_sum, rNorm_sq_aux]
    ring
  -- the diagonal Gram entry
  have hBsum : ∑ i, ((u - s • a) i) ^ 2
      = ∑ i, ((u i) ^ 2 - 2 * s * (u i * a i) + s ^ 2 * (a i) ^ 2) :=
    Finset.sum_congr rfl (fun i _ => by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring)
  have hkey : ∑ i, ((u - s • a) i) ^ 2
      = ∑ i, (u i) ^ 2 - 2 * s * (∑ i, u i * a i) + s ^ 2 * ∑ i, (a i) ^ 2 := by
    rw [hBsum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
  have hnorm : rNorm (u - s • a) ^ 2 = rNorm u ^ 2 + s ^ 2 * rNorm a ^ 2 := by
    rw [rNorm_sq_aux, rNorm_sq_aux, rNorm_sq_aux, hkey, hsum0]
    ring
  rw [hda, hnorm]
  ring

/-- The covolume `wedgeR` of the pair `(a, u - s • a)` equals `‖a‖‖u‖` whenever `u ⊥ a`. -/
lemma wedgeR_sub_smul_eq {ι : Type*} [Fintype ι] (a u : ι → ℝ) (s : ℝ)
    (h : dotR u a = 0) : wedgeR a (u - s • a) = rNorm a * rNorm u := by
  rw [wedgeR, gram_det_orth_sub a u s h,
    Real.sqrt_sq (mul_nonneg (rNorm_nonneg_aux a) (rNorm_nonneg_aux u))]

/-- If the real vector `toR w` differs from `u` by a multiple of `toR x` (`toR w = u - s • toR x`)
and `u ⊥ x` (`dotR u (toR x) = 0`), then the covolume `wedgeNorm x w = √(‖x‖²‖w‖² - ⟨x,w⟩²)`
equals `eNorm x * rNorm u`.

Indeed `eNorm w ^ 2 = rNorm u ^ 2 + s^2 * eNorm x ^ 2` and
`dotR (toR x) (toR w) = -s * eNorm x ^ 2`, so the expression under the square root is
`eNorm x ^ 2 * rNorm u ^ 2`. -/
theorem wedgeNorm_eq_of_sub {ι : Type*} [Fintype ι] (x w : ι → ℤ) (u : ι → ℝ) (s : ℝ)
    (hwx : toR w = u - s • toR x) (horth : dotR u (toR x) = 0) :
    wedgeNorm x w = eNorm x * rNorm u := by
  rw [wedgeNorm_eq_wedgeR, hwx, eNorm_eq_rNorm_toR_W]
  exact wedgeR_sub_smul_eq (toR x) u s horth

end Work.HP.HP3
