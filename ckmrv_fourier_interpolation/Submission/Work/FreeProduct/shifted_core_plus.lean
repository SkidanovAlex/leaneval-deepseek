import Mathlib
import Submission.Work.FreeProduct.shiftedDefs
import Submission.Work.FreeProduct.IdealImDirect
import Submission.Work.FreeProduct.IdealIpDirect
import Submission.Work.FreeProduct.shifted_orbit_corollary

/-!
# The shifted core `(T - ν) u ∈ (Y² - νY + ν²)(X + 1)·RR  ⟹  (T - ν) u = 0`

This file proves `Work.FreeProduct.shifted_core_plus`, the shifted analogue (parameter `ν`)
of the "core" of CKMRV's directness statement for `𝓘₊` (Proposition 3.1 in the paper, proved
in `Work.FreeProduct.IdealIpDirect` as `(T - 1)² u = (X + 1) w → u = 0`).

Concretely, with `Tnu ν = T - ν` and `MUpv ν = Y² - νY + ν²`, we show that

  `(T - ν) u = (Y² - νY + ν²)(X + 1) r  →  (T - ν) u = 0`

whenever `ν ≠ 0` and `1 + ν³ ≠ 0`.

The strategy is exactly the one of `IdealIpDirect`, with `q = (Y² - Y + 1)(X + 1)` replaced by
`qν ν = (Y² - νY + ν²)(X + 1)` and the (unshifted) orbit corollary replaced by the shifted
orbit corollary `Work.FreeProduct.shifted_orbit_corollary`:

* the canonical form `exists_canon_MUp` writes `r = c·1 + Y r₁ + Y² r₂ + (X - 1) t`, and
  `qν ν (X - 1) = 0` kills the last term (since `(X + 1)(X - 1) = 0`);
* a maximal-length element `γ` of the support of `r₁` or `r₂` produces a coefficient of
  `(T - ν)u` at `y x y γ` (resp. `y x y² γ`) equal to `-ν·coeff rᵢ γ ≠ 0`, while all the
  nonzero `⟨T⟩`-translates of that point are strictly longer than the support of `(T - ν)u`;
* the shifted orbit corollary then contradicts `(T - ν)u = Tnu ν * u`.
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

namespace SpCore

/-- `qν ν = (Y² - νY + ν²)(X + 1)`, the shifted analogue of CKMRV's `q`. -/
def qν (ν : ℂ) : RR := MUpv ν * (X + 1)

lemma coeff_smul' (c : ℂ) (f : RR) (z : FP) :
    MonoidAlgebra.coeff (c • f) z = c * MonoidAlgebra.coeff f z := rfl

/-- The coefficient of a scalar multiple of a monomial `of g`. -/
lemma coeff_smul_of_mul (c : ℂ) (g : FP) (s : RR) (z : FP) :
    MonoidAlgebra.coeff ((c • MonoidAlgebra.of ℂ FP g) * s) z
      = c * MonoidAlgebra.coeff s (g⁻¹ * z) := by
  rw [smul_mul_assoc]
  show c * MonoidAlgebra.coeff (MonoidAlgebra.of ℂ FP g * s) z
      = c * MonoidAlgebra.coeff s (g⁻¹ * z)
  rw [IpDirect.coeff_of_mul_Ip]

/-- Expansion of `qν ν` into its six monomials. -/
lemma qν_expand (ν : ℂ) : qν ν =
    MonoidAlgebra.of ℂ FP (y2*x) - ν • MonoidAlgebra.of ℂ FP (y*x) + (ν^2) • MonoidAlgebra.of ℂ FP x
    + MonoidAlgebra.of ℂ FP y2 - ν • MonoidAlgebra.of ℂ FP y
    + (ν^2) • MonoidAlgebra.of ℂ FP (1:FP) := by
  rw [qν, MUpv, Y2, Y, X, show (1:RR) = MonoidAlgebra.of ℂ FP (1:FP) from (map_one _).symm]
  simp only [mul_add, add_mul, sub_mul, mul_sub, one_mul, mul_one,
    Algebra.mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, ← map_mul]
  module

/-- `qν` is supported on elements of length at most `2`. -/
lemma coeff_qν_of_three_le (ν : ℂ) {z : FP} (hz : 3 ≤ elen z) :
    MonoidAlgebra.coeff (qν ν) z = 0 := by
  have h0 : ∀ g : FP, elen g ≤ 2 → MonoidAlgebra.coeff (MonoidAlgebra.of ℂ FP g) z = 0 := by
    intro g hg
    refine IpDirect.coeff_of_eq_zero_of_ne (fun hcon => ?_)
    rw [← hcon] at hz; omega
  rw [qν_expand]
  simp only [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_add, Finsupp.sub_apply, Finsupp.add_apply,
    coeff_smul', h0 (y2*x) (by decide), h0 (y*x) (by decide), h0 x (by decide), h0 y2 (by decide),
    h0 y (by decide), h0 (1:FP) (by decide)]
  ring

/-- The coefficient of `qν ν` at `y * x` is `-ν`. -/
lemma coeff_qν_yx (ν : ℂ) : MonoidAlgebra.coeff (qν ν) (y * x) = -ν := by
  rw [qν_expand]
  simp only [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_add, Finsupp.sub_apply, Finsupp.add_apply,
    coeff_smul']
  rw [IpDirect.coeff_of_eq_zero_of_ne (g := y2*x) (by decide), IpDirect.coeff_of_self (y*x),
    IpDirect.coeff_of_eq_zero_of_ne (g := y2) (by decide),
    IpDirect.coeff_of_eq_zero_of_ne (g := y) (by decide),
    IpDirect.coeff_of_eq_zero_of_ne (g := x) (by decide),
    IpDirect.coeff_of_eq_zero_of_ne (g := (1:FP)) (by decide)]
  ring

/-- `qν ν · Y` expanded into monomials. -/
def qνY (ν : ℂ) : RR :=
  MonoidAlgebra.of ℂ FP (y2*x*y) - ν • MonoidAlgebra.of ℂ FP (y*x*y)
    + (ν^2) • MonoidAlgebra.of ℂ FP (x*y) + 1 - ν • MonoidAlgebra.of ℂ FP y2
    + (ν^2) • MonoidAlgebra.of ℂ FP y

lemma qν_mul_Y (ν : ℂ) : qν ν * Y = qνY ν := by
  rw [qν_expand, qνY, Y]
  simp only [sub_mul, add_mul, one_mul, smul_mul_assoc, Algebra.mul_smul_comm,
    ← map_mul, y2_mul_y, y_mul_y, map_one]

/-- `qν ν · Y²` expanded into monomials. -/
def qνY2 (ν : ℂ) : RR :=
  MonoidAlgebra.of ℂ FP (y2*x*y2) - ν • MonoidAlgebra.of ℂ FP (y*x*y2)
    + (ν^2) • MonoidAlgebra.of ℂ FP (x*y2) + MonoidAlgebra.of ℂ FP y - ν • 1
    + (ν^2) • MonoidAlgebra.of ℂ FP y2

lemma qν_mul_Y2 (ν : ℂ) : qν ν * Y2 = qνY2 ν := by
  rw [qν_expand, qνY2, Y2]
  simp only [sub_mul, add_mul, one_mul, smul_mul_assoc, Algebra.mul_smul_comm,
    ← map_mul, y2_mul_y2, y_mul_y2, map_one, smul_eq_mul, mul_one]

/-- Coefficients of `qνY ν * r` expanded into the six monomials of `qνY ν`. -/
lemma coeff_qνY_mul (ν : ℂ) (r : RR) (z : FP) :
    MonoidAlgebra.coeff (qνY ν * r) z
      = MonoidAlgebra.coeff r ((y2*x*y)⁻¹ * z) - ν * MonoidAlgebra.coeff r ((y*x*y)⁻¹ * z)
        + ν^2 * MonoidAlgebra.coeff r ((x*y)⁻¹ * z) + MonoidAlgebra.coeff r z
        - ν * MonoidAlgebra.coeff r (y2⁻¹ * z) + ν^2 * MonoidAlgebra.coeff r (y⁻¹ * z) := by
  rw [qνY]
  simp only [sub_mul, add_mul, one_mul, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply, coeff_smul_of_mul, IpDirect.coeff_of_mul_Ip]

/-- Coefficients of `qνY2 ν * r` expanded into the six monomials of `qνY2 ν`. -/
lemma coeff_qνY2_mul (ν : ℂ) (r : RR) (z : FP) :
    MonoidAlgebra.coeff (qνY2 ν * r) z
      = MonoidAlgebra.coeff r ((y2*x*y2)⁻¹ * z) - ν * MonoidAlgebra.coeff r ((y*x*y2)⁻¹ * z)
        + ν^2 * MonoidAlgebra.coeff r ((x*y2)⁻¹ * z) + MonoidAlgebra.coeff r (y⁻¹ * z)
        - ν * MonoidAlgebra.coeff r z + ν^2 * MonoidAlgebra.coeff r (y2⁻¹ * z) := by
  rw [qνY2]
  simp only [sub_mul, add_mul, one_mul, smul_mul_assoc, MonoidAlgebra.coeff_add,
    MonoidAlgebra.coeff_sub, Finsupp.add_apply, Finsupp.sub_apply, coeff_smul',
    coeff_smul_of_mul, IpDirect.coeff_of_mul_Ip]

/-- `qν ν * (c · 1) = c • qν ν`. -/
lemma qν_mul_single_one (ν : ℂ) (c : ℂ) :
    qν ν * MonoidAlgebra.single (1 : FP) c = c • qν ν := by
  have hs : (MonoidAlgebra.single (1 : FP) c : RR) = c • (1 : RR) := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [hs, mul_smul_comm, mul_one]

/-- The coefficient of `qν ν * (c·1 + Y·r₁ + Y²·r₂)` splits into its three parts. -/
lemma coeff_qν_mul_split (ν : ℂ) (c : ℂ) (r1 r2 : RR) (z : FP) :
    MonoidAlgebra.coeff (qν ν * (MonoidAlgebra.single (1 : FP) c + Y * r1 + Y2 * r2)) z
      = c * MonoidAlgebra.coeff (qν ν) z
        + MonoidAlgebra.coeff (qνY ν * r1) z + MonoidAlgebra.coeff (qνY2 ν * r2) z := by
  rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, qν_mul_single_one, qν_mul_Y, qν_mul_Y2]
  rw [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply,
    coeff_smul']


/-- `qν ν * (X - 1) = 0`. -/
lemma qν_mul_X_sub_one (ν : ℂ) : qν ν * (X - 1) = 0 := by
  rw [qν, mul_assoc, IpDirect.X_add_one_mul_X_sub_one, mul_zero]

/-- `c * coeff (qν ν) z = 0` for `elen z ≥ 3`. -/
lemma coeff_qν_mul_single_eq_zero (ν : ℂ) (c : ℂ) {z : FP} (hz : 3 ≤ elen z) :
    c * MonoidAlgebra.coeff (qν ν) z = 0 := by
  rw [coeff_qν_of_three_le ν hz, mul_zero]

theorem coeff_qνY_mul_eq_zero_of_long (ν : ℂ) {r : RR} {N : ℕ}
    (h : ∀ δ ∈ (MonoidAlgebra.coeff r).support, elen δ ≤ N) {z : FP} (hz : 3 + N < elen z) :
    MonoidAlgebra.coeff (qνY ν * r) z = 0 := by
  have h1 : elen (y2 * x * y : FP) ≤ 3 := by decide
  have h2 : elen (y * x * y : FP) ≤ 3 := by decide
  have h3 : elen (x * y : FP) ≤ 3 := by decide
  have h4 : elen (1 : FP) ≤ 3 := by decide
  have h5 : elen (y2 : FP) ≤ 3 := by decide
  have h6 : elen (y : FP) ≤ 3 := by decide
  have hL : ∀ g : FP, elen g ≤ 3 → MonoidAlgebra.coeff r (g⁻¹ * z) = 0 := fun g hg =>
    IpDirect.coeff_inv_mul_eq_zero_of_long h hg hz
  have h4' : MonoidAlgebra.coeff r z = 0 := by
    simpa using IpDirect.coeff_inv_mul_eq_zero_of_long h h4 hz
  rw [coeff_qνY_mul, hL _ h1, hL _ h2, hL _ h3, h4', hL _ h5, hL _ h6]
  ring

theorem coeff_qνY2_mul_eq_zero_of_long (ν : ℂ) {r : RR} {N : ℕ}
    (h : ∀ δ ∈ (MonoidAlgebra.coeff r).support, elen δ ≤ N) {z : FP} (hz : 3 + N < elen z) :
    MonoidAlgebra.coeff (qνY2 ν * r) z = 0 := by
  have h1 : elen (y2 * x * y2 : FP) ≤ 3 := by decide
  have h2 : elen (y * x * y2 : FP) ≤ 3 := by decide
  have h3 : elen (x * y2 : FP) ≤ 3 := by decide
  have h4 : elen (1 : FP) ≤ 3 := by decide
  have h5 : elen (y2 : FP) ≤ 3 := by decide
  have h6 : elen (y : FP) ≤ 3 := by decide
  have hL : ∀ g : FP, elen g ≤ 3 → MonoidAlgebra.coeff r (g⁻¹ * z) = 0 := fun g hg =>
    IpDirect.coeff_inv_mul_eq_zero_of_long h hg hz
  have h4' : MonoidAlgebra.coeff r z = 0 := by
    simpa using IpDirect.coeff_inv_mul_eq_zero_of_long h h4 hz
  rw [coeff_qνY2_mul, hL _ h1, hL _ h2, hL _ h3, hL _ h6, h4', hL _ h5]
  ring


/-- The core case: `(T - ν)u = c • qν ν` with `c ≠ 0` is impossible. -/
theorem core_contra {ν : ℂ} (hν : ν ≠ 0) {u : RR} {c : ℂ} (hc : c ≠ 0)
    (hv : Tnu ν * u = qν ν * MonoidAlgebra.single (1 : FP) c) : False := by
  have hlong : ∀ z : FP, 3 ≤ elen z → MonoidAlgebra.coeff (Tnu ν * u) z = 0 := by
    intro z hz
    rw [hv, qν_mul_single_one, coeff_smul', coeff_qν_of_three_le ν hz, mul_zero]
  have h0 : MonoidAlgebra.coeff (Tnu ν * u) (y * x) = -ν * c := by
    rw [hv, qν_mul_single_one, coeff_smul', coeff_qν_yx]
    ring
  refine shifted_orbit_corollary (u := u) (w := Tnu ν * u) (γ := y * x) (c := -ν * c)
    hν T_zpow_injective rfl h0 (mul_ne_zero (neg_ne_zero.mpr hν) hc) ?_
  intro n hn
  refine hlong _ ?_
  have hb := (IpDirect.elen_T_zpow_mul_ge IpDirect.XF_x_Ip hn).2.2
  omega

/-- Branch 2: the maximal-length element sits in the `Y²`-slot. -/
theorem branch2_contra {ν : ℂ} (hν : ν ≠ 0) {u : RR} {c : ℂ} {r1 r2 : RR} {γ : FP}
    (hγ : XF γ)
    (h1XF : ∀ δ ∈ (MonoidAlgebra.coeff r1).support, XF δ)
    (h1len : ∀ δ ∈ (MonoidAlgebra.coeff r1).support, elen δ ≤ elen γ)
    (h2XF : ∀ δ ∈ (MonoidAlgebra.coeff r2).support, XF δ)
    (h2len : ∀ δ ∈ (MonoidAlgebra.coeff r2).support, elen δ ≤ elen γ)
    (hγr2 : MonoidAlgebra.coeff r2 γ ≠ 0)
    (hv : Tnu ν * u = qν ν * (MonoidAlgebra.single (1 : FP) c + Y * r1 + Y2 * r2)) : False := by
  have hδlen : elen (y * x * y2 * γ) = elen γ + 3 := by
    rw [show y * x * y2 * γ = y * (x * y2 * γ) from by noncomm_ring,
      IpDirect.elen_y_mul_of_XF (IpDirect.XF_xy2_mul_of_XF hγ), IpDirect.elen_xy2_mul_of_XF hγ]
  have hlong : ∀ z : FP, 3 + elen γ < elen z →
      MonoidAlgebra.coeff (Tnu ν * u) z = 0 := by
    intro z hz
    rw [hv, coeff_qν_mul_split ν, coeff_qν_mul_single_eq_zero ν c (by omega),
      coeff_qνY_mul_eq_zero_of_long ν h1len (by omega),
      coeff_qνY2_mul_eq_zero_of_long ν h2len (by omega)]
    ring
  have hcoe : MonoidAlgebra.coeff (Tnu ν * u) (y * x * y2 * γ) = -ν * MonoidAlgebra.coeff r2 γ := by
    rw [hv, coeff_qν_mul_split ν, coeff_qν_mul_single_eq_zero ν c (by rw [hδlen]; omega)]
    have hA : MonoidAlgebra.coeff (qνY ν * r1) (y * x * y2 * γ) = 0 := by
      rw [coeff_qνY_mul]
      have b1 : MonoidAlgebra.coeff r1 ((y2*x*y)⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc,
          show (y2*x*y)⁻¹ * (y * x * y2) = toProd [Ly2,Lx,Ly2,Lx,Ly2] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b2 : MonoidAlgebra.coeff r1 ((y*x*y)⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc, show (y*x*y)⁻¹ * (y * x * y2) = y from by decide]
        exact IpDirect.not_XF_y_mul_Ip hγ
      have b3 : MonoidAlgebra.coeff r1 ((x*y)⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc,
          show (x*y)⁻¹ * (y * x * y2) = toProd [Ly2,Lx,Ly,Lx,Ly2] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b4 : MonoidAlgebra.coeff r1 (y * x * y2 * γ) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [show (y * x * y2 : FP) = toProd [Ly,Lx,Ly2] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b5 : MonoidAlgebra.coeff r1 (y2⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc, show y2⁻¹ * (y * x * y2) = toProd [Ly2,Lx,Ly2] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b6 : MonoidAlgebra.coeff r1 (y⁻¹ * (y * x * y2 * γ)) = 0 := by
        rw [← mul_assoc, show y⁻¹ * (y * x * y2) = x * y2 from by decide]
        exact IpDirect.coeff_eq_zero_of_len_supp h1len (by rw [IpDirect.elen_xy2_mul_of_XF hγ]; omega)
      rw [b1, b2, b3, b4, b5, b6]
      ring
    have hB : MonoidAlgebra.coeff (qνY2 ν * r2) (y * x * y2 * γ) = -ν * MonoidAlgebra.coeff r2 γ := by
      rw [coeff_qνY2_mul]
      have b1 : MonoidAlgebra.coeff r2 ((y2*x*y2)⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [← mul_assoc,
          show (y2*x*y2)⁻¹ * (y * x * y2) = toProd [Ly,Lx,Ly2,Lx,Ly2] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b2 : MonoidAlgebra.coeff r2 ((y*x*y2)⁻¹ * (y * x * y2 * γ)) = MonoidAlgebra.coeff r2 γ := by
        rw [← mul_assoc, show (y*x*y2)⁻¹ * (y * x * y2) = 1 from by decide, one_mul]
      have b3 : MonoidAlgebra.coeff r2 ((x*y2)⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [← mul_assoc,
          show (x*y2)⁻¹ * (y * x * y2) = toProd [Ly,Lx,Ly,Lx,Ly2] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b4 : MonoidAlgebra.coeff r2 (y⁻¹ * (y * x * y2 * γ)) = 0 := by
        rw [← mul_assoc, show y⁻¹ * (y * x * y2) = x * y2 from by decide]
        exact IpDirect.coeff_eq_zero_of_len_supp h2len (by rw [IpDirect.elen_xy2_mul_of_XF hγ]; omega)
      have b5 : MonoidAlgebra.coeff r2 (y * x * y2 * γ) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [show (y * x * y2 : FP) = toProd [Ly,Lx,Ly2] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b6 : MonoidAlgebra.coeff r2 (y2⁻¹ * (y * x * y2 * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [← mul_assoc, show y2⁻¹ * (y * x * y2) = toProd [Ly2,Lx,Ly2] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      rw [b1, b2, b3, b4, b5, b6]
      ring
    rw [hA, hB]
    ring
  refine shifted_orbit_corollary (u := u) (w := Tnu ν * u) (γ := y * x * y2 * γ)
    (c := -ν * MonoidAlgebra.coeff r2 γ) hν T_zpow_injective rfl hcoe
    (mul_ne_zero (neg_ne_zero.mpr hν) hγr2) ?_
  intro n hn
  refine hlong _ ?_
  have hb := (IpDirect.elen_T_zpow_mul_ge hγ hn).2.1
  omega


/-- Branch 1: the maximal-length element sits in the `Y`-slot. -/
theorem branch1_contra {ν : ℂ} (hν : ν ≠ 0) {u : RR} {c : ℂ} {r1 r2 : RR} {γ : FP}
    (hγ : XF γ)
    (h1XF : ∀ δ ∈ (MonoidAlgebra.coeff r1).support, XF δ)
    (h1len : ∀ δ ∈ (MonoidAlgebra.coeff r1).support, elen δ ≤ elen γ)
    (h2XF : ∀ δ ∈ (MonoidAlgebra.coeff r2).support, XF δ)
    (h2len : ∀ δ ∈ (MonoidAlgebra.coeff r2).support, elen δ ≤ elen γ)
    (h2van : ∀ z : FP, elen γ ≤ elen z → MonoidAlgebra.coeff r2 z = 0)
    (hγr1 : MonoidAlgebra.coeff r1 γ ≠ 0)
    (hv : Tnu ν * u = qν ν * (MonoidAlgebra.single (1 : FP) c + Y * r1 + Y2 * r2)) : False := by
  have hδlen : elen (y * x * y * γ) = elen γ + 3 := by
    rw [show y * x * y * γ = y * (x * y * γ) from by noncomm_ring,
      IpDirect.elen_y_mul_of_XF (IpDirect.XF_xy_mul_of_XF hγ), IpDirect.elen_xy_mul_of_XF hγ]
  have hlong : ∀ z : FP, 3 + elen γ < elen z →
      MonoidAlgebra.coeff (Tnu ν * u) z = 0 := by
    intro z hz
    rw [hv, coeff_qν_mul_split ν, coeff_qν_mul_single_eq_zero ν c (by omega),
      coeff_qνY_mul_eq_zero_of_long ν h1len (by omega),
      coeff_qνY2_mul_eq_zero_of_long ν h2len (by omega)]
    ring
  have hcoe : MonoidAlgebra.coeff (Tnu ν * u) (y * x * y * γ) = -ν * MonoidAlgebra.coeff r1 γ := by
    rw [hv, coeff_qν_mul_split ν, coeff_qν_mul_single_eq_zero ν c (by rw [hδlen]; omega)]
    have hA : MonoidAlgebra.coeff (qνY ν * r1) (y * x * y * γ) = -ν * MonoidAlgebra.coeff r1 γ := by
      rw [coeff_qνY_mul]
      have b1 : MonoidAlgebra.coeff r1 ((y2*x*y)⁻¹ * (y * x * y * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc,
          show (y2*x*y)⁻¹ * (y * x * y) = toProd [Ly2,Lx,Ly2,Lx,Ly] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b2 : MonoidAlgebra.coeff r1 ((y*x*y)⁻¹ * (y * x * y * γ)) = MonoidAlgebra.coeff r1 γ := by
        rw [← mul_assoc, show (y*x*y)⁻¹ * (y * x * y) = 1 from by decide, one_mul]
      have b3 : MonoidAlgebra.coeff r1 ((x*y)⁻¹ * (y * x * y * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc, show (x*y)⁻¹ * (y * x * y) = toProd [Ly2,Lx,Ly,Lx,Ly] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b4 : MonoidAlgebra.coeff r1 (y * x * y * γ) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [show (y * x * y : FP) = toProd [Ly,Lx,Ly] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b5 : MonoidAlgebra.coeff r1 (y2⁻¹ * (y * x * y * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h1XF ?_
        rw [← mul_assoc, show y2⁻¹ * (y * x * y) = toProd [Ly2,Lx,Ly] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b6 : MonoidAlgebra.coeff r1 (y⁻¹ * (y * x * y * γ)) = 0 := by
        rw [← mul_assoc, show y⁻¹ * (y * x * y) = x * y from by decide]
        exact IpDirect.coeff_eq_zero_of_len_supp h1len (by rw [IpDirect.elen_xy_mul_of_XF hγ]; omega)
      rw [b1, b2, b3, b4, b5, b6]
      ring
    have hB : MonoidAlgebra.coeff (qνY2 ν * r2) (y * x * y * γ) = 0 := by
      rw [coeff_qνY2_mul]
      have b1 : MonoidAlgebra.coeff r2 ((y2*x*y2)⁻¹ * (y * x * y * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [← mul_assoc,
          show (y2*x*y2)⁻¹ * (y * x * y) = toProd [Ly,Lx,Ly2,Lx,Ly] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b2 : MonoidAlgebra.coeff r2 ((y*x*y2)⁻¹ * (y * x * y * γ)) = 0 := by
        rw [← mul_assoc, show (y*x*y2)⁻¹ * (y * x * y) = y2 from by decide]
        exact IpDirect.coeff_eq_zero_of_not_XF_supp h2XF (IpDirect.not_XF_y2_mul_Ip hγ)
      have b3 : MonoidAlgebra.coeff r2 ((x*y2)⁻¹ * (y * x * y * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [← mul_assoc, show (x*y2)⁻¹ * (y * x * y) = toProd [Ly,Lx,Ly,Lx,Ly] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b4 : MonoidAlgebra.coeff r2 (y⁻¹ * (y * x * y * γ)) = 0 := by
        rw [← mul_assoc, show y⁻¹ * (y * x * y) = x * y from by decide]
        exact h2van _ (by rw [IpDirect.elen_xy_mul_of_XF hγ]; omega)
      have b5 : MonoidAlgebra.coeff r2 (y * x * y * γ) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [show (y * x * y : FP) = toProd [Ly,Lx,Ly] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      have b6 : MonoidAlgebra.coeff r2 (y2⁻¹ * (y * x * y * γ)) = 0 := by
        refine IpDirect.coeff_eq_zero_of_not_XF_supp h2XF ?_
        rw [← mul_assoc, show y2⁻¹ * (y * x * y) = toProd [Ly2,Lx,Ly] from by decide]
        exact IpDirect.not_XF_toProd_mul (by decide) (by decide) (by decide) (by decide) (by decide) hγ
      rw [b1, b2, b3, b4, b5, b6]
      ring
    rw [hA, hB]
    ring
  refine shifted_orbit_corollary (u := u) (w := Tnu ν * u) (γ := y * x * y * γ)
    (c := -ν * MonoidAlgebra.coeff r1 γ) hν T_zpow_injective rfl hcoe
    (mul_ne_zero (neg_ne_zero.mpr hν) hγr1) ?_
  intro n hn
  refine hlong _ ?_
  have hb := (IpDirect.elen_T_zpow_mul_ge hγ hn).1
  omega

end SpCore

theorem shifted_core_plus {ν : ℂ} (hν : ν ≠ 0) (hν3 : 1 + ν ^ 3 ≠ 0)
    {u r : Work.FreeProduct.RR}
    (h : Work.FreeProduct.Tnu ν * u = Work.FreeProduct.MUpv ν * (Work.FreeProduct.X + 1) * r) :
    Work.FreeProduct.Tnu ν * u = 0 := by
  obtain ⟨c, r1, r2, t, hdec, h1XF, h2XF⟩ := IpDirect.exists_canon_MUp r
  have hzero : SpCore.qν ν * ((X - 1) * t) = 0 := by
    rw [← mul_assoc, SpCore.qν_mul_X_sub_one, zero_mul]
  have hv' : Tnu ν * u
      = SpCore.qν ν * (MonoidAlgebra.single (1 : FP) c + Y * r1 + Y2 * r2) := by
    have hq : MUpv ν * (X + 1) * r = SpCore.qν ν * r := by rw [SpCore.qν]
    rw [h, hq, hdec, mul_add, hzero, add_zero]
  by_cases h12 : r1 = 0 ∧ r2 = 0
  · obtain ⟨hr1, hr2⟩ := h12
    rw [hr1, hr2, mul_zero, mul_zero, add_zero, add_zero] at hv'
    by_cases hc : c = 0
    · rw [hc, MonoidAlgebra.single_zero, mul_zero] at hv'
      exact hv'
    · exact absurd (SpCore.core_contra hν hc hv') (by simp)
  · by_cases hb : r2 ≠ 0 ∧ IpDirect.rlen r1 ≤ IpDirect.rlen r2
    · obtain ⟨hr2ne, hle⟩ := hb
      obtain ⟨γ, hγmem, hγlen⟩ := IpDirect.exists_rlen hr2ne
      exact (SpCore.branch2_contra hν (h2XF γ hγmem) (fun δ hδ => h1XF δ hδ)
        (fun δ hδ => by have := IpDirect.rlen_le_of_mem hδ; rw [hγlen]; omega)
        (fun δ hδ => h2XF δ hδ)
        (fun δ hδ => by have := IpDirect.rlen_le_of_mem hδ; rw [hγlen]; omega)
        (Finsupp.mem_support_iff.mp hγmem) hv').elim
    · by_cases hr2z : r2 = 0
      · have hr1ne : r1 ≠ 0 := by
          rintro rfl
          exact h12 ⟨rfl, hr2z⟩
        obtain ⟨γ, hγmem, hγlen⟩ := IpDirect.exists_rlen hr1ne
        exact (SpCore.branch1_contra hν (h1XF γ hγmem)
          (fun δ hδ => h1XF δ hδ)
          (fun δ hδ => by have := IpDirect.rlen_le_of_mem hδ; rw [hγlen]; omega)
          (fun δ hδ => by rw [hr2z] at hδ; simp at hδ)
          (fun δ hδ => by rw [hr2z] at hδ; simp at hδ)
          (fun z _ => by rw [hr2z]; simp)
          (Finsupp.mem_support_iff.mp hγmem) hv').elim
      · have hlt : IpDirect.rlen r2 < IpDirect.rlen r1 := by
          rcases lt_or_ge (IpDirect.rlen r2) (IpDirect.rlen r1) with hh | hh
          · exact hh
          · exact absurd ⟨hr2z, hh⟩ hb
        have hr1ne : r1 ≠ 0 := by
          rintro rfl
          rw [IpDirect.rlen_zero] at hlt
          omega
        obtain ⟨γ, hγmem, hγlen⟩ := IpDirect.exists_rlen hr1ne
        exact (SpCore.branch1_contra hν (h1XF γ hγmem)
          (fun δ hδ => h1XF δ hδ)
          (fun δ hδ => by have := IpDirect.rlen_le_of_mem hδ; rw [hγlen]; omega)
          (fun δ hδ => h2XF δ hδ)
          (fun δ hδ => by
            have h1 := IpDirect.rlen_le_of_mem hδ
            rw [← hγlen] at hlt
            omega)
          (fun z hz => by
            by_contra hc
            have h1 := IpDirect.rlen_le_of_mem (Finsupp.mem_support_iff.mpr hc)
            rw [hγlen] at hz
            omega)
          (Finsupp.mem_support_iff.mp hγmem) hv').elim

end

end Work.FreeProduct
