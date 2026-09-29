import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.H_conv_alt
import Submission.Work.A14D.H_local_at_one
import Submission.Work.A14D.H_not_holo_at_one
import Submission.Work.A14D.uh_not_holo_at_ninth
import Submission.Work.A14D.logCoeff_exists
import Submission.Work.A14D.uh_ode
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.A14D.jump_not_zero_Om1
import Submission.Work.A14D.D_zero_of_c_eq_zero
import Submission.Work.A14D.kappaU_minus_kappaL

namespace Work.A14D

/-
THE CRUX of area A14D (design `REFS/design/a14/A14_design.lean.txt` (K)): the jump of `H` across the
slit `(-∞,1]` has a non-zero log-coefficient at `x = 1/9` on at least one side.  This is what lets
`relation_to_LC_A` cancel `κ` and conclude `(LC)`; without it the paper's monodromy step is vacuous
in the ARel case (`Sym⁺H` has trivial monodromy around `y = -1/72` because `H` is analytic on
`ball 0 1 ⊃ 1/9`), which is exactly why this analytic statement is needed.

SETUP.  `H = Hfun a b c` satisfies `LZ H = rhsZ b c` on `ball 0 1` (ARel ⇒ overconvergence,
`H_conv_alt`).  `HU` resp. `HL` is the continuation of `H` to the half-plane `SU` resp. `SL`;
`D = HU - HL` on `SU ∩ SL`, continued to `Om1` (see `kappa_jump_sol`), and `LZ D = 0` on `Om1`.

FACTS THAT MAKE THIS PROVABLE.
(1) `R f := fun z => conj (f (conj z))` preserves solutions (`LZ` has real coefficients) and
    `R HU = HL` (both are analytic on `SL`, agree with `H` on `SL ∩ ball 0 1`).  Hence `R D = -D`
    (`D` is "anti-real") and therefore `κL = -conj κU`:  for anti-real `f`, `Λ^L f = conj (Λ^U (R f))
    = -conj (Λ^U f)`.  So it SUFFICES to prove `κU ≠ 0`.
(2) Write `Ñ := I * D / (2 * π)`.  Then `D = -2π I * Ñ` and `Ñ` is a real-coefficient solution of
    `LZ = 0` on `Om1`; consequently `κU = -2π I * Λ^U(Ñ)`, so it suffices to show that `Ñ` is not
    a `ℂ`-multiple of `y9`, i.e. `Λ^U(Ñ) ≠ 0`, i.e. `Ñ` is not holomorphic at `x = 1/9`.
(3) `H_local_at_one` gives `H = e0 + e1·ell + e2·ell²` on `lens1 δ'` with `ell = log(1-z)` and
    `e2 = -(c/16)·uh`.  On the two half-discs of `ball 1 δ'` the relevant branches of `log (1 - z)`
    differ by `2π I`, and (with the correct product rule
    `LZ(fg) = g·LZ f + f·LZ g + 2·PZ·f'·g' - RZ·f·g`) the coefficient of `ell²` identifies
    `LZ e2 = 0`, of `ell` gives `LZ e1 = 2(1-18z)e2 + 4·PZ·e2'/(1-z)` and of `1/(1-z)` gives
    `e2 1 = -c/16`.  From this one computes, on the wedge `SU ∩ SL` (near `x = 1`),
    `D = -2π I*(e1 + 2*e2*η) + 4π²*e2` for a branch `η` of `log (1-z)`; equivalently
    `Ñ = e1 + 2*e2*log (z-1)`  (principal `log (z-1)`, real on `(1,∞)`).
(4) `c = 0` case (clear): `e2 = 0` so `Ñ = e1`; `LZ e1 = 0` and `e1` is analytic at `1`, hence
    `e1 = α·uh` with `uh` the holomorphic solution at `1` (`uh 1 = 1`); `α ≠ 0` because otherwise
    `H = e0` would be holomorphic at `1`, contradicting `H_not_holo_at_one a b c h hb hc`; and
    `Λ^U(uh) ≠ 0` because otherwise `uh` would be holomorphic at `1/9`, contradicting
    `uh_not_holo_at_ninth`.  So `κU = -2π I*α*Λ^U(uh) ≠ 0`.
(5) `c ≠ 0` case: by ARel, `H = b·H_B' + c·H_C'` with `H_B' := H_B - (L/2)·H_A` (solves `LZ = 1`,
    so case (4) applies to it) and `H_C' := H_C - (ζ(2)/4)·H_A` (solves `LZ = 1/(1-x)`).  Since
    `H ↦ (D, Ñ, Λ^U(Ñ))` is linear, and `Λ^U(uh) =: λ ≠ 0`,
    `κU = -2π I * λ * (b·α' + c·β)` with `α' = e1^{B'}(1)` real and non-zero and
    `β = Λ^U(Ñ_C')/λ`; it therefore suffices to show `α' + c·β ≠ 0` for all `c : ℤ` (so for
    instance `β ∉ ℝ` would do, since `α'` is real non-zero).  A numeric check (double–to–40-digit
    analytic continuation of the explicit power series of `H_A, H_B, H_C`, Taylor stepping around
    `1/9`, fitting the log-coefficient against the Frobenius solution `y9` at `1/9`, which satisfies
    `LZ y9 = 0` with `y9 = 1 - 9/4 (z-1/9) + 405/32 (z-1/9)² - ...`) gives for `b = 1`:
    `c=0: κU = 0.20001428 + 2.95897713 I`,  `c=1: 3.86724947 + 2.83561339 I`,
    `c=2: 7.53448465 + 2.71224965 I`, `c=-1: -3.46722090 + 3.08234087 I`,
    i.e. `λ·(α' + cβ)` with `λ ≈ -1.55784321 + 0.10530358 I`, `α' ≈ 0.302288` real,
    `β ≈ 0.012681 - 0.373801 I` — so `κU ≠ 0` for every tested `c`, and `Im β ≠ 0`.
-/
open Complex Metric
open scoped BigOperators
open Work.A14D

theorem kappa_jump_nnz (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (hb : b ≠ 0)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (y9 : ℂ → ℂ) (δ : ℝ) (hY : Y9 y9 δ)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z)
    (κU κL : ℂ) (hU : LogCoeff y9 δ (halfU δ) D κU) (hL : LogCoeff y9 δ (halfL δ) D κL) :
    κU ≠ 0 ∨ κL ≠ 0 := by
  by_cases hc : c = 0
  · -- CASE `c = 0` (PROVED).  If `κU = 0` then the jump `D` extends holomorphically across
    -- `1/9`; the `c = 0` local analysis (`Work.A14D.D_zero_of_c_eq_zero`) then shows `D ≡ 0`
    -- on `Om1`, contradicting `Work.A14D.jump_not_zero_Om1`.
    refine Or.inl (fun hκU => ?_)
    exact jump_not_zero_Om1 a b c h hb HU HL hHU hHL D hD hDL hDj
      (D_zero_of_c_eq_zero a b c h hb hc HU HL hHU hHL y9 δ hY D hD hDL hDj κU hU hκU)
  · -- CASE `c ≠ 0`.  Suppose both log coefficients vanish.  By the design identity
    -- `Work.A14D.kappaU_minus_kappaL`, `κU - κL = -(π²c/2)·λ` with `λ ≠ 0` the (non-zero)
    -- log coefficient of `uh` on the lens `ball (1/9) δ ∩ ball 1 (8/9)`
    -- (`Work.A14D.uh_logCoeff_lens`).  With `κU = κL = 0` this forces `c = 0`,
    -- contradicting the case assumption.
    by_contra hcon
    push_neg at hcon
    obtain ⟨hκU0, hκL0⟩ := hcon
    obtain ⟨lam, hlam, -, hdiff⟩ :=
      kappaU_minus_kappaL a b c h HU HL hHU hHL y9 δ hY D hD hDL hDj κU κL hU hL
    have hzero : -(Real.pi ^ 2 * (c : ℂ) / 2) * lam = 0 := by
      rw [← hdiff, hκU0, hκL0, sub_zero]
    have hc0 : (c : ℂ) = 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have h2 : Real.pi ^ 2 * (c : ℂ) / 2 = 0 := by
        have h1 : (Real.pi ^ 2 * (c : ℂ) / 2) * lam = 0 := by
          have h := hzero
          rw [neg_mul] at h
          exact neg_eq_zero.mp h
        exact (mul_eq_zero.mp h1).resolve_right hlam
      rw [div_eq_zero_iff] at h2
      rcases h2 with h2 | h2
      · exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 hpi)
      · norm_num at h2
    exact hc (by exact_mod_cast hc0)

end Work.A14D
