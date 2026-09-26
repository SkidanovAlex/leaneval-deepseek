import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24B7Bound_proof
import Submission.Work.Asymptotics.KhatE1Core.Bracket24XtruncDefs

/-!
# Bounding the explicit remainders `XR4` / `XW` of `Bracket24TailPlan.lean`: findings and atoms

This module records the state of the *remaining-remainder* bounds of the
`Xtrunc` route to `Bracket24TailCore` (plan: `KhatE1Core/Bracket24TailPlan.lean`,
`KhatE1Core/Bracket24XtruncDefs.lean`, `Bracket24XtruncRing.lean`), and supplies the reusable
`BoundQ` atoms for them.

## What is needed

`Xtrunc2_decomp` gives

  `Xtrunc2 - B₂E² - B₃E³ - B₄E⁴ - B₅E⁵ = (Ept z)^4 · XR4 ℓ τ z + (Ept z)^6 · XW ℓ τ z`

with `XR4`, `XW` *explicit* finite sums of monomials.  Together with the truncation-tail bound
(`X - Xtrunc2`, the `Sm_i - Sm_iT` and K₋ analogues) and the proved coefficient bounds
(`Bracket24E3_bound`, `Bracket24B4Bound_proof`, `Bracket24E5_bound`), the target
`‖Sh·Bracket24 - E²B₂‖ ≤ C ‖q(τ)‖(scale τ)^N(1+t)^M e^{-2πt}` follows as soon as

* `‖XR4 ℓ τ z‖ ≤ C (scale τ)^N (1+t)^M` and
* `‖XW ℓ τ z‖ ≤ C ‖q(τ)‖⁻¹ (scale τ)^N (1+t)^M`.

Both are *explicit-polynomial* bounds in the atoms
`{Δ, E₂, E₄, E₆, j, ψ₂, ψ₄}(τ)`, `{z, S0z z, Ept z}`, `cuspC ℓ`, `π`, and the atoms needed are
supplied below (`BoundQ_E2Fun`, `BoundQ_zC`, `BoundQ_tauC`, `BoundQ_S0z`, `BoundQ_Ept`; the
τ-atoms `Δ, E₄, E₆, j, ψ₂, ψ₄` are the already-proved `BoundQ.DeltaFun`, `BoundQ.E4Fun`,
`BoundQ.E6Fun`, `BoundQ.jInvariantFun`, `BoundQ.psi2`, `BoundQ.psi4` of
`Bracket24B7Bound_proof`).

## The one genuine weight obstruction, and its resolution

Every monomial of `XR4` has `j(τ)`-degree `≤ 1` and every monomial of `XW` has `j(τ)`-degree
`≤ 1` **except two**:

  `(7/4)·π⁻¹·Ept z·E₄(τ)²·ψ₄(τ)·j(τ)²`  and  `-(7/4)·π⁻¹·Ept z·E₄(τ)E₆(τ)·ψ₂(τ)·j(τ)²`.

Their `j²` forces `‖q(τ)‖⁻²`, one power too much for the target.  They are, however, *exactly* the
`θ₂₄` pair: their sum is `(7/4)·π⁻¹·Ept z·(ψ₄E₈ - ψ₂E₁₀)(τ)·j(τ)²` (using
`E₈ = E₄²`, `E₁₀ = E₄E₆`), and `ψ₄E₈ - ψ₂E₁₀ = O(‖q(τ)‖(scale τ)^N)` ("the near-identity",
`BoundQ.theta24`), which supplies exactly the missing power of `‖q(τ)‖`.  The `BoundQ` bound for
that group is proved below as `BoundQ_theta24_group`.

## A toolkit that removes the `mul_le_mul` bookkeeping

The `F`/`R` route to `Bracket24TailCore` (`Bracket24TailPlan.lean`, and its sections 7-9 which
record the cost of the raw `mul_le_mul`-style proofs of `d{Pfun,Vfun}*_bound`, `dPhi_bound`,
`dSm1_bound`) is made cheap by the *two-exponent bound calculus* `Bound2` of
`KhatE1Core/DSm1RowBound.lean`: `Bound2 f n k` means
`‖f τ z‖ ≤ C ‖q(τ)‖^n (scale τ)^N (1+t)^M ‖q(z)‖^k`, sums take the `min` of the exponents,
products the sum, and `Bound2.shift` trades one power of `‖q(τ)‖` for one of `‖q(z)‖` (via
`‖q(z)‖ ≤ ‖q(τ)‖` on the strip).  With the atom bounds of that file every one of the five
`K₊` deviation rows is a three-line proof, and the whole row package closes as

* `Bound2_dSm1 : Bound2 dSm1 0 2`, `Bound2_dSm2 : Bound2 dSm2 (-1) 1`,
  `Bound2_dSm3 : Bound2 dSm3 (-1) 3`, `Bound2_dSm4 ℓ : Bound2 dSm4 0 3`,
  `Bound2_dSm5 ℓ : Bound2 dSm5 (-1) 3`,
* `Bound2_dKPlusSum ℓ : Bound2 dKPlusSum (-1) 1` (the `K₊` half of the split),
  with raw corollaries `dSm1_row_bound`, `dSm1_row_bound_qt`, `dSm2_row_bound`,
  `dKPlusSum_bound ℓ`.

(`Bound2 dSm1 0 2` is *stronger* than the plan's `‖q(τ)‖⁻¹‖q(z)‖²`: it gives `‖q(z)‖²`, and
`‖q(z)‖ ≤ ‖q(τ)‖` supplies the `‖q(τ)‖⁻¹`.)  The same `BoundQ` calculus of
`Bracket24B7Bound_proof` (`BoundQ f n`: one `‖q(τ)‖`-exponent only) is what the atom bounds above
extend; using it, none of the nine traps of `Bracket24TailPlan.lean` §7-§9 can arise.

## Practical obstacle (recorded for whoever picks this up)

`XR4` has 30 monomials; `XW` has 254.  A *monolithic* proof — build the `BoundQ` tree of the
monomial bounds and close with
`congr fun τ z => by simp only [XW]; ring` — reaches the elaborator limits: with
`set_option maxHeartbeats 8000000` a goal whose two sides both carry the 254 monomials of `XW`
fails with

  `(deterministic) timeout at «synthesize pending MVars»` (while *stating* the goal),

and the equality of two *re-associated* 254-term sums is likewise out of reach for `ring` at this
budget.  (`def XW` itself does elaborate, with `set_option maxRecDepth 10000`; only *equalities*
about it are expensive.)  A workable organisation is therefore to split `XW` along the tree
structure of its own definition (`XW = G₁ + G₂` at the top level, recursively) and bound each
group with a *small* `ring`, so that no single goal ever carries the full sum.  The tooling used
to attempt the monolithic version is the generator `_genxr.py` in the workspace root; it parses
the definitions of `XR4`/`XW` out of `Bracket24XtruncRing.lean` and emits the `BoundQ` tree.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-! ## Additional `BoundQ` atoms for the `XR4`/`XW` monomials -/

/-- `E₂(τ) = O(1)` on the funnel. -/
theorem BoundQ_E2Fun : BoundQ (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
    Work.Kernels.E2Fun τ) 0 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.E2Fun_bound
  exact ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim =>
    by simpa only [zpow_zero, Real.rpow_zero, mul_one] using hb τ (le_trans (by norm_num) hF.2)⟩

/-- `z = O(1+t)` on the strip `0 ≤ Re z ≤ 1`, `Im z = t`. -/
theorem BoundQ_zC : BoundQ (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => (z : ℂ)) 0 := by
  refine ⟨2, 0, 1, by norm_num, le_rfl, by norm_num, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h1 : ‖(z : ℂ)‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  have h2 : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith, hz1⟩
  have h3 : |z.im| = t := by rw [abs_of_pos z.im_pos, hzim]
  have ht0 : (0 : ℝ) ≤ t := by have := hF.2; linarith
  simp only [zpow_zero, Real.rpow_zero, Real.rpow_one, mul_one, one_mul]
  linarith

/-- `τ = O(scale τ)` on the funnel. -/
theorem BoundQ_tauC : BoundQ (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) => (τ : ℂ)) 0 := by
  refine ⟨1, 1, 0, by norm_num, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := by
    have h0 : (0 : ℝ) ≤ (τ.im)⁻¹ := inv_nonneg.mpr τ.im_pos.le
    rw [Work.Kernels.scale]; linarith
  simp only [zpow_zero, Real.rpow_zero, Real.rpow_one, mul_one, one_mul]
  exact h

/-- `S0z z = O(1)`. -/
theorem BoundQ_S0z : BoundQ (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
    Work.Asymptotics.KhatE1.S0z z) 0 := by
  refine ⟨3, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  have h : ‖Work.Asymptotics.KhatE1.S0z z‖ ≤ 3 := Work.Asymptotics.K24F.zS0_norm z hz1'
  simpa only [zpow_zero, Real.rpow_zero, mul_one] using h

/-- `Ept z = O(1)`. -/
theorem BoundQ_Ept : BoundQ (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
    Work.Residues.Ept z) 0 := by
  refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hz0' : (0 : ℝ) ≤ z.im := z.im_pos.le
  have h : ‖Work.Residues.Ept z‖ ≤ 1 := by
    rw [Work.Residues.norm_Ept, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz0']
  simpa only [zpow_zero, Real.rpow_zero, mul_one] using h

/-! ## The `θ₂₄` pair of `XW` -/

/-- **The two `j²`-monomials of `XW` together**: `(7/4)π⁻¹Ept·(ψ₄E₈ - ψ₂E₁₀)j²` is
`O(‖q(τ)‖⁻¹ (scale τ)^N)`, the same weight as all the other monomials of `XW`. -/
theorem BoundQ_theta24_group (ℓ : Work.Kernels.LogLambdaData) :
    BoundQ (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      (7 / 4 : ℂ) * (((Real.pi : ℂ))) ^ (-1 : ℤ) * Work.Residues.Ept z
        * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
            - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
        * Work.Kernels.jInvariantFun τ ^ 2) (-1) :=
  BoundQ.mono (by norm_num)
    ((((((BoundQ.const ((7 / 4 : ℂ) * ((Real.pi : ℂ) ^ (-1 : ℤ)))).mul BoundQ_Ept).mul
      (BoundQ.theta24 ℓ)).mul BoundQ.jInvariantFun).mul BoundQ.jInvariantFun).congr
      (fun τ z => by ring))

end

end Work.Asymptotics.KhatE1Core
