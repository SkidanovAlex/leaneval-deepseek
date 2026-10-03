/-
# The vocabulary of the §6 Poisson step (6.7) → (6.9), in smooth form

`Work.FIArea2.sum_gBox_eq_sum_congruences` turns the `w`-sum of (5.27) into a sum over the
parametrising pairs `(c₁,c₂) ∈ ℤ²` with `Δ ∣ c₁²z₂ − c₂²z₁`, of `f(|w|²)`, `w = wOf z₁ z₂ c₁ c₂`.
The Poisson step needs that summand written as the value at the lattice point `(c₁,c₂)` of a
function on `ℝ²`:

  `φ(t) = F(|t₁²z₂ − t₂²z₁|²/|Δ|²)`   (`Work.FIArea2.phiOf` with a *real* variable function),

because then the class sums modulo `m = |Δ|` can be summed by the two-dimensional Poisson formula
(`Work.FIArea2.poisson_coset_2d`).

This file fixes the two objects the assembly needs:

* `gphase z₁ z₂ t = |t₁²z₂ − t₂²z₁|²/|Δ|²`, the argument of `F` in `phiOf` — so that
  `phiOf F z₁ z₂ t = F (gphase z₁ z₂ t)` by definition, and the *concrete* evaluation
  `gphase z₁ z₂ (c₁,c₂) = |wOf z₁ z₂ c₁ c₂|²` (`gphase_wOf`) which is what makes the lattice sum
  below equal the `w`-sum of (6.7);
* `IsSmoothMajorant M F` — the *smooth* majorant of (5.19)/(§7): `C⁴`, compactly supported in
  the annulus `[M/4, 4M]` of (5.19), `0 ≤ F ≤ 1`, `≥ 1` on the dyadic segment of (4.18), with the
  derivative bounds `|f^{(j)}| ≤ C·M^{-min(j,2)}` (`j ≤ 4`) which are what §7 actually uses
  (the frozen `IsMajorant`'s second-difference bounds give these; see
  `Work.FIArea2.smooth_ext_of_isMajorant`).
-/
import Mathlib
import Submission.Work.FIArea2.Sec6Defs
import Submission.Work.FIArea2.gnorm_wOf
import Submission.Work.FITop3.Defs3

set_option autoImplicit false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The argument of the lattice phase of (6.7): `|t₁²z₂ − t₂²z₁|²/|Δ|²`. -/
def gphase (z1 z2 : GaussianInt) (t : ℝ × ℝ) : ℝ :=
  ((t.1 ^ 2 * (z2.re : ℝ) - t.2 ^ 2 * (z1.re : ℝ)) ^ 2
      + (t.1 ^ 2 * (z2.im : ℝ) - t.2 ^ 2 * (z1.im : ℝ)) ^ 2)
    / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2

/-- `phiOf` is `F` composed with the phase `gphase` — by definition. -/
theorem phiOf_eq_gphase (F : ℝ → ℝ) (z1 z2 : GaussianInt) (t : ℝ × ℝ) :
    phiOf F z1 z2 t = F (gphase z1 z2 t) := rfl

/-- **(6.7) evaluated on a lattice point**: on the parametrising pair `(c₁,c₂)` of (6.3) the phase
of the Poisson step is the *integer* `|w|²`, `w = wOf z₁ z₂ c₁ c₂`.  This is the identity that
joins the finite lattice sum produced by `sum_gBox_eq_sum_congruences` to the smooth function to
which Poisson summation is applied. -/
theorem gphase_wOf (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) {c1 c2 : ℤ}
    (h : ∃ w : GaussianInt, Work.FIPlan.cForm w z1 = c1 * c1 ∧
      Work.FIPlan.cForm w z2 = c2 * c2) :
    gphase z1 z2 ((c1 : ℝ), (c2 : ℝ))
      = ((Work.FIPlan.gnorm (wOf z1 z2 c1 c2) : ℕ) : ℝ) := by
  have hΔR : (((Work.FIPlan.Delta z1 z2 : ℤ)) : ℝ) ≠ 0 := by
    intro h
    exact hΔ (by exact_mod_cast h)
  -- `norm` of a Gaussian integer, and `gnorm`, in coordinates
  have hnorm_coord : ∀ N : GaussianInt,
      (((N.norm : ℤ)) : ℝ) = ((N.re : ℤ) : ℝ) ^ 2 + ((N.im : ℤ) : ℝ) ^ 2 := by
    intro N
    rw [Zsqrtd.norm_def]
    push_cast
    ring
  have hgnorm_norm : ∀ N : GaussianInt,
      ((Work.FIPlan.gnorm N : ℕ) : ℝ) = (((N.norm : ℤ)) : ℝ) := by
    intro N
    have hN : Work.FIPlan.gnorm N = ((N.re ^ 2 + N.im ^ 2 : ℤ)).natAbs := by
      simp [Work.FIPlan.gnorm, Zsqrtd.norm_def, sq]
    rw [hN, Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by push_cast; positivity),
      hnorm_coord N]
    push_cast
    ring
  -- `(c : ℤ[i])²` is the cast of `c²`, so that `re`/`im` are read off without powers
  have hkey : ((c1 : GaussianInt) ^ 2 * z2 - (c2 : GaussianInt) ^ 2 * z1)
      = (((c1 ^ 2 : ℤ) : GaussianInt) * z2 - ((c2 ^ 2 : ℤ) : GaussianInt) * z1) := by
    push_cast
    ring
  have hre : (((c1 : GaussianInt) ^ 2 * z2 - (c2 : GaussianInt) ^ 2 * z1).re)
      = c1 ^ 2 * z2.re - c2 ^ 2 * z1.re := by
    rw [hkey]
    simp only [Zsqrtd.re_sub, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
    ring
  have him : (((c1 : GaussianInt) ^ 2 * z2 - (c2 : GaussianInt) ^ 2 * z1).im)
      = c1 ^ 2 * z2.im - c2 ^ 2 * z1.im := by
    rw [hkey]
    simp only [Zsqrtd.im_sub, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
    ring
  have hnormN : ((((c1 : GaussianInt) ^ 2 * z2 - (c2 : GaussianInt) ^ 2 * z1).norm : ℤ) : ℝ)
      = ((c1 : ℝ) ^ 2 * (z2.re : ℝ) - (c2 : ℝ) ^ 2 * (z1.re : ℝ)) ^ 2
        + ((c1 : ℝ) ^ 2 * (z2.im : ℝ) - (c2 : ℝ) ^ 2 * (z1.im : ℝ)) ^ 2 := by
    rw [hnorm_coord, hre, him]
    push_cast
    ring
  -- `|wOf|²·Δ² = |c₁²z₂ − c₂²z₁|²`
  have hnormR : (((wOf z1 z2 c1 c2).norm : ℤ) : ℝ) * (((Work.FIPlan.Delta z1 z2 : ℤ)) : ℝ) ^ 2
      = ((((c1 : GaussianInt) ^ 2 * z2 - (c2 : GaussianInt) ^ 2 * z1).norm : ℤ) : ℝ) := by
    have hcast := congrArg (fun n : ℤ => (n : ℝ)) (norm_wOf_eq z1 z2 hΔ h)
    push_cast at hcast
    rw [hcast]
  have hstep : ((((c1 : GaussianInt) ^ 2 * z2 - (c2 : GaussianInt) ^ 2 * z1).norm : ℤ) : ℝ)
      = (((wOf z1 z2 c1 c2).norm : ℤ) : ℝ) * (((Work.FIPlan.Delta z1 z2 : ℤ)) : ℝ) ^ 2 :=
    hnormR.symm
  have habs : (((Work.FIPlan.absDelta z1 z2 : ℕ)) : ℝ) ^ 2
      = ((((Work.FIPlan.Delta z1 z2 : ℤ)) : ℝ)) ^ 2 := by
    rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [gphase, habs, div_eq_iff (pow_ne_zero 2 hΔR), ← hnormN, hstep,
    hgnorm_norm (wOf z1 z2 c1 c2)]

/-- **The smooth majorant of (5.19)/(§7)**, in the form in which §7 consumes it: `F` is `C⁴` with
compact support in a unit-neighbourhood of the annulus `[M/4, 4M]` of (5.19), `|F| ≤ 2`, `F ≥ 1`
at the Gaussian norms `gnorm w` of the dyadic annulus `M < |w|² ≤ 2M` of (4.18) (this is the
condition `IsMajorant` imposes — it is a condition on the *integers* `|w|²`, not on all reals, and
stating it on all reals would be incompatible with `F n = f n` at the integers that are not values
of `gnorm`), and its first four derivatives obey the bounds §7's
integration by parts uses, `|F^{(j)}| ≤ C·M^{-1}` for `j = 1` and `|F^{(j)}| ≤ C·M^{-2}` for
`j = 2,3,4` (written uniformly as `M^{-min(j,2)}`).  The paper's `|f^{(j)}| ≤ M^{-j}` (`j ≤ 4`) is
stronger; this is what the frozen `IsMajorant`'s difference bounds can actually deliver, and (by
the geometric inequalities (7.2)–(7.4)) it is what the proof of Lemma 7.1 needs. -/
def IsSmoothMajorant (M : ℝ) (F : ℝ → ℝ) : Prop :=
  ContDiff ℝ 4 F ∧ HasCompactSupport F ∧
  (∀ x, |F x| ≤ 2) ∧
  (∀ w : GaussianInt, M < (Work.FIPlan.gnorm w : ℝ) →
      (Work.FIPlan.gnorm w : ℝ) ≤ 2 * M → 1 ≤ F (Work.FIPlan.gnorm w)) ∧
  (∀ x, F x ≠ 0 → M / 4 - 1 ≤ x ∧ x ≤ 4 * M + 1) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ j ∈ Finset.Icc 0 4, ∀ x : ℝ,
      |iteratedDeriv j F x| ≤ C * M ^ (-(min j 2 : ℕ) : ℝ))

/-- The §6/§7 frequency `u₁ = h₁|Δ z₂|^{−1/2}`, with `|z|` the modulus `√(gnorm z)`: this is the
first argument of `Fint` in (6.9), and the one that occurs in Lemma 7.1's weight
`(1 + u₁²δ√M)^{−1}` (`δ² = 1 − γ²`). -/
def secFreq₁ (z1 z2 : GaussianInt) (h : ℤ) : ℝ :=
  (h : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
    * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)))

/-- The same for `u₂ = h₂|Δ z₁|^{−1/2}`. -/
def secFreq₂ (z1 z2 : GaussianInt) (h : ℤ) : ℝ :=
  (h : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
    * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)))

/-- The weight constant of the `(9.1)` error: `c₁ = δ√M/(|Δ|·|z₂|)`, `δ² = 1 − γ²`.  The weight
`(1 + u₁²δ√M)^{−1}` of Lemma 7.1 is `(1 + h₁²c₁)^{−1}` (`secFreq_sq_mul`), so the `h`-sum of
`sec9_frequency_sum_bound` is the Mehler-type sum of `tsum_gcd_weight_le`. -/
def secWeight₁ (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) : ℝ :=
  Real.sqrt (1 - (gamOf z1 z2) ^ 2) * Real.sqrt Pa.M
    / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)))

/-- The same for the second frequency: `c₂ = δ√M/(|Δ|·|z₁|)`. -/
def secWeight₂ (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) : ℝ :=
  Real.sqrt (1 - (gamOf z1 z2) ^ 2) * Real.sqrt Pa.M
    / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)))

/-- **The weight identity of Lemma 7.1's `h`-sum**: `u₁²δ√M = h₁²c₁` with `u₁ = secFreq₁`. -/
theorem secFreq_sq_mul (Pa : Work.FITop.Params) (z1 z2 : GaussianInt)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) (hγ0 : 0 ≤ gamOf z1 z2) (hγ1 : gamOf z1 z2 < 1)
    (hM : 1 ≤ Pa.M) (h : ℤ) :
    (secFreq₁ z1 z2 h) ^ 2 * Real.sqrt (1 - (gamOf z1 z2) ^ 2) * Real.sqrt Pa.M
      = (h : ℝ) ^ 2 * secWeight₁ Pa z1 z2 := by
  have hAbs : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
    simp only [Work.FIPlan.absDelta]
    exact fun hz => hΔ ((Int.natAbs_eq_zero).mp hz)
  have hA : (0 : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hAbs
  have hz2 : z2 ≠ 0 := by
    intro hz
    exact hΔ (by simp [Work.FIPlan.Delta, hz])
  have hn2 : (0 : ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos hz2
  have hs2 : (0 : ℝ) < Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := Real.sqrt_pos.2 hn2
  have hD : (0 : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := mul_pos hA hs2
  have hMpos : (0 : ℝ) < Real.sqrt Pa.M := Real.sqrt_pos.2 (by linarith)
  have hδ2 : (0 : ℝ) < 1 - (gamOf z1 z2) ^ 2 := by nlinarith [hγ0, hγ1, sq_nonneg (gamOf z1 z2)]
  unfold secFreq₁ secWeight₁
  rw [div_pow, Real.sq_sqrt hD.le]
  push_cast
  field_simp
  try ring

end

end Work.FIArea2
