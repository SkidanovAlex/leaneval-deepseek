/-
# `Submission.Work.FIArea6.TauPieces.CleanSumEqTsum`

The regrouping of the *clean* §16 sum by the norm: the finite sum over the box `boxN Pa` of the
clean summand `p(|z|²)μ(|z|²)γ(|z|²;C)ψ_m(z)` (supported on primary, small-prime-free `z`) equals
the Möbius-twisted Hecke sum `Tsum = Σ_n 1_{(n,Π)=1}λ_m(n)μ(n)γ(n;C)p(n)` of (16.29)/(16.30).

The point is that the `n`-summand of `Tsum` is the *fibre* of the box sum over the primary `z` with
`|z|² = n`: the box `boxN Pa = gBox ⌈√(4N)⌉` contains every primary `z` with `|z|² ≤ (1+θ)N`
(ν `θ ≤ 1`, so `(1+θ)N ≤ 2N` and `|Re z|,|Im z| ≤ √(2N) ≤ ⌈√(4N)⌉`), and `heckeLam` is by
definition the sum of `ψ` over the primary `z` of a fixed norm.  The support condition
`p u ≠ 0 → N < u ≤ (1+θ)N` makes the `tsum` defining `Tsum` finite and supported in the norms
occurring in the box.
-/
import Mathlib
import Submission.Work.FIArea6.S16TsumHeartDefs
import Submission.Work.FIArea4.S15box
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Work.FIArea4.GaussMoebiusCore

set_option autoImplicit false
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Work.FIArea6.TauPieces

noncomputable section

/-- `NoSmallPrimes` on `z` is `NoSmallPrimesNat` on `|z|²`. -/
lemma noSmallPrimes_iff_nat (Pa : Work.FITop.Params) (z : GaussianInt) :
    Work.FITop4.NoSmallPrimes Pa z ↔ Work.FIArea6Hecke.NoSmallPrimesNat Pa (Work.FIPlan.gnorm z) :=
  Iff.rfl

/-- A Gaussian integer of norm at most `(1+θ)N` lies in the box `boxN Pa`.  (No primitivity is
needed: `|Re z|, |Im z| ≤ √|z|² ≤ √(2N) ≤ ⌈√(4N)⌉ = radN Pa`.) -/
lemma mem_boxN_of_le (Pa : Work.FITop.Params) {z : GaussianInt}
    (hn : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N) : z ∈ Work.FITop.boxN Pa := by
  have hθ : Pa.θ ≤ 1 := Work.FIArea4.theta_le_one Pa
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hgn2 : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N :=
    le_trans hn (mul_le_mul_of_nonneg_right (by linarith) hN0)
  set R : ℕ := ⌈Real.sqrt (4 * Pa.N)⌉₊ with hRdef
  have hRZ : Work.FITop.radN Pa = (R : ℤ) := rfl
  have hsq_le : ((z.re.natAbs : ℝ)) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ) := by
    have h : z.re.natAbs ^ 2 ≤ Work.FIPlan.gnorm z := by
      rw [Work.FIArea4.gnorm_eq_re_sq_add_im_sq]; exact Nat.le_add_right _ _
    exact_mod_cast h
  have hsq_le_im : ((z.im.natAbs : ℝ)) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ) := by
    have h : z.im.natAbs ^ 2 ≤ Work.FIPlan.gnorm z := by
      rw [Work.FIArea4.gnorm_eq_re_sq_add_im_sq]; exact Nat.le_add_left _ _
    exact_mod_cast h
  have hsqrt : Real.sqrt (Work.FIPlan.gnorm z : ℝ) ≤ (R : ℝ) := by
    have h1 : Real.sqrt (Work.FIPlan.gnorm z : ℝ) ≤ Real.sqrt (2 * Pa.N) := Real.sqrt_le_sqrt hgn2
    have h2 : Real.sqrt (2 * Pa.N) ≤ Real.sqrt (4 * Pa.N) := Real.sqrt_le_sqrt (by linarith)
    have h3 : Real.sqrt (4 * Pa.N) ≤ (R : ℝ) := by rw [hRdef]; exact Nat.le_ceil _
    linarith
  have hb (c : ℤ) (hc : ((c.natAbs : ℝ)) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ)) :
      c ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa) := by
    rw [hRZ, Finset.mem_Icc]
    have h1 : (c.natAbs : ℝ) ≤ (R : ℝ) := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg (c.natAbs))]
      exact le_trans (Real.sqrt_le_sqrt hc) hsqrt
    have h2 : c.natAbs ≤ R := by exact_mod_cast h1
    have habs : |c| ≤ (R : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h2
    exact abs_le.mp habs
  rw [Work.FITop.boxN, Work.FIArea5.S16Hecke.mem_gBox_iff]
  exact ⟨hb z.re hsq_le, hb z.im hsq_le_im⟩

/-- The Hecke eigenvalue at `n` is the sum of `ψ` over the primary `z` of norm `n` lying in the
box `boxN Pa`, provided that box contains all the primary `z` of norm `n`. -/
lemma heckeLam_eq_sum_boxN_filter (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (n : ℕ)
    (hbox : ∀ z : GaussianInt, Work.FIPlan.gnorm z = n → z ∈ Work.FITop.boxN Pa) :
    Work.FIArea5.S16Hecke.heckeLam chi m n
      = ∑ z ∈ (Work.FITop.boxN Pa).filter
          (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n),
          Work.FIArea5.S16Hecke.psi chi m z := by
  have hAB : (Work.FIPlan.gBox (n : ℤ)).filter
        (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n)
      = (Work.FITop.boxN Pa).filter
        (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨-, hp, hg⟩
      exact ⟨hbox x hg, hp, hg⟩
    · rintro ⟨-, hp, hg⟩
      refine ⟨?_, hp, hg⟩
      rw [Work.FIArea5.S16Hecke.mem_gBox_iff, Finset.mem_Icc, Finset.mem_Icc]
      have hc := Work.FIArea4.gnorm_eq_coords x
      rw [hg] at hc
      have hre : x.re ^ 2 ≤ (n : ℤ) := by linarith [sq_nonneg x.im]
      have him : x.im ^ 2 ≤ (n : ℤ) := by linarith [sq_nonneg x.re]
      exact ⟨abs_le.mp (le_trans (Work.FIArea4.abs_le_sq x.re) hre),
             abs_le.mp (le_trans (Work.FIArea4.abs_le_sq x.im) him)⟩
  rw [Work.FIArea5.S16Hecke.heckeLam, hAB]

/-- The Möbius-twisted Hecke sum is the finite sum over the norms occurring in the box. -/
lemma Tsum_eq_sum_image (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (hbox : ∀ (n : ℕ) (z : GaussianInt), (n : ℝ) ≤ (1 + Pa.θ) * Pa.N →
        Work.FIPlan.gnorm z = n → z ∈ Work.FITop.boxN Pa)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) :
    Work.FIArea6Hecke.Tsum Pa chi m p
      = ∑ n ∈ (Work.FITop.boxN Pa).image Work.FIPlan.gnorm,
          (if Work.FIArea6Hecke.NoSmallPrimesNat Pa n then
            Work.FIArea5.S16Hecke.heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C n : ℂ) * (p n : ℂ) else 0) := by
  unfold Work.FIArea6Hecke.Tsum
  refine tsum_eq_sum (s := (Work.FITop.boxN Pa).image Work.FIPlan.gnorm) ?_
  intro n hn
  by_cases hN : Work.FIArea6Hecke.NoSmallPrimesNat Pa n
  · rw [if_pos hN]
    by_cases hp : p (n : ℝ) = 0
    · simp [hp]
    · have hnn := hpsupp (n : ℝ) hp
      have hlam : Work.FIArea5.S16Hecke.heckeLam chi m n = 0 := by
        rw [Work.FIArea5.S16Hecke.heckeLam]
        apply Finset.sum_eq_zero
        intro z hz
        rw [Finset.mem_filter] at hz
        obtain ⟨-, hprim, hgn⟩ := hz
        exact absurd (Finset.mem_image.mpr ⟨z, hbox n z hnn.2 hgn, hgn⟩) hn
      rw [hlam]
      simp
  · rw [if_neg hN]

/-- The fibre of the box over `n` contributes exactly the `n`-th summand of `Tsum`. -/
lemma sum_summand_fiber (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) (n : ℕ) :
    ∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => Work.FIPlan.gnorm z = n),
        Work.FIArea6.S16CleanSummand Pa chi m p z
      = (if Work.FIArea6Hecke.NoSmallPrimesNat Pa n then
            Work.FIArea5.S16Hecke.heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C n : ℂ) * (p n : ℂ) else 0) := by
  by_cases hN : Work.FIArea6Hecke.NoSmallPrimesNat Pa n
  · rw [if_pos hN]
    by_cases hp : p (n : ℝ) = 0
    · have hzero : ∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => Work.FIPlan.gnorm z = n),
            Work.FIArea6.S16CleanSummand Pa chi m p z = 0 := by
        apply Finset.sum_eq_zero
        intro z hz
        rw [Finset.mem_filter] at hz
        obtain ⟨-, hgn⟩ := hz
        unfold Work.FIArea6.S16CleanSummand
        rw [hgn]
        by_cases hcond : (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z)
        · rw [if_pos hcond]
          simp [hp]
        · rw [if_neg hcond]
      rw [hzero]
      simp [hp]
    · have hnn := hpsupp (n : ℝ) hp
      have hbox : ∀ z : GaussianInt, Work.FIPlan.gnorm z = n → z ∈ Work.FITop.boxN Pa :=
        fun z hz => mem_boxN_of_le Pa (by rw [hz]; exact hnn.2)
      have hstep : ∀ z ∈ (Work.FITop.boxN Pa).filter (fun z => Work.FIPlan.gnorm z = n),
          Work.FIArea6.S16CleanSummand Pa chi m p z
            = ((p (n : ℝ) : ℂ) * (ArithmeticFunction.moebius n : ℂ)
                * (Work.FIPlan.gammaTrunc Pa.C n : ℂ))
              * (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z) then
                  Work.FIArea5.S16Hecke.psi chi m z else 0) := by
        intro z hz
        rw [Finset.mem_filter] at hz
        obtain ⟨-, hgn⟩ := hz
        unfold Work.FIArea6.S16CleanSummand
        rw [hgn]
        by_cases hcond : (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z)
        · rw [if_pos hcond, if_pos hcond]
        · rw [if_neg hcond, if_neg hcond, mul_zero]
      have hsum : (∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => Work.FIPlan.gnorm z = n),
            (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z) then
              Work.FIArea5.S16Hecke.psi chi m z else 0))
          = Work.FIArea5.S16Hecke.heckeLam chi m n := by
        rw [heckeLam_eq_sum_boxN_filter Pa chi m n hbox]
        have e2 : ∀ z ∈ (Work.FITop.boxN Pa).filter (fun z => Work.FIPlan.gnorm z = n),
            (if (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z) then
              Work.FIArea5.S16Hecke.psi chi m z else 0)
              = (if Work.FIPlan.IsPrimary z then Work.FIArea5.S16Hecke.psi chi m z else 0) := by
          intro z hz
          rw [Finset.mem_filter] at hz
          obtain ⟨-, hgn⟩ := hz
          have hsp : Work.FITop4.NoSmallPrimes Pa z := by
            rw [noSmallPrimes_iff_nat, hgn]; exact hN
          by_cases hpz : Work.FIPlan.IsPrimary z
          · rw [if_pos ⟨hpz, hsp⟩, if_pos hpz]
          · rw [if_neg (fun h => hpz h.1), if_neg hpz]
        rw [Finset.sum_congr rfl e2, ← Finset.sum_filter]
        apply Finset.sum_congr
        · apply Finset.ext
          intro a
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨hboxa, hgn⟩, hpr⟩
            exact ⟨hboxa, hpr, hgn⟩
          · rintro ⟨hboxa, hpr, hgn⟩
            exact ⟨⟨hboxa, hgn⟩, hpr⟩
        · intro x hx
          rfl
      rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hsum]
      ring
  · rw [if_neg hN]
    apply Finset.sum_eq_zero
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hgn⟩ := hz
    unfold Work.FIArea6.S16CleanSummand
    rw [hgn]
    have hsp : ¬ Work.FITop4.NoSmallPrimes Pa z := by
      rw [noSmallPrimes_iff_nat, hgn]; exact hN
    rw [if_neg (fun h => hsp h.2)]

/-- **The clean §16 box sum regroups by the norm into the Möbius-twisted Hecke sum.** -/
theorem CleanSumEqTsum (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) :
    (∑ z ∈ Work.FITop.boxN Pa, Work.FIArea6.S16CleanSummand Pa chi m p z)
      = Work.FIArea6Hecke.Tsum Pa chi m p := by
  have hbox : ∀ (n : ℕ) (z : GaussianInt), (n : ℝ) ≤ (1 + Pa.θ) * Pa.N →
      Work.FIPlan.gnorm z = n → z ∈ Work.FITop.boxN Pa :=
    fun n z h hz => mem_boxN_of_le Pa (by rw [hz]; exact h)
  rw [Tsum_eq_sum_image Pa chi m p hbox hpsupp]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Work.FITop.boxN Pa)
        (t := (Work.FITop.boxN Pa).image Work.FIPlan.gnorm) (g := Work.FIPlan.gnorm)
        (fun z hz => Finset.mem_image_of_mem _ hz)]
  exact Finset.sum_congr rfl (fun n _ => sum_summand_fiber Pa chi m p hpsupp n)

end

end Work.FIArea6.TauPieces
