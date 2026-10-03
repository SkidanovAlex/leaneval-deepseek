/-
# The class factor of the twist `(|z|² | d)` on the `e`-strata of *FI* §15

Writing `z = e·ρ + i·s = scalePt e w` (`w = ρ + is`), the *twist* `(|z|² | e d')` of the round-6
coefficient is a function of the stratum `e` and of the class of `w` modulo `4d'` alone: with
`a = Im w·(Re w)⁻¹ ∈ [0,4d')` it equals the **class factor** `(e² + a² | d')`.  This is the
identity that lets the round-6 §15 chain factor its kernel with class factor `1`
(`Work.FIArea4.A6psi.pDng6_le_EvarG`); equivalently, the twist `(|z|² | d)` of a pair of an
`e`-stratum is the frozen class factor `(e² + a² | oddPart (d/e))` of that stratum, which is what
`Work.FIArea4.S15red.pdF` (in `pDng_e_le_EvarG`) consumes.

The two ingredients are elementary:

* the `e`-part of the symbol is `1`, because `|z|² = e²ρ² + s² ≡ s² (mod e)` and `(s,e) = 1`
  makes `s` a unit modulo each prime divisor of `e` (this is where `hs` is used);
* the `d'`-part only sees `|z|²` modulo `d'`, and `|z|² ≡ ρ²·(e² + a²) (mod d')` because
  `a ≡ s·ρ⁻¹ (mod 4d')`; the square factor `ρ²` contributes `1` since `(ρ, 4d') = 1`
  (this is where `hc` is used).
-/
import Mathlib
import Submission.Work.FIArea4.S15red.stratumSumE_le_EvarG
import Submission.Work.FIArea7.ReSymbolTwist
import Submission.Work.FIArea7.FIsymbols

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.A6psi

/-! ## Elementary Jacobi tool: the symbol only sees the numerator modulo the denominator -/

/-- Two numerators congruent modulo the denominator have the same Jacobi symbol. -/
private lemma jacobiSym_eq_of_dvd_sub {a b : ℤ} {c : ℕ} (h : (c : ℤ) ∣ a - b) :
    jacobiSym a c = jacobiSym b c := by
  apply jacobiSym.mod_left'
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  exact (Int.dvd_iff_emod_eq_zero).mp h

theorem jacobiSym_gnorm_scalePt_eq_classFactor (e d' : ℕ) (he : 1 ≤ e) (hd' : 1 ≤ d')
    (w : GaussianInt)
    (hc : Nat.Coprime w.re.natAbs (4 * d'))
    (hs : Nat.Coprime w.im.natAbs e) :
    jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w) : ℤ)) (e * d')
      = jacobiSym ((e : ℤ) ^ 2
          + ((((w.im : ZMod (4 * d')) * ((w.re : ZMod (4 * d')))⁻¹).val : ℤ)) ^ 2) d' := by
  classical
  have he0 : e ≠ 0 := by omega
  have hd0 : d' ≠ 0 := by omega
  -- the norm of the scaled point, as an integer
  have hN : (Work.FIPlan.gnorm (Work.FIArea4.scalePt e w) : ℤ)
      = (e : ℤ) ^ 2 * w.re ^ 2 + w.im ^ 2 := by
    rw [Work.FIArea7.norm_eq]
    simp only [Work.FIArea4.scalePt_re, Work.FIArea4.scalePt_im]
    ring
  -- ## the `e`-part of the symbol is `1`
  have hA : jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w) : ℤ)) e = 1 := by
    have hcong : jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w) : ℤ)) e
        = jacobiSym (w.im ^ 2) e :=
      jacobiSym_eq_of_dvd_sub ⟨(e : ℤ) * w.re ^ 2, by rw [hN]; ring⟩
    rw [hcong]
    refine jacobiSym.sq_one' ?_
    rw [Int.gcd_def, Int.natAbs_natCast]
    exact hs
  -- ## the `d'`-part of the symbol sees only the class of `w` modulo `4d'`
  have hB : jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w) : ℤ)) d'
      = jacobiSym ((e : ℤ) ^ 2
          + ((((w.im : ZMod (4 * d')) * ((w.re : ZMod (4 * d')))⁻¹).val : ℤ)) ^ 2) d' := by
    set a : ℤ := (((w.im : ZMod (4 * d')) * ((w.re : ZMod (4 * d')))⁻¹).val : ℤ) with hadef
    haveI : NeZero (4 * d') := ⟨by omega⟩
    -- the class representative satisfies the class congruence modulo `4d'`
    have hcl : (w.im : ZMod (4 * d')) = (a : ZMod (4 * d')) * (w.re : ZMod (4 * d')) := by
      have hval : (a : ZMod (4 * d'))
          = (w.im : ZMod (4 * d')) * (((w.re : ZMod (4 * d'))))⁻¹ := by
        rw [hadef]; push_cast; exact ZMod.natCast_zmod_val _
      rw [hval, mul_assoc,
        ZMod.inv_mul_of_unit _ (Work.FIArea4.isUnit_intCast_zmod' (4 * d') w.re hc), mul_one]
    -- read modulo `d'`: `d' ∣ Im w - a·Re w`
    have hvd : (d' : ℤ) ∣ w.im - a * w.re := by
      have h1 : (4 * d' : ℤ) ∣ a * w.re - w.im :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub w.im (a * w.re) (4 * d')).mp (by
          push_cast; exact hcl)
      have h2 : (d' : ℤ) ∣ (4 * d' : ℤ) := ⟨4, by ring⟩
      have h4 : (d' : ℤ) ∣ -(a * w.re - w.im) := dvd_neg.mpr (h2.trans h1)
      rwa [neg_sub] at h4
    -- `Re w` stays invertible modulo `d'`
    have hg2 : w.re.gcd (d' : ℤ) = 1 := by
      rw [Int.gcd_def, Int.natAbs_natCast]
      exact Nat.Coprime.coprime_dvd_right (dvd_mul_left d' 4) hc
    -- `|z|² ≡ Re w²·(e² + a²) (mod d')`
    have hcong : jacobiSym ((Work.FIPlan.gnorm (Work.FIArea4.scalePt e w) : ℤ)) d'
        = jacobiSym (((e : ℤ) ^ 2 + a ^ 2) * w.re ^ 2) d' := by
      refine jacobiSym_eq_of_dvd_sub ?_
      have hfac : (Work.FIPlan.gnorm (Work.FIArea4.scalePt e w) : ℤ)
            - ((e : ℤ) ^ 2 + a ^ 2) * w.re ^ 2
          = (w.im - a * w.re) * (w.im + a * w.re) := by
        rw [hN]; ring
      rw [hfac]
      exact dvd_mul_of_dvd_left hvd _
    rw [hcong, jacobiSym.mul_left, jacobiSym.sq_one' (a := w.re) (b := d') hg2, mul_one]
  -- ## assembly
  rw [jacobiSym.mul_right' _ he0 hd0, hA, one_mul, hB]

end Work.FIArea4.A6psi
