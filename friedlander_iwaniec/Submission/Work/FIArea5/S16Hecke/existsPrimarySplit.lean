/-
# `Submission.Work.FIArea5.S16Hecke.existsPrimarySplit`

For a rational prime `p ≡ 1 (mod 4)` there is a **primary** Gaussian integer `π` of norm `p`
which is irreducible (i.e. a Gaussian prime over `p`) and which is not associated to its
conjugate `π̄ = star π`.

The construction is the classical one:

* Fermat's two-squares theorem (`Nat.Prime.sq_add_sq`) gives `p = a² + b²`, so
  `z₀ = a + b i` has norm `p`, hence is irreducible;
* `Commons.NumberTheory.GaussianInt.primary_associate_exists_unique` produces the (unique)
  primary associate `π` of `z₀` — the element `≡ 1 (mod 1 + i)` normalisation;
* `π` is still irreducible and of norm `p` because these properties only depend on the
  associate class, and it is not associated to `π̄` because `z₀` is not associated to `z₀̄`
  (`Commons.NumberTheory.GaussianInt.mk_ne_mk_star`: for `p ≡ 1 (mod 4)` the two prime
  factors of `p` in `ℤ[i]` are non-associate) and conjugation preserves associate classes.

This is the split-prime input to the local recursion `Submission.Work.FIArea5.S16Hecke.splitPrimaryClass`.
-/
import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_irred_norm_prime
import Submission.Work.FIPlan.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Work.FIPlan

/-- `gnorm z = |z|²` is multiplicative. -/
private theorem gnorm_mul_aux (z w : GaussianInt) : gnorm (z * w) = gnorm z * gnorm w := by
  simp only [gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- Conjugation (`star`) maps associated elements to associated elements: it is the ring
endomorphism `starRingEnd` of `ℤ[i]`, so `Associated.map` applies. -/
private theorem mk_star_eq_of_associated {z w : GaussianInt} (h : Associated z w) :
    Associates.mk (star z) = Associates.mk (star w) := by
  have h' : Associated ((starRingEnd GaussianInt) z) ((starRingEnd GaussianInt) w) :=
    Associated.map (starRingEnd GaussianInt) h
  rw [starRingEnd_apply, starRingEnd_apply] at h'
  exact Associates.mk_eq_mk_iff_associated.mpr h'

theorem existsPrimarySplit (p : ℕ) (hp : p.Prime) (h1 : p % 4 = 1) :
    ∃ π : GaussianInt, Work.FIPlan.IsPrimary π ∧ Work.FIPlan.gnorm π = p ∧
      Irreducible π ∧ ¬ Associated π (star π) := by
  have hne3 : p % 4 ≠ 3 := by omega
  have hp2 : p ≠ 2 := by omega
  -- Fermat's two-squares theorem: `p = a ^ 2 + b ^ 2`.
  obtain ⟨a, b, hab⟩ := @Nat.Prime.sq_add_sq p ⟨hp⟩ hne3
  set z0 : GaussianInt := ⟨(a : ℤ), (b : ℤ)⟩ with hz0
  have hz0re : z0.re = (a : ℤ) := by rw [hz0]
  have hz0im : z0.im = (b : ℤ) := by rw [hz0]
  have hnorm_z0 : z0.norm.natAbs = p := by
    rw [Commons.NumberTheory.GaussianInt.norm_natAbs_eq_iff, hz0re, hz0im]
    exact_mod_cast hab
  have hgn0 : gnorm z0 = p := hnorm_z0
  have hz0ne : z0 ≠ 0 := by
    intro h
    rw [h] at hnorm_z0
    simp at hnorm_z0
    exact hp.ne_zero hnorm_z0.symm
  have hodd : Odd z0.norm.natAbs := by
    rw [hnorm_z0]
    exact hp.odd_of_ne_two hp2
  -- the primary associate of `z0`
  obtain ⟨w, ⟨hwassoc, hwre, hwe, hwc⟩, _⟩ :=
    Commons.NumberTheory.GaussianInt.primary_associate_exists_unique hz0ne hodd
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · -- `IsPrimary w`
    refine ⟨hwre, hwe, ?_⟩
    have hcast : ((w.im : ℤ) : ZMod 4) = (((w.re - 1 : ℤ)) : ZMod 4) := by
      rw [hwc]; push_cast; ring
    exact (ZMod.intCast_eq_intCast_iff w.im (w.re - 1) 4).mp hcast
  · -- `gnorm w = p`
    have hcw : gnorm z0 = gnorm w := by
      obtain ⟨c, hc⟩ := hwassoc
      have hc1 : gnorm (↑c : GaussianInt) = 1 := Zsqrtd.norm_eq_one_iff.mpr (Units.isUnit c)
      have h2 : gnorm z0 = gnorm w * gnorm (↑c : GaussianInt) := by rw [← hc, gnorm_mul_aux]
      rw [hc1, mul_one] at h2
      exact h2
    rw [← hcw]
    exact hgn0
  · -- `Irreducible w`
    exact (Associated.irreducible_iff hwassoc).mpr
      (Commons.NumberTheory.GaussianInt.irreducible_of_norm_natAbs_eq_prime hp hnorm_z0)
  · -- `¬ Associated w (star w)`
    intro hws
    have hA : Associates.mk w = Associates.mk z0 :=
      Associates.mk_eq_mk_iff_associated.mpr hwassoc
    have hB : Associates.mk (star w) = Associates.mk (star z0) :=
      mk_star_eq_of_associated hwassoc
    have hC : Associates.mk w = Associates.mk (star w) :=
      Associates.mk_eq_mk_iff_associated.mpr hws
    exact (Commons.NumberTheory.GaussianInt.mk_ne_mk_star hp h1 hab)
      (hA.symm.trans (hC.trans hB))

end Work.FIArea5.S16Hecke
