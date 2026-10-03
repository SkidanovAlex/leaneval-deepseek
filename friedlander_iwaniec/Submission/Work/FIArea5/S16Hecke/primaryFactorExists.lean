import Mathlib
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Commons.NumberTheory.GaussianInt.factor_exists_of_norm_mul
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea5.S16Hecke

/-- **A primary Gaussian integer factors, along coprime factors of its norm, into primary
factors.**  If `z` is primary and `gnorm z = m * n` with `m`, `n` coprime and positive, then
`z = z₁ z₂` with `z₁`, `z₂` primary and `gnorm z₁ = m`, `gnorm z₂ = n`.

The norm is multiplicative and `z` primary forces `gnorm z` (hence `m` and `n`) odd, so every
`z` of norm `m * n` splits as `w * z₂` with `gnorm w = m`, `gnorm z₂ = n`; replacing `w` by its
(unique) primary associate `z₁ = w * ε` only multiplies `z₂` by the unit `ε⁻¹`, and the primary
condition on `z = z₁ · (ε⁻¹ z₂)` together with that on `z₁` propagates to the second factor by
cancellation. -/
theorem primaryFactorExists {z : GaussianInt} {m n : ℕ} (hz : Work.FIPlan.IsPrimary z)
    (hgn : Work.FIPlan.gnorm z = m * n) (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n) :
    ∃ z1 z2 : GaussianInt, Work.FIPlan.IsPrimary z1 ∧ Work.FIPlan.IsPrimary z2 ∧
      Work.FIPlan.gnorm z1 = m ∧ Work.FIPlan.gnorm z2 = n ∧ z = z1 * z2 := by
  have hmodd : Odd m :=
    (Nat.odd_mul.mp (by rw [← hgn]; exact isPrimary_odd_gnorm hz)).1
  -- split `z` along the coprime factors `m`, `n` of its norm
  obtain ⟨w, z₂, hzw, hw, hz₂⟩ :=
    Commons.NumberTheory.GaussianInt.factor_exists_of_norm_mul hm hn hcop z hgn
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp only [Zsqrtd.norm_zero, Int.natAbs_zero] at hw
    omega
  -- replace `w` by its primary associate `w'`
  obtain ⟨w', ⟨hassoc, hw're, hw'im, hw'c⟩, -⟩ :=
    Commons.NumberTheory.GaussianInt.primary_associate_exists_unique hw0 (by rw [hw]; exact hmodd)
  have hprim1 : Work.FIPlan.IsPrimary w' :=
    ⟨hw're, hw'im, (ZMod.intCast_eq_intCast_iff w'.im (w'.re - 1) 4).mp (by
      push_cast
      exact hw'c)⟩
  have hgw' : Work.FIPlan.gnorm w' = m := by
    have h := Zsqrtd.norm_eq_of_associated (d := -1) (by norm_num) hassoc
    show w'.norm.natAbs = m
    rw [h]
    exact hw
  obtain ⟨u, hu⟩ := hassoc
  -- `z = w' * (u * z₂)`, and `u * z₂` is the second factor
  have hz_eq : z = w' * ((↑u : GaussianInt) * z₂) := by
    rw [hzw, ← hu, mul_assoc]
  have hprim2 : Work.FIPlan.IsPrimary ((↑u : GaussianInt) * z₂) :=
    isPrimary_of_isPrimary_mul_right hprim1 (by rw [← hz_eq]; exact hz)
  have hgz2' : Work.FIPlan.gnorm ((↑u : GaussianInt) * z₂) = n := by
    show ((↑u : GaussianInt) * z₂).norm.natAbs = n
    rw [Zsqrtd.norm_mul, Int.natAbs_mul,
      Commons.NumberTheory.GaussianInt.isUnit_norm_natAbs u.isUnit, one_mul]
    exact hz₂
  exact ⟨w', (↑u : GaussianInt) * z₂, hprim1, hprim2, hgw', hgz2', hz_eq⟩

end Work.FIArea5.S16Hecke
