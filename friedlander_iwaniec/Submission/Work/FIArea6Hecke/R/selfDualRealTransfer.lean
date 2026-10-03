/-
# `Submission.Work.FIArea6Hecke.R.selfDualRealTransfer`

**Every self-dual strict character pair has a real partner with the same Hecke eigenvalues.**

`Work.FIArea6Hecke.R.SelfDual d chi m` says that
`psi_{χ,m}(z) = χ(z)·(z/|z|)^m` satisfies `(psi_{χ,m} z)^2 = 1` for every `z` which is *primary*
and a *unit modulo `4d`* — exactly the values of `z` that the Hecke eigenvalues
`heckeLam chi m n = Σ_{z primary, |z|²=n} psi_{χ,m}(z)` see.

The theorem produces a strict character `χ'` modulo `4d` which is **real valued**,
`star (χ' z) = χ' z` for all `z`, and whose Hecke eigenvalues with weight `0` agree with those of
`(χ, m)`:

  `heckeLam χ' 0 n = heckeLam χ m n`  for all `n`.

The construction (`Work.FIArea6Hecke.R.chiPrime`, see `R/chiPrimeDefs`), is the classical one of
*FI* §16: normalise an element to its *primary* associate before evaluating `χ`,

  `χ' z = χ (primAssoc z)`  for `z` a unit modulo `4d`,   `χ' z = 0`  otherwise.

`SelfDual` forces `m = 0` (`Work.FIArea6Hecke.R.m_eq_zero_of_selfDual`), and then `χ` is `±1` on the
primary units, so `χ'` is real valued there (and `0` elsewhere); on the primary elements
`primAssoc z = z`, so `χ'` agrees with `χ` there and hence has the same Hecke eigenvalues
(`Work.FIArea6Hecke.R.heckeLam_eq_of_primary_agree`).

The one arithmetic point is that `χ'` is again a character modulo `4d`.  Multiplicativity is the
multiplicativity of `primAssoc` on odd elements (`Work.FIArea6Hecke.R.primAssoc_mul_odd`); the
delicate axiom is *periodicity*: if `z ≡ w (mod 4d)` are units modulo `4d`, then
`χ (primAssoc z) = χ (primAssoc w)`.  For that it suffices to know that the primary associate is
equivariant for the four units, i.e. that the class of an element modulo `4` determines the unit
correction — equivalently that `IsPrimary` depends only on the class modulo `4`
(`IsPrimary z ⟺ Odd z.re ∧ Even z.im ∧ z.im ≡ z.re - 1 (mod 4)`), which is the lemma
`sdt_isPrimary_of_dvd_sub_four` below.  Writing `primAssoc z = v·z` with `v ∈ μ₄`, the same `v`
normalises `w` (because `4 ∣ 4d ∣ z - w`), whence `primAssoc z - primAssoc w = v·(z - w)` is
divisible by `4d` and `χ`'s periodicity applies.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeStripLogDerivConductor
import Submission.Work.FIArea6Hecke.R.m_eq_zero_of_selfDual
import Submission.Work.FIArea6Hecke.R.chiPrimeDefs
import Submission.Work.FIArea6Hecke.R.chiPrimeAgree
import Submission.Work.FIArea6Hecke.R.LamOneNeZeroDefs
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core
import Submission.Work.FIArea4.GaussMoebiusCore
import Submission.Work.FIArea6Hecke.R.exists_realCharacter_agreeing_on_primary

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Work.FIPlan

noncomputable section

namespace SelfDualTransfer

/-- **`IsPrimary` depends only on the class modulo `4`**: the three defining conditions
(`z.re` odd, `z.im` even, `z.im ≡ z.re - 1 mod 4`) are all conditions on `z` modulo `4`. -/
lemma sdt_isPrimary_of_dvd_sub_four {a b : GaussianInt} (h : (4 : GaussianInt) ∣ (a - b))
    (ha : IsPrimary a) : IsPrimary b := by
  have h4 := (Zsqrtd.intCast_dvd (d := -1) (4 : ℤ) (a - b)).mp h
  rw [Zsqrtd.re_sub, Zsqrtd.im_sub] at h4
  obtain ⟨hre4, him4⟩ := h4
  have hrem : a.re ≡ b.re [ZMOD 4] :=
    Int.modEq_iff_dvd.mpr (by rw [← neg_sub]; exact dvd_neg.mpr hre4)
  have himm : a.im ≡ b.im [ZMOD 4] :=
    Int.modEq_iff_dvd.mpr (by rw [← neg_sub]; exact dvd_neg.mpr him4)
  have hre_even : Even (a.re - b.re) := by
    obtain ⟨k, hk⟩ := hre4; exact ⟨2 * k, by omega⟩
  have him_even : Even (a.im - b.im) := by
    obtain ⟨k, hk⟩ := him4; exact ⟨2 * k, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · have hb : b.re = a.re - (a.re - b.re) := by ring
    rw [hb]; exact ha.1.sub_even hre_even
  · have hb : b.im = a.im - (a.im - b.im) := by ring
    rw [hb]; exact ha.2.1.sub him_even
  · exact himm.symm.trans (ha.2.2.trans (hrem.sub (Int.ModEq.refl 1)))

/-- **A unit modulo `4d` is odd** (`d ≥ 1`): `IsUnitMod4d d z` says that `|z|²` is coprime to `4d`,
in particular odd. -/
lemma sdt_odd_gnorm_of_isUnitMod4d {d : ℕ} [NeZero (4 * d)] {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z) : Odd (gnorm z) := by
  have hcop : Nat.Coprime (gnorm z) (4 * d) :=
    (Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime z).mp hz
  rw [Nat.coprime_iff_gcd_eq_one] at hcop
  rw [← Nat.not_even_iff_odd]
  intro hev
  have h2 : (2 : ℕ) ∣ gnorm z := by
    rcases hev with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have h2' : (2 : ℕ) ∣ 4 * d := ⟨2 * d, by ring⟩
  have hg : (2 : ℕ) ∣ Nat.gcd (gnorm z) (4 * d) := Nat.dvd_gcd h2 h2'
  rw [hcop] at hg
  omega

/-- **The unit connecting `z` with its primary associate**: if `z` is odd then
`primAssoc z = v·z` for some unit `v ∈ ℤ[i]ˣ`. -/
lemma sdt_exists_unit_mul_primAssoc {z : GaussianInt} (hz : z ≠ 0) (hodd : Odd (gnorm z)) :
    ∃ v : GaussianIntˣ, (↑v : GaussianInt) * z = Work.FIArea4.primAssoc z := by
  obtain ⟨u, hu⟩ := Work.FIArea4.primAssoc_associated hz hodd
  refine ⟨u⁻¹, ?_⟩
  have h' : Work.FIArea4.primAssoc z = z * (↑u⁻¹ : GaussianInt) := by
    have h1 := congrArg (fun t : GaussianInt => t * (↑u⁻¹ : GaussianInt)) hu
    simpa [mul_assoc] using h1
  rw [mul_comm]; exact h'.symm

/-- **Periodicity of `z ↦ χ (primAssoc z)` on the units modulo `4d`.**  If `z ≡ w (mod 4d)` are
both units modulo `4d`, their primary associates differ by a multiple of `4d`, so `χ`, being
periodic modulo `4d`, takes the same value at them. -/
lemma sdt_chi_primAssoc_periodic {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hper : ∀ z w : GaussianInt, ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ (z - w) → chi z = chi w)
    {z w : GaussianInt} (hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z)
    (hw : Work.FIArea5.S16Hecke.IsUnitMod4d d w)
    (h : ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ (z - w)) :
    chi (Work.FIArea4.primAssoc z) = chi (Work.FIArea4.primAssoc w) := by
  haveI : NeZero (4 * d) := ⟨by omega⟩
  have hoddz : Odd (gnorm z) := sdt_odd_gnorm_of_isUnitMod4d hz
  have hoddw : Odd (gnorm w) := sdt_odd_gnorm_of_isUnitMod4d hw
  have hz0 : z ≠ 0 := ne_zero_of_odd_gnorm hoddz
  have hw0 : w ≠ 0 := ne_zero_of_odd_gnorm hoddw
  obtain ⟨v, hv⟩ := sdt_exists_unit_mul_primAssoc hz0 hoddz
  have h4 : (4 : GaussianInt) ∣ (z - w) := by
    obtain ⟨k, hk⟩ := h
    refine ⟨(d : GaussianInt) * k, ?_⟩
    rw [hk]; push_cast; ring
  have h4' : (4 : GaussianInt) ∣ (Work.FIArea4.primAssoc z - (↑v : GaussianInt) * w) := by
    obtain ⟨k, hk⟩ := h4
    refine ⟨(↑v : GaussianInt) * k, ?_⟩
    rw [← hv]
    have h1 : (↑v : GaussianInt) * z - ↑v * w = ↑v * (z - w) := by ring
    rw [h1, hk]; ring
  have hprim : IsPrimary ((↑v : GaussianInt) * w) :=
    sdt_isPrimary_of_dvd_sub_four h4' (Work.FIArea4.primAssoc_primary hz0 hoddz)
  have hassoc : Associated ((↑v : GaussianInt) * w) w :=
    Commons.NumberTheory.GaussianInt.associated_of_isUnit_mul_left (Units.isUnit v)
  have hvw : (↑v : GaussianInt) * w = Work.FIArea4.primAssoc w :=
    primAssoc_unique_of_odd hw0 hoddw hassoc hprim
  refine hper _ _ ?_
  rw [← hv, ← hvw]
  obtain ⟨k, hk⟩ := h
  refine ⟨(↑v : GaussianInt) * k, ?_⟩
  have h1 : (↑v : GaussianInt) * z - ↑v * w = ↑v * (z - w) := by ring
  rw [h1, hk]; ring

/-- **`chiPrime d χ` is a character modulo `4d`** (in the sense of `Work.FITop3.IsCharMod4d`):
`χ' 1 = 1`, `χ'` multiplicative, `‖χ'‖ ≤ 1`, periodic modulo `4d` and vanishing on multiples of
`4d`. -/
theorem sdt_chiPrime_isCharMod4d {d : ℕ} {chi : GaussianInt → ℂ} (hd : 1 ≤ d)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    Work.FITop3.IsCharMod4d d (chiPrime d chi) := by
  haveI : NeZero (4 * d) := ⟨by omega⟩
  obtain ⟨⟨h1, hmul, hb, hper, hzero⟩, hoff⟩ := hchi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [chiPrime_of_unit (Work.FIArea6Hecke.GaussUnit.isUnitMod4d_one (d := d)),
      Work.FIArea4.primAssoc_eq_self Work.FIArea5.S16Hecke.isPrimary_one, h1]
  · intro z w
    by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
    · by_cases hw : Work.FIArea5.S16Hecke.IsUnitMod4d d w
      · rw [chiPrime_of_unit (Work.FIArea6Hecke.GaussUnit.isUnitMod4d_mul hz hw),
          chiPrime_of_unit hz, chiPrime_of_unit hw,
          primAssoc_mul_odd (sdt_odd_gnorm_of_isUnitMod4d hz) (sdt_odd_gnorm_of_isUnitMod4d hw)]
        exact hmul _ _
      · rw [chiPrime_of_not_unit hw, mul_zero,
          chiPrime_of_not_unit (fun h => hw (Work.FIArea6Hecke.GaussUnit.isUnitMod4d_of_mul_right h))]
    · rw [chiPrime_of_not_unit hz, zero_mul,
        chiPrime_of_not_unit (fun h => hz (Work.FIArea6Hecke.GaussUnit.isUnitMod4d_of_mul_left h))]
  · intro z
    by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
    · rw [chiPrime_of_unit hz]; exact hb (Work.FIArea4.primAssoc z)
    · rw [chiPrime_of_not_unit hz]; simp
  · intro z w hzw
    by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
    · have hw : Work.FIArea5.S16Hecke.IsUnitMod4d d w :=
        (Work.FIArea6Hecke.GaussUnit.isUnitMod4d_congr hzw).mp hz
      rw [chiPrime_of_unit hz, chiPrime_of_unit hw]
      exact sdt_chi_primAssoc_periodic hd hper hz hw hzw
    · have hw : ¬ Work.FIArea5.S16Hecke.IsUnitMod4d d w :=
        fun h => hz ((Work.FIArea6Hecke.GaussUnit.isUnitMod4d_congr hzw).mpr h)
      rw [chiPrime_of_not_unit hz, chiPrime_of_not_unit hw]
  · intro z hz
    exact chiPrime_of_not_unit (Work.FIArea6Hecke.GaussUnit.not_isUnitMod4d_of_dvd hd hz)

/-- **`chiPrime d χ` is real valued** when `(χ, m)` is self-dual.  On a unit `z` the value is
`χ (primAssoc z)` with `primAssoc z` primary; if that is again a unit modulo `4d` then self-duality
(and `m = 0`, forced by `SelfDual`) makes it `±1`, otherwise `χ` vanishes there by strictness. -/
theorem sdt_chiPrime_star {d : ℕ} {chi : GaussianInt → ℂ} {m : ℤ}
    (hd : 1 ≤ d) (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hsd : SelfDual d chi m) (hm : m = 0) :
    ∀ z : GaussianInt, star (chiPrime d chi z) = chiPrime d chi z := by
  haveI : NeZero (4 * d) := ⟨by omega⟩
  intro z
  by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · rw [chiPrime_of_unit hz]
    have hodd : Odd (gnorm z) := sdt_odd_gnorm_of_isUnitMod4d hz
    have hz0 : z ≠ 0 := ne_zero_of_odd_gnorm hodd
    have hp : IsPrimary (Work.FIArea4.primAssoc z) := Work.FIArea4.primAssoc_primary hz0 hodd
    by_cases hu : Work.FIArea5.S16Hecke.IsUnitMod4d d (Work.FIArea4.primAssoc z)
    · have h2 := hsd _ hp hu
      rw [hm] at h2
      have hpsi : Work.FIArea5.S16Hecke.psi chi 0 (Work.FIArea4.primAssoc z)
          = chi (Work.FIArea4.primAssoc z) := by
        rw [Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one]
      rw [hpsi] at h2
      rcases sq_eq_one_iff.mp h2 with h' | h' <;> rw [h'] <;> simp
    · rw [hchi.2 _ hu]; simp
  · rw [chiPrime_of_not_unit hz]; simp

end SelfDualTransfer

/-- **Every self-dual strict character pair has a real partner with the same Hecke eigenvalues.**
The witness is `Work.FIArea6Hecke.R.chiPrime d chi`. -/
theorem selfDualRealTransfer {d : ℕ} {chi : GaussianInt → ℂ} {m : ℤ}
    (hd : 1 ≤ d) (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hsd : Work.FIArea6Hecke.R.SelfDual d chi m) :
    ∃ chi' : GaussianInt → ℂ,
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi' ∧
      (∀ z : GaussianInt, star (chi' z) = chi' z) ∧
      (∀ n : ℕ, Work.FIArea5.S16Hecke.heckeLam chi' 0 n = Work.FIArea5.S16Hecke.heckeLam chi m n) := by
  refine ⟨chiPrime d chi,
    ⟨SelfDualTransfer.sdt_chiPrime_isCharMod4d hd hchi, fun z hz => chiPrime_of_not_unit hz⟩,
    SelfDualTransfer.sdt_chiPrime_star hd hchi hsd (m_eq_zero_of_selfDual hd hchi hsd), ?_⟩
  intro n
  rw [m_eq_zero_of_selfDual hd hchi hsd]
  refine heckeLam_eq_of_primary_agree (chi := chiPrime d chi) (chi' := chi) (k := 0) ?_ n
  intro z hzp
  by_cases hzu : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · exact chiPrime_eq_chi_of_primary hzp hzu
  · rw [chiPrime_of_not_unit hzu, hchi.2 z hzu]

end

end Work.FIArea6Hecke.R
