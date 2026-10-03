import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core
import Submission.Work.FIArea7.mk_injOn_primarySet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Road

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Counting the primary elements of a given norm

These two lemmas are the arithmetic content of the target: for odd `n` the number of *primary*
Gaussian integers of norm `n` equals `A n`, the number of associate classes of Gaussian integers of
norm `n` (`Commons.NumberTheory.GaussianInt.A`), and `A n` is the divisor sum `Σ_{e ∣ n} χ₄(e)`.
-/

/-- `A n = Σ_{e ∣ n} χ₄(e)`, the divisor-sum form of the number of associate classes: both sides
equal `r₂(n)/4` (`two_squares_repr_count_eq_sum_chi4`, `targetF_card_eq_four_mul_A`). -/
lemma A_cast_eq_sum_chi4 (n : ℕ) (hn : 1 ≤ n) :
    (Commons.NumberTheory.GaussianInt.A n : ℤ) =
      ∑ e ∈ n.divisors,
        (if e % 4 = 1 then (1 : ℤ) else if e % 4 = 3 then (-1 : ℤ) else 0) := by
  have h1 : ((Commons.NumberTheory.GaussianInt.targetF n).card : ℤ)
      = 4 * (Commons.NumberTheory.GaussianInt.A n : ℤ) := by
    rw [Commons.NumberTheory.GaussianInt.targetF_card_eq_four_mul_A n hn]
    push_cast
    ring
  have h2 : ((Commons.NumberTheory.GaussianInt.targetF n).card : ℤ)
      = 4 * ∑ e ∈ n.divisors,
          (if e % 4 = 1 then (1 : ℤ) else if e % 4 = 3 then (-1 : ℤ) else 0) :=
    Commons.NumberTheory.GaussianInt.two_squares_repr_count_eq_sum_chi4 n hn
  rw [h1] at h2
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h2

/-- For **odd** `n` the number of primary Gaussian integers of norm `n` is the number `A n` of
associate classes of Gaussian integers of norm `n`: passing to the associate class is injective
(`Work.FIArea7.mk_injOn_primarySet`, two associated primary elements are equal) and surjective
(every `z ≠ 0` of odd norm has a primary associate, `primary_associate_exists_unique`). -/
lemma primarySet_card_eq_A (n : ℕ) (hodd : Odd n) :
    (Work.FIArea7.primarySet n).card = Commons.NumberTheory.GaussianInt.A n := by
  have hn : 1 ≤ n := by rcases hodd with ⟨k, hk⟩; omega
  have himg : (Associates.mk '' ((Work.FIArea7.primarySet n) : Set GaussianInt))
      = Commons.NumberTheory.GaussianInt.Xset n := by
    ext κ
    constructor
    · rintro ⟨z, hz, rfl⟩
      show Commons.NumberTheory.GaussianInt.nc (Associates.mk z) = n
      rw [Commons.NumberTheory.GaussianInt.nc_mk]
      exact (Work.FIArea7.mem_primarySet.mp hz).2
    · intro hκ
      rw [Commons.NumberTheory.GaussianInt.Xset_eq_image n hn, Set.mem_image] at hκ
      obtain ⟨z, hz, rfl⟩ := hκ
      have hzn : Work.FIPlan.gnorm z = n :=
        (Commons.NumberTheory.GaussianInt.mem_elemF hn z).mp hz
      have hz0 : z ≠ 0 := by
        intro h
        rw [h] at hzn
        simp [Work.FIPlan.gnorm] at hzn
        omega
      obtain ⟨w, hw, -⟩ :=
        Commons.NumberTheory.GaussianInt.primary_associate_exists_unique hz0
          (by rw [show z.norm.natAbs = n from hzn]; exact hodd)
      have hwre : Odd w.re := hw.2.1
      have hwim : Even w.im := hw.2.2.1
      have hwc : (w.im : ZMod 4) = (w.re : ZMod 4) - 1 := hw.2.2.2
      have hwprim : Work.FIPlan.IsPrimary w :=
        (Work.FIArea7.isPrimary_iff_zmod4 w).mpr ⟨hwre, hwim, hwc⟩
      have hmk : Associates.mk w = Associates.mk z :=
        Associates.mk_eq_mk_iff_associated.mpr hw.1
      have hnc : w.norm.natAbs = z.norm.natAbs := by
        simpa using congrArg Commons.NumberTheory.GaussianInt.nc hmk
      have hwgn : Work.FIPlan.gnorm w = n := by
        show w.norm.natAbs = n
        rw [hnc, show z.norm.natAbs = n from hzn]
      exact ⟨w, (Work.FIArea7.mem_primarySet).mpr ⟨hwprim, hwgn⟩, hmk⟩
  have hcard : (Work.FIArea7.primarySet n).card
      = (Associates.mk '' ((Work.FIArea7.primarySet n) : Set GaussianInt)).ncard := by
    rw [Set.InjOn.ncard_image (Work.FIArea7.mk_injOn_primarySet n), Set.ncard_coe_finset]
  rw [hcard, himg, Commons.NumberTheory.GaussianInt.Xset_ncard n hn]

/-- The same count, in the value group `ℂ` in which the Hecke eigenvalue lives. -/
lemma primCount_cast_eq_sum_chi4 (n : ℕ) (hodd : Odd n) :
    ((Work.FIArea7.primarySet n).card : ℂ) =
      ∑ e ∈ n.divisors,
        (if e % 4 = 1 then (1 : ℂ) else if e % 4 = 3 then (-1 : ℂ) else 0) := by
  have hn : 1 ≤ n := by rcases hodd with ⟨k, hk⟩; omega
  rw [primarySet_card_eq_A n hodd]
  have hA := A_cast_eq_sum_chi4 n hn
  rw [show (Commons.NumberTheory.GaussianInt.A n : ℂ)
      = ((Commons.NumberTheory.GaussianInt.A n : ℤ) : ℂ) from (Int.cast_natCast _).symm, hA]
  push_cast
  rfl

/-! ## The main theorem -/

/-- **The Hecke eigenvalue in the *trivial Größencharacter* case.**  If `ψ_m(z) = χ(z)·(z/|z|)^m`
equals `1` for every *primary* unit `z` mod `4d` (the case in which the Hecke `L`-function is
`ζ_{ℚ(i)}` with finitely many Euler factors removed, so that the inverse bound
`HeckeLcontInvBoundAll` is vacuous — no entire completion exists), then the Hecke eigenvalue
`λ_m(n) = Σ_{|z|²=n, z primary} ψ_m(z)` equals `Σ_{e | n} χ_4(e)` (the number of ideals of `ℤ[i]`
of norm `n`) when `(n, 4d) = 1`, and `0` otherwise.

The count `Σ_{e|n}χ_4(e)` is written as `Σ_{e | n}(1 if e ≡ 1, -1 if e ≡ 3, 0 mod 4)`, the form of
`Commons.NumberTheory.GaussianInt.two_squares_repr_count_eq_sum_chi4`
(`Submission/Commons/NumberTheory/GaussianInt/two_squares_repr_count_eq_sum_chi4.lean`,
`r_2(n) = 4Σ_{d|n}χ_4(d)`); the passage from the `r_2`-count to primary elements is
`primary_associate_exists_unique` (same directory: each nonzero class modulo units has exactly one
primary representative, so the number of primary `z` of norm `n` is `r_2(n)/4`).  For `(n,4d) > 1`
every `z` with `|z|² = n` shares a Gaussian prime with `4d`, hence is not a unit mod `4d`, and
`IsCharMod4dStrict` forces `χ z = 0`. -/
theorem HeckeLamTrivialPsi (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (htriv : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → Work.FIArea5.S16Hecke.psi chi m z = 1) (n : ℕ) :
    Work.FIArea5.S16Hecke.heckeLam chi m n
      = if Nat.Coprime n (4 * d) then
          ((∑ e ∈ n.divisors,
            (if e % 4 = 1 then (1 : ℂ) else if e % 4 = 3 then (-1 : ℂ) else 0)))
        else 0 := by
  classical
  haveI : NeZero (4 * d) := ⟨by omega⟩
  rw [Work.FIArea5.S16Hecke.heckeLam,
    show (Work.FIPlan.gBox (n : ℤ)).filter
        (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n)
        = Work.FIArea7.primarySet n from rfl]
  by_cases hcop : Nat.Coprime n (4 * d)
  · rw [if_pos hcop]
    have hodd : Odd n :=
      (Nat.Coprime.of_dvd_right (show 2 ∣ 4 * d from ⟨2 * d, by ring⟩) hcop).odd_of_right
    have hterm : ∀ z ∈ Work.FIArea7.primarySet n, Work.FIArea5.S16Hecke.psi chi m z = 1 := by
      intro z hz
      obtain ⟨hprim, hgn⟩ := Work.FIArea7.mem_primarySet.mp hz
      refine htriv z hprim ?_
      rw [Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime, hgn]
      exact hcop
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact primCount_cast_eq_sum_chi4 n hodd
  · rw [if_neg hcop]
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨hprim, hgn⟩ := Work.FIArea7.mem_primarySet.mp hz
    have hnot : ¬ Work.FIArea5.S16Hecke.IsUnitMod4d d z := by
      intro hu
      rw [Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime, hgn] at hu
      exact hcop hu
    rw [Work.FIArea5.S16Hecke.psi, hchi.2 z hnot, zero_mul]

end

end Work.FIArea6Road
