import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea2.G0_fix
import Submission.Work.FIArea2.G0_defect
import Submission.Work.FIArea2.Cnt_eq_Nsol
import Submission.Work.FIArea2.Nsol_eq_two_sum_jacobi
import Submission.Work.FIArea2.coprime_gnorm_absDelta
import Submission.Work.FIArea2.coprime_re_absDelta
import Submission.Work.FIArea2.coprime_residue_absDelta
import Submission.Work.FIArea2.eight_dvd_absDelta_of_congr
import Submission.Work.FIArea2.a_mod_eight
import Submission.Work.FIArea7.ReSymbolTwist

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `G₀ = 2 Σ_{4d|Δ} (φ(d)/d)·(z₂/z₁|d)` with *FI*'s ratio symbol

The corrected kernel of `Submission.Work.FITop4.Defs6` is the count (6.12),
`G0 = G0fix = Cnt/|Δ|` (`Work.FIArea2.G0fix`).  Its (8.16) evaluation is *FI*'s Lemma 8.4:

  `G₀(z₁,z₂) = 2 Σ_{4d|Δ} (φ(d)/d)(z₂/z₁|d)`,

where `(z₂/z₁|d)` is the Jacobi symbol of the *rational* residue (6.6) of the Gaussian ratio
`z₂/z₁`, i.e. of `Re(z̄₁z₂)·|z₁|²⁻¹ (mod d)` — this is `Work.FIArea7.ratioSym`.  The frozen round-4
symbol used `(Re(z̄₁z₂)|d)` instead, which differs by the quadratic character `(|z₁|²|d)`
(`Work.FIArea7.jacobiSym_re_eq_ratioSym_mul`).

`Work.FIArea2.Cnt_eq_two_sum_of_primitive` already proves the (8.16) sum for an *arbitrary*
residue `a` of `z₂/z₁` modulo `|Δ|`,

  `Cnt z₁ z₂ = |Δ|·2 Σ_{4d|Δ}(φ(d)/d)(a/d)`.

The lemma below is the remaining dictionary: the canonical residue that `ratioSym` writes down
term-by-term is the *same* residue, so the two sums coincide.  It is the identity the round-6
reduction needs in order to state `T(β)`, `D₀` and the three cuts (10.13), (10.15)–(10.17) with
**one** symbol, `ratioSym`, as the lead's addendum requires.
-/

namespace Work.FITop4.Red6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

set_option linter.style.haveILetI false

noncomputable section

/-- **`SameClass8` is the congruence `z₂ ≡ z₁ (mod 8)` in `ℤ[i]`.**  The class of (5.7) is the
pair `(Re z mod 8, Im z mod 8)`; two points of it differ by a multiple of `8` in each coordinate,
i.e. by `8m` in `ℤ[i]`.  This is the hypothesis `z₂ − z₁ = 8m` of `eight_dvd_absDelta_of_congr`. -/
theorem exists_eq_eight_mul_of_sameClass8 {z1 z2 : GaussianInt}
    (hcl : Work.FITop4.SameClass8 z1 z2) :
    ∃ m : GaussianInt, z2 - z1 = 8 * m := by
  have h1' : (z1.re : ZMod 8) = (z2.re : ZMod 8) := by
    have := congrArg Prod.fst hcl
    simpa [Work.FITop4.SameClass8, Work.FITop4.cls8] using this
  have h2' : (z1.im : ZMod 8) = (z2.im : ZMod 8) := by
    have := congrArg Prod.snd hcl
    simpa [Work.FITop4.SameClass8, Work.FITop4.cls8] using this
  have hre : (8 : ℤ) ∣ z2.re - z1.re :=
    Int.modEq_iff_dvd.mp ((ZMod.intCast_eq_intCast_iff _ _ 8).mp h1')
  have him : (8 : ℤ) ∣ z2.im - z1.im :=
    Int.modEq_iff_dvd.mp ((ZMod.intCast_eq_intCast_iff _ _ 8).mp h2')
  obtain ⟨p, hp⟩ := hre
  obtain ⟨q, hq⟩ := him
  exact ⟨⟨p, q⟩, by ext <;> simp [hp, hq]⟩

/-- **The residue (6.6) has a canonical representative whose numerator is `Re(z̄₁z₂)`.**  For
`(|z₁|²,|Δ|) = 1` the element `a = Re(z̄₁z₂)·|z₁|²⁻¹` of `ℤ/|Δ|` satisfies

  `a·|z₁|² ≡ Re(z̄₁z₂) (mod |Δ|)`

with `a` the canonical representative in `{0,…,|Δ|−1}`.  This is the input `ha` of
`Cnt_eq_two_sum_of_primitive` (the residue of `z₂/z₁` of (6.6)). -/
theorem exists_residue_absDelta {z1 z2 : GaussianInt} (hD : Work.FIPlan.absDelta z1 z2 ≠ 0)
    (hcop : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2)) :
    ∃ a : ℕ, (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)] := by
  haveI : NeZero (Work.FIPlan.absDelta z1 z2) := ⟨hD⟩
  refine ⟨((((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) *
      ((Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)))⁻¹).val), ?_⟩
  have hunit : IsUnit ((Work.FIPlan.gnorm z1 : ℕ) : ZMod (Work.FIPlan.absDelta z1 z2)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr hcop
  have haux : ((((((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) *
      ((Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)))⁻¹).val : ℕ)) :
        ZMod (Work.FIPlan.absDelta z1 z2)) *
      (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2))
      = (star z1 * z2).re := by
    rw [ZMod.natCast_zmod_val]
    rw [mul_assoc, ZMod.inv_mul_of_unit _ hunit, mul_one]
  refine (ZMod.intCast_eq_intCast_iff _ _ (Work.FIPlan.absDelta z1 z2)).mp ?_
  push_cast
  exact haux

/-- **The Jacobi symbol of the residue (6.6) is `ratioSym`.**  If `a` is a residue of `z₂/z₁`
modulo `|Δ|` (`a·|z₁|² ≡ Re(z̄₁z₂) (mod |Δ|)`) and `1 ≤ d ∣ |Δ|` with `(|z₁|²,d) = 1`, then `a`
and the numerator of `ratioSym z₁ z₂ d` agree modulo `d`, hence the two Jacobi symbols agree.
This is the step that replaces the frozen symbol `(Re(z̄₁z₂)|d)` by *FI*'s `(z₂/z₁|d)`. -/
theorem jacobiSym_residue_eq_ratioSym {z1 z2 : GaussianInt} {a d : ℕ}
    (hd1 : 1 ≤ d)
    (hdvd : d ∣ Work.FIPlan.absDelta z1 z2)
    (hcong : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)])
    (hcopard : Nat.Coprime (Work.FIPlan.gnorm z1) d) :
    jacobiSym (a : ℤ) d = Work.FIArea7.ratioSym z1 z2 d := by
  haveI : NeZero d := ⟨by omega⟩
  have hunit : IsUnit ((Work.FIPlan.gnorm z1 : ℕ) : ZMod d) :=
    (ZMod.isUnit_iff_coprime _ _).mpr hcopard
  have hdvdZ : (d : ℤ) ∣ (Work.FIPlan.absDelta z1 z2 : ℤ) := by exact_mod_cast hdvd
  have hcongd : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
      ≡ (star z1 * z2).re [ZMOD (d : ℤ)] := Int.ModEq.of_dvd hdvdZ hcong
  rw [Work.FIArea7.ratioSym]
  set ad : ZMod d :=
    ((star z1 * z2).re : ZMod d) * ((Work.FIPlan.gnorm z1 : ZMod d))⁻¹ with had_def
  have hzd : ((a : ZMod d) * (Work.FIPlan.gnorm z1 : ZMod d))
      = ((star z1 * z2).re : ZMod d) := by
    have hh := (ZMod.intCast_eq_intCast_iff _ _ d).mpr hcongd
    push_cast at hh
    exact hh
  have h_eq : (a : ZMod d) = ad := by
    rw [had_def]
    calc (a : ZMod d) = (a : ZMod d) * 1 := (mul_one _).symm
      _ = (a : ZMod d) *
            ((Work.FIPlan.gnorm z1 : ZMod d) * (Work.FIPlan.gnorm z1 : ZMod d)⁻¹) := by
            rw [ZMod.mul_inv_of_unit _ hunit]
      _ = ((a : ZMod d) * (Work.FIPlan.gnorm z1 : ZMod d)) *
            (Work.FIPlan.gnorm z1 : ZMod d)⁻¹ := by
            rw [mul_assoc]
      _ = ((star z1 * z2).re : ZMod d) * (Work.FIPlan.gnorm z1 : ZMod d)⁻¹ := by rw [hzd]
  have h_eq_int : ((a : ℤ) : ZMod d) = ((ad.val : ℤ) : ZMod d) := by
    push_cast
    rw [h_eq, ZMod.natCast_zmod_val]
  have hmod : (a : ℤ) % (d : ℤ) = ((ad.val : ℤ)) % (d : ℤ) :=
    (ZMod.intCast_eq_intCast_iff' _ _ d).mp h_eq_int
  exact jacobiSym.mod_left' hmod

/-- **The corrected (8.16) at *FI*'s ratio symbol.**  For `z₁` of odd norm in a fixed class of
`z₂` modulo eight, with `Δ ≠ 0`, `(z₁,z₂) = 1`, `z₁` and `z₂` primitive, the count kernel is the
`ratioSym`-sum of (8.16):

  `G₀(z₁,z₂) = 2 Σ_{4d|Δ} (φ(d)/d)·(z₂/z₁|d)`.

This is `Cnt_eq_two_sum_of_primitive` (Lemma 8.4) with its residue `a` identified term-by-term
with the numerator of `ratioSym` (`jacobiSym_residue_eq_ratioSym`). -/
theorem G0_eq_ratioSym_sum {z1 z2 : GaussianInt}
    (hodd : Odd (Work.FIPlan.gnorm z1))
    (hcl : Work.FITop4.SameClass8 z1 z2)
    (hD : Work.FIPlan.absDelta z1 z2 ≠ 0)
    (h12 : Work.FIPlan.GaussCoprime z1 z2)
    (h1 : IsCoprime z1 (star z1)) (h2 : IsCoprime z2 (star z2)) :
    Work.FITop4.G0 z1 z2
      = 2 * ∑ d ∈ Work.FITop4.Sset z1 z2,
          ((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ) := by
  -- (5.7) is the congruence `z₂ − z₁ = 8m`.
  obtain ⟨m, hm⟩ := exists_eq_eight_mul_of_sameClass8 hcl
  -- The side condition `(|z₁|²,|Δ|) = 1` is automatic.
  have hcopN : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2) :=
    Work.FIArea2.coprime_gnorm_absDelta h12 h1
  -- The canonical residue `a` of (6.6) modulo `|Δ|`.
  obtain ⟨a, ha_cong⟩ := exists_residue_absDelta hD hcopN
  -- Lemma 8.4 / (8.16): the count equals `|Δ|·2 Σ (φ(d)/d)(a/d)`.
  have hcnt := Work.FIArea2.Cnt_eq_two_sum_of_primitive hodd hm hD h12 h1 h2 ha_cong
  -- Term-by-term, `(a/d) = ratioSym z₁ z₂ d` for `4d ∣ |Δ|`.
  have hterm : ∀ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
      jacobiSym (a : ℤ) d = Work.FIArea7.ratioSym z1 z2 d := by
    intro d hd
    have hdmem := Finset.mem_filter.mp hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdmem.1).1
    have hdvd : d ∣ Work.FIPlan.absDelta z1 z2 :=
      dvd_trans (Dvd.intro 4 (by ring)) hdmem.2
    exact jacobiSym_residue_eq_ratioSym hd1 hdvd ha_cong (hcopN.coprime_dvd_right hdvd)
  -- The two sums coincide.
  have hSum : (∑ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
        ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym (a : ℤ) d : ℝ))
      = ∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ) := by
    unfold Work.FITop4.Sset
    exact Finset.sum_congr rfl (fun d hd => by rw [hterm d hd])
  have hNnz : (Work.FIPlan.absDelta z1 z2 : ℝ) ≠ 0 := by exact_mod_cast hD
  rw [show Work.FITop4.G0 z1 z2
        = (Work.FIArea2.Cnt z1 z2 : ℝ) / (Work.FIPlan.absDelta z1 z2 : ℝ) from rfl, hcnt,
      mul_div_cancel_left₀ _ hNnz, hSum]

end

end Work.FITop4.Red6
