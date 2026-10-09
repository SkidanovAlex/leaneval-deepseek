import Mathlib
import Submission.Work.SSGRoute.PT.alphaTwo_beta
import Submission.Work.SSGRoute.Nakayama.br_pTorsion
import Submission.Work.SSGRoute.PT.H2_decomp_p_divisible
import Submission.Work.SSGRoute.PT.resH2_kill_index_torsion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open Work


/-- **The `p`-divisibility/non-vanishing input of the corestriction crux.**  For `A` a finite place
of `Ω = k̄` over the number field `k`, `U ≤ D_A = decomp k A` an open subgroup of finite index
`n = [D_A : U]` with `p ∣ n`, there is a class `w ∈ H²(D_A, \bar k^×)` whose restriction to `U` is
`p`-torsion and which is **not** annihilated by `n`, i.e. `p · res_U(w) = 0` and `n · w ≠ 0`.

Mathematically: `H²(D_A, Ω^×) ≅ Br(k_v) ≅ ℚ/ℤ` is divisible, so classes of any order exist; a class
`w` of order exactly `nout` has `res_U(w) = n·w` of order `p`.  The workspaces's own level structure
(`Work.SSGRoute.PTCore.H2_units_level_structure`, `psiTilde`, `H2_level_cover_alt`,
`exists_superlevel_p_dvd_index`, `Work.SSGRoute.PTembedding.brauer_pPrimary_divisible`) supplies
classes of arbitrarily large `p`-power order. -/
theorem exists_resH2_pTorsion_nsmul_ne_zero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)]
    (hp : p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U)) :
    ∃ w : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)),
      p • Work.SSGRoute.PT.resH2 U w = 0 ∧
        Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • w ≠ 0 := by
  classical
  -- `n = [D_A : U]`, written `n = p ^ a * m` with `p ∤ m`; `H²(D_A, Ωˣ)` is `p`-divisible and
  -- `U` is an open subgroup, so `resH2 U` kills the `n`-torsion while `H²(D_A, Ωˣ)` has a
  -- non-zero `p`-torsion class.  The element `w` below is a `p ^ a`-th root of that class.
  set n := Nat.card (↥(SSGRoute.decomp k A) ⧸ U) with hn
  set a := padicValNat p n with ha
  set m := n / p ^ a with hm
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : Nonempty (↥(SSGRoute.decomp k A) ⧸ U) :=
    ⟨((1 : ↥(SSGRoute.decomp k A)) : ↥(SSGRoute.decomp k A) ⧸ U)⟩
  have hn0 : n ≠ 0 := by
    rw [hn, Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  have hn_eq : n = p ^ a * m := by
    rw [ha, hm, hn]
    exact (Nat.mul_div_cancel' (pow_padicValNat_dvd (p := p) (n := n))).symm
  have hm_ne0 : m ≠ 0 := by
    intro h0
    exact hn0 (by rw [hn_eq, h0, mul_zero])
  have hm_not_dvd : ¬ p ∣ m := by
    have h1 : padicValNat p m = 0 := by
      rw [hm, ha, padicValNat.div_pow (a := padicValNat p n) (b := n) pow_padicValNat_dvd,
        Nat.sub_self]
    rcases (padicValNat.eq_zero_iff (p := p) (n := m)).mp h1 with h | h | h
    · exact absurd h (Fact.out : p.Prime).ne_one
    · exact absurd h hm_ne0
    · exact h
  -- a non-zero `p`-torsion class of `H²(D_A, Ωˣ)`
  have hcard := Work.SSGRoute.Nakayama.br_pTorsion p k Ω A hA
  haveI : Finite {x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) //
      p • x = 0} := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp0)
  haveI : Fintype {x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) //
      p • x = 0} := Fintype.ofFinite _
  have hgt : 1 < Fintype.card {x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
      (Additive (Units Ω)) // p • x = 0} := by
    rw [Fintype.card_eq_nat_card, hcard]; exact (Fact.out : p.Prime).one_lt
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card hgt
    (⟨0, by simp⟩ : {x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
      (Additive (Units Ω)) // p • x = 0})
  have hx0 : x.1 ≠ 0 := fun h => hx (Subtype.ext h)
  have hxp : p • x.1 = 0 := x.2
  -- iterated `p`-th roots, using the `p`-divisibility of `H²(D_A, Ωˣ)`
  have hdiv : ∀ z : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)),
      ∃ y, p • y = z := H2_decomp_p_divisible p k Ω A hA
  have hroot : ∀ j : ℕ, ∃ e : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
      (Additive (Units Ω)), p ^ j • e = x.1 := by
    intro j
    induction j with
    | zero => exact ⟨x.1, by rw [pow_zero, one_nsmul]⟩
    | succ j ih =>
        obtain ⟨e, he⟩ := ih
        obtain ⟨e', he'⟩ := hdiv e
        refine ⟨e', ?_⟩
        rw [pow_succ, mul_nsmul' e' (p ^ j) p, he', he]
  obtain ⟨e, he⟩ := hroot a
  refine ⟨e, ?_, ?_⟩
  · -- `p · res_U(e) = res_U(p · e) = 0`, because `n · (p · e) = 0`
    rw [← map_nsmul]
    refine resH2_kill_index_torsion k Ω A hA U hU (p • e) ?_
    rw [← hn, hn_eq]
    have hstep : (p ^ a * m) • (p • e) = m • (p • (p ^ a • e)) := by
      rw [mul_nsmul' (p • e) (p ^ a) m, nsmul_left_comm (p • e) m (p ^ a),
        nsmul_left_comm e p (p ^ a)]
    rw [hstep, he, hxp, smul_zero]
  · -- `n · e = m · x ≠ 0`, since `x` has order `p` and `p ∤ m`
    have hstep : n • e = m • x.1 := by
      rw [hn_eq, mul_nsmul' e (p ^ a) m, nsmul_left_comm e m (p ^ a), he]
    rw [hstep]
    intro h
    have hxord : addOrderOf x.1 = p := by
      have hdvd : addOrderOf x.1 ∣ p := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hxp
      have hne1 : addOrderOf x.1 ≠ 1 := fun hh => hx0 (AddMonoid.addOrderOf_eq_one_iff.mp hh)
      exact (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) _ hdvd).resolve_left hne1
    have hpm : p ∣ m := by
      have : addOrderOf x.1 ∣ m := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
      rwa [hxord] at this
    exact hm_not_dvd hpm

end Work.SSGRoute.PT
