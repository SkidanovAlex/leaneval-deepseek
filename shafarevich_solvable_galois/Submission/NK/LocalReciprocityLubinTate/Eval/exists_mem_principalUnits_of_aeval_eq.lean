import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_add
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_level
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_ann
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_mem
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_smul2
import Submission.NK.LocalReciprocityLubinTate.Eval.natCard_principalUnits_quotient
import Submission.NK.LocalReciprocityLubinTate.Eval.ltLevelIsSimple_of_fibre
import Submission.NK.LocalReciprocityLubinTate.LubinTate.ncard_fiber_LTdivisionSet
import Submission.NK.LocalReciprocityLubinTate.LubinTate.TorsionCardinality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.Eval

open NK.LocalReciprocityLubinTate

theorem exists_mem_principalUnits_of_aeval_eq {F : Type*} [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (n : ℕ) (hn : 2 ≤ n)
    (M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π
      (NK.LocalReciprocityLubinTate.residueCard F))
    (hpi : M.toLaw.piEndo = NK.LocalReciprocityLubinTate.piXAddXq π
      (NK.LocalReciprocityLubinTate.residueCard F))
    (Θ : MvPowerSeries (Fin 2) (↥(ValuativeRel.valuation F).integer)) (hΘ : IsUnit Θ)
    (hlaw : (M.toLaw.law : MvPowerSeries (Fin 2) (↥(ValuativeRel.valuation F).integer)) =
      MvPowerSeries.X 0 + MvPowerSeries.X 1 * Θ)
    {w z : AlgebraicClosure F}
    (hw : w ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n)
    (hw' : w ∉ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) (n - 1))
    (hz : z ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n)
    (hf : (Polynomial.aeval z) (NK.LocalReciprocityLubinTate.LTpoly (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F)) =
      (Polynomial.aeval w) (NK.LocalReciprocityLubinTate.LTpoly (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F))) :
    ∃ u : (↥(ValuativeRel.valuation F).integer)ˣ,
      u ∈ NK.LocalReciprocityLubinTate.principalUnits F (n - 1) ∧
      z = NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n
        (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hw (↑u) := by
  classical
  have hq : 2 ≤ NK.LocalReciprocityLubinTate.residueCard F :=
    NK.LocalReciprocityLubinTate.two_le_residueCard F
  have hn1 : 1 ≤ n := by omega
  -- ### Step 1: `z = a · w` for some `a ∈ 𝒪[F]`
  have hzrange : z ∈ Set.range (fun b : O F =>
      smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hw b) := by
    rw [range_smulDiv_eq_LTdivisionSet π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq
      hn1 rfl M hpi hw hw']
    exact hz
  obtain ⟨a, rfl⟩ := hzrange
  -- ### Step 2: the `π`-multiples of `z = a · w` and of `w` agree, because `f(z) = f(w)`
  have hpm : smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hw a ∈
      NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n :=
    smulDiv_mem π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi w hw a
  have hiter1 : NK.LocalReciprocityLubinTate.LTpolyIter (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) 1 =
      NK.LocalReciprocityLubinTate.LTpoly (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) := by
    rw [LTpolyIter_succ, LTpolyIter_zero, Polynomial.X_comp]
  have hpi1 : smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hz (π ^ 1)
      = smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hw (π ^ 1) := by
    rw [smulDiv_pi_pow π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi
        (smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hw a) hz 1,
      smulDiv_pi_pow π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi w hw 1,
      hiter1]
    exact hf
  have hpi2 : smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hz (π ^ 1)
      = smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hw (π * a) := by
    rw [show hz = hpm from Subsingleton.elim hz hpm]
    simpa using smulDiv_smul2 π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi w hw π a
  have hkey : smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hw (π * a)
      = smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hw π := by
    rw [← hpi2, hpi1, pow_one]
  -- ### Step 3: `(π * a - π) · w = 0`, hence `π ^ n ∣ π * (a - 1)`
  have hspan : (π * a) - π ∈ Ideal.span {(π : O F) ^ n} := by
    obtain ⟨H, hH, hform⟩ :=
      smulDiv_add_formula π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M Θ hΘ hlaw
        hw π (π * a - π)
    rw [show (π : O F) + (π * a - π) = π * a from by ring, hkey] at hform
    have hzero : smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hw (π * a - π)
        * H = 0 :=
      add_left_cancel
        (a := smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hw π)
        (by rw [add_zero]; exact hform.symm)
    have hz0 : smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hw (π * a - π)
        = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hH
    exact (smulDiv_eq_zero_iff π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi hw
      hw' hn1 (π * a - π)).mp hz0
  -- ### Step 4: `a - 1 ∈ (π ^ (n-1))`
  have hpa : (π : O F) * (a - 1) ∈ Ideal.span {(π : O F) ^ n} := by
    rwa [show (π : O F) * (a - 1) = π * a - π from by ring]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hpa
  have ha1 : a - 1 ∈ Ideal.span {(π : O F) ^ (n - 1)} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩
    refine mul_left_cancel₀ hπ.ne_zero ?_
    rw [hc, show (π : O F) ^ n = (π : O F) ^ (n - 1) * π by
      rw [← pow_succ, Nat.sub_add_cancel hn1]]
    ring
  -- ### Step 5: `a` is a unit, congruent to `1` modulo `π ^ (n-1)`
  have hmemm : a - 1 ∈ (IsLocalRing.maximalIdeal (O F)) ^ (n - 1) := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact ha1
  have hnonunits : (1 : O F) - a ∈ nonunits (O F) := by
    rw [← IsLocalRing.mem_maximalIdeal]
    have h1 : a - 1 ∈ IsLocalRing.maximalIdeal (O F) := by
      simpa using (Ideal.pow_le_pow_right (show 1 ≤ n - 1 by omega)) hmemm
    rw [show (1 : O F) - a = -(a - 1) from by ring]
    exact neg_mem h1
  have hunit : IsUnit a := IsLocalRing.isUnit_of_mem_nonunits_one_sub_self a hnonunits
  refine ⟨hunit.unit, ?_, ?_⟩
  · change ((hunit.unit : (O F)ˣ) : O F) - 1 ∈ (IsLocalRing.maximalIdeal (O F)) ^ (n - 1)
    rw [IsUnit.unit_spec]
    exact hmemm
  · show smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hw a
      = smulDiv π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq M hw (↑hunit.unit)
    rw [IsUnit.unit_spec]

end NK.LocalReciprocityLubinTate.Eval
