import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.NumberTheory.NumberField.Completion.finite_quotient_units_range_norm_adicCompletion
import Submission.NK.GlobalCFT.Place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.ArtinBridge

open scoped NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- **Principal units of a level.**  In a valued field `F` with value group `Γ₀`, the units which
are congruent to `1` modulo the closed ball of radius `ε` (for a level `ε < 1`) form a subgroup of
`Fˣ`: this is the classical group of principal units `1 + 𝔪^ε`. -/
private def principalUnits (F : Type*) [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued F Γ₀] (ε : Γ₀) (hε : ε < 1) : Subgroup Fˣ where
  carrier := {z | Valued.v ((z : F) - 1) ≤ ε}
  one_mem' := by
    show Valued.v (((1 : Fˣ) : F) - 1) ≤ ε
    rw [Units.val_one, sub_self, map_zero]
    exact zero_le
  mul_mem' := by
    intro y z hy hz
    show Valued.v (((y * z : Fˣ) : F) - 1) ≤ ε
    have hε1 : ε ≤ 1 := le_of_lt hε
    have hdec : (((y * z : Fˣ) : F) - 1)
        = ((y : F) - 1) + ((z : F) - 1) + ((y : F) - 1) * ((z : F) - 1) := by
      rw [Units.val_mul]; ring
    rw [hdec]
    calc Valued.v (((y : F) - 1) + ((z : F) - 1) + ((y : F) - 1) * ((z : F) - 1))
        ≤ max (Valued.v (((y : F) - 1) + ((z : F) - 1)))
            (Valued.v (((y : F) - 1) * ((z : F) - 1))) := Valuation.map_add_le_max' _ _ _
      _ ≤ max (max (Valued.v ((y : F) - 1)) (Valued.v ((z : F) - 1)))
            (Valued.v (((y : F) - 1) * ((z : F) - 1))) :=
          max_le_max (Valuation.map_add_le_max' _ _ _) le_rfl
      _ ≤ ε := by
          refine max_le (max_le hy hz) ?_
          rw [Valuation.map_mul]
          refine (mul_le_mul' hy hz).trans ?_
          calc ε * ε ≤ ε * 1 := mul_le_mul' le_rfl hε1
            _ = ε := mul_one ε
  inv_mem' := by
    intro y hy
    show Valued.v (((y⁻¹ : Fˣ) : F) - 1) ≤ ε
    have hlt : Valued.v ((y : F) - 1) < 1 := lt_of_le_of_lt hy hε
    have hyv : Valued.v ((y : F)) = 1 := by
      have h := Valuation.map_add_eq_of_lt_left (v := Valued.v)
        (x := (1 : F)) (y := (y : F) - 1) (by rw [map_one]; exact hlt)
      simpa using h
    have hdecode : (((y⁻¹ : Fˣ) : F) - 1) = ((y : F) - 1) * (-((y : F)⁻¹)) := by
      rw [Units.val_inv_eq_inv_val]
      field_simp
      ring
    rw [hdecode, Valuation.map_mul, Valuation.map_neg, Valuation.map_inv, hyv, inv_one, mul_one]
    exact hy

/-- **The local norm is open at the origin.**  For a finite place `Q` of `K` and a place `q` of `L`
above it, there is a level `n > 0` such that every unit `z` of `K_Q` with `z ≡ 1 mod 𝔪^n` is a norm
from `L_q`.  (Universe-polymorphic form of `NK.CFTLib.ExistsCongruence.exists_level_localNormFinite`,
proved from the commons.) -/
private theorem exists_level_localNormFinite_range {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    ∃ n : ℕ, 0 < n ∧ ∀ z : (Q.adicCompletion K)ˣ,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          ((z : Q.adicCompletion K) - 1) ≤
        (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) →
      z ∈ (NK.GlobalCFT.Place.localNormFinite q Q hq).range := by
  obtain ⟨D, u₀, hu₀, hu₀D⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_trace_eq_one_adicCompletion
      (K := K) (L := L) Q q hq
  refine ⟨2 * D + 2, by omega, ?_⟩
  intro z hz
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  obtain ⟨x, hx⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_norm_eq_of_val_sub_one_le_aux
      (K := K) (L := L) Q q hq D u₀ hu₀ hu₀D (z : Q.adicCompletion K) hz
  haveI : Module.Free (Q.adicCompletion K) (q.adicCompletion L) :=
    Module.Free.of_divisionRing _ _
  haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  have hxne : x ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hx
    exact Units.ne_zero z hx.symm
  refine MonoidHom.mem_range.mpr ⟨Units.mk0 x hxne, ?_⟩
  refine Units.ext ?_
  rw [show NK.GlobalCFT.Place.localNormFinite q Q hq =
    Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K)
      from rfl]
  rw [Units.coe_map, Units.val_mk0]
  exact hx

theorem exists_isOpen_subgroup_le_localNormFinite_range {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    ∃ A : Subgroup ((IsDedekindDomain.HeightOneSpectrum.adicCompletion K Q)ˣ),
      IsOpen (A : Set ((IsDedekindDomain.HeightOneSpectrum.adicCompletion K Q)ˣ)) ∧
      A ≤ (NK.GlobalCFT.Place.localNormFinite q Q hq).range := by
  classical
  obtain ⟨n, hnpos, hn⟩ :=
    exists_level_localNormFinite_range (K := K) (L := L) Q q hq
  set ε : WithZero (Multiplicative ℤ) := WithZero.exp (-(n : ℤ)) with hεdef
  have hεlt : ε < 1 := by
    rw [hεdef, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  refine ⟨principalUnits (Q.adicCompletion K) ε hεlt, ?_, ?_⟩
  · have hball : IsOpen {x : Q.adicCompletion K |
        Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤ ε} := by
      have hεne : ε ≠ 0 := by
        rw [hεdef]; exact WithZero.exp_ne_zero
      obtain ⟨y₀, hy₀⟩ :=
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective (K := K) (v := Q) ε
      have hseteq : {x : Q.adicCompletion K |
          Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤ ε} =
          {x : Q.adicCompletion K |
            (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))).restrict x ≤
              (Valued.v (R := Q.adicCompletion K)
                (Γ₀ := WithZero (Multiplicative ℤ))).restrict y₀} := by
        ext x
        simp only [Set.mem_ofPred_eq]
        rw [Valuation.restrict_le_iff, hy₀]
      rw [hseteq]
      refine Valued.isOpen_closedBall (Q.adicCompletion K) (r :=
        (Valued.v (R := Q.adicCompletion K)
          (Γ₀ := WithZero (Multiplicative ℤ))).restrict y₀) ?_
      intro h0
      rw [Valuation.restrict_eq_zero_iff] at h0
      rw [hy₀] at h0
      exact WithZero.exp_ne_zero h0
    have hcont : Continuous (fun z : (Q.adicCompletion K)ˣ =>
        ((z : Q.adicCompletion K) - 1)) := Units.continuous_val.sub continuous_const
    exact hball.preimage hcont
  · intro z hz
    exact hn z hz

end NK.NUV2.ArtinBridge
