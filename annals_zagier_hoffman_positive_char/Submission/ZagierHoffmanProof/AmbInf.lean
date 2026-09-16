import Submission.ZagierHoffmanProof.Step3Val
import Mathlib.FieldTheory.RatFunc.Valuation
open Polynomial
open scoped WithZero Topology RatFunc.CompletionAtInfty
open MonoidWithZeroHom.ValueGroup₀
namespace ZagierHoffmanPositiveChar
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

noncomputable def ambKHomAmb : RatFunc F →+* Ambient F :=
  (ambK F).subtype.comp (ambKEquiv F).toRingHom

omit [DecidableEq (RatFunc F)] in
lemma ambKHomAmb_apply (x : RatFunc F) :
    ambKHomAmb F x = ((ambKEquiv F x : ↥(ambK F)) : Ambient F) := rfl

set_option maxHeartbeats 1000000 in
theorem tendsto_ambKHomAmb_zero :
    Filter.Tendsto (ambKHomAmb F) (𝓝 (0 : RatFunc F)) (𝓝 (0 : Ambient F)) := by
  letI : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  have hq1 : (0:ℚ) < (Nat.card F : ℚ) - 1 := by
    have h2 : (2 : ℚ) ≤ (Nat.card F : ℚ) := by
      exact_mod_cast (show (2 : ℕ) ≤ Nat.card F from two_le_ambCard F)
    linarith
  have hvX : ∀ z : ℤ, Valued.v ((RatFunc.X : RatFunc F) ^ z) = WithZero.exp z := by
    intro z
    show RatFunc.inftyValuation F (RatFunc.X ^ z) = WithZero.exp z
    exact RatFunc.inftyValuation.X_zpow F z
  rw [(Valued.hasBasis_nhds_zero (RatFunc F) ℤᵐ⁰).tendsto_iff
      (Valued.hasBasis_nhds_zero (Ambient F) ℚᵐ⁰)]
  intro γ _
  obtain ⟨e, he⟩ : ∃ e : ℚ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp e := by
    refine ⟨(MonoidWithZeroHom.ValueGroup₀.embedding γ.1).log, ?_⟩
    exact (WithZero.exp_log (by
      intro h
      exact Units.ne_zero γ ((MonoidWithZeroHom.ValueGroup₀.embedding_inj).mp
        (by rw [h, map_zero])))).symm
  obtain ⟨m, hm⟩ : ∃ m : ℤ, -e < ((Nat.card F : ℚ) - 1) * ((m : ℚ) + 1) := by
    obtain ⟨m, hm0⟩ := exists_int_gt ((-e) / ((Nat.card F : ℚ) - 1))
    refine ⟨m, ?_⟩
    have h1 : -e < (m : ℚ) * ((Nat.card F : ℚ) - 1) := (div_lt_iff₀ hq1).mp hm0
    nlinarith
  refine ⟨Units.mk0 (Valued.v.restrict ((RatFunc.X : RatFunc F) ^ (-m))) ?_, trivial, ?_⟩
  · rw [ne_eq, Valuation.restrict_eq_zero_iff, hvX]
    exact WithZero.exp_ne_zero
  · intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hx' : Valued.v.restrict x < Valued.v.restrict ((RatFunc.X : RatFunc F) ^ (-m)) := hx
    rw [Valuation.restrict_lt_iff, hvX] at hx'
    rw [Valuation.restrict_lt_iff_lt_embedding, he]
    by_cases hx0 : x = 0
    · subst hx0
      rw [show (ambKHomAmb F) 0 = 0 from map_zero _]
      rw [Valuation.map_zero]
      exact WithZero.exp_pos
    · have hx'' : RatFunc.inftyValuation F x < WithZero.exp (-m) := hx'
      rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero F hx0,
        WithZero.exp_lt_exp] at hx''
      have hxint : RatFunc.intDegree x ≤ -m - 1 := by
        have h'' : RatFunc.intDegree x < -m := by exact_mod_cast hx''
        omega
      rw [ambKHomAmb_apply, v_ambKEquiv F x hx0, WithZero.exp_lt_exp]
      have hcast : ((RatFunc.intDegree x : ℤ) : ℚ) ≤ ((-m - 1 : ℤ) : ℚ) := by
        exact_mod_cast hxint
      have hstep : ((Nat.card F : ℚ) - 1) * ((RatFunc.intDegree x : ℤ) : ℚ)
          ≤ ((Nat.card F : ℚ) - 1) * ((-m - 1 : ℤ) : ℚ) :=
        mul_le_mul_of_nonneg_left hcast hq1.le
      have hfinal : ((Nat.card F : ℚ) - 1) * ((-m - 1 : ℤ) : ℚ) < e := by
        push_cast
        linarith
      linarith

set_option maxHeartbeats 400000 in
theorem continuous_ambKHomAmb : Continuous (ambKHomAmb F) := by
  letI : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  refine continuous_of_continuousAt_zero (ambKHomAmb F) ?_
  rw [ContinuousAt, map_zero]
  exact tendsto_ambKHomAmb_zero F

noncomputable def ambInfHom : RatFunc.CompletionAtInfty F →+* Ambient F :=
  letI : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  UniformSpace.Completion.extensionHom (ambKHomAmb F) (continuous_ambKHomAmb F)

lemma ambInfHom_coe (x : RatFunc F) :
    ambInfHom F (x : RatFunc.CompletionAtInfty F) = ambKHomAmb F x := by
  letI : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  exact UniformSpace.Completion.extensionHom_coe _ _ x

/-- `ambInfHom` is continuous (it is the extension to the completion of a continuous ring hom). -/
theorem continuous_ambInfHom : Continuous (ambInfHom F) := by
  letI : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  exact UniformSpace.Completion.continuous_extension

end ZagierHoffmanPositiveChar
