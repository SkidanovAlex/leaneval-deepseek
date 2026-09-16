import Submission.ZagierHoffmanProof.PeriodL
import Submission.Commons.RingTheory.Valuation.comp_strictMono
import Submission.Commons.FieldTheory.PerfectClosureValuation.exists_valuation
import Submission.Commons.Order.WithZeroRat.archimedean
import Submission.ZagierHoffmanProof.GenEvalEntire
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# The ambient field `L` for the ABP criterion

The Anderson–Brownawell–Papanikolas criterion needs a complete nonarchimedean field containing
`q`-th roots of the entries of the auxiliary function (`O = A^{q^{-∞}}`).  The field `F((y))` of
`LaurentSeries F`, used for the `Ω`/`L`-series chapter, is complete but not perfect.

Here we construct

  `L := UniformSpace.Completion (PerfectClosure (LaurentSeries F) p)`

with values in `ℚᵐ⁰ = WithZero (Multiplicative ℚ)`: the valuation on `F((y))` (the `y`-adic
one, with `v y = exp (-1)`) is pushed along `ℤᵐ⁰ →*₀ ℚᵐ⁰`, extended to the perfect closure by
`Commons.FieldTheory.PerfectClosureValuation.exists_valuation`, and then to the completion by
Mathlib's `Valued.valuedCompletion`.  The value group `ℚᵐ⁰` is divisible (so `q`-th roots exist)
and archimedean (`GammaArchimedean`).
-/

set_option autoImplicit false
open scoped WithZero Topology
open LaurentSeries HahnSeries

namespace ZagierHoffmanPositiveChar

/-- The monoid homomorphism `Multiplicative ℤ →* Multiplicative ℚ` induced by `ℤ ↪ ℚ`. -/
noncomputable def intToRatMul : Multiplicative ℤ →* Multiplicative ℚ :=
  AddMonoidHom.toMultiplicative (Int.castAddHom ℚ)

lemma intToRatMul_apply (z : Multiplicative ℤ) :
    intToRatMul z = Multiplicative.ofAdd ((z.toAdd : ℤ) : ℚ) := by
  rw [intToRatMul, AddMonoidHom.toMultiplicative_apply_apply]
  rfl

lemma strictMono_intToRatMul : StrictMono intToRatMul := by
  intro a b h
  rw [intToRatMul_apply, intToRatMul_apply]
  exact Int.cast_strictMono (R := ℚ) h

/-- The monoid-with-zero homomorphism `ℤᵐ⁰ →*₀ ℚᵐ⁰` induced by the inclusion `ℤ ↪ ℚ`. -/
noncomputable def zpowZeroToRat : ℤᵐ⁰ →*₀ ℚᵐ⁰ :=
  WithZero.map' intToRatMul

@[simp] lemma zpowZeroToRat_zero : zpowZeroToRat (0 : ℤᵐ⁰) = 0 := rfl

@[simp] lemma zpowZeroToRat_coe (z : Multiplicative ℤ) :
    zpowZeroToRat (z : ℤᵐ⁰) = (intToRatMul z : ℚᵐ⁰) :=
  WithZero.map'_coe intToRatMul z

@[simp] lemma zpowZeroToRat_exp (z : ℤ) :
    zpowZeroToRat (WithZero.exp z) = WithZero.exp (z : ℚ) := by
  rw [WithZero.exp_eq_coe_ofAdd, zpowZeroToRat_coe, intToRatMul_apply]
  rfl

/-- `zpowZeroToRat` is strictly monotone. -/
lemma strictMono_zpowZeroToRat : StrictMono zpowZeroToRat := by
  intro x y hxy
  induction x using WithZero.recZeroCoe with
  | zero =>
    induction y using WithZero.recZeroCoe with
    | zero => exact absurd hxy (lt_irrefl _)
    | coe b =>
      simp only [zpowZeroToRat_zero, zpowZeroToRat_coe]
      exact WithZero.zero_lt_coe _
  | coe a =>
    induction y using WithZero.recZeroCoe with
    | zero =>
      exact absurd hxy (not_lt_of_ge (show (0 : ℤᵐ⁰) ≤ (a : ℤᵐ⁰) from zero_le))
    | coe b =>
      simp only [zpowZeroToRat_coe, WithZero.coe_lt_coe] at hxy ⊢
      exact strictMono_intToRatMul hxy

section Base

variable (F : Type*) [Field F] [Finite F]

/-- The `ℚᵐ⁰`-valued valuation on `F((y))` obtained by pushing the `y`-adic valuation
(whose value group is `ℤᵐ⁰`) along the inclusion `ℤᵐ⁰ →*₀ ℚᵐ⁰`. -/
noncomputable def valRatLaurent : Valuation (LaurentSeries F) ℚᵐ⁰ :=
  ((Valued.v : Valuation (LaurentSeries F) ℤᵐ⁰)).map zpowZeroToRat
    strictMono_zpowZeroToRat.monotone

omit [Finite F] in
lemma valRatLaurent_apply (x : LaurentSeries F) :
    valRatLaurent F x = zpowZeroToRat (Valued.v x) := rfl

omit [Finite F] in
lemma valRatLaurent_kummerY : valRatLaurent F (kummerY F) = WithZero.exp (-1 : ℚ) := by
  rw [valRatLaurent_apply, kummerY, LaurentSeries.valuation_single_zpow]
  norm_num

lemma valRatLaurent_kummerTheta :
    valRatLaurent F (kummerTheta F) = WithZero.exp ((Nat.card F : ℚ) - 1) := by
  rw [valRatLaurent_apply, v_kummerTheta]
  norm_num

end Base

section PerfectClosure

variable (F : Type*) [Field F] [Finite F]

/-- For a finite field `F`, `ringChar F` is prime. -/
lemma ringChar_prime_field : (ringChar F).Prime := CharP.prime_ringChar F

/-- The field `F((y))` has characteristic `ringChar F`. -/
lemma charP_laurentSeries_ringChar : CharP (LaurentSeries F) (ringChar F) :=
  charP_of_injective_algebraMap (algebraMap F (LaurentSeries F)).injective _

noncomputable instance instFactRingCharPrime : Fact (ringChar F).Prime :=
  ⟨ringChar_prime_field F⟩

noncomputable instance instCharPLaurentSeriesRingChar : CharP (LaurentSeries F) (ringChar F) :=
  charP_laurentSeries_ringChar F

end PerfectClosure

section Ambient

variable (F : Type*) [Field F] [Finite F]

/-- The perfect closure `F((y))^{p^{-∞}}` of `F((y))`, `p = ringChar F`. -/
noncomputable abbrev AmbientPerf : Type _ := PerfectClosure (LaurentSeries F) (ringChar F)

/-- The `ℚᵐ⁰`-valued valuation on the perfect closure, extending the pushed valuation of
`F((y))`. -/
noncomputable instance instValuedAmbientPerf : Valued (AmbientPerf F) ℚᵐ⁰ :=
  Valued.mk'
    (Commons.FieldTheory.PerfectClosureValuation.toValuation (valRatLaurent F))

lemma valAmbientPerf_of (a : LaurentSeries F) :
    Valued.v (PerfectClosure.of (LaurentSeries F) (ringChar F) a) = valRatLaurent F a := by
  change Commons.FieldTheory.PerfectClosureValuation.wFun (valRatLaurent F)
      (PerfectClosure.of (LaurentSeries F) (ringChar F) a) = valRatLaurent F a
  rw [PerfectClosure.of_apply, Commons.FieldTheory.PerfectClosureValuation.wFun_mk]
  have h := Commons.FieldTheory.PerfectClosureValuation.root_pow (ringChar F) 0
    (ringChar_prime_field F).ne_zero (valRatLaurent F a)
  simpa using h

/-- The ambient field `L`: the completion of the perfect closure of `F((y))`. -/
noncomputable abbrev Ambient : Type _ := UniformSpace.Completion (AmbientPerf F)

noncomputable instance instValuedAmbient : Valued (Ambient F) ℚᵐ⁰ :=
  Valued.valuedCompletion

noncomputable instance instNonarchimedeanAddGroupAmbient : NonarchimedeanAddGroup (Ambient F) :=
  Commons.Topology.Algebra.Valued.nonarchimedeanAddGroup (K := Ambient F) (Γ₀ := ℚᵐ⁰)

noncomputable instance instNonarchimedeanRingAmbient : NonarchimedeanRing (Ambient F) :=
  Commons.Topology.Algebra.Valued.nonarchimedeanRing (K := Ambient F) (Γ₀ := ℚᵐ⁰)

lemma valAmbient_coe (a : AmbientPerf F) :
    Valued.v (a : Ambient F) = Valued.v a :=
  Valued.extensionValuation_apply_coe a

/-- `θ = -y^{-(q-1)}`, viewed in the ambient field `L`. -/
noncomputable def ambTheta : Ambient F :=
  ((PerfectClosure.of (LaurentSeries F) (ringChar F) (kummerTheta F) : AmbientPerf F) : Ambient F)

/-- `μ = y^q`, viewed in the ambient field `L`. -/
noncomputable def ambMu : Ambient F :=
  ((PerfectClosure.of (LaurentSeries F) (ringChar F) (kummerMu F) : AmbientPerf F) : Ambient F)

lemma v_ambTheta : Valued.v (ambTheta F) = WithZero.exp ((Nat.card F : ℚ) - 1) := by
  rw [ambTheta, valAmbient_coe, valAmbientPerf_of, valRatLaurent_kummerTheta]

lemma v_ambMu : Valued.v (ambMu F) = WithZero.exp (-(Nat.card F : ℚ)) := by
  rw [ambMu, valAmbient_coe, valAmbientPerf_of, valRatLaurent_apply, kummerMu,
    LaurentSeries.valuation_single_zpow]
  norm_num

end Ambient

section Completion

variable {K : Type*} [Field K] [UniformSpace K] [IsTopologicalRing K]
  [IsUniformAddGroup K] [T0Space K]

/-- The completion of a field of characteristic `p` again has characteristic `p`. -/
theorem charP_completionUniform {p : ℕ} [CharP K p] : CharP (UniformSpace.Completion K) p where
  cast_eq_zero_iff n := by
    rw [← map_natCast (UniformSpace.Completion.coeRingHom : K →+* UniformSpace.Completion K) n,
      ← map_zero (UniformSpace.Completion.coeRingHom : K →+* UniformSpace.Completion K),
      (UniformSpace.Completion.coeRingHom : K →+* UniformSpace.Completion K).injective.eq_iff]
    exact CharP.cast_eq_zero_iff K p n

end Completion

section Rat

/-- The value group `ℚᵐ⁰` is archimedean. -/
theorem gammaArchimedean_rat : GammaArchimedean ℚᵐ⁰ := by
  intro a ha ε hε
  exact Commons.Order.WithZeroRat.archimedean (zero_le (a := a)) ha
    (lt_of_le_of_ne (zero_le (a := ε)) (Ne.symm hε))

end Rat

section FrobAmbient

variable (F : Type*) [Field F] [Finite F]

/-- The completion of the perfect closure of `F((y))` has characteristic `ringChar F`. -/
noncomputable instance instCharPAmbient : CharP (Ambient F) (ringChar F) :=
  charP_completionUniform (K := AmbientPerf F)

/-- `q = |F|` is a Frobenius exponent for the ambient field `L`. -/
theorem frobPow_ambient : FrobPow (Ambient F) (Nat.card F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hprime, hcard⟩ := FiniteField.card F (ringChar F)
  have hcard' : Nat.card F = ringChar F ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcard
  rw [hcard']
  exact FrobPow.of_charP (R := Ambient F) (p := ringChar F) (f : ℕ)

instance : FrobPow (Ambient F) (Nat.card F) := frobPow_ambient F

end FrobAmbient

end ZagierHoffmanPositiveChar
