import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField

/-- At a finite place `v` (a non-zero prime ideal of `𝓞 K`), the `v`-adic absolute value of `x`
is `≤ 1` if and only if the `v`-adic valuation of `x` is `≤ 1`. This is the dictionary between
the absolute-value formulation of the finite places and the `ℤᵐ⁰`-valued valuation attached to a
maximal ideal. -/
lemma adicAbv_le_one_iff_valuation_le_one {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : K) :
    NumberField.HeightOneSpectrum.adicAbv K v x ≤ 1 ↔
      (IsDedekindDomain.HeightOneSpectrum.valuation K v) x ≤ 1 := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, NNReal.coe_le_one,
    WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)]

/-- A number field element whose finite places all have `v`-adic absolute value `≤ 1` is an
algebraic integer. This is the "local" (non-archimedean) half of the product formula
characterisation of `𝓞 K` as the intersection of the valuation rings of the finite places. -/
theorem isIntegral_of_forall_finitePlace_le_one {K : Type*} [Field K] [NumberField K] (β : K)
    (h : ∀ v : NumberField.FinitePlace K, v β ≤ 1) : IsIntegral ℤ β := by
  refine (IsIntegralClosure.isIntegral_iff (A := NumberField.RingOfIntegers K) (R := ℤ)
    (B := K)).mpr ?_
  have key : β ∈ (algebraMap (NumberField.RingOfIntegers K) K).range :=
    IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
      (R := NumberField.RingOfIntegers K) K β (fun v => ?_)
  · obtain ⟨y, hy⟩ := key
    exact ⟨y, hy⟩
  · have hle : NumberField.HeightOneSpectrum.adicAbv K v β ≤ 1 := by
      have h1 := h (NumberField.FinitePlace.mk v)
      rwa [NumberField.FinitePlace.mk_apply, NumberField.FinitePlace.norm_embedding] at h1
    exact (adicAbv_le_one_iff_valuation_le_one v β).mp hle

end Work.BW
