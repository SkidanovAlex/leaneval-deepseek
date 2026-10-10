import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.NK.HeckeL.Zeta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain Filter Topology
open scoped BigOperators Classical
open Commons.NumberTheory.NumberField.DedekindZeta

noncomputable section

namespace NK.HeckeL.Product

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-! ## The pieces of the bijection -/

/-- The finite place of `K` below a finite place of `L`: the contraction of the prime ideal. -/
noncomputable def underPrimeIdeal (𝔮 : NK.HeckeL.PrimeIdeal L) : NK.HeckeL.PrimeIdeal K :=
  ⟨𝔮.asIdeal.under (𝓞 K), inferInstance, Ideal.under_ne_bot (A := 𝓞 K) 𝔮.ne_bot⟩

@[simp] theorem underPrimeIdeal_asIdeal (𝔮 : NK.HeckeL.PrimeIdeal L) :
    (underPrimeIdeal (K := K) 𝔮).asIdeal = 𝔮.asIdeal.under (𝓞 K) := rfl

theorem liesOver_underPrimeIdeal (𝔮 : NK.HeckeL.PrimeIdeal L) :
    𝔮.asIdeal.LiesOver (underPrimeIdeal (K := K) 𝔮).asIdeal :=
  Ideal.over_under (A := 𝓞 K) 𝔮.asIdeal

/-- Two finite places of `K` over which a common finite place of `L` lies coincide. -/
theorem eq_of_liesOver_of_liesOver {𝔭 𝔭' : NK.HeckeL.PrimeIdeal K}
    {𝔮 : NK.HeckeL.PrimeIdeal L} (h : 𝔮.asIdeal.LiesOver 𝔭.asIdeal)
    (h' : 𝔮.asIdeal.LiesOver 𝔭'.asIdeal) : 𝔭 = 𝔭' :=
  HeightOneSpectrum.ext (h.over.trans h'.over.symm)

/-- The finite places of `L` that do not lie over any place of the modulus `S`. -/
def UnramifiedOutside (S : Finset (NK.HeckeL.PrimeIdeal K))
    (𝔮 : NK.HeckeL.PrimeIdeal L) : Prop :=
  ∀ Q ∈ S, ¬ 𝔮.asIdeal.LiesOver Q.asIdeal

/-- The index set of the right hand side: pairs consisting of a place `𝔭` of `K` outside `S` and a
place `P` of `L` above it. -/
abbrev FiberIndex (S : Finset (NK.HeckeL.PrimeIdeal K)) : Type _ :=
  (𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}) × (𝔭.1.asIdeal.primesOver (𝓞 L))

/-- An element of the fibre index set as a finite place of `L`. -/
noncomputable def sigmaPrime (S : Finset (NK.HeckeL.PrimeIdeal K))
    (x : FiberIndex (K := K) (L := L) S) : NK.HeckeL.PrimeIdeal L :=
  ⟨x.2.1, x.2.2.1, Ideal.ne_bot_of_mem_primesOver x.1.1.ne_bot x.2.2⟩

@[simp] theorem sigmaPrime_asIdeal (S : Finset (NK.HeckeL.PrimeIdeal K))
    (x : FiberIndex (K := K) (L := L) S) : (sigmaPrime (K := K) S x).asIdeal = x.2.1 := rfl

/-- Two elements of the fibre index set which induce the same place of `L` are equal: a prime of
`L` determines the prime of `K` below it. -/
theorem sigmaPrime_injective (S : Finset (NK.HeckeL.PrimeIdeal K)) :
    Function.Injective (sigmaPrime (K := K) (L := L) S) := by
  rintro ⟨𝔭, P⟩ ⟨𝔭', P'⟩ h
  have hP : P.1 = P'.1 := congrArg (fun 𝔮 : NK.HeckeL.PrimeIdeal L => 𝔮.asIdeal) h
  have h𝔭as : 𝔭.1.asIdeal = 𝔭'.1.asIdeal :=
    P.2.2.over.trans
      ((by rw [hP] : P.1.under (𝓞 K) = P'.1.under (𝓞 K)).trans P'.2.2.over.symm)
  have h𝔭 : 𝔭 = 𝔭' := Subtype.ext (HeightOneSpectrum.ext h𝔭as)
  cases h𝔭
  have hPP : P = P' := Subtype.ext hP
  cases hPP
  rfl

/-- An element of the fibre index set as a finite place of `L` that does not lie over `S`.  A
place of `L` lying over a place of `S` would put that place of `S` below a place of `K` outside
`S`, which is impossible. -/
noncomputable def sigmaUnram (S : Finset (NK.HeckeL.PrimeIdeal K))
    (x : FiberIndex (K := K) (L := L) S) :
    {𝔮 : NK.HeckeL.PrimeIdeal L // UnramifiedOutside S 𝔮} :=
  ⟨sigmaPrime (K := K) S x, fun _Q hQ hLQ =>
    x.1.2 ((eq_of_liesOver_of_liesOver hLQ x.2.2.2) ▸ hQ)⟩

/-! ## The Euler factors -/

/-- The complex Euler factor `(1 - N P^{-s})⁻¹` attached to an ideal of `𝓞 L`. -/
noncomputable def fiberFactor (L : Type*) [Field L] [NumberField L] (s : ℝ)
    (I : Ideal (𝓞 L)) : ℂ :=
  (1 - (((Ideal.absNorm I : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹

theorem fiberFactor_apply (s : ℝ) (I : Ideal (𝓞 L)) :
    fiberFactor L s I = (1 - (((Ideal.absNorm I : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := rfl

/-- The complex Euler factor is the coercion of the real one. -/
theorem fiberFactor_eq_ofReal (s : ℝ) (I : Ideal (𝓞 L)) :
    fiberFactor L s I = ((localFactor L s I : ℝ) : ℂ) := by
  rw [fiberFactor, localFactor, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]

/-! ## Multipliability of the fibre-indexed family -/

/-- The product over the fibre index set converges: it is, up to a bijection of the index sets,
the product over the primes of `L`, whose convergence is the convergence of the logarithms. -/
theorem multipliable_fiberFactor (S : Finset (NK.HeckeL.PrimeIdeal K)) {s : ℝ} (hs : 1 < s) :
    Multipliable (fun x : FiberIndex (K := K) (L := L) S => fiberFactor L s x.2.1) := by
  have hlog : Summable (fun 𝔮 : NK.HeckeL.PrimeIdeal L =>
      Real.log (localFactor L s 𝔮.asIdeal)) := summable_log_localFactor (K := L) hs
  have hcomp : Summable ((fun 𝔮 : NK.HeckeL.PrimeIdeal L =>
      Real.log (localFactor L s 𝔮.asIdeal)) ∘ sigmaPrime (K := K) (L := L) S) :=
    hlog.comp_injective (sigmaPrime_injective (K := K) (L := L) S)
  have hlogSigma : Summable (fun x : FiberIndex (K := K) (L := L) S =>
      Real.log (localFactor L s x.2.1)) := by
    have hfun : ((fun 𝔮 : NK.HeckeL.PrimeIdeal L => Real.log (localFactor L s 𝔮.asIdeal)) ∘
        sigmaPrime (K := K) (L := L) S) =
        (fun x : FiberIndex (K := K) (L := L) S => Real.log (localFactor L s x.2.1)) := by
      funext x
      rw [Function.comp_apply, sigmaPrime_asIdeal]
    exact hfun ▸ hcomp
  have hpos : ∀ x : FiberIndex (K := K) (L := L) S, 0 < localFactor L s x.2.1 := by
    intro x
    have hlt : (Ideal.absNorm x.2.1 : ℝ) ^ (-s) < 1 :=
      rpow_neg_absNorm_primeIdeal_lt_one (K := L) (lt_trans zero_lt_one hs)
        (sigmaPrime (K := K) S x)
    rw [localFactor]
    exact inv_pos.mpr (by linarith)
  exact ((Real.multipliable_of_summable_log hpos hlogSigma).map Complex.ofRealHom
    Complex.continuous_ofReal).congr (fun x => (fiberFactor_eq_ofReal (L := L) s x.2.1).symm)

/-! ## The rearrangement of the Euler product -/

/-- **The fibre decomposition of the truncated Euler product of `L`.**  The product over the
places of `L` outside `S` equals the product over the places of `K` outside `S` of the products
over their fibres. -/
theorem tprod_unramified_eq_tprod_fiber (S : Finset (NK.HeckeL.PrimeIdeal K)) {s : ℝ}
    (hs : 1 < s) :
    (∏' 𝔮 : {𝔮 : NK.HeckeL.PrimeIdeal L // UnramifiedOutside S 𝔮},
        fiberFactor L s 𝔮.1.asIdeal) =
      ∏' σ : FiberIndex (K := K) (L := L) S, fiberFactor L s σ.2.1 :=
  tprod_eq_tprod_of_ne_one_bij
    (f := fun 𝔮 : {𝔮 : NK.HeckeL.PrimeIdeal L // UnramifiedOutside S 𝔮} =>
      fiberFactor L s 𝔮.1.asIdeal)
    (fun x => sigmaUnram (K := K) (L := L) S x.1) (fun x y h => by
      have h' : sigmaPrime (K := K) S x.1 = sigmaPrime (K := K) S y.1 :=
        congrArg Subtype.val h
      exact Subtype.ext (sigmaPrime_injective (K := K) (L := L) S h'))
    (fun 𝔮 _ => by
      refine ⟨⟨⟨⟨underPrimeIdeal (K := K) 𝔮.1, ?_⟩,
        ⟨𝔮.1.asIdeal, ?_, ?_⟩⟩, ?_⟩, ?_⟩
      · intro hmem
        exact 𝔮.2 (underPrimeIdeal (K := K) 𝔮.1) hmem
          (liesOver_underPrimeIdeal (K := K) 𝔮.1)
      · exact 𝔮.1.isPrime
      · exact liesOver_underPrimeIdeal (K := K) 𝔮.1
      · exact ‹fiberFactor L s 𝔮.1.asIdeal ≠ 1›
      · exact Subtype.ext (HeightOneSpectrum.ext rfl))
    (fun x => by
      show fiberFactor L s (sigmaPrime (K := K) S x.1).asIdeal = fiberFactor L s x.1.2.1
      rw [sigmaPrime_asIdeal])

/-- The product over the fibre index set is the iterated product over the places of `K` outside
`S` of the products over the fibres. -/
theorem tprod_fiber_eq_iterated (S : Finset (NK.HeckeL.PrimeIdeal K)) {s : ℝ} (hs : 1 < s) :
    (∏' σ : FiberIndex (K := K) (L := L) S, fiberFactor L s σ.2.1) =
      ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
        ∏' P : 𝔭.1.asIdeal.primesOver (𝓞 L), fiberFactor L s P.1 :=
  Multipliable.tprod_sigma'
    (fun 𝔭 => (hasProd_fintype
      (fun P : 𝔭.1.asIdeal.primesOver (𝓞 L) => fiberFactor L s P.1)).multipliable)
    (multipliable_fiberFactor (K := K) (L := L) S hs)

/-! ## The main theorem -/

theorem zetaUnramified_eq_tprod_fiber {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) {s : ℝ} (hs : 1 < s) :
    NK.HeckeL.zetaUnramified K L S s =
      ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
        ∏ P : 𝔭.1.asIdeal.primesOver (NumberField.RingOfIntegers L),
          (1 - (((Ideal.absNorm P.1 : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
  rw [NK.HeckeL.zetaUnramified]
  change (∏' 𝔮 : {𝔮 : NK.HeckeL.PrimeIdeal L // UnramifiedOutside S 𝔮},
      fiberFactor L s 𝔮.1.asIdeal) =
    ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
      ∏ P : 𝔭.1.asIdeal.primesOver (𝓞 L),
        (1 - (((Ideal.absNorm P.1 : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
  rw [tprod_unramified_eq_tprod_fiber (K := K) (L := L) S hs,
    tprod_fiber_eq_iterated (K := K) (L := L) S hs]
  refine tprod_congr fun 𝔭 => ?_
  exact (tprod_fintype
      (fun P : 𝔭.1.asIdeal.primesOver (𝓞 L) => fiberFactor L s P.1)).trans
    (Finset.prod_congr rfl fun P _ => fiberFactor_apply (L := L) s P.1)

end NK.HeckeL.Product
