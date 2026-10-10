import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.NK.TameStructureDeep.Tame.dvr_comap_eq_adicCompletionIntegers
import Submission.NK.TameStructureDeep.Tame.fixedField_wildInertia_le_tameClosure_of_inertia_le_unramified
import Submission.NK.TameStructureDeep.Tame.inertiaFixedField_le_unramifiedClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

/-- **Any discrete valuation ring of a finite extension `M/κ` of a `p`-adic field `κ = K_𝔭` is
Henselian.**

This is the one hypothesis of the Kummer-theoretic step
(`NK.TameStructureDeep.Tame.fixedField_wildInertia_le_tameClosure_of_inertia_le_unramified`)
which is not literally present in the statement of `wildInertia_le_tameClosure`, but *is* a
consequence of the other hypotheses.

Indeed, `A` contracts to the ring of integers `𝒪_κ` of `κ`
(`NK.TameStructureDeep.Tame.dvr_comap_eq_adicCompletionIntegers`, which only needs `A` to be a
discrete valuation ring of an *algebraic* extension), and `𝒪_κ` is Henselian
(`Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing`).  On the other hand a
Henselian discrete valuation ring of `M` exists
(`NK.TameStructureDeep.Tame.exists_valuationRing_henselian`) and also contracts to `𝒪_κ`; the
uniqueness of the extension of a Henselian valuation to an algebraic extension
(`Commons.RingTheory.Valuation.eq_of_comap_eq_of_isAlgebraic`) forces `A` to be that ring, hence
Henselian. -/
theorem henselianLocalRing_of_isDiscreteValuationRing {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {M : Type*} [Field M] [Algebra (𝔭.adicCompletion K) M]
    [FiniteDimensional (𝔭.adicCompletion K) M]
    (A : ValuationSubring M) [IsDiscreteValuationRing A] : HenselianLocalRing A := by
  haveI : Algebra.IsAlgebraic (𝔭.adicCompletion K) M := Algebra.IsAlgebraic.of_finite _ _
  obtain ⟨A₀, hDVR₀, hHens₀, hcard₀⟩ :=
    NK.TameStructureDeep.Tame.exists_valuationRing_henselian (K := K) 𝔭 (B := M)
  haveI : IsDiscreteValuationRing A₀ := hDVR₀
  have hcomap₀ : A₀.comap (algebraMap (𝔭.adicCompletion K) M) = 𝔭.adicCompletionIntegers K :=
    NK.TameStructureDeep.Tame.dvr_comap_eq_adicCompletionIntegers 𝔭 A₀
  have hcomapA : A.comap (algebraMap (𝔭.adicCompletion K) M) = 𝔭.adicCompletionIntegers K :=
    NK.TameStructureDeep.Tame.dvr_comap_eq_adicCompletionIntegers 𝔭 A
  haveI : HenselianLocalRing (𝔭.adicCompletionIntegers K) :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing 𝔭
  have hAeq : A = A₀ :=
    Commons.RingTheory.Valuation.eq_of_comap_eq_of_isAlgebraic
      (𝔭.adicCompletionIntegers K) A A₀ hcomapA hcomap₀
  exact hAeq.symm ▸ hHens₀

/-- **The fixed field of the wild inertia is tamely ramified, hence contained in `κ^{tr}`.** Let `κ = K_𝔭`, `p = resCharAt 𝔭` (a prime), `π` a uniformiser of `κ`, `K'` a separable closure, and `T = κ^{tr} = tameClosure p π = κ^{ur}(π^{1/n} : p ∤ n)`. For a finite-dimensional Galois extension `M/κ` inside `K'` and a `Gal(M/κ)`-stable discrete valuation ring `A` of `M` whose residue field is perfect of cardinality `p^f`, the fixed field of the wild inertia subgroup `G_1 = ramificationSubgroup A 1` is contained in `T`, equivalently `M^{G_1} ⊆ M ∩ κ^{tr}`.  **Route.** `dvr_comap_eq_adicCompletionIntegers` (proved) gives `A ∩ κ = 𝒪_κ`; then `Commons.RingTheory.Valuation.eq_of_comap_eq_of_isAlgebraic` with an extension `A₀` of `𝒪_κ` (`Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq`, or `NK.TameStructureDeep.Tame.exists_valuationSubring_residueData_comap`) identifies `A` with the canonical (complete, Henselian) valuation ring. Let `L = M^{G_1}`, `B = A ∩ L` (a DVR of `L`, `Gal(L/κ)`-stable with `ramificationSubgroup B 1 = ⊥` by the tower compatibility `NK.RamificationDeep.image_ramificationSubgroup_eq_of_tower` and `NK.Ramification.herbrand_one`), `G_0 = B.inertiaSubgroup κ`, `F = L^{G_0}`, `e = #G_0`, `q = #(B/𝔪_B)`. Then `G_0 ↪ (B/𝔪_B)^×` is injective with cyclic image (`NK.RamificationDeep.unitHom_ker`), so `G_0` is cyclic and `e ∣ q - 1`. Hensel in `B` lifts a generator `ḡ` of `(B/𝔪_B)^×` to a primitive `(q-1)`-st root of unity `ω ∈ B ⊆ L`; every `σ ∈ G_0` fixes `ω` (both `σω/ω` and `ω` are `(q-1)`-st roots of unity congruent modulo `𝔪_B`, and a root of unity of prime-to-`p` order congruent to `1` modulo `𝔪_B` is `1`), so `ω ∈ F ⊆ κ^{ur}` (`NK.LocalAnabelian.mem_unramifiedClosure_of_pow_eq_one`, as `ω^{q-1} = 1` with `p ∤ q-1`). Since `μ_e ⊆ κ(ω) ⊆ F` and `L/F` is cyclic of degree `e = #G_0` (image of the cyclic `G_0`), Kummer theory over `F` (`Polynomial.KummerExtension.exists_root_adjoin_eq_top_of_isCyclic`) gives `L = F(α)` with `α^e ∈ F ⊆ κ^{ur}`; `NK.TameStructureDeep.Tame.pow_class_unramifiedClosure_pow` writes `α^e = π^j c^e` with `c ∈ κ^{ur}`, so `(α/c)^e = π^j` and `α/c` is `π^{j/e}` up to a root of unity, and since `π^{1/e} ∈ T` (`e` prime to `p`) we get `α ∈ T` and hence `L ⊆ T`. Finally `M^{G_1} = L`, and `comap M.val T` is exactly `M ∩ κ^{tr}`. -/
theorem wildInertia_le_tameClosure {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    (M : IntermediateField (𝔭.adicCompletion K) K') [FiniteDimensional (𝔭.adicCompletion K) M]
    [IsGalois (𝔭.adicCompletion K) M]
    (A : ValuationSubring M) [IsDiscreteValuationRing A]
    [PerfectField (IsLocalRing.ResidueField A)]
    (hdec : A.decompositionSubgroup (𝔭.adicCompletion K) = ⊤)
    (f : ℕ) (hp : (NK.TameStructureDeep.Tame.resCharAt 𝔭).Prime)
    (hq : Nat.card (IsLocalRing.ResidueField A) = (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f) :
    IntermediateField.fixedField
        (Subgroup.map (A.decompositionSubgroup (𝔭.adicCompletion K)).subtype
          (NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 1))
      ≤ IntermediateField.comap M.val (NK.TameStructureDeep.Tame.tameClosure
          (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)) := by
  classical
  haveI : Algebra.IsAlgebraic (𝔭.adicCompletion K) M := Algebra.IsAlgebraic.of_finite _ _
  -- the valuation ring `A` of `M` is Henselian, being the (unique) extension of `𝒪_κ`
  haveI : HenselianLocalRing A :=
    NK.TameStructureDeep.Tame.henselianLocalRing_of_isDiscreteValuationRing 𝔭 A
  -- its residue field has cardinality a power of the residue characteristic
  have hcard : ∃ f : ℕ, Nat.card (IsLocalRing.ResidueField A) =
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f := ⟨f, hq⟩
  -- the inertia field is unramified
  have hU := NK.TameStructureDeep.Tame.inertiaFixedField_le_unramifiedClosure
    (K := K) 𝔭 (M := M) A hdec hcard
  -- hence the fixed field of the wild inertia, a Kummer extension of the inertia field with
  -- radicand over `κ^{ur}` of prime-to-`p` order, is contained in the tame closure
  have hmain :=
    NK.TameStructureDeep.Tame.fixedField_wildInertia_le_tameClosure_of_inertia_le_unramified
      (K := K) 𝔭 hπ (M := M) A hdec hcard hU
  exact (IntermediateField.map_le_iff_le_comap (f := M.val)).mp hmain

end NK.TameStructureDeep.Tame
