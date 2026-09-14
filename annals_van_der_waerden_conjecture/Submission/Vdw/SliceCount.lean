import Mathlib
import Submission.Vdw.BlockMahler
import Submission.Vdw.ImprimitiveSlice
import Submission.Vdw.WitnessCount
import Submission.Commons.NumberTheory.NumberField.ncard_integral_tuple_mahler_le
import Submission.Commons.NumberTheory.NumberField.finiteDimensional_adjoin_of_isIntegral
import Submission.Commons.NumberTheory.NumberField.mahlerK_algEquiv
import Submission.Commons.NumberTheory.NumberField.mahlerK_eq_prod_algHom
import Submission.Commons.NumberTheory.NumberField.card_algHom_eq_finrank
import Submission.Commons.NumberTheory.Polynomial.ncard_monic_intpoly_mahler_le
import Submission.Commons.FieldTheory.Galois.prod_algHom_map_algEquiv
import Submission.Commons.FieldTheory.Galois.algHom_fieldRange_eq_adjoin_image
import Submission.Commons.NumberTheory.NumberField.minpoly_int_eq_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.natDegree_minpoly_int_eq_finrank_adjoin
import Submission.Commons.NumberTheory.Polynomial.mapMahlerMeasure_minpoly_eq_prod_algHom
import Submission.Commons.NumberTheory.NumberField.isIntegral_map_of_isIntegral
import Submission.Commons.RingTheory.Polynomial.exists_adjoin_single_sum_bounded
import Submission.Commons.NumberTheory.Polynomial.mapMahlerMeasure_minpoly_eq_prod_algHom_simple
import Submission.Commons.NumberTheory.NumberField.finite_setOf_isIntegral_mahler_le
import Submission.Commons.NumberTheory.Polynomial.finite_monic_minpoly_mahler_le
import Submission.Commons.NumberTheory.Polynomial.ncard_monic_minpoly_mahler_le
import Submission.Commons.Analysis.Real.polylog_le_const_mul_rpow
import Submission.Commons.NumberTheory.NumberField.natDegree_minpoly_int_eq_finrank_adjoin_simple

open Polynomial Filter Asymptotics
open scoped BigOperators Pointwise IntermediateField Classical
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option maxHeartbeats 4000000

/-!
# Counting the imprimitive slice by the block polynomial

For `f` in the `k`-slice of the imprimitive box (`k * m = n`), let `L_f` be the
field of definition of a chosen block and `P_f` the block polynomial over it.
Writing `c_j` for the coefficients of `P_f` and choosing a generator
`γ = Σ_j μ_j c_j` of `L_f` (`μ` from the finite set `Fin k → Fin (m²+2)`), the
map

`f ↦ (ψ_f(γ_f), ψ_f(c_1), …, ψ_f(c_{k-1})) ∈ ℂ^k`

(`ψ_f` a complex embedding of `L_f`) is *injective* (the norm identity
`normIdentity` recovers `f` from the block polynomial), and
`#{γ}` is `≪ H^m` while the fibre is `≪ H^{k-1} (log H)^{m-1}`
(`ncard_monic_intpoly_mahler_le`, `ncard_integral_tuple_mahler_le`).  Summing
over the finitely many `μ` gives the slice bound `≪ H^{k+m-1+ε}`, which is
`O(H^{n-1})` as soon as `(k-1)(m-1) ≥ 2`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

variable {n H k m : ℕ}

/-! ## The chosen block data of a slice polynomial -/

/-- A chosen irreducibility witness of a slice polynomial. -/
def sliceIrred (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) : Irreducible (f.map φℚ) :=
  Classical.choose hf.2.2

/-- The separability of the rational image of a slice polynomial. -/
def sliceSep (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) : (f.map φℚ).Separable :=
  separable_of_irreducible_rat (sliceIrred f hf)

/-- The degree of a slice polynomial is `n`. -/
lemma sliceNatDegree (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) :
    (f.map φℚ).natDegree = n := by
  rw [monic_natDegree_map_rat f hf.1.1, Polynomial.natDegree_eq_of_degree_eq_some hf.1.2.1]

/-- A chosen block of a slice polynomial (naive action). -/
def sliceBlock (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) :
    Set (Fin ((f.map φℚ).natDegree)) :=
  Classical.choose ((hasBlockSize_iff f (sliceIrred f hf) k).mp
    (Classical.choose_spec hf.2.2))

/-- The chosen block is a block of the naive Galois action. -/
lemma sliceBlock_isBlock (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) :
    MulAction.IsBlock (galFinHomN (f.map φℚ) (sliceSep f hf)).range (sliceBlock f hf) :=
  (Classical.choose_spec ((hasBlockSize_iff f (sliceIrred f hf) k).mp
    (Classical.choose_spec hf.2.2))).1

/-- The chosen block has cardinality `k`. -/
lemma sliceBlock_ncard (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) :
    (sliceBlock f hf).ncard = k :=
  (Classical.choose_spec ((hasBlockSize_iff f (sliceIrred f hf) k).mp
    (Classical.choose_spec hf.2.2))).2

lemma sliceBlock_nonempty (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hk : 2 ≤ k) :
    (sliceBlock f hf).Nonempty := by
  have h := sliceBlock_ncard f hf
  by_contra hc
  rw [Set.not_nonempty_iff_eq_empty] at hc
  rw [hc, Set.ncard_empty] at h
  omega

lemma slice_pretransitive (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) :
    MulAction.IsPretransitive (↥(galImg (f.map φℚ) (sliceSep f hf)))
      (Fin (f.map φℚ).natDegree) := by
  haveI : Fact ((Polynomial.map (algebraMap ℚ (f.map φℚ).SplittingField)
      (f.map φℚ)).Splits) := ⟨Polynomial.SplittingField.splits (f.map φℚ)⟩
  exact galFinHomN_pretransitive (f.map φℚ) (sliceIrred f hf) (sliceSep f hf)

/-- The field of definition of the chosen block. -/
abbrev sliceL (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) :
    IntermediateField ℚ (f.map φℚ).SplittingField :=
  sfield (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)

/-- The block polynomial over the field of definition. -/
abbrev slicePL (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) : (↥(sliceL f hf))[X] :=
  spolyL (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)

/-- The degree of the block field is `m` (given `k * m = n`). -/
theorem slice_finrank (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n) (hk : 2 ≤ k) :
    Module.finrank ℚ ↥(sliceL f hf) = m := by
  haveI : Fact ((Polynomial.map (algebraMap ℚ (f.map φℚ).SplittingField)
      (f.map φℚ)).Splits) := ⟨Polynomial.SplittingField.splits (f.map φℚ)⟩
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨sliceIrred f hf⟩
  have h1 : (MulAction.orbit (↥(galImg (f.map φℚ) (sliceSep f hf)))
      (sliceBlock f hf)).ncard * (sliceBlock f hf).ncard
        = Nat.card (Fin (f.map φℚ).natDegree) :=
    Commons.GroupTheory.GroupAction.ncard_orbit_mul_ncard_of_isBlock
      (slice_pretransitive f hf) (sliceBlock_isBlock f hf) (sliceBlock_nonempty f hf hk)
  rw [Nat.card_fin, sliceBlock_ncard f hf] at h1
  have h2 : (MulAction.orbit (↥(galImg (f.map φℚ) (sliceSep f hf)))
      (sliceBlock f hf)).ncard * k = m * k := by
    rw [mul_comm m k]
    exact (h1.trans (sliceNatDegree f hf)).trans hkm.symm
  have hk0 : 0 < k := by omega
  have hcard : (MulAction.orbit (↥(galImg (f.map φℚ) (sliceSep f hf)))
      (sliceBlock f hf)).ncard = m :=
    Nat.eq_of_mul_eq_mul_right hk0 h2
  have h3 : (orbitF (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)).card
      = (MulAction.orbit (↥(galImg (f.map φℚ) (sliceSep f hf)))
          (sliceBlock f hf)).ncard := orbitF_card _ _ _
  rw [hcard] at h3
  exact (card_orbitF_eq_finrank (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)
    (sliceBlock_isBlock f hf)).symm.trans h3

/-- The complex embedding of the block field attached to the slice data. -/
def slicePsi (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) : ↥(sliceL f hf) →ₐ[ℚ] ℂ :=
  (Classical.choice (exists_algHom_complex (f.map φℚ))).comp (sliceL f hf).val

/-! ## The generator and its complex value -/

/-- The candidate generator `Σ_{j<k} μ_j c_j` of the block field, formed from
the coefficients of the block polynomial. -/
def sliceGamma (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (μ : Fin k → ℕ) :
    ↥(sliceL f hf) :=
  ∑ j : Fin k, ((μ j : ℕ) : ↥(sliceL f hf)) * (slicePL f hf).coeff (j : ℕ)

/-- The complex value of the generator (`ψ(γ)`), i.e. the candidate for the
generator of the field `ℚ(b)` attached to the slice data. -/
def sliceZ (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (μ : Fin k → ℕ) : ℂ :=
  slicePsi f hf (sliceGamma f hf μ)

/-- `ψ(γ) = Σ_j μ_j ψ(c_j)`. -/
lemma sliceZ_eq_sum (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (μ : Fin k → ℕ) :
    sliceZ f hf μ = ∑ j : Fin k, ((μ j : ℕ) : ℂ) * slicePsi f hf ((slicePL f hf).coeff (j : ℕ)) := by
  rw [sliceZ, sliceGamma, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, map_natCast]

/-! ## The block field is generated by the block coefficients -/

/-- The block polynomial coefficients generate the field of definition. -/
lemma adjoin_coeff_eq_top (p : ℚ[X]) (hsep : p.Separable) (B : Set (Fin p.natDegree)) :
    Algebra.adjoin ℚ (Set.range fun i : Fin p.natDegree => (spolyL p hsep B).coeff i) = ⊤ := by
  haveI : Algebra.IsAlgebraic ℚ ↥(sfield p hsep B) := inferInstance
  rw [← IntermediateField.adjoin_eq_top_iff]
  have hrange : ((sfield p hsep B).val ''
        (Set.range fun i : Fin p.natDegree => (spolyL p hsep B).coeff i))
      = Set.range fun i : Fin p.natDegree => (spoly p hsep B).coeff i := by
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (sfield_val_coeff p hsep B i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, sfield_val_coeff p hsep B i⟩
  have hfr : (sfield p hsep B).val.fieldRange = sfield p hsep B := by
    ext y
    rw [AlgHom.mem_fieldRange]
    constructor
    · rintro ⟨x, rfl⟩; exact x.2
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
  have key : IntermediateField.map (sfield p hsep B).val
      (IntermediateField.adjoin ℚ
        (Set.range fun i : Fin p.natDegree => (spolyL p hsep B).coeff i))
      = IntermediateField.map (sfield p hsep B).val ⊤ := by
    rw [IntermediateField.adjoin_map, hrange, ← AlgHom.fieldRange_eq_map (sfield p hsep B).val,
      hfr]
    rfl
  exact IntermediateField.map_injective (sfield p hsep B).val key

/-- The block coefficients, indexed by `Fin k` instead of `Fin (natDegree)`,
still generate the field of definition. -/
lemma adjoin_coeff_eq_top_k (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hm : 0 < m)
    (hkm : k * m = n) :
    Algebra.adjoin ℚ (Set.range fun j : Fin k => (slicePL f hf).coeff (j : ℕ)) = ⊤ := by
  have hkn : k ≤ (f.map φℚ).natDegree := by
    rw [sliceNatDegree f hf, ← hkm]
    exact Nat.le_mul_of_pos_right k hm
  have hdeg : (spolyL (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)).natDegree = k :=
    (spolyL_natDegree (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)).trans
      (sliceBlock_ncard f hf)
  have hmon := spolyL_monic (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)
  have hbase := adjoin_coeff_eq_top (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)
  refine le_antisymm le_top ?_
  rw [← hbase]
  refine Algebra.adjoin_le_iff.mpr fun y hy => ?_
  obtain ⟨i, rfl⟩ := hy
  dsimp only
  rcases lt_trichotomy (i : ℕ) k with hi | hi | hi
  · exact Algebra.subset_adjoin ⟨⟨i, hi⟩, rfl⟩
  · have hik : (i : ℕ) = (spolyL (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)).natDegree := by
      rw [hdeg]; exact hi
    have h1 : (spolyL (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)).coeff (i : ℕ) = 1 :=
      (congrArg (fun m => (spolyL (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)).coeff m)
        hik).trans (hmon.leadingCoeff ▸ Polynomial.coeff_natDegree)
    rw [h1]
    exact Subalgebra.one_mem _
  · have h0 : (spolyL (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)).coeff (i : ℕ) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h0]
    exact Subalgebra.zero_mem _

/-! ## Covering the slice by `µ`-slices -/

/-- **Covering by `µ`-slices.**  For every slice polynomial there is
`μ : Fin k → Fin (m²+2)` with `μ_0 ≠ 0` such that the generator `Σ_j μ_j c_j` of
the block coefficients generates the whole block field. -/
theorem muGood_covers (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n)
    (hk : 2 ≤ k) (hm : 2 ≤ m) (hn0 : 0 < n) :
    ∃ μ : Fin k → Fin (m * m + 2), (∀ hk0 : 0 < k, μ ⟨0, hk0⟩ ≠ 0) ∧
      IntermediateField.adjoin ℚ ({sliceGamma f hf (fun j => (μ j : ℕ))} :
        Set ↥(sliceL f hf)) = ⊤ := by
  haveI : Fact ((Polynomial.map (algebraMap ℚ (f.map φℚ).SplittingField)
      (f.map φℚ)).Splits) := ⟨Polynomial.SplittingField.splits (f.map φℚ)⟩
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨sliceIrred f hf⟩
  haveI : NumberField ↥(sliceL f hf) := ⟨⟩
  have hfin : Module.finrank ℚ ↥(sliceL f hf) = m := slice_finrank f hf hkm hk
  have hk0 : 0 < k := by omega
  have hgen : Algebra.adjoin ℚ (Set.range fun j : Fin k => (slicePL f hf).coeff (j : ℕ)) = ⊤ :=
    adjoin_coeff_eq_top_k f hf (by omega) hkm
  obtain ⟨μ', hμ'0, hμ'bd, hμ'gen⟩ :=
    Commons.RingTheory.Polynomial.exists_adjoin_single_sum_bounded
      (fun j : Fin k => (slicePL f hf).coeff (j : ℕ)) hgen ⟨0, hk0⟩
  have hbound : ∀ j, μ' j ≤ m * m + 1 := by
    intro j
    have h := hμ'bd j
    rw [hfin] at h
    calc μ' j ≤ m ^ 2 + 1 := h
      _ = m * m + 1 := by ring
  refine ⟨fun j => ⟨μ' j, by have := hbound j; omega⟩, ?_, ?_⟩
  · intro hk0' hcon
    have h1 : μ' ⟨0, hk0'⟩ = 0 := congrArg Fin.val hcon
    have h2 : μ' ⟨0, hk0⟩ = 0 := by
      rw [← show (⟨0, hk0'⟩ : Fin k) = ⟨0, hk0⟩ from Fin.ext rfl]
      exact h1
    exact hμ'0 h2
  · have hsum : sliceGamma f hf (fun j => ((⟨μ' j, by have := hbound j; omega⟩ :
        Fin (m * m + 2)) : ℕ))
        = ∑ j : Fin k, ((μ' j : ℕ) : ↥(sliceL f hf)) * (slicePL f hf).coeff (j : ℕ) := by
      rw [sliceGamma]
    rw [hsum]
    exact IntermediateField.adjoin_eq_top_iff.mpr hμ'gen

/-! ## The `µ`-slices -/

/-- The `μ`-slice of the imprimitive box: the slice polynomials for which the
generator `Σ_j μ_j c_j` has nonzero top coefficient `μ_0` and generates the
block field. -/
def muGood (n H k m : ℕ) (μ : Fin k → Fin (m * m + 2)) : Set ℤ[X] :=
  {f | ∃ hf : f ∈ imprimSlice n H k, ∃ hk : 0 < k, μ ⟨0, hk⟩ ≠ 0 ∧
      IntermediateField.adjoin ℚ ({sliceGamma f hf (fun i => (μ i : ℕ))} :
        Set ↥(sliceL f hf)) = ⊤}

/-- The top coefficient `μ_0` of a `muGood` parameter is nonzero. -/
lemma muGood_mu0 (μ : Fin k → Fin (m * m + 2)) {f : ℤ[X]} (hf : f ∈ muGood n H k m μ)
    {hk0 : 0 < k} : μ ⟨0, hk0⟩ ≠ 0 := by
  obtain ⟨hf', hk, hμ, -⟩ := hf
  intro hcon
  exact hμ ((congrArg μ (Fin.ext rfl)).trans hcon)

/-- **The `µ`-slices cover the slice.** -/
lemma imprimSlice_subset_iUnion_muGood (hkm : k * m = n) (hk : 2 ≤ k) (hm : 2 ≤ m)
    (hn0 : 0 < n) :
    imprimSlice n H k ⊆ ⋃ μ : Fin k → Fin (m * m + 2), muGood n H k m μ := by
  intro f hf
  obtain ⟨μ, hμ0, hμgen⟩ := muGood_covers f hf hkm hk hm hn0
  refine Set.mem_iUnion.mpr ⟨μ, ?_⟩
  exact ⟨hf, by omega, hμ0 _, hμgen⟩

/-! ## The range of the slice embedding -/

/-- **The range of the slice embedding is the field generated by the
generator.**  If `γ` generates the block field then `ψ(L) = ℚ(ψ(γ))`. -/
lemma slice_fieldRange (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤) :
    (slicePsi f hf).fieldRange
      = IntermediateField.adjoin ℚ ({sliceZ f hf μ} : Set ℂ) := by
  have h := Commons.FieldTheory.Galois.algHom_fieldRange_eq_adjoin_image (slicePsi f hf)
    ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) hgen
  rw [Set.image_singleton] at h
  have hz : sliceZ f hf μ = slicePsi f hf (sliceGamma f hf μ) := rfl
  rw [h, ← hz]

/-- Every value of the slice embedding lies in the field generated by the
generator. -/
lemma slicePsi_mem (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    (x : ↥(sliceL f hf)) :
    slicePsi f hf x ∈ IntermediateField.adjoin ℚ ({sliceZ f hf μ} : Set ℂ) := by
  rw [← slice_fieldRange f hf μ hgen]
  exact (AlgHom.mem_fieldRange).mpr ⟨x, rfl⟩

/-! ## The isomorphism of the block field with `ℚ(b)` -/

/-- A chosen complex embedding of the splitting field. -/
noncomputable def sliceIota (f : ℤ[X]) : (f.map φℚ).SplittingField →ₐ[ℚ] ℂ :=
  Classical.choice (exists_algHom_complex (f.map φℚ))

/-- The slice embedding, with values in the field `ℚ(b)` generated by the
complex value of the generator. -/
noncomputable def sliceHom (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf μ = b) : ↥(sliceL f hf) →ₐ[ℚ] ↥(ℚ⟮b⟯) where
  toFun x := ⟨slicePsi f hf x, by rw [← hb]; exact slicePsi_mem f hf μ hgen x⟩
  map_one' := Subtype.ext (map_one (slicePsi f hf))
  map_mul' x y := Subtype.ext (map_mul (slicePsi f hf) x y)
  map_zero' := Subtype.ext (map_zero (slicePsi f hf))
  map_add' x y := Subtype.ext (map_add (slicePsi f hf) x y)
  commutes' r := Subtype.ext (by
    show ((slicePsi f hf) (algebraMap ℚ ↥(sliceL f hf) r) : ℂ) =
      ((algebraMap ℚ ↥(ℚ⟮b⟯) r : ↥(ℚ⟮b⟯)) : ℂ)
    rw [AlgHom.commutes]
    rfl)

@[simp]
lemma sliceHom_apply (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf μ = b) (x : ↥(sliceL f hf)) :
    ((sliceHom f hf μ hgen hb x : ↥(ℚ⟮b⟯)) : ℂ) = slicePsi f hf x := rfl

/-! ## The degree of the field generated by the slice data -/

/-- The coefficients of the block polynomial are integral over `ℤ`. -/
lemma isIntegral_slicePL_coeff (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (j : ℕ) :
    IsIntegral ℤ ((slicePL f hf).coeff j) :=
  isIntegral_spolyL_coeff (f := f) (hsep := sliceSep f hf) hf.1.1 (sliceBlock f hf) j

/-- The complex value of the generator is integral over `ℤ`. -/
lemma isIntegral_sliceZ (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (μ : Fin k → ℕ) :
    IsIntegral ℤ (sliceZ f hf μ) := by
  have h : IsIntegral ℤ (sliceGamma f hf μ) := by
    rw [sliceGamma]
    exact IsIntegral.sum _ fun j _ =>
      IsIntegral.mul (isIntegral_natCast' (μ j)) (isIntegral_slicePL_coeff f hf j)
  rw [sliceZ]
  exact IsIntegral.map (slicePsi f hf) h

/-- **The degree of `ℚ(ψ(γ))` is at most the degree of the block field.** -/
lemma finrank_adjoin_sliceZ_le (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤) :
    Module.finrank ℚ ↥(ℚ⟮sliceZ f hf μ⟯) ≤ Module.finrank ℚ ↥(sliceL f hf) := by
  haveI : NumberField ↥(sliceL f hf) := ⟨⟩
  have hbint : IsIntegral ℚ (sliceZ f hf μ) := (isIntegral_sliceZ f hf μ).tower_top
  have hgint : IsIntegral ℚ (sliceGamma f hf μ) := Algebra.IsIntegral.isIntegral _
  have haeval : Polynomial.aeval (sliceZ f hf μ) (minpoly ℚ (sliceGamma f hf μ)) = 0 := by
    rw [sliceZ, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have h3 : Module.finrank ℚ ↥(sliceL f hf) = (minpoly ℚ (sliceGamma f hf μ)).natDegree := by
    have hfr : Module.finrank ℚ
          (IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)))
        = (minpoly ℚ (sliceGamma f hf μ)).natDegree :=
      IntermediateField.adjoin.finrank hgint
    rw [← hfr, hgen, IntermediateField.finrank_top']
  calc Module.finrank ℚ ↥(ℚ⟮sliceZ f hf μ⟯)
      = (minpoly ℚ (sliceZ f hf μ)).natDegree := IntermediateField.adjoin.finrank hbint
    _ ≤ (minpoly ℚ (sliceGamma f hf μ)).natDegree := by
        refine Polynomial.natDegree_le_of_dvd ?_ (minpoly.ne_zero hgint)
        exact minpoly.dvd ℚ (sliceZ f hf μ) haeval
    _ = Module.finrank ℚ ↥(sliceL f hf) := h3.symm

/-- `ℚ(ψ(γ))` is a number field. -/
lemma numberField_adjoin_sliceZ (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (μ : Fin k → ℕ) :
    NumberField ↥(ℚ⟮sliceZ f hf μ⟯) := by
  haveI := Commons.NumberTheory.NumberField.finiteDimensional_adjoin_of_isIntegral
    (sliceZ f hf μ) (isIntegral_sliceZ f hf μ)
  exact ⟨⟩

/-- **The degree of `ℚ(ψ(γ))` is exactly `m`.** -/
lemma finrank_adjoin_sliceZ (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n)
    (hk : 2 ≤ k) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤) :
    Module.finrank ℚ ↥(ℚ⟮sliceZ f hf μ⟯) = m := by
  haveI : NumberField ↥(sliceL f hf) := ⟨⟩
  haveI : NumberField ↥(ℚ⟮sliceZ f hf μ⟯) := numberField_adjoin_sliceZ f hf μ
  have h1 : Module.finrank ℚ ↥(ℚ⟮sliceZ f hf μ⟯) ≤ m :=
    (finrank_adjoin_sliceZ_le f hf μ hgen).trans (le_of_eq (slice_finrank f hf hkm hk))
  have h2 : m ≤ Module.finrank ℚ ↥(ℚ⟮sliceZ f hf μ⟯) := by
    have hinj : Function.Injective (sliceHom f hf μ hgen rfl) :=
      RingHom.injective (sliceHom f hf μ hgen rfl).toRingHom
    have h := LinearMap.finrank_le_finrank_of_injective
      (f := (sliceHom f hf μ hgen rfl).toLinearMap) hinj
    rwa [slice_finrank f hf hkm hk] at h
  exact le_antisymm h1 h2

/-! ## The slice embedding is an isomorphism -/

/-- **The slice embedding onto `ℚ(b)` is bijective** (it is an injective map of
`ℚ`-vector spaces of the same dimension `m`). -/
lemma sliceHom_bijective (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n)
    (hk : 2 ≤ k) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf μ = b)
    [NumberField ↥(ℚ⟮b⟯)] (hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m) :
    Function.Bijective (sliceHom f hf μ hgen hb) := by
  haveI : NumberField ↥(sliceL f hf) := ⟨⟩
  have hinj : Function.Injective (sliceHom f hf μ hgen hb) :=
    RingHom.injective (sliceHom f hf μ hgen hb).toRingHom
  refine ⟨hinj, ?_⟩
  have hfd : Module.finrank ℚ ↥(sliceL f hf) = Module.finrank ℚ ↥(ℚ⟮b⟯) := by
    rw [slice_finrank f hf hkm hk, hfin]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (sliceHom f hf μ hgen hb).toLinearMap) hfd).mp hinj

/-- **The block field is isomorphic to `ℚ(b)`** where `b = ψ(γ)`. -/
noncomputable def sliceEquiv (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n)
    (hk : 2 ≤ k) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf μ = b)
    [NumberField ↥(ℚ⟮b⟯)] (hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m) :
    ↥(sliceL f hf) ≃ₐ[ℚ] ↥(ℚ⟮b⟯) :=
  AlgEquiv.ofBijective (sliceHom f hf μ hgen hb)
    (sliceHom_bijective f hf hkm hk μ hgen hb hfin)

@[simp]
lemma sliceEquiv_apply (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n)
    (hk : 2 ≤ k) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf μ = b)
    [NumberField ↥(ℚ⟮b⟯)] (hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m) (x : ↥(sliceL f hf)) :
    sliceEquiv f hf hkm hk μ hgen hb hfin x = sliceHom f hf μ hgen hb x := rfl

/-! ## The block polynomial over `ℚ(b)` -/

/-- The block polynomial, transported to the field `ℚ(b)` along the slice
isomorphism. -/
noncomputable def sliceQB (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n)
    (hk : 2 ≤ k) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf μ = b)
    [NumberField ↥(ℚ⟮b⟯)] (hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m) : (↥(ℚ⟮b⟯))[X] :=
  (slicePL f hf).map (sliceEquiv f hf hkm hk μ hgen hb hfin).toRingHom

@[simp]
lemma sliceQB_coeff (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n) (hk : 2 ≤ k)
    (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf μ = b)
    [NumberField ↥(ℚ⟮b⟯)] (hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m) (j : ℕ) :
    (sliceQB f hf hkm hk μ hgen hb hfin).coeff j
      = sliceEquiv f hf hkm hk μ hgen hb hfin ((slicePL f hf).coeff j) :=
  Polynomial.coeff_map _ j

lemma sliceQB_monic (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n) (hk : 2 ≤ k)
    (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf μ = b)
    [NumberField ↥(ℚ⟮b⟯)] (hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m) :
    (sliceQB f hf hkm hk μ hgen hb hfin).Monic :=
  (spolyL_monic (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)).map _

lemma sliceQB_natDegree (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n) (hk : 2 ≤ k)
    (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf μ = b)
    [NumberField ↥(ℚ⟮b⟯)] (hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m) :
    (sliceQB f hf hkm hk μ hgen hb hfin).natDegree = k :=
  ((spolyL_monic (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)).natDegree_map _).trans
    ((spolyL_natDegree (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)).trans
      (sliceBlock_ncard f hf))

/-! ## The norm identity over `ℚ(b)` -/

/-- **The norm identity over `ℚ(b)`**: `f` is recovered from the block
polynomial over `ℚ(b)`. -/
theorem slice_normIdentityB (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n)
    (hk : 2 ≤ k) (hmonic : (f.map φℚ).Monic) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf μ = b)
    [NumberField ↥(ℚ⟮b⟯)] (hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m) :
    (∏ χ : (↥(ℚ⟮b⟯) →ₐ[ℚ] ℂ), (sliceQB f hf hkm hk μ hgen hb hfin).map χ.toRingHom)
      = (f.map φℚ).map (algebraMap ℚ ℂ) := by
  haveI : Fact ((Polynomial.map (algebraMap ℚ (f.map φℚ).SplittingField)
      (f.map φℚ)).Splits) := ⟨Polynomial.SplittingField.splits (f.map φℚ)⟩
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨sliceIrred f hf⟩
  haveI : NumberField ↥(sliceL f hf) := ⟨⟩
  haveI hpre : MulAction.IsPretransitive (↥(galImg (f.map φℚ) (sliceSep f hf)))
      (Fin (f.map φℚ).natDegree) := slice_pretransitive f hf
  have hNI := normIdentity (f.map φℚ) (sliceSep f hf) hmonic (sliceBlock_isBlock f hf)
    (sliceBlock_nonempty f hf hk) (sliceIota f)
  have hkey := Commons.FieldTheory.Galois.prod_algHom_map_algEquiv
    (sliceEquiv f hf hkm hk μ hgen hb hfin) (slicePL f hf)
  exact hkey.trans hNI

/-! ## Integrality and the Mahler bound of the coordinates -/

/-- The coefficients of `sliceQB` are integral over `ℤ`. -/
lemma isIntegral_sliceQB_coeff (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n)
    (hk : 2 ≤ k) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf μ = b)
    [NumberField ↥(ℚ⟮b⟯)] (hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m) (j : ℕ) :
    IsIntegral ℤ ((sliceQB f hf hkm hk μ hgen hb hfin).coeff j) := by
  have hx : IsIntegral ℤ ((slicePL f hf).coeff j) := isIntegral_slicePL_coeff f hf j
  rw [sliceQB_coeff]
  exact IsIntegral.map (sliceEquiv f hf hkm hk μ hgen hb hfin) hx

/-- The Mahler measure of the coefficients of `sliceQB` is bounded by
`2^(k*m) · Y` once `M(f_ℂ) ≤ Y`. -/
theorem mahlerK_sliceQB_coeff_le (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n)
    (hk : 2 ≤ k) (hmonic : (f.map φℚ).Monic) (μ : Fin k → ℕ)
    (hgen : IntermediateField.adjoin ℚ ({sliceGamma f hf μ} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf μ = b)
    [NumberField ↥(ℚ⟮b⟯)]
    (hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m) {Y : ℝ}
    (hY : ((f.map φℚ).map (algebraMap ℚ ℂ)).mahlerMeasure ≤ Y) (j : ℕ) :
    Commons.NumberTheory.NumberField.mahlerK ↥(ℚ⟮b⟯)
        ((sliceQB f hf hkm hk μ hgen hb hfin).coeff j) ≤ 2 ^ (k * m) * Y := by
  haveI : Fact ((Polynomial.map (algebraMap ℚ (f.map φℚ).SplittingField)
      (f.map φℚ)).Splits) := ⟨Polynomial.SplittingField.splits (f.map φℚ)⟩
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨sliceIrred f hf⟩
  haveI : NumberField ↥(sliceL f hf) := ⟨⟩
  haveI hpre : MulAction.IsPretransitive (↥(galImg (f.map φℚ) (sliceSep f hf)))
      (Fin (f.map φℚ).natDegree) := slice_pretransitive f hf
  have hmain := mahlerK_spolyL_coeff_le (f.map φℚ) (sliceSep f hf) (sliceBlock_isBlock f hf)
    (sliceBlock_nonempty f hf hk) (sliceIota f) hmonic hY
    (fun i => isIntegral_spolyL_coeff (f := f) (hsep := sliceSep f hf) hf.1.1
      (sliceBlock f hf) i) j
  have hcard : (sliceBlock f hf).ncard = k := sliceBlock_ncard f hf
  have hfl : Module.finrank ℚ ↥(sliceL f hf) = m := slice_finrank f hf hkm hk
  have hrew : Commons.NumberTheory.NumberField.mahlerK ↥(ℚ⟮b⟯)
        (sliceEquiv f hf hkm hk μ hgen hb hfin ((slicePL f hf).coeff j))
      = Commons.NumberTheory.NumberField.mahlerK ↥(sliceL f hf) ((slicePL f hf).coeff j) :=
    Commons.NumberTheory.NumberField.mahlerK_algEquiv
      (sliceEquiv f hf hkm hk μ hgen hb hfin) _
  rw [sliceQB_coeff, hrew]
  calc Commons.NumberTheory.NumberField.mahlerK ↥(sliceL f hf) ((slicePL f hf).coeff j)
      ≤ 2 ^ ((sliceBlock f hf).ncard * Module.finrank ℚ ↥(sliceL f hf)) * Y := hmain
    _ = 2 ^ (k * m) * Y := by rw [hcard, hfl]

/-! ## The counting bounds -/

/-- The Mahler bound for a box polynomial of degree `n` and height `H`. -/
def sliceMf (n H : ℕ) : ℝ := ((n : ℝ) + 1) * ((H : ℝ) + 1)

/-- The Mahler bound for the block coefficients. -/
def sliceYC (n H k m : ℕ) : ℝ := 2 ^ (k * m) * sliceMf n H

/-- The Mahler bound for the generator. -/
def sliceYG (n H k m : ℕ) : ℝ := ((n * (m * m + 1) * 2 ^ k : ℕ) : ℝ) ^ m * sliceMf n H

/-- The fibre bound. -/
def sliceFib (n H k m : ℕ) : ℝ :=
  ((200000 : ℝ) ^ m * sliceYC n H k m * (1 + Real.log (sliceYC n H k m)) ^ (m - 1)) ^ (k - 1)

/-- The generator count bound. -/
def sliceGen (n H k m : ℕ) : ℝ := (m : ℝ) * ((2 : ℝ) ^ (m + 2) * sliceYG n H k m) ^ m

/-- The map `f ↦ ψ_f(γ_f)` on the whole box. -/
noncomputable def sliceZAll (n H k : ℕ) (μ : Fin k → ℕ) (f : ℤ[X]) : ℂ :=
  if hf : f ∈ imprimSlice n H k then sliceZ f hf μ else 0

lemma sliceZAll_eq {f : ℤ[X]} (hf : f ∈ imprimSlice n H k) (μ : Fin k → ℕ) :
    sliceZAll n H k μ f = sliceZ f hf μ := dif_pos hf

lemma map_map_int (f : ℤ[X]) :
    (f.map φℚ).map (algebraMap ℚ ℂ) = f.map (Int.castRingHom ℂ) := by
  have h : (algebraMap ℚ ℂ).comp φℚ = Int.castRingHom ℂ := by
    rw [φℚ]
    exact (IsScalarTower.algebraMap_eq ℤ ℚ ℂ).symm
  rw [Polynomial.map_map, h]

/-- The Mahler measure of `f` over `ℂ` is at most `sliceMf n H` for a box polynomial. -/
lemma mahlerMeasure_map_le_sliceMf {f : ℤ[X]} (hf : f ∈ Box n H) :
    ((f.map φℚ).map (algebraMap ℚ ℂ)).mahlerMeasure ≤ sliceMf n H := by
  rw [map_map_int, sliceMf]
  exact mahlerMeasure_mem_Box_le hf

lemma one_le_sliceMf (n H : ℕ) : 1 ≤ sliceMf n H := by
  rw [sliceMf]
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h2 : (1 : ℝ) ≤ (H : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    linarith
  nlinarith

lemma one_le_sliceYC (n H k m : ℕ) : 1 ≤ sliceYC n H k m := by
  rw [sliceYC]
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_sliceMf n H)

lemma one_le_sliceYG (n H k m : ℕ) (hn : 1 ≤ n) : 1 ≤ sliceYG n H k m := by
  rw [sliceYG]
  refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ ?_) (one_le_sliceMf n H)
  have h : 1 ≤ n * (m * m + 1) * 2 ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact_mod_cast h

/-! ## Splitting a sum over `Fin k` -/

lemma fin_succ_lt {k : ℕ} (hk : 1 ≤ k) {i : Fin (k - 1)} : (i : ℕ) + 1 < k :=
  calc (i : ℕ) + 1 ≤ k - 1 := Nat.succ_le_of_lt i.2
    _ < k := Nat.sub_lt (by omega) (by omega)

lemma sum_fin_split {M : Type*} [AddCommMonoid M] {k : ℕ} (hk : 1 ≤ k) (f : Fin k → M) :
    (∑ j : Fin k, f j)
      = f ⟨0, hk⟩ + ∑ i : Fin (k - 1), f ⟨(i : ℕ) + 1, fin_succ_lt hk⟩ := by
  classical
  set g : ℕ → M := fun m => if h : m < k then f ⟨m, h⟩ else 0 with hgdef
  have h1a : (∑ j : Fin k, f j) = ∑ j : Fin k, g (j : ℕ) :=
    Finset.sum_congr rfl fun j _ => by
      rw [hgdef]
      simp only
      rw [dif_pos j.2]
  have h1b : (∑ j : Fin k, g (j : ℕ)) = ∑ m ∈ Finset.range k, g m :=
    Fin.sum_univ_eq_sum_range g k
  have h2 : (∑ m ∈ Finset.range k, g m) = g 0 + ∑ m ∈ Finset.range (k - 1), g (m + 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [Finset.sum_range_succ', add_comm]
  have h3 : (∑ m ∈ Finset.range (k - 1), g (m + 1))
      = ∑ i : Fin (k - 1), f ⟨(i : ℕ) + 1, fin_succ_lt hk⟩ := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => g (m + 1)) (k - 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hgdef]
    simp only
    rw [dif_pos (fin_succ_lt hk)]
  have h4 : g 0 = f ⟨0, hk⟩ := by
    rw [hgdef]
    simp only
    rw [dif_pos (show 0 < k from hk)]
  rw [h1a, h1b, h2, h3, h4]

/-! ## The generator relation over `ℚ(b)` -/

/-- **The generator relation over `ℚ(b)`**: `b` is the image of `Σ_j μ_j c_j`. -/
theorem sliceQB_generator_eq (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n)
    (hk : 2 ≤ k) (μ : Fin k → Fin (m * m + 2))
    (hgen : IntermediateField.adjoin ℚ
      ({sliceGamma f hf (fun i => (μ i : ℕ))} : Set ↥(sliceL f hf)) = ⊤)
    {b : ℂ} (hb : sliceZ f hf (fun i => (μ i : ℕ)) = b)
    [NumberField ↥(ℚ⟮b⟯)] (hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m) :
    b = ∑ j : Fin k, ((μ j : ℕ) : ℂ)
      * (((sliceQB f hf hkm hk (fun i => (μ i : ℕ)) hgen hb hfin).coeff (j : ℕ) :
        ↥(ℚ⟮b⟯)) : ℂ) := by
  have hcoe : ∀ j : Fin k,
      (((sliceQB f hf hkm hk (fun i => (μ i : ℕ)) hgen hb hfin).coeff (j : ℕ) :
        ↥(ℚ⟮b⟯)) : ℂ) = slicePsi f hf ((slicePL f hf).coeff (j : ℕ)) := by
    intro j
    rw [sliceQB_coeff, sliceEquiv_apply, sliceHom_apply]
  have h1 : (∑ j : Fin k, ((μ j : ℕ) : ℂ)
      * (((sliceQB f hf hkm hk (fun i => (μ i : ℕ)) hgen hb hfin).coeff (j : ℕ) :
        ↥(ℚ⟮b⟯)) : ℂ))
      = ∑ j : Fin k, ((μ j : ℕ) : ℂ) * slicePsi f hf ((slicePL f hf).coeff (j : ℕ)) :=
    Finset.sum_congr rfl fun j _ => by rw [hcoe j]
  have h2 : (∑ j : Fin k, ((μ j : ℕ) : ℂ) * slicePsi f hf ((slicePL f hf).coeff (j : ℕ)))
      = sliceZ f hf (fun i => (μ i : ℕ)) := (sliceZ_eq_sum f hf _).symm
  exact hb.symm.trans (h1.trans h2).symm


/-! ## Injectivity of the block-coefficient tuple -/

/-- The block polynomial of a slice polynomial is monic. -/
lemma sliceMonic (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) : (f.map φℚ).Monic :=
  hf.1.1.map φℚ

/-- **Injectivity of the tuple of block coefficients.**  Two slice polynomials
with the same value `b` of the generator and the same block coefficients
`c_1, …, c_{k-1}` over `ℚ(b)` are equal. -/
theorem slice_tuple_inj {f f' : ℤ[X]} {hf : f ∈ imprimSlice n H k}
    {hf' : f' ∈ imprimSlice n H k} (hkm : k * m = n) (hk : 2 ≤ k)
    (μ : Fin k → Fin (m * m + 2))
    {hgen : IntermediateField.adjoin ℚ
      ({sliceGamma f hf (fun i => (μ i : ℕ))} : Set ↥(sliceL f hf)) = ⊤}
    {hgen' : IntermediateField.adjoin ℚ
      ({sliceGamma f' hf' (fun i => (μ i : ℕ))} : Set ↥(sliceL f' hf')) = ⊤}
    {b : ℂ} {hb : sliceZ f hf (fun i => (μ i : ℕ)) = b}
    {hb' : sliceZ f' hf' (fun i => (μ i : ℕ)) = b}
    [NumberField ↥(ℚ⟮b⟯)] {hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m}
    (hμ0 : ∀ hk0 : 0 < k, μ ⟨0, hk0⟩ ≠ 0)
    (htup : ∀ i : Fin (k - 1),
      (sliceQB f hf hkm hk (fun i => (μ i : ℕ)) hgen hb hfin).coeff ((i : ℕ) + 1)
        = (sliceQB f' hf' hkm hk (fun i => (μ i : ℕ)) hgen' hb' hfin).coeff ((i : ℕ) + 1)) :
    f = f' := by
  classical
  let Q : (↥(ℚ⟮b⟯))[X] := sliceQB f hf hkm hk (fun i => (μ i : ℕ)) hgen hb hfin
  let Q' : (↥(ℚ⟮b⟯))[X] := sliceQB f' hf' hkm hk (fun i => (μ i : ℕ)) hgen' hb' hfin
  have hQnd : Q.natDegree = k := sliceQB_natDegree f hf hkm hk _ hgen hb hfin
  have hQ'nd : Q'.natDegree = k := sliceQB_natDegree f' hf' hkm hk _ hgen' hb' hfin
  have hQm : Q.Monic := sliceQB_monic f hf hkm hk _ hgen hb hfin
  have hQ'm : Q'.Monic := sliceQB_monic f' hf' hkm hk _ hgen' hb' hfin
  have hk1 : 1 ≤ k := by omega
  have hQ : Q = Q' := by
    refine Polynomial.ext fun j => ?_
    rcases lt_trichotomy j k with hj | hj | hj
    · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · rw [hj0]
        have H1 := sliceQB_generator_eq f hf hkm hk μ hgen hb hfin
        have H2 := sliceQB_generator_eq f' hf' hkm hk μ hgen' hb' hfin
        rw [show sliceQB f hf hkm hk (fun i => (μ i : ℕ)) hgen hb hfin = Q from rfl] at H1
        rw [show sliceQB f' hf' hkm hk (fun i => (μ i : ℕ)) hgen' hb' hfin = Q' from rfl] at H2
        rw [sum_fin_split hk1 (fun j : Fin k => ((μ j : ℕ) : ℂ) * ((Q.coeff (j : ℕ) : ↥(ℚ⟮b⟯)) : ℂ))] at H1
        rw [sum_fin_split hk1 (fun j : Fin k => ((μ j : ℕ) : ℂ) * ((Q'.coeff (j : ℕ) : ↥(ℚ⟮b⟯)) : ℂ))] at H2
        have hs : (∑ i : Fin (k - 1), ((μ ⟨(i : ℕ) + 1, fin_succ_lt hk1⟩ : ℕ) : ℂ)
              * ((Q.coeff ((⟨(i : ℕ) + 1, fin_succ_lt hk1⟩ : Fin k) : ℕ) : ↥(ℚ⟮b⟯)) : ℂ))
            = ∑ i : Fin (k - 1), ((μ ⟨(i : ℕ) + 1, fin_succ_lt hk1⟩ : ℕ) : ℂ)
              * ((Q'.coeff ((⟨(i : ℕ) + 1, fin_succ_lt hk1⟩ : Fin k) : ℕ) : ↥(ℚ⟮b⟯)) : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [htup i]
        have ha : ((μ ⟨0, hk1⟩ : ℕ) : ℂ) * ((Q.coeff 0 : ↥(ℚ⟮b⟯)) : ℂ)
            = ((μ ⟨0, hk1⟩ : ℕ) : ℂ) * ((Q'.coeff 0 : ↥(ℚ⟮b⟯)) : ℂ) := by
          rw [hs] at H1
          exact add_right_cancel (H1.symm.trans H2)
        have hne : ((μ ⟨0, hk1⟩ : ℕ) : ℂ) ≠ 0 := by
          have h := hμ0 hk1
          intro hc
          exact h (Fin.ext (by simpa using hc))
        apply Subtype.ext
        exact mul_left_cancel₀ hne ha
      · have hi : (j - 1) + 1 = j := Nat.sub_add_cancel hjpos
        have := htup ⟨j - 1, by omega⟩
        rwa [hi] at this
    · rw [hj]
      have h1 : Q.coeff k = 1 := by
        rw [← hQnd, Polynomial.coeff_natDegree, hQm.leadingCoeff]
      have h2 : Q'.coeff k = 1 := by
        rw [← hQ'nd, Polynomial.coeff_natDegree, hQ'm.leadingCoeff]
      rw [h1, h2]
    · have h1 : Q.coeff j = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (p := Q) (by rw [hQnd]; omega)
      have h2 : Q'.coeff j = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (p := Q') (by rw [hQ'nd]; omega)
      rw [h1, h2]
  have hNI := slice_normIdentityB f hf hkm hk (sliceMonic f hf) (fun i => (μ i : ℕ)) hgen hb hfin
  have hNI' := slice_normIdentityB f' hf' hkm hk (sliceMonic f' hf') (fun i => (μ i : ℕ)) hgen' hb' hfin
  have heq : (f.map φℚ).map (algebraMap ℚ ℂ) = (f'.map φℚ).map (algebraMap ℚ ℂ) := by
    rw [← hNI, ← hNI', show sliceQB f hf hkm hk (fun i => (μ i : ℕ)) hgen hb hfin = Q from rfl,
      show sliceQB f' hf' hkm hk (fun i => (μ i : ℕ)) hgen' hb' hfin = Q' from rfl, hQ]
  rw [map_map_int, map_map_int] at heq
  exact Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective heq


/-! ## The Mahler bound for the slice generator -/

/-- **The Mahler bound for the slice generator.**  With `γ = Σ_{j<k} μ_j c_j`
and `μ_j ≤ M0`, the Mahler measure of the block field at `γ` is at most
`(n·M0·2^k)^m · Y`. -/
theorem mahlerK_sliceGamma_le (f : ℤ[X]) (hf : f ∈ imprimSlice n H k) (hkm : k * m = n)
    (hk : 2 ≤ k) (hm1 : 1 ≤ m) (μ : Fin k → ℕ) {M0 : ℕ} (hM0 : 1 ≤ M0)
    (hμ : ∀ j, μ j ≤ M0) {Y : ℝ}
    (hY : ((f.map φℚ).map (algebraMap ℚ ℂ)).mahlerMeasure ≤ Y) :
    Commons.NumberTheory.NumberField.mahlerK ↥(sliceL f hf) (sliceGamma f hf μ)
      ≤ (((n * M0 * 2 ^ k : ℕ) : ℝ) ^ m) * Y := by
  classical
  haveI : Fact ((Polynomial.map (algebraMap ℚ (f.map φℚ).SplittingField)
      (f.map φℚ)).Splits) := ⟨Polynomial.SplittingField.splits (f.map φℚ)⟩
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨sliceIrred f hf⟩
  haveI : NumberField ↥(sliceL f hf) := ⟨⟩
  have hkn : k ≤ n := by
    rw [← hkm]
    exact Nat.le_mul_of_pos_right k (by omega)
  have hK : Module.finrank ℚ ↥(sliceL f hf) = Fintype.card (↥(sliceL f hf) →ₐ[ℚ] ℂ) :=
    (Commons.NumberTheory.NumberField.card_algHom_eq_finrank).symm
  have hfin : Module.finrank ℚ ↥(sliceL f hf) = m := slice_finrank f hf hkm hk
  have hinteg : IsIntegral ℤ (sliceGamma f hf μ) := by
    rw [sliceGamma]
    exact IsIntegral.sum _ fun j _ =>
      IsIntegral.mul (isIntegral_natCast' (μ j)) (isIntegral_slicePL_coeff f hf j)
  rw [Commons.NumberTheory.NumberField.mahlerK_eq_prod_algHom hinteg]
  have hfac : ∀ χ : (↥(sliceL f hf) →ₐ[ℚ] ℂ),
      max 1 ‖χ (sliceGamma f hf μ)‖
        ≤ (((n * M0 * 2 ^ k : ℕ) : ℝ)
            * ((slicePL f hf).map χ.toRingHom).mahlerMeasure) := by
    intro χ
    have hM1 : 1 ≤ ((slicePL f hf).map χ.toRingHom).mahlerMeasure :=
      Commons.Analysis.Polynomial.one_le_mahlerMeasure_of_monic
        ((spolyL_monic (f.map φℚ) (sliceSep f hf) (sliceBlock f hf)).map χ.toRingHom)
    have hMnn : 0 ≤ ((slicePL f hf).map χ.toRingHom).mahlerMeasure :=
      Polynomial.mahlerMeasure_nonneg _
    have hmap : χ (sliceGamma f hf μ)
        = ∑ j : Fin k, ((μ j : ℕ) : ℂ) * χ ((slicePL f hf).coeff (j : ℕ)) := by
      rw [sliceGamma, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, map_natCast]
    have hstep : ‖χ (sliceGamma f hf μ)‖
        ≤ (((n * M0 * 2 ^ k : ℕ) : ℝ)
            * ((slicePL f hf).map χ.toRingHom).mahlerMeasure) := by
      rw [hmap]
      have h2k : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hM0' : (1 : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hM0
      calc ‖∑ j : Fin k, ((μ j : ℕ) : ℂ) * χ ((slicePL f hf).coeff (j : ℕ))‖
          ≤ ∑ j : Fin k, ‖((μ j : ℕ) : ℂ) * χ ((slicePL f hf).coeff (j : ℕ))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _j : Fin k, ((M0 : ℝ)
              * ((2 : ℝ) ^ k * ((slicePL f hf).map χ.toRingHom).mahlerMeasure)) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [norm_mul, Complex.norm_natCast]
            have h1 : ((μ j : ℕ) : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hμ j
            have h2 := norm_algHom_coeff_le (f.map φℚ) (sliceSep f hf) (sliceBlock f hf) χ (j : ℕ)
            rw [sliceBlock_ncard f hf] at h2
            exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = (((k : ℝ) * M0 * 2 ^ k) * ((slicePL f hf).map χ.toRingHom).mahlerMeasure) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
        _ ≤ (((n * M0 * 2 ^ k : ℕ) : ℝ)
              * ((slicePL f hf).map χ.toRingHom).mahlerMeasure) := by
            have hkR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
            have hM0nn : (0 : ℝ) ≤ (M0 : ℝ) := by positivity
            have h2knn : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
            push_cast
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hkR hM0nn) h2knn) hMnn
    refine max_le ?_ hstep
    have hC1 : (1 : ℝ) ≤ ((n * M0 * 2 ^ k : ℕ) : ℝ) := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        have : 1 ≤ n := by omega
        exact_mod_cast this
      have h2k : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hM0' : (1 : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hM0
      have hnn : (0 : ℝ) ≤ ((n * M0 * 2 ^ k : ℕ) : ℝ) := by positivity
      push_cast
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ (n : ℝ) * M0 * 2 ^ k :=
            mul_le_mul_of_nonneg (mul_le_mul hn1 hM0' (by norm_num) (by linarith)) h2k
              (by norm_num) (by positivity)
    nlinarith [hC1, hM1, hMnn]
  haveI hpre : MulAction.IsPretransitive (↥(galImg (f.map φℚ) (sliceSep f hf)))
      (Fin (f.map φℚ).natDegree) := slice_pretransitive f hf
  have hprod : ∏ χ : (↥(sliceL f hf) →ₐ[ℚ] ℂ),
        ((slicePL f hf).map χ.toRingHom).mahlerMeasure
      = ((f.map φℚ).map (algebraMap ℚ ℂ)).mahlerMeasure := by
    rw [← Commons.Analysis.Polynomial.mahlerMeasure_prod,
      normIdentity (f.map φℚ) (sliceSep f hf) (sliceMonic f hf) (sliceBlock_isBlock f hf)
        (sliceBlock_nonempty f hf hk) (sliceIota f)]
  calc ∏ χ : (↥(sliceL f hf) →ₐ[ℚ] ℂ), max 1 ‖χ (sliceGamma f hf μ)‖
      ≤ ∏ χ : (↥(sliceL f hf) →ₐ[ℚ] ℂ),
          (((n * M0 * 2 ^ k : ℕ) : ℝ)
            * ((slicePL f hf).map χ.toRingHom).mahlerMeasure) :=
        Finset.prod_le_prod (fun χ _ => by positivity) (fun χ _ => hfac χ)
    _ = (((n * M0 * 2 ^ k : ℕ) : ℝ) ^ (Fintype.card (↥(sliceL f hf) →ₐ[ℚ] ℂ)))
          * ∏ χ : (↥(sliceL f hf) →ₐ[ℚ] ℂ),
              ((slicePL f hf).map χ.toRingHom).mahlerMeasure := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        rfl
    _ = (((n * M0 * 2 ^ k : ℕ) : ℝ) ^ (Module.finrank ℚ ↥(sliceL f hf)))
          * ((f.map φℚ).map (algebraMap ℚ ℂ)).mahlerMeasure := by
        rw [hprod, ← hK]
    _ ≤ (((n * M0 * 2 ^ k : ℕ) : ℝ) ^ m) * Y := by
        rw [hfin]
        exact mul_le_mul_of_nonneg_left hY (by positivity)

/-! ## The generator count -/

/-- The Mahler measure of the minimal polynomial of the generator's value is at
most `sliceYG n H k m`. -/
theorem mapMahlerMeasure_minpoly_sliceZ_le (f : ℤ[X]) (hf : f ∈ imprimSlice n H k)
    (hkm : k * m = n) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (μ : Fin k → Fin (m * m + 2))
    (hgen : IntermediateField.adjoin ℚ
      ({sliceGamma f hf (fun i => (μ i : ℕ))} : Set ↥(sliceL f hf)) = ⊤) :
    Polynomial.mapMahlerMeasure (minpoly ℤ (sliceZ f hf (fun i => (μ i : ℕ))))
        (Int.castRingHom ℂ) ≤ sliceYG n H k m := by
  classical
  let z : ℂ := sliceZ f hf (fun i => (μ i : ℕ))
  have hzint : IsIntegral ℤ z := isIntegral_sliceZ f hf (fun i => (μ i : ℕ))
  haveI : NumberField ↥(ℚ⟮z⟯) := numberField_adjoin_sliceZ f hf (fun i => (μ i : ℕ))
  have hfin : Module.finrank ℚ ↥(ℚ⟮z⟯) = m :=
    finrank_adjoin_sliceZ f hf hkm hk (fun i => (μ i : ℕ)) hgen
  have hx : IsIntegral ℤ (IntermediateField.AdjoinSimple.gen ℚ z) := by
    refine (isIntegral_algebraMap_iff (algebraMap ↥(ℚ⟮z⟯) ℂ).injective).mp ?_
    show IsIntegral ℤ z
    exact hzint
  have h1 : Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ)
      = ∏ χ : (↥(ℚ⟮z⟯) →ₐ[ℚ] ℂ), max 1 ‖χ (IntermediateField.AdjoinSimple.gen ℚ z)‖ :=
    Commons.NumberTheory.Polynomial.mapMahlerMeasure_minpoly_eq_prod_algHom_simple z hzint
  have h2 : (∏ χ : (↥(ℚ⟮z⟯) →ₐ[ℚ] ℂ),
        max 1 ‖χ (IntermediateField.AdjoinSimple.gen ℚ z)‖)
      = Commons.NumberTheory.NumberField.mahlerK ↥(ℚ⟮z⟯)
          (IntermediateField.AdjoinSimple.gen ℚ z) :=
    (Commons.NumberTheory.NumberField.mahlerK_eq_prod_algHom hx).symm
  haveI : NumberField ↥(sliceL f hf) := ⟨⟩
  have hgen_eq : sliceEquiv f hf hkm hk (fun i => (μ i : ℕ)) hgen rfl hfin
        (sliceGamma f hf (fun i => (μ i : ℕ)))
      = IntermediateField.AdjoinSimple.gen ℚ z := by
    apply Subtype.ext
    rw [sliceEquiv_apply, sliceHom_apply]
    rfl
  have h3 : Commons.NumberTheory.NumberField.mahlerK ↥(ℚ⟮z⟯)
        (IntermediateField.AdjoinSimple.gen ℚ z)
      = Commons.NumberTheory.NumberField.mahlerK ↥(sliceL f hf)
          (sliceGamma f hf (fun i => (μ i : ℕ))) := by
    rw [← hgen_eq, Commons.NumberTheory.NumberField.mahlerK_algEquiv
      (sliceEquiv f hf hkm hk (fun i => (μ i : ℕ)) hgen rfl hfin)
      (sliceGamma f hf (fun i => (μ i : ℕ)))]
  have h4 : Commons.NumberTheory.NumberField.mahlerK ↥(sliceL f hf)
        (sliceGamma f hf (fun i => (μ i : ℕ)))
      ≤ (((n * (m * m + 1) * 2 ^ k : ℕ) : ℝ) ^ m) * sliceMf n H :=
    mahlerK_sliceGamma_le f hf hkm hk hm1 (fun i => (μ i : ℕ)) (by omega) (fun j => by
      have := (μ j).2; omega) (mahlerMeasure_map_le_sliceMf hf.1)
  calc Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ)
      = ∏ χ : (↥(ℚ⟮z⟯) →ₐ[ℚ] ℂ),
          max 1 ‖χ (IntermediateField.AdjoinSimple.gen ℚ z)‖ := h1
    _ = Commons.NumberTheory.NumberField.mahlerK ↥(ℚ⟮z⟯)
          (IntermediateField.AdjoinSimple.gen ℚ z) := h2
    _ = Commons.NumberTheory.NumberField.mahlerK ↥(sliceL f hf)
          (sliceGamma f hf (fun i => (μ i : ℕ))) := h3
    _ ≤ (((n * (m * m + 1) * 2 ^ k : ℕ) : ℝ) ^ m) * sliceMf n H := h4
    _ = sliceYG n H k m := by rw [sliceYG]


/-! ## Accessors for the `muGood` data -/

noncomputable def mgSlice (μ : Fin k → Fin (m * m + 2)) (f : ℤ[X])
    (h : f ∈ muGood n H k m μ) : f ∈ imprimSlice n H k :=
  Classical.choose h

noncomputable def mgHk (μ : Fin k → Fin (m * m + 2)) (f : ℤ[X])
    (h : f ∈ muGood n H k m μ) : 0 < k :=
  Classical.choose (Classical.choose_spec h)

noncomputable def mgMu0 (μ : Fin k → Fin (m * m + 2)) (f : ℤ[X])
    (h : f ∈ muGood n H k m μ) : μ ⟨0, mgHk μ f h⟩ ≠ 0 :=
  (Classical.choose_spec (Classical.choose_spec h)).1

noncomputable def mgGen (μ : Fin k → Fin (m * m + 2)) (f : ℤ[X])
    (h : f ∈ muGood n H k m μ) :
    IntermediateField.adjoin ℚ ({sliceGamma f (mgSlice μ f h) (fun i => (μ i : ℕ))} :
      Set ↥(sliceL f (mgSlice μ f h))) = ⊤ :=
  (Classical.choose_spec (Classical.choose_spec h)).2

lemma mgHb (μ : Fin k → Fin (m * m + 2)) (f : ℤ[X]) (h : f ∈ muGood n H k m μ)
    {b : ℂ} (hb : sliceZAll n H k (fun j => (μ j : ℕ)) f = b) :
    sliceZ f (mgSlice μ f h) (fun j => (μ j : ℕ)) = b :=
  (sliceZAll_eq (mgSlice μ f h) _).symm.trans hb

lemma zero_le_sliceFib (n H k m : ℕ) : 0 ≤ sliceFib n H k m := by
  rw [sliceFib]
  have h1 : (0:ℝ) ≤ (200000:ℝ) ^ m := by positivity
  have h2 : (0:ℝ) ≤ sliceYC n H k m := le_trans zero_le_one (one_le_sliceYC n H k m)
  have h3 : (0:ℝ) ≤ 1 + Real.log (sliceYC n H k m) := by
    have := Real.log_nonneg (one_le_sliceYC n H k m); linarith
  exact pow_nonneg (mul_nonneg (mul_nonneg h1 h2) (pow_nonneg h3 _)) _

/-! ## The fibre count -/
/-- **The fibre count**: for fixed `b`, the number of slice polynomials with
`ψ_f(γ_f) = b` is at most the number of tuples of `k-1` integral elements of
`ℚ(b)` of Mahler measure at most `2^(k·m)·Y`. -/
theorem slice_fiber_ncard_le (hkm : k * m = n) (hk : 2 ≤ k) (hm : 2 ≤ m) (hn : 1 ≤ n)
    (μ : Fin k → Fin (m * m + 2)) (b : ℂ) :
    (({f : ℤ[X] | f ∈ muGood n H k m μ ∧
        sliceZAll n H k (fun j => (μ j : ℕ)) f = b} : Set ℤ[X]).ncard : ℝ)
      ≤ sliceFib n H k m := by
  classical
  let FS : Set ℤ[X] :=
    {f : ℤ[X] | f ∈ muGood n H k m μ ∧ sliceZAll n H k (fun j => (μ j : ℕ)) f = b}
  change ((FS.ncard : ℝ) ≤ sliceFib n H k m)
  rcases FS.eq_empty_or_nonempty with hem | ⟨f₀, hf₀⟩
  · rw [hem, Set.ncard_empty]
    simpa using zero_le_sliceFib n H k m
  · rw [Set.mem_ofPred_eq] at hf₀
    obtain ⟨hf₀mg, hf₀b⟩ := hf₀
    obtain ⟨hf₀slice, hk0, hμ0, hgen0⟩ := hf₀mg
    have hb0 : sliceZ f₀ hf₀slice (fun j => (μ j : ℕ)) = b := by
      rw [← hf₀b, sliceZAll_eq hf₀slice]
    haveI hNF : NumberField ↥(ℚ⟮b⟯) := by
      rw [← hb0]
      exact numberField_adjoin_sliceZ f₀ hf₀slice (fun j => (μ j : ℕ))
    have hfin : Module.finrank ℚ ↥(ℚ⟮b⟯) = m := by
      rw [← hb0]
      exact finrank_adjoin_sliceZ f₀ hf₀slice hkm hk (fun j => (μ j : ℕ)) hgen0
    let T := {v : Fin (k - 1) → ↥(ℚ⟮b⟯) // (∀ i, IsIntegral ℤ (v i)) ∧
        ∀ i, Commons.NumberTheory.NumberField.mahlerK ↥(ℚ⟮b⟯) (v i) ≤ sliceYC n H k m}
    have hTfin : ({v : Fin (k - 1) → ↥(ℚ⟮b⟯) | (∀ i, IsIntegral ℤ (v i)) ∧
        ∀ i, Commons.NumberTheory.NumberField.mahlerK ↥(ℚ⟮b⟯) (v i)
          ≤ sliceYC n H k m} : Set (Fin (k - 1) → ↥(ℚ⟮b⟯))).Finite := by
      have h := Set.Finite.pi (fun _ : Fin (k - 1) =>
        Commons.NumberTheory.NumberField.finite_setOf_isIntegral_mahler_le
          (K := ↥(ℚ⟮b⟯)) (sliceYC n H k m))
      refine Set.Finite.subset h ?_
      intro v hv
      rw [Set.mem_ofPred_eq] at hv
      rw [Set.mem_pi]
      exact fun i _ => ⟨hv.1 i, hv.2 i⟩
    haveI : Finite T := hTfin.to_subtype
    let Φ : ↥FS → T := fun f =>
      have mem1 : f.1 ∈ muGood n H k m μ := ((Set.mem_ofPred_eq).mp f.2).1
      have mem2 : sliceZAll n H k (fun j => (μ j : ℕ)) f.1 = b := ((Set.mem_ofPred_eq).mp f.2).2
      ⟨fun i => (sliceQB f.1 (mgSlice μ f.1 mem1) hkm hk (fun j => (μ j : ℕ))
          (mgGen μ f.1 mem1) (mgHb μ f.1 mem1 mem2) hfin).coeff ((i : ℕ) + 1),
        fun i => isIntegral_sliceQB_coeff f.1 (mgSlice μ f.1 mem1) hkm hk _
          (mgGen μ f.1 mem1) (mgHb μ f.1 mem1 mem2) hfin _,
        fun i => by
          have h := mahlerK_sliceQB_coeff_le f.1 (mgSlice μ f.1 mem1) hkm hk
            (sliceMonic f.1 (mgSlice μ f.1 mem1)) _ (mgGen μ f.1 mem1)
            (mgHb μ f.1 mem1 mem2) hfin
            (mahlerMeasure_map_le_sliceMf (mgSlice μ f.1 mem1).1) ((i : ℕ) + 1)
          rw [sliceYC]
          exact h⟩
    have hΦinj : Function.Injective Φ := by
      intro f f' hff'
      have mem1 : f.1 ∈ muGood n H k m μ := ((Set.mem_ofPred_eq).mp f.2).1
      have mem2 : sliceZAll n H k (fun j => (μ j : ℕ)) f.1 = b := ((Set.mem_ofPred_eq).mp f.2).2
      have mem1' : f'.1 ∈ muGood n H k m μ := ((Set.mem_ofPred_eq).mp f'.2).1
      have mem2' : sliceZAll n H k (fun j => (μ j : ℕ)) f'.1 = b := ((Set.mem_ofPred_eq).mp f'.2).2
      apply Subtype.ext
      have htup : ∀ i : Fin (k - 1),
          (sliceQB f.1 (mgSlice μ f.1 mem1) hkm hk (fun j => (μ j : ℕ))
              (mgGen μ f.1 mem1) (mgHb μ f.1 mem1 mem2) hfin).coeff ((i : ℕ) + 1)
            = (sliceQB f'.1 (mgSlice μ f'.1 mem1') hkm hk (fun j => (μ j : ℕ))
              (mgGen μ f'.1 mem1') (mgHb μ f'.1 mem1' mem2') hfin).coeff ((i : ℕ) + 1) := by
        intro i
        exact congrFun (congrArg Subtype.val hff') i
      refine slice_tuple_inj hkm hk μ ?_ htup
      intro hk0 hcon
      refine mgMu0 μ f.1 mem1 ?_
      rwa [show (⟨0, hk0⟩ : Fin k) = ⟨0, mgHk μ f.1 mem1⟩ from Fin.ext rfl] at hcon
    have h1 : Nat.card ↥FS ≤ Nat.card T := Nat.card_le_card_of_injective Φ hΦinj
    have h2 : (Nat.card T : ℝ) ≤ sliceFib n H k m := by
      rw [sliceFib]
      exact Commons.NumberTheory.NumberField.ncard_integral_tuple_mahler_le
        (K := ↥(ℚ⟮b⟯)) m hm hfin (k - 1) (sliceYC n H k m) (one_le_sliceYC n H k m)
    calc (FS.ncard : ℝ) = (Nat.card ↥FS : ℝ) := by rw [Nat.card_coe_set_eq]
      _ ≤ (Nat.card T : ℝ) := by exact_mod_cast h1
      _ ≤ sliceFib n H k m := h2


/-- **The generator count**: the number of values of `ψ_f(γ_f)` is `≪ H^m`. -/
theorem slice_image_ncard_le (hkm : k * m = n) (hk : 2 ≤ k) (hm : 2 ≤ m) (hn : 1 ≤ n)
    (μ : Fin k → Fin (m * m + 2)) :
    (((sliceZAll n H k (fun j => (μ j : ℕ)) '' (muGood n H k m μ)).ncard : ℕ) : ℝ)
      ≤ ((sliceGen n H k m : ℝ)) := by
  classical
  set Z : Set ℂ := {z : ℂ | (minpoly ℤ z).Monic ∧ (minpoly ℤ z).natDegree = m ∧
    Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ) ≤ sliceYG n H k m} with hZ
  have hsub : (sliceZAll n H k (fun j => (μ j : ℕ)) '' (muGood n H k m μ)) ⊆ Z := by
    rintro z ⟨f, hfmg, rfl⟩
    obtain ⟨hf, hk0, hμ0, hgen⟩ := hfmg
    rw [sliceZAll_eq hf]
    have hzint : IsIntegral ℤ (sliceZ f hf (fun i => (μ i : ℕ))) :=
      isIntegral_sliceZ f hf (fun i => (μ i : ℕ))
    refine ⟨minpoly.monic hzint, ?_, ?_⟩
    · rw [Commons.NumberTheory.NumberField.natDegree_minpoly_int_eq_finrank_adjoin_simple _
        hzint]
      exact finrank_adjoin_sliceZ f hf hkm hk (fun i => (μ i : ℕ)) hgen
    · exact mapMahlerMeasure_minpoly_sliceZ_le f hf hkm hk (by omega) μ hgen
  have hZfin : Z.Finite := Set.Finite.subset
    (Commons.NumberTheory.Polynomial.finite_monic_minpoly_mahler_le m (sliceYG n H k m))
    (fun z hz => ⟨hz.1, hz.2.1, hz.2.2⟩)
  calc (((sliceZAll n H k (fun j => (μ j : ℕ)) '' (muGood n H k m μ)).ncard : ℕ) : ℝ)
      ≤ (Z.ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hZfin
    _ ≤ (m : ℝ) * ((2 : ℝ) ^ (m + 2) * sliceYG n H k m) ^ m :=
        Commons.NumberTheory.Polynomial.ncard_monic_minpoly_mahler_le m (by omega)
          (sliceYG n H k m) (one_le_sliceYG n H k m hn)
    _ = sliceGen n H k m := by rw [sliceGen]


/-! ## Assembling the slice bound -/

lemma muGood_subset_box (n H k m : ℕ) (μ : Fin k → Fin (m * m + 2)) :
    muGood n H k m μ ⊆ Box n H := by
  rintro f ⟨hf, -⟩
  exact hf.1

theorem muGood_ncard_le (hkm : k * m = n) (hk : 2 ≤ k) (hm : 2 ≤ m) (hn : 1 ≤ n)
    (μ : Fin k → Fin (m * m + 2)) :
    ((muGood n H k m μ).ncard : ℝ) ≤ (⌈sliceFib n H k m⌉₊ : ℝ) * ⌈sliceGen n H k m⌉₊ := by
  classical
  have hbox : (Box n H).Finite := box_finite n H
  have hsub := muGood_subset_box n H k m μ
  have himg : (sliceZAll n H k (fun j => (μ j : ℕ)) '' (muGood n H k m μ)).Finite :=
    (hbox.subset hsub).image _
  have hfib : ∀ b ∈ sliceZAll n H k (fun j => (μ j : ℕ)) '' (muGood n H k m μ),
      ((muGood n H k m μ) ∩ sliceZAll n H k (fun j => (μ j : ℕ)) ⁻¹' {b}).Finite ∧
      ((muGood n H k m μ) ∩ sliceZAll n H k (fun j => (μ j : ℕ)) ⁻¹' {b}).ncard
        ≤ ⌈sliceFib n H k m⌉₊ := by
    intro b hb
    have hset : ((muGood n H k m μ) ∩ sliceZAll n H k (fun j => (μ j : ℕ)) ⁻¹' {b})
        = {f : ℤ[X] | f ∈ muGood n H k m μ ∧
            sliceZAll n H k (fun j => (μ j : ℕ)) f = b} := by
      ext f
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · rw [hset]
      exact hbox.subset fun f hf => muGood_subset_box n H k m μ hf.1
    · rw [hset]
      have hb' := slice_fiber_ncard_le (n := n) (H := H) (k := k) (m := m) hkm hk hm hn μ b
      exact_mod_cast hb'.trans (Nat.le_ceil (sliceFib n H k m))
  have hmain : (muGood n H k m μ).ncard
      ≤ ⌈sliceFib n H k m⌉₊
        * (sliceZAll n H k (fun j => (μ j : ℕ)) '' (muGood n H k m μ)).ncard :=
    ncard_le_mul_ncard_image_of_fiber_le
      (φ := sliceZAll n H k (fun j => (μ j : ℕ))) (s := muGood n H k m μ)
      (N := ⌈sliceFib n H k m⌉₊) himg hfib
  have h2 : (((sliceZAll n H k (fun j => (μ j : ℕ)) '' (muGood n H k m μ)).ncard : ℕ) : ℝ)
      ≤ sliceGen n H k m := slice_image_ncard_le (n := n) (H := H) (k := k) (m := m) hkm hk hm hn μ
  have h2' : (((sliceZAll n H k (fun j => (μ j : ℕ)) '' (muGood n H k m μ)).ncard : ℕ) : ℝ)
      ≤ (⌈sliceGen n H k m⌉₊ : ℝ) := h2.trans (Nat.le_ceil _)
  calc (((muGood n H k m μ).ncard : ℕ) : ℝ)
      ≤ ((⌈sliceFib n H k m⌉₊
          * (sliceZAll n H k (fun j => (μ j : ℕ)) '' (muGood n H k m μ)).ncard : ℕ) : ℝ) := by
        exact_mod_cast hmain
    _ = (⌈sliceFib n H k m⌉₊ : ℝ)
          * (((sliceZAll n H k (fun j => (μ j : ℕ)) '' (muGood n H k m μ)).ncard : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ (⌈sliceFib n H k m⌉₊ : ℝ) * (⌈sliceGen n H k m⌉₊ : ℝ) :=
        mul_le_mul_of_nonneg_left h2' (by positivity)

theorem imprimSlice_ncard_le (hkm : k * m = n) (hk : 2 ≤ k) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    ((imprimSlice n H k).ncard : ℝ)
      ≤ ((m * m + 2) ^ k : ℕ) * ((⌈sliceFib n H k m⌉₊ : ℝ) * ⌈sliceGen n H k m⌉₊) := by
  classical
  have hcover := imprimSlice_subset_iUnion_muGood (n := n) (H := H) (k := k) (m := m)
    hkm hk hm (by omega)
  have hfin : (⋃ μ : Fin k → Fin (m * m + 2), muGood n H k m μ).Finite :=
    (box_finite n H).subset fun f hf => by
      rw [Set.mem_iUnion] at hf
      obtain ⟨μ, hfμ⟩ := hf
      exact muGood_subset_box n H k m μ hfμ
  have hEq : (⋃ μ : Fin k → Fin (m * m + 2), muGood n H k m μ)
      = ⋃ μ ∈ (Finset.univ : Finset (Fin k → Fin (m * m + 2))), muGood n H k m μ := by
    ext f
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨μ, hμ⟩
      exact ⟨μ, Finset.mem_univ μ, hμ⟩
    · rintro ⟨μ, -, hμ⟩
      exact ⟨μ, hμ⟩
  have hstep : (⋃ μ : Fin k → Fin (m * m + 2), muGood n H k m μ).ncard
      ≤ ∑ μ : Fin k → Fin (m * m + 2), (muGood n H k m μ).ncard := by
    rw [hEq]
    exact Finset.set_ncard_biUnion_le (Finset.univ : Finset (Fin k → Fin (m * m + 2)))
      (fun μ => muGood n H k m μ)
  calc ((imprimSlice n H k).ncard : ℝ)
      ≤ ((⋃ μ : Fin k → Fin (m * m + 2), muGood n H k m μ).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hcover hfin
    _ ≤ (∑ μ : Fin k → Fin (m * m + 2), (muGood n H k m μ).ncard : ℝ) := by
        exact_mod_cast hstep
    _ = ∑ μ : Fin k → Fin (m * m + 2), ((muGood n H k m μ).ncard : ℝ) := rfl
    _ ≤ ∑ _μ : Fin k → Fin (m * m + 2), (⌈sliceFib n H k m⌉₊ : ℝ) * ⌈sliceGen n H k m⌉₊ :=
        Finset.sum_le_sum fun μ _ => muGood_ncard_le hkm hk hm hn μ
    _ = ((m * m + 2) ^ k : ℕ) * ((⌈sliceFib n H k m⌉₊ : ℝ) * ⌈sliceGen n H k m⌉₊) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        congr 1
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]


/-! ## The asymptotic bounds -/

lemma one_add_log_pow_le (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → (1 + Real.log x) ^ D ≤ C * x ^ δ := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := Commons.Analysis.Real.polylog_le_const_mul_rpow D δ hδ
  refine ⟨(2:ℝ)^D * (1 + C₀), by positivity, fun x hx => ?_⟩
  have hLnn : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : (1 + Real.log x) ≤ 2 * max 1 (Real.log x) := by
    by_cases h : Real.log x ≤ 1
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right (le_of_lt (not_le.mp h))]; linarith
  have h2 : (max 1 (Real.log x)) ^ D ≤ 1 + (Real.log x) ^ D := by
    rcases le_total (Real.log x) 1 with h | h
    · rw [max_eq_left h, one_pow]
      exact le_add_of_nonneg_right (pow_nonneg hLnn D)
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (by norm_num)
  have h4 : (1:ℝ) ≤ x ^ δ := Real.one_le_rpow hx (le_of_lt hδ)
  calc (1 + Real.log x) ^ D ≤ (2 * max 1 (Real.log x)) ^ D :=
        pow_le_pow_left₀ (by linarith) h1 D
    _ = (2:ℝ) ^ D * (max 1 (Real.log x)) ^ D := mul_pow _ _ _
    _ ≤ (2:ℝ) ^ D * (1 + (Real.log x) ^ D) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ (2:ℝ) ^ D * (1 + C₀ * x ^ δ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hC₀ x hx]
    _ ≤ ((2:ℝ) ^ D * (1 + C₀)) * x ^ δ := by
        have h5 : (1 + C₀ * x ^ δ) ≤ (1 + C₀) * x ^ δ := by nlinarith [h4, hC₀0]
        have h6 : (2:ℝ) ^ D * ((1 + C₀) * x ^ δ) = (2:ℝ) ^ D * (1 + C₀) * x ^ δ := by ring
        rw [← h6]
        exact mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ (2:ℝ) ^ D)

/-- The fibre bound is `≪ H^k`. -/
lemma sliceFib_le (n k m : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, sliceFib n H k m ≤ C * ((H : ℝ) + 1) ^ ((k : ℝ)) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := one_add_log_pow_le ((m - 1) * (k - 1)) (1/4) (by norm_num)
  set c : ℝ := (2:ℝ) ^ (k * m) * ((n : ℝ) + 1) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  refine ⟨(200000 : ℝ) ^ (m * (k - 1)) * c ^ (k - 1) * (C₀ * c ^ ((1:ℝ)/4)), by positivity,
    fun H => ?_⟩
  set X : ℝ := (H : ℝ) + 1 with hXdef
  have hX1 : (1:ℝ) ≤ X := by
    rw [hXdef]
    have h : (0:ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    linarith
  have hX0 : (0:ℝ) < X := lt_of_lt_of_le one_pos hX1
  have hYC : sliceYC n H k m = c * X := by rw [sliceYC, sliceMf, hcdef, hXdef]; ring
  have hY1 : 1 ≤ sliceYC n H k m := one_le_sliceYC n H k m
  have hL1 : (1:ℝ) ≤ c * X := by rw [← hYC]; exact hY1
  have hA : (1 + Real.log (c * X)) ^ ((m - 1) * (k - 1))
      ≤ C₀ * c ^ ((1:ℝ)/4) * X ^ ((1:ℝ)/4) := by
    calc (1 + Real.log (c * X)) ^ ((m - 1) * (k - 1))
        = (1 + Real.log (sliceYC n H k m)) ^ ((m - 1) * (k - 1)) := by rw [hYC]
      _ ≤ C₀ * (sliceYC n H k m) ^ ((1:ℝ)/4) := hC₀ _ hY1
      _ = C₀ * (c * X) ^ ((1:ℝ)/4) := by rw [hYC]
      _ = C₀ * (c ^ ((1:ℝ)/4) * X ^ ((1:ℝ)/4)) := by
          rw [Real.mul_rpow (le_of_lt hc0) (le_of_lt hX0)]
      _ = C₀ * c ^ ((1:ℝ)/4) * X ^ ((1:ℝ)/4) := by ring
  have hmain : sliceFib n H k m
      ≤ (200000 : ℝ) ^ (m * (k - 1)) * c ^ (k - 1) * (C₀ * c ^ ((1:ℝ)/4))
          * X ^ ((k : ℝ)) := by
    rw [sliceFib, hYC]
    calc (200000 ^ m * (c * X) * (1 + Real.log (c * X)) ^ (m - 1)) ^ (k - 1)
        = (200000 ^ m) ^ (k - 1) * (c * X) ^ (k - 1)
            * ((1 + Real.log (c * X)) ^ (m - 1)) ^ (k - 1) := by
          rw [mul_pow, mul_pow]
      _ = (200000 ^ m) ^ (k - 1) * (c * X) ^ (k - 1)
            * (1 + Real.log (c * X)) ^ ((m - 1) * (k - 1)) := by rw [pow_mul]
      _ ≤ (200000 ^ m) ^ (k - 1) * (c * X) ^ (k - 1)
            * (C₀ * c ^ ((1:ℝ)/4) * X ^ ((1:ℝ)/4)) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = (200000 ^ m) ^ (k - 1) * c ^ (k - 1) * (C₀ * c ^ ((1:ℝ)/4))
            * (X ^ (k - 1) * X ^ ((1:ℝ)/4)) := by
          rw [mul_pow]; ring
      _ = (200000 ^ m) ^ (k - 1) * c ^ (k - 1) * (C₀ * c ^ ((1:ℝ)/4))
            * X ^ (((k - 1 : ℕ) : ℝ) + (1:ℝ)/4) := by
          rw [mul_pow]
          rw [show X ^ (k - 1) = X ^ (((k - 1 : ℕ) : ℝ)) from
            (Real.rpow_natCast X (k - 1)).symm]
          rw [← Real.rpow_add hX0]
      _ ≤ (200000 ^ m) ^ (k - 1) * c ^ (k - 1) * (C₀ * c ^ ((1:ℝ)/4)) * X ^ ((k : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
          have hkR : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
          have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
          rw [hcast]; linarith
      _ = (200000 : ℝ) ^ (m * (k - 1)) * c ^ (k - 1) * (C₀ * c ^ ((1:ℝ)/4))
            * X ^ ((k : ℝ)) := by
          rw [← pow_mul]
  exact hmain

/-- The generator count is `≪ H^m`. -/
lemma sliceGen_le (n k m : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, sliceGen n H k m ≤ C * ((H : ℝ) + 1) ^ ((m : ℝ)) := by
  set A : ℝ := ((n * (m * m + 1) * 2 ^ k : ℕ) : ℝ) with hAdef
  have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine ⟨(m : ℝ) * ((2:ℝ) ^ (m + 2) * A ^ m * ((n : ℝ) + 1)) ^ m, by positivity, fun H => ?_⟩
  have hX0 : (0:ℝ) < (H : ℝ) + 1 := by positivity
  have hYG : sliceYG n H k m = A ^ m * ((H : ℝ) + 1) * ((n : ℝ) + 1) := by
    rw [sliceYG, sliceMf, hAdef]; ring
  rw [sliceGen, hYG]
  refine le_of_eq ?_
  rw [show (2:ℝ) ^ (m + 2) * (A ^ m * ((H : ℝ) + 1) * ((n : ℝ) + 1))
      = (2:ℝ) ^ (m + 2) * A ^ m * ((n : ℝ) + 1) * ((H : ℝ) + 1) from by ring,
    mul_pow, Real.rpow_natCast]
  ring


lemma one_le_sliceFib (n H k m : ℕ) : 1 ≤ sliceFib n H k m := by
  rw [sliceFib]
  refine one_le_pow₀ (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_sliceYC n H k m)) ?_)
  refine one_le_pow₀ ?_
  have := Real.log_nonneg (one_le_sliceYC n H k m)
  linarith

lemma one_le_sliceGen (n H k m : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) : 1 ≤ sliceGen n H k m := by
  rw [sliceGen]
  have hmR : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  refine one_le_mul_of_one_le_of_one_le hmR (one_le_pow₀ ?_)
  have h1 : (1:ℝ) ≤ (2:ℝ) ^ (m + 2) := one_le_pow₀ (by norm_num)
  exact one_le_mul_of_one_le_of_one_le h1 (one_le_sliceYG n H k m hn)

/-- **The imprimitive slice is `O(H^(k+m))`.** -/
theorem imprimitiveSliceBoundExp (n : ℕ) (hn : 6 ≤ n) :
    ImprimitiveSliceBoundExp n (fun k m => (k : ℝ) + m) := by
  intro k m hk hm hkm
  obtain ⟨C₁, hC₁0, hC₁⟩ := sliceFib_le n k m hk (by omega)
  obtain ⟨C₂, hC₂0, hC₂⟩ := sliceGen_le n k m (by omega) (by omega)
  refine ⟨((m * m + 2) ^ k : ℕ) * ((2 * C₁) * (2 * C₂)), by positivity, fun H => ?_⟩
  have hX1 : (1:ℝ) ≤ (H : ℝ) + 1 := by
    have h : (0:ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    linarith
  have hX0 : (0:ℝ) < (H : ℝ) + 1 := lt_of_lt_of_le one_pos hX1
  have hcf : (⌈sliceFib n H k m⌉₊ : ℝ) ≤ 2 * sliceFib n H k m := by
    have h1 : (⌈sliceFib n H k m⌉₊ : ℝ) < sliceFib n H k m + 1 :=
      Nat.ceil_lt_add_one (le_trans zero_le_one (one_le_sliceFib n H k m))
    have h2 : (1:ℝ) ≤ sliceFib n H k m := one_le_sliceFib n H k m
    linarith
  have hcg : (⌈sliceGen n H k m⌉₊ : ℝ) ≤ 2 * sliceGen n H k m := by
    have h1 : (⌈sliceGen n H k m⌉₊ : ℝ) < sliceGen n H k m + 1 :=
      Nat.ceil_lt_add_one (le_trans zero_le_one (one_le_sliceGen n H k m (by omega) (by omega)))
    have h2 : (1:ℝ) ≤ sliceGen n H k m := one_le_sliceGen n H k m (by omega) (by omega)
    linarith
  have hstep : (2 * sliceFib n H k m) * (2 * sliceGen n H k m)
      ≤ ((2 * C₁) * (2 * C₂)) * ((H : ℝ) + 1) ^ ((k : ℝ) + m) := by
    have hF : sliceFib n H k m ≤ C₁ * ((H : ℝ) + 1) ^ ((k : ℝ)) := hC₁ H
    have hG : sliceGen n H k m ≤ C₂ * ((H : ℝ) + 1) ^ ((m : ℝ)) := hC₂ H
    calc (2 * sliceFib n H k m) * (2 * sliceGen n H k m)
        ≤ (2 * (C₁ * ((H : ℝ) + 1) ^ ((k : ℝ))))
            * (2 * (C₂ * ((H : ℝ) + 1) ^ ((m : ℝ)))) := by
          have hG0 : (0:ℝ) ≤ C₂ * ((H : ℝ) + 1) ^ ((m : ℝ)) :=
            mul_nonneg (le_of_lt hC₂0) (Real.rpow_nonneg (le_of_lt hX0) _)
          have hF0 : (0:ℝ) ≤ C₁ * ((H : ℝ) + 1) ^ ((k : ℝ)) :=
            mul_nonneg (le_of_lt hC₁0) (Real.rpow_nonneg (le_of_lt hX0) _)
          refine mul_le_mul (mul_le_mul_of_nonneg_left hF (by norm_num))
            (mul_le_mul_of_nonneg_left hG (by norm_num))
            (by have := one_le_sliceGen n H k m (by omega) (by omega); linarith)
            (mul_nonneg (by norm_num) hF0)
      _ = ((2 * C₁) * (2 * C₂)) * (((H : ℝ) + 1) ^ ((k : ℝ)) * ((H : ℝ) + 1) ^ ((m : ℝ))) := by
          ring
      _ = ((2 * C₁) * (2 * C₂)) * ((H : ℝ) + 1) ^ ((k : ℝ) + m) := by
          rw [Real.rpow_add hX0]
  calc ((imprimSlice n H k).ncard : ℝ)
      ≤ ((m * m + 2) ^ k : ℕ) * ((⌈sliceFib n H k m⌉₊ : ℝ) * ⌈sliceGen n H k m⌉₊) :=
        imprimSlice_ncard_le hkm hk hm (by omega)
    _ ≤ ((m * m + 2) ^ k : ℕ) * ((2 * sliceFib n H k m) * (2 * sliceGen n H k m)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hcf hcg
          (by have := one_le_sliceGen n H k m (by omega) (by omega); linarith)
          (by have := one_le_sliceFib n H k m; linarith)
    _ ≤ ((m * m + 2) ^ k : ℕ) * (((2 * C₁) * (2 * C₂)) * ((H : ℝ) + 1) ^ ((k : ℝ) + m)) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (((m * m + 2) ^ k : ℕ) * ((2 * C₁) * (2 * C₂))) * ((H : ℝ) + 1) ^ ((k : ℝ) + m) := by
        ring

end

end Submission.Vdw
