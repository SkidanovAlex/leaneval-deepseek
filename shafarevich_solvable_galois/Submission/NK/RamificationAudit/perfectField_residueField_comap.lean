import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.NK.RamificationAudit.exists_mul_mem_and_valuation_eq_one
import Submission.NK.RamificationAudit.perfectField_of_forall_monic_aeval_eq_zero_natDegree_le

/-!
# Perfection of the residue field of `A ∩ M`

Let `L / K` be a finite Galois extension of fields, `A` a discrete valuation ring of `L` (a
`ValuationSubring L` which is a DVR) which is stable under `Gal(L/K)`, and `M` an intermediate
field.  We show that if the residue field of `A` is perfect, then so is the residue field of
`B := A ∩ M = A.comap (algebraMap ↥M L)`.

The mathematical content is in two independent parts:

* `NK.RamificationAudit.exists_mul_mem_and_valuation_eq_one`: in a valuation ring `B` of a field
  `M`, finitely many elements of `M` can be scaled into `B` with one of them becoming a unit.
  This is the "clearing denominators" step which shows that `κ_A` is algebraic of bounded degree
  over `κ_B` (`NK.RamificationAudit.linearIndependent_lift` and
  `NK.RamificationAudit.exists_monic_aeval_eq_zero_natDegree_le`);
* `NK.RamificationAudit.perfectField_of_forall_monic_aeval_eq_zero_natDegree_le`: perfection
  descends along a field extension in which every element is a root of a monic polynomial of
  bounded degree.
-/

namespace NK.RamificationAudit

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The canonical ring homomorphism `A ∩ M → A` (for `B := A.comap (algebraMap ↥M L)`, so that
`B`'s elements are the elements of `M` whose image in `L` lies in `A`). -/
def comapToA (A : ValuationSubring L) (M : IntermediateField K L) :
    ↥(A.comap (algebraMap ↥M L)) →+* ↥A where
  toFun b := ⟨algebraMap ↥M L (b : ↥M), ValuationSubring.mem_comap.mp b.2⟩
  map_one' := by ext; simp
  map_mul' := by intro x y; ext; simp
  map_zero' := by ext; simp
  map_add' := by intro x y; ext; simp

@[simp]
theorem comapToA_coe (A : ValuationSubring L) (M : IntermediateField K L)
    (b : ↥(A.comap (algebraMap ↥M L))) :
    ((comapToA A M b : ↥A) : L) = algebraMap ↥M L (b : ↥M) := rfl

/-- `A ∩ M → A` is a local ring homomorphism: if the image of `b` is a unit of `A`, then `b` is a
unit of `A ∩ M` (for valuation subrings a non-unit is exactly an element whose inverse is not in
the ring). -/
instance comapToA_isLocalHom (A : ValuationSubring L) (M : IntermediateField K L) :
    IsLocalHom (comapToA A M) := by
  refine IsLocalHom.mk fun x hx => ?_
  obtain ⟨y, hy⟩ := hx
  have hmul : comapToA A M x * ((y⁻¹ : Units ↥A) : ↥A) = 1 := by rw [← hy]; exact y.mul_inv
  have hmul' : algebraMap ↥M L (x : ↥M) * (((y⁻¹ : Units ↥A) : ↥A) : L) = 1 := by
    have h := congrArg (fun z : ↥A => (z : L)) hmul
    simpa using h
  have hx0 : (x : ↥M) ≠ 0 := by
    rintro h0
    have h1 : algebraMap ↥M L (x : ↥M) = 0 := by rw [h0, map_zero]
    rw [h1, zero_mul] at hmul'
    exact zero_ne_one hmul'
  have hmem : ((x : ↥M)⁻¹) ∈ A.comap (algebraMap ↥M L) := by
    refine ValuationSubring.mem_comap.mpr ?_
    have hinv : algebraMap ↥M L ((x : ↥M)⁻¹) = (((y⁻¹ : Units ↥A) : ↥A) : L) := by
      rw [map_inv₀, inv_eq_of_mul_eq_one_right hmul']
    rw [hinv]
    exact ((y⁻¹ : Units ↥A) : ↥A).2
  refine ⟨⟨x, ⟨(x : ↥M)⁻¹, hmem⟩, ?_, ?_⟩, rfl⟩
  · ext; simp [hx0]
  · ext; simp [hx0]

/-- The residue field of `A ∩ M` is naturally a subfield of the residue field of `A`: the map
induced by the local homomorphism `A ∩ M → A`. -/
noncomputable instance residueFieldAlgebra (A : ValuationSubring L) (M : IntermediateField K L) :
    Algebra (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥M L))) (IsLocalRing.ResidueField ↥A) :=
  (IsLocalRing.ResidueField.map (comapToA A M)).toAlgebra

/-- The residue map `κ_{A ∩ M} → κ_A` is the algebra structure map. -/
theorem algebraMap_residueField_eq (A : ValuationSubring L) (M : IntermediateField K L)
    (b : ↥(A.comap (algebraMap ↥M L))) :
    algebraMap (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥M L)))
        (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue _ b)
      = IsLocalRing.residue _ (comapToA A M b) := by
  rw [RingHom.algebraMap_toAlgebra, IsLocalRing.ResidueField.map_residue]


open Polynomial in
/-- **The lifts of residue-linearly independent elements are linearly independent.**  If
`a : ι → A` is such that the residues `residue (a i)` are linearly independent over the residue
field `κ_{A ∩ M}` of `A ∩ M`, then the `a i`, viewed in `L`, are linearly independent over `M`.

This is the standard "linear independence of lifts" argument: given a nontrivial `M`-linear
relation `∑ c i • a i = 0`, clear denominators in the valuation ring `B = A ∩ M`
(`NK.RamificationAudit.exists_mul_mem_and_valuation_eq_one`) to arrange that all `s * c i` lie in
`B` with one of them a unit of `B`; reducing the relation modulo the maximal ideal of `A` then
produces a nontrivial `κ_{A ∩ M}`-linear relation among the residues, contradicting the
hypothesis. -/
theorem linearIndependent_lift (A : ValuationSubring L) (M : IntermediateField K L)
    {ι : Type*} [Fintype ι] (a : ι → ↥A)
    (hv : LinearIndependent (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥M L)))
        (fun i => IsLocalRing.residue ↥A (a i))) :
    LinearIndependent ↥M (fun i => ((a i : ↥A) : L)) := by
  classical
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg i
  by_contra hne
  set B : ValuationSubring ↥M := A.comap (algebraMap ↥M L) with hB
  have hne' : Nonempty {j : ι // g j ≠ 0} := ⟨⟨i, hne⟩⟩
  obtain ⟨s, _hs0, hsmem, j₀, hj₀⟩ :=
    exists_mul_mem_and_valuation_eq_one B (fun j : {j : ι // g j ≠ 0} => g j.1) (fun j => j.2)
  have hmem : ∀ j : ι, s * g j ∈ B := by
    intro j
    by_cases hj : g j = 0
    · rw [hj, mul_zero]; exact B.zero_mem
    · exact hsmem ⟨j, hj⟩
  have hrel : ∑ j, (comapToA A M ⟨s * g j, hmem j⟩ : ↥A) * a j = 0 := by
    apply ValuationSubring.subtype_injective (K := L)
    rw [map_zero, map_sum]
    have hterm : ∀ j, (ValuationSubring.subtype A) ((comapToA A M ⟨s * g j, hmem j⟩ : ↥A) * a j)
        = algebraMap ↥M L s * (g j • ((a j : ↥A) : L)) := by
      intro j
      simp only [map_mul, ValuationSubring.coe_subtype, comapToA_coe, Algebra.smul_def]
      ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum, hg, mul_zero]
  have hres : ∑ j, (IsLocalRing.residue B ⟨s * g j, hmem j⟩) •
      (IsLocalRing.residue ↥A (a j)) = 0 := by
    have h1 : (IsLocalRing.residue ↥A) (∑ j, (comapToA A M ⟨s * g j, hmem j⟩ : ↥A) * a j) = 0 := by
      rw [hrel, map_zero]
    rw [map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra,
      IsLocalRing.ResidueField.map_residue]
  have hv' := hv (fun j => IsLocalRing.residue B ⟨s * g j, hmem j⟩) hres j₀.1
  have hj₀' : B.valuation ((⟨s * g j₀.1, hmem j₀.1⟩ : ↥B) : ↥M) = 1 := hj₀
  have hunit : IsUnit (⟨s * g j₀.1, hmem j₀.1⟩ : ↥B) :=
    (ValuationSubring.valuation_eq_one_iff B _).mpr hj₀'
  exact (IsUnit.map (IsLocalRing.residue ↥B) hunit).ne_zero hv'

open Polynomial in
/-- **Every element of `κ_A` is a root of a monic polynomial over `κ_{A ∩ M}` of degree at most
`[L : M]`.**  This is the degree bound required by
`NK.RamificationAudit.perfectField_of_forall_monic_aeval_eq_zero_natDegree_le`: it follows from
`linearIndependent_lift`, since `1, x, …, x ^ [L : M]` (that is, `[L : M] + 1` elements) cannot be
linearly independent over `κ_{A ∩ M}`. -/
theorem exists_monic_aeval_eq_zero_natDegree_le (A : ValuationSubring L) (M : IntermediateField K L)
    [FiniteDimensional K L] (x : IsLocalRing.ResidueField ↥A) :
    ∃ f : Polynomial (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥M L))),
      f.Monic ∧ f.natDegree ≤ Module.finrank ↥M L ∧ Polynomial.aeval x f = 0 := by
  classical
  set N := Module.finrank ↥M L with hN
  have hdep : ¬ LinearIndependent (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥M L)))
      (fun i : Fin (N + 1) => x ^ (i : ℕ)) := by
    intro hind
    have hlift : ∀ i : Fin (N + 1), ∃ a : ↥A, IsLocalRing.residue ↥A a = x ^ (i : ℕ) :=
      fun i => IsLocalRing.residue_surjective _
    choose a ha using hlift
    have hind' : LinearIndependent (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥M L)))
        (fun i => IsLocalRing.residue ↥A (a i)) := by
      simpa only [ha] using hind
    have hli := linearIndependent_lift A M a hind'
    have hcard := LinearIndependent.fintype_card_le_finrank hli
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨g, hg, i₀, hg₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  set f : Polynomial (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥M L))) :=
    ∑ i : Fin (N + 1), Polynomial.C (g i) * Polynomial.X ^ (i : ℕ) with hf
  have hcoeff : f.coeff (i₀ : ℕ) = g i₀ := by
    rw [hf, Polynomial.finsetSum_coeff, Finset.sum_eq_single i₀]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      exact fun h => hb (Fin.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ i₀) h
  have hf0 : f ≠ 0 := fun hzero =>
    hg₀ (by rw [hzero, Polynomial.coeff_zero] at hcoeff; exact hcoeff.symm)
  have hdeg : f.natDegree ≤ N := by
    rw [hf, Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro M' hM'
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have hi : (i : ℕ) < M' := by have h1 : (i : ℕ) < N + 1 := i.isLt; omega
    rw [if_neg (by omega), mul_zero]
  have heval : Polynomial.aeval x f = 0 := by
    rw [hf, map_sum]
    simpa only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Algebra.smul_def] using hg
  refine ⟨Polynomial.C f.leadingCoeff⁻¹ * f, ?_, ?_, ?_⟩
  · exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
      (by rw [inv_mul_cancel₀ ((Polynomial.leadingCoeff_ne_zero).mpr hf0)])
  · rw [Polynomial.natDegree_C_mul (inv_ne_zero ((Polynomial.leadingCoeff_ne_zero).mpr hf0))]
    exact hdeg
  · rw [map_mul, Polynomial.aeval_C, heval, mul_zero]

/-- **The residue field of `A ∩ M` is perfect when that of `A` is.**  `B := A.comap (algebraMap ↥M L)`
is a valuation subring of `M`; its residue field `B/𝔪_B` embeds into the residue field `A/𝔪_A` of
`A` (the maximal ideal of `B` is `B ∩ 𝔪_A`), and the corresponding extension of residue fields is
finite of degree at most `[L : M]`: by
`NK.RamificationAudit.linearIndependent_lift`, linearly independent residue classes lift to
`M`-linearly independent elements of `L`, and hence there are at most `[L : M]` of them.  So every
element of `A/𝔪_A` is a root of a monic polynomial over `B/𝔪_B` of degree at most `[L : M]`
(`NK.RamificationAudit.exists_monic_aeval_eq_zero_natDegree_le`), and a finite extension of a
perfect field which is perfect on top is perfect at the bottom
(`NK.RamificationAudit.perfectField_of_forall_monic_aeval_eq_zero_natDegree_le`).

Indeed: if `a ∈ B/𝔪_B` is not a `p`-th power, then `a^{1/p^n} ∈ A/𝔪_A` for every `n` (as `A/𝔪_A`
is perfect), so `[A/𝔪_A : B/𝔪_B] ≥ p^n` for all `n`, contradicting finiteness. -/
theorem perfectField_residueField_comap {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (M : IntermediateField K L) [IsGalois K ↥M] [IsGalois K L]
    [Finite ↥(A.decompositionSubgroup K)] (hA : A.decompositionSubgroup K = ⊤)
    [PerfectField (IsLocalRing.ResidueField A)] :
    PerfectField (IsLocalRing.ResidueField (A.comap (algebraMap ↥M L))) := by
  -- `Gal(L/K)` is finite, so `L/K` and hence `L/M` are finite dimensional.
  have htop : Finite ↥(⊤ : Subgroup (L ≃ₐ[K] L)) := by rw [← hA]; infer_instance
  have hfin : Finite (L ≃ₐ[K] L) :=
    Finite.of_equiv ↥(⊤ : Subgroup (L ≃ₐ[K] L)) Subgroup.topEquiv.toEquiv
  have hfd : FiniteDimensional K L := IsGalois.finiteDimensional_of_finite K L
  exact perfectField_of_forall_monic_aeval_eq_zero_natDegree_le (Module.finrank ↥M L)
    (fun x => exists_monic_aeval_eq_zero_natDegree_le A M x)

end NK.RamificationAudit
