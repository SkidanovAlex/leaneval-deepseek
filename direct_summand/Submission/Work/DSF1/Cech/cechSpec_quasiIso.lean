import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Cech.CechMain
import Submission.Work.DSF1.Cech.UnitCase
import Submission.Work.DSF1.Cech.isIsoDeletion_Qi
import Submission.Work.DSF1.Cech.exists_pow_smul_mem_range_loc
import Submission.Work.DSF1.Cech.eq_zero_of_loc_eq_zero
import Submission.Work.DSF1.Cech.coaug0_injective
import Submission.Work.DSF1.Cech.LcH0

/-!
# The Čech complex of `Spec R` resolves `R` (Stacks 01X9, `R`-form)

Let `R` be a commutative ring and `f : ι → R` a finite family generating the unit ideal.
Writing `U i = D (f i)` for the principal opens and `𝒞` for the Čech complex of the
structure sheaf of `Spec R` along `U` (as a complex of `R`-modules), the coaugmentation
`R ⟶ 𝒞⁰` is a quasi-isomorphism of chain complexes.

The proof is assembled in `Submission.Work.DSF1.Cech.CechMain`: for each `i` the
localized complex `𝒞ᵢ` (the Čech complex of the presheaf `W ↦ 𝒪 (W ⊓ D (f i))`) is
acyclic in positive degrees and has `H⁰ = 𝒪(D (f i))` by the unit case
(`UnitCase`, `isIsoDeletion_Qi`); this descends to `𝒞` by clearing denominators
(`exists_pow_smul_mem_range_loc`, `eq_zero_of_loc_eq_zero`) and the partition of unity
(`exists_d_eq_of_localized`), while in degree `0` the two statements
`coaug0_injective` and `coaug0_surjective_ker` identify `H⁰ (𝒞)` with `R`.  Transporting
along `HomologicalComplex.extendSingleIso` gives the result for the `ℤ`-graded complex
`DSMap.cechZ`.
-/

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace Work.DSF1.Cech

universe u

/-- **Stacks 01X9 (`R`-form).**  For a finite family `f` generating the unit ideal, the
Čech complex of the structure sheaf of `Spec R` along the principal opens `D (f i)` is a
resolution of `R`: the coaugmentation is a quasi-isomorphism. -/
theorem cechSpec_quasiIso (R : Type u) [CommRing R] {ι : Type u} [Finite ι] (f : ι → R)
    (h : Ideal.span (Set.range f) = ⊤) :
    ∃ cc : (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          (ModuleCat.of R R) ⟶
        DSMap.cechZ R (AlgebraicGeometry.Spec (CommRingCat.of R))
          (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of R)))
          (fun i => PrimeSpectrum.basicOpen (f i)),
      HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ) cc := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hC1 : ∀ i : ι, ∀ (m : ℕ) (z : (cechSpecQi f i).X m),
      ∃ (k : ℕ) (t : (cechSpec f).X m), (loc f i).f m t = f i ^ k • z :=
    fun i => exists_pow_smul_mem_range_loc f i
  have hC2 : ∀ i : ι, ∀ (m : ℕ) (t : (cechSpec f).X m), (loc f i).f m t = 0 →
      ∃ k : ℕ, f i ^ k • t = 0 :=
    fun i => eq_zero_of_loc_eq_zero f i
  have hpos : ∀ i : ι, ∀ n : ℕ, ∀ s : (cechSpecQi f i).X (n + 1),
      ((cechSpecQi f i).d (n + 1) (n + 2)).hom s = 0 →
        ∃ t : (cechSpecQi f i).X n, ((cechSpecQi f i).d n (n + 1)).hom t = s :=
    fun i => (UnitCase (basicOpens f) (Qi (basicOpens f) (specPresheaf R) i) i
      (isIsoDeletion_Qi (basicOpens f) (specPresheaf R) i)).2.1
  have hZ : ∀ i : ι, ∀ s : (cechSpecQi f i).X 0, ((cechSpecQi f i).d 0 1).hom s = 0 →
      ∃ q : (Qi (basicOpens f) (specPresheaf R) i).obj (Opposite.op ⊤),
        (coaugQi f i).hom q = s :=
    fun i => (UnitCase (basicOpens f) (Qi (basicOpens f) (specPresheaf R) i) i
      (isIsoDeletion_Qi (basicOpens f) (specPresheaf R) i)).2.2.2
  exact ⟨cechZCC f, quasiIso_cechZCC f (quasiIso_coaugMap f
    (exact_of_localized f h hpos hC1 hC2) (coaug0_injective f h)
      (coaug0_surjective_of_localized f h hZ))⟩

end Work.DSF1.Cech
