import Mathlib
import Submission.Work.DSF1.Cech.CechDefs
import Submission.Work.DSF1.Cech.basicOpen_localization_facts
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi
import Submission.Work.DSF1.Cech.isIsoDeletion_Qi
import Submission.Work.DSF1.Cech.CoaugCycle

/-!
# Clearing denominators for the comparison map `locᵢ : 𝒞 ⟶ 𝒞ᵢ`

Let `R` be a commutative ring, `f : ι → R` a finite family, `U i = D (f i)` the family of
principal opens of `Spec R`, and `Qᵢ` the presheaf `W ↦ 𝒪 (W ⊓ U i)`.  The comparison map
`loc f i : cechSpec f ⟶ cechSpecQi f i` is induced by the restriction `P ⟶ Qᵢ`.

The main result of this file is `exists_pow_smul_mem_range_loc`: every element `z` of a term of
`cechSpecQi f i` becomes, after multiplying by a power of `f i`, the image under `loc f i` of an
element of the corresponding term of `cechSpec f`.

The proof is componentwise.  In degree `n` both complexes are products, indexed by the
`(n+1)`-simplices `x`, of the section modules `𝒪 (E n x)` resp. `𝒪 (E n x ⊓ U i)`, and `loc` is
the product of the restriction maps.  Each simplex open `E n x` is a basic open,
`E n x = D (∏ a, f (x a))`, so `basicOpen_localization_facts` applies: `𝒪 (E n x ⊓ U i)` is the
localization of `𝒪 (E n x)` away from `f i`, which is precisely the componentwise statement.
Since the index set of the product is finite, the (finitely many) exponents can be collected
into a single one.

## Main results

* `specPresheaf_basicOpen_surj`: the "surjectivity up to powers" half of
  `basicOpen_localization_facts`, phrased for the module `specPresheaf R`;
* `Eobj_basicOpens`: the open attached to a simplex is the basic open of the product of the
  corresponding `f`'s;
* `Eobj_loc_component`: the componentwise version of the main theorem;
* `exists_pow_smul_mem_range_loc`: the main theorem.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

variable {R : Type u} [CommRing R] {ι : Type u} [Fintype ι]

/-- **Surjectivity up to powers, for a basic open.**  Every element of `𝒪 (D g ⊓ D h)` is,
after multiplying by a power of the image of `h`, the restriction of an element of `𝒪 (D g)`.

This is the first half of `basicOpen_localization_facts`, rewritten so that the scalar action
of `R` on the section module replaces the multiplication in the ring of sections. -/
theorem specPresheaf_basicOpen_surj (g h : R)
    (z : (specPresheaf R).obj (op (PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen h))) :
    ∃ (k : ℕ) (t : (specPresheaf R).obj (op (PrimeSpectrum.basicOpen g))),
      ((specPresheaf R).map (homOfLE (inf_le_left : PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen h ≤ PrimeSpectrum.basicOpen g)).op).hom t
        = h ^ k • z := by
  obtain ⟨k, t, ht⟩ := (basicOpen_localization_facts R g h).1 z
  refine ⟨k, t, ?_⟩
  have ht2 : (show ↑(secRing R (PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen h)) from z) * (resSection R (le_top : PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen h ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h)) ^ k
      = ((specPresheaf R).map (homOfLE (inf_le_left : PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen h ≤ PrimeSpectrum.basicOpen g)).op).hom t := ht
  rw [← ht2, resSection_le_top_GammaSpecIso_inv R (PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen h) h]
  simp only [← map_pow]
  rw [smul_eq_algebraMap_mul, mul_comm]

/-- The open attached to a simplex `x : Fin (n+1) → ι` of the Čech nerve of the principal
opens `D (f a)` is the basic open of the product `∏ a, f (x a)`. -/
lemma Eobj_basicOpens (f : ι → R) (n : ℕ) (x : Fin (n+1) → ι) :
    Eobj (basicOpens f) n x = PrimeSpectrum.basicOpen (∏ a, f (x a)) := by
  have h1 : Eobj (basicOpens f) n x = ⨅ a, PrimeSpectrum.basicOpen (f (x a)) := by
    apply le_antisymm
    · exact le_iInf fun a => leOfHom (Pi.π (fun a => (basicOpens f) (x a)) a)
    · exact leOfHom (Pi.lift fun a => homOfLE (iInf_le (fun a => PrimeSpectrum.basicOpen (f (x a))) a))
  have key : ∀ s : Finset (Fin (n+1)), s.inf (fun a => PrimeSpectrum.basicOpen (f (x a)))
      = PrimeSpectrum.basicOpen (∏ a ∈ s, f (x a)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Finset.inf_empty, Finset.prod_empty, PrimeSpectrum.basicOpen_one]
    | insert a s ha ih => rw [Finset.inf_insert, Finset.prod_insert ha, PrimeSpectrum.basicOpen_mul, ih]
  have h2 := key Finset.univ
  rw [Finset.inf_eq_iInf] at h2
  have h3 : (⨅ a, PrimeSpectrum.basicOpen (f (x a)))
      = ⨅ a ∈ (Finset.univ : Finset (Fin (n+1))), PrimeSpectrum.basicOpen (f (x a)) := by simp
  rw [h1, h3, h2]

variable (f : ι → R) (i : ι)

/-- **Componentwise clearing of denominators.**  For a simplex `x`, every element `z` of
`𝒪 (E n x ⊓ U i)` is, after multiplying by a power of `f i`, the restriction of an element of
`𝒪 (E n x)`.

This is `specPresheaf_basicOpen_surj` transported along `Eobj_basicOpens`. -/
lemma Eobj_loc_component (n : ℕ) (x : Fin (n+1) → ι)
    (z : (Qi (basicOpens f) (specPresheaf R) i).obj (op (Eobj (basicOpens f) n x))) :
    ∃ (k : ℕ) (t : (specPresheaf R).obj (op (Eobj (basicOpens f) n x))),
      ((specPresheaf R).map (homOfLE (inf_le_left : Eobj (basicOpens f) n x ⊓ basicOpens f i ≤ Eobj (basicOpens f) n x)).op).hom t
        = f i ^ k • z := by
  have hx : Eobj (basicOpens f) n x = PrimeSpectrum.basicOpen (∏ a, f (x a)) :=
    Eobj_basicOpens f n x
  have hi : Eobj (basicOpens f) n x ⊓ basicOpens f i
      = PrimeSpectrum.basicOpen (∏ a, f (x a)) ⊓ basicOpens f i :=
    congrArg (fun U => U ⊓ basicOpens f i) hx
  obtain ⟨k, t', ht'⟩ := specPresheaf_basicOpen_surj (∏ a, f (x a)) (f i)
    (((specPresheaf R).map (eqToHom hi.symm).op).hom z)
  refine ⟨k, ((specPresheaf R).map (eqToHom hx).op).hom t', ?_⟩
  have hsq : (specPresheaf R).map (eqToHom hx).op ≫
        (specPresheaf R).map (homOfLE (inf_le_left : Eobj (basicOpens f) n x ⊓ basicOpens f i ≤ Eobj (basicOpens f) n x)).op
      = (specPresheaf R).map (homOfLE (inf_le_left : PrimeSpectrum.basicOpen (∏ a, f (x a)) ⊓ basicOpens f i ≤ PrimeSpectrum.basicOpen (∏ a, f (x a)))).op ≫
        (specPresheaf R).map (eqToHom hi).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hsq, ModuleCat.hom_comp, LinearMap.comp_apply, ht', map_smul]
  congr 1

/-- **Clearing denominators for `locᵢ`.**  Every element of a term of the localized Čech
complex `𝒞ᵢ = cechSpecQi f i` is, up to a power of `f i`, in the image of the comparison map
`loc f i : 𝒞 ⟶ 𝒞ᵢ`. -/
theorem exists_pow_smul_mem_range_loc {R : Type u} [CommRing R] {ι : Type u} [Fintype ι] (f : ι → R) (i : ι) (n : ℕ) (z : (Work.DSF1.Cech.cechSpecQi f i).X n) : ∃ (k : ℕ) (t : (Work.DSF1.Cech.cechSpec f).X n), (Work.DSF1.Cech.loc f i).f n t = f i ^ k • z := by
  classical
  -- For every simplex `x` we clear denominators in the `x`-th component of `z`.
  have hcomp : ∀ x : Fin (n+1) → ι,
      ∃ (k : ℕ) (t : (specPresheaf R).obj (op (Eobj (basicOpens f) n x))),
        ((specPresheaf R).map (homOfLE (inf_le_left : Eobj (basicOpens f) n x ⊓ basicOpens f i ≤ Eobj (basicOpens f) n x)).op).hom t
          = f i ^ k • (Pi.π (fun y : Fin (n+1) → ι => (Qi (basicOpens f) (specPresheaf R) i).obj (op (Eobj (basicOpens f) n y))) x).hom z :=
    fun x => Eobj_loc_component f i n x _
  choose k tk hk using hcomp
  have hK : ∀ x, k x ≤ ∑ y, k y := fun x =>
    Finset.single_le_sum (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
  -- Reassemble the components, clearing all denominators with the common exponent `∑ k`.
  refine ⟨∑ y, k y, (ModuleCat.piIsoPi (fun x : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj (basicOpens f) n x)))).inv.hom
      (fun x => f i ^ ((∑ y, k y) - k x) • tk x), ?_⟩
  -- Check the identity componentwise.
  have hkey : ∀ x : Fin (n+1) → ι,
      (Pi.π (fun y : Fin (n+1) → ι => (Qi (basicOpens f) (specPresheaf R) i).obj (op (Eobj (basicOpens f) n y))) x).hom
        ((loc f i).f n ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj (basicOpens f) n x)))).inv.hom
          (fun x => f i ^ ((∑ y, k y) - k x) • tk x)))
      = (Pi.π (fun y : Fin (n+1) → ι => (Qi (basicOpens f) (specPresheaf R) i).obj (op (Eobj (basicOpens f) n y))) x).hom
          (f i ^ (∑ y, k y) • z) := by
    intro x
    have hstep : (Pi.π (fun y : Fin (n+1) → ι => (Qi (basicOpens f) (specPresheaf R) i).obj (op (Eobj (basicOpens f) n y))) x).hom
          ((loc f i).f n ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj (basicOpens f) n x)))).inv.hom
            (fun x => f i ^ ((∑ y, k y) - k x) • tk x)))
        = ((specPresheaf R).map (homOfLE (inf_le_left : Eobj (basicOpens f) n x ⊓ basicOpens f i ≤ Eobj (basicOpens f) n x)).op).hom
            ((Pi.π (fun y : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj (basicOpens f) n y))) x).hom
              ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj (basicOpens f) n x)))).inv.hom
                (fun x => f i ^ ((∑ y, k y) - k x) • tk x))) := by
      have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (cechComplexFunctor_map_pi (basicOpens f) (etaI (basicOpens f) (specPresheaf R) i) n x))
        ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj (basicOpens f) n x)))).inv.hom
          (fun x => f i ^ ((∑ y, k y) - k x) • tk x))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    rw [hstep, ModuleCat.piIsoPi_inv_kernel_ι_apply]
    rw [map_smul, hk x, smul_smul, ← pow_add, Nat.sub_add_cancel (hK x)]
    exact (map_smul (Pi.π (fun y : Fin (n+1) → ι => (Qi (basicOpens f) (specPresheaf R) i).obj (op (Eobj (basicOpens f) n y))) x).hom (f i ^ (∑ y, k y)) z).symm
  have h1 : (ModuleCat.piIsoPi (fun y : Fin (n+1) → ι => (Qi (basicOpens f) (specPresheaf R) i).obj (op (Eobj (basicOpens f) n y)))).hom.hom
        ((loc f i).f n ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj (basicOpens f) n x)))).inv.hom
          (fun x => f i ^ ((∑ y, k y) - k x) • tk x)))
      = (ModuleCat.piIsoPi (fun y : Fin (n+1) → ι => (Qi (basicOpens f) (specPresheaf R) i).obj (op (Eobj (basicOpens f) n y)))).hom.hom
          (f i ^ (∑ y, k y) • z) := by
    funext x
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply, ModuleCat.piIsoPi_hom_ker_subtype_apply]
    exact hkey x
  have h2 := congrArg (ModuleCat.piIsoPi (fun y : Fin (n+1) → ι => (Qi (basicOpens f) (specPresheaf R) i).obj (op (Eobj (basicOpens f) n y)))).inv.hom h1
  simpa only [Iso.hom_inv_id_apply] using h2

end Work.DSF1.Cech
