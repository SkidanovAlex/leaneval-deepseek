import Mathlib
import Submission.Work.DSF1.Cech.CechSetup
import Submission.Work.DSF1.Cech.CechLocalized
import Submission.Work.DSF1.Cech.CechComponents
import Submission.Work.DSF1.Cech.basicOpen_localization_facts

/-!
# Definitions for the affine Čech exactness (`cechSpec_quasiIso`)

Let `R` be a commutative ring, `f : ι → R` a finite family, `X = Spec R` and
`U i = D (f i)` the family of principal opens.  This file sets up the objects
used by the main argument:

* `cechSpec f` — the Čech complex `𝒞` of the structure sheaf of `Spec R`
  (viewed as a presheaf of `R`-modules) along the family `U`;
* `cechSpecQi f i` — the Čech complex `𝒞ᵢ` of the presheaf `W ↦ 𝒪 (W ⊓ U i)`;
* `loc f i : 𝒞 ⟶ 𝒞ᵢ` — the chain map induced by the restriction;
* `coaugQ f` — the coaugmentation `𝒪(⊤) ⟶ 𝒞⁰`;
* `coaug0 f` — the coaugmentation `R ⟶ 𝒞⁰` (`R = 𝒪(Spec R, ⊤)`).

It also contains the "partition of unity" step `exists_d_eq_of_localized`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

variable {R : Type u} [CommRing R] {ι : Type u}

/-- The affine scheme `Spec R`. -/
noncomputable abbrev spec (R : Type u) [CommRing R] : Scheme.{u} := Spec (CommRingCat.of R)

/-- The structure sheaf of `Spec R` as a presheaf of `R`-modules. -/
noncomputable abbrev specPresheaf (R : Type u) [CommRing R] :
    (spec R).Opensᵒᵖ ⥤ ModuleCat R :=
  DSMap.cechPresheaf R (spec R) (𝟙 (spec R))

/-- The family of principal opens `D (f i)`. -/
noncomputable abbrev basicOpens (f : ι → R) : ι → (spec R).Opens :=
  fun i => PrimeSpectrum.basicOpen (f i)

/-- The Čech complex of the structure sheaf of `Spec R` along the principal opens. -/
noncomputable abbrev cechSpec (f : ι → R) : CochainComplex (ModuleCat R) ℕ :=
  (cechComplexFunctor (basicOpens f)).obj (specPresheaf R)

/-- The Čech complex of the presheaf `W ↦ 𝒪 (W ⊓ D (f i))`. -/
noncomputable abbrev cechSpecQi (f : ι → R) (i : ι) : CochainComplex (ModuleCat R) ℕ :=
  (cechComplexFunctor (basicOpens f)).obj (Qi (basicOpens f) (specPresheaf R) i)

/-- The chain map `locᵢ : 𝒞 ⟶ 𝒞ᵢ` induced by the restriction `P V ⟶ P (V ⊓ U i)`. -/
noncomputable def loc (f : ι → R) (i : ι) : cechSpec f ⟶ cechSpecQi f i :=
  (cechComplexFunctor (basicOpens f)).map (etaI (basicOpens f) (specPresheaf R) i)

/-- The coaugmentation `𝒪(⊤) ⟶ 𝒞⁰` of the Čech complex of the structure sheaf. -/
noncomputable abbrev coaugQ (f : ι → R) :
    (specPresheaf R).obj (op ⊤) ⟶ (cechSpec f).X 0 :=
  coaug (basicOpens f) (specPresheaf R)

/-- The coaugmentation of the localized Čech complex `𝒞ᵢ`: `Qi(⊤) ⟶ 𝒞ᵢ⁰`. -/
noncomputable abbrev coaugQi (f : ι → R) (i : ι) :
    (Qi (basicOpens f) (specPresheaf R) i).obj (Opposite.op ⊤) ⟶ (cechSpecQi f i).X 0 :=
  coaug (basicOpens f) (Qi (basicOpens f) (specPresheaf R) i)

/-- The restriction `𝒪(⊤) ⟶ Qi(⊤)` of the comparison map `locᵢ` in degree `0`. -/
noncomputable abbrev etaITop (f : ι → R) (i : ι) :
    (specPresheaf R).obj (Opposite.op ⊤) ⟶
      (Qi (basicOpens f) (specPresheaf R) i).obj (Opposite.op ⊤) :=
  (etaI (basicOpens f) (specPresheaf R) i).app (Opposite.op ⊤)

/-- The map `R → Γ(Spec R, ⊤) = 𝒪(⊤)` given by the algebra structure. -/
noncomputable abbrev unitTop (R : Type u) [CommRing R] :
    ModuleCat.of R R ⟶ (specPresheaf R).obj (op ⊤) :=
  DSMap.unitTop R (spec R) (𝟙 (spec R))

/-- The coaugmentation `R ⟶ 𝒞⁰`. -/
noncomputable abbrev coaug0 (f : ι → R) :
    ModuleCat.of R R ⟶ (cechSpec f).X 0 :=
  DSMap.coaug0 R (spec R) (𝟙 (spec R)) (basicOpens f)

/-- The coaugmentation for `R` factors through the coaugmentation for `𝒪(⊤)`. -/
lemma unitTop_comp_coaugQ (f : ι → R) :
    unitTop R ≫ coaugQ f = coaug0 f := by
  rw [show coaugQ f = Pi.lift (fun x => (specPresheaf R).map (homOfLE le_top).op) from rfl,
    show coaug0 f = Pi.lift (fun x => unitTop R ≫ (specPresheaf R).map (homOfLE le_top).op)
      from rfl]
  refine Pi.hom_ext _ _ (fun b => ?_)
  rw [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π]

/-- **Partition of unity.**  If for every `i` some power of `f i` times `s` is a
boundary in `𝒞`, then `s` itself is a boundary. -/
theorem exists_d_eq_of_localized (f : ι → R) (h : Ideal.span (Set.range f) = ⊤) (n : ℕ)
    (s : (cechSpec f).X (n + 1))
    (H : ∀ i : ι, ∃ (k : ℕ) (t : (cechSpec f).X n),
      ((cechSpec f).d n (n + 1)).hom t = f i ^ k • s) :
    ∃ t : (cechSpec f).X n, ((cechSpec f).d n (n + 1)).hom t = s := by
  have hmem : s ∈ LinearMap.range (((cechSpec f).d n (n + 1)).hom) :=
    Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range f) h s (fun r => by
      obtain ⟨i, hi⟩ := Set.mem_range.mp r.2
      obtain ⟨k, t, ht⟩ := H i
      refine ⟨k, ?_⟩
      rw [← hi]
      exact ⟨t, ht⟩)
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, ht⟩

end Work.DSF1.Cech

namespace Work.DSF1.Cech

variable {R : Type u} [CommRing R] {ι : Type u}

/-! ## Interface lemmas

The complexes `cechSpec f` and `cechSpecQi f i` are products, over the simplices of the
Čech nerve, of the section modules `Γ(Spec R, W)`.  The `R`-module structure on these is
the one induced by the structure sheaf, and it agrees definitionally with the Mathlib
algebra structure `Algebra R ↥(secRing R W)` of `basicOpen_localization_facts`: the two
lemmas below record how to move between the two descriptions.  Note that statements about
ring operations on sections are easiest to elaborate when an element `x` of a section
module is coerced with `(show ↥(secRing R W) from x)`. -/

/-- The scalar action on the section module of `Spec R` over `W` is multiplication by the
image of the scalar in the ring of sections. -/
lemma smul_eq_algebraMap_mul (r : R) (W : (spec R).Opens)
    (x : (specPresheaf R).obj (op W)) :
    r • x = (algebraMap R ↑(secRing R W) r) * (show ↑(secRing R W) from x) :=
  rfl

/-- The map on sections of the structure sheaf is the restriction map. -/
lemma specPresheaf_map_apply {W W' : (spec R).Opens} (h : W ≤ W')
    (x : (specPresheaf R).obj (op W')) :
    ((specPresheaf R).map (homOfLE h).op).hom x =
      resSection R h (show ↑(secRing R W') from x) :=
  rfl

end Work.DSF1.Cech
