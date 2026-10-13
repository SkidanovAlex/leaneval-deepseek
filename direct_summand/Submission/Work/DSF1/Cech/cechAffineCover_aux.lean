import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Cech.CechOLocal
import Submission.Work.DSF1.Cech.CechQo
import Submission.Work.DSF1.Cech.isIsoDeletion_Qo
import Submission.Work.DSF1.Cech.isAffineOpen_Eobj
import Submission.Work.DSF1.Cech.eq_zero_of_loc_eq_zero
import Submission.Work.DSF1.Cech.loc_coaug_naturality
import Submission.Work.DSF1.Cech.CechMain
import Submission.Work.DSF1.Cech.UnitCase
import Submission.Work.DSF1.Cech.LcH0
import Submission.Work.DSF1.Cech.coaug0_injective
import Submission.Work.DSF1.Cech.specPresheaf_loc_affine

/-!
# The affine cover case of the Čech resolution

This file assembles the proof that the Čech complex of the structure sheaf of `Spec R` along
*any* finite cover by affine opens resolves `R`.  The mathematical content is the standard
"clearing denominators at a principal open inside a member of the cover + partition of unity"
argument:

* for `g : R` and a member `U i₀ ⊇ D g` of the cover, the presheaf `W ↦ 𝒪 (W ⊓ D g)` inverts the
  cofaces inserting `i₀` (`isIsoDeletion_Qo`), so the unit case (`UnitCase`) shows that its Čech
  complex `cechOQ R U (D g)` is exact in positive degrees with cohomology `Γ(D g)` in degree `0`;
* `specPresheaf_loc_affine` transports this to the original complex: the comparison map
  `locO R U (D g)` is a localization at `g` on every Čech term, so exactness of the localized
  complex implies exactness (resp. the degree zero statements) up to powers of `g`;
* the `g` with `D g ≤ U i` for some `i` generate the unit ideal (`span_basicOpen_le_generates`),
  so a single application of `Submodule.mem_of_span_eq_top_of_smul_pow_mem` finishes.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

variable {R : Type u} [CommRing R] {ι : Type u}

/-- In degree `0`, the comparison map `locO R U V` is the product over the `0`-simplices of
the restrictions `η : P (Eobj U 0 x) ⟶ Qo P V (Eobj U 0 x)`. -/
lemma locO_f_zero (R : Type u) [CommRing R] {ι : Type u} (U : ι → (spec R).Opens)
    (V : (spec R).Opens) :
    (locO R U V).f 0 =
      Limits.Pi.map (fun x => (etaO (specPresheaf R) V).app (op (Eobj U 0 x))) := by
  rw [locO]
  simp only [CategoryTheory.cechComplexFunctor,
    FormalCoproduct.cochainComplexFunctor_map_f]

/-- The coaugmentation is natural with respect to the comparison map `locO R U V`. -/
theorem locO_coaug_naturality (R : Type u) [CommRing R] {ι : Type u} (U : ι → (spec R).Opens)
    (V : (spec R).Opens) :
    CategoryTheory.CategoryStruct.comp (coaug U (specPresheaf R)) ((locO R U V).f 0) =
      CategoryTheory.CategoryStruct.comp ((etaO (specPresheaf R) V).app (op ⊤))
        (coaug U (Qo (specPresheaf R) V)) := by
  have h1 := locO_f_zero R U V
  have hmain :
      Limits.Pi.lift (fun x : (E U).obj (op ⦋0⦌) |>.I =>
          (specPresheaf R).map (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op) ≫
        Limits.Pi.map (fun x => (etaO (specPresheaf R) V).app (op (Eobj U 0 x))) =
      (etaO (specPresheaf R) V).app (op ⊤) ≫
        Limits.Pi.lift (fun x : (E U).obj (op ⦋0⦌) |>.I =>
          (Qo (specPresheaf R) V).map (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op) := by
    rw [pi_lift_comp_map, pi_comp_lift]
    refine Limits.Pi.hom_ext
      (f := fun x => (Qo (specPresheaf R) V).obj (op (Eobj U 0 x))) _ _ (fun x => ?_)
    rw [Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π]
    exact ((etaO (specPresheaf R) V).naturality
      (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op).symm
  rw [h1]
  exact hmain

/-- The coaugmentation `unitTop ≫ coaug` is `coaugO`. -/
lemma unitTop_comp_coaugO (R : Type u) [CommRing R] {ι : Type u} (U : ι → (spec R).Opens) :
    unitTop R ≫ coaug U (specPresheaf R) = coaugO R U := by
  rw [show coaugO R U = DSMap.coaug0 R (spec R) (𝟙 (spec R)) U from rfl]
  rw [show coaug U (specPresheaf R) =
    Pi.lift (fun x : (E U).obj (op ⦋0⦌) |>.I =>
      (specPresheaf R).map (homOfLE (le_top : Eobj U 0 x ≤ ⊤)).op) from rfl]
  rw [pi_comp_lift]
  rfl

/-- **The unit case for the localized presheaf `W ↦ 𝒪 (W ⊓ V)`.**  If `V ≤ U i₀` then the
Čech complex `cechOQ R U V` is exact in positive degrees and its degree zero cohomology is
`𝒪 (V)`, with the coaugmentation injective onto the cycles. -/
theorem unitCase_Qo (R : Type u) [CommRing R] {ι : Type u} (U : ι → (spec R).Opens)
    (V : (spec R).Opens) (i₀ : ι) (hV : V ≤ U i₀) :
    (coaug U (Qo (specPresheaf R) V) ≫ (cechOQ R U V).d 0 1 = 0) ∧
      (∀ (n : ℕ) (s : (cechOQ R U V).X (n + 1)),
        (cechOQ R U V).d (n + 1) (n + 2) s = 0 →
          ∃ t : (cechOQ R U V).X n, (cechOQ R U V).d n (n + 1) t = s) ∧
      Function.Injective (coaug U (Qo (specPresheaf R) V)).hom ∧
      (∀ s : (cechOQ R U V).X 0, (cechOQ R U V).d 0 1 s = 0 →
        ∃ q : (Qo (specPresheaf R) V).obj (op ⊤),
          (coaug U (Qo (specPresheaf R) V)).hom q = s) :=
  UnitCase U (Qo (specPresheaf R) V) i₀ (isIsoDeletion_Qo hV)

/-! ## Exactness in positive degrees -/

variable (R : Type u) [CommRing R] {ι : Type u} (U : ι → (spec R).Opens)

/-- **Clearing denominators at one localizing open.**  Let `V` be an open, `g : R`, and
suppose that the comparison map `locO R U V` is a localization at `g` on every Čech term (the
hypotheses `hsurj` and `hker`) and that the localized complex is exact in positive degrees
(`hexact`).  Then a cycle `s` of the Čech complex becomes a boundary after multiplying by a
power of `g`. -/
theorem exists_pow_smul_mem_range_dO (g : R) (V : (spec R).Opens)
    (hsurj : ∀ (n : ℕ) (z : (cechOQ R U V).X n),
      ∃ (k : ℕ) (t : (cechO R U).X n), (locO R U V).f n t = g ^ k • z)
    (hker : ∀ (n : ℕ) (t : (cechO R U).X n),
      (locO R U V).f n t = 0 → ∃ k : ℕ, g ^ k • t = 0)
    (hexact : ∀ (n : ℕ) (s : (cechOQ R U V).X (n + 1)),
      (cechOQ R U V).d (n + 1) (n + 2) s = 0 →
        ∃ t : (cechOQ R U V).X n, (cechOQ R U V).d n (n + 1) t = s)
    (n : ℕ) (s : (cechO R U).X (n + 1)) (hs : (cechO R U).d (n + 1) (n + 2) s = 0) :
    ∃ (k : ℕ) (t : (cechO R U).X n), (cechO R U).d n (n + 1) t = g ^ k • s := by
  have hcomm := (locO R U V).comm' (n + 1) (n + 2) (by simp)
  have hcommn := (locO R U V).comm' n (n + 1) (by simp)
  -- the image of the cycle `s` is a cycle of the localized complex
  have hcyc : (cechOQ R U V).d (n + 1) (n + 2) ((locO R U V).f (n + 1) s) = 0 := by
    have hh : (locO R U V).f (n + 2) ((cechO R U).d (n + 1) (n + 2) s) =
        (cechOQ R U V).d (n + 1) (n + 2) ((locO R U V).f (n + 1) s) := by
      have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcomm) s
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this.symm
    rw [← hh, hs, map_zero]
  obtain ⟨z, hz⟩ := hexact n _ hcyc
  obtain ⟨k, t, ht⟩ := hsurj n z
  -- the difference is killed by `locO`, hence by a power of `g`
  have h1 : (locO R U V).f (n + 1) ((cechO R U).d n (n + 1) t) =
      (cechOQ R U V).d n (n + 1) ((locO R U V).f n t) := by
    have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcommn) t
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this.symm
  have hL : (locO R U V).f (n + 1) ((cechO R U).d n (n + 1) t - g ^ k • s) = 0 := by
    rw [map_sub, h1, ht, map_smul, hz, map_smul, sub_self]
  obtain ⟨l, hl⟩ := hker (n + 1) _ hL
  refine ⟨l + k, g ^ l • t, ?_⟩
  have h5 : g ^ l • ((cechO R U).d n (n + 1) t) = g ^ (l + k) • s := by
    have hh := hl
    rw [smul_sub, smul_smul, ← pow_add] at hh
    exact sub_eq_zero.mp hh
  rw [map_smul, h5]

/-- **Exactness in positive degrees.**  If for every `g` in a set `G` spanning the unit ideal
the localized complex `cechOQ R U (D g)` is exact in positive degrees and the comparison map
`locO R U (D g)` is a localization at `g` on each Čech term, then the Čech complex `cechO R U`
is exact in positive degrees. -/
theorem exact_positive_cechO (G : Set R) (hspan : Ideal.span G = ⊤)
    (hsurj : ∀ g ∈ G, ∀ (n : ℕ) (z : (cechOQ R U (PrimeSpectrum.basicOpen g)).X n),
      ∃ (k : ℕ) (t : (cechO R U).X n),
        (locO R U (PrimeSpectrum.basicOpen g)).f n t = g ^ k • z)
    (hker : ∀ g ∈ G, ∀ (n : ℕ) (t : (cechO R U).X n),
      (locO R U (PrimeSpectrum.basicOpen g)).f n t = 0 → ∃ k : ℕ, g ^ k • t = 0)
    (hexact : ∀ g ∈ G, ∀ (n : ℕ) (s : (cechOQ R U (PrimeSpectrum.basicOpen g)).X (n + 1)),
      (cechOQ R U (PrimeSpectrum.basicOpen g)).d (n + 1) (n + 2) s = 0 →
        ∃ t : (cechOQ R U (PrimeSpectrum.basicOpen g)).X n,
          (cechOQ R U (PrimeSpectrum.basicOpen g)).d n (n + 1) t = s)
    (n : ℕ) (s : (cechO R U).X (n + 1)) (hs : (cechO R U).d (n + 1) (n + 2) s = 0) :
    ∃ t : (cechO R U).X n, (cechO R U).d n (n + 1) t = s := by
  have hmem : s ∈ LinearMap.range ((cechO R U).d n (n + 1)).hom := by
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ G hspan s (fun r => ?_)
    obtain ⟨k, t, ht⟩ := exists_pow_smul_mem_range_dO R U (r : R) (PrimeSpectrum.basicOpen (r : R))
      (hsurj (r : R) r.2) (hker (r : R) r.2) (hexact (r : R) r.2) n s hs
    exact ⟨k, t, ht⟩
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, ht⟩

/-! ## The elements defining a basic open inside a member of the cover span the unit ideal -/

/-- If the opens `U i` cover `Spec R`, then the `g : R` whose basic open is contained in some
`U i` generate the unit ideal. -/
theorem span_basicOpen_le_generates (hcov : sSup (Set.range U) = ⊤) :
    Ideal.span (setOf fun g : R => ∃ i : ι, PrimeSpectrum.basicOpen g ≤ U i) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm_max, hm_le⟩ := Ideal.exists_le_maximal _ hne
  let p : (spec R) := ⟨m, hm_max.isPrime⟩
  have hpU : p ∈ sSup (Set.range U) := by rw [hcov]; trivial
  rw [sSup_range] at hpU
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hpU
  obtain ⟨t, ⟨g, rfl⟩, hpt, htU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (U i).isOpen
  have hgS : g ∈ setOf (fun g : R => ∃ i : ι, PrimeSpectrum.basicOpen g ≤ U i) := ⟨i, htU⟩
  have hgm : g ∈ m := hm_le (Ideal.subset_span hgS)
  exact (PrimeSpectrum.mem_basicOpen g p).mp hpt hgm

/-! ## The degree zero part -/

/-- The global section of `a : R` is the image of `a` under `ΓSpecIso`. -/
lemma unitTop_eq_ΓSpecIso_inv (R : Type u) [CommRing R] (a : R) :
    (unitTop R).hom a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := by
  have h1 : ∀ x : Γ(spec R, ⊤),
      ((spec R).presheaf.map (homOfLE (le_top : (⊤ : (spec R).Opens) ≤ ⊤)).op).hom x = x := by
    intro x
    rw [show (homOfLE (le_top : (⊤ : (spec R).Opens) ≤ ⊤)) = 𝟙 (⊤ : (spec R).Opens)
      from Subsingleton.elim _ _]
    simp
  have hphi : DSMap.phi R (spec R) (𝟙 (spec R)) a =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := by
    have h := DSMap.phi_SpecMap (A := R) (B := R) (𝟙 (CommRingCat.of R))
    rw [Spec.map_id, Category.id_comp] at h
    exact congrArg (fun (f : CommRingCat.of R ⟶ Γ(spec R, ⊤)) => CommRingCat.Hom.hom f a) h
  have h2 : (unitTop R).hom a = DSMap.phi R (spec R) (𝟙 (spec R)) a := rfl
  rw [h2, hphi]

/-- The global section of an element is injective into the sections over `⊤`. -/
lemma unitTop_injective (R : Type u) [CommRing R] : Function.Injective (unitTop R).hom := by
  have key : ∀ a : R, (unitTop R).hom a = 0 → a = 0 := by
    intro a ha
    rw [unitTop_eq_ΓSpecIso_inv] at ha
    have h2 := congrArg (fun x => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) ha
    simpa [Iso.hom_inv_id_apply] using h2
  intro a b hab
  have h : (unitTop R).hom (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (key (a - b) h)

/-- Every section over a basic open is, up to a power of the localizing element, the restriction
of a global section. -/
lemma specPresheaf_loc_lift (g : R)
    (z : (Qo (specPresheaf R) (PrimeSpectrum.basicOpen g)).obj (op ⊤)) :
    ∃ (k : ℕ) (a : R), g ^ k • z =
      (etaO (specPresheaf R) (PrimeSpectrum.basicOpen g)).app (op ⊤) ((unitTop R).hom a) := by
  obtain ⟨k, t, ht⟩ := (specPresheaf_loc_affine R (isAffineOpen_top (spec R)) g).1 z
  refine ⟨k, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom t, ?_⟩
  rw [show (etaO (specPresheaf R) (PrimeSpectrum.basicOpen g)).app (op ⊤) =
      (specPresheaf R).map (homOfLE (inf_le_left :
        ⊤ ⊓ PrimeSpectrum.basicOpen g ≤ ⊤)).op from rfl]
  rw [unitTop_eq_ΓSpecIso_inv, Iso.hom_inv_id_apply]
  exact ht.symm

/-- A global section `q` whose restriction to the basic open `D g` vanishes is killed by a power
of `g`. -/
lemma eta_top_global_eq_zero (g q : R)
    (h : (etaO (specPresheaf R) (PrimeSpectrum.basicOpen g)).app (op ⊤) ((unitTop R).hom q) = 0) :
    ∃ k : ℕ, g ^ k * q = 0 := by
  obtain ⟨k, hk⟩ := (specPresheaf_loc_affine R (isAffineOpen_top (spec R)) g).2
    ((unitTop R).hom q) h
  refine ⟨k, ?_⟩
  apply unitTop_injective R
  rw [map_zero, show g ^ k * q = g ^ k • q from (smul_eq_mul _ _).symm, map_smul]
  exact hk

/-- Injectivity of the coaugmentation of the Čech complex, from the localized statements. -/
theorem coaugO_injective_of_localized (G : Set R) (hspan : Ideal.span G = ⊤)
    (hinj : ∀ g ∈ G, Function.Injective
      (coaug U (Qo (specPresheaf R) (PrimeSpectrum.basicOpen g))).hom)
    (hzero : ∀ g ∈ G, ∀ q : R,
      (etaO (specPresheaf R) (PrimeSpectrum.basicOpen g)).app (op ⊤) ((unitTop R).hom q) = 0 →
        ∃ k : ℕ, g ^ k * q = 0) :
    ∀ q : R, (coaugO R U).hom q = 0 → q = 0 := by
  intro q hq
  have key : ∀ g ∈ G, ∃ k : ℕ, g ^ k * q = 0 := by
    intro g hg
    refine hzero g hg q ?_
    refine hinj g hg ?_
    rw [map_zero]
    have hcoe : (coaug U (specPresheaf R)).hom ((unitTop R).hom q) = (coaugO R U).hom q := by
      rw [← unitTop_comp_coaugO R U, ModuleCat.hom_comp, LinearMap.comp_apply]
    have hnat := congrArg (fun (φ : (specPresheaf R).obj (op ⊤) ⟶
        (cechOQ R U (PrimeSpectrum.basicOpen g)).X 0) => φ.hom ((unitTop R).hom q))
      (locO_coaug_naturality R U (PrimeSpectrum.basicOpen g))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [← hnat, hcoe, hq, map_zero]
  have hmem : q ∈ (⊥ : Submodule R R) :=
    Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule R R) G hspan q (fun r => by
      obtain ⟨k, hk⟩ := key (r : R) r.2
      exact ⟨k, by simpa using hk⟩)
  simpa using hmem

/-- Surjectivity of the coaugmentation of the Čech complex onto the `0`-cycles, from the
localized statements. -/
theorem coaugO_surjective_of_localized (G : Set R) (hspan : Ideal.span G = ⊤)
    (hcoaug : ∀ g ∈ G, ∀ s : (cechOQ R U (PrimeSpectrum.basicOpen g)).X 0,
      (cechOQ R U (PrimeSpectrum.basicOpen g)).d 0 1 s = 0 →
        ∃ z : (Qo (specPresheaf R) (PrimeSpectrum.basicOpen g)).obj (op ⊤),
          (coaug U (Qo (specPresheaf R) (PrimeSpectrum.basicOpen g))).hom z = s)
    (hlift : ∀ g ∈ G, ∀ z : (Qo (specPresheaf R) (PrimeSpectrum.basicOpen g)).obj (op ⊤),
      ∃ (k : ℕ) (a : R), g ^ k • z =
        (etaO (specPresheaf R) (PrimeSpectrum.basicOpen g)).app (op ⊤) ((unitTop R).hom a))
    (hker0 : ∀ g ∈ G, ∀ t : (cechO R U).X 0,
      (locO R U (PrimeSpectrum.basicOpen g)).f 0 t = 0 → ∃ k : ℕ, g ^ k • t = 0) :
    ∀ s : (cechO R U).X 0, (cechO R U).d 0 1 s = 0 → ∃ q : R, (coaugO R U).hom q = s := by
  intro s hs
  have key : ∀ g ∈ G, ∃ (k : ℕ) (a : R), (coaugO R U).hom a = g ^ k • s := by
    intro g hg
    have hcyc : (cechOQ R U (PrimeSpectrum.basicOpen g)).d 0 1
        ((locO R U (PrimeSpectrum.basicOpen g)).f 0 s) = 0 := by
      have hcomm := (locO R U (PrimeSpectrum.basicOpen g)).comm' 0 1 (by simp)
      have hh : (locO R U (PrimeSpectrum.basicOpen g)).f 1 ((cechO R U).d 0 1 s) =
          (cechOQ R U (PrimeSpectrum.basicOpen g)).d 0 1
            ((locO R U (PrimeSpectrum.basicOpen g)).f 0 s) := by
        have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcomm) s
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this.symm
      rw [← hh, hs, map_zero]
    obtain ⟨z, hz⟩ := hcoaug g hg _ hcyc
    obtain ⟨k, a, ha⟩ := hlift g hg z
    have hnat := congrArg (fun (φ : (specPresheaf R).obj (op ⊤) ⟶
        (cechOQ R U (PrimeSpectrum.basicOpen g)).X 0) => φ.hom ((unitTop R).hom a))
      (locO_coaug_naturality R U (PrimeSpectrum.basicOpen g))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    have hcoe : (coaug U (specPresheaf R)).hom ((unitTop R).hom a) = (coaugO R U).hom a := by
      rw [← unitTop_comp_coaugO R U, ModuleCat.hom_comp, LinearMap.comp_apply]
    have hEq : (locO R U (PrimeSpectrum.basicOpen g)).f 0 (g ^ k • s) =
        (locO R U (PrimeSpectrum.basicOpen g)).f 0 ((coaugO R U).hom a) := by
      calc (locO R U (PrimeSpectrum.basicOpen g)).f 0 (g ^ k • s)
          = g ^ k • ((locO R U (PrimeSpectrum.basicOpen g)).f 0 s) := by rw [map_smul]
        _ = g ^ k • (coaug U (Qo (specPresheaf R) (PrimeSpectrum.basicOpen g))).hom z := by
              rw [hz]
        _ = (coaug U (Qo (specPresheaf R) (PrimeSpectrum.basicOpen g))).hom (g ^ k • z) := by
              rw [map_smul]
        _ = (coaug U (Qo (specPresheaf R) (PrimeSpectrum.basicOpen g))).hom
              ((etaO (specPresheaf R) (PrimeSpectrum.basicOpen g)).app (op ⊤)
                ((unitTop R).hom a)) := by rw [ha]
        _ = (locO R U (PrimeSpectrum.basicOpen g)).f 0
              ((coaug U (specPresheaf R)).hom ((unitTop R).hom a)) := hnat.symm
        _ = (locO R U (PrimeSpectrum.basicOpen g)).f 0 ((coaugO R U).hom a) := by rw [hcoe]
    have hL : (locO R U (PrimeSpectrum.basicOpen g)).f 0
        (g ^ k • s - (coaugO R U).hom a) = 0 := by
      rw [map_sub, hEq, sub_self]
    obtain ⟨l, hl⟩ := hker0 g hg _ hL
    refine ⟨l + k, g ^ l * a, ?_⟩
    have hsm : g ^ l • ((coaugO R U).hom a) = (coaugO R U).hom (g ^ l * a) := by
      rw [show g ^ l * a = g ^ l • a from (smul_eq_mul _ _).symm, map_smul]
    have h5 : g ^ l • (g ^ k • s) = g ^ (l + k) • s := by
      rw [smul_smul, ← pow_add]
    have hh := hl
    rw [smul_sub, h5, hsm] at hh
    exact (sub_eq_zero.mp hh).symm
  have hmem : s ∈ LinearMap.range (coaugO R U).hom :=
    Submodule.mem_of_span_eq_top_of_smul_pow_mem _ G hspan s (fun r => by
      obtain ⟨k, a, ha⟩ := key (r : R) r.2
      exact ⟨k, a, ha⟩)
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, hq⟩

end Work.DSF1.Cech
