/-
# Homology of the pointwise product complex

The pointwise product complex `piCplx R C` of a family `C : ι → CochainComplex (ModuleCat R) ℤ`
is (up to the canonical identification) the categorical product of the complexes `C i`, and
homology — computed as `cycles / boundaries` — commutes with products of modules.  Here we
prove the resulting statement: for every degree `n`,

  `(piCplx R C).homology n ≅ ModuleCat.of R (∀ i, (C i).homology n)`.

The proof proceeds in three steps, each of which is a separate lemma below:

* `linHom f g` is the concrete description `ker g / im f` of the homology of a short complex
  `X₁ --f--> X₂ --g--> X₃` of `R`-modules; `shortComplex_homology_iso` identifies it with
  Mathlib's categorical `ShortComplex.homology` (via `ShortComplex.moduleCatLeftHomologyData`);
* `piMap_linHom_equiv` computes `linHom` of the product of two families of linear maps as the
  product of the `linHom`'s (`ker` and `range` commute with products, and quotients of products
  by products of submodules are products of quotients);
* the degreewise identification of the differentials of `piCplx R C` with the product of the
  differentials of the `C i` finishes the argument.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.PiCplxDefs
import Submission.NK.GlobalCFTdeep.Herbrand.PiDefs

namespace NK.GlobalCFTdeep.Herbrand

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## A concrete model for the homology of a short complex of modules -/

/-- The concrete homology `ker g / im f` of a pair of composable linear maps `f` and `g`
with `g ∘ f = 0`: the quotient of the kernel of `g` by the image of `f` (which lies in the
kernel of `g`). -/
abbrev linHom {R : Type*} [Ring R] {A B D : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup D] [Module R D] (f : A →ₗ[R] B)
    (g : B →ₗ[R] D) : Type _ :=
  (LinearMap.ker g) ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype

set_option backward.isDefEq.respectTransparency false in
/-- The homology of a short complex of `R`-modules is the quotient of the kernel of its second
map by the image of its first map, the image being viewed inside the kernel. -/
lemma shortComplex_homology_iso {R : Type} [Ring R] (S : ShortComplex (ModuleCat R)) :
    Nonempty (S.homology ≅ ModuleCat.of R (linHom S.f.hom S.g.hom)) :=
  ⟨S.moduleCatLeftHomologyData.homologyIso ≪≫
    eqToIso (ShortComplex.moduleCatLeftHomologyData_H S) ≪≫
    LinearEquiv.toModuleIso (Submodule.quotEquivOfEq _ _
      (LinearMap.range_codRestrict _ _ _))⟩

/-- An isomorphism in `ModuleCat R` viewed as a linear equivalence of the underlying modules. -/
noncomputable def moduleCatIsoToLinearEquiv {R : Type} [Ring R] {M N : ModuleCat R}
    (e : M ≅ N) : (↥M) ≃ₗ[R] (↥N) :=
  LinearEquiv.ofBijective e.hom.hom
    ⟨(ModuleCat.mono_iff_injective e.hom).mp inferInstance,
      (ModuleCat.epi_iff_surjective e.hom).mp inferInstance⟩

/-! ## Two lemmas about `Submodule.pi` -/

/-- The image of a submodule of a subtype under the canonical identification `p ≃ q` of
subtypes associated to an equality `p = q` of submodules of an ambient module, in terms of
`Submodule.map` of the inclusion. -/
lemma map_ofEq_subtype {R : Type} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {p q : Submodule R M} (h : p = q) (r : Submodule R (↥p)) :
    Submodule.map (LinearEquiv.ofEq p q h : ↥p →ₗ[R] ↥q) r =
      Submodule.comap q.subtype (Submodule.map p.subtype r) := by
  ext y
  rw [Submodule.mem_map_equiv, LinearEquiv.ofEq_symm, Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hy
    exact ⟨(LinearEquiv.ofEq q p h.symm) y, hy, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    have h1 : (LinearEquiv.ofEq q p h.symm) y = x := Subtype.ext (by
      rw [LinearEquiv.coe_ofEq_apply]
      exact hxy.symm)
    rw [h1]
    exact hx

/-- The canonical identification of a product of submodules with the product of the projections:
under `Submodule.piEquiv`, the product of the `q i` corresponds to the product of the `q i`,
viewed inside `↥(Submodule.pi univ p)`. -/
lemma map_piEquiv_pi {R : Type} [Ring R] {ι : Type} {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (p q : ∀ i, Submodule R (M i)) :
    Submodule.map (Submodule.piEquiv p : (↥(Submodule.pi Set.univ p)) →ₗ[R] ((i:ι) → ↥(p i)))
      ((Submodule.pi Set.univ q).comap (Submodule.pi Set.univ p).subtype) =
    Submodule.pi Set.univ (fun i => (q i).comap (p i).subtype) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx1, hx2, rfl⟩ := hy
    intro i
    exact hx1 i
  · intro hy
    refine ⟨⟨fun i => (y i : M i), fun i _ => (y i).2⟩, ?_, ?_⟩
    · intro i
      exact hy i
    · ext i
      rfl

/-! ## `linHom` of a product is the product of the `linHom`s -/

set_option backward.isDefEq.respectTransparency false in
/-- The concrete homology of the product of two families of linear maps is the product of the
concrete homologies: kernels and ranges commute with products, and a quotient of a product by a
product of submodules is the product of the quotients. -/
lemma piMap_linHom_equiv {R : Type} [Ring R] {ι : Type} {A B D : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
    [∀ i, AddCommGroup (D i)] [∀ i, Module R (D i)]
    (f : ∀ i, A i →ₗ[R] B i) (g : ∀ i, B i →ₗ[R] D i) (h : ∀ i, g i ∘ₗ f i = 0) :
    Nonempty (linHom (LinearMap.piMap f) (LinearMap.piMap g) ≃ₗ[R]
      (∀ i, linHom (f i) (g i))) := by
  have hle : LinearMap.range (LinearMap.piMap f) ≤ LinearMap.ker (LinearMap.piMap g) :=
    LinearMap.range_le_ker_iff.mpr (LinearMap.piMap_comp_eq_zero f g h)
  have hA : Submodule.map (LinearEquiv.ofEq _ _ (LinearMap.ker_piMap g) :
        ↥(LinearMap.ker (LinearMap.piMap g)) →ₗ[R]
          ↥(Submodule.pi Set.univ (fun i => (LinearMap.ker (g i)))))
      ((LinearMap.range (LinearMap.piMap f)).comap (LinearMap.ker (LinearMap.piMap g)).subtype) =
      (LinearMap.range (LinearMap.piMap f)).comap
        (Submodule.pi Set.univ (fun i => (LinearMap.ker (g i)))).subtype := by
    have h1 := map_ofEq_subtype (p := LinearMap.ker (LinearMap.piMap g))
      (q := Submodule.pi Set.univ (fun i => (LinearMap.ker (g i)))) (LinearMap.ker_piMap g)
      ((LinearMap.range (LinearMap.piMap f)).comap (LinearMap.ker (LinearMap.piMap g)).subtype)
    rw [h1, Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  have hB : Submodule.map (Submodule.piEquiv (fun i => (LinearMap.ker (g i))) :
        ↥(Submodule.pi Set.univ (fun i => (LinearMap.ker (g i)))) →ₗ[R]
          ((i:ι) → ↥(LinearMap.ker (g i))))
      ((LinearMap.range (LinearMap.piMap f)).comap
        (Submodule.pi Set.univ (fun i => (LinearMap.ker (g i)))).subtype) =
      Submodule.pi Set.univ (fun i => (LinearMap.range (f i)).comap (LinearMap.ker (g i)).subtype) := by
    rw [LinearMap.range_piMap]
    exact map_piEquiv_pi (fun i => (LinearMap.ker (g i))) (fun i => (LinearMap.range (f i)))
  exact ⟨(Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (LinearMap.ker_piMap g)) hA).trans
    ((Submodule.Quotient.equiv _ _ (Submodule.piEquiv (fun i => (LinearMap.ker (g i)))) hB).trans
      (Submodule.quotientPiEquiv
        (fun i => (LinearMap.range (f i)).comap (LinearMap.ker (g i)).subtype)))⟩

/-! ## The main statement -/

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary form of `piCplx_homology_iso`, with the def-unfolding transparency of the
elaborator turned off (some of the identifications of the differentials of `piCplx R C` with
the products of the differentials of the `C i` are `rfl` only at that transparency). -/
theorem piCplx_homology_iso_aux {R : Type} [Ring R] {ι : Type}
    (C : ι → CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    Nonempty ((piCplx R C).homology n ≅ ModuleCat.of R ((i : ι) → ↥((C i).homology n))) := by
  have hfg : ∀ i, ((C i).sc n).g.hom ∘ₗ ((C i).sc n).f.hom = 0 := fun i => by
    have h := congrArg ModuleCat.Hom.hom (ShortComplex.zero ((C i).sc n))
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact h
  have e1 : (piCplx R C).homology n ≅
      ModuleCat.of R (linHom ((piCplx R C).sc n).f.hom ((piCplx R C).sc n).g.hom) :=
    (shortComplex_homology_iso ((piCplx R C).sc n)).some
  have e2 : ModuleCat.of R (linHom (LinearMap.piMap (fun i => ((C i).sc n).f.hom))
        (LinearMap.piMap (fun i => ((C i).sc n).g.hom))) ≅
      ModuleCat.of R (∀ i, linHom ((C i).sc n).f.hom ((C i).sc n).g.hom) :=
    LinearEquiv.toModuleIso (piMap_linHom_equiv (fun i => ((C i).sc n).f.hom)
      (fun i => ((C i).sc n).g.hom) hfg).some
  have e3 : ModuleCat.of R (∀ i, linHom ((C i).sc n).f.hom ((C i).sc n).g.hom) ≅
      ModuleCat.of R ((i : ι) → ↥((C i).homology n)) :=
    LinearEquiv.toModuleIso (LinearEquiv.piCongrRight fun i =>
      (moduleCatIsoToLinearEquiv (shortComplex_homology_iso ((C i).sc n)).some).symm)
  exact ⟨e1 ≪≫ e2 ≪≫ e3⟩

/-- The homology of the pointwise product complex is the product of the homologies. -/
theorem piCplx_homology_iso {R : Type} [Ring R] {ι : Type}
    (C : ι → CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    Nonempty ((piCplx R C).homology n ≅ ModuleCat.of R ((i : ι) → ↥((C i).homology n))) :=
  piCplx_homology_iso_aux C n

end

end NK.GlobalCFTdeep.Herbrand
