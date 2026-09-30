import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.HALG.bocksteinTwo
import Submission.Work.Pi6.EMZ.BocksteinCore
import Submission.Work.Pi6.BOCK.CoeffIso
import Submission.Work.Pi6.BOCK.coeffSESShortExact
import Submission.Work.SSS.ExpTensLES
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# AREA SQASM — the three coefficient-change facts used by `Work.Pi6.sqCyclic`

The SQASM argument needs exactly three consequences of the mod-2 coefficient change `ℤ → 𝔽₂`:

* `isZero_modTwo_of_subsingleton`: if `H_{n+1}(X;ℤ)/2H_{n+1}(X;ℤ)` and `H_n(X;ℤ)[2]` are trivial,
  then `H_{n+1}(X;𝔽₂) = 0`;
* `exists_ne_zero_modTwo_of_not_subsingleton_cok`: if `H_{n+1}(X;ℤ)/2H_{n+1}(X;ℤ) ≠ 0`, then
  `H_{n+1}(X;𝔽₂) ≠ 0`;
* `isIso_modTwo_of_isIso_int`: a map which is an isomorphism on `H_n(−;ℤ)` and `H_{n+1}(−;ℤ)` is an
  isomorphism on `H_{n+1}(−;𝔽₂)` (the five statement for the map of Bockstein sequences).

The first two are read off from the three-term Bockstein short exact sequence
`Work.Pi6.HALG.bocksteinAux` (area HALG).  The third is the *five statement* for the map of short
exact sequences of chain complexes `Work.Pi6.EMZ.bockSES 2 X → Work.Pi6.EMZ.bockSES 2 Y` induced by
`f`, using `HomologySequence.isIso_homologyMap_τ₃`: the outer terms are the integral chain
complexes, so the hypothesis is exactly the integral isomorphism supplied by the range Whitehead
statement, and the conclusion concerns the mod-2 term.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.SQASM

noncomputable section

/-! ## 1. The three-term Bockstein short exact sequence -/

/-- **`M/2M = 0` if multiplication by `2` is onto.** -/
theorem subsingleton_twoCok_of_surjective (M : ModuleCat ℤ)
    (h : Function.Surjective (fun x : ↥M => (2 : ℤ) • x)) :
    Subsingleton ↥(Work.Pi6.HALG.twoCok M) := by
  have hh : LinearMap.range (Work.Pi6.HALG.mulTwo M).hom = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨x, hx⟩ := h y
    exact ⟨x, by rw [Work.Pi6.HALG.mulTwo_apply]; exact hx⟩
  show Subsingleton (↥M ⧸ LinearMap.range (Work.Pi6.HALG.mulTwo M).hom)
  rw [hh]
  exact Submodule.Quotient.subsingleton_iff.mpr rfl

/-- **The `2`-torsion of a trivial group is trivial.** -/
theorem subsingleton_twoKer_of_subsingleton (M : ModuleCat ℤ) [Subsingleton ↥M] :
    Subsingleton ↥(Work.Pi6.HALG.twoKer M) := by
  show Subsingleton ↥(LinearMap.ker (Work.Pi6.HALG.mulTwo M).hom)
  exact ⟨fun a b => Subtype.ext (Subsingleton.elim (a : ↥M) (b : ↥M))⟩

/-- An additive group which is not a subsingleton has a non-zero element. -/
theorem exists_ne_zero_of_not_subsingleton {A : Type*} [AddCommGroup A] (h : ¬ Subsingleton A) :
    ∃ x : A, x ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h ⟨fun a b => by rw [hc a, hc b]⟩

/-- **If `H_{n+1}(X;ℤ)/2H_{n+1}(X;ℤ)` and `H_n(X;ℤ)[2]` are trivial, then `H_{n+1}(X;𝔽₂) = 0`.** -/
theorem isZero_modTwo_of_subsingleton (X : Type) [TopologicalSpace X] (n : ℕ)
    (h1 : Subsingleton ↥(Work.Pi6.HALG.twoCok (Work.Pi6.HR ℤ X (n + 1))))
    (h2 : Subsingleton ↥(Work.Pi6.HALG.twoKer (Work.Pi6.HR ℤ X n))) :
    CategoryTheory.Limits.IsZero (Work.Pi6.HR (ZMod 2) X (n + 1)) := by
  haveI := h1
  haveI := h2
  obtain ⟨i, p, hi, hex, _hp⟩ := Work.Pi6.HALG.bocksteinAux X n
  have key : ∀ y : ↥(Work.Pi6.HR (ZMod 2) X (n + 1)), y = 0 := by
    intro y
    have hpy : p y = 0 := Subsingleton.elim _ _
    obtain ⟨x, hx⟩ := Set.mem_range.mp ((hex y).mp hpy)
    have hx0 : x = 0 := Subsingleton.elim x 0
    calc y = i x := hx.symm
      _ = i 0 := congrArg i hx0
      _ = 0 := map_zero i
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => by rw [key a, key b]⟩

/-- **If `H_{n+1}(X;ℤ)/2H_{n+1}(X;ℤ) ≠ 0`, then `H_{n+1}(X;𝔽₂) ≠ 0`.** -/
theorem exists_ne_zero_modTwo_of_not_subsingleton_cok (X : Type) [TopologicalSpace X] (n : ℕ)
    (h : ¬ Subsingleton ↥(Work.Pi6.HALG.twoCok (Work.Pi6.HR ℤ X (n + 1)))) :
    ∃ c : Work.Pi6.HR (ZMod 2) X (n + 1), c ≠ 0 := by
  obtain ⟨i, _p, hi, _hex, _hp⟩ := Work.Pi6.HALG.bocksteinAux X n
  obtain ⟨x, hx⟩ := exists_ne_zero_of_not_subsingleton h
  exact ⟨i x, fun h0 => hx (hi (h0.trans (map_zero i).symm))⟩

/-! ## 2. The five statement for the Bockstein sequence -/

section Five

/-- **Naturality of the unit identification `expTens K ℤ ≅ K`** with respect to a chain map. -/
theorem expTensUnitIso_naturality_mapHom (K K' : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ K') :
    Work.Pi6.BOCK.expTensMapHom K K' φ (𝟙_ (ModuleCat ℤ)) ≫ (Work.SSS.expTensUnitIso K').hom =
      (Work.SSS.expTensUnitIso K).hom ≫ φ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, Work.Pi6.BOCK.expTensMapHom_f]
  exact MonoidalCategory.rightUnitor_naturality (φ.f n)

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Naturality of the integral identification** `H_n(C_*(X;ℤ) ⊗ ℤ) ≅ H_n(X;ℤ)`. -/
theorem expTensUnitHomologyIso_natural (f : C(X, Y)) (k : ℕ) :
    HomologicalComplex.homologyMap
        (Work.Pi6.BOCK.expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y)
          (Work.Pi6.BOCK.chMapZ f) (𝟙_ (ModuleCat ℤ))) k ≫
        (Work.Pi6.EMZ.expTensUnitHomologyIso Y k).hom =
      (Work.Pi6.EMZ.expTensUnitHomologyIso X k).hom ≫ Work.Pi6.hmap ℤ f k := by
  have h := congrArg (fun t => HomologicalComplex.homologyMap t k)
    (expTensUnitIso_naturality_mapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y)
      (Work.Pi6.BOCK.chMapZ f))
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  exact h

/-- **A map which is an isomorphism on `H_n(−;ℤ)` and `H_{n+1}(−;ℤ)` is an isomorphism on
`H_{n+1}(−;𝔽₂)`** (the five statement for the Bockstein sequences of `X` and `Y`). -/
theorem isIso_modTwo_of_isIso_int (f : C(X, Y)) (n : ℕ)
    (h1 : IsIso (Work.Pi6.hmap ℤ f n)) (h2 : IsIso (Work.Pi6.hmap ℤ f (n + 1))) :
    IsIso (Work.Pi6.hmap (ZMod 2) f (n + 1)) := by
  have hp2 : Nat.Prime 2 := Nat.prime_two
  have hcoeff : (Work.Pi6.EMZ.coeffSES 2).ShortExact :=
    Work.Pi6.BOCK.coeffSESShortExact 2 hp2
  have hSX : (Work.Pi6.EMZ.bockSES 2 X).ShortExact :=
    Work.Pi6.EMZ.bockSES_shortExact 2 (by norm_num) X hcoeff
  have hSY : (Work.Pi6.EMZ.bockSES 2 Y).ShortExact :=
    Work.Pi6.EMZ.bockSES_shortExact 2 (by norm_num) Y hcoeff
  -- the morphism of short complexes induced by `f`
  let Φ : Work.Pi6.EMZ.bockSES 2 X ⟶ Work.Pi6.EMZ.bockSES 2 Y :=
    ShortComplex.homMk
      (Work.Pi6.BOCK.expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y)
        (Work.Pi6.BOCK.chMapZ f) (𝟙_ (ModuleCat ℤ)))
      (Work.Pi6.BOCK.expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y)
        (Work.Pi6.BOCK.chMapZ f) (𝟙_ (ModuleCat ℤ)))
      (Work.Pi6.BOCK.expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y)
        (Work.Pi6.BOCK.chMapZ f) (Work.Pi6.EMZ.Mp 2))
      (Work.Pi6.BOCK.expTensMapHom_expTensHom _ _ _ (Work.Pi6.EMZ.mulP 2))
      (Work.Pi6.BOCK.expTensMapHom_expTensHom _ _ _ (Work.Pi6.EMZ.redP 2))
  -- naturality of the two identifications, stated with `Φ`
  have hnat1 (k : ℕ) : HomologicalComplex.homologyMap Φ.τ₁ k ≫
      (Work.Pi6.EMZ.expTensUnitHomologyIso Y k).hom =
      (Work.Pi6.EMZ.expTensUnitHomologyIso X k).hom ≫ Work.Pi6.hmap ℤ f k :=
    expTensUnitHomologyIso_natural f k
  set G : (Work.Pi6.BOCK.Fp 2).obj (Work.Pi6.HR (ZMod 2) X (n + 1)) ⟶
      (Work.Pi6.BOCK.Fp 2).obj (Work.Pi6.HR (ZMod 2) Y (n + 1)) :=
    (Work.Pi6.BOCK.Fp 2).map (HomologicalComplex.homologyMap
      (Work.Pi6.BOCK.chMapK 2 f) (n + 1)) with hG
  have hnat3 : HomologicalComplex.homologyMap Φ.τ₃ (n + 1) ≫
      (Work.Pi6.BOCK.eCIso' 2 hp2 Y (n + 1)).hom =
      (Work.Pi6.BOCK.eCIso' 2 hp2 X (n + 1)).hom ≫ G := by
    rw [hG]
    exact Work.Pi6.BOCK.eCIso_natural_mor 2 hp2 f (n + 1)
  -- the isomorphisms on the first two terms
  have hisoZ (k : ℕ) (hk : IsIso (Work.Pi6.hmap ℤ f k)) :
      IsIso (HomologicalComplex.homologyMap Φ.τ₁ k) := by
    have hcomp : IsIso (HomologicalComplex.homologyMap Φ.τ₁ k ≫
        (Work.Pi6.EMZ.expTensUnitHomologyIso Y k).hom) := by
      rw [hnat1 k]
      haveI := hk
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Work.Pi6.EMZ.expTensUnitHomologyIso Y k).hom
  -- the five statement
  have hres : IsIso (HomologicalComplex.homologyMap Φ.τ₃ (n + 1)) := by
    refine HomologySequence.isIso_homologyMap_τ₃ Φ hSX hSY (n + 1) ?_ ?_ ?_ ?_
    · haveI := hisoZ (n + 1) h2
      infer_instance
    · exact hisoZ (n + 1) h2
    · intro j hj
      have hj' : j + 1 = n + 1 := (ComplexShape.down_Rel ℕ (n + 1) j).mp hj
      have hjn : j = n := by omega
      rw [hjn]
      exact hisoZ n h1
    · intro j hj
      have hj' : j + 1 = n + 1 := (ComplexShape.down_Rel ℕ (n + 1) j).mp hj
      have hjn : j = n := by omega
      rw [hjn]
      haveI : IsIso (HomologicalComplex.homologyMap Φ.τ₂ n) := hisoZ n h1
      infer_instance
  -- transfer along the mod-2 identification
  have hisoK : IsIso G := by
    haveI : IsIso (HomologicalComplex.homologyMap Φ.τ₃ (n + 1)) := hres
    have h2 : IsIso (HomologicalComplex.homologyMap Φ.τ₃ (n + 1) ≫
        (Work.Pi6.BOCK.eCIso' 2 hp2 Y (n + 1)).hom) := IsIso.comp_isIso
    rw [hnat3] at h2
    exact IsIso.of_isIso_comp_left (Work.Pi6.BOCK.eCIso' 2 hp2 X (n + 1)).hom G
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (ConcreteCategory.isIso_iff_bijective G).mp hisoK

end Five

end

end Work.Pi6.SQASM
