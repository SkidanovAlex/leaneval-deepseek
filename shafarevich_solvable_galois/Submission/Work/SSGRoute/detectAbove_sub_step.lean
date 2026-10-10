import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.E7bZ8Step2Aux2
import Submission.Work.SSGRoute.detectAbove_kummer
import Submission.Work.SSGRoute.levelPair_comp_extHMap
import Submission.Work.SSGRoute.localUnits_infl_injective
import Submission.Work.SSGRoute.local_pTorsion_card

/-!
# Z6 (`Work.SSGRoute.detectAbove_sub_step`), clause (i), sub-`𝔽_p` orientation

The `Ext`-level plumbing of the dévissage step of the E7b design (`requests/ssg6/DESIGN_E7B.md`,
node Z6) together with the statement of the step.

The remaining inputs are the sibling nodes `Work.SSGRoute.levelPair_comp_extHMap` (Z1) and
`Work.SSGRoute.localUnits_infl_injective` (Z2), together with the local Kummer input
(`Work.SSGRoute.dass_local_kummer_dies`, provided by the module `detectAbove_kummer` of this
directory).
-/

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

/-- temporary inlined copy of `Work.SSGRoute.levelPair_coeff_naturality` -/
lemma dass_levelPair_coeff_naturality {H G : Type} [Group H] [Group G] (f : H →* G)
    {M M' : Rep.{0} Coeff G} (π : M ⟶ M') {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (y : Abelian.Ext.{0} M' A r)
    (h : extH (Rep.res f M) s) :
    levelPair f ι ((Abelian.Ext.mk₀ π).comp y (zero_add r)) h =
      levelPair f ι y (h.comp (Abelian.Ext.mk₀ (Rep.resMap f π)) (add_zero s)) := by
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero]

lemma dass_resMap_comp {G H : Type} [Group G] [Group H] (f : H →* G) {M N K : Rep Coeff G}
    (p : M ⟶ N) (q : N ⟶ K) : Rep.resMap f (p ≫ q) = Rep.resMap f p ≫ Rep.resMap f q := by
  rw [show Rep.resMap f (p ≫ q) = (Rep.resFunctor f).map (p ≫ q) from rfl,
      show Rep.resMap f p = (Rep.resFunctor f).map p from rfl,
      show Rep.resMap f q = (Rep.resFunctor f).map q from rfl, Functor.map_comp]

lemma dass_extRes_comp {G₁ G D : Type} [Group G₁] [Group G] [Group D] (f : G₁ →* D) (g : G →* G₁)
    {X Y : Rep Coeff D} (n : ℕ) (x : Abelian.Ext X Y n) :
    extRes g (extRes f x) = extRes (f.comp g) x := by
  rw [extRes, extRes, extRes]
  rw [Work.SSGRoute.ext_mapExactFunctor_comp_functor_aux (C := Rep Coeff D) (D := Rep Coeff G₁)
    (E := Rep Coeff G) (Rep.resFunctor f) (Rep.resFunctor g) n X Y x]
  rfl

/-- **(D)** `extHMap` as a post-composition. -/
lemma dass_extHMap_eq_comp {G₁ G : Type} [Group G₁] [Group G]
    (g : G →* G₁) {B₁ : Rep Coeff G₁} {B : Rep Coeff G}
    (ι : Rep.res g B₁ ⟶ B) (s : ℕ) (x : extH B₁ s) :
    extHMap g ι x = (extHMap g (𝟙 (Rep.res g B₁)) x).comp
      (Abelian.Ext.mk₀ ι) (add_zero s) := by
  simp only [extHMap, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.comp_assoc, Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_mk₀_id]

/-- **(E')** `extHMap` commutes with post-composition by a coefficient morphism. -/
lemma dass_extHMap_comp_mk₀ {G₁ G : Type} [Group G₁] [Group G]
    (g : G →* G₁) {A A' : Rep Coeff G₁} {B : Rep Coeff G}
    (ψ : Rep.res g A ⟶ B) (φ : A' ⟶ A) (s : ℕ) (x : extH A' s) :
    extHMap g ψ (x.comp (Abelian.Ext.mk₀ φ) (add_zero s)) =
      extHMap g (Rep.resMap g φ ≫ ψ) x := by
  simp only [extHMap, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc, Abelian.Ext.mk₀_comp_mk₀]

noncomputable def dassZLvl {D H : Type} [Group D] [Group H] (f : H →* D)
    {S : ShortComplex (Rep Coeff D)} {P A : Rep Coeff D} (e : S.X₁ ≅ P) (z : P ⟶ A)
    {B : Rep Coeff H} (ι : Rep.res f A ⟶ B) : Rep.res f S.X₁ ⟶ B :=
  Rep.resMap f e.hom ≫ Rep.resMap f z ≫ ι

noncomputable def dassDelta {D H : Type} [Group D] [Group H] (f : H →* D)
    {S : ShortComplex (Rep Coeff D)} (hS : S.ShortExact) (h'' : extH (Rep.res f S.X₃) 1) :
    extH (Rep.res f S.X₁) 2 :=
  h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl)

noncomputable def dassW {D : Type} [Group D] {S : ShortComplex (Rep Coeff D)} (hS : S.ShortExact)
    {P A : Rep Coeff D} (e : S.X₁ ≅ P) (z : P ⟶ A) : Abelian.Ext S.X₃ A 1 :=
  hS.extClass.comp (Abelian.Ext.mk₀ (e.hom ≫ z)) (add_zero 1)

lemma dass_levelPair_W {D H : Type} [Group D] [Group H] (f : H →* D)
    {S : ShortComplex (Rep Coeff D)} (hS : S.ShortExact) {P A : Rep Coeff D}
    (e : S.X₁ ≅ P) (z : P ⟶ A) {B : Rep Coeff H} (ι : Rep.res f A ⟶ B)
    (h'' : extH (Rep.res f S.X₃) 1) :
    levelPair f ι (dassW hS e z) h'' =
      (dassDelta f hS h'').comp (Abelian.Ext.mk₀ (dassZLvl f e z ι)) (add_zero 2) := by
  show levelPair f ι (hS.extClass.comp (Abelian.Ext.mk₀ (e.hom ≫ z)) (add_zero 1)) h'' =
    (h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl)).comp
      (Abelian.Ext.mk₀ (Rep.resMap f e.hom ≫ Rep.resMap f z ≫ ι)) (add_zero 2)
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc]
  rw [dass_resMap_comp f e.hom z, Abelian.Ext.mk₀_comp_mk₀]
  simp only [Category.assoc]

lemma dass_delta_eq_zero_iff {D H : Type} [Group D] [Group H] (f : H →* D)
    {S : ShortComplex (Rep Coeff D)} (hS : S.ShortExact)
    (h'' : extH (Rep.res f S.X₃) 1) (h : dassDelta f hS h'' = 0) :
    ∃ h₂ : extH (Rep.res f S.X₂) 1,
      h₂.comp (Abelian.Ext.mk₀ (Rep.resMap f S.g)) (add_zero 1) = h'' := by
  have h' : h''.comp (extRes f hS.extClass) (show (1:ℕ)+1 = 2 from rfl) = 0 := h
  refine Abelian.Ext.covariant_sequence_exact₃ (unitRep H)
    (hS.map_of_exact (Rep.resFunctor f)) h'' (show (1:ℕ)+1 = 2 from rfl) ?_
  rw [← Abelian.Ext.mapExactFunctor_extClass]
  exact h'

lemma dass_levelPair_kills {D H : Type} [Group D] [Group H] (f : H →* D)
    {S : ShortComplex (Rep Coeff D)} (hS : S.ShortExact) {A : Rep Coeff D} {B : Rep Coeff H}
    (ι : Rep.res f A ⟶ B) {y : Abelian.Ext S.X₂ A 1} {y'' : Abelian.Ext S.X₃ A 1}
    (hy : (Abelian.Ext.mk₀ S.g).comp y'' (zero_add 1) = y)
    (hvan : ∀ h₂ : extH (Rep.res f S.X₂) 1, levelPair f ι y h₂ = 0)
    (h : extH (Rep.res f S.X₂) 1) :
    levelPair f ι y'' (h.comp (Abelian.Ext.mk₀ (Rep.resMap f S.g)) (add_zero 1)) = 0 := by
  have key := dass_levelPair_coeff_naturality f ι (π := S.g) (r := 1) (s := 1) y'' h
  rw [← key, hy]
  exact hvan h

lemma dass_delta_naturality {G₁ G D : Type} [Group G₁] [Group G] [Group D]
    (f₁ : G₁ →* D) (g : G →* G₁) {S : ShortComplex (Rep Coeff D)} (hS : S.ShortExact)
    (h'' : extH (Rep.res f₁ S.X₃) 1) :
    (extHMap g (𝟙 (Rep.res g (Rep.res f₁ S.X₃))) h'').comp (extRes (f₁.comp g) hS.extClass)
        (show (1:ℕ) + 1 = 2 from rfl)
      = extHMap g (𝟙 (Rep.res g (Rep.res f₁ S.X₁)))
          (h''.comp (extRes f₁ hS.extClass) (show (1:ℕ) + 1 = 2 from rfl)) := by
  rw [dass_extHMap_eq_comp g (𝟙 (Rep.res g (Rep.res f₁ S.X₁)))]
  simp only [extHMap, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc, Abelian.Ext.comp_mk₀_id, Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.mk₀_id_comp]
  rw [Work.SSGRoute.ext_mapExactFunctor_comp_functor_aux (C := Rep Coeff D) (D := Rep Coeff G₁)
    (E := Rep Coeff G) (Rep.resFunctor f₁) (Rep.resFunctor g) 1 S.X₃ S.X₁ hS.extClass]
  rfl

/-! ## (A) proportionality -/

lemma dass_prop_smul {V T : Type} [AddCommGroup V] [AddCommGroup T] {p : ℕ} [Fact p.Prime]
    (hT : ∀ t : T, p • t = 0 → t ≠ 0 → ∀ t' : T, p • t' = 0 → ∃ m : ℤ, t' = m • t)
    (f g : V →+ T) (hf : ∀ v : V, p • f v = 0) (hg : ∀ v : V, p • g v = 0)
    (h : ∀ v : V, g v = 0 → f v = 0) :
    ∃ m : ℤ, ∀ v : V, f v = m • g v := by
  by_cases hg0 : ∀ v, g v = 0
  · refine ⟨0, fun v => ?_⟩
    rw [h v (hg0 v), zero_smul]
  · push_neg at hg0
    obtain ⟨v₀, hv₀⟩ := hg0
    obtain ⟨m, hm⟩ := hT (g v₀) (hg v₀) hv₀ (f v₀) (hf v₀)
    refine ⟨m, fun v => ?_⟩
    obtain ⟨k, hk⟩ := hT (g v₀) (hg v₀) hv₀ (g v) (hg v)
    have hfk : f (v - k • v₀) = 0 := h _ (by rw [map_sub, map_zsmul, hk, sub_self])
    have h1 : f v = k • f v₀ := by
      have h2 : f (v - k • v₀) = f v - k • f v₀ := by rw [map_sub, map_zsmul]
      rw [h2] at hfk
      exact sub_eq_zero.mp hfk
    rw [h1, hm, hk, smul_comm]

/-! ## (B) the p-torsion of a monogenic group is generated by each non-zero element -/

lemma dass_pTorsion_gen {A : Type} [AddCommGroup A] (p : ℕ) [Fact p.Prime]
    (hA : (∀ x : A, p • x = 0 → x = 0) ∨
      ∃ x : A, p • x = 0 ∧ ∀ y : A, p • y = 0 → ∃ m : ℤ, y = m • x) :
    ∀ t : A, p • t = 0 → t ≠ 0 → ∀ t' : A, p • t' = 0 → ∃ m : ℤ, t' = m • t := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rcases hA with h0 | ⟨x, hx, hgen⟩
  · exact fun t ht htne => absurd (h0 t ht) htne
  · by_cases hx0 : x = 0
    · intro t ht htne
      obtain ⟨m, hm⟩ := hgen t ht
      rw [hx0, smul_zero] at hm
      exact absurd hm htne
    · have hxord : addOrderOf x = p := addOrderOf_eq_prime hx hx0
      intro t ht htne t' ht'
      obtain ⟨m₀, hm₀⟩ := hgen t ht
      obtain ⟨m₁, hm₁⟩ := hgen t' ht'
      have hne : ((m₀ : ℤ) : ZMod p) ≠ 0 := by
        intro hz
        have hd : (p : ℤ) ∣ m₀ := (ZMod.intCast_zmod_eq_zero_iff_dvd m₀ p).mp hz
        apply htne
        obtain ⟨j, hj⟩ := hd
        rw [hm₀, hj, mul_comm (p : ℤ) j, mul_zsmul, natCast_zsmul, hx, smul_zero]
      set M : ℤ := (((m₁ : ZMod p) * (((m₀ : ℤ) : ZMod p))⁻¹).val : ℤ) with hM
      refine ⟨M, ?_⟩
      have hcast : ((M : ZMod p)) = (m₁ : ZMod p) * (((m₀ : ℤ) : ZMod p))⁻¹ := by
        rw [hM, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
      have hmul : (M : ZMod p) * ((m₀ : ℤ) : ZMod p) = (m₁ : ZMod p) := by
        rw [hcast, mul_assoc, inv_mul_cancel₀ hne, mul_one]
      have hdvd : (p : ℤ) ∣ (m₁ - M * m₀) := by
        have hz : (((m₁ - M * m₀ : ℤ)) : ZMod p) = 0 := by
          rw [Int.cast_sub, Int.cast_mul, hmul, sub_self]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
      have heq : m₁ • x = (M * m₀) • x := by
        have h0 : (m₁ - M * m₀) • x = 0 :=
          addOrderOf_dvd_iff_zsmul_eq_zero.mp (by rw [hxord]; exact hdvd)
        rw [show m₁ = M * m₀ + (m₁ - M * m₀) from by ring, add_zsmul, h0, add_zero]
      rw [hm₁, hm₀, ← mul_zsmul]
      exact heq

/-! ## (K) the Kummer step -/

open NK.GlobalCFT in
theorem dass_kummer_step (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    (z : Rep.trivial Coeff (decompK (k := k) w) (ZMod p) ⟶ localUnitsK (k := k) w) (hz : z ≠ 0)
    (S : ShortComplex (Rep Coeff (decompK (k := k) w))) (hS : S.ShortExact)
    (e : S.X₁ ≅ Rep.trivial Coeff (decompK (k := k) w) (ZMod p))
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (h'' : extH (Rep.res f S.X₃) 1)
    (hx : (h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl)).comp
        (Abelian.Ext.mk₀ (Rep.resMap f e.hom ≫ Rep.resMap f z ≫ ι)) (add_zero 2) = 0) :
    ∃ (L' : Type) (hF : Field L') (hN : NumberField L') (hA : Algebra k L') (hAL : Algebra L L')
      (hST : IsScalarTower k L L') (hFD : FiniteDimensional k L') (hGal : IsGalois k L')
      (w'' : NK.GlobalCFT.Place L') (hw'' : NK.GlobalCFT.Place.LiesOver w'' w')
      (g : MulAction.stabilizer (L' ≃ₐ[k] L') w'' →* MulAction.stabilizer (L ≃ₐ[k] L) w')
      (hg : ∀ σ, ((g σ : MulAction.stabilizer (L ≃ₐ[k] L) w') : L ≃ₐ[k] L) =
        galRes k L L' (σ : L' ≃ₐ[k] L')),
      (extHMap g (𝟙 (Rep.res g (Rep.res f S.X₃))) h'').comp (extRes (f.comp g) hS.extClass)
        (show (1:ℕ) + 1 = 2 from rfl) = 0 := by
  classical
  have hzl_ne : (Rep.resMap f z ≫ ι : Rep.trivial Coeff (decompK (k := k) w') (ZMod p) ⟶
      NK.HassePrinciple.localUnitsRep k L w') ≠ 0 := by
    obtain ⟨x, hx0⟩ : ∃ x : ZMod p,
        (z.hom x : ↑(Rep.res f (localUnitsK (k := k) w))) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hz
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro y
      simpa using hcon y
    set u : (NK.GlobalCFT.Place.localField K w)ˣ :=
      Additive.toMul (z.hom x : ↑(Rep.res f (localUnitsK (k := k) w))) with hu
    have hux : (Additive.ofMul u : ↑(Rep.res f (localUnitsK (k := k) w))) = z.hom x := by
      rw [hu]
      exact ofMul_toMul _
    have hune : u ≠ 1 := by
      intro h1
      apply hx0
      rw [← hux, h1]
      rfl
    intro hz0
    have h0 : (Rep.Hom.hom (Rep.resMap f z ≫ ι)) x = 0 := by
      have h := congrArg (fun φ => Rep.Hom.hom φ x) hz0
      exact h
    have h2 : (Rep.Hom.hom (Rep.resMap f z ≫ ι)) x =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u) := by
      have h1 : ι.hom (Additive.ofMul u) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u) := hι u
      rw [hux] at h1
      rw [show (Rep.Hom.hom (Rep.resMap f z ≫ ι)) x = ι.hom (z.hom x) from rfl]
      exact h1
    rw [h2] at h0
    have h3 : Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' 1) := by
      rw [h0, map_one]
      rfl
    exact hune (NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_injective hw'
      (by simpa using Additive.ofMul.injective h3))
  have hxh0 : (((h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl)).comp
        (Abelian.Ext.mk₀ (Rep.resMap f e.hom)) (add_zero 2)) :
        extH (Rep.trivial Coeff (decompK (k := k) w') (ZMod p)) 2).comp
      (Abelian.Ext.mk₀ (Rep.resMap f z ≫ ι)) (add_zero 2) = 0 := by
    have hx' := hx
    rw [show (Rep.resMap f e.hom ≫ Rep.resMap f z ≫ ι : Rep.res f S.X₁ ⟶
        NK.HassePrinciple.localUnitsRep k L w')
      = (Rep.resMap f e.hom ≫ (Rep.resMap f z ≫ ι)) from rfl] at hx'
    rw [← Abelian.Ext.mk₀_comp_mk₀] at hx'
    rw [← Abelian.Ext.comp_assoc_of_third_deg_zero] at hx'
    exact hx'
  obtain ⟨L', hF, hN, hA, hAL, hST, hFD, hGal, w'', hw'', g, hg, hz4⟩ :=
    Work.SSGRoute.dass_local_kummer_dies p k L w' (Rep.resMap f z ≫ ι) hzl_ne _ hxh0
  refine ⟨L', hF, hN, hA, hAL, hST, hFD, hGal, w'', hw'', g, hg, ?_⟩
  -- Z4's conclusion, in the form of the identity coefficient (they are definitionally equal)
  have h3 : extHMap g (𝟙 (Rep.res g (Rep.res f (Rep.trivial Coeff (decompK (k := k) w)
      (ZMod p)))))
      ((((h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl)).comp
        (Abelian.Ext.mk₀ (Rep.resMap f e.hom)) (add_zero 2)) :
        extH (Rep.trivial Coeff (decompK (k := k) w') (ZMod p)) 2)) = 0 := hz4
  -- (E'): this class is the inflation of the connecting class
  have h4 : extHMap g (Rep.resMap g (Rep.resMap f e.hom))
      (h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl)) = 0 := by
    have hE := dass_extHMap_comp_mk₀ g (𝟙 (Rep.res g (Rep.res f (Rep.trivial Coeff
      (decompK (k := k) w) (ZMod p))))) (Rep.resMap f e.hom) 2
      (h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl))
    rw [show (Rep.resMap g (Rep.resMap f e.hom) ≫ 𝟙 (Rep.res g (Rep.res f (Rep.trivial Coeff
        (decompK (k := k) w) (ZMod p))))) = Rep.resMap g (Rep.resMap f e.hom)
      from Category.comp_id _] at hE
    rw [← hE]
    exact h3
  -- (D): the same, post-composed
  have h5 : (extHMap g (𝟙 (Rep.res g (Rep.res f S.X₁)))
      (h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl))).comp
      (Abelian.Ext.mk₀ (Rep.resMap g (Rep.resMap f e.hom))) (add_zero 2) = 0 := by
    rw [← dass_extHMap_eq_comp g (Rep.resMap g (Rep.resMap f e.hom)) 2
      (h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl))]
    exact h4
  -- the transport `resMap g (resMap f e.hom)` has `resMap g (resMap f e.inv)` as a right inverse
  have hpsi : Rep.resMap g (Rep.resMap f e.hom) ≫ Rep.resMap g (Rep.resMap f e.inv)
      = 𝟙 (Rep.res g (Rep.res f S.X₁)) :=
    ((Rep.resFunctor f ⋙ Rep.resFunctor g).mapIso e).hom_inv_id
  have h6 : extHMap g (𝟙 (Rep.res g (Rep.res f S.X₁)))
      (h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl)) = 0 := by
    calc extHMap g (𝟙 (Rep.res g (Rep.res f S.X₁)))
          (h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl))
        = (extHMap g (𝟙 (Rep.res g (Rep.res f S.X₁)))
            (h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl))).comp
            (Abelian.Ext.mk₀ (𝟙 (Rep.res g (Rep.res f S.X₁)))) (add_zero 2) :=
          (Abelian.Ext.comp_mk₀_id _).symm
      _ = (extHMap g (𝟙 (Rep.res g (Rep.res f S.X₁)))
            (h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl))).comp
            (Abelian.Ext.mk₀ (Rep.resMap g (Rep.resMap f e.hom) ≫
              Rep.resMap g (Rep.resMap f e.inv))) (add_zero 2) := by rw [hpsi]
      _ = ((extHMap g (𝟙 (Rep.res g (Rep.res f S.X₁)))
            (h''.comp (extRes f hS.extClass) (show (1:ℕ) + 1 = 2 from rfl))).comp
            (Abelian.Ext.mk₀ (Rep.resMap g (Rep.resMap f e.hom))) (add_zero 2)).comp
            (Abelian.Ext.mk₀ (Rep.resMap g (Rep.resMap f e.inv))) (add_zero 2) := by
          simp only [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.comp_assoc]
      _ = 0 := by rw [h5, Abelian.Ext.zero_comp]
  rw [dass_delta_naturality f g hS h'']
  exact h6


/-! ## Linearity of the level pairing -/

lemma dass_levelPair_zero_h {H G : Type} [Group H] [Group G] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    {r s : ℕ} (x : Abelian.Ext.{0} M A r) :
    levelPair f ι x (0 : extH (Rep.res f M) s) = 0 := by
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_zero, Abelian.Ext.zero_comp,
    Abelian.Ext.comp_zero]

lemma dass_levelPair_add_h {H G : Type} [Group H] [Group G] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    {r s : ℕ} (x : Abelian.Ext.{0} M A r) (h₁ h₂ : extH (Rep.res f M) s) :
    levelPair f ι x (h₁ + h₂) = levelPair f ι x h₁ + levelPair f ι x h₂ := by
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp]

lemma dass_levelPair_nsmul_h {H G : Type} [Group H] [Group G] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    {r s : ℕ} (x : Abelian.Ext.{0} M A r) (n : ℕ) (h : extH (Rep.res f M) s) :
    levelPair f ι x (n • h) = n • levelPair f ι x h :=
  AddMonoidHom.map_nsmul
    { toFun := fun h => levelPair f ι x h
      map_zero' := dass_levelPair_zero_h f ι x
      map_add' := fun a b => dass_levelPair_add_h f ι x a b } n h

lemma dass_levelPair_zsmul_h {H G : Type} [Group H] [Group G] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    {r s : ℕ} (x : Abelian.Ext.{0} M A r) (m : ℤ) (h : extH (Rep.res f M) s) :
    levelPair f ι x (m • h) = m • levelPair f ι x h :=
  AddMonoidHom.map_zsmul
    { toFun := fun h => levelPair f ι x h
      map_zero' := dass_levelPair_zero_h f ι x
      map_add' := fun a b => dass_levelPair_add_h f ι x a b } m h

lemma dass_levelPair_zero {H G : Type} [Group H] [Group G] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    {r s : ℕ} (h : extH (Rep.res f M) s) :
    levelPair f ι (0 : Abelian.Ext.{0} M A r) h = 0 := by
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_zero, Abelian.Ext.zero_comp,
    Abelian.Ext.comp_zero]

lemma dass_levelPair_add {H G : Type} [Group H] [Group G] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    {r s : ℕ} (x₁ x₂ : Abelian.Ext.{0} M A r) (h : extH (Rep.res f M) s) :
    levelPair f ι (x₁ + x₂) h = levelPair f ι x₁ h + levelPair f ι x₂ h := by
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp,
    Abelian.Ext.comp_add]

lemma dass_levelPair_zsmul {H G : Type} [Group H] [Group G] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    {r s : ℕ} (m : ℤ) (x : Abelian.Ext.{0} M A r) (h : extH (Rep.res f M) s) :
    levelPair f ι (m • x) h = m • levelPair f ι x h :=
  AddMonoidHom.map_zsmul
    { toFun := fun x => levelPair f ι x h
      map_zero' := dass_levelPair_zero f ι h
      map_add' := fun a b => dass_levelPair_add f ι a b h } m x

/-- The pairing of a `p`-torsion cohomology class with `p`-torsion coefficients is `p`-torsion. -/
lemma dass_levelPair_pTorsion_h {H G : Type} [Group H] [Group G] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    {r s : ℕ} (x : Abelian.Ext.{0} M A r) (p : ℕ) (h : extH (Rep.res f M) s)
    (hh : p • h = 0) : p • levelPair f ι x h = 0 := by
  rw [← dass_levelPair_nsmul_h f ι x p h, hh, dass_levelPair_zero_h]

/-- `Rep.resMap` of a composite group homomorphism (`rfl`, the composite functors agree on
objects and morphisms). -/
lemma dass_resMap_resMap {G H I : Type} [Group G] [Group H] [Group I] (f : H →* G) (g : I →* H)
    {A B : Rep Coeff G} (φ : A ⟶ B) :
    Rep.resMap g (Rep.resMap f φ) = Rep.resMap (f.comp g) φ := rfl

lemma dass_levelPair_neg {H G : Type} [Group H] [Group G] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    {r s : ℕ} (x : Abelian.Ext.{0} M A r) (h : extH (Rep.res f M) s) :
    levelPair f ι (-x) h = -levelPair f ι x h := by
  have h1 : levelPair f ι x h + levelPair f ι (-x) h = 0 := by
    rw [← dass_levelPair_add, add_neg_cancel, dass_levelPair_zero]
  exact eq_neg_of_add_eq_zero_right h1

lemma dass_levelPair_sub {H G : Type} [Group H] [Group G] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    {r s : ℕ} (x₁ x₂ : Abelian.Ext.{0} M A r) (h : extH (Rep.res f M) s) :
    levelPair f ι (x₁ - x₂) h = levelPair f ι x₁ h - levelPair f ι x₂ h := by
  rw [sub_eq_add_neg, dass_levelPair_add, dass_levelPair_neg, sub_eq_add_neg]

/-- **(Z6-a) The Kummer step at a level.**  If the level pairing of the Kummer class
`dassW hS e z` with a class `h ∈ H¹(D_{w'}, X₃)` vanishes, then so does the level pairing of `y''`
with `h`, assuming `y''` pulls back to a class `y` vanishing above the base level.

The proof is the design's §2(3): `hZ` says that the Kummer pushforward of the connecting class
`δ h` vanishes, so local Kummer theory (`dass_kummer_step`/`local_kummer_dies`) produces a higher
level `L'` at which `δ h` dies; there `h` is the pullback of a class `h₂` from `X₂`, and the
vanishing hypothesis `hy` applies to `h₂`; inflation injectivity (`Z2`, `localUnits_infl_injective`)
descends the resulting vanishing back to the level `L`. -/
theorem dass_E_zero_of_Z_zero (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    (z : Rep.trivial Coeff (decompK (k := k) w) (ZMod p) ⟶ localUnitsK (k := k) w) (hz : z ≠ 0)
    (S : ShortComplex (Rep Coeff (decompK (k := k) w))) (hS : S.ShortExact)
    (e : S.X₁ ≅ Rep.trivial Coeff (decompK (k := k) w) (ZMod p))
    (A₀ : Type) [Field A₀] [NumberField A₀] [Algebra k A₀] [Algebra K A₀] [IsScalarTower k K A₀]
      [FiniteDimensional k A₀] [IsGalois k A₀]
    (w₀ : NK.GlobalCFT.Place A₀) (hw₀ : NK.GlobalCFT.Place.LiesOver w₀ w)
    (f₀ : MulAction.stabilizer (A₀ ≃ₐ[k] A₀) w₀ →* decompK (k := k) w)
    (hf₀ : ∀ σ, ((f₀ σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K A₀ (σ : A₀ ≃ₐ[k] A₀))
    (ι₀ : Rep.res f₀ (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k A₀ w₀)
    (hι₀ : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι₀.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ u))
    (y : Abelian.Ext.{0} S.X₂ (localUnitsK (k := k) w) 1)
    (y'' : Abelian.Ext.{0} S.X₃ (localUnitsK (k := k) w) 1)
    (hy'' : (Abelian.Ext.mk₀ S.g).comp y'' (zero_add 1) = y)
    (hy : VanishesAbove k K y A₀ w₀ f₀ ι₀)
    (a : ℤ)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra A₀ L] [IsScalarTower k A₀ L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw'₀ : NK.GlobalCFT.Place.LiesOver w' w₀)
    (g : MulAction.stabilizer (L ≃ₐ[k] L) w' →* MulAction.stabilizer (A₀ ≃ₐ[k] A₀) w₀)
    (hg : ∀ σ, ((g σ : MulAction.stabilizer (A₀ ≃ₐ[k] A₀) w₀) : A₀ ≃ₐ[k] A₀) =
      galRes k A₀ L (σ : L ≃ₐ[k] L))
    (ι₁ : Rep.res g (NK.HassePrinciple.localUnitsRep k A₀ w₀) ⟶
      NK.HassePrinciple.localUnitsRep k L w')
    (hι₁ : ∀ u : (NK.GlobalCFT.Place.localField A₀ w₀)ˣ,
      ι₁.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀ hw'₀ u))
    [Algebra K L] [IsScalarTower k K L] [IsScalarTower K A₀ L]
    (h : extH (Rep.res (f₀.comp g) S.X₃) 1)
    (hZ : levelPair (f₀.comp g) (Rep.resMap g ι₀ ≫ ι₁) (dassW hS e z) h = 0) :
    levelPair (f₀.comp g) (Rep.resMap g ι₀ ≫ ι₁) (y'' - a • dassW hS e z) h = 0 := by
  classical
  -- ## 1. `hZ` in the shape required by the Kummer step
  have hw : levelPair (f₀.comp g) (Rep.resMap g ι₀ ≫ ι₁) (dassW hS e z) h
      = (h.comp (extRes (f₀.comp g) hS.extClass) (show (1:ℕ) + 1 = 2 from rfl)).comp
        (Abelian.Ext.mk₀ (Rep.resMap (f₀.comp g) e.hom ≫ Rep.resMap (f₀.comp g) z
          ≫ (Rep.resMap g ι₀ ≫ ι₁))) (add_zero 2) :=
    dass_levelPair_W (f₀.comp g) hS e z (Rep.resMap g ι₀ ≫ ι₁) h
  have hx : (h.comp (extRes (f₀.comp g) hS.extClass) (show (1:ℕ) + 1 = 2 from rfl)).comp
      (Abelian.Ext.mk₀ (Rep.resMap (f₀.comp g) e.hom ≫ Rep.resMap (f₀.comp g) z
        ≫ (Rep.resMap g ι₀ ≫ ι₁))) (add_zero 2) = 0 := by
    rw [← hw]; exact hZ
  -- ## 2. the `K`-structure at the level and the Kummer step
  have hw'K : NK.GlobalCFT.Place.LiesOver w' w :=
    Work.SSGRoute.place_liesOver_trans (K := K) (L := A₀) (M := L) hw'₀ hw₀
  have hf : ∀ σ, (((f₀.comp g) σ : decompK (k := k) w) : K ≃ₐ[k] K) =
      galRes k K L (σ : L ≃ₐ[k] L) := by
    intro σ
    rw [MonoidHom.comp_apply, hf₀ (g σ)]
    exact (congrArg (fun (e : A₀ ≃ₐ[k] A₀) => galRes k K A₀ e) (hg σ)).trans
      (galRes_trans (k := k) (K := K) (L := A₀) (L' := L) (σ := σ))
  have hιL : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      (Rep.resMap g ι₀ ≫ ι₁).hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw'K u) := by
    intro u
    have hv : (Rep.Hom.hom (Rep.resMap g ι₀ ≫ ι₁)) (Additive.ofMul u) =
        (Rep.Hom.hom ι₁) ((Rep.Hom.hom ι₀) (Additive.ofMul u)) := by
      rfl
    rw [hv, hι₀ u]
    refine (hι₁ (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ u)).trans ?_
    refine congrArg Additive.ofMul ?_
    rw [← MonoidHom.comp_apply, Work.SSGRoute.localAlgebraMapUnits_comp (K := K) (L := A₀)
      (M := L) (v := w) (w := w₀) (w' := w') hw'₀ hw₀ hw'K]
  obtain ⟨L', hF', hN', hAK', hAL', hST', hFD', hGal', w'', hw'', g₀, hg₀, hz4⟩ :=
    dass_kummer_step p k K w z hz S hS e L w' hw'K (f₀.comp g) hf (Rep.resMap g ι₀ ≫ ι₁) hιL
      h hx
  letI : Algebra k L' := hAK'
  letI : Algebra L L' := hAL'
  letI : IsScalarTower k L L' := hST'
  letI : FiniteDimensional k L' := hFD'
  letI : IsGalois k L' := hGal'
  obtain ⟨ι₂, hι₂⟩ := Work.SSGRoute.localUnitsMap_exists k L L' w' w'' hw'' g₀ hg₀
  -- ## 3. the composite `A₀ → L → L'` structure and datum
  letI : Algebra A₀ L' := ((algebraMap L L').comp (algebraMap A₀ L)).toAlgebra
  haveI hSTkA₀L' : IsScalarTower k A₀ L' := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    show algebraMap k L' x = algebraMap A₀ L' (algebraMap k A₀ x)
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply k L L' x, IsScalarTower.algebraMap_apply k A₀ L x]
  haveI hSTA₀LL' : IsScalarTower A₀ L L' := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    show algebraMap A₀ L' x = algebraMap L L' (algebraMap A₀ L x)
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  have hw''₀ : NK.GlobalCFT.Place.LiesOver w'' w₀ :=
    Work.SSGRoute.place_liesOver_trans (K := A₀) (L := L) (M := L') hw'' hw'₀
  have hg'' : ∀ σ, ((g.comp g₀ σ : MulAction.stabilizer (A₀ ≃ₐ[k] A₀) w₀) : A₀ ≃ₐ[k] A₀)
      = galRes k A₀ L' (σ : L' ≃ₐ[k] L') := by
    intro σ
    rw [MonoidHom.comp_apply, hg (g₀ σ)]
    exact (congrArg (fun (e : L ≃ₐ[k] L) => galRes k A₀ L e) (hg₀ σ)).trans
      (galRes_trans (k := k) (K := A₀) (L := L) (L' := L') (σ := σ))
  have hι''₀ : ∀ u : (NK.GlobalCFT.Place.localField A₀ w₀)ˣ,
      (Rep.resMap g₀ ι₁ ≫ ι₂).hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w'' w₀ hw''₀ u) := by
    intro u
    have hv : (Rep.Hom.hom (Rep.resMap g₀ ι₁ ≫ ι₂)) (Additive.ofMul u) =
        (Rep.Hom.hom ι₂) ((Rep.Hom.hom ι₁) (Additive.ofMul u)) := by
      rfl
    rw [hv, hι₁ u]
    refine (hι₂ (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀ hw'₀ u)).trans ?_
    refine congrArg Additive.ofMul ?_
    rw [← MonoidHom.comp_apply, Work.SSGRoute.localAlgebraMapUnits_comp (K := A₀) (L := L)
      (M := L') (v := w₀) (w := w') (w' := w'') hw'' hw'₀ hw''₀]
  -- ## 4. the vanishing hypothesis at the pushed level
  have hyL' : ∀ h₂ : extH (Rep.res (f₀.comp (g.comp g₀)) S.X₂) 1,
      levelPair (f₀.comp (g.comp g₀))
        (Rep.resMap (g.comp g₀) ι₀ ≫ (Rep.resMap g₀ ι₁ ≫ ι₂)) y h₂ = 0 :=
    fun h₂ => hy L' w'' hw''₀ (g.comp g₀) hg'' (Rep.resMap g₀ ι₁ ≫ ι₂) hι''₀ h₂
  -- ## 5. exactness at the pushed level
  obtain ⟨h₂, hh₂⟩ := dass_delta_eq_zero_iff (f := (f₀.comp g).comp g₀) hS
    (extHMap g₀ (𝟙 (Rep.res g₀ (Rep.res (f₀.comp g) S.X₃))) h) hz4
  -- ## 6. the pairing of `y''` at the pushed level vanishes
  have h1 : levelPair ((f₀.comp g).comp g₀)
      (Rep.resMap (g.comp g₀) ι₀ ≫ (Rep.resMap g₀ ι₁ ≫ ι₂)) y''
      (extHMap g₀ (𝟙 (Rep.res g₀ (Rep.res (f₀.comp g) S.X₃))) h) = 0 := by
    rw [← hh₂, ← dass_levelPair_coeff_naturality (f := (f₀.comp g).comp g₀) (π := S.g)
      (ι := (Rep.resMap (g.comp g₀) ι₀ ≫ (Rep.resMap g₀ ι₁ ≫ ι₂))) (r := 1) (s := 1) y'' h₂]
    rw [hy'']
    exact hyL' h₂
  -- ## 7. `Z1` and the coefficient bridge
  have hZ1 : levelPair ((f₀.comp g).comp g₀)
      (Rep.resMap g₀ (Rep.resMap g ι₀ ≫ ι₁) ≫ ι₂) y''
        (extHMap g₀ (𝟙 (Rep.res g₀ (Rep.res (f₀.comp g) S.X₃))) h)
      = extHMap g₀ ι₂ (levelPair (f₀.comp g) (Rep.resMap g ι₀ ≫ ι₁) y'' h) :=
    Work.SSGRoute.levelPair_comp_extHMap (f₁ := f₀.comp g) (g := g₀)
      (ι₀ := (Rep.resMap g ι₀ ≫ ι₁)) (ι₁ := ι₂) (r := 1) (s := 1) y'' h
  have hze : Rep.resMap (g.comp g₀) ι₀ ≫ (Rep.resMap g₀ ι₁ ≫ ι₂)
      = Rep.resMap g₀ (Rep.resMap g ι₀ ≫ ι₁) ≫ ι₂ := by
    rw [dass_resMap_comp g₀ (Rep.resMap g ι₀) ι₁, ← dass_resMap_resMap g g₀ ι₀]
    simp only [Category.assoc]
  rw [hze, hZ1] at h1
  have hY : levelPair (f₀.comp g) (Rep.resMap g ι₀ ≫ ι₁) y'' h = 0 :=
    (Work.SSGRoute.localUnits_infl_injective k L w' L' w'' hw'' g₀ hg₀ ι₂ hι₂)
      (h1.trans (Work.SSGRoute.E6Util.extHMap_zero g₀ ι₂).symm)
  -- ## 8. the `𝔽_p`-torsion of the same element, and the conclusion
  rw [dass_levelPair_sub, dass_levelPair_zsmul, hY, hZ, smul_zero, sub_zero]

namespace Work.SSGRoute

theorem detectAbove_sub_step (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    (z : Rep.trivial Coeff (decompK (k := k) w) (ZMod p) ⟶ localUnitsK (k := k) w) (hz : z ≠ 0)
    (S : ShortComplex (Rep Coeff (decompK (k := k) w))) (hS : S.ShortExact)
    (e : S.X₁ ≅ Rep.trivial Coeff (decompK (k := k) w) (ZMod p))
    [Finite S.X₂] (hp₂ : ∀ m : S.X₂, p • m = 0)
    (hbase : DetectAbove k K w (Rep.trivial Coeff (decompK (k := k) w) (ZMod p)))
    (h₃ : DetectAbove k K w S.X₃) :
    DetectAbove k K w S.X₂ := by
  intro L₀ hF₀ hN₀ hA₀ hAK₀ hST₀ hFD₀ hGal₀ w₀ hw₀ f₀ hf₀ ι₀ hι₀ y hy
  classical
  -- ### Step 1: `i^* y` vanishes above `λ₀`, hence is zero by the base case.
  have hiy_van : VanishesAbove k K ((Abelian.Ext.mk₀ S.f).comp y (zero_add 1))
      L₀ w₀ f₀ ι₀ := by
    intro L hF hN hA hAK hST hFD hGal w' hw' g hg ι₁ hι₁ h
    rw [dass_levelPair_coeff_naturality (f := f₀.comp g) (π := S.f)
      (ι := (Rep.resMap g ι₀ ≫ ι₁)) (r := 1) (s := 1) y h]
    exact hy L w' hw' g hg ι₁ hι₁
      (h.comp (Abelian.Ext.mk₀ (Rep.resMap (f₀.comp g) S.f)) (add_zero 1))
  have hiy_van' : VanishesAbove k K
      ((Abelian.Ext.mk₀ e.inv).comp ((Abelian.Ext.mk₀ S.f).comp y (zero_add 1)) (zero_add 1))
      L₀ w₀ f₀ ι₀ := by
    intro L hF hN hA hAK hST hFD hGal w' hw' g hg ι₁ hι₁ h
    rw [dass_levelPair_coeff_naturality (f := f₀.comp g) (π := e.inv)
      (ι := (Rep.resMap g ι₀ ≫ ι₁)) (r := 1) (s := 1)
      ((Abelian.Ext.mk₀ S.f).comp y (zero_add 1) :
        Abelian.Ext S.X₁ (localUnitsK (k := k) w) 1) h]
    exact hiy_van L w' hw' g hg ι₁ hι₁
      (h.comp (Abelian.Ext.mk₀ (Rep.resMap (f₀.comp g) e.inv)) (add_zero 1))
  have hiy_zero : (Abelian.Ext.mk₀ S.f).comp y (zero_add 1) = 0 := by
    have h0 : ((Abelian.Ext.mk₀ e.inv).comp ((Abelian.Ext.mk₀ S.f).comp y (zero_add 1))
        (zero_add 1)) = 0 :=
      hbase L₀ w₀ hw₀ f₀ hf₀ ι₀ hι₀ _ hiy_van'
    have h1 := congrArg (fun t => (Abelian.Ext.mk₀ e.hom).comp t (zero_add 1)) h0
    rw [Abelian.Ext.comp_zero] at h1
    rw [← h1]
    rw [← Abelian.Ext.comp_assoc_of_second_deg_zero (Abelian.Ext.mk₀ e.hom)
      (Abelian.Ext.mk₀ e.inv) ((Abelian.Ext.mk₀ S.f).comp y (zero_add 1)) (zero_add 1)]
    rw [Abelian.Ext.mk₀_comp_mk₀, e.hom_inv_id, Abelian.Ext.mk₀_id_comp]
  -- ### Step 2: `y = π^* y''`.
  obtain ⟨y'', hy''⟩ := Abelian.Ext.contravariant_sequence_exact₂ hS
    (localUnitsK (k := k) w) y hiy_zero
  -- ### Step 3: the pairing against `w = extClass ∘ z` kills the pullback.
  suffices hgoal : ∃ a : ℤ, y'' = a • dassW hS e z by
    obtain ⟨a, ha⟩ := hgoal
    rw [← hy'', ha]
    have hw0 : (Abelian.Ext.mk₀ S.g).comp (dassW hS e z) (zero_add 1) = 0 := by
      simpa only [dassW] using
        (ShortComplex.ShortExact.comp_extClass_assoc hS
          (Abelian.Ext.mk₀ (e.hom ≫ z)) (add_zero 1))
    have h2 : (Abelian.Ext.mk₀ S.g).comp (a • dassW hS e z) (zero_add 1)
        = a • ((Abelian.Ext.mk₀ S.g).comp (dassW hS e z) (zero_add 1)) :=
      AddMonoidHom.map_zsmul
        { toFun := fun t : Abelian.Ext S.X₃ (localUnitsK (k := k) w) 1 =>
            (Abelian.Ext.mk₀ S.g).comp t (zero_add 1)
          map_zero' := by rw [Abelian.Ext.comp_zero]
          map_add' := fun x y => by rw [Abelian.Ext.comp_add] } a (dassW hS e z)
    rw [h2, hw0, smul_zero]
  -- ### Step 4: the functional argument.
  -- `X₃` is `p`-torsion (a quotient of the `p`-torsion module `X₂`).
  have hX3 : ∀ m : S.X₃, p • m = 0 := by
    intro m
    obtain ⟨x, rfl⟩ := (Rep.epi_iff_surjective S.g).mp hS.epi_g m
    show p • (Rep.Hom.hom S.g).toLinearMap x = 0
    rw [← map_nsmul (Rep.Hom.hom S.g).toLinearMap p x, hp₂ x, map_zero]
  by_cases hwit : ∃ (L₁ : Type) (hF₁ : Field L₁) (hN₁ : NumberField L₁) (hA₁ : Algebra k L₁)
      (hA₀₁ : Algebra L₀ L₁) (hST₁ : IsScalarTower k L₀ L₁) (hFD₁ : FiniteDimensional k L₁)
      (hGal₁ : IsGalois k L₁) (w₁ : NK.GlobalCFT.Place L₁)
      (hw₁ : NK.GlobalCFT.Place.LiesOver w₁ w₀)
      (g₁ : MulAction.stabilizer (L₁ ≃ₐ[k] L₁) w₁ →* MulAction.stabilizer (L₀ ≃ₐ[k] L₀) w₀)
      (hg₁ : ∀ σ, ((g₁ σ : MulAction.stabilizer (L₀ ≃ₐ[k] L₀) w₀) : L₀ ≃ₐ[k] L₀) =
        galRes k L₀ L₁ (σ : L₁ ≃ₐ[k] L₁))
      (ι₁ : Rep.res g₁ (NK.HassePrinciple.localUnitsRep k L₀ w₀) ⟶
        NK.HassePrinciple.localUnitsRep k L₁ w₁)
      (hι₁ : ∀ u : (NK.GlobalCFT.Place.localField L₀ w₀)ˣ,
        ι₁.hom (Additive.ofMul u)
          = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w₁ w₀ hw₁ u))
      (h₁ : extH (Rep.res (f₀.comp g₁) S.X₃) 1),
      levelPair (f₀.comp g₁) (Rep.resMap g₁ ι₀ ≫ ι₁) (dassW hS e z) h₁ ≠ 0
  · -- ## Case A: a level above `λ₀` detects `dassW hS e z`.
    obtain ⟨L₁, hF₁, hN₁, hA₁, hA₀₁, hST₁, hFD₁, hGal₁, w₁, hw₁, g₁, hg₁, ι₁, hι₁, h₁, hne⟩ := hwit
    letI : Algebra k L₁ := hA₁
    letI : Algebra L₀ L₁ := hA₀₁
    letI : IsScalarTower k L₀ L₁ := hST₁
    letI : FiniteDimensional k L₁ := hFD₁
    letI : IsGalois k L₁ := hGal₁
    -- the composite `K → L₀ → L₁`
    letI : Algebra K L₁ := ((algebraMap L₀ L₁).comp (algebraMap K L₀)).toAlgebra
    haveI hSTkK₁ : IsScalarTower k K L₁ := by
      refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
      show algebraMap k L₁ x = algebraMap K L₁ (algebraMap k K x)
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        IsScalarTower.algebraMap_apply k L₀ L₁ x, IsScalarTower.algebraMap_apply k K L₀ x]
    haveI hSTKL₀₁ : IsScalarTower K L₀ L₁ := by
      refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
      show algebraMap K L₁ x = algebraMap L₀ L₁ (algebraMap K L₀ x)
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    -- the `K`-level datum at `λ₁`
    have hwK₁ : NK.GlobalCFT.Place.LiesOver w₁ w :=
      Work.SSGRoute.place_liesOver_trans (K := K) (L := L₀) (M := L₁) hw₁ hw₀
    have hf₁ : ∀ σ, (((f₀.comp g₁) σ : decompK (k := k) w) : K ≃ₐ[k] K) =
        galRes k K L₁ (σ : L₁ ≃ₐ[k] L₁) := by
      intro σ
      rw [MonoidHom.comp_apply, hf₀ (g₁ σ)]
      exact (congrArg (fun (e : L₀ ≃ₐ[k] L₀) => galRes k K L₀ e) (hg₁ σ)).trans
        (galRes_trans (k := k) (K := K) (L := L₀) (L' := L₁) (σ := σ))
    have hιL₁ : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
        (Rep.resMap g₁ ι₀ ≫ ι₁).hom (Additive.ofMul u) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w₁ w hwK₁ u) := by
      intro u
      have hv : (Rep.Hom.hom (Rep.resMap g₁ ι₀ ≫ ι₁)) (Additive.ofMul u) =
          (Rep.Hom.hom ι₁) ((Rep.Hom.hom ι₀) (Additive.ofMul u)) := by
        rfl
      rw [hv, hι₀ u]
      refine (hι₁ (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ u)).trans ?_
      refine congrArg Additive.ofMul ?_
      rw [← MonoidHom.comp_apply, Work.SSGRoute.localAlgebraMapUnits_comp (K := K) (L := L₀)
        (M := L₁) (v := w) (w := w₀) (w' := w₁) hw₁ hw₀ hwK₁]
    -- the scalar `a`, from the monogeneity of the `p`-torsion of the level Brauer group
    have hp₁ : p • h₁ = 0 :=
      E6Util.ext_nsmul_p_torsion p (fun m : Rep.res (f₀.comp g₁) S.X₃ => hX3 m) h₁
    have hptW : p • levelPair (f₀.comp g₁) (Rep.resMap g₁ ι₀ ≫ ι₁) (dassW hS e z) h₁ = 0 :=
      dass_levelPair_pTorsion_h (f₀.comp g₁) (Rep.resMap g₁ ι₀ ≫ ι₁) (dassW hS e z) p h₁ hp₁
    have hptY : p • levelPair (f₀.comp g₁) (Rep.resMap g₁ ι₀ ≫ ι₁) y'' h₁ = 0 :=
      dass_levelPair_pTorsion_h (f₀.comp g₁) (Rep.resMap g₁ ι₀ ≫ ι₁) y'' p h₁ hp₁
    obtain ⟨a, ha⟩ := (dass_pTorsion_gen p
      (Work.SSGRoute.ext_localUnits_pTorsion p k L₁ w₁))
      (levelPair (f₀.comp g₁) (Rep.resMap g₁ ι₀ ≫ ι₁) (dassW hS e z) h₁) hptW hne
      (levelPair (f₀.comp g₁) (Rep.resMap g₁ ι₀ ≫ ι₁) y'' h₁) hptY
    have hE₁ : levelPair (f₀.comp g₁) (Rep.resMap g₁ ι₀ ≫ ι₁)
        (y'' - a • dassW hS e z) h₁ = 0 := by
      rw [dass_levelPair_sub, dass_levelPair_zsmul, ha, sub_self]
    refine ⟨a, ?_⟩
    -- ## the vanishing of `y'' - a·w` above `λ₁`
    have hvan : VanishesAbove k K (y'' - a • dassW hS e z) L₁ w₁ (f₀.comp g₁)
        (Rep.resMap g₁ ι₀ ≫ ι₁) := by
      intro L hF hN hA hAL₁ hSTt hFD hGal w' hw' g hg ι₂ hι₂ h
      letI : Algebra k L := hA
      letI : Algebra L₁ L := hAL₁
      letI : IsScalarTower k L₁ L := hSTt
      letI : FiniteDimensional k L := hFD
      letI : IsGalois k L := hGal
      -- composites `L₀ → L`, `K → L`
      letI : Algebra L₀ L := ((algebraMap L₁ L).comp (algebraMap L₀ L₁)).toAlgebra
      haveI hSTkL₀L : IsScalarTower k L₀ L := by
        refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
        show algebraMap k L x = algebraMap L₀ L (algebraMap k L₀ x)
        rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
          IsScalarTower.algebraMap_apply k L₁ L x, IsScalarTower.algebraMap_apply k L₀ L₁ x]
      haveI hSTL₀L₁L : IsScalarTower L₀ L₁ L := by
        refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
        show algebraMap L₀ L x = algebraMap L₁ L (algebraMap L₀ L₁ x)
        rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
      letI : Algebra K L := ((algebraMap L₀ L).comp (algebraMap K L₀)).toAlgebra
      haveI hSTkKL : IsScalarTower k K L := by
        refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
        show algebraMap k L x = algebraMap K L (algebraMap k K x)
        rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
          IsScalarTower.algebraMap_apply k L₀ L x, IsScalarTower.algebraMap_apply k K L₀ x]
      haveI hSTKL₀L : IsScalarTower K L₀ L := by
        refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
        show algebraMap K L x = algebraMap L₀ L (algebraMap K L₀ x)
        rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
      -- the `λ₀`-level datum at `L`
      have hg' : ∀ σ, (((g₁.comp g) σ : MulAction.stabilizer (L₀ ≃ₐ[k] L₀) w₀) : L₀ ≃ₐ[k] L₀)
          = galRes k L₀ L (σ : L ≃ₐ[k] L) := by
        intro σ
        rw [MonoidHom.comp_apply, hg₁ (g σ)]
        exact (congrArg (fun (e : L₁ ≃ₐ[k] L₁) => galRes k L₀ L₁ e) (hg σ)).trans
          (galRes_trans (k := k) (K := L₀) (L := L₁) (L' := L) (σ := σ))
      have hι' : ∀ u : (NK.GlobalCFT.Place.localField L₀ w₀)ˣ,
          (Rep.resMap g ι₁ ≫ ι₂).hom (Additive.ofMul u) =
            Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀
              (Work.SSGRoute.place_liesOver_trans (K := L₀) (L := L₁) (M := L) hw' hw₁) u) := by
        intro u
        have hv : (Rep.Hom.hom (Rep.resMap g ι₁ ≫ ι₂)) (Additive.ofMul u) =
            (Rep.Hom.hom ι₂) ((Rep.Hom.hom ι₁) (Additive.ofMul u)) := by
          rfl
        rw [hv, hι₁ u]
        refine (hι₂ (NK.GlobalCFT.Place.localAlgebraMapUnits w₁ w₀ hw₁ u)).trans ?_
        refine congrArg Additive.ofMul ?_
        rw [← MonoidHom.comp_apply, Work.SSGRoute.localAlgebraMapUnits_comp (K := L₀) (L := L₁)
          (M := L) (v := w₀) (w := w₁) (w' := w')
          hw' hw₁ (Work.SSGRoute.place_liesOver_trans (K := L₀) (L := L₁) (M := L) hw' hw₁)]
      -- the coefficient bridge
      have hcoeff : Rep.resMap (g₁.comp g) ι₀ ≫ (Rep.resMap g ι₁ ≫ ι₂)
          = Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂ := by
        rw [dass_resMap_comp g (Rep.resMap g₁ ι₀) ι₁, ← dass_resMap_resMap g₁ g ι₀]
        simp only [Category.assoc]
      -- `Z`-vanishing at level `L` implies `E`-vanishing
      have hZof0 : ∀ hh : extH (Rep.res ((f₀.comp g₁).comp g) S.X₃) 1,
          levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
            (dassW hS e z) hh = 0 →
          levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
            (y'' - a • dassW hS e z) hh = 0 := by
        intro hh hZhh
        have hZ₀ : levelPair (f₀.comp (g₁.comp g))
            (Rep.resMap (g₁.comp g) ι₀ ≫ (Rep.resMap g ι₁ ≫ ι₂))
            (dassW hS e z) hh = 0 := by
          rw [hcoeff]; exact hZhh
        have hE₀ := dass_E_zero_of_Z_zero p k K w z hz S hS e L₀ w₀ hw₀ f₀ hf₀ ι₀ hι₀ y y''
          hy'' hy a L w'
          (Work.SSGRoute.place_liesOver_trans (K := L₀) (L := L₁) (M := L) hw' hw₁)
          (g₁.comp g) hg' (Rep.resMap g ι₁ ≫ ι₂) hι' hh hZ₀
        rw [← hcoeff]; exact hE₀
      -- the two branches
      have hX3L : ∀ m : Rep.res ((f₀.comp g₁).comp g) S.X₃, p • m = 0 := fun m => hX3 m
      have hptZ : p • levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
          (dassW hS e z) h = 0 :=
        dass_levelPair_pTorsion_h _ _ (dassW hS e z) p h
          (E6Util.ext_nsmul_p_torsion p (fun m => hX3L m) h)
      by_cases hZ : levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
          (dassW hS e z) h = 0
      · exact hZof0 h hZ
      · -- the level detects `dassW`: reduce to the known vanishing at `h₁`
        have hH1 : levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
            (dassW hS e z) (extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁) ≠ 0 := by
          intro hzero
          have hZ1 := Work.SSGRoute.levelPair_comp_extHMap (f₁ := f₀.comp g₁) (g := g)
            (ι₀ := Rep.resMap g₁ ι₀ ≫ ι₁) (ι₁ := ι₂) (r := 1) (s := 1) (dassW hS e z) h₁
          rw [hZ1] at hzero
          exact hne ((Work.SSGRoute.localUnits_infl_injective k L₁ w₁ L w' hw' g hg ι₂ hι₂)
            (hzero.trans (E6Util.extHMap_zero g ι₂).symm))
        have hptt : p • levelPair ((f₀.comp g₁).comp g)
            (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂) (dassW hS e z)
              (extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁) = 0 :=
          dass_levelPair_pTorsion_h _ _ (dassW hS e z) p _
            (E6Util.ext_nsmul_p_torsion p (fun m => hX3L m) _)
        obtain ⟨m, hm⟩ := (dass_pTorsion_gen p (Work.SSGRoute.ext_localUnits_pTorsion p k L w'))
          (levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
            (dassW hS e z) (extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁))
          hptt hH1
          (levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
            (dassW hS e z) h) hptZ
        have hZ0 : levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
            (dassW hS e z) (h - m • extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁)
            = 0 := by
          have hsub : levelPair ((f₀.comp g₁).comp g)
              (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂) (dassW hS e z)
                (h - m • extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁)
              = levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
                  (dassW hS e z) h
                - m • levelPair ((f₀.comp g₁).comp g)
                    (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂) (dassW hS e z)
                    (extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁) := by
            rw [sub_eq_add_neg, ← neg_zsmul, dass_levelPair_add_h, dass_levelPair_zsmul_h,
              sub_eq_add_neg, neg_zsmul]
          rw [hsub, hm, sub_self]
        have hE1 : levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
            (y'' - a • dassW hS e z)
            (extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁) = 0 := by
          rw [Work.SSGRoute.levelPair_comp_extHMap (f₁ := f₀.comp g₁) (g := g)
            (ι₀ := Rep.resMap g₁ ι₀ ≫ ι₁) (ι₁ := ι₂) (r := 1) (s := 1)
            (y'' - a • dassW hS e z) h₁]
          rw [hE₁, E6Util.extHMap_zero]
        calc levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
              (y'' - a • dassW hS e z) h
            = levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
                (y'' - a • dassW hS e z)
                (m • extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁
                  + (h - m • extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁)) := by
              rw [show m • extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁
                  + (h - m • extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁) = h
                from by abel]
          _ = m • levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
                (y'' - a • dassW hS e z)
                (extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁)
              + levelPair ((f₀.comp g₁).comp g) (Rep.resMap g (Rep.resMap g₁ ι₀ ≫ ι₁) ≫ ι₂)
                (y'' - a • dassW hS e z)
                (h - m • extHMap g (𝟙 (Rep.res g (Rep.res (f₀.comp g₁) S.X₃))) h₁) := by
              rw [dass_levelPair_add_h, dass_levelPair_zsmul_h]
          _ = 0 := by rw [hE1, hZof0 _ hZ0, smul_zero, zero_add]
    have hzero := h₃ L₁ w₁ hwK₁ (f₀.comp g₁) hf₁ (Rep.resMap g₁ ι₀ ≫ ι₁) hιL₁
      (y'' - a • dassW hS e z) hvan
    exact sub_eq_zero.mp hzero
  · -- ## Case B: no level above `λ₀` detects `dassW hS e z`.
    refine ⟨0, ?_⟩
    rw [zero_smul]
    have hvan : VanishesAbove k K y'' L₀ w₀ f₀ ι₀ := by
      intro L hF hN hA hAL₀ hSTt hFD hGal w' hw' g hg ι₂ hι₂ h
      letI : Algebra k L := hA
      letI : Algebra L₀ L := hAL₀
      letI : IsScalarTower k L₀ L := hSTt
      letI : FiniteDimensional k L := hFD
      letI : IsGalois k L := hGal
      letI : Algebra K L := ((algebraMap L₀ L).comp (algebraMap K L₀)).toAlgebra
      haveI hSTkKL : IsScalarTower k K L := by
        refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
        show algebraMap k L x = algebraMap K L (algebraMap k K x)
        rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
          IsScalarTower.algebraMap_apply k L₀ L x, IsScalarTower.algebraMap_apply k K L₀ x]
      haveI hSTKL₀L : IsScalarTower K L₀ L := by
        refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
        show algebraMap K L x = algebraMap L₀ L (algebraMap K L₀ x)
        rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
      have hZ0 : levelPair (f₀.comp g) (Rep.resMap g ι₀ ≫ ι₂) (dassW hS e z) h = 0 := by
        by_contra hne
        exact hwit ⟨L, hF, hN, hA, hAL₀, hSTt, hFD, hGal, w', hw', g, hg, ι₂, hι₂, h, hne⟩
      have hE := dass_E_zero_of_Z_zero p k K w z hz S hS e L₀ w₀ hw₀ f₀ hf₀ ι₀ hι₀ y y''
        hy'' hy 0 L w' hw' g hg ι₂ hι₂ h hZ0
      simpa only [zero_smul, sub_zero] using hE
    have hzero := h₃ L₀ w₀ hw₀ f₀ hf₀ ι₀ hι₀ y'' hvan
    rw [hzero]
end Work.SSGRoute
