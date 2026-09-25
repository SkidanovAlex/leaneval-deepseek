import Mathlib
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.HassePrinciple.hilbert90_levelGroup
import Submission.NK.NUV2.ABHN.exists_units_map_eq_of_mem_fixedField
import Submission.NK.NUV2.ABHN.hilbert90_ker_levelQuotHom

open CategoryTheory

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NK.NUV2.ABHN

universe u

section Abstract

variable {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H]

example (f : G →* H) (A : Rep k H) (B : Rep k G) (φ : Rep.res f A ⟶ B) (g : G) (x : A.V) :
    φ.hom (A.ρ (f g) x) = B.ρ g (φ.hom x) := by
  exact Rep.hom_comm_apply φ g x

example (f : G →* H) (A : Rep k H) (g : G) (x : A.V) :
    (Rep.res f A).ρ g x = A.ρ (f g) x := rfl

lemma mapCocycles₂_apply' {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : Rep.res f A ⟶ B)
    (w : groupCohomology.cocycles₂ A) (a b : G) :
    (groupCohomology.mapCocycles₂ f φ w) (a, b) = φ.hom (w (f a, f b)) := by
  rw [groupCohomology.coe_mapCocycles₂]
  rfl

lemma hom_comm_apply' {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : Rep.res f A ⟶ B)
    (g : G) (x : A.V) : φ.hom (A.ρ (f g) x) = B.ρ g (φ.hom x) :=
  Rep.hom_comm_apply φ g x

lemma eq_of_sub_add_eq {M : Type*} [AddCommGroup M] {A b C D : M} (h : A - b + C = D) :
    b = A + C - D := by
  rw [← h]; abel

lemma eq_of_sub_add_eq_left {M : Type*} [AddCommGroup M] {A b C : M} (h : A - b + C = A) :
    b = C := by
  have h1 : A - b + C - A = 0 := by rw [h, sub_self]
  have h2 : C - b = 0 := by
    rwa [show A - b + C - A = C - b from by abel] at h1
  exact (sub_eq_zero.mp h2).symm

lemma eq_of_sub_add_eq_right {M : Type*} [AddCommGroup M] {A b C : M} (h : A - b + C = C) :
    A = b := by
  have h1 : (A - b) + C = 0 + C := by rw [h]; abel
  exact sub_eq_zero.mp (add_right_cancel h1)

end Abstract

section Main

variable {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H]

/-- **Injectivity of inflation in degree two**: if `φ : Res_f A ⟶ B` is injective with image
exactly the invariants of `B` under `ker f`, and every `1`-cocycle on `ker f` with values in `B`
is a coboundary, then `H²(H, A) → H²(G, B)` is injective. -/
theorem groupCohomology_map_two_injective
    (f : G →* H) (hf : Function.Surjective f)
    (A : Rep k H) (B : Rep k G) (φ : Rep.res f A ⟶ B)
    (hφ : Function.Injective ⇑φ.hom)
    (hφsurj : ∀ b : B.V, (∀ s : f.ker, B.ρ (s : G) b = b) → ∃ a : A.V, φ.hom a = b)
    (hH90 : ∀ α : f.ker → B.V, (∀ a b : f.ker, α (a * b) = B.ρ (a : G) (α b) + α a) →
      ∃ y : B.V, ∀ a : f.ker, α a = B.ρ (a : G) y - y) :
    Function.Injective (fun x : groupCohomology A 2 => (groupCohomology.map f φ 2).hom x) := by
  classical
  have key : ∀ z : groupCohomology A 2, (groupCohomology.map f φ 2).hom z = 0 → z = 0 := by
    intro z hz
    revert hz
    refine groupCohomology.H2_induction_on (A := A) z ?_
    intro w hw
    have hw' : (groupCohomology.H2π B) (groupCohomology.mapCocycles₂ f φ w) = 0 := by
      rw [← groupCohomology.H2π_comp_map_apply f φ w]
      exact hw
    obtain ⟨β, hβ⟩ := LinearMap.mem_range.mp ((groupCohomology.H2π_eq_zero_iff _).mp hw')
    have hstar : ∀ a b : G, B.ρ a (β b) - β (a * b) + β a = φ.hom (w (f a, f b)) := by
      intro a b
      have h := congrFun hβ (a, b)
      rw [groupCohomology.d₁₂_hom_apply, mapCocycles₂_apply' f φ w a b] at h
      exact h
    -- Step 1
    have hβ1 : β 1 = φ.hom (w (1, 1)) := by
      have h := hstar 1 1
      simpa using h
    have hβ1inv : ∀ s : f.ker, B.ρ (s : G) (β 1) = β 1 := by
      intro s
      have hs : f (s : G) = 1 := MonoidHom.mem_ker.mp s.2
      have h := hstar (s : G) 1
      rw [hs, map_one, mul_one] at h
      rw [← hβ1] at h
      simpa using h
    -- Step 2
    set α : f.ker → B.V := fun s => β 1 - β (s : G) with hαdef
    have hαcoc : ∀ a b : f.ker, α (a * b) = B.ρ (a : G) (α b) + α a := by
      intro a b
      have ha : f (a : G) = 1 := MonoidHom.mem_ker.mp a.2
      have hb : f (b : G) = 1 := MonoidHom.mem_ker.mp b.2
      have h1 : B.ρ (a : G) (β (b : G)) - β ((a : G) * (b : G)) + β (a : G)
          = φ.hom (w (1, 1)) := by
        have h := hstar (a : G) (b : G)
        rw [ha, hb] at h
        exact h
      have h2 : β ((a : G) * (b : G)) = B.ρ (a : G) (β (b : G)) + β (a : G) - β 1 := by
        rw [← hβ1] at h1
        exact eq_of_sub_add_eq h1
      simp only [hαdef]
      change β 1 - β ((a : G) * (b : G)) =
        B.ρ (a : G) (β 1 - β (b : G)) + (β 1 - β (a : G))
      rw [h2, map_sub, hβ1inv a]
      abel
    -- Step 3
    obtain ⟨y, hy⟩ := hH90 α hαcoc
    set β₁ : G → B.V := fun a => β a + B.ρ a y - y with hβ₁def
    have hβ₁d : ∀ a b : G, B.ρ a (β₁ b) - β₁ (a * b) + β₁ a = φ.hom (w (f a, f b)) := by
      intro a b
      have hc : B.ρ a (B.ρ b y) = B.ρ (a * b) y := by
        rw [← Module.End.mul_apply, ← map_mul]
      have h1 : B.ρ a (β b + B.ρ b y - y) = B.ρ a (β b) + B.ρ a (B.ρ b y) - B.ρ a y := by
        rw [map_sub, map_add]
      rw [hβ₁def]
      simp only
      rw [h1, hc]
      rw [← hstar a b]
      abel
    have hβ₁ker : ∀ s : f.ker, β₁ (s : G) = φ.hom (w (1, 1)) := by
      intro s
      have hs := hy s
      simp only [hαdef] at hs
      have h2 : β (s : G) + (B.ρ (s : G) y - y) = β 1 := by
        rw [← hs]; abel
      rw [hβ₁def]
      change β (s : G) + B.ρ (s : G) y - y = (Rep.Hom.hom φ) (w (1, 1))
      rw [add_sub_assoc, h2, hβ1]
    -- Step 4
    have hright : ∀ (a : G) (s : f.ker), β₁ (a * (s : G)) = β₁ a := by
      intro a s
      have h := hβ₁d a (s : G)
      have hfs : f (s : G) = 1 := MonoidHom.mem_ker.mp s.2
      have hφw : φ.hom (w (f a, f (s : G))) = B.ρ a (β₁ (s : G)) := by
        rw [hfs, groupCohomology.cocycles₂_map_one_snd w (f a)]
        rw [hom_comm_apply' f φ a (w (1, 1))]
        rw [hβ₁ker s]
      rw [hφw, hβ₁ker s] at h
      exact eq_of_sub_add_eq_left h
    -- Step 5
    have hfix : ∀ (a : G) (s : f.ker), B.ρ (s : G) (β₁ a) = β₁ a := by
      intro a s
      have hmem : a⁻¹ * (s : G) * a ∈ f.ker := by
        rw [MonoidHom.mem_ker]
        simp [MonoidHom.mem_ker.mp s.2]
      have hsa : (s : G) * a = a * (a⁻¹ * (s : G) * a) := by group
      have h := hβ₁d (s : G) a
      have hfs : f (s : G) = 1 := MonoidHom.mem_ker.mp s.2
      rw [hfs, groupCohomology.cocycles₂_map_one_fst w (f a)] at h
      rw [hβ₁ker s, hsa, hright a ⟨a⁻¹ * (s : G) * a, hmem⟩] at h
      exact eq_of_sub_add_eq_right h
    -- Step 6
    let sec : H → G := fun σ => Classical.choose (hf σ)
    have hsec : ∀ σ, f (sec σ) = σ := fun σ => Classical.choose_spec (hf σ)
    have hdescent : ∀ a : G, ∃ x : A.V, φ.hom x = β₁ a := fun a => hφsurj (β₁ a) (hfix a)
    let β₀ : H → A.V := fun σ => Classical.choose (hdescent (sec σ))
    have hβ₀ : ∀ σ, φ.hom (β₀ σ) = β₁ (sec σ) := fun σ => Classical.choose_spec (hdescent (sec σ))
    have hcongr : ∀ a b : G, f a = f b → β₁ a = β₁ b := by
      intro a b hab
      have hmem : b⁻¹ * a ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
      have h := hright b ⟨b⁻¹ * a, hmem⟩
      rwa [mul_inv_cancel_left b a] at h
    have hmain : (groupCohomology.d₁₂ A).hom β₀ = ⇑w := by
      funext q
      obtain ⟨σ, τ⟩ := q
      show (groupCohomology.d₁₂ A).hom β₀ (σ, τ) = w (σ, τ)
      apply hφ
      rw [groupCohomology.d₁₂_hom_apply]
      show φ.hom (A.ρ σ (β₀ τ) - β₀ (σ * τ) + β₀ σ) = φ.hom (w (σ, τ))
      rw [map_add, map_sub]
      have hstep : φ.hom (A.ρ σ (β₀ τ)) = B.ρ (sec σ) (φ.hom (β₀ τ)) := by
        have h := hom_comm_apply' f φ (sec σ) (β₀ τ)
        rwa [hsec σ] at h
      rw [hstep, hβ₀ τ, hβ₀ σ, hβ₀ (σ * τ)]
      have hw' : φ.hom (w (f (sec σ), f (sec τ))) = φ.hom (w (σ, τ)) := by
        rw [hsec σ, hsec τ]
      rw [← hw', ← hβ₁d (sec σ) (sec τ)]
      rw [← hcongr (sec σ * sec τ) (sec (σ * τ)) (by simp only [map_mul, hsec])]
    exact (groupCohomology.H2π_eq_zero_iff w).2 (LinearMap.mem_range.mpr ⟨β₀, hmain⟩)
  intro x y hxy
  have hxy' : (groupCohomology.map f φ 2).hom x = (groupCohomology.map f φ 2).hom y := hxy
  have h0 : (groupCohomology.map f φ 2).hom (x - y) = 0 := by
    rw [map_sub, hxy', sub_self]
  exact sub_eq_zero.mp (key (x - y) h0)

end Main

section Concrete

open NK.HassePrinciple NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

lemma levelQuotHom_surjective_aux {L L' : FiniteGaloisIntermediateField K K'}
    (hh : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) :
    Function.Surjective (levelQuotHom (U := (⊤ : Subgroup Gal(K'/K))) hh) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H u => exact ⟨QuotientGroup.mk u, by simp [NK.BrauerHasse.levelQuotHom]⟩

lemma unitsInclLinearMap_injective_aux {L L' : FiniteGaloisIntermediateField K K'}
    (hh : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) :
    Function.Injective (unitsInclLinearMap L L' hh) := by
  intro a b hab
  rw [unitsInclLinearMap_apply, unitsInclLinearMap_apply] at hab
  refine congrArg Additive.ofMul ?_
  exact Units.map_injective (f := (IntermediateField.inclusion hh).toMonoidHom)
      (IntermediateField.inclusion_injective hh) (Additive.ofMul.injective hab)

lemma unitsLevelMapCoeff_injective_aux {L L' : FiniteGaloisIntermediateField K K'}
    (hh : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) :
    Function.Injective ⇑(unitsLevelMapCoeff (⊤ : Subgroup Gal(K'/K)) hh).hom := by
  intro a b hab
  set a' : Additive (↥L)ˣ := a with ha'
  set b' : Additive (↥L)ˣ := b with hb'
  have hab' : unitsInclLinearMap.{u, u} L L' hh a' = unitsInclLinearMap.{u, u} L L' hh b' := hab
  exact unitsInclLinearMap_injective_aux.{u, u} hh hab'

/-! ## The target theorem -/

theorem unitsLevelMap_injective {K K' : Type} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K']
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    Function.Injective (fun x : ↥(NK.HassePrinciple.UnitsLevelH2 (⊤ : Subgroup Gal(K'/K)) L) =>
      (NK.HassePrinciple.unitsLevelMap (⊤ : Subgroup Gal(K'/K))
        ((FiniteGaloisIntermediateField.le_iff L L').mp h)).hom x) := by
  have hhf : (L : IntermediateField K K') ≤ (L' : IntermediateField K K') :=
    (FiniteGaloisIntermediateField.le_iff L L').mp h
  refine groupCohomology_map_two_injective (levelQuotHom (U := (⊤ : Subgroup Gal(K'/K))) hhf)
    (levelQuotHom_surjective_aux hhf) (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)
    (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L') (unitsLevelMapCoeff (⊤ : Subgroup Gal(K'/K)) hhf)
    (unitsLevelMapCoeff_injective_aux hhf) ?_ ?_
  · intro b hb
    set b' : Additive (↥L')ˣ := b with hb'
    obtain ⟨v, hv⟩ := exists_units_map_eq_of_mem_fixedField hhf (Additive.toMul b') (by
      intro σ hσ
      let sg : ↥(⊤ : Subgroup Gal(K'/K)) := ⟨σ, Subgroup.mem_top σ⟩
      have hs : QuotientGroup.mk sg ∈ (levelQuotHom (U := (⊤ : Subgroup Gal(K'/K))) hhf).ker := by
        rw [MonoidHom.mem_ker, NK.BrauerHasse.levelQuotHom, QuotientGroup.map_mk]
        exact (QuotientGroup.eq_one_iff _).2 hσ
      have hbs : (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L').ρ (QuotientGroup.mk sg) b' = b' :=
        hb ⟨QuotientGroup.mk sg, hs⟩
      have hbs' : ((levelRestrict L' (sg : Gal(K'/K))) • b' : Additive (↥L')ˣ) = b' := hbs
      have h4 : Units.map (levelRestrict L' (sg : Gal(K'/K))).toMonoidHom (Additive.toMul b') =
          Additive.toMul b' := congrArg Additive.toMul hbs'
      have h5 : (levelRestrict L' (sg : Gal(K'/K))) ((Additive.toMul b' : (↥L')ˣ) : ↥L') =
          ((Additive.toMul b' : (↥L')ˣ) : ↥L') := by
        have := congrArg (fun u : (↥L')ˣ => (u : ↥L')) h4
        rwa [Units.coe_map] at this
      have h6 : σ (((Additive.toMul b' : (↥L')ˣ) : ↥L') : K') =
          (((Additive.toMul b' : (↥L')ˣ) : ↥L') : K') := by
        have := congrArg (fun z : ↥L' => (z : K')) h5
        rw [AlgEquiv.restrictNormalHom_apply] at this
        simpa using this
      exact h6)
    refine ⟨Additive.ofMul v, ?_⟩
    have h1 : (unitsLevelMapCoeff (⊤ : Subgroup Gal(K'/K)) hhf).hom (Additive.ofMul v)
        = unitsInclLinearMap.{0, 0} L L' hhf (Additive.ofMul v) :=
      NK.HassePrinciple.unitsLevelMapCoeff_apply.{0, 0, 0} (⊤ : Subgroup Gal(K'/K)) hhf (Additive.ofMul v)
    have h2 : unitsInclLinearMap.{0, 0} L L' hhf (Additive.ofMul v) =
        Additive.ofMul ((Units.map (IntermediateField.inclusion hhf).toRingHom) v) := rfl
    exact h1.trans (h2.trans (congrArg Additive.ofMul hv))
  · exact hilbert90_ker_levelQuotHom hhf

end Concrete


end NK.NUV2.ABHN
