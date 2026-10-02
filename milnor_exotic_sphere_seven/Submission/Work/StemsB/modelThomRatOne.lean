import Mathlib
import Submission.Work.StemsB.ModelThomRatDefs
import Submission.Work.StemsB.S0SubspaceRat
import Submission.Work.StemsB.pairDelta_mixedCup_general_R

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The model Thom class of rank one over `ℚ`: `Work.StemsB.ModelThomRat B 1`

The rank-one case of the rational model Thom class (`Work.StemsB.ModelThomRat`), by the
"difference + connecting map" argument of `MODELTHOM_RAT_PLAN.md`: for the pair
`(X, A) = (B × ℝ¹, B × S⁰)` with `S⁰ = {±1}`, the connecting map `δ : H⁰(A;ℚ) → H¹(X,A;ℚ)` is
surjective with kernel the diagonal `Δ ⊆ H⁰(B;ℚ) ⊕ H⁰(B;ℚ)`; the class
`σ := e⁻¹(1 ⊞ −1)` transgresses to `τ := δσ`, and for `x ∈ H^k(B;ℚ)` one has
`δ(x|_A ⌣ σ) = (−1)^k · p₂^*(x) ⌣ τ` with `x|_A ⌣ σ` of components `(x, −x)`.  Since
`x ↦ x ⊞ −x` induces an isomorphism `H^k(B;ℚ) ≅ (H^k(B;ℚ) ⊕ H^k(B;ℚ))/Δ` over `ℚ` (2 is
invertible), the cup map `x ↦ p₂^*(x) ⌣ τ` is bijective.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.StemsB

open CategoryTheory Limits Work.Cohomology

noncomputable section

/-! ## Elementwise API for binary biproducts of `ModuleCat R` -/

/-- The element of `A ⊞ B` with components `u`, `v`. -/
def biprodPair {R : Type} [Ring R] {A B : ModuleCat R} (u : A) (v : B) :
    (A ⊞ B : ModuleCat R) :=
  (biprod.inl : A ⟶ (A ⊞ B : ModuleCat R)).hom u
    + (biprod.inr : B ⟶ (A ⊞ B : ModuleCat R)).hom v

theorem biprodPair_fst {R : Type} [Ring R] {A B : ModuleCat R} (u : A) (v : B) :
    (biprod.fst : (A ⊞ B : ModuleCat R) ⟶ A).hom (biprodPair (R:=R) u v) = u := by
  rw [biprodPair, map_add,
    ← ModuleCat.comp_apply (biprod.inl : A ⟶ (A ⊞ B : ModuleCat R))
      (biprod.fst : (A ⊞ B : ModuleCat R) ⟶ A) u,
    ← ModuleCat.comp_apply (biprod.inr : B ⟶ (A ⊞ B : ModuleCat R))
      (biprod.fst : (A ⊞ B : ModuleCat R) ⟶ A) v,
    biprod.inl_fst, biprod.inr_fst]
  simp

theorem biprodPair_snd {R : Type} [Ring R] {A B : ModuleCat R} (u : A) (v : B) :
    (biprod.snd : (A ⊞ B : ModuleCat R) ⟶ B).hom (biprodPair (R:=R) u v) = v := by
  rw [biprodPair, map_add,
    ← ModuleCat.comp_apply (biprod.inl : A ⟶ (A ⊞ B : ModuleCat R))
      (biprod.snd : (A ⊞ B : ModuleCat R) ⟶ B) u,
    ← ModuleCat.comp_apply (biprod.inr : B ⟶ (A ⊞ B : ModuleCat R))
      (biprod.snd : (A ⊞ B : ModuleCat R) ⟶ B) v,
    biprod.inl_snd, biprod.inr_snd]
  simp

theorem biprodPair_fst_snd_eq {R : Type} [Ring R] {A B : ModuleCat R}
    (z : (A ⊞ B : ModuleCat R)) :
    biprodPair (R:=R) ((biprod.fst : (A ⊞ B : ModuleCat R) ⟶ A).hom z)
      ((biprod.snd : (A ⊞ B : ModuleCat R) ⟶ B).hom z) = z := by
  have h0 := congrArg (fun (φ : (A ⊞ B : ModuleCat R) ⟶ (A ⊞ B : ModuleCat R)) =>
    (ConcreteCategory.hom φ) z) (biprod.total (X := A) (Y := B))
  simp only [ModuleCat.hom_add, ModuleCat.hom_id, ModuleCat.comp_apply, LinearMap.add_apply,
    LinearMap.id_apply] at h0
  rw [biprodPair]
  exact h0

theorem biprod_ext_elem {R : Type} [Ring R] {A B : ModuleCat R} {a b : (A ⊞ B : ModuleCat R)}
    (h1 : (biprod.fst : (A ⊞ B : ModuleCat R) ⟶ A).hom a
      = (biprod.fst : (A ⊞ B : ModuleCat R) ⟶ A).hom b)
    (h2 : (biprod.snd : (A ⊞ B : ModuleCat R) ⟶ B).hom a
      = (biprod.snd : (A ⊞ B : ModuleCat R) ⟶ B).hom b) : a = b := by
  rw [← biprodPair_fst_snd_eq a, ← biprodPair_fst_snd_eq b, h1, h2]

/-! ## The classes `1`, `σ`, `τ` -/

/-- The unit class `1 ∈ H⁰(B;ℚ)`. -/
abbrev oneHat (B : Type) [TopologicalSpace B] : singularCohomology ℚ 0 (TopCat.of B) :=
  oneH ℚ (TopCat.toSSet.obj (TopCat.of B))

/-- `1 ⊞ (−1) ∈ H⁰(B;ℚ) ⊕ H⁰(B;ℚ)`. -/
def uHat (B : Type) [TopologicalSpace B] :
    (singularCohomology ℚ 0 (TopCat.of B) ⊞ singularCohomology ℚ 0 (TopCat.of B) : ModuleCat ℚ) :=
  biprodPair (oneHat B) (-(oneHat B))

/-- `σ = e⁻¹(1 ⊞ −1) ∈ H⁰(A;ℚ)`, the class whose components are `1` and `−1`. -/
def sigmaRat (B : Type) [TopologicalSpace B] : singularCohomology ℚ 0 (TopCat.of ↥(Aone B)) :=
  (cohAoneIso (B:=B) 0).inv.hom (uHat B)

variable {B : Type} [TopologicalSpace B]

abbrev HB (B : Type) [TopologicalSpace B] (k : ℕ) := singularCohomology ℚ k (TopCat.of B)
abbrev HX (B : Type) [TopologicalSpace B] (k : ℕ) := singularCohomology ℚ k (Xone B)
abbrev HA (B : Type) [TopologicalSpace B] (k : ℕ) := singularCohomology ℚ k (TopCat.of ↥(Aone B))
abbrev HB2 (B : Type) [TopologicalSpace B] (k : ℕ) := (HB B k ⊞ HB B k : ModuleCat ℚ)
abbrev RR (B : Type) [TopologicalSpace B] (k : ℕ) := relCohomology ℚ (Xone B) (Aone B) (k+1)

abbrev Pmap (B : Type) [TopologicalSpace B] (k : ℕ) : HB B k ⟶ HX B k :=
  singularCohomologyMap ℚ (Xone B) (TopCat.of B) (xProj B) k
abbrev Jmap (B : Type) [TopologicalSpace B] (k : ℕ) : HX B k ⟶ HA B k :=
  singularCohomologyMap ℚ (TopCat.of ↥(Aone B)) (Xone B) (aIncl B) k
abbrev Emap (B : Type) [TopologicalSpace B] (k : ℕ) : HA B k ⟶ HB2 B k := (cohAoneIso (B:=B) k).hom
abbrev Dmap (B : Type) [TopologicalSpace B] (k : ℕ) : HB B k ⟶ HB2 B k :=
  biprod.lift (𝟙 (HB B k)) (𝟙 (HB B k))
abbrev phimap (B : Type) [TopologicalSpace B] (k : ℕ) : HB B k ⟶ HB2 B k :=
  biprod.lift (𝟙 (HB B k)) (-𝟙 (HB B k))
abbrev cupSigma (B : Type) [TopologicalSpace B] (k : ℕ) : HA B k ⟶ HA B k :=
  ModuleCat.ofHom ((cupH' ℚ (TopCat.toSSet.obj (TopCat.of ↥(Aone B))) k 0).flip (sigmaRat B))
abbrev aSec₁Coh (B : Type) [TopologicalSpace B] (k : ℕ) : HA B k ⟶ HB B k :=
  singularCohomologyMap ℚ (TopCat.of B) (TopCat.of ↥(Aone B)) (aSec₁ B) k
abbrev aSec₂Coh (B : Type) [TopologicalSpace B] (k : ℕ) : HA B k ⟶ HB B k :=
  singularCohomologyMap ℚ (TopCat.of B) (TopCat.of ↥(Aone B)) (aSec₂ B) k

/-- `Ψ = j^* ∘ p₂^*` followed by the cup product with `σ`. -/
abbrev Psi (B : Type) [TopologicalSpace B] (k : ℕ) : HB B k ⟶ HA B k :=
  Pmap B k ≫ Jmap B k ≫ cupSigma B k

/-- The connecting map `δ : H^k(A;ℚ) ⟶ H^{k+1}(X,A;ℚ)`. -/
abbrev delmap (B : Type) [TopologicalSpace B] (k : ℕ) : HA B k ⟶ RR B k :=
  pairδ ℚ (Xone B) (Aone B) k

/-- **The Thom class of the rank-one model over `ℚ`**: `τ = δσ`. -/
def tauRat (B : Type) [TopologicalSpace B] : RelCohRat 1 (B × Euc1) (Aone B) :=
  (delmap B 0).hom (sigmaRat B)

instance instPmapIsIso (k : ℕ) : IsIso (Pmap B k) := isIso_xProj_pullback (B:=B) k

/-! ## The pullbacks along the two sections and `σ` -/

theorem aSec₁_pullback_sigma : aSec₁Coh B 0 (sigmaRat B) = oneHat B := by
  have hf := cohAoneIso_fst (B:=B) 0
  show (singularCohomologyMap ℚ (TopCat.of B) (TopCat.of ↥(Aone B)) (aSec₁ B) 0).hom
      ((cohAoneIso (B:=B) 0).inv.hom (uHat B)) = oneHat B
  rw [← hf, ModuleCat.comp_apply]
  rw [← ModuleCat.comp_apply (cohAoneIso (B:=B) 0).inv (cohAoneIso (B:=B) 0).hom (uHat B),
    (cohAoneIso (B:=B) 0).inv_hom_id, ModuleCat.id_apply]
  exact biprodPair_fst _ _

theorem aSec₂_pullback_sigma : aSec₂Coh B 0 (sigmaRat B) = -(oneHat B) := by
  have hf := cohAoneIso_snd (B:=B) 0
  show (singularCohomologyMap ℚ (TopCat.of B) (TopCat.of ↥(Aone B)) (aSec₂ B) 0).hom
      ((cohAoneIso (B:=B) 0).inv.hom (uHat B)) = -(oneHat B)
  rw [← hf, ModuleCat.comp_apply]
  rw [← ModuleCat.comp_apply (cohAoneIso (B:=B) 0).inv (cohAoneIso (B:=B) 0).hom (uHat B),
    (cohAoneIso (B:=B) 0).inv_hom_id, ModuleCat.id_apply]
  exact biprodPair_snd _ _

/-! ## The identification `e ∘ j^* = Δ ∘ (p₂^*)⁻¹` -/

/-- **`j^* ≫ e = (p₂^*)⁻¹ ≫ Δ`**: the diagonal in the `S⁰`-decomposition of the restriction. -/
theorem hF1 (k : ℕ) : Jmap B k ≫ Emap B k = inv (Pmap B k) ≫ Dmap B k :=
  (IsIso.eq_inv_comp (Pmap B k)).mpr (xProj_restr_cohAoneIso (B:=B) k)

theorem J_aSec₁ (k : ℕ) : Jmap B k ≫ aSec₁Coh B k = inv (Pmap B k) := by
  have h := congrArg (fun f => f ≫ (biprod.fst : HB2 B k ⟶ HB B k)) (hF1 (B:=B) k)
  rw [Category.assoc, cohAoneIso_fst, Category.assoc, biprod.lift_fst, Category.comp_id] at h
  exact h

theorem J_aSec₂ (k : ℕ) : Jmap B k ≫ aSec₂Coh B k = inv (Pmap B k) := by
  have h := congrArg (fun f => f ≫ (biprod.snd : HB2 B k ⟶ HB B k)) (hF1 (B:=B) k)
  rw [Category.assoc, cohAoneIso_snd, Category.assoc, biprod.lift_snd, Category.comp_id] at h
  exact h

/-! ## The cup product with `σ` and the sections -/

theorem cupSigma_apply (k : ℕ) (y : HA B k) :
    (cupSigma B k).hom y = (cupH' ℚ (TopCat.toSSet.obj (TopCat.of ↥(Aone B))) k 0 y) (sigmaRat B) :=
  rfl

theorem aSec₁_cupSigma (k : ℕ) : cupSigma B k ≫ aSec₁Coh B k = aSec₁Coh B k := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rw [ModuleCat.comp_apply, cupSigma_apply]
  have h := cupNaturalH ℚ (aSec₁ B) k 0 y (sigmaRat B)
  rw [aSec₁_pullback_sigma, cupH'_one_right] at h
  exact h

theorem aSec₂_cupSigma_apply (k : ℕ) (y : HA B k) :
    (aSec₂Coh B k).hom ((cupH' ℚ (TopCat.toSSet.obj (TopCat.of ↥(Aone B))) k 0 y) (sigmaRat B))
      = -((aSec₂Coh B k).hom y) := by
  have h := cupNaturalH ℚ (aSec₂ B) k 0 y (sigmaRat B)
  rw [aSec₂_pullback_sigma] at h
  refine h.trans ?_
  rw [map_neg, cupH'_one_right]

/-! ## The components of `e`, `Δ`, `φ`, and the inverses of `p₂^*` -/

theorem invPmap_apply (k : ℕ) (z : HX B k) :
    (Pmap B k).hom ((inv (Pmap B k)).hom z) = z := by
  rw [← ModuleCat.comp_apply (inv (Pmap B k)) (Pmap B k) z, IsIso.inv_hom_id, ModuleCat.id_apply]

theorem invPmap_apply' (k : ℕ) (z : HB B k) :
    (inv (Pmap B k)).hom ((Pmap B k).hom z) = z := by
  rw [← ModuleCat.comp_apply (Pmap B k) (inv (Pmap B k)) z, IsIso.hom_inv_id, ModuleCat.id_apply]

theorem Dmap_fst (k : ℕ) (y : HB B k) :
    (biprod.fst : HB2 B k ⟶ HB B k).hom ((Dmap B k).hom y) = y := by
  rw [← ModuleCat.comp_apply (Dmap B k) (biprod.fst : HB2 B k ⟶ HB B k) y, biprod.lift_fst,
    ModuleCat.id_apply]

theorem Dmap_snd (k : ℕ) (y : HB B k) :
    (biprod.snd : HB2 B k ⟶ HB B k).hom ((Dmap B k).hom y) = y := by
  rw [← ModuleCat.comp_apply (Dmap B k) (biprod.snd : HB2 B k ⟶ HB B k) y, biprod.lift_snd,
    ModuleCat.id_apply]

theorem phimap_fst (k : ℕ) (y : HB B k) :
    (biprod.fst : HB2 B k ⟶ HB B k).hom ((phimap B k).hom y) = y := by
  rw [← ModuleCat.comp_apply (phimap B k) (biprod.fst : HB2 B k ⟶ HB B k) y, biprod.lift_fst,
    ModuleCat.id_apply]

theorem phimap_snd (k : ℕ) (y : HB B k) :
    (biprod.snd : HB2 B k ⟶ HB B k).hom ((phimap B k).hom y) = -y := by
  rw [← ModuleCat.comp_apply (phimap B k) (biprod.snd : HB2 B k ⟶ HB B k) y, biprod.lift_snd]
  simp only [ModuleCat.hom_neg, ModuleCat.hom_id, LinearMap.neg_apply, LinearMap.id_apply]

/-! ## The two key computation rules -/

/-- `e(j^* w) = Δ((p₂^*)⁻¹ w)`. -/
theorem Emap_J_apply (k : ℕ) (w : HX B k) :
    (Emap B k).hom ((Jmap B k).hom w) = (Dmap B k).hom ((inv (Pmap B k)).hom w) := by
  have h := congrArg (fun f => (ConcreteCategory.hom f) w) (hF1 (B:=B) k)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
  exact h

/-- `e(j^*(p₂^*x) ⌣ σ) = φ x`, with `φ = 𝟙 ⊞ (−𝟙)`. -/
theorem Emap_cupSigma_apply (k : ℕ) (w : HX B k) :
    (Emap B k).hom ((cupSigma B k).hom ((Jmap B k).hom w))
      = (phimap B k).hom ((inv (Pmap B k)).hom w) := by
  have hJ₁ : (aSec₁Coh B k).hom ((Jmap B k).hom w) = (inv (Pmap B k)).hom w := by
    have h := congrArg (fun f => (ConcreteCategory.hom f) w) (J_aSec₁ (B:=B) k)
    rw [ModuleCat.comp_apply] at h
    exact h
  have hJ₂ : (aSec₂Coh B k).hom ((Jmap B k).hom w) = (inv (Pmap B k)).hom w := by
    have h := congrArg (fun f => (ConcreteCategory.hom f) w) (J_aSec₂ (B:=B) k)
    rw [ModuleCat.comp_apply] at h
    exact h
  apply biprod_ext_elem
  · rw [← ModuleCat.comp_apply (Emap B k) (biprod.fst : HB2 B k ⟶ HB B k)
        ((cupSigma B k).hom ((Jmap B k).hom w)), cohAoneIso_fst, cupSigma_apply]
    have h := cupNaturalH ℚ (aSec₁ B) k 0 ((Jmap B k).hom w) (sigmaRat B)
    refine h.trans ?_
    rw [hJ₁, aSec₁_pullback_sigma, cupH'_one_right]
    rw [← ModuleCat.comp_apply (phimap B k) (biprod.fst : HB2 B k ⟶ HB B k)
      ((inv (Pmap B k)).hom w), biprod.lift_fst, ModuleCat.id_apply]
  · rw [← ModuleCat.comp_apply (Emap B k) (biprod.snd : HB2 B k ⟶ HB B k)
        ((cupSigma B k).hom ((Jmap B k).hom w)), cohAoneIso_snd, cupSigma_apply,
      aSec₂_cupSigma_apply, hJ₂]
    rw [← ModuleCat.comp_apply (phimap B k) (biprod.snd : HB2 B k ⟶ HB B k)
      ((inv (Pmap B k)).hom w), biprod.lift_snd]
    simp only [ModuleCat.hom_neg, ModuleCat.hom_id, LinearMap.neg_apply, LinearMap.id_apply]

/-- `Ψ x = j^*(p₂^*x) ⌣ σ` has `e(Ψ x) = φ x`. -/
theorem Emap_Psi_apply (k : ℕ) (x : HB B k) :
    (Emap B k).hom ((Psi B k).hom x) = (phimap B k).hom x := by
  have hΨ : (Psi B k).hom x = (cupSigma B k).hom ((Jmap B k).hom ((Pmap B k).hom x)) := by
    rw [Psi, ModuleCat.comp_apply, ModuleCat.comp_apply]
  rw [hΨ, Emap_cupSigma_apply, invPmap_apply']

/-! ## The pair long exact sequence -/

/-- The kernel of the connecting map is the image of `j^*`. -/
theorem ker_delmap (k : ℕ) :
    LinearMap.ker (delmap B k).hom = LinearMap.range (Jmap B k).hom := by
  have hEx := pair_exact₃ ℚ (Xone B) (Aone B) k
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
  rw [← hEx]
  rw [show Jmap B k = HomologicalComplex.homologyMap (restr ℚ (Xone B) (Aone B)) k from rfl]

/-- `j^*` is injective. -/
theorem Jmap_injective (k : ℕ) : Function.Injective (Jmap B k).hom := by
  intro w₁ w₂ h
  have hE := congrArg (fun z => (Emap B k).hom z) h
  rw [Emap_J_apply, Emap_J_apply] at hE
  have h1 := congrArg (fun z => (biprod.fst : HB2 B k ⟶ HB B k).hom z) hE
  rw [Dmap_fst, Dmap_fst] at h1
  have h2 := congrArg (fun z => (Pmap B k).hom z) h1
  rw [invPmap_apply, invPmap_apply] at h2
  exact h2

/-- `e` is injective. -/
theorem Emap_injective (k : ℕ) : Function.Injective (Emap B k).hom := by
  intro a b hab
  have h := congrArg (fun z => (cohAoneIso (B:=B) k).inv.hom z) hab
  rw [← ModuleCat.comp_apply (cohAoneIso (B:=B) k).hom (cohAoneIso (B:=B) k).inv a,
      ← ModuleCat.comp_apply (cohAoneIso (B:=B) k).hom (cohAoneIso (B:=B) k).inv b,
      (cohAoneIso (B:=B) k).hom_inv_id, ModuleCat.id_apply, ModuleCat.id_apply] at h
  exact h

/-- The connecting map `δ` is surjective. -/
theorem delmap_surjective (k : ℕ) : Function.Surjective (delmap B k).hom := by
  have hEx1 := pair_exact₁ ℚ (Xone B) (Aone B) k
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx1
  have hEx2 := pair_exact₂ ℚ (Xone B) (Aone B) (k+1)
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx2
  have hker : LinearMap.ker
      (HomologicalComplex.homologyMap (restr ℚ (Xone B) (Aone B)) (k+1)).hom = ⊥ :=
    LinearMap.ker_eq_bot.mpr (Jmap_injective (B:=B) (k+1))
  have hbot : LinearMap.range
      (HomologicalComplex.homologyMap (relIncl ℚ (Xone B) (Aone B)) (k+1)).hom = ⊥ := by
    rw [hEx2, hker]
  have hzero : (HomologicalComplex.homologyMap (relIncl ℚ (Xone B) (Aone B)) (k+1)).hom = 0 :=
    LinearMap.range_eq_bot.mp hbot
  intro z
  refine LinearMap.mem_range.mp ?_
  rw [hEx1, hzero, LinearMap.ker_zero]
  exact Submodule.mem_top

/-! ## The main theorem -/

theorem modelThomRatOne (B : Type) [TopologicalSpace B] : Work.StemsB.ModelThomRat B 1 := by
  refine ⟨tauRat B, fun k => ?_⟩
  change Function.Bijective (fun x : HB B k =>
    (mixedCupR ℚ (Xone B) (Aone B) k 1) ((Pmap B k).hom x) (tauRat B))
  -- the derivation: `δ(Ψ x) = (-1)^k · (p₂^*(x) ⌣ τ)`
  have hdelta : ∀ x : HB B k, (delmap B k).hom ((Psi B k).hom x)
      = ((-1 : ℚ) ^ k) • ((mixedCupR ℚ (Xone B) (Aone B) k 1)
          ((Pmap B k).hom x) (tauRat B)) := by
    intro x
    exact pairDelta_mixedCup_general_R ℚ (Xone B) (Aone B) k 0 ((Pmap B k).hom x) (sigmaRat B)
  have hF : ∀ x : HB B k, ((mixedCupR ℚ (Xone B) (Aone B) k 1)
        ((Pmap B k).hom x) (tauRat B))
      = ((-1 : ℚ) ^ k)⁻¹ • ((delmap B k).hom ((Psi B k).hom x)) := by
    intro x
    rw [hdelta x, smul_smul, inv_mul_cancel₀ (pow_ne_zero k (by norm_num : (-1 : ℚ) ≠ 0)),
      one_smul]
  constructor
  · -- injectivity: `ker δ = im j^*`, and `e(Ψ x) = φ x` with `φ = 𝟙 ⊞ (−𝟙)`
    intro x y hxy
    have hxy' : ((mixedCupR ℚ (Xone B) (Aone B) k 1) ((Pmap B k).hom x)) (tauRat B)
        = ((mixedCupR ℚ (Xone B) (Aone B) k 1) ((Pmap B k).hom y)) (tauRat B) := hxy
    have hd : (delmap B k).hom ((Psi B k).hom x) = (delmap B k).hom ((Psi B k).hom y) := by
      rw [hdelta x, hdelta y, hxy']
    have hd0 : (delmap B k).hom ((Psi B k).hom x - (Psi B k).hom y) = 0 := by
      rw [map_sub, hd, sub_self]
    have hmem : (Psi B k).hom x - (Psi B k).hom y ∈ LinearMap.range (Jmap B k).hom := by
      rw [← ker_delmap (B:=B) k, LinearMap.mem_ker]
      exact hd0
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
    have hPsi_sub : (Psi B k).hom x - (Psi B k).hom y = (Psi B k).hom (x - y) := by
      rw [map_sub]
    have hE : (Emap B k).hom ((Jmap B k).hom w)
        = (Emap B k).hom ((Psi B k).hom (x - y)) := by
      rw [hw, hPsi_sub]
    rw [Emap_J_apply, Emap_Psi_apply] at hE
    have h1 := congrArg (fun z => (biprod.fst : HB2 B k ⟶ HB B k).hom z) hE
    rw [Dmap_fst, phimap_fst] at h1
    have h2 := congrArg (fun z => (biprod.snd : HB2 B k ⟶ HB B k).hom z) hE
    rw [Dmap_snd, phimap_snd] at h2
    have h3 : x - y = -(x - y) := h1.symm.trans h2
    have h4 : (x - y) + (x - y) = 0 := eq_neg_iff_add_eq_zero.mp h3
    have h5 : x - y = 0 := by
      have h2a : (2 : ℚ) • (x - y) = 0 := by
        rw [two_smul ℚ (x - y)]
        exact h4
      have hc := congrArg (fun z => (2 : ℚ)⁻¹ • z) h2a
      rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℚ) ≠ 0), one_smul, smul_zero] at hc
    exact sub_eq_zero.mp h5
  · -- surjectivity: solve `Δ w' = φ x − u` for `x`
    intro z
    obtain ⟨y, hy⟩ := delmap_surjective (B:=B) k z
    let y' : HA B k := ((-1 : ℚ) ^ k) • y
    let u : HB2 B k := (Emap B k).hom y'
    let u₁ : HB B k := (biprod.fst : HB2 B k ⟶ HB B k).hom u
    let u₂ : HB B k := (biprod.snd : HB2 B k ⟶ HB B k).hom u
    let x : HB B k := (2 : ℚ)⁻¹ • (u₁ - u₂)
    let w' : HB B k := x - u₁
    have h2x : x + x = u₁ - u₂ := by
      have h : (2 : ℚ) • x = u₁ - u₂ := by
        rw [show x = (2 : ℚ)⁻¹ • (u₁ - u₂) from rfl, smul_smul,
          mul_inv_cancel₀ (by norm_num : (2 : ℚ) ≠ 0), one_smul]
      rwa [two_smul] at h
    have hw' : w' = -x - u₂ := by
      have h3 : u₁ = (x + x) + u₂ := sub_eq_iff_eq_add.mp h2x.symm
      rw [show w' = x - u₁ from rfl, h3]
      abel
    have hDw : (Dmap B k).hom w' = (phimap B k).hom x - u := by
      apply biprod_ext_elem
      · rw [Dmap_fst, map_sub, phimap_fst]
      · rw [Dmap_snd, map_sub, phimap_snd]
        exact hw'
    have hEJ : (Emap B k).hom ((Jmap B k).hom ((Pmap B k).hom w'))
        = (Emap B k).hom ((Psi B k).hom x - y') := by
      rw [Emap_J_apply, invPmap_apply', hDw, map_sub, Emap_Psi_apply]
    have hJw : (Jmap B k).hom ((Pmap B k).hom w') = (Psi B k).hom x - y' :=
      Emap_injective (B:=B) k hEJ
    have hker : (delmap B k).hom ((Psi B k).hom x - y') = 0 := by
      rw [← LinearMap.mem_ker, ker_delmap (B:=B) k]
      exact LinearMap.mem_range.mpr ⟨(Pmap B k).hom w', hJw⟩
    have hPsi : (delmap B k).hom ((Psi B k).hom x) = (delmap B k).hom y' := by
      have h := hker
      rw [map_sub] at h
      exact sub_eq_zero.mp h
    have hdz : (delmap B k).hom y' = ((-1 : ℚ) ^ k) • z := by
      rw [show y' = ((-1 : ℚ) ^ k) • y from rfl, map_smul, hy]
    refine ⟨x, ?_⟩
    show ((mixedCupR ℚ (Xone B) (Aone B) k 1) ((Pmap B k).hom x)) (tauRat B) = z
    rw [hF x, hPsi, hdz, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero k (by norm_num : (-1 : ℚ) ≠ 0)), one_smul]

end

end Work.StemsB
