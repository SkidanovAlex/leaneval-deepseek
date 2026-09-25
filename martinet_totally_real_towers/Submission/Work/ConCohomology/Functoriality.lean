/-
Copyright: the martinet_totally_real_towers team.

# Functoriality of continuous cohomology

Two kinds of functoriality for the cohomology of `Submission.Work.ConCohomology.Defs`:

* **Coefficient change**: an equivariant additive map `F : A →+ B` of discrete modules induces
  maps `Z¹(A) → Z¹(B)`, `H¹(A) → H¹(B)`, `Z²(A) → Z²(B)`, `H²(A) → H²(B)` and `H⁰(A) → H⁰(B)`.

* **Group change**: a continuous homomorphism `ψ : H →* G` such that the `H`-action on `M` is the
  pullback of the `G`-action along `ψ` induces maps `H^n(G,M) → H^n(H,M)` (restriction/inflation).
-/

import Submission.Work.ConCohomology.Setup

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

/-! ### Coefficient change -/

section CoeffChange

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable [DistribMulAction G A] [DistribMulAction G B]
variable [IsDiscreteGModule G A] [IsDiscreteGModule G B]

/-- Postcomposition with an equivariant coefficient map, on `1`-cochains. -/
def cochain1Map (F : EqHom G A B) : Cochain1 G A →+ Cochain1 G B :=
  LocallyConstant.mapAddMonoidHom F.toAddMonoidHom

/-- Postcomposition with an equivariant coefficient map, on `2`-cochains. -/
def cochain2Map (F : EqHom G A B) : Cochain2 G A →+ Cochain2 G B :=
  LocallyConstant.mapAddMonoidHom F.toAddMonoidHom

@[simp] lemma cochain1Map_apply (F : EqHom G A B) (f : Cochain1 G A) (σ : G) :
    cochain1Map F f σ = F (f σ) := rfl

@[simp] lemma cochain2Map_apply (F : EqHom G A B) (f : Cochain2 G A) (p : G × G) :
    cochain2Map F f p = F (f p) := rfl

@[simp] lemma d1Hom_cochain1Map (F : EqHom G A B) (f : Cochain1 G A) :
    d1Hom G B (cochain1Map F f) = cochain2Map F (d1Hom G A f) := by
  ext p
  obtain ⟨σ, τ⟩ := p
  simp only [d1Hom_apply, cochain1Map_apply, cochain2Map_apply]
  rw [map_add, map_sub, EqHom.map_smul]

@[simp] lemma d0Hom_cochain1Map (F : EqHom G A B) (a : A) :
    d0Hom G B (F a) = cochain1Map F (d0Hom G A a) := by
  ext σ
  simp only [d0Hom_apply, cochain1Map_apply]
  rw [map_sub, EqHom.map_smul]

@[simp] lemma cochain3Map_apply (F : EqHom G A B) (f : Cochain3 G A) (p : G × G × G) :
    LocallyConstant.mapAddMonoidHom F.toAddMonoidHom f p = F (f p) := rfl

@[simp] lemma d2Hom_cochain2Map (F : EqHom G A B) (f : Cochain2 G A) :
    d2Hom G B (cochain2Map F f) =
      LocallyConstant.mapAddMonoidHom F.toAddMonoidHom (d2Hom G A f) := by
  ext p
  obtain ⟨σ, τ, ρ⟩ := p
  simp only [d2Hom_apply, cochain2Map_apply, cochain3Map_apply]
  rw [map_sub, map_add, map_sub, EqHom.map_smul]

/-- Coefficient change on `1`-cocycles. -/
def Z1Map (F : EqHom G A B) : Z1 G A →+ Z1 G B :=
  AddMonoidHom.codRestrict ((cochain1Map F).comp (Z1 G A).subtype) (Z1 G B) fun z => by
    rw [mem_Z1]
    exact (mem_Z1.mp z.2).comp F

/-- Coefficient change on `2`-cocycles. -/
def Z2Map (F : EqHom G A B) : Z2 G A →+ Z2 G B :=
  AddMonoidHom.codRestrict ((cochain2Map F).comp (Z2 G A).subtype) (Z2 G B) fun z => by
    rw [mem_Z2]
    exact (mem_Z2.mp z.2).comp F

@[simp] lemma Z1Map_coe (F : EqHom G A B) (z : Z1 G A) :
    ((Z1Map F z : Z1 G B) : Cochain1 G B) = cochain1Map F (z : Cochain1 G A) := rfl

@[simp] lemma Z2Map_coe (F : EqHom G A B) (z : Z2 G A) :
    ((Z2Map F z : Z2 G B) : Cochain2 G B) = cochain2Map F (z : Cochain2 G A) := rfl

/-- Coefficient change on `H¹`. -/
noncomputable def H1Map (F : EqHom G A B) : H1 G A →+ H1 G B :=
  QuotientAddGroup.map (B1' G A) (B1' G B) (Z1Map F) fun z hz => by
    rw [mem_B1'] at hz
    show (Z1Map F z : Cochain1 G B) ∈ B1 G B
    obtain ⟨a, ha⟩ := hz
    refine ⟨F a, ?_⟩
    rw [Z1Map_coe, ← ha, d0Hom_cochain1Map]

/-- Coefficient change on `H²`. -/
noncomputable def H2Map (F : EqHom G A B) : H2 G A →+ H2 G B :=
  QuotientAddGroup.map (B2' G A) (B2' G B) (Z2Map F) fun z hz => by
    rw [mem_B2'] at hz
    show (Z2Map F z : Cochain2 G B) ∈ B2 G B
    obtain ⟨a, ha⟩ := hz
    refine ⟨cochain1Map F a, ?_⟩
    rw [Z2Map_coe, ← ha, d1Hom_cochain1Map]

/-- Coefficient change on `H⁰ = M^G`. -/
def H0Map (F : EqHom G A B) : H0 G A →+ H0 G B where
  toFun a := ⟨F a, fun σ => by rw [← EqHom.map_smul, a.2 σ]⟩
  map_zero' := by ext; exact F.map_zero
  map_add' a b := by ext; exact F.map_add a b

@[simp] lemma H1Map_mk (F : EqHom G A B) (z : Z1 G A) :
    H1Map F (H1.mk z) = H1.mk (Z1Map F z) := rfl

@[simp] lemma H2Map_mk (F : EqHom G A B) (z : Z2 G A) :
    H2Map F (H2.mk z) = H2.mk (Z2Map F z) := rfl

@[simp] lemma H0Map_coe (F : EqHom G A B) (a : H0 G A) :
    ((H0Map F a : H0 G B) : B) = F a := rfl

lemma H1Map_id : H1Map (EqHom.id G A) = AddMonoidHom.id (H1 G A) := by
  refine AddMonoidHom.ext fun x => ?_
  refine QuotientAddGroup.induction_on x ?_
  intro z
  change H1Map (EqHom.id G A) (H1.mk z) = H1.mk z
  rw [H1Map_mk]
  congr 1

lemma H2Map_id : H2Map (EqHom.id G A) = AddMonoidHom.id (H2 G A) := by
  refine AddMonoidHom.ext fun x => ?_
  refine QuotientAddGroup.induction_on x ?_
  intro z
  change H2Map (EqHom.id G A) (H2.mk z) = H2.mk z
  rw [H2Map_mk]
  congr 1

end CoeffChange

/-! ### Group change (restriction and inflation) -/

section GroupChange

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction H M]

variable (ψ : H →* G) (hψ : Continuous ψ)

/-- Pullback of `1`-cochains along a continuous homomorphism `ψ : H →* G`. -/
def cochain1Res : Cochain1 G M →+ Cochain1 H M :=
  LocallyConstant.comapAddMonoidHom (⟨ψ, hψ⟩ : C(H, G))

/-- Pullback of `2`-cochains along a continuous homomorphism `ψ : H →* G`. -/
def cochain2Res : Cochain2 G M →+ Cochain2 H M :=
  LocallyConstant.comapAddMonoidHom
    (⟨fun p : H × H => (ψ p.1, ψ p.2),
      (hψ.comp continuous_fst).prodMk (hψ.comp continuous_snd)⟩ : C(H × H, G × G))

@[simp] lemma cochain1Res_apply (f : Cochain1 G M) (h : H) :
    cochain1Res ψ hψ f h = f (ψ h) := rfl

@[simp] lemma cochain2Res_apply (f : Cochain2 G M) (p : H × H) :
    cochain2Res ψ hψ f p = f (ψ p.1, ψ p.2) := rfl

variable {ψ hψ}

lemma d0Fun_cochain1Res (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m) (m : M) :
    d0Fun (G := H) m = fun h : H => d0Fun (G := G) m (ψ h) := by
  funext σ
  simp only [d0Fun_apply]
  rw [hcomp]

lemma d1Fun_cochain1Res (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m) (f : G → M) :
    d1Fun (fun h : H => f (ψ h)) = fun p : H × H => d1Fun f (ψ p.1, ψ p.2) := by
  funext p
  obtain ⟨σ, τ⟩ := p
  simp only [d1Fun_apply]
  rw [hcomp σ (f (ψ τ))]
  simp only [map_mul]

lemma d2Fun_cochain2Res (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m) (f : G × G → M) :
    d2Fun (fun p : H × H => f (ψ p.1, ψ p.2)) =
      fun q : H × H × H => d2Fun f (ψ q.1, ψ q.2.1, ψ q.2.2) := by
  funext q
  obtain ⟨σ, τ, ρ⟩ := q
  simp only [d2Fun_apply]
  rw [hcomp σ (f (ψ τ, ψ ρ))]
  simp only [map_mul]

lemma isCocycle1_comp_res (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m) {f : G → M}
    (hf : IsCocycle1 f) : IsCocycle1 (fun h : H => f (ψ h)) := by
  rw [isCocycle1_iff_d1Fun] at hf ⊢
  rw [d1Fun_cochain1Res hcomp, hf]
  rfl

lemma isCocycle2_comp_res (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m) {f : G × G → M}
    (hf : IsCocycle2 f) : IsCocycle2 (fun p : H × H => f (ψ p.1, ψ p.2)) := by
  rw [isCocycle2_iff_d2Fun] at hf ⊢
  rw [d2Fun_cochain2Res hcomp, hf]
  rfl

variable (ψ hψ)

/-- Restriction/inflation on `1`-cocycles. -/
def Z1Res (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m)
    [IsDiscreteGModule G M] [IsDiscreteGModule H M] : Z1 G M →+ Z1 H M :=
  AddMonoidHom.codRestrict ((cochain1Res ψ hψ).comp (Z1 G M).subtype) (Z1 H M) fun z => by
    rw [mem_Z1]
    exact isCocycle1_comp_res hcomp (mem_Z1.mp z.2)

/-- Restriction/inflation on `2`-cocycles. -/
def Z2Res (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m)
    [IsDiscreteGModule G M] [IsDiscreteGModule H M] : Z2 G M →+ Z2 H M :=
  AddMonoidHom.codRestrict ((cochain2Res ψ hψ).comp (Z2 G M).subtype) (Z2 H M) fun z => by
    rw [mem_Z2]
    exact isCocycle2_comp_res hcomp (mem_Z2.mp z.2)

/-- Restriction/inflation on `H¹`. -/
noncomputable def H1Res (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m)
    [IsDiscreteGModule G M] [IsDiscreteGModule H M] : H1 G M →+ H1 H M :=
  QuotientAddGroup.map (B1' G M) (B1' H M) (Z1Res ψ hψ hcomp) fun z hz => by
    rw [mem_B1'] at hz
    show (Z1Res ψ hψ hcomp z : Cochain1 H M) ∈ B1 H M
    obtain ⟨m, hm⟩ := hz
    refine ⟨m, ?_⟩
    refine LocallyConstant.ext fun h => ?_
    change d0Fun (G := H) m h = (z : Cochain1 G M) (ψ h)
    rw [d0Fun_cochain1Res hcomp]
    exact DFunLike.congr_fun hm (ψ h)

/-- Restriction/inflation on `H²`. -/
noncomputable def H2Res (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m)
    [IsDiscreteGModule G M] [IsDiscreteGModule H M] : H2 G M →+ H2 H M :=
  QuotientAddGroup.map (B2' G M) (B2' H M) (Z2Res ψ hψ hcomp) fun z hz => by
    rw [mem_B2'] at hz
    show (Z2Res ψ hψ hcomp z : Cochain2 H M) ∈ B2 H M
    obtain ⟨f, hf⟩ := hz
    refine ⟨cochain1Res ψ hψ f, ?_⟩
    refine LocallyConstant.ext fun p => ?_
    obtain ⟨σ, τ⟩ := p
    change d1Fun (fun h : H => f (ψ h)) (σ, τ) = (z : Cochain2 G M) (ψ σ, ψ τ)
    rw [d1Fun_cochain1Res hcomp]
    exact DFunLike.congr_fun hf (ψ σ, ψ τ)

@[simp] lemma H2Res_mk (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m)
    [IsDiscreteGModule G M] [IsDiscreteGModule H M] (z : Z2 G M) :
    H2Res ψ hψ hcomp (H2.mk z) = H2.mk (Z2Res ψ hψ hcomp z) := rfl

@[simp] lemma Z2Res_coe (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m)
    [IsDiscreteGModule G M] [IsDiscreteGModule H M] (z : Z2 G M) :
    ((Z2Res ψ hψ hcomp z : Z2 H M) : Cochain2 H M) =
      cochain2Res ψ hψ (z : Cochain2 G M) := rfl

@[simp] lemma H1Res_mk (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m)
    [IsDiscreteGModule G M] [IsDiscreteGModule H M] (z : Z1 G M) :
    H1Res ψ hψ hcomp (H1.mk z) = H1.mk (Z1Res ψ hψ hcomp z) := rfl

end GroupChange

section GroupChangeH0

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [Group H] [TopologicalSpace H]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction H M]
variable (ψ : H →* G)

/-- Restriction/inflation on `H⁰ = M^G`. -/
def H0Res (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m) : H0 G M →+ H0 H M where
  toFun m := ⟨m, fun h => by rw [hcomp h m]; exact m.2 (ψ h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma H0Res_coe (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m) (m : H0 G M) :
    ((H0Res ψ hcomp m : H0 H M) : M) = m := rfl

end GroupChangeH0

end Work.ConCohomology
