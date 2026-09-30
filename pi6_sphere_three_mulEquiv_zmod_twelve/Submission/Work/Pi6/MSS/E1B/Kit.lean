import Mathlib
import Submission.Work.Pi6.MSS.E1Aux
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.SSSR.serreE2Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The evaluation map from the cohomological `E_1` row to the dual of the chain `E_1` row

For a continuous map `p : E → B` and a field `𝕜` we construct the comparison map
`evS : E_1^{s,n}(p;𝕜) ⟶ Hom_𝕜(H_n(gr_s C_*(E)), 𝕜)` from the first page of the cohomological Serre
spectral sequence of `p` to the `𝕜`-dual of the `s`-th graded piece of the Serre chain filtration.

An element of `E_1^{s,n}` is represented by a cochain `c ∈ F^s` with `dc ∈ F^{s+1}`, i.e. a
functional on the chains of `A_{s+1}` vanishing on the chains of `A_s` whose coboundary vanishes on
the chains of `A_{s+1}`; it therefore restricts to a functional on the cycles of `A_{s+1}/A_s`,
well defined on homology.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology

namespace Work.Pi6.MSS.E1B

noncomputable section

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The morphism `Sing p : Sing E ⟶ Sing B` of singular simplicial sets. -/
abbrev sF (p : C(E, B)) : Work.SSS.sSing E ⟶ Work.SSS.sSing B := Work.SSS.sSingP p

/-- The chains of the `k`-th Serre subcomplex (`A_k` = the simplices whose image in `B` has
essential dimension `< k`). -/
abbrev Cc (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k : ℕ) : ChainComplex (ModuleCat 𝕜) ℕ :=
  Work.SSSR.sChains 𝕜 (serreSubSSet (sF p) k)

/-- The inclusion of the chains of `A_k` into the chains of `E`. -/
abbrev inclL (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k : ℕ) :
    Cc 𝕜 p k ⟶ Work.SSSR.sChains 𝕜 (Work.SSS.sSing E) :=
  serreChainsIncl 𝕜 (sF p) k

/-- The Serre cochain filtration of `p`, as a `CohFilt`. -/
abbrev Wc (𝕜 : Type) [Field 𝕜] (p : C(E, B)) : CohFilt 𝕜 := serreCF 𝕜 E B p

/-- The `s`-th graded piece of the Serre chain filtration of `p`. -/
abbrev Kg (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s : ℕ) : ChainComplex (ModuleCat 𝕜) ℕ :=
  Work.SSSR.grF (Work.SSSR.serF 𝕜 (sF p)) s

/-- The projection `C_*(A_{s+1}) ⟶ Kg s`. -/
abbrev Kgπ (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s : ℕ) :
    (Work.SSSR.serF 𝕜 (sF p)).obj s ⟶ Kg 𝕜 p s :=
  Work.SSSR.grFι 𝕜 (sF p) s

@[simp] theorem Kgπ_zero (𝕜 : Type) [Field 𝕜] (p : C(E, B)) : Kgπ 𝕜 p 0 = 𝟙 _ := rfl

theorem Kgπ_succ (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s : ℕ) :
    Kgπ 𝕜 p (s+1) = cokernel.π (Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) s) := rfl

/-- The inclusion `C_*(A_{s+1}) ⟶ C_*(A_{s+2})` in degree `n`. -/
abbrev grD (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    (Cc 𝕜 p (s+1)).X n ⟶ (Cc 𝕜 p (s+2)).X n :=
  (Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) s).f n

/-- The boundaries in `C_*(A_{s+2})`, i.e. the image of `C_*(A_{s+1})`. -/
abbrev grQ (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    Submodule 𝕜 ↥((Cc 𝕜 p (s+2)).X n) :=
  (grD 𝕜 p s n).hom.range

/-- A retraction of the inclusion of the boundaries. -/
noncomputable def grRetr (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    ↥((Cc 𝕜 p (s+2)).X n) →ₗ[𝕜] ↥(grQ 𝕜 p s n) :=
  Classical.choose (Work.StemsB.exists_retraction_subspace_field 𝕜 (grQ 𝕜 p s n))

theorem grRetr_spec (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    (grRetr 𝕜 p s n).comp (grQ 𝕜 p s n).subtype = LinearMap.id :=
  Classical.choose_spec (Work.StemsB.exists_retraction_subspace_field 𝕜 (grQ 𝕜 p s n))

/-- The projection of `C_*(A_{s+2})` onto a complement of the boundaries. -/
noncomputable def grRho (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    ↥((Cc 𝕜 p (s+2)).X n) →ₗ[𝕜] ↥((Cc 𝕜 p (s+2)).X n) :=
  LinearMap.id - (grQ 𝕜 p s n).subtype.comp (grRetr 𝕜 p s n)

theorem grRho_sub_mem (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (x : ↥((Cc 𝕜 p (s+2)).X n)) : grRho 𝕜 p s n x - x ∈ grQ 𝕜 p s n := by
  have : grRho 𝕜 p s n x - x = -(((grRetr 𝕜 p s n x : ↥(grQ 𝕜 p s n)) :
      ↥((Cc 𝕜 p (s+2)).X n))) := by
    simp only [grRho, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      Submodule.subtype_apply]
    abel
  rw [this]
  exact (grQ 𝕜 p s n).neg_mem (grRetr 𝕜 p s n x).2

theorem grRetr_val (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    {x : ↥((Cc 𝕜 p (s+2)).X n)} (hx : x ∈ grQ 𝕜 p s n) :
    ((grRetr 𝕜 p s n x : ↥(grQ 𝕜 p s n)) : ↥((Cc 𝕜 p (s+2)).X n)) = x := by
  have h := LinearMap.congr_fun (grRetr_spec 𝕜 p s n) (⟨x, hx⟩ : ↥(grQ 𝕜 p s n))
  have h' : (grRetr 𝕜 p s n x : ↥(grQ 𝕜 p s n)) = ⟨x, hx⟩ := h
  rw [h']

theorem grRho_kill (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    {x : ↥((Cc 𝕜 p (s+2)).X n)} (hx : x ∈ grQ 𝕜 p s n) : grRho 𝕜 p s n x = 0 := by
  simp only [grRho, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Submodule.subtype_apply]
  rw [show ((grRetr 𝕜 p s n x : ↥(grQ 𝕜 p s n)) : ↥((Cc 𝕜 p (s+2)).X n)) = x from
    grRetr_val 𝕜 p s n hx, sub_self]

/-- A linear section of the quotient map `C_*(A_{s+2}) ⟶ C_*(A_{s+2})/C_*(A_{s+1})`. -/
noncomputable def grSecQ (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    (↥((Cc 𝕜 p (s+2)).X n) ⧸ grQ 𝕜 p s n) →ₗ[𝕜] ↥((Cc 𝕜 p (s+2)).X n) :=
  Submodule.liftQ (grQ 𝕜 p s n) (grRho 𝕜 p s n)
    (by intro x hx; rw [LinearMap.mem_ker]; exact grRho_kill 𝕜 p s n hx)

theorem grSecQ_grRho (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (x : ↥((Cc 𝕜 p (s+2)).X n)) :
    grSecQ 𝕜 p s n (Submodule.Quotient.mk x) = grRho 𝕜 p s n x := by
  show (Submodule.liftQ (grQ 𝕜 p s n) (grRho 𝕜 p s n) _) (Submodule.Quotient.mk x) = _
  rw [Submodule.liftQ_apply]

theorem grSecQ_spec (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    (grQ 𝕜 p s n).mkQ.comp (grSecQ 𝕜 p s n) = LinearMap.id := by
  apply LinearMap.ext
  intro w
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (grQ 𝕜 p s n) w
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  simp only [Submodule.mkQ_apply, grSecQ_grRho]
  rw [Submodule.Quotient.eq]
  exact grRho_sub_mem 𝕜 p s n x

/-- The comparison `Kg (s+1) ≅ cokernel (grD p s n)`. -/
noncomputable def grIso1 (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    (Kg 𝕜 p (s+1)).X n ≅ cokernel (grD 𝕜 p s n) :=
  PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat 𝕜) (ComplexShape.down ℕ) n)
    (Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) s)

/-- The quotient model of `cokernel (grD p s n)`. -/
noncomputable def grIso2 (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    cokernel (grD 𝕜 p s n) ≅
      ModuleCat.of 𝕜 (↥((Cc 𝕜 p (s+2)).X n) ⧸ grQ 𝕜 p s n) :=
  ModuleCat.cokernelIsoRangeQuotient (grD 𝕜 p s n)

/-- A linear section of the projection `C_*(A_{s+1}) ⟶ Kg s`. -/
noncomputable def grSecX (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    (Kg 𝕜 p s).X n →ₗ[𝕜] (Cc 𝕜 p (s+1)).X n :=
  match s with
  | 0 => LinearMap.id
  | (k + 1) => (grSecQ 𝕜 p k n).comp (((grIso1 𝕜 p k n) ≪≫ (grIso2 𝕜 p k n)).hom.hom)

theorem grSecX_succ (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k n : ℕ) :
    grSecX 𝕜 p (k+1) n =
      (grSecQ 𝕜 p k n).comp (((grIso1 𝕜 p k n) ≪≫ (grIso2 𝕜 p k n)).hom.hom) := rfl

@[simp] theorem grSecX_zero (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (n : ℕ) :
    grSecX 𝕜 p 0 n = LinearMap.id := rfl

/-- The relation between the quotient quotient and the graded piece. -/
theorem grIso2_π (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    cokernel.π (grD 𝕜 p s n) ≫ (grIso2 𝕜 p s n).hom = ModuleCat.ofHom (grQ 𝕜 p s n).mkQ :=
  ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom (grD 𝕜 p s n)

/-- The section is a section of the projection, at the level of morphisms of `ModuleCat`. -/
theorem grSecX_mor (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    ModuleCat.ofHom (grSecX 𝕜 p s n) ≫ (Kgπ 𝕜 p s).f n = 𝟙 ((Kg 𝕜 p s).X n) := by
  match s with
  | 0 =>
      rw [grSecX_zero, ModuleCat.ofHom_id, Kgπ_zero, HomologicalComplex.id_f,
        Category.id_comp]
      rfl
  | (k + 1) =>
      have hsecQ : (grQ 𝕜 p k n).mkQ.comp (grSecQ 𝕜 p k n) = LinearMap.id :=
        grSecQ_spec 𝕜 p k n
      have hgr : ((Kgπ 𝕜 p (k+1)).f n) ≫ (grIso1 𝕜 p k n).hom = cokernel.π (grD 𝕜 p k n) := by
        have h := PreservesCokernel.π_iso_hom
          (HomologicalComplex.eval (ModuleCat 𝕜) (ComplexShape.down ℕ) n)
          (Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k)
        rw [Kgπ_succ]
        exact h
      have h1 : ((Kgπ 𝕜 p (k+1)).f n) = cokernel.π (grD 𝕜 p k n) ≫ (grIso1 𝕜 p k n).inv := by
        rw [← hgr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      have hπ : cokernel.π (grD 𝕜 p k n) =
          ModuleCat.ofHom (grQ 𝕜 p k n).mkQ ≫ (grIso2 𝕜 p k n).inv := by
        rw [← Category.comp_id (cokernel.π (grD 𝕜 p k n)),
          ← Iso.hom_inv_id (grIso2 𝕜 p k n), ← Category.assoc, grIso2_π]
      have h2 : ModuleCat.ofHom (grSecQ 𝕜 p k n) ≫ cokernel.π (grD 𝕜 p k n) =
          (grIso2 𝕜 p k n).inv := by
        rw [← cancel_mono (grIso2 𝕜 p k n).hom]
        rw [Category.assoc, grIso2_π, ← ModuleCat.ofHom_comp, hsecQ, ModuleCat.ofHom_id,
          Iso.inv_hom_id]
      have hmid : ModuleCat.ofHom (grSecQ 𝕜 p k n) ≫ (Kgπ 𝕜 p (k+1)).f n =
          (grIso1 𝕜 p k n ≪≫ grIso2 𝕜 p k n).inv := by
        calc ModuleCat.ofHom (grSecQ 𝕜 p k n) ≫ (Kgπ 𝕜 p (k+1)).f n
            = ModuleCat.ofHom (grSecQ 𝕜 p k n) ≫ cokernel.π (grD 𝕜 p k n) ≫
                (grIso1 𝕜 p k n).inv := by rw [h1]
          _ = (ModuleCat.ofHom (grSecQ 𝕜 p k n) ≫ cokernel.π (grD 𝕜 p k n)) ≫
                (grIso1 𝕜 p k n).inv := (Category.assoc _ _ _).symm
          _ = (grIso2 𝕜 p k n).inv ≫ (grIso1 𝕜 p k n).inv := by rw [h2]
          _ = (grIso1 𝕜 p k n ≪≫ grIso2 𝕜 p k n).inv := (Iso.trans_inv _ _).symm
      rw [grSecX_succ, ModuleCat.ofHom_comp]
      rw [show ModuleCat.ofHom (((grIso1 𝕜 p k n) ≪≫ (grIso2 𝕜 p k n)).hom.hom) =
          ((grIso1 𝕜 p k n) ≪≫ (grIso2 𝕜 p k n)).hom from rfl]
      rw [Category.assoc, hmid, Iso.hom_inv_id]

/-- The section property, elementwise. -/
theorem Kgπ_grSecX_apply (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (z : (Kg 𝕜 p s).X n) : ((Kgπ 𝕜 p s).f n).hom (grSecX 𝕜 p s n z) = z := by
  have h := congrArg (fun (f : (Kg 𝕜 p s).X n ⟶ (Kg 𝕜 p s).X n) => f.hom z)
    (grSecX_mor 𝕜 p s n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] at h
  exact h


/-! ## The kernel of the projection to the graded piece -/

/-- The inclusion whose range is the kernel of the projection `Kgπ` (the dummy `0` for `s = 0`,
where the projection is an isomorphism and the kernel is trivial). -/
noncomputable def grIncl (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    (Cc 𝕜 p s).X n ⟶ (Cc 𝕜 p (s+1)).X n :=
  match s with
  | 0 => 0
  | (k + 1) => (Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f n

/-- The kernel of the projection `Kgπ s` is contained in the range of `grIncl s`. -/
theorem ker_Kgπ_le_grIncl (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    LinearMap.ker ((Kgπ 𝕜 p s).f n).hom ≤ LinearMap.range (grIncl 𝕜 p s n).hom := by
  match s with
  | 0 =>
      rw [Kgπ_zero, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.ker_id]
      exact bot_le
  | (k + 1) =>
      intro x hx
      show x ∈ LinearMap.range ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f n).hom
      have hx' : ((Kgπ 𝕜 p (k+1)).f n).hom x = 0 := hx
      have hconn : (cokernel.π ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f n)).hom x = 0 := by
        have h := congrArg ModuleCat.Hom.hom
          (PreservesCokernel.π_iso_hom
            (HomologicalComplex.eval (ModuleCat 𝕜) (ComplexShape.down ℕ) n)
            (Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k))
        rw [ModuleCat.hom_comp] at h
        have h2 := LinearMap.congr_fun h x
        rw [LinearMap.comp_apply] at h2
        have hx'' : (((HomologicalComplex.eval (ModuleCat 𝕜) (ComplexShape.down ℕ) n).map
            (cokernel.π (Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k))).hom) x = 0 := hx'
        rw [hx'', map_zero] at h2
        exact h2.symm
      have h3 := congrArg ModuleCat.Hom.hom
        (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom
          ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f n))
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h3
      have h4 := LinearMap.congr_fun h3 x
      rw [LinearMap.comp_apply, hconn, map_zero] at h4
      exact (Submodule.Quotient.mk_eq_zero _).mp (by simpa [Submodule.mkQ_apply] using h4.symm)

/-- The compatibility of the inclusion `inclL` with the structure maps of the Serre filtration. -/
theorem inclL_comp_apply (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k n : ℕ)
    (y : ↥(((Work.SSSR.serF 𝕜 (sF p)).obj k).X n)) :
    ((inclL 𝕜 p (k+2)).f n).hom (((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f n).hom y) =
      ((inclL 𝕜 p (k+1)).f n).hom y := by
  have h2 := congrArg (fun (g : (Work.SSSR.serreFiltrationOf (R := 𝕜) p).F.obj k ⟶
      Work.Cohomology.singularChains 𝕜 (TopCat.of E)) => (g.f n).hom y)
    ((Work.SSSR.serreFiltrationOf (R := 𝕜) p).compat (Nat.le_succ k))
  exact h2

/-- The annihilator of the `s`-th Serre subcomplex kills the image of the kernel of `Kgπ s`. -/
theorem ker_Kgπ_inclL_eq_zero (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n)
    (x : (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X n →ₗ[𝕜] 𝕜)
    (hx : x ∈ coFilt 𝕜 (sF p) s n)
    (w : ↥((Cc 𝕜 p (s+1)).X n)) (hw : ((Kgπ 𝕜 p s).f n).hom w = 0) :
    x (((inclL 𝕜 p (s+1)).f n).hom w) = 0 := by
  match s with
  | 0 =>
      have hw0 : w = 0 := hw
      rw [hw0, map_zero, map_zero]
  | (k + 1) =>
      have hxk : x ∈ compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) (k+1)) n := by
        rw [← hann (k+1) n]; exact hx
      obtain ⟨y, hy⟩ := ker_Kgπ_le_grIncl 𝕜 p (k+1) n (LinearMap.mem_ker.mpr hw)
      rw [← hy]
      change x (((inclL 𝕜 p (k+2)).f n).hom
        (((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f n).hom y)) = 0
      rw [inclL_comp_apply 𝕜 p k n y]
      exact hxk y

/-! ## The evaluation map on representatives -/

/-- A cochain of the Serre filtration, viewed as a linear functional on the chains of `E`. -/
def cochainFun (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (n : ℕ)
    (x : ↥((Wc 𝕜 p).C.X n)) : (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X n →ₗ[𝕜] 𝕜 := x

/-- The differential of the Serre cochain filtration as a transposed differential. -/
theorem Wc_d_apply (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (n : ℕ)
    (x : ↥((Wc 𝕜 p).C.X n)) :
    ((Wc 𝕜 p).d n) x = (x : (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X n →ₗ[𝕜] 𝕜).comp
      ((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (n+1) n).hom := by
  show (ModuleCat.Hom.hom ((Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).d n
      (n+1))) x = _
  rw [Work.Cohomology.SSetCochainComplex_d]
  rfl

/-- The transposed differential, in applied form. -/
theorem Wc_d_apply_applied (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (n : ℕ)
    (x : ↥((Wc 𝕜 p).C.X n)) (z : ↥((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X (n+1))) :
    cochainFun 𝕜 p n x (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (n+1) n).hom z) =
      cochainFun 𝕜 p (n+1) (((Wc 𝕜 p).d n) x) z := by
  rw [Wc_d_apply 𝕜 p n x]
  rfl

/-- The projection `Kgπ` is a chain map (componentwise form). -/
theorem Kgπ_d (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    (Kgπ 𝕜 p s).f (n+1) ≫ (Kg 𝕜 p s).d (n+1) n =
      ((Work.SSSR.serF 𝕜 (sF p)).obj s).d (n+1) n ≫ (Kgπ 𝕜 p s).f n :=
  (Kgπ 𝕜 p s).comm (n+1) n

/-- The inclusion `inclL` is a chain map (componentwise form). -/
theorem inclL_d (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k n : ℕ) :
    (inclL 𝕜 p k).f (n+1) ≫ (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (n+1) n =
      (Cc 𝕜 p k).d (n+1) n ≫ (inclL 𝕜 p k).f n :=
  (inclL 𝕜 p k).comm (n+1) n

/-! ## The evaluation of a cocycle on the cycles of the graded piece -/

/-- The evaluation of a cycle of the first page on the boundary of a lift. -/
theorem ev_cycles_zero (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n)
    (x : ↥(pZ 𝕜 (Wc 𝕜 p) 1 s n)) (y : ↥((Kg 𝕜 p s).X (n+1))) :
    cochainFun 𝕜 p n x.1 (((inclL 𝕜 p (s+1)).f n).hom
      (grSecX 𝕜 p s n (((Kg 𝕜 p s).d (n+1) n).hom y))) = 0 := by
  set w : ↥((Kg 𝕜 p s).X n) := ((Kg 𝕜 p s).d (n+1) n).hom y with hw
  set y' : ↥((Cc 𝕜 p (s+1)).X (n+1)) := grSecX 𝕜 p s (n+1) y with hy'
  set z₁ : ↥((Cc 𝕜 p (s+1)).X n) := ((Cc 𝕜 p (s+1)).d (n+1) n).hom y' with hz₁
  set z₀ : ↥((Cc 𝕜 p (s+1)).X n) := grSecX 𝕜 p s n w with hz₀
  -- `x` kills the image of the boundary of the lift
  have hz₁zero : cochainFun 𝕜 p n x.1 (((inclL 𝕜 p (s+1)).f n).hom z₁) = 0 := by
    rw [hz₁]
    have hchain : ((inclL 𝕜 p (s+1)).f n).hom
        (((Cc 𝕜 p (s+1)).d (n+1) n).hom y') =
        (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (n+1) n).hom)
          (((inclL 𝕜 p (s+1)).f (n+1)).hom y') := by
      have h := congrArg (fun (g : (Cc 𝕜 p (s+1)).X (n+1) ⟶
          (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X n) => g.hom y')
          (inclL_d 𝕜 p (s+1) n)
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
        LinearMap.comp_apply] at h
      exact h.symm
    rw [hchain]
    have hx3 : ((Wc 𝕜 p).d n) (x.1 : ↥((Wc 𝕜 p).C.X n)) ∈ (Wc 𝕜 p).F (s+1) (n+1) := x.2.2
    have hx3' : ((Wc 𝕜 p).d n) (x.1 : ↥((Wc 𝕜 p).C.X n)) ∈
        compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) (s+1)) (n+1) := by
      rw [← hann (s+1) (n+1)]; exact hx3
    rw [Wc_d_apply_applied 𝕜 p n x.1 (((inclL 𝕜 p (s+1)).f (n+1)).hom y')]
    exact hx3' y'
  -- `Kgπ` of the two lifts
  have hzπ₀ : ((Kgπ 𝕜 p s).f n).hom z₀ = w := Kgπ_grSecX_apply 𝕜 p s n w
  have hzπ₁ : ((Kgπ 𝕜 p s).f n).hom z₁ = w := by
    rw [hz₁]
    have hc := congrArg (fun (g : ((Work.SSSR.serF 𝕜 (sF p)).obj s).X (n+1) ⟶
        (Kg 𝕜 p s).X n) => g.hom y') (Kgπ_d 𝕜 p s n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at hc
    rw [show (((Kgπ 𝕜 p s).f (n+1)).hom y') = y from Kgπ_grSecX_apply 𝕜 p s (n+1) y] at hc
    rw [← hw] at hc
    exact hc.symm
  have hker : ((Kgπ 𝕜 p s).f n).hom (z₀ - z₁) = 0 := by
    rw [map_sub, hzπ₀, hzπ₁, sub_self]
  have hxz : cochainFun 𝕜 p n x.1 (((inclL 𝕜 p (s+1)).f n).hom (z₀ - z₁)) = 0 :=
    ker_Kgπ_inclL_eq_zero 𝕜 p s n hann (cochainFun 𝕜 p n x.1) x.2.1 (z₀ - z₁) hker
  have hsplit : (((inclL 𝕜 p (s+1)).f n).hom z₀ - ((inclL 𝕜 p (s+1)).f n).hom z₁) =
      ((inclL 𝕜 p (s+1)).f n).hom (z₀ - z₁) := (map_sub _ z₀ z₁).symm
  rw [hz₀]
  have hsum : cochainFun 𝕜 p n x.1 (((inclL 𝕜 p (s+1)).f n).hom z₀) =
      cochainFun 𝕜 p n x.1 (((inclL 𝕜 p (s+1)).f n).hom z₁) +
      cochainFun 𝕜 p n x.1 (((inclL 𝕜 p (s+1)).f n).hom (z₀ - z₁)) := by
    rw [← hsplit, map_sub]
    abel
  rw [hsum, hz₁zero, hxz, add_zero]

/-- The underlying functional of `evZ` kills the boundaries. -/
theorem evZ_kill (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n)
    (x : ↥(pZ 𝕜 (Wc 𝕜 p) 1 s n)) :
    Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n ≤
      (((cochainFun 𝕜 p n x.1).comp ((inclL 𝕜 p (s+1)).f n).hom).comp
        ((grSecX 𝕜 p s n).comp (Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n).subtype)).ker := by
  rw [Work.StemsB.fdH]
  refine (LinearMap.range_le_ker_iff).mpr ?_
  ext y
  change cochainFun 𝕜 p n x.1 (((inclL 𝕜 p (s+1)).f n).hom
    (grSecX 𝕜 p s n (((Kg 𝕜 p s).d (n+1) n).hom y))) = 0
  exact ev_cycles_zero 𝕜 p s n hann x y

/-- **The evaluation map on the representatives** of the first page: a cochain `x ∈ Z_1^s` is
evaluated on the cycles of the graded piece `grF ξ.F s`. -/
noncomputable def evZ (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n) :
    ↥(pZ 𝕜 (Wc 𝕜 p) 1 s n) →ₗ[𝕜]
      ((↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n) ⧸ Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n) →ₗ[𝕜] 𝕜) :=
  LinearMap.mk₂ 𝕜
    (fun x => Submodule.liftQ (Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n)
      (((cochainFun 𝕜 p n x.1).comp ((inclL 𝕜 p (s+1)).f n).hom).comp
        ((grSecX 𝕜 p s n).comp (Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n).subtype))
      (evZ_kill 𝕜 p s n hann x))
    (fun x x' => by
      intro w
      obtain ⟨z, rfl⟩ := (Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n).mkQ_surjective w
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply, Submodule.liftQ_apply]
      simp only [LinearMap.comp_apply, LinearMap.add_apply, Submodule.coe_add]
      rfl)
    (fun a x => by
      intro w
      obtain ⟨z, rfl⟩ := (Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n).mkQ_surjective w
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply, Submodule.liftQ_apply]
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_smul]
      rfl)
    (fun x y z => map_add _ y z)
    (fun a x z => map_smul _ a z)

/-- The evaluation of `evZ` on a cycle class. -/
theorem evZ_apply (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n)
    (x : ↥(pZ 𝕜 (Wc 𝕜 p) 1 s n)) (z : ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n)) :
    evZ 𝕜 p s n hann x ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n).mkQ z) =
      cochainFun 𝕜 p n x.1 (((inclL 𝕜 p (s+1)).f n).hom (grSecX 𝕜 p s n z)) := by
  change (Submodule.liftQ (Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n)
      (((cochainFun 𝕜 p n x.1).comp ((inclL 𝕜 p (s+1)).f n).hom).comp
        ((grSecX 𝕜 p s n).comp (Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n).subtype))
      (evZ_kill 𝕜 p s n hann x))
    ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n).mkQ z) = _
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  rfl

/-! ## The page `E_1` as a subquotient of the cocycles -/

/-- `Z_0^{s+1} = F^{s+1}` in the Serre cochain filtration. -/
theorem pZ_zero_eq (𝕜 : Type) [CommRing 𝕜] (W : CohFilt 𝕜) (s n : ℕ) :
    pZ 𝕜 W 0 (s+1) n = W.F (s+1) n := by
  refine le_antisymm inf_le_left ?_
  exact le_inf le_rfl fun x hx => W.F_leib (s+1) n x hx

/-- `B_1^s = d(F^s)`. -/
theorem pB_one_eq (𝕜 : Type) [CommRing 𝕜] (W : CohFilt 𝕜) (s n : ℕ) :
    pB 𝕜 W 1 s n = (W.F s (n-1)).map (W.dPrev n) := by
  match n with
  | 0 =>
      refine le_antisymm inf_le_right ?_
      refine le_inf ?_ le_rfl
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hshape : W.C.d (0-1) 0 = 0 := by
        rw [show (0:ℕ) - 1 = 0 from rfl]
        exact HomologicalComplex.shape W.C 0 0 (by simp [ComplexShape.down])
      rw [CohFilt.dPrev, hshape, ModuleCat.hom_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
  | (k+1) =>
      refine le_antisymm inf_le_right ?_
      refine le_inf ?_ le_rfl
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact W.F_leib s k y hy

/-- The denominator of `E_1^s`: `F^{s+1} + d(F^s)`. -/
theorem pDen_one_eq (𝕜 : Type) [CommRing 𝕜] (W : CohFilt 𝕜) (s n : ℕ) :
    pDen 𝕜 W 1 s n = W.F (s+1) n ⊔ (W.F s (n-1)).map (W.dPrev n) := by
  rw [pDen, show (1:ℕ) - 1 = 0 from rfl, pZ_zero_eq, pB_one_eq]

theorem evZ_eq_zero_of_mem_pDen (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n)
    (x : ↥(pZ 𝕜 (Wc 𝕜 p) 1 s n))
    (hx : (x : ↥((Wc 𝕜 p).C.X n)) ∈ pDen 𝕜 (Wc 𝕜 p) 1 s n) :
    evZ 𝕜 p s n hann x = 0 := by
  match n with
  | 0 =>
      have hbmap : (Wc 𝕜 p).dPrev 0 = 0 := by
        rw [CohFilt.dPrev, show (0:ℕ) - 1 = 0 from rfl]
        exact congrArg ModuleCat.Hom.hom
          (HomologicalComplex.shape (Wc 𝕜 p).C 0 0 (by simp [ComplexShape.up]))
      have hpd : pDen 𝕜 (Wc 𝕜 p) 1 s 0 = (Wc 𝕜 p).F (s+1) 0 := by
        rw [pDen_one_eq, hbmap, Submodule.map_zero, sup_bot_eq]
      rw [hpd] at hx
      apply LinearMap.ext
      intro w
      obtain ⟨z, rfl⟩ := (Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) 0).mkQ_surjective w
      rw [evZ_apply, LinearMap.zero_apply]
      have ha' : (x : ↥((Wc 𝕜 p).C.X 0)) ∈
          compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) (s+1)) 0 := by
        rw [← hann (s+1) 0]; exact hx
      exact ha' (grSecX 𝕜 p s 0 z)
  | (k+1) =>
      have hden : pDen 𝕜 (Wc 𝕜 p) 1 s (k+1) =
          (Wc 𝕜 p).F (s+1) (k+1) ⊔ ((Wc 𝕜 p).F s k).map ((Wc 𝕜 p).d k) := by
        rw [pDen_one_eq]
        rfl
      rw [hden] at hx
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
      obtain ⟨y, hy, rfl⟩ := hb
      apply LinearMap.ext
      intro w
      obtain ⟨z, rfl⟩ := (Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) (k+1)).mkQ_surjective w
      rw [evZ_apply, LinearMap.zero_apply]
      set Wv : ↥((Cc 𝕜 p (s+1)).X (k+1)) :=
        grSecX 𝕜 p s (k+1) (z : ↥((Kg 𝕜 p s).X (k+1))) with hWv
      have hz0 : ((Kg 𝕜 p s).d (k+1) k) (z : ↥((Kg 𝕜 p s).X (k+1))) = 0 := by
        simpa using z.2
      have hy' : y ∈ coFilt 𝕜 (sF p) s k := hy
      have ha' : a ∈ compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) (s+1)) (k+1) := by
        rw [← hann (s+1) (k+1)]; exact ha
      have hπ : ((Kgπ 𝕜 p s).f (k+1)).hom Wv = (z : ↥((Kg 𝕜 p s).X (k+1))) :=
        Kgπ_grSecX_apply 𝕜 p s (k+1) _
      have haz : cochainFun 𝕜 p (k+1) a (((inclL 𝕜 p (s+1)).f (k+1)).hom Wv) = 0 := by
        simpa [cochainFun, inclL, Cc] using ha' Wv
      have hkerv : ((Kgπ 𝕜 p s).f k).hom (((Cc 𝕜 p (s+1)).d (k+1) k).hom Wv) = 0 := by
        have h2 : ((Kg 𝕜 p s).d (k+1) k).hom (((Kgπ 𝕜 p s).f (k+1)).hom Wv)
            = ((Kgπ 𝕜 p s).f k).hom
                ((((Work.SSSR.serF 𝕜 (sF p)).obj s).d (k+1) k).hom Wv) :=
          congrArg (fun (g : ((Work.SSSR.serF 𝕜 (sF p)).obj s).X (k+1) ⟶
            (Kg 𝕜 p s).X k) => g.hom Wv) ((Kgπ 𝕜 p s).comm (k+1) k)
        rw [hπ, hz0] at h2
        exact h2.symm
      have hbz : cochainFun 𝕜 p (k+1) ((Wc 𝕜 p).d k y)
          (((inclL 𝕜 p (s+1)).f (k+1)).hom Wv) = 0 := by
        rw [← Wc_d_apply_applied 𝕜 p k y (((inclL 𝕜 p (s+1)).f (k+1)).hom Wv)]
        have hcomp := congrArg (fun (g : (Cc 𝕜 p (s+1)).X (k+1) ⟶
            (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X k) => g.hom Wv)
            (inclL_d 𝕜 p (s+1) k)
        have hcomp' : (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (k+1) k).hom
            (((inclL 𝕜 p (s+1)).f (k+1)).hom Wv))
            = ((inclL 𝕜 p (s+1)).f k).hom (((Cc 𝕜 p (s+1)).d (k+1) k).hom Wv) := hcomp
        rw [hcomp']
        exact ker_Kgπ_inclL_eq_zero 𝕜 p s k hann (cochainFun 𝕜 p k y) hy'
          (((Cc 𝕜 p (s+1)).d (k+1) k).hom Wv) hkerv
      have hxval : cochainFun 𝕜 p (k+1) (x : ↥((Wc 𝕜 p).C.X (k+1)))
          (((inclL 𝕜 p (s+1)).f (k+1)).hom Wv) =
          cochainFun 𝕜 p (k+1) a (((inclL 𝕜 p (s+1)).f (k+1)).hom Wv) +
          cochainFun 𝕜 p (k+1) ((Wc 𝕜 p).d k y)
            (((inclL 𝕜 p (s+1)).f (k+1)).hom Wv) := by
        rw [← hab]
        rfl
      rw [hxval, haz, hbz, add_zero]

/-- **The evaluation map on the first page.** -/
noncomputable def evS (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n) :
    pEraw 𝕜 (Wc 𝕜 p) 1 s n →ₗ[𝕜]
      ((↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) n) ⧸ Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n) →ₗ[𝕜] 𝕜) :=
  Submodule.liftQ ((pDen 𝕜 (Wc 𝕜 p) 1 s n).comap (pZ 𝕜 (Wc 𝕜 p) 1 s n).subtype)
    (evZ 𝕜 p s n hann) (by
      intro y hy
      rw [LinearMap.mem_ker]
      exact evZ_eq_zero_of_mem_pDen 𝕜 p s n hann y hy)

end

end Work.Pi6.MSS.E1B
