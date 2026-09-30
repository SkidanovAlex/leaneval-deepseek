import Mathlib
import Submission.Work.Pi6.MSS.kunnethDefs
import Submission.Work.StemsB.FieldDualUCT
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Künneth map `H_s(C) ⊗ M ⟶ H_s(C ⊗ M)` over a field

For a chain complex `C` of `𝕜`-vector spaces and a `𝕜`-vector space `M`, the coefficient-unit chain
map `tensUnit C M m : C ⟶ C ⊗ M` (`x ↦ x ⊗ m`) induces the "Künneth" map

`K : H_s(C) ⊗ M ⟶ H_s(C ⊗ M),   [z] ⊗ m ↦ [z ⊗ m]`.

Over a field this map is an isomorphism (the Künneth theorem for a complex with coefficients in a
vector space): tensoring with `M` is exact, so `Z_s(C) ⊗ M = Z_s(C ⊗ M)`,
`B_s(C) ⊗ M = B_s(C ⊗ M)` and `H_s(C ⊗ M) = (Z_s ⊗ M)/(B_s ⊗ M) = H_s(C) ⊗ M`.

This file proves `Work.Pi6.MSS.kunneth_exists`.

The vocabulary of "cycles modulo boundaries" used here is `Work.StemsB.fdZ` / `Work.StemsB.fdH`
(the `n`-cycles `Z_n = ker d_n` of a chain complex of vector spaces and the `n`-boundaries inside
the cycles), together with the canonical isomorphism `homZBIso : H_n ≅ Z_n/B_n`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Pi6.MSS

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## The differential of the coefficient extension -/

/-- The differential of `expTens 𝕜 C M` in arbitrary degrees. -/
theorem expTens_d_eq (𝕜 : Type) [CommRing 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ)
    (M : ModuleCat 𝕜) (i j : ℕ) : (expTens 𝕜 C M).d i j = C.d i j ▷ M := by
  by_cases h : (ComplexShape.down ℕ).Rel i j
  · obtain rfl : j + 1 = i := h
    rw [expTens_d]
  · rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.shape C _ _ h]
    simp

/-! ## The canonical isomorphism `H_n ≅ Z_n ⧸ B_n` -/

/-- The `n`-cycles of `E`, identified with the concrete submodule `Z_n = ker d_n`. -/
noncomputable def cycZIso (𝕜 : Type) [Field 𝕜] (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) :
    E.cycles n ≅ ModuleCat.of 𝕜 ↥(Work.StemsB.fdZ 𝕜 E n) :=
  (E.cyclesIsoSc' (n + 1) n (n - 1) (Work.Cohomology.down_prev n)
      (Work.Cohomology.down_next n)) ≪≫
    ShortComplex.moduleCatCyclesIso (E.sc' (n + 1) n (n - 1))

/-- `cycZIso` is compatible with the inclusions of the cycles. -/
lemma cycZIso_hom_i (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) :
    (cycZIso 𝕜 E n).hom ≫
        (ShortComplex.moduleCatLeftHomologyData (E.sc' (n + 1) n (n - 1))).i = E.iCycles n := by
  rw [cycZIso, Iso.trans_hom, Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- `cycZIso` does not change the underlying element of the complex. -/
lemma cycZIso_hom_val (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) (c : ↥(E.cycles n)) :
    ((cycZIso 𝕜 E n).hom c : ↥(E.X n)) = (E.iCycles n).hom c := by
  have h := congrArg (fun (m : E.cycles n ⟶ E.X n) => ModuleCat.Hom.hom m c)
    (cycZIso_hom_i (𝕜 := 𝕜) (E := E) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- **The canonical isomorphism `H_n ≅ Z_n ⧸ B_n`** for a chain complex of vector spaces: the
composite of the identification of the homology with the homology of the short complex
`E_{n+1} → E_n → E_{n-1}` and the explicit description of that homology. -/
noncomputable def homZBIso (𝕜 : Type) [Field 𝕜] (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) :
    E.homology n ≅ ModuleCat.of 𝕜 (↥(Work.StemsB.fdZ 𝕜 E n) ⧸ Work.StemsB.fdH 𝕜 E n) :=
  (E.homologyIsoSc' (n + 1) n (n - 1) (Work.Cohomology.down_prev n)
      (Work.Cohomology.down_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso (E.sc' (n + 1) n (n - 1))

/-- The projection of the left homology data of `E.sc' (n+1) n (n-1)` is the quotient map onto
`Z_n ⧸ B_n`. -/
lemma LHD_pi_eq (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) :
    (ShortComplex.moduleCatLeftHomologyData (E.sc' (n + 1) n (n - 1))).π
      = ModuleCat.ofHom ((Work.StemsB.fdH 𝕜 E n).mkQ) := by
  rw [ModuleCat.hom_ext_iff, ShortComplex.moduleCatLeftHomologyData_π_hom]
  rfl

/-- `homZBIso` is the composite of the identification of the abstract cycles with `Z_n` and the
quotient map onto `Z_n ⧸ B_n`. -/
lemma homZBIso_comp (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) :
    (E.homologyπ n) ≫ (homZBIso 𝕜 E n).hom
      = (cycZIso 𝕜 E n).hom ≫ ModuleCat.ofHom ((Work.StemsB.fdH 𝕜 E n).mkQ) := by
  simp only [homZBIso, Iso.trans_hom, Category.assoc, cycZIso,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.π_moduleCatCyclesIso_hom]
  rw [LHD_pi_eq (𝕜 := 𝕜) (E := E) n]

/-- **The computation rule for `homZBIso`**: the homology class of a cycle is the class of the same
element of `Z_n ⧸ B_n`. -/
lemma homZBIso_apply (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) (c : ↥(E.cycles n)) :
    (homZBIso 𝕜 E n).hom.hom ((E.homologyπ n).hom c)
      = (Work.StemsB.fdH 𝕜 E n).mkQ ((cycZIso 𝕜 E n).hom c) := by
  have h := congrArg (fun (m : E.cycles n ⟶
      ModuleCat.of 𝕜 (↥(Work.StemsB.fdZ 𝕜 E n) ⧸ Work.StemsB.fdH 𝕜 E n)) =>
      ModuleCat.Hom.hom m c) (homZBIso_comp (𝕜 := 𝕜) (E := E) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] using h

/-! ## The concrete maps induced by a chain map -/

/-- The concrete map on the cycles `Z_n` induced by a chain map. -/
noncomputable def cycMap {K L : ChainComplex (ModuleCat 𝕜) ℕ} (φ : K ⟶ L) (n : ℕ) :
    ↥(Work.StemsB.fdZ 𝕜 K n) →ₗ[𝕜] ↥(Work.StemsB.fdZ 𝕜 L n) where
  toFun z := ⟨(φ.f n).hom z, by
    have h := congrArg (fun (m : K.X n ⟶ L.X (n - 1)) => (ModuleCat.Hom.hom m) (z : ↥(K.X n)))
      (HomologicalComplex.Hom.comm φ n (n - 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    show (L.d n (n - 1)).hom ((φ.f n).hom (z : ↥(K.X n))) = 0
    rw [h, z.2, map_zero]⟩
  map_add' z z' := by ext; simp
  map_smul' a z := by ext; simp

lemma cycMap_val {K L : ChainComplex (ModuleCat 𝕜) ℕ} (φ : K ⟶ L) (n : ℕ)
    (z : ↥(Work.StemsB.fdZ 𝕜 K n)) :
    ((cycMap φ n z : ↥(Work.StemsB.fdZ 𝕜 L n)) : ↥(L.X n)) =
      (φ.f n).hom (z : ↥(K.X n)) := rfl

/-- The concrete map on the quotients `Z_n ⧸ B_n` induced by a chain map. -/
noncomputable def cycQuotMap {K L : ChainComplex (ModuleCat 𝕜) ℕ} (φ : K ⟶ L) (n : ℕ) :
    (↥(Work.StemsB.fdZ 𝕜 K n) ⧸ Work.StemsB.fdH 𝕜 K n) →ₗ[𝕜]
      (↥(Work.StemsB.fdZ 𝕜 L n) ⧸ Work.StemsB.fdH 𝕜 L n) :=
  (Work.StemsB.fdH 𝕜 K n).liftQ
    ((Work.StemsB.fdH 𝕜 L n).mkQ ∘ₗ cycMap φ n) (by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Work.StemsB.mem_fdH]
      have hx' : (x : ↥(K.X n)) ∈ Work.StemsB.fdB 𝕜 K n := (Work.StemsB.mem_fdH 𝕜 K n x).1 hx
      rw [Work.StemsB.fdB] at hx'
      obtain ⟨w, hw⟩ := hx'
      refine ⟨(φ.f (n + 1)).hom w, ?_⟩
      have h := congrArg (fun (m : K.X (n + 1) ⟶ L.X n) => (ModuleCat.Hom.hom m) w)
        (HomologicalComplex.Hom.comm φ (n + 1) n)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      rw [h, hw, cycMap_val])

lemma cycQuotMap_mkQ {K L : ChainComplex (ModuleCat 𝕜) ℕ} (φ : K ⟶ L) (n : ℕ)
    (z : ↥(Work.StemsB.fdZ 𝕜 K n)) :
    cycQuotMap φ n ((Work.StemsB.fdH 𝕜 K n).mkQ z) =
      (Work.StemsB.fdH 𝕜 L n).mkQ (cycMap φ n z) := by
  simp only [cycQuotMap, Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply]

/-! ## Naturality of the concrete homology description

The following lemmas show that `homZBIso` is natural with respect to the map induced by a chain map,
where the induced map on `Z_n ⧸ B_n` is the concrete map `cycQuotMap`.  (Proved in parallel by a
colleague as `Work.Pi6.MSS.homZBIso_homologyMap`; reproduced here so that this file is
self-contained.)
-/

/-- The identification `cycZIso : cycles n ≅ Z_n` is natural, and it transports the abstract map
`cyclesMap φ n` on the cycles to the concrete map `cycMap φ n` on the submodules `Z_n`. -/
lemma cycZIso_cyclesMap' {K L : ChainComplex (ModuleCat 𝕜) ℕ} (φ : K ⟶ L) (n : ℕ) :
    HomologicalComplex.cyclesMap φ n ≫ (cycZIso 𝕜 L n).hom =
      (cycZIso 𝕜 K n).hom ≫ ModuleCat.ofHom (cycMap φ n) := by
  rw [ModuleCat.hom_ext_iff]
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  apply Subtype.ext
  rw [cycZIso_hom_val, cycMap_val]
  have h := congrArg (fun (m : K.cycles n ⟶ L.X n) => (ModuleCat.Hom.hom m) c)
    (HomologicalComplex.cyclesMap_i φ n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, cycZIso_hom_val]

/-- The concrete map induced on the quotients `Z_n ⧸ B_n` by a chain map is the map induced on the
quotients by the concrete map on the cycles: `cycQuotMap φ n ∘ mkQ = mkQ ∘ cycMap φ n`. -/
lemma mkQ_cycQuotMap' {K L : ChainComplex (ModuleCat 𝕜) ℕ} (φ : K ⟶ L) (n : ℕ) :
    ModuleCat.ofHom ((Work.StemsB.fdH 𝕜 K n).mkQ) ≫ ModuleCat.ofHom (cycQuotMap φ n) =
      ModuleCat.ofHom (cycMap φ n) ≫ ModuleCat.ofHom ((Work.StemsB.fdH 𝕜 L n).mkQ) := by
  rw [ModuleCat.hom_ext_iff, ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    ModuleCat.hom_ofHom]
  apply LinearMap.ext
  intro z
  exact cycQuotMap_mkQ φ n z

/-- `homZBIso` is natural with respect to the maps induced by a chain map, where the map on the
right hand side is the concrete map `cycQuotMap φ n` on `Z_n ⧸ B_n`. -/
theorem homZBIso_homologyMap' {𝕜 : Type} [Field 𝕜] {K L : ChainComplex (ModuleCat 𝕜) ℕ}
    (φ : K ⟶ L) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap φ n)
        (Work.Pi6.MSS.homZBIso 𝕜 L n).hom =
      CategoryTheory.CategoryStruct.comp (Work.Pi6.MSS.homZBIso 𝕜 K n).hom
        (ModuleCat.ofHom (Work.Pi6.MSS.cycQuotMap φ n)) := by
  apply (cancel_epi (HomologicalComplex.homologyπ K n)).mp
  conv_lhs =>
    rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
      Work.Pi6.MSS.homZBIso_comp, ← Category.assoc, cycZIso_cyclesMap']
  conv_rhs =>
    rw [← Category.assoc, Work.Pi6.MSS.homZBIso_comp, Category.assoc, mkQ_cycQuotMap',
      ← Category.assoc]

/-! ## The cycles and boundaries of `C ⊗ M`

Over a field, tensoring with `M` is exact, so `Z_s(C) ⊗ M = Z_s(C ⊗ M)` and
`B_s(C) ⊗ M = B_s(C ⊗ M)`: the canonical elementwise map `z ⊗ m ↦ z ⊗ m` is a linear equivalence
identifying the cycles, and it carries the boundaries inside the cycles onto the boundaries.
-/

/-- **The cycles and the boundaries of `expTens 𝕜 C M`**: the canonical map `z ⊗ m ↦ z ⊗ m` is a
linear equivalence `Z_s(C) ⊗ M ≃ Z_s(C ⊗ M)` which carries `B_s(C) ⊗ M` onto `B_s(C ⊗ M)`. -/
theorem expTens_fdZ_tens_iso (𝕜 : Type) [Field 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ)
    (M : ModuleCat 𝕜) (s : ℕ) :
    ∃ e : TensorProduct 𝕜 ↥(Work.StemsB.fdZ 𝕜 C s) ↥M ≃ₗ[𝕜]
        ↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s),
      (∀ (z : ↥(Work.StemsB.fdZ 𝕜 C s)) (m : ↥M),
        ((e (z ⊗ₜ[𝕜] m) : ↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s)) :
            ↥((expTens 𝕜 C M).X s)) = (z : ↥(C.X s)) ⊗ₜ[𝕜] m) ∧
      (LinearMap.range ((Work.StemsB.fdH 𝕜 C s).subtype.rTensor ↥M)).map
          (e : TensorProduct 𝕜 ↥(Work.StemsB.fdZ 𝕜 C s) ↥M →ₗ[𝕜]
            ↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s)) =
        Work.StemsB.fdH 𝕜 (expTens 𝕜 C M) s := by
  have hker : LinearMap.ker ((C.d s (s - 1)).hom.rTensor ↥M) =
      LinearMap.range ((Work.StemsB.fdZ 𝕜 C s).subtype.rTensor ↥M) :=
    LinearMap.exact_iff.mp (Module.Flat.rTensor_exact ↥M
      (LinearMap.exact_subtype_ker_map ((C.d s (s - 1)).hom)))
  have hfdZ : Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s =
      LinearMap.ker ((C.d s (s - 1)).hom.rTensor ↥M) := by
    rw [Work.StemsB.fdZ, expTens_d_eq 𝕜 C M s (s - 1), ModuleCat.hom_whiskerRight]
  let ψ : ↥(Work.StemsB.fdZ 𝕜 C s) ⊗[𝕜] ↥M →ₗ[𝕜] ↥(C.X s) ⊗[𝕜] ↥M :=
    (Work.StemsB.fdZ 𝕜 C s).subtype.rTensor ↥M
  have hψ : LinearMap.range ψ = Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s := hker.symm.trans hfdZ.symm
  let ψ' : ↥(Work.StemsB.fdZ 𝕜 C s) ⊗[𝕜] ↥M →ₗ[𝕜]
      ↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s) :=
    ψ.codRestrict _ (fun x => hψ ▸ LinearMap.mem_range_self ψ x)
  have hinj : Function.Injective ψ' := by
    intro a b hab
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥M) _
      (fun _ _ h => Subtype.ext h) (congrArg Subtype.val hab : ψ a = ψ b)
  have hsurj : Function.Surjective ψ' := by
    intro y
    have hy : ((y : ↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s)) : ↥(C.X s) ⊗[𝕜] ↥M) ∈
        LinearMap.range ψ := by
      rw [hψ]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let e : ↥(Work.StemsB.fdZ 𝕜 C s) ⊗[𝕜] ↥M ≃ₗ[𝕜]
      ↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s) := LinearEquiv.ofBijective ψ' ⟨hinj, hsurj⟩
  have he_val : ∀ x, ((e x : ↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s)) :
      ↥((expTens 𝕜 C M).X s)) = ψ x := by
    intro x
    show ((ψ' x : ↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s)) : ↥((expTens 𝕜 C M).X s)) = ψ x
    rfl
  let g : ↥(C.X (s + 1)) →ₗ[𝕜] ↥(Work.StemsB.fdZ 𝕜 C s) :=
    ((C.d (s + 1) s).hom).codRestrict (Work.StemsB.fdZ 𝕜 C s) (fun x => by
      show (C.d s (s - 1)).hom ((C.d (s + 1) s).hom x) = 0
      have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d C (s + 1) s (s - 1))
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      exact LinearMap.congr_fun h x)
  have hg : LinearMap.range g = Work.StemsB.fdH 𝕜 C s := rfl
  let gD : ↥((expTens 𝕜 C M).X (s + 1)) →ₗ[𝕜]
      ↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s) :=
    (((expTens 𝕜 C M).d (s + 1) s).hom).codRestrict
      (Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s) (fun x => by
        show ((expTens 𝕜 C M).d s (s - 1)).hom (((expTens 𝕜 C M).d (s + 1) s).hom x) = 0
        have h := congrArg ModuleCat.Hom.hom
          (HomologicalComplex.d_comp_d (expTens 𝕜 C M) (s + 1) s (s - 1))
        simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
        exact LinearMap.congr_fun h x)
  have hgD : LinearMap.range gD = Work.StemsB.fdH 𝕜 (expTens 𝕜 C M) s := rfl
  have hcomp : (e : ↥(Work.StemsB.fdZ 𝕜 C s) ⊗[𝕜] ↥M →ₗ[𝕜]
        ↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s)).comp (g.rTensor ↥M) = gD := by
    refine TensorProduct.ext' (fun a b => ?_)
    apply Subtype.ext
    rw [LinearMap.comp_apply,
      show ((e : ↥(Work.StemsB.fdZ 𝕜 C s) ⊗[𝕜] ↥M →ₗ[𝕜]
          ↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s)) ((LinearMap.rTensor ↥M g) (a ⊗ₜ[𝕜] b))) =
        e ((LinearMap.rTensor ↥M g) (a ⊗ₜ[𝕜] b)) from rfl,
      he_val, show ψ = (Work.StemsB.fdZ 𝕜 C s).subtype.rTensor ↥M from rfl,
      LinearMap.rTensor_tmul, LinearMap.codRestrict_apply,
      expTens_d_eq 𝕜 C M (s + 1) s, ModuleCat.hom_whiskerRight, LinearMap.rTensor_tmul]
    rfl
  refine ⟨e, ?_, ?_⟩
  · intro z m
    rw [he_val]
    show ψ (z ⊗ₜ[𝕜] m) = (z : ↥(C.X s)) ⊗ₜ[𝕜] m
    rw [show ψ = (Work.StemsB.fdZ 𝕜 C s).subtype.rTensor ↥M from rfl, LinearMap.rTensor_tmul]
    rfl
  · have hA : LinearMap.range ((Work.StemsB.fdH 𝕜 C s).subtype.rTensor ↥M) =
        LinearMap.range (g.rTensor ↥M) := by
      rw [hg.symm]
      exact (LinearMap.rTensor_range (Q := ↥M) (g := g)).symm
    rw [hA, ← LinearMap.range_comp (f := g.rTensor ↥M)
      (g := (e : ↥(Work.StemsB.fdZ 𝕜 C s) ⊗[𝕜] ↥M →ₗ[𝕜]
        ↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s))), hcomp, hgD]

/-- **Naturality of `homZBIso`, elementwise form**: the class of a cycle is sent to the class of
its image. -/
theorem homZBIso_homologyMap_apply {𝕜 : Type} [Field 𝕜] {K L : ChainComplex (ModuleCat 𝕜) ℕ}
    (φ : K ⟶ L) (n : ℕ) (x : ↥(K.homology n)) (z : ↥(Work.StemsB.fdZ 𝕜 K n))
    (hx : (homZBIso 𝕜 K n).hom.hom x = (Work.StemsB.fdH 𝕜 K n).mkQ z) :
    (homZBIso 𝕜 L n).hom.hom ((HomologicalComplex.homologyMap φ n).hom x)
      = (Work.StemsB.fdH 𝕜 L n).mkQ (cycMap φ n z) := by
  have h := congrArg (fun (m : K.homology n ⟶
      ModuleCat.of 𝕜 (↥(Work.StemsB.fdZ 𝕜 L n) ⧸ Work.StemsB.fdH 𝕜 L n)) =>
      ModuleCat.Hom.hom m x) (homZBIso_homologyMap' (𝕜 := 𝕜) φ n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  rw [h, hx, cycQuotMap_mkQ]

/-! ## The Künneth isomorphism -/

theorem kunneth_exists (𝕜 : Type) [Field 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ)
    (M : ModuleCat 𝕜) (s : ℕ) :
    ∃ K : TensorProduct 𝕜 ↥(C.homology s) ↥M →ₗ[𝕜] ↥((Work.Pi6.MSS.expTens 𝕜 C M).homology s),
      (∀ m : M, K ∘ₗ (TensorProduct.mk 𝕜 ↥(C.homology s) ↥M).flip m
          = (HomologicalComplex.homologyMap (Work.Pi6.MSS.tensUnit C M m) s).hom) ∧
      Function.Bijective K := by
  obtain ⟨e, he, hH⟩ := expTens_fdZ_tens_iso 𝕜 C M s
  let Φ : (TensorProduct 𝕜 (↥(Work.StemsB.fdZ 𝕜 C s) ⧸ Work.StemsB.fdH 𝕜 C s) ↥M) ≃ₗ[𝕜]
      (↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s) ⧸
        Work.StemsB.fdH 𝕜 (expTens 𝕜 C M) s) :=
    (TensorProduct.quotientTensorEquiv ↥M (Work.StemsB.fdH 𝕜 C s)).trans
      (Submodule.Quotient.equiv _ _ e hH)
  have hΦ : ∀ (z : ↥(Work.StemsB.fdZ 𝕜 C s)) (m : ↥M),
      Φ ((Work.StemsB.fdH 𝕜 C s).mkQ z ⊗ₜ[𝕜] m) =
        (Work.StemsB.fdH 𝕜 (expTens 𝕜 C M) s).mkQ (e (z ⊗ₜ[𝕜] m)) := by
    intro z m
    simp only [Φ, LinearEquiv.trans_apply, TensorProduct.quotientTensorEquiv_apply_tmul_mk,
      Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
    rfl
  let eC : ↥(C.homology s) ≃ₗ[𝕜]
      (↥(Work.StemsB.fdZ 𝕜 C s) ⧸ Work.StemsB.fdH 𝕜 C s) := (homZBIso 𝕜 C s).toLinearEquiv
  let eD : ↥((expTens 𝕜 C M).homology s) ≃ₗ[𝕜]
      (↥(Work.StemsB.fdZ 𝕜 (expTens 𝕜 C M) s) ⧸
        Work.StemsB.fdH 𝕜 (expTens 𝕜 C M) s) :=
    (homZBIso 𝕜 (expTens 𝕜 C M) s).toLinearEquiv
  let Kel : (TensorProduct 𝕜 ↥(C.homology s) ↥M) ≃ₗ[𝕜] ↥((expTens 𝕜 C M).homology s) :=
    ((LinearEquiv.rTensor ↥M eC).trans Φ).trans eD.symm
  have hKel : ∀ (x : ↥(C.homology s)) (m : ↥M),
      Kel (x ⊗ₜ[𝕜] m) = eD.symm (Φ (eC x ⊗ₜ[𝕜] m)) := by
    intro x m
    rw [show Kel (x ⊗ₜ[𝕜] m) =
        eD.symm (Φ ((LinearEquiv.rTensor ↥M eC) (x ⊗ₜ[𝕜] m))) from rfl,
      LinearEquiv.rTensor_tmul]
  refine ⟨Kel.toLinearMap, ?_, ?_⟩
  · intro m
    apply LinearMap.ext
    intro x
    have hflip : ((TensorProduct.mk 𝕜 ↥(C.homology s) ↥M).flip m) x = x ⊗ₜ[𝕜] m := by
      rw [LinearMap.flip_apply, TensorProduct.mk_apply]
    obtain ⟨z, hz⟩ := (Work.StemsB.fdH 𝕜 C s).mkQ_surjective (eC x)
    have hφ := homZBIso_homologyMap_apply (𝕜 := 𝕜) (K := C) (L := expTens 𝕜 C M)
      (φ := tensUnit C M m) s x z
      (show (homZBIso 𝕜 C s).hom.hom x = (Work.StemsB.fdH 𝕜 C s).mkQ z from hz.symm)
    have hez : e (z ⊗ₜ[𝕜] m) = cycMap (tensUnit C M m) s z := by
      apply Subtype.ext
      rw [he z m, cycMap_val]
      rfl
    show Kel.toLinearMap (((TensorProduct.mk 𝕜 ↥(C.homology s) ↥M).flip m) x) =
      (HomologicalComplex.homologyMap (tensUnit C M m) s).hom x
    rw [hflip, LinearEquiv.coe_toLinearMap, hKel, ← hz, hΦ, hez]
    rw [← hφ]
    exact LinearEquiv.symm_apply_apply eD _
  · exact Kel.bijective

end

end Work.Pi6.MSS
