/-
# The boundary (`k = 0`) comparison of the degree shift, over `ℚ`

`Work.Serre.MVShift.shK K n` is the degree-`n` shift of a `ℕ`-indexed cochain complex of
`ℚ`-modules (the restriction of `K` along the shape embedding `k ↦ k + n`), and
`Work.Serre.MVShift.shK_homologyIso` identifies the `k`-th homology of `shK K n` with `K.homology
(k+n)` in the *interior* `k ≥ 1`.  At the boundary `k = 0` the object `(shK K n).homology 0` is
the module of `0`-cycles of the shifted complex, i.e. the `n`-cycles of `K` (there is no incoming
differential), and the natural comparison with `K.homology (0+n) = K.homology n` forgets the
boundaries.

This file is the `ℚ`-coefficient port of the `ℤ`-coefficient file
`Submission/Work/Thom/shS_delta_comm_zero.lean` (together with the definitions of
`Work.Thom.shK_homologyZero`, `Work.Thom.shK_cyclesZeroTo` from `Submission/Work/Thom/cupSESChain.lean`).
It supplies:

* `Work.Serre.MVShift.shK_homologyZero`, the boundary comparison
  `(shK K n).homology 0 ⟶ K.homology (0+n)`;
* `shK_homologyZero_spec` (its defining property on cycles), `shK_homologyZero_natural` (its
  naturality in `K`) and `shS_delta_comm_zero` (the `k = 0` case of `shS_delta_comm`: the
  connecting map of the shifted short exact sequence in degrees `0 → 1`, read through the
  restriction isomorphisms, is the connecting map of the original one in degrees `n → n+1`).

The target `Work.Serre.MVShift.shKZeroRat` assembles these three properties into the single
dependent comparison `z : ∀ K, (shK K n).homology 0 ⟶ K.homology (0+n)` used by the rational
Mayer--Vietoris analysis of `Work.Serre.mvDelta`.
-/
import Mathlib
import Submission.Work.Serre.MVShift.ShQ
import Submission.Work.Cohomology.Endgame.dshDelta

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.MVShift

/-! ## The boundary comparison on opcycles -/

/-- The boundary comparison `(shK K n).opcycles 0 ⟶ K.opcycles (0+n)`: the projection of the
`0`-th opcycles of the shifted complex (which is the `n`-th degree of `K`) onto the `(0+n)`-th
opcycles of `K`. -/
noncomputable def shK_opcyclesZero (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (shK K n).opcycles 0 ⟶ K.opcycles (0+n) :=
  (shK K n).descOpcycles (K.pOpcycles (0+n)) 0
    (by simp [ComplexShape.prev])
    (by rw [shK_d]; exact K.d_pOpcycles (0+n) (0+n))

/-- The defining property of the boundary comparison on opcycles. -/
theorem shK_opcyclesZero_pOpcycles (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (shK K n).pOpcycles 0 ≫ shK_opcyclesZero K n = K.pOpcycles (0+n) :=
  (shK K n).p_descOpcycles _ 0 _ _

/-! ## Transport of the comparisons along an equality of the degrees

The objects `K.cycles j`, `K.opcycles j`, `K.homology j` depend on the degree `j`, and `eqToHom`
along an equality `j = j'` of degrees is compatible with `cyclesMap`, `homologyMap`, `homologyπ`
and `opcyclesToCycles`. -/

theorem shKZero_cyclesMap_congr {K L : CochainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) {j j' : ℕ}
    (h : j = j') :
    CategoryTheory.eqToHom (congrArg (fun m => K.cycles m) h) ≫ HomologicalComplex.cyclesMap φ j'
      = HomologicalComplex.cyclesMap φ j
        ≫ CategoryTheory.eqToHom (congrArg (fun m => L.cycles m) h) := by
  cases h; simp

theorem shKZero_homologyMap_congr {K L : CochainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) {j j' : ℕ}
    (h : j = j') :
    CategoryTheory.eqToHom (congrArg (fun m => K.homology m) h)
        ≫ HomologicalComplex.homologyMap φ j'
      = HomologicalComplex.homologyMap φ j
        ≫ CategoryTheory.eqToHom (congrArg (fun m => L.homology m) h) := by
  cases h; simp

theorem shKZero_homologyπ_congr (K : CochainComplex (ModuleCat ℚ) ℕ) {j j' : ℕ} (h : j = j') :
    CategoryTheory.eqToHom (congrArg (fun m => K.cycles m) h) ≫ HomologicalComplex.homologyπ K j'
      = HomologicalComplex.homologyπ K j
        ≫ CategoryTheory.eqToHom (congrArg (fun m => K.homology m) h) := by
  cases h; simp

theorem shKZero_opcyclesToCycles_congr (K : CochainComplex (ModuleCat ℚ) ℕ) {a b b' : ℕ}
    (hb : b' = b) :
    HomologicalComplex.opcyclesToCycles K a b
      = HomologicalComplex.opcyclesToCycles K a b'
        ≫ CategoryTheory.eqToHom (congrArg (fun m => K.cycles m) hb) := by
  cases hb; simp

/-! ## The boundary comparison `(shK K n).homology 0 ⟶ K.homology n`

The restriction isomorphism `shK_homologyIso` compares `(shK K n).homology k` with `K.homology
(k+n)` only for `k ≥ 1`.  At the boundary `k = 0` the object `(shK K n).homology 0` is the module
of cycles of `K` in degree `n` (there is no incoming differential), and the natural map to
`K.homology n` is the projection forgetting the boundaries. -/

/-- The comparison `(shK K n).cycles 0 ⟶ K.cycles (0+n)` (the cycles of the shifted complex in
degree `0` are the cycles of `K` in degree `n`). -/
noncomputable def shK_cyclesZeroTo (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (shK K n).cycles 0 ⟶ K.cycles (0+n) :=
  (K.restrictionCyclesIso (shEmb n) 0 1
    (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel 0 1 from rfl)) rfl rfl
    (show (ComplexShape.up ℕ).next (0+n) = (1:ℕ)+n from
      ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (0+n) ((1:ℕ)+n) from by
        change 0 + n + 1 = 1 + n
        omega))).hom

/-- `shK_cyclesZeroTo` is the degree-`0` case of the cycles isomorphism of the shift. -/
theorem shK_cyclesZeroTo_eq (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    shK_cyclesZeroTo K n = (shK_cyclesIso K n 0).hom := rfl

/-- The boundary comparison `(shK K n).homology 0 ⟶ K.homology (0+n)`: the class of a `0`-cycle
of the shifted complex (i.e. of a cycle of `K` in degree `n`) in `H^n(K)`. -/
noncomputable def shK_homologyZero (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (shK K n).homology 0 ⟶ K.homology (0+n) :=
  ((shK K n).sc 0).descHomology (shK_cyclesZeroTo K n ≫ K.homologyπ (0+n)) (by
    have hprev : (ComplexShape.up ℕ).prev 0 = 0 := by simp [ComplexShape.prev]
    have hSf : ((shK K n).sc 0).f = 0 := by
      show (shK K n).d ((ComplexShape.up ℕ).prev 0) 0 = 0
      rw [hprev]
      exact (shK K n).shape 0 0 (by simp [ComplexShape.up_Rel])
    have hto : ((shK K n).sc 0).toCycles = 0 := by
      refine (cancel_mono ((shK K n).sc 0).iCycles).mp ?_
      rw [ShortComplex.toCycles_i, hSf, zero_comp]
    rw [hto, zero_comp])

/-- The defining property of the boundary comparison. -/
theorem shK_homologyZero_spec (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (shK K n).homologyπ 0 ≫ shK_homologyZero K n
      = shK_cyclesZeroTo K n ≫ K.homologyπ (0+n) := by
  show ((shK K n).sc 0).homologyπ ≫ shK_homologyZero K n = _
  rw [shK_homologyZero]
  exact ShortComplex.π_descHomology (S := (shK K n).sc 0) (A := K.homology (0+n))
    (shK_cyclesZeroTo K n ≫ K.homologyπ (0+n)) _

/-- The defining property of the boundary comparison, in the form in which it is compared with
the interior isomorphism `shK_cyclesIso _ n 0`. -/
theorem shK_homologyZero_spec' (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (shK K n).homologyπ 0 ≫ shK_homologyZero K n
      = (shK_cyclesIso K n 0).hom ≫ K.homologyπ (0+n) := by
  rw [shK_homologyZero_spec, shK_cyclesZeroTo_eq]

/-! ## Naturality of the comparisons -/

/-- Naturality of `shK_homologyZero` with respect to `homologyMap`. -/
theorem shK_homologyZero_natural {K L : CochainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (n : ℕ) :
    shK_homologyZero K n ≫ HomologicalComplex.homologyMap φ (0+n)
      = HomologicalComplex.homologyMap (shMap φ n) 0 ≫ shK_homologyZero L n := by
  have hk0 : (ComplexShape.up ℕ).next 0 = 1 := ComplexShape.next_eq' _
    (by simp [ComplexShape.up_Rel])
  have hkS : (ComplexShape.up ℕ).next (0+n) = 1+n :=
    ComplexShape.next_eq' _ (by simp [ComplexShape.up_Rel]; omega)
  rw [← cancel_epi ((shK K n).homologyπ 0)]
  conv_lhs => rw [← Category.assoc, shK_homologyZero_spec, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  conv_rhs => rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
    shK_homologyZero_spec, ← Category.assoc]
  rw [show shK_cyclesZeroTo K n = (K.restrictionCyclesIso (shEmb n) 0 1 hk0
      (j' := 0+n) (k' := 1+n) rfl rfl hkS).hom from rfl]
  rw [show shK_cyclesZeroTo L n = (L.restrictionCyclesIso (shEmb n) 0 1 hk0
      (j' := 0+n) (k' := 1+n) rfl rfl hkS).hom from rfl]
  rw [Work.Cohomology.restrictionCyclesIso_natural (e := shEmb n) (φ := φ) 0 1 hk0
    (j' := 0+n) (k' := 1+n) rfl rfl hkS]

/-- Naturality of `shK_opcyclesZero` with respect to `opcyclesMap`. -/
theorem shK_opcyclesZero_natural {K L : CochainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (n : ℕ) :
    shK_opcyclesZero K n ≫ HomologicalComplex.opcyclesMap φ (0+n)
      = HomologicalComplex.opcyclesMap (shMap φ n) 0 ≫ shK_opcyclesZero L n := by
  rw [← cancel_epi ((shK K n).pOpcycles 0)]
  rw [← Category.assoc, shK_opcyclesZero_pOpcycles]
  rw [HomologicalComplex.p_opcyclesMap]
  rw [HomologicalComplex.p_opcyclesMap_assoc]
  rw [shK_opcyclesZero_pOpcycles]
  rfl

/-! ## Compatibility with `iCycles`, `toCycles` and with the snake diagram's internal maps -/

theorem shK_cyclesZeroTo_iCycles (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    shK_cyclesZeroTo K n ≫ K.iCycles (0+n) = (shK K n).iCycles 0 := by
  have hk0 : (ComplexShape.up ℕ).next 0 = 1 := ComplexShape.next_eq' _
    (by simp [ComplexShape.up_Rel])
  have hkS : (ComplexShape.up ℕ).next (0+n) = 1+n :=
    ComplexShape.next_eq' _ (by simp [ComplexShape.up_Rel]; omega)
  rw [show shK_cyclesZeroTo K n = (K.restrictionCyclesIso (shEmb n) 0 1 hk0
      (j' := 0+n) (k' := 1+n) rfl rfl hkS).hom from rfl]
  rw [HomologicalComplex.restrictionCyclesIso_hom_iCycles]
  simp [HomologicalComplex.restrictionXIso]

theorem shK_cyclesIso_iCycles (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (shK_cyclesIso K n 1).hom ≫ K.iCycles (1+n) = (shK K n).iCycles 1 := by
  have hk1 : (ComplexShape.up ℕ).next 1 = 1+1 := ComplexShape.next_eq' _
    (by simp [ComplexShape.up_Rel])
  have hkS : (ComplexShape.up ℕ).next (1+n) = (1+1)+n :=
    ComplexShape.next_eq' _ (by simp [ComplexShape.up_Rel]; omega)
  rw [show (shK_cyclesIso K n 1).hom = (K.restrictionCyclesIso (shEmb n) 1 (1+1) hk1
      (j' := 1+n) (k' := (1+1)+n) rfl rfl hkS).hom from rfl]
  rw [HomologicalComplex.restrictionCyclesIso_hom_iCycles]
  simp [HomologicalComplex.restrictionXIso]

theorem shK_toCycles_cyclesIso (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    K.toCycles (0+n) (1+n) = (shK K n).toCycles 0 1 ≫ (shK_cyclesIso K n 1).hom := by
  rw [← cancel_mono (K.iCycles (1+n))]
  rw [HomologicalComplex.toCycles_i, Category.assoc, shK_cyclesIso_iCycles,
    HomologicalComplex.toCycles_i]
  rfl

theorem shK_opcyclesZero_opcyclesToCycles (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    shK_opcyclesZero K n ≫ K.opcyclesToCycles (0+n) (1+n)
      = (shK K n).opcyclesToCycles 0 1 ≫ (shK_cyclesIso K n 1).hom := by
  rw [← cancel_epi ((shK K n).pOpcycles 0)]
  conv_lhs => rw [← Category.assoc, shK_opcyclesZero_pOpcycles,
    HomologicalComplex.pOpcycles_opcyclesToCycles]
  conv_rhs => rw [← Category.assoc, HomologicalComplex.pOpcycles_opcyclesToCycles]
  rw [shK_toCycles_cyclesIso]

theorem shK_homologyZero_homologyι (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    shK_homologyZero K n ≫ K.homologyι (0+n)
      = (shK K n).homologyι 0 ≫ shK_opcyclesZero K n := by
  rw [← cancel_epi ((shK K n).homologyπ 0)]
  conv_lhs => rw [← Category.assoc, shK_homologyZero_spec, Category.assoc,
    HomologicalComplex.homology_π_ι, ← Category.assoc]
  conv_rhs => rw [← Category.assoc, HomologicalComplex.homology_π_ι, Category.assoc,
    shK_opcyclesZero_pOpcycles]
  rw [shK_cyclesZeroTo_iCycles]

/-! ## The reindexing isomorphisms, spelled out with the embeddings' images

These `rfl`-lemmas expose the `HomologicalComplex.restrictionHomologyIso` (resp.
`restrictionCyclesIso`) terms hidden in `shK_cyclesIso` and `shK_homologyIso`, with the implicit
degrees `i'`, `j'`, `k'` instantiated at `1+n`, `(1+1)+n`, ... so that the general naturality
lemmas of `HomologicalComplex` can be applied. -/

theorem shK_cyclesIso_eq (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (shK_cyclesIso K n 1).hom =
      (K.restrictionCyclesIso (shEmb n) 1 (1+1)
        (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel 1 (1+1) from rfl))
        (j' := 1+n) (k' := 1+1+n) rfl rfl
        (by change (ComplexShape.up ℕ).next (1+n) = 1+1+n
            exact ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (1+n) (1+1+n) from by
              change 1+n+1 = 1+1+n; omega))).hom := rfl

theorem shK_cyclesIso_natural {K L : CochainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (n : ℕ) :
    (shK_cyclesIso K n 1).hom ≫ HomologicalComplex.cyclesMap φ (1+n)
      = HomologicalComplex.cyclesMap (shMap φ n) 1 ≫ (shK_cyclesIso L n 1).hom := by
  rw [shK_cyclesIso_eq K n, shK_cyclesIso_eq L n]
  exact Work.Cohomology.restrictionCyclesIso_natural (e := shEmb n) (φ := φ) 1 (1+1)
    (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel 1 (1+1) from rfl))
    (j' := 1+n) (k' := 1+1+n) rfl rfl
    (by change (ComplexShape.up ℕ).next (1+n) = 1+1+n
        exact ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (1+n) (1+1+n) from by
          change 1+n+1 = 1+1+n; omega))

theorem shK_homologyIso_eq (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (shK_homologyIso K n 1 (by omega)).hom =
      (K.restrictionHomologyIso (shEmb n) (1-1) 1 (1+1)
        (ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel (1-1) 1 from by
          change (1-1)+1 = 1; omega))
        (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel 1 (1+1) from rfl))
        (i' := 1+n-1) (j' := 1+n) (k' := 1+1+n)
        (by change (1-1)+n = 1+n-1; omega) (by change 1+n = 1+n; rfl)
        (by change 1+1+n = 1+1+n; rfl)
        (by change (ComplexShape.up ℕ).prev (1+n) = 1+n-1
            exact ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel (1+n-1) (1+n) from by
              change (1+n-1)+1 = 1+n; omega))
        (by change (ComplexShape.up ℕ).next (1+n) = 1+1+n
            exact ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (1+n) (1+1+n) from by
              change 1+n+1 = 1+1+n; omega))).hom := rfl

theorem shK_cyclesIso_homologyπ (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (shK_cyclesIso K n 1).hom ≫ K.homologyπ (1+n)
      = (shK K n).homologyπ 1 ≫ (shK_homologyIso K n 1 (by omega)).hom := by
  rw [shK_cyclesIso_eq K n, shK_homologyIso_eq K n]
  rw [HomologicalComplex.homologyπ_restrictionHomologyIso_hom]

theorem shK_homologyIso_natural {K L : CochainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (n : ℕ) :
    (shK_homologyIso K n 1 (by omega)).hom ≫ HomologicalComplex.homologyMap φ (1+n)
      = HomologicalComplex.homologyMap (shMap φ n) 1
          ≫ (shK_homologyIso L n 1 (by omega)).hom := by
  rw [shK_homologyIso_eq K n, shK_homologyIso_eq L n]
  exact Work.Cohomology.restrictionHomologyIso_natural (e := shEmb n) (φ := φ) (1-1) 1 (1+1)
    (ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel (1-1) 1 from by
      change (1-1)+1 = 1; omega))
    (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel 1 (1+1) from rfl))
    (i' := 1+n-1) (j' := 1+n) (k' := 1+1+n)
    (by change (1-1)+n = 1+n-1; omega) (by change 1+n = 1+n; rfl) (by change 1+1+n = 1+1+n; rfl)
    (by change (ComplexShape.up ℕ).prev (1+n) = 1+n-1
        exact ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel (1+n-1) (1+n) from by
          change (1+n-1)+1 = 1+n; omega))
    (by change (ComplexShape.up ℕ).next (1+n) = 1+1+n
        exact ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (1+n) (1+1+n) from by
          change 1+n+1 = 1+1+n; omega))

/-! ## The connecting map of the shifted short exact sequence in degrees `0 → 1` -/

theorem shS_delta_comm_zero (S : CategoryTheory.ShortComplex (CochainComplex (ModuleCat ℚ) ℕ))
    (hS : S.ShortExact) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp
        ((Work.Serre.MVShift.shS_shortExact S hS n).δ 0 1
          (show (ComplexShape.up ℕ).Rel 0 1 from rfl))
        ((Work.Serre.MVShift.shK_homologyIso S.X₁ n 1 (by omega)).hom)
      = CategoryTheory.CategoryStruct.comp
        (Work.Serre.MVShift.shK_homologyZero S.X₃ n)
        (CategoryTheory.CategoryStruct.comp
          (hS.δ (0+n) (0+n+1) (show (ComplexShape.up ℕ).Rel (0+n) (0+n+1) from rfl))
          (CategoryTheory.eqToHom
            (congrArg (fun m => S.X₁.homology m) (by omega : 0+n+1 = 1+n)))) := by
  let A : ShortComplex.SnakeInput (ModuleCat ℚ) :=
    HomologicalComplex.HomologySequence.snakeInput (shS_shortExact S hS n) 0 1
      (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
  let B : ShortComplex.SnakeInput (ModuleCat ℚ) :=
    HomologicalComplex.HomologySequence.snakeInput hS (0+n) (0+n+1)
      (show (ComplexShape.up ℕ).Rel (0+n) (0+n+1) from rfl)
  have hα : 1+n = 0+n+1 := by omega
  let g₀ : A.L₀ ⟶ B.L₀ := ShortComplex.homMk (shK_homologyZero S.X₁ n) (shK_homologyZero S.X₂ n)
      (shK_homologyZero S.X₃ n) (shK_homologyZero_natural S.f n) (shK_homologyZero_natural S.g n)
  let g₁ : A.L₁ ⟶ B.L₁ := ShortComplex.homMk (shK_opcyclesZero S.X₁ n) (shK_opcyclesZero S.X₂ n)
      (shK_opcyclesZero S.X₃ n) (shK_opcyclesZero_natural S.f n) (shK_opcyclesZero_natural S.g n)
  let g₂ : A.L₂ ⟶ B.L₂ := ShortComplex.homMk
      ((shK_cyclesIso S.X₁ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.cycles m) hα))
      ((shK_cyclesIso S.X₂ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₂.cycles m) hα))
      ((shK_cyclesIso S.X₃ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₃.cycles m) hα))
      (by
        show ((shK_cyclesIso S.X₁ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.cycles m) hα))
            ≫ HomologicalComplex.cyclesMap S.f (0+n+1)
          = HomologicalComplex.cyclesMap (shMap S.f n) 1
            ≫ ((shK_cyclesIso S.X₂ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₂.cycles m) hα))
        rw [Category.assoc, shKZero_cyclesMap_congr S.f hα, ← Category.assoc, shK_cyclesIso_natural S.f n,
           Category.assoc])
      (by
        show ((shK_cyclesIso S.X₂ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₂.cycles m) hα))
            ≫ HomologicalComplex.cyclesMap S.g (0+n+1)
          = HomologicalComplex.cyclesMap (shMap S.g n) 1
            ≫ ((shK_cyclesIso S.X₃ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₃.cycles m) hα))
        rw [Category.assoc, shKZero_cyclesMap_congr S.g hα, ← Category.assoc, shK_cyclesIso_natural S.g n,
           Category.assoc])
  let g₃ : A.L₃ ⟶ B.L₃ := ShortComplex.homMk
      ((shK_homologyIso S.X₁ n 1 (by omega)).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) hα))
      ((shK_homologyIso S.X₂ n 1 (by omega)).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₂.homology m) hα))
      ((shK_homologyIso S.X₃ n 1 (by omega)).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₃.homology m) hα))
      (by
        show ((shK_homologyIso S.X₁ n 1 (by omega)).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) hα))
            ≫ HomologicalComplex.homologyMap S.f (0+n+1)
          = HomologicalComplex.homologyMap (shMap S.f n) 1
            ≫ ((shK_homologyIso S.X₂ n 1 (by omega)).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₂.homology m) hα))
        rw [Category.assoc, shKZero_homologyMap_congr S.f hα, ← Category.assoc, shK_homologyIso_natural S.f n,
           Category.assoc])
      (by
        show ((shK_homologyIso S.X₂ n 1 (by omega)).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₂.homology m) hα))
            ≫ HomologicalComplex.homologyMap S.g (0+n+1)
          = HomologicalComplex.homologyMap (shMap S.g n) 1
            ≫ ((shK_homologyIso S.X₃ n 1 (by omega)).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₃.homology m) hα))
        rw [Category.assoc, shKZero_homologyMap_congr S.g hα, ← Category.assoc, shK_homologyIso_natural S.g n,
           Category.assoc])
  have c01 : g₀ ≫ B.v₀₁ = A.v₀₁ ≫ g₁ := by
    apply ShortComplex.hom_ext
    · show shK_homologyZero S.X₁ n ≫ S.X₁.homologyι (0+n)
          = (shK S.X₁ n).homologyι 0 ≫ shK_opcyclesZero S.X₁ n
      exact shK_homologyZero_homologyι S.X₁ n
    · show shK_homologyZero S.X₂ n ≫ S.X₂.homologyι (0+n)
          = (shK S.X₂ n).homologyι 0 ≫ shK_opcyclesZero S.X₂ n
      exact shK_homologyZero_homologyι S.X₂ n
    · show shK_homologyZero S.X₃ n ≫ S.X₃.homologyι (0+n)
          = (shK S.X₃ n).homologyι 0 ≫ shK_opcyclesZero S.X₃ n
      exact shK_homologyZero_homologyι S.X₃ n
  have c12 : g₁ ≫ B.v₁₂ = A.v₁₂ ≫ g₂ := by
    apply ShortComplex.hom_ext
    · show shK_opcyclesZero S.X₁ n ≫ S.X₁.opcyclesToCycles (0+n) (0+n+1)
          = (shK S.X₁ n).opcyclesToCycles 0 1
            ≫ ((shK_cyclesIso S.X₁ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.cycles m) hα))
      rw [shKZero_opcyclesToCycles_congr (S.X₁) (a := 0+n) (b := 0+n+1) (b' := 1+n) hα]
      rw [← Category.assoc, shK_opcyclesZero_opcyclesToCycles, Category.assoc]
    · show shK_opcyclesZero S.X₂ n ≫ S.X₂.opcyclesToCycles (0+n) (0+n+1)
          = (shK S.X₂ n).opcyclesToCycles 0 1
            ≫ ((shK_cyclesIso S.X₂ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₂.cycles m) hα))
      rw [shKZero_opcyclesToCycles_congr (S.X₂) (a := 0+n) (b := 0+n+1) (b' := 1+n) hα]
      rw [← Category.assoc, shK_opcyclesZero_opcyclesToCycles, Category.assoc]
    · show shK_opcyclesZero S.X₃ n ≫ S.X₃.opcyclesToCycles (0+n) (0+n+1)
          = (shK S.X₃ n).opcyclesToCycles 0 1
            ≫ ((shK_cyclesIso S.X₃ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₃.cycles m) hα))
      rw [shKZero_opcyclesToCycles_congr (S.X₃) (a := 0+n) (b := 0+n+1) (b' := 1+n) hα]
      rw [← Category.assoc, shK_opcyclesZero_opcyclesToCycles, Category.assoc]
  have c23 : g₂ ≫ B.v₂₃ = A.v₂₃ ≫ g₃ := by
    apply ShortComplex.hom_ext
    · show ((shK_cyclesIso S.X₁ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.cycles m) hα))
            ≫ S.X₁.homologyπ (0+n+1)
          = (shK S.X₁ n).homologyπ 1
            ≫ ((shK_homologyIso S.X₁ n 1 (by omega)).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) hα))
      rw [Category.assoc, shKZero_homologyπ_congr (S.X₁) hα, ← Category.assoc,
        shK_cyclesIso_homologyπ S.X₁ n, Category.assoc]
    · show ((shK_cyclesIso S.X₂ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₂.cycles m) hα))
            ≫ S.X₂.homologyπ (0+n+1)
          = (shK S.X₂ n).homologyπ 1
            ≫ ((shK_homologyIso S.X₂ n 1 (by omega)).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₂.homology m) hα))
      rw [Category.assoc, shKZero_homologyπ_congr (S.X₂) hα, ← Category.assoc,
        shK_cyclesIso_homologyπ S.X₂ n, Category.assoc]
    · show ((shK_cyclesIso S.X₃ n 1).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₃.cycles m) hα))
            ≫ S.X₃.homologyπ (0+n+1)
          = (shK S.X₃ n).homologyπ 1
            ≫ ((shK_homologyIso S.X₃ n 1 (by omega)).hom ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₃.homology m) hα))
      rw [Category.assoc, shKZero_homologyπ_congr (S.X₃) hα, ← Category.assoc,
        shK_cyclesIso_homologyπ S.X₃ n, Category.assoc]
  let F : A ⟶ B := ⟨g₀, g₁, g₂, g₃, c01, c12, c23⟩
  have hF : (shS_shortExact S hS n).δ 0 1 (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
        ≫ ((shK_homologyIso S.X₁ n 1 (by omega)).hom
            ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) hα))
      = shK_homologyZero S.X₃ n
        ≫ hS.δ (0+n) (0+n+1) (show (ComplexShape.up ℕ).Rel (0+n) (0+n+1) from rfl) :=
    ShortComplex.SnakeInput.naturality_δ F
  have hcancel : CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) hα)
        ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) (by omega : 0+n+1 = 1+n))
      = 𝟙 (S.X₁.homology (1+n)) := by
    rw [CategoryTheory.eqToHom_trans]
    exact CategoryTheory.eqToHom_refl _ _
  have h1 : (shS_shortExact S hS n).δ 0 1 (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
        ≫ (shK_homologyIso S.X₁ n 1 (by omega)).hom
      = ((shS_shortExact S hS n).δ 0 1 (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
          ≫ ((shK_homologyIso S.X₁ n 1 (by omega)).hom
              ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) hα)))
        ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) (by omega : 0+n+1 = 1+n)) := by
    rw [Category.assoc, Category.assoc, hcancel, Category.comp_id]
  have h2 : ((shS_shortExact S hS n).δ 0 1 (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
          ≫ ((shK_homologyIso S.X₁ n 1 (by omega)).hom
              ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) hα)))
        ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) (by omega : 0+n+1 = 1+n))
      = (shK_homologyZero S.X₃ n
          ≫ hS.δ (0+n) (0+n+1) (show (ComplexShape.up ℕ).Rel (0+n) (0+n+1) from rfl))
        ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) (by omega : 0+n+1 = 1+n)) := by
    rw [hF]
  have h3 : (shK_homologyZero S.X₃ n
          ≫ hS.δ (0+n) (0+n+1) (show (ComplexShape.up ℕ).Rel (0+n) (0+n+1) from rfl))
        ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) (by omega : 0+n+1 = 1+n))
      = shK_homologyZero S.X₃ n
        ≫ (hS.δ (0+n) (0+n+1) (show (ComplexShape.up ℕ).Rel (0+n) (0+n+1) from rfl)
            ≫ CategoryTheory.eqToHom (congrArg (fun m => S.X₁.homology m) (by omega : 0+n+1 = 1+n))) := by
    rw [Category.assoc]
  exact h1.trans (h2.trans h3)

theorem shKZeroRat (n : ℕ) :
    ∃ z : ∀ K : CochainComplex (ModuleCat ℚ) ℕ,
        (Work.Serre.MVShift.shK K n).homology 0 ⟶ K.homology (0 + n),
      (∀ (K : CochainComplex (ModuleCat ℚ) ℕ) (c : (Work.Serre.MVShift.shK K n).cycles 0),
          (ModuleCat.Hom.hom (z K)) ((ModuleCat.Hom.hom ((Work.Serre.MVShift.shK K n).homologyπ 0)) c)
          = (ModuleCat.Hom.hom (K.homologyπ (0 + n)))
              ((ModuleCat.Hom.hom (Work.Serre.MVShift.shK_cyclesIso K n 0).hom) c)) ∧
      (∀ (K L : CochainComplex (ModuleCat ℚ) ℕ) (φ : K ⟶ L),
          CategoryTheory.CategoryStruct.comp
              (HomologicalComplex.homologyMap (Work.Serre.MVShift.shMap φ n) 0) (z L)
            = CategoryTheory.CategoryStruct.comp (z K)
                (HomologicalComplex.homologyMap φ (0 + n))) ∧
      (∀ (S : CategoryTheory.ShortComplex (CochainComplex (ModuleCat ℚ) ℕ)) (hS : S.ShortExact),
          CategoryTheory.CategoryStruct.comp
              ((Work.Serre.MVShift.shS_shortExact S hS n).δ 0 1
                (show (ComplexShape.up ℕ).Rel 0 1 from rfl))
              ((Work.Serre.MVShift.shK_homologyIso S.X₁ n 1 (by omega)).hom)
            = CategoryTheory.CategoryStruct.comp (z S.X₃)
                (CategoryTheory.CategoryStruct.comp
                  (hS.δ (0 + n) (0 + n + 1)
                    (show (ComplexShape.up ℕ).Rel (0 + n) (0 + n + 1) from rfl))
                  (CategoryTheory.eqToHom
                    (congrArg (fun m => S.X₁.homology m) (by omega : 0 + n + 1 = 1 + n))))) := by
  refine ⟨fun K => shK_homologyZero K n, ?_, ?_, ?_⟩
  · intro K c
    have h := congrArg (fun (g : (shK K n).cycles 0 ⟶ K.homology (0+n)) =>
      (ModuleCat.Hom.hom g) c) (shK_homologyZero_spec' K n)
    simpa using h
  · intro K L φ
    exact (shK_homologyZero_natural φ n).symm
  · intro S hS
    exact shS_delta_comm_zero S hS n

end Work.Serre.MVShift
