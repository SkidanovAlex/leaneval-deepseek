/-
# The connecting map of a degree shift of a short complex of `ℚ`-cochain complexes,
# compatible with the restriction isomorphisms

`Work.Serre.MVShift.shS S n` is the degree-`n` shift of a short complex of cochain complexes of
`ℚ`-modules (the restriction of `S` along the shape embedding `up ℕ → up ℕ`, `k ↦ k + n`), and
`Work.Serre.MVShift.shK_homologyIso` identifies the homology of the shifted complex in degree
`k ≥ 1` with the homology of the original complex in degree `k + n`.

This file proves `Work.Serre.MVShift.shS_delta_comm`: the connecting map of the shifted short exact
sequence, read through the restriction isomorphisms, is the connecting map of the original short
exact sequence in the shifted degrees.  It is the `ℚ`-coefficient port of `Work.Thom.shS_delta_comm`
(which is the same statement for `ℤ`-coefficients); the mathematical proof is the same:

the two homology sequences are related by a morphism of snake inputs whose components are the
restriction isomorphisms, and one applies the naturality of the snake-lemma connecting map
(`ShortComplex.SnakeInput.naturality_δ`).  The naturality of the restriction isomorphisms
(`Work.Cohomology.restrictionCyclesIso_natural`, `restrictionOpcyclesIso_natural`,
`restrictionHomologyIso_natural`) is coefficient-independent.
-/
import Mathlib
import Submission.Work.Serre.MVShift.ShQ
import Submission.Work.Cohomology.Endgame.dshDelta

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Serre.MVShift

namespace ShSdeltaAux

/-! ## Degree bookkeeping for the shape `up ℕ` -/

lemma up_rel_prev (k : ℕ) (hk : 1 ≤ k) : (ComplexShape.up ℕ).Rel (k - 1) k := by
  rw [ComplexShape.up_Rel]; omega

lemma up_rel_next (k : ℕ) : (ComplexShape.up ℕ).Rel k (k + 1) := by
  rw [ComplexShape.up_Rel]

lemma up_rel_nextn (k n : ℕ) : (ComplexShape.up ℕ).Rel (k + n) ((k + 1) + n) := by
  rw [ComplexShape.up_Rel]; omega

/-! ## Pinned forms of the restriction isomorphisms

These are `abbrev`s (hence reducible) with the ambient degree pinned to `i + n`, `j + n`: they are
the same isomorphisms as `shK_*Iso`, but with a transparent syntactic shape, which makes the
degree bookkeeping in the naturality statements below manageable. -/

/-- The `X`-isomorphism of the shift, pinned to `i ↦ i + n`. -/
noncomputable abbrev xIso (K : CochainComplex (ModuleCat ℚ) ℕ) (n i : ℕ) :
    (shK K n).X i ≅ K.X (i + n) :=
  K.restrictionXIso (shEmb n) (rfl : (shEmb n).f i = i + n)

/-- The cycles of the shift, pinned to `j ↦ j + n`. -/
noncomputable abbrev cycIso (K : CochainComplex (ModuleCat ℚ) ℕ) (n j : ℕ)
    [K.HasHomology (j + n)] : (shK K n).cycles j ≅ K.cycles (j + n) :=
  K.restrictionCyclesIso (shEmb n) j (j + 1)
    (ComplexShape.next_eq' _ (up_rel_next j))
    (by change (j : ℕ) + n = j + n; rfl)
    (by change (j + 1) + n = (j + 1) + n; rfl)
    (ComplexShape.next_eq' _ (up_rel_nextn j n))

/-- The opcycles of the shift, pinned to `j ↦ j + n` (for `j ≥ 1`). -/
noncomputable abbrev opcIso (K : CochainComplex (ModuleCat ℚ) ℕ) (n j : ℕ) (hj : 1 ≤ j)
    [K.HasHomology (j + n)] : (shK K n).opcycles j ≅ K.opcycles (j + n) :=
  K.restrictionOpcyclesIso (shEmb n) (j - 1) j
    (ComplexShape.prev_eq' _ (up_rel_prev j hj))
    (by change j - 1 + n = j + n - 1; omega)
    (by change j + n = j + n; rfl)
    (by change (ComplexShape.up ℕ).prev (j + n) = j + n - 1
        exact ComplexShape.prev_eq' _ (by rw [ComplexShape.up_Rel]; omega))

/-! ## Naturality of the restriction isomorphisms -/

/-- Naturality of `shK_homologyIso` with respect to a morphism of complexes. -/
theorem shK_homologyIso_natural {K L : CochainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (n k : ℕ)
    (hk : 1 ≤ k) [K.HasHomology (k + n)] [L.HasHomology (k + n)] :
    (shK_homologyIso K n k hk).hom ≫ homologyMap φ (k + n)
      = homologyMap (shMap φ n) k ≫ (shK_homologyIso L n k hk).hom :=
  Work.Cohomology.restrictionHomologyIso_natural (e := shEmb n) φ (k - 1) k (k + 1)
    (ComplexShape.prev_eq' _ (up_rel_prev k hk))
    (ComplexShape.next_eq' _ (up_rel_next k))
    (by change k - 1 + n = k + n - 1; omega)
    (by change (shEmb n).f k = k + n; rfl)
    (by change (shEmb n).f (k + 1) = k + 1 + n; rfl)
    (ComplexShape.prev_eq' _ (up_rel_prev (k + n) (by omega)))
    (ComplexShape.next_eq' _ (up_rel_nextn k n))

/-- Naturality of `shK_opcyclesIso` with respect to a morphism of complexes. -/
theorem shK_opcyclesIso_natural {K L : CochainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (n k : ℕ)
    (hk : 1 ≤ k) [K.HasHomology (k + n)] [L.HasHomology (k + n)] :
    (shK_opcyclesIso K n k hk).hom ≫ opcyclesMap φ (k + n)
      = opcyclesMap (shMap φ n) k ≫ (shK_opcyclesIso L n k hk).hom :=
  Work.Cohomology.restrictionOpcyclesIso_natural (e := shEmb n) φ (k - 1) k
    (ComplexShape.prev_eq' _ (up_rel_prev k hk))
    (by change k - 1 + n = k + n - 1; omega)
    (by change (shEmb n).f k = k + n; rfl)
    (ComplexShape.prev_eq' _ (up_rel_prev (k + n) (by omega)))

/-- Naturality of `shK_cyclesIso` with respect to a morphism of complexes. -/
theorem shK_cyclesIso_natural {K L : CochainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (n k : ℕ)
    [K.HasHomology (k + n)] [L.HasHomology (k + n)] :
    (shK_cyclesIso K n k).hom ≫ cyclesMap φ (k + n)
      = cyclesMap (shMap φ n) k ≫ (shK_cyclesIso L n k).hom := by
  show (K.restrictionCyclesIso (shEmb n) k (k + 1)
      (ComplexShape.next_eq' _ (up_rel_next k))
      (by change (k : ℕ) + n = k + n; rfl)
      (by change (k + 1) + n = (k + 1) + n; rfl)
      (ComplexShape.next_eq' _ (up_rel_nextn k n))).hom ≫ cyclesMap φ (k + n)
      = cyclesMap (restrictionMap φ (shEmb n)) k
        ≫ (L.restrictionCyclesIso (shEmb n) k (k + 1)
          (ComplexShape.next_eq' _ (up_rel_next k))
          (by change (k : ℕ) + n = k + n; rfl)
          (by change (k + 1) + n = (k + 1) + n; rfl)
          (ComplexShape.next_eq' _ (up_rel_nextn k n))).hom
  exact Work.Cohomology.restrictionCyclesIso_natural (e := shEmb n) φ k (k + 1)
    (ComplexShape.next_eq' _ (up_rel_next k))
    (by change (k : ℕ) + n = k + n; rfl)
    (by change (k + 1) + n = (k + 1) + n; rfl)
    (ComplexShape.next_eq' _ (up_rel_nextn k n))

/-! ## Compatibility with `homologyι`, `homologyπ` and `opcyclesToCycles` -/

/-- `shK_homologyIso` is compatible with the canonical map `homology ⟶ opcycles`. -/
theorem shK_homology_ι (K : CochainComplex (ModuleCat ℚ) ℕ) (n k : ℕ) (hk : 1 ≤ k)
    [K.HasHomology (k + n)] :
    (shK_homologyIso K n k hk).hom ≫ K.homologyι (k + n)
      = (shK K n).homologyι k ≫ (shK_opcyclesIso K n k hk).hom := by
  show (K.restrictionHomologyIso (shEmb n) (k - 1) k (k + 1)
      (ComplexShape.prev_eq' _ (up_rel_prev k hk))
      (ComplexShape.next_eq' _ (up_rel_next k))
      (by change k - 1 + n = k + n - 1; omega)
      (by change (shEmb n).f k = k + n; rfl)
      (by change (shEmb n).f (k + 1) = k + 1 + n; rfl)
      (ComplexShape.prev_eq' _ (up_rel_prev (k + n) (by omega)))
      (ComplexShape.next_eq' _ (up_rel_nextn k n))).hom ≫ K.homologyι (k + n)
      = (K.restriction (shEmb n)).homologyι k ≫
        (K.restrictionOpcyclesIso (shEmb n) (k - 1) k
          (ComplexShape.prev_eq' _ (up_rel_prev k hk))
          (by change k - 1 + n = k + n - 1; omega)
          (by change (shEmb n).f k = k + n; rfl)
          (ComplexShape.prev_eq' _ (up_rel_prev (k + n) (by omega)))).hom
  exact HomologicalComplex.restrictionHomologyIso_hom_homologyι (e := shEmb n) K (k - 1) k (k + 1)
    (ComplexShape.prev_eq' _ (up_rel_prev k hk))
    (ComplexShape.next_eq' _ (up_rel_next k))
    (by change k - 1 + n = k + n - 1; omega)
    (by change (shEmb n).f k = k + n; rfl)
    (by change (shEmb n).f (k + 1) = k + 1 + n; rfl)
    (ComplexShape.prev_eq' _ (up_rel_prev (k + n) (by omega)))
    (ComplexShape.next_eq' _ (up_rel_nextn k n))

/-- `shK_homologyIso` is compatible with the canonical map `cycles ⟶ homology`. -/
theorem shK_homology_π (K : CochainComplex (ModuleCat ℚ) ℕ) (n k : ℕ) (hk : 1 ≤ k)
    [K.HasHomology ((k + 1) + n)] :
    (shK K n).homologyπ (k + 1) ≫ (shK_homologyIso K n (k + 1) (by omega)).hom
      = (shK_cyclesIso K n (k + 1)).hom ≫ K.homologyπ ((k + 1) + n) := by
  show (K.restriction (shEmb n)).homologyπ (k + 1) ≫
      (K.restrictionHomologyIso (shEmb n) ((k + 1) - 1) (k + 1) ((k + 1) + 1)
        (ComplexShape.prev_eq' _ (up_rel_prev (k + 1) (by omega)))
        (ComplexShape.next_eq' _ (up_rel_next (k + 1)))
        (by change ((k + 1) - 1) + n = (k + 1) + n - 1; omega)
        (by change ((k + 1) + n) = (k + 1) + n; rfl)
        (by change ((k + 1) + 1) + n = ((k + 1) + 1) + n; rfl)
        (ComplexShape.prev_eq' _ (up_rel_prev ((k + 1) + n) (by omega)))
        (ComplexShape.next_eq' _ (up_rel_nextn (k + 1) n))).hom
      = (K.restrictionCyclesIso (shEmb n) (k + 1) ((k + 1) + 1)
        (ComplexShape.next_eq' _ (up_rel_next (k + 1)))
        (by change ((k + 1) : ℕ) + n = (k + 1) + n; rfl)
        (by change ((k + 1) + 1) + n = ((k + 1) + 1) + n; rfl)
        (ComplexShape.next_eq' _ (up_rel_nextn (k + 1) n))).hom ≫ K.homologyπ ((k + 1) + n)
  exact HomologicalComplex.homologyπ_restrictionHomologyIso_hom (e := shEmb n) K ((k + 1) - 1)
    (k + 1) ((k + 1) + 1)
    (ComplexShape.prev_eq' _ (up_rel_prev (k + 1) (by omega)))
    (ComplexShape.next_eq' _ (up_rel_next (k + 1)))
    (by change ((k + 1) - 1) + n = (k + 1) + n - 1; omega)
    (by change ((k + 1) + n) = (k + 1) + n; rfl)
    (by change ((k + 1) + 1) + n = ((k + 1) + 1) + n; rfl)
    (ComplexShape.prev_eq' _ (up_rel_prev ((k + 1) + n) (by omega)))
    (ComplexShape.next_eq' _ (up_rel_nextn (k + 1) n))

/-- The shift commutes with `toCycles` (in the pinned degrees). -/
theorem toCycles_shift (K : CochainComplex (ModuleCat ℚ) ℕ) (n i j : ℕ)
    [K.HasHomology (j + n)] :
    (K.restrictionXIso (shEmb n) (rfl : (shEmb n).f i = i + n)).hom
        ≫ K.toCycles (i + n) (j + n)
      = (shK K n).toCycles i j ≫ (shK_cyclesIso K n j).hom := by
  show (xIso K n i).hom ≫ K.toCycles (i + n) (j + n)
      = (shK K n).toCycles i j ≫ (cycIso K n j).hom
  rw [← cancel_mono (K.iCycles (j + n))]
  simp only [Category.assoc]
  rw [HomologicalComplex.toCycles_i]
  have ecyc : (cycIso K n j).hom ≫ K.iCycles (j + n)
      = (shK K n).iCycles j ≫ (xIso K n j).hom := by
    simp only [cycIso, xIso, HomologicalComplex.restrictionCyclesIso_hom_iCycles]
  rw [ecyc, ← Category.assoc, HomologicalComplex.toCycles_i]
  have ed : (shK K n).d i j ≫ (xIso K n j).hom = (xIso K n i).hom ≫ K.d (i + n) (j + n) := by
    rw [show (shK K n).d i j = (K.restriction (shEmb n)).d i j from rfl]
    rw [HomologicalComplex.restriction_d_eq K (shEmb n) (rfl : (shEmb n).f i = i + n)
      (rfl : (shEmb n).f j = j + n)]
    simp only [Category.assoc, xIso]
    rfl
  rw [ed]

/-- The shift commutes with `opcyclesToCycles` (in the pinned degrees). -/
theorem opcyclesToCycles_shift (K : CochainComplex (ModuleCat ℚ) ℕ) (n k : ℕ) (hk : 1 ≤ k)
    [K.HasHomology ((k + 1) + n)] :
    (shK_opcyclesIso K n k hk).hom ≫ K.opcyclesToCycles (k + n) ((k + 1) + n)
      = (shK K n).opcyclesToCycles k (k + 1) ≫ (shK_cyclesIso K n (k + 1)).hom := by
  show (opcIso K n k hk).hom ≫ K.opcyclesToCycles (k + n) ((k + 1) + n)
      = (shK K n).opcyclesToCycles k (k + 1) ≫ (cycIso K n (k + 1)).hom
  rw [← cancel_epi ((shK K n).pOpcycles k)]
  have e1 : (shK K n).pOpcycles k ≫ (opcIso K n k hk).hom
      = (xIso K n k).hom ≫ K.pOpcycles (k + n) := by
    simp only [opcIso, xIso, shK, HomologicalComplex.pOpcycles_restrictionOpcyclesIso_hom]
  rw [← Category.assoc, e1, Category.assoc, HomologicalComplex.pOpcycles_opcyclesToCycles]
  rw [← Category.assoc, HomologicalComplex.pOpcycles_opcyclesToCycles]
  exact toCycles_shift K n k (k + 1)

/-- Reindexing the connecting map along an equality of degrees. -/
theorem delta_eqToHom {S : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ)} (hS : S.ShortExact)
    {i j j' : ℕ} (hij : (ComplexShape.up ℕ).Rel i j) (hij' : (ComplexShape.up ℕ).Rel i j')
    (h : j = j') :
    hS.δ i j hij ≫ eqToHom (congrArg (fun m => S.X₁.homology m) h) = hS.δ i j' hij' := by
  cases h
  simp

/-- The form of `delta_eqToHom` used to compare `(k+n)+1` with `k+(n+1)`. -/
theorem delta_reindex (S : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ)) (hS : S.ShortExact)
    (n k : ℕ) (hk : 1 ≤ k) (hij2 : (ComplexShape.up ℕ).Rel (k + n) ((k + 1) + n)) :
    hS.δ (k + n) ((k + 1) + n) hij2
      = hS.δ (k + n) (k + n + 1) (up_rel_next (k + n))
        ≫ eqToHom (congrArg (fun m => S.X₁.homology m) (by omega : k + n + 1 = (k + 1) + n)) :=
  (delta_eqToHom hS (up_rel_next (k + n)) hij2 (by omega : k + n + 1 = (k + 1) + n)).symm

end ShSdeltaAux

theorem shS_delta_comm (S : CategoryTheory.ShortComplex (CochainComplex (ModuleCat ℚ) ℕ))
    (hS : S.ShortExact) (n k : ℕ) (hk : 1 ≤ k) :
    CategoryTheory.CategoryStruct.comp
        ((shS_shortExact S hS n).δ k (k+1) (show (ComplexShape.up ℕ).Rel k (k+1) from rfl))
        ((shK_homologyIso S.X₁ n (k+1) (by omega)).hom)
      = CategoryTheory.CategoryStruct.comp
        ((shK_homologyIso S.X₃ n k hk).hom)
        (CategoryTheory.CategoryStruct.comp
          (hS.δ (k+n) (k+n+1) (show (ComplexShape.up ℕ).Rel (k+n) (k+n+1) from rfl))
          (CategoryTheory.eqToHom
            (congrArg (fun m => S.X₁.homology m) (by omega : k+n+1 = (k+1)+n)))) := by
  have hk1 : 1 ≤ k + 1 := by omega
  have hij : (ComplexShape.up ℕ).Rel k (k + 1) := ShSdeltaAux.up_rel_next k
  have hij2 : (ComplexShape.up ℕ).Rel (k + n) ((k + 1) + n) := ShSdeltaAux.up_rel_nextn k n
  have hmn : k + n + 1 = (k + 1) + n := by omega
  let T₁ := HomologySequence.snakeInput (shS_shortExact S hS n) k (k + 1) hij
  let T₂ := HomologySequence.snakeInput hS (k + n) ((k + 1) + n) hij2
  let F : ShortComplex.SnakeInput.Hom T₁ T₂ :=
    { f₀ := ShortComplex.homMk
        (shK_homologyIso S.X₁ n k hk).hom
        (shK_homologyIso S.X₂ n k hk).hom
        (shK_homologyIso S.X₃ n k hk).hom
        (by
          show (shK_homologyIso S.X₁ n k hk).hom ≫ homologyMap S.f (k + n)
              = homologyMap (shMap S.f n) k ≫ (shK_homologyIso S.X₂ n k hk).hom
          exact ShSdeltaAux.shK_homologyIso_natural S.f n k hk)
        (by
          show (shK_homologyIso S.X₂ n k hk).hom ≫ homologyMap S.g (k + n)
              = homologyMap (shMap S.g n) k ≫ (shK_homologyIso S.X₃ n k hk).hom
          exact ShSdeltaAux.shK_homologyIso_natural S.g n k hk)
      f₁ := ShortComplex.homMk
        (shK_opcyclesIso S.X₁ n k hk).hom
        (shK_opcyclesIso S.X₂ n k hk).hom
        (shK_opcyclesIso S.X₃ n k hk).hom
        (by
          show (shK_opcyclesIso S.X₁ n k hk).hom ≫ opcyclesMap S.f (k + n)
              = opcyclesMap (shMap S.f n) k ≫ (shK_opcyclesIso S.X₂ n k hk).hom
          exact ShSdeltaAux.shK_opcyclesIso_natural S.f n k hk)
        (by
          show (shK_opcyclesIso S.X₂ n k hk).hom ≫ opcyclesMap S.g (k + n)
              = opcyclesMap (shMap S.g n) k ≫ (shK_opcyclesIso S.X₃ n k hk).hom
          exact ShSdeltaAux.shK_opcyclesIso_natural S.g n k hk)
      f₂ := ShortComplex.homMk
        (shK_cyclesIso S.X₁ n (k + 1)).hom
        (shK_cyclesIso S.X₂ n (k + 1)).hom
        (shK_cyclesIso S.X₃ n (k + 1)).hom
        (by
          show (shK_cyclesIso S.X₁ n (k + 1)).hom ≫ cyclesMap S.f ((k + 1) + n)
              = cyclesMap (shMap S.f n) (k + 1) ≫ (shK_cyclesIso S.X₂ n (k + 1)).hom
          exact ShSdeltaAux.shK_cyclesIso_natural S.f n (k + 1))
        (by
          show (shK_cyclesIso S.X₂ n (k + 1)).hom ≫ cyclesMap S.g ((k + 1) + n)
              = cyclesMap (shMap S.g n) (k + 1) ≫ (shK_cyclesIso S.X₃ n (k + 1)).hom
          exact ShSdeltaAux.shK_cyclesIso_natural S.g n (k + 1))
      f₃ := ShortComplex.homMk
        (shK_homologyIso S.X₁ n (k + 1) hk1).hom
        (shK_homologyIso S.X₂ n (k + 1) hk1).hom
        (shK_homologyIso S.X₃ n (k + 1) hk1).hom
        (by
          show (shK_homologyIso S.X₁ n (k + 1) hk1).hom ≫ homologyMap S.f ((k + 1) + n)
              = homologyMap (shMap S.f n) (k + 1) ≫ (shK_homologyIso S.X₂ n (k + 1) hk1).hom
          exact ShSdeltaAux.shK_homologyIso_natural S.f n (k + 1) hk1)
        (by
          show (shK_homologyIso S.X₂ n (k + 1) hk1).hom ≫ homologyMap S.g ((k + 1) + n)
              = homologyMap (shMap S.g n) (k + 1) ≫ (shK_homologyIso S.X₃ n (k + 1) hk1).hom
          exact ShSdeltaAux.shK_homologyIso_natural S.g n (k + 1) hk1)
      comm₀₁ := by
        apply ShortComplex.hom_ext
        · show (shK_homologyIso S.X₁ n k hk).hom ≫ S.X₁.homologyι (k + n)
              = (shK S.X₁ n).homologyι k ≫ (shK_opcyclesIso S.X₁ n k hk).hom
          exact ShSdeltaAux.shK_homology_ι S.X₁ n k hk
        · show (shK_homologyIso S.X₂ n k hk).hom ≫ S.X₂.homologyι (k + n)
              = (shK S.X₂ n).homologyι k ≫ (shK_opcyclesIso S.X₂ n k hk).hom
          exact ShSdeltaAux.shK_homology_ι S.X₂ n k hk
        · show (shK_homologyIso S.X₃ n k hk).hom ≫ S.X₃.homologyι (k + n)
              = (shK S.X₃ n).homologyι k ≫ (shK_opcyclesIso S.X₃ n k hk).hom
          exact ShSdeltaAux.shK_homology_ι S.X₃ n k hk
      comm₁₂ := by
        apply ShortComplex.hom_ext
        · show (shK_opcyclesIso S.X₁ n k hk).hom ≫ S.X₁.opcyclesToCycles (k + n) ((k + 1) + n)
              = (shK S.X₁ n).opcyclesToCycles k (k + 1) ≫ (shK_cyclesIso S.X₁ n (k + 1)).hom
          exact ShSdeltaAux.opcyclesToCycles_shift S.X₁ n k hk
        · show (shK_opcyclesIso S.X₂ n k hk).hom ≫ S.X₂.opcyclesToCycles (k + n) ((k + 1) + n)
              = (shK S.X₂ n).opcyclesToCycles k (k + 1) ≫ (shK_cyclesIso S.X₂ n (k + 1)).hom
          exact ShSdeltaAux.opcyclesToCycles_shift S.X₂ n k hk
        · show (shK_opcyclesIso S.X₃ n k hk).hom ≫ S.X₃.opcyclesToCycles (k + n) ((k + 1) + n)
              = (shK S.X₃ n).opcyclesToCycles k (k + 1) ≫ (shK_cyclesIso S.X₃ n (k + 1)).hom
          exact ShSdeltaAux.opcyclesToCycles_shift S.X₃ n k hk
      comm₂₃ := by
        apply ShortComplex.hom_ext
        · show (shK_cyclesIso S.X₁ n (k + 1)).hom ≫ S.X₁.homologyπ ((k + 1) + n)
              = (shK S.X₁ n).homologyπ (k + 1) ≫ (shK_homologyIso S.X₁ n (k + 1) hk1).hom
          exact (ShSdeltaAux.shK_homology_π S.X₁ n k hk).symm
        · show (shK_cyclesIso S.X₂ n (k + 1)).hom ≫ S.X₂.homologyπ ((k + 1) + n)
              = (shK S.X₂ n).homologyπ (k + 1) ≫ (shK_homologyIso S.X₂ n (k + 1) hk1).hom
          exact (ShSdeltaAux.shK_homology_π S.X₂ n k hk).symm
        · show (shK_cyclesIso S.X₃ n (k + 1)).hom ≫ S.X₃.homologyπ ((k + 1) + n)
              = (shK S.X₃ n).homologyπ (k + 1) ≫ (shK_homologyIso S.X₃ n (k + 1) hk1).hom
          exact (ShSdeltaAux.shK_homology_π S.X₃ n k hk).symm }
  have key : (shS_shortExact S hS n).δ k (k + 1) hij
        ≫ (shK_homologyIso S.X₁ n (k + 1) hk1).hom
      = (shK_homologyIso S.X₃ n k hk).hom ≫ hS.δ (k + n) ((k + 1) + n) hij2 :=
    ShortComplex.SnakeInput.naturality_δ F
  rw [key, ShSdeltaAux.delta_reindex S hS n k hk hij2]

end Work.Serre.MVShift
