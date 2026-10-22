import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.ZS.Data
import Submission.Work.ATOM.ZS.Topo.TSpace
import Submission.Work.ATOM.ZS.Topo.Maps
import Submission.Work.ATOM.ZS.e_fix_of_mem_A_of_le
import Submission.Work.ATOM.ZS.e_pred_eq_of_mem_A
import Submission.Work.ATOM.ZS.gHat_descend
import Submission.Work.ATOM.ZS.F_vanishing
import Submission.Work.ATOM.ZS.G_vanishing
import Submission.Work.ATOM.ZS.FP_vanishing
import Submission.Work.ATOM.Toolkit.EA
import Submission.Work.ATOM.Toolkit.PS_desc
import Submission.Work.ATOM.Toolkit.PP_desc
import Submission.Work.ATOM.Toolkit.homFreeEquiv_value_of_descend
import Submission.Work.ATOM.zdesc
import Submission.Work.ATOM.zmap_ext_of_closed_cover
import Submission.Work.ATOM.zfree_iso_pt_biprod_zred
import Submission.Work.ATOM.projective_P

/-!
# AREA ATOM: the null-sequence data on `ℤ[S]` (REFS/03 §1)

This file constructs the morphisms of the null-sequence trick of REFS/03 §1 for an infinite light
profinite set `S`, from the explicit continuous maps of `Submission/Work/ATOM/ZS/Topo/` and the
descent lemmas of `Submission/Work/ATOM/Toolkit/`:

* `g : P ⟶ ℤ[S]`, the null sequence `e_j ↦ [a_j] - [e_{n(j)-1} a_j]`, glued over `T'`
  (`Work.ATOM.gBig`, `Work.ATOM.g`) and `g̃ = g ≫ qred : P ⟶ ℤ̃[S]`;
* `F : P ⊗ ℤ[S] ⟶ ℤ̃[S]`, `(k,x) ↦ [x] - [ẽ(k,x)]`;
* `s : ℤ̃[S] ⟶ P ⊗ ℤ[S]`, the corrected `(0,-)` map;
* `G : P ⊗ ℤ[S] ⟶ P`, `(k,x) ↦ e_{ψ(k,x)}`;
* `F_P : P ⊗ P ⟶ P`, `(k,j) ↦ e_{φ_P(k,j)}`;
* `s_P : P ⟶ P ⊗ P`, the map `e_j ↦ e_0 ⊗ e_j`.

Each is characterised by a specification lemma (`..._spec`) in terms of `zmap`-combinations of the
explicit continuous maps, which is the form in which the identities `h₁`–`h₇` of the scheme
(`Work.ANALYTIC.scheme_bijective`) are checked.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

noncomputable section

namespace Work.ATOM

variable (S : LightProfinite.{0}) [Infinite S]

/-! ## The value of `homFreeEquiv` on zero -/

private theorem homFreeEquiv_zero (T : LightProfinite.{0}) (A : LightCondAb) :
    homFreeEquiv T A (0 : zfree T ⟶ A) = 0 := by
  have h := homFreeEquiv_naturality_target T (0 : zfree T ⟶ A) (0 : zfree T ⟶ zfree T)
  rw [zero_comp] at h
  rw [h]
  simp

/-! ## The null sequence `g : P ⟶ ℤ[S]` -/

/-- `ĝ = zmap pr₂ − zmap β`, the section of `ℤ[S]` over `T'` defining the null sequence. -/
def gHat : zfree (T' S) ⟶ zfree S := zmap (pr₂T S) - zmap (betaT S)

/-- The descended section `ℤ[ℕ∪{∞}] ⟶ ℤ[S]`. -/
def gBig : zfree (LightProfinite.NatUnionInfty) ⟶ zfree S :=
  (zdesc (tProj S) (tProj_surjective S) (gHat S) (ZS.gHat_descend S)).choose

theorem gBig_spec : zmap (tProj S) ≫ gBig S = gHat S :=
  (zdesc (tProj S) (tProj_surjective S) (gHat S) (ZS.gHat_descend S)).choose_spec.1

/-- The point `∞` of `T'` (any point of the form `(∞,x)`). -/
def tInfty : ↥(T' S) := ⟨mkNS S ∞ ((levelData S).s₀), mem_tSet_infty _⟩

@[simp] lemma tProj_tInfty : tProj S (tInfty S) = (∞ : ℕ∪{∞}) := rfl

theorem gBig_aug : zmap LightCondensed.ι ≫ gBig S = 0 := by
  apply (homFreeEquiv pt (zfree S)).injective
  have hι : (LightCondensed.ι : (LightProfinite.of PUnit.{1}) ⟶ ℕ∪{∞}) =
      ptAt (∞ : ℕ∪{∞}) := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [hι, ← tProj_tInfty S]
  rw [Toolkit.homFreeEquiv_value_of_descend (tProj S) (gHat S) (gBig S) (gBig_spec S) (tInfty S)]
  have hpt : ptAt (tInfty S) ≫ pr₂T S = ptAt (tInfty S) ≫ betaT S := by
    rw [Toolkit.ptAt_comp (pr₂T S), Toolkit.ptAt_comp (betaT S),
      (betaT_eq_pr₂T_of_infty S (tInfty S) rfl).symm]
  have hzero : zmap (ptAt (tInfty S)) ≫ gHat S = 0 := by
    show zmap (ptAt (tInfty S)) ≫ (zmap (pr₂T S) - zmap (betaT S)) = 0
    rw [Preadditive.comp_sub, sub_eq_zero, ← Functor.map_comp, ← Functor.map_comp, hpt]
  rw [hzero, homFreeEquiv_zero]

/-- **The null sequence of REFS/03 §1**: `g : P ⟶ ℤ[S]`, the descent of `ĝ` along
`T' ⟶ ℕ∪{∞}`. -/
def g : P ⟶ zfree S :=
  P_homMk (zfree S) (gBig S) (by simpa only [P_map, zmap] using gBig_aug S)

theorem g_spec : P_proj ≫ g S = gBig S := cokernel.π_desc _ _ _

/-- `g̃ = g ≫ qred : P ⟶ ℤ̃[S]`, the null sequence with values in the reduced free object. -/
def gRed : P ⟶ zred S (levelData S).s₀ := g S ≫ qred S (levelData S).s₀

/-! ## The map `F : P ⊗ ℤ[S] ⟶ ℤ̃[S]` -/

/-- The section `(k,x) ↦ [x] - [ẽ(k,x)]` of `ℤ̃[S]` over `(ℕ∪{∞}) × S`. -/
def Fsection : zfree (NS S) ⟶ zred S (levelData S).s₀ :=
  (zmap (pr₂N S) - zmap (ePred S)) ≫ qred S (levelData S).s₀

/-- **`F`**: the descent of `[pr₂] - [ẽ]` along `ℤ[(ℕ∪{∞}) × S] ⟶ P ⊗ ℤ[S]`. -/
def F : tmul P (zfree S) ⟶ zred S (levelData S).s₀ :=
  (Toolkit.PS_desc S (Fsection S) (ZS.F_vanishing S)).choose

theorem F_spec : EA S ≫ F S = Fsection S :=
  (Toolkit.PS_desc S (Fsection S) (ZS.F_vanishing S)).choose_spec.1

/-! ## The map `G : P ⊗ ℤ[S] ⟶ P` -/

/-- The section `(k,x) ↦ e_{ψ(k,x)}` of `P` over `(ℕ∪{∞}) × S`. -/
def Gsection : zfree (NS S) ⟶ P := zmap (psiN S) ≫ P_proj

/-- **`G`**: the descent of `zmap ψ ≫ P_proj` along `ℤ[(ℕ∪{∞}) × S] ⟶ P ⊗ ℤ[S]`. -/
def G : tmul P (zfree S) ⟶ P :=
  (Toolkit.PS_desc S (Gsection S) (ZS.G_vanishing S)).choose

theorem G_spec : EA S ≫ G S = Gsection S :=
  (Toolkit.PS_desc S (Gsection S) (ZS.G_vanishing S)).choose_spec.1

/-! ## The map `F_P : P ⊗ P ⟶ P` -/

/-- The section `(k,j) ↦ e_{φ_P(k,j)}` of `P` over `(ℕ∪{∞})²`. -/
def FPsection : zfree NS2 ⟶ P := zmap (phiP S) ≫ P_proj

/-- **`F_P`**: the descent of `zmap φ_P ≫ P_proj` along `ℤ[(ℕ∪{∞})²] ⟶ P ⊗ P`. -/
def FP : tmul P P ⟶ P :=
  (Toolkit.PP_desc (FPsection S) (ZS.FP_vanishing S).1 (ZS.FP_vanishing S).2).choose

theorem FP_spec : EApp ≫ FP S = FPsection S :=
  (Toolkit.PP_desc (FPsection S) (ZS.FP_vanishing S).1 (ZS.FP_vanishing S).2).choose_spec.1

/-! ## The corrected `(0,-)` map `s : ℤ̃[S] ⟶ P ⊗ ℤ[S]` -/

/-- `e₀ : 𝟙_ ⟶ P`, the point `e_0` of `P` (`P_proj` of the basis vector `e_0` of `ℤ[ℕ∪{∞}]`). -/
def e0 : 𝟙_ LightCondAb ⟶ P :=
  unitIso.hom ≫ zmap (ptAt (((0 : ℕ) : ℕ∪{∞}))) ≫ P_proj

/-- The map `x ↦ e₀ ⊗ x : ℤ[S] ⟶ P ⊗ ℤ[S]`. -/
def sBig : zfree S ⟶ tmul P (zfree S) :=
  (λ_ (zfree S)).inv ≫ (e0 ▷ zfree S)

/-- `ŝ' : x ↦ e₀ ⊗ ([x] - [s₀])`: the corrected `(0,-)` map on `ℤ[S]`, which kills `[s₀]`. -/
def sHat : zfree S ⟶ tmul P (zfree S) :=
  (𝟙 (zfree S) - aug S ≫ zmap (ptAt (levelData S).s₀)) ≫ sBig S

theorem sHat_vanishing : zmap (ptAt (levelData S).s₀) ≫ sHat S = 0 := by
  have h1 : zmap (ptAt (levelData S).s₀) ≫
      (𝟙 (zfree S) - aug S ≫ zmap (ptAt (levelData S).s₀)) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id]
    have h2 : zmap (ptAt (levelData S).s₀) ≫ aug S = 𝟙 (zfree pt) := by
      rw [aug, ← zmap_comp_zfree, ptAt_comp_toPt, zmap_id_zfree]
    rw [show zmap (ptAt (levelData S).s₀) ≫
          (aug S ≫ zmap (ptAt (levelData S).s₀)) =
        (zmap (ptAt (levelData S).s₀) ≫ aug S) ≫ zmap (ptAt (levelData S).s₀) from
      (Category.assoc _ _ _).symm]
    rw [h2, Category.id_comp, sub_self]
  rw [sHat, ← Category.assoc, h1, zero_comp]

/-- **`s`**: the corrected `(0,-)` map of `NOTES_LEAD_solid_gaps1.md` §3.2. -/
def s : zred S (levelData S).s₀ ⟶ tmul P (zfree S) :=
  cokernel.desc (zmap (ptAt (levelData S).s₀)) (sHat S) (sHat_vanishing S)

theorem s_spec : qred S (levelData S).s₀ ≫ s S = sHat S := cokernel.π_desc _ _ _

/-! ## The remaining maps of the scheme -/

/-- **`s_P`**: the map `e_j ↦ e₀ ⊗ e_j`. -/
def sP : P ⟶ tmul P P := (λ_ P).inv ≫ (e0 ▷ P)

/-- **`m`**: the map `P ◁ g : P ⊗ P ⟶ P ⊗ ℤ[S]` of the scheme. -/
def m : tmul P P ⟶ tmul P (zfree S) := MonoidalCategory.whiskerLeft P (g S)


/-- **Identity `h₆` of REFS/03 §1**: `m ≫ T = T' ≫ m`, which is the interchange law for the
whiskerings (`Work.ATOM.m S = P ◁ g`). -/
theorem h_six (S : LightProfinite.{0}) [Infinite S] :
    m S ≫ preShift (zfree S) = preShiftP ≫ m S :=
  MonoidalCategory.whisker_exchange oneMinusShift (g S)


end Work.ATOM
