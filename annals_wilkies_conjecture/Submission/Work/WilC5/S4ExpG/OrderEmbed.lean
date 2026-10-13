import Mathlib
import Submission.Work.WilC5.S4ExpG.EmbedComm
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.tr_leE_axioms

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilC5.S4ExpG

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 5. An `LRc`-embedding of a `Dcl`-closed substructure preserves the order

`S ≤ K` is `Dcl`-closed, hence an *elementary* `LRc`-substructure of `K` (`hOM`), and
`S ⊨ TR` (`model_TR_of_dcl_closed`); since `TR` is model complete (`hMCr`), an `LRc`-embedding
`σ' : S ↪ L` into another model of `TR` is *elementary*.  Applying elementarity to the
two-variable `LRc`-formula whose realization is the definable order `leEL x y := ∃z, z*z = y-x`
(which is the field order by `leEL_iff_le`) gives both directions of the order preservation.
The argument is the one used in `Work.WilC5.StepExpCut`. -/

/-- The two-variable `LRc`-formula whose realization is `leEL`. -/
def lpLeForm2 : LRc.Formula (Fin 2) :=
  Work.WilC5.leFormL (Term.var (Sum.inl (0 : Fin 2))) (Term.var (Sum.inl (1 : Fin 2)))

theorem lpLeForm2_realize {M : Type} [LRc.Structure M] (v : Fin 2 → M) :
    lpLeForm2.Realize v ↔ Work.WilC5.leEL (v 0) (v 1) := by
  have h := Work.WilC5.leFormL_realize (t₁ := Term.var (Sum.inl (0 : Fin 2)))
    (t₂ := Term.var (Sum.inl (1 : Fin 2))) (v := v) (xs := (default : Fin 0 → M))
  simpa [lpLeForm2, Formula.Realize, Term.realize_var] using h

theorem lpOrderEmbed {K L : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [LEc.Structure L] [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    [FirstOrder.Ring.CompatibleRing L] [WilkiesDesign.CG.rexpL.Structure L]
    [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
    (S : WilkiesDesign.CG.LRc.Substructure K)
    (hSdcl : @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) (S : Set K)
      ⊆ (S : Set K))
    (σ' : WilkiesDesign.CG.LRc.Embedding ↥S L) :
    (∀ x y : ↥S, (((x : K) ≤ (y : K)) ↔ ((σ' x : L) ≤ (σ' y)))) ∧
      (∀ x : ↥S, (0 < (x : K) ↔ 0 < (σ' x : L))) := by
  have hSie : S.IsElementary := by
    have hmeet : FirstOrder.Language.MeetsDefinable (L := LRc) (S : Set K) :=
      Work.WilC5.meetsDefinable_of_dclClosed hOM hSdcl
    have h := FirstOrder.Language.MeetsDefinable.isElementary_closure (L := LRc) (M := K)
      (A := (S : Set K)) hmeet
    rwa [Substructure.closure_eq] at h
  have hSTR : (↥S) ⊨ WilkiesDesign.CG.TR :=
    Work.WilC5.model_TR_of_dcl_closed hOM S hSdcl
  have hle : ∀ x y : ↥S, (((x : K) ≤ (y : K)) ↔ ((σ' x : L) ≤ (σ' y))) := by
    intro x y
    have h1 : Work.WilC5.leEL (x : K) (y : K) ↔ Work.WilC5.leEL x y := by
      have hh := hSie lpLeForm2 (fun i : Fin 2 => ![x, y] i)
      rw [lpLeForm2_realize, lpLeForm2_realize] at hh
      simpa using hh
    have h2 : Work.WilC5.leEL (σ' x) (σ' y) ↔ Work.WilC5.leEL x y := by
      haveI := hSTR
      have hh := hMCr (↥S) L σ' lpLeForm2 (fun i : Fin 2 => ![x, y] i)
      rw [lpLeForm2_realize, lpLeForm2_realize] at hh
      simpa using hh
    calc ((x : K) ≤ (y : K))
        ↔ Work.WilC5.leEL (x : K) (y : K) :=
          (Work.WilC5.leEL_iff_le (M := K) (inferInstance : K ⊨ WilkiesDesign.CG.TR)
            (x : K) (y : K)).symm
      _ ↔ Work.WilC5.leEL x y := h1
      _ ↔ Work.WilC5.leEL (σ' x) (σ' y) := h2.symm
      _ ↔ (σ' x : L) ≤ (σ' y) :=
          Work.WilC5.leEL_iff_le (M := L) (inferInstance : L ⊨ WilkiesDesign.CG.TR)
            (σ' x) (σ' y)
  refine ⟨hle, ?_⟩
  have h0S : (0 : K) ∈ S := by
    have h := hSdcl (Work.WilC5.S4ExpF.dcl_zero_mem (S : Set K))
    exact h
  have hz0 : σ' ⟨(0 : K), h0S⟩ = (0 : L) :=
    lpEmbed_zero S σ' h0S
  intro x
  have h1 : ((x : K) ≤ (0 : K)) ↔ (σ' x ≤ (0 : L)) := by
    simpa [hz0] using hle x ⟨(0 : K), h0S⟩
  have h2 : ((0 : K) ≤ (x : K)) ↔ ((0 : L) ≤ σ' x) := by
    simpa [hz0] using hle ⟨(0 : K), h0S⟩ x
  constructor
  · intro hx
    have hx' := lt_iff_le_not_ge.mp hx
    exact lt_iff_le_not_ge.mpr ⟨h2.mp hx'.1, (not_congr h1).mp hx'.2⟩
  · intro hx
    have hx' := lt_iff_le_not_ge.mp hx
    exact lt_iff_le_not_ge.mpr ⟨h2.mpr hx'.1, (not_congr h1).mpr hx'.2⟩

end Work.WilC5.S4ExpG
