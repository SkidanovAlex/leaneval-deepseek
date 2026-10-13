-- NOTE (WilC5 / S4OnePoint_general): a clash-free *copy* of `Submission/Work/WilC5/StepSeqLogPresAux2.lean`
-- (proved by colleagues): every import in the `StepSeqLogClosure`/`StepSeqLogPres` chain is
-- redirected to the corresponding `…Cut` copy (in which the auxiliary definition `canonSyn` is
-- renamed), because the original `Work.WilC5.canonSyn` clashes with the identically named
-- definition of `Submission/Work/WilC5/StepKeyOfValProp.lean`, which is imported transitively by
-- `Submission/Work/WilC5/ExistsStepSeq.lean`; both are needed by the final assembly of vdDMM
-- Lemma 4.4 (`StepSeqTower.lean`).

/-
  WilC5 — `StepSeqLogPresAux2`: an `LRc`-embedding of a `rexp`-reduct maps infinitesimals to
  infinitesimals (via order preservation, with all the field-theoretic compatibility supplied
  explicitly).

  This is the piece of `Work.WilC5.StepSeqLogPres` that computes with `(n : K) + 1`, its inverse and
  its negative; it is kept separate so that the proofs stay in reasonably sized modules.
-/
import Mathlib
import Submission.Work.WilC5.StepSeqLogPresAuxCut
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.S4ExpG.OrderEmbed
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.model_TR_of_dcl_closed

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section
open Classical

namespace Work.WilC5.SSLPAux

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

variable {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
  [Field K] [Field L] [LinearOrder K] [LinearOrder L]
  [IsStrictOrderedRing K] [IsStrictOrderedRing L]

/-- **A `Ring.CompatibleRing` whose ring structure is that of the `rexp`-reduct**: the composition
`LR.withConstantsStructure ℝ` built from it is the reduct up to definitional equality. -/
noncomputable def compatRingOfBridges {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K]
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hneg : ∀ x : K, Work.WilC5.negE x = -x)
    (hzero : (Work.WilC5.zeroE : K) = 0)
    (hone : (Work.WilC5.oneE : K) = 1) : FirstOrder.Ring.CompatibleRing K :=
  { toStructure := @Work.WilC5.lrcRingReduct K (Work.WilC5.instStructureLRcOfLEc K)
    funMap_add := fun x => by
      rw [Work.WilC5.lrcRingReduct_funMap]
      have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
      rw [hx]; exact hadd _ _
    funMap_mul := fun x => by
      rw [Work.WilC5.lrcRingReduct_funMap]
      have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
      rw [hx]; exact hmul _ _
    funMap_neg := fun x => by
      rw [Work.WilC5.lrcRingReduct_funMap]
      have hx : x = ![x 0] := by funext i; fin_cases i <;> rfl
      rw [hx]; exact hneg _
    funMap_zero := fun x => by
      rw [Work.WilC5.lrcRingReduct_funMap]
      rw [show x = default from Subsingleton.elim _ _]
      exact hzero
    funMap_one := fun x => by
      rw [Work.WilC5.lrcRingReduct_funMap]
      rw [show x = default from Subsingleton.elim _ _]
      exact hone }

/-- **An `LRc`-embedding of a `rexp`-reduct preserves infinitesimals**, given that it preserves
the order and that the substructure is closed under the field operations (so that all the
`(n : K) + 1`, their inverses and negatives have images). -/
theorem isInfinitesimal_map_of_embedding
    {T : @WilkiesDesign.CG.LRc.Substructure K (Work.WilC5.reductStruct K)}
    (σ' : @Embedding WilkiesDesign.CG.LRc ↥T L _ (Work.WilC5.reductStruct L))
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeK : (Work.WilC5.oneE : K) = 1) (honeL : (Work.WilC5.oneE : L) = 1)
    (hnegK : ∀ x : K, Work.WilC5.negE x = -x)
    (hnegL : ∀ x : L, Work.WilC5.negE x = -x)
    (hzeroK : (Work.WilC5.zeroE : K) = 0) (hzeroL : (Work.WilC5.zeroE : L) = 0)
    (hleT : ∀ x y : ↥T, (((x : K) ≤ (y : K)) ↔ ((σ' x : L) ≤ (σ' y))))
    (hIntT : ∀ z : ℤ, ((z : ℤ) : K) ∈ (T : Set K))
    (hNatT : ∀ m : ℕ, (((m : ℕ) : K)) ∈ (T : Set K))
    (h1T : (1 : K) ∈ (T : Set K))
    (haddcl : ∀ x ∈ (T : Set K), ∀ y ∈ (T : Set K), x + y ∈ (T : Set K))
    (hnegcl : ∀ x ∈ (T : Set K), -x ∈ (T : Set K))
    (hinvcl : ∀ x ∈ (T : Set K), x ≠ 0 → x⁻¹ ∈ (T : Set K))
    {ε : K} (hεT : ε ∈ (T : Set K)) (hε : Work.WilC5.IsInfinitesimal ε) :
    Work.WilC5.IsInfinitesimal ((σ' ⟨ε, hεT⟩ : L)) := by
  intro m
  have hcT : (((m : ℕ) : K) + 1) ∈ (T : Set K) := haddcl _ (hNatT m) _ h1T
  have hc0 : (((m : ℕ) : K) + 1) ≠ 0 := by positivity
  have hciT : ((((m : ℕ) : K) + 1))⁻¹ ∈ (T : Set K) := hinvcl _ hcT hc0
  have hnciT : -((((m : ℕ) : K) + 1))⁻¹ ∈ (T : Set K) := hnegcl _ hciT
  have hσc : (σ' ⟨(((m : ℕ) : K) + 1), hcT⟩ : L) = ((m : ℕ) : L) + 1 := by
    have h := embAdd (T := T) σ' haddK haddL ⟨((m : ℕ) : K), hNatT m⟩ ⟨(1 : K), h1T⟩ hcT
    rw [embOne (T := T) σ' honeK honeL h1T] at h
    have hnat : (σ' ⟨((m : ℕ) : K), hNatT m⟩ : L) = ((m : ℕ) : L) := by
      have he : (⟨((m : ℕ) : K), hNatT m⟩ : ↥T) = ⟨((m : ℤ) : K), hIntT (m : ℤ)⟩ := by
        apply Subtype.ext; push_cast; ring
      rw [he, embInt (T := T) σ' haddK haddL honeK honeL hnegK hnegL hzeroK hzeroL hIntT (m : ℤ)]
      push_cast; ring
    rw [hnat] at h
    exact h
  have hσci : (σ' ⟨((((m : ℕ) : K) + 1))⁻¹, hciT⟩ : L) = ((((m : ℕ) : L) + 1))⁻¹ := by
    have h := embInv (T := T) σ' hmulK hmulL honeK honeL ⟨(((m : ℕ) : K) + 1), hcT⟩ hc0 hciT
    rw [hσc] at h
    exact h
  have hσnci : (σ' ⟨-((((m : ℕ) : K) + 1))⁻¹, hnciT⟩ : L) = -((((m : ℕ) : L) + 1))⁻¹ := by
    have h := embNeg (T := T) σ' hnegK hnegL ⟨((((m : ℕ) : K) + 1))⁻¹, hciT⟩ hnciT
    rw [hσci] at h
    exact h
  have hb := hε m
  have h1 := (hleT ⟨-((((m : ℕ) : K) + 1))⁻¹, hnciT⟩ ⟨ε, hεT⟩).mp (abs_le.mp hb).1
  have h2 := (hleT ⟨ε, hεT⟩ ⟨((((m : ℕ) : K) + 1))⁻¹, hciT⟩).mp (abs_le.mp hb).2
  rw [hσnci] at h1
  rw [hσci] at h2
  rw [abs_le]
  exact ⟨h1, h2⟩

/-- **Order and positivity preservation at the `rexp`-reduct** for an `LRc`-embedding of a
`Dcl`-closed substructure into a model of `TR`. -/
theorem orderEmbed_of_dcl_closed {K L : Type}
    [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (hK : K ⊨ WilkiesDesign.CG.TE) (hL : L ⊨ WilkiesDesign.CG.TE)
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (honeK : (Work.WilC5.oneE : K) = 1)
    (hlenegK : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeL : (Work.WilC5.oneE : L) = 1)
    (hlenegL : ∀ x y : L, Work.WilC5.leE x y ↔ x ≤ y)
    (hstructK : (Work.WilC5.reductStruct K : WilkiesDesign.CG.LRc.Structure K) =
      WilkiesDesign.CG.LR.withConstantsStructure ℝ)
    (hstructL : (Work.WilC5.reductStruct L : WilkiesDesign.CG.LRc.Structure L) =
      WilkiesDesign.CG.LR.withConstantsStructure ℝ)
    {T : @WilkiesDesign.CG.LRc.Substructure K (Work.WilC5.reductStruct K)}
    (hTdcl_red : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (T : Set K) ⊆ (T : Set K))
    (σ' : @WilkiesDesign.CG.LRc.Embedding ↥T L _ (Work.WilC5.reductStruct L)) :
    (∀ x y : ↥T, (((x : K) ≤ (y : K)) ↔ ((σ' x : L) ≤ (σ' y : L)))) ∧
      (∀ a : ↥T, (0 < (a : K) ↔ 0 < (σ' a : L))) := by
  classical
  have hzK := Work.WilC5.S4ExpF.zeroE_eq_zero hK haddK
  have hnegK := fun x : K => Work.WilC5.S4ExpF.negE_eq_neg hK haddK x
  have hzL := Work.WilC5.S4ExpF.zeroE_eq_zero hL haddL
  have hnegL := fun x : L => Work.WilC5.S4ExpF.negE_eq_neg hL haddL x
  letI : FirstOrder.Ring.CompatibleRing K :=
    compatRingOfBridges haddK hmulK hnegK hzK honeK
  letI : FirstOrder.Ring.CompatibleRing L :=
    compatRingOfBridges haddL hmulL hnegL hzL honeL
  have hdclK : ∀ A : Set K, @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) A =
      @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) A :=
    fun A => congrArg (fun i => @Work.WilC2.Dcl K i A) hstructK
  have hTdcl : @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) (T : Set K)
      ⊆ (T : Set K) := fun x hx => hTdcl_red ((hdclK (T : Set K)).symm ▸ hx)
  have h0T : (0 : K) ∈ (T : Set K) :=
    hTdcl (Work.WilC5.S4ExpF.dcl_zero_mem (T : Set K))
  haveI hKTRr : @Theory.Model LRc K (reductStruct K) TR := reduct_model_TR K hK
  haveI hLTRr : @Theory.Model LRc L (reductStruct L) TR := reduct_model_TR L hL
  haveI hKTRc : @Theory.Model LRc K (LR.withConstantsStructure ℝ) TR :=
    hstructK ▸ reduct_model_TR K hK
  haveI hLTRc : @Theory.Model LRc L (LR.withConstantsStructure ℝ) TR :=
    hstructL ▸ reduct_model_TR L hL
  have hmeet : MeetsDefinable (L := LRc) (T : Set K) :=
    Eq.mpr (congrArg (fun i => @MeetsDefinable LRc K i (T : Set K)) hstructK)
      (@meetsDefinable_of_dclClosed K _ _ _ _ _ _ hOM (T : Set K) hKTRc hTdcl)
  have helem : T.IsElementary := by
    have h := MeetsDefinable.isElementary_closure (L := LRc) (M := K) (A := (T : Set K)) hmeet
    rwa [Substructure.closure_eq] at h
  haveI hTTR : (↥T) ⊨ TR :=
    (ElementarySubstructure.theory_model_iff ⟨T, helem⟩ TR).mpr (inferInstance : K ⊨ TR)
  have hleELK : ∀ x y : K, leEL x y ↔ x ≤ y := fun x y =>
    (congrArg (fun j => @leEL K j x y) hstructK) ▸ (leEL_iff_le (M := K) hKTRc x y)
  have hleELL : ∀ x y : L, leEL x y ↔ x ≤ y := fun x y =>
    (congrArg (fun j => @leEL L j x y) hstructL) ▸ (leEL_iff_le (M := L) hLTRc x y)
  have hleT := fun x y : ↥T => by
    have h1 : leEL (x : K) (y : K) ↔ leEL x y := by
      have hh := helem S4ExpG.lpLeForm2 (fun i : Fin 2 => ![x, y] i)
      rw [S4ExpG.lpLeForm2_realize, S4ExpG.lpLeForm2_realize] at hh
      simpa using hh
    have h2 : leEL (σ' x) (σ' y) ↔ leEL x y := by
      have hh := hMCr (↥T) L σ' S4ExpG.lpLeForm2 (fun i : Fin 2 => ![x, y] i)
      rw [S4ExpG.lpLeForm2_realize, S4ExpG.lpLeForm2_realize] at hh
      simpa using hh
    calc ((x : K) ≤ (y : K)) ↔ leEL (x : K) (y : K) := (hleELK _ _).symm
      _ ↔ leEL x y := h1
      _ ↔ leEL (σ' x) (σ' y) := h2.symm
      _ ↔ (σ' x : L) ≤ (σ' y) := hleELL _ _
  have hσ'0 := SSLPAux.embZero (T := T) σ' hzK hzL h0T
  have hposT : ∀ a : ↥T, (0 < (a : K) ↔ 0 < (σ' a : L)) := fun a => by
    have h1 : ((a : K) ≤ (0 : K)) ↔ ((σ' a : L) ≤ (0 : L)) := by
      simpa [hσ'0] using hleT a ⟨(0 : K), h0T⟩
    have h2 : ((0 : K) ≤ (a : K)) ↔ ((0 : L) ≤ (σ' a : L)) := by
      simpa [hσ'0] using hleT ⟨(0 : K), h0T⟩ a
    exact ⟨fun hx => lt_iff_le_not_ge.mpr ⟨h2.mp (lt_iff_le_not_ge.mp hx).1,
        (not_congr h1).mp (lt_iff_le_not_ge.mp hx).2⟩,
      fun hx => lt_iff_le_not_ge.mpr ⟨h2.mpr (lt_iff_le_not_ge.mp hx).1,
        (not_congr h1).mpr (lt_iff_le_not_ge.mp hx).2⟩⟩
  exact ⟨hleT, hposT⟩

end Work.WilC5.SSLPAux
