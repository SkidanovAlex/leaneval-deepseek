import Mathlib
import Submission.Work.WilC5.StepSeqDecomp
import Submission.Work.WilC5.StepSeqIndep
import Submission.Work.WilC5.StepSeqCutStep
import Submission.Work.WilC5.StepSeqChain
import Submission.Work.WilC5.StepSeqEstimates
import Submission.Work.WilC5.CutComp
import Submission.Work.WilC5.ClassArith
import Submission.Work.WilC5.LogDominatedOfInfinite
import Submission.Work.WilC5.S4ExpG.OrderEmbed
import Submission.Work.WilC5.S4ExpG.EmbedComm
import Submission.Work.WilC5.FOV.SubfieldClosureL
import Submission.Work.WilC5.S4ExpF.logFun_pow_nat
import Submission.Work.WilC5.S4ExpF.logFun_zpow
import Submission.Work.WilC5.LogUnitFinite
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.realizes_cut_order_preserving

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder
/-! ## Auxiliary lemmas (private to this file) -/

/-- `realConst K (N : ℝ) = (N : K)` at the `rexp`-reduct of a model of `TE`.

The proof follows `Work.WilC5.StepSeqLogDominated`: locally replace the `Ring`/`rexpL`/`constantsOn`
instances by the `rexp`-reduct ones (the "instance pinning" of `StepSeqDecomp`) so that the
syntactic `LRc`-structure is the reduct; then `Work.WilC5.reductStruct_eq_withConstants` and
`Work.WilC5.realConst_natCast` give the claim, and `Work.WilC5.realConst_reduct_synth` transports it
back to the reduct. -/
theorem sscb_realConst_natCast {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hK : K ⊨ WilkiesDesign.CG.TE)
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y) :
    ∀ N : ℕ, Work.WilC5.realConst K (N : ℝ) = (N : K) := by
  have hTE : K ⊨ WilkiesDesign.CG.TE := hK
  let myCR : FirstOrder.Ring.CompatibleRing K :=
    { toStructure := @Work.WilC5.lrcRingReduct K (Work.WilC5.instStructureLRcOfLEc K)
      funMap_add := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact hadd _ _
      funMap_mul := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact hmul _ _
      funMap_neg := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact Work.WilC5.S4ExpF.negE_eq_neg hTE hadd _
      funMap_zero := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show ys = default from Subsingleton.elim _ _]
        exact Work.WilC5.S4ExpF.zeroE_eq_zero hTE hadd
      funMap_one := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show ys = default from Subsingleton.elim _ _]
        exact hone }
  letI : FirstOrder.Ring.CompatibleRing K := myCR
  letI hRX : WilkiesDesign.CG.rexpL.Structure K :=
    @Work.WilC5.lrcRexpReduct K (Work.WilC5.reductStruct K)
  letI hCT : (FirstOrder.Language.constantsOn ℝ).Structure K :=
    @Work.WilC5.lrcConstReduct K (Work.WilC5.reductStruct K)
  have hstruct : (Work.WilC5.reductStruct K : LRc.Structure K) = LR.withConstantsStructure ℝ :=
    Work.WilC5.reductStruct_eq_withConstants (M := K)
  have hTR : @FirstOrder.Language.Theory.Model LRc K (LR.withConstantsStructure ℝ)
      WilkiesDesign.CG.TR :=
    hstruct ▸ (Work.WilC5.reduct_model_TR K hTE)
  have hnatC : ∀ N : ℕ,
      @Work.WilC5.realConst K (LR.withConstantsStructure ℝ) (N : ℝ) = (N : K) :=
    fun N => @Work.WilC5.realConst_natCast K _ _ _ _ _ _ hTR N
  intro N
  exact (Work.WilC5.realConst_reduct_synth (M := K) N).trans (hnatC N)

/-- Positivity of the elements of a `StepSeq`, in the order of the field. -/
theorem sscb_xs_pos {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hTE : K ⊨ WilkiesDesign.CG.TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {B : WilkiesDesign.CG.LRc.Substructure K} (S : Work.WilC5.StepSeq B) (n : ℕ) :
    0 < S.xs n :=
  (Work.WilC5.S4ExpF.leE_zero_iff hTE hadd hleneg (S.xs n)).mp (S.hpos n)

/-- The elements of an `Unbounded` `StepSeq` exceed every natural number. -/
theorem sscb_xs_big {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (hnat : ∀ N : ℕ, Work.WilC5.realConst K (N : ℝ) = (N : K))
    {B : WilkiesDesign.CG.LRc.Substructure K} {S : Work.WilC5.StepSeq B}
    (hunb : Work.WilC5.StepSeq.Unbounded S) (n : ℕ) (N : ℕ) :
    (N : K) < S.xs n := by
  obtain ⟨h1, h2⟩ := hunb n N
  have h1' : Work.WilC5.realConst K (N : ℝ) ≤ S.xs n := (hleneg _ _).mp h1
  have h2' : ¬ (S.xs n ≤ Work.WilC5.realConst K (N : ℝ)) :=
    fun h => h2 ((hleneg _ _).mpr h)
  rw [hnat N] at h1' h2'
  exact lt_of_le_of_ne h1' (fun hh => h2' (le_of_eq hh.symm))

/-- An infinite element in the sense above is not `IsFiniteVal`. -/
theorem sscb_not_finite {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x : K} (hbig : ∀ N : ℕ, (N : K) < x) : ¬ Work.WilC5.IsFiniteVal x := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin
  have h := hbig (N + 1)
  have hcast : (((N + 1 : ℕ)) : K) = (N : K) + 1 := by push_cast; ring
  rw [hcast] at h
  have hle := (abs_le.mp hN).2
  linarith

/-- Every nonnegative element of a model of `TE` is a square (the local instance-pinning of
`Work.WilC5.StepSeqLogDominated` reduces this to `Work.WilC2.model_exists_sq`). -/
theorem sscb_exists_sq {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hK : K ⊨ WilkiesDesign.CG.TE)
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y) :
    ∀ x : K, 0 ≤ x → ∃ z : K, x = z * z := by
  have hTE : K ⊨ WilkiesDesign.CG.TE := hK
  let myCR : FirstOrder.Ring.CompatibleRing K :=
    { toStructure := @Work.WilC5.lrcRingReduct K (Work.WilC5.instStructureLRcOfLEc K)
      funMap_add := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact hadd _ _
      funMap_mul := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact hmul _ _
      funMap_neg := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact Work.WilC5.S4ExpF.negE_eq_neg hTE hadd _
      funMap_zero := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show ys = default from Subsingleton.elim _ _]
        exact Work.WilC5.S4ExpF.zeroE_eq_zero hTE hadd
      funMap_one := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show ys = default from Subsingleton.elim _ _]
        exact hone }
  letI : FirstOrder.Ring.CompatibleRing K := myCR
  letI hRX : WilkiesDesign.CG.rexpL.Structure K :=
    @Work.WilC5.lrcRexpReduct K (Work.WilC5.reductStruct K)
  letI hCT : (FirstOrder.Language.constantsOn ℝ).Structure K :=
    @Work.WilC5.lrcConstReduct K (Work.WilC5.reductStruct K)
  have hstruct : (Work.WilC5.reductStruct K : LRc.Structure K) = LR.withConstantsStructure ℝ :=
    Work.WilC5.reductStruct_eq_withConstants (M := K)
  have hTR : @FirstOrder.Language.Theory.Model LRc K (LR.withConstantsStructure ℝ)
      WilkiesDesign.CG.TR :=
    hstruct ▸ (Work.WilC5.reduct_model_TR K hTE)
  intro x hx
  exact Work.WilC2.model_exists_sq (M := K) hTR x hx

/-- `leE` is the order of the field, in a model of `TE`. -/
theorem sscb_leE_iff_le {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hsub : ∀ x y : K, Work.WilC5.subE x y = x - y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hex : ∀ x : K, 0 ≤ x → ∃ z : K, x = z * z) :
    ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y := by
  intro x y
  constructor
  · rintro ⟨z, hz⟩
    have h1 : z * z = y - x := by rw [← hsub, ← hmul]; exact hz
    have h2 : (0 : K) ≤ y - x := by rw [← h1]; exact mul_self_nonneg z
    linarith
  · intro hxy
    obtain ⟨z, hz⟩ := hex (y - x) (by linarith)
    refine ⟨z, ?_⟩
    rw [hsub, hmul]
    exact hz.symm

/-- The definable logarithm is strictly increasing on positive elements, in field form. -/
theorem sscb_log_lt {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hK : K ⊨ WilkiesDesign.CG.TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y) :
    ∀ {x y : K}, 0 < x → 0 < y → (Work.WilC5.logFun x < Work.WilC5.logFun y ↔ x < y) := by
  intro x y hx hy
  have hx0 : Work.WilC5.leE Work.WilC5.zeroE x ∧ ¬ Work.WilC5.leE x Work.WilC5.zeroE :=
    (Work.WilC5.S4ExpF.leE_zero_iff hK hadd hleneg x).mpr hx
  have hy0 : Work.WilC5.leE Work.WilC5.zeroE y ∧ ¬ Work.WilC5.leE y Work.WilC5.zeroE :=
    (Work.WilC5.S4ExpF.leE_zero_iff hK hadd hleneg y).mpr hy
  have hxl : Work.WilC5.expE (Work.WilC5.logFun x) = x :=
    Work.WilC5.expE_logFun_of_pos_of_model hK hx0
  have hyl : Work.WilC5.expE (Work.WilC5.logFun y) = y :=
    Work.WilC5.expE_logFun_of_pos_of_model hK hy0
  have h := Work.WilC5.expE_lt_expE_iff_of_model hK (Work.WilC5.logFun x) (Work.WilC5.logFun y)
  rw [hxl, hyl] at h
  rw [hleneg, hleneg, hleneg, hleneg] at h
  have h' : (x < y) ↔ (Work.WilC5.logFun x < Work.WilC5.logFun y) := by
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
    exact h
  exact h'.symm

/-- The coercion to `M` of an `LRc`-symbol applied inside a substructure. -/
theorem sscb_sub_coe {M : Type} [LRc.Structure M] {T : WilkiesDesign.CG.LRc.Substructure M}
    {n : ℕ} (f : LRc.Functions n) (xs : Fin n → ↥T) :
    ((@FirstOrder.Language.Structure.funMap LRc ↥T _ n f xs : ↥T) : M)
      = @FirstOrder.Language.Structure.funMap LRc M _ n f (fun i => (xs i : M)) := by
  have h := @FirstOrder.Language.Embedding.map_fun' LRc ↥T M _ _
    (Substructure.subtype T) n f xs
  have h2 : (fun i => ((xs i : ↥T) : M)) = (⇑(Substructure.subtype T).toEmbedding ∘ xs) := by
    funext i; rfl
  rw [h2]
  exact h

/-- The coercion of a product inside a substructure. -/
theorem sscb_coe_mul {M : Type} [LEc.Structure M] [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hmul : ∀ x y : M, Work.WilC5.mulE x y = x * y)
    {T : WilkiesDesign.CG.LRc.Substructure M} (u v : ↥T) :
    ((Work.WilC5.mulEL u v : ↥T) : M) = (u : M) * (v : M) := by
  change ((@FirstOrder.Language.Structure.funMap LRc ↥T _ 2
    (Sum.inl (Sum.inl Ring.mulFunc)) ![u, v] : ↥T) : M) = (u : M) * (v : M)
  have h := sscb_sub_coe (Sum.inl (Sum.inl Ring.mulFunc)) ![u, v]
  have h2 : (fun i : Fin 2 => ((![u, v] i : ↥T) : M)) = ![(u : M), (v : M)] := by
    funext i; fin_cases i <;> rfl
  rw [h2] at h
  rw [h]
  exact hmul (u : M) (v : M)

/-- The coercion of a sum inside a substructure. -/
theorem sscb_coe_add {M : Type} [LEc.Structure M] [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hadd : ∀ x y : M, Work.WilC5.addE x y = x + y)
    {T : WilkiesDesign.CG.LRc.Substructure M} (u v : ↥T) :
    ((Work.WilC5.addEL u v : ↥T) : M) = (u : M) + (v : M) := by
  change ((@FirstOrder.Language.Structure.funMap LRc ↥T _ 2
    (Sum.inl (Sum.inl Ring.addFunc)) ![u, v] : ↥T) : M) = (u : M) + (v : M)
  have h := sscb_sub_coe (Sum.inl (Sum.inl Ring.addFunc)) ![u, v]
  have h2 : (fun i : Fin 2 => ((![u, v] i : ↥T) : M)) = ![(u : M), (v : M)] := by
    funext i; fin_cases i <;> rfl
  rw [h2] at h
  rw [h]
  exact hadd (u : M) (v : M)

/-- The coercion of a negation inside a substructure. -/
theorem sscb_coe_neg {M : Type} [LEc.Structure M] [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hneg : ∀ x : M, Work.WilC5.negE x = -x)
    {T : WilkiesDesign.CG.LRc.Substructure M} (u : ↥T) :
    ((Work.WilC5.negEL u : ↥T) : M) = -(u : M) := by
  change ((@FirstOrder.Language.Structure.funMap LRc ↥T _ 1
    (Sum.inl (Sum.inl Ring.negFunc)) ![u] : ↥T) : M) = -(u : M)
  have h := sscb_sub_coe (Sum.inl (Sum.inl Ring.negFunc)) ![u]
  have h2 : (fun i : Fin 1 => ((![u] i : ↥T) : M)) = ![(u : M)] := by
    funext i; fin_cases i <;> rfl
  rw [h2] at h
  rw [h]
  exact hneg (u : M)

/-- An `LRc`-embedding out of a substructure of `K` all of whose positive elements have square
roots in the substructure preserves the order. -/
theorem sscb_emb_order {K L : Type} [LEc.Structure K] [LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hnegK : ∀ x : K, Work.WilC5.negE x = -x)
    (hleEL : ∀ x y : L, Work.WilC5.leEL x y → x ≤ y)
    {F : WilkiesDesign.CG.LRc.Substructure K}
    (hsub : ∀ a b : K, a ∈ (F : Set K) → b ∈ (F : Set K) → a - b ∈ (F : Set K))
    (hroot : ∀ a : K, a ∈ (F : Set K) → 0 < a → ∃ z : K, z ∈ (F : Set K) ∧ z * z = a)
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L) :
    (∀ a b : ↥F, (((a : K) ≤ (b : K)) ↔ ((σ a : L) ≤ (σ b : L)))) := by
  have hcoe_mul : ∀ u v : ↥F, ((Work.WilC5.mulEL u v : ↥F) : K) = (u : K) * (v : K) :=
    fun u v => sscb_coe_mul (M := K) hmulK u v
  have hcoe_add : ∀ u v : ↥F, ((Work.WilC5.addEL u v : ↥F) : K) = (u : K) + (v : K) :=
    fun u v => sscb_coe_add (M := K) haddK u v
  have hcoe_neg : ∀ u : ↥F, ((Work.WilC5.negEL u : ↥F) : K) = -(u : K) :=
    fun u => sscb_coe_neg (M := K) hnegK u
  have hcoe_sub : ∀ u v : ↥F, ((Work.WilC5.subEL u v : ↥F) : K) = (u : K) - (v : K) := by
    intro u v
    rw [show ((Work.WilC5.subEL u v : ↥F) : K)
        = ((Work.WilC5.addEL u (Work.WilC5.negEL v) : ↥F) : K) from rfl, hcoe_add, hcoe_neg]
    ring
  have hleEL_sub : ∀ u v : ↥F, (Work.WilC5.leEL u v ↔ (u : K) ≤ (v : K)) := by
    intro u v
    constructor
    · rintro ⟨w, hw⟩
      have h4 : (w : K) * (w : K) = (v : K) - (u : K) := by
        have hh : ((Work.WilC5.mulEL w w : ↥F) : K) = ((Work.WilC5.subEL v u : ↥F) : K) :=
          congrArg Subtype.val hw
        rw [hcoe_mul, hcoe_sub] at hh
        exact hh
      have h5 : (0 : K) ≤ (v : K) - (u : K) := by rw [← h4]; exact mul_self_nonneg _
      linarith
    · intro huv
      rcases lt_or_eq_of_le huv with hlt | heq
      · obtain ⟨z, hzF, hz2⟩ := hroot ((v : K) - (u : K)) (hsub (v : K) (u : K) v.2 u.2)
          (by linarith)
        refine ⟨⟨z, hzF⟩, ?_⟩
        apply Subtype.ext
        rw [hcoe_mul, hcoe_sub, hz2]
      · have huv' : u = v := Subtype.ext heq
        rw [huv']
        refine ⟨⟨(0 : K), ?_⟩, ?_⟩
        · rw [← sub_self (u : K)]; exact hsub (u : K) (u : K) u.2 u.2
        · apply Subtype.ext
          rw [hcoe_mul, hcoe_sub]
          ring
  have fwd : ∀ a b : ↥F, (a : K) ≤ (b : K) → (σ a : L) ≤ (σ b : L) := by
    intro a b hab
    exact hleEL (σ a) (σ b)
      (Work.WilC5.map_leEL_of_embedding σ ((hleEL_sub a b).mpr hab))
  intro a b
  refine ⟨fwd a b, ?_⟩
  intro hcon
  by_contra hbad
  have hba : (b : K) ≤ (a : K) := le_of_lt (lt_of_not_ge hbad)
  have h1 : (σ b : L) ≤ (σ a : L) := fwd b a hba
  have h2 : (σ b : L) ≠ (σ a : L) := by
    intro h
    have h' : b = a := σ.injective h
    exact hbad (le_of_eq (congrArg Subtype.val h').symm)
  exact absurd hcon (not_le.mpr (lt_of_le_of_ne h1 h2))



/-- Two positive elements of the same archimedean class lie on the same side of any element whose
class differs from theirs. -/
theorem sscb_same_arch_cut {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {w b t : F} (hw : 0 < w) (hb : 0 < b) (ht : 0 < t)
    (hsame : Work.WilC5.SameArch w b) (hnew : ¬ Work.WilC5.SameArch b t) :
    (w < t ↔ b < t) ∧ (t < w ↔ t < b) := by
  obtain ⟨hVLeL, hVLeR, -, -, hcross, hsame_cut⟩ :=
    Work.WilC5.ClassArith (F := F)
  have hwt : ¬ Work.WilC5.SameArch w t :=
    fun h => hnew (Work.WilC5.SameArch_equiv.trans (Work.WilC5.SameArch_equiv.symm hsame) h)
  refine ⟨hsame_cut hw hb hsame hwt, ?_⟩
  rw [(hcross ht hw (fun h => hwt (Work.WilC5.SameArch_equiv.symm h))).1,
    (hcross ht hb (fun h => hnew (Work.WilC5.SameArch_equiv.symm h))).1,
    hVLeL hsame, hVLeR hsame]

/-- Natural numerals in a subset closed under `0`, `1` and `+`. -/
theorem sscb_natCast_mem {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {S : Set K} (h0 : (0 : K) ∈ S) (h1 : (1 : K) ∈ S)
    (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) : ∀ m : ℕ, (m : K) ∈ S := by
  intro m
  induction m with
  | zero => simpa using h0
  | succ j ih =>
      have hcast : (((j + 1 : ℕ)) : K) = (j : K) + 1 := by push_cast; ring
      rw [hcast]
      exact hadd _ ih _ h1

/-- Integer numerals in a subset closed under `0`, `1`, `-` and `+`. -/
theorem sscb_intCast_mem {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {S : Set K} (h0 : (0 : K) ∈ S) (h1 : (1 : K) ∈ S)
    (hneg : ∀ a ∈ S, -a ∈ S) (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) :
    ∀ k : ℤ, (k : K) ∈ S := by
  intro k
  rcases Int.eq_nat_or_neg k with ⟨m, hm | hm⟩
  · rw [hm]; simpa using sscb_natCast_mem h0 h1 hadd m
  · rw [hm]
    have hcast : ((-(m : ℤ) : ℤ) : K) = -((m : K)) := by push_cast; ring
    rw [hcast]
    exact hneg _ (sscb_natCast_mem h0 h1 hadd m)

/-- Integer powers of a positive element of a subset closed under `1`, `*` and `⁻¹`. -/
theorem sscb_zpow_mem {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {S : Set K} (h1 : (1 : K) ∈ S) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hinv : ∀ a ∈ S, a ≠ 0 → a⁻¹ ∈ S) :
    ∀ (x : K), x ∈ S → 0 < x → ∀ z : ℤ, x ^ z ∈ S := by
  intro x hx hxp z
  have hpowN : ∀ k : ℕ, x ^ k ∈ S := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ]; exact hmul _ ih _ hx
  rcases Int.eq_nat_or_neg z with ⟨k, hk | hk⟩
  · rw [hk, zpow_natCast]; exact hpowN k
  · rw [hk, zpow_neg, zpow_natCast]
    exact hinv _ (hpowN k) (pow_ne_zero k (ne_of_gt hxp))

/-- An order-preserving embedding of a substructure of `K` into an ordered field sends positive
elements to positive elements. -/
theorem sscb_emb_pos {K L : Type} [LEc.Structure K] [LEc.Structure L] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    {F : WilkiesDesign.CG.LRc.Substructure K} (hF0 : (0 : K) ∈ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L) (hσ0 : σ ⟨(0 : K), hF0⟩ = (0 : L))
    (hσord : ∀ a b : ↥F, ((a : K) ≤ (b : K) ↔ (σ a : L) ≤ (σ b : L))) :
    ∀ a : ↥F, 0 < (a : K) → 0 < (σ a : L) := by
  intro a ha
  have hle : (σ ⟨(0 : K), hF0⟩ : L) ≤ σ a := (hσord ⟨(0 : K), hF0⟩ a).mp (le_of_lt ha)
  rw [hσ0] at hle
  refine lt_of_le_of_ne hle (Ne.symm fun h => ?_)
  have hinj : a = ⟨(0 : K), hF0⟩ := σ.injective (h.trans hσ0.symm)
  exact (ne_of_gt ha) (by simpa using congrArg Subtype.val hinj)

end Work.WilC5
