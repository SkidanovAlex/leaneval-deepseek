import Mathlib
import Submission.Work.WilC5.S4OnePointCases
import Submission.Work.WilC5.S4OnePoint
import Submission.Work.WilC5.dmm42_cut_extend
import Submission.Work.WilC5.realizes_cut
import Submission.Work.WilC5.expE_lt_iff_logFun_lt
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.valIneq_span
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.ExistsEmbeddingClosurePoint
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.expE_add_of_model
import Submission.Work.WilC5.expE_of_logFun_preserving
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.dclClosed_substructure
import Submission.Work.WilC5.dcl_substructure_subset
import Submission.Work.WilC5.extends_elemOn_sat
import Submission.Work.WilC5.elemOn_insert_of_type
import Submission.Work.WilC5.stdPart
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC4.dcl_inv
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC2.meetsDefinable_dcl
import Submission.Work.WilC2.dcl_exchange
import Submission.Work.WilC2.Square
import Submission.Work.WilC5.S4Exp.va_exp
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.S4ExpG.cut_exp_aux
import Submission.Work.WilC5.S4ExpG.Glue
import Submission.Work.WilC5.S4ExpG.hynew_exp_aux
import Submission.Work.WilC5.S4ExpG.logPreserving_exp_aux
import Submission.Work.WilC5.S4ExpF.logclosure_exp

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

attribute [local instance] Work.WilC5.reductStruct

theorem S4OnePoint_exp_proved (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels) (hVI : WilkiesDesign.CG.ValIneq) :
    Work.WilC5.S4OnePoint_exp := by
  classical
  intro K L instK instL hK hL κ hκ hsat A hA σ hlog x hx hxa
  -- ------------------------------------------------------------------ #
  -- the canonical ordered-field data on `K` and on `L`
  -- ------------------------------------------------------------------ #
  letI : LRc.Structure K := reductStruct K
  have hKTR : K ⊨ TR := reduct_model_TR K hK
  have hKfld : K ⊨ Theory.field := tr_ring_field K hKTR
  letI : Field K := trField K hKTR
  letI : LinearOrder K := trLinearOrder K hKTR
  letI : Ring.CompatibleRing K := FirstOrder.Field.compatibleRingOfModelField K
  letI : IsStrictOrderedRing K := tr_isStrictOrderedRing K hKTR
  letI : LRc.Structure L := reductStruct L
  have hLTR : L ⊨ TR := reduct_model_TR L hL
  have hLfld : L ⊨ Theory.field := tr_ring_field L hLTR
  letI : Field L := trField L hLTR
  letI : LinearOrder L := trLinearOrder L hLTR
  letI : Ring.CompatibleRing L := FirstOrder.Field.compatibleRingOfModelField L
  letI : IsStrictOrderedRing L := tr_isStrictOrderedRing L hLTR
  have hstructK : (reductStruct K : LRc.Structure K) = (LR.withConstantsStructure ℝ) :=
    reductStruct_eq_withConstants
  have hstructL : (reductStruct L : LRc.Structure L) = (LR.withConstantsStructure ℝ) :=
    reductStruct_eq_withConstants
  have hKTRsyn : @Theory.Model LRc K (LR.withConstantsStructure ℝ) TR := hstructK ▸ hKTR
  have hLTRsyn : @Theory.Model LRc L (LR.withConstantsStructure ℝ) TR := hstructL ▸ hLTR
  obtain ⟨a, ha⟩ := hxa
  -- ------------------------------------------------------------------ #
  -- the domain `A` at the syntactic `LRc`-structure, with the same carrier
  -- ------------------------------------------------------------------ #
  let As : @FirstOrder.Language.Substructure LRc K (LR.withConstantsStructure ℝ) :=
    mkSubAt K _ (A : Set K) (fun {n} f y hy => by
      rw [funMap_reduct_synth]; exact A.fun_mem f y hy)
  have hAscoe : (As : Set K) = (A : Set K) := rfl
  -- ------------------------------------------------------------------ #
  -- closure facts
  -- ------------------------------------------------------------------ #
  have hdclRed : @Work.WilC2.Dcl K (reductStruct K) (As : Set K) ⊆ (As : Set K) := by
    intro z hz
    rw [hAscoe] at hz ⊢
    exact hA.dcl_closed hz
  have hlogRed : LogClosed (As : Set K) := fun z hz => hA.log_closed z (by rwa [hAscoe] at hz)
  -- bridges between the two `LRc`-structures, stated before the switch
  -- the function induced by `σ` on the new domain
  let σfun : ↥As → L := fun b => σ ⟨(b : K), mem_congr hAscoe b.2⟩
  have hσfun_inj : Function.Injective σfun := by
    intro u v huv
    have h : (⟨(u : K), mem_congr hAscoe u.2⟩ : ↥A)
        = ⟨(v : K), mem_congr hAscoe v.2⟩ := σ.injective huv
    exact Subtype.ext (congrArg (fun z : ↥A => (z : K)) h)
  have hσfun_map : ∀ {n : ℕ} (f : LRc.Functions n) (y : Fin n → ↥As),
      σfun (@Structure.funMap LRc ↥As
          (@FirstOrder.Language.Substructure.inducedStructure LRc K
            (LR.withConstantsStructure ℝ) As) n f y)
        = @Structure.funMap LRc L (LR.withConstantsStructure ℝ) n f (σfun ∘ y) := by
    intro n f y
    let w : Fin n → ↥A := fun i => ⟨(y i : K), mem_congr hAscoe (y i).2⟩
    have hLHS : σfun (@Structure.funMap LRc ↥As _ n f y)
        = σ (@Structure.funMap LRc ↥A _ n f w) := by
      apply congrArg σ
      apply Subtype.ext
      show @Structure.funMap LRc K (LR.withConstantsStructure ℝ) n f (fun i => (y i : K))
        = @Structure.funMap LRc K (reductStruct K) n f (fun i => (w i : K))
      exact funMap_reduct_synth f (fun i => (w i : K))
    have hRHS : @Structure.funMap LRc L (LR.withConstantsStructure ℝ) n f (σfun ∘ y)
        = @Structure.funMap LRc L (reductStruct L) n f (σ ∘ w) := by
      show @Structure.funMap LRc L (LR.withConstantsStructure ℝ) n f (σfun ∘ y)
        = @Structure.funMap LRc L (reductStruct L) n f (σ ∘ w)
      exact funMap_reduct_synth f (σ ∘ w)
    rw [hLHS, hRHS]
    exact @FirstOrder.Language.Embedding.map_fun' LRc ↥A L _ _ σ n f w
  let σsyn : @FirstOrder.Language.Embedding LRc ↥As L
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (LR.withConstantsStructure ℝ) As)
      (LR.withConstantsStructure ℝ) :=
    @Embedding.mk LRc ↥As L
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (LR.withConstantsStructure ℝ) As)
      (LR.withConstantsStructure ℝ) ⟨σfun, hσfun_inj⟩ hσfun_map
      (by intro n R x; exact nomatch R)
  -- ------------------------------------------------------------------ #
  -- from here on: the syntactic `LRc`-structure
  -- ------------------------------------------------------------------ #
  letI : LRc.Structure K := LR.withConstantsStructure ℝ
  letI : LRc.Structure L := LR.withConstantsStructure ℝ
  haveI hKTRsyn' : @Theory.Model LRc K (inferInstance) TR := hKTRsyn
  haveI hLTRsyn' : @Theory.Model LRc L (inferInstance) TR := hLTRsyn
  have hdclSynth : @Work.WilC2.Dcl K (inferInstance) (As : Set K) ⊆ (As : Set K) := by
    have h1 : @Work.WilC2.Dcl K (inferInstance) (As : Set K)
        = @Work.WilC2.Dcl K (reductStruct K) (As : Set K) :=
      congrArg (fun i => @Work.WilC2.Dcl K i (As : Set K)) hstructK.symm
    intro z hz
    rw [h1] at hz
    exact hdclRed hz
  have hAsTR : (As : Type) ⊨ TR := by
    haveI : @Theory.Model LRc K (inferInstance) TR := hKTRsyn
    exact model_TR_of_dcl_closed (M := K) hOM As hdclSynth
  have hAsElem : As.IsElementary := by
    have hmeet : FirstOrder.Language.MeetsDefinable (L := LRc) (As : Set K) :=
      meetsDefinable_of_dclClosed hOM hdclSynth
    have h := FirstOrder.Language.MeetsDefinable.isElementary_closure (L := LRc) (M := K)
      (A := (As : Set K)) hmeet
    rwa [FirstOrder.Language.Substructure.closure_eq] at h
  let ES : LRc.ElementarySubstructure K := ⟨As, hAsElem⟩
  -- ------------------------------------------------------------------ #
  -- `σfun` as an `LRc`-embedding
  -- ------------------------------------------------------------------ #
  -- ------------------------------------------------------------------ #
  -- the order on `K` in `leE`-form, and the cut of `x` over `As`
  -- ------------------------------------------------------------------ #
  have hmulE : ∀ u v : K, mulE u v = u * v := by
    intro u v; rw [mulE]; exact FirstOrder.Ring.CompatibleRing.funMap_mul ![u, v]
  have haddE : ∀ u v : K, addE u v = u + v := by
    intro u v; rw [addE]; exact FirstOrder.Ring.CompatibleRing.funMap_add ![u, v]
  have hnegE : ∀ u : K, negE u = -u := by
    intro u; rw [negE]; exact FirstOrder.Ring.CompatibleRing.funMap_neg ![u]
  have hsubE : ∀ u v : K, subE u v = u - v := by
    intro u v; rw [subE, haddE, hnegE]; ring
  have hleE : ∀ u v : K, leE u v ↔ u ≤ v := by
    intro u v
    rw [leE, isSquare]
    constructor
    · rintro ⟨z, hz⟩
      rw [hmulE z z, hsubE v u] at hz
      nlinarith [mul_self_nonneg z]
    · intro h
      obtain ⟨z, hz⟩ := Work.WilC2.model_exists_sq (M := K) hKTRsyn (v - u) (sub_nonneg.mpr h)
      exact ⟨z, by rw [hmulE z z, hsubE v u]; exact hz.symm⟩
  set y : L := expE (σsyn ⟨a, mem_congr hAscoe a.2⟩) with hydef
  have hmemAsOf : ∀ f : ↥As, logFun (f : K) ∈ (As : Set K) :=
    fun f => mem_congr hAscoe.symm (hA.log_closed (f : K) (mem_congr hAscoe f.2))
  have hσlog : ∀ f : ↥As, σsyn ⟨logFun (f : K), hmemAsOf f⟩ = logFun (σsyn f) := by
    intro f
    have hf := hlog (⟨(f : K), mem_congr hAscoe f.2⟩ : ↥A)
    have h1 : σsyn ⟨logFun (f : K), hmemAsOf f⟩
        = σ ⟨logFun (f : K), mem_congr hAscoe (hmemAsOf f)⟩ := rfl
    have h2 : σsyn f = σ ⟨(f : K), mem_congr hAscoe f.2⟩ := rfl
    rw [h1, h2]
    rw [show (⟨logFun (f : K), mem_congr hAscoe (hmemAsOf f)⟩ : ↥A)
        = ⟨logFun (f : K), hA.log_closed (f : K) (mem_congr hAscoe f.2)⟩ from Subtype.ext rfl]
    exact hf
  have hmulL : ∀ u v : L, mulE u v = u * v := by
    intro u v; rw [mulE]; exact FirstOrder.Ring.CompatibleRing.funMap_mul ![u, v]
  have haddL : ∀ u v : L, addE u v = u + v := by
    intro u v; rw [addE]; exact FirstOrder.Ring.CompatibleRing.funMap_add ![u, v]
  have hnegL : ∀ u : L, negE u = -u := by
    intro u; rw [negE]; exact FirstOrder.Ring.CompatibleRing.funMap_neg ![u]
  have hsubL : ∀ u v : L, subE u v = u - v := by
    intro u v; rw [subE, haddL, hnegL]; ring
  have hleL : ∀ u v : L, leE u v ↔ u ≤ v := by
    intro u v
    rw [leE, isSquare]
    constructor
    · rintro ⟨z, hz⟩
      rw [hmulL z z, hsubL v u] at hz
      nlinarith [mul_self_nonneg z]
    · intro h
      obtain ⟨z, hz⟩ := Work.WilC2.model_exists_sq (M := L) hLTRsyn (v - u) (sub_nonneg.mpr h)
      exact ⟨z, by rw [hmulL z z, hsubL v u]; exact hz.symm⟩
  -- the bridge hypotheses in the form used by the `S4Exp`/`S4ExpF` library
  have hrexpK : ∀ x : K, @FirstOrder.Language.Structure.funMap rexpL K _ 1 rexpFunc.rexp ![x]
      = Work.WilC5.rexpFromExp x := by
    intro x
    rw [Work.WilC5.lrcRexpReduct_funMap]
    exact Work.WilC5.reductStruct_funMap_rexp K ![x]
  have hrexpL : ∀ x : L, @FirstOrder.Language.Structure.funMap rexpL L _ 1 rexpFunc.rexp ![x]
      = Work.WilC5.rexpFromExp x := by
    intro x
    rw [Work.WilC5.lrcRexpReduct_funMap]
    exact Work.WilC5.reductStruct_funMap_rexp L ![x]
  have haddK : ∀ x y : K, Work.WilC5.addE x y = x + y := haddE
  have hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y := hmulE
  have honeK : (Work.WilC5.oneE : K) = 1 := by
    rw [Work.WilC5.oneE]
    exact FirstOrder.Ring.CompatibleRing.funMap_one default
  have hlenegK : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y := hleE
  have hlenegL : ∀ x y : L, Work.WilC5.leE x y ↔ x ≤ y := hleL
  have honeL : (Work.WilC5.oneE : L) = 1 := by
    rw [Work.WilC5.oneE]
    exact FirstOrder.Ring.CompatibleRing.funMap_one default
  -- ------------------------------------------------------------------ #
  -- §2.  `x = expE a` for `a : ↥As`, and the parameter set `B₀ = σ '' As ⊆ L`
  -- ------------------------------------------------------------------ #
  have hxeq : x = Work.WilC5.expE (a : K) := ha
  have hxAs : Work.WilC5.expE (a : K) ∉ (As : Set K) := by
    rw [← hxeq]; rw [hAscoe]; exact hx
  have hAlogAs : ∀ z ∈ (As : Set K), Work.WilC5.logFun z ∈ (As : Set K) :=
    fun z hz => hmemAsOf ⟨z, hz⟩
  have hcut : (∀ f : ↥As, ((f : K) < x ↔ (σsyn f : L) < y))
      ∧ (∀ f : ↥As, (x < (f : K) ↔ y < (σsyn f : L))) := by
    haveI hKTRinst : @FirstOrder.Language.Theory.Model LRc K (LR.withConstantsStructure ℝ)
      WilkiesDesign.CG.TR := hKTRsyn
    haveI hLTRinst : @FirstOrder.Language.Theory.Model LRc L (LR.withConstantsStructure ℝ)
      WilkiesDesign.CG.TR := hLTRsyn
    have h := @Work.WilC5.S4ExpG.cut_exp_aux K L instK instL _ _ _ _
      (inferInstance : WilkiesDesign.CG.rexpL.Structure K)
      (inferInstance : (FirstOrder.Language.constantsOn ℝ).Structure K) hKTRinst
      _ _ _ _ (inferInstance : WilkiesDesign.CG.rexpL.Structure L)
      (inferInstance : (FirstOrder.Language.constantsOn ℝ).Structure L) hLTRinst
      hMCr hOM hK hL hrexpK haddK hmulK honeK hlenegK hrexpL haddL hmulL honeL hlenegL
      As hdclSynth hAlogAs ⟨(a : K), mem_congr hAscoe a.2⟩ σsyn hσlog
    exact ⟨fun f => by rw [ha, hydef]; exact h.1 f,
      fun f => by rw [ha, hydef]; exact h.2 f⟩
  set B₀ : Set L := Set.range (fun f : ↥As => (σsyn f : L)) with hB₀def
  let bPre : ↥B₀ → ↥As := fun b => Classical.choose b.2
  have hbPre : ∀ b : ↥B₀, (σsyn (bPre b) : L) = (b : L) :=
    fun b => Classical.choose_spec b.2
  let τ₀ : ↥B₀ → K := fun b => (bPre b : K)
  -- ------------------------------------------------------------------ #
  -- §3.  The type of `x` over `As` is the type of `y` over `σ '' As`
  -- ------------------------------------------------------------------ #
  have htype : ∀ ψ : LRc.Formula (↥B₀ ⊕ Fin 1),
      ψ.Realize (Sum.elim τ₀ (fun _ : Fin 1 => x)) ↔
      ψ.Realize (Sum.elim (Subtype.val : ↥B₀ → L) (fun _ : Fin 1 => y)) := by
    intro ψ
    let g : (↥B₀ ⊕ Fin 1) → (↥As ⊕ Fin 1) := Sum.map bPre id
    have hmain := Work.WilC5.cut_determines_type_F (K := K) (L := L) hMCr hOM As hAsTR
      hdclSynth σsyn hcut (n := 0) (ψ.relabel g) (fun i : Fin 0 => i.elim0)
    rw [Formula.realize_relabel, Formula.realize_relabel] at hmain
    have e1 : (Sum.elim (Subtype.val : ↥As → K)
        (Fin.cons x (fun i : Fin 0 => ((i.elim0 : ↥As) : K)))) ∘ g
        = Sum.elim τ₀ (fun _ : Fin 1 => x) := by
      funext c
      rcases c with b | i
      · rfl
      · fin_cases i
        rfl
    have e2 : (Sum.elim (fun f : ↥As => (σsyn f : L))
        (Fin.cons y (fun i : Fin 0 => ((σsyn (i.elim0) : L))))) ∘ g
        = Sum.elim (Subtype.val : ↥B₀ → L) (fun _ : Fin 1 => y) := by
      funext c
      rcases c with b | i
      · exact hbPre b
      · fin_cases i
        rfl
    exact (iff_of_eq (congrArg (fun w => ψ.Realize w) e1.symm)).trans
      (hmain.trans (iff_of_eq (congrArg (fun w => ψ.Realize w) e2)))
  -- ------------------------------------------------------------------ #
  -- §4.  `ElemOn` on `insert y B₀`, and (by saturation) a map `G : K → L`
  -- ------------------------------------------------------------------ #
  have hElemOn : Work.WilC5.ElemOn (L := LRc) (M := K) (N := L)
      (insert y B₀) (Work.WilC5.PEM.extendFun τ₀ y x) :=
    Work.WilC5.elemOn_insert_of_type (L := LRc) (M := K) (N := L) (B := B₀)
      (τ := τ₀) (m := x) (x := fun _ : Fin 1 => y) htype
  have hsatL : @Work.WilC5.IsSaturated LRc L (inferInstance : LRc.Structure L) κ :=
    (isSaturated_congr (i := reductStruct L) (i' := (inferInstance : LRc.Structure L)) hstructL κ).mp
      (lrcSaturated_of_lecSaturated κ hsat)
  obtain ⟨B', hBB', τ', hτ'elem, hτ'agree, G, hGtau⟩ :=
    Work.WilC5.extends_elemOn_sat (L := LRc) (M := K) (N := L) hElemOn κ hκ hsatL
  have hτ'inj : Function.Injective τ' := Work.WilC5.elemOn_injective hτ'elem
  -- `G` agrees with `σ` on `As`
  have hGas : ∀ a' : ↥As, G (a' : K) = (σsyn a' : L) := by
    intro a'
    have h1 : τ' ⟨G (a' : K), (hGtau (a' : K)).choose⟩ = a' := (hGtau (a' : K)).choose_spec
    have h2 : τ' ⟨(σsyn a' : L), hBB' (Set.mem_insert_of_mem y (Set.mem_range_self a'))⟩ = a' := by
      have h := hτ'agree ⟨(σsyn a' : L), Set.mem_insert_of_mem y (Set.mem_range_self a')⟩
      rw [h]
      show (if hh : (σsyn a' : L) ∈ B₀ then τ₀ ⟨(σsyn a' : L), hh⟩ else x) = a'
      rw [dif_pos (Set.mem_range_self a')]
      exact congrArg Subtype.val
        (σsyn.injective (hbPre ⟨(σsyn a' : L), Set.mem_range_self a'⟩))
    have h3 : (⟨G (a' : K), (hGtau (a' : K)).choose⟩ : ↥B')
        = ⟨(σsyn a' : L), hBB' (Set.mem_insert_of_mem y (Set.mem_range_self a'))⟩ :=
      hτ'inj (by rw [h1, h2])
    exact congrArg Subtype.val h3
  -- `y ∉ B₀`, since otherwise the cut would force `x ∈ As`
  have hyB₀ : y ∉ B₀ := by
    intro hmem
    obtain ⟨f, hf⟩ := hmem
    have hf' : (σsyn f : L) = y := hf
    have h1 : ((f : K) < x) ↔ ((σsyn f : L) < y) := hcut.1 f
    have h2 : (x < (f : K)) ↔ (y < (σsyn f : L)) := hcut.2 f
    have hfx : ¬ ((f : K) < x) := fun hh => absurd (hf' ▸ h1.mp hh) (lt_irrefl y)
    have hxf : ¬ (x < (f : K)) := fun hh => absurd (hf'.symm ▸ h2.mp hh) (lt_irrefl y)
    have hxeq' : x = (f : K) := le_antisymm (not_lt.mp hfx) (not_lt.mp hxf)
    exact hx (hAscoe ▸ hxeq'.symm ▸ f.2)
  have hyB' : y ∈ B' := hBB' (Set.mem_insert y B₀)
  have hτ'y : τ' ⟨y, hyB'⟩ = x := by
    have h := hτ'agree ⟨y, Set.mem_insert y B₀⟩
    rw [h]
    show (if hh : y ∈ B₀ then τ₀ ⟨y, hh⟩ else x) = x
    exact dif_neg hyB₀
  have hGx : G x = y := by
    have h1 : τ' ⟨G x, (hGtau x).choose⟩ = τ' ⟨y, hyB'⟩ := by
      rw [(hGtau x).choose_spec, hτ'y]
    exact congrArg Subtype.val (hτ'inj h1)
  have hGinj : Function.Injective G := G.injective
  have hGmap : ∀ {n : ℕ} (f : LRc.Functions n) (y : Fin n → K),
      G (@Structure.funMap LRc K (reductStruct K) n f y)
        = @Structure.funMap LRc L (reductStruct L) n f (fun i => G (y i)) := by
    intro n f y
    rw [← Work.WilC5.funMap_reduct_synth (M := K) f y,
      ← Work.WilC5.funMap_reduct_synth (M := L) f (fun i => G (y i))]
    exact G.map_fun f y
  -- ------------------------------------------------------------------ #
  -- §5.  `S' = Dcl (As ∪ {x})`, its `Dcl`- and log-closure
  -- ------------------------------------------------------------------ #
  set S' : Set K := @Work.WilC2.Dcl K (inferInstance : LRc.Structure K)
    ((As : Set K) ∪ {x}) with hS'def
  have hS'dcl : @Work.WilC2.Dcl K (inferInstance : LRc.Structure K) S' ⊆ S' := by
    intro z hz
    rw [hS'def] at hz ⊢
    rwa [Work.WilC2.dcl_idem] at hz
  have hS'cl : ∀ {n : ℕ} (f : LRc.Functions n) (v : Fin n → K),
      (∀ i, v i ∈ S') → @Structure.funMap LRc K (inferInstance : LRc.Structure K) n f v ∈ S' := by
    intro n f v hv
    have h := Work.WilC5.term_realize_mem_dcl (A := S') (Functions.term f) v (fun i => hv i)
    have hfun : (Functions.term f).realize v =
        @Structure.funMap LRc K (inferInstance : LRc.Structure K) n f v := by
      simp [Functions.term, Term.realize_func, Term.realize_var]
    rw [hfun] at h
    exact hS'dcl h
  let Asyn : @FirstOrder.Language.Substructure LRc K (inferInstance : LRc.Structure K) :=
    mkSubAt K _ S' hS'cl
  have hAsyncoe : (Asyn : Set K) = S' := rfl
  -- the value decomposition on `S'`
  have hynew : ∀ c ∈ (As : Set K), c ≠ 0 →
      ¬ WilkiesDesign.CG.IsUnitVal (c * Work.WilC5.expE (a : K)) := by
    haveI hKTRinst : @FirstOrder.Language.Theory.Model LRc K (LR.withConstantsStructure ℝ)
      WilkiesDesign.CG.TR := hKTRsyn
    exact @Work.WilC5.S4ExpG.hynew_exp_aux K instK _ _ _ _
      (inferInstance : WilkiesDesign.CG.rexpL.Structure K)
      (inferInstance : (FirstOrder.Language.constantsOn ℝ).Structure K) hKTRinst
      hK hrexpK haddK hmulK honeK hlenegK (As : Set K) hdclSynth hAlogAs (a : K)
      (mem_congr hAscoe a.2) hxAs
  have hVA : ∀ w ∈ @Work.WilC2.Dcl K (inferInstance : LRc.Structure K)
        ((As : Set K) ∪ {Work.WilC5.expE (a : K)}),
      w ≠ 0 → ∃ Q : ℤ, 0 < Q ∧ ∃ N : ℤ, ∃ z ∈ (As : Set K), z ≠ 0 ∧
        ∃ ε : K, Work.WilC5.IsInfinitesimal ε ∧
          w ^ Q = z * (Work.WilC5.expE (a : K)) ^ N * (1 + ε) := by
    intro w hw hw0
    exact Work.WilC5.S4Exp.va_exp (K := K) hVI (As : Set K) hdclSynth ES rfl (a : K)
      (mem_congr hAscoe a.2) hxAs
      hynew w hw hw0
  have hSlog : ∀ w ∈ S', Work.WilC5.logFun w ∈ S' := by
    letI : LRc.Structure K := reductStruct K
    haveI hKTRinst : @FirstOrder.Language.Theory.Model LRc K (LR.withConstantsStructure ℝ)
      WilkiesDesign.CG.TR := hKTRsyn
    intro w hw
    have hw' := hw
    rw [hS'def] at hw'
    rw [hxeq] at hw'
    have h := @Work.WilC5.S4ExpF.logclosure_exp K _ _ _ _ _
      (inferInstance : WilkiesDesign.CG.rexpL.Structure K)
      (inferInstance : (FirstOrder.Language.constantsOn ℝ).Structure K)
      hKTRinst hK hrexpK haddK hmulK honeK hlenegK
      (As : Set K) hdclSynth hAlogAs (a : K) (mem_congr hAscoe a.2) hxAs hVA w hw'
    rw [hS'def]
    rw [hxeq]
    exact h
  -- ------------------------------------------------------------------ #
  -- §6.  The restriction of `G` to `S'`, and its log-preservation
  -- ------------------------------------------------------------------ #
  let σ'syn : @FirstOrder.Language.Embedding LRc ↥Asyn L
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (inferInstance : LRc.Structure K) Asyn)
      (inferInstance : LRc.Structure L) :=
    FirstOrder.Language.Embedding.mk ⟨fun w => G (w : K), fun _ _ h => Subtype.ext (G.injective h)⟩
      (fun {n} f v => by
        show G (@Structure.funMap LRc K (inferInstance : LRc.Structure K) n f (fun i => (v i : K)))
          = @Structure.funMap LRc L (inferInstance : LRc.Structure L) n f (fun i => G (v i))
        exact G.map_fun f (fun i => (v i : K)))
      (fun {n} r v => by nomatch r)
  have hσ'synB : ∀ b : ↥As, σ'syn ⟨(b : K), Work.WilC2.subset_dcl_aux _ (Or.inl b.2)⟩ = σsyn b := by
    intro b
    show G (b : K) = (σsyn b : L)
    exact hGas b
  have hxS' : Work.WilC5.expE (a : K) ∈ S' := by
    rw [hS'def]
    exact Work.WilC2.subset_dcl_aux _ (Or.inr hxeq.symm)
  have hσ'synx : σ'syn ⟨Work.WilC5.expE (a : K), hxS'⟩ = y := by
    show G (Work.WilC5.expE (a : K)) = y
    rw [← hxeq]; exact hGx
  have hlogpres : ∀ w : ↥Asyn,
      σ'syn ⟨Work.WilC5.logFun (w : K), hSlog (w : K) w.2⟩ = Work.WilC5.logFun (σ'syn w) := by
    haveI hKTRinst : @FirstOrder.Language.Theory.Model LRc K (LR.withConstantsStructure ℝ)
      WilkiesDesign.CG.TR := hKTRsyn
    haveI hLTRinst : @FirstOrder.Language.Theory.Model LRc L (LR.withConstantsStructure ℝ)
      WilkiesDesign.CG.TR := hLTRsyn
    have hBleS : As ≤ Asyn := fun z hz => Work.WilC2.subset_dcl_aux _ (Or.inl hz)
    have hSe : (Asyn : Set K) = @Work.WilC2.Dcl K (inferInstance : LRc.Structure K)
        ((As : Set K) ∪ {Work.WilC5.expE (a : K)}) := by
      rw [hAsyncoe, hS'def, hxeq]
    exact @Work.WilC5.S4ExpG.logPreserving_exp_aux K L instK instL _ _ _ _
      (inferInstance : WilkiesDesign.CG.rexpL.Structure K)
      (inferInstance : (FirstOrder.Language.constantsOn ℝ).Structure K) hKTRinst
      _ _ _ _ (inferInstance : WilkiesDesign.CG.rexpL.Structure L)
      (inferInstance : (FirstOrder.Language.constantsOn ℝ).Structure L) hLTRinst
      hMCr hOM hK hL hrexpK haddK hmulK honeK hlenegK hrexpL haddL hmulL honeL hlenegL
      (As : Set K) hdclSynth hAlogAs As rfl hAlogAs ⟨(a : K), mem_congr hAscoe a.2⟩ hxAs
      hVA σsyn hσlog Asyn hSe hS'dcl hSlog hBleS hxS' σ'syn hσ'synB hσ'synx
  have hdclA' : @Work.WilC2.Dcl K (reductStruct K) S' ⊆ S' := by
    have h1 : @Work.WilC2.Dcl K (reductStruct K) S' =
        @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) S' :=
      congrArg (fun i => @Work.WilC2.Dcl K i S') hstructK
    rw [h1]; exact hS'dcl
  -- ------------------------------------------------------------------ #
  -- §7.  Transport to the `rexp`-reduct of `K`
  -- ------------------------------------------------------------------ #
  letI : LRc.Structure K := reductStruct K
  letI : LRc.Structure L := reductStruct L
  let A' : @FirstOrder.Language.Substructure LRc K (reductStruct K) :=
    mkSubAt K (reductStruct K) S' (fun {n} f v hv => hstructK.symm ▸ (hS'cl f v hv))
  have hA'coe : (A' : Set K) = S' := rfl
  have hA'S4Dom : S4Dom A' :=
    ⟨fun z hz => hdclA' (hA'coe ▸ hz),
     fun z hz => hSlog z (hA'coe ▸ hz)⟩
  let σ' : @FirstOrder.Language.Embedding LRc ↥A' L
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (reductStruct K) A')
      (reductStruct L) :=
    FirstOrder.Language.Embedding.mk ⟨fun w => G (w : K), fun _ _ h => Subtype.ext (hGinj h)⟩
      (fun {n} f v => hGmap f (fun i => (v i : K)))
      (fun {n} r v => by nomatch r)
  refine ⟨A', hA'S4Dom, σ', ?_, ⟨⟨x, ?_⟩, rfl⟩, ?_, ?_⟩
  · -- `A ≤ A'`
    intro a' ha'
    show (a' : K) ∈ S'
    exact Work.WilC2.subset_dcl_aux _ (Or.inl (mem_congr hAscoe ha'))
  · show x ∈ S'
    rw [hxeq]
    exact hxS'
  · -- agreement with `σ` on `A`
    intro a' ha'
    show G (a' : K) = (σ ⟨a'.1, a'.2⟩ : L)
    rw [hGas ⟨(a' : K), mem_congr hAscoe a'.2⟩]
    exact congrArg (fun z : ↥A => (σ z : L)) (Subtype.ext rfl)
  · -- log-preservation, at the reduct structure
    intro w
    have hw : (w : K) ∈ S' := hA'coe ▸ w.2
    show G (Work.WilC5.logFun (w : K)) = Work.WilC5.logFun (G (w : K))
    exact hlogpres ⟨(w : K), hw⟩

end Work.WilC5
