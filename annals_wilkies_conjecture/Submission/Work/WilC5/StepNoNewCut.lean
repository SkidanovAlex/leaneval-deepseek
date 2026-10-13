-- NOTE (WilC5 / S4OnePoint_general): a clash-free *copy* of `Submission/Work/WilC5/StepNoNew.lean`:
-- the import of the `StepNoNewPrep`/`StepNoNew` chain is redirected to the corresponding
-- `…Cut` copies, in which the auxiliary definition `mkSubAt` is renamed to `mkSubAtSN`, because
-- the original `Work.WilC5.mkSubAt` clashes with the identically named definition of
-- `Submission/Work/WilC5/S4ExpG/Glue.lean` (which the §4 Lemma-4.4 assembly needs through
-- `ExistsStepSeq`/`StepSeqDecomp`/`DclExtensionCast`).

/-
  WilC5 — `Work.WilC5.StepNoNew`: vdDMM Lemma 4.2 (the "no new value" step of §4), as a single
  extension step of the §4 iteration.

  The situation is that of `Work.WilC5.S4Pair` (`S4Setup.lean`): `p = (B, τ)` is a partial extension
  of the §4 iteration — `B ≤ K` is a `Dcl`-closed `LRc`-substructure of the `rexp`-reduct of a model
  `K ⊨ TE`, closed under the definable logarithm, and `τ : B → L` is an `LRc`-embedding into
  `L ⊨ TE` commuting with the definable logarithm — and `x ∉ B` is an element of `K` such that
  *every* element of the definable closure `F = Dcl (B ∪ {x})` has the value of an element of `B`
  (`v(F^×) = v(B^×)`, the hypothesis of vdDMM Lemma 4.2).  The claim is that `p` extends strictly
  to a partial extension whose domain contains `x`.

  The proof has three parts.

  * **The domain.**  `F = Dcl (B ∪ {x})` is `Dcl`-closed, so it is the carrier of an
    `LRc`-substructure `S ≤ K` which is a model of `TR` (Tarski–Vaught:
    `Work.WilC5.model_TR_of_dcl_closed`).  The `Dcl`-API of `WilC2`/`WilC4` is stated at the
    `LRc`-structure synthesized from the canonical instance bundle, whereas the §4 layer fixes the
    `rexp`-reduct `Work.WilC5.reductStruct`; `model_TR_of_dclClosed_reduct` (`StepNoNewPrep.lean`)
    transports the conclusion across the (explicitly proved) equality of the two.

  * **The embedding.**  `B ⊨ TR` and `L` is `κ`-saturated with `κ > |K| ≥ |B|`, so model
    completeness of `TR` (`Work.WilC5.hasExtProp_of_modelComplete`) extends `τ` to an `LRc`-embedding
    `g : K → L`; its restriction to `S` is the required extension (elementary on `S`, since
    `S ⊨ TR`).

  * **Log-closure and log-preservation.**  `Work.WilC5.logHalf` (`StepNoNewLog.lean`): the
    value-theoretic content of vdDMM Lemma 4.2 — the `z(1+ε)` decomposition of an element of `F`
    (`decomposition_of_same_value`), the definability of `log (1+ε)` from the parameters `w`,
    `z` (`logFun_one_add_rexp`, `logFun_eq_of_rexp_eq`, `mem_dcl_of_unique_solution`), and the
    resulting log-closure of `F` together with the log-preservation of the extension.
-/
import Mathlib
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.LRcSatOfLEcSat
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.hasExtProp_of_modelComplete
import Submission.Work.WilC5.dclClosed_substructure
import Submission.Work.WilC2.meetsDefinable_dcl
import Submission.Work.WilC2.dcl_exchange
import Submission.Work.WilC2.Square
import Submission.Work.WilC5.StepNoNewPrepCut
import Submission.Work.WilC5.StepNoNewLogCut

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

theorem StepNoNew
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR) (hOM : WilkiesDesign.CG.OMinModels) (hVI : WilkiesDesign.CG.ValIneq)
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    (hK : K ⊨ WilkiesDesign.CG.TE) (hL : L ⊨ WilkiesDesign.CG.TE)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk K < κ)
    (hsat : @Work.WilC5.IsSaturated WilkiesDesign.CG.LEc L _ κ)
    {A₀ : WilkiesDesign.CG.LRc.Substructure K}
    {σ₀ : @FirstOrder.Language.Embedding WilkiesDesign.CG.LRc ↥A₀ L _ (Work.WilC5.reductStruct L)}
    (p : Work.WilC5.S4Pair A₀ σ₀)
    {x : K} (hx : x ∉ (p.dom : Set K))
    (hvg : ∀ w : K, w ∈ Work.WilC2.Dcl ((p.dom : Set K) ∪ {x}) →
      ∃ b : ↥p.dom, Work.WilC5.SameVal K hK (b : K) w) :
    ∃ q : Work.WilC5.S4Pair A₀ σ₀, p ≤ q ∧ ∃ b : ↥q.dom, (b : K) = x := by
  classical
  -- ------------------------------------------------------------------ #
  -- the canonical instances on `K` and on `L`
  -- ------------------------------------------------------------------ #
  letI : LRc.Structure K := reductStruct K
  have hKTR : K ⊨ TR := reduct_model_TR K hK
  have hKfld : K ⊨ Theory.field := tr_ring_field K hKTR
  letI : Field K := cField K hK
  letI : LinearOrder K := cLin K hK
  letI : Ring.CompatibleRing K := FirstOrder.Field.compatibleRingOfModelField K
  letI : IsStrictOrderedRing K := tr_isStrictOrderedRing K hKTR
  letI : LRc.Structure L := reductStruct L
  have hLTR : L ⊨ TR := reduct_model_TR L hL
  have hLfld : L ⊨ Theory.field := tr_ring_field L hLTR
  letI : Field L := trField L hLTR
  letI : LinearOrder L := trLinearOrder L hLTR
  letI : Ring.CompatibleRing L := FirstOrder.Field.compatibleRingOfModelField L
  letI : IsStrictOrderedRing L := tr_isStrictOrderedRing L hLTR
  -- ------------------------------------------------------------------ #
  -- the bridge between the two `LRc`-structures
  -- ------------------------------------------------------------------ #
  have hstruct : (reductStruct K : LRc.Structure K) = canonStruct K := by
    ext n f y
    · rcases f with (g | c)
      · rcases g with (g | r)
        · rfl
        · cases r; show rexpFromExp (y 0) = _; rfl
      · rfl
    · nomatch f
  have hstructL : (reductStruct L : LRc.Structure L) = canonStruct L := by
    ext n f y
    · rcases f with (g | c)
      · rcases g with (g | r)
        · rfl
        · cases r; show rexpFromExp (y 0) = _; rfl
      · rfl
    · nomatch f
  haveI hKTRcan : @Theory.Model LRc K (canonStruct K) TR := by rw [← hstruct]; exact hKTR
  have hLTRcan : @Theory.Model LRc L (canonStruct L) TR := by rw [← hstructL]; exact hLTR
  -- ------------------------------------------------------------------ #
  -- arithmetic bridges on `K`
  -- ------------------------------------------------------------------ #
  have haddK : ∀ u v : K, addE u v = u + v := by
    intro u v; rw [addE]; exact FirstOrder.Ring.CompatibleRing.funMap_add ![u, v]
  have hmulK : ∀ u v : K, mulE u v = u * v := by
    intro u v; rw [mulE]; exact FirstOrder.Ring.CompatibleRing.funMap_mul ![u, v]
  have honeK : (oneE : K) = 1 := by
    rw [oneE]; exact FirstOrder.Ring.CompatibleRing.funMap_one ![]
  have hzeroK : (zeroE : K) = 0 := by
    rw [zeroE]; exact FirstOrder.Ring.CompatibleRing.funMap_zero ![]
  have hnegK : ∀ u : K, negE u = -u := fun u => by
    rw [negE]; exact FirstOrder.Ring.CompatibleRing.funMap_neg ![u]
  have hsubK : ∀ u v : K, subE u v = u - v := by
    intro u v
    rw [subE, haddK u (negE v), hnegK v, sub_eq_add_neg]
  have hleEK : ∀ u v : K, leE u v ↔ u ≤ v := by
    intro u v
    rw [leE, isSquare]
    constructor
    · rintro ⟨z, hz⟩
      rw [hmulK z z, hsubK v u] at hz
      nlinarith [mul_self_nonneg z]
    · intro h
      obtain ⟨z, hz⟩ := Work.WilC2.model_exists_sq (M := K) hKTRcan (v - u) (sub_nonneg.mpr h)
      exact ⟨z, by rw [hmulK z z, hsubK v u]; exact hz.symm⟩
  have haddELK : ∀ u v : K, @Work.WilC5.addEL K (reductStruct K) u v = u + v := by
    intro u v
    show @Structure.funMap LRc K (reductStruct K) 2 (Sum.inl (Sum.inl Ring.addFunc)) ![u, v]
      = u + v
    rw [reductStruct_funMap_ring]
    rw [← addE]
    exact haddK u v
  have hmulELK : ∀ u v : K, @Work.WilC5.mulEL K (reductStruct K) u v = u * v := by
    intro u v
    show @Structure.funMap LRc K (reductStruct K) 2 (Sum.inl (Sum.inl Ring.mulFunc)) ![u, v]
      = u * v
    rw [reductStruct_funMap_ring]
    rw [← mulE]
    exact hmulK u v
  have honeELK : (@Work.WilC5.oneEL K (reductStruct K)) = 1 := by
    show @Structure.funMap LRc K (reductStruct K) 0 (Sum.inl (Sum.inl Ring.oneFunc))
      (fun i : Fin 0 => Fin.elim0 i) = 1
    rw [reductStruct_funMap_ring]
    exact FirstOrder.Ring.CompatibleRing.funMap_one (R := K) (fun i : Fin 0 => Fin.elim0 i)
  have hleELK2 : ∀ u v : K, @Work.WilC5.leEL K (reductStruct K) u v ↔ u ≤ v := fun u v =>
    (show @Work.WilC5.leEL K (reductStruct K) u v ↔ leE u v from Iff.rfl).trans (hleEK u v)
  -- ------------------------------------------------------------------ #
  -- arithmetic bridges on `L`
  -- ------------------------------------------------------------------ #
  have haddL : ∀ u v : L, addE u v = u + v := by
    intro u v; rw [addE]; exact FirstOrder.Ring.CompatibleRing.funMap_add ![u, v]
  have hmulL : ∀ u v : L, mulE u v = u * v := by
    intro u v; rw [mulE]; exact FirstOrder.Ring.CompatibleRing.funMap_mul ![u, v]
  have honeL : (oneE : L) = 1 := by
    rw [oneE]; exact FirstOrder.Ring.CompatibleRing.funMap_one ![]
  have hzeroL : (zeroE : L) = 0 := by
    rw [zeroE]; exact FirstOrder.Ring.CompatibleRing.funMap_zero ![]
  have hnegL : ∀ u : L, negE u = -u := fun u => by
    rw [negE]; exact FirstOrder.Ring.CompatibleRing.funMap_neg ![u]
  have hsubL : ∀ u v : L, subE u v = u - v := by
    intro u v
    rw [subE, haddL u (negE v), hnegL v, sub_eq_add_neg]
  have hleEL : ∀ u v : L, leE u v ↔ u ≤ v := by
    intro u v
    rw [leE, isSquare]
    constructor
    · rintro ⟨z, hz⟩
      rw [hmulL z z, hsubL v u] at hz
      nlinarith [mul_self_nonneg z]
    · intro h
      obtain ⟨z, hz⟩ := Work.WilC2.model_exists_sq (M := L) hLTRcan (v - u) (sub_nonneg.mpr h)
      exact ⟨z, by rw [hmulL z z, hsubL v u]; exact hz.symm⟩
  have hleELL2 : ∀ u v : L, @Work.WilC5.leEL L (reductStruct L) u v ↔ u ≤ v := fun u v =>
    (show @Work.WilC5.leEL L (reductStruct L) u v ↔ leE u v from Iff.rfl).trans (hleEL u v)
  -- ------------------------------------------------------------------ #
  -- the new domain `Dcl (B ∪ {x})`
  -- ------------------------------------------------------------------ #
  set B : Set K := (p.dom : Set K) with hBdef
  have htransB : @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x})
      = @Work.WilC2.Dcl K (canonStruct K) (B ∪ {x}) :=
    congrArg (fun i => @Work.WilC2.Dcl K i (B ∪ {x})) hstruct
  have htransKo : ∀ Y : Set K, @Work.WilC2.Dcl K (canonStruct K) Y
      = @Work.WilC2.Dcl K (reductStruct K) Y :=
    fun Y => congrArg (fun i => @Work.WilC2.Dcl K i Y) hstruct.symm
  have hdclidem : @Work.WilC2.Dcl K (reductStruct K)
      (@Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}))
      = @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}) := by
    have hcan : @Work.WilC2.Dcl K (canonStruct K)
        (@Work.WilC2.Dcl K (canonStruct K) (B ∪ {x}))
        = @Work.WilC2.Dcl K (canonStruct K) (B ∪ {x}) :=
      Work.WilC2.dcl_idem (B ∪ {x})
    calc @Work.WilC2.Dcl K (reductStruct K) (@Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}))
        = @Work.WilC2.Dcl K (reductStruct K) (@Work.WilC2.Dcl K (canonStruct K) (B ∪ {x})) := by
          rw [htransB]
      _ = @Work.WilC2.Dcl K (canonStruct K) (@Work.WilC2.Dcl K (canonStruct K) (B ∪ {x})) :=
          (htransKo _).symm
      _ = @Work.WilC2.Dcl K (canonStruct K) (B ∪ {x}) := hcan
      _ = @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}) := htransB.symm
  have hDdcl : @Work.WilC2.Dcl K (reductStruct K)
      (@Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}))
      ⊆ @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}) := le_of_eq hdclidem
  obtain ⟨S, hScoe⟩ := dclClosed_substructure (A := @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}))
    hDdcl
  have hSdcl : @Work.WilC2.Dcl K (reductStruct K) (S : Set K) ⊆ (S : Set K) := by
    rw [hScoe]; exact hDdcl
  have hSTR : @Theory.Model LRc ↥S
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (reductStruct K) S) TR :=
    model_TR_of_dclClosed_reduct hstruct hOM hKTR S hSdcl
  have hBTR : @Theory.Model LRc ↥p.dom
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (reductStruct K) p.dom) TR :=
    model_TR_of_dclClosed_reduct hstruct hOM hKTR p.dom p.h4.dcl_closed
  have hBsub : (p.dom : Set K) ⊆ (S : Set K) := by
    intro y hy
    rw [hScoe]
    have h1 : y ∈ @Work.WilC2.Dcl K (canonStruct K) (B ∪ {x}) :=
      Work.WilC2.subset_dcl_aux (B ∪ {x}) (Or.inl (by rw [hBdef]; exact hy))
    rwa [← htransB] at h1
  have hxS : x ∈ (S : Set K) := by
    rw [hScoe]
    have h1 : x ∈ @Work.WilC2.Dcl K (canonStruct K) (B ∪ {x}) :=
      Work.WilC2.subset_dcl_aux (B ∪ {x}) (Or.inr (Set.mem_singleton x))
    rwa [← htransB] at h1
  -- ------------------------------------------------------------------ #
  -- the extension of `p.emb` to the whole of `K`
  -- ------------------------------------------------------------------ #
  have hcK : Cardinal.mk ↥S < κ := lt_of_le_of_lt (Cardinal.mk_subtype_le _) hκ
  have hsatR : @Work.WilC5.IsSaturated LRc L (reductStruct L) κ :=
    lrcSaturated_of_lecSaturated κ hsat
  obtain ⟨g, hg⟩ := hasExtProp_of_modelComplete hMCr K L hKTR hLTR κ hκ hsatR p.dom hBTR p.emb
  let gS : @Embedding LRc ↥S L _ (reductStruct L) := g.comp (Substructure.subtype S)
  have hgS_B : ∀ b : ↥p.dom, ∀ hb : (b : K) ∈ (S : Set K),
      gS ⟨(b : K), hb⟩ = p.emb b := by
    intro b hb
    show g (b : K) = p.emb b
    exact hg b
  -- ------------------------------------------------------------------ #
  -- the hypotheses of `logHalf` that reduce to `B = p.dom`
  -- ------------------------------------------------------------------ #
  have hBconst : ∀ r : ℝ, realConst K r ∈ B := by
    intro r
    have h : realConst K r ∈ (p.dom : Set K) := by
      have h1 := p.dom.fun_mem
        (Sum.inr (r : (FirstOrder.Language.constantsOn ℝ).Functions 0) : LRc.Functions 0)
        (![] : Fin 0 → K) (fun i => i.elim0)
      rwa [← Work.WilC5.realConst_funMap] at h1
    exact h
  have hBmul : ∀ u ∈ B, ∀ v ∈ B, mulE u v ∈ B := by
    intro u hu v hv
    have h := p.dom.fun_mem (ringSymL Ring.mulFunc) ![u, v]
      (by intro i; fin_cases i <;> assumption)
    exact h
  have hBzero : (0 : K) ∈ B := by
    have h := p.dom.fun_mem (Sum.inl (Sum.inl Ring.zeroFunc)) (fun i : Fin 0 => Fin.elim0 i)
      (fun i => i.elim0)
    have h2 : @Structure.funMap LRc K (reductStruct K) 0 (Sum.inl (Sum.inl Ring.zeroFunc))
        (fun i : Fin 0 => Fin.elim0 i) = (0 : K) := by
      rw [reductStruct_funMap_ring]
      exact FirstOrder.Ring.CompatibleRing.funMap_zero (R := K) (fun i : Fin 0 => Fin.elim0 i)
    rwa [h2] at h
  have hvg' : ∀ w : K, w ∈ @Work.WilC2.Dcl K (reductStruct K) (B ∪ {x}) →
      ∃ b ∈ B, SameArch w b := by
    intro w hw
    have hw' : w ∈ Work.WilC2.Dcl ((p.dom : Set K) ∪ {x}) := by
      rw [← hBdef]; exact hw
    obtain ⟨b, hb⟩ := hvg w hw'
    exact ⟨(b : K), by rw [hBdef]; exact b.2,
      SameArch_equiv.symm (by simpa only [SameVal] using hb)⟩
  have hglog : ∀ b ∈ B, g (logFun b) = logFun (g b) := by
    intro b hb
    have hb' : b ∈ (p.dom : Set K) := by rw [hBdef] at hb; exact hb
    have h1 : g (logFun b) = p.emb ⟨logFun b, p.h4.log_closed b hb'⟩ :=
      hg ⟨logFun b, p.h4.log_closed b hb'⟩
    have h2 : p.emb ⟨logFun b, p.h4.log_closed b hb'⟩ = logFun (p.emb ⟨b, hb'⟩) :=
      p.logpres ⟨b, hb'⟩
    have h3 : p.emb ⟨b, hb'⟩ = g b := (hg ⟨b, hb'⟩).symm
    rw [h1, h2, h3]
  -- ------------------------------------------------------------------ #
  -- the log half of Lemma 4.2
  -- ------------------------------------------------------------------ #
  have hlog := logHalf hK hL hKTRcan hstruct hleEK haddK hmulK honeK hzeroK hnegK
    hleEL hzeroL B S x hScoe hdclidem hBsub
    (fun b hb => p.h4.log_closed b (by rw [hBdef] at hb; exact hb)) hBconst hBmul hBzero
    g hglog hvg'
  have hlogclosed : LogClosed (S : Set K) := hlog.1
  -- ------------------------------------------------------------------ #
  -- the assembly
  -- ------------------------------------------------------------------ #
  have hle_dom : A₀ ≤ S := p.le_dom.trans hBsub
  have hagrees : ∀ a : A₀, gS ⟨(a : K), hle_dom a.2⟩ = σ₀ a := by
    intro a
    have h : gS ⟨(a : K), hle_dom a.2⟩ = p.emb ⟨(a : K), p.le_dom a.2⟩ :=
      hgS_B ⟨(a : K), p.le_dom a.2⟩ (hBsub (p.le_dom a.2))
    rw [h]
    exact p.agrees a
  let q : S4Pair A₀ σ₀ :=
    { dom := S
      emb := gS
      h4 := ⟨hSdcl, hlogclosed⟩
      logpres := fun w => hlog.2 (w : K) w.2
      le_dom := hle_dom
      agrees := hagrees }
  have hpq : p ≤ q := ⟨hBsub, fun a => hgS_B a (hBsub a.2)⟩
  exact ⟨q, hpq, ⟨⟨x, hxS⟩, rfl⟩⟩

end Work.WilC5
