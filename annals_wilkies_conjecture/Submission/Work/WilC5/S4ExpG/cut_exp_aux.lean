import Mathlib
import Submission.Work.WilC5.expE_lt_iff_logFun_lt
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.LRcReduct
import Submission.Work.WilC5.Bridge
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.ExpLog
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.embedding_map_leEL
import Submission.Work.WilC5.S4ExpG.ord_cut_aux
import Submission.Work.WilC5.S4ExpG.exp_cut_field

namespace Work.WilC5.S4ExpG

/-- **The cut of `expE a` over `B` is the image of the cut of `a`** (vdDMM Lemma 4.3, cut step).

`K, L ⊨ T_E` with the canonical `L_Rc`-data (`hrexp`, `hadd`, …, `hleneg`), `hMCr` is model
completeness of `T_R` and `hOM` o-minimality of its models.  `B ≤ K` is a substructure which is
`Dcl`-closed (`hBdcl`) and log-closed (`hBlog`), `a : B`, and `τ : B ↪ L` is an `L_Rc`-embedding
which commutes with the definable logarithm (`hτlog`).

Then for every `f : B`,

  `f < expE a  ↔  τ f < expE (τ a)`,   and   `expE a < f  ↔  expE (τ a) < τ f`.

Proof sketch.  `expE` is strictly increasing and `expE (logFun w) = w` for `w > 0`, so for `f > 0`
both sides reduce to `logFun f < a ↔ τ (logFun f) < τ a` (`expE_lt_iff_logFun_lt`), which holds
because `τ` preserves `≤` (through the definable order `leEL`, using `hMCr` on the two inclusions
`B ↪ K`, `B ↪ L`) with strictness coming from injectivity; the case `f ≤ 0` is immediate since
`expE` is positive.  (`hmulK`, `hmulL`, `honeK`, `honeL`, `hrexpK`, `hrexpL` are carried only for
uniformity with the sibling steps and may well be unused.) -/
theorem cut_exp_aux {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
    (hTEK : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hTEL : FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TE)
    (hrexpK : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (honeK : (Work.WilC5.oneE : K) = 1)
    (hlenegK : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (hrexpL : ∀ x : L, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL L _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeL : (Work.WilC5.oneE : L) = 1)
    (hlenegL : ∀ x y : L, Work.WilC5.leE x y ↔ x ≤ y)
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBdcl : @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) (B : Set K) ⊆ (B : Set K))
    (hBlog : ∀ x ∈ (B : Set K), Work.WilC5.logFun x ∈ (B : Set K))
    (a : ↥B) (τ : WilkiesDesign.CG.LRc.Embedding B L)
    (hτlog : ∀ x : B, τ ⟨Work.WilC5.logFun (x : K), hBlog (x : K) x.2⟩ = Work.WilC5.logFun (τ x)) :
    (∀ f : B, ((f : K) < Work.WilC5.expE (a : K) ↔ (τ f : L) < Work.WilC5.expE (τ a))) ∧
      (∀ f : B, (Work.WilC5.expE (a : K) < (f : K) ↔ Work.WilC5.expE (τ a) < τ f)) := by
  obtain ⟨hle, hlt, hpos⟩ := ord_cut_aux (K := K) (L := L) hMCr hOM B hBdcl τ
  have hKa : (0 : K) < Work.WilC5.expE (a : K) :=
    (Work.WilC5.S4ExpF.leE_zero_iff hTEK haddK hlenegK _).mp
      (Work.WilC5.expE_pos_of_model hTEK (a : K))
  have hLa : (0 : L) < Work.WilC5.expE (τ a) :=
    (Work.WilC5.S4ExpF.leE_zero_iff hTEL haddL hlenegL _).mp
      (Work.WilC5.expE_pos_of_model hTEL (τ a))
  have hlef : ∀ f : ↥B, (τ f : L) ≤ 0 ↔ (f : K) ≤ 0 := by
    intro f
    constructor
    · intro h
      by_contra hc
      exact absurd ((hpos f).mp (not_le.mp hc)) (not_lt.mpr h)
    · intro h
      by_contra hc
      exact absurd ((hpos f).mpr (not_le.mp hc)) (not_lt.mpr h)
  constructor
  · intro f
    by_cases hf : (0 : K) < (f : K)
    · have hfL : (0 : L) < (τ f : L) := (hpos f).mp hf
      rw [(Work.WilC5.S4ExpG.exp_cut_field hTEK haddK hlenegK hf).1,
        (Work.WilC5.S4ExpG.exp_cut_field hTEL haddL hlenegL hfL).1, (hτlog f).symm]
      have h := hlt ⟨Work.WilC5.logFun (f : K), hBlog (f : K) f.2⟩ a
      simpa using h
    · have hfK : (f : K) ≤ 0 := not_lt.mp hf
      have hfL : (τ f : L) ≤ 0 := (hlef f).mpr hfK
      exact iff_of_true (lt_of_le_of_lt hfK hKa) (lt_of_le_of_lt hfL hLa)
  · intro f
    by_cases hf : (0 : K) < (f : K)
    · have hfL : (0 : L) < (τ f : L) := (hpos f).mp hf
      rw [(Work.WilC5.S4ExpG.exp_cut_field hTEK haddK hlenegK hf).2,
        (Work.WilC5.S4ExpG.exp_cut_field hTEL haddL hlenegL hfL).2, (hτlog f).symm]
      have h := hlt a ⟨Work.WilC5.logFun (f : K), hBlog (f : K) f.2⟩
      simpa using h
    · have hfK : (f : K) ≤ 0 := not_lt.mp hf
      have hfL : (τ f : L) ≤ 0 := (hlef f).mpr hfK
      exact iff_of_false (fun h => absurd (lt_of_lt_of_le h hfK) (not_lt.mpr (le_of_lt hKa)))
        (fun h => absurd (lt_of_lt_of_le h hfL) (not_lt.mpr (le_of_lt hLa)))

end Work.WilC5.S4ExpG
