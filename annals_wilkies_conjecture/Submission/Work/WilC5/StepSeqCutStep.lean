import Mathlib
import Submission.Work.WilC5.StepExpCut
import Submission.Work.WilC5.StepSeq
import Submission.Work.WilC5.expE_lt_iff_logFun_lt
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.expE_add_of_model
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.S4ExpG.exp_cut_field
import Submission.Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos
import Submission.Work.WilC5.embedding_map_leEL

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.WilC5

theorem StepSeqCutStep
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
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
    (hBdcl : @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) (B : Set K)
      ⊆ (B : Set K))
    (hBlog : ∀ x ∈ (B : Set K), Work.WilC5.logFun x ∈ (B : Set K))
    (hBexp : ∀ x ∈ (B : Set K), Work.WilC5.expE x ∈ (B : Set K))
    (τ : WilkiesDesign.CG.LRc.Embedding B L)
    (hτlog : ∀ x : B, τ ⟨Work.WilC5.logFun (x : K), hBlog (x : K) x.2⟩ = Work.WilC5.logFun (τ x))
    (hτexp : ∀ x : B, τ ⟨Work.WilC5.expE (x : K), hBexp (x : K) x.2⟩ = Work.WilC5.expE (τ x))
    {x x' : K} {y y' : L} (a : B)
    (hrel : Work.WilC5.logFun x = Work.WilC5.addE (a : K) x')
    (hrelL : Work.WilC5.logFun y = Work.WilC5.addE (τ a) y')
    (hcut : ∀ b : B, ((b : K) < x ↔ (τ b : L) < y) ∧ (x < (b : K) ↔ y < τ b)) :
    ∀ b : B, ((b : K) < x' ↔ (τ b : L) < y') ∧ (x' < (b : K) ↔ y' < τ b) := by
  classical
  -- ## 0. bridges between the `LEc` symbols and the field operations
  have hzeroK : (Work.WilC5.zeroE : K) = 0 := Work.WilC5.S4ExpF.zeroE_eq_zero hTEK haddK
  have hnegK : ∀ x : K, Work.WilC5.negE x = -x :=
    fun x => Work.WilC5.S4ExpF.negE_eq_neg hTEK haddK x
  have hzeroL : (Work.WilC5.zeroE : L) = 0 := Work.WilC5.S4ExpF.zeroE_eq_zero hTEL haddL
  have hnegL : ∀ x : L, Work.WilC5.negE x = -x :=
    fun x => Work.WilC5.S4ExpF.negE_eq_neg hTEL haddL x
  -- ## 1. the ring operations of `↥B` and of the `LRc`-structure of `L` are the field ones
  have hcoe_add : ∀ u v : ↥B, ((Work.WilC5.addEL u v : ↥B) : K) = (u : K) + (v : K) := by
    intro u v
    show B.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥B _ 2
        (Work.WilC5.ringSymL FirstOrder.Ring.addFunc) ![u, v]) = (u : K) + (v : K)
    have h := (FirstOrder.Language.Substructure.subtype B).map_fun
      (Work.WilC5.ringSymL FirstOrder.Ring.addFunc) ![u, v]
    have h2 : (B.subtype ∘ ![u, v]) = ![(u : K), (v : K)] := by
      funext i; fin_cases i <;> rfl
    rw [h2] at h
    rw [h]
    show @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc K _ 2
        (Sum.inl (Sum.inl FirstOrder.Ring.addFunc)) ![(u : K), (v : K)] = (u : K) + (v : K)
    rw [Work.WilC5.reductStruct_funMap_ring]
    exact haddK (u : K) (v : K)
  have hcoe_neg : ∀ u : ↥B, ((Work.WilC5.negEL u : ↥B) : K) = -(u : K) := by
    intro u
    show B.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥B _ 1
        (Work.WilC5.ringSymL FirstOrder.Ring.negFunc) ![u]) = -(u : K)
    have h := (FirstOrder.Language.Substructure.subtype B).map_fun
      (Work.WilC5.ringSymL FirstOrder.Ring.negFunc) ![u]
    have h2 : (B.subtype ∘ ![u]) = ![(u : K)] := by
      funext i; fin_cases i <;> rfl
    rw [h2] at h
    rw [h]
    show @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc K _ 1
        (Sum.inl (Sum.inl FirstOrder.Ring.negFunc)) ![(u : K)] = -(u : K)
    rw [Work.WilC5.reductStruct_funMap_ring]
    exact hnegK (u : K)
  have hcoe_sub : ∀ u v : ↥B, ((Work.WilC5.subEL u v : ↥B) : K) = (u : K) - (v : K) := by
    intro u v
    show ((Work.WilC5.addEL u (Work.WilC5.negEL v) : ↥B) : K) = (u : K) - (v : K)
    rw [hcoe_add u (Work.WilC5.negEL v), hcoe_neg v]
    ring
  have haddEL_L : ∀ u v : L, @Work.WilC5.addEL L (Work.WilC5.reductStruct L) u v = u + v := by
    intro u v
    show @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc L
        (Work.WilC5.reductStruct L) 2 (Sum.inl (Sum.inl FirstOrder.Ring.addFunc)) ![u, v] = u + v
    rw [Work.WilC5.reductStruct_funMap_ring]
    exact haddL u v
  have hnegEL_L : ∀ u : L, @Work.WilC5.negEL L (Work.WilC5.reductStruct L) u = -u := by
    intro u
    show @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc L
        (Work.WilC5.reductStruct L) 1 (Sum.inl (Sum.inl FirstOrder.Ring.negFunc)) ![u] = -u
    rw [Work.WilC5.reductStruct_funMap_ring]
    exact hnegL u
  have hsubEL_L : ∀ u v : L, @Work.WilC5.subEL L (Work.WilC5.reductStruct L) u v = u - v := by
    intro u v
    show @Work.WilC5.addEL L (Work.WilC5.reductStruct L) u
      (@Work.WilC5.negEL L (Work.WilC5.reductStruct L) v) = u - v
    rw [haddEL_L u (@Work.WilC5.negEL L (Work.WilC5.reductStruct L) v), hnegEL_L v, sub_eq_add_neg]
  -- ## 2. `τ` is strictly increasing: `x < y` in `B` implies `τ x < τ y`
  -- (`y - x = exp (log (y - x))` and `exp` is positive; the logarithm of an element of `B` and
  -- the exponential of an element of `B` stay in `B` and are preserved by `τ`)
  have strictFwd : ∀ a b : ↥B, (a : K) < (b : K) → τ a < τ b := by
    intro a b hab
    let d : ↥B := Work.WilC5.subEL b a
    have hd : (d : K) = (b : K) - (a : K) := hcoe_sub b a
    have hdpos : (0 : K) < (d : K) := by rw [hd]; linarith
    have hlogd : Work.WilC5.logFun (d : K) ∈ (B : Set K) := hBlog (d : K) d.2
    have hexp : Work.WilC5.expE (Work.WilC5.logFun (d : K)) = (d : K) :=
      Work.WilC5.expE_logFun_of_pos_of_model hTEK
        ((Work.WilC5.S4ExpF.leE_zero_iff hTEK haddK hlenegK (d : K)).mpr hdpos)
    have hdEq : d = ⟨Work.WilC5.expE (Work.WilC5.logFun (d : K)),
        hBexp (Work.WilC5.logFun (d : K)) hlogd⟩ :=
      Subtype.ext hexp.symm
    have hτd : (τ d : L) = Work.WilC5.expE (τ ⟨Work.WilC5.logFun (d : K), hlogd⟩) := by
      have h1 : τ d = τ ⟨Work.WilC5.expE (Work.WilC5.logFun (d : K)),
          hBexp (Work.WilC5.logFun (d : K)) hlogd⟩ := congrArg τ hdEq
      rw [h1, hτexp ⟨Work.WilC5.logFun (d : K), hlogd⟩]
    have hpos : (0 : L) < (τ d : L) := by
      rw [hτd]
      exact (Work.WilC5.S4ExpF.leE_zero_iff hTEL haddL hlenegL _).mp
        (Work.WilC5.expE_pos_of_model hTEL _)
    have hτd' : (τ d : L) = (τ b : L) - (τ a : L) := by
      have h1 : τ d = Work.WilC5.subEL (τ b) (τ a) := by
        rw [show d = Work.WilC5.subEL b a from rfl]
        exact Work.WilC5.map_subEL τ b a
      rw [h1]
      exact hsubEL_L (τ b) (τ a)
    rw [hτd'] at hpos
    linarith
  -- ## 3. consequently `τ` preserves and reflects the strict order on `B`
  have hτlt : ∀ a b : ↥B, (a : K) < (b : K) ↔ τ a < τ b := by
    intro a b
    constructor
    · intro hb; exact strictFwd a b hb
    · intro h
      by_contra hcon
      push_neg at hcon
      rcases lt_or_eq_of_le hcon with hlt | heq
      · exact absurd (strictFwd b a hlt) (not_lt.mpr (le_of_lt h))
      · have hba : b = a := Subtype.ext heq
        rw [hba] at h
        exact absurd h (lt_irrefl (τ a))
  have hzB : ((Work.WilC5.zeroEL : ↥B) : K) = (0 : K) := by
    show B.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥B _ 0
        (Work.WilC5.ringSymL FirstOrder.Ring.zeroFunc) (![] : Fin 0 → ↥B)) = 0
    have h := (FirstOrder.Language.Substructure.subtype B).map_fun
      (Work.WilC5.ringSymL FirstOrder.Ring.zeroFunc) (![] : Fin 0 → ↥B)
    have h2 : (B.subtype ∘ (![] : Fin 0 → ↥B)) = (![] : Fin 0 → K) := by
      funext i; exact Fin.elim0 i
    rw [h2] at h
    rw [h]
    show @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc K _ 0
        (Sum.inl (Sum.inl FirstOrder.Ring.zeroFunc)) (![] : Fin 0 → K) = 0
    rw [Work.WilC5.reductStruct_funMap_ring]
    exact hzeroK
  have hτzB : τ (Work.WilC5.zeroEL : ↥B) = (0 : L) := by
    show τ (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥B _ 0
        (Work.WilC5.ringSymL FirstOrder.Ring.zeroFunc) (![] : Fin 0 → ↥B)) = 0
    have h := τ.map_fun (Work.WilC5.ringSymL FirstOrder.Ring.zeroFunc) (![] : Fin 0 → ↥B)
    have h2 : (τ ∘ (![] : Fin 0 → ↥B)) = (![] : Fin 0 → L) := by
      funext i; exact Fin.elim0 i
    rw [h2] at h
    rw [h]
    show @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc L _ 0
        (Sum.inl (Sum.inl FirstOrder.Ring.zeroFunc)) (![] : Fin 0 → L) = 0
    rw [Work.WilC5.reductStruct_funMap_ring]
    exact hzeroL
  -- ## 4. the sign of `x` determines the sign of `y`
  have hpos : (0 : K) < x ↔ (0 : L) < y := by
    have h := (hcut (Work.WilC5.zeroEL : ↥B)).1
    rwa [hzB, hτzB] at h
  -- ## 5. the two sides of the relation, solved for `x'` and `y'`
  have hlogx : x' = Work.WilC5.logFun x - (a : K) := by
    rw [eq_sub_iff_add_eq, add_comm]
    rw [haddK] at hrel
    exact hrel.symm
  have hlogy : y' = Work.WilC5.logFun y - (τ a : L) := by
    rw [eq_sub_iff_add_eq, add_comm]
    rw [haddL] at hrelL
    exact hrelL.symm
  -- ## 6. the cut of `logFun x` is the image of the cut of `logFun y`
  have key : ∀ c : ↥B,
      (((c : K) < Work.WilC5.logFun x ↔ (τ c : L) < Work.WilC5.logFun y) ∧
       (Work.WilC5.logFun x < (c : K) ↔ Work.WilC5.logFun y < τ c)) := by
    intro c
    by_cases hx0 : (0 : K) < x
    · have hy0 : (0 : L) < y := hpos.mp hx0
      have hKc := Work.WilC5.S4ExpG.exp_cut_field (w := x) (x := (c : K))
        hTEK haddK hlenegK hx0
      have hLc := Work.WilC5.S4ExpG.exp_cut_field (w := y) (x := (τ c : L))
        hTEL haddL hlenegL hy0
      constructor
      · have hc := (hcut ⟨Work.WilC5.expE (c : K), hBexp (c : K) c.2⟩).1
        rw [hτexp c] at hc
        exact hKc.2.symm.trans (hc.trans hLc.2)
      · have hc := (hcut ⟨Work.WilC5.expE (c : K), hBexp (c : K) c.2⟩).2
        rw [hτexp c] at hc
        exact hKc.1.symm.trans (hc.trans hLc.1)
    · have hy0 : ¬ (0 : L) < y := fun h => hx0 (hpos.mpr h)
      have hzx : Work.WilC5.logFun x = (0 : K) :=
        Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos hTEK haddK honeK hlenegK x hx0
      have hzy : Work.WilC5.logFun y = (0 : L) :=
        Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos hTEL haddL honeL hlenegL y hy0
      rw [hzx, hzy]
      refine ⟨?_, ?_⟩
      · have h := hτlt c (Work.WilC5.zeroEL : ↥B)
        rwa [hzB, hτzB] at h
      · have h := hτlt (Work.WilC5.zeroEL : ↥B) c
        rwa [hzB, hτzB] at h
  -- ## 7. assemble the cut of `x'` from the cut of `logFun x`, shifting by `a`
  intro b
  have hmemK : (b : K) + (a : K) = ((Work.WilC5.addEL b a : ↥B) : K) := (hcoe_add b a).symm
  have hmemL : τ (Work.WilC5.addEL b a) = (τ b : L) + (τ a : L) := by
    rw [Work.WilC5.map_addEL]
    exact haddEL_L (τ b) (τ a)
  constructor
  · rw [hlogx, hlogy, lt_sub_iff_add_lt, lt_sub_iff_add_lt, hmemK, ← hmemL]
    exact (key (Work.WilC5.addEL b a)).1
  · rw [hlogx, hlogy, sub_lt_iff_lt_add, sub_lt_iff_lt_add, hmemK, ← hmemL]
    exact (key (Work.WilC5.addEL b a)).2

end Work.WilC5
