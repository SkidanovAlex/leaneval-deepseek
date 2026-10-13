import Mathlib
import Submission.Work.WilC5.ExpLog
import Submission.Work.WilC5.Bridge
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC5.LogDefSetModel
import Submission.Work.WilC5.LogFunMap
import Submission.Work.WilC5.logFun_expE

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- An `LEc`-substructure of a model of `TE` which is itself a model of `TE` is closed under the
definable logarithm: `x ∈ F → logFun x ∈ F`.

This is the "graph of the definable logarithm" argument of `LogFunMap.lean` applied to the
inclusion embedding `F ↪[LEc] K`: the definable logarithm is preserved by `LEc`-embeddings of
models of `TE`, so `logFun` computed in `K` on an element of `F` is the image of `logFun`
computed in `F`, hence lies in `F`. -/
theorem logFun_mem_of_substructure {K : Type} [WilkiesDesign.CG.LEc.Structure K]
    (hK : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (F : WilkiesDesign.CG.LEc.Substructure K) (hF : (F : Type) ⊨ WilkiesDesign.CG.TE)
    {x : K} (hx : x ∈ F) :
    Work.WilC5.logFun x ∈ F := by
  -- `LogFunMap` for the inclusion embedding `F.subtype : F ↪[LEc] K`, specialised at `⟨x, hx⟩`
  have hmap : F.subtype (Work.WilC5.logFun (⟨x, hx⟩ : F)) = Work.WilC5.logFun x := by
    have h := Work.WilC5.LogFunMap hF hK (Substructure.subtype F) (⟨x, hx⟩ : F)
    simpa using h
  -- the value of `logFun` at `⟨x, hx⟩` lies in `F` (it is a coefficient of an element of `F`)
  have hmem : F.subtype (Work.WilC5.logFun (⟨x, hx⟩ : F)) ∈ F :=
    (Work.WilC5.logFun (⟨x, hx⟩ : F)).2
  rwa [hmap] at hmem

end Work.WilC5
