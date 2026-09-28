import Mathlib
import Submission.Work.SSS.Packet
import Submission.Work.SSS.SSetChain
import Submission.Work.StemsB.SerreFiltration
import Submission.Work.Cohomology.Chains

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

/-- The **Serre filtration** of the singular chain complex of `E` along a map `p : E → B` is a
saturated filtration in the sense of `Work.SSS.Filtration`: its `s`-th term is the singular chain
complex of the preimage under `Sing p` of the `(s+1)`-skeleton of `Sing B` (so that it contains all
singular `s`-chains, the field `Filtration.sat`), and its `s`-th graded piece is the chain complex
of the quotient of the nondegenerate `s`-simplices of `Sing B`. -/
theorem serreFiltration (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    ∃ ξ : Work.SSS.Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)),
      ξ.F = Work.SSS.natShift ⋙
        Work.StemsB.serreChainFiltration (TopCat.toSSet.map (TopCat.ofHom p)) ℤ := by
  let f : TopCat.toSSet.obj (TopCat.of E) ⟶ TopCat.toSSet.obj (TopCat.of B) :=
    TopCat.toSSet.map (TopCat.ofHom p)
  let S : ℕ → (TopCat.toSSet.obj (TopCat.of E)).Subcomplex :=
    fun n => Work.StemsB.serreSubcomplex f n
  let ξF : ℕ ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
    Work.SSS.natShift ⋙ Work.StemsB.serreChainFiltration f ℤ
  let incl : ∀ s, ξF.obj s ⟶ Work.Cohomology.singularChains ℤ (TopCat.of E) :=
    fun s => Work.SSS.sChainMap ℤ (Subfunctor.ι (S (s + 1)))
  refine ⟨⟨ξF, ?_, incl, ?_, ?_, ?_⟩, rfl⟩
  · intro s
    exact mono_serreChainFiltration_map ℤ f
      (Work.SSS.natShift.map (homOfLE (Nat.le_succ s)))
  · intro s
    exact sChainMap_mono ℤ (Subfunctor.ι (S (s + 1))) inferInstance
  · intro s t h
    show Work.SSS.sChainMap ℤ
          ((Work.StemsB.serreFiltration f).map (Work.SSS.natShift.map (homOfLE h))) ≫
        Work.SSS.sChainMap ℤ (Subfunctor.ι (S (t + 1))) =
      Work.SSS.sChainMap ℤ (Subfunctor.ι (S (s + 1)))
    exact (sChainMap_comp ℤ _ _).trans
      (congrArg (fun w => Work.SSS.sChainMap ℤ w) (serreFiltration_map_iota f s t h))
  · intro n
    exact isIso_f_of_bijective ℤ (Subfunctor.ι (S (n + 1))) n
      (bijective_iota_app_of_obj_eq_top (S (n + 1)) n (serreSubcomplex_obj_eq_top f n))

end

end Work.SSS
