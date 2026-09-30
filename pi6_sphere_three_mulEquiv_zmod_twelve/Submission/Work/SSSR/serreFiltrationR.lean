import Mathlib
import Submission.Work.SSSR.SSetChain
import Submission.Work.SSSR.StemsB.SerreFiltration
import Submission.Work.SSSR.Cohomology.Chains
import Submission.Work.SSSR.Filtration
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Serre filtration of the singular chains, over an arbitrary coefficient ring

`Work.SSSR.serreFiltrationR R p` is the R-coefficient version of `Work.SSS.serreFiltration`:
the Serre filtration of the singular chain complex `C_*(E; R)` along `p : E → B`, whose `s`-th term
is the chains of the preimage under `Sing p` of the `(s+1)`-skeleton of `Sing B`.
-/

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

/-- The **Serre filtration** of the singular chain complex of `E` (coefficients in `R`) along a map
`p : E → B` is a saturated filtration in the sense of `Work.SSSR.Filtration`: its `s`-th term is
the singular chain complex of the preimage under `Sing p` of the `(s+1)`-skeleton of `Sing B`. -/
theorem serreFiltrationR (R : Type) [CommRing R] [Nontrivial R]
    (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    ∃ ξ : Filtration R (Work.SSSR.Cohomology.singularChains R (TopCat.of E)),
      ξ.F = Work.SSSR.natShift ⋙
        Work.SSSR.StemsB.serreChainFiltration (TopCat.toSSet.map (TopCat.ofHom p)) R := by
  let f : TopCat.toSSet.obj (TopCat.of E) ⟶ TopCat.toSSet.obj (TopCat.of B) :=
    TopCat.toSSet.map (TopCat.ofHom p)
  let S : ℕ → (TopCat.toSSet.obj (TopCat.of E)).Subcomplex :=
    fun n => Work.SSSR.StemsB.serreSubcomplex f n
  let ξF : ℕ ⥤ ChainComplex (ModuleCat R) ℕ :=
    Work.SSSR.natShift ⋙ Work.SSSR.StemsB.serreChainFiltration f R
  let incl : ∀ s, ξF.obj s ⟶ Work.SSSR.Cohomology.singularChains R (TopCat.of E) :=
    fun s => Work.SSSR.sChainMap R (Subfunctor.ι (S (s + 1)))
  refine ⟨⟨ξF, ?_, incl, ?_, ?_, ?_⟩, rfl⟩
  · intro s
    exact Work.SSSR.mono_serreChainFiltration_map R f
      (Work.SSSR.natShift.map (homOfLE (Nat.le_succ s)))
  · intro s
    exact Work.SSSR.sChainMap_mono R (Subfunctor.ι (S (s + 1))) inferInstance
  · intro s t h
    show Work.SSSR.sChainMap R
          ((Work.SSSR.StemsB.serreFiltration f).map (Work.SSSR.natShift.map (homOfLE h))) ≫
        Work.SSSR.sChainMap R (Subfunctor.ι (S (t + 1))) =
      Work.SSSR.sChainMap R (Subfunctor.ι (S (s + 1)))
    exact (Work.SSSR.sChainMap_comp R _ _).trans
      (congrArg (fun w => Work.SSSR.sChainMap R w) (Work.SSSR.serreFiltration_map_iota f s t h))
  · intro n
    exact Work.SSSR.isIso_f_of_bijective R (Subfunctor.ι (S (n + 1))) n
      (Work.SSSR.bijective_iota_app_of_obj_eq_top (S (n + 1)) n
        (Work.SSSR.serreSubcomplex_obj_eq_top f n))

end

end Work.SSSR
