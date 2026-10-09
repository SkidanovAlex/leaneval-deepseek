import Mathlib
import Submission.Work.SSGRoute.PT.kummerSES
import Submission.Work.SSGRoute.kummerBase_euler_connectingH3_descent
import Submission.Work.SSGRoute.range_deltaH3_eq_ker_mapH3
import Submission.Work.SSGRoute.range_mapH2_eq_ker_deltaH3
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.H3Map.mapC3c_mem_Z3_mem_B3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H³(G, Hom_ℤ(ℤ/p, C)) = 0` under the Kummer hypotheses

The coefficient Kummer sequence

  `0 → Hom_ℤ(ℤ/p, C) → C →^{p·} C → 0`

of a `p`-divisible discrete `G`-module `C` (`Work.SSGRoute.PT.kummerSES`) yields the segment

  `H²(G,C) →^{p·} H²(G,C) →^{δ³} H³(G, Hom_ℤ(ℤ/p, C)) → H³(G,C)`

of the long exact sequence.  Its exactness at `H²(G,C)` and at `H³(G, Hom_ℤ(ℤ/p, C))` gives

* `ker δ³ = range (p· on H²) = ⊤` when `p · : H²(G,C) → H²(G,C)` is onto;
* `range δ³ = ker H³(ι)`, hence `H³(ι)` is injective;

and an injection into the trivial group `H³(G,C) = 0` has trivial source.
-/

open scoped Classical

namespace Work.SSGRoute.PTfin

/-- **`H³` of `Hom_ℤ(ℤ/p, C)` vanishes when `H³(G,C) = 0` and `H²(G,C)` is `p`-divisible.**

The coefficient Kummer sequence `0 → Hom_ℤ(ℤ/p,C) → C →^{p·} C → 0` gives the exact diagram

  `H²(G,C) →^{p·} H²(G,C) →^{δ³} H³(G,Hom_ℤ(ℤ/p,C)) →^{H³(ι)} H³(G,C)`.

Surjectivity of `p ·` on `H²(G,C)` makes `δ³` vanish, so exactness makes `H³(ι)` injective; as
`H³(G,C)` is a subsingleton, so is `H³(G, Hom_ℤ(ℤ/p,C))`. -/
theorem subsingleton_H3_conjHom_of_units (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {C : Type*} [AddCommGroup C] [DistribMulAction G C]
    (hdiv : ∀ c : C, ∃ c' : C, p • c' = c) (hM : Work.AbsoluteKummer.IsDiscreteModule G C)
    (h2div : Function.Surjective (fun x : Work.AbsoluteKummer.H2 G C => p • x))
    (h3C : Subsingleton (Work.SSGRoute.H3 (M := C) G)) :
    Subsingleton (Work.SSGRoute.H3
      (M := Work.SSGRoute.PT.ConjHom (Work.SSGRoute.PT.TrivMod G p) C) G) := by
  -- the coefficient Kummer sequence `0 → Hom_ℤ(ℤ/p,C) → C →^{p·} C → 0`
  obtain ⟨S, hSι, hSπ⟩ := Work.SSGRoute.PT.kummerSES (G := G) p hdiv hM
  -- `p ·` on `H²(G,C)` is `mapH²(S.π)`, which is therefore onto
  have hsurj : Function.Surjective (Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant) := by
    intro y
    obtain ⟨x, hx⟩ := h2div y
    exact ⟨x, by rw [Work.SSGRoute.PT.mapH2_eq_nsmul p S hSπ x]; exact hx⟩
  -- exactness at `H²(G,C)`: `ker δ³ = range (p·) = ⊤`, so `δ³ = 0`
  have hker : S.deltaH3.ker = ⊤ := by
    rw [← Work.SSGRoute.range_mapH2_eq_ker_deltaH3 S]
    exact AddMonoidHom.range_eq_top.mpr hsurj
  have hd3 : S.deltaH3 = 0 := AddMonoidHom.ext fun x => by
    have hx : x ∈ S.deltaH3.ker := by rw [hker]; exact AddSubgroup.mem_top x
    simpa using (AddMonoidHom.mem_ker.mp hx)
  -- exactness at `H³(G, Hom_ℤ(ℤ/p,C))`: `ker H³(ι) = range δ³ = ⊥`, so `H³(ι)` is injective
  have hinj : Function.Injective (Work.SSGRoute.H3Map.mapH3 S.iota S.iota_equivariant) := by
    rw [← AddMonoidHom.ker_eq_bot_iff]
    rw [← Work.SSGRoute.range_deltaH3_eq_ker_mapH3 S, hd3, AddMonoidHom.range_zero]
  exact ⟨fun x y => hinj (Subsingleton.elim _ _)⟩

end Work.SSGRoute.PTfin
