import Mathlib
import Submission.Work.OROneRel.winGateDefs
import Submission.Work.OROneRel.freiheitssatz_not_supportedOn

namespace Work.OROneRel

universe u

theorem winGateFreiheitssatz {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) {S : Set (α × ℤ)}
    (hS : S ⊆ Work.OROneRel.winE c lo hi)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator (Work.OROneRel.winRoot Wt c lo hi u))
    (hout : ¬ Work.OROneRel.SupportedOn (Work.OROneRel.winRoot Wt c lo hi u)
      (Set.range (Work.OROneRel.winBetaSubVal Wt c hS))) :
    Function.Injective
      ((PresentedGroup.mk ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))).comp
        (FreeGroup.lift (fun e : Work.OROneRel.winBetaSub Wt c S =>
          FreeGroup.of (Work.OROneRel.winBetaSubVal Wt c hS e)))) := by
  classical
  -- The Freiheitssatz applies to the vertex relator `winRoot ^ l` with the gate's alphabet
  -- `T = range (winBetaSubVal …)`: `presentedGroupMap (winRoot ^ l) T` is injective.
  have hfrei : Function.Injective (presentedGroupMap (Work.OROneRel.winRoot Wt c lo hi u ^ l)
      (Set.range (Work.OROneRel.winBetaSubVal Wt c hS))) :=
    freiheitssatz_pow_of_not_supportedOn l hl hcyc hout
  -- The gate alphabet `winBetaSub Wt c S` is in bijection with the range `T` of `winBetaSubVal`.
  let φ : Work.OROneRel.winBetaSub Wt c S → Set.range (Work.OROneRel.winBetaSubVal Wt c hS) :=
    fun e => ⟨Work.OROneRel.winBetaSubVal Wt c hS e, Set.mem_range_self e⟩
  have hφ : Function.Injective φ := by
    intro e e' h
    have h1 : Work.OROneRel.winBetaSubVal Wt c hS e = Work.OROneRel.winBetaSubVal Wt c hS e' :=
      Subtype.ext_iff.mp h
    exact Subtype.ext (by simpa using congrArg Subtype.val h1)
  -- The target map is `presentedGroupMap (winRoot ^ l) T` composed with `FreeGroup.map φ`, hence
  -- injective as a composite of injective maps.
  have hgoal : (PresentedGroup.mk ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
        Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))).comp
        (FreeGroup.lift (fun e : Work.OROneRel.winBetaSub Wt c S =>
          FreeGroup.of (Work.OROneRel.winBetaSubVal Wt c hS e)))
      = (presentedGroupMap (Work.OROneRel.winRoot Wt c lo hi u ^ l)
          (Set.range (Work.OROneRel.winBetaSubVal Wt c hS))).comp
          (FreeGroup.map φ) := by
    apply FreeGroup.ext_hom
    intro e
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.map.of, presentedGroupMap]
    rfl
  rw [hgoal]
  exact hfrei.comp (FreeGroup.map_injective (f := φ) hφ)

end Work.OROneRel
