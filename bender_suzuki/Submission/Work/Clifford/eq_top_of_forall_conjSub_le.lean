import Mathlib
import Submission.Work.Clifford.ResSetup
import Submission.Work.CharCore.fdRep_simple_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.eq_top_of_forall_conjSub_le`

If `V : FDRep ℂ G` is simple as a `G`-representation, `N ⊴ G` is normal, and
`W ≠ ⊥` is a `ℂ[N]`-submodule of `V` which is carried into itself by every conjugate
`gW` (`conjSub V g W ≤ W`), then `W = ⊤`.

The hypothesis `conjSub V g W ≤ W` for `g` *and* `g⁻¹` gives `gW = W`, so `W` is
`G`-stable; it is therefore a nonzero subrepresentation of the simple representation
`V`, hence everything.
-/

noncomputable section

open Classical
open scoped MonoidAlgebra

namespace Work.Clifford

theorem eq_top_of_forall_conjSub_le {G : Type*} [Group G] [Fintype G] (V : FDRep ℂ G)
    [CategoryTheory.Simple V] {N : Subgroup G} [N.Normal]
    (W : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V))
    (hW : W ≠ ⊥) (hG : ∀ g : G, conjSub V g W ≤ W) : W = ⊤ := by
  -- `W` is stable under the action of every `g : G`.
  have hstab : ∀ (g : G) {x : ResMod N V}, x ∈ W → resAct N V g x ∈ W :=
    fun g x hx => hG g (conjSub_apply_mem (N := N) V g W hx)
  -- View `W` as a subrepresentation of `V` for the `G`-action.
  let S : Subrepresentation V.ρ :=
    { toSubmodule := W.restrictScalars ℂ
      apply_mem_toSubmodule := fun g _x hx => hstab g hx }
  haveI : Representation.IsIrreducible V.ρ :=
    (Work.CharCore.fdRep_simple_iff V).mp inferInstance
  haveI : IsSimpleOrder (Subrepresentation V.ρ) := ‹Representation.IsIrreducible V.ρ›
  have hinj := Submodule.restrictScalars_injective ℂ ℂ[N] (ResMod N V)
  rcases eq_bot_or_eq_top S with h | h
  · -- `S = ⊥` would force `W = ⊥`, contradicting `hW`.
    exfalso
    apply hW
    have hbot : S.toSubmodule = ⊥ := by rw [h]; rfl
    have h1 : W.restrictScalars ℂ
        = (⊥ : Submodule ℂ[N] (ResMod N V)).restrictScalars ℂ := by
      rw [Submodule.restrictScalars_bot]
      exact hbot
    exact hinj h1
  · -- `S = ⊤` gives `W = ⊤`.
    have htop : S.toSubmodule = ⊤ := by rw [h]; rfl
    have h1 : W.restrictScalars ℂ
        = (⊤ : Submodule ℂ[N] (ResMod N V)).restrictScalars ℂ := by
      rw [Submodule.restrictScalars_top]
      exact htop
    exact hinj h1

end Work.Clifford
