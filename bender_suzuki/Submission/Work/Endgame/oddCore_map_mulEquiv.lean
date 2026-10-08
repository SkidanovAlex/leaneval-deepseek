import Mathlib
import Submission.Work.Endgame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Endgame

/-- `O(G) = O_{2'}(G)` (the largest normal subgroup of odd order) is carried by any
isomorphism: `Subgroup.map` is a left adjoint, hence commutes with the defining `sSup`, and the
index set `{N | N.Normal ∧ Odd (Nat.card N)}` is transported to the corresponding one for `H`
because an isomorphism restricts to an equivalence of `N` with `N.map f`, and normality is
preserved in both directions.

No finiteness hypothesis is needed: `Nat.card` of an infinite subgroup is `0`, which is not odd,
so infinite subgroups are excluded from the defining families on both sides. -/
theorem oddCore_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) : Subgroup.map e.toMonoidHom (Submission.Blueprint.oddCore G) = Submission.Blueprint.oddCore H := by
  have hinj : Function.Injective ⇑e.toMonoidHom := e.injective
  have hsurj : Function.Surjective ⇑e.toMonoidHom := e.surjective
  have hrange : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  apply le_antisymm
  · -- `map` is a left adjoint, so it commutes with the `sSup` defining `oddCore G`, and each
    -- normal odd-order subgroup of `G` maps to one of `H`.
    rw [Submission.Blueprint.oddCore, Submission.Blueprint.oddCore,
      (Subgroup.gc_map_comap e.toMonoidHom).l_sSup]
    refine iSup_le fun N => iSup_le fun hN => le_sSup ?_
    refine ⟨hN.1.map e.toMonoidHom hsurj, ?_⟩
    rw [Subgroup.card_map_of_injective hinj]
    exact hN.2
  · -- Conversely every normal odd-order subgroup of `H` pulls back to one of `G`.
    rw [Submission.Blueprint.oddCore, Submission.Blueprint.oddCore]
    refine sSup_le fun M hM => ?_
    have hmap : Subgroup.map e.toMonoidHom (Subgroup.comap e.toMonoidHom M) = M :=
      Subgroup.map_comap_eq_self (by rw [hrange]; exact le_top)
    have hcard : Nat.card ↥(Subgroup.comap e.toMonoidHom M) = Nat.card ↥M := by
      rw [← Subgroup.card_map_of_injective hinj (K := Subgroup.comap e.toMonoidHom M), hmap]
    have hKmem :
        Subgroup.comap e.toMonoidHom M ∈ {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)} :=
      ⟨hM.1.comap e.toMonoidHom, by rw [hcard]; exact hM.2⟩
    calc M = Subgroup.map e.toMonoidHom (Subgroup.comap e.toMonoidHom M) := hmap.symm
      _ ≤ Subgroup.map e.toMonoidHom (Submission.Blueprint.oddCore G) :=
            Subgroup.map_mono (le_sSup hKmem)

end Work.Endgame
