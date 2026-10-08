import Mathlib
import Submission.Work.ThreePoints.Basic
import Submission.Work.LocalPrelim.card_map_mul_card_inf_ker
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_conj_map

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Strong embeddedness passes to the quotient by an odd normal subgroup

If `H` is strongly embedded in a finite group `G` and `N ◁ G` is a normal subgroup of odd
order contained in `H`, then the image `H/N` of `H` in `G/N` is strongly embedded in `G/N`.

Write `f : G →* G ⧸ N` for the quotient map and `M = H.map f`.  Since `N ≤ H = f.ker`, the
quotient map restricted to `H` has kernel `N`, so `|M| · |N| = |H|`; as `|H|` is even and `|N|`
is odd, `|M|` is even.  Properness transports because `comap f (M) = H ≠ ⊤`.  Finally, for
`g ∉ M` with a lift `x` (`f x = g`), the subgroup `H ⊓ H^x` of `G` has odd order by strong
embeddedness of `H`, and its image under `f` is exactly `M ⊓ M^g`; an odd number has only odd
divisors.
-/

namespace Work.ThreePoints

open LeanEval.GroupTheory.Defs

theorem isStronglyEmbedded_map_quotient {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hodd : Odd (Nat.card N)) {H : Subgroup G} (hNH : N ≤ H)
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded (H.map (QuotientGroup.mk' N)) := by
  classical
  set f := QuotientGroup.mk' N with hf
  have hker : f.ker = N := QuotientGroup.ker_mk' N
  have hkerH : f.ker ≤ H := by rw [hker]; exact hNH
  refine ⟨?_, ?_, ?_⟩
  · -- `H/N ≠ ⊤` because `H` is the preimage of `H/N`.
    intro htop
    have h1 := Subgroup.comap_map_eq_self (f := f) hkerH
    rw [htop, Subgroup.comap_top] at h1
    exact hH.1 h1.symm
  · -- `|H/N|` is even since `|H| = |N| · |H/N|`, `|H|` even and `|N|` odd.
    have hM : Nat.card (Subgroup.map f H) * Nat.card N = Nat.card H := by
      have h := Work.LocalPrelim.card_map_mul_card_inf_ker f H
      rw [hker, inf_eq_right.mpr hNH] at h
      exact h
    have h2 : 2 ∣ Nat.card (Subgroup.map f H) := by
      have h2H : 2 ∣ Nat.card H := even_iff_two_dvd.mp hH.2.1
      rw [← hM] at h2H
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2H with h | h
      · exact h
      · exact absurd h ((odd_iff_not_two_dvd _).mp hodd)
    exact even_iff_two_dvd.mpr h2
  · -- for `g ∉ H/N` the odd-order subgroup `H ⊓ H^x` of `G` maps onto
    -- `(H/N) ⊓ (H/N)^g`, which therefore has odd order.
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N g
    have hxH : x ∉ H := fun hx => hg (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have hoddA := hH.2.2 x hxH
    have hB : Subgroup.map f (H ⊓ Subgroup.map (MulAut.conj x).toMonoidHom H)
        = Subgroup.map f H ⊓ Subgroup.map (MulAut.conj (f x)).toMonoidHom (Subgroup.map f H) := by
      rw [Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le f H
        (Subgroup.map (MulAut.conj x).toMonoidHom H) hkerH]
      rw [Commons.GroupTheory.Subgroup.map_conj_map f H x]
    have hdvd : Nat.card
          ↥(Subgroup.map f H ⊓ Subgroup.map (MulAut.conj (f x)).toMonoidHom (Subgroup.map f H))
        ∣ Nat.card ↥(H ⊓ Subgroup.map (MulAut.conj x).toMonoidHom H) := by
      rw [← hB]
      exact Subgroup.card_map_dvd _ f
    exact Nat.not_even_iff_odd.mp fun hev =>
      (Nat.not_even_iff_odd.mpr hoddA)
        (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hev) hdvd))

end Work.ThreePoints
