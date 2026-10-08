import Mathlib
import Submission.Work.LocalPrelim.card_map_mul_card_inf_ker
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_conj_map
import Submission.Work.ThreePoints.isStronglyEmbedded_map_quotient
import Submission.Work.Endgame.isStronglyEmbedded_map

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Strong embeddedness passes to the image under a surjection with odd kernel

Let `φ : F →* Y` be a surjective homomorphism of groups with `F` finite and `ker φ` of odd order,
and let `H ≤ F` be strongly embedded with `ker φ ≤ H`.  Then `H.map φ` is strongly embedded in
`Y`.

Since `ker φ ≤ H` is normal in `F`, the situation is that of the quotient by an odd normal
subgroup contained in `H` (the case `Y = F ⧸ ker φ`), so the proof follows
`Work.ThreePoints.isStronglyEmbedded_map_quotient` verbatim:

* properness: `H = comap φ (H.map φ)`, so `H.map φ = ⊤` would force `H = ⊤`;
* even order: `|H.map φ| * |ker φ| = |H|` (`Work.LocalPrelim.card_map_mul_card_inf_ker`, using
  `H ⊓ ker φ = ker φ`), with `|H|` even and `|ker φ|` odd;
* intersections with conjugates: for `g = φ x ∉ H.map φ` (so `x ∉ H`) the subgroup
  `H ⊓ H^x` has odd order and maps onto
  `H.map φ ⊓ (H.map φ)^g` (using `map_inf_eq_of_ker_le` with `ker φ ≤ H` and
  `map_conj_map`); a divisor of an odd number is odd.
-/

namespace Work.ThreePoints.P3NeBot

theorem isStronglyEmbedded_map_of_ker_odd {F Y : Type} [Group F] [Finite F] [Group Y]
    (φ : F →* Y) (hφ : Function.Surjective φ) {H : Subgroup F}
    (hodd : Odd (Nat.card φ.ker)) (hkerH : φ.ker ≤ H)
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded (H.map φ) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- `H.map φ ≠ ⊤`, since `H` is the preimage of `H.map φ`.
    intro htop
    have h1 : Subgroup.comap φ (Subgroup.map φ H) = H := Subgroup.comap_map_eq_self hkerH
    rw [htop, Subgroup.comap_top] at h1
    exact hH.1 h1.symm
  · -- `|H.map φ|` is even: `|H.map φ| * |ker φ| = |H|`, `|H|` even, `|ker φ|` odd.
    have hM : Nat.card (H.map φ) * Nat.card φ.ker = Nat.card H := by
      have h := Work.LocalPrelim.card_map_mul_card_inf_ker φ H
      rwa [inf_eq_right.mpr hkerH] at h
    have h2 : 2 ∣ Nat.card (H.map φ) := by
      have h2H : 2 ∣ Nat.card H := even_iff_two_dvd.mp hH.2.1
      rw [← hM] at h2H
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2H with h | h
      · exact h
      · exact absurd h ((odd_iff_not_two_dvd _).mp hodd)
    exact even_iff_two_dvd.mpr h2
  · -- For `g ∉ H.map φ` with a lift `x`, the odd-order group `H ⊓ H^x` maps onto
    -- `(H.map φ) ⊓ (H.map φ)^g`.
    intro g hg
    obtain ⟨x, rfl⟩ := hφ g
    have hxH : x ∉ H := fun hx => hg (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have hoddA := hH.2.2 x hxH
    have hB : Subgroup.map φ (H ⊓ Subgroup.map (MulAut.conj x).toMonoidHom H)
        = Subgroup.map φ H
          ⊓ Subgroup.map (MulAut.conj (φ x)).toMonoidHom (Subgroup.map φ H) := by
      rw [Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le φ H _ hkerH,
        Commons.GroupTheory.Subgroup.map_conj_map φ H x]
    have hdvd : Nat.card ↥(Subgroup.map φ H
          ⊓ Subgroup.map (MulAut.conj (φ x)).toMonoidHom (Subgroup.map φ H))
        ∣ Nat.card ↥(H ⊓ Subgroup.map (MulAut.conj x).toMonoidHom H) := by
      rw [← hB]
      exact Subgroup.card_map_dvd _ φ
    exact Odd.of_dvd_nat hoddA hdvd

end Work.ThreePoints.P3NeBot
