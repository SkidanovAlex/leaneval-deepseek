import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers
import Submission.Work.ThreePoints.EvenCardSource.sec3_prop1_exists_uncond
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThreePoints.EvenCardSource.lemma2_propagation_uncond`

Ch. I §4 Lemma 2, part 2 (the propagation step), with the Brauer–Suzuki hypothesis removed:
assuming the conditional half `Sec4Lemma2Part1` of Lemma 2 (maximality plus evenness at *one* fixed
point forces `Q` to be a `p`-Sylow of the two-point stabiliser), we deduce the full Lemma 2
`Sec4Lemma2`.

This is a transcription of `Work.DoubleTransitivity.Sec4.sec4_lemma2_of_part1` with `hBrSz`
deleted; the only use of `hBrSz` in that argument is Ch. I §3 Prop. 1
(`Work.DoubleTransitivity.Sec3.prop1`), which is replaced here by the Brauer–Suzuki-free form
`Work.ThreePoints.EvenCardSource.sec3_prop1_exists_uncond`.

The argument is the source's (p. 156): Ch. I §3 Prop. 1 produces one fixed point `ω` of `Q` with
`|N_G(Q) ⊓ Stab ω|` even.  For any other fixed point `ω'` of `Q`, part 1 shows that `Q` is a
`p`-Sylow of `Stab ω ⊓ Stab ω'`, so Ch. I §3 Lemma 1 (`Work.ThreePoints.sec3_lemma1`) produces an
involution `u ∈ N_G(Q)` with `u • ω = ω'`, whence `N_G(Q) ⊓ Stab ω' = (N_G(Q) ⊓ Stab ω)^u` and the
orders agree.  Thus every fixed point of `Q` has an even-order normaliser, and part 1 applied to any
pair of distinct fixed points of `Q` gives both conclusions of Lemma 2 (with `P = Q` for the
second).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

namespace Work.ThreePoints.EvenCardSource

variable {G : Type} [Group G] [Finite G]

/-- Ch. I §4 Lemma 2, the propagation step, without the Brauer–Suzuki hypothesis. -/
theorem sec4_lemma2_of_part1_uncond {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1 : Work.DoubleTransitivity.Sec4.Sec4Lemma2Part1 p H) :
    Work.DoubleTransitivity.Sec4.Sec4Lemma2 p H := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro Q hQmax hQinv ω₁ ω₂ hne hQω₁ hQω₂
  obtain ⟨ωs, hωs, hEven⟩ := sec3_prop1_exists_uncond hH hp hp2 hQmax.1 hQmax.2.1
    (fun R hQR hRp hR3 => le_antisymm (hQmax.2.2 R hRp hR3 hQR) hQR)
  have hωs' : Q ≤ MulAction.stabilizer G ωs := mem_fixedPts_iff_le_stabilizer.mp hωs
  have hEven' : Even (Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓
      MulAction.stabilizer G ωs)) := by
    rw [inf_comm]; exact hEven
  have hEvenAll : ∀ ω : Work.DoubleTransitivity.Omega H, Q ≤ MulAction.stabilizer G ω →
      Even (Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ω)) := by
    intro ω hω
    by_cases hωeq : ω = ωs
    · rw [hωeq]; exact hEven'
    · have hPsyl := h1 Q hQmax hQinv ωs ω hωeq hωs' hω hEven'
      obtain ⟨u, _hu2, huQ, huω⟩ := Work.ThreePoints.sec3_lemma1 hH hp (fun h => hωeq h.symm) hPsyl
      have hconjN : conj u (Subgroup.normalizer (Q : Set G)) = Subgroup.normalizer (Q : Set G) := by
        have h := Subgroup.map_normalizer_eq_of_bijective (Q : Subgroup G)
            (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).bijective
        rw [show conj u (Subgroup.normalizer (Q : Set G)) =
              (Subgroup.normalizer (Q : Set G)).map (MulAut.conj u).toMonoidHom from rfl, h]
        rw [show (Q : Subgroup G).map (MulAut.conj u).toMonoidHom = conj u Q from rfl, huQ]
      have hcard : Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ωs) =
          Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ω) := by
        have hstep : conj u (Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ωs) =
            Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ω := by
          rw [Work.ThreePoints.conj_inf, hconjN,
            ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj u ωs, huω]
        rw [← hstep]
        exact (Subgroup.card_map_of_injective (f := (MulAut.conj u).toMonoidHom)
          (MulAut.conj u).injective).symm
      rw [← hcard]
      exact hEven'
  exact ⟨h1 Q hQmax hQinv ω₁ ω₂ hne hQω₁ hQω₂ (hEvenAll ω₁ hQω₁),
    ⟨Q, h1 Q hQmax hQinv ω₁ ω₂ hne hQω₁ hQω₂ (hEvenAll ω₁ hQω₁), hEvenAll ω₁ hQω₁⟩⟩

end Work.ThreePoints.EvenCardSource
