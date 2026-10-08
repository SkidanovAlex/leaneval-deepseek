import Mathlib
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.Reductions.OddResidual
import Submission.Work.PSU3.StageA.lemma2cAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

/-
# The two remaining assembly glue pieces

For the final assembly of `Work.PSU3.StageB.centralizer_oddResidual_isPSU3_v2` (via
`Work.PSU3.StageB.isPSU3_of_step4_data`, whose parameter list fixes the shape):

* `t ∈ F` where `F = Work.PSU3.StageB.centralizerOddResidual P = O^{2'}(C_G(P))`: `t` centralises
  `P` (`hPV : P ≤ centD H t ≤ C_G(t)`), so `t ∈ C_G(P)`, and `t` is a `2`-element (it is an
  involution, `hS.split.invol`), so it lies in `O^{2'}(C_G(P))` — the same argument as
  `StageA/lemma2c`'s `htF`, via `mem_map_oddResidual_of_orderOf_eq_two_pow` (in
  `StageA/lemma2cAux.lean`, listed in `depends_on`; `mem_oddResidual_of_mul_self_mem` in
  `Reductions/OddResidual.lean` is also available for the `orderOf = 2` case);

* the quotient isomorphism `↥F ⧸ Z(↥F) ≃* Y` from an epimorphism `φ : ↥F →* Y` with
  `φ.ker = Z(↥F)` — Mathlib's `QuotientGroup.quotientKerEquivOfSurjective` (with
  `QuotientGroup.quotientMulEquivOfEq hker.symm` to move the kernel), returned as `Nonempty` so the
  caller can `obtain` it.

Both are inputs of `isPSU3_of_step4_data` (`t` for the datum transfer, the isomorphism for the
final conjunct). -/
theorem t_mem_and_center_quotient {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) :
    t ∈ Work.PSU3.StageB.centralizerOddResidual P ∧
      ∀ {Y : Type} [Group Y]
        (φ : ↥(Work.PSU3.StageB.centralizerOddResidual P) →* Y),
        Function.Surjective φ →
        φ.ker = Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P) →
        Nonempty (↥(Work.PSU3.StageB.centralizerOddResidual P) ⧸
          (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)) ≃* Y) := by
  refine ⟨?_, ?_⟩
  · -- `t` centralises `P`, hence lies in `C_G(P)`, and it is a `2`-element
    have htC : t ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hPV hx)).2
    simpa [centralizerOddResidual] using
      (Work.PSU3.StageA.mem_map_oddResidual_of_orderOf_eq_two_pow
        (C := Subgroup.centralizer (P : Set G)) htC (k := 1)
        (by rw [hS.split.invol, pow_one]))
  · -- the quotient by the kernel of a surjection with kernel `Z(F)`
    intro Y _ φ hφ hker
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

end Work.PSU3.StageB
