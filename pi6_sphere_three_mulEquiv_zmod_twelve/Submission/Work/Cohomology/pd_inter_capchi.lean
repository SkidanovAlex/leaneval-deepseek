import Mathlib
import Submission.Work.Cohomology.pd_glue3
import Submission.Work.Cohomology.pd_crux_weak
import Submission.Work.Cohomology.pd_crux

/-!
# The cap product of the coboundary over the "intersection" chain

This is the chain-level identity used for the *middle* (intersection) slot of the
Mayer–Vietoris / Poincaré–Lefschetz duality computation: for a cochain `χ` that is relative
with respect to both `K` and `L` inside `W = U ∪ V`, and a chain `α₂` whose boundary lies in
`(W∖(K∪L)) + (W∖L) + (W∖K)`, the cap product of the coboundary `δχ` with `α₂` is, up to the
global sign, the boundary of the cap product of `χ` itself:

  `cap (δχ) mj (α₂) = -(-1)^k • d (cap χ (mj+1) α₂)`.

This is exactly the boundary formula `cap_d` for `χ` together with the vanishing of `χ` on the
three summands of `d α₂` (`cap_eq_zero_of_mem_range_inclChains`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The elementary `ℤ`-`zsmul` rearrangement closing the computation: if `dc = s • (0 - c)` for
a scalar `s` with `s * s = 1`, then `c = (-s) • dc`. -/
private lemma pd_inter_capchi_zsmul (s : ℤ) (hs : s * s = 1) {A : Type*} [AddCommGroup A]
    (dc c : A) (h : dc = s • (0 - c)) : c = (-s) • dc := by
  rw [h, neg_zsmul, ← mul_zsmul, hs, one_smul, neg_sub, sub_zero]

theorem pd_inter_capchi {M : TopCat} {U V : Set M} {K L : Set M} {k mj : ℕ}
    (χ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) k)
    (α₂ : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X (k + (mj + 1)))
    (hχK : χ ∈ relKern ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) K) k)
    (hχL : χ ∈ relKern ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) L) k)
    (hdα₂ : ∃ (g e f : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X (k + mj)),
        (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₂ = g - e - f ∧
        g ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdRelSub (U ∪ V) (K ∪ L))).f (k + mj)).hom ∧
        e ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdRelSub (U ∪ V) L)).f (k + mj)).hom ∧
        f ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdRelSub (U ∪ V) K)).f (k + mj)).hom) :
    cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
        (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) χ) mj
        ((capIdx k mj) ▸ α₂)
      = -((-1 : ℤ) ^ k) • (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (mj + 1) mj
          (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ (mj + 1) α₂) := by
  obtain ⟨g, e, f, hd, hg, he, hf⟩ := hdα₂
  -- `(W∖(K∪L)) ⊆ (W∖K)`, so `χ` (relative for `K`) kills the first summand of `d α₂`
  have hsub : pdRelSub (U ∪ V) (K ∪ L) ⊆ pdRelSub (U ∪ V) K := by
    intro y hy hyK
    exact hy (Or.inl hyK)
  have hg0 : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ mj g = 0 :=
    cap_eq_zero_of_mem_range_inclChains (TopCat.of ↥(U ∪ V)) _ _ hsub χ hχK hg
  have he0 : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ mj e = 0 :=
    cap_eq_zero_of_mem_range_inclChains (TopCat.of ↥(U ∪ V)) _ _ (fun _ h => h) χ hχL he
  have hf0 : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ mj f = 0 :=
    cap_eq_zero_of_mem_range_inclChains (TopCat.of ↥(U ∪ V)) _ _ (fun _ h => h) χ hχK hf
  -- hence `χ` kills `d α₂`
  have hzero : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ mj
      ((ModuleCat.Hom.hom (((TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))).chainComplex
        (ModuleCat.of ℤ ℤ)).d (k + (mj + 1)) (k + mj))) α₂) = 0 := by
    rw [show (ModuleCat.Hom.hom (((TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))).chainComplex
        (ModuleCat.of ℤ ℤ)).d (k + (mj + 1)) (k + mj))) α₂
        = (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₂ from rfl]
    rw [hd, map_sub, map_sub, hg0, he0, hf0]
    simp
  have hs : ((-1:ℤ)^k) * ((-1:ℤ)^k) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩
  -- the boundary formula `cap_d` for `χ`, with the vanishing term removed
  have hz : (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (mj + 1) mj
        (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ (mj + 1) α₂)
      = ((-1:ℤ)^k) • ((0 : ↑(((TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))).chainComplex
            (ModuleCat.of ℤ ℤ)).X mj))
          - cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
          (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) χ) mj
          ((capIdx k mj) ▸ α₂)) := by
    have h := cap_d ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) (m := mj) χ α₂
    rw [hzero] at h
    exact h.trans (int_smul_eq_zsmul (inferInstance : Module ℤ
      (↑(((TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))).chainComplex (ModuleCat.of ℤ ℤ)).X mj)))
      ((-1:ℤ)^k) (0 - cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
          (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) χ) mj
          ((capIdx k mj) ▸ α₂)))
  exact pd_inter_capchi_zsmul ((-1:ℤ)^k) hs _ _ hz

end

end Work.Cohomology
