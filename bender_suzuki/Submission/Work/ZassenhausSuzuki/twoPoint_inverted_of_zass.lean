import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- In a split rank-one configuration with `H` a Zassenhaus subgroup, the Weyl element `t`
inverts the two-point stabiliser `D = H ∩ H^t`:

`∀ d ∈ twoPoint H t, t * d * t⁻¹ = d⁻¹`.

This is `Work.ZassenhausSuzuki.twoPoint_inverted` with its two spurious hypotheses removed.
Suggested proof: `Work.ZassenhausPSL2.ZData.centD_eq_bot_aux H Q t h hZ` (which carries no
hypothesis on `Q`) says `D` has trivial centraliser in `t`; conjugation by `t` is then a
fixed-point-free automorphism of `D` of order two, so Burnside's lemma
(`Work.ZassenhausPSL2.ZData.eq_inv_of_fpf_order_two`) inverts every element. The proof of
`Work.ZassenhausPSL2.ZData.t_conj_eq_inv` is exactly this argument; it never uses its
hypotheses `hQ : Q ≠ ⊥` and `h2 : IsPGroup 2 Q`, so it can be transcribed verbatim.
(Note `t * t = 1`, so `t * d * t⁻¹ = t * d * t`.) -/
theorem twoPoint_inverted_of_zass {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H) :
    ∀ d ∈ Submission.Blueprint.twoPoint H t, t * d * t⁻¹ = d⁻¹ := by
  -- `V = C_D(t) = 1`, so conjugation by `t` is a fixed-point-free automorphism of `D`
  -- of order two, hence inversion (Burnside's lemma).
  have hV : centD H t = ⊥ := Work.ZassenhausPSL2.ZData.centD_eq_bot_aux H Q t h hZ
  let φhom : ↥(twoPoint H t) →* ↥(twoPoint H t) :=
    { toFun := fun x => ⟨(MulAut.conj t) (x : G), by
        rw [MulAut.conj_apply, Work.ZassenhausPSL2.t_inv h]
        exact Work.ZassenhausPSL2.dStab_conj_mem h x.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show (MulAut.conj t) (↑(x * y) : G) = (MulAut.conj t) ↑x * (MulAut.conj t) ↑y
        rw [Subgroup.coe_mul, map_mul] }
  have hcoe_apply : ∀ x : ↥(twoPoint H t), (φhom x : G) = t * (x : G) * t⁻¹ := by
    intro x
    show (MulAut.conj t) (x : G) = t * (x : G) * t⁻¹
    rw [MulAut.conj_apply]
  have hφ2 : ∀ x : ↥(twoPoint H t), φhom (φhom x) = x := by
    intro x
    apply Subtype.ext
    show (MulAut.conj t) ((MulAut.conj t) (x : G)) = (x : G)
    rw [MulAut.conj_apply, MulAut.conj_apply, Work.ZassenhausPSL2.t_inv h]
    exact Work.ZassenhausPSL2.t_conj_invol h (x : G)
  have hφfpf : ∀ x : ↥(twoPoint H t), φhom x = x → x = 1 := by
    intro x hx
    have h1 : t * (x : G) * t⁻¹ = (x : G) := by
      rw [← hcoe_apply x]
      exact congrArg Subtype.val hx
    rw [Work.ZassenhausPSL2.t_inv h] at h1
    have hcoe : (x : G) * t = t * (x : G) := by
      have h2' : t * (x : G) = (x : G) * t := by
        calc t * (x : G) = t * (x : G) * (t * t) := by
              rw [Work.ZassenhausPSL2.t_mul_t h, mul_one]
          _ = (t * (x : G) * t) * t := by group
          _ = (x : G) * t := by rw [h1]
      exact h2'.symm
    have hmem : (x : G) ∈ centD H t := by
      rw [Work.ThreePoints.mem_centD]
      exact ⟨(Subgroup.mem_inf.mp x.2).1, (Work.ThreePoints.mem_twoPoint.mp x.2).2, hcoe⟩
    have : (x : G) = 1 := Subgroup.mem_bot.mp (hV ▸ hmem)
    exact Subtype.ext this
  have key := Work.ZassenhausPSL2.ZData.eq_inv_of_fpf_order_two φhom hφ2 hφfpf
  intro d hd
  rw [Work.ZassenhausPSL2.t_inv h]
  have hx := key ⟨d, hd⟩
  have h1 : (φhom ⟨d, hd⟩ : G) = (⟨d, hd⟩ : ↥(twoPoint H t))⁻¹ := congrArg Subtype.val hx
  rw [hcoe_apply ⟨d, hd⟩, Subgroup.coe_inv, Work.ZassenhausPSL2.t_inv h] at h1
  exact h1

end Work.ZassenhausSuzuki
