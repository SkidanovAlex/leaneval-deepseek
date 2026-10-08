/-
# The fibre count for the anisotropic squaring form

Given a biadditive cocycle `b : V → V → W` with `|V| = |W| ^ 2`, all involutions of
`P = TwoStep V W b` central, `Z(P) = kerFst`, and an automorphism `ξ` of `P` permuting the
involutions transitively, the squaring form `Q v = b v v` is anisotropic and every non-zero
fibre of `Q` has cardinality `|W| + 1`.

The proof: `ξ` preserves the centre, hence induces an additive automorphism `xiW` of `W`
(`Q3/induced.lean`) whose squaring-form equivariance is `xiV_quad`.  Transitivity of `ξ` on the
involutions (which are exactly the elements `⟨0,w⟩`, `w ≠ 0`, by `cocycle_setup.lean`) says that
`xiW` is transitive on `W ∖ {0}`, so the iterates of `xiV` transport every non-zero fibre of `Q`
bijectively onto every other one.  The fibres therefore all have the same cardinality `c`; since
`Q⁻¹ 0 = {0}` (anisotropy), summing over `W` gives `|W| ^ 2 = 1 + (|W| - 1) * c`, whence
`c = |W| + 1`.
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.cocycle_setup
import Submission.Work.Higman.Q3.L12.induced_local

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman.Q3

open Work.Higman

theorem fiber_card_sq
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    {b : V → V → W} [Biadd b]
    (hcardV : Nat.card V = Nat.card W ^ 2) (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b))
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    (w : W) (hw : w ≠ 0) :
    Nat.card {v : V // b v v = w} = Nat.card W + 1 := by
  classical
  haveI hfinW : Finite W := finite_of_hW hW
  haveI hfinV : Finite V := finite_V_of_hcardV hcardV hW
  -- the squaring form is anisotropic
  have hane : ∀ v : V, b v v = 0 → v = 0 := fun v => (b_self_eq_zero_iff hinvol hcenter v).mp
  -- `ξ` on the centre, in terms of `Function.iterate`
  have hpow : ∀ k : ℕ, ∀ a : W,
      (ξ ^ k) (⟨0, a⟩ : TwoStep V W b) = ⟨0, (xiW hcenter ξ)^[k] a⟩ := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ, MulAut.mul_apply, xi_apply_zero hcenter ξ, ih, Function.iterate_succ_apply]
  -- `xiW` is transitive on `W ∖ {0}`
  have htransW : ∀ a c : W, a ≠ 0 → c ≠ 0 → ∃ k : ℕ, (xiW hcenter ξ)^[k] a = c := by
    intro a c ha hc
    obtain ⟨k, hk⟩ := htrans ⟨0, a⟩ ⟨0, c⟩
      ((orderOf_eq_two_iff hinvol hcenter _).mpr ⟨rfl, ha⟩)
      ((orderOf_eq_two_iff hinvol hcenter _).mpr ⟨rfl, hc⟩)
    refine ⟨k, ?_⟩
    rw [hpow k a] at hk
    simpa using congrArg (fun x : TwoStep V W b => x.snd) hk
  -- equivariance of the squaring form under the iterates of `xiV`
  have hiter : ∀ k : ℕ, ∀ u : V,
      b ((xiV hcenter ξ)^[k] u) ((xiV hcenter ξ)^[k] u) = (xiW hcenter ξ)^[k] (b u u) := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', xiV_quad hcenter ξ, ih]
  -- the fibre cardinalities are constant over the non-zero elements of `W`
  have hfiber : ∀ z : W, z ≠ 0 →
      Nat.card {v : V // b v v = z} = Nat.card {v : V // b v v = w} := by
    intro z hz
    obtain ⟨k, hk⟩ := htransW z w hz hw
    let E : V ≃ V := (xiV hcenter ξ : V ≃ V)
    let Wm : W ≃ W := (xiW hcenter ξ : W ≃ W)
    have hk' : (Wm ^ k) z = w := by rw [Equiv.Perm.coe_pow]; exact hk
    have hEp : ∀ n : ℕ, ∀ u : V, b ((E ^ n) u) ((E ^ n) u) = (Wm ^ n) (b u u) := by
      intro n u
      rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
      exact hiter n u
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨(E ^ k) x.1, ?_⟩
        invFun := fun x => ⟨(E ^ k).symm x.1, ?_⟩
        left_inv := fun x => Subtype.ext (Equiv.symm_apply_apply (E ^ k) x.1)
        right_inv := fun x => Subtype.ext (Equiv.apply_symm_apply (E ^ k) x.1) }
    · rw [hEp k x.1, x.2, hk']
    · have h1 := hEp k ((E ^ k).symm x.1)
      rw [Equiv.apply_symm_apply] at h1
      rw [x.2] at h1
      have h2 : (Wm ^ k) (b ((E ^ k).symm x.1) ((E ^ k).symm x.1)) = (Wm ^ k) z := by
        rw [← h1, hk']
      exact Equiv.injective (Wm ^ k) h2
  -- the fibre over `0` is a singleton
  have hc0 : Nat.card {v : V // b v v = 0} = 1 := by
    haveI : Subsingleton {v : V // b v v = 0} :=
      ⟨fun x y => Subtype.ext (by rw [hane x.1 x.2, hane y.1 y.2])⟩
    haveI : Nonempty {v : V // b v v = 0} := ⟨⟨0, Biadd.zero_left (b := b) (0 : V)⟩⟩
    exact Nat.card_unique
  haveI hFV : Fintype V := Fintype.ofFinite V
  haveI hFW : Fintype W := Fintype.ofFinite W
  -- double counting over the fibres of `Q`
  have hsum : Nat.card V = ∑ z : W, Nat.card {v : V // b v v = z} := by
    rw [← Nat.card_sigma (β := fun z : W => {v : V // b v v = z})]
    exact (Nat.card_congr (Equiv.sigmaPreimageEquiv (fun v : V => b v v))).symm
  have hsplit : (∑ z : W, Nat.card {v : V // b v v = z})
      = 1 + (Nat.card W - 1) * Nat.card {v : V // b v v = w} := by
    rw [← Finset.sum_erase_add (s := (Finset.univ : Finset W))
      (f := fun z : W => Nat.card {v : V // b v v = z}) (Finset.mem_univ 0)]
    rw [hc0]
    have h1 : ∑ x ∈ (Finset.univ : Finset W).erase 0, Nat.card {v : V // b v v = x}
        = ∑ _x ∈ (Finset.univ : Finset W).erase 0, Nat.card {v : V // b v v = w} := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      exact hfiber x (by rw [Finset.mem_erase] at hx; exact hx.1)
    rw [h1, Finset.sum_const_nat (fun _ _ => rfl),
      Finset.card_erase_of_mem (Finset.mem_univ (0 : W)), Finset.card_univ,
      Nat.card_eq_fintype_card (α := W), Nat.add_comm]
  have hmain : 1 + (Nat.card W - 1) * Nat.card {v : V // b v v = w} = Nat.card W ^ 2 := by
    rw [← hsplit, ← hsum, hcardV]
  -- solve for the common fibre cardinality
  have hq1 : 0 < Nat.card W - 1 := by omega
  have h1 : (Nat.card W - 1) * Nat.card {v : V // b v v = w} = Nat.card W ^ 2 - 1 :=
    Nat.eq_sub_of_add_eq (by rw [Nat.add_comm, ← hmain])
  have h2 : (Nat.card W - 1) * (Nat.card W + 1) = Nat.card W ^ 2 - 1 := by
    rw [Nat.mul_comm]
    simpa using (Nat.sq_sub_sq (Nat.card W) 1).symm
  have heq : (Nat.card W - 1) * Nat.card {v : V // b v v = w}
      = (Nat.card W - 1) * (Nat.card W + 1) := by rw [h1, h2]
  exact Nat.mul_left_cancel hq1 heq

end Work.Higman.Q3
