import Mathlib
import Submission.Work.Higman.RedAux.crux_helpers

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Higman.RedAux

/-- **Maschke for one operator of odd order on an elementary abelian 2-group.**

Let `Q` be an elementary abelian 2-group (`q ^ 2 = 1` for all `q`), `σ` an automorphism of `Q`
with `σ ^ e = 1` for some odd natural number `e`, and `S ≤ Q` a `σ`-invariant subgroup.  Then `S`
admits a `σ`-invariant complement.

The argument transports `Q` to the `𝔽₂`-vector space `Additive Q` (via
`AddCommGroup.zmodModule`, which uses the fact that `e`, being odd, is invertible in `𝔽₂`), applies
the averaged-projection complement `RedAux.odd_compl`, and transports the resulting subspace back
to a subgroup of `Q`. -/
theorem elem_abelian_invariant_compl {Q : Type*} [CommGroup Q]
    (h2 : ∀ q : Q, q ^ 2 = 1) (σ : MulAut Q) {e : ℕ} (he : Odd e) (hσ : σ ^ e = 1)
    (S : Subgroup Q) (hS : ∀ x ∈ S, σ x ∈ S) :
    ∃ N : Subgroup Q, (∀ x ∈ N, σ x ∈ N) ∧ S ⊓ N = ⊥ ∧ S ⊔ N = ⊤ := by
  classical
  -- `Additive Q` is an `𝔽₂`-vector space because `Q` has exponent two.
  have hmod : ∀ x : Additive Q, 2 • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact h2 x.toMul
  letI : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule hmod
  -- `σ` as an additive (hence `𝔽₂`-linear) automorphism of `Additive Q`.
  let σA : Additive Q ≃+ Additive Q :=
    { toFun := fun x => Additive.ofMul (σ x.toMul)
      invFun := fun x => Additive.ofMul (σ.symm x.toMul)
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_add' := fun x y => by rw [toMul_add, map_mul, ofMul_mul] }
  let σL : Additive Q ≃ₗ[ZMod 2] Additive Q :=
    LinearEquiv.mk (AddMonoidHom.toZModLinearMap 2 σA.toAddMonoidHom)
      σA.invFun σA.left_inv σA.right_inv
  -- `S` as an `𝔽₂`-subspace.
  let S' : Submodule (ZMod 2) (Additive Q) :=
    { Subgroup.toAddSubgroup S with
      smul_mem' := fun c x hx => by
        show c • x ∈ Subgroup.toAddSubgroup S
        exact ZMod.smul_mem hx c }
  have hm1 : ∀ x : Additive Q, x ∈ S' ↔ Additive.toMul x ∈ S := by
    intro x; simp [S', Additive.mem_toAddSubgroup]
  have happ : ∀ x : Additive Q, Additive.toMul (σL x) = σ x.toMul := fun _ => rfl
  have hσL_pow : ∀ k x, (σL ^ k) x = Additive.ofMul ((σ ^ k) x.toMul) := by
    intro k x
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih]
      show Additive.ofMul (σ ((σ ^ k) x.toMul)) = Additive.ofMul ((σ ^ (k + 1)) x.toMul)
      rw [pow_succ', MulAut.mul_apply]
  have hσL : σL ^ e = 1 := by
    apply LinearEquiv.ext
    intro x
    rw [hσL_pow, hσ]
    simp
  have hS' : ∀ x ∈ S', σL x ∈ S' := by
    intro x hx
    rw [hm1] at hx ⊢
    rw [happ]
    exact hS _ hx
  obtain ⟨N', hN'inv, hsup, hinf⟩ := odd_compl σL he hσL S' hS'
  -- Transport the subspace back to a subgroup of `Q`.
  let N : Subgroup Q :=
    { carrier := {q | Additive.ofMul q ∈ N'}
      one_mem' := by
        show Additive.ofMul (1 : Q) ∈ N'
        rw [ofMul_one]; exact N'.zero_mem
      mul_mem' := by
        intro a b ha hb
        show Additive.ofMul (a * b) ∈ N'
        rw [ofMul_mul]; exact N'.add_mem ha hb
      inv_mem' := by
        intro a ha
        show Additive.ofMul a⁻¹ ∈ N'
        rw [ofMul_inv]; exact N'.neg_mem ha }
  refine ⟨N, ?_, ?_, ?_⟩
  · intro x hx
    show Additive.ofMul (σ x) ∈ N'
    have h1 : Additive.ofMul (σ x) = σL (Additive.ofMul x) := rfl
    rw [h1]
    exact hN'inv _ hx
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxS, hxN⟩ := hx
    have h1 : Additive.ofMul x ∈ S' := (hm1 x).mpr hxS
    have h3 : Additive.ofMul x ∈ S' ⊓ N' := Submodule.mem_inf.mpr ⟨h1, hxN⟩
    rw [hinf, Submodule.mem_bot] at h3
    show x = 1
    have hx' : x = (Additive.ofMul x).toMul := rfl
    rw [hx', h3]
    exact toMul_zero
  · apply eq_top_iff.mpr
    intro x _
    rw [Subgroup.mem_sup]
    have h1 : Additive.ofMul x ∈ S' ⊔ N' := by rw [hsup]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at h1
    obtain ⟨s, hs, n, hn, hsn⟩ := h1
    refine ⟨Additive.toMul s, (hm1 s).mp hs, Additive.toMul n, hn, ?_⟩
    have hthis : (s + n).toMul = x := by rw [hsn]; rfl
    rw [toMul_add] at hthis
    exact hthis

end Work.Higman.RedAux
