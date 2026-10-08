/-
# The automorphisms of `V` and `W` induced by an automorphism of `TwoStep V W b`

Let `P = TwoStep V W b` satisfy the hypotheses of `Work.Higman.cocycle_normal_form` with `Z(P) =
kerFst` and `|V| = |W| ^ 2` (so `P` has order `|W| ^ 3`).  Any `ξ : MulAut P` preserves the centre
`Z(P) = kerFst`, hence induces

* `xiV ξ : V ≃+ V`,  `xiV ξ v = (ξ ⟨v, 0⟩).fst` (the action on `P / Z(P)`), and
* `xiW ξ : W ≃+ W`,  `xiW ξ w = (ξ ⟨0, w⟩).snd` (the action on `Z(P) ≅ W`),

and the two are linked by `ξ ⟨u, w⟩ = ⟨xiV ξ u, xiW ξ w + …⟩`.  Everything in the classification of
`Work.Higman.cocycle_normal_form` is stated in terms of `xiV`; this file isolates these two
additive automorphisms and the equivariance of the squaring form.

The centre is characteristic (`mulAut_mem_center`), so no hypothesis beyond `Z(P) = kerFst` is
needed for the invariance of `kerFst`.
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.cocycle_setup
import Submission.Work.Higman.Q3.twoStep_action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Higman

variable {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
variable {b : V → V → W} [Biadd b]

/-- An automorphism of the two-step group preserves `kerFst` (which is the centre). -/
theorem xi_mem_kerFst (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) {x : TwoStep V W b} (hx : x ∈ TwoStep.kerFst) :
    ξ x ∈ TwoStep.kerFst := by
  rw [← hcenter]
  exact Work.Higman.Q3.mulAut_mem_center' ξ (by rwa [← hcenter] at hx)

/-- An automorphism of the two-step group maps `⟨0,w⟩` into `kerFst`, hence fixes the
`V`-coordinate `0`. -/
theorem xi_zero_fst (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (w : W) : (ξ (⟨0, w⟩ : TwoStep V W b)).fst = 0 := by
  have h : (⟨0, w⟩ : TwoStep V W b) ∈ TwoStep.kerFst := rfl
  have := xi_mem_kerFst hcenter ξ h
  simpa using this

section Induced

variable [Finite V] [Finite W]

/-- `v ↦ (ξ ⟨v,0⟩).fst` is injective. -/
theorem xiV_injective (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) :
    Function.Injective (fun v : V => (ξ (⟨v, 0⟩ : TwoStep V W b)).fst) := by
  intro u v huv
  have huv' : (ξ (⟨u, 0⟩ : TwoStep V W b)).fst = (ξ (⟨v, 0⟩ : TwoStep V W b)).fst := huv
  have hmul : (ξ ((⟨u, 0⟩ : TwoStep V W b) * (⟨v, 0⟩ : TwoStep V W b)⁻¹)).fst = 0 := by
    rw [map_mul, map_inv, TwoStep.fst_mul, TwoStep.fst_inv, huv', AddExpTwo.add_self]
  have hmem : (ξ ((⟨u, 0⟩ : TwoStep V W b) * (⟨v, 0⟩ : TwoStep V W b)⁻¹)) ∈
      TwoStep.kerFst := hmul
  have hmem2 : ((⟨u, 0⟩ : TwoStep V W b) * (⟨v, 0⟩ : TwoStep V W b)⁻¹) ∈ TwoStep.kerFst := by
    have := xi_mem_kerFst hcenter (ξ⁻¹) hmem
    simpa using this
  have huv0 : u + v = 0 := by
    have := (TwoStep.mem_kerFst).mp hmem2
    simpa [TwoStep.fst_mul, TwoStep.fst_inv] using this
  calc u = u + 0 := by rw [add_zero]
    _ = u + (v + v) := by rw [AddExpTwo.add_self]
    _ = (u + v) + v := by abel
    _ = v := by rw [huv0, zero_add]

/-- `v ↦ (ξ ⟨v,0⟩).fst` is additive. -/
theorem xiV_add (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (u v : V) :
    (ξ (⟨u + v, 0⟩ : TwoStep V W b)).fst =
    (ξ (⟨u, 0⟩ : TwoStep V W b)).fst + (ξ (⟨v, 0⟩ : TwoStep V W b)).fst := by
  obtain ⟨z, hz, hzu⟩ : ∃ z ∈ TwoStep.kerFst,
      (⟨u, 0⟩ : TwoStep V W b) * ⟨v, 0⟩ = z * ⟨u + v, 0⟩ := by
    refine ⟨(⟨u, 0⟩ : TwoStep V W b) * ⟨v, 0⟩ * (⟨u + v, 0⟩)⁻¹, ?_, ?_⟩
    · rw [TwoStep.mem_kerFst]
      simp only [TwoStep.fst_mul, TwoStep.fst_inv]
      rw [AddExpTwo.add_self]
    · group
  have h1 : ξ ((⟨u, 0⟩ : TwoStep V W b) * ⟨v, 0⟩) =
      ξ z * ξ (⟨u + v, 0⟩ : TwoStep V W b) := by
    rw [hzu, map_mul]
  have h2 := congrArg (fun x : TwoStep V W b => x.fst) h1
  rw [map_mul, TwoStep.fst_mul, TwoStep.fst_mul] at h2
  have hz0 : (ξ z).fst = 0 := by
    have := xi_mem_kerFst hcenter ξ hz
    simpa using this
  rw [hz0, zero_add] at h2
  exact h2.symm

/-- **The automorphism of `V` induced by `ξ`** (its action on `V = P / Z(P)`). -/
def xiV (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) : V ≃+ V :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun v : V => (ξ (⟨v, 0⟩ : TwoStep V W b)).fst) (xiV_add hcenter ξ))
    ⟨xiV_injective hcenter ξ, Finite.surjective_of_injective (xiV_injective hcenter ξ)⟩

/-- The defining property of `xiV`. -/
theorem xiV_apply (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (v : V) :
    xiV hcenter ξ v = (ξ (⟨v, 0⟩ : TwoStep V W b)).fst := rfl

/-- **`ξ` on coordinates:** the `V`-coordinate of `ξ x` is `xiV (x.fst)`. -/
theorem xiV_fst (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (x : TwoStep V W b) :
    (ξ x).fst = xiV hcenter ξ x.fst := by
  have hx : (⟨x.fst, 0⟩ : TwoStep V W b) * ⟨0, x.snd⟩ = x := by
    ext <;> simp [TwoStep.fst_mul, TwoStep.snd_mul, Biadd.zero_right, Biadd.zero_left]
  have h1 : ξ x = ξ (⟨x.fst, 0⟩ : TwoStep V W b) * ξ (⟨0, x.snd⟩ : TwoStep V W b) := by
    rw [← map_mul, hx]
  rw [h1, TwoStep.fst_mul, xi_zero_fst hcenter ξ, add_zero]
  rfl

/-- `w ↦ (ξ ⟨0,w⟩).snd` is injective. -/
theorem xiW_injective (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) :
    Function.Injective (fun w : W => (ξ (⟨0, w⟩ : TwoStep V W b)).snd) := by
  intro u v huv
  have h : ξ (⟨0, u⟩ : TwoStep V W b) = ξ (⟨0, v⟩ : TwoStep V W b) := by
    ext
    · rw [xi_zero_fst hcenter ξ, xi_zero_fst hcenter ξ]
    · exact huv
  have h' : (⟨0, u⟩ : TwoStep V W b) = ⟨0, v⟩ := by
    simpa using congrArg (fun x => ξ⁻¹ x) h
  simpa using congrArg (fun x : TwoStep V W b => x.snd) h'

/-- `w ↦ (ξ ⟨0,w⟩).snd` is additive. -/
theorem xiW_add (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (u v : W) :
    (ξ (⟨0, u + v⟩ : TwoStep V W b)).snd =
    (ξ (⟨0, u⟩ : TwoStep V W b)).snd + (ξ (⟨0, v⟩ : TwoStep V W b)).snd := by
  have h5 : (⟨0, u⟩ : TwoStep V W b) * ⟨0, v⟩ = ⟨0, u + v⟩ := by
    ext <;> simp [TwoStep.snd_mul, Biadd.zero_left]
  have h1 : ξ ((⟨0, u⟩ : TwoStep V W b) * ⟨0, v⟩) =
      ξ (⟨0, u⟩ : TwoStep V W b) * ξ (⟨0, v⟩ : TwoStep V W b) := map_mul ξ _ _
  have h2 := congrArg (fun x : TwoStep V W b => x.snd) h1
  rw [h5, TwoStep.snd_mul] at h2
  simp only [xi_zero_fst hcenter ξ, Biadd.zero_left, add_zero] at h2
  exact h2

/-- **The automorphism of `W` induced by `ξ`** (its action on `kerFst ≅ W`). -/
def xiW (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) : W ≃+ W :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun w : W => (ξ (⟨0, w⟩ : TwoStep V W b)).snd) (xiW_add hcenter ξ))
    ⟨xiW_injective hcenter ξ, Finite.surjective_of_injective (xiW_injective hcenter ξ)⟩

/-- The defining property of `xiW`. -/
theorem xiW_apply (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (w : W) :
    xiW hcenter ξ w = (ξ (⟨0, w⟩ : TwoStep V W b)).snd := rfl

/-- `ξ ⟨0,w⟩ = ⟨0, xiW w⟩`. -/
theorem xi_apply_zero (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (w : W) :
    ξ (⟨0, w⟩ : TwoStep V W b) = ⟨0, xiW hcenter ξ w⟩ := by
  ext
  · exact xi_zero_fst hcenter ξ w
  · rfl

/-- **The action on the centre is by the induced additive map.** -/
theorem xi_snd_eq (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (x : TwoStep V W b) :
    (ξ x).snd = xiW hcenter ξ x.snd +
      (ξ (⟨x.fst, 0⟩ : TwoStep V W b)).snd := by
  have hx : (⟨x.fst, 0⟩ : TwoStep V W b) * ⟨0, x.snd⟩ = x := by
    ext <;> simp [TwoStep.fst_mul, TwoStep.snd_mul, Biadd.zero_right, Biadd.zero_left]
  have h1 : ξ x = ξ (⟨x.fst, 0⟩ : TwoStep V W b) * ξ (⟨0, x.snd⟩ : TwoStep V W b) := by
    rw [← map_mul, hx]
  rw [h1, TwoStep.snd_mul, xi_zero_fst hcenter ξ,
    show b (ξ (⟨x.fst, 0⟩ : TwoStep V W b)).fst (0 : V) = 0 from Biadd.zero_right _, add_zero,
    xiW_apply]
  abel

/-- **`ξ`-equivariance of the squaring form:** `b (xiV u) (xiV u) = xiW (b u u)`. -/
theorem xiV_quad (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (u : V) :
    b (xiV hcenter ξ u) (xiV hcenter ξ u) = xiW hcenter ξ (b u u) := by
  have h1 : (ξ (⟨u, 0⟩ : TwoStep V W b)) ^ 2 =
      (⟨0, b (xiV hcenter ξ u) (xiV hcenter ξ u)⟩ : TwoStep V W b) := by
    rw [TwoStep.sq_eq, xiV_apply]
  have h2 : (ξ (⟨u, 0⟩ : TwoStep V W b)) ^ 2 =
      (⟨0, xiW hcenter ξ (b u u)⟩ : TwoStep V W b) := by
    rw [← map_pow, TwoStep.sq_eq, xi_apply_zero]
  have h3 := congrArg (fun x : TwoStep V W b => x.snd) (h1.symm.trans h2)
  simpa using h3

/-- **`ξ`-equivariance of the polar form:** the alternating form `(u,v) ↦ b u v + b v u` is
the polar form of the squaring form `Q u = b u u`, so equivariance follows from `xiV_quad`. -/
theorem xiV_polar (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (u v : V) :
    b (xiV hcenter ξ u) (xiV hcenter ξ v) + b (xiV hcenter ξ v) (xiV hcenter ξ u) =
      xiW hcenter ξ (b u v + b v u) := by
  have h1 := xiV_quad hcenter ξ (u + v)
  have hL : b (xiV hcenter ξ (u + v)) (xiV hcenter ξ (u + v)) =
      xiW hcenter ξ (b u u) + (b (xiV hcenter ξ u) (xiV hcenter ξ v) +
        b (xiV hcenter ξ v) (xiV hcenter ξ u)) + xiW hcenter ξ (b v v) := by
    simp only [map_add, Biadd.add_left, Biadd.add_right, xiV_quad hcenter ξ u,
      xiV_quad hcenter ξ v]
    abel
  have hR : xiW hcenter ξ (b (u + v) (u + v)) =
      xiW hcenter ξ (b u u) + (xiW hcenter ξ (b u v) + xiW hcenter ξ (b v u)) +
        xiW hcenter ξ (b v v) := by
    simp only [Biadd.add_left, Biadd.add_right, map_add]
    abel
  have h4 : xiW hcenter ξ (b u u) + (b (xiV hcenter ξ u) (xiV hcenter ξ v) +
        b (xiV hcenter ξ v) (xiV hcenter ξ u)) + xiW hcenter ξ (b v v) =
      xiW hcenter ξ (b u u) + (xiW hcenter ξ (b u v) + xiW hcenter ξ (b v u)) +
        xiW hcenter ξ (b v v) := by
    rw [← hL, ← hR]
    exact h1
  have h3 : b (xiV hcenter ξ u) (xiV hcenter ξ v) +
      b (xiV hcenter ξ v) (xiV hcenter ξ u) =
      xiW hcenter ξ (b u v) + xiW hcenter ξ (b v u) :=
    add_left_cancel (add_right_cancel h4)
  exact h3.trans (map_add _ _ _).symm

end Induced

end Work.Higman
