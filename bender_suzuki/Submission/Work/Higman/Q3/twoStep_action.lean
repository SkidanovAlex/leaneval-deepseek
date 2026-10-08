/-
# The action of an automorphism of `TwoStep V W b` on the `V`-coordinates

Vocabulary used by `Work.Higman.Q3.regular_aut_exists`.

An automorphism `φ` of `P = TwoStep V W b` preserves the centre `Z(P) = kerFst ≅ W`, hence the
`fst`-coordinate of `φ x` depends only on the `fst`-coordinate of `x`; the resulting map
`vActFun φ : V → V` is additive (`vActFun_add`), compatible with composition
(`vActFun_mul`) and gives an additive equivalence `vActEquiv φ : V ≃+ V`.  An automorphism
trivial on `kerFst` preserves the squaring form `Q v = b v v` (`quad_vActEquiv`).
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.cocycle_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.Higman.Q3

variable {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
variable {b : V → V → W} [Biadd b]

/-- An automorphism of a group preserves the centre. -/
theorem mulAut_mem_center' {G : Type*} [Group G] (φ : MulAut G) {z : G}
    (hz : z ∈ Subgroup.center G) : φ z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  obtain ⟨y', rfl⟩ := φ.surjective y
  rw [← map_mul, ← map_mul, hz y']

/-- Automorphisms of `TwoStep V W b` preserve `kerFst` (which is the centre). -/
theorem mulAut_kerFst (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (φ : MulAut (TwoStep V W b)) {x : TwoStep V W b} (hx : x ∈ TwoStep.kerFst) :
    φ x ∈ TwoStep.kerFst := by
  have h1 : x ∈ Subgroup.center (TwoStep V W b) := by rwa [hcenter]
  have h2 : φ x ∈ Subgroup.center (TwoStep V W b) := mulAut_mem_center' φ h1
  rwa [hcenter] at h2

/-- The `V`-coordinate of the action of an automorphism. -/
def vActFun (φ : MulAut (TwoStep V W b)) : V → V :=
  fun v => (φ (⟨v, 0⟩ : TwoStep V W b)).fst

@[simp] theorem vActFun_apply (φ : MulAut (TwoStep V W b)) (v : V) :
    vActFun φ v = (φ (⟨v, 0⟩ : TwoStep V W b)).fst := rfl

theorem vActFun_one (v : V) : vActFun (1 : MulAut (TwoStep V W b)) v = v := rfl

/-- The `fst`-coordinate of `φ ⟨X, z⟩` does not depend on `z`. -/
theorem fst_mulAut_apply_eq (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (φ : MulAut (TwoStep V W b)) (X : V) (z : W) :
    (φ (⟨X, z⟩ : TwoStep V W b)).fst = (φ (⟨X, 0⟩ : TwoStep V W b)).fst := by
  have hsplit : (⟨X, z⟩ : TwoStep V W b) = ⟨X, 0⟩ * ⟨0, z⟩ := by
    ext <;> simp [TwoStep.fst_mul, TwoStep.snd_mul, Biadd.zero_right]
  rw [hsplit, map_mul, TwoStep.fst_mul]
  have h0 : (φ (⟨0, z⟩ : TwoStep V W b)).fst = 0 := mulAut_kerFst hcenter φ rfl
  rw [h0, add_zero]

/-- Composition of the induced actions. -/
theorem vActFun_mul (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (φ ψ : MulAut (TwoStep V W b)) (v : V) :
    vActFun (φ * ψ) v = vActFun φ (vActFun ψ v) := by
  have h1 : ψ (⟨v, 0⟩ : TwoStep V W b) = ⟨vActFun ψ v, (ψ (⟨v, 0⟩ : TwoStep V W b)).snd⟩ :=
    TwoStep.ext_iff rfl rfl
  rw [vActFun_apply, MulAut.mul_apply, h1, vActFun_apply]
  exact fst_mulAut_apply_eq hcenter φ (vActFun ψ v) (ψ (⟨v, 0⟩ : TwoStep V W b)).snd

/-- Additivity of the induced action. -/
theorem vActFun_add (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (φ : MulAut (TwoStep V W b)) (u v : V) :
    vActFun φ (u + v) = vActFun φ u + vActFun φ v := by
  have hsplit : (⟨u + v, (0 : W)⟩ : TwoStep V W b) =
      (⟨u, 0⟩ * ⟨v, 0⟩) * ⟨0, b u v⟩ := by
    ext <;> simp [TwoStep.fst_mul, TwoStep.snd_mul, Biadd.zero_right, AddExpTwo.add_self]
  have h0 : (φ (⟨0, b u v⟩ : TwoStep V W b)).fst = 0 := mulAut_kerFst hcenter φ rfl
  calc vActFun φ (u + v)
      = (φ ((⟨u, 0⟩ * ⟨v, 0⟩) * ⟨0, b u v⟩ : TwoStep V W b)).fst := by
          rw [vActFun_apply, hsplit]
    _ = (φ (⟨u, 0⟩ * ⟨v, 0⟩) * φ (⟨0, b u v⟩)).fst := by rw [map_mul]
    _ = (φ (⟨u, 0⟩ * ⟨v, 0⟩)).fst + (φ (⟨0, b u v⟩)).fst := by rw [TwoStep.fst_mul]
    _ = (φ ⟨u, 0⟩ * φ ⟨v, 0⟩).fst + 0 := by rw [map_mul, h0]
    _ = (φ ⟨u, 0⟩).fst + (φ ⟨v, 0⟩).fst := by rw [TwoStep.fst_mul, add_zero]
    _ = vActFun φ u + vActFun φ v := rfl

/-- The iterates of the induced action. -/
theorem vActFun_iterate (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (φ : MulAut (TwoStep V W b)) (k : ℕ) (v : V) :
    (vActFun φ)^[k] v = ((φ ^ k) (⟨v, 0⟩ : TwoStep V W b)).fst := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', MulAut.mul_apply]
    exact (fst_mulAut_apply_eq hcenter φ ((φ ^ k) (⟨v, 0⟩ : TwoStep V W b)).fst
      ((φ ^ k) (⟨v, 0⟩ : TwoStep V W b)).snd).symm

/-- The `V`-coordinate action of an automorphism, as an additive equivalence. -/
def vActEquiv (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (φ : MulAut (TwoStep V W b)) : V ≃+ V where
  toFun := vActFun φ
  invFun := vActFun φ⁻¹
  left_inv v := by
    have h := vActFun_mul hcenter φ⁻¹ φ v
    rw [inv_mul_cancel, vActFun_one] at h
    exact h.symm
  right_inv v := by
    have h := vActFun_mul hcenter φ φ⁻¹ v
    rw [mul_inv_cancel, vActFun_one] at h
    exact h.symm
  map_add' u v := vActFun_add hcenter φ u v

@[simp] theorem vActEquiv_apply (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (φ : MulAut (TwoStep V W b)) (v : V) :
    vActEquiv hcenter φ v = vActFun φ v := rfl

/-- An automorphism trivial on `kerFst` preserves the squaring form `Q v = b v v`. -/
theorem quad_vActEquiv (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (φ : MulAut (TwoStep V W b)) (hker : ∀ x ∈ TwoStep.kerFst, φ x = x) (v : V) :
    b (vActEquiv hcenter φ v) (vActEquiv hcenter φ v) = b v v := by
  have h1 : φ ((⟨v, 0⟩ : TwoStep V W b) ^ 2) = (φ (⟨v, 0⟩ : TwoStep V W b)) ^ 2 :=
    map_pow φ _ 2
  rw [TwoStep.sq_eq] at h1
  have h2 : φ (⟨0, b v v⟩ : TwoStep V W b) = ⟨0, b v v⟩ := hker _ rfl
  rw [h2] at h1
  have h3 := congrArg (fun x : TwoStep V W b => x.snd) h1
  rw [TwoStep.sq_eq] at h3
  simpa [vActEquiv, vActFun] using h3.symm

end Work.Higman.Q3
