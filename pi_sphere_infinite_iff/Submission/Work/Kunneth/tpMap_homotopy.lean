import Mathlib
import Submission.Work.Kunneth.EZAWTensor
import Submission.Work.Kunneth.Algebra

/-!
# Homotopy invariance of the Koszul tensor product `tpMap`

`Work.Kunneth.tpMap f g` (`Submission/Work/Kunneth/EZAWTensor.lean`) is the tensor product of
two chain maps on the Koszul tensor product `Work.Kunneth.tpC`.  This file proves that it is
compatible with chain homotopies: if `f` and `f'` are homotopic, and `g` and `g'` are homotopic,
then `tpMap f g` and `tpMap f' g'` are homotopic.

The one-sided statements are proved first: for a homotopy `Hf : Homotopy f f'` the "left"
homotopy component on the summand `(p,q)` is `s_p ⊗ g_q` (where `s_i = Hf.hom i (i+1)`), and for
a homotopy `Hg : Homotopy g g'` the "right" homotopy component on `(p,q)` is
`(-1)^p · (f'_p ⊗ t_q)`.  Both identities
`tpMapLin f g - tpMapLin f' g = ∂ ∘ h + h ∘ ∂` are verified by an explicit element computation
(the Koszul sign is what makes the "off-diagonal" summands cancel).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## The one-sided homotopy components -/

/-- The shift `(p,q) ↦ (p+1,q)` of bidegrees. -/
abbrev tpIdx₁ (n : ℕ) (pq : tpIdx n) : tpIdx (n + 1) := ⟨(pq.1.1 + 1, pq.1.2), by omega⟩

/-- The shift `(p,q) ↦ (p,q+1)` of bidegrees. -/
abbrev tpIdx₂ (n : ℕ) (pq : tpIdx n) : tpIdx (n + 1) := ⟨(pq.1.1, pq.1.2 + 1), by omega⟩

/-- The component of the "left" homotopy `Hf ⊗ g` of chain maps: on the summand `(p,q)` it is
`TensorProduct.map (s p) (g q)`, landing in the summand `(p+1,q)`. -/
def tpMapHomLLin (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (g : B ⟶ B')
    (s : ∀ i, A.X i ⟶ A'.X (i + 1)) (n : ℕ) : tpX A B n →ₗ[ℤ] tpX A' B' (n + 1) :=
  DirectSum.toModule ℤ (tpIdx n) (tpX A' B' (n + 1)) (fun pq =>
    (tpLof A' B' (n + 1) (tpIdx₁ n pq)).comp
      (TensorProduct.map (s pq.1.1).hom (g.f pq.1.2).hom))

/-- The value of `tpMapHomLLin` on a summand generator. -/
lemma tpMapHomLLin_lof (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (g : B ⟶ B')
    (s : ∀ i, A.X i ⟶ A'.X (i + 1)) (n : ℕ) (pq : tpIdx n) (z : tpSummand A B pq.1.1 pq.1.2) :
    tpMapHomLLin A A' B B' g s n (tpLof A B n pq z)
      = tpLof A' B' (n + 1) (tpIdx₁ n pq)
          ((TensorProduct.map (s pq.1.1).hom (g.f pq.1.2).hom) z) := by
  rw [tpMapHomLLin, DirectSum.toModule_lof]; rfl

/-- The value of `tpMapHomLLin` on a pure tensor of generators. -/
lemma tpMapHomLLin_tmul (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (g : B ⟶ B')
    (s : ∀ i, A.X i ⟶ A'.X (i + 1))
    (n : ℕ) (pq : tpIdx n) (x : ↥(A.X pq.1.1)) (y : ↥(B.X pq.1.2)) :
    tpMapHomLLin A A' B B' g s n (tpLof A B n pq (x ⊗ₜ[ℤ] y))
      = tpLof A' B' (n + 1) (tpIdx₁ n pq)
          ((s pq.1.1).hom x ⊗ₜ[ℤ] (g.f pq.1.2).hom y) := by
  rw [tpMapHomLLin_lof]
  simp only [TensorProduct.map_tmul]

/-- The component of the "right" homotopy `f' ⊗ Hg`: on the summand `(p,q)` it is
`(-1)^p · TensorProduct.map (f'_p) (t_q)`, landing in the summand `(p,q+1)`. -/
def tpMapHomRLin (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f' : A ⟶ A')
    (t : ∀ i, B.X i ⟶ B'.X (i + 1)) (n : ℕ) : tpX A B n →ₗ[ℤ] tpX A' B' (n + 1) :=
  DirectSum.toModule ℤ (tpIdx n) (tpX A' B' (n + 1)) (fun pq =>
    ((-1 : ℤ) ^ pq.1.1) • ((tpLof A' B' (n + 1) (tpIdx₂ n pq)).comp
      (TensorProduct.map (f'.f pq.1.1).hom (t pq.1.2).hom)))

/-- The value of `tpMapHomRLin` on a summand generator. -/
lemma tpMapHomRLin_lof (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f' : A ⟶ A')
    (t : ∀ i, B.X i ⟶ B'.X (i + 1)) (n : ℕ) (pq : tpIdx n) (z : tpSummand A B pq.1.1 pq.1.2) :
    tpMapHomRLin A A' B B' f' t n (tpLof A B n pq z)
      = (-1 : ℤ) ^ pq.1.1 • tpLof A' B' (n + 1) (tpIdx₂ n pq)
          ((TensorProduct.map (f'.f pq.1.1).hom (t pq.1.2).hom) z) := by
  rw [tpMapHomRLin, DirectSum.toModule_lof]; rfl

/-- The value of `tpMapHomRLin` on a pure tensor of generators. -/
lemma tpMapHomRLin_tmul (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f' : A ⟶ A')
    (t : ∀ i, B.X i ⟶ B'.X (i + 1))
    (n : ℕ) (pq : tpIdx n) (x : ↥(A.X pq.1.1)) (y : ↥(B.X pq.1.2)) :
    tpMapHomRLin A A' B B' f' t n (tpLof A B n pq (x ⊗ₜ[ℤ] y))
      = (-1 : ℤ) ^ pq.1.1 • tpLof A' B' (n + 1) (tpIdx₂ n pq)
          ((f'.f pq.1.1).hom x ⊗ₜ[ℤ] (t pq.1.2).hom y) := by
  rw [tpMapHomRLin_lof]
  simp only [TensorProduct.map_tmul]

/-! ## The homotopy relation in element form -/

/-- The element-level form of the chain homotopy relation `Hf : Homotopy f f'`. -/
lemma Homotopy_comm_apply' {A A' : ChainComplex (ModuleCat ℤ) ℕ} {f f' : A ⟶ A'}
    (Hf : Homotopy f f') (p : ℕ) (x : ↥(A.X p)) :
    (f.f p).hom x = (A'.d (p+1) p).hom ((Hf.hom p (p+1)).hom x)
      + (Hf.hom (p-1) p).hom ((A.d p (p-1)).hom x) + (f'.f p).hom x := by
  have h := congrArg (fun (φ : A.X p ⟶ A'.X p) => ModuleCat.Hom.hom φ x) (Hf.comm p)
  rw [ModuleCat.hom_add, ModuleCat.hom_add, LinearMap.add_apply, LinearMap.add_apply] at h
  rw [prevD_eq Hf.hom (show (ComplexShape.down ℕ).Rel (p+1) p from rfl),
      dNext_nat A A' p Hf.hom] at h
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [h]; abel

/-- The element-level form of the chain homotopy relation `Hf : Homotopy f f'` in degree `0`. -/
lemma Homotopy_comm_apply_zero {A A' : ChainComplex (ModuleCat ℤ) ℕ} {f f' : A ⟶ A'}
    (Hf : Homotopy f f') (x : ↥(A.X 0)) :
    (f.f 0).hom x = (A'.d 1 0).hom ((Hf.hom 0 1).hom x) + (f'.f 0).hom x := by
  have h := Homotopy_comm_apply' Hf 0 x
  have hz : Hf.hom (0-1) 0 = 0 := by
    rw [show (0-1 : ℕ) = 0 from rfl]
    exact Hf.zero 0 0 (by decide)
  rw [hz] at h
  simpa using h

/-! ## The left identity -/

/-- **The tensor product with a fixed map respects homotopies in the first variable**:
at every positive degree, `tpMapLin f g - tpMapLin f' g` is the homotopy boundary of the
left homotopy component `tpMapHomLLin`. -/
theorem left_succ (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f f' : A ⟶ A') (g : B ⟶ B')
    (Hf : Homotopy f f') (k : ℕ) :
    tpMapLin A A' B B' f g (k+1) - tpMapLin A A' B B' f' g (k+1)
      = (tpD A' B' (k+1)).comp (tpMapHomLLin A A' B B' g (fun i => Hf.hom i (i+1)) (k+1))
        + (tpMapHomLLin A A' B B' g (fun i => Hf.hom i (i+1)) k).comp (tpD A B k) := by
  apply DirectSum.linearMap_ext ℤ
  intro pq
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply]
  rw [tpMapLin_tmul, tpMapLin_tmul]
  rw [tpMapHomLLin_tmul]
  rw [tpD_lof_tmul]
  rw [tpD_lof_tmul]
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  simp only [Subtype.coe_mk, tpIdx₁]
  simp only [LinearMap.map_add]
  rw [apply_dite (tpMapHomLLin A A' B B' g (fun i => Hf.hom i (i+1)) k) (1 ≤ p),
      apply_dite (tpMapHomLLin A A' B B' g (fun i => Hf.hom i (i+1)) k) (1 ≤ q)]
  simp only [map_zero]
  split_ifs with hp1 hq hp hqq
  · -- `1 ≤ p`, `1 ≤ q`
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [tpMapHomLLin_tmul, map_zsmul, tpMapHomLLin_tmul]
    rw [Hom_comm_apply g (q'+1) (q'+1-1) y]
    rw [Homotopy_comm_apply' Hf (p'+1) x]
    iterate 2 rw [TensorProduct.add_tmul]
    iterate 2 rw [LinearMap.map_add]
    rw [add_sub_cancel_right, add_add_add_comm, ← add_zsmul]
    rw [show (-1 : ℤ) ^ (p' + 1 + 1) + (-1) ^ (p' + 1) = 0 from by rw [pow_succ]; ring]
    rw [zero_zsmul, add_zero]
    rfl
  · -- `1 ≤ p + 1`, `1 ≤ q`, `¬ 1 ≤ p` (so `p = 0`)
    rw [zero_add, add_assoc]
    obtain rfl : p = 0 := by omega
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [map_zsmul, tpMapHomLLin_tmul]
    rw [Hom_comm_apply g (q'+1) (q'+1-1) y]
    rw [Homotopy_comm_apply_zero Hf x]
    rw [TensorProduct.add_tmul, LinearMap.map_add, add_sub_cancel_right]
    rw [← add_zsmul]
    try rw [show (-1 : ℤ) ^ (0 + 1) + (-1) ^ 0 = 0 from by norm_num]
    try rw [zero_zsmul, add_zero]
    try rfl
  · -- `1 ≤ p + 1`, `¬ 1 ≤ q` (so `q = 0`), `1 ≤ p`
    simp only [add_zero]
    obtain rfl : q = 0 := by omega
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [tpMapHomLLin_tmul]
    rw [Homotopy_comm_apply' Hf (p'+1) x]
    iterate 2 rw [TensorProduct.add_tmul]
    iterate 2 rw [LinearMap.map_add]
    rw [add_sub_cancel_right]
    rfl
  · -- `p = 0`, `q = 0`
    obtain rfl : p = 0 := by omega
    obtain rfl : q = 0 := by omega
    rw [Homotopy_comm_apply_zero Hf x]
    rw [TensorProduct.add_tmul, LinearMap.map_add, add_sub_cancel_right]
    simp only [add_zero]
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

/-- The left identity in degree `0`, where the source differential term vanishes. -/
theorem left_zero (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f f' : A ⟶ A') (g : B ⟶ B')
    (Hf : Homotopy f f') :
    tpMapLin A A' B B' f g 0 - tpMapLin A A' B B' f' g 0
      = (tpD A' B' 0).comp (tpMapHomLLin A A' B B' g (fun i => Hf.hom i (i+1)) 0) := by
  apply DirectSum.linearMap_ext ℤ
  intro pq
  apply TensorProduct.ext'
  intro x y
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  have hp : p = 0 := by omega
  have hq : q = 0 := by omega
  subst hp
  subst hq
  simp only [LinearMap.sub_apply, LinearMap.comp_apply]
  rw [tpMapLin_tmul, tpMapLin_tmul]
  rw [tpMapHomLLin_tmul]
  rw [tpD_lof_tmul]
  show _ = (if hp : 1 ≤ (0 + 1) then _ else 0) + (if hq : 1 ≤ (0 : ℕ) then _ else 0)
  rw [dif_pos (by decide : 1 ≤ (0 + 1)), dif_neg (by decide : ¬ 1 ≤ (0 : ℕ)), add_zero]
  simp only [Subtype.coe_mk]
  rw [Homotopy_comm_apply_zero Hf x]
  rw [TensorProduct.add_tmul, LinearMap.map_add, add_sub_cancel_right]
  try rfl

/-! ## The right identity -/

/-- The sign identity `(-1)^p * (-1)^p = 1`. -/
private lemma neg_one_pow_mul_self (p : ℕ) : (-1 : ℤ) ^ p * (-1) ^ p = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- The double sign `(-1)^p • ((-1)^p • X) = X`. -/
private lemma neg_one_pow_smul_self {M : Type*} [AddCommGroup M] (p : ℕ) (X : M) :
    (-1 : ℤ) ^ p • ((-1 : ℤ) ^ p • X) = X := by
  rw [← mul_zsmul, neg_one_pow_mul_self p, one_zsmul]

/-- **The tensor product with a fixed map respects homotopies in the second variable**:
at every positive degree, `tpMapLin f' g - tpMapLin f' g'` is the homotopy boundary of the
right homotopy component `tpMapHomRLin`. -/
theorem right_succ (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f' : A ⟶ A') (g g' : B ⟶ B')
    (Hg : Homotopy g g') (k : ℕ) :
    tpMapLin A A' B B' f' g (k+1) - tpMapLin A A' B B' f' g' (k+1)
      = (tpD A' B' (k+1)).comp (tpMapHomRLin A A' B B' f' (fun i => Hg.hom i (i+1)) (k+1))
        + (tpMapHomRLin A A' B B' f' (fun i => Hg.hom i (i+1)) k).comp (tpD A B k) := by
  apply DirectSum.linearMap_ext ℤ
  intro pq
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply]
  rw [tpMapLin_tmul, tpMapLin_tmul]
  rw [tpMapHomRLin_tmul]
  rw [map_zsmul]
  rw [tpD_lof_tmul]
  rw [tpD_lof_tmul]
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  simp only [Subtype.coe_mk, tpIdx₂]
  simp only [zsmul_add]
  simp only [LinearMap.map_add]
  rw [apply_dite (tpMapHomRLin A A' B B' f' (fun i => Hg.hom i (i+1)) k) (1 ≤ p),
      apply_dite (tpMapHomRLin A A' B B' f' (fun i => Hg.hom i (i+1)) k) (1 ≤ q)]
  simp only [map_zero]
  split_ifs with hp1 hq hp hqq
  · -- `1 ≤ p`, `1 ≤ q`
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [tpMapHomRLin_tmul, map_zsmul, tpMapHomRLin_tmul]
    rw [Hom_comm_apply f' (p'+1) (p'+1-1) x]
    rw [Homotopy_comm_apply' Hg (q'+1) y]
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
    rw [LinearMap.map_add, LinearMap.map_add]
    rw [add_sub_cancel_right]
    rw [neg_one_pow_smul_self, neg_one_pow_smul_self]
    rw [add_add_add_comm, ← add_zsmul]
    rw [show (-1 : ℤ) ^ (p'+1) + (-1) ^ (p'+1-1) = 0 from by
      rw [show (p'+1-1 : ℕ) = p' from rfl, pow_succ]; ring]
    rw [zero_zsmul, zero_add]
    try rfl
  · -- `1 ≤ p`, `q = 0`
    obtain rfl : q = 0 := by omega
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [tpMapHomRLin_tmul]
    rw [Hom_comm_apply f' (p'+1) (p'+1-1) x]
    rw [Homotopy_comm_apply_zero Hg y]
    rw [TensorProduct.tmul_add, LinearMap.map_add, add_sub_cancel_right]
    rw [neg_one_pow_smul_self]
    simp only [Subtype.coe_mk]
    rw [add_zero, add_right_comm, ← add_zsmul]
    rw [show (-1 : ℤ) ^ (p'+1) + (-1) ^ (p'+1-1) = 0 from by
      rw [show (p'+1-1 : ℕ) = p' from rfl, pow_succ]; ring]
    rw [zero_zsmul, zero_add]
    try rfl
  · exfalso; omega
  · exfalso; omega
  · -- `p = 0`, `1 ≤ q`
    obtain rfl : p = 0 := by omega
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [map_zsmul, tpMapHomRLin_tmul]
    rw [Homotopy_comm_apply' Hg (q'+1) y]
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
    rw [LinearMap.map_add, LinearMap.map_add]
    rw [add_sub_cancel_right]
    simp only [pow_zero, one_zsmul, zero_zsmul, zero_add, add_zero]
    try rfl
  · -- `p = 0`, `q = 0`
    obtain rfl : p = 0 := by omega
    obtain rfl : q = 0 := by omega
    rw [Homotopy_comm_apply_zero Hg y]
    rw [TensorProduct.tmul_add, LinearMap.map_add, add_sub_cancel_right]
    simp only [pow_zero, one_zsmul, zero_zsmul, zero_add, add_zero]
  · exfalso; omega
  · exfalso; omega

/-- The right identity in degree `0`. -/
theorem right_zero (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f' : A ⟶ A') (g g' : B ⟶ B')
    (Hg : Homotopy g g') :
    tpMapLin A A' B B' f' g 0 - tpMapLin A A' B B' f' g' 0
      = (tpD A' B' 0).comp (tpMapHomRLin A A' B B' f' (fun i => Hg.hom i (i+1)) 0) := by
  apply DirectSum.linearMap_ext ℤ
  intro pq
  apply TensorProduct.ext'
  intro x y
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  have hp : p = 0 := by omega
  have hq : q = 0 := by omega
  subst hp
  subst hq
  simp only [LinearMap.sub_apply, LinearMap.comp_apply]
  rw [tpMapLin_tmul, tpMapLin_tmul]
  rw [tpMapHomRLin_tmul]
  rw [map_zsmul]
  rw [tpD_lof_tmul]
  rw [zsmul_add]
  simp only [pow_zero, one_zsmul]
  split_ifs with h1 h2
  · exfalso; omega
  · exfalso; omega
  · rw [zero_add]
    rw [Homotopy_comm_apply_zero Hg y]
    rw [TensorProduct.tmul_add, LinearMap.map_add, add_sub_cancel_right]
    try rfl
  · exfalso; omega

/-! ## Assembling the chain homotopies -/

/-- The family of components of the left homotopy, as a family of morphisms of `ℤ`-modules. -/
def leftHom (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (g : B ⟶ B')
    (s : ∀ i, A.X i ⟶ A'.X (i + 1)) : ∀ i j, (tpC A B).X i ⟶ (tpC A' B').X j :=
  fun i j => dite (j = i + 1)
    (fun h => h ▸ ModuleCat.ofHom (tpMapHomLLin A A' B B' g s i)) (fun _ => 0)

lemma leftHom_succ (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (g : B ⟶ B')
    (s : ∀ i, A.X i ⟶ A'.X (i + 1)) (i : ℕ) :
    leftHom A A' B B' g s i (i + 1) = ModuleCat.ofHom (tpMapHomLLin A A' B B' g s i) := by
  rw [leftHom, dif_pos rfl]

lemma leftHom_ne (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (g : B ⟶ B')
    (s : ∀ i, A.X i ⟶ A'.X (i + 1)) {i j : ℕ} (h : ¬ (j = i + 1)) :
    leftHom A A' B B' g s i j = 0 := by
  rw [leftHom, dif_neg h]

/-- The chain map `nullHomotopicMap` of the left homotopy components is `tpMap f g - tpMap f' g`. -/
theorem left_null (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f f' : A ⟶ A') (g : B ⟶ B')
    (Hf : Homotopy f f') :
    Homotopy.nullHomotopicMap (leftHom A A' B B' g (fun i => Hf.hom i (i+1)))
      = tpMap A A' B B' f g - tpMap A A' B B' f' g := by
  apply HomologicalComplex.Hom.ext
  funext i
  rcases i with _ | k
  · rw [Homotopy.nullHomotopicMap_f_of_not_rel_left (show (ComplexShape.down ℕ).Rel 1 0 from rfl)
        (by intro l; exact Nat.succ_ne_zero l), leftHom_succ, tpC_d]
    apply ModuleCat.hom_ext
    change (tpD A' B' 0).comp (tpMapHomLLin A A' B B' g (fun i => Hf.hom i (i+1)) 0)
      = tpMapLin A A' B B' f g 0 - tpMapLin A A' B B' f' g 0
    exact (left_zero A A' B B' f f' g Hf).symm
  · rw [Homotopy.nullHomotopicMap_f (show (ComplexShape.down ℕ).Rel (k+2) (k+1) from rfl)
        (show (ComplexShape.down ℕ).Rel (k+1) k from rfl), leftHom_succ, leftHom_succ, tpC_d, tpC_d]
    apply ModuleCat.hom_ext
    change (tpMapHomLLin A A' B B' g (fun i => Hf.hom i (i+1)) k).comp (tpD A B k)
        + (tpD A' B' (k+1)).comp (tpMapHomLLin A A' B B' g (fun i => Hf.hom i (i+1)) (k+1))
      = tpMapLin A A' B B' f g (k+1) - tpMapLin A A' B B' f' g (k+1)
    exact (add_comm _ _).trans (left_succ A A' B B' f f' g Hf k).symm

/-- **The first-variable homotopy**: homotopic maps induce homotopic tensor products. -/
noncomputable def left_homotopy (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f f' : A ⟶ A') (g : B ⟶ B')
    (Hf : Homotopy f f') : Homotopy (tpMap A A' B B' f g) (tpMap A A' B B' f' g) :=
  (Homotopy.equivSubZero).symm
    ((Homotopy.ofEq (left_null A A' B B' f f' g Hf).symm).trans
      (Homotopy.nullHomotopy (leftHom A A' B B' g (fun i => Hf.hom i (i+1))) (by
        intro i j h
        exact leftHom_ne A A' B B' g (fun i => Hf.hom i (i+1)) (fun e => h e.symm))))

/-- The family of components of the right homotopy, as a family of morphisms of `ℤ`-modules. -/
def rightHom (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f' : A ⟶ A')
    (t : ∀ i, B.X i ⟶ B'.X (i + 1)) : ∀ i j, (tpC A B).X i ⟶ (tpC A' B').X j :=
  fun i j => dite (j = i + 1)
    (fun h => h ▸ ModuleCat.ofHom (tpMapHomRLin A A' B B' f' t i)) (fun _ => 0)

lemma rightHom_succ (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f' : A ⟶ A')
    (t : ∀ i, B.X i ⟶ B'.X (i + 1)) (i : ℕ) :
    rightHom A A' B B' f' t i (i + 1) = ModuleCat.ofHom (tpMapHomRLin A A' B B' f' t i) := by
  rw [rightHom, dif_pos rfl]

lemma rightHom_ne (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f' : A ⟶ A')
    (t : ∀ i, B.X i ⟶ B'.X (i + 1)) {i j : ℕ} (h : ¬ (j = i + 1)) :
    rightHom A A' B B' f' t i j = 0 := by
  rw [rightHom, dif_neg h]

/-- The chain map `nullHomotopicMap` of the right homotopy components is `tpMap f' g - tpMap f' g'`. -/
theorem right_null (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f' : A ⟶ A') (g g' : B ⟶ B')
    (Hg : Homotopy g g') :
    Homotopy.nullHomotopicMap (rightHom A A' B B' f' (fun i => Hg.hom i (i+1)))
      = tpMap A A' B B' f' g - tpMap A A' B B' f' g' := by
  apply HomologicalComplex.Hom.ext
  funext i
  rcases i with _ | k
  · rw [Homotopy.nullHomotopicMap_f_of_not_rel_left (show (ComplexShape.down ℕ).Rel 1 0 from rfl)
        (by intro l; exact Nat.succ_ne_zero l), rightHom_succ, tpC_d]
    apply ModuleCat.hom_ext
    change (tpD A' B' 0).comp (tpMapHomRLin A A' B B' f' (fun i => Hg.hom i (i+1)) 0)
      = tpMapLin A A' B B' f' g 0 - tpMapLin A A' B B' f' g' 0
    exact (right_zero A A' B B' f' g g' Hg).symm
  · rw [Homotopy.nullHomotopicMap_f (show (ComplexShape.down ℕ).Rel (k+2) (k+1) from rfl)
        (show (ComplexShape.down ℕ).Rel (k+1) k from rfl), rightHom_succ, rightHom_succ, tpC_d, tpC_d]
    apply ModuleCat.hom_ext
    change (tpMapHomRLin A A' B B' f' (fun i => Hg.hom i (i+1)) k).comp (tpD A B k)
        + (tpD A' B' (k+1)).comp (tpMapHomRLin A A' B B' f' (fun i => Hg.hom i (i+1)) (k+1))
      = tpMapLin A A' B B' f' g (k+1) - tpMapLin A A' B B' f' g' (k+1)
    exact (add_comm _ _).trans (right_succ A A' B B' f' g g' Hg k).symm

/-- **The second-variable homotopy**: homotopic maps induce homotopic tensor products. -/
noncomputable def right_homotopy (A A' B B' : ChainComplex (ModuleCat ℤ) ℕ) (f' : A ⟶ A') (g g' : B ⟶ B')
    (Hg : Homotopy g g') : Homotopy (tpMap A A' B B' f' g) (tpMap A A' B B' f' g') :=
  (Homotopy.equivSubZero).symm
    ((Homotopy.ofEq (right_null A A' B B' f' g g' Hg).symm).trans
      (Homotopy.nullHomotopy (rightHom A A' B B' f' (fun i => Hg.hom i (i+1))) (by
        intro i j h
        exact rightHom_ne A A' B B' f' (fun i => Hg.hom i (i+1)) (fun e => h e.symm))))

/-- **Milnor's `tpMap`, i.e. the Koszul tensor product of chain maps, is homotopy invariant.** -/
theorem tpMap_homotopy (C C' D D' : ChainComplex (ModuleCat ℤ) ℕ) (f f' : Work.Kunneth.chHom C C')
    (g g' : Work.Kunneth.chHom D D') (Hf : Homotopy f f') (Hg : Homotopy g g') :
    Nonempty (Homotopy (Work.Kunneth.tpMap C C' D D' f g)
      (Work.Kunneth.tpMap C C' D D' f' g')) :=
  ⟨(left_homotopy C C' D D' f f' g Hf).trans (right_homotopy C C' D D' f' g g' Hg)⟩

end

end Work.Kunneth
