import Mathlib
import Submission.Work.SymQuot.NormPoint.Basic
import Submission.Work.SymQuot.NormPoint.detT_eq_zero_of_swap_fixed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open TensorProduct
open scoped TensorProduct

universe u

namespace Work.SymQuot.NormPoint

variable {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q] {n : ℕ}

/-- **Expansion of an alternating form in a basis.**  For an alternating `n`-form `Ψ` on `Q` and
a basis `v` of `Q`, the value of `Ψ` at `f : Fin n → Q` is the sum over all `p : Fin n → Fin n`
of the product of the coordinates of `f` times `Ψ` evaluated on the basis vectors selected by
`p`.  This is the multilinear expansion of `Ψ` in the basis `v`. -/
lemma detT_mul_aux_expand (v : Module.Basis (Fin n) F Q) (Ψ : Q [⋀^Fin n]→ₗ[F] F)
    (f : Fin n → Q) :
    Ψ f = ∑ p : Fin n → Fin n, (∏ i, (v.repr (f i)) (p i)) • Ψ (fun i => v (p i)) := by
  conv_lhs =>
    rw [show f = fun i => ∑ j, (v.repr (f i)) j • v j from by
      funext i; exact (v.sum_repr (f i)).symm]
  change (Ψ : MultilinearMap F (fun _ : Fin n => Q) F)
      (fun i => ∑ j, (v.repr (f i)) j • v j)
    = ∑ p : Fin n → Fin n, (∏ i, (v.repr (f i)) (p i)) • Ψ (fun i => v (p i))
  rw [MultilinearMap.map_sum (Ψ : MultilinearMap F (fun _ : Fin n => Q) F)
        (fun i j => (v.repr (f i)) j • v j)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [MultilinearMap.map_smul_univ (Ψ : MultilinearMap F (fun _ : Fin n => Q) F)
        (fun i => (v.repr (f i)) (p i)) (fun i => v (p i))]
  rfl

/-- An alternating `n`-form on `Q` (free of rank `n`) vanishing at the tuple of basis vectors is
zero: expanding any tuple `f` in the basis `v` reduces to the values at basis tuples, which
either vanish (useless index) or are `±` the value at `v` itself. -/
lemma detT_mul_aux_eq_zero_of_apply_basis (v : Module.Basis (Fin n) F Q)
    (Θ : Q [⋀^Fin n]→ₗ[F] F) (h : Θ (⇑v) = 0) : Θ = 0 := by
  ext f
  rw [detT_mul_aux_expand v Θ f]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hp : Function.Injective p
  · obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), ⇑σ = p :=
      ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.mp hp), Equiv.coe_ofBijective p _⟩
    rw [show (fun i => v (p i)) = (⇑v) ∘ ⇑σ from by rw [hσ]; rfl]
    simp [AlternatingMap.map_perm, h]
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hp
    rw [AlternatingMap.map_eq_zero_of_eq Θ (fun k => v (p k)) (by rw [hij]) hne, smul_zero]

/-- **The top alternating forms on `Q` are one dimensional** and `v.det` is a basis: any
alternating `n`-form `Ψ` on the free module `Q` of rank `n` equals `Ψ v • v.det`. -/
lemma detT_mul_aux_eq_smul_det (v : Module.Basis (Fin n) F Q) (Ψ : Q [⋀^Fin n]→ₗ[F] F) :
    Ψ = Ψ (⇑v) • v.det := by
  have hv : (Ψ - Ψ (⇑v) • v.det) (⇑v) = 0 := by
    simp only [AlternatingMap.sub_apply, AlternatingMap.smul_apply, v.det_self, smul_eq_mul,
      mul_one, sub_self]
  exact sub_eq_zero.mp (detT_mul_aux_eq_zero_of_apply_basis v _ hv)

/-- The alternating `n`-form `f ↦ detT v (t * tprod f)`, for a symmetric tensor `t`.  It is
alternating because `t` is invariant under permutations of the tensor factors while `detT v`
changes by the sign of the permutation. -/
noncomputable def detT_mul_aux_PhiT (v : Module.Basis (Fin n) F Q) (t : Tens F Q n)
    (ht : t ∈ symTensors F Q n) : Q [⋀^Fin n]→ₗ[F] F where
  toMultilinearMap := (detT v).compMultilinearMap
      ((LinearMap.mulLeft F t).compMultilinearMap (PiTensorProduct.tprod F))
  map_eq_zero_of_eq' := by
    intro f i j hfij hne
    change detT v (t * PiTensorProduct.tprod F f) = 0
    apply detT_eq_zero_of_swap_fixed v hne
    rw [map_mul, (mem_symTensors.mp ht) (Equiv.swap i j), permAlg_tprod]
    simp only [Equiv.symm_swap]
    have hfun : (fun k => f (Equiv.swap i j k)) = f := by
      funext k
      by_cases hki : k = i
      · rw [hki, Equiv.swap_apply_left, hfij]
      · by_cases hkj : k = j
        · rw [hkj, Equiv.swap_apply_right, hfij]
        · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [hfun]

theorem detT_mul {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q] {n : ℕ}
    (v : Module.Basis (Fin n) F Q) {t : Tens F Q n} (ht : t ∈ symTensors F Q n)
    (w : Tens F Q n) : detT v (t * w) = normVal v t * detT v w := by
  obtain hΦ := detT_mul_aux_eq_smul_det v (detT_mul_aux_PhiT v t ht)
  have hc : (detT_mul_aux_PhiT v t ht) (⇑v) = normVal v t := by
    change detT v (t * PiTensorProduct.tprod F ⇑v) = detT v (t * PiTensorProduct.tprod F v)
    rfl
  have hpoint : ∀ f : Fin n → Q,
      detT v (t * PiTensorProduct.tprod F f) = normVal v t * v.det f := by
    intro f
    change (detT_mul_aux_PhiT v t ht) f = normVal v t * v.det f
    have h0 := DFunLike.congr_fun hΦ f
    rw [AlternatingMap.smul_apply] at h0
    rw [h0, hc, smul_eq_mul]
  let ψ₁ : Tens F Q n →ₗ[F] F := (detT v).comp (LinearMap.mulLeft F t)
  let ψ₂ : Tens F Q n →ₗ[F] F := (normVal v t) • detT v
  have hψ : ψ₁ = ψ₂ := by
    apply PiTensorProduct.ext
    ext f
    simp only [LinearMap.compMultilinearMap_apply]
    change detT v (t * PiTensorProduct.tprod F f) = normVal v t • detT v (PiTensorProduct.tprod F f)
    rw [hpoint f, detT_tprod, smul_eq_mul]
  have hw := DFunLike.congr_fun hψ w
  simpa [ψ₁, ψ₂, LinearMap.comp_apply, smul_eq_mul] using hw

end Work.SymQuot.NormPoint
