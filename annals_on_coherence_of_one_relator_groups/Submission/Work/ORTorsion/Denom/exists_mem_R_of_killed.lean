import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Denom

-- The proof should use the `denom` field of `LaurentBase` (common right denominators),
-- the fact that every element of a tensor product is a finite sum of pure tensors
-- (`TensorProduct.exists_sum_tmul_eq`, or induction on the tensor product),
-- flatness of `V` over the field `K` (`TensorProduct.map_injective_of_flat_flat`),
-- and the commutation of the diagonal action with right multiplication by an element of `D(H)`.
open scoped TensorProduct
open Work.ORTorsion
open Work.ORTorsion.LaurentBase

/-- Naturality of the diagonal action with respect to a `K`-algebra map `F : M →ₐ[K] M'`
compatible with the structure maps `jM`, `jM'`: tensoring on the second factor with `F` is
`K[H]`-linear for the diagonal actions. -/
theorem diagRingHom_map_natural {K : Type*} [Field K] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module K V] [Module (MonoidAlgebra K G) V]
    [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] {M M' : Type*} [Ring M] [Algebra K M] [Ring M'] [Algebra K M']
    (jG : H →* G) (jM : H →* M) (jM' : H →* M') (F : M →ₐ[K] M')
    (hF : ∀ h : H, F (jM h) = jM' h) (x : MonoidAlgebra K H) :
    ∀ z : V ⊗[K] M,
    TensorProduct.map (LinearMap.id : V →ₗ[K] V) F.toLinearMap (diagRingHom (V := V) jG jM x z)
      = diagRingHom (V := V) jG jM' x (TensorProduct.map (LinearMap.id : V →ₗ[K] V) F.toLinearMap z) := by
  induction x using MonoidAlgebra.induction_on with
  | of h =>
    intro z
    rw [MonoidAlgebra.of_apply, diagRingHom_single, diagRingHom_single]
    show TensorProduct.map (LinearMap.id : V →ₗ[K] V) F.toLinearMap
        (diagElem jG jM h z) = diagElem jG jM' h (TensorProduct.map (LinearMap.id : V →ₗ[K] V) F.toLinearMap z)
    simp only [diagElem]
    have hmul : F.toLinearMap.comp (LinearMap.mulLeft K (jM h))
        = (LinearMap.mulLeft K (jM' h)).comp F.toLinearMap := by
      ext y; simp [map_mul, hF]
    have hmap : (TensorProduct.map (LinearMap.id : V →ₗ[K] V) F.toLinearMap).comp
        (TensorProduct.map (gAct (K := K) (jG h)) (LinearMap.mulLeft K (jM h)))
        = (TensorProduct.map (gAct (K := K) (jG h)) (LinearMap.mulLeft K (jM' h))).comp
          (TensorProduct.map (LinearMap.id : V →ₗ[K] V) F.toLinearMap) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hmul,
        LinearMap.id_comp, LinearMap.comp_id]
    exact LinearMap.congr_fun hmap z
  | add x y hx hy =>
    intro z
    simp only [map_add, LinearMap.add_apply]
    rw [hx z, hy z]
  | smul r x hx =>
    intro z
    have hlin : diagRingHom (V := V) jG jM (r • x) = r • diagRingHom (V := V) jG jM x := by
      change (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) H (diagGroupHom jG jM)) (r • x)
          = r • (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) H (diagGroupHom jG jM)) x
      rw [map_smul]
    have hlin' : diagRingHom (V := V) jG jM' (r • x) = r • diagRingHom (V := V) jG jM' x := by
      change (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M')) H (diagGroupHom jG jM')) (r • x)
          = r • (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M')) H (diagGroupHom jG jM')) x
      rw [map_smul]
    rw [hlin, hlin', LinearMap.smul_apply, map_smul, hx z, LinearMap.smul_apply]

/-- Right multiplication by a fixed element `a` of the coefficient ring commutes with the
diagonal action. -/
theorem diagRingHom_mulRight {K : Type*} [Field K] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module K V] [Module (MonoidAlgebra K G) V]
    [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] {M : Type*} [Ring M] [Algebra K M]
    (jG : H →* G) (jM : H →* M) (a : M) (x : MonoidAlgebra K H) :
    ∀ z : V ⊗[K] M,
      diagRingHom (V := V) jG jM x (TensorProduct.map (LinearMap.id : V →ₗ[K] V) (LinearMap.mulRight K a) z)
        = TensorProduct.map (LinearMap.id : V →ₗ[K] V) (LinearMap.mulRight K a) (diagRingHom (V := V) jG jM x z) := by
  induction x using MonoidAlgebra.induction_on with
  | of h =>
    intro z
    rw [MonoidAlgebra.of_apply, diagRingHom_single]
    show diagElem jG jM h (TensorProduct.map LinearMap.id (LinearMap.mulRight K a) z)
        = TensorProduct.map LinearMap.id (LinearMap.mulRight K a) (diagElem jG jM h z)
    simp only [diagElem]
    have hmul : (LinearMap.mulLeft K (jM h)).comp (LinearMap.mulRight K a)
        = (LinearMap.mulRight K a).comp (LinearMap.mulLeft K (jM h)) := by
      ext y; simp [mul_assoc]
    have hmap : (TensorProduct.map (gAct (K := K) (jG h)) (LinearMap.mulLeft K (jM h))).comp
        (TensorProduct.map (LinearMap.id : V →ₗ[K] V) (LinearMap.mulRight K a))
        = (TensorProduct.map (LinearMap.id : V →ₗ[K] V) (LinearMap.mulRight K a)).comp
          (TensorProduct.map (gAct (K := K) (jG h)) (LinearMap.mulLeft K (jM h))) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hmul,
        LinearMap.id_comp, LinearMap.comp_id]
    exact LinearMap.congr_fun hmap z
  | add x y hx hy =>
    intro z
    simp only [map_add, LinearMap.add_apply]
    rw [hx z, hy z]
  | smul r x hx =>
    intro z
    have hlin : diagRingHom (V := V) jG jM (r • x) = r • diagRingHom (V := V) jG jM x := by
      change (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) H (diagGroupHom jG jM)) (r • x)
          = r • (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) H (diagGroupHom jG jM)) x
      rw [map_smul]
    rw [hlin, LinearMap.smul_apply, hx z, LinearMap.smul_apply, map_smul]

theorem exists_mem_R_of_killed {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (x : MonoidAlgebra K H) (m : V ⊗[K] ↥(L.D H)) (hm : m ≠ 0) (hxm : x • m = 0) :
    ∃ m₂ : V ⊗[K] ↥Lb.R, m₂ ≠ 0 ∧ x • m₂ = 0 := by
  -- `m` is a finite sum of pure tensors.
  obtain ⟨n, v, e, hdec⟩ := TensorProduct.exists_sum_tmul_eq m
  -- a common right denominator `t` for the second components, which is a unit of `D(H)`
  -- and satisfies `e i * t ∈ R`.
  obtain ⟨t, _ht_ne, ht_unit, hmem⟩ := Lb.denom n e
  let y : Fin n → ↥Lb.R := fun i => ⟨(((e i) * t : ↥(L.D H)) : U), hmem i⟩
  let m₂ : V ⊗[K] ↥Lb.R := ∑ i, v i ⊗ₜ[K] y i
  -- the inclusion `V ⊗ R → V ⊗ D(H)` is injective
  have hinj : Function.Injective
      (TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Subalgebra.inclusion Lb.R_le_DH).toLinearMap) :=
    TensorProduct.map_injective_of_flat_flat (LinearMap.id)
      (Subalgebra.inclusion Lb.R_le_DH).toLinearMap Function.injective_id
      (Subalgebra.inclusion_injective Lb.R_le_DH)
  have hF : ∀ h : H, Subalgebra.inclusion Lb.R_le_DH (Lb.genR h) = L.genD H h :=
    fun h => Subtype.ext rfl
  -- `m₂` maps to `m * t`
  have hincL : TensorProduct.map (LinearMap.id : V →ₗ[K] V)
        (Subalgebra.inclusion Lb.R_le_DH).toLinearMap m₂
      = ∑ i, v i ⊗ₜ[K] (e i * t) := by
    dsimp only [m₂]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [show (Subalgebra.inclusion Lb.R_le_DH).toLinearMap (y i) = e i * t from Subtype.ext rfl]
  have hMulTs : TensorProduct.map (LinearMap.id : V →ₗ[K] V) (LinearMap.mulRight K t) m
      = ∑ i, v i ⊗ₜ[K] (e i * t) := by
    rw [hdec, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mulRight_apply]
  have hinc : TensorProduct.map (LinearMap.id : V →ₗ[K] V)
        (Subalgebra.inclusion Lb.R_le_DH).toLinearMap m₂
      = TensorProduct.map (LinearMap.id : V →ₗ[K] V) (LinearMap.mulRight K t) m :=
    hincL.trans hMulTs.symm
  -- right multiplication by the unit `t` is injective
  have hMulT_inj : Function.Injective
      (TensorProduct.map (LinearMap.id : V →ₗ[K] V) (LinearMap.mulRight K t)) := by
    have hmr : (LinearMap.mulRight K ((ht_unit.unit⁻¹ : (↥(L.D H))ˣ) : ↥(L.D H))).comp
        (LinearMap.mulRight K t) = LinearMap.id := by
      ext z
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.id_apply]
      rw [mul_assoc, IsUnit.mul_val_inv ht_unit, mul_one]
    have hleft : (TensorProduct.map (LinearMap.id : V →ₗ[K] V)
          (LinearMap.mulRight K ((ht_unit.unit⁻¹ : (↥(L.D H))ˣ) : ↥(L.D H)))).comp
        (TensorProduct.map (LinearMap.id : V →ₗ[K] V) (LinearMap.mulRight K t)) = LinearMap.id := by
      rw [← TensorProduct.map_comp, hmr, LinearMap.id_comp, TensorProduct.map_id]
    intro a b hab
    have h2 : (TensorProduct.map (LinearMap.id : V →ₗ[K] V)
          (LinearMap.mulRight K ((ht_unit.unit⁻¹ : (↥(L.D H))ˣ) : ↥(L.D H))))
          ((TensorProduct.map (LinearMap.id : V →ₗ[K] V) (LinearMap.mulRight K t)) a)
        = (TensorProduct.map (LinearMap.id : V →ₗ[K] V)
          (LinearMap.mulRight K ((ht_unit.unit⁻¹ : (↥(L.D H))ˣ) : ↥(L.D H))))
          ((TensorProduct.map (LinearMap.id : V →ₗ[K] V) (LinearMap.mulRight K t)) b) :=
      congrArg _ hab
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply] at h2
    rw [hleft, LinearMap.id_apply, LinearMap.id_apply] at h2
    exact h2
  refine ⟨m₂, ?_, ?_⟩
  · -- `m₂ ≠ 0`
    intro h0
    have h1 : TensorProduct.map (LinearMap.id : V →ₗ[K] V) (LinearMap.mulRight K t) m = 0 := by
      rw [← hinc, h0, map_zero]
    exact hm (hMulT_inj (by rw [h1, map_zero]))
  · -- `x • m₂ = 0`
    apply hinj
    rw [map_zero]
    rw [show x • m₂ = diagRingHom (V := V) H.subtype Lb.genR x m₂ from rfl]
    rw [diagRingHom_map_natural H.subtype Lb.genR (L.genD H) (Subalgebra.inclusion Lb.R_le_DH) hF x m₂]
    rw [hinc]
    rw [diagRingHom_mulRight H.subtype (L.genD H) t x m]
    rw [show diagRingHom (V := V) H.subtype (L.genD H) x m = x • m from rfl, hxm, map_zero]

end Work.ORTorsion.Denom
