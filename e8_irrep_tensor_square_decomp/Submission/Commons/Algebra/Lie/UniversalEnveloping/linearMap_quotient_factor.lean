import Mathlib.Algebra.Lie.UniversalEnveloping

open scoped TensorProduct

namespace Commons.Algebra.Lie.UniversalEnveloping

universe u

private def taRelSet (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L] :
    Set (TensorAlgebra K L) :=
  {z | ∃ (r s : TensorAlgebra K L) (x y : L),
    z = r * (TensorAlgebra.ι K x * TensorAlgebra.ι K y -
              TensorAlgebra.ι K y * TensorAlgebra.ι K x - TensorAlgebra.ι K ⁅x, y⁆) * s}

private def taRelSpan (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L] :
    Submodule K (TensorAlgebra K L) :=
  Submodule.span K (taRelSet K L)

private lemma taRel_mem_span {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]
    (x y : L) (r s : TensorAlgebra K L) :
    r * (TensorAlgebra.ι K x * TensorAlgebra.ι K y -
          TensorAlgebra.ι K y * TensorAlgebra.ι K x - TensorAlgebra.ι K ⁅x, y⁆) * s ∈
      taRelSpan K L := by
  exact Submodule.subset_span ⟨r, s, x, y, rfl⟩

private lemma taRelSpan_mul_left {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]
    (t u : TensorAlgebra K L) (hu : u ∈ taRelSpan K L) : t * u ∈ taRelSpan K L := by
  refine Submodule.span_induction (s := taRelSet K L) (p := fun z _ => t * z ∈ taRelSpan K L)
    ?mem ?zero ?add ?smul hu
  · intro z hz
    rcases hz with ⟨r, s, x, y, rfl⟩
    have hmem : (t * r) * (TensorAlgebra.ι K x * TensorAlgebra.ι K y -
          TensorAlgebra.ι K y * TensorAlgebra.ι K x - TensorAlgebra.ι K ⁅x, y⁆) * s ∈
        taRelSpan K L := by
      exact Submodule.subset_span ⟨t * r, s, x, y, rfl⟩
    simpa [mul_assoc] using hmem
  · simp [taRelSpan]
  · intro a b _ _ hta htb
    rw [mul_add]
    exact Submodule.add_mem (taRelSpan K L) hta htb
  · intro k a _ hta
    rw [mul_smul_comm]
    exact Submodule.smul_mem (taRelSpan K L) k hta

private lemma taRelSpan_mul_right {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]
    (t u : TensorAlgebra K L) (ht : t ∈ taRelSpan K L) : t * u ∈ taRelSpan K L := by
  refine Submodule.span_induction (s := taRelSet K L) (p := fun z _ => z * u ∈ taRelSpan K L)
    ?mem ?zero ?add ?smul ht
  · intro z hz
    rcases hz with ⟨r, s, x, y, rfl⟩
    have hmem : r * (TensorAlgebra.ι K x * TensorAlgebra.ι K y -
          TensorAlgebra.ι K y * TensorAlgebra.ι K x - TensorAlgebra.ι K ⁅x, y⁆) * (s * u) ∈
        taRelSpan K L := by
      exact Submodule.subset_span ⟨r, s * u, x, y, rfl⟩
    simpa [mul_assoc] using hmem
  · simp [taRelSpan]
  · intro a b _ _ hta htb
    rw [add_mul]
    exact Submodule.add_mem (taRelSpan K L) hta htb
  · intro k a _ hta
    rw [smul_mul_assoc]
    exact Submodule.smul_mem (taRelSpan K L) k hta

private noncomputable def taRelIdeal (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L] :
    TwoSidedIdeal (TensorAlgebra K L) :=
  TwoSidedIdeal.mk' (taRelSpan K L : Set (TensorAlgebra K L))
    (Submodule.zero_mem (taRelSpan K L))
    (fun {_x _y} hx hy => Submodule.add_mem (taRelSpan K L) hx hy)
    (fun {_} hx => Submodule.neg_mem (taRelSpan K L) hx)
    (fun {x y} hy => taRelSpan_mul_left x y hy)
    (fun {x y} hx => taRelSpan_mul_right x y hx)

private lemma taRelCon_le_ideal {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L] :
    UniversalEnvelopingAlgebra.ringCon K L ≤ (taRelIdeal K L).ringCon := by
  change ringConGen (UniversalEnvelopingAlgebra.Rel K L) ≤ (taRelIdeal K L).ringCon
  rw [RingCon.ringConGen_le]
  intro a b hab
  rw [TwoSidedIdeal.rel_iff]
  cases hab with
  | lie_compat x y =>
      have hmem : 1 * (TensorAlgebra.ι K x * TensorAlgebra.ι K y -
            TensorAlgebra.ι K y * TensorAlgebra.ι K x - TensorAlgebra.ι K ⁅x, y⁆) * 1 ∈
          taRelSpan K L := by
        exact taRel_mem_span x y 1 1
      have hneg : -((TensorAlgebra.ι K x * TensorAlgebra.ι K y -
            TensorAlgebra.ι K y * TensorAlgebra.ι K x - TensorAlgebra.ι K ⁅x, y⁆)) ∈
          taRelSpan K L := by
        simpa using (Submodule.neg_mem (taRelSpan K L) hmem)
      have hEq : (TensorAlgebra.ι K ⁅x, y⁆ + TensorAlgebra.ι K y * TensorAlgebra.ι K x) -
            TensorAlgebra.ι K x * TensorAlgebra.ι K y =
          -((TensorAlgebra.ι K x * TensorAlgebra.ι K y -
            TensorAlgebra.ι K y * TensorAlgebra.ι K x - TensorAlgebra.ι K ⁅x, y⁆)) := by
        abel
      rw [hEq]
      simpa [taRelIdeal] using hneg

private noncomputable def taToUEA (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L] :
    TensorAlgebra K L →ₗ[K] UniversalEnvelopingAlgebra K L :=
  (UniversalEnvelopingAlgebra.mkAlgHom K L).toLinearMap

private lemma taRel_ker_le_span {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]
    (a : TensorAlgebra K L) (ha : a ∈ LinearMap.ker (taToUEA K L)) : a ∈ taRelSpan K L := by
  have hqa0 : UniversalEnvelopingAlgebra.mkAlgHom K L a = 0 := by
    simpa [taToUEA] using (LinearMap.mem_ker.mp ha)
  have hc : UniversalEnvelopingAlgebra.ringCon K L a 0 := by
    exact (RingCon.eq (UniversalEnvelopingAlgebra.ringCon K L)).1 (by
      change (UniversalEnvelopingAlgebra.mkAlgHom K L a : UniversalEnvelopingAlgebra K L) =
          (0 : UniversalEnvelopingAlgebra K L)
      exact hqa0)
  have hcon : (taRelIdeal K L).ringCon a 0 := taRelCon_le_ideal (K := K) (L := L) hc
  have hmemI : a ∈ taRelIdeal K L := hcon
  simpa [taRelIdeal] using hmemI

private lemma taRelSpan_le_kerf {K L M : Type u} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M]
    (f : TensorAlgebra K L →ₗ[K] M)
    (hrel : ∀ (x y : L) (r s : TensorAlgebra K L),
      f (r * (TensorAlgebra.ι K x * TensorAlgebra.ι K y -
              TensorAlgebra.ι K y * TensorAlgebra.ι K x - TensorAlgebra.ι K ⁅x, y⁆) * s) = 0) :
    taRelSpan K L ≤ LinearMap.ker f := by
  change Submodule.span K (taRelSet K L) ≤ LinearMap.ker f
  rw [Submodule.span_le]
  intro z hz
  rcases hz with ⟨r, s, x, y, rfl⟩
  exact LinearMap.mem_ker.mpr (hrel x y r s)

/-- Any K-linear map out of the tensor algebra of a Lie algebra L that vanishes on every relator
element with arbitrary context factors through the universal enveloping algebra. -/
theorem linearMap_quotient_factor (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L]
    {M : Type u} [AddCommGroup M] [Module K M]
    (f : TensorAlgebra K L →ₗ[K] M)
    (hrel : ∀ (x y : L) (r s : TensorAlgebra K L),
      f (r * (TensorAlgebra.ι K x * TensorAlgebra.ι K y -
              TensorAlgebra.ι K y * TensorAlgebra.ι K x - TensorAlgebra.ι K ⁅x, y⁆) * s) = 0) :
    ∃ fbar : UniversalEnvelopingAlgebra K L →ₗ[K] M,
      ∀ a : TensorAlgebra K L, fbar (UniversalEnvelopingAlgebra.mkAlgHom K L a) = f a := by
  let q : TensorAlgebra K L →ₗ[K] UniversalEnvelopingAlgebra K L := taToUEA K L
  have hker : LinearMap.ker q ≤ LinearMap.ker f := by
    intro a ha
    have hspan : a ∈ taRelSpan K L :=
      taRel_ker_le_span (K := K) (L := L) a (by simpa [q] using ha)
    exact (taRelSpan_le_kerf f hrel) hspan
  have hqsurj : Function.Surjective q := by
    intro u
    rcases (RingCon.mkₐ_surjective (UniversalEnvelopingAlgebra.ringCon K L) (α := K) u) with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    change UniversalEnvelopingAlgebra.mkAlgHom K L a = u
    exact ha
  let e : (TensorAlgebra K L ⧸ LinearMap.ker q) ≃ₗ[K] UniversalEnvelopingAlgebra K L :=
    q.quotKerEquivOfSurjective hqsurj
  let φ : TensorAlgebra K L ⧸ LinearMap.ker q →ₗ[K] M := (LinearMap.ker q).liftQ f hker
  refine ⟨φ.comp e.symm.toLinearMap, ?_⟩
  intro a
  change (φ.comp e.symm.toLinearMap) (q a) = f a
  simp [φ, e, LinearMap.comp_apply, Submodule.liftQ_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply]

end Commons.Algebra.Lie.UniversalEnveloping