import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12.Gl2Cyclic

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- Cayley–Hamilton in dimension two, in the form used below: an endomorphism `z` of a
two-dimensional space satisfies `z ^ 2 = (tr z) • z - (det z) • 1`. -/
lemma sq_eq_trace_smul_sub_det_smul_one {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : Module.finrank F V = 2) (z : V →ₗ[F] V) :
    z * z = (LinearMap.trace F V z) • z - (LinearMap.det z) • (1 : V →ₗ[F] V) := by
  have hch : z.charpoly = Polynomial.X ^ 2 - Polynomial.C (LinearMap.trace F V z) * Polynomial.X
      + Polynomial.C (LinearMap.det z) := by
    let b : Module.Basis (Fin 2) F V := (Module.finBasis F V).reindex (finCongr h2)
    have h1 : (LinearMap.toMatrix b b z).charpoly = z.charpoly := LinearMap.charpoly_toMatrix z b
    rw [← h1, Matrix.charpoly_fin_two]
    have htr : (LinearMap.toMatrix b b z).trace = LinearMap.trace F V z :=
      (LinearMap.trace_eq_matrix_trace F b z).symm
    have hdet : (LinearMap.toMatrix b b z).det = LinearMap.det z := LinearMap.det_toMatrix b z
    rw [htr, hdet]
  have h := LinearMap.aeval_self_charpoly z
  rw [hch] at h
  simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h
  simp only [Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul] at h
  rw [pow_two] at h
  exact sub_eq_zero.mp (by
    rw [show z * z - ((LinearMap.trace F V z) • z - (LinearMap.det z) • (1 : V →ₗ[F] V))
          = z * z - (LinearMap.trace F V z) • z + (LinearMap.det z) • (1 : V →ₗ[F] V)
        from by abel]
    exact h)

/-- Any endomorphism commuting with a two-dimensional endomorphism `x` without eigenvectors is a
linear combination of `1` and `x`. The proof picks `0 ≠ v`, observes that `(v, x v)` is a basis,
writes `y v = a • v + b • (x v)` and checks that `y` and `a • 1 + b • x` agree on that basis. -/
lemma exists_smul_one_add_smul_of_commute {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : Module.finrank F V = 2) {x y : V →ₗ[F] V}
    (hreg : ∀ c : F, ∀ v : V, v ≠ 0 → x v ≠ c • v)
    (hxy : y * x = x * y) :
    ∃ a b : F, y = a • (1 : V →ₗ[F] V) + b • x := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [h2]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hli : LinearIndependent F ![v, x v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      have h1 : t • (x v) = -(s • v) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
      have hxvt : x v = (-(t⁻¹ * s)) • v := by
        have key : x v = t⁻¹ • (t • (x v)) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [key, h1]
        simp only [smul_neg, smul_smul, neg_smul]
      exact hreg (-(t⁻¹ * s)) v hv hxvt
    subst ht
    refine ⟨?_, rfl⟩
    have : s • v = 0 := by simpa using hst
    exact (smul_eq_zero.mp this).resolve_right hv
  have hspan : Submodule.span F (Set.range ![v, x v]) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank hli (by rw [Fintype.card_fin]; exact h2.symm)
  have hyv : y v ∈ Submodule.span F (Set.range ![v, x v]) := by
    rw [hspan]; exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hyv
  obtain ⟨c, hc⟩ := hyv
  rw [Fin.sum_univ_two] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  refine ⟨c 0, c 1, ?_⟩
  apply LinearMap.ext_on hspan
  intro w hw
  rw [Set.mem_range] at hw
  obtain ⟨i, rfl⟩ := hw
  fin_cases i
  · show y v = (c 0 • (1 : V →ₗ[F] V) + c 1 • x) v
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact hc.symm
  · show y (x v) = (c 0 • (1 : V →ₗ[F] V) + c 1 • x) (x v)
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
        show y (x v) = x (y v) by rw [← Module.End.mul_apply, hxy, Module.End.mul_apply], ← hc,
        map_add, map_smul, map_smul]

/-- The kernel of a nonzero endomorphism of the form `α • 1 + β • x` is trivial, provided `x` has
no eigenvectors. -/
lemma eq_zero_of_smul_one_add_smul_eq_zero {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {x : V →ₗ[F] V} (hreg : ∀ c : F, ∀ v : V, v ≠ 0 → x v ≠ c • v)
    {α β : F} (hne : α • (1 : V →ₗ[F] V) + β • x ≠ 0) {z : V}
    (hz : (α • (1 : V →ₗ[F] V) + β • x) z = 0) : z = 0 := by
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply] at hz
  by_contra hz0
  by_cases hβ : β = 0
  · subst hβ
    simp only [zero_smul, add_zero] at hz
    have hα : α = 0 := (smul_eq_zero.mp hz).resolve_right hz0
    subst hα
    exact hne (by simp)
  · have h1 : β • (x z) = -(α • z) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hz
    have hxz : x z = (-(β⁻¹ * α)) • z := by
      have key : x z = β⁻¹ • (β • (x z)) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
      rw [key, h1]
      simp only [smul_neg, smul_smul, neg_smul]
    exact hreg (-(β⁻¹ * α)) z hz0 hxz

/-- Hence such a nonzero endomorphism of the form `α • 1 + β • x` is injective. -/
lemma injective_of_ne_zero_smul_one_add_smul {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {x : V →ₗ[F] V} (hreg : ∀ c : F, ∀ v : V, v ≠ 0 → x v ≠ c • v)
    {α β : F} (hne : α • (1 : V →ₗ[F] V) + β • x ≠ 0) :
    Function.Injective (α • (1 : V →ₗ[F] V) + β • x) := by
  intro u w huw
  have h : u - w = 0 := by
    apply eq_zero_of_smul_one_add_smul_eq_zero hreg hne
    rw [map_sub, huw, sub_self]
  exact sub_eq_zero.mp h

/-- The algebraic identity that drives the argument: if `x, y` commute and both satisfy the same
two-term quadratic relation `z * z = S * z - D`, then `(x - y) * (x + y - S) = 0`. -/
lemma mul_sub_mul_eq_zero {R : Type*} [Ring R] {x y S D : R}
    (hxy : y * x = x * y) (hx : x * x = S * x - D) (hy : y * y = S * y - D)
    (hSx : S * x = x * S) (hSy : S * y = y * S) :
    (x - y) * (x + y - S) = 0 := by
  noncomm_ring [hxy, hx, hy, hSx, hSy]

theorem eq_or_eq_trace_smul_sub_of_commute {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : Module.finrank F V = 2) {x y : V →ₗ[F] V}
    (hns : ∀ c : F, x ≠ c • (1 : V →ₗ[F] V))
    (hreg : ∀ c : F, ∀ v : V, v ≠ 0 → x v ≠ c • v)
    (hxy : y * x = x * y)
    (htr : LinearMap.trace F V y = LinearMap.trace F V x)
    (hdet : LinearMap.det y = LinearMap.det x) :
    y = x ∨ y = (LinearMap.trace F V x) • (1 : V →ₗ[F] V) - x := by
  obtain ⟨a, b, hy⟩ := exists_smul_one_add_smul_of_commute h2 hreg hxy
  have hxCH : x * x = (LinearMap.trace F V x) • x - (LinearMap.det x) • (1 : V →ₗ[F] V) :=
    sq_eq_trace_smul_sub_det_smul_one h2 x
  have hyCH : y * y = (LinearMap.trace F V x) • y - (LinearMap.det x) • (1 : V →ₗ[F] V) := by
    rw [← htr, ← hdet]; exact sq_eq_trace_smul_sub_det_smul_one h2 y
  have hSx : ((LinearMap.trace F V x) • (1 : V →ₗ[F] V)) * x
      = x * ((LinearMap.trace F V x) • (1 : V →ₗ[F] V)) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one]
  have hSy : ((LinearMap.trace F V x) • (1 : V →ₗ[F] V)) * y
      = y * ((LinearMap.trace F V x) • (1 : V →ₗ[F] V)) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one]
  have hxCH' : x * x = ((LinearMap.trace F V x) • (1 : V →ₗ[F] V)) * x
      - (LinearMap.det x) • (1 : V →ₗ[F] V) := by
    rw [Algebra.smul_mul_assoc, one_mul]; exact hxCH
  have hyCH' : y * y = ((LinearMap.trace F V x) • (1 : V →ₗ[F] V)) * y
      - (LinearMap.det x) • (1 : V →ₗ[F] V) := by
    rw [Algebra.smul_mul_assoc, one_mul]; exact hyCH
  have hpq : (x - y) * (x + y - (LinearMap.trace F V x) • (1 : V →ₗ[F] V)) = 0 :=
    mul_sub_mul_eq_zero hxy hxCH' hyCH' hSx hSy
  by_cases hxy0 : x - y = 0
  · left; exact (sub_eq_zero.mp hxy0).symm
  · right
    have hxyd : x - y = (-a) • (1 : V →ₗ[F] V) + (1 - b) • x := by
      rw [hy]; module
    have hne' : (-a) • (1 : V →ₗ[F] V) + (1 - b) • x ≠ 0 := by rw [← hxyd]; exact hxy0
    have hinj : Function.Injective (x - y) := by
      rw [hxyd]; exact injective_of_ne_zero_smul_one_add_smul hreg hne'
    have hq : x + y - (LinearMap.trace F V x) • (1 : V →ₗ[F] V) = 0 := by
      ext w
      show (x + y - (LinearMap.trace F V x) • (1 : V →ₗ[F] V)) w = 0
      refine hinj ?_
      have hmul : (x - y) ((x + y - (LinearMap.trace F V x) • (1 : V →ₗ[F] V)) w)
          = ((x - y) * (x + y - (LinearMap.trace F V x) • (1 : V →ₗ[F] V))) w := by
        rw [Module.End.mul_apply]
      rw [hmul, hpq]; simp
    exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact sub_eq_zero.mp hq)

end Work.ThmF.ChV12.Gl2Cyclic
