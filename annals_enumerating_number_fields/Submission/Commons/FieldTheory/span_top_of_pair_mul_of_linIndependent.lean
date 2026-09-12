import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Module Submodule

namespace Commons.FieldTheory

theorem span_top_of_pair_mul_of_linIndependent {F K : Type*} [Field F] [Field K]
    [Algebra F K] [FiniteDimensional F K] {m : ℕ} (a : Fin m → K)
    (ha : LinearIndependent F a) (hm : m + m > Module.finrank F K) :
    Submodule.span F (Set.range (fun p : Fin m × Fin m => a p.1 * a p.2)) = ⊤ := by
  classical
  let U : Submodule F K := Submodule.span F (Set.range a)
  let W : Submodule F K :=
    Submodule.span F (Set.range (fun p : Fin m × Fin m => a p.1 * a p.2))
  change W = ⊤
  by_contra hW
  -- The subspace spanned by the pairwise products of elements of `U` equals `W`.
  have hWW : W = U * U := by
    dsimp [W, U]
    rw [Submodule.span_mul_span]
    congr 1
    ext x
    constructor
    · intro hx
      rcases hx with ⟨p, rfl⟩
      exact Set.mul_mem_mul ⟨p.1, rfl⟩ ⟨p.2, rfl⟩
    · intro hx
      rw [Set.mem_mul] at hx
      rcases hx with ⟨y, hy, z, hz, hyz⟩
      rcases hy with ⟨i, hi⟩
      rcases hz with ⟨j, hj⟩
      refine ⟨(i, j), ?_⟩
      change a i * a j = x
      rw [hi, hj]
      exact hyz
  have hmulmem : ∀ ⦃u v : K⦄, u ∈ U → v ∈ U → u * v ∈ U * U := by
    intro u v hu hv
    rw [Submodule.mul_eq_span_mul_set]
    exact Submodule.subset_span (Set.mul_mem_mul hu hv)
  have hUprod : U * U ≤ W := by
    rw [hWW]
  -- Since `W` is proper, choose a nonzero linear functional `f` vanishing on `W`.
  have hflt : Module.finrank F W < Module.finrank F K := Submodule.finrank_lt hW
  have hAne : W.dualAnnihilator ≠ ⊥ := by
    intro hAeq
    have hfin0 : Module.finrank F (W.dualAnnihilator) = 0 := by
      rw [hAeq]
      exact finrank_bot F (Module.Dual F K)
    have hsum : Module.finrank F W + Module.finrank F (W.dualAnnihilator) =
        Module.finrank F K :=
      Subspace.finrank_add_finrank_dualAnnihilator_eq (K := F) (V := K) W
    have heq : Module.finrank F W = Module.finrank F K := by omega
    exact (ne_of_lt hflt) heq
  obtain ⟨f, hfA, hfne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hAne
  have hfW : ∀ ⦃w : K⦄, w ∈ W → f w = 0 := (Submodule.mem_dualAnnihilator f).mp hfA
  -- The map `x ↦ (y ↦ f (x * y))` is injective, because `K` is a field and `f ≠ 0`.
  let D : K →ₗ[F] Module.Dual F K :=
    (LinearMap.llcomp F K K F f).comp (LinearMap.mul F K)
  have hD_apply : ∀ x y : K, (D x) y = f (x * y) := by
    intro x y
    simp [D]
  have hDker : LinearMap.ker D = ⊥ := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      by_contra hx0
      have hfz : ∀ z : K, f z = 0 := by
        intro z
        have hxinv : x * (x⁻¹ * z) = z := by
          rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
        have hh : (D x) (x⁻¹ * z) = 0 := by
          simpa using congrArg (fun φ : Module.Dual F K => φ (x⁻¹ * z)) hx
        calc
          f z = f (x * (x⁻¹ * z)) := by rw [hxinv]
          _ = (D x) (x⁻¹ * z) := hD_apply x (x⁻¹ * z)
          _ = 0 := hh
      exact hfne (LinearMap.ext (fun z => by simpa using hfz z))
    · intro x hx
      simp at hx
      subst x
      simp
  have hDind : LinearIndependent F (⇑D ∘ a) := LinearIndependent.map' ha D hDker
  -- Each `D (a i)` annihilates `U`.
  let AA : Submodule F (Module.Dual F K) := U.dualAnnihilator
  have hDmem : ∀ i : Fin m, D (a i) ∈ AA := by
    intro i
    dsimp [AA]
    rw [Submodule.mem_dualAnnihilator]
    intro u hu
    have hUa : a i ∈ U := Submodule.subset_span (Set.mem_range_self i)
    have hpw : a i * u ∈ W := hUprod (hmulmem hUa hu)
    have hf : f (a i * u) = 0 := hfW hpw
    rw [hD_apply]
    exact hf
  let g : Fin m → AA := fun i => ⟨D (a i), hDmem i⟩
  have hg : LinearIndependent F g := by
    refine LinearIndependent.of_comp (AA.subtype : AA →ₗ[F] Module.Dual F K) ?_
    change LinearIndependent F (fun i : Fin m => D (a i))
    exact hDind
  -- Count dimensions: `m ≤ finrank (U.dualAnnihilator) = finrank K - m`, contradiction.
  have hfinU : Module.finrank F U = m := by
    dsimp [U]
    rw [finrank_span_eq_card ha]
    simp
  have hsumAA : Module.finrank F U + Module.finrank F AA = Module.finrank F K := by
    dsimp [AA]
    exact Subspace.finrank_add_finrank_dualAnnihilator_eq (K := F) (V := K) U
  have hle : m ≤ Module.finrank F AA := by
    have hc := LinearIndependent.fintype_card_le_finrank hg
    simpa using hc
  have hm2 : m + m ≤ Module.finrank F K := by omega
  exact (not_le_of_gt hm) hm2

end Commons.FieldTheory