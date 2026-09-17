import Mathlib
import Submission.Commons.Lattice.Minkowski.covol_span_wedge
import Submission.Commons.Lattice.Discrete.discreteTopology_span_linIndep
import Submission.Commons.Lattice.Discrete.discreteTopology_of_le
import Submission.Commons.Lattice.Discrete.discreteTopology_of_linearImage
import Submission.Commons.Lattice.Packing.rogers_conversion
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_eq_abs_det

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open scoped BigOperators

namespace Commons.Lattice.Counting

theorem exists_qary_lattice_covolume_and_image {n q : ℕ} [Fact q.Prime] {R : ℝ} (hR : 0 < R)
    (a : Fin n → ZMod q) (ha : a ≠ 0) :
    ∃ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ),
      ZLattice.covolume Λ = (q : ℝ) / R ^ n ∧
      ∀ x : EuclideanSpace ℝ (Fin n), x ∈ Λ ↔
        ∃ k : Fin n → ℤ, (∑ i, (k i : ZMod q) * a i = 0) ∧
          x = WithLp.toLp 2 (fun i => (k i : ℝ) / R) := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqR : (0:ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hqRne : (q:ℝ) ≠ 0 := ne_of_gt hqR
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact absurd (funext fun i => i.elim0) ha
    · exact h
  obtain ⟨p, hp⟩ : ∃ p : Fin n, a p ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  let iZ : (Fin n → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin n) :=
    { toFun := fun k => WithLp.toLp 2 (fun i => (k i : ℝ))
      map_add' := by
        intro u w
        apply PiLp.ext
        intro i
        simp only [WithLp.ofLp_add, Pi.add_apply, Int.cast_add]
      map_smul' := by
        intro m w
        apply PiLp.ext
        intro i
        simp only [WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply]
        rw [zsmul_eq_mul]
        push_cast
        ring }
  let ψ : (Fin n → ℤ) →ₗ[ℤ] ZMod q :=
    { toFun := fun w => ∑ i, (w i : ZMod q) * a i
      map_add' := by
        intro u w
        simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro m w
        simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, RingHom.id_apply,
          Finset.mul_sum, zsmul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  let Z : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
    Submodule.span ℤ (Set.range (fun i : Fin n => EuclideanSpace.basisFun (Fin n) ℝ i))
  let L : Submodule ℤ (EuclideanSpace ℝ (Fin n)) := Submodule.map iZ ψ.ker
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (1 / R) • LinearMap.id
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)) := Submodule.map (T.restrictScalars ℤ) L
  have hv : LinearIndependent ℝ (fun i : Fin n => EuclideanSpace.basisFun (Fin n) ℝ i) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.linearIndependent
  have hZdef : Z = Submodule.span ℤ
      (Set.range (fun i : Fin n => EuclideanSpace.basisFun (Fin n) ℝ i)) := rfl
  haveI hZdis : DiscreteTopology Z :=
    Commons.Lattice.Discrete.discreteTopology_span_linIndep _ hv
  haveI hZZL : IsZLattice ℝ Z := by
    refine ⟨?_⟩
    rw [hZdef, Submodule.span_span_of_tower ℤ ℝ]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq
  have hcovZ : ZLattice.covolume Z = 1 := by
    rw [hZdef, Commons.Lattice.Minkowski.covol_span_wedge n hn _ hv,
      Commons.Analysis.InnerProductSpace.norm_iMulti_eq_abs_det _ hv]
    have hmat : (Matrix.of fun i j : Fin n =>
        ((fun i : Fin n => EuclideanSpace.basisFun (Fin n) ℝ i) j).ofLp i)
        = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.one_apply, EuclideanSpace.basisFun_apply,
        PiLp.single_apply]
    rw [hmat, Matrix.det_one, abs_one]
  have htoLp : ∀ (c : Fin n → ℝ),
      WithLp.toLp 2 c = ∑ i, c i • (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    intro c
    rw [(OrthonormalBasis.sum_repr (EuclideanSpace.basisFun (Fin n) ℝ)
      (WithLp.toLp 2 c)).symm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [EuclideanSpace.basisFun_repr, PiLp.toLp_apply]
  have iZ_eq : ∀ (k : Fin n → ℤ),
      iZ k = ∑ j, (k j : ℤ) • (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    intro k
    have h1 : iZ k = WithLp.toLp 2 (fun i => (k i : ℝ)) := rfl
    rw [h1, htoLp]
    exact Finset.sum_congr rfl (fun i _ => (Int.cast_smul_eq_zsmul ℝ (k i) _))
  have iZ_mem : ∀ k : Fin n → ℤ, iZ k ∈ Z := by
    intro k
    rw [hZdef, iZ_eq k]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))
  have hZeq : Z = Submodule.map iZ ⊤ := by
    refine le_antisymm ?_ ?_
    · rw [hZdef, Submodule.span_le]
      rintro x ⟨i, rfl⟩
      refine Submodule.mem_map.mpr ⟨Pi.single i (1:ℤ), Submodule.mem_top, ?_⟩
      rw [iZ_eq, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_smul]
      · intro h; exact absurd (Finset.mem_univ i) h
    · intro x hx
      rw [Submodule.mem_map] at hx
      obtain ⟨k, -, hk⟩ := hx
      rw [← hk]
      exact iZ_mem k
  have hLleZ : L ≤ Z := by
    rintro x ⟨k, -, rfl⟩
    exact iZ_mem k
  haveI hLdis : DiscreteTopology L := Commons.Lattice.Discrete.discreteTopology_of_le hLleZ
  have hψsingle : ∀ i : Fin n, ψ (Pi.single i (1:ℤ)) = a i := by
    intro i
    have h1 : ψ (Pi.single i (1:ℤ))
        = ∑ j, (((Pi.single i (1:ℤ) : Fin n → ℤ)) j : ZMod q) * a j := rfl
    rw [h1, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, Int.cast_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hiZsingle : ∀ i : Fin n,
      iZ (Pi.single i (1:ℤ)) = EuclideanSpace.basisFun (Fin n) ℝ i := by
    intro i
    rw [iZ_eq, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i) h
  haveI hLZL : IsZLattice ℝ L := by
    refine ⟨?_⟩
    rw [eq_top_iff, ← (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    have hmem : (q : ℝ) • (EuclideanSpace.basisFun (Fin n) ℝ i) ∈ L := by
      refine Submodule.mem_map.mpr ⟨(q : ℤ) • Pi.single i (1:ℤ), ?_, ?_⟩
      · rw [LinearMap.mem_ker]
        rw [map_smul, hψsingle i, zsmul_eq_mul]
        rw [show (((q : ℤ) : ZMod q)) = 0 by rw [Int.cast_natCast, ZMod.natCast_self]]
        rw [zero_mul]
      · show iZ ((q : ℤ) • Pi.single i (1:ℤ)) = (q : ℝ) • EuclideanSpace.basisFun (Fin n) ℝ i
        rw [map_smul, hiZsingle, ← Int.cast_smul_eq_zsmul ℝ (q : ℤ)
          (EuclideanSpace.basisFun (Fin n) ℝ i), Int.cast_natCast]
    have h1 := Submodule.smul_mem (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))))
      ((q:ℝ)⁻¹) (Submodule.subset_span hmem)
    simpa [smul_smul, inv_mul_cancel₀ hqRne] using h1
  have hsurj : Function.Surjective ψ := by
    intro y
    refine ⟨((y * (a p)⁻¹).val : ℤ) • Pi.single p (1:ℤ), ?_⟩
    have h1 : ψ (((y * (a p)⁻¹).val : ℤ) • Pi.single p (1:ℤ))
        = ∑ i, (((((y * (a p)⁻¹).val : ℤ) • Pi.single p (1:ℤ) : Fin n → ℤ)) i : ZMod q) * a i := rfl
    rw [h1, Finset.sum_eq_single p]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Int.cast_natCast,
        ZMod.natCast_zmod_val]
      rw [mul_assoc, inv_mul_cancel₀ hp, mul_one]
    · intro i _ hi
      rw [Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero, Int.cast_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ p) h
  have hLmap : L.toAddSubgroup
      = AddSubgroup.map iZ.toAddMonoidHom (ψ.ker).toAddSubgroup :=
    Submodule.map_toAddSubgroup iZ ψ.ker
  have hZmap : Z.toAddSubgroup
      = AddSubgroup.map iZ.toAddMonoidHom (⊤ : AddSubgroup (Fin n → ℤ)) := by
    have h1 : Z.toAddSubgroup = (Submodule.map iZ ⊤).toAddSubgroup := by rw [hZeq]
    rw [h1]
    exact Submodule.map_toAddSubgroup iZ ⊤
  have hizinj : Function.Injective ⇑iZ.toAddMonoidHom := by
    intro k l hkl
    have h2 : iZ k = iZ l := hkl
    have h3 : ∀ i, (k i : ℝ) = (l i : ℝ) := by
      intro i
      have h4 := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v.ofLp i) h2
      simpa [iZ, PiLp.toLp_apply] using h4
    ext i
    exact_mod_cast h3 i
  have hrel : L.toAddSubgroup.relIndex Z.toAddSubgroup = q := by
    rw [hLmap, hZmap, AddSubgroup.relIndex_map_map_of_injective _ _ hizinj,
      AddSubgroup.relIndex_top_right]
    have h1 : (ψ.ker).toAddSubgroup.index
        = Nat.card ((Fin n → ℤ) ⧸ (ψ.ker).toAddSubgroup) := rfl
    rw [h1]
    have h2 : Nat.card ((Fin n → ℤ) ⧸ (ψ.ker).toAddSubgroup) = Nat.card ψ.range :=
      Nat.card_congr (LinearMap.quotKerEquivRange ψ).toEquiv
    rw [h2, LinearMap.range_eq_top.mpr hsurj]
    rw [Nat.card_congr (Submodule.topEquiv (R := ℤ)).toEquiv, Nat.card_zmod]
  have hcovL : ZLattice.covolume L = q := by
    have h := ZLattice.covolume_div_covolume_eq_relIndex' L Z hLleZ
    rw [hcovZ, hrel] at h
    simpa using h
  have hTinj : Function.Injective T := by
    intro x y hxy
    have h1 : T x = (1/R) • x := rfl
    have h2 : T y = (1/R) • y := rfl
    have h3 : (1/R) • x = (1/R) • y := by rw [← h1, ← h2]; exact hxy
    exact smul_right_injective _ (by positivity : (1/R) ≠ 0) h3
  have hdetT : |LinearMap.det T| = (1/R)^n := by
    have h1 : LinearMap.det T = (1/R)^n := by
      rw [show T = (1/R) • (LinearMap.id :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) from rfl]
      rw [LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_euclideanSpace_fin]
    rw [h1, abs_of_nonneg (by positivity)]
  haveI hΛdis : DiscreteTopology Λ :=
    Commons.Lattice.Discrete.discreteTopology_of_linearImage T hTinj L
  haveI hΛZL : IsZLattice ℝ Λ := by
    refine ⟨?_⟩
    have hset : (Λ : Set (EuclideanSpace ℝ (Fin n)))
        = T '' (L : Set (EuclideanSpace ℝ (Fin n))) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    rw [hset, ← Submodule.map_span, IsZLattice.span_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hTinj)
  have hcovΛ : ZLattice.covolume Λ = (q : ℝ) / R ^ n := by
    rw [Commons.Lattice.Packing.covolume_map_linear L T hTinj, hcovL, hdetT]
    rw [one_div, inv_pow, div_eq_mul_inv]
    ring
  have hkey : ∀ k : Fin n → ℤ,
      T (iZ k) = WithLp.toLp 2 (fun i => (k i : ℝ) / R) := by
    intro k
    have h1 : T (iZ k) = (1/R) • (iZ k) := rfl
    rw [h1]
    have h2 : (1/R) • (iZ k) = WithLp.toLp 2 (fun i => (1/R) * (k i : ℝ)) := rfl
    rw [h2]
    congr 1
    ext i
    rw [div_eq_mul_inv]
    ring
  refine ⟨Λ, hΛdis, hΛZL, hcovΛ, ?_⟩
  intro x
  rw [show x ∈ Λ ↔ ∃ y ∈ L, T y = x from Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨k, hk, hky⟩ := Submodule.mem_map.mp hy
    refine ⟨k, ?_, ?_⟩
    · exact show (∑ i, (k i : ZMod q) * a i) = 0 from hk
    · rw [← hyx, ← hky, hkey k]
  · rintro ⟨k, hk, hkx⟩
    refine ⟨iZ k, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨k, (show ψ k = 0 from hk), rfl⟩
    · rw [hkey k, ← hkx]

end Commons.Lattice.Counting
