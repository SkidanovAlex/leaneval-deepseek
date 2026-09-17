import Mathlib
import Submission.Commons.Lattice.Minkowski.covol_span_wedge
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_eq_abs_det
import Submission.Commons.Lattice.Discrete.discreteTopology_span_linIndep

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Commons.Lattice.MinkowskiHlawka

open scoped BigOperators

/-- A product over `Fin d` (`d ≥ 1`) of a two-valued function which is `u` at `0`. -/
private lemma prod_ite_zero_fin {d : ℕ} [NeZero d] (u v : ℝ) :
    (∏ i : Fin d, (if i = 0 then u else v)) = u * v ^ (d - 1) := by
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin d))
      (fun i : Fin d => if i = 0 then u else v) (Finset.mem_univ (0 : Fin d))]
  have h1 : (∏ i ∈ Finset.univ.erase (0 : Fin d), (if i = 0 then u else v))
      = ∏ _i ∈ Finset.univ.erase (0 : Fin d), v := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_erase] at hi
    rw [if_neg hi.1]
  rw [h1, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin d)),
    Finset.card_univ, Fintype.card_fin, if_pos rfl]
  ring

/-- **The `q`-ary lattice of a covector.**  Let `q` be a prime, `a : (ℤ/q)^d` a non-zero
covector and `R > 0`.  If no non-zero integer vector of norm at most `R` is annihilated by `a`
modulo `q`, then there is a lattice `Λ ⊆ ℝ^d` of minimum norm at least `1` whose covolume is at
most `q / R^d`: it is `R⁻¹` times the kernel `{x ∈ ℤ^d : ∑ xᵢ aᵢ ≡ 0 (mod q)}`, which has index
`q` in `ℤ^d` and minimum norm `> R`. -/
theorem lattice_of_covector {d q : ℕ} [NeZero d] [Fact q.Prime] {R : ℝ} (hR : 0 < R)
    (a : Fin d → ZMod q) (ha0 : a 0 ≠ 0)
    (hno : ∀ x : Fin d → ℤ, x ≠ 0 → (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2 →
        (∑ i, (x i : ZMod q) * a i) ≠ 0) :
    ∃ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (h₁ : DiscreteTopology Λ) (h₂ : IsZLattice ℝ Λ),
      (∀ v : Λ, v ≠ 0 → 1 ≤ ‖(v : EuclideanSpace ℝ (Fin d))‖) ∧
      ZLattice.covolume Λ ≤ (q : ℝ) / R ^ d := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  -- integer lifts of the covector
  let c : Fin d → ℤ := fun j => (((a j) * (a 0)⁻¹ : ZMod q).val : ℤ)
  have hc : ∀ j : Fin d, (c j : ZMod q) * a 0 = a j := by
    intro j
    have h1 : ((c j : ZMod q)) = a j * (a 0)⁻¹ := by
      simp only [c, Int.cast_natCast]
      exact ZMod.natCast_zmod_val _
    rw [h1, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  -- integer generators of the kernel lattice
  let Zvec : Fin d → (Fin d → ℤ) := fun j i =>
    if j = 0 then (if i = 0 then (q : ℤ) else 0)
    else (if i = j then 1 else 0) - c j * (if i = 0 then 1 else 0)
  have hZ0 : ∀ i : Fin d, Zvec 0 i = (if i = 0 then (q : ℤ) else 0) := by
    intro i; simp only [Zvec, if_pos rfl]
  have hZj : ∀ j : Fin d, j ≠ 0 → ∀ i : Fin d,
      Zvec j i = (if i = j then 1 else 0) - c j * (if i = 0 then 1 else 0) := by
    intro j hj i; simp only [Zvec, if_neg hj]
  -- the integral covector
  let ψ : (Fin d → ℤ) →ₗ[ℤ] ZMod q :=
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
  have hψZ : ∀ j : Fin d, ψ (Zvec j) = 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      have h : ∀ i : Fin d, ((Zvec 0 i : ℤ) : ZMod q) = 0 := by
        intro i
        rw [hZ0 i]
        by_cases hi : i = 0
        · rw [if_pos hi, Int.cast_natCast]
          exact ZMod.natCast_self q
        · rw [if_neg hi, Int.cast_zero]
      calc ψ (Zvec 0) = ∑ i : Fin d, ((Zvec 0 i : ℤ) : ZMod q) * a i := rfl
        _ = ∑ _i : Fin d, (0 : ZMod q) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [h i, zero_mul]
        _ = 0 := Finset.sum_const_zero
    · have h : ∀ i : Fin d, ((Zvec j i : ℤ) : ZMod q)
          = (if i = j then (1 : ZMod q) else 0)
            - (c j : ZMod q) * (if i = 0 then (1 : ZMod q) else 0) := by
        intro i
        rw [hZj j hj i]
        by_cases hij : i = j
        · rw [if_pos hij, if_pos hij]
          by_cases hi0 : i = 0
          · rw [if_pos hi0, if_pos hi0]
            push_cast
            ring
          · rw [if_neg hi0, if_neg hi0]
            push_cast
            ring
        · rw [if_neg hij, if_neg hij]
          by_cases hi0 : i = 0
          · rw [if_pos hi0, if_pos hi0]
            push_cast
            ring
          · rw [if_neg hi0, if_neg hi0]
            push_cast
            ring
      have hsplit : (∑ i : Fin d, ((if i = j then (1 : ZMod q) else 0)
            - (c j : ZMod q) * (if i = 0 then (1 : ZMod q) else 0)) * a i)
          = (∑ i : Fin d, (if i = j then (1 : ZMod q) else 0) * a i)
            - ∑ i : Fin d, ((c j : ZMod q) * (if i = 0 then (1 : ZMod q) else 0)) * a i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [sub_mul]
      have hA : (∑ i : Fin d, (if i = j then (1 : ZMod q) else 0) * a i) = a j := by
        rw [Finset.sum_eq_single j]
        · rw [if_pos rfl, one_mul]
        · intro i _ hij
          rw [if_neg hij, zero_mul]
        · intro hh
          exact absurd (Finset.mem_univ j) hh
      have hB : (∑ i : Fin d,
            ((c j : ZMod q) * (if i = 0 then (1 : ZMod q) else 0)) * a i)
          = (c j : ZMod q) * a 0 := by
        have hstep : (∑ i : Fin d,
              ((c j : ZMod q) * (if i = 0 then (1 : ZMod q) else 0)) * a i)
            = (c j : ZMod q) * ∑ i : Fin d, (if i = 0 then (1 : ZMod q) else 0) * a i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hstep]
        congr 1
        rw [Finset.sum_eq_single (0 : Fin d)]
        · rw [if_pos rfl, one_mul]
        · intro i _ hi
          rw [if_neg hi, zero_mul]
        · intro hh
          exact absurd (Finset.mem_univ (0 : Fin d)) hh
      calc ψ (Zvec j) = ∑ i : Fin d, ((Zvec j i : ℤ) : ZMod q) * a i := rfl
        _ = ∑ i : Fin d, ((if i = j then (1 : ZMod q) else 0)
              - (c j : ZMod q) * (if i = 0 then (1 : ZMod q) else 0)) * a i := by
              apply Finset.sum_congr rfl
              intro i _
              rw [h i]
        _ = 0 := by rw [hsplit, hA, hB, hc j, sub_self]
  -- the integral lattice vectors as elements of the Euclidean space
  let iZ : (Fin d → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin d) :=
    { toFun := fun w => WithLp.toLp 2 (fun i => (w i : ℝ))
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
  have hiz_apply : ∀ (w : Fin d → ℤ) (i : Fin d), (iZ w) i = (w i : ℝ) := fun w i => rfl
  -- the generators of the lattice
  let V : Fin d → EuclideanSpace ℝ (Fin d) := fun j => (1 / R) • iZ (Zvec j)
  have hVcoord : ∀ (j : Fin d) (i : Fin d), (V j) i = (1 / R) * ((Zvec j i : ℤ) : ℝ) := by
    intro j i
    simp only [V, PiLp.smul_apply, smul_eq_mul, hiz_apply]
  have hV0 : ∀ i : Fin d, (V 0) i = (q / R) * (if i = 0 then 1 else 0) := by
    intro i
    rw [hVcoord 0 i, hZ0 i]
    by_cases hi : i = 0
    · rw [if_pos hi, if_pos hi]
      push_cast
      rw [div_eq_mul_inv]
      ring
    · rw [if_neg hi, if_neg hi]
      push_cast
      ring
  have hVj : ∀ j : Fin d, j ≠ 0 → ∀ i : Fin d,
      (V j) i = (1 / R) * ((if i = j then 1 else 0) - (c j : ℝ) * (if i = 0 then 1 else 0)) := by
    intro j hj i
    rw [hVcoord j i, hZj j hj i]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij]
      by_cases hi0 : i = 0
      · rw [if_pos hi0, if_pos hi0]
        push_cast
        ring
      · rw [if_neg hi0, if_neg hi0]
        push_cast
        ring
    · rw [if_neg hij, if_neg hij]
      by_cases hi0 : i = 0
      · rw [if_pos hi0, if_pos hi0]
        push_cast
        ring
      · rw [if_neg hi0, if_neg hi0]
        push_cast
        ring
  -- the matrix of the family `V` and its determinant
  let A : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun i j => (V j) i)
  have hAup : A.IsUpperTriangular := by
    intro i j hji
    have hi0 : i ≠ 0 := fun h => by subst h; exact absurd hji (Fin.not_lt_zero j)
    have hij : i ≠ j := fun h => by rw [h] at hji; exact absurd hji (lt_irrefl j)
    by_cases hj : j = 0
    · subst hj
      rw [show A i 0 = (V 0) i from rfl, hV0 i, if_neg hi0]
      ring
    · rw [show A i j = (V j) i from rfl, hVj j hj i, if_neg hij, if_neg hi0]
      ring
  have hdiag : ∀ i : Fin d, A i i = if i = 0 then q / R else 1 / R := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [show A 0 0 = (V 0) 0 from rfl, hV0 0, if_pos rfl, if_pos rfl, mul_one]
    · rw [show A i i = (V i) i from rfl, hVj i hi i]
      simp [hi]
  have hdetA : A.det = q / R ^ d := by
    rw [Matrix.det_of_isUpperTriangular hAup]
    have hprod : (∏ i : Fin d, A i i) = (q / R) * (1 / R) ^ (d - 1) := by
      have h1 : (∏ i : Fin d, A i i) = ∏ i : Fin d, (if i = 0 then q / R else 1 / R) :=
        Finset.prod_congr rfl (fun i _ => hdiag i)
      rw [h1, prod_ite_zero_fin]
    rw [hprod]
    have hpow : (1 / R) ^ (d - 1) * (1 / R) = (1 / R) ^ d := by
      rw [← pow_succ, Nat.sub_add_cancel hd1]
    calc q / R * (1 / R) ^ (d - 1) = q * ((1 / R) * (1 / R) ^ (d - 1)) := by ring
      _ = q * ((1 / R) ^ (d - 1) * (1 / R)) := by ring
      _ = q * (1 / R) ^ d := by rw [hpow]
      _ = q / R ^ d := by
            rw [div_eq_mul_inv]
            congr 1
            rw [one_mul, inv_pow]
  have hdetne : A.det ≠ 0 := by
    rw [hdetA]
    exact div_ne_zero (by positivity) (pow_ne_zero _ hR0)
  -- the family `V` is ℝ-linearly independent
  have hlin : LinearIndependent ℝ V := by
    have hns : A.Nonsingular := Matrix.nonsingular_iff_det_ne_zero.mpr hdetne
    have hcol : LinearIndependent ℝ A.col := hns.linearIndependent_col
    refine LinearIndependent.of_comp (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap ?_
    have hcol' : LinearIndependent ℝ (fun j : Fin d => (V j).ofLp) := hcol
    exact hcol'
  -- the lattice
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℤ (Set.range V)
  have hdisc : DiscreteTopology Λ := by
    show DiscreteTopology (Submodule.span ℤ (Set.range V))
    exact Commons.Lattice.Discrete.discreteTopology_span_linIndep V hlin
  have hisZ : IsZLattice ℝ Λ := ⟨by
    show Submodule.span ℝ (Submodule.span ℤ (Set.range V) : Set (EuclideanSpace ℝ (Fin d))) = ⊤
    rw [Submodule.span_span_of_tower ℤ ℝ]
    exact le_antisymm le_top (Commons.Lattice.Minkowski.span_top_of_linearIndependent V hlin)⟩
  have hcov : ZLattice.covolume Λ = q / R ^ d := by
    have h1 : ZLattice.covolume (Submodule.span ℤ (Set.range V))
        = ‖exteriorPower.ιMulti ℝ d V‖ :=
      Commons.Lattice.Minkowski.covol_span_wedge d (Nat.pos_of_ne_zero (NeZero.ne d)) V hlin
    have h2 : ‖exteriorPower.ιMulti ℝ d V‖
        = |(Matrix.of (fun (i j : Fin d) => (V j) i)).det| :=
      Commons.Analysis.InnerProductSpace.norm_iMulti_eq_abs_det V hlin
    change ZLattice.covolume (Submodule.span ℤ (Set.range V)) = q / R ^ d
    rw [h1, h2]
    have h3 : (Matrix.of (fun (i j : Fin d) => (V j) i)) = A := rfl
    rw [h3, hdetA, abs_of_pos (div_pos (by positivity) (pow_pos hR d))]
  -- the minimum norm
  have hRV : ∀ j : Fin d, R • V j = iZ (Zvec j) := by
    intro j
    rw [show V j = (1 / R) • iZ (Zvec j) from rfl, smul_smul, one_div, mul_inv_cancel₀ hR0,
      one_smul]
  let K : Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
    Submodule.span ℤ (Set.range (fun j : Fin d => iZ (Zvec j)))
  have hK : K ≤ Submodule.map iZ ψ.ker := by
    show Submodule.span ℤ (Set.range (fun j : Fin d => iZ (Zvec j))) ≤ Submodule.map iZ ψ.ker
    rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    exact Submodule.mem_map.mpr ⟨Zvec j, by rw [LinearMap.mem_ker]; exact hψZ j, rfl⟩
  have hmin : ∀ v : Λ, v ≠ 0 → 1 ≤ ‖(v : EuclideanSpace ℝ (Fin d))‖ := by
    intro v hv
    by_contra hlt
    rw [not_le] at hlt
    have hvne : (v : EuclideanSpace ℝ (Fin d)) ≠ 0 := fun h => hv (Subtype.ext h)
    have hvx : (v : EuclideanSpace ℝ (Fin d)) ∈ Submodule.span ℤ (Set.range V) := v.2
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := V)
      (x := (v : EuclideanSpace ℝ (Fin d)))).1 hvx
    have hRx : R • (v : EuclideanSpace ℝ (Fin d)) ∈ K := by
      rw [← hm, Finset.smul_sum]
      apply Submodule.sum_mem
      intro j _
      rw [show R • (m j • V j) = m j • (R • V j) by rw [smul_comm], hRV j]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨y, hyker, hyeq⟩ := Submodule.mem_map.mp (hK hRx)
    have hyne : y ≠ 0 := by
      intro h0
      refine hvne ?_
      have hz : R • (v : EuclideanSpace ℝ (Fin d)) = 0 := by rw [← hyeq, h0]; simp
      exact (smul_eq_zero.mp hz).resolve_left hR0
    have hypsi : ψ y = 0 := hyker
    have hynorm : (∑ i, ((y i : ℝ)) ^ 2) = R ^ 2 * ‖(v : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
      have h1 : (∑ i, ((y i : ℝ)) ^ 2) = ‖iZ y‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        apply Finset.sum_congr rfl
        intro i _
        rw [show (iZ y) i = (y i : ℝ) from rfl]
      rw [h1, hyeq, norm_smul, Real.norm_of_nonneg (le_of_lt hR), mul_pow]
    have hle : (∑ i, ((y i : ℝ)) ^ 2) ≤ R ^ 2 := by
      rw [hynorm]
      have h2 : ‖(v : EuclideanSpace ℝ (Fin d))‖ ^ 2 < 1 := by
        nlinarith [norm_nonneg (v : EuclideanSpace ℝ (Fin d))]
      nlinarith [pow_pos hR 2, h2]
    exact (hno y hyne hle) hypsi
  exact ⟨Λ, hdisc, hisZ, hmin, le_of_eq hcov⟩

end Commons.Lattice.MinkowskiHlawka
