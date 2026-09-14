import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.SuccessiveMinima.positive
import Submission.Commons.Lattice.SuccessiveMinima.exact_realization
import Submission.Commons.Lattice.Minkowski.minkowski_second_upper
import Submission.Commons.Lattice.Minkowski.flag_basis
import Submission.Commons.Lattice.Module.basis_extension_pure_rank
import Submission.Commons.Lattice.Minkowski.bounded_basis_of_bounded_realizers

open Module MeasureTheory Metric Set Submodule
open scoped ENNReal BigOperators
noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Commons.Lattice.Minkowski

open flagBasis

/-! # A bounded `ℤ`-basis for lattices of covolume one and minimum at least one

The theorem of this module (`bounded_basis_covolume_one`) states that for every rank `m`
there is a constant `C(m)` such that any full-rank `ℤ`-lattice `ℒ ≤ EuclideanSpace ℝ (Fin m)`
with covolume `1` and all nonzero vectors of norm `≥ 1` has a `ℤ`-basis whose vectors all
have norm `≤ C(m)`.

Strategy.  Let `λᵢ` be the successive minima of `ℒ`.
1.  All `λᵢ ≥ 1` (hypothesis), and Minkowski's second theorem bounds `λ_m ≤ A(m)`.
2.  Exact realisers `v₁,…,vₘ ∈ ℒ` (`‖vⱼ‖ ≤ λⱼ`) are therefore bounded by `R := A(m)`.
3.  **Flag extension with norm control** (the main geometric content): working along the
    flag `W_t := span(v₁,…,v_t)`, `Q_t := ℒ ∩ W_t`, any `ℤ`-basis of `Q_t` with vectors of
    norm `≤ t·R` extends to a `ℤ`-basis of `Q_{t+1}` with all vectors of norm `≤ (t+1)·R`:
    choose a basis-extension generator `x`; kill its `W_t`-component by adding a lattice
    point of `Q_t` close to that component (rounding in the realiser basis of `W_t`); the
    remaining perpendicular component is bounded by `R` because it is a nonzero integral
    multiple of the realiser `v_{t+1}`'s perpendicular component.
4.  Induction over `t` gives a basis of `Q_m = ℒ` with all norms `≤ m·R`, and `R ≤ A(m)`.
-/

-- =====================================================================
-- Part 1 : unit ball volume, and the bound on λ_m from Minkowski's 2nd theorem
-- =====================================================================

section BoundLambda

abbrev EuBB (m : ℕ) := EuclideanSpace ℝ (Fin m)

lemma finrank_euclid (m : ℕ) : Module.finrank ℝ (EuBB m) = m := by
  have hb : Module.Basis (Fin m) ℝ (EuBB m) := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  rw [Module.finrank_eq_card_basis hb]
  simp

lemma finrank_lattice_euclid {m : ℕ} (L : Submodule ℤ (EuBB m)) [DiscreteTopology L]
    [IsZLattice ℝ L] : Module.finrank ℤ L = m := by
  rw [ZLattice.rank ℝ L, finrank_euclid]

lemma vol_unit_ball_pos {m : ℕ} (hm : 0 < m) :
    0 < (volume (Metric.closedBall (0 : EuBB m) 1)).toReal := by
  classical
  haveI : Nontrivial (EuBB m) := by
    refine ⟨⟨(EuclideanSpace.basisFun (Fin m) ℝ) ⟨0, hm⟩, 0, ?_⟩⟩
    intro hz
    have hnz : ‖(EuclideanSpace.basisFun (Fin m) ℝ) ⟨0, hm⟩‖ ≠ 0 := by
      rw [(EuclideanSpace.basisFun (Fin m) ℝ).orthonormal.1 ⟨0, hm⟩]
      norm_num
    exact hnz (by rw [hz, norm_zero])
  have hbdd : (volume (Metric.closedBall (0 : EuBB m) 1) : ℝ≥0∞) ≠ ∞ := by
    exact (Bornology.IsBounded.measure_lt_top (Metric.isBounded_closedBall)).ne
  have hpos : 0 < (volume (Metric.closedBall (0 : EuBB m) 1) : ℝ≥0∞) := by
    simpa using (measure_closedBall_pos volume (0 : EuBB m) (by norm_num : (0 : ℝ) < 1))
  exact ENNReal.toReal_pos hpos.ne' hbdd

/-- `λ₁ ≥ 1` under the hypothesis that all nonzero vectors have norm `≥ 1`. -/
lemma lambda1_ge_one {m : ℕ} (hm : 0 < m) (L : Submodule ℤ (EuBB m)) [DiscreteTopology L]
    [IsZLattice ℝ L] (hmin : ∀ v : L, v ≠ 0 → 1 ≤ ‖(v : EuBB m)‖) :
    1 ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum L 1 := by
  classical
  exact Commons.Lattice.SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge L (1 : ℝ)
    (by norm_num)
    (Commons.Lattice.SuccessiveMinima.nonempty_successiveMinimumSet L 1
      (by simpa [finrank_lattice_euclid L]))
    hmin

/-- Product of finitely many real numbers all `≥ 1` is `≥ 1`. -/
private lemma prod_ge_one_of_ge_one {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, (1 : ℝ) ≤ f i) : (1 : ℝ) ≤ ∏ i ∈ s, f i := by
  classical
  revert f
  refine Finset.induction_on s ?_ (fun a s has ih => ?_)
  · intro f hf
    simp
  · intro f hf
    rw [Finset.prod_insert has]
    have hfa : (1 : ℝ) ≤ f a := hf a (Finset.mem_insert_self a s)
    have hrest : (1 : ℝ) ≤ ∏ i ∈ s, f i := by
      exact ih f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hfa0 : 0 ≤ f a := le_trans zero_le_one hfa
    have hmain : f a * 1 ≤ f a * (∏ i ∈ s, f i) := mul_le_mul_of_nonneg_left hrest hfa0
    calc
      (1 : ℝ) ≤ f a := hfa
      _ = f a * 1 := by ring
      _ ≤ f a * (∏ i ∈ s, f i) := hmain

/-- Under the hypotheses `covolume = 1` and `λ₁ ≥ 1`, the top successive minimum is bounded
by `2^{2m}/vol(B₁)`. -/
lemma lambda_m_bound {m : ℕ} (hm : 0 < m) (L : Submodule ℤ (EuBB m)) [DiscreteTopology L]
    [IsZLattice ℝ L] (hcov : ZLattice.covolume L = 1)
    (hmin : ∀ v : L, v ≠ 0 → 1 ≤ ‖(v : EuBB m)‖) :
    Commons.Lattice.SuccessiveMinima.successiveMinimum L m ≤
      (2 : ℝ) ^ (2 * m) / (volume (Metric.closedBall (0 : EuBB m) 1)).toReal := by
  classical
  haveI : Nontrivial (EuBB m) := by
    refine ⟨⟨(EuclideanSpace.basisFun (Fin m) ℝ) ⟨0, hm⟩, 0, ?_⟩⟩
    intro hz
    have hnz : ‖(EuclideanSpace.basisFun (Fin m) ℝ) ⟨0, hm⟩‖ ≠ 0 := by
      rw [(EuclideanSpace.basisFun (Fin m) ℝ).orthonormal.1 ⟨0, hm⟩]
      norm_num
    exact hnz (by rw [hz, norm_zero])
  let V : ℝ := (volume (Metric.closedBall (0 : EuBB m) 1)).toReal
  have hV : 0 < V := vol_unit_ball_pos hm
  have hprod := minkowski_second_upper (d := m) (hd := hm) (E := EuBB m) L (finrank_lattice_euclid L)
  have hprod' : (∏ i : Fin m, Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑i + 1)) * V ≤
      (2 : ℝ) ^ (2 * m) := by
    simpa [hcov] using hprod
  have hlam_ge : ∀ i : Fin m, (1 : ℝ) ≤
      Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑i + 1) := by
    intro i
    have hi_le : (i.val + 1) ≤ Module.finrank ℤ L := by
      rw [finrank_lattice_euclid L]
      omega
    exact Commons.Lattice.SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge L (1 : ℝ)
      (by omega)
      (Commons.Lattice.SuccessiveMinima.nonempty_successiveMinimumSet L (i.val + 1) hi_le) hmin
  have hlast : m - 1 < m := by omega
  let ilast : Fin m := ⟨m - 1, hlast⟩
  have hival : ilast.val + 1 = m := by
    simp [ilast]
    omega
  have hterm_le : Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑ilast + 1) ≤
      ∏ i : Fin m, Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑i + 1) := by
    have hsplit : (∏ i : Fin m, Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑i + 1)) =
        Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑ilast + 1) *
          ∏ i ∈ Finset.univ.erase ilast, Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑i + 1) := by
      rw [← Finset.prod_erase_mul Finset.univ
        (fun i : Fin m => Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑i + 1))
        (Finset.mem_univ ilast)]
      exact mul_comm _ _
    rw [hsplit]
    have hothers : (1 : ℝ) ≤ ∏ i ∈ Finset.univ.erase ilast,
        Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑i + 1) := by
      exact prod_ge_one_of_ge_one (Finset.univ.erase ilast)
        (fun i : Fin m => Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑i + 1)) (by
          intro i hi
          exact hlam_ge i)
    have hlam0 : 0 ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑ilast + 1) :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1) (hlam_ge ilast)
    nlinarith
  have hpr_ge : Commons.Lattice.SuccessiveMinima.successiveMinimum L m ≤
      ∏ i : Fin m, Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑i + 1) := by
    have heq : Commons.Lattice.SuccessiveMinima.successiveMinimum L m =
        Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑ilast + 1) := by
      exact (congrArg (Commons.Lattice.SuccessiveMinima.successiveMinimum L) hival).symm
    rw [heq]
    exact hterm_le
  have hmul : Commons.Lattice.SuccessiveMinima.successiveMinimum L m * V ≤ (2 : ℝ) ^ (2 * m) := by
    calc
      Commons.Lattice.SuccessiveMinima.successiveMinimum L m * V ≤
          (∏ i : Fin m, Commons.Lattice.SuccessiveMinima.successiveMinimum L (↑i + 1)) * V := by
        exact mul_le_mul_of_nonneg_right hpr_ge (le_of_lt hV)
      _ ≤ (2 : ℝ) ^ (2 * m) := hprod'
  exact (le_div_iff₀ hV).2 hmul

end BoundLambda

-- =====================================================================
-- Part 2 : orthogonal projection helpers (finite-dimensional inner product spaces)
-- =====================================================================

section ProjectionHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Orthogonal projection onto `Sᗮ` kills elements of `S`. -/
lemma proj_orth_eq_zero_of_mem' (S : Submodule ℝ E) {x : E} (hx : x ∈ S) :
    (Submodule.orthogonal S).starProjection x = 0 := by
  classical
  have hx' : x ∈ (Submodule.orthogonal S)ᗮ := by
    intro w hw
    exact (inner_eq_zero_symm.mp ((Submodule.mem_orthogonal (K := S) w).mp hw x hx))
  have hzero : (0 : E) ∈ (Submodule.orthogonal S) := Submodule.zero_mem _
  exact Submodule.eq_starProjection_of_mem_orthogonal (K := (Submodule.orthogonal S)) (u := x) (v := 0) hzero (by
    simpa using hx')

/-- If orthogonal projection onto `Sᗮ` kills `x`, then `x ∈ S`. -/
lemma mem_of_proj_orth_eq_zero' (S : Submodule ℝ E) {x : E}
    (hx : (Submodule.orthogonal S).starProjection x = 0) : x ∈ S := by
  classical
  have hdec : x = S.starProjection x + (Submodule.orthogonal S).starProjection x := by
    have h : (Submodule.orthogonal S).starProjection x = x - S.starProjection x := by
      rw [Submodule.starProjection_orthogonal' S]
      rfl
    rw [h]
    abel
  rw [hdec, hx, add_zero]
  exact Submodule.starProjection_apply_mem S x

end ProjectionHelpers

end Commons.Lattice.Minkowski

-- =====================================================================
-- Part 3 : flag geometry (rounding in the realiser basis of the ambient space)
-- =====================================================================

namespace Commons.Lattice.Minkowski

section FlagGeometry

open flagBasis

variable {m : ℕ} (L : Submodule ℤ (EuBB m)) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The full realiser family is an `ℝ`-basis of the ambient space. -/
noncomputable def RealBasis (v : Fin m → L) (hv : LinearIndependent ℝ (fun j : Fin m => (v j : EuBB m)))
    (hfin : Module.finrank ℤ L = m) : Module.Basis (Fin m) ℝ (EuBB m) := by
  classical
  have hfinE : Module.finrank ℝ (EuBB m) = m := finrank_euclid m
  have hcard : Fintype.card (Fin m) = Module.finrank ℝ (EuBB m) := by
    simp [hfinE]
  exact basisOfLinearIndependentOfCardEqFinrank' (b := fun j : Fin m => (v j : EuBB m)) hv hcard

/-- The realiser basis vector at `j` is the realiser `v j`. -/
lemma RealBasis_apply (v : Fin m → L) (hv : LinearIndependent ℝ (fun j : Fin m => (v j : EuBB m)))
    (hfin : Module.finrank ℤ L = m) (j : Fin m) :
    (RealBasis L v hv hfin j : EuBB m) = (v j : EuBB m) := by
  classical
  simp [RealBasis]

/-- The coordinates (in a basis `b`) of an element of the span of the first `t` basis
vectors vanish beyond index `t`. -/
lemma repr_prefix_zero (b : Module.Basis (Fin m) ℝ (EuBB m)) {t : ℕ} (ht : t ≤ m)
    {x : EuBB m}
    (hx : x ∈ Submodule.span ℝ (Set.range (fun i : Fin t => (b (Fin.castLE ht i)))))
    {j : Fin m} (hj : t ≤ j.val) : b.repr x j = 0 := by
  classical
  let fam : Fin t → EuBB m := fun i => (b (Fin.castLE ht i))
  have hxrange : x ∈ (Finsupp.linearCombination ℝ fam).range := by
    simpa [fam, Finsupp.range_linearCombination] using hx
  rcases hxrange with ⟨l, hl⟩
  have hrep : b.repr x = ∑ i : Fin t, l i • Finsupp.single (Fin.castLE ht i) (1 : ℝ) := by
    calc
      b.repr x = b.repr (Finsupp.linearCombination ℝ fam l) := by rw [hl]
      _ = b.repr (∑ i : Fin t, l i • b (Fin.castLE ht i)) := by
        simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype, fam]
      _ = ∑ i : Fin t, l i • Finsupp.single (Fin.castLE ht i) (1 : ℝ) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, Module.Basis.repr_self]
  rw [hrep]
  simp
  apply Finset.sum_eq_zero
  intro i hi
  have hneq : Fin.castLE ht i ≠ j := by
    intro h
    have hval : i.val = j.val := congrArg Fin.val h
    omega
  exact Finsupp.single_eq_of_ne (α := Fin m) hneq.symm

/-- Coordinates (realiser basis) of an element of `W t` vanish beyond index `t`. -/
lemma coord_zero_outside (v : Fin m → L) (hv : LinearIndependent ℝ (fun j : Fin m => (v j : EuBB m)))
    (hfin : Module.finrank ℤ L = m) {t : ℕ} (ht : t ≤ m)
    {x : EuBB m} (hx : x ∈ W L m v t ht) {j : Fin m} (hj : t ≤ j.val) :
    (RealBasis L v hv hfin).repr x j = 0 := by
  classical
  let b := RealBasis L v hv hfin
  have hx' : x ∈ Submodule.span ℝ (Set.range (fun i : Fin t => (b (Fin.castLE ht i)))) := by
    have hW : W L m v t ht = Submodule.span ℝ (Set.range (fun i : Fin t => (v (Fin.castLE ht i) : EuBB m))) := rfl
    have hxW : x ∈ Submodule.span ℝ (Set.range (fun i : Fin t => (v (Fin.castLE ht i) : EuBB m))) := by
      simpa [hW] using hx
    simpa [b, RealBasis_apply] using hxW
  exact repr_prefix_zero b ht hx' hj

/-- The nearest integer to `a` (distance ≤ 1/2). -/
def roundz (a : ℝ) : ℤ := Int.floor (a + 1 / 2)

lemma roundz_zero : roundz 0 = 0 := by
  norm_num [roundz]

lemma roundz_dist (a : ℝ) : |a - (roundz a : ℝ)| ≤ 1 / 2 := by
  let n : ℤ := Int.floor (a + 1 / 2)
  have h1 : (n : ℝ) ≤ a + 1 / 2 := by
    simpa [n] using (Int.floor_le (a + 1 / 2))
  have h2 : a + 1 / 2 < (n : ℝ) + 1 := by
    simpa [n] using (Int.lt_floor_add_one (a + 1 / 2))
  have hn : (roundz a : ℝ) = (n : ℝ) := by simp [roundz, n]
  rw [abs_le]
  constructor <;> linarith

/-- Rounding an ambient point `x ∈ W t` to a lattice point of `Q t`. -/
noncomputable def roundNear (v : Fin m → L) (hv : LinearIndependent ℝ (fun j : Fin m => (v j : EuBB m)))
    (hfin : Module.finrank ℤ L = m) {t : ℕ} (ht : t ≤ m) (x : EuBB m) (hx : x ∈ W L m v t ht) :
    ↥(Q L m v t ht) := by
  classical
  let b := RealBasis L v hv hfin
  let n : Fin m → ℤ := fun j => if h : j.val < t then roundz ((b.repr x) j) else 0
  let qE : EuBB m := ∑ j : Fin m, (n j : ℤ) • (v j : EuBB m)
  have hqL : qE ∈ L := by
    have hmem : ∀ j : Fin m, (n j : ℤ) • (v j : EuBB m) ∈ L := by
      intro j
      exact L.smul_mem (n j) ((v j : L).2)
    exact Submodule.sum_mem L (fun j hj => hmem j)
  have hqW : qE ∈ W L m v t ht := by
    apply Submodule.sum_mem (W L m v t ht)
    intro j hj
    by_cases hlt : j.val < t
    · have hvjW : (v j : EuBB m) ∈ W L m v t ht := by
        apply subset_span
        exact ⟨⟨j.val, hlt⟩, by simp⟩
      have hmem : (n j : ℤ) • (v j : EuBB m) ∈ W L m v t ht := by
        rw [← Int.cast_smul_eq_zsmul ℝ (n j) (v j : EuBB m)]
        exact (W L m v t ht).smul_mem ((n j : ℤ) : ℝ) hvjW
      simpa [n, hlt] using hmem
    · have hnz : n j = 0 := by simp [n, hlt]
      have hzero : (n j : ℤ) • (v j : EuBB m) = 0 := by simp [hnz]
      simp [hzero]
  exact ⟨qE, Submodule.mem_inf.mpr ⟨hqL, hqW⟩⟩

/-- The rounding bound: `‖x - roundNear x‖ ≤ (t/2)·R` when all realisers have norm ≤ R
and `x ∈ W t`. -/
lemma roundNear_dist (v : Fin m → L) (hv : LinearIndependent ℝ (fun j : Fin m => (v j : EuBB m)))
    (hfin : Module.finrank ℤ L = m) {t : ℕ} (ht : t ≤ m) (x : EuBB m) (hx : x ∈ W L m v t ht)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ j : Fin m, ‖(v j : EuBB m)‖ ≤ R) :
    ‖x - ((roundNear L v hv hfin ht x hx : ↥(Q L m v t ht)) : EuBB m)‖ ≤ (t : ℝ) * R / 2 := by
  classical
  let b := RealBasis L v hv hfin
  let n : Fin m → ℤ := fun j => if h : j.val < t then roundz ((b.repr x) j) else 0
  have hqE : ((roundNear L v hv hfin ht x hx : ↥(Q L m v t ht)) : EuBB m) =
      ∑ j : Fin m, ((n j : ℤ) : ℝ) • (v j : EuBB m) := by
    simp [roundNear, b, n]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hlt : j.val < t
    · simp [hlt]
      exact (Int.cast_smul_eq_zsmul ℝ (roundz ((b.repr x) j)) (v j : EuBB m)).symm
    · simp [hlt]
  have hxexp : x = ∑ j : Fin m, (b.repr x) j • (b j : EuBB m) := by
    simpa using (Module.Basis.sum_repr b x).symm
  have hqE' : ((roundNear L v hv hfin ht x hx : ↥(Q L m v t ht)) : EuBB m) =
      ∑ j : Fin m, ((n j : ℤ) : ℝ) • (b j : EuBB m) := by
    rw [hqE]
    apply Finset.sum_congr rfl
    intro j hj
    rw [RealBasis_apply L v hv hfin j]
  have hsum : x - ((roundNear L v hv hfin ht x hx : ↥(Q L m v t ht)) : EuBB m) =
      ∑ j : Fin m, ((b.repr x) j - ((n j : ℤ) : ℝ)) • (b j : EuBB m) := by
    have h1 : x - ((roundNear L v hv hfin ht x hx : ↥(Q L m v t ht)) : EuBB m) =
        (∑ j : Fin m, (b.repr x) j • (b j : EuBB m)) -
          ((roundNear L v hv hfin ht x hx : ↥(Q L m v t ht)) : EuBB m) := by
      exact congrArg (fun z : EuBB m => z - ((roundNear L v hv hfin ht x hx : ↥(Q L m v t ht)) : EuBB m)) hxexp
    have h2 : (∑ j : Fin m, (b.repr x) j • (b j : EuBB m)) -
          ((roundNear L v hv hfin ht x hx : ↥(Q L m v t ht)) : EuBB m) =
        (∑ j : Fin m, (b.repr x) j • (b j : EuBB m)) -
          (∑ j : Fin m, ((n j : ℤ) : ℝ) • (b j : EuBB m)) := by
      exact congrArg (fun z : EuBB m => (∑ j : Fin m, (b.repr x) j • (b j : EuBB m)) - z) hqE'
    calc
      x - ((roundNear L v hv hfin ht x hx : ↥(Q L m v t ht)) : EuBB m)
          = (∑ j : Fin m, (b.repr x) j • (b j : EuBB m)) -
              ((roundNear L v hv hfin ht x hx : ↥(Q L m v t ht)) : EuBB m) := h1
      _ = (∑ j : Fin m, (b.repr x) j • (b j : EuBB m)) -
              (∑ j : Fin m, ((n j : ℤ) : ℝ) • (b j : EuBB m)) := h2
      _ = ∑ j : Fin m, ((b.repr x) j • (b j : EuBB m) -
              ((n j : ℤ) : ℝ) • (b j : EuBB m)) := by
              rw [← Finset.sum_sub_distrib]
      _ = ∑ j : Fin m, ((b.repr x) j - ((n j : ℤ) : ℝ)) • (b j : EuBB m) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [sub_smul]
  have hnorm_sum : (∑ j : Fin m, |(b.repr x) j - ((n j : ℤ) : ℝ)| * ‖(b j : EuBB m)‖) ≤
      (t : ℝ) * R / 2 := by
    have hstep : (∑ j : Fin m, |(b.repr x) j - ((n j : ℤ) : ℝ)| * ‖(b j : EuBB m)‖) ≤
        ∑ j : Fin m, (if j.val < t then (1 / 2) * R else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hlt : j.val < t
      · have hrd : |(b.repr x) j - ((n j : ℤ) : ℝ)| ≤ 1 / 2 := by
          have hn : (n j : ℤ) = roundz ((b.repr x) j) := by simp [n, hlt]
          simpa [hn] using (roundz_dist ((b.repr x) j))
        have hnormv : ‖(b j : EuBB m)‖ = ‖(v j : EuBB m)‖ := by rw [RealBasis_apply L v hv hfin j]
        have h1 : |(b.repr x) j - ((n j : ℤ) : ℝ)| * ‖(b j : EuBB m)‖ ≤ (1 / 2) * R := by
          rw [hnormv]
          calc
            |(b.repr x) j - ((n j : ℤ) : ℝ)| * ‖(v j : EuBB m)‖ ≤ (1 / 2) * ‖(v j : EuBB m)‖ := by
              exact mul_le_mul_of_nonneg_right hrd (norm_nonneg (v j : EuBB m))
            _ ≤ (1 / 2) * R := by
              exact mul_le_mul_of_nonneg_left (hR j) (by norm_num)
        simpa [hlt] using h1
      · have hnz : n j = 0 := by simp [n, hlt]
        have hα : (b.repr x) j = 0 := coord_zero_outside L v hv hfin ht hx (le_of_not_gt hlt)
        simp [hnz, hα, hlt]
    have hcnt : ((Finset.univ : Finset (Fin m)).filter (fun j : Fin m => j.val < t)).card = t := by
      let f : Fin t → Fin m := fun i => Fin.castLE ht i
      have hfinj : Function.Injective f := Fin.castLE_injective ht
      have hF : (Finset.univ.filter (fun j : Fin m => j.val < t)) =
          (Finset.univ : Finset (Fin t)).map ⟨f, hfinj⟩ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Finset.mem_map]
        constructor
        · intro hj
          refine ⟨⟨j.val, hj⟩, by simp, ?_⟩
          apply Fin.ext
          simp [f]
        · intro h
          rcases h with ⟨i, _hin, hg⟩
          rw [← hg]
          exact i.isLt
      rw [hF]
      simp
    have hcntsum : (∑ j : Fin m, (if j.val < t then (1 / 2) * R else 0)) = (t : ℝ) * R / 2 := by
      calc
        (∑ j : Fin m, (if j.val < t then (1 / 2) * R else 0))
            = ((1 / 2) * R) * (∑ j : Fin m, (if j.val < t then (1 : ℝ) else 0)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                by_cases h : j.val < t <;> simp [h] <;> ring
        _ = ((1 / 2) * R) * (t : ℝ) := by
                congr 1
                calc
                  (∑ j : Fin m, (if j.val < t then (1 : ℝ) else 0))
                      = ((Finset.univ.filter (fun j : Fin m => j.val < t)).card : ℝ) := by
                          rw [Finset.sum_boole]
                  _ = (t : ℝ) := by exact_mod_cast hcnt
        _ = (t : ℝ) * R / 2 := by ring
    exact le_trans hstep (le_of_eq hcntsum)

  calc
    ‖x - ((roundNear L v hv hfin ht x hx : ↥(Q L m v t ht)) : EuBB m)‖
        ≤ ∑ j : Fin m, ‖(((b.repr x) j - ((n j : ℤ) : ℝ)) • (b j : EuBB m))‖ := by
          rw [hsum]
          exact norm_sum_le _ _
    _ = ∑ j : Fin m, |(b.repr x) j - ((n j : ℤ) : ℝ)| * ‖(b j : EuBB m)‖ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [norm_smul, Real.norm_eq_abs]
    _ ≤ (t : ℝ) * R / 2 := hnorm_sum

end FlagGeometry


-- =====================================================================

-- =====================================================================
-- Main theorem: a bounded basis for covolume-one lattices of minimum ≥ 1
-- =====================================================================

theorem bounded_basis_covolume_one :
    ∀ (m : ℕ), ∃ C : ℝ,
      ∀ (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) [DiscreteTopology ℒ],
        IsZLattice ℝ ℒ → ZLattice.covolume ℒ = 1 →
        (∀ v : ℒ, v ≠ 0 → 1 ≤ ‖(v : EuclideanSpace ℝ (Fin m))‖) →
        ∃ b : Module.Basis (Fin m) ℤ ℒ,
          ∀ i : Fin m, ‖((b i : ℒ) : EuclideanSpace ℝ (Fin m))‖ ≤ C := by
  intro m
  by_cases hm0 : m = 0
  · -- m = 0 : the empty basis works, constant 0
    refine ⟨0, ?_⟩
    subst m
    intro ℒ hDT hℒ hcov hmin
    classical
    haveI : IsZLattice ℝ ℒ := hℒ
    have hfin : Module.finrank ℤ ℒ = 0 := by
      simpa using (finrank_lattice_euclid ℒ)
    let v : Fin 0 → ℒ := fun j => Fin.elim0 j
    have hv : LinearIndependent ℝ (fun j : Fin 0 => (v j : EuclideanSpace ℝ (Fin 0))) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      exact Fin.elim0 i
    obtain ⟨b, hb⟩ := bounded_basis_of_bounded_realizers ℒ hfin v hv 0 (by norm_num) (by
      intro j
      exact Fin.elim0 j)
    refine ⟨b, ?_⟩
    intro i
    simpa using (hb i)
  · -- m ≥ 1
    have hm : 0 < m := Nat.pos_of_ne_zero hm0
    let vol : ℝ := (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal
    let A : ℝ := (2 : ℝ) ^ (2 * m) / vol
    refine ⟨(2 * (m : ℝ) + 1) * A, ?_⟩
    intro ℒ hDT hℒ hcov hmin
    classical
    haveI : IsZLattice ℝ ℒ := hℒ
    have hfin : Module.finrank ℤ ℒ = m := finrank_lattice_euclid ℒ
    have hA0 : 0 ≤ A := by
      dsimp [A, vol]
      exact div_nonneg (pow_nonneg (by norm_num) _) (le_of_lt (vol_unit_ball_pos hm))
    have hA_lambda : Commons.Lattice.SuccessiveMinima.successiveMinimum ℒ m ≤ A := by
      dsimp [A, vol]
      exact lambda_m_bound hm ℒ hcov hmin
    obtain ⟨v, hv, hvl⟩ := Commons.Lattice.SuccessiveMinima.exact_realization
      (E := EuclideanSpace ℝ (Fin m)) ℒ m hfin
    have hvA : ∀ j : Fin m, ‖(v j : EuclideanSpace ℝ (Fin m))‖ ≤ A := by
      intro j
      have hmono : Commons.Lattice.SuccessiveMinima.successiveMinimum ℒ (j.val + 1) ≤
          Commons.Lattice.SuccessiveMinima.successiveMinimum ℒ m := by
        exact Commons.Lattice.SuccessiveMinima.successiveMinimum_mono ℒ (by omega)
          (by simpa [hfin])
      exact le_trans (le_trans (hvl j) hmono) hA_lambda
    obtain ⟨b, hb⟩ := bounded_basis_of_bounded_realizers ℒ hfin v hv A hA0 hvA
    refine ⟨b, ?_⟩
    intro i
    exact hb i

end Commons.Lattice.Minkowski
