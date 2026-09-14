import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Lattice.Minkowski.flag_basis
import Submission.Commons.Lattice.Module.basis_extension_pure_rank

open Module MeasureTheory Metric Set Submodule
open scoped ENNReal BigOperators
noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Commons.Lattice.Minkowski

open flagBasis

/-! # A bounded `ℤ`-basis from bounded realisers

The theorem of this module (`bounded_basis_of_bounded_realizers`) states that if a full-rank
`ℤ`-lattice `ℒ ≤ EuclideanSpace ℝ (Fin m)` admits `m` real-valued (`ℝ`-linearly independent)
realisers `v₁,…,vₘ ∈ ℒ` of norm at most `R`, then `ℒ` has a `ℤ`-basis whose vectors all have
norm at most `(2m+1)·R`.

Strategy (flag extension with rounding).  Work along the flag
`W_t := span(v₁,…,v_t)`, `Q_t := ℒ ∩ W_t`.
- For `t = 0`, `Q₀ = {0}` admits the empty basis.
- Extension `Q_t ↦ Q_{t+1}`: choose a basis-extension generator `x` of `Q_{t+1}` over `Q_t`
  (`basis_extension_pure_rank`, purity by `pure_Q`); write `x = y + z` with `y ∈ W_t` and
  `z ∈ W_tᗮ`.  Round `y` to a lattice point `c ∈ Q_t` (in the realiser basis of `W_t`), so
  `‖y - c‖ ≤ tR/2`; the new generator is `g := x - c`, whose `W_tᗮ`-part is `z`, and since
  `v_{t+1}` is an integral multiple of `z` in the projection (with multiplier `≥ 1` in absolute
  value), `‖z‖ ≤ ‖v_{t+1}‖ ≤ R`.  Hence `‖g‖ ≤ (t+1)R`.
- Induction gives a basis of `Q_m = ℒ` with all norms `≤ m·R ≤ (2m+1)·R`.
-/

namespace bbbr

/-- The ambient space `ℝ^m` for the lattice. -/
abbrev EuBB (m : ℕ) := EuclideanSpace ℝ (Fin m)

-- =====================================================================
-- Part 1 : ambient helpers
-- =====================================================================

lemma finrank_euclid (m : ℕ) : Module.finrank ℝ (EuBB m) = m := by
  have hb : Module.Basis (Fin m) ℝ (EuBB m) := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  rw [Module.finrank_eq_card_basis hb]
  simp

lemma finrank_lattice_euclid {m : ℕ} (L : Submodule ℤ (EuBB m)) [DiscreteTopology L]
    [IsZLattice ℝ L] : Module.finrank ℤ L = m := by
  rw [ZLattice.rank ℝ L, finrank_euclid]

-- =====================================================================
-- Part 2 : orthogonal projection helpers (finite-dimensional inner product spaces)
-- =====================================================================

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


-- =====================================================================
-- Part 3 : flag geometry (rounding in the realiser basis of the ambient space)
-- =====================================================================

section FlagGeometry

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
-- Part 3b : coordinate lemmas over ℤ
-- =====================================================================

section IntCoordinates

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- Evaluating a finite sum of finitely-supported functions at an index distributes. -/
lemma finsupp_sum_apply (ι : Type*) [Fintype ι] (n : ℕ) (f : ι → (Fin n →₀ ℤ)) (j : Fin n) :
    (∑ i : ι, f i) j = ∑ i : ι, f i j := by
  classical
  let ℓ : (Fin n →₀ ℤ) →ₗ[ℤ] ℤ := Finsupp.lapply j
  rw [show (∑ i : ι, f i) j = ℓ (∑ i : ι, f i) by rfl]
  rw [map_sum]
  rfl

/-- The coordinate at the last index of an element of the span of the first `n` basis vectors
(of a basis indexed by `Fin (n+1)`) vanishes. -/
lemma repr_last_eq_zero_of_mem_prefixSpan {n : ℕ} (b : Module.Basis (Fin (n+1)) ℤ M) {q : M}
    (hq : q ∈ Submodule.span ℤ (Set.range (fun i : Fin n => (b (Fin.castSucc i))))) :
    (b.repr q) (Fin.last n) = 0 := by
  classical
  let ell : M →ₗ[ℤ] ℤ := {
    toFun := fun x => (b.repr x) (Fin.last n)
    map_add' := by intro x y; simp [Finsupp.add_apply]
    map_smul' := by intro c x; simp [Finsupp.smul_apply] }
  have hgen : Set.range (fun i : Fin n => (b (Fin.castSucc i))) ⊆ ell.ker := by
    intro y hy
    rcases hy with ⟨i, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hneq : Fin.castSucc i ≠ Fin.last n := by
      intro h
      have hlt : (Fin.castSucc i).val < (Fin.last n).val := by simpa using i.isLt
      exact (ne_of_lt hlt) (congrArg Fin.val h)
    simp [ell, Module.Basis.repr_self, hneq]
  have hker : q ∈ ell.ker := (Submodule.span_le.mpr hgen) hq
  simpa [ell] using (LinearMap.mem_ker.mp hker)


end IntCoordinates









-- =====================================================================
-- Part 4 : the flag extension step
-- =====================================================================

section Extension

variable {m : ℕ} (L : Submodule ℤ (EuBB m)) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The `t`-th realiser does not lie in the span of the first `t` realisers. -/
lemma realizer_notin_prefix (v : Fin m → L) (hv : LinearIndependent ℝ (fun j : Fin m => (v j : EuBB m)))
    (hfin : Module.finrank ℤ L = m) {t : ℕ} (ht : t ≤ m) (ht' : t + 1 ≤ m) :
    (v ⟨t, by omega⟩ : EuBB m) ∉ W L m v t ht := by
  classical
  intro hmem
  have hlt : t < m := by omega
  have hmem' : (v ⟨t, hlt⟩ : EuBB m) ∈ W L m v t ht := by simpa using hmem
  have h0 : (RealBasis L v hv hfin).repr (v ⟨t, hlt⟩ : EuBB m) ⟨t, hlt⟩ = 0 := by
    simpa using coord_zero_outside L v hv hfin ht hmem' (le_refl t)
  have h1 : (RealBasis L v hv hfin).repr (v ⟨t, hlt⟩ : EuBB m) ⟨t, hlt⟩ = 1 := by
    have hb : (RealBasis L v hv hfin).repr (RealBasis L v hv hfin ⟨t, hlt⟩) ⟨t, hlt⟩ = 1 := by
      rw [Module.Basis.repr_self]
      simp
    simpa [RealBasis_apply L v hv hfin ⟨t, hlt⟩] using hb
  linarith

end Extension


section Extension

variable {m : ℕ} (L : Submodule ℤ (EuBB m)) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The flag extension step: a bounded `ℤ`-basis of `Q t` gives a bounded `ℤ`-basis of `Q (t+1)`. -/
lemma extend_flag_basis
    (v : Fin m → L) (hv : LinearIndependent ℝ (fun j : Fin m => (v j : EuBB m)))
    (hfin : Module.finrank ℤ L = m) (R : ℝ) (hR0 : 0 ≤ R)
    (hvR : ∀ j : Fin m, ‖(v j : EuBB m)‖ ≤ R)
    {t : ℕ} (ht : t ≤ m) (ht' : t + 1 ≤ m)
    (β : Module.Basis (Fin t) ℤ ↥(Q L m v t ht))
    (hβ : ∀ i : Fin t, ‖((β i : ↥(Q L m v t ht)) : EuBB m)‖ ≤ (t : ℝ) * R) :
    ∃ γ : Module.Basis (Fin (t + 1)) ℤ ↥(Q L m v (t + 1) ht'),
      ∀ j : Fin (t + 1), ‖((γ j : ↥(Q L m v (t + 1) ht')) : EuBB m)‖ ≤ ((t : ℝ) + 1) * R := by
  classical
  let M := ↥(Q L m v (t + 1) ht')
  let N : Submodule ℤ M := (Q L m v t ht).comap ((Q L m v (t + 1) ht').subtype)
  let W0 : Submodule ℝ (EuBB m) := W L m v t ht
  have hle : Q L m v t ht ≤ Q L m v (t + 1) ht' := Q_mono L m v ht ht' (Nat.le_succ t)
  let eN : ↥N ≃ₗ[ℤ] ↥(Q L m v t ht) := Submodule.comapSubtypeEquivOfLe hle
  let bN : Module.Basis (Fin t) ℤ ↥N := β.map eN.symm
  let bM : Module.Basis (Fin (t + 1)) ℤ M := Q_basis L m v (t + 1) ht' hv
  haveI : Module.Free ℤ M := Module.Free.of_basis bM
  haveI : Module.Finite ℤ M := Module.Finite.of_basis bM
  haveI : Module.Free ℤ ↥N := Module.Free.of_basis bN
  haveI : Module.Finite ℤ ↥N := Module.Finite.of_basis bN
  have hpureN : ∀ x : M, (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ N) → x ∈ N := by
    intro x ha
    exact pure_Q L m v t ht ht' hle x ha
  obtain ⟨e, he⟩ := Commons.Lattice.Module.basis_extension_pure_rank
    (hd := Nat.le_succ t) (M := M) (N := N) bM bN hpureN
  let x : M := e (Fin.last t)
  have he' : ∀ i : Fin t, (e (Fin.castSucc i)) = ((bN i : ↥N) : M) := by
    intro i
    exact he i
  have hval_bN : ∀ i : Fin t, (((bN i : ↥N) : M) : EuBB m) = ((β i : ↥(Q L m v t ht)) : EuBB m) := by
    intro i
    dsimp [bN, eN]
    rw [Submodule.comapSubtypeEquivOfLe_symm_apply]
  have hN_ker : ∀ p : M, p ∈ N → (e.repr p) (Fin.last t) = 0 := by
    intro p hp
    have hpQ : ((p : M) : EuBB m) ∈ Q L m v t ht := by
      exact (Submodule.mem_comap.mp hp)
    let q0 : ↥(Q L m v t ht) := ⟨((p : M) : EuBB m), hpQ⟩
    have hp_eq : p = Submodule.inclusion hle q0 := by
      apply Subtype.ext
      rfl
    have hsumq : q0 = ∑ i : Fin t, (β.repr q0) i • (β i) := (Module.Basis.sum_repr β q0).symm
    have hinc : ∀ i : Fin t, Submodule.inclusion hle (β i) = ((bN i : ↥N) : M) := by
      intro i
      apply Subtype.ext
      change (((β i : ↥(Q L m v t ht)) : EuBB m)) = ((((bN i : ↥N) : M) : EuBB m))
      rw [hval_bN i]
    have hbvrepr : ∀ i : Fin t, e.repr (((bN i : ↥N) : M)) = Finsupp.single (Fin.castSucc i) (1 : ℤ) := by
      intro i
      rw [← he' i]
      rw [Module.Basis.repr_self]
    have hincl_sum : Submodule.inclusion hle q0 =
        ∑ i : Fin t, (β.repr q0) i • ((bN i : ↥N) : M) := by
      calc
        Submodule.inclusion hle q0
            = Submodule.inclusion hle (∑ i : Fin t, (β.repr q0) i • (β i)) := by
                conv_lhs => rw [hsumq]
        _ = ∑ i : Fin t, (β.repr q0) i • (Submodule.inclusion hle (β i)) := by
                rw [map_sum]
                apply Finset.sum_congr rfl
                intro i hi
                rw [map_smul]
        _ = ∑ i : Fin t, (β.repr q0) i • ((bN i : ↥N) : M) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [hinc i]
    have heval : (e.repr (∑ i : Fin t, (β.repr q0) i • ((bN i : ↥N) : M))) (Fin.last t) = 0 := by
      calc
        (e.repr (∑ i : Fin t, (β.repr q0) i • ((bN i : ↥N) : M))) (Fin.last t)
            = (∑ i : Fin t, (e.repr ((β.repr q0) i • ((bN i : ↥N) : M)))) (Fin.last t) := by
                rw [map_sum]
        _ = ∑ i : Fin t, (e.repr ((β.repr q0) i • ((bN i : ↥N) : M))) (Fin.last t) := by
                rw [finsupp_sum_apply]
        _ = ∑ i : Fin t, ((β.repr q0) i • Finsupp.single (Fin.castSucc i) (1 : ℤ)) (Fin.last t) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [map_smul]
                rw [hbvrepr i]
        _ = 0 := by
                apply Finset.sum_eq_zero
                intro i hi
                have hneq : Fin.castSucc i ≠ Fin.last t := by
                  intro h
                  have hlt : (Fin.castSucc i).val < (Fin.last t).val := by
                    simpa using i.isLt
                  exact (ne_of_lt hlt) (congrArg Fin.val h)
                simp [Finsupp.single_eq_of_ne hneq.symm, Finsupp.smul_apply]
    calc
      (e.repr p) (Fin.last t) = (e.repr (Submodule.inclusion hle q0)) (Fin.last t) := by
        rw [hp_eq]
      _ = (e.repr (∑ i : Fin t, (β.repr q0) i • ((bN i : ↥N) : M))) (Fin.last t) := by
        rw [hincl_sum]
      _ = 0 := heval
  have htlt : t < m := by omega
  let vtE : EuBB m := (v ⟨t, htlt⟩ : EuBB m)
  have heq_last : Fin.castLE ht' (Fin.last t) = ⟨t, htlt⟩ := by
    apply Fin.ext
    simp
  have hvtW : vtE ∈ W L m v (t + 1) ht' := by
    dsimp [vtE]
    have hgen : (v (Fin.castLE ht' (Fin.last t)) : EuBB m) ∈ W L m v (t + 1) ht' := by
      exact subset_span ⟨Fin.last t, rfl⟩
    simpa [heq_last] using hgen
  have hvtQ : vtE ∈ Q L m v (t + 1) ht' := by
    exact Submodule.mem_inf.mpr ⟨(v ⟨t, htlt⟩ : L).2, hvtW⟩
  let vtM : M := ⟨vtE, hvtQ⟩
  let z0 : ℤ := (e.repr vtM) (Fin.last t)
  have hrelN : ∀ q : M, q - (e.repr q) (Fin.last t) • x ∈ N := by
    intro q
    let z : ℤ := (e.repr q) (Fin.last t)
    have hqfull : q = ∑ j : Fin (t + 1), (e.repr q) j • (e j : M) :=
      (Module.Basis.sum_repr e q).symm
    have hsplit : (∑ j : Fin (t + 1), (e.repr q) j • (e j : M)) =
        (∑ i : Fin t, (e.repr q) (Fin.castSucc i) • (e (Fin.castSucc i))) + z • x := by
      rw [Fin.sum_univ_castSucc]
    have hblock : (∑ i : Fin t, (e.repr q) (Fin.castSucc i) • (e (Fin.castSucc i))) ∈ N := by
      apply N.sum_mem
      intro i hi
      exact N.smul_mem ((e.repr q) (Fin.castSucc i)) (by
        rw [he' i]
        exact (bN i).2)
    have heq : q - z • x =
        ∑ i : Fin t, (e.repr q) (Fin.castSucc i) • (e (Fin.castSucc i)) := by
      calc
        q - z • x
            = (∑ j : Fin (t + 1), (e.repr q) j • (e j : M)) - z • x := by
                conv_lhs => rw [hqfull]
        _ = ∑ i : Fin t, (e.repr q) (Fin.castSucc i) • (e (Fin.castSucc i)) := by
                rw [hsplit]
                abel
    rw [heq]
    exact hblock
  have hrelvtN : vtM - z0 • x ∈ N := by
    simpa [z0] using hrelN vtM
  have hz_ne : z0 ≠ 0 := by
    intro hz
    have hvtN : vtM ∈ N := by
      simpa [hz] using hrelvtN
    have hvtQ0 : vtE ∈ Q L m v t ht := by
      exact (Submodule.mem_comap.mp hvtN)
    have hvtW0 : vtE ∈ W L m v t ht := Q_mem_W L m v t ht hvtQ0
    exact realizer_notin_prefix L v hv hfin ht ht' (by simpa [vtE] using hvtW0)
  let π : EuBB m →ₗ[ℝ] EuBB m := (Submodule.orthogonal W0).starProjection
  have hvtW0' : vtE - (((z0 : ℤ) : ℝ) • (x : EuBB m)) ∈ W0 := by
    have hmem : ((vtM - z0 • x : M) : EuBB m) ∈ Q L m v t ht :=
      Submodule.mem_comap.mp hrelvtN
    have hconv : ((vtM - z0 • x : M) : EuBB m) = vtE - (((z0 : ℤ) : ℝ) • (x : EuBB m)) := by
      dsimp [vtM, vtE]
      rw [Int.cast_smul_eq_zsmul]
      rfl
    rw [hconv] at hmem
    exact Q_mem_W L m v t ht hmem
  have hπrel : π vtE = ((z0 : ℤ) : ℝ) • π (x : EuBB m) := by
    have hk : π (vtE - (((z0 : ℤ) : ℝ) • (x : EuBB m))) = 0 := by
      dsimp [π]
      exact proj_orth_eq_zero_of_mem' W0 hvtW0'
    have hlin : π vtE - π ((((z0 : ℤ) : ℝ) • (x : EuBB m))) = 0 := by
      simpa [map_sub] using hk
    have hsmul : π ((((z0 : ℤ) : ℝ) • (x : EuBB m))) = (((z0 : ℤ) : ℝ) • π (x : EuBB m)) := by
      simp [map_smul]
    rw [hsmul] at hlin
    exact eq_of_sub_eq_zero hlin
  have hπx_bound : ‖π (x : EuBB m)‖ ≤ R := by
    have hz1 : (1 : ℝ) ≤ |((z0 : ℤ) : ℝ)| := by
      have hzin : (1 : ℤ) ≤ |z0| := by
        have hnz : |z0| ≠ 0 := by
          intro hh
          apply hz_ne
          exact abs_eq_zero.mp hh
        have hz0n : 0 ≤ |z0| := abs_nonneg z0
        omega
      rw [← Int.cast_abs]
      exact_mod_cast hzin
    have hmain : ‖((z0 : ℤ) : ℝ) • π (x : EuBB m)‖ = ‖π (x : EuBB m)‖ * |((z0 : ℤ) : ℝ)| := by
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
    have h1 : ‖π (x : EuBB m)‖ ≤ ‖π vtE‖ := by
      have hx0 : 0 ≤ ‖π (x : EuBB m)‖ := norm_nonneg _
      calc
        ‖π (x : EuBB m)‖ = 1 * ‖π (x : EuBB m)‖ := by ring
        _ ≤ |((z0 : ℤ) : ℝ)| * ‖π (x : EuBB m)‖ := by
          exact mul_le_mul_of_nonneg_right hz1 hx0
        _ = ‖π vtE‖ := by
          rw [hπrel, hmain, mul_comm]
    exact le_trans h1 (by
      calc
        ‖π vtE‖ ≤ ‖vtE‖ := by
          dsimp [π]
          simpa using (Submodule.norm_starProjection_apply_le (K := (Submodule.orthogonal W0)) (v := vtE))
        _ ≤ R := by simpa [vtE] using (hvR ⟨t, htlt⟩))
  let yA : EuBB m := W0.starProjection (x : EuBB m)
  have hxA_mem : yA ∈ W0 := by simpa [yA] using (Submodule.starProjection_apply_mem W0 (x : EuBB m))
  let c0 : ↥(Q L m v t ht) := roundNear L v hv hfin ht yA hxA_mem
  have hc_bound : ‖yA - (c0 : EuBB m)‖ ≤ (t : ℝ) * R / 2 := by
    exact roundNear_dist L v hv hfin ht yA hxA_mem R hR0 hvR
  have hcQ1 : (c0 : EuBB m) ∈ Q L m v (t + 1) ht' := by
    exact Q_mono L m v ht ht' (Nat.le_succ t) c0.2
  let nc : M := ⟨(c0 : EuBB m), hcQ1⟩
  have hncN : nc ∈ N := by
    dsimp [nc]
    apply Submodule.mem_comap.mpr
    exact c0.2
  let g : M := x - nc
  have hx_eq2 : x = g + nc := by
    dsimp [g]
    abel
  have hxy : (x : EuBB m) - yA = π (x : EuBB m) := by
    dsimp [π, yA]
    exact (Submodule.starProjection_orthogonal_val (K := W0) (u := (x : EuBB m))).symm
  have hxdec : (x : EuBB m) = yA + π (x : EuBB m) := by
    calc
      (x : EuBB m) = ((x : EuBB m) - yA) + yA := by abel
      _ = π (x : EuBB m) + yA := by rw [hxy]
      _ = yA + π (x : EuBB m) := by abel
  have hvalg : (g : EuBB m) = π (x : EuBB m) + (yA - (c0 : EuBB m)) := by
    dsimp [g]
    calc
      (x : EuBB m) - (c0 : EuBB m) = (yA + π (x : EuBB m)) - (c0 : EuBB m) := by
        conv_lhs => rw [hxdec]
      _ = π (x : EuBB m) + (yA - (c0 : EuBB m)) := by abel
  have hg_bound : ‖(g : EuBB m)‖ ≤ ((t : ℝ) + 1) * R := by
    calc
      ‖(g : EuBB m)‖ ≤ ‖π (x : EuBB m)‖ + ‖yA - (c0 : EuBB m)‖ := by
        rw [hvalg]
        exact norm_add_le _ _
      _ ≤ R + (t : ℝ) * R / 2 := by
        exact add_le_add hπx_bound hc_bound
      _ ≤ ((t : ℝ) + 1) * R := by
        have htR : 0 ≤ (t : ℝ) * R := mul_nonneg (by positivity) hR0
        nlinarith
  have hg_gen : ∀ q : M, ∃ c : ℤ, q + c • g ∈ N := by
    intro q
    let z : ℤ := (e.repr q) (Fin.last t)
    have hmain : q - z • g ∈ N := by
      have h' : q - z • (g + nc) ∈ N := by
        have hq := hrelN q
        rwa [hx_eq2] at hq
      have heq : q - z • g = (q - z • (g + nc)) + z • nc := by
        rw [smul_add]
        abel
      rw [heq]
      exact N.add_mem h' (N.smul_mem z hncN)
    refine ⟨-z, ?_⟩
    simpa [smul_neg, sub_eq_add_neg] using hmain
  have hli : ∀ (c : ℤ), ∀ x' ∈ N, c • g + x' = 0 → c = 0 := by
    intro c0 x' hx' h0
    have hcgN : c0 • g ∈ N := by
      have : c0 • g = -x' := by
        exact eq_neg_of_add_eq_zero_left h0
      rw [this]
      exact N.neg_mem hx'
    have hcxN : c0 • x ∈ N := by
      have h : c0 • x = c0 • g + c0 • nc := by
        rw [hx_eq2, smul_add]
      rw [h]
      exact N.add_mem hcgN (N.smul_mem c0 hncN)
    have hz : (e.repr (c0 • x)) (Fin.last t) = 0 := hN_ker (c0 • x) hcxN
    have hval : (e.repr (c0 • x)) (Fin.last t) = c0 := by
      simp [x]
    exact (hz.symm.trans hval).symm
  let γ : Module.Basis (Fin (t + 1)) ℤ M := bN.mkFinSnoc g hli hg_gen
  have hγ_coe : (γ : Fin (t + 1) → M) = Fin.snoc (fun i : Fin t => ((bN i : ↥N) : M)) g := by
    exact Module.Basis.coe_mkFinSnoc (b := bN) (y := g) (hli := hli) (hsp := hg_gen)
  refine ⟨γ, ?_⟩
  intro j
  by_cases hj : j.val < t
  · let i : Fin t := ⟨j.val, hj⟩
    have hji : j = i.castSucc := by
      apply Fin.ext
      simp [i]
    have hγj : (γ j : M) = ((bN i : ↥N) : M) := by
      rw [hγ_coe]
      rw [hji]
      simp
    have hb : ‖(((bN i : ↥N) : M) : EuBB m)‖ ≤ (t : ℝ) * R := by
      rw [hval_bN i]
      exact hβ i
    have hb' : ‖((γ j : M) : EuBB m)‖ ≤ (t : ℝ) * R := by
      rw [hγj]
      simpa using hb
    have htR : 0 ≤ (t : ℝ) * R := mul_nonneg (by positivity) hR0
    nlinarith
  · have hjlast : j = Fin.last t := by
      apply Fin.ext
      simp
      omega
    have hγl : γ (Fin.last t) = g := by
      rw [hγ_coe]
      simp
    rw [hjlast]
    rw [hγl]
    simpa using hg_bound

/-- Chain of bounded `ℤ`-bases along the flag `Q t` (`t·R` bound). -/
lemma bounded_chain
    (v : Fin m → L) (hv : LinearIndependent ℝ (fun j : Fin m => (v j : EuBB m)))
    (hfin : Module.finrank ℤ L = m) (R : ℝ) (hR0 : 0 ≤ R)
    (hvR : ∀ j : Fin m, ‖(v j : EuBB m)‖ ≤ R) {t : ℕ} (ht : t ≤ m) :
    ∃ β : Module.Basis (Fin t) ℤ ↥(Q L m v t ht),
      ∀ i : Fin t, ‖((β i : ↥(Q L m v t ht)) : EuBB m)‖ ≤ (t : ℝ) * R := by
  classical
  induction t with
  | zero =>
      let β0 : Module.Basis (Fin 0) ℤ ↥(Q L m v 0 ht) := Q_basis L m v 0 ht hv
      refine ⟨β0, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ t ih =>
      have ht0 : t ≤ m := by omega
      obtain ⟨βt, hβt⟩ := ih ht0
      obtain ⟨γ, hγ⟩ := extend_flag_basis L v hv hfin R hR0 hvR ht0 ht βt hβt
      refine ⟨γ, ?_⟩
      intro i
      rw [show ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 by norm_num]
      exact hγ i

end Extension

end bbbr

/-- A bounded `ℤ`-basis from bounded realisers. -/
theorem bounded_basis_of_bounded_realizers {m : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin m))) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfin : Module.finrank ℤ L = m) (v : Fin m → L)
    (hv : LinearIndependent ℝ (fun j : Fin m => (v j : EuclideanSpace ℝ (Fin m))))
    (R : ℝ) (hR0 : 0 ≤ R) (hvR : ∀ j : Fin m, ‖(v j : EuclideanSpace ℝ (Fin m))‖ ≤ R) :
    ∃ b : Module.Basis (Fin m) ℤ L,
      ∀ i : Fin m, ‖((b i : L) : EuclideanSpace ℝ (Fin m))‖ ≤ (2 * (m : ℝ) + 1) * R := by
  classical
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  obtain ⟨βm, hβm⟩ := bbbr.bounded_chain L v hv hfin R hR0 hvR (t := m) (le_refl m)
  have hQtop : Q L m v m (le_refl m) = L := flagBasis.Q_top L m v hfin hv
  let eQ : ↥(Q L m v m (le_refl m)) ≃ₗ[ℤ] L := LinearEquiv.ofEq (Q L m v m (le_refl m)) L hQtop
  let b : Module.Basis (Fin m) ℤ L := βm.map eQ
  refine ⟨b, ?_⟩
  intro i
  have hval : ‖((b i : L) : (EuclideanSpace ℝ (Fin m)))‖ = ‖((βm i : ↥(Q L m v m (le_refl m))) : (EuclideanSpace ℝ (Fin m)))‖ := by
    dsimp [b]
    rw [flagBasis.ofEq_val_eqZ (Q L m v m (le_refl m)) L hQtop (βm i)]
  rw [hval]
  have hb : ‖((βm i : ↥(Q L m v m (le_refl m))) : (EuclideanSpace ℝ (Fin m)))‖ ≤ (m : ℝ) * R := hβm i
  nlinarith