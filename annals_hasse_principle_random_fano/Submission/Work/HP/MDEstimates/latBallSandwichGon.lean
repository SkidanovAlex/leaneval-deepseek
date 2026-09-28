import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.GonLib
import Submission.Work.HP.Sig2.Recursion
import Submission.Work.HP.MDEstimates.LatCubeDefs

/-!
# The lattice-point / volume sandwich for a presented lattice

Let `Φ : (Fin R → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι` be injective, so that `Λ = Φ(ℤ^R)` is a lattice of
covolume `latCovol Φ` in `Φ`'s image; the lattice points of norm at most `T` are counted by
`latCount Φ T`.  Writing `N(x) = ‖Φ x‖` for the transported norm on the coefficient space `ℝ^R`
(with `ℤ^R` the standard lattice in it), the half-open cube `halfCube R = [-1/2, 1/2)^R` is a
fundamental domain for `ℤ^R` and `‖Φ y‖ ≤ (1/2) ∑ i, ‖Φ e_i‖` for `y` in it.  Hence, if
`μ ≥ (1/2) ∑ i, ‖Φ e_i‖`, the translates of the cube centred at the lattice points tile `ℝ^R` and
each of them fits into the `N`-ball of radius `μ` about its centre.  This gives the two-sided
comparison

`#{x ∈ ℤ^R : N x ≤ T} ≤ vol{x : N x ≤ T + μ}`   and   `vol{x : N x ≤ T - μ} ≤ #{x ∈ ℤ^R : N x ≤ T}`,

the sandwich used in the proof of the asymptotic lattice point count (`ballCount_asymp`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory

namespace Work.HP.MDEstimates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The half-open cube and its translates -/

/-- The translate of the half-open cube to the lattice point `z`, as a product of half-open
intervals centred at the integer coordinates of `z`. -/
lemma cubeAtZ_eq {R : ℕ} (z : Fin R → ℤ) :
    cubeAtZ z = Set.univ.pi (fun i : Fin R => Set.Ico ((z i : ℝ) - 1 / 2) ((z i : ℝ) + 1 / 2)) := by
  ext x
  rw [mem_cubeAtZ_iff, mem_halfCube_iff, Set.mem_univ_pi]
  constructor
  · intro h i
    have hi := h i
    simp only [toRealVec, Pi.sub_apply] at hi
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  · intro h i
    have hi := h i
    simp only [toRealVec, Pi.sub_apply] at hi ⊢
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- The half-open unit cube has volume one. -/
lemma volume_halfCube (R : ℕ) : volume (halfCube R) = 1 := by
  rw [halfCube, Real.volume_pi_Ico]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [show (1 / 2 : ℝ) - (-(1 / 2)) = 1 by norm_num]
  exact ENNReal.ofReal_one

/-- Every translate of the half-open unit cube has volume one. -/
lemma volume_cubeAtZ {R : ℕ} (z : Fin R → ℤ) : volume (cubeAtZ z) = 1 := by
  rw [cubeAtZ_eq, Real.volume_pi_Ico]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [show ((z i : ℝ) + 1 / 2) - ((z i : ℝ) - 1 / 2) = 1 by ring]
  exact ENNReal.ofReal_one

/-- Every translate of the half-open unit cube is measurable. -/
lemma measurableSet_cubeAtZ {R : ℕ} (z : Fin R → ℤ) : MeasurableSet (cubeAtZ z) := by
  rw [cubeAtZ_eq]
  exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico

/-- Distinct translates of the half-open unit cube are disjoint (the half-open cube is a
fundamental domain for `ℤ^R`). -/
lemma disjoint_cubeAtZ {R : ℕ} {z z' : Fin R → ℤ} (h : z ≠ z') :
    Disjoint (cubeAtZ z) (cubeAtZ z') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have hx1 : ∀ i, x i ∈ Set.Ico ((z i : ℝ) - 1 / 2) ((z i : ℝ) + 1 / 2) := by
    rw [cubeAtZ_eq] at hx
    exact Set.mem_univ_pi.mp hx
  have hx2 : ∀ i, x i ∈ Set.Ico ((z' i : ℝ) - 1 / 2) ((z' i : ℝ) + 1 / 2) := by
    rw [cubeAtZ_eq] at hx'
    exact Set.mem_univ_pi.mp hx'
  apply h
  funext i
  by_contra hne
  have hzu : x i < (z i : ℝ) + 1 / 2 := (hx1 i).2
  have hzl : (z i : ℝ) - 1 / 2 ≤ x i := (hx1 i).1
  have hz'u : x i < (z' i : ℝ) + 1 / 2 := (hx2 i).2
  have hz'l : (z' i : ℝ) - 1 / 2 ≤ x i := (hx2 i).1
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcast : ((z i : ℤ) : ℝ) + 1 ≤ ((z' i : ℤ) : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hlt)
    linarith
  · have hcast : ((z' i : ℤ) : ℝ) + 1 ≤ ((z i : ℤ) : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hgt)
    linarith

/-- Rounding to the nearest lattice point: every point of coefficient space lies in one of the
half-open cubes centred at the lattice points. -/
lemma exists_mem_cubeAtZ (R : ℕ) (x : Fin R → ℝ) : ∃ z : Fin R → ℤ, x ∈ cubeAtZ z := by
  refine ⟨fun i => ⌊x i + 1 / 2⌋, ?_⟩
  rw [cubeAtZ_eq, Set.mem_univ_pi]
  intro i
  have h1 : ((⌊x i + 1 / 2⌋ : ℤ) : ℝ) ≤ x i + 1 / 2 := Int.floor_le _
  have h2 : x i + 1 / 2 < ((⌊x i + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  exact ⟨by linarith, by linarith⟩

omit [DecidableEq ι] in
/-- Membership in `latSet` in terms of the real coefficient vector. -/
lemma mem_latSet_iff {R : ℕ} (Φ : Work.HP.LatMap (ι := ι) R) (T : ℝ) (z : Fin R → ℤ) :
    z ∈ latSet Φ T ↔ ‖Φ (toRealVec z)‖ ≤ T := Iff.rfl

/-! ## The norm bound on the half-open cube -/

omit [DecidableEq ι] in
/-- On the half-open cube `[-1/2,1/2)^R` the transported norm is at most the half-sum of the norms
of the images of the standard basis vectors. -/
lemma normLeMuOfMemHalfCube {R : ℕ}
    (Φ : Work.HP.LatMap (ι := ι) R) {μ : ℝ}
    (hμ : (1 / 2) * ∑ i, ‖Φ (Pi.basisFun ℝ (Fin R) i)‖ ≤ μ) {y : Fin R → ℝ}
    (hy : y ∈ halfCube R) : ‖Φ y‖ ≤ μ := by
  have hrepr : ∑ i, y i • Pi.basisFun ℝ (Fin R) i = y := by
    have := Module.Basis.sum_repr (Pi.basisFun ℝ (Fin R)) y
    simpa using this
  have hcoord : ∀ i, |y i| ≤ 1 / 2 := by
    intro i
    have hi := mem_halfCube_iff.mp hy i
    exact abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩
  have hmap : Φ y = ∑ i, y i • Φ (Pi.basisFun ℝ (Fin R) i) := by
    conv_lhs => rw [← hrepr]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul Φ (y i) _
  calc ‖Φ y‖ = ‖∑ i, y i • Φ (Pi.basisFun ℝ (Fin R) i)‖ := by rw [hmap]
    _ ≤ ∑ i, ‖y i • Φ (Pi.basisFun ℝ (Fin R) i)‖ := norm_sum_le _ _
    _ = ∑ i, |y i| * ‖Φ (Pi.basisFun ℝ (Fin R) i)‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, (1 / 2) * ‖Φ (Pi.basisFun ℝ (Fin R) i)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_right (hcoord i) (norm_nonneg _)
    _ = (1 / 2) * ∑ i, ‖Φ (Pi.basisFun ℝ (Fin R) i)‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ μ := hμ

/-! ## Finiteness of the lattice point set -/

omit [DecidableEq ι] in
/-- The coefficient vectors of the lattice points of norm at most `T` form a finite set. -/
lemma latSet_finite_of {R : ℕ} (Φ : Work.HP.LatMap (ι := ι) R) (hΦ : Function.Injective Φ)
    (T : ℝ) : (latSet Φ T).Finite := by
  obtain ⟨K, -, hK⟩ := Φ.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hΦ)
  refine (Set.Finite.pi fun _ : Fin R => Set.finite_Icc (-⌈(K : ℝ) * T⌉) ⌈(K : ℝ) * T⌉).subset ?_
  intro t ht
  rw [Set.mem_pi]
  intro i _
  rw [Set.mem_Icc]
  have hb : |(t i : ℝ)| ≤ (K : ℝ) * T := by
    have h1 : ‖(t i : ℝ)‖ ≤ ‖fun j : Fin R => (t j : ℝ)‖ :=
      norm_le_pi_norm (fun j : Fin R => (t j : ℝ)) i
    have h2 : ‖fun j : Fin R => (t j : ℝ)‖ ≤ (K : ℝ) * ‖Φ (fun j : Fin R => (t j : ℝ))‖ := by
      have := hK.le_mul_dist (fun j : Fin R => (t j : ℝ)) 0
      simpa [dist_zero_right, map_zero] using this
    calc |(t i : ℝ)| = ‖(t i : ℝ)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fun j : Fin R => (t j : ℝ)‖ := h1
      _ ≤ (K : ℝ) * ‖Φ (fun j : Fin R => (t j : ℝ))‖ := h2
      _ ≤ (K : ℝ) * T := mul_le_mul_of_nonneg_left ht K.coe_nonneg
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb
  constructor
  · have hcast : ((-⌈(K : ℝ) * T⌉ : ℤ) : ℝ) ≤ ((t i : ℤ) : ℝ) := by
      push_cast
      calc -(⌈(K : ℝ) * T⌉ : ℝ) ≤ -((K : ℝ) * T) := neg_le_neg (Int.le_ceil _)
        _ ≤ (t i : ℝ) := hlo
    exact Int.cast_le.mp hcast
  · have hcast : ((t i : ℤ) : ℝ) ≤ ((⌈(K : ℝ) * T⌉ : ℤ) : ℝ) := hhi.trans (Int.le_ceil _)
    exact Int.cast_le.mp hcast

/-! ## The two measure / count comparisons -/

omit [DecidableEq ι] in
/-- If a set of coefficient vectors is covered by the cubes centred at the lattice points of norm
at most `A`, then its volume is at most the number of those lattice points. -/
lemma volume_le_ncard_of_bdd {R : ℕ} (Φ : Work.HP.LatMap (ι := ι) R)
    (hΦ : Function.Injective Φ) (A : ℝ) {S : Set (Fin R → ℝ)}
    (h : ∀ x ∈ S, ∃ z : Fin R → ℤ, z ∈ latSet Φ A ∧ x ∈ cubeAtZ z) :
    volume S ≤ ((latSet Φ A).ncard : ENNReal) := by
  have hf : (latSet Φ A).Finite := latSet_finite_of Φ hΦ A
  have hcov : S ⊆ ⋃ z ∈ hf.toFinset, cubeAtZ z := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := h x hx
    exact Set.mem_iUnion₂.mpr ⟨z, (Set.Finite.mem_toFinset hf).mpr hz, hxz⟩
  calc volume S ≤ volume (⋃ z ∈ hf.toFinset, cubeAtZ z) := measure_mono hcov
    _ ≤ ∑ z ∈ hf.toFinset, volume (cubeAtZ z) :=
          MeasureTheory.measure_biUnion_finset_le _ _
    _ = ∑ _z ∈ hf.toFinset, (1 : ENNReal) := by simp [volume_cubeAtZ]
    _ = (hf.toFinset.card : ENNReal) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ((latSet Φ A).ncard : ENNReal) := by rw [Set.ncard_eq_toFinset_card (latSet Φ A) hf]

omit [DecidableEq ι] in
/-- If the cubes centred at the lattice points of norm at most `A` are all contained in a set,
then their number is at most the volume of that set. -/
lemma ncard_le_volume_of_cells {R : ℕ} (Φ : Work.HP.LatMap (ι := ι) R)
    (hΦ : Function.Injective Φ) (A : ℝ) {S : Set (Fin R → ℝ)}
    (h : ∀ z ∈ latSet Φ A, cubeAtZ z ⊆ S) :
    ((latSet Φ A).ncard : ENNReal) ≤ volume S := by
  have hf : (latSet Φ A).Finite := latSet_finite_of Φ hΦ A
  have hsub : ⋃ z ∈ hf.toFinset, cubeAtZ z ⊆ S := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hx
    exact h z ((Set.Finite.mem_toFinset hf).mp hz) hxz
  have hdisj : (↑hf.toFinset : Set (Fin R → ℤ)).PairwiseDisjoint cubeAtZ := by
    intro a _ b _ hab
    exact disjoint_cubeAtZ hab
  have hmeas : ∀ b ∈ hf.toFinset, MeasurableSet (cubeAtZ b) := fun b _ => measurableSet_cubeAtZ b
  calc ((latSet Φ A).ncard : ENNReal) = (hf.toFinset.card : ENNReal) := by
        rw [Set.ncard_eq_toFinset_card (latSet Φ A) hf]
    _ = ∑ _z ∈ hf.toFinset, (1 : ENNReal) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ∑ z ∈ hf.toFinset, volume (cubeAtZ z) := by simp [volume_cubeAtZ]
    _ = volume (⋃ z ∈ hf.toFinset, cubeAtZ z) :=
          (MeasureTheory.measure_biUnion_finset hdisj hmeas).symm
    _ ≤ volume S := measure_mono hsub

omit [DecidableEq ι] in
/-- The `Φ`-ball of radius `T + μ` has finite volume. -/
lemma volume_ball_add_lt_top {R : ℕ} (Φ : Work.HP.LatMap (ι := ι) R)
    (hΦ : Function.Injective Φ) (T μ : ℝ)
    (hμ : (1 / 2) * ∑ i, ‖Φ (Pi.basisFun ℝ (Fin R) i)‖ ≤ μ) :
    volume {x : Fin R → ℝ | ‖Φ x‖ ≤ T + μ} ≠ ⊤ := by
  have hle := volume_le_ncard_of_bdd Φ hΦ (T + 2 * μ)
    (S := {x : Fin R → ℝ | ‖Φ x‖ ≤ T + μ}) fun x hx => ?_
  · exact ne_top_of_le_ne_top
      (ENNReal.natCast_ne_top ((latSet Φ (T + 2 * μ)).ncard)) hle
  · obtain ⟨z, hz⟩ := exists_mem_cubeAtZ R x
    refine ⟨z, ?_, hz⟩
    have hx' : ‖Φ (x - toRealVec z)‖ ≤ μ :=
      normLeMuOfMemHalfCube Φ hμ (mem_cubeAtZ_iff.mp hz)
    have hnx : ‖Φ (toRealVec z)‖ ≤ T + 2 * μ := by
      have hdecomp : Φ (toRealVec z) = Φ x - Φ (x - toRealVec z) := by
        have h2 : x - (x - toRealVec z) = toRealVec z := by abel
        calc Φ (toRealVec z) = Φ (x - (x - toRealVec z)) := by rw [h2]
          _ = Φ x - Φ (x - toRealVec z) := map_sub Φ x (x - toRealVec z)
      calc ‖Φ (toRealVec z)‖ = ‖Φ x - Φ (x - toRealVec z)‖ := by rw [hdecomp]
        _ ≤ ‖Φ x‖ + ‖Φ (x - toRealVec z)‖ := norm_sub_le _ _
        _ ≤ (T + μ) + μ := add_le_add hx hx'
        _ = T + 2 * μ := by ring
    exact (mem_latSet_iff Φ (T + 2 * μ) z).mpr hnx

/-! ## The sandwich -/

theorem latBallSandwichGon {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ}
    (Φ : Work.HP.LatMap (ι := ι) R) (hΦ : Function.Injective Φ) (T μ : ℝ) (hT : 0 ≤ T)
    (hμ : (1 / 2) * ∑ i, ‖Φ (Pi.basisFun ℝ (Fin R) i)‖ ≤ μ) :
    (Work.HP.latCount Φ T : ℝ) ≤
        (MeasureTheory.volume {x : Fin R → ℝ | ‖Φ x‖ ≤ T + μ}).toReal ∧
    (MeasureTheory.volume {x : Fin R → ℝ | ‖Φ x‖ ≤ T - μ}).toReal ≤
        (Work.HP.latCount Φ T : ℝ) := by
  constructor
  · have hB' := ncard_le_volume_of_cells Φ hΦ T (S := {x : Fin R → ℝ | ‖Φ x‖ ≤ T + μ})
      (fun z hz x hx => ?_)
    · have hB : (latCount Φ T : ENNReal) ≤ volume {x : Fin R → ℝ | ‖Φ x‖ ≤ T + μ} := by
        simpa [latCount] using hB'
      have htop := volume_ball_add_lt_top Φ hΦ T μ hμ
      have h2 := ENNReal.toReal_mono htop hB
      simpa [ENNReal.toReal_natCast] using h2
    · have hzT : ‖Φ (toRealVec z)‖ ≤ T := (mem_latSet_iff Φ T z).mp hz
      have hx' : ‖Φ (x - toRealVec z)‖ ≤ μ :=
        normLeMuOfMemHalfCube Φ hμ (mem_cubeAtZ_iff.mp hx)
      show ‖Φ x‖ ≤ T + μ
      have hdecomp : Φ x = Φ (toRealVec z) + Φ (x - toRealVec z) := by
        have h2 : toRealVec z + (x - toRealVec z) = x := by abel
        calc Φ x = Φ (toRealVec z + (x - toRealVec z)) := by rw [h2]
          _ = Φ (toRealVec z) + Φ (x - toRealVec z) := map_add Φ (toRealVec z) (x - toRealVec z)
      calc ‖Φ x‖ = ‖Φ (toRealVec z) + Φ (x - toRealVec z)‖ := by rw [hdecomp]
        _ ≤ ‖Φ (toRealVec z)‖ + ‖Φ (x - toRealVec z)‖ := norm_add_le _ _
        _ ≤ T + μ := add_le_add hzT hx'
  · have hA' := volume_le_ncard_of_bdd Φ hΦ T (S := {x : Fin R → ℝ | ‖Φ x‖ ≤ T - μ})
      (fun x hx => ?_)
    · have hA : volume {x : Fin R → ℝ | ‖Φ x‖ ≤ T - μ} ≤ (latCount Φ T : ENNReal) := by
        simpa [latCount] using hA'
      have h2 := ENNReal.toReal_mono (ENNReal.natCast_ne_top (latCount Φ T)) hA
      simpa [ENNReal.toReal_natCast] using h2
    · obtain ⟨z, hz⟩ := exists_mem_cubeAtZ R x
      refine ⟨z, ?_, hz⟩
      have hx' : ‖Φ (x - toRealVec z)‖ ≤ μ :=
        normLeMuOfMemHalfCube Φ hμ (mem_cubeAtZ_iff.mp hz)
      have hzT : ‖Φ (toRealVec z)‖ ≤ T := by
        have hdecomp : Φ (toRealVec z) = Φ x - Φ (x - toRealVec z) := by
          have h2 : x - (x - toRealVec z) = toRealVec z := by abel
          calc Φ (toRealVec z) = Φ (x - (x - toRealVec z)) := by rw [h2]
            _ = Φ x - Φ (x - toRealVec z) := map_sub Φ x (x - toRealVec z)
        calc ‖Φ (toRealVec z)‖ = ‖Φ x - Φ (x - toRealVec z)‖ := by rw [hdecomp]
          _ ≤ ‖Φ x‖ + ‖Φ (x - toRealVec z)‖ := norm_sub_le _ _
          _ ≤ (T - μ) + μ := add_le_add hx hx'
          _ = T := by ring
      exact (mem_latSet_iff Φ T z).mpr hzT

end Work.HP.MDEstimates
