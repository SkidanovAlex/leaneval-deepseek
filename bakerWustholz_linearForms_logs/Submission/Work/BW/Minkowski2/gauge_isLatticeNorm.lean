import Mathlib
import Submission.Work.BW.basisRed_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The gauge of a symmetric convex body is a lattice norm

For a convex set `K ⊆ ℝᵈ` which is symmetric (`x ∈ K → -x ∈ K`), bounded and has nonempty
interior, the Minkowski functional `gauge K` is a norm on `ℝᵈ`, and its sublevel sets contain only
finitely many points of `ℤᵈ`.  This is exactly `Work.BW.IsLatticeNorm (gauge K)`, the hypothesis
under which the successive-minimum machinery of `Submission/Work/BW/basisRed_defs.lean` applies.

The five fields of `Work.BW.IsLatticeNorm` are Mathlib's gauge lemmas:

* positivity and subadditivity: `gauge_nonneg` and `gauge_add_le`;
* `gauge K x = 0 ↔ x = 0`: `gauge_eq_zero`, for which `K` must be absorbent (it is a neighbourhood
  of `0`, because `0 ∈ interior K`) and von Neumann bounded (equivalent to `Bornology.IsBounded`);
* absolute homogeneity: `gauge_smul_of_nonneg` handles the factor `|t| ≥ 0` and the symmetry of `K`
  turns `-|t| • x` into `|t| • x` via `gauge_neg`;
* finiteness of the sublevel sets on `ℤᵈ`: `le_gauge_of_subset_closedBall` bounds `‖x‖` by
  `t * R ≤ max (t * R) 0` on `{x | gauge K x ≤ t}` whenever `K ⊆ closedBall 0 R`, so each
  coordinate of an integer point of the sublevel set lies in the finite interval
  `[-(⌈max (t*R) 0⌉), ⌈max (t*R) 0⌉]`.
-/

namespace Work.BW.Minkowski2

open scoped Pointwise

/-- A convex symmetric set with nonempty interior contains `0` in its interior: `0` is the midpoint
of a point `y` of the interior with its negative `-y ∈ K`. -/
theorem zero_mem_interior_of_convex_symm {d : ℕ} {K : Set (Fin d → ℝ)} (hKc : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hKi : (interior K).Nonempty) :
    (0 : Fin d → ℝ) ∈ interior K := by
  obtain ⟨y, hy⟩ := hKi
  have hyK : y ∈ K := interior_subset hy
  have hnegyK : -y ∈ K := hsym y hyK
  have h := hKc.combo_interior_self_mem_interior hy hnegyK (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hzero : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • (-y) = 0 := by
    rw [smul_neg, add_neg_cancel]
  rwa [hzero] at h

/-- A convex symmetric set with nonempty interior is absorbent: it is a neighbourhood of `0`. -/
theorem absorbent_of_convex_symm {d : ℕ} {K : Set (Fin d → ℝ)} (hKc : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hKi : (interior K).Nonempty) : Absorbent ℝ K :=
  absorbent_nhds_zero
    (Filter.mem_of_superset (isOpen_interior.mem_nhds (zero_mem_interior_of_convex_symm hKc hsym hKi))
      interior_subset)

/-- Only finitely many integer vectors of `ℤᵈ` lie in a bounded subset of `ℝᵈ`. -/
theorem finite_intVecs_of_isBounded {d : ℕ} {S : Set (Fin d → ℝ)} (hS : Bornology.IsBounded S) :
    {v : Fin d → ℤ | (fun i => (v i : ℝ)) ∈ S}.Finite := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hS
  refine (Set.Finite.pi'
    (t := fun _ : Fin d => Set.Icc (-⌈max C 0⌉) ⌈max C 0⌉)
    (fun _ => Set.finite_Icc _ _)).subset ?_
  intro v hv i
  have hnorm : ‖(fun i => (v i : ℝ))‖ ≤ max C 0 := le_trans (hC _ hv) (le_max_left _ _)
  have habs : |(v i : ℝ)| ≤ max C 0 := by
    have h1 : ‖((v i : ℝ))‖ ≤ ‖(fun i => (v i : ℝ))‖ :=
      norm_le_pi_norm (fun i => (v i : ℝ)) i
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 hnorm
  obtain ⟨hlow, hhigh⟩ := abs_le.mp habs
  have hceil : max C 0 ≤ ((⌈max C 0⌉ : ℤ) : ℝ) := Int.le_ceil _
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · have h3 : (((-⌈max C 0⌉ : ℤ)) : ℝ) ≤ ((v i : ℤ) : ℝ) := by
      push_cast
      linarith
    exact Int.cast_le.mp h3
  · exact Int.cast_le.mp (le_trans hhigh hceil)

theorem gauge_isLatticeNorm {d : ℕ} (K : Set (Fin d → ℝ)) (hKc : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hKbd : Bornology.IsBounded K) (hKi : (interior K).Nonempty) :
    Work.BW.IsLatticeNorm (gauge K) := by
  have habs : Absorbent ℝ K := absorbent_of_convex_symm hKc hsym hKi
  have hbdd : Bornology.IsVonNBounded ℝ K := NormedSpace.isVonNBounded_of_isBounded ℝ hKbd
  refine ⟨fun x => gauge_nonneg x, fun x => gauge_eq_zero habs hbdd, ?_, ?_, ?_⟩
  · intro t x
    rcases le_or_gt 0 t with ht | ht
    · rw [gauge_smul_of_nonneg ht x, smul_eq_mul, abs_of_nonneg ht]
    · have htx : t • x = -((|t|) • x) := by rw [← neg_smul, abs_of_neg ht, neg_neg]
      rw [htx, gauge_neg hsym, gauge_smul_of_nonneg (abs_nonneg t) x, smul_eq_mul]
  · intro x y
    exact gauge_add_le hKc habs x y
  · intro t
    obtain ⟨R, hRpos, hRK⟩ : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.closedBall 0 R := by
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hKbd
      refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_trans (hC x hx) (le_max_left C 1)
    have hbd : ∀ x : Fin d → ℝ, gauge K x ≤ t → ‖x‖ ≤ t * R := by
      intro x hx
      have h1 : ‖x‖ / R ≤ gauge K x :=
        le_gauge_of_subset_closedBall (s := K) (r := R) (x := x) habs hRpos.le hRK
      have h2 : ‖x‖ / R ≤ t := le_trans h1 hx
      rwa [div_le_iff₀ hRpos] at h2
    refine (finite_intVecs_of_isBounded (S := {x : Fin d → ℝ | gauge K x ≤ t}) ?_).subset ?_
    · refine (isBounded_iff_forall_norm_le).mpr ⟨max (t * R) 0, fun x hx => ?_⟩
      exact le_trans (hbd x hx) (le_max_left _ _)
    · intro v hv
      exact hv

end Work.BW.Minkowski2
