/-
  WilE9G / Lagrange — **`Good` for the constructed Lagrange stratum**.

  `Work.WilE9G.Lagrange.lagStratum S Phi c` is the `EffStratum` whose single disjunct consists of

  * the `1 + (m + S.j + 1)` equations `lagEqs S Phi c` (the `1+m` Lagrange equations `lagL`, the
    `S.j` lifted equations `lagH` and the normalisation `lagN`), and
  * the strict inequalities `lagPos S Phi c`, namely `lagDet² > 0` (the nonvanishing of the fibre
    determinant of the system) together with the interior conditions `1 - x_i² > 0` on the
    base-and-fibre coordinates.

  This file proves that this stratum is `Good` in the sense of `EffStratum.Good`:

  * the equations vanish on the set, because they are the equations of its only disjunct;
  * the fibre determinant of the stratum does not vanish on the set, because it is one of the
    strict inequalities of that disjunct (`lagStratum_eaEval_lagDet` rewrites the evaluated symbolic
    determinant `lagDet` as `(lagBlock …).det` — `eaEval` is `MvPolynomial.eval` at a point, so
    it commutes with `Matrix.det`);
  * `X.set` is ambiently locally the zero set of the equations.  The only non-trivial point here
    is that the *cube* condition `|z_j| ≤ 1` has to be recovered on a neighbourhood of a point `z`
    of the set from the equations alone: the base-and-fibre coordinates `j < n + (1 + m)` are
    bounded strictly by the interior inequalities, while the multiplier coordinates
    `(μ, μ₀)` are bounded by the *normalisation* equation `∑ μ_a² + μ₀² = 1` (index bookkeeping:
    the last equation of `lagEqs` is `lagN`, `lagStratum_lagEqs_last`).
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.Stratum

set_option autoImplicit false
noncomputable section

open Classical Topology Filter MeasureTheory

namespace Work.WilE9G.Lagrange

open WilkiesDesign WilkiesDesign.E Work.WilE9G

/-! ## Evaluation helpers -/

/-- Evaluating the determinant of a matrix of EA polynomials is taking the determinant of the
evaluated matrix. -/
theorem lagStratum_eaEval_det {k r Q : ℕ} (c : EAChain k r)
    (M : Matrix (Fin Q) (Fin Q) (EAPoly k r)) (z : Fin k → ℝ) :
    eaEval c M.det z = (M.map (fun P => eaEval c P z)).det := by
  have h := RingHom.map_det (MvPolynomial.eval (Sum.elim z fun j => Real.exp (c.ell j z))) M
  have hmat : (MvPolynomial.eval (Sum.elim z fun j => Real.exp (c.ell j z))).mapMatrix M
      = M.map (fun P => eaEval c P z) := by
    ext i j; rfl
  rw [hmat] at h
  exact h

/-- The evaluation of an exp-affine polynomial is continuous in the point. -/
theorem lagStratum_continuous_eaEval {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) :
    Continuous fun x : Fin k → ℝ => eaEval c Q x := by
  apply (MvPolynomial.continuous_eval Q).comp
  refine continuous_pi (fun s => ?_)
  cases s with
  | inl i => simpa using (continuous_apply i : Continuous fun x : Fin k → ℝ => x i)
  | inr j => exact Real.continuous_exp.comp (by unfold EAChain.ell; fun_prop)

/-- The value of the normalisation equation `lagN` of the construction at a point: the sum of the
squares of the multiplier coordinates. -/
theorem lagStratum_eaEval_lagN {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (z : Fin (n + (1 + (m + S.j + 1))) → ℝ) :
    eaEval (lagChain S) (lagN S) z
      = (∑ a : Fin S.j, (z (muIdx n m a)) ^ 2) + (z (mu0Idx n m S.j)) ^ 2 - 1 := by
  simp only [eaEval, lagN, muVar, mu0Var, map_add, map_sub, map_pow, map_sum, map_one,
    MvPolynomial.eval_X, Sum.elim_inl]

/-- The value of an interior condition `1 - x_i²` of `lagPos` at a point. -/
theorem lagStratum_eaEval_lagPos {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (z : Fin (n + (1 + (m + S.j + 1))) → ℝ) (i : Fin (n + (1 + m))) :
    eaEval (lagChain S) (1 - (MvPolynomial.X (Sum.inl (Fin.castLE (by omega) i))) ^ 2) z
      = 1 - (z (Fin.castLE (by omega) i)) ^ 2 := by
  simp only [eaEval, map_sub, map_one, map_pow, MvPolynomial.eval_X, Sum.elim_inl]

/-- **The last equation of the constructed stratum is the normalisation.**  The index
`m + S.j + 1` is the last one, and under the block equivalence `lagEquiv` it is the pair
`(Fin.last S.j, 0)` of the block decomposition `(1+m) + (S.j + 1)` of the equation indices. -/
theorem lagStratum_lagEqs_last {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    lagEqs S Phi c ⟨m + S.j + 1, by omega⟩ = lagN S := by
  have hidx : lagEquiv m S.j ⟨m + S.j + 1, by omega⟩
      = Fin.natAdd (1 + m) (Fin.last S.j) := by
    ext
    simp only [lagEquiv, Work.WilE7.finEquiv_apply_val, Fin.val_natAdd, Fin.val_last]
    omega
  have hidx2 : (Fin.last S.j : Fin (S.j + 1)) = Fin.natAdd S.j (0 : Fin 1) := by
    ext
    simp [Fin.natAdd]
  unfold lagEqs
  rw [hidx, Fin.addCases_right, hidx2, Fin.addCases_right]

/-- The square of the evaluated fibre determinant `lagDet` of the construction is the square of
its value (the point of writing it this way is that `lagPos` contains the product
`lagDet * lagDet`, so that `0 < lagDet²` is exactly `lagDet ≠ 0`). -/
theorem lagStratum_eaEval_lagDet_sq {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + (m + S.j + 1))) → ℝ) :
    eaEval (lagChain S) (lagDet S Phi c * lagDet S Phi c) z
      = eaEval (lagChain S) (lagDet S Phi c) z * eaEval (lagChain S) (lagDet S Phi c) z := by
  simp only [eaEval, map_mul]

/-- Evaluating the symbolic fibre determinant `lagDet` of the constructed stratum gives the fibre
block `lagBlock` of the stratum. -/
theorem lagStratum_eaEval_lagDet {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + (m + S.j + 1))) → ℝ) :
    eaEval (lagChain S) (lagDet S Phi c) z = (lagBlock S Phi c z).det := by
  have h := lagStratum_eaEval_det (lagChain S)
    (Matrix.of fun (a l : Fin (1 + (m + S.j + 1))) =>
      eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a)) z
  exact h

/-! ## `Good` for the constructed stratum -/

theorem lagStratum_good {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    (Work.WilE9G.Lagrange.lagStratum S Phi c).Good := by
  intro z hz
  simp only [lagStratum, WilkiesDesign.E.SemiPf.set, Set.mem_ofPred_eq] at hz
  obtain ⟨_, B, hBmem, hBeq, hBpos⟩ := hz
  have hBmem' : B = (⟨List.ofFn (lagEqs S Phi c), lagPos S Phi c⟩ :
      Basic (n + (1 + (m + S.j + 1))) S.X.r) := List.mem_singleton.mp hBmem
  subst hBmem'
  -- the evaluated determinant of the stratum does not vanish at `z`: its square is one of the
  -- strict inequalities of the disjunct
  have hdet_ne : eaEval (lagChain S) (lagDet S Phi c) z ≠ 0 := by
    have hpos := hBpos _ (by unfold lagPos; exact List.mem_cons_self)
    rw [lagStratum_eaEval_lagDet_sq S Phi c z] at hpos
    exact mul_self_pos.mp hpos
  refine ⟨?_, ?_, ?_⟩
  · -- the equations vanish on `X.set`
    intro a
    exact hBeq _ (List.mem_ofFn.mpr ⟨a, rfl⟩)
  · -- the fibre block of the stratum is invertible on `X.set`
    change (lagBlock S Phi c z).det ≠ 0
    rw [← lagStratum_eaEval_lagDet S Phi c z]
    exact hdet_ne
  · -- `X.set` is ambiently locally the zero set of the equations
    have hcontDet : Continuous fun z' : Fin (n + (1 + (m + S.j + 1))) → ℝ =>
        eaEval (lagChain S) (lagDet S Phi c) z' := lagStratum_continuous_eaEval _ _
    have hev_det : ∀ᶠ z' in 𝓝 z, eaEval (lagChain S) (lagDet S Phi c) z' ≠ 0 :=
      hcontDet.continuousAt.eventually_ne hdet_ne
    have hev_pos : ∀ᶠ z' in 𝓝 z, ∀ i : Fin (n + (1 + m)),
        1 - (z' (Fin.castLE (by omega) i)) ^ 2 > 0 := by
      rw [Filter.eventually_all]
      intro i
      have hcont_i : Continuous fun z' : Fin (n + (1 + (m + S.j + 1))) → ℝ =>
          1 - (z' (Fin.castLE (by omega) i)) ^ 2 := by fun_prop
      have hi : 0 < 1 - (z (Fin.castLE (by omega) i)) ^ 2 := by
        have h := hBpos _
          (by unfold lagPos; exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
        simpa only [lagStratum_eaEval_lagPos S z i] using h
      exact (isOpen_lt continuous_const hcont_i).mem_nhds hi
    filter_upwards [hev_det, hev_pos] with z' hz'det hz'pos heq
    have heq' : ∀ a, eaEval (lagChain S) (lagEqs S Phi c a) z' = 0 := heq
    -- the normalisation equation at `z'`
    have hsum : (∑ a : Fin S.j, (z' (muIdx n m a)) ^ 2) + (z' (mu0Idx n m S.j)) ^ 2 = 1 := by
      have h0 : eaEval (lagChain S) (lagEqs S Phi c ⟨m + S.j + 1, by omega⟩) z' = 0 := heq' _
      rw [lagStratum_lagEqs_last S Phi c, lagStratum_eaEval_lagN S z'] at h0
      linarith
    -- the cube condition, from the interior inequalities and the normalisation
    have hcube : z' ∈ cubeC (n + (1 + (m + S.j + 1))) := by
      intro j
      by_cases hj : j.val < n + (1 + m)
      · -- a base-and-fibre coordinate: strictly interior at `z`, hence at `z'`
        have hlt := hz'pos ⟨j.val, hj⟩
        have hjeq : (Fin.castLE (by omega) (⟨j.val, hj⟩ : Fin (n + (1 + m)))) = j :=
          Fin.ext rfl
        have hsq : z' (Fin.castLE (by omega) (⟨j.val, hj⟩ : Fin (n + (1 + m)))) ^ 2 < 1 := by
          linarith
        rw [sq_lt_one_iff_abs_lt_one] at hsq
        rw [hjeq] at hsq
        exact le_of_lt hsq
      · -- a multiplier coordinate: bounded by the normalisation
        have hle : n + (1 + m) ≤ j.val := Nat.le_of_not_lt hj
        have hbound : (∑ a : Fin S.j, (z' (muIdx n m a)) ^ 2) ≤ 1 := by
          have := sq_nonneg (z' (mu0Idx n m S.j)); linarith
        have hmu : ∀ a : Fin S.j, |z' (muIdx n m a)| ≤ 1 := by
          intro a
          rw [← sq_le_one_iff_abs_le_one]
          have h := Finset.single_le_sum (f := fun i : Fin S.j => (z' (muIdx n m i)) ^ 2)
            (fun i _ => sq_nonneg _) (Finset.mem_univ a)
          simpa using le_trans h hbound
        have hmu0 : |z' (mu0Idx n m S.j)| ≤ 1 := by
          rw [← sq_le_one_iff_abs_le_one]
          exact le_trans (le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => sq_nonneg _))
            (le_of_eq hsum)
        have ht_lt : j.val - (n + (1 + m)) < S.j + 1 := by omega
        by_cases ht : j.val - (n + (1 + m)) < S.j
        · have hjeq : muIdx n m (⟨j.val - (n + (1 + m)), ht⟩ : Fin S.j) = j := by
            ext; simp only [muIdx_val]; omega
          rw [← hjeq]; exact hmu _
        · have htS : j.val - (n + (1 + m)) = S.j := by omega
          have hjeq : mu0Idx n m S.j = j := by
            ext; simp only [mu0Idx_val]; omega
          rw [← hjeq]; exact hmu0
    refine ⟨hcube, ⟨List.ofFn (lagEqs S Phi c), lagPos S Phi c⟩, List.mem_singleton_self _,
      ?_, ?_⟩
    · -- the equations of the disjunct hold at `z'` by hypothesis
      intro f hf
      obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hf
      exact heq' a
    · -- the strict inequalities of the disjunct hold at `z'` on the chosen neighbourhood
      intro g hg
      unfold lagPos at hg
      rcases List.mem_cons.mp hg with hg | hg
      · subst hg
        show 0 < eaEval (lagChain S) (lagDet S Phi c * lagDet S Phi c) z'
        rw [lagStratum_eaEval_lagDet_sq S Phi c z']
        exact mul_self_pos.mpr hz'det
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
        show 0 < eaEval (lagChain S)
          (1 - (MvPolynomial.X (Sum.inl (Fin.castLE (by omega) i))) ^ 2) z'
        rw [lagStratum_eaEval_lagPos S z' i]
        exact hz'pos i

end Work.WilE9G.Lagrange
