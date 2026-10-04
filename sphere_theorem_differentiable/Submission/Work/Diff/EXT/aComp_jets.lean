import Mathlib
import Submission.Work.Diff.EXT.chartData_step_aux
import Submission.Work.Diff.EXT.norm_iteratedFDeriv_le_basisSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Chart jets of the connection difference from its covariant jets

`Work.Diff.EXT.aComp_jets`: the chart derivatives of `aComp` (the chart array of the lowered
connection difference `g_t(∇^{g_t} − ∇^{g_0})`) up to order `k` are bounded by the *covariant*
derivatives `aCovArr` (taken with respect to the fixed background connection `∇^{G 0}`) up to order
`k`, together with the chart jets of the background Christoffel symbols `cGam (G 0)`.

The recursion `fderiv (aCovArr m) = aCovArr (m+1) + (background Christoffel corrections)` is
inverted by a double induction: for every level `j` and every `m` with `m + j ≤ k` one bounds the
`j`-th chart jet of `aCovArr m`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

theorem aComp_jets
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E) (k : ℕ)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hcore : ∀ m ≤ k, ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
        |aCovArr (I := I) (M := M) G x₀ t m v i j l y| ≤ Cm)
    (hcGam0 : ∀ m ≤ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
        (pt (I := I) x₀ y') l i j) y‖ ≤ C)
    (hsm0 : ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
        (pt (I := I) x₀ y') l i j) y)
    (hsmA : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => aComp (I := I) (M := M) G x₀ t y' i j l) y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ m ≤ k,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => aComp (I := I) (M := M) G x₀ t y' i j l) y‖ ≤ C := by
  classical
  -- a uniform bound on the background Christoffel jets up to order `k`
  obtain ⟨CΓ, hCΓ0, hCΓ⟩ := exists_uniform_bound_of_le
    (P := fun m C => ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
        (pt (I := I) x₀ y') l i j) y‖ ≤ C)
    (fun m C C' h hle y hy i j l => le_trans (h y hy i j l) hle) k hcGam0
  -- a uniform basis-expansion constant for all levels `≤ k + 1`
  obtain ⟨Cbs, hCbs0, hCbs⟩ := exists_uniform_bound_of_le
    (P := fun (j : ℕ) (C : ℝ) => ∀ (f : E → ℝ) (y : E),
      ‖iteratedFDeriv ℝ j f y‖ ≤ C * ∑ ρ : Fin j → Fin (Module.finrank ℝ E),
        ‖iteratedFDeriv ℝ j f y (fun s => Module.finBasis ℝ E (ρ s))‖)
    (fun j C C' h hle f y => le_trans (h f y)
      (mul_le_mul_of_nonneg_right hle (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
    (k + 1) (fun j _ => norm_iteratedFDeriv_le_basisSum (E := E) (F := ℝ) j)
  -- a geometric constant for the norm of the basis vectors
  set Kb : ℝ := max 1 (∑ m : Fin (Module.finrank ℝ E), ‖Module.finBasis ℝ E m‖) with hKbdef
  have hKbnorm : ∀ m : Fin (Module.finrank ℝ E), ‖Module.finBasis ℝ E m‖ ≤ Kb := by
    intro m
    exact le_trans (Finset.single_le_sum (fun i _ => norm_nonneg (Module.finBasis ℝ E i))
      (Finset.mem_univ m)) (le_max_right _ _)
  -- a uniform value bound for `aCovArr m`, `m ≤ k`
  obtain ⟨Ccore, hCcore0, hCcore⟩ := exists_uniform_bound_of_le
    (P := fun m C => ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
        |aCovArr (I := I) (M := M) G x₀ t m v i j l y| ≤ C)
    (fun m C C' h hle t ht y hy v i j l => le_trans (h t ht y hy v i j l) hle) k hcore
  -- smoothness of the arrays `aCovArr m` at the points of `K`
  have hsm : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (m : ℕ) (v : Fin m → Fin (Module.finrank ℝ E))
      (a b c : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => aCovArr (I := I) (M := M) G x₀ t m v a b c y') y := by
    intro t ht y hy m
    induction m with
    | zero =>
        intro v a b c
        exact hsmA t ht y hy a b c
    | succ m ih =>
        intro v a b c
        have hfd : ContDiffAt ℝ (⊤ : ℕ∞)
            (fun y' : E => fderiv ℝ (fun y'' : E =>
              aCovArr (I := I) (M := M) G x₀ t m (fun s => v s.succ) a b c y'') y') y :=
          (ih (fun s => v s.succ) a b c).fderiv_right (by simp)
        have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => fderiv ℝ (fun y'' : E =>
              aCovArr (I := I) (M := M) G x₀ t m (fun s => v s.succ) a b c y'') y'
              (Work.Diff.GE.cBasis (E := E) (v 0))) y :=
          hfd.clm_apply contDiffAt_const
        have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ r : Fin m,
            ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (v r.succ) (v 0)
                * aCovArr (I := I) (M := M) G x₀ t m
                    (Function.update (fun s => v s.succ) r p) a b c y') y :=
          ContDiffAt.sum fun r _ => ContDiffAt.sum fun p _ =>
            ContDiffAt.mul (hsm0 y hy (v r.succ) (v 0) p)
              (ih (Function.update (fun s => v s.succ) r p) a b c)
        have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p a (v 0)
                * aCovArr (I := I) (M := M) G x₀ t m (fun s => v s.succ) p b c y') y :=
          ContDiffAt.sum fun p _ =>
            ContDiffAt.mul (hsm0 y hy a (v 0) p) (ih (fun s => v s.succ) p b c)
        have h4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p b (v 0)
                * aCovArr (I := I) (M := M) G x₀ t m (fun s => v s.succ) a p c y') y :=
          ContDiffAt.sum fun p _ =>
            ContDiffAt.mul (hsm0 y hy b (v 0) p) (ih (fun s => v s.succ) a p c)
        have h5 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p c (v 0)
                * aCovArr (I := I) (M := M) G x₀ t m (fun s => v s.succ) a b p y') y :=
          ContDiffAt.sum fun p _ =>
            ContDiffAt.mul (hsm0 y hy c (v 0) p) (ih (fun s => v s.succ) a b p)
        have hgoal : (fun y' : E => aCovArr (I := I) (M := M) G x₀ t (m + 1) v a b c y')
            = fun y' : E => fderiv ℝ (fun y'' : E =>
                  aCovArr (I := I) (M := M) G x₀ t m (fun s => v s.succ) a b c y'') y'
                  (Work.Diff.GE.cBasis (E := E) (v 0))
              - (∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
                  Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (v r.succ) (v 0)
                    * aCovArr (I := I) (M := M) G x₀ t m
                        (Function.update (fun s => v s.succ) r p) a b c y')
              - (∑ p : Fin (Module.finrank ℝ E),
                  Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p a (v 0)
                    * aCovArr (I := I) (M := M) G x₀ t m (fun s => v s.succ) p b c y')
              - (∑ p : Fin (Module.finrank ℝ E),
                  Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p b (v 0)
                    * aCovArr (I := I) (M := M) G x₀ t m (fun s => v s.succ) a p c y')
              - (∑ p : Fin (Module.finrank ℝ E),
                  Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p c (v 0)
                    * aCovArr (I := I) (M := M) G x₀ t m (fun s => v s.succ) a b p y') := by
          funext y'
          simp only [aCovArr]
        rw [hgoal]
        exact (((h1.sub h2).sub h3).sub h4).sub h5
  -- the main double induction
  have key : ∀ j, j ≤ k → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ i ≤ j,
      ∀ (m : ℕ), m + i ≤ k → ∀ (v : Fin m → Fin (Module.finrank ℝ E))
        (a b c : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ i (fun y' : E => aCovArr (I := I) (M := M) G x₀ t m v a b c y') y‖
          ≤ C := by
    intro j
    induction j with
    | zero =>
        intro _
        refine ⟨Ccore, hCcore0, fun t ht y hy i hi m hm v a b c => ?_⟩
        have hi0 : i = 0 := Nat.le_zero.mp hi
        subst hi0
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hCcore m hm t ht y hy v a b c
    | succ j ih =>
        intro hjk
        obtain ⟨Cj, hCj0, hCj⟩ := ih (by omega)
        set Bmax : ℝ := max CΓ Cj with hBmaxdef
        have hBmax0 : 0 ≤ Bmax := le_trans hCΓ0 (le_max_left _ _)
        have hCΓB : CΓ ≤ Bmax := le_max_left _ _
        have hCjB : Cj ≤ Bmax := le_max_right _ _
        set P : ℝ := (2 : ℝ) ^ j * Bmax * Bmax with hPdef
        have hP0 : 0 ≤ P := by positivity
        set Eb : ℝ := max Cj (max ((k : ℝ) * ((Module.finrank ℝ E : ℝ) * P))
          ((Module.finrank ℝ E : ℝ) * P)) with hEbdef
        have hEb0 : 0 ≤ Eb := le_trans hCj0 (le_max_left _ _)
        set Dtot : ℝ := 16 * Eb with hDtotdef
        have hDtot0 : 0 ≤ Dtot := by rw [hDtotdef]; positivity
        -- bound for a product of a background Christoffel symbol and an `aCovArr` entry
        have hprod : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (p q e : Fin (Module.finrank ℝ E))
            (m' : ℕ), m' + j ≤ k → ∀ (v : Fin m' → Fin (Module.finrank ℝ E))
            (a b c : Fin (Module.finrank ℝ E)),
            ‖iteratedFDeriv ℝ j (fun y' : E => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p q e
              * aCovArr (I := I) (M := M) G x₀ t m' v a b c y') y‖ ≤ P := by
          intro t ht y hy p q e m' hm' v a b c
          refine norm_iteratedFDeriv_mul_le_at_le (k := j) (m := j) le_rfl
            (hsm0 y hy q e p) (hsm t ht y hy m' v a b c) hBmax0 ?_ ?_
          · intro i hi
            exact le_trans (hCΓ i (by omega) y hy q e p) hCΓB
          · intro i hi
            exact le_trans (hCj t ht y hy i (by omega) m' (by omega) v a b c) hCjB
        -- bound for the derivative function, by the recursion
        have hderiv : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (m : ℕ), m + (j + 1) ≤ k →
            ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (a b c d : Fin (Module.finrank ℝ E)),
            ‖iteratedFDeriv ℝ j (fun y' : E => fderiv ℝ (fun y'' : E =>
                aCovArr (I := I) (M := M) G x₀ t m v a b c y'') y'
                (Work.Diff.GE.cBasis (E := E) d)) y‖ ≤ Dtot := by
          intro t ht y hy m hm v a b c d
          have hm1 : m + 1 + j ≤ k := by omega
          have hid : (fun y' : E => fderiv ℝ (fun y'' : E =>
                aCovArr (I := I) (M := M) G x₀ t m v a b c y'') y'
                (Work.Diff.GE.cBasis (E := E) d))
              = fun y' : E => aCovArr (I := I) (M := M) G x₀ t (m + 1) (Fin.cons d v) a b c y'
                + (∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
                    Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (v r) d
                      * aCovArr (I := I) (M := M) G x₀ t m (Function.update v r p) a b c y')
                + (∑ p : Fin (Module.finrank ℝ E),
                    Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p a d
                      * aCovArr (I := I) (M := M) G x₀ t m v p b c y')
                + (∑ p : Fin (Module.finrank ℝ E),
                    Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p b d
                      * aCovArr (I := I) (M := M) G x₀ t m v a p c y')
                + (∑ p : Fin (Module.finrank ℝ E),
                    Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p c d
                      * aCovArr (I := I) (M := M) G x₀ t m v a b p y') := by
            funext y'
            exact fderiv_aCovArr_eq G x₀ t m d v a b c y'
          -- smoothness of the five summands
          have hsmB : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
              aCovArr (I := I) (M := M) G x₀ t (m + 1) (Fin.cons d v) a b c y') y :=
            hsm t ht y hy (m + 1) (Fin.cons d v) a b c
          have hsmS1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ r : Fin m,
              ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (v r) d
                  * aCovArr (I := I) (M := M) G x₀ t m (Function.update v r p) a b c y') y :=
            ContDiffAt.sum fun r _ => ContDiffAt.sum fun p _ =>
              ContDiffAt.mul (hsm0 y hy (v r) d p) (hsm t ht y hy m (Function.update v r p) a b c)
          have hsmS2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p a d
                  * aCovArr (I := I) (M := M) G x₀ t m v p b c y') y :=
            ContDiffAt.sum fun p _ =>
              ContDiffAt.mul (hsm0 y hy a d p) (hsm t ht y hy m v p b c)
          have hsmS3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p b d
                  * aCovArr (I := I) (M := M) G x₀ t m v a p c y') y :=
            ContDiffAt.sum fun p _ =>
              ContDiffAt.mul (hsm0 y hy b d p) (hsm t ht y hy m v a p c)
          have hsmS4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p c d
                  * aCovArr (I := I) (M := M) G x₀ t m v a b p y') y :=
            ContDiffAt.sum fun p _ =>
              ContDiffAt.mul (hsm0 y hy c d p) (hsm t ht y hy m v a b p)
          -- the individual bounds
          have hBd : ‖iteratedFDeriv ℝ j (fun y' : E =>
              aCovArr (I := I) (M := M) G x₀ t (m + 1) (Fin.cons d v) a b c y') y‖ ≤ Cj :=
            hCj t ht y hy j le_rfl (m + 1) hm1 (Fin.cons d v) a b c
          have hS1d : ‖iteratedFDeriv ℝ j (fun y' : E => ∑ r : Fin m,
              ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (v r) d
                  * aCovArr (I := I) (M := M) G x₀ t m (Function.update v r p) a b c y') y‖
              ≤ (m : ℝ) * ((Module.finrank ℝ E : ℝ) * P) := by
            refine le_trans (norm_iteratedFDeriv_sum_le_at (E := E)
              (s := (Finset.univ : Finset (Fin m)))
              (φ := fun r y' => ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (v r) d
                  * aCovArr (I := I) (M := M) G x₀ t m (Function.update v r p) a b c y')
              (x := y) (n := j) (C := (Module.finrank ℝ E : ℝ) * P) ?_ ?_) ?_
            · intro r _
              exact ContDiffAt.sum fun p _ =>
                ContDiffAt.mul (hsm0 y hy (v r) d p) (hsm t ht y hy m (Function.update v r p) a b c)
            · intro r _
              refine le_trans (norm_iteratedFDeriv_sum_le_at (E := E)
                (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
                (φ := fun p y' => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (v r) d
                  * aCovArr (I := I) (M := M) G x₀ t m (Function.update v r p) a b c y')
                (x := y) (n := j) (C := P) ?_ ?_) ?_
              · intro p _
                exact ContDiffAt.mul (hsm0 y hy (v r) d p)
                  (hsm t ht y hy m (Function.update v r p) a b c)
              · intro p _
                exact hprod t ht y hy p (v r) d m (by omega) (Function.update v r p) a b c
              · simp
            · simp
          have hS2d : ‖iteratedFDeriv ℝ j (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p a d
                  * aCovArr (I := I) (M := M) G x₀ t m v p b c y') y‖
              ≤ (Module.finrank ℝ E : ℝ) * P := by
            refine le_trans (norm_iteratedFDeriv_sum_le_at (E := E)
              (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
              (φ := fun p y' => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p a d
                * aCovArr (I := I) (M := M) G x₀ t m v p b c y')
              (x := y) (n := j) (C := P) ?_ ?_) ?_
            · intro p _
              exact ContDiffAt.mul (hsm0 y hy a d p) (hsm t ht y hy m v p b c)
            · intro p _
              exact hprod t ht y hy p a d m (by omega) v p b c
            · simp
          have hS3d : ‖iteratedFDeriv ℝ j (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p b d
                  * aCovArr (I := I) (M := M) G x₀ t m v a p c y') y‖
              ≤ (Module.finrank ℝ E : ℝ) * P := by
            refine le_trans (norm_iteratedFDeriv_sum_le_at (E := E)
              (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
              (φ := fun p y' => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p b d
                * aCovArr (I := I) (M := M) G x₀ t m v a p c y')
              (x := y) (n := j) (C := P) ?_ ?_) ?_
            · intro p _
              exact ContDiffAt.mul (hsm0 y hy b d p) (hsm t ht y hy m v a p c)
            · intro p _
              exact hprod t ht y hy p b d m (by omega) v a p c
            · simp
          have hS4d : ‖iteratedFDeriv ℝ j (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p c d
                  * aCovArr (I := I) (M := M) G x₀ t m v a b p y') y‖
              ≤ (Module.finrank ℝ E : ℝ) * P := by
            refine le_trans (norm_iteratedFDeriv_sum_le_at (E := E)
              (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
              (φ := fun p y' => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p c d
                * aCovArr (I := I) (M := M) G x₀ t m v a b p y')
              (x := y) (n := j) (C := P) ?_ ?_) ?_
            · intro p _
              exact ContDiffAt.mul (hsm0 y hy c d p) (hsm t ht y hy m v a b p)
            · intro p _
              exact hprod t ht y hy p c d m (by omega) v a b p
            · simp
          -- the common bound and the five-term combination
          have hmk' : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : m ≤ k)
          have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by positivity
          have hB' : ‖iteratedFDeriv ℝ j (fun y' : E =>
              aCovArr (I := I) (M := M) G x₀ t (m + 1) (Fin.cons d v) a b c y') y‖ ≤ Eb :=
            le_trans hBd (le_max_left _ _)
          have hS1' : ‖iteratedFDeriv ℝ j (fun y' : E => ∑ r : Fin m,
              ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (v r) d
                  * aCovArr (I := I) (M := M) G x₀ t m (Function.update v r p) a b c y') y‖ ≤ Eb := by
            refine le_trans hS1d ?_
            refine le_trans (mul_le_mul_of_nonneg_right hmk' (by positivity)) ?_
            exact le_trans (le_max_left _ _) (le_max_right _ _)
          have hS2' : ‖iteratedFDeriv ℝ j (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p a d
                  * aCovArr (I := I) (M := M) G x₀ t m v p b c y') y‖ ≤ Eb :=
            le_trans hS2d (le_trans (le_max_right _ _) (le_max_right _ _))
          have hS3' : ‖iteratedFDeriv ℝ j (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p b d
                  * aCovArr (I := I) (M := M) G x₀ t m v a p c y') y‖ ≤ Eb :=
            le_trans hS3d (le_trans (le_max_right _ _) (le_max_right _ _))
          have hS4' : ‖iteratedFDeriv ℝ j (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p c d
                  * aCovArr (I := I) (M := M) G x₀ t m v a b p y') y‖ ≤ Eb :=
            le_trans hS4d (le_trans (le_max_right _ _) (le_max_right _ _))
          rw [hid, hDtotdef]
          exact norm_iteratedFDeriv_add5_le_at (n := j) (C := Eb) hsmB hsmS1 hsmS2 hsmS3 hsmS4
            hB' hS1' hS2' hS3' hS4'
        -- the level `j + 1` bound
        set Cnew : ℝ := max Cj (Cbs * ((Fintype.card
            (Fin (j + 1) → Fin (Module.finrank ℝ E)) : ℝ) * (Dtot * Kb ^ j))) with hCnewdef
        have hCnew0 : 0 ≤ Cnew := by
          rw [hCnewdef]
          exact le_trans hCj0 (le_max_left _ _)
        refine ⟨Cnew, ?_, ?_⟩
        · have h4 : (0 : ℝ) ≤ Kb ^ j := pow_nonneg (le_trans zero_le_one (le_max_left _ _)) j
          have h6 : (0 : ℝ) ≤ (Fintype.card (Fin (j + 1) → Fin (Module.finrank ℝ E)) : ℝ) := by positivity
          have h7 : Cbs * ((Fintype.card (Fin (j + 1) → Fin (Module.finrank ℝ E)) : ℝ)
              * (Dtot * Kb ^ j)) ≥ 0 := by positivity
          rw [hCnewdef]
          exact le_max_of_le_left hCj0
        · intro t ht y hy i hi m hm v a b c
          rcases lt_or_eq_of_le hi with hlt | heq
          · exact le_trans (hCj t ht y hy i (by omega) m (by omega) v a b c) (le_max_left _ _)
          · subst heq
            have hbs := hCbs (j + 1) (by omega)
              (fun y' : E => aCovArr (I := I) (M := M) G x₀ t m v a b c y') y
            refine le_trans hbs ?_
            have hterm : ∀ ρ : Fin (j + 1) → Fin (Module.finrank ℝ E),
                ‖iteratedFDeriv ℝ (j + 1)
                  (fun y' : E => aCovArr (I := I) (M := M) G x₀ t m v a b c y') y
                  (fun s => Module.finBasis ℝ E (ρ s))‖
                  ≤ Dtot * Kb ^ j := by
              intro ρ
              rw [iteratedFDeriv_succ_apply_right (𝕜 := ℝ)
                (f := fun y' : E => aCovArr (I := I) (M := M) G x₀ t m v a b c y') (x := y) (n := j)
                (m := fun s : Fin (j + 1) => Module.finBasis ℝ E (ρ s))]
              rw [iteratedFDeriv_clm_apply_const (E := E) (F := E) (G := ℝ)
                (Ψ := fun y' : E => fderiv ℝ (fun y'' : E =>
                  aCovArr (I := I) (M := M) G x₀ t m v a b c y'') y')
                (x := y) (n := j) (ζ := Module.finBasis ℝ E (ρ (Fin.last j)))
                (v := Fin.init (fun s : Fin (j + 1) => Module.finBasis ℝ E (ρ s)))
                ((hsm t ht y hy m v a b c).fderiv_right (by simp))]
              refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
              have hprod : ∏ s : Fin j,
                  ‖(Fin.init (fun s : Fin (j + 1) => Module.finBasis ℝ E (ρ s))) s‖ ≤ Kb ^ j := by
                calc ∏ s : Fin j,
                      ‖(Fin.init (fun s : Fin (j + 1) => Module.finBasis ℝ E (ρ s))) s‖
                    ≤ ∏ _s : Fin j, Kb := by
                      gcongr with s _
                      exact hKbnorm _
                  _ = Kb ^ j := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
              exact mul_le_mul (hderiv t ht y hy m hm v a b c (ρ (Fin.last j))) hprod
                (by positivity) (by positivity)
            calc Cbs * ∑ ρ : Fin (j + 1) → Fin (Module.finrank ℝ E),
                  ‖iteratedFDeriv ℝ (j + 1)
                    (fun y' : E => aCovArr (I := I) (M := M) G x₀ t m v a b c y') y
                    (fun s => Module.finBasis ℝ E (ρ s))‖
                ≤ Cbs * ∑ _ρ : Fin (j + 1) → Fin (Module.finrank ℝ E),
                    (Dtot * Kb ^ j) :=
                  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ρ _ => hterm ρ) hCbs0
              _ = Cbs * ((Fintype.card (Fin (j + 1) → Fin (Module.finrank ℝ E)) : ℝ)
                    * (Dtot * Kb ^ j)) := by
                  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
              _ ≤ Cnew := by
                  rw [hCnewdef]
                  exact le_max_right _ _
  -- the level `k` bound gives the result
  obtain ⟨Ck, hCk0, hCk⟩ := key k le_rfl
  refine ⟨Ck, hCk0, fun t ht y hy m hm i j l => ?_⟩
  have h := hCk t ht y hy m hm 0 (by omega) (Fin.elim0) i j l
  simpa only [aCovArr] using h

end Work.Diff.EXT
