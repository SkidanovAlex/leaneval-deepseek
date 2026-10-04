import Mathlib
import Submission.Work.Diff.EXT.chartData_step_aux
import Submission.Work.Diff.EXT.chartData_contDiffOn
import Submission.Work.Diff.EXT.norm_iteratedFDeriv_le_basisSum
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.EXT.gramInv_jets
import Submission.Work.Diff.EXT.aComp_jets
import Submission.Work.Diff.EXT.cGam_jets

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The one-step a priori estimate for the chart data of a Ricci flow family (`EXT`)

This file proves `Work.Diff.EXT.chartData_step`: the `(k+1)`-st chart jet of the metric `G t` is
bounded on `K` by the `k`-jet bounds of the chart data of `G t`, the `k`-jet bounds of the chart
covariant derivatives (`aCovArr`) of the connection difference, and the `k`-jet bounds of the
background Christoffel symbols `cGam (G 0)`.

The chart data at time `t` is reconstructed from these by the chain

* `GramInv` (the inverse Gram matrix) from the `k`-jets of `GramM` (Cramer's rule);
* `aComp` (the chart array of the lowered connection difference) from the `k`-jet bounds of
  `aCovArr` (`aCovArr` is the recursion for the *covariant* derivatives with respect to the fixed
  background connection `∇^{G 0}`, and inverting the recursion costs only the background
  Christoffel symbols `cGam (G 0)`);
* `cGam (G t)` from `cGam (G 0) + GramInv · aComp` (pure algebra);
* the `(k+1)`-jets of `chartMat` from the derivative identity `hderiv` and the Leibniz rule.

The three first steps are proved in the modules `Work.Diff.EXT.gramInv_jets`,
`Work.Diff.EXT.aComp_jets` and `Work.Diff.EXT.cGam_jets`; the last step is
`Work.Diff.EXT.chartMat_succ_jets_of_data` below.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The coordinate functional `E →L[ℝ] ℝ` of the `m`-th vector of `Module.finBasis`. -/
noncomputable def coordCLM (m : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord m)

theorem coordCLM_apply (m : Fin (Module.finrank ℝ E)) (z : E) :
    coordCLM (E := E) m z = (Module.finBasis ℝ E).coord m z := by
  rw [coordCLM, LinearMap.coe_toContinuousLinearMap']

theorem coordCLM_apply_finBasis (m m' : Fin (Module.finrank ℝ E)) :
    coordCLM (E := E) m (Module.finBasis ℝ E m') = if m = m' then (1 : ℝ) else 0 := by
  rw [coordCLM_apply]
  exact finBasis_coord_finBasis m m'

/-- Evaluation at a vector commutes with finite sums of continuous linear maps. -/
theorem Finset.sum_clm_apply {ι : Type*} (s : Finset ι) (f : ι → (E →L[ℝ] ℝ)) (z : E) :
    (∑ i ∈ s, f i) z = ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

/-- The first derivatives of the chart matrix, as an explicit `CLM`-valued function of the chart
coordinate. -/
noncomputable def PhiFun (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (i j : Fin (Module.finrank ℝ E)) : E → (E →L[ℝ] ℝ) :=
  fun y' => ∑ p : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
    (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m i
        * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') p j
      + Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m j
        * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') i p) • coordCLM (E := E) m

theorem PhiFun_apply_finBasis (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (i j : Fin (Module.finrank ℝ E)) (y' : E) (m : Fin (Module.finrank ℝ E)) :
    PhiFun G x₀ t i j y' (Module.finBasis ℝ E m)
      = ∑ p : Fin (Module.finrank ℝ E),
          (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m i
              * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') p j
            + Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m j
              * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') i p) := by
  rw [show PhiFun G x₀ t i j y'
      = ∑ p : Fin (Module.finrank ℝ E), ∑ m' : Fin (Module.finrank ℝ E),
          (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m' i
              * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') p j
            + Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m' j
              * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') i p)
            • coordCLM (E := E) m' from rfl]
  rw [Finset.sum_clm_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_clm_apply]
  simp only [smul_apply, smul_eq_mul, coordCLM_apply_finBasis]
  rw [Finset.sum_eq_single m]
  · simp
  · intro m' _ hm'
    simp [hm']
  · intro hm
    exact absurd (Finset.mem_univ m) hm

theorem contDiffAt_PhiFun (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hΓ : ∀ (p m : Fin (Module.finrank ℝ E)), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m i) y)
    (hΓ' : ∀ (p m : Fin (Module.finrank ℝ E)), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m j) y)
    (hG : ∀ (a b : Fin (Module.finrank ℝ E)), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') a b) y) :
    ContDiffAt ℝ (⊤ : ℕ∞) (PhiFun G x₀ t i j) y := by
  refine ContDiffAt.sum fun p _ => ContDiffAt.sum fun m _ => ?_
  exact ContDiffAt.smul
    (ContDiffAt.add (ContDiffAt.mul (hΓ p m) (hG p j))
      (ContDiffAt.mul (hΓ' p m) (hG i p))) contDiffAt_const

/-- **The `(k+1)`-jet of the chart matrix, from the `k`-jets of the chart data.** -/
theorem chartMat_succ_jets_of_data
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E) (k : ℕ)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hPh : ∃ CP : ℝ, 0 ≤ CP ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ m ≤ k,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ CP)
    (hGh : ∃ CG : ℝ, 0 ≤ CG ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ m ≤ k,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.cGam (G t) x₀
          (pt (I := I) x₀ y') l i j) y‖ ≤ CG)
    (hsmΓ : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G t) x₀
        (pt (I := I) x₀ y') l i j) y)
    (hsmM : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.GramM G x₀ t
        (pt (I := I) x₀ y') i j) y)
    (hderiv : ∀ t ∈ Set.Ico σ T, ∀ y ∈ (extChartAt I x₀).target,
      ∀ (i j m : Fin (Module.finrank ℝ E)),
      fderiv ℝ (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y
          (Module.finBasis ℝ E m)
        = ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) p m i
                * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) p j
              + Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) p m j
                * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i p)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ (k + 1)
        (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C := by
  classical
  obtain ⟨CP, hCP0, hCP⟩ := hPh
  obtain ⟨CG, hCG0, hCG⟩ := hGh
  obtain ⟨Cbs, hCbs0, hCbs⟩ := norm_iteratedFDeriv_le_basisSum (E := E) (F := ℝ) (k + 1)
  set Kb : ℝ := max 1 (∑ m : Fin (Module.finrank ℝ E), ‖Module.finBasis ℝ E m‖) with hKbdef
  have hKbnorm : ∀ m : Fin (Module.finrank ℝ E), ‖Module.finBasis ℝ E m‖ ≤ Kb := by
    intro m
    exact le_trans (Finset.single_le_sum (fun i _ => norm_nonneg (Module.finBasis ℝ E i))
      (Finset.mem_univ m)) (le_max_right _ _)
  set Cc : ℝ := max CP CG with hCcdef
  have hCcle : CP ≤ Cc := le_max_left _ _
  have hCGle : CG ≤ Cc := le_max_right _ _
  set L : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cc * Cc with hLdef
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ => by positivity
  -- the Leibniz bound for a product of a `Γ`-component and a `GramM`-component
  have hprod1 : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (p m i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m i
            * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') p j) y‖ ≤ L := by
    intro t ht y hy p m i j
    refine le_trans (norm_iteratedFDeriv_mul_le_at (E := E)
      (f := fun y' : E => Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m i)
      (g := fun y' : E => Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') p j)
      (C := Cc) (hsmΓ t ht y hy m i p) (hsmM t ht y hy p j) ?_ ?_) le_rfl
    · intro i' hi'
      exact le_trans (hCG t ht y hy i' hi' m i p) hCGle
    · intro i' hi'
      exact le_trans (hCP t ht y hy i' hi' p j) hCcle
  have hprod2 : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (p m i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m j
            * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') i p) y‖ ≤ L := by
    intro t ht y hy p m i j
    refine le_trans (norm_iteratedFDeriv_mul_le_at (E := E)
      (f := fun y' : E => Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m j)
      (g := fun y' : E => Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') i p)
      (C := Cc) (hsmΓ t ht y hy m j p) (hsmM t ht y hy i p) ?_ ?_) le_rfl
    · intro i' hi'
      exact le_trans (hCG t ht y hy i' hi' m j p) hCGle
    · intro i' hi'
      exact le_trans (hCP t ht y hy i' hi' i p) hCcle
  -- the bound on the `k`-jets of the components of `PhiFun`
  have hpsi : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j m : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k (fun y' : E => PhiFun G x₀ t i j y' (Module.finBasis ℝ E m)) y‖
        ≤ 2 * ((Module.finrank ℝ E : ℝ) * L) := by
    intro t ht y hy i j m
    have hsmA : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m i
          * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') p j)) y :=
      ContDiffAt.sum fun p _ =>
        ContDiffAt.mul (hsmΓ t ht y hy m i p) (hsmM t ht y hy p j)
    have hsmB : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m j
          * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') i p)) y :=
      ContDiffAt.sum fun p _ =>
        ContDiffAt.mul (hsmΓ t ht y hy m j p) (hsmM t ht y hy i p)
    have hjetA : ‖iteratedFDeriv ℝ k (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m i
          * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') p j)) y‖
        ≤ (Module.finrank ℝ E : ℝ) * L := by
      refine le_trans (norm_iteratedFDeriv_sum_le_at (E := E)
        (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        (φ := fun p y' => Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m i
          * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') p j)
        (x := y) (n := k) (C := L) ?_ ?_) ?_
      · intro p _
        exact ContDiffAt.mul (hsmΓ t ht y hy m i p) (hsmM t ht y hy p j)
      · intro p _
        exact hprod1 t ht y hy p m i j
      · simp
    have hjetB : ‖iteratedFDeriv ℝ k (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m j
          * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') i p)) y‖
        ≤ (Module.finrank ℝ E : ℝ) * L := by
      refine le_trans (norm_iteratedFDeriv_sum_le_at (E := E)
        (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        (φ := fun p y' => Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m j
          * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') i p)
        (x := y) (n := k) (C := L) ?_ ?_) ?_
      · intro p _
        exact ContDiffAt.mul (hsmΓ t ht y hy m j p) (hsmM t ht y hy i p)
      · intro p _
        exact hprod2 t ht y hy p m i j
      · simp
    have hfun_eq : (fun y' : E => PhiFun G x₀ t i j y' (Module.finBasis ℝ E m))
        = fun y' : E => (∑ p : Fin (Module.finrank ℝ E),
              (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m i
                * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') p j))
            + (∑ p : Fin (Module.finrank ℝ E),
              (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m j
                * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') i p)) := by
      funext y'
      rw [PhiFun_apply_finBasis, Finset.sum_add_distrib]
    rw [hfun_eq]
    refine le_trans (norm_iteratedFDeriv_add_le_at (E := E)
      (f := fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m i
          * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') p j))
      (g := fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p m j
          * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') i p))
      (C := (Module.finrank ℝ E : ℝ) * L) hsmA hsmB hjetA hjetB) le_rfl
  -- the final assembly
  refine ⟨Cbs * (Fintype.card (Fin (k + 1) → Fin (Module.finrank ℝ E)) : ℝ)
      * (2 * ((Module.finrank ℝ E : ℝ) * L)) * Kb ^ k, ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg (mul_nonneg hCbs0 (by positivity)) (by positivity)) ?_
    exact pow_nonneg (le_trans zero_le_one (le_max_left _ _)) k
  · intro t ht y hy i j
    have hb := hCbs (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y
    have hfun : (fun y' : E => fderiv ℝ (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y')
        =ᶠ[𝓝 y] PhiFun G x₀ t i j := by
      filter_upwards [(isOpen_extChartAt_target (I := I) x₀).mem_nhds (hKt hy)] with y' hy'
      refine ContinuousLinearMap.ext fun z => ?_
      have hb' : ∀ m : Fin (Module.finrank ℝ E),
          fderiv ℝ (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y'
            (Module.finBasis ℝ E m) = PhiFun G x₀ t i j y' (Module.finBasis ℝ E m) := by
        intro m
        rw [hderiv t ht y' hy' i j m, PhiFun_apply_finBasis]
      have hlin : (fderiv ℝ (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y').toLinearMap
          = (PhiFun G x₀ t i j y').toLinearMap :=
        (Module.finBasis ℝ E).ext fun m => by simpa using hb' m
      exact congrArg (fun L : E →ₗ[ℝ] ℝ => L z) hlin
    have hjet : iteratedFDeriv ℝ k (fun y' : E => fderiv ℝ
          (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y') y
        = iteratedFDeriv ℝ k (PhiFun G x₀ t i j) y :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hfun k).eq_of_nhds
    have hsmPhi : ContDiffAt ℝ (⊤ : ℕ∞) (PhiFun G x₀ t i j) y :=
      contDiffAt_PhiFun G x₀ t i j
        (fun p m => hsmΓ t ht y hy m i p) (fun p m => hsmΓ t ht y hy m j p)
        (fun a b => hsmM t ht y hy a b)
    have hterm : ∀ ρ : Fin (k + 1) → Fin (Module.finrank ℝ E),
        ‖iteratedFDeriv ℝ (k + 1) (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y
          (fun s : Fin (k + 1) => Module.finBasis ℝ E (ρ s))‖
          ≤ (2 * ((Module.finrank ℝ E : ℝ) * L)) * Kb ^ k := by
      intro ρ
      rw [iteratedFDeriv_succ_apply_right (𝕜 := ℝ)
        (f := fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) (x := y) (n := k)
        (m := fun s : Fin (k + 1) => Module.finBasis ℝ E (ρ s))]
      rw [hjet]
      rw [iteratedFDeriv_clm_apply_const (E := E) (F := E) (G := ℝ) (Ψ := PhiFun G x₀ t i j)
        (x := y) (n := k) (ζ := Module.finBasis ℝ E (ρ (Fin.last k)))
        (v := Fin.init (fun s : Fin (k + 1) => Module.finBasis ℝ E (ρ s))) hsmPhi]
      refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
      have hprod : ∏ s : Fin k,
          ‖(Fin.init (fun s : Fin (k + 1) => Module.finBasis ℝ E (ρ s))) s‖ ≤ Kb ^ k := by
        calc ∏ s : Fin k,
              ‖(Fin.init (fun s : Fin (k + 1) => Module.finBasis ℝ E (ρ s))) s‖
            ≤ ∏ _s : Fin k, Kb := by
              gcongr with s _
              exact hKbnorm _
          _ = Kb ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul (hpsi t ht y hy i j (ρ (Fin.last k))) hprod (by positivity) (by positivity)
    calc ‖iteratedFDeriv ℝ (k + 1)
            (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y‖
        ≤ Cbs * ∑ ρ : Fin (k + 1) → Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ (k + 1)
              (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y
              (fun s => Module.finBasis ℝ E (ρ s))‖ := hb
      _ ≤ Cbs * ∑ _ρ : Fin (k + 1) → Fin (Module.finrank ℝ E),
            ((2 * ((Module.finrank ℝ E : ℝ) * L)) * Kb ^ k) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ρ _ => hterm ρ) hCbs0
      _ = Cbs * ((Fintype.card (Fin (k + 1) → Fin (Module.finrank ℝ E)) : ℝ)
            * ((2 * ((Module.finrank ℝ E : ℝ) * L)) * Kb ^ k)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = Cbs * (Fintype.card (Fin (k + 1) → Fin (Module.finrank ℝ E)) : ℝ)
            * (2 * ((Module.finrank ℝ E : ℝ) * L)) * Kb ^ k := by ring

/-- **Smoothness of the chart matrix in the chart coordinate, from the manifold structure.** -/
theorem contDiffAt_chartMat_chart [I.Boundaryless] [T2Space M] (G : ℝ → Submission.Diff.SMet I M)
    (x₀ : M) (t : ℝ) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y :=
  (((chartData_contDiffOn (I := I) (M := M) G x₀ (extChartAt I x₀).target subset_rfl).1 t i j).contDiffAt
    ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy))

/-- **Smoothness of the chart Christoffel symbols, from the manifold structure.** -/
theorem contDiffAt_cGam_chart [I.Boundaryless] [T2Space M] (G : ℝ → Submission.Diff.SMet I M)
    (x₀ : M) (t : ℝ) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i j l : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G t) x₀
      (pt (I := I) x₀ y') l i j) y :=
  (((chartData_contDiffOn (I := I) (M := M) G x₀ (extChartAt I x₀).target subset_rfl).2.1 t i j l).contDiffAt
    ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy))

/-- **Smoothness of the Gram matrix in the chart coordinate.** -/
theorem contDiffAt_GramM_chart [I.Boundaryless] [T2Space M] (G : ℝ → Submission.Diff.SMet I M)
    (x₀ : M) (t : ℝ) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.GramM G x₀ t
      (pt (I := I) x₀ y') i j) y :=
  (((chartData_contDiffOn (I := I) (M := M) G x₀ (extChartAt I x₀).target subset_rfl).2.2 t i j).contDiffAt
    ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy))

/-- **Smoothness of the inverse Gram matrix in the chart coordinate.** -/
theorem contDiffAt_GramInv_chart [I.Boundaryless] [T2Space M] (G : ℝ → Submission.Diff.SMet I M)
    (x₀ : M) (t : ℝ) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (hdet : (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)).det ≠ 0)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.GramInv G x₀ t
      (pt (I := I) x₀ y') i j) y := by
  have hA : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
      (fun a b : Fin (Module.finrank ℝ E) => Work.Diff.GE.GramM G x₀ t
        (pt (I := I) x₀ y') a b : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) y := by
    rw [contDiffAt_pi]
    intro a
    rw [contDiffAt_pi]
    intro b
    exact contDiffAt_GramM_chart G x₀ t hy a b
  have hinv := (contDiffAt_matrix_inv_pi (n := Module.finrank ℝ E)
    (M := fun a b => Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) a b) hdet).comp y hA
  have h4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
      (Matrix.of (fun a b : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') a b))⁻¹ i j) y :=
    (contDiffAt_pi.mp ((contDiffAt_pi.mp hinv) i)) j
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y' => ?_)
  show (Matrix.of (fun a b : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') a b))⁻¹ i j
      = Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y') i j
  rw [Work.Diff.GE.GramInv]
  congr 1

/-- **Smoothness of the chart array of the lowered connection difference.** -/
theorem contDiffAt_aComp_chart [I.Boundaryless] [T2Space M] (G : ℝ → Submission.Diff.SMet I M)
    (x₀ : M) (t : ℝ) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i j l : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => aComp (I := I) (M := M) G x₀ t y' i j l) y := by
  have h : (fun y' : E => aComp (I := I) (M := M) G x₀ t y' i j l)
      = fun y' : E => ∑ m : Fin (Module.finrank ℝ E),
          Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') l m
            * (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') m i j
                - Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') m i j) := rfl
  rw [h]
  refine ContDiffAt.sum fun m _ => ContDiffAt.mul ?_ (ContDiffAt.sub ?_ ?_)
  · exact contDiffAt_GramM_chart G x₀ t hy l m
  · exact contDiffAt_cGam_chart G x₀ t hy i j m
  · exact contDiffAt_cGam_chart G x₀ 0 hy i j m


/-- **Assembly of the one-step estimate.**  Given the conclusions of the three auxiliary estimates
(`GramInv`-, `aComp`- and `cGam`-jets) the `(k+1)`-st chart jet of the metric is bounded. -/
theorem chartData_step_of_children
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target) (k : ℕ)
    (hdet : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      c ≤ (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)).det)
    (hP : ∀ m ≤ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C)
    (hderiv : ∀ t ∈ Set.Ico σ T, ∀ y ∈ (extChartAt I x₀).target,
      ∀ (i j m : Fin (Module.finrank ℝ E)),
      fderiv ℝ (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y
          (Module.finBasis ℝ E m)
        = ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) p m i
                * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) p j
              + Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) p m j
                * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i p))
    (hcGam : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ m ≤ k,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.cGam (G t) x₀
          (pt (I := I) x₀ y') l i j) y‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ (k + 1)
        (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C := by
  obtain ⟨CP, hCP0, hCP⟩ := exists_uniform_bound_of_le (P := fun m C =>
      ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C)
    (fun m C C' hC hle t ht y hy i j => le_trans (hC t ht y hy i j) hle) k hP
  exact chartMat_succ_jets_of_data G σ T x₀ K k hKt ⟨CP, hCP0, fun t ht y hy m hm i j =>
      hCP m hm t ht y hy i j⟩ hcGam
    (fun t ht y hy i j l => contDiffAt_cGam_chart G x₀ t (hKt hy) i j l)
    (fun t ht y hy i j => contDiffAt_GramM_chart G x₀ t (hKt hy) i j) hderiv

theorem chartData_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target) (hU : UniqueDiffOn ℝ K) (k : ℕ)
    (hcore : ∀ m ≤ k, ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
        |Work.Diff.EXT.aCovArr (I := I) (M := M) G x₀ t m v i j l y| ≤ Cm)
    (hcGam0 : ∀ m ≤ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (Work.Diff.EXT.pt (I := I) x₀ y') l i j) y‖ ≤ C)
    (hdet : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      c ≤ (Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y)).det)
    (hsmM : ∀ t ∈ Set.Ico σ T, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) K)
    (hsmG : ∀ t ∈ Set.Ico σ T, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G t) x₀
        (Work.Diff.EXT.pt (I := I) x₀ y') l i j) K)
    (hderiv : ∀ t ∈ Set.Ico σ T, ∀ y ∈ (extChartAt I x₀).target,
      ∀ (i j m : Fin (Module.finrank ℝ E)),
      fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
          (Module.finBasis ℝ E m)
        = ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m i
                * Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) p j
              + Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m j
                * Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i p))
    (hP : ∀ m ≤ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j)
          y‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ (k + 1)
          (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C := by
  have hsmM : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.GramM G x₀ t
        (pt (I := I) x₀ y') i j) y :=
    fun t ht y hy i j => contDiffAt_GramM_chart G x₀ t (hKt hy) i j
  have hsm0 : ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
        (pt (I := I) x₀ y') l i j) y :=
    fun y hy i j l => contDiffAt_cGam_chart G x₀ 0 (hKt hy) i j l
  have hsmA : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => aComp (I := I) (M := M) G x₀ t y' i j l) y :=
    fun t ht y hy i j l => contDiffAt_aComp_chart G x₀ t (hKt hy) i j l
  have hsmGInv : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.GramInv G x₀ t
        (pt (I := I) x₀ y') i j) y := by
    intro t ht y hy i j
    obtain ⟨c, hc0, hc⟩ := hdet
    refine contDiffAt_GramInv_chart G x₀ t (hKt hy) ?_ i j
    have h := hc t ht y hy
    intro hzero
    rw [hzero] at h
    linarith
  have hgramInv := gramInv_jets G σ T x₀ K k hKt hdet hsmM hP
  have haComp := aComp_jets G σ T x₀ K k hKt hcore hcGam0 hsm0 hsmA
  have hcGam' := cGam_jets G σ T x₀ K k hKt hdet hcGam0 hgramInv haComp hsm0 hsmGInv hsmA
  exact chartData_step_of_children G σ T x₀ K hKt k hdet hP hderiv hcGam'

end Work.Diff.EXT
