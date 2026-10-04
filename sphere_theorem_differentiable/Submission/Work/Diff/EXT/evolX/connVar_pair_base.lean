import Mathlib
import Submission.Work.Diff.EXT.evolX.connVarPairDefs
import Submission.Work.Diff.EXT.evolX.connVarPairIns
import Submission.Work.Diff.EXT.evolCompK_one
import Submission.Work.Diff.Evol.covDLC_B_identity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The value form of the connection-variation pairing

`Work.Diff.EXT.evolX.connVar_pair_jets` bounds the jets of the pairing
`(V, W, Z) ↦ y ↦ g_y(dLC G t V W y, Z y)` of the first variation of the Levi-Civita connection
along a Ricci flow.  This module proves the **base case**, i.e. the pointwise identity behind it:
along a Ricci flow, near the base point and in any frame which is orthonormal near it, the pairing
is minus the sum of the three frame traces of `∇Rm`

`⟪∂ₜ∇_V W, Z⟫ = −(tr ∇Rm(·, V, ·, W, Z) + tr ∇Rm(·, W, ·, V, Z) − tr ∇Rm(·, Z, ·, V, W))`,

the traces being taken in the two curvature slots `1` and `3`.

## Route

* `Work.Diff.Evol.covDLC_B_dLC_pairing_ric` writes the pairing as minus the combination of the
  three `∇Ric` patterns `dRicPhi` (Koszul's formula differentiated in `t`, using `∂ₜ g = −2 Ric`);
* `Work.Diff.Evol.covDLC_B_dRicPhi_eq_sum_covRm_field` identifies each `dRicPhi` with the frame
  trace of `∇Rm` (tensoriality of `∇Ric`);
* `Work.Diff.EXT.ckt_one_eq_covRm` identifies that trace with the level-`1` tower `ckt g 1` on the
  insertion pattern `cvHins ρ Z e_m`, which is what `cvTr0ρ` sums.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

/-! ## The insertion patterns at level `0`, as `5`-blocks -/

section Blocks

variable {α : Type*}

/-! The values of the three slot permutations on the three indices. -/

@[simp] theorem cvRho2_zero : cvRho2 (0 : Fin 3) = 1 := by decide
@[simp] theorem cvRho2_one : cvRho2 (1 : Fin 3) = 0 := by decide
@[simp] theorem cvRho2_two : cvRho2 (2 : Fin 3) = 2 := by decide

@[simp] theorem cvRho3_zero : cvRho3 (0 : Fin 3) = 2 := by decide
@[simp] theorem cvRho3_one : cvRho3 (1 : Fin 3) = 0 := by decide
@[simp] theorem cvRho3_two : cvRho3 (2 : Fin 3) = 1 := by decide

/-- **The level-`0` insertion is the `5`-block**: `cvHins ρ Z u = (Z (ρ 0), u, Z (ρ 1), u, Z (ρ 2))`
(the first `a = 0` differentiation slots are empty). -/
theorem cvHins_zero (ρ : Fin 3 ≃ Fin 3) (Z : Fin 3 → α) (u : α) :
    cvHins (a := 0) ρ Z u = cvIns5 (fun t : Fin 3 => Z (ρ t)) u := by
  funext j
  fin_cases j <;> simp [cvHins, cvIns5, Fin.append, Fin.addCases]

/-- The insertion of the first `∇Ric` term: `(Z 0, u, Z 1, u, Z 2)`. -/
theorem cvHins_cvRho1 (Z : Fin 3 → α) (u : α) :
    cvHins (a := 0) cvRho1 Z u = cvIns5 Z u := by
  have h : (fun t : Fin 3 => Z (cvRho1 t)) = Z := by
    funext t
    fin_cases t <;> simp [cvRho1]
  rw [cvHins_zero, h]

/-- The insertion of the second `∇Ric` term: `(Z 1, u, Z 0, u, Z 2)`. -/
theorem cvHins_cvRho2 (Z : Fin 3 → α) (u : α) :
    cvHins (a := 0) cvRho2 Z u = cvIns5 (cvSw3 Z) u := by
  have h : (fun t : Fin 3 => Z (cvRho2 t)) = cvSw3 Z := by
    funext t
    fin_cases t <;> simp [cvSw3]
  rw [cvHins_zero, h]

/-- The insertion of the third `∇Ric` term: `(Z 2, u, Z 0, u, Z 1)`. -/
theorem cvHins_cvRho3 (Z : Fin 3 → α) (u : α) :
    cvHins (a := 0) cvRho3 Z u = cvIns5 (cvCyc3 Z) u := by
  have h : (fun t : Fin 3 => Z (cvRho3 t)) = cvCyc3 Z := by
    funext t
    fin_cases t <;> simp [cvRho3, cvCyc3]
  rw [cvHins_zero, h]

end Blocks

/-! ## The trace identity for `∇Ric` in the `EXT` vocabulary -/

section Trace

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- The `5`-block `cvIns5 Z u` is a tuple of smooth fields when `Z` and `u` are smooth. -/
theorem smoothF_cvIns5 (Z : Fin 3 → TField (I := I) (M := M))
    (hZ : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (Z i))
    (u : TField (I := I) (M := M)) (hu : Work.Diff.EXT.SmoothF (I := I) (M := M) u) :
    ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (cvIns5 Z u i) := by
  intro i
  fin_cases i <;> simp [cvIns5] <;>
    first
      | exact hZ 0
      | exact hZ 1
      | exact hZ 2
      | exact hu

/-- **The trace of the level-`1` tower is the trace of `∇Rm`**: for every permutation `ρ` of the
three free slots, `cvTr0ρ g ef ρ Z y` is the metric trace of `∇Rm` along `ef`, the frame vector
sitting in the two curvature slots `1` and `3`, and the free arguments `Z (ρ 0), Z (ρ 1), Z (ρ 2)`
sitting in the remaining three. -/
theorem cvTr0ρ_eq_sum_covRm (hLC : LCSmooth I M) (g : SMet I M)
    (ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (hef : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (ef i))
    (Z : Fin 3 → TField (I := I) (M := M))
    (hZ : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (Z i))
    (y : M) (ρ : Fin 3 ≃ Fin 3) :
    cvTr0ρ g ef ρ Z y
      = ∑ m, covRm g y (Z (ρ 0) y) (ef m y) (Z (ρ 1) y) (ef m y) (Z (ρ 2) y) := by
  simp only [cvTr0ρ]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hW : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M)
      (cvIns5 (fun t : Fin 3 => Z (ρ t)) (ef m) i) :=
    smoothF_cvIns5 (fun t : Fin 3 => Z (ρ t)) (fun t => hZ (ρ t)) (ef m) (hef m)
  rw [show cvHins (a := 0) ρ Z (ef m) = cvIns5 (fun t : Fin 3 => Z (ρ t)) (ef m) from
    cvHins_zero ρ Z (ef m)]
  exact Work.Diff.EXT.ckt_one_eq_covRm hLC g _ hW y

end Trace

/-! ## The three traces of the pairing -/

section PairTraces

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

theorem cvTr0ρ_cvRho1 (hLC : LCSmooth I M) (g : SMet I M)
    (ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (hef : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (ef i))
    (Z : Fin 3 → TField (I := I) (M := M))
    (hZ : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (Z i)) (y : M) :
    cvTr0ρ g ef cvRho1 Z y
      = ∑ m, covRm g y (Z 0 y) (ef m y) (Z 1 y) (ef m y) (Z 2 y) := by
  rw [cvTr0ρ_eq_sum_covRm hLC g ef hef Z hZ y cvRho1]
  simp [cvRho1]

/-- The second `∇Ric` term as a frame trace of `∇Rm`. -/
theorem cvTr0ρ_cvRho2 (hLC : LCSmooth I M) (g : SMet I M)
    (ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (hef : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (ef i))
    (Z : Fin 3 → TField (I := I) (M := M))
    (hZ : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (Z i)) (y : M) :
    cvTr0ρ g ef cvRho2 Z y
      = ∑ m, covRm g y (Z 1 y) (ef m y) (Z 0 y) (ef m y) (Z 2 y) := by
  rw [cvTr0ρ_eq_sum_covRm hLC g ef hef Z hZ y cvRho2]
  simp

/-- The third `∇Ric` term as a frame trace of `∇Rm`. -/
theorem cvTr0ρ_cvRho3 (hLC : LCSmooth I M) (g : SMet I M)
    (ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (hef : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (ef i))
    (Z : Fin 3 → TField (I := I) (M := M))
    (hZ : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (Z i)) (y : M) :
    cvTr0ρ g ef cvRho3 Z y
      = ∑ m, covRm g y (Z 2 y) (ef m y) (Z 0 y) (ef m y) (Z 1 y) := by
  rw [cvTr0ρ_eq_sum_covRm hLC g ef hef Z hZ y cvRho3]
  simp [cvRho3]

end PairTraces

/-! ## The target -/

theorem connVar_pair_base
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x : M)
    {ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hef : Work.Diff.EXT.IsFrameNear (I := I) (M := M) (G t) x ef)
    (Z : Fin 3 → Work.Diff.EXT.TField (I := I) (M := M))
    (hZ : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (Z i)) :
    (Work.Diff.EXT.evolX.cvPairOp (I := I) (M := M) G t Z) =ᶠ[nhds x]
      (fun y => -(((Work.Diff.EXT.evolX.cvTr0ρ (I := I) (M := M) (G t) ef
            Work.Diff.EXT.evolX.cvRho1) Z y)
        + ((Work.Diff.EXT.evolX.cvTr0ρ (I := I) (M := M) (G t) ef
            Work.Diff.EXT.evolX.cvRho2) Z y)
        - ((Work.Diff.EXT.evolX.cvTr0ρ (I := I) (M := M) (G t) ef
            Work.Diff.EXT.evolX.cvRho3) Z y))) := by
  classical
  have hZs : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (Z i) := hZ
  have hEfs : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (ef i) := hef.1
  -- the time interval is open and the flow is jointly smooth on it
  have hJopen : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  have hJs : Submission.Diff.JointSmooth G (Set.Ioo (0 : ℝ) T) :=
    hflow.1.mono (Set.prod_mono Set.Ioo_subset_Ico_self (Subset.refl _))
  -- `∂ₜ g = -2 Ric` at the interior time `t`
  have hdt : ∀ (y : M) (u v : TangentSpace I y),
      Submission.Diff.dtMet G t y u v = -2 * Submission.Diff.ricAt (lcOf (G t)) y u v := by
    intro y u v
    have hnb : Set.Ico (0 : ℝ) T ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ico_self
    have hd := hflow.2 t ⟨le_of_lt ht.1, ht.2⟩ y u v
    rw [Submission.Diff.dtMet, (hd.hasDerivAt hnb).deriv]
  filter_upwards [hef.2] with y hy
  -- the pairing identity (Koszul, differentiated in `t`)
  have hp := Work.Diff.Evol.covDLC_B_dLC_pairing_ric (I := I) (M := M) hLV hJopen hJs ht hdt
    (Z 0) (Z 1) (Z 2) (hZs 0) (hZs 1) (hZs 2) y
  -- each `dRicPhi` is a frame trace of `∇Rm`
  have h1 := Work.Diff.Evol.covDLC_B_dRicPhi_eq_sum_covRm_field (I := I) (M := M) hLC (G t) y
    (Z 0 y) (fun m => ef m y) hy (Z 1) (Z 2) (hZs 1) (hZs 2)
  have h2 := Work.Diff.Evol.covDLC_B_dRicPhi_eq_sum_covRm_field (I := I) (M := M) hLC (G t) y
    (Z 1 y) (fun m => ef m y) hy (Z 0) (Z 2) (hZs 0) (hZs 2)
  have h3 := Work.Diff.Evol.covDLC_B_dRicPhi_eq_sum_covRm_field (I := I) (M := M) hLC (G t) y
    (Z 2 y) (fun m => ef m y) hy (Z 0) (Z 1) (hZs 0) (hZs 1)
  -- the three traces of `∇Rm` are the `cvTr0ρ` sums
  have t1 := cvTr0ρ_cvRho1 hLC (G t) ef hEfs Z hZs y
  have t2 := cvTr0ρ_cvRho2 hLC (G t) ef hEfs Z hZs y
  have t3 := cvTr0ρ_cvRho3 hLC (G t) ef hEfs Z hZs y
  rw [cvPairOp]
  rw [hp, h1, h2, h3, t1, t2, t3]

end Work.Diff.EXT.evolX
