import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HkNorm_Dz_le_open
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.HkMem_Dz_pth_of_diag =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `D_z ∂_θ V ∈ ℋ^k` from `D_z ∂_θ² V ∈ ℋ^k`

This module proves `Work.FTS.EllSol.PkgK5.HkMem_Dz_pth_of_diag`: on the open quadrant
`(0,∞) × (0,π/2)`, the *angular Hardy/Poincaré descent*

  `D_z ∂_θ² V ∈ ℋ^k  ⟹  D_z ∂_θ V ∈ ℋ^k`

for `V` of class `C^∞` on the open quadrant whose angular `D_z`-slices `D_z^j V z ·`
(`j ≤ k+1`, `z > 0`) vanish at both endpoints `θ = 0, π/2` in the sense of *limits*, and with
`D_z ∂_θ²V` honestly in `ℋ^k` (`0 < α ≤ 1/4`).

## Route

Both `D_z` and `∂_θ` only see the *open* quadrant, and on it they commute (Clairaut):

  `∂_θ (D_z^j V) = D_z^j (∂_θ V)`      (`ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen`),

so, as functions on `(0,∞) × (0,π/2)`,

  `∂_θ² (D_z V) = ∂_θ (D_z (∂_θ V)) = D_z (∂_θ² V)`,
  `∂_θ (D_z V) = D_z (∂_θ V)`.

Since `ℋ^k`-membership only depends on the values on the open quadrant
(`RPFresh.HkMem_of_agreeOnQ`), the assertion is therefore the *per-slice* angular Poincaré
descent for the single function `f := D_z V`:

  `∂_θ² f ∈ ℋ^k  ⟹  ∂_θ f ∈ ℋ^k`,

which is `VopAux.thetaPoincareOpenTrace`, the trace (limit) form of the angular
Hardy inequality `∫ |∂_θ f|²  ≲ ∫ |∂_θ² f|²` — the vanishing of the angular slices of
`D_z^j f = D_z^{j+1} V` at `θ = 0, π/2` for `j ≤ k` being exactly the hypothesis on `V` at
levels `≤ k+1`.

Everything rests on `[propext, Classical.choice, Quot.sound]`: the three inputs
`thetaPoincareOpenTrace`, `HkMem_of_agreeOnQ` and `pth_DzIter_eqOn_of_isOpen` are
`sorry`-free.
-/

namespace Work.FTS.EllSol.PkgK5

set_option linter.unusedVariables false

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Auxiliary facts -/

/-- Composition of `DzIter` with the outermost `D_z`: `D_z^j (D_z V) = D_z^{j+1} V`. -/
private lemma DzIter_Dz_eq (j : ℕ) (V : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (Work.Spaces.Dz V) = Work.Spaces.DzIter (j + 1) V := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Work.Spaces.DzIter_succ]; exact congrArg Work.Spaces.Dz ih

/-- `AgreeOnQ` from an `EqOn` on the open quadrant. -/
private lemma agreeOnQ_of_eqOn_Q0 {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    Work.FTS.EllipticEst.AgreeOnQ F G :=
  fun z θ hz hθ hlt => h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩)

/-- `AgreeOnQ` is symmetric (it is an equality on the open quadrant). -/
private lemma agreeOnQ_symm {F G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.AgreeOnQ F G) :
    Work.FTS.EllipticEst.AgreeOnQ G F :=
  fun z θ hz hθ hlt => (h z θ hz hθ hlt).symm

/-- `AgreeOnQ` is transitive (it is an equality on the open quadrant). -/
private lemma agreeOnQ_trans {F G H : ℝ → ℝ → ℝ} (h1 : Work.FTS.EllipticEst.AgreeOnQ F G)
    (h2 : Work.FTS.EllipticEst.AgreeOnQ G H) : Work.FTS.EllipticEst.AgreeOnQ F H :=
  fun z θ hz hθ hlt => (h1 z θ hz hθ hlt).trans (h2 z θ hz hθ hlt)

theorem HkMem_Dz_pth_of_diag (k : ℕ) (hk : 1 ≤ k) :
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pthIter 2 V)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)) := by
  intro α V hα0 hα4 hV hV0 hVpi htr hmem
  obtain ⟨C, _hCpos, hC⟩ := Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace k
  -- `V` and `∂_θV` are `C^n` on the open quadrant for every `n`
  have hsmV : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry V) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.forall hV
  have hsmPthV : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth V))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.forall (Work.FTS.EllipticEst.SmoothOpen.pth hV)
  -- Clairaut on the open quadrant: `∂_θ (D_z V) = D_z (∂_θ V)`
  have hcl1 : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pth (Work.Spaces.Dz V))
      (Work.Spaces.Dz (Work.Spaces.pth V)) :=
    agreeOnQ_of_eqOn_Q0
      (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
        Work.FTS.EllipticEst.isOpen_Q0 hsmV 1)
  -- and `∂_θ (D_z (∂_θ V)) = D_z (∂_θ² V)`
  have hcl2 : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.pth V)))
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth V))) :=
    agreeOnQ_of_eqOn_Q0
      (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
        Work.FTS.EllipticEst.isOpen_Q0 hsmPthV 1)
  -- hence `pth (pth (Dz V))` and `pth (Dz (pth V))` agree too
  have hcl1p : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz V)))
      (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.pth V))) := hcl1.pth
  -- Step 1: `D_z ∂_θ²V ∈ ℋ^k` implies `∂_θ² (D_z V) ∈ ℋ^k` (same function off the null set)
  have hmemA : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Spaces.Dz V)) :=
    Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ
      (agreeOnQ_trans (agreeOnQ_symm hcl2) (agreeOnQ_symm hcl1p)) hmem
  -- Step 2: the trace hypothesis for `D_z V` (`DzIter j (Dz V) = DzIter (j+1) V`)
  have htr' : ∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Spaces.Dz V) z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Spaces.Dz V) z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    intro j hj z hz
    have h := htr (j + 1) (by omega) z hz
    simpa only [DzIter_Dz_eq j V] using h
  have hsmDzV : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz V))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.forall (Work.FTS.EllipticEst.SmoothOpen.Dz hV)
  -- Step 3: the angular Poincaré descent for `f := D_z V`
  have hB : Work.Spaces.HkMem α k (Work.Spaces.pth (Work.Spaces.Dz V)) :=
    (hC α (Work.Spaces.Dz V) hα0 hα4 hsmDzV htr' hmemA).2.1
  -- Step 4: transport back across the open quadrant, `∂_θ (D_z V) = D_z (∂_θ V)`
  exact Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ hcl1 hB

end Work.FTS.EllSol.PkgK5
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.uopDzIter2Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## The elementary split `D_z²X = D_zX + z²∂_z²X` on the open quadrant -/

private lemma dzIter2_eq (X : ℝ → ℝ → ℝ) (hX : Work.FTS.EllipticEst.SmoothOpen X)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hlt : θ < Real.pi / 2) :
    Work.Spaces.DzIter 2 X z θ
      = Work.Spaces.Dz X z θ + z ^ 2 * Work.Spaces.pzIter 2 X z θ := by
  have h := Work.FTS.EllipticEst.DzAmgmSect.DzIter_two_decomp X hX
    (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ, hlt⟩)
  have h2 : Work.Spaces.DzIter 2 X z θ
      - (z ^ 2 * Work.Spaces.pzIter 2 X z θ + Work.Spaces.Dz X z θ) = 0 := h
  linarith [h2]

/-! ## `HkSq` and `HkNorm` of `D_z²X` only see `D_zX + z²∂_z²X` -/

private lemma hkSq_dzIter2_eq (α : ℝ) (k : ℕ) (X : ℝ → ℝ → ℝ)
    (hX : Work.FTS.EllipticEst.SmoothOpen X) :
    Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 X)
      = Work.Spaces.HkSq α k (fun z θ => Work.Spaces.Dz X z θ
          + z ^ 2 * Work.Spaces.pzIter 2 X z θ) :=
  Work.FTS.EllipticEst.HkSq_congr_open α k
    (fun z θ hz hθ hlt => dzIter2_eq X hX hz hθ hlt)

private lemma hkNorm_dzIter2_eq (α : ℝ) (k : ℕ) (X : ℝ → ℝ → ℝ)
    (hX : Work.FTS.EllipticEst.SmoothOpen X) :
    Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 X)
      = Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.Dz X z θ
          + z ^ 2 * Work.Spaces.pzIter 2 X z θ) := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hkSq_dzIter2_eq α k X hX]

/-! ## The statement -/

theorem uopDzIter2Bound (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (X : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen X →
      (∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j X z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j X z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 X) →
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) →
      Work.Spaces.HkMem α k X ∧
      Work.Spaces.HkMem α k (Work.Spaces.pth X) ∧
      Work.Spaces.HkNorm α k X ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 X) ∧
      Work.Spaces.HkNorm α k (Work.Spaces.pth X) ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 X) ∧
      Work.Spaces.HkMem α k (Work.Spaces.Dz X) ∧
      α * Work.Spaces.HkNorm α k (Work.Spaces.Dz X)
        ≤ C * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 X)
            + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ)) ∧
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 X) ∧
      α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 X)
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 X)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace k
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FTS.EllipticEst.HkNorm_Dz_le_open k
  refine ⟨C1 + C2 * max C1 1 + Real.sqrt 2 * (1 + C2 * max C1 1) + 1, ?_, ?_⟩
  · have hKnn : 0 ≤ C2 * max C1 1 :=
      mul_nonneg (le_of_lt hC2pos) (le_trans zero_le_one (le_max_right C1 1))
    have hSnn : 0 ≤ Real.sqrt 2 * (1 + C2 * max C1 1) :=
      mul_nonneg (Real.sqrt_nonneg 2) (by linarith)
    linarith
  intro α X hα0 hα4 hSO htrace hmemP2 hmemZ2
  -- the two angular sentences (Poincaré with vanishing traces)
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨hmemX, hmemP, hXle, hPle⟩ := hC1 α X hα0 hα4 hSO.forall htrace hmemP2
  -- the radial Agmon--Nirenberg inequality for `D_z X`
  obtain ⟨hmemDz, hDzle⟩ := hC2 α X hα0 hα1 hSO.forall hmemX hmemZ2
  -- the second summand of the split is smooth on the open quadrant
  have hZ2sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) :=
    Work.FTS.EllipticEst.DzAmgmSect.SmoothOpen_zsqPz2 X hSO
  -- membership of `D_z²X`, via the split and the `HkMem`-congruence on the open quadrant
  have hmemSum : Work.Spaces.HkMem α k
      (fun z θ => Work.Spaces.Dz X z θ + z ^ 2 * Work.Spaces.pzIter 2 X z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hSO.Dz hZ2sm hmemDz hmemZ2
  have hmemD2 : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 X) :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ
      (f := fun z θ => Work.Spaces.Dz X z θ + z ^ 2 * Work.Spaces.pzIter 2 X z θ)
      (g := Work.Spaces.DzIter 2 X) (hSO.DzIter 2)
      (fun z θ hz hθ hlt => (dzIter2_eq X hSO hz hθ hlt).symm) hmemSum
  -- the triangle inequality for the split
  have htri : Work.Spaces.HkNorm α k
      (fun z θ => Work.Spaces.Dz X z θ + z ^ 2 * Work.Spaces.pzIter 2 X z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (Work.Spaces.Dz X)
          + Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ)) :=
    Work.FTS.EllipticEst.HkNorm_add_le α k (f := Work.Spaces.Dz X)
      (g := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ)
      hSO.Dz.forall hZ2sm.forall hmemDz hmemZ2
  set P : ℝ := Work.Spaces.HkNorm α k X with hP
  set M : ℝ := Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 X) with hM
  set N : ℝ := Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) with hN
  set DD : ℝ := Work.Spaces.HkNorm α k (Work.Spaces.Dz X) with hDD
  set D2 : ℝ := Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 X) with hD2
  have hPnn : 0 ≤ P := Real.sqrt_nonneg _
  have hMnn : 0 ≤ M := Real.sqrt_nonneg _
  have hNnn : 0 ≤ N := Real.sqrt_nonneg _
  have hD2eq : D2 = Work.Spaces.HkNorm α k
      (fun z θ => Work.Spaces.Dz X z θ + z ^ 2 * Work.Spaces.pzIter 2 X z θ) :=
    hkNorm_dzIter2_eq α k X hSO
  have hD2le : D2 ≤ Real.sqrt 2 * (DD + N) := by
    rw [hD2eq]; exact htri
  -- the three constants of the estimate (`C1`, `C2 · max C1 1`, `√2 · (1 + C2 · max C1 1)`)
  -- are all dominated by the constant of the statement
  have hKnn : 0 ≤ C2 * max C1 1 :=
    mul_nonneg (le_of_lt hC2pos) (le_trans zero_le_one (le_max_right C1 1))
  have hSnn : 0 ≤ Real.sqrt 2 * (1 + C2 * max C1 1) :=
    mul_nonneg (Real.sqrt_nonneg 2) (by linarith)
  have hC1le : C1 ≤ C1 + C2 * max C1 1 + Real.sqrt 2 * (1 + C2 * max C1 1) + 1 := by
    linarith
  have hKle : C2 * max C1 1 ≤ C1 + C2 * max C1 1 + Real.sqrt 2 * (1 + C2 * max C1 1) + 1 := by
    linarith
  have hSle : Real.sqrt 2 * (1 + C2 * max C1 1)
      ≤ C1 + C2 * max C1 1 + Real.sqrt 2 * (1 + C2 * max C1 1) + 1 := by
    linarith
  -- the lower-order term
  have hα2Nnn : 0 ≤ α ^ 2 * N := mul_nonneg (sq_nonneg α) hNnn
  have hZnn : 0 ≤ M + α ^ 2 * N := add_nonneg hMnn hα2Nnn
  have hPleK : P ≤ max C1 1 * M :=
    le_trans hXle (mul_le_mul_of_nonneg_right (le_max_left C1 1) hMnn)
  have hYnn : 0 ≤ C2 * (P + α ^ 2 * N) :=
    mul_nonneg (le_of_lt hC2pos) (add_nonneg hPnn hα2Nnn)
  have hNleK : α ^ 2 * N ≤ max C1 1 * (α ^ 2 * N) := by
    calc α ^ 2 * N = 1 * (α ^ 2 * N) := by ring
      _ ≤ max C1 1 * (α ^ 2 * N) :=
          mul_le_mul_of_nonneg_right (le_max_right C1 1) hα2Nnn
  have hPK : P + α ^ 2 * N ≤ max C1 1 * (M + α ^ 2 * N) := by
    calc P + α ^ 2 * N ≤ max C1 1 * M + max C1 1 * (α ^ 2 * N) := add_le_add hPleK hNleK
      _ = max C1 1 * (M + α ^ 2 * N) := by ring
  have hC2K : C2 * (P + α ^ 2 * N) ≤ C2 * (max C1 1 * (M + α ^ 2 * N)) :=
    mul_le_mul_of_nonneg_left hPK (le_of_lt hC2pos)
  refine ⟨hmemX, hmemP, ?_, ?_, hmemDz, ?_, hmemD2, ?_⟩
  · -- conjunct 3: `|X|_{ℋᵏ} ≤ C |∂_θ²X|_{ℋᵏ}`
    exact le_trans hXle (mul_le_mul_of_nonneg_right hC1le hMnn)
  · -- conjunct 4: `|∂_θX|_{ℋᵏ} ≤ C |∂_θ²X|_{ℋᵏ}`
    exact le_trans hPle (mul_le_mul_of_nonneg_right hC1le hMnn)
  · -- conjunct 6: `α |D_zX|_{ℋᵏ} ≤ C (|∂_θ²X|_{ℋᵏ} + α² |z²∂_z²X|_{ℋᵏ})`
    calc α * DD ≤ C2 * (P + α ^ 2 * N) := hDzle
      _ ≤ C2 * (max C1 1 * (M + α ^ 2 * N)) := hC2K
      _ = (C2 * max C1 1) * (M + α ^ 2 * N) := by ring
      _ ≤ (C1 + C2 * max C1 1 + Real.sqrt 2 * (1 + C2 * max C1 1) + 1)
            * (M + α ^ 2 * N) := mul_le_mul_of_nonneg_right hKle hZnn
  · -- conjunct 8: `α² |D_z²X|_{ℋᵏ} ≤ C (α² |z²∂_z²X|_{ℋᵏ} + |∂_θ²X|_{ℋᵏ})`
    have hα2D2 : α ^ 2 * D2 ≤ Real.sqrt 2 * (α ^ 2 * DD + α ^ 2 * N) := by
      have h := mul_le_mul_of_nonneg_left hD2le (show (0 : ℝ) ≤ α ^ 2 by positivity)
      calc α ^ 2 * D2 ≤ α ^ 2 * (Real.sqrt 2 * (DD + N)) := h
        _ = Real.sqrt 2 * (α ^ 2 * DD + α ^ 2 * N) := by ring
    have hαDD : α ^ 2 * DD ≤ (1 / 4) * (C2 * max C1 1) * (M + α ^ 2 * N) := by
      have h1 : α ^ 2 * DD = α * (α * DD) := by ring
      rw [h1]
      calc α * (α * DD) ≤ α * (C2 * (P + α ^ 2 * N)) :=
            mul_le_mul_of_nonneg_left hDzle (le_of_lt hα0)
        _ ≤ (1 / 4) * (C2 * (P + α ^ 2 * N)) := mul_le_mul_of_nonneg_right hα4 hYnn
        _ ≤ (1 / 4) * (C2 * (max C1 1 * (M + α ^ 2 * N))) :=
            mul_le_mul_of_nonneg_left hC2K (by norm_num)
        _ = (1 / 4) * (C2 * max C1 1) * (M + α ^ 2 * N) := by ring
    have hsum : α ^ 2 * DD + α ^ 2 * N
        ≤ (1 + (1 / 4) * (C2 * max C1 1)) * (M + α ^ 2 * N) := by
      calc α ^ 2 * DD + α ^ 2 * N
          ≤ (1 / 4) * (C2 * max C1 1) * (M + α ^ 2 * N) + 1 * (M + α ^ 2 * N) :=
            add_le_add hαDD (by linarith [hMnn])
        _ = (1 + (1 / 4) * (C2 * max C1 1)) * (M + α ^ 2 * N) := by ring
    have hfac : (1 + (1 / 4) * (C2 * max C1 1)) * (M + α ^ 2 * N)
        ≤ (1 + C2 * max C1 1) * (M + α ^ 2 * N) :=
      mul_le_mul_of_nonneg_right (by linarith [hKnn]) hZnn
    calc α ^ 2 * D2 ≤ Real.sqrt 2 * (α ^ 2 * DD + α ^ 2 * N) := hα2D2
      _ ≤ Real.sqrt 2 * ((1 + C2 * max C1 1) * (M + α ^ 2 * N)) :=
          mul_le_mul_of_nonneg_left (le_trans hsum hfac) (Real.sqrt_nonneg 2)
      _ = (Real.sqrt 2 * (1 + C2 * max C1 1)) * (α ^ 2 * N + M) := by ring
      _ ≤ (C1 + C2 * max C1 1 + Real.sqrt 2 * (1 + C2 * max C1 1) + 1)
            * (α ^ 2 * N + M) :=
          mul_le_mul_of_nonneg_right hSle (add_nonneg hα2Nnn hMnn)

end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Pointwise

namespace Work.FTS.EpsEngine.PerzTools

/-! ## Restricted-measurability variants of the two inductions

`Work.FTS.StrongEps.E5G5.mixed_intervalIntegral_eq_gen` assumes the a.e.-strong-measurability
of *every* slot `mixed k l` in the parameter `s`.  Its two internal inductions, however, only
ever evaluate that hypothesis at slots of order `k + l ≤ n` (the angular one at `(0, l)` and
`(0, l+1)`, the radial one at `(k, l)` and `(k+1, l)`).  The two lemmas below record exactly
that: they are the same statements with the measurability hypothesis restricted to the slots
of order `≤ n`, and their proofs are the inductions of
`Submission/Work/FTS/StrongEps/E5G5/DthIter_intervalIntegral_eq_gen.lean` and
`Submission/Work/FTS/StrongEps/E5G5/DzIter_intervalIntegral_eq_gen.lean`, verbatim. -/

/-- **The angular exchange for an arbitrary order `l ≤ n`, with restricted measurability.** -/
theorem DthIter_intervalIntegral_eq_gen_restricted {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ}
    {n l : ℕ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ n → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ n → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    (hl : l ≤ n) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0:ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have hsubIoc : Set.Ioc a b ⊆ Set.Icc (0:ℝ) T := fun t ht =>
    ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  induction l with
  | zero => intro z θ _; rfl
  | succ l ih =>
    intro z θ hzθ
    rw [Set.mem_prod] at hzθ
    obtain ⟨hzz, hθθ⟩ := hzθ
    have hzcl : z ∈ Set.Icc z₁ z₂ := ⟨le_of_lt hzz.1, le_of_lt hzz.2⟩
    have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨hzcl, ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩⟩
    obtain ⟨hz0, hθ0, hθπ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzQ
    set θlo : ℝ := max θ₁ (θ / 2) with hθlo
    set θhi : ℝ := min θ₂ ((θ + Real.pi / 2) / 2) with hθhi
    have hθlo_lt : θlo < θ := by
      rw [hθlo]; exact max_lt hθθ.1 (by linarith)
    have hθ_lt_θhi : θ < θhi := by
      rw [hθhi]; exact lt_min hθθ.2 (by linarith)
    have hθlo0 : 0 < θlo := lt_of_lt_of_le (by linarith : (0:ℝ) < θ / 2) (le_max_right _ _)
    have hθhi_lt : θhi < Real.pi / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    obtain ⟨smin, hsmin_pos, hsmin_le⟩ := Work.FTS.StrongEps.exists_pos_min_sin_two hθlo0 hθhi_lt
    have hmem_box : ∀ y ∈ Set.Ioo θlo θhi,
        (z, y) ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ := by
      intro y hy
      exact ⟨hzcl, ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hy.1),
        le_of_lt (lt_of_lt_of_le hy.2 (min_le_left _ _))⟩⟩
    have hyQ : ∀ y ∈ Set.Ioo θlo θhi, (z, y) ∈ Work.FTS.EllipticEst.Q0 :=
      fun y hy => hboxQ (hmem_box y hy)
    have hyf : ∀ y ∈ Set.Ioo θlo θhi, 0 < y ∧ y < Real.pi / 2 := by
      intro y hy
      obtain ⟨-, hy1, hy2⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hyQ y hy)
      exact ⟨hy1, hy2⟩
    have hcore := Work.FTS.StrongEps.hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b)
      (G := fun t y => Work.Spaces.DthIter l (H t) z y)
      (G' := fun t y => Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y))
      (bound := fun _ => C / smin) hθlo_lt hθ_lt_θhi ?_ ?_ ?_ ?_ ?_ ?_
    rotate_left
    · intro y hy
      have := (hmeas 0 l (by omega) z y (hyQ y hy)).mono_measure
        (Measure.restrict_mono hsub le_rfl)
      simpa only [Work.Spaces.mixed_zero_left] using this
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
      · have h1 := (hmeas 0 l (by omega) z θ hzQ).mono_measure
          (Measure.restrict_mono hsubIoc le_rfl)
        simpa only [Work.Spaces.mixed_zero_left] using h1
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs]
        have htT : t ∈ Set.Icc (0:ℝ) T := hsubIoc ht
        have := hbdd t htT 0 l (by omega) (z, θ)
          ⟨hzcl, ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩⟩
        simpa only [Work.Spaces.mixed_zero_left] using this
    · have h1 := (hmeas 0 (l + 1) (by omega) z θ hzQ).mono_measure
        (Measure.restrict_mono hsub le_rfl)
      simpa only [div_eq_mul_inv] using h1.mul_const (Real.sin (2 * θ))⁻¹
    · intro t ht y hy
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hsinpos : 0 < Real.sin (2 * y) :=
        lt_of_lt_of_le hsmin_pos (hsmin_le y (Set.Ioo_subset_Icc_self hy))
      have hb := hbdd t htT 0 (l + 1) (by omega) (z, y) (hmem_box y hy)
      calc |Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y)|
          = |Work.Spaces.mixed 0 (l + 1) (H t) z y| / Real.sin (2 * y) := by
            rw [abs_div, abs_of_pos hsinpos]
        _ ≤ C / Real.sin (2 * y) := div_le_div_of_nonneg_right hb (le_of_lt hsinpos)
        _ ≤ C / smin := div_le_div_of_nonneg_left hC hsmin_pos
            (hsmin_le y (Set.Ioo_subset_Icc_self hy))
    · exact intervalIntegrable_const
    · intro t ht y hy
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hder := Work.FTS.StrongEps.SmoothOpen.hasDerivAt_slice_th
        (Work.FTS.LocData.contDiffOn_DthIter Work.FTS.EllipticEst.isOpen_Q0
          (hsm t htT) l) hz0 (hyf y hy)
      have hid : Work.Spaces.pth (Work.Spaces.DthIter l (H t)) z y
          = Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y) := by
        simpa only [Work.Spaces.mixed_zero_left] using
          Work.FTS.StrongEps.LocUnif.pth_mixed_div 0 l (hsm t htT) z y (hyQ y hy)
      exact hder.congr_deriv hid
    have hev : (fun y => Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z y)
        =ᶠ[𝓝 θ] (fun y => ∫ s in a..b, Work.Spaces.DthIter l (H s) z y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθθ] with y hy
      exact ih (by omega) z y ⟨hzz, hy⟩
    have hpth : Work.Spaces.pth (Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ)) z θ
        = ∫ s in a..b, Work.Spaces.mixed 0 (l + 1) (H s) z θ / Real.sin (2 * θ) := by
      show deriv (fun y => Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z y) θ = _
      rw [hev.deriv_eq, hcore.deriv]
    have hsinne : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    calc Work.Spaces.DthIter (l + 1) (fun z θ => ∫ s in a..b, H s z θ) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth
            (Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ)) z θ := by
          rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      _ = Real.sin (2 * θ) * (∫ s in a..b,
            Work.Spaces.mixed 0 (l + 1) (H s) z θ / Real.sin (2 * θ)) := by rw [hpth]
      _ = Real.sin (2 * θ) * ((∫ s in a..b,
            Work.Spaces.mixed 0 (l + 1) (H s) z θ) / Real.sin (2 * θ)) := by
          rw [intervalIntegral.integral_div]
      _ = ∫ s in a..b, Work.Spaces.mixed 0 (l + 1) (H s) z θ :=
          mul_div_cancel₀ _ hsinne
      _ = ∫ s in a..b, Work.Spaces.DthIter (l + 1) (H s) z θ := rfl

/-- **The radial exchange for an arbitrary order, with restricted measurability.** -/
theorem DzIter_intervalIntegral_eq_gen_restricted {H : ℝ → ℝ → ℝ → ℝ}
    {T a b C z₁ z₂ θ₁ θ₂ : ℝ} {n : ℕ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ n → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ n → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    (k l : ℕ) (hkl : k + l ≤ n) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.DzIter k (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) z θ
        = ∫ s in a..b, Work.Spaces.DzIter k (Work.Spaces.DthIter l (H s)) z θ := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0:ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have hsubIoc : Set.Ioc a b ⊆ Set.Icc (0:ℝ) T := fun t ht =>
    ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  induction k with
  | zero => intro z θ _; rfl
  | succ k ih =>
    intro z θ hzθ
    rw [Set.mem_prod] at hzθ
    obtain ⟨hzz, hθθ⟩ := hzθ
    have hθcl : θ ∈ Set.Icc θ₁ θ₂ := ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩
    have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨⟨le_of_lt hzz.1, le_of_lt hzz.2⟩, hθcl⟩
    obtain ⟨hz0, hθ0, hθπ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzQ
    set zlo : ℝ := max z₁ (z / 2) with hzlo
    have hzlo_lt : zlo < z := by
      rw [hzlo]; exact max_lt hzz.1 (by linarith)
    have hmem_box : ∀ x ∈ Set.Ioo zlo z₂,
        (x, θ) ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ := by
      intro x hx
      exact ⟨⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx.1), le_of_lt hx.2⟩, hθcl⟩
    have hxQ : ∀ x ∈ Set.Ioo zlo z₂, (x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      fun x hx => hboxQ (hmem_box x hx)
    have hxpos : ∀ x ∈ Set.Ioo zlo z₂, 0 < x := fun x hx =>
      lt_of_lt_of_le (by linarith : (0:ℝ) < z / 2)
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1))
    have hcore := Work.FTS.StrongEps.hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b)
      (G := fun t x => Work.Spaces.DzIter k (Work.Spaces.DthIter l (H t)) x θ)
      (G' := fun t x => Work.Spaces.mixed (k + 1) l (H t) x θ / x)
      (bound := fun _ => C * (2 / z)) hzlo_lt hzz.2 ?_ ?_ ?_ ?_ ?_ ?_
    rotate_left
    · intro x hx
      have := (hmeas k l (by omega) x θ (hxQ x hx)).mono_measure
        (Measure.restrict_mono hsub le_rfl)
      simpa only [Work.Spaces.mixed] using this
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
      · have h1 := (hmeas k l (by omega) z θ hzQ).mono_measure
          (Measure.restrict_mono hsubIoc le_rfl)
        simpa only [Work.Spaces.mixed] using h1
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs]
        have htT : t ∈ Set.Icc (0:ℝ) T := hsubIoc ht
        exact hbdd t htT k l (by omega) (z, θ) ⟨⟨le_of_lt hzz.1, le_of_lt hzz.2⟩, hθcl⟩
    · have h1 := (hmeas (k + 1) l (by omega) z θ hzQ).mono_measure
        (Measure.restrict_mono hsub le_rfl)
      simpa only [div_eq_mul_inv] using h1.mul_const z⁻¹
    · intro t ht x hx
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hx2 : z / 2 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1)
      have hb := hbdd t htT (k + 1) l (by omega) (x, θ) (hmem_box x hx)
      calc |Work.Spaces.mixed (k + 1) l (H t) x θ / x|
          = |Work.Spaces.mixed (k + 1) l (H t) x θ| / x := by
            rw [abs_div, abs_of_pos (hxpos x hx)]
        _ ≤ C / x := div_le_div_of_nonneg_right hb (le_of_lt (hxpos x hx))
        _ ≤ C / (z / 2) := div_le_div_of_nonneg_left hC (by linarith) hx2
        _ = C * (2 / z) := by field_simp
    · exact intervalIntegrable_const
    · intro t ht x hx
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hder : HasDerivAt (fun x' => Work.Spaces.mixed k l (H t) x' θ)
          (Work.Spaces.pz (Work.Spaces.mixed k l (H t)) x θ) x :=
        Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice
          (Work.FTS.LocData.contDiffOn_mixed Work.FTS.EllipticEst.isOpen_Q0 (hsm t htT) k l)
          (θ := θ) ⟨hθ0, hθπ2⟩ (hxpos x hx)
      exact hder.congr_deriv
        (Work.FTS.StrongEps.LocUnif.pz_mixed_div k l (hsm t htT) x θ (hxQ x hx))
    have hloc : (fun x => Work.Spaces.DzIter k
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) x θ)
        =ᶠ[𝓝 z] (fun x => ∫ s in a..b, Work.Spaces.DzIter k (Work.Spaces.DthIter l (H s)) x θ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hzz] with x hx
      exact ih (by omega) x θ ⟨hx, hθθ⟩
    have hpz : Work.Spaces.pz (Work.Spaces.DzIter k
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ)) z θ
        = ∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ / z := by
      show deriv (fun x => Work.Spaces.DzIter k
        (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) x θ) z = _
      rw [hloc.deriv_eq, hcore.deriv]
    have hzne : z ≠ 0 := ne_of_gt hz0
    calc Work.Spaces.DzIter (k + 1)
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter k
            (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ)) z θ := by
          rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      _ = z * (∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ / z) := by rw [hpz]
      _ = z * ((∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ) / z) := by
          rw [intervalIntegral.integral_div]
      _ = ∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ := mul_div_cancel₀ _ hzne
      _ = ∫ s in a..b, Work.Spaces.DzIter (k + 1) (Work.Spaces.DthIter l (H s)) z θ := rfl

/-- **Exchange of `mixed j i` (`j + i ≤ n`) with the interval integral, with the measurability
hypothesis restricted to the slots of order `≤ n`.**

This is `Work.FTS.StrongEps.E5G5.mixed_intervalIntegral_eq_gen` with the (otherwise unused)
measurability of the higher slots dropped: the two inductions behind it only ever evaluate
`hmeas` at slots of order `≤ n`. -/
theorem mixed_intervalIntegral_eq_gen_restricted {H : ℝ → ℝ → ℝ → ℝ}
    {T a b C z₁ z₂ θ₁ θ₂ : ℝ} {n : ℕ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ n → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ n → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ n) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := by
  have hbox_open : IsOpen (Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) := isOpen_Ioo.prod isOpen_Ioo
  intro z θ hzθ
  have hA := DthIter_intervalIntegral_eq_gen_restricted (H := H) haT hbT hab hC hsm hmeas hbdd
    hboxQ (l := i) (by omega)
  have hB := DzIter_intervalIntegral_eq_gen_restricted (H := H) haT hbT hab hC hsm hmeas hbdd
    hboxQ j i hji z θ hzθ
  have hA' : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => ∫ s in a..b, H s z θ)))
      (Function.uncurry (fun z θ => ∫ s in a..b, Work.Spaces.DthIter i (H s) z θ))
      (Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) := fun p hp => hA p.1 p.2 hp
  have hloc := Work.FTS.StrongEps.DzIter_congr_of_isOpen hbox_open hA' j hzθ
  simp only [Function.uncurry] at hloc
  calc Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
      = Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => ∫ s in a..b, H s z θ)) z θ := rfl
    _ = Work.Spaces.DzIter j (fun z θ => ∫ s in a..b, Work.Spaces.DthIter i (H s) z θ) z θ := hloc
    _ = ∫ s in a..b, Work.Spaces.DzIter j (Work.Spaces.DthIter i (H s)) z θ := hB
    _ = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := rfl

end Work.FTS.EpsEngine.PerzTools
end
end
