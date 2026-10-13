/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `D_z`-honesty package for the `Uop` slot (`uopDzIter2Bound`)

`Work.FTS.EllSol.PkgK5.uopDzIter2Bound` is the bookkeeping node of the `PkgK5` (`U`-slot) chain
that turns the two *honesty* inputs of the elliptic estimate

* `HkMem α k (∂_θ²X)`  (`X` is twice angularly differentiable in `ℋ^k`), and
* `HkMem α k (z²∂_z²X)`

into the full list of memberships and open-quadrant transfers for `X`, `∂_θX`, `D_zX = z∂_zX`
and `D_z²X = D_z(D_zX)`:

* `HkMem` of `X`, `∂_θX`, `D_zX`, `D_z²X`;
* `‖X‖_{ℋ^k} ≤ C‖∂_θ²X‖_{ℋ^k}` and `‖∂_θX‖_{ℋ^k} ≤ C‖∂_θ²X‖_{ℋ^k}` (the angular Poincaré
  estimate with vanishing boundary traces);
* `α‖D_zX‖_{ℋ^k} ≤ C(‖∂_θ²X‖_{ℋ^k} + α²‖z²∂_z²X‖_{ℋ^k})` (the radial Agmon--Nirenberg
  interpolation for `D_z`);
* `α²‖D_z²X‖_{ℋ^k} ≤ C(α²‖z²∂_z²X‖_{ℋ^k} + ‖∂_θ²X‖_{ℋ^k})`.

The last item is the composition of the interpolation with the elementary split
`D_z²X = D_zX + z²∂_z²X` (the product rule for `z ↦ z∂_zX` on the open quadrant).

Every ingredient is a *proved* module of the tree; this file only assembles them:

* `Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace` for the two angular sentences;
* `Work.FTS.EllipticEst.HkNorm_Dz_le_open` (the radial Agmon--Nirenberg inequality) for `D_zX`;
* `Work.FTS.EllipticEst.HkNorm_add_le` (subadditivity of the `ℋᵏ`-norm on the open quadrant) and
  `Work.FTS.EllipticEst.HkSq_congr_open` + `HkMem_agreeOnQ` (the `ℋᵏ`-norm and the
  `ℋᵏ`-membership only see the open quadrant) for the transfer from `D_zX + z²∂_z²X` to `D_z²X`;
* `Work.FTS.EllipticEst.HkMem_add_open` for the membership of the sum, and
  `Work.FTS.EllipticEst.DzAmgmSect` for the split and the smoothness of `z²∂_z²X`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.HkNorm_Dz_le_open
import Submission.Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Gbar_sin

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
