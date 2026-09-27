import Mathlib
import Submission.Work.Drive.chartShiftBaseLocus
import Submission.Work.Drive.planeChain

/-!
# The counting engine's input from the chart-shift endpoint

The engine `Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet` (`manifold_triple_inter_boundary_parity`
plus the seam cancellation) takes **two** inputs: the packaged hypotheses
`Work.Drive.Meet3Hyp M D`, and the seam/slice separation

`hdisj : ∀ k x, x ∈ tripleBdryMeet M D k → ¬ (onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1))`.

This file records that the second is **free from the first**: `hdisj` follows from the *face clause* of
`Meet3Hyp` alone, by `Work.Drive.not_seam_and_slice_of_generic` (`planeChain.lean`, which the reviewer of
the engine noted already).  Consequently the parametrised-Sard endpoint
`Work.Drive.exists_meet3Hyp_chartShiftCharted_of_boxBall` produces the engine's **complete** input, and
`Work.Drive.exists_engineInput_chartShiftCharted_of_boxBall` states that in one shot: a parameter `t`
with `‖t‖ < ε'`, the packaged hypotheses, the separation, and the identification of the base slice with the
design's own chain on the box.

* `Work.Drive.Meet3Generic.of_meet3Hyp` — `Meet3Hyp → Meet3Generic` (drop the smoothness and the seam);
* **`Work.Drive.hdisj_of_meet3Hyp`** — `Meet3Hyp → hdisj`;
* **`Work.Drive.exists_engineInput_chartShiftCharted_of_boxBall`** — the engine's input, one shot.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **`Meet3Hyp` gives the genericity data.** -/
theorem Meet3Generic.of_meet3Hyp (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (h : Meet3Hyp M D) : Meet3Generic M D :=
  ⟨h.trans, h.face⟩

/-- **The engine's seam/slice separation is free from `Meet3Hyp`.** -/
theorem hdisj_of_meet3Hyp (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (h : Meet3Hyp M D) (k : Fin 3) :
    ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3), x ∈ tripleBdryMeet M D k →
      ¬ (onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1)) :=
  not_seam_and_slice_of_generic D (Meet3Generic.of_meet3Hyp D h) k

/-- **The engine's two inputs (`Meet3Hyp` and the separation) plus the base identification.** -/
theorem exists_engineInput_chartShiftCharted_of_boxBall (p : M)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 3) (𝓡 4) Ctop (P k))
    (hPseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Work.Drive.onSeam x → P k (Work.Drive.seamInv x) = P k x)
    (hsrc : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), P k x ∈ (Work.Drive.chr p).source)
    (c : EuclideanSpace ℝ (Fin 4)) {r₁ r₂ r'' : ℝ} (h1 : 0 < r₁) (h12 : r₁ < r₂) (hr'' : r'' < r₁)
    (htarget : ∀ u ∈ Metric.closedBall c r₂, u ∈ (Work.Drive.chr p).target)
    (hbox : ∀ y ∈ Submission.Drive.unitBox 8, ∀ k : Fin 3,
      (Work.Drive.chr p) (P k (Work.Drive.TParity.bPartC k y)) ∈ Metric.closedBall c r'') :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
      Meet3Hyp M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
        (fun j x' => (chr p) (P j x')) t) ∧
      (∀ (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)),
        x ∈ tripleBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
          (fun j x' => (chr p) (P j x')) t) k →
        ¬ (onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1))) ∧
      (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 9)), y ∈ Submission.Drive.unitBox 8 →
        chartShiftClamped p (clampFun c r₁ r₂ h1 h12) (fun j x' => (chr p) (P j x'))
          0 k (Work.Drive.TParity.bPartC k y) = P k (Work.Drive.TParity.bPartC k y)) := by
  intro ε' hε'
  obtain ⟨t, ht, hM, hbase⟩ :=
    exists_meet3Hyp_chartShiftCharted_of_boxBall p P hP hPseam hsrc c h1 h12 hr'' htarget hbox ε' hε'
  exact ⟨t, ht, hM, hdisj_of_meet3Hyp _ hM, hbase⟩

/-- **The engine's conclusion, end to end, for the design's own chain.**  Same hypotheses as
`Work.Drive.exists_engineInput_chartShiftCharted_of_boxBall`; the conclusion is the engine's parity for
the chart-shift family of `(chr p) ∘ P` at the generic parameter, together with the identification of the
base slice with `P` on the box. -/
theorem even_sum_bdryMeet_chartShiftCharted_of_boxBall (p : M)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 3) (𝓡 4) Ctop (P k))
    (hPseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Work.Drive.onSeam x → P k (Work.Drive.seamInv x) = P k x)
    (hsrc : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), P k x ∈ (Work.Drive.chr p).source)
    (c : EuclideanSpace ℝ (Fin 4)) {r₁ r₂ r'' : ℝ} (h1 : 0 < r₁) (h12 : r₁ < r₂) (hr'' : r'' < r₁)
    (htarget : ∀ u ∈ Metric.closedBall c r₂, u ∈ (Work.Drive.chr p).target)
    (hbox : ∀ y ∈ Submission.Drive.unitBox 8, ∀ k : Fin 3,
      (Work.Drive.chr p) (P k (Work.Drive.TParity.bPartC k y)) ∈ Metric.closedBall c r'') :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
      Even (((topBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
                (fun j x' => (chr p) (P j x')) t) 0).ncard
            + (bottomBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
                (fun j x' => (chr p) (P j x')) t) 0).ncard)
          + ((topBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
                (fun j x' => (chr p) (P j x')) t) 1).ncard
            + (bottomBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
                (fun j x' => (chr p) (P j x')) t) 1).ncard)
          + ((topBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
                (fun j x' => (chr p) (P j x')) t) 2).ncard
            + (bottomBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
                (fun j x' => (chr p) (P j x')) t) 2).ncard)) ∧
      (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 9)), y ∈ Submission.Drive.unitBox 8 →
        chartShiftClamped p (clampFun c r₁ r₂ h1 h12) (fun j x' => (chr p) (P j x'))
          0 k (Work.Drive.TParity.bPartC k y) = P k (Work.Drive.TParity.bPartC k y)) := by
  intro ε' hε'
  obtain ⟨t, ht, hM, hdisj, hbase⟩ :=
    exists_engineInput_chartShiftCharted_of_boxBall p P hP hPseam hsrc c h1 h12 hr'' htarget
      hbox ε' hε'
  exact ⟨t, ht, even_sum_topBdryMeet_add_bottomBdryMeet M _ hM hdisj, hbase⟩

/-- **The engine's complete interface and conclusion, in the single-ball form of the endpoint.**  Same
hypotheses as `Work.Drive.exists_meet3Hyp_chartShiftCharted_of_ball` (a smooth, seam-invariant, chart
resident chain family and one ball `closedBall c r₂ ⊆ (chr p).target` whose *open* version contains the
charted values on the box); the conclusion produces the inner radius `r₁` and, for every `ε' > 0`, a
parameter `t` with `‖t‖ < ε'`, the packaged hypotheses `Meet3Hyp M (G t)`, the seam/slice separation for
`G t`, the engine's parity conclusion, and the identification of the base slice with `P` on the box. -/
theorem even_sum_bdryMeet_chartShiftCharted_of_ball (p : M)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 3) (𝓡 4) Ctop (P k))
    (hPseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Work.Drive.onSeam x → P k (Work.Drive.seamInv x) = P k x)
    (hsrc : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), P k x ∈ (Work.Drive.chr p).source)
    (c : EuclideanSpace ℝ (Fin 4)) {r₂ : ℝ}
    (htarget : ∀ u ∈ Metric.closedBall c r₂, u ∈ (Work.Drive.chr p).target)
    (hball : ∀ y ∈ Submission.Drive.unitBox 8, ∀ k : Fin 3,
      (Work.Drive.chr p) (P k (Work.Drive.TParity.bPartC k y)) ∈ Metric.ball c r₂) :
    ∃ (r₁ : ℝ) (h1 : 0 < r₁) (h12 : r₁ < r₂),
      ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Meet3Hyp M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
          (fun j x' => (chr p) (P j x')) t) ∧
        (∀ (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)),
          x ∈ tripleBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
            (fun j x' => (chr p) (P j x')) t) k →
          ¬ (onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1))) ∧
        Even (((topBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
                  (fun j x' => (chr p) (P j x')) t) 0).ncard
              + (bottomBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
                  (fun j x' => (chr p) (P j x')) t) 0).ncard)
            + ((topBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
                  (fun j x' => (chr p) (P j x')) t) 1).ncard
              + (bottomBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
                  (fun j x' => (chr p) (P j x')) t) 1).ncard)
            + ((topBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
                  (fun j x' => (chr p) (P j x')) t) 2).ncard
              + (bottomBdryMeet M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
                  (fun j x' => (chr p) (P j x')) t) 2).ncard)) ∧
        (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 9)), y ∈ Submission.Drive.unitBox 8 →
          chartShiftClamped p (clampFun c r₁ r₂ h1 h12) (fun j x' => (chr p) (P j x'))
            0 k (Work.Drive.TParity.bPartC k y) = P k (Work.Drive.TParity.bPartC k y)) := by
  obtain ⟨r₁, h1, h12, hmain⟩ :=
    exists_meet3Hyp_chartShiftCharted_of_ball p P hP hPseam hsrc c htarget hball
  refine ⟨r₁, h1, h12, fun ε' hε' => ?_⟩
  obtain ⟨t, ht, hM, hbase⟩ := hmain ε' hε'
  exact ⟨t, ht, hM, hdisj_of_meet3Hyp _ hM,
    even_sum_topBdryMeet_add_bottomBdryMeet M _ hM (hdisj_of_meet3Hyp _ hM), hbase⟩

/-- **The engine's complete interface and conclusion for an *arbitrary* clamp.**  Same hypotheses as
`Work.Drive.exists_meet3Hyp_chartShift_of_localId` (a smooth, seam-invariant, chart-resident chain family
`P`, an arbitrary smooth clamp `ψ` valued in the chart's target and agreeing with the identity near the
shifted base values on `K`, and the base containment), plus the pointwise condition that `ψ` fixes the
charted base values; the conclusion is, for every `ε' > 0`, a parameter `t` with `‖t‖ < ε'`, the packaged
hypotheses `Meet3Hyp M (G t)`, the seam/slice separation, the engine's parity, and the identification of
the base slice with `P` on the box.

Compared with `Work.Drive.even_sum_bdryMeet_chartShiftCharted_of_ball` the *ball* data (`c`, `r₂` and the
two containment conditions) is replaced by the single condition that `ψ` be locally the identity on the
shifted values — the form that survives the opacity of `chartAt`'s target. -/
theorem even_sum_bdryMeet_chartShift_of_localId (p : M)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 3) (𝓡 4) Ctop (P k))
    (hPseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Work.Drive.onSeam x → P k (Work.Drive.seamInv x) = P k x)
    (hsrc : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), P k x ∈ (Work.Drive.chr p).source)
    (ψ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hψ : ContDiff ℝ Ctop ψ) (hψt : ∀ u, ψ u ∈ (Work.Drive.chr p).target)
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (hbase : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      TParity.meet3 (chartShiftClamped p ψ (fun j x' => (chr p) (P j x')) 0) y →
      y ∈ interior K)
    (hshift : ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < ε →
      y ∈ K → ∀ k : Fin 3,
        (fun u : EuclideanSpace ℝ (Fin 4) => ψ u)
          =ᶠ[𝓝 ((chr p) (P k (TParity.bPartC k y)) + blk k t)] id)
    (hidbase : ∀ y ∈ Submission.Drive.unitBox 8, ∀ k : Fin 3,
      ψ ((chr p) (P k (TParity.bPartC k y))) = (chr p) (P k (TParity.bPartC k y))) :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
      Meet3Hyp M (chartShiftClamped p ψ (fun j x' => (chr p) (P j x')) t) ∧
      (∀ (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)),
        x ∈ tripleBdryMeet M (chartShiftClamped p ψ (fun j x' => (chr p) (P j x')) t) k →
        ¬ (onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1))) ∧
      Even (((topBdryMeet M (chartShiftClamped p ψ (fun j x' => (chr p) (P j x')) t) 0).ncard
            + (bottomBdryMeet M (chartShiftClamped p ψ (fun j x' => (chr p) (P j x')) t) 0).ncard)
          + ((topBdryMeet M (chartShiftClamped p ψ (fun j x' => (chr p) (P j x')) t) 1).ncard
            + (bottomBdryMeet M (chartShiftClamped p ψ (fun j x' => (chr p) (P j x')) t) 1).ncard)
          + ((topBdryMeet M (chartShiftClamped p ψ (fun j x' => (chr p) (P j x')) t) 2).ncard
            + (bottomBdryMeet M (chartShiftClamped p ψ (fun j x' => (chr p) (P j x')) t) 2).ncard)) ∧
      (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 9)), y ∈ Submission.Drive.unitBox 8 →
        chartShiftClamped p ψ (fun j x' => (chr p) (P j x')) 0 k (Work.Drive.TParity.bPartC k y)
          = P k (Work.Drive.TParity.bPartC k y)) := by
  have hchart : ContMDiffOn (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) Ctop ((chr p : M → _))
      (chr p).source := by
    have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
    simpa [Work.Drive.chr] using h
  have hA : ∀ k : Fin 3, ContDiff ℝ Ctop
      (fun x : EuclideanSpace ℝ (Fin 3) => (chr p) (P k x)) := by
    intro k
    have hcomp : ContMDiff (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) Ctop
        (fun x : EuclideanSpace ℝ (Fin 3) => (chr p) (P k x)) := by
      rw [← contMDiffOn_univ]
      exact hchart.comp (hP k).contMDiffOn (fun x _ => hsrc k x)
    exact (contMDiff_iff_contDiff (𝕜 := ℝ) (n := Ctop)).mp hcomp
  have hAseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), Work.Drive.onSeam x →
      (fun j x' => (chr p) (P j x')) k (Work.Drive.seamInv x)
        = (fun j x' => (chr p) (P j x')) k x :=
    fun k x hx => by
      show (chr p) (P k (Work.Drive.seamInv x)) = (chr p) (P k x)
      rw [hPseam k x hx]
  intro ε' hε'
  obtain ⟨t, ht, hM⟩ := exists_meet3Hyp_chartShift_of_localId p
    (fun j x' => (chr p) (P j x')) hA hAseam ψ hψ hψt K hK hε hbase hshift ε' hε'
  refine ⟨t, ht, hM, hdisj_of_meet3Hyp _ hM,
    even_sum_topBdryMeet_add_bottomBdryMeet M _ hM (hdisj_of_meet3Hyp _ hM), fun k y hy => ?_⟩
  exact chartShiftClamped_charted_zero_of_localId p P ψ k (Work.Drive.TParity.bPartC k y)
    (hsrc k _) (hidbase y hy k)

end

end Work.Drive
