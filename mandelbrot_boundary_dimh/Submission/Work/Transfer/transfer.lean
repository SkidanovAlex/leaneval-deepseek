import Mathlib
import Submission.Work.Interfaces.Basic
import Submission.Work.Transfer.Setup
import Submission.Work.Transfer.hit
import Submission.Work.Transfer.zeroTransfer
import Submission.Work.Transfer.hitSet_subset_frontier
import Submission.Work.Transfer.holderPsi
import Submission.Work.Transfer.holderDim

/-! Guidance from the project lead (the requester):

AREA TRANSFER (from an IFS at a boundary parameter to dimH of the boundary of M; replaces MSS Lemma III.2 and Shishikura Lemma 3.2). Interface: Submission/Work/Interfaces/Basic.lean. You assume MsetStatement, MotionStatement, DimStatement as hypotheses. Montel is available: Submission.Work.Normal.montel_omits_three / montel_two_omitted (single-disjunct normality on PRECONNECTED open sets, see Submission/Work/Normal/NOTES.md).
Given c0 in frontier M, HypIFS c0 N K (tau, n, p, r), 0 < a < 1. Apply MotionStatement with exponent a' := sqrt a to get rho, pi. Write v(c) := (Tc c)^[m] c = (Tc c)^[m+1] 0.
Step 1 (hit parameter, Montel with moving targets; route by the lead): Delta := ball c0 rho (preconnected). Pick two words x1 /= x2; h_j(c) := pi c x_j are holomorphic, h_1 /= h_2 pointwise (injectivity). If for every m and c in Delta, v_m(c) /= h_1(c), h_2(c), then G_m(c) := (v_m(c) - h_1(c)) / (h_2(c) - h_1(c)) omit 0 and 1, so {G_m} is normal (montel_two_omitted), hence {v_m} is normal. But c0 in M: |v_m(c0)| <= 2 for all m, so no subsequence tends to infinity locally uniformly; and Delta contains c' not in M (c0 in frontier), where v_m(c') -> infinity (MSET), so no subsequence converges to a finite holomorphic limit. Contradiction. So some m and c1 in Delta and word w* in {x1, x2} have v_m(c1) = pi c1 w*.
Step 2 (non-degeneracy, for EVERY word w): e_w(c) := v_m(c) - pi c w is not identically 0 on Delta.
Step 3 (existence of hits for nearby codes, no Rouche needed): minimum-modulus principle.
Step 4 (Y' in frontier M): Y' := {c in ball c1 rho1 | exists w in that cylinder, v_m(c) = pi c w}; equicontinuity + Cauchy estimates.
Step 5 (dimension): Psi(c) = pi c1 (code of c) is a'-Holder, surjects onto a cylinder piece, and the two Holder losses give a'^2 = a.

The five steps are proved in the sibling modules `hit`, `zeroTransfer`, `hitSet_subset_frontier`,
`holderPsi`, `holderDim`; this file assembles them.
-/

namespace Work.Transfer

open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Topology
open Classical

theorem transfer (hM : MsetStatement) (hMo : MotionStatement) (hD : DimStatement) :
    TransferStatement := by
  intro c₀ hc₀ N K hN hifs a ha0 ha1
  obtain ⟨τ, n, p, r, hcon, hdyn⟩ := hifs
  haveI : NeZero N := ⟨by omega⟩
  -- the exponent used for the holomorphic motion: a' = sqrt a, so that the two Holder losses
  -- give a'^2 = a.
  set a' : ℝ := Real.sqrt a with ha'_def
  have ha'0 : 0 < a' := Real.sqrt_pos.2 ha0
  have ha'1 : a' < 1 := by
    rw [ha'_def, Real.sqrt_lt' one_pos]
    simpa using ha1
  obtain ⟨ρ, hρ, phi, hbase, hdiff, hinj, hequiv, hobdd, hcontr, hlip, hhold⟩ :=
    hMo c₀ N τ n p r K hN hcon hdyn a' ha'1
  have hMD : Work.Transfer.MotionData c₀ N τ n p ρ a' phi :=
    ⟨hbase, hdiff, hinj, hequiv, hobdd, hcontr, hlip, hhold⟩
  -- Step 1: the critical value hits the moving limit set.
  obtain ⟨m, c₁, w, hc₁, hhit⟩ := hit hM hc₀ hN hρ hMD
  -- a small ball around the hit, contained in the domain of the motion
  have hd : dist c₁ c₀ < ρ := Metric.mem_ball.mp hc₁
  set ρ₁ : ℝ := (ρ - dist c₁ c₀) / 2 with hρ₁_def
  have hρ₁ : 0 < ρ₁ := by rw [hρ₁_def]; linarith
  have hsub : Metric.ball c₁ ρ₁ ⊆ Metric.ball c₀ ρ := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have h1 : dist z c₀ ≤ dist z c₁ + dist c₁ c₀ := dist_triangle _ _ _
    rw [hρ₁_def] at hz
    linarith
  -- Step 2: for every word, the critical value is not identically a point of the limit set.
  have hne : ∀ w : ℕ → Fin N, ∃ z ∈ Metric.ball c₀ ρ, critOrbit m z ≠ phi z w :=
    fun w => exists_critOrbit_ne_pi hM hc₀ hρ hMD m w
  -- Step 3: hits exist for all codes close to the code of the hit.
  obtain ⟨k₀, hk₀⟩ := zeroTransfer hρ hMD (hne w) hρ₁ hc₁ hsub hhit
  set l : List (Fin N) := (List.range k₀).map w with hl_def
  set W : Set (ℕ → Fin N) := MandelDim.cylinder l with hW_def
  have hcylW : MandelDim.cylinder l ⊆ W := subset_rfl
  have hzt : ∀ (w : ℕ → Fin N), (∃ z ∈ Metric.ball c₀ ρ, critOrbit m z ≠ phi z w) →
      ∀ {R : ℝ} {c_s : ℂ}, 0 < R → c_s ∈ Metric.ball c₀ ρ →
        Metric.ball c_s R ⊆ Metric.ball c₀ ρ →
        critOrbit m c_s = phi c_s w →
        ∃ k₀ : ℕ, ∀ u : ℕ → Fin N, (∀ j < k₀, u j = w j) →
          ∃ c ∈ Metric.ball c_s R, critOrbit m c = phi c u :=
    fun w hne' R c_s hR hcs hbsub hz => zeroTransfer hρ hMD hne' hR hcs hbsub hz
  -- Step 4: the hit set lies in the frontier of the Mandelbrot set.
  have hfront : Work.Transfer.HitSet m c₁ ρ₁ phi W ⊆ frontier Mandelbrot :=
    hitSet_subset_frontier hM hN hρ hMD m hc₁ hρ₁ hsub hne hzt W
  -- the coding map of the hit set surjects onto the cylinder piece
  have hsurj : ∀ ω ∈ MandelDim.cylinder l,
      ∃ c ∈ Work.Transfer.HitSet m c₁ ρ₁ phi W, codeOf m phi c = ω := by
    intro ω hω
    have hagree : ∀ j < k₀, ω j = w j := (mem_cylinder_map_range w k₀).1 hω
    obtain ⟨c, hc, hcc⟩ := hk₀ ω hagree
    refine ⟨c, ⟨hc, ω, hω, hcc⟩, ?_⟩
    exact codeOf_eq m phi (hinj c (hsub hc)) hcc
  -- Step 5: Holder map, dimension lower bound.
  obtain ⟨K', hholder⟩ := holderPsi hρ hMD ha'0 ha'1.le m hc₁ hρ₁ hsub W
  have hmain := holderDim hD hN hρ hcon hMD ha'0 ha'1 m hc₁ hcylW hfront hsurj hholder
  rw [show a' ^ 2 = a from by rw [ha'_def]; exact Real.sq_sqrt ha0.le] at hmain
  exact hmain

end Work.Transfer
