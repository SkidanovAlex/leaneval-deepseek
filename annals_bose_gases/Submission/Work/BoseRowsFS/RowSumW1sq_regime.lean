import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.Defs
import Submission.Work.BoseRowsFS.honest_chat_W1sq_integral_le
import Submission.Work.BoseRowsFS.honest_lattice_W1sq_le_uniform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.RowSumW1sq_regime`

The first FS §11 row (`RowSumW1sq`, FS `eq:I2-integral`) at the honest model,
**restricted to the dilute régime** `μ a³ ≤ εg`: the caller supplies the régime
row

    ∀ μ, 0 < μ → μ a³ ≤ εg → 1 ≤ ellH v μ ∧ R ≤ ellH v μ · chiR0

(i.e. FS's two side-length conditions `1 ≤ ℓ`, `R ≤ ℓ·chiR0`), and the statement
is then the gate's `hsumW1sq` row for those `μ`, with an absolute constant `Cws`.

## Route

The on-régime part of the row is *proved* (`RowSumW1sq_of_lattice`, assembled
there from the two uniform rows `honest_lattice_W1sq_le_uniform` and
`honest_chat_W1sq_integral_le`).  The off-régime part of that assembly is not
available here — and is not needed: the hypothesis `hrég` says the régime holds
exactly for the `μ` the conclusion quantifies over.

`rowSumW1sq_range` below isolates the on-régime reduction as a statement about
an arbitrary constant `C`: from

    ∀ ℓ ≥ 1, R ≤ ℓ·chiR0, ∀ N,
      ℓ⁻³ Σ_{n ≠ 0 ∈ Lab N} Ŵ₁(kmomLab ℓ N n)²/‖kmomLab ℓ N n‖² ≤ C · a v

one gets the honest row (cut dropped, sum restricted to a filtered sub-lattice of
the cube) with the same constant `C`.  Instantiating with
`C := CL · KE` (`CL` from the uniform lattice-versus-continuum comparison, `KE`
from the continuum bound of FS's `eq:I2-integral`) gives the theorem.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowsFS

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases
open Work.BoseGateFS

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The on-régime reduction of row 1.**  If the *scaled* lattice sum is bounded
by `C · a v` for every side `ℓ` in FS's range and every cube size `N`, then the
honest row (the UV-cut `W₁ = ζ_{Λ_N}Ŵ₁`, summed over the `P_H^q`-filtered
sub-lattice of the cube `Lab N`) is bounded by `C · aScat` for every honest model
in that range. -/
theorem rowSumW1sq_range {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R C : ℝ}
    (hlat : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 → ∀ N : ℕ,
      ℓ ^ (-(3 : ℝ)) *
        (∑ n ∈ (Finset.univ.erase (0 : Work.BoseBoxFock.Lab N)),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (Work.BoseBoxFock.kmomLab ℓ N n)) ^ 2
              / ‖Work.BoseBoxFock.kmomLab ℓ N n‖ ^ 2)
        ≤ C * _root_.BoseGases.a v) :
    ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
      1 ≤ Work.BoseBoxFock.ellH v μ →
      R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 →
      (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ q ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
              ((Work.BoseRowsFS.honF v h fc fu HM μ).PHq
                (Work.BoseRowsFS.honE v h fc fu HM μ).KH
                (Work.BoseRowsFS.honE v h fc fu HM μ).aScat),
            (Work.BoseRowsFS.honE v h fc fu HM μ).W1 q ^ 2
              / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom q‖ ^ 2
        ≤ C * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat := by
  intro HM μ hμ h1 h2
  by_cases hpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  · -- the honest side is in FS's range: drop the UV cut, extend to `excited`
    -- and read off the scaled-lattice hypothesis `hlat`
    set ℓ := Work.BoseBoxFock.ellH v μ with hℓdef
    have hellH : ℓ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
      rw [hℓdef, Work.BoseBoxFock.ellH, if_pos hpos]
    have hell : (Work.BoseRowsFS.honE v h fc fu HM μ).ell = ℓ := by
      show Work.BoseBox.sideAt μ (_root_.BoseGases.a v) = ℓ
      exact hellH.symm
    have hℓpos : 0 < ℓ := by
      rw [hℓdef]; exact Work.BoseBoxFock.ellH_pos v μ
    have hkmom : ∀ q : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseRowsFS.honF v h fc fu HM μ).kmom q
          = Work.BoseBoxFock.kmomLab ℓ (HM μ).N q := by
      intro q; rw [hℓdef]; rfl
    have hW1eq : ∀ q : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseRowsFS.honE v h fc fu HM μ).W1 q
        = Work.BoseBoxFock.uvCut fu
            (Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N)
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N q)
          * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N q) :=
      fun q => rfl
    -- the pointwise comparison: the cut `ζ ≤ 1` can be dropped
    have hpt : ∀ q ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
          ((Work.BoseRowsFS.honF v h fc fu HM μ).PHq
            (Work.BoseRowsFS.honE v h fc fu HM μ).KH
            (Work.BoseRowsFS.honE v h fc fu HM μ).aScat),
        (Work.BoseRowsFS.honE v h fc fu HM μ).W1 q ^ 2
            / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom q‖ ^ 2
        ≤ (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
              (Work.BoseBoxFock.kmomLab ℓ (HM μ).N q)) ^ 2
            / ‖Work.BoseBoxFock.kmomLab ℓ (HM μ).N q‖ ^ 2 := by
      intro q _
      rw [hW1eq q, ← hℓdef, ← hellH, hkmom q]
      have hle1 : fu.f (‖Work.BoseBoxFock.kmomLab ℓ (HM μ).N q‖
          / Work.BoseBoxFock.uvRad ℓ (HM μ).N) ≤ 1 := fu.le_one _
      have hle0 : 0 ≤ fu.f (‖Work.BoseBoxFock.kmomLab ℓ (HM μ).N q‖
          / Work.BoseBoxFock.uvRad ℓ (HM μ).N) := fu.nonneg _
      have hsq : (Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N)
          (Work.BoseBoxFock.kmomLab ℓ (HM μ).N q)) ^ 2 ≤ 1 := by
        rw [Work.BoseBoxFock.uvCut]
        nlinarith
      calc (Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N)
              (Work.BoseBoxFock.kmomLab ℓ (HM μ).N q)
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
              (Work.BoseBoxFock.kmomLab ℓ (HM μ).N q)) ^ 2
            / ‖Work.BoseBoxFock.kmomLab ℓ (HM μ).N q‖ ^ 2
          = (Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N)
                (Work.BoseBoxFock.kmomLab ℓ (HM μ).N q)) ^ 2
            * (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
                (Work.BoseBoxFock.kmomLab ℓ (HM μ).N q)) ^ 2
            / ‖Work.BoseBoxFock.kmomLab ℓ (HM μ).N q‖ ^ 2 := by ring
        _ ≤ 1 * (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
                (Work.BoseBoxFock.kmomLab ℓ (HM μ).N q)) ^ 2
            / ‖Work.BoseBoxFock.kmomLab ℓ (HM μ).N q‖ ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (sq_nonneg _))
              (sq_nonneg _)
        _ = _ := by ring
    have hsum_le : (∑ q ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
          ((Work.BoseRowsFS.honF v h fc fu HM μ).PHq
            (Work.BoseRowsFS.honE v h fc fu HM μ).KH
            (Work.BoseRowsFS.honE v h fc fu HM μ).aScat),
          (Work.BoseRowsFS.honE v h fc fu HM μ).W1 q ^ 2
            / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom q‖ ^ 2)
        ≤ ∑ q ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab (HM μ).N)).erase 0,
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
              (Work.BoseBoxFock.kmomLab ℓ (HM μ).N q)) ^ 2
              / ‖Work.BoseBoxFock.kmomLab ℓ (HM μ).N q‖ ^ 2 := by
      refine le_trans (Finset.sum_le_sum hpt) ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun q _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
    calc (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          (∑ q ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
            ((Work.BoseRowsFS.honF v h fc fu HM μ).PHq
              (Work.BoseRowsFS.honE v h fc fu HM μ).KH
              (Work.BoseRowsFS.honE v h fc fu HM μ).aScat),
            (Work.BoseRowsFS.honE v h fc fu HM μ).W1 q ^ 2
              / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom q‖ ^ 2)
        = ℓ ^ (-(3 : ℝ)) * (∑ q ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
            ((Work.BoseRowsFS.honF v h fc fu HM μ).PHq
              (Work.BoseRowsFS.honE v h fc fu HM μ).KH
              (Work.BoseRowsFS.honE v h fc fu HM μ).aScat),
            (Work.BoseRowsFS.honE v h fc fu HM μ).W1 q ^ 2
              / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom q‖ ^ 2) := by rw [hell]
      _ ≤ ℓ ^ (-(3 : ℝ)) *
            (∑ q ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab (HM μ).N)).erase 0,
              (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
                (Work.BoseBoxFock.kmomLab ℓ (HM μ).N q)) ^ 2
                / ‖Work.BoseBoxFock.kmomLab ℓ (HM μ).N q‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsum_le (Real.rpow_nonneg hℓpos.le _)
      _ ≤ C * _root_.BoseGases.a v := hlat ℓ h1 h2 (HM μ).N
      _ = C * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat := by
          rw [show (Work.BoseRowsFS.honE v h fc fu HM μ).aScat = _root_.BoseGases.a v
            from rfl]
  · -- the degenerate side: `ellH v μ = 1`, and `(honE …).ell = sideAt μ (a v) ≤ 0`,
    -- so the left-hand side is `≤ 0` while `hlat 1` makes the right-hand side `≥ 0`
    have hell1 : Work.BoseBoxFock.ellH v μ = 1 := by
      rw [Work.BoseBoxFock.ellH, if_neg hpos]
    have hR1 : R ≤ 1 * Submission.BoseGases.chiR0 := by rw [← hell1]; exact h2
    have hS : 0 ≤ ∑ n ∈ (Finset.univ.erase (0 : Work.BoseBoxFock.Lab (HM μ).N)),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h 1)
          (Work.BoseBoxFock.kmomLab 1 (HM μ).N n)) ^ 2
          / ‖Work.BoseBoxFock.kmomLab 1 (HM μ).N n‖ ^ 2 :=
      Finset.sum_nonneg (fun n _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
    have hRHSnn : 0 ≤ C * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat := by
      have h' := hlat 1 le_rfl hR1 (HM μ).N
      rw [Real.one_rpow, one_mul] at h'
      have hmono : C * _root_.BoseGases.a v
          = C * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat := by
        rw [show (Work.BoseRowsFS.honE v h fc fu HM μ).aScat = _root_.BoseGases.a v
          from rfl]
      exact le_trans hS (le_trans h' hmono.le)
    have hell0 : (Work.BoseRowsFS.honE v h fc fu HM μ).ell ≤ 0 := by
      show Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ≤ 0
      exact not_lt.mp hpos
    have hpow : (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) ≤ 0 :=
      (Real.rpow_neg_natCast _ 3).trans_le (inv_nonpos.mpr (by
        have hx2 : 0 ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).ell
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell := mul_self_nonneg _
        calc (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ 3
            = ((Work.BoseRowsFS.honE v h fc fu HM μ).ell
                * (Work.BoseRowsFS.honE v h fc fu HM μ).ell)
                * (Work.BoseRowsFS.honE v h fc fu HM μ).ell := by ring
          _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx2 hell0))
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hpow
      (Finset.sum_nonneg (fun q _ => div_nonneg (sq_nonneg _) (sq_nonneg _)))) hRHSnn

/-- **FS §11 `eq:I2-integral` (row 1) in the dilute régime.**  Given FS §4's régime
for `v` and the side-length row `hrég` (`1 ≤ ℓ` and `R ≤ ℓ·chiR0` whenever
`μ a³ ≤ εg`), the honest weighted lattice sum of the UV-cut `Ŵ₁²` is bounded by
an absolute constant times `a v`, for every honest mode choice `HM` and every
`0 < μ` with `μ a³ ≤ εg`. -/
theorem RowSumW1sq_regime {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (εg : ℝ)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    ∃ Cws : ℝ, 0 ≤ Cws ∧ ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ),
      0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ q ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
              ((Work.BoseRowsFS.honF v h fc fu HM μ).PHq
                (Work.BoseRowsFS.honE v h fc fu HM μ).KH
                (Work.BoseRowsFS.honE v h fc fu HM μ).aScat),
            (Work.BoseRowsFS.honE v h fc fu HM μ).W1 q ^ 2
              / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom q‖ ^ 2
        ≤ Cws * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat := by
  obtain ⟨CL, hCL, hlat⟩ := honest_lattice_W1sq_le_uniform R hR hv_nonneg hvrad hv_supp
  obtain ⟨KE, hKE, hcont⟩ := honest_chat_W1sq_integral_le R hR hv_nonneg hvrad hv_supp
  refine ⟨CL * KE, mul_nonneg hCL hKE, ?_⟩
  intro HM μ hμ hε
  obtain ⟨h1, h2⟩ := hrég μ hμ hε
  refine rowSumW1sq_range (C := CL * KE) ?_ HM μ hμ h1 h2
  intro ℓ hℓ hRℓ N
  calc ℓ ^ (-(3 : ℝ)) *
        (∑ n ∈ (Finset.univ.erase (0 : Work.BoseBoxFock.Lab N)),
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
            (Work.BoseBoxFock.kmomLab ℓ N n)) ^ 2
            / ‖Work.BoseBoxFock.kmomLab ℓ N n‖ ^ 2)
      ≤ CL * (((2 * Real.pi) ^ 3)⁻¹
          * (∫ p, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2
              / (2 * ‖p‖ ^ 2))) := hlat ℓ hℓ hRℓ N
    _ ≤ CL * (KE * _root_.BoseGases.a v) :=
        mul_le_mul_of_nonneg_left (hcont ℓ hℓ hRℓ) hCL
    _ = (CL * KE) * _root_.BoseGases.a v := by ring

end Work.BoseRowsFS
