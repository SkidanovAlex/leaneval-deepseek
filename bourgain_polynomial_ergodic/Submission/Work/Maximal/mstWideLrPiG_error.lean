import Mathlib
import Submission.Work.Maximal.mstWideAux

namespace Work.Maximal

open Finset
open scoped BigOperators

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

open Work.BourgainPlan.Maximal (mstG mstWeyl mstU mstLevel mstLevel_succ iwRep)

/-- The annulus `𝒰(s+1) ∖ 𝒰(s)` of the level-`s` model is contained in `𝒰(s+1)`. -/
theorem mstAnnulus_subset_mstU (l s : ℕ) : mstAnnulus l s ⊆ mstU l (s + 1) := by
  intro β hβ
  have h1 : β ∈ mstLevel l (s + 1) := (Finset.mem_sdiff.mp hβ).1
  rwa [mstLevel_succ] at h1

/-- **The pointwise error of the weighted wide arc sum** (MST arXiv:1512.07518, eq. (95) inside
(79)): for large `s` the weighted arc sum `Π̃^G_s = Σ_{β} star (G β) ϱ_s(·−β)` differs at every
frequency `ξ` from the frozen multiplier `star (m_J ξ) · Π̃_s(ξ)` (`J = ⌊exp √(s+1)⌋`,
`μ_J = mstWeyl P J`) by at most `C exp(−√(s+1)/2)`.

Indeed, writing `W = mstWeyl P (mstLrJ s) ξ`,

`Π̃^G_s(ξ) − star W · Π̃_s(ξ) = Σ_{β ∈ annulus} (star (G β) − star W) · ϱ_s(ξ−β)`,

and every summand is handled separately: if `ϱ_s(ξ−β) = 0` it vanishes, and otherwise
`|iwRep (ξ−β)| ≤ ½·2^{−s(d−χ)}` (`mstLrBump_abs_iwRep`), which is exactly the hypothesis under
which `mstLrWeyl_approx_of_abs` (MST's pointwise Weyl approximation) gives
`‖G β − W‖ ≤ C exp(−√(s+1)/2)`.  Summing and using the uniform arc-sum bound
`Σ_β ‖ϱ_s(ξ−β)‖ ≤ M'` (`mstLrBump_arcSum_le`) yields the claim. -/
theorem mstWideLrPiG_error (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ S₀ : ℕ, ∀ s : ℕ, S₀ ≤ s → ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
      ‖Work.Maximal.mstWidePiG P l χ η s ξ
          - star (Work.BourgainPlan.Maximal.mstWeyl P (Work.Maximal.mstLrJ s) ξ)
              * Work.Maximal.mstWidePi P l χ η s ξ‖
        ≤ C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
  classical
  -- the two analytic inputs
  obtain ⟨Cw, hCw, N₁, hN₁⟩ := mstLrWeyl_approx_of_abs P hd hc hχ0 hχ1 l hl
  obtain ⟨M', hM', hM'le⟩ :=
    mstLrBump_arcSum_le P hd hχ1 l hl η M hM hηc.continuous hηbd hηsup
  -- the quantitative narrowness of the wide bump, valid for large `s`
  have hχd : χ ≤ (P.natDegree : ℝ) := by
    have hdR : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨S₁, hS₁⟩ := mstLrBump_abs_iwRep P hd (le_of_lt hχ0) hχd η hηsup
  refine ⟨Cw * M' + 1, by positivity, max S₁ N₁, fun s hs ξ => ?_⟩
  have hsS₁ : S₁ ≤ s := le_trans (le_max_left _ _) hs
  have hsN₁ : N₁ ≤ s := le_trans (le_max_right _ _) hs
  set E : ℝ := Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hE0 : 0 ≤ E := hEpos.le
  -- the pointwise bound on each summand
  have key : ∀ β ∈ mstAnnulus l s,
      ‖star (mstG P β) - star (mstWeyl P (mstLrJ s) ξ)‖
          * ‖mstWideBump P χ η s (ξ - β)‖
        ≤ (Cw * E) * ‖mstWideBump P χ η s (ξ - β)‖ := by
    intro β hβ
    rcases eq_or_ne (mstWideBump P χ η s (ξ - β)) 0 with hzero | hne
    · rw [hzero, norm_zero, mul_zero, mul_zero]
    · have hβU : β ∈ mstU l (s + 1) := mstAnnulus_subset_mstU l s hβ
      have habs := hS₁ s hsS₁ (ξ - β) hne
      have hw := hN₁ s hsN₁ β ξ hβU habs
      have hsub : star (mstG P β) - star (mstWeyl P (mstLrJ s) ξ)
          = star (mstG P β - mstWeyl P (mstLrJ s) ξ) := (star_sub _ _).symm
      have hnorm : ‖star (mstG P β) - star (mstWeyl P (mstLrJ s) ξ)‖
          = ‖mstWeyl P (mstLrJ s) ξ - mstG P β‖ := by
        rw [hsub, norm_star, norm_sub_rev]
      calc ‖star (mstG P β) - star (mstWeyl P (mstLrJ s) ξ)‖
              * ‖mstWideBump P χ η s (ξ - β)‖
          = ‖mstWeyl P (mstLrJ s) ξ - mstG P β‖
              * ‖mstWideBump P χ η s (ξ - β)‖ := by rw [hnorm]
        _ ≤ (Cw * E) * ‖mstWideBump P χ η s (ξ - β)‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [hEdef]
            exact hw
  -- the algebraic splitting of the difference into the summands handled above
  have hsplit : mstWidePiG P l χ η s ξ
        - star (mstWeyl P (mstLrJ s) ξ) * mstWidePi P l χ η s ξ
      = ∑ β ∈ mstAnnulus l s,
          (star (mstG P β) - star (mstWeyl P (mstLrJ s) ξ))
            * mstWideBump P χ η s (ξ - β) := by
    rw [mstWidePiG_apply, mstWidePi_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun β _ => by rw [sub_mul])
  rw [hsplit]
  calc ‖∑ β ∈ mstAnnulus l s,
          (star (mstG P β) - star (mstWeyl P (mstLrJ s) ξ))
            * mstWideBump P χ η s (ξ - β)‖
      ≤ ∑ β ∈ mstAnnulus l s,
          ‖(star (mstG P β) - star (mstWeyl P (mstLrJ s) ξ))
            * mstWideBump P χ η s (ξ - β)‖ := norm_sum_le _ _
    _ = ∑ β ∈ mstAnnulus l s,
          ‖star (mstG P β) - star (mstWeyl P (mstLrJ s) ξ)‖
            * ‖mstWideBump P χ η s (ξ - β)‖ :=
        Finset.sum_congr rfl (fun β _ => norm_mul _ _)
    _ ≤ ∑ β ∈ mstAnnulus l s, (Cw * E) * ‖mstWideBump P χ η s (ξ - β)‖ :=
        Finset.sum_le_sum key
    _ = (Cw * E) * ∑ β ∈ mstAnnulus l s, ‖mstWideBump P χ η s (ξ - β)‖ := by
        rw [Finset.mul_sum]
    _ ≤ (Cw * E) * M' :=
        mul_le_mul_of_nonneg_left (hM'le s ξ) (mul_nonneg hCw.le hE0)
    _ ≤ (Cw * M' + 1) * E := by
        have h1 : (Cw * E) * M' = (Cw * M') * E := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right (by linarith [hCw, hM']) hE0

end Work.Maximal
