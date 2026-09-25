import Mathlib
import Submission.Work.NN.Core.fiberPot
import Submission.Work.NN.Core.fiberBeurling
import Submission.Work.NN.Core.fiberPot_fiberBeurling_induction
import Submission.Work.NN.Core.holderNorm_fiberPot_of_vanishing
import Submission.Work.NN.Core.contDiff_fiberPot
import Submission.Work.CR.Flat.Cauchy.polydiscCutoff
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_neg

namespace Work.NN.Core

open scoped NNReal ENNReal Topology
open Set MeasureTheory Filter

noncomputable section

variable {n : ℕ}

/-- **The fixed-disc fibre Cauchy potential is bounded on the Hölder scale `C^{m,α}`.**

With `fiberPot R j u z = -(1/π) ∫_{‖w‖ < R} u (z with z j replaced by w) / (w - z j) dw`
(`Submission.Work.NN.Core.fiberPot`), for `0 < α < 1`, `m : ℕ` and multi-radii `r` with
`0 < r i < R` for all `i`, there is `C > 0` (depending on `n, R, α, m, r`) such that for every
`C^m` function `u : ℂⁿ → ℂ`

  `‖fiberPot R j u‖_{C^{m,α}(polydisc 0 r)} ≤ C * ‖u‖_{C^{m,α}(polydisc 0 (r with r_j := R))}`.

No support hypothesis on `u` is needed (unlike for the translation invariant `dbarTransform`): the
region of integration is the *fixed* disc `‖w‖ < R` in the `j`-th fibre and the pole is at `z j`, so
evaluating the potential at `z ∈ polydisc 0 r` only reads `u` at points whose `j`-th coordinate lies
in `‖w‖ < R` and whose other coordinates are those of `z`; that is exactly the polydisc
`polydisc 0 (Function.update r j R)` on the right hand side.

The proof cuts `u = χ u + (1 - χ) u` with a smooth cutoff `χ` equal to `1` on a polydisc
`polydisc 0 s` with `r i < s i < R` and supported in the band `‖z j‖ < R`.  The first term is
band-supported, so `fiberPot_fiberBeurling_induction` applies to it; the second vanishes on
`polydisc 0 s`, so `holderNorm_fiberPot_of_vanishing` applies.  Both terms are related to `u` by
the Leibniz bound `holderNorm_mul_le_of_hasCompactSupport`. -/
theorem holderNorm_fiberPot_le {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα : 0 < α)
    (hα1 : α < 1) (m : ℕ) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Work.NN.Core.Cn n → ℂ, ContDiff ℝ m u →
      Work.CR.Flat.holderNorm m α (Work.NN.Core.fiberPot R j u) (Work.CR.Flat.polydisc 0 r)
        ≤ ENNReal.ofReal C *
          Work.CR.Flat.holderNorm m α u (Work.CR.Flat.polydisc 0 (Function.update r j R)) := by
  -- the intermediate and cutoff radii
  set s : Fin n → ℝ := fun i => (r i + R) / 2 with hs
  have hrs : ∀ i, r i < s i := by intro i; simp only [hs]; linarith [hrR i]
  have hsR : ∀ i, s i < R := by intro i; simp only [hs]; linarith [hrR i]
  have hs0 : ∀ i, 0 < s i := by intro i; simp only [hs]; linarith [hr i, hR]
  set s' : Fin n → ℝ := fun i => (s i + R) / 2 with hs'
  have hss' : ∀ i, s i < s' i := by intro i; simp only [hs']; linarith [hsR i]
  -- the two analytic inputs
  obtain ⟨Cp, hCp, hPm, _hSm⟩ :=
    fiberPot_fiberBeurling_induction hR j hα hα1 hr hrR m
  obtain ⟨Cr, hCr, hRem⟩ :=
    holderNorm_fiberPot_of_vanishing hR j hα hα1 m hr hrs hsR
  -- the cutoff
  obtain ⟨η, hηsm, hη01, hη1, hη0, hηcs, -, -⟩ :=
    Work.CR.Flat.Cauchy.polydiscCutoff (n := n) (c := (0 : Cn n)) (r₁ := s)
      (r₂ := Function.update s' j R) 0 hs0 (fun i => by
        by_cases hi : i = j
        · subst hi; rw [Function.update_self]; exact hsR i
        · rw [Function.update_of_ne hi]; exact hss' i)
  set χ : Cn n → ℂ := fun z => (η z : ℂ) with hχ
  have hχsm : ContDiff ℝ (m + 1) χ := by
    rw [hχ]
    exact (Complex.ofRealCLM.contDiff.comp hηsm).of_le (by simp)
  have hχsm_m : ContDiff ℝ m χ := hχsm.of_le (by simp)
  have hχcs : HasCompactSupport χ := by rw [hχ]; exact hηcs
  have hχ1 : ∀ z : Cn n, (∀ i, ‖z i‖ ≤ s i) → χ z = 1 := by
    intro z hz
    show (η z : ℂ) = 1
    rw [hη1 z (fun i => by simpa using hz i)]
    norm_num
  have hχ0 : ∀ z : Cn n, (∃ i, Function.update s' j R i ≤ ‖z i‖) → χ z = 0 := by
    intro z hz
    show (η z : ℂ) = 0
    rw [hη0 z (by obtain ⟨i, hi⟩ := hz; exact ⟨i, by simpa using hi⟩)]
    norm_num
  -- the Leibniz constant
  have hAopen : IsOpen (fiberAccess r j R) := fiberAccess_isOpen r j R
  obtain ⟨B1, hB1, hmul1⟩ := Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
    (Ω := fiberAccess r j R) hAopen.uniqueDiffOn (k := m) (α := α) hα.le hα1.le hχsm hχcs
  refine ⟨max 0 (max (Cp * B1 + Cr * (B1 + 1)) 0) + 1, by positivity, ?_⟩
  intro u hu
  by_cases htop : Work.CR.Flat.holderNorm m α u (fiberAccess r j R) = ⊤
  · have hgoal : Work.CR.Flat.holderNorm m α u
        (Work.CR.Flat.polydisc 0 (Function.update r j R)) = ⊤ := by rw [← htop]; rfl
    rw [hgoal, ENNReal.mul_top (by
      rw [ENNReal.ofReal_ne_zero_iff]
      positivity)]
    exact le_top
  · -- the two pieces
    set v1 : Cn n → ℂ := fun z => χ z * u z with hv1
    set v2 : Cn n → ℂ := fun z => (1 - χ z) * u z with hv2
    have hv1cd : ContDiff ℝ m v1 := by rw [hv1]; exact hχsm_m.mul hu
    have hv2cd : ContDiff ℝ m v2 := by rw [hv2]; exact (contDiff_const.sub hχsm_m).mul hu
    have hband1 : fiberBand R j v1 := by
      intro z hz
      simp only [hv1]
      have h0 : χ z = 0 := hχ0 z ⟨j, by simpa [Function.update_self] using hz⟩
      rw [h0, zero_mul]
    have hvanish2 : ∀ z : Cn n, (∀ i, ‖z i‖ < s i) → v2 z = 0 := by
      intro z hz
      simp only [hv2]
      have h1 : χ z = 1 := hχ1 z (fun i => (hz i).le)
      rw [h1]; ring
    -- the sum decomposition
    have hsplit : fiberPot R j u = fun z => fiberPot R j v1 z + fiberPot R j v2 z := by
      funext z
      have h1 : Continuous v1 := hv1cd.continuous
      have h2 : Continuous v2 := hv2cd.continuous
      have h := fiberPot_add R j h1 h2 z
      have hsum : (fun y => v1 y + v2 y) = u := by
        funext y
        rw [hv1, hv2]; ring
      rw [hsum] at h
      exact h
    rw [show Work.CR.Flat.holderNorm m α (fiberPot R j u) (Work.CR.Flat.polydisc 0 r)
        = Work.CR.Flat.holderNorm m α (fun z => fiberPot R j v1 z + fiberPot R j v2 z)
            (Work.CR.Flat.polydisc 0 r) from by rw [hsplit]]
    have hΩopen : IsOpen (Work.CR.Flat.polydisc (0 : Cn n) r) :=
      Work.CR.Flat.isOpen_polydisc 0 r
    have hv1sub : Work.CR.Flat.polydisc (0 : Cn n) r ⊆ {z : Cn n | ‖z j‖ < R} := by
      intro z hz
      have h := hz j
      simpa using lt_of_lt_of_le h (hrR j).le
    have hadd := Work.CR.Flat.Holder.holderNorm_add_le (k := m) (α := α)
      (f := fiberPot R j v1) (g := fiberPot R j v2) (Ω := Work.CR.Flat.polydisc 0 r)
      ((contDiff_fiberPot R m j hv1cd).mono hv1sub)
      ((contDiff_fiberPot R m j hv2cd).mono hv1sub)
      hΩopen.uniqueDiffOn
    refine (hadd.trans ?_)
    -- the Leibniz bounds
    have hleib1 : Work.CR.Flat.holderNorm m α v1 (fiberAccess r j R)
        ≤ ENNReal.ofReal B1 * Work.CR.Flat.holderNorm m α u (fiberAccess r j R) := by
      rw [hv1]
      exact hmul1 u hu.contDiffOn
    have hleib2 : Work.CR.Flat.holderNorm m α v2 (fiberAccess r j R)
        ≤ ENNReal.ofReal (B1 + 1) * Work.CR.Flat.holderNorm m α u (fiberAccess r j R) := by
      have hdecomp : v2 = fun z => u z + -(χ z * u z) := by
        funext z; rw [hv2]; ring
      have hsmooth1 : ContDiffOn ℝ (m:ℕ∞) u (fiberAccess r j R) := hu.contDiffOn
      have hsmooth2 : ContDiffOn ℝ (m:ℕ∞) (fun z => -(χ z * u z)) (fiberAccess r j R) :=
        (hχsm_m.contDiffOn.mul hu.contDiffOn).neg
      calc Work.CR.Flat.holderNorm m α v2 (fiberAccess r j R)
          = Work.CR.Flat.holderNorm m α (fun z => u z + -(χ z * u z))
              (fiberAccess r j R) := by rw [hdecomp]
        _ ≤ Work.CR.Flat.holderNorm m α u (fiberAccess r j R)
              + Work.CR.Flat.holderNorm m α (fun z => -(χ z * u z)) (fiberAccess r j R) :=
            Work.CR.Flat.Holder.holderNorm_add_le hsmooth1 hsmooth2 hAopen.uniqueDiffOn
        _ = Work.CR.Flat.holderNorm m α u (fiberAccess r j R)
              + Work.CR.Flat.holderNorm m α (fun z => χ z * u z) (fiberAccess r j R) := by
            rw [show (fun z => -(χ z * u z)) = -(fun z => χ z * u z) from rfl,
              Work.CR.Flat.Holder.holderNorm_neg (hχsm_m.contDiffOn.mul hu.contDiffOn)
                hAopen.uniqueDiffOn]
        _ ≤ Work.CR.Flat.holderNorm m α u (fiberAccess r j R)
              + ENNReal.ofReal B1 * Work.CR.Flat.holderNorm m α u (fiberAccess r j R) :=
            add_le_add le_rfl hleib1
        _ = ENNReal.ofReal (B1 + 1) * Work.CR.Flat.holderNorm m α u (fiberAccess r j R) := by
            nth_rewrite 1 [← one_mul (Work.CR.Flat.holderNorm m α u (fiberAccess r j R))]
            rw [← add_mul, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hB1.le, add_comm]
    -- the two estimates
    have hN : Work.CR.Flat.holderNorm m α u (fiberAccess r j R)
        = Work.CR.Flat.holderNorm m α u (Work.CR.Flat.polydisc 0 (Function.update r j R)) := rfl
    have hb1 : Work.CR.Flat.holderNorm m α (fiberPot R j v1) (Work.CR.Flat.polydisc 0 r)
        ≤ ENNReal.ofReal (Cp * B1) * Work.CR.Flat.holderNorm m α u
            (Work.CR.Flat.polydisc 0 (Function.update r j R)) := by
      refine (hPm v1 hv1cd hband1).trans ?_
      rw [← hN]
      refine (mul_le_mul' (le_refl _) hleib1).trans ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul hCp.le]
    have hb2 : Work.CR.Flat.holderNorm m α (fiberPot R j v2) (Work.CR.Flat.polydisc 0 r)
        ≤ ENNReal.ofReal (Cr * (B1 + 1)) * Work.CR.Flat.holderNorm m α u
            (Work.CR.Flat.polydisc 0 (Function.update r j R)) := by
      refine (hRem v2 hv2cd hvanish2).trans ?_
      rw [← hN]
      refine (mul_le_mul' (le_refl _) hleib2).trans ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul hCr.le]
    refine (add_le_add hb1 hb2).trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hCp.le hB1.le) (mul_nonneg hCr.le (by linarith))]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (le_refl _)
    have h2 : Cp * B1 + Cr * (B1 + 1)
        ≤ max 0 (max (Cp * B1 + Cr * (B1 + 1)) 0) + 1 := by
      have h3 := le_max_right 0 (max (Cp * B1 + Cr * (B1 + 1)) 0)
      have h4 := le_max_left (Cp * B1 + Cr * (B1 + 1)) 0
      linarith
    linarith [h2]

end
end Work.NN.Core
