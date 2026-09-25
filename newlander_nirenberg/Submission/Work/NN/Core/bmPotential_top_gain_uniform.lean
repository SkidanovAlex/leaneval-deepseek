import Mathlib
import Submission.Work.NN.Core.bmPot_riesz_Ck
import Submission.Work.NN.Core.bmPot_holder_C0a
import Submission.Work.CR.Flat.Cauchy.iteratedFDeriv_succ_of_slice_bounds

noncomputable section

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace Work.NN.Core

/-- **Uniform (in `k`) top-order Schauder bound for the Bochner–Martinelli potential.**

Same conclusion as `Work.NN.Core.bmPotential_top_gain`, but the constant is independent of `k`:
there is `C > 0`, depending only on `n`, `c`, `r` and `α`, such that for *every* `k` and every
`C^k` datum `f` with finite `C^{k,α}`-norm supported in the half polydisc `polydisc c (r/2)`,

  `‖D^{k+1}(bmPotential f)‖_sup + ‖D^{k+1}(bmPotential f)‖_α ≤ C · Σ_j ‖f_j‖_{C^{k,α}}`

on `polydisc c (r/2)`.  The proof is that of `bmPotential_top_gain`, whose constant `2 C₀` is
already obtained from the `k = 0` Schauder estimate `bmPot_holder_C0a` before the datum is
introduced, hence does not depend on `k`. -/
theorem bmPotential_top_gain_uniform {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (f : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ k (f j)) →
      (∀ j, Work.CR.Flat.holderNorm k α (f j) Set.univ < ⊤) →
      (∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → f j z = 0) →
      Work.CR.Flat.iterDerivNorm (k + 1) (Work.CR.Flat.Cauchy.bmPotential f)
          (Work.CR.Flat.polydisc c (fun j => r j / 2))
        + Work.CR.Flat.holderSeminorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential f)
          (Work.CR.Flat.polydisc c (fun j => r j / 2))
      ≤ ENNReal.ofReal C * ∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ := by
  classical
  -- the `C^{0,α}` estimate for the datum, on the doubled polydisc `polydisc c (2r)`
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.NN.Core.bmPot_holder_C0a (n := n) hn (c := c)
    (r := fun j => 2 * r j) hα hα1 (fun j => by linarith [hr j])
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro k f hf hffin hfsup
  set P : Set (Fin n → ℂ) := Work.CR.Flat.polydisc c (fun j => r j / 2) with hPdef
  have hPopen : IsOpen P := Work.CR.Flat.isOpen_polydisc c _
  have hPconv : Convex ℝ P := Work.NN.Core.convex_polydisc c _
  have hsub : P ⊆ Work.CR.Flat.polydisc c r := by
    rw [hPdef]
    exact Work.CR.Flat.polydisc_mono (fun j => by linarith [hr j])
  -- the total size of the data, as a real number
  set Sm : ℝ := ∑ j, (Work.CR.Flat.holderNorm k α (f j) Set.univ).toReal with hSmdef
  have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
  have hsumlt : (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ) < ⊤ := by
    rw [ENNReal.sum_lt_top]
    exact fun j _ => hffin j
  have hsum_eq : (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ) = ENNReal.ofReal Sm := by
    rw [hSmdef, ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_toReal (ne_of_lt (hffin j))).symm
  -- ### the derived datum `ψ u = D^k f · u`
  set ψ : (Fin k → (Fin n → ℂ)) → Fin n → (Fin n → ℂ) → ℂ :=
    fun u j y => iteratedFDeriv ℝ k (f j) y u with hψdef
  have hψcont : ∀ u j, Continuous (ψ u j) := by
    intro u j
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => (Fin n → ℂ)) ℂ u).continuous).comp
      ((hf j).continuous_iteratedFDeriv (m := k) le_rfl)
  -- the derived datum vanishes outside the polydisc of radii `r`
  have hψsupp : ∀ u j z, (∃ i, r i ≤ ‖z i - c i‖) → ψ u j z = 0 := by
    intro u j z hz
    obtain ⟨i, hi⟩ := hz
    have hev : f j =ᶠ[𝓝 z] (0 : (Fin n → ℂ) → ℂ) := by
      refine Filter.mem_of_superset (Metric.ball_mem_nhds z (half_pos (hr i))) ?_
      intro w hw
      apply hfsup j w
      refine ⟨i, ?_⟩
      have h1 : ‖w i - z i‖ ≤ dist w z := by
        rw [dist_eq_norm]
        exact norm_le_pi_norm (w - z) i
      have h2 : ‖z i - c i‖ ≤ ‖w i - c i‖ + ‖w i - z i‖ := by
        have h4 : ‖z i - c i‖ ≤ ‖z i - w i‖ + ‖w i - c i‖ := by
          calc ‖z i - c i‖ = ‖(z i - w i) + (w i - c i)‖ := by ring_nf
            _ ≤ ‖z i - w i‖ + ‖w i - c i‖ := norm_add_le _ _
        rw [norm_sub_rev (z i) (w i)] at h4
        linarith
      have h3 : dist w z < r i / 2 := by
        simpa only [Metric.mem_ball, dist_comm] using hw
      linarith
    have h2 : iteratedFDeriv ℝ k (f j) z = iteratedFDeriv ℝ k (0 : (Fin n → ℂ) → ℂ) z :=
      (hev.iteratedFDeriv ℝ k).eq_of_nhds
    show iteratedFDeriv ℝ k (f j) z u = 0
    rw [h2]
    simp
  -- the `C^{0,α}`-norm of the derived datum
  have hψnorm : ∀ u j, Work.CR.Flat.holderNorm 0 α (ψ u j) Set.univ
      ≤ ENNReal.ofReal (∏ i, ‖u i‖) * Work.CR.Flat.holderNorm k α (f j) Set.univ := by
    intro u j
    exact Work.CR.Flat.Cauchy.holderNorm_zero_iteratedFDeriv_apply_le (m := k) le_rfl (α := α) u
  have hψfin : ∀ u j, Work.CR.Flat.holderNorm 0 α (ψ u j) Set.univ < ⊤ := by
    intro u j
    refine lt_of_le_of_lt (hψnorm u j) ?_
    rw [ENNReal.mul_lt_top_iff]
    exact Or.inl ⟨ENNReal.ofReal_lt_top, hffin j⟩
  have hψsum : ∀ u, (∑ j, Work.CR.Flat.holderNorm 0 α (ψ u j) Set.univ)
      ≤ ENNReal.ofReal (∏ i, ‖u i‖) * ENNReal.ofReal Sm := by
    intro u
    calc (∑ j, Work.CR.Flat.holderNorm 0 α (ψ u j) Set.univ)
        ≤ ∑ j, ENNReal.ofReal (∏ i, ‖u i‖) * Work.CR.Flat.holderNorm k α (f j) Set.univ :=
          Finset.sum_le_sum fun j _ => hψnorm u j
      _ = ENNReal.ofReal (∏ i, ‖u i‖) * (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ) := by
          rw [Finset.mul_sum]
      _ = ENNReal.ofReal (∏ i, ‖u i‖) * ENNReal.ofReal Sm := by rw [hsum_eq]
  -- ### the `C^{1,α}` bound for the potential of the derived datum, on `polydisc c r`
  have h1α : ∀ u, Work.CR.Flat.holderNorm 1 α
        (fun z => Work.CR.Flat.Cauchy.bmPot (ψ u) z) (Work.CR.Flat.polydisc c r)
      ≤ ENNReal.ofReal (C₀ * (∏ i, ‖u i‖) * Sm) := by
    intro u
    have hsupp2 : ∀ j z, (∃ i, (2 * r i) / 2 ≤ ‖z i - c i‖) → ψ u j z = 0 := by
      intro j z hz
      obtain ⟨i, hi⟩ := hz
      exact hψsupp u j z ⟨i, by rw [show 2 * r i / 2 = r i from by ring] at hi; exact hi⟩
    have hmain := hC₀ (ψ u) hsupp2 (fun j => ne_of_lt (hψfin u j))
    have hpd : (fun j : Fin n => (2 * r j) / 2) = r := by funext j; ring
    calc Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.Cauchy.bmPot (ψ u) z)
          (Work.CR.Flat.polydisc c r)
        = Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.Cauchy.bmPot (ψ u) z)
          (Work.CR.Flat.polydisc c (fun j => (2 * r j) / 2)) := by rw [hpd]
      _ ≤ ENNReal.ofReal C₀ * ∑ j, Work.CR.Flat.holderNorm 0 α (ψ u j) Set.univ := hmain
      _ ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal (∏ i, ‖u i‖) * ENNReal.ofReal Sm) :=
          mul_le_mul_right (hψsum u) _
      _ = ENNReal.ofReal (C₀ * (∏ i, ‖u i‖) * Sm) := by
          calc ENNReal.ofReal C₀ * (ENNReal.ofReal (∏ i, ‖u i‖) * ENNReal.ofReal Sm)
              = (ENNReal.ofReal C₀ * ENNReal.ofReal (∏ i, ‖u i‖)) * ENNReal.ofReal Sm := by
                rw [mul_assoc]
            _ = ENNReal.ofReal (C₀ * (∏ i, ‖u i‖)) * ENNReal.ofReal Sm := by
                rw [← ENNReal.ofReal_mul hC₀pos.le]
            _ = ENNReal.ofReal (C₀ * (∏ i, ‖u i‖) * Sm) := by
                rw [← ENNReal.ofReal_mul (mul_nonneg hC₀pos.le
                  (Finset.prod_nonneg fun i _ => norm_nonneg _))]
  -- ### the slice bounds required by the top-order currying lemma
  have hslice_bound : ∀ u, ∀ z ∈ P,
      ‖fderiv ℝ (fun y => Work.CR.Flat.Cauchy.bmPotential (ψ u) y) z‖ ≤ (C₀ * Sm) * ∏ i, ‖u i‖ := by
    intro u z hz
    have hfun : (fun y => Work.CR.Flat.Cauchy.bmPotential (ψ u) y)
        = fun y => Work.CR.Flat.Cauchy.bmPot (ψ u) y :=
      funext fun y => Work.CR.Flat.Cauchy.bmPotential_eq_bmPot (ψ u) y
    rw [hfun]
    have hC : 0 ≤ C₀ * (∏ i, ‖u i‖) * Sm := by
      refine mul_nonneg (mul_nonneg hC₀pos.le (Finset.prod_nonneg fun i _ => norm_nonneg _)) hSm0
    have h4 := Work.NN.Core.holderNorm_one_bounds (Work.CR.Flat.isOpen_polydisc c r) hC (h1α u)
    have hz' := h4.2.2.1 z (hsub hz)
    rwa [show C₀ * (∏ i, ‖u i‖) * Sm = (C₀ * Sm) * ∏ i, ‖u i‖ from by ring] at hz'
  have hslice_holder : ∀ u, ∀ z ∈ P, ∀ z' ∈ P,
      ‖fderiv ℝ (fun y => Work.CR.Flat.Cauchy.bmPotential (ψ u) y) z
        - fderiv ℝ (fun y => Work.CR.Flat.Cauchy.bmPotential (ψ u) y) z'‖
      ≤ ((C₀ * Sm) * ∏ i, ‖u i‖) * ‖z - z'‖ ^ α := by
    intro u z hz z' hz'
    have hfun : (fun y => Work.CR.Flat.Cauchy.bmPotential (ψ u) y)
        = fun y => Work.CR.Flat.Cauchy.bmPot (ψ u) y :=
      funext fun y => Work.CR.Flat.Cauchy.bmPotential_eq_bmPot (ψ u) y
    rw [hfun]
    have hC : 0 ≤ C₀ * (∏ i, ‖u i‖) * Sm := by
      refine mul_nonneg (mul_nonneg hC₀pos.le (Finset.prod_nonneg fun i _ => norm_nonneg _)) hSm0
    have h4 := Work.NN.Core.holderNorm_one_bounds (Work.CR.Flat.isOpen_polydisc c r) hC (h1α u)
    have hz'' := h4.2.2.2 z (hsub hz) z' (hsub hz')
    rwa [show C₀ * (∏ i, ‖u i‖) * Sm = (C₀ * Sm) * ∏ i, ‖u i‖ from by ring] at hz''
  -- ### the slices of `D^k (bmPotential f)` are the potentials of the derived data
  have hslice : ∀ u, (fun y => iteratedFDeriv ℝ k (Work.CR.Flat.Cauchy.bmPotential f) y u)
      = fun y => Work.CR.Flat.Cauchy.bmPotential (ψ u) y := by
    intro u
    funext y
    exact Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv (n := n) hn (c := c) (R := r) hr
      (G := f) hf hfsup u y
  have hslice_diff : ∀ u, ∀ z ∈ P,
      DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ k (Work.CR.Flat.Cauchy.bmPotential f) y u) z := by
    intro u z hz
    rw [hslice u]
    exact Work.NN.Core.bmPot_diff_continuous (n := n) hn (c := c) (r := fun j => 2 * r j) hα hα1
      (fun j => by linarith [hr j]) (hψcont u) (fun j => hψfin u j)
      (fun j w hw => by
        obtain ⟨i, hi⟩ := hw
        exact hψsupp u j w ⟨i, by rw [show 2 * r i / 2 = r i from by ring] at hi; exact hi⟩)
      z (by
        rw [show (fun j : Fin n => (2 * r j) / 2) = r from funext fun j => by ring]
        exact hsub hz)
  -- ### the top-order estimate via the currying lemma
  have htop := Work.CR.Flat.Cauchy.iteratedFDeriv_succ_of_slice_bounds (F := Work.CR.Flat.Cauchy.bmPotential f)
    (Ω := P) hPopen hPconv hα (mul_nonneg hC₀pos.le hSm0)
    hslice_diff
    (fun u z hz => by rw [hslice u]; exact hslice_bound u z hz)
    (fun u z hz z' hz' => by rw [hslice u]; exact hslice_holder u z hz z' hz')
  -- ### extract the two top-order bounds and add them
  have htop1 : Work.CR.Flat.iterDerivNorm (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) P
      ≤ ENNReal.ofReal C₀ * ∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ := by
    rw [Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun z hz => ?_
    rw [show iteratedFDerivWithin ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) P z
        = iteratedFDeriv ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) z from
        iteratedFDerivWithin_of_isOpen (k + 1) hPopen hz]
    calc ENNReal.ofReal ‖iteratedFDeriv ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) z‖
        ≤ ENNReal.ofReal (C₀ * Sm) := ENNReal.ofReal_le_ofReal
          (ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hC₀pos.le hSm0)
            (fun w => htop.1 z hz w))
      _ = ENNReal.ofReal C₀ * ∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ := by
          rw [hsum_eq, ENNReal.ofReal_mul hC₀pos.le]
  have htop2 : Work.CR.Flat.holderSeminorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential f) P
      ≤ ENNReal.ofReal C₀ * ∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ := by
    rw [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun z hz => iSup₂_le fun z' hz' => iSup_le fun hzz => ?_
    rw [show iteratedFDerivWithin ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) P z
          = iteratedFDeriv ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) z from
          iteratedFDerivWithin_of_isOpen (k + 1) hPopen hz,
        show iteratedFDerivWithin ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) P z'
          = iteratedFDeriv ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) z' from
          iteratedFDerivWithin_of_isOpen (k + 1) hPopen hz']
    have hb : 0 < ‖z - z'‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzz)) α
    calc ENNReal.ofReal (‖iteratedFDeriv ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) z
            - iteratedFDeriv ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) z'‖ / ‖z - z'‖ ^ α)
        ≤ ENNReal.ofReal (((C₀ * Sm) * ‖z - z'‖ ^ α) / ‖z - z'‖ ^ α) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (htop.2 z hz z' hz') hb.le)
      _ = ENNReal.ofReal (C₀ * Sm) := by rw [mul_div_cancel_right₀ _ (ne_of_gt hb)]
      _ = ENNReal.ofReal C₀ * ∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ := by
          rw [hsum_eq, ENNReal.ofReal_mul hC₀pos.le]
  calc Work.CR.Flat.iterDerivNorm (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) P
        + Work.CR.Flat.holderSeminorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential f) P
      ≤ ENNReal.ofReal C₀ * (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ)
        + ENNReal.ofReal C₀ * (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ) :=
        add_le_add htop1 htop2
    _ = ENNReal.ofReal (2 * C₀)
          * (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ) := by
        rw [← add_mul, ← ENNReal.ofReal_add hC₀pos.le hC₀pos.le]
        congr 1
        ring

end Work.NN.Core
