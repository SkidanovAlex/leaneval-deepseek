import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.DbarCnPertAux
import Submission.Work.NN.Core.norm_Bop_le
import Submission.Work.NN.Core.beltramiImplicit_fixedpoint
import Submission.Work.NN.Core.famNorm_contraction_fixedpoint
import Submission.Work.NN.Core.czB_L2_bounded_continuous
import Submission.Work.NN.Core.contDiff_one_bmPotential_of_holder
import Submission.Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul
import Submission.Work.NN.Core.bmPotential_differentiableAt_holder
import Submission.Work.NN.Core.dbarCn_implicit_form
import Submission.Work.NN.Core.implicit_fixpoint_eq_zero
import Submission.Work.NN.Core.exists_betaCut_small
import Submission.Work.NN.Ratio.Setup
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport

/-!
# The Beltrami reduction of the perturbed `∂̄`-equation

Given a perturbation `A` of the standard complex structure `Jstd` on `ℂⁿ`, small in `C^{0,α}` on
a polydisc, every `C¹` compactly supported solution `W` of the perturbed equation
`dbarCn (Jstd + A) W = G` with `G` of finite `C^{0,α}` norm can be written in Beltrami form

  `∂̄_m W = Σ_j c m j · ∂_j W + G'_m`

with a *smooth* compactly supported coefficient `c` of `C^{0,α}`-norm `≤ C ε` and an error
`G'` which is again of finite `C^{0,α}` norm.

The proof does **not** construct the decoupled coefficient `(1+BopBar)⁻¹ Bop` (which need not be
smooth when `A` is only Hölder).  Instead it is shown directly that
`u_m = ∂̄_m W` has finite `C^{0,α}`-norm, after which `c = 0` does the job:

* the implicit form `(1 + BopBar A z) u = G + Bop A z d` (`dbarCn_implicit_form`) together with
  the Bochner–Martinelli identity `bmPotential (∂̄W) = bmGamma n · W` turns the equation into the
  fixed point equation `u = Tfun β u + G` with `β = betaCoef A` (a *Hölder* coefficient, cut off
  so as to be supported in the polydisc);
* `famNorm_contraction_fixedpoint` produces a solution `F` of the same fixed point equation with
  finite `C^{0,α}`-norm (the operator is a contraction because the Schauder estimate for
  `∂(bmPotential ·)` is available for `C^{0,α}` data);
* `u - F` solves the *homogeneous* implicit equation, so it vanishes by the `L²`
  Calderón–Zygmund estimate (`implicit_fixpoint_eq_zero`).
-/

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

namespace Work.NN.Core

variable {n : ℕ}

/-! ## Elementary calculus helpers -/

/-- `dCoord` of a constant multiple. -/
lemma dCoord_const_mul (γ : ℂ) (f : Cn n → ℂ) (j : Fin n) (z : Cn n)
    (hf : DifferentiableAt ℝ f z) :
    Work.CR.Flat.dCoord j (fun y => γ * f y) z = γ * Work.CR.Flat.dCoord j f z := by
  simp only [Work.CR.Flat.dCoord, fderiv_const_mul hf, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- The `∂`-derivatives of the Bochner--Martinelli potential of the `(0,1)`-derivatives of a `C¹`
compactly supported function `W` are `bmGamma n` times the `∂`-derivatives of `W`
(Pompeiu + `fderiv_const_mul`). -/
lemma dCoord_bmPotential_dbarCoord (hn : 0 < n) {W : Cn n → ℂ}
    (hW : ContDiff ℝ 1 W) (hWs : HasCompactSupport W) (j : Fin n) (z : Cn n) :
    Work.CR.Flat.dCoord j
        (Work.CR.Flat.Cauchy.bmPotential (fun l => Work.CR.Flat.dbarCoord l W)) z
      = Work.CR.Flat.Cauchy.bmGamma n * Work.CR.Flat.dCoord j W z := by
  have hfun : Work.CR.Flat.Cauchy.bmPotential (fun l => Work.CR.Flat.dbarCoord l W)
      = fun y => Work.CR.Flat.Cauchy.bmGamma n * W y := by
    funext y
    exact (bmPotential_dbarCoord_eq_bmGamma_mul hn hW hWs y).symm
  rw [hfun]
  exact dCoord_const_mul _ _ _ _ ((hW.differentiable (by norm_num)).differentiableAt)

/-- At a point where `W` is locally zero, `fderiv ℝ W` vanishes. -/
lemma fderiv_eq_zero_of_notMem_tsupport {W : Cn n → ℂ} {z : Cn n}
    (hzt : z ∉ tsupport W) : fderiv ℝ W z = 0 := by
  have hev : W =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [(isClosed_tsupport W).isOpen_compl.mem_nhds hzt] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  have h : fderiv ℝ W z = fderiv ℝ (fun _ : Cn n => (0 : ℂ)) z := hev.fderiv_eq
  rw [h]
  simp

/-- If `W` vanishes on the closed complement of `polydisc 0 ρ'` then its derivative vanishes at
every point *strictly* outside `polydisc 0 ρ'`. -/
lemma fderiv_eq_zero_of_vanishing {W : Cn n → ℂ} {ρ' : Fin n → ℝ}
    (hWvan : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → W z = 0) :
    ∀ z, (∃ i, ρ' i < ‖z i‖) → fderiv ℝ W z = 0 := by
  intro z hz
  obtain ⟨j, hj⟩ := hz
  have hopen : IsOpen {w : Cn n | ρ' j < ‖w j‖} :=
    isOpen_lt continuous_const ((continuous_apply j).norm)
  have hev : W =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds (show z ∈ {w : Cn n | ρ' j < ‖w j‖} from hj)] with w hw
    exact hWvan w ⟨j, le_of_lt hw⟩
  have h : fderiv ℝ W z = fderiv ℝ (fun _ : Cn n => (0 : ℂ)) z := hev.fderiv_eq
  rw [h]
  simp

lemma dbarCoord_eq_zero_of_fderiv_eq_zero {W : Cn n → ℂ} {z : Cn n}
    (hfd : fderiv ℝ W z = 0) (m : Fin n) : Work.CR.Flat.dbarCoord m W z = 0 := by
  simp [Work.CR.Flat.dbarCoord, hfd]

lemma dCoord_eq_zero_of_fderiv_eq_zero {W : Cn n → ℂ} {z : Cn n}
    (hfd : fderiv ℝ W z = 0) (m : Fin n) : Work.CR.Flat.dCoord m W z = 0 := by
  simp [Work.CR.Flat.dCoord, hfd]

lemma dbarCn_apply_eq_zero_of_fderiv_eq_zero {A : Cn n → Cn n →L[ℝ] Cn n} {W : Cn n → ℂ}
    {z : Cn n} (hfd : fderiv ℝ W z = 0) (m : Fin n) :
    dbarCn (JstdCn n + A) W z (Pi.single m 1) = 0 := by
  simp [dbarCn, hfd]

/-- `dbarCoord` of a compactly supported `C¹` function has compact support. -/
lemma hasCompactSupport_dbarCoord_of_hasCompactSupport {W : Cn n → ℂ}
    (hWs : HasCompactSupport W) (m : Fin n) :
    HasCompactSupport (fun z => Work.CR.Flat.dbarCoord m W z) := by
  refine hWs.mono' ?_
  intro z hz
  by_contra hzt
  exact hz (dbarCoord_eq_zero_of_fderiv_eq_zero (fderiv_eq_zero_of_notMem_tsupport hzt) m)

/-- **The Beltrami reduction.**  See the module docstring. -/
theorem exists_beltrami_reduction {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ ρ' : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ'0 : ∀ j, 0 < ρ' j) (hρ' : ∀ j, ρ' j < ρ j) : ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∀ {A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)} {ε : ℝ}, 0 ≤ ε → ε ≤ δ → (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) → ∃ c : Fin n → Fin n → (Fin n → ℂ) → ℂ, (∀ k j, ContDiff ℝ ⊤ (c k j)) ∧ (∀ k j, HasCompactSupport (c k j)) ∧ (∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) ∧ (∀ k j, Work.CR.Flat.holderNorm 0 α (c k j) Set.univ ≤ ENNReal.ofReal (C * ε)) ∧ ∀ (W : (Fin n → ℂ) → ℂ) (G : Fin n → (Fin n → ℂ) → ℂ), ContDiff ℝ 1 W → HasCompactSupport W → (∀ z, (∃ i, ρ' i ≤ ‖z i‖) → W z = 0) → (∀ m, HasCompactSupport (G m)) → (∀ m, Work.CR.Flat.holderNorm 0 α (G m) Set.univ < ⊤) → (∀ m z, Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) W z (Pi.single m 1) = G m z) → ∃ G' : Fin n → (Fin n → ℂ) → ℂ, (∀ m, Continuous (G' m)) ∧ (∀ m, HasCompactSupport (G' m)) ∧ (∀ m, Work.CR.Flat.holderNorm 0 α (G' m) Set.univ < ⊤) ∧ (∀ m z, Work.CR.Flat.dbarCoord m W z = (∑ j, c m j z * Work.CR.Flat.dCoord j W z) + G' m z) := by
  obtain ⟨η, hηpos, hη⟩ := implicit_fixpoint_eq_zero (n := n) hn hα0 hα1
  obtain ⟨CT, hCTpos, hCT⟩ := Tfun_bound (n := n) hn hα0 hα1 hρ0
  obtain ⟨Cχ, hCχpos, hCχ⟩ := exists_betaCut_small (n := n) hn hα0 hα1 hρ0 hρ'0 hρ'
  set δT : ℝ := min (1 / (2 * CT)) η with hδTdef
  have hδTpos : 0 < δT := lt_min (by positivity) hηpos
  have hδThalf : CT * δT ≤ 1 / 2 := by
    have h1 : δT ≤ 1 / (2 * CT) := min_le_left _ _
    calc CT * δT ≤ CT * (1 / (2 * CT)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hδTη : δT ≤ η := min_le_right _ _
  refine ⟨δT / Cχ, by positivity, 1, by norm_num, ?_⟩
  intro A ε hε0 hεδ hA
  obtain ⟨χ, hχ1, hχne, hχnorm⟩ := hCχ A ε hε0 hA
  have hγ : Work.CR.Flat.Cauchy.bmGamma n ≠ 0 :=
    Work.CR.Flat.Cauchy.bmGamma_ne_zero_of (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2
  set βc : Fin n → Fin n → Cn n → ℂ := fun j l z => χ z * betaCoef A j l z with hβcdef
  have hβcnorm : ∀ i j, Work.CR.Flat.holderNorm 0 α (βc i j) Set.univ ≤ ENNReal.ofReal δT := by
    intro i j
    have hle : Cχ * ε ≤ δT := by
      have h := hεδ
      rw [le_div_iff₀ hCχpos] at h
      linarith
    show Work.CR.Flat.holderNorm 0 α (fun z => χ z * betaCoef A i j z) Set.univ
      ≤ ENNReal.ofReal δT
    refine (hχnorm i j).trans ?_
    rw [ENNReal.ofReal_le_ofReal_iff hδTpos.le]
    exact hle
  have hβcsupp : ∀ i j z, βc i j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ := by
    intro i j z hz
    have hz' : χ z * betaCoef A i j z ≠ 0 := hz
    exact hχne z (fun h0 => hz' (by rw [h0, zero_mul]))
  refine ⟨fun _ _ _ => 0, fun k j => contDiff_const, fun k j => HasCompactSupport.zero, ?_, ?_, ?_⟩
  · intro k j z hz
    exact absurd rfl hz
  · intro k j
    show Work.CR.Flat.holderNorm 0 α (0 : Cn n → ℂ) Set.univ ≤ ENNReal.ofReal (1 * ε)
    rw [Work.CR.Flat.holderNorm_zero]
    exact bot_le
  · intro W G hW1 hWcs hWvan hGcs hGfin hGeq
    let u : Fin n → Cn n → ℂ := fun m z => Work.CR.Flat.dbarCoord m W z
    have huc : ∀ m, Continuous (u m) := fun m => continuous_dbarCoord_of_contDiff hW1 m
    have hucs : ∀ m, HasCompactSupport (u m) :=
      fun m => hasCompactSupport_dbarCoord_of_hasCompactSupport hWcs m
    have hstrict : ∀ {z : Cn n}, z ∉ Work.CR.Flat.polydisc 0 ρ → ∃ i, ρ' i < ‖z i‖ := by
      intro z hz
      rw [Work.CR.Flat.mem_polydisc] at hz
      simp only [Pi.zero_apply, sub_zero, not_forall, not_lt] at hz
      obtain ⟨i, hi⟩ := hz
      exact ⟨i, lt_of_lt_of_le (hρ' i) hi⟩
    have hGvan : ∀ m z, z ∉ Work.CR.Flat.polydisc 0 ρ → G m z = 0 := by
      intro m z hz
      rw [← hGeq m z]
      exact dbarCn_apply_eq_zero_of_fderiv_eq_zero
        (fderiv_eq_zero_of_vanishing hWvan z (hstrict hz)) m
    have hvec : ∀ z (j : Fin n),
        Work.CR.Flat.dbarCoord j W z
          + (∑ l, Work.CR.Flat.dbarCoord l W z * (starRingEnd ℂ (betaCoef A j l z)))
        = G j z + (∑ l, Work.CR.Flat.dCoord l W z * betaCoef A j l z) := by
      intro z j
      have h := congrFun (dbarCn_implicit_form (n := n) A W z) j
      simp only [add_apply, one_apply_eq_self, Pi.add_apply, BopBar_apply, Bop_apply] at h
      rw [hGeq j z] at h
      exact h
    have hvec' : ∀ z (j : Fin n),
        Work.CR.Flat.dbarCoord j W z
          + (∑ l, Work.CR.Flat.dbarCoord l W z * (starRingEnd ℂ (βc j l z)))
        = G j z + (∑ l, Work.CR.Flat.dCoord l W z * βc j l z) := by
      intro z j
      by_cases hz : ∀ i, ‖z i‖ ≤ ρ' i
      · have hχ1z : χ z = 1 := hχ1 z hz
        have h := hvec z j
        simpa only [hβcdef, hχ1z, one_mul] using h
      · simp only [not_forall, not_le] at hz
        obtain ⟨i, hi⟩ := hz
        have hfd : fderiv ℝ W z = 0 := fderiv_eq_zero_of_vanishing hWvan z ⟨i, hi⟩
        have hu0 : ∀ l, Work.CR.Flat.dbarCoord l W z = 0 :=
          fun l => dbarCoord_eq_zero_of_fderiv_eq_zero hfd l
        have hd0 : ∀ l, Work.CR.Flat.dCoord l W z = 0 :=
          fun l => dCoord_eq_zero_of_fderiv_eq_zero hfd l
        have hG0 : G j z = 0 := by
          rw [← hGeq j z]
          exact dbarCn_apply_eq_zero_of_fderiv_eq_zero hfd j
        simp [hu0, hd0, hG0]
    have hfix_u : ∀ j z, u j z = Tfun βc u j z + G j z := by
      intro j z
      have hv := hvec' z j
      have hd : ∀ l, Work.CR.Flat.dCoord l W z
          = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
            Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential u) z := by
        intro l
        show Work.CR.Flat.dCoord l W z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
            Work.CR.Flat.dCoord l
              (Work.CR.Flat.Cauchy.bmPotential (fun m z => Work.CR.Flat.dbarCoord m W z)) z
        rw [dCoord_bmPotential_dbarCoord (n := n) hn hW1 hWcs l z, ← mul_assoc,
          inv_mul_cancel₀ hγ, one_mul]
      have hdsum : (∑ l, Work.CR.Flat.dCoord l W z * βc j l z)
          = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
            (∑ l, βc j l z
              * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential u) z) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hd l]
        ring
      have hv'' : u j z + (∑ l, (starRingEnd ℂ (βc j l z)) * u l z)
          = G j z + (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
            (∑ l, βc j l z
              * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential u) z) := by
        have hcomm : (∑ l, (starRingEnd ℂ (βc j l z)) * Work.CR.Flat.dbarCoord l W z)
            = ∑ l, Work.CR.Flat.dbarCoord l W z * (starRingEnd ℂ (βc j l z)) :=
          Finset.sum_congr rfl fun l _ => mul_comm _ _
        have hv2 : Work.CR.Flat.dbarCoord j W z
              + (∑ l, (starRingEnd ℂ (βc j l z)) * Work.CR.Flat.dbarCoord l W z)
            = G j z + (∑ l, Work.CR.Flat.dCoord l W z * βc j l z) := by
          simpa only [hcomm] using hv
        show Work.CR.Flat.dbarCoord j W z
              + (∑ l, (starRingEnd ℂ (βc j l z)) * Work.CR.Flat.dbarCoord l W z)
            = G j z + (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
              (∑ l, βc j l z
                * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential u) z)
        rw [hv2, hdsum]
      simp only [Tfun, Pi.sub_apply, BTheta.beltramiTheta_apply, mulFam]
      have hkey : u j z = G j z + (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
            (∑ l, βc j l z
              * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential u) z)
          - (∑ l, (starRingEnd ℂ (βc j l z)) * u l z) := by
        rw [← hv'']; ring
      rw [hkey]; ring
    obtain ⟨F, hFfin, hFvan, hFeq⟩ := famNorm_contraction_fixedpoint (n := n) hα0 hα1 hρ0
      (Tfun βc) (CT * δT) (by positivity) hδThalf
      (Tfun_zero βc)
      (fun Y j z hz => Tfun_vanishes hβcsupp Y j z hz)
      (fun Y Y' hYf hYv hY'f hY'v j z =>
        Tfun_sub_apply (ρ := ρ) (τ := fun j => ρ j + 1) hn hα0 hα1 hρ0
          (fun j => by linarith [hρ0 j]) (fun j => by linarith [hρ0 j])
          hβcsupp hYf hYv hY'f hY'v j z)
      (fun Y hYf hYv => hCT βc Y δT hδTpos.le hβcnorm hβcsupp hYf hYv)
      hGvan (BTheta.famNorm_lt_top hGfin)
    have hFc : ∀ m, Continuous (F m) := fun m => continuous_of_holderNorm_zero_lt_top hα0 (hFfin m)
    have hFcs : ∀ m, HasCompactSupport (F m) :=
      fun m => BTheta.hasCompactSupport_of_vanishing_off_polydisc hn hρ0 (hFvan m)
    have hsubP : Work.CR.Flat.Cauchy.bmPotential (u - F)
        = Work.CR.Flat.Cauchy.bmPotential u - Work.CR.Flat.Cauchy.bmPotential F :=
      BTheta.bmPotential_sub_fun hn huc hucs hFc hFcs
    have hbmu : Work.CR.Flat.Cauchy.bmPotential u
        = fun z => Work.CR.Flat.Cauchy.bmGamma n * W z := by
      funext z
      show Work.CR.Flat.Cauchy.bmPotential (fun m z => Work.CR.Flat.dbarCoord m W z) z
          = Work.CR.Flat.Cauchy.bmGamma n * W z
      rw [← bmPotential_dbarCoord_eq_bmGamma_mul hn hW1 hWcs z]
    have hbmF : ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential F) :=
      contDiff_one_bmPotential_of_holder hn hα0 hα1 hFcs hFfin
    have hlin : ∀ j z, Tfun βc u j z - Tfun βc F j z = Tfun βc (u - F) j z := by
      intro j z
      have hdu : DifferentiableAt ℝ (fun z => Work.CR.Flat.Cauchy.bmPotential u z) z := by
        rw [hbmu]
        exact ((hW1.differentiable (by norm_num)).differentiableAt).const_mul _
      have hdF : DifferentiableAt ℝ (fun z => Work.CR.Flat.Cauchy.bmPotential F z) z :=
        (hbmF.differentiable (by norm_num)).differentiableAt
      have hdc : ∀ l, Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential u) z
            - Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z
          = Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential (u - F)) z := by
        intro l
        rw [hsubP]
        exact (BTheta.dCoord_sub_local l _ _ z hdu hdF).symm
      have h1 : (∑ l, βc j l z
              * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential u) z)
          - (∑ l, βc j l z
              * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z)
          = ∑ l, βc j l z
              * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential (u - F)) z := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← mul_sub, hdc l]
      have h2 : (∑ l, (starRingEnd ℂ (βc j l z)) * u l z)
          - (∑ l, (starRingEnd ℂ (βc j l z)) * F l z)
          = ∑ l, (starRingEnd ℂ (βc j l z)) * (u l z - F l z) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => by rw [mul_sub]
      simp only [Tfun, BTheta.beltramiTheta_apply, mulFam, Pi.sub_apply]
      rw [← h1, ← h2]
      ring
    let E : Fin n → Cn n → ℂ := u - F
    have hEcont : ∀ j, Continuous (E j) := fun j => (huc j).sub (hFc j)
    have hEcs : ∀ j, HasCompactSupport (E j) := fun j => (hucs j).sub (hFcs j)
    have hbmE : ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential E) := by
      show ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential (u - F))
      rw [hsubP, hbmu]
      exact (contDiff_const.mul hW1).sub hbmF
    have hEeq : ∀ j z, E j z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
            (∑ l, βc j l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential E) z)
          - (∑ l, (starRingEnd ℂ (βc j l z)) * E l z) := by
      intro j z
      have hval : E j z = Tfun βc u j z - Tfun βc F j z := by
        show u j z - F j z = Tfun βc u j z - Tfun βc F j z
        rw [hfix_u j z, hFeq j z]
        ring
      rw [hval, hlin j z]
      show Tfun βc (u - F) j z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
            (∑ l, βc j l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential E) z)
          - (∑ l, (starRingEnd ℂ (βc j l z)) * E l z)
      simp only [Tfun, BTheta.beltramiTheta_apply, mulFam]
      rfl
    have hβcη : ∀ i j, Work.CR.Flat.holderNorm 0 α (βc i j) Set.univ ≤ ENNReal.ofReal η :=
      fun i j => (hβcnorm i j).trans (ENNReal.ofReal_le_ofReal hδTη)
    have hEzero : E = 0 := hη βc E hβcη hEcont hEcs hbmE hEeq
    have huF : ∀ m z, u m z = F m z := by
      intro m z
      have h := congrFun (congrFun hEzero m) z
      exact sub_eq_zero.mp h
    refine ⟨F, hFc, hFcs, hFfin, ?_⟩
    intro m z
    rw [← huF m z]
    show Work.CR.Flat.dbarCoord m W z
      = (∑ j, (fun _ _ _ => (0 : ℂ)) m j z * Work.CR.Flat.dCoord j W z)
        + Work.CR.Flat.dbarCoord m W z
    simp

end Work.NN.Core
