import Mathlib
import Submission.Work.NN.Core.exists_beltrami_reduction
import Submission.Work.NN.Core.exists_betaCut_small
import Submission.Work.NN.Core.dbarCn_implicit_form
import Submission.Work.NN.Core.implicit_fixpoint_eq_zero
import Submission.Work.NN.Core.famNorm_contraction_fixedpoint
import Submission.Work.NN.Core.beltramiImplicit_fixedpoint
import Submission.Work.NN.Core.DbarCnPertAux

/-!
# Finiteness of the flat `∂̄`-data from the perturbed `∂̄`-data

Let `A` be a perturbation of the standard complex structure `Jstd` on `ℂⁿ = Fin n → ℂ`, small in
`C^{0,α}` on the polydisc `polydisc 0 ρ`, and let `W` be a compactly supported `C¹` function which
vanishes on the closed complement of the smaller polydisc `polydisc 0 ρ'`, `ρ' < ρ`.  The theorem
proves that the *flat* `(0,1)`-derivatives `∂̄_m W` have finite `C^{0,α}`-norm on all of `ℂⁿ` as
soon as the *perturbed* `(0,1)`-derivatives `∂̄_{Jstd + A} W` do.

The proof is the Beltrami reduction already used for `Work.NN.Core.exists_beltrami_reduction`: the
perturbed equation in implicit form `(1 + B̄(z)) ∂̄W(z) = ∂̄_{Jstd+A}W(z) + B(z) ∂W(z)`
(`Work.NN.Core.dbarCn_implicit_form`) together with the Bochner–Martinelli identity
`bmPotential (∂̄W) = γ · W` turns `u = ∂̄W` into a fixed point equation
`u = Tfun βc u + G` with a small `C^{0,α}`-coefficient family `βc`; the Banach fixed point
`famNorm_contraction_fixedpoint` produces a solution with finite `C^{0,α}`-norm on `ℂⁿ`, and
*u*niqueness of the fixed point (`implicit_fixpoint_eq_zero`, an `L²` Calderón–Zygmund argument)
identifies it with `u`.  Hence `u` itself has finite `C^{0,α}`-norm.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

namespace Work.NN.Core

variable {n : ℕ}

theorem dbarCoord_finite_of_perturbed_data {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ'0 : ∀ j, 0 < ρ' j) (hρ' : ∀ j, ρ' j < ρ j) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)} {ε : ℝ}, 0 ≤ ε → ε ≤ δ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j)
            (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) →
        ∀ W : (Fin n → ℂ) → ℂ, ContDiff ℝ 1 W → HasCompactSupport W →
          (∀ z, (∃ i, ρ' i ≤ ‖z i‖) → W z = 0) →
          (∀ m : Fin n, Work.CR.Flat.holderNorm 0 α
              (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) W z (Pi.single m 1))
              Set.univ < ⊤) →
          ∀ m : Fin n, Work.CR.Flat.holderNorm 0 α
              (fun z => Work.CR.Flat.dbarCoord m W z) Set.univ < ⊤ := by
  classical
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
  refine ⟨δT / Cχ, by positivity, ?_⟩
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
    show Work.CR.Flat.holderNorm 0 α (fun z => χ z * betaCoef A i j z) Set.univ ≤ ENNReal.ofReal δT
    refine (hχnorm i j).trans ?_
    rw [ENNReal.ofReal_le_ofReal_iff hδTpos.le]
    exact hle
  have hβcsupp : ∀ i j z, βc i j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ := by
    intro i j z hz
    have hz' : χ z * betaCoef A i j z ≠ 0 := hz
    exact hχne z (fun h0 => hz' (by rw [h0, zero_mul]))
  intro W hW1 hWcs hWvan hGfin
  let G : Fin n → Cn n → ℂ := fun m z => dbarCn (JstdCn n + A) W z (Pi.single m 1)
  have hGcs : ∀ m, HasCompactSupport (G m) := by
    intro m
    refine hWcs.mono' ?_
    intro z hz
    by_contra hzt
    exact hz (dbarCn_apply_eq_zero_of_fderiv_eq_zero
      (fderiv_eq_zero_of_notMem_tsupport hzt) m)
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
    exact dbarCn_apply_eq_zero_of_fderiv_eq_zero
      (fderiv_eq_zero_of_vanishing (ρ' := ρ') hWvan z (hstrict hz)) m
  have hGfin' : ∀ m, Work.CR.Flat.holderNorm 0 α (G m) Set.univ < ⊤ := fun m => hGfin m
  have hvec : ∀ z (j : Fin n),
      Work.CR.Flat.dbarCoord j W z
        + (∑ l, Work.CR.Flat.dbarCoord l W z * (starRingEnd ℂ (betaCoef A j l z)))
      = G j z + (∑ l, Work.CR.Flat.dCoord l W z * betaCoef A j l z) := by
    intro z j
    have h := congrFun (dbarCn_implicit_form (n := n) A W z) j
    simp only [add_apply, one_apply_eq_self, Pi.add_apply, BopBar_apply, Bop_apply] at h
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
      have hfd : fderiv ℝ W z = 0 := fderiv_eq_zero_of_vanishing (ρ' := ρ') hWvan z ⟨i, hi⟩
      have hu0 : ∀ l, Work.CR.Flat.dbarCoord l W z = 0 :=
        fun l => dbarCoord_eq_zero_of_fderiv_eq_zero hfd l
      have hd0 : ∀ l, Work.CR.Flat.dCoord l W z = 0 :=
        fun l => dCoord_eq_zero_of_fderiv_eq_zero hfd l
      have hG0 : G j z = 0 := by
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
          (∑ l, βc j l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential u) z)
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
    hGvan (BTheta.famNorm_lt_top hGfin')
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
  intro m
  have hFu : (fun z => Work.CR.Flat.dbarCoord m W z) = F m := funext fun z => huF m z
  rw [hFu]
  exact hFfin m

end Work.NN.Core
