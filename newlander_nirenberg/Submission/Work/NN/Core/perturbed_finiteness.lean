import Mathlib
import Submission.Work.NN.Core.perturbed_aux
import Submission.Work.NN.Core.exists_beltrami_reduction
import Submission.Work.NN.Core.holderNorm_fderiv_le_dir
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.NN.Core.dbarCoord_finite_of_perturbed_data
import Submission.Work.NN.Core.iterDerivNorm_succ_le_dir
import Submission.Work.NN.Core.holderSeminorm_succ_le_dir
import Submission.Work.NN.Core.dbarCn_dirDeriv_data_finite

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff Topology
open Set

noncomputable section

variable {n : ℕ}

/-! ## Elementary facts about the perturbed `∂̄`-data -/

/-- The perturbed `(0,1)`-coefficient `∂̄_{Jstd+A}W·e_l` is continuous as soon as `A` is
continuous and `W` is `C¹`. -/
lemma continuous_dbarCn_singleCoef {A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)}
    {W : (Fin n → ℂ) → ℂ} (hA : Continuous A) (hW : ContDiff ℝ 1 W) (l : Fin n) :
    Continuous (fun z => dbarCn (JstdCn n + A) W z (Pi.single l (1 : ℂ))) := by
  have hfd : Continuous (fun z => fderiv ℝ W z) := hW.continuous_fderiv (by norm_num)
  have hJ : Continuous (fun z => (JstdCn n + A) z (Pi.single l (1 : ℂ))) := by
    have h2 : Continuous (fun z => A z (Pi.single l (1 : ℂ))) := hA.clm_apply continuous_const
    have h1 : Continuous (fun z => (JstdCn n) z (Pi.single l (1 : ℂ))) := by
      simp only [JstdCn_apply]; exact continuous_const
    rw [show (fun z => (JstdCn n + A) z (Pi.single l (1 : ℂ)))
        = fun z => (JstdCn n) z (Pi.single l (1 : ℂ)) + A z (Pi.single l (1 : ℂ)) from by
      funext z; simp only [add_apply, Pi.add_apply]]
    exact h1.add h2
  rw [show (fun z => dbarCn (JstdCn n + A) W z (Pi.single l (1 : ℂ)))
      = fun z => (1 / 2 : ℂ) * (fderiv ℝ W z (Pi.single l (1 : ℂ))
          + Complex.I * fderiv ℝ W z ((JstdCn n + A) z (Pi.single l (1 : ℂ)))) from
    funext (fun z => dbarCn_apply _ _ _ _)]
  exact continuous_const.mul ((hfd.clm_apply continuous_const).add
    (continuous_const.mul (hfd.clm_apply hJ)))

/-- The `(0,1)`-coefficient `∂̄_l W` is continuous for `W` of class `C¹`. -/
lemma continuous_dbarCoord_of_contDiff_one {W : (Fin n → ℂ) → ℂ} (hW : ContDiff ℝ 1 W) (l : Fin n) :
    Continuous (fun z => Work.CR.Flat.dbarCoord l W z) := by
  have hfd : Continuous (fun z => fderiv ℝ W z) := hW.continuous_fderiv (by norm_num)
  rw [show (fun z => Work.CR.Flat.dbarCoord l W z) = fun z => (1 / 2 : ℂ) *
      (fderiv ℝ W z (Pi.single l (1 : ℂ)) + Complex.I * fderiv ℝ W z (Pi.single l Complex.I)) from
    funext (fun z => rfl)]
  exact continuous_const.mul ((hfd.clm_apply continuous_const).add
    (continuous_const.mul (hfd.clm_apply continuous_const)))

/-- The perturbed `(0,1)`-data of a function vanishing off `polydisc 0 ρ'` vanishes on the closed
complement of that polydisc. -/
lemma dbarCn_singleCoef_eq_zero_of_vanishing {A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)}
    {W : (Fin n → ℂ) → ℂ} {ρ' : Fin n → ℝ} (hA : Continuous A) (hW : ContDiff ℝ 1 W)
    (hvan : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → W z = 0) (l : Fin n) :
    ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → dbarCn (JstdCn n + A) W z (Pi.single l (1 : ℂ)) = 0 := by
  refine eq_zero_of_cont_of_vanishing (continuous_dbarCn_singleCoef hA hW l) ?_
  intro z hz
  obtain ⟨i, hi⟩ := hz
  have hopen : IsOpen {w : Fin n → ℂ | ρ' i < ‖w i‖} :=
    isOpen_lt continuous_const ((continuous_apply i).norm)
  have hev : W =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hi] with w hw
    exact hvan w ⟨i, le_of_lt hw⟩
  have hfd : fderiv ℝ W z = 0 := by
    rw [hev.fderiv_eq]; simp
  exact dbarCn_apply_eq_zero_of_fderiv_eq_zero hfd l

/-- The flat `(0,1)`-coefficient `∂̄_l W` of a function vanishing off `polydisc 0 ρ'` vanishes on
the closed complement of that polydisc. -/
lemma dbarCoord_eq_zero_of_vanishing_closed {W : (Fin n → ℂ) → ℂ} {ρ' : Fin n → ℝ}
    (hW : ContDiff ℝ 1 W) (hvan : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → W z = 0) (l : Fin n) :
    ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → Work.CR.Flat.dbarCoord l W z = 0 := by
  refine eq_zero_of_cont_of_vanishing (continuous_dbarCoord_of_contDiff_one hW l) ?_
  intro z hz
  obtain ⟨i, hi⟩ := hz
  have hopen : IsOpen {w : Fin n → ℂ | ρ' i < ‖w i‖} :=
    isOpen_lt continuous_const ((continuous_apply i).norm)
  have hev : W =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hi] with w hw
    exact hvan w ⟨i, le_of_lt hw⟩
  have hfd : fderiv ℝ W z = 0 := by
    rw [hev.fderiv_eq]; simp
  exact dbarCoord_eq_zero_of_fderiv_eq_zero hfd l

/-- The derivative of a `C^{m+1}` function vanishing on the closed complement of `polydisc 0 ρ'`
vanishes there. -/
lemma fderiv_eq_zero_of_vanishing_closed {ρ' : Fin n → ℝ} {m : ℕ} {W : (Fin n → ℂ) → ℂ}
    (hρ'0 : ∀ j, 0 < ρ' j) (hW : ContDiff ℝ (m + 1) W)
    (hvan : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → W z = 0) :
    ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → fderiv ℝ W z = 0 := by
  intro z hz
  have h1 : iteratedFDeriv ℝ 1 W z = 0 :=
    iteratedFDeriv_eq_zero_of_vanishing_closedComplement (ρ := ρ') hρ'0 (m := m + 1) hW hvan 1
      (by omega) z hz
  ext u
  have h2 := iteratedFDeriv_one_apply (𝕜 := ℝ) (f := W) (x := z) (fun _ : Fin 1 => u)
  rw [h1] at h2
  simpa using h2.symm

/-- Splitting off the top term of the `C^{k,α}` norm. -/
lemma holderNorm_succ_decomp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ℕ) (α : ℝ) (f : X → ℂ) (Ω : Set X) :
    Work.CR.Flat.holderNorm (k + 1) α f Ω
      = Work.CR.Flat.holderNorm k α f Ω
        + (Work.CR.Flat.iterDerivNorm (k + 1) f Ω + Work.CR.Flat.holderSeminorm (k + 1) α f Ω) := by
  simp only [Work.CR.Flat.holderNorm]
  rw [Finset.sum_range_succ]

/-! ## The base case of the induction: `C^{0,α}` data give a `C^{1,α}` function -/

private theorem base_one_lt_top (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ'0 : ∀ j, 0 < ρ' j) (hρ' : ∀ j, ρ' j < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)},
      (∀ q : ℕ, ContDiff ℝ q A) → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε₀ →
      (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j)
          (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) →
      ∀ W : (Fin n → ℂ) → ℂ, (∀ z, (∃ i, ρ' i ≤ ‖z i‖) → W z = 0) →
        ContDiff ℝ 1 W →
        (∀ l : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => dbarCn (JstdCn n + A) W z (Pi.single l 1)) (Work.CR.Flat.polydisc 0 ρ') < ⊤) →
        Work.CR.Flat.holderNorm 1 α W (Work.CR.Flat.polydisc 0 ρ') < ⊤ := by
  obtain ⟨δ, hδpos, hmain⟩ := dbarCoord_finite_of_perturbed_data (n := n) hn hα0 hα1 hρ0 hρ'0 hρ'
  refine ⟨δ, hδpos, ?_⟩
  intro A hA ε hε0 hεδ hsmall W hvan hW1 hdata
  have hcs : HasCompactSupport W := hasCompactSupport_of_vanishing hvan
  have hAcont : Continuous A := (hA 0).continuous
  have hDuni : ∀ l : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => dbarCn (JstdCn n + A) W z (Pi.single l 1)) Set.univ < ⊤ := by
    intro l
    have hvan' := dbarCn_singleCoef_eq_zero_of_vanishing (ρ' := ρ') hAcont hW1 hvan l
    have hcont := continuous_dbarCn_singleCoef (n := n) hAcont hW1 l
    have hle := Work.NN.Core.holderNorm_univ_le_holderNorm_polydisc_of_contDiff_vanishing
      (n := n) (α := α) hα0 hρ'0 (m := 0) (g := fun z => dbarCn (JstdCn n + A) W z (Pi.single l 1))
      (contDiff_zero.mpr hcont) hvan'
    exact lt_of_le_of_lt hle (hdata l)
  have hflat : ∀ l : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => Work.CR.Flat.dbarCoord l W z) Set.univ < ⊤ :=
    hmain hε0 hεδ hsmall W hW1 hcs hvan hDuni
  have hfldcont : ∀ l : Fin n, Continuous (fun z => Work.CR.Flat.dbarCoord l W z) :=
    fun l => continuous_dbarCoord_of_contDiff_one hW1 l
  have hfldcs : ∀ l : Fin n, HasCompactSupport (fun z => Work.CR.Flat.dbarCoord l W z) :=
    fun l => hasCompactSupport_dbarCoord_of_hasCompactSupport hcs l
  have hfldvan : ∀ l : Fin n, ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → Work.CR.Flat.dbarCoord l W z = 0 :=
    fun l => dbarCoord_eq_zero_of_vanishing_closed hW1 hvan l
  obtain ⟨Cp, hCppos, hpot⟩ := bmPotential_gain (n := n) hn hα0 hα1 hρ'0 0
  have hpotfin : Work.CR.Flat.holderNorm 1 α
      (Work.CR.Flat.Cauchy.bmPotential (fun l z => Work.CR.Flat.dbarCoord l W z))
      (Work.CR.Flat.polydisc 0 ρ') < ⊤ := by
    refine lt_of_le_of_lt (hpot (fun l z => Work.CR.Flat.dbarCoord l W z)
      (fun l => contDiff_zero.mpr (hfldcont l)) hfldcs hflat hfldvan).2 ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr (fun l _ => hflat l))
  have hγ : Work.CR.Flat.Cauchy.bmGamma n ≠ 0 :=
    Work.CR.Flat.Cauchy.bmGamma_ne_zero_of (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2
  have hEqOn : ∀ z ∈ Work.CR.Flat.polydisc 0 ρ',
      W z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
        Work.CR.Flat.Cauchy.bmPotential (fun l y => Work.CR.Flat.dbarCoord l W y) z := by
    intro z _
    have h := bmPotential_dbarCoord_eq_bmGamma_mul (n := n) hn hW1 hcs z
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hγ, one_mul]
  calc Work.CR.Flat.holderNorm 1 α W (Work.CR.Flat.polydisc 0 ρ')
      = Work.CR.Flat.holderNorm 1 α (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
          Work.CR.Flat.Cauchy.bmPotential (fun l y => Work.CR.Flat.dbarCoord l W y) z)
          (Work.CR.Flat.polydisc 0 ρ') := holderNorm_congr_eqOn hEqOn
    _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ *
          Work.CR.Flat.holderNorm 1 α
            (Work.CR.Flat.Cauchy.bmPotential (fun l y => Work.CR.Flat.dbarCoord l W y))
            (Work.CR.Flat.polydisc 0 ρ') :=
        holderNorm_const_mul_le ((Work.CR.Flat.isOpen_polydisc 0 ρ').uniqueDiffOn) _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpotfin

/-! ## The induction -/

private theorem finiteness_level (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ'0 : ∀ j, 0 < ρ' j) (hρ' : ∀ j, ρ' j < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (m : ℕ) {A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)},
      (∀ q : ℕ, ContDiff ℝ q A) → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε₀ →
      (∀ i j : Fin n, Work.CR.Flat.holderNorm m α (fun z => A z (Pi.single i 1) j)
          (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) →
      ∀ W : (Fin n → ℂ) → ℂ, (∀ z, (∃ i, ρ' i ≤ ‖z i‖) → W z = 0) →
        ContDiff ℝ (m + 1) W →
        (∀ l : Fin n, Work.CR.Flat.holderNorm m α
            (fun z => dbarCn (JstdCn n + A) W z (Pi.single l 1)) (Work.CR.Flat.polydisc 0 ρ') < ⊤) →
        Work.CR.Flat.holderNorm (m + 1) α W (Work.CR.Flat.polydisc 0 ρ') < ⊤ := by
  obtain ⟨ε₀, hε₀pos, hbase⟩ := base_one_lt_top (n := n) hn hα0 hα1 hρ0 hρ'0 hρ'
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro m
  induction m with
  | zero =>
      intro A hA ε hε0 hεε hsmall W hvan hW hdata
      exact hbase hA hε0 hεε hsmall W hvan hW hdata
  | succ m ih =>
      intro A hA ε hε0 hεε hsmall W hvan hW hdata
      have hΩ : IsOpen (Work.CR.Flat.polydisc 0 ρ') := Work.CR.Flat.isOpen_polydisc 0 ρ'
      have hsmallm : ∀ i j : Fin n, Work.CR.Flat.holderNorm m α
          (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε :=
        fun i j => (Work.CR.Flat.holderNorm_mono_k (Nat.le_succ m) α _ _).trans (hsmall i j)
      have hdatam : ∀ l : Fin n, Work.CR.Flat.holderNorm m α
          (fun z => dbarCn (JstdCn n + A) W z (Pi.single l 1)) (Work.CR.Flat.polydisc 0 ρ') < ⊤ :=
        fun l => lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_k (Nat.le_succ m) α _ _) (hdata l)
      have hWm1 : ContDiff ℝ (m + 1) W := hW.of_le (by simp)
      have hWfin : Work.CR.Flat.holderNorm (m + 1) α W (Work.CR.Flat.polydisc 0 ρ') < ⊤ :=
        ih hA hε0 hεε hsmallm W hvan hWm1 hdatam
      have hstep : ∀ p : Fin n × Bool, Work.CR.Flat.holderNorm (m + 1) α
          (fun z => fderiv ℝ W z (if p.2 then Pi.single p.1 Complex.I else Pi.single p.1 (1 : ℂ)))
          (Work.CR.Flat.polydisc 0 ρ') < ⊤ := by
        intro p
        have hsm1 : ContDiff ℝ (m + 1) (fderiv ℝ W) :=
          hW.fderiv_right (by rw [← Nat.cast_one, ← Nat.cast_add])
        have hb : ContDiff ℝ (m + 1) (fun z => fderiv ℝ W z
            (if p.2 then Pi.single p.1 Complex.I else Pi.single p.1 (1 : ℂ))) :=
          hsm1.clm_apply contDiff_const
        have hvanb : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) →
            (fun y => fderiv ℝ W y (if p.2 then Pi.single p.1 Complex.I
              else Pi.single p.1 (1 : ℂ))) z = 0 := by
          intro z hz
          have hfd : fderiv ℝ W z = 0 :=
            fderiv_eq_zero_of_vanishing_closed (ρ' := ρ') (m := m + 1) hρ'0 hW hvan z hz
          show (fderiv ℝ W z) _ = 0
          rw [hfd]; simp
        have hdatab : ∀ l : Fin n, Work.CR.Flat.holderNorm m α
            (fun z => dbarCn (JstdCn n + A) (fun y => fderiv ℝ W y
              (if p.2 then Pi.single p.1 Complex.I else Pi.single p.1 (1 : ℂ))) z
              (Pi.single l 1)) (Work.CR.Flat.polydisc 0 ρ') < ⊤ :=
          fun l => dbarCn_dirDeriv_data_finite (n := n) (m := m) (α := α) (ρ' := ρ') hα0 hα1
            (A := A) hA (W := W) hW hdata hWfin _ l
        exact ih hA hε0 hεε hsmallm _ hvanb hb hdatab
      have hsplit : Work.CR.Flat.holderNorm (m + 2) α W (Work.CR.Flat.polydisc 0 ρ')
          = Work.CR.Flat.holderNorm (m + 1) α W (Work.CR.Flat.polydisc 0 ρ')
            + (Work.CR.Flat.iterDerivNorm (m + 2) W (Work.CR.Flat.polydisc 0 ρ')
              + Work.CR.Flat.holderSeminorm (m + 2) α W (Work.CR.Flat.polydisc 0 ρ')) :=
        holderNorm_succ_decomp (m + 1) α W _
      rw [hsplit]
      refine ENNReal.add_lt_top.mpr ⟨hWfin, ?_⟩
      refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
      · refine lt_of_le_of_lt (iterDerivNorm_succ_le_dir (n := n) (k := m + 1) hΩ ?_)
          (ENNReal.sum_lt_top.mpr (fun p _ => ?_))
        · have := hW.contDiffOn (s := Work.CR.Flat.polydisc 0 ρ')
          simpa only [Nat.cast_add, Nat.cast_one] using this
        · exact lt_of_le_of_lt
            (Work.CR.Flat.iterDerivNorm_le_holderNorm (m + 1) α _ _ le_rfl) (hstep p)
      · refine lt_of_le_of_lt (holderSeminorm_succ_le_dir (n := n) (k := m + 1) (α := α) hΩ ?_)
          (ENNReal.sum_lt_top.mpr (fun p _ => ?_))
        · have := hW.contDiffOn (s := Work.CR.Flat.polydisc 0 ρ')
          simpa only [Nat.cast_add, Nat.cast_one] using this
        · exact lt_of_le_of_lt
            (Work.CR.Flat.holderSeminorm_le_holderNorm (m + 1) α _ _ le_rfl) (hstep p)

end

theorem perturbed_finiteness {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ ρ' : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ'0 : ∀ j, 0 < ρ' j) (hρ' : ∀ j, ρ' j < ρ j) (k : ℕ) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)}, (∀ m : ℕ, ContDiff ℝ m A) → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε₀ → (∀ i j : Fin n, Work.CR.Flat.holderNorm (k+1) α (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) → (∀ z v : (Fin n → ℂ), (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) → ∀ v : (Fin n → ℂ) → ℂ, (∀ z, (∃ i, ρ' i ≤ ‖z i‖) → v z = 0) → ContDiffOn ℝ (((k+1 : ℕ)) : WithTop ENat) v (Work.CR.Flat.polydisc 0 ρ) → (∑ j : Fin n, Work.CR.Flat.holderNorm k α (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) v z (Pi.single j 1)) (Work.CR.Flat.polydisc 0 ρ')) < ⊤ → Work.CR.Flat.holderNorm (k+1) α v (Work.CR.Flat.polydisc 0 ρ') < ⊤ := by
  obtain ⟨ε₀, hε₀pos, hlev⟩ := finiteness_level (n := n) hn hα0 hα1 hρ0 hρ'0 hρ'
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro A hA ε hε0 hεε hsmall _hJ v hvan hvC hdata
  have hvglob : ContDiff ℝ (k + 1) v := contDiff_of_contDiffOn_of_vanishing hρ' hvC hvan
  have hsmallk : ∀ i j : Fin n, Work.CR.Flat.holderNorm k α (fun z => A z (Pi.single i 1) j)
      (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε :=
    fun i j => (Work.CR.Flat.holderNorm_mono_k (Nat.le_succ k) α _ _).trans (hsmall i j)
  have hdatak : ∀ l : Fin n, Work.CR.Flat.holderNorm k α
      (fun z => dbarCn (JstdCn n + A) v z (Pi.single l 1)) (Work.CR.Flat.polydisc 0 ρ') < ⊤ := by
    intro l
    have hle : Work.CR.Flat.holderNorm k α
        (fun z => dbarCn (JstdCn n + A) v z (Pi.single l 1)) (Work.CR.Flat.polydisc 0 ρ')
        ≤ ∑ j : Fin n, Work.CR.Flat.holderNorm k α
          (fun z => dbarCn (JstdCn n + A) v z (Pi.single j 1)) (Work.CR.Flat.polydisc 0 ρ') := by
      simpa using Finset.single_le_sum
        (f := fun j : Fin n => Work.CR.Flat.holderNorm k α
          (fun z => dbarCn (JstdCn n + A) v z (Pi.single j 1)) (Work.CR.Flat.polydisc 0 ρ'))
        (fun i _ => bot_le) (Finset.mem_univ l)
    exact lt_of_le_of_lt hle hdata
  exact hlev k hA hε0 hεε hsmallk v hvan hvglob hdatak

end Work.NN.Core
