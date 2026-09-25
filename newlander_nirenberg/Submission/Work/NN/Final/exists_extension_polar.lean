import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.exists_moment_data
import Submission.Work.NN.Final.PolarDefs
import Submission.Work.NN.Final.PolarRegions
import Submission.Work.NN.Final.PolarGlob
import Submission.Work.NN.Final.PolarChain
import Submission.Work.NN.PolarChain.one_sided_extension_finite

namespace Work.NN.Final

/-- Polar ("multi-radial") Seeley extension for the polydisc pair `pd n ρ 1 ⊂ pd n ρ 2`.
Construction (see `SESSION6_NOTES.md` and, crucially, the already-present infrastructure in
`Submission/Work/NN/Final/PolarDefs.lean`, `PolarRegions.lean`, `PolarGlob.lean`): in the log-radius
variables `u j = log (ρ j / ‖z j‖)` (positive inside `pd1`), `E v z = v z` when `u j ≥ 0` for all
`j`, and otherwise `E v z = ∑' m, a m • (∏ j, c j m z) • v (τ m z)`, where
* `τ m` reflects, in every coordinate with `u j < 0`, the log-modulus by
  `log ↦ (1 + b m) log ρ j - b m * log` (fixing the argument `z j / ‖z j‖`), and keeps the
  coordinates with `u j ≥ 0`; hence `τ m z` lies in the closed `pd1` for every `z`;
* the factor `c j m z` is `1` when `u j z ≥ 0` and `χ (b m * u j z)` when `u j z < 0`, with `χ` the
  standard bump (`seeleyCut`), `1` near `0` and flat at `0`.
The moment identities `∑' m, a m * (-(b m))^j = 1` (from `Work.NN.Final.exists_moment_data`) make
all jets match across the faces — including the corners, since the reflection acts independently in
each coordinate and `D τ m` is diagonal in the (radial, angular) basis with entries `-b m` (active
radial) and `1` (everything else).  `PolarDefs.lean` already provides `polarExtLin` together with
the agreement (`polarExtLin_of_mem`) and the dependence only on the values on `pd1`; what has to be
proved here is the `C^{k,α}` estimate on `pd n ρ 2` in terms of the norm on `pd n ρ 1` for a `v`
which is `C^k` on `pd n ρ 3`. -/
theorem exists_extension_polar {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hα0 : 0 < α) (hα1 : α < 1) : ∃ E : ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ), ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ (∀ v : (Fin n → ℂ) → ℂ, (∀ m : ℕ, ContDiffOn ℝ m v (Work.NN.Final.pd n ρ 1)) → ∀ z, z ∈ Work.NN.Final.pd n ρ 1 → E v z = v z) ∧ (∀ v w : (Fin n → ℂ) → ℂ, (∀ z, z ∈ Work.NN.Final.pd n ρ 1 → v z = w z) → E v = E w) ∧ (∀ (k : ℕ) (v : (Fin n → ℂ) → ℂ), ContDiffOn ℝ (k : WithTop ENat) v (Work.NN.Final.pd n ρ 3) → Work.CR.Flat.holderNorm k α (E v) (Work.NN.Final.pd n ρ 2) ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1)) := by
  classical
  obtain ⟨a, b, hb, hbT, ha, hsum⟩ := exists_moment_data
  obtain ⟨C, hC0, hC⟩ :=
    radialExt_holderNorm_est_stepNG (n := n) (ρ := ρ) hρ hα0 hα1 hb hbT ha hsum
  have hb1 : ∀ m : ℕ, 1 ≤ b m := fun m => le_trans (by norm_num) (hb m)
  refine ⟨polarExtension n ρ a b hρ hb1 hbT, fun k => (C k) ^ n, ?_, ?_, ?_, ?_⟩
  · intro k
    exact pow_pos (hC0 k) n
  · intro v _ z hz
    exact polarExtension_of_mem hρ hb1 hbT v hz
  · intro v w hvw
    exact polarExtension_congr hρ hb1 hbT hvw
  · intro k v hv
    rcases eq_or_ne (Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1)) ⊤ with htop | hfin
    · have hpos : ENNReal.ofReal ((C k) ^ n) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact pow_pos (hC0 k) n
      rw [htop, ENNReal.mul_top hpos]
      exact le_top
    · -- the finite case: build the honest seed on `pd n ρ 2`
      obtain ⟨Cseed, hCseed0, hCseed⟩ :=
        Work.NN.PolarChain.one_sided_extension_finite (n := n) (ρ := ρ) hρ hα0 hα1 (c := 2)
          (by norm_num)
      have hv1 : ∀ m : ℕ, m ≤ k → ContDiffOn ℝ (m : WithTop ENat) v (Work.NN.Final.pd n ρ 1) :=
        fun m hm => (hv.of_le (show ((m : WithTop ENat) ≤ (k : WithTop ENat)) by
          exact_mod_cast hm)).mono
          (pd_mono hρ (by norm_num : (1 : ℝ) ≤ 3))
      obtain ⟨w, hwsm, hweq, hwbd⟩ := hCseed k v hv1 hfin
      have hwfin : Work.CR.Flat.holderNorm k α w (Work.NN.Final.pd n ρ 2) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hwbd
      -- the closed polydisc
      have hwv : ∀ ζ : Fin n → ℂ, (∀ i, ‖ζ i‖ ≤ ρ i) → w ζ = v ζ := by
        intro ζ hζ
        have hcl : closure (Work.NN.Final.pd n ρ 1) = {z : Fin n → ℂ | ∀ i, ‖z i‖ ≤ ρ i} :=
          closure_pd n hρ
        have hcontw : ContinuousOn w (closure (Work.NN.Final.pd n ρ 1)) :=
          hwsm.continuousOn.mono (by
            intro z hz
            rw [hcl] at hz
            rw [mem_pd]
            intro i
            have := hz i
            have hp := hρ i
            nlinarith)
        have hcontv : ContinuousOn v (closure (Work.NN.Final.pd n ρ 1)) :=
          hv.continuousOn.mono (by
            intro z hz
            rw [hcl] at hz
            rw [mem_pd]
            intro i
            have := hz i
            have hp := hρ i
            nlinarith)
        have hall := Set.EqOn.of_subset_closure (s := Work.NN.Final.pd n ρ 1)
          (t := closure (Work.NN.Final.pd n ρ 1))
          (fun z hz => hweq z hz) hcontw hcontv (fun z hz => subset_closure hz) subset_rfl
        exact hall (by rw [hcl]; exact hζ)
      have hvw : ∀ ζ : Fin n → ℂ, (∀ i, ‖ζ i‖ ≤ ρ i) →
          polarReg n ρ hρ v ζ = w ζ := by
        intro ζ hζ
        rw [hwv ζ hζ]
        by_cases hmem : ζ ∈ Work.NN.Final.pd n ρ 1
        · exact polarReg_of_mem hρ v hmem
        · rw [polarReg_of_not_mem hρ v hmem]
          exact polarEval_apply_of_continuousOn hρ hζ hv.continuousOn
      have hbound := iterateFrom_polarReg_holderNorm_le (n := n) (ρ := ρ) hρ hα0 hα1 hb hbT ha
        hsum hC0 hC hv hfin hwsm hwfin hvw
      rw [polarExtension_apply, iterExt_eq_iterateFrom]
      exact hbound

end Work.NN.Final
