import Mathlib
import Submission.Work.CR.Flat.Polydisc.dbarCoord_add
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm
import Submission.Work.NN.Core.telescopeTwo
import Submission.Work.NN.Core.fiberPot_dbarCoord
import Submission.Work.NN.Core.fiberPot_dbarCoord_self
import Submission.Work.NN.Core.contDiff_fiberPot
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace Work.NN.Final

variable {n : ℕ}

/-! ## Tracking regions and fibre cylinders -/

/-- The `m`-th tracking radius in coordinate `k`: the first `m` coordinates are tracked in the
`R`-disc, the remaining ones in the `R'`-disc. -/
def telRegB (R R' : ℝ) (m : ℕ) (k : Fin n) : ℝ := if (k : ℕ) < m then R else R'

/-- The `m`-th tracking region: `z` with `‖z k‖ < telRegB R R' m k` for all `k`. -/
def telReg (R R' : ℝ) (m : ℕ) : Set (Work.NN.Core.Cn n) :=
  {z | ∀ k, ‖z k‖ < telRegB R R' m k}

/-- The `j`-fibre cylinder: the `j`-th coordinate varies in the closed ball of radius `R`, the
other coordinates within `ρ` of `z`. -/
def telCyl (R ρ : ℝ) (j : Fin n) (z : Work.NN.Core.Cn n) : Set (Work.NN.Core.Cn n) :=
  {y | ∀ k : Fin n, y k ∈ Metric.closedBall (Function.update z j 0 k)
        (if k = j then R else ρ)}

@[simp] lemma mem_telReg {R R' : ℝ} {m : ℕ} {z : Work.NN.Core.Cn n} :
    z ∈ telReg R R' m ↔ ∀ k, ‖z k‖ < telRegB R R' m k := Iff.rfl

lemma telRegB_zero (R R' : ℝ) (k : Fin n) : telRegB R R' 0 k = R' := by
  simp [telRegB]

lemma telRegB_self (R R' : ℝ) (k : Fin n) : telRegB R R' n k = R := by
  simp [telRegB, k.isLt]

lemma telRegB_le {R R' : ℝ} (hRR' : R ≤ R') (m : ℕ) (k : Fin n) :
    telRegB R R' m k ≤ R' := by
  unfold telRegB
  split <;> linarith

lemma telRegB_mono {R R' : ℝ} (hRR' : R ≤ R') {m m' : ℕ} (h : m ≤ m') (k : Fin n) :
    telRegB R R' m' k ≤ telRegB R R' m k := by
  unfold telRegB
  by_cases h1 : (k : ℕ) < m
  · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 h)]
  · rw [if_neg h1]
    by_cases h2 : (k : ℕ) < m'
    · rw [if_pos h2]; exact hRR'
    · rw [if_neg h2]

lemma telReg_mono {R R' : ℝ} (hRR' : R ≤ R') {m m' : ℕ} (h : m ≤ m') :
    telReg (n := n) R R' m' ⊆ telReg (n := n) R R' m :=
  fun z hz k => lt_of_lt_of_le (hz k) (telRegB_mono hRR' h k)

lemma telReg_zero (R R' : ℝ) : telReg R R' 0 = Work.CR.Flat.polydisc 0 (fun _ : Fin n => R') := by
  ext z; simp only [mem_telReg, Work.CR.Flat.mem_polydisc, telRegB_zero, Pi.zero_apply,
    sub_zero]

lemma telReg_n (R R' : ℝ) : telReg R R' n = Work.CR.Flat.polydisc 0 (fun _ : Fin n => R) := by
  ext z; simp only [mem_telReg, Work.CR.Flat.mem_polydisc, telRegB_self, Pi.zero_apply, sub_zero]

lemma telReg_subset_polydisc {R R' : ℝ} (hRR' : R ≤ R') (m : ℕ) :
    telReg R R' m ⊆ Work.CR.Flat.polydisc 0 (fun _ : Fin n => R') := by
  intro z hz k
  simpa using lt_of_lt_of_le (hz k) (telRegB_le hRR' m k)

lemma isOpen_telReg (R R' : ℝ) (m : ℕ) : IsOpen (telReg (n := n) R R' m) := by
  have h : telReg (n := n) R R' m = ⋂ k, {z : Work.NN.Core.Cn n | ‖z k‖ < telRegB R R' m k} := by
    ext z; simp [telReg]
  rw [h]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_lt ((continuous_apply k).norm) continuous_const

@[simp] lemma mem_telCyl {R ρ : ℝ} {j : Fin n} {z y : Work.NN.Core.Cn n} :
    y ∈ telCyl R ρ j z ↔ ‖y j‖ ≤ R ∧ ∀ k, k ≠ j → ‖y k - z k‖ ≤ ρ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h j
      simpa [telCyl, Function.update_self, dist_eq_norm] using this
    · intro k hk
      have := h k
      rw [Function.update_of_ne hk, ite_eq_right hk] at this
      simpa [dist_eq_norm] using this
  · rintro ⟨h1, h2⟩ k
    by_cases hk : k = j
    · subst hk; simpa [telCyl, Function.update_self, dist_eq_norm] using h1
    · have := h2 k hk
      rw [ite_eq_right hk]
      simpa [telCyl, Function.update_of_ne hk, dist_eq_norm, sub_eq_add_neg] using this

lemma isCompact_telCyl (R ρ : ℝ) (j : Fin n) (z : Work.NN.Core.Cn n) :
    IsCompact (telCyl R ρ j z) := by
  have h : telCyl R ρ j z = {y | ∀ k : Fin n, y k ∈
      Metric.closedBall (Function.update z j 0 k) (if k = j then R else ρ)} := rfl
  rw [h]
  exact isCompact_pi_infinite fun k => isCompact_closedBall _ _

/-! ## Bump extension of data that is locally smooth -/

/-- If `χ` is smooth with `tsupport χ ⊆ V` (`V` open) and `g` is `C^k` on `V`, then `χ * g` is
globally `C^k` (the product is `0` off the support of `χ`). -/
lemma contDiff_mul_of_contDiffOn {k : ℕ} {χ g : Work.NN.Core.Cn n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    {V : Set (Work.NN.Core.Cn n)} (hV : IsOpen V) (hts : tsupport χ ⊆ V)
    (hg : ContDiffOn ℝ k g V) : ContDiff ℝ k (fun y => χ y * g y) := by
  rw [← contDiffOn_univ]
  refine contDiffOn_of_locally_contDiffOn (fun x _ => ?_)
  by_cases hx : x ∈ V
  · exact ⟨V, hV, hx, by rw [Set.univ_inter]; exact ((hχ.contDiffOn).of_le (by simp)).mul hg⟩
  · refine ⟨(tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl, fun h => hx (hts h), ?_⟩
    rw [Set.univ_inter]
    refine ContDiffOn.congr (contDiffOn_const (c := (0 : ℂ))) (fun y hy => ?_)
    have hy' : y ∉ tsupport χ := hy
    have h0 : χ y = 0 := by
      by_contra h
      exact hy' (subset_tsupport χ (Function.mem_support.mpr h))
    rw [h0, zero_mul]

/-- Extension of data that is `C^k` on an open set containing the cylinder. -/
lemma exists_contDiff_ext_of_telCyl {k : ℕ} {R ρ : ℝ} {j : Fin n} {z : Work.NN.Core.Cn n}
    {V : Set (Work.NN.Core.Cn n)} (hV : IsOpen V) (hCV : telCyl R ρ j z ⊆ V)
    {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiffOn ℝ k u V) :
    ∃ ũ : Work.NN.Core.Cn n → ℂ, ContDiff ℝ k ũ ∧
      ∀ y ∈ telCyl R ρ j z, ũ y = u y := by
  obtain ⟨χ, W, hχ, _hcs, hts, _hWo, hCW, hχW⟩ :=
    Work.NN.Core.exists_contDiff_bump_of_isCompact_subset (K := telCyl R ρ j z) (U := V)
      (isCompact_telCyl R ρ j z) hV hCV
  exact ⟨fun y => χ y * u y, contDiff_mul_of_contDiffOn hχ hV hts hu,
    fun y hy => by simp only [hχW y (hCW hy), one_mul]⟩

/-! ## Local fibre-potential lemmas -/

/-- A point of a smaller cylinder is an interior point of a bigger one. -/
lemma telCyl_mem_nhds {R ρ R' ρ' : ℝ} (hR : R' < R) (hρ : ρ' < ρ)
    {j : Fin n} {z y : Work.NN.Core.Cn n} (hy : y ∈ telCyl R' ρ' j z) :
    telCyl R ρ j z ∈ 𝓝 y := by
  rw [Metric.mem_nhds_iff]
  refine ⟨min ((R - R') / 2) ((ρ - ρ') / 2), lt_min (by linarith) (by linarith), ?_⟩
  intro y' hy'
  rw [Metric.mem_ball, dist_eq_norm] at hy'
  rw [mem_telCyl] at hy ⊢
  obtain ⟨hy1, hy2⟩ := hy
  have hεR : ‖y' - y‖ < (R - R') / 2 := lt_of_lt_of_le hy' (min_le_left _ _)
  have hερ : ‖y' - y‖ < (ρ - ρ') / 2 := lt_of_lt_of_le hy' (min_le_right _ _)
  constructor
  · have h1 : ‖y' j - y j‖ ≤ ‖y' - y‖ := by simpa using norm_le_pi_norm (y' - y) j
    have h2 : ‖y' j‖ ≤ ‖y' j - y j‖ + ‖y j‖ := by
      calc ‖y' j‖ = ‖(y' j - y j) + y j‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  · intro k hk
    have h1 : ‖y' k - y k‖ ≤ ‖y' - y‖ := by simpa using norm_le_pi_norm (y' - y) k
    have h2 : ‖y' k - z k‖ ≤ ‖y' k - y k‖ + ‖y k - z k‖ := by
      calc ‖y' k - z k‖ = ‖(y' k - y k) + (y k - z k)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith [hy2 k hk]

/-- If the data agree on a cylinder then the fibre potentials agree on the corresponding ball. -/
lemma fiberPot_congr_of_telCyl {R ρ : ℝ} (hρ : 0 < ρ) {j : Fin n} {z : Work.NN.Core.Cn n}
    {u ũ : Work.NN.Core.Cn n → ℂ} (h : ∀ y ∈ telCyl R (2 * ρ) j z, u y = ũ y) :
    ∀ y ∈ Metric.ball z ρ,
      Work.NN.Core.fiberPot R j u y = Work.NN.Core.fiberPot R j ũ y := by
  intro y hy
  rw [Work.NN.Core.fiberPot_apply, Work.NN.Core.fiberPot_apply]
  congr 1
  refine setIntegral_congr_fun measurableSet_ball (fun w hw => ?_)
  have hw' : ‖w‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hw
  have hy' : ‖y - z‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hy
  have hmem : Function.update y j w ∈ telCyl R (2 * ρ) j z := by
    rw [mem_telCyl]
    refine ⟨?_, ?_⟩
    · rw [Function.update_self]; exact le_of_lt hw'
    · intro k hk
      rw [Function.update_of_ne hk]
      calc ‖y k - z k‖ ≤ ‖y - z‖ := by simpa using norm_le_pi_norm (y - z) k
        _ ≤ 2 * ρ := by linarith
  rw [h _ hmem]

/-- Fibre potentials of data vanishing on the cylinder vanish on the ball. -/
lemma fiberPot_eq_zero_of_telCyl {R ρ : ℝ} (hρ : 0 < ρ) {j : Fin n} {z : Work.NN.Core.Cn n}
    {u : Work.NN.Core.Cn n → ℂ} (h : ∀ y ∈ telCyl R (2 * ρ) j z, u y = 0) :
    ∀ y ∈ Metric.ball z ρ, Work.NN.Core.fiberPot R j u y = 0 := by
  intro y hy
  exact (fiberPot_congr_of_telCyl (R := R) (ρ := ρ) hρ (j := j) (z := z) (u := u)
    (ũ := fun _ => (0 : ℂ)) (fun y' hy' => by rw [h y' hy']) y hy).trans (by simp)

/-- **Local self-inverse of the fibre potential.** -/
lemma dbarCoord_fiberPot_self_of_telCyl {R ρ : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    {j : Fin n} {z : Work.NN.Core.Cn n} {u ũ : Work.NN.Core.Cn n → ℂ}
    (hũ : ContDiff ℝ 1 ũ) (h : ∀ y ∈ telCyl R (2 * ρ) j z, u y = ũ y) (hz : ‖z j‖ < R) :
    Work.CR.Flat.dbarCoord j (Work.NN.Core.fiberPot R j u) z = u z := by
  have heq : Work.NN.Core.fiberPot R j u =ᶠ[𝓝 z] Work.NN.Core.fiberPot R j ũ := by
    filter_upwards [Metric.ball_mem_nhds z hρ] with y hy
    exact fiberPot_congr_of_telCyl hρ h y hy
  have hfd : fderiv ℝ (Work.NN.Core.fiberPot R j u) z
      = fderiv ℝ (Work.NN.Core.fiberPot R j ũ) z := heq.fderiv_eq
  have hL : Work.CR.Flat.dbarCoord j (Work.NN.Core.fiberPot R j u) z
      = Work.CR.Flat.dbarCoord j (Work.NN.Core.fiberPot R j ũ) z := by
    rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, hfd]
  rw [hL, Work.NN.Core.fiberPot_dbarCoord_self R hR j hũ hz]
  exact (h z (by rw [mem_telCyl]; exact ⟨le_of_lt hz, fun k _ => by
    simp only [sub_self, norm_zero]; positivity⟩)).symm

/-- **Local commutation of the fibre potential with the other `∂̄`s.** -/
lemma dbarCoord_fiberPot_of_telCyl {R ρ : ℝ} (hρ : 0 < ρ) {j k : Fin n} (hkj : k ≠ j)
    {z : Work.NN.Core.Cn n} {u ũ : Work.NN.Core.Cn n → ℂ} (hũ : ContDiff ℝ 1 ũ)
    (h : ∀ y ∈ telCyl R (2 * ρ) j z, u y = ũ y)
    (hdiff : DifferentiableAt ℝ (Work.NN.Core.fiberPot R j u) z) :
    Work.CR.Flat.dbarCoord k (Work.NN.Core.fiberPot R j u) z
      = Work.NN.Core.fiberPot R j (Work.CR.Flat.dbarCoord k u) z := by
  have heq : Work.NN.Core.fiberPot R j u =ᶠ[𝓝 z] Work.NN.Core.fiberPot R j ũ := by
    filter_upwards [Metric.ball_mem_nhds z hρ] with y hy
    exact fiberPot_congr_of_telCyl hρ h y hy
  have hfd : fderiv ℝ (Work.NN.Core.fiberPot R j u) z
      = fderiv ℝ (Work.NN.Core.fiberPot R j ũ) z := heq.fderiv_eq
  have hdiff' : DifferentiableAt ℝ (Work.NN.Core.fiberPot R j ũ) z :=
    (heq.differentiableAt_iff).mp hdiff
  have hL : Work.CR.Flat.dbarCoord k (Work.NN.Core.fiberPot R j u) z
      = Work.CR.Flat.dbarCoord k (Work.NN.Core.fiberPot R j ũ) z := by
    rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, hfd]
  rw [hL, Work.NN.Core.fiberPot_dbarCoord R j hkj hũ z hdiff']
  have hkey : ∀ w : ℂ, ‖w‖ < R →
      Work.CR.Flat.dbarCoord k u (Function.update z j w)
        = Work.CR.Flat.dbarCoord k ũ (Function.update z j w) := by
    intro w hw
    have hy : Function.update z j w ∈ telCyl (‖w‖) ρ j z := by
      rw [mem_telCyl]
      refine ⟨by rw [Function.update_self], fun k' hk' => ?_⟩
      rw [Function.update_of_ne hk', sub_self, norm_zero]; exact le_of_lt hρ
    have hnhds : telCyl R (2 * ρ) j z ∈ 𝓝 (Function.update z j w) :=
      telCyl_mem_nhds (R' := ‖w‖) (ρ' := ρ) (by linarith) (by linarith) hy
    have hev : u =ᶠ[𝓝 (Function.update z j w)] ũ := by
      filter_upwards [hnhds] with y' hy'
      exact h y' hy'
    rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, hev.fderiv_eq]
  have hcongr : Work.NN.Core.fiberPot R j (Work.CR.Flat.dbarCoord k ũ) z
      = Work.NN.Core.fiberPot R j (Work.CR.Flat.dbarCoord k u) z := by
    rw [Work.NN.Core.fiberPot_apply, Work.NN.Core.fiberPot_apply]
    congr 1
    refine setIntegral_congr_fun measurableSet_ball (fun w hw => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hw
    rw [hkey w hw]
  rw [hcongr]

/-- **Local smoothness of the fibre potential.** -/
lemma contDiffOn_fiberPot_of_telCyl {R ρ : ℝ} (hρ : 0 < ρ) {j : Fin n} {k : ℕ}
    {z : Work.NN.Core.Cn n} {u ũ : Work.NN.Core.Cn n → ℂ} (hũ : ContDiff ℝ k ũ)
    (h : ∀ y ∈ telCyl R (2 * ρ) j z, u y = ũ y) (hρR : ρ + ‖z j‖ ≤ R) :
    ContDiffOn ℝ k (Work.NN.Core.fiberPot R j u) (Metric.ball z ρ) := by
  have hball : Metric.ball z ρ ⊆ {y | ‖y j‖ < R} := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have h1 : ‖y j - z j‖ ≤ ‖y - z‖ := by simpa using norm_le_pi_norm (y - z) j
    have h2 : ‖y j‖ ≤ ‖y j - z j‖ + ‖z j‖ := by
      calc ‖y j‖ = ‖(y j - z j) + z j‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    calc ‖y j‖ ≤ ‖y j - z j‖ + ‖z j‖ := h2
      _ ≤ ‖y - z‖ + ‖z j‖ := add_le_add_left h1 _
      _ < ρ + ‖z j‖ := add_lt_add_left hy _
      _ ≤ R := hρR
  exact (Work.NN.Core.contDiff_fiberPot R k j hũ).congr_mono
    (fun y hy => fiberPot_congr_of_telCyl hρ h y hy) hball

/-! ## Shrinking the tracking region -/

/-- A cylinder with small radius around a point of `telReg R R' (m+1)` is contained in
`telReg R R' m`. -/
lemma telCyl_subset_telReg {R R' : ℝ} (hRR' : R < R') {m : ℕ} (hm : m < n)
    {z : Work.NN.Core.Cn n} {s : ℝ}
    (hz : z ∈ telReg R R' (m+1))
    (hs : ∀ k : Fin n, k ≠ (⟨m, hm⟩ : Fin n) →
      ‖z k‖ + 2 * s < telRegB R R' (m+1) k) :
    telCyl R (2 * s) (⟨m, hm⟩ : Fin n) z ⊆ telReg R R' m := by
  intro y hy
  rw [mem_telCyl] at hy
  obtain ⟨hy1, hy2⟩ := hy
  intro k
  by_cases hk : k = (⟨m, hm⟩ : Fin n)
  · subst hk
    have hb : telRegB R R' m (⟨m, hm⟩ : Fin n) = R' := by
      simp [telRegB]
    rw [hb]
    linarith
  · have hbd : ‖y k‖ < telRegB R R' (m+1) k := by
      have h1 : ‖y k - z k‖ ≤ 2 * s := hy2 k hk
      have h2 : ‖y k‖ ≤ ‖y k - z k‖ + ‖z k‖ := by
        calc ‖y k‖ = ‖(y k - z k) + z k‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith [hs k hk]
    exact lt_of_lt_of_le hbd (telRegB_mono hRR'.le (by omega) k)

/-- A ball of small radius around a point of `telReg R R' (m+1)` stays in
`telReg R R' (m+1)`. -/
lemma ball_subset_telReg {R R' : ℝ} {m : ℕ} {z : Work.NN.Core.Cn n} {s : ℝ}
    (hs : ∀ k : Fin n, ‖z k‖ + s < telRegB R R' (m+1) k) :
    Metric.ball z s ⊆ telReg R R' (m+1) := by
  intro y hy k
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have h1 : ‖y k - z k‖ ≤ ‖y - z‖ := by simpa using norm_le_pi_norm (y - z) k
  have h2 : ‖y k‖ ≤ ‖y k - z k‖ + ‖z k‖ := by
    calc ‖y k‖ = ‖(y k - z k) + z k‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  linarith [hs k]

/-- The shrinking radius attached to a point of the tracking region. -/
lemma exists_rho_of_mem_telReg {R R' : ℝ} (hRR' : R < R') {m : ℕ} (hm : m < n)
    (hn : 0 < n) {z : Work.NN.Core.Cn n} (hz : z ∈ telReg R R' (m+1)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ + ‖z (⟨m, hm⟩ : Fin n)‖ ≤ R ∧
      Metric.ball z ρ ⊆ telReg R R' (m+1) ∧
      telCyl R (2 * ρ) (⟨m, hm⟩ : Fin n) z ⊆ telReg R R' m := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set j : Fin n := ⟨m, hm⟩ with hj
  have hzj : ‖z j‖ < R := by
    have := hz j
    simpa [telRegB, hj] using this
  set δ : ℝ := (Finset.univ : Finset (Fin n)).inf' Finset.univ_nonempty
    (fun k => telRegB R R' (m+1) k - ‖z k‖) with hδ
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    intro k _
    have := hz k
    linarith
  have hδk : ∀ k : Fin n, δ ≤ telRegB R R' (m+1) k - ‖z k‖ := by
    intro k
    rw [hδ]; exact Finset.inf'_le _ (Finset.mem_univ k)
  set ρ : ℝ := min (δ / 4) ((R - ‖z j‖) / 2) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact lt_min (by linarith) (by linarith)
  refine ⟨ρ, hρpos, ?_, ?_, ?_⟩
  · rw [hρdef] at *
    have : ρ ≤ (R - ‖z j‖) / 2 := min_le_right _ _
    linarith
  · refine ball_subset_telReg (fun k => ?_)
    have h3 : ρ ≤ δ / 4 := min_le_left _ _
    have := hδk k
    linarith
  · refine telCyl_subset_telReg hRR' hm hz (fun k hk => ?_)
    have h3 : 2 * ρ ≤ δ / 2 := by
      have hle : ρ ≤ δ / 4 := min_le_left _ _
      linarith
    have := hδk k
    linarith

/-! ## `∂̄`-calculus helpers -/

/-- The `∂̄`-derivative of a `C^{k+1}` function is `C^k`. -/
lemma contDiffOn_dbarCoord_le {k : ℕ} {u : Work.NN.Core.Cn n → ℂ}
    {s : Set (Work.NN.Core.Cn n)} (hs : IsOpen s) (hu : ContDiffOn ℝ (k + 1) u s) (j : Fin n) :
    ContDiffOn ℝ k (fun z => Work.CR.Flat.dbarCoord j u z) s := by
  have hfd : ContDiffOn ℝ k (fun z => fderiv ℝ u z) s :=
    hu.fderiv_of_isOpen hs (by push_cast; rfl)
  have hfun : (fun z => Work.CR.Flat.dbarCoord j u z)
      = fun z => (Work.CR.Flat.Polydisc.dbarCoordPhi j) (fderiv ℝ u z) := by
    funext z
    exact congrFun (Work.CR.Flat.Polydisc.dbarCoord_eq_comp j u) z
  rw [hfun]
  exact ((Work.CR.Flat.Polydisc.dbarCoordPhi j).contDiff.contDiffOn).comp hfd
    (fun x _ => Set.mem_univ _)

/-- `∂̄` of a difference, at differentiable points. -/
lemma dbarCoord_sub_apply {u v : Work.NN.Core.Cn n → ℂ} {z : Work.NN.Core.Cn n}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (j : Fin n) :
    Work.CR.Flat.dbarCoord j (fun y => u y - v y) z
      = Work.CR.Flat.dbarCoord j u z - Work.CR.Flat.dbarCoord j v z := by
  have hfd : fderiv ℝ (fun y => u y - v y) z = fderiv ℝ u z - fderiv ℝ v z :=
    fderiv_sub hu hv
  simp only [Work.CR.Flat.dbarCoord, hfd, sub_apply]
  ring

/-- `∂̄` only depends on the germ. -/
lemma dbarCoord_congr_of_eventuallyEq {f g : Work.NN.Core.Cn n → ℂ} {z : Work.NN.Core.Cn n}
    (h : f =ᶠ[𝓝 z] g) (j : Fin n) :
    Work.CR.Flat.dbarCoord j f z = Work.CR.Flat.dbarCoord j g z := by
  rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, h.fderiv_eq]

/-- `∂̄` of a function vanishing near a point vanishes there. -/
lemma dbarCoord_eq_zero_of_eventuallyEq_zero {f : Work.NN.Core.Cn n → ℂ}
    {z : Work.NN.Core.Cn n} (h : f =ᶠ[𝓝 z] 0) (j : Fin n) :
    Work.CR.Flat.dbarCoord j f z = 0 := by
  rw [dbarCoord_congr_of_eventuallyEq h j, Work.CR.Flat.dbarCoord,
    show (0 : Work.NN.Core.Cn n → ℂ) = Function.const _ (0 : ℂ) from rfl, fderiv_const]
  simp

/-- `∂̄` commutes with finite sums, at points where every summand is differentiable. -/
lemma dbarCoord_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Work.NN.Core.Cn n → ℂ)
    (j : Fin n) (z : Work.NN.Core.Cn n) (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    Work.CR.Flat.dbarCoord j (fun w => ∑ i ∈ s, f i w) z
      = ∑ i ∈ s, Work.CR.Flat.dbarCoord j (f i) z := by
  have hfun : (fun w => ∑ i ∈ s, f i w) = (∑ i ∈ s, f i : Work.NN.Core.Cn n → ℂ) := by
    funext w; simp
  have hsum : fderiv ℝ (∑ i ∈ s, f i : Work.NN.Core.Cn n → ℂ) z
      = ∑ i ∈ s, fderiv ℝ (f i) z := fderiv_sum h
  rw [hfun, Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
  simp only [Function.comp_apply]
  rw [hsum, map_sum]
  simp only [Work.CR.Flat.Polydisc.dbarCoord_eq_comp, Function.comp_apply]

/-- The stage-`m` potential is the fibre potential of the `m`-th row of the stage-`m` defect. -/
lemma telPsi_eq_fiberPot (R : ℝ) (ζ : Fin n → Fin n → Work.NN.Core.Cn n → ℂ) {m : ℕ}
    (hm : m < n) :
    Work.NN.Core.telPsi R ζ m
      = fun l z => Work.NN.Core.fiberPot R ⟨m, hm⟩
          (Work.NN.Core.telD R ζ m ⟨m, hm⟩ l) z := by
  cases m with
  | zero =>
      funext l z
      rw [Work.NN.Core.telPsi_zero]; simp only [dif_pos hm]
  | succ k =>
      funext l z
      rw [Work.NN.Core.telPsi_succ]; simp only [dif_pos hm]

/-! ## The exponent bookkeeping -/

/-- The regularity exponent `n + 2 - m` of the `m`-th stage, as an element of `WithTop ℕ∞`. -/
abbrev telExp (n m : ℕ) : WithTop ℕ∞ := ((n + 2 - m : ℕ) : WithTop ℕ∞)

lemma telExp_zero (n : ℕ) : telExp n 0 = ((n : WithTop ℕ∞) + 2) := by
  simp only [telExp, Nat.sub_zero, Nat.cast_add, Nat.cast_ofNat]

lemma telExp_succ_le {n m : ℕ} (hm : m ≤ n) : telExp n (m + 1) ≤ telExp n m := by
  unfold telExp
  exact_mod_cast (by omega : n + 2 - (m + 1) ≤ n + 2 - m)

lemma telExp_succ_add_one {n m : ℕ} (hm : m ≤ n) : telExp n (m + 1) + 1 = telExp n m := by
  unfold telExp
  exact_mod_cast (by omega : n + 2 - (m + 1) + 1 = n + 2 - m)

lemma contDiffOn_telExp_succ {n m : ℕ} {f : Work.NN.Core.Cn n → ℂ}
    {s : Set (Work.NN.Core.Cn n)} (h : ContDiffOn ℝ (telExp n m) f s) (hm : m ≤ n) :
    ContDiffOn ℝ (telExp n (m + 1)) f s := h.of_le (telExp_succ_le hm)

lemma contDiffOn_dbarCoord_telExp {n m : ℕ} {u : Work.NN.Core.Cn n → ℂ}
    {s : Set (Work.NN.Core.Cn n)} (hs : IsOpen s) (hu : ContDiffOn ℝ (telExp n m) u s)
    (hm : m ≤ n) (j : Fin n) :
    ContDiffOn ℝ (telExp n (m + 1)) (fun z => Work.CR.Flat.dbarCoord j u z) s := by
  have hk : telExp n m = (((n + 2 - (m + 1)) + 1 : ℕ) : WithTop ℕ∞) := by
    rw [telExp]; congr 1; omega
  rw [hk] at hu
  have h := contDiffOn_dbarCoord_le (k := n + 2 - (m + 1)) hs hu j
  rw [telExp]
  exact h

/-- The `∂̄`-derivative of a `C²` function is differentiable. -/
lemma diffAt_dbarCoord {u : Work.NN.Core.Cn n → ℂ} {z : Work.NN.Core.Cn n}
    (hu : ContDiffAt ℝ 2 u z) (j : Fin n) :
    DifferentiableAt ℝ (fun y => Work.CR.Flat.dbarCoord j u y) z := by
  have hdw : DifferentiableAt ℝ (fun y => fderiv ℝ u y) z :=
    (hu.fderiv_right (m := (1 : ℕ∞)) (by norm_num)).differentiableAt (by norm_num)
  have h1 : DifferentiableAt ℝ (fun y => (fderiv ℝ u y) (Pi.single j 1)) z :=
    hdw.clm_apply (differentiableAt_const _)
  have h2 : DifferentiableAt ℝ (fun y => (fderiv ℝ u y) (Pi.single j Complex.I)) z :=
    hdw.clm_apply (differentiableAt_const _)
  have h : (fun y => Work.CR.Flat.dbarCoord j u y) = fun y =>
      (1 / 2 : ℂ) * ((fderiv ℝ u y) (Pi.single j 1)
        + Complex.I * (fderiv ℝ u y) (Pi.single j Complex.I)) := rfl
  rw [h]
  exact (differentiableAt_const (1 / 2 : ℂ)).mul
    (h1.add ((differentiableAt_const Complex.I).mul h2))

/-- `∂̄` of a function vanishing on an open set vanishes there. -/
lemma dbarCoord_eq_zero_of_eq_zero_on_open {s : Set (Work.NN.Core.Cn n)} (hs : IsOpen s)
    {f : Work.NN.Core.Cn n → ℂ} {z : Work.NN.Core.Cn n} (hz : z ∈ s)
    (h0 : ∀ y ∈ s, f y = 0) (j : Fin n) : Work.CR.Flat.dbarCoord j f z = 0 :=
  dbarCoord_eq_zero_of_eventuallyEq_zero
    (Filter.eventually_of_mem (hs.mem_nhds hz) (fun y hy => h0 y hy)) j

end Work.NN.Final
