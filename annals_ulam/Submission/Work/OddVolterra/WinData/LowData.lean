import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.WinData.Basic
import Submission.Work.OddVolterra.Window.WindowDefs
import Submission.Work.OddVolterra.Window.TW_regular
import Submission.Work.OddVolterra.Window.TW2_regular
import Submission.Work.OddExistence.Manifest.thetaM_lipschitz
import Submission.Work.OddCurveB.Est.exists_linearization
import Submission.Work.VolterraLong.Main
import Submission.Work.OddVolterra.Existence.base_volterra
import Submission.Work.OddVolterra.Existence.xi_close_of_small
import Submission.Work.OddVolterra.Existence.aw_contDiffOn_awGodd
import Submission.Work.OddExistence.Estimates.theta_lipschitz

/-!
# The low-slope piece of the odd transition-slope construction: the clamped data

On the slope interval `[1/4, 4/5]` the bump `h` (supported in `[4/5, 9/10]`) vanishes together
with all its derivatives on an open neighbourhood, so on that window the state datum
`Godd n h s` and the manifest kernel `ThetaM n h s σ` coincide with the unperturbed data
`Godd n 0 s`, `ThetaM n 0 s σ`.  Consequently the low-slope part of the paper's system is a
Volterra system with *fixed* data and a modified source; the long-interval engine
`Work.VolterraLong.volterra_long_exists_eps` solves it with constants that do not depend on `h`.

This file sets up the clamped data of that piece: the cut-offs, the clamped state datum
`lcGodd` and the clamped kernel `lcTheta`, together with the positivity of the radicands, the
smoothness of the underlying manifest data on the region of use, and the basic API
(continuity, values at the base state).
-/

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra

/-! ## The low slope window and its cut-off -/

/-- The left end of the low slope window. -/
def lcA : ℝ := 1 / 4

/-- The right end of the low slope window, the left edge of the support of `h`. -/
def lcB : ℝ := 4 / 5

/-- The centre of the low slope cut-off. -/
def lcCenter : ℝ := 21 / 40

/-- The inner radius of the low slope cut-off: it makes the cut-off `1` on `[1/4, 4/5]`. -/
def lcRin : ℝ := 11 / 40

/-- The outer radius of the low slope cut-off. -/
def lcRout : ℝ := 3 / 10

lemma lcRin_lt_lcRout : lcRin < lcRout := by norm_num [lcRin, lcRout]
lemma lcRin_pos : 0 < lcRin := by norm_num [lcRin]
lemma lcA_pos : 0 < lcA := by norm_num [lcA]
lemma lcA_le_lcB : lcA ≤ lcB := by norm_num [lcA, lcB]

/-- The low-slope cut-off bump: `= 1` on `[1/4, 4/5]`, support inside `(9/40, 33/40)`. -/
def lcCs : ContDiffBump lcCenter := ⟨lcRin, lcRout, lcRin_pos, lcRin_lt_lcRout⟩

/-- The low-slope cut-off, as a function of the slope. -/
def lcS (s : ℝ) : ℝ := (lcCs : ℝ → ℝ) s

lemma lcS_eq_one_of_mem {s : ℝ} (hs : s ∈ Set.Icc lcA lcB) : lcS s = 1 := by
  have h1 : (1 : ℝ) / 4 ≤ s := by simpa [lcA] using hs.1
  have h2 : s ≤ 4 / 5 := by simpa [lcB] using hs.2
  have h : |s - lcCenter| ≤ lcRin := by
    have hc : lcCenter = 21 / 40 := rfl
    have hr : lcRin = 11 / 40 := rfl
    rw [hc, hr, abs_le]
    constructor <;> linarith
  refine ContDiffBump.one_of_mem_closedBall lcCs ?_
  rw [Metric.mem_closedBall, Real.dist_eq, lcCs]
  exact h

lemma lcS_eq_zero_of_le_dist {s : ℝ} (hs : lcRout ≤ |s - lcCenter|) : lcS s = 0 := by
  refine ContDiffBump.zero_of_le_dist lcCs ?_
  rw [Real.dist_eq, lcCs]
  exact hs

lemma lcS_eq_zero_of_le {s : ℝ} (hs : s ≤ 9 / 40) : lcS s = 0 := by
  refine lcS_eq_zero_of_le_dist ?_
  have hc : lcCenter = 21 / 40 := rfl
  have hro : lcRout = 3 / 10 := rfl
  have h : s - lcCenter ≤ 0 := by rw [hc]; linarith
  rw [abs_of_nonpos h, hro, hc]; linarith

lemma lcS_eq_zero_of_ge {s : ℝ} (hs : 33 / 40 ≤ s) : lcS s = 0 := by
  refine lcS_eq_zero_of_le_dist ?_
  have hc : lcCenter = 21 / 40 := rfl
  have hro : lcRout = 3 / 10 := rfl
  have h : 0 ≤ s - lcCenter := by rw [hc]; linarith
  rw [abs_of_nonneg h, hro, hc]; linarith

lemma lcS_nonneg (s : ℝ) : 0 ≤ lcS s := ContDiffBump.nonneg lcCs
lemma lcS_le_one (s : ℝ) : lcS s ≤ 1 := ContDiffBump.le_one lcCs
lemma abs_lcS_le_one (s : ℝ) : |lcS s| ≤ 1 := by
  rw [abs_of_nonneg (lcS_nonneg s)]; exact lcS_le_one s

lemma lcS_support_subset : Function.support lcS ⊆ Set.Ioo (9 / 40 : ℝ) (33 / 40) := by
  intro s hs
  rw [Function.mem_support] at hs
  constructor
  · by_contra h
    push_neg at h
    exact hs (lcS_eq_zero_of_le h)
  · by_contra h
    push_neg at h
    exact hs (lcS_eq_zero_of_ge h)

lemma contDiff_lcS : ContDiff ℝ (⊤ : ℕ∞) lcS := ContDiffBump.contDiff lcCs

/-! ## The regions of the low window on which the manifest data are smooth -/

/-- The open region of `(s,σ,z)` on which the manifest kernel `ThetaM n 0` is smooth. -/
def lcU : Set (ℝ × (ℝ × St)) :=
  {q | q.1 ∈ Set.Ioo (1 / 5) 1 ∧ q.2.1 ∈ Set.Ioo (1 / 5) 1 ∧
    1 / 5 < |q.2.2 0| ∧ 1 / 5 < |q.2.2 1|}

/-- The open region of `(s,z)` on which the manifest state datum `GoddM n 0` is smooth. -/
def lcV : Set (ℝ × St) :=
  {p | p.1 ∈ Set.Ioo (1 / 5) 1 ∧ 1 / 5 < |p.2 0| ∧ 1 / 5 < |p.2 1|}

lemma isOpen_lcU : IsOpen lcU := by
  set φ : ℝ × (ℝ × St) → ℝ × ℝ × ℝ × ℝ :=
    fun q => (q.1, q.2.1, |q.2.2 0|, |q.2.2 1|) with hφ
  have hcont : Continuous φ := by rw [hφ]; fun_prop
  have hset : lcU = φ ⁻¹' (Set.Ioo (1 / 5 : ℝ) 1 ×ˢ
      (Set.Ioo (1 / 5 : ℝ) 1 ×ˢ
        ((Set.Ioi (1 / 5 : ℝ)) ×ˢ (Set.Ioi (1 / 5 : ℝ))))) := by
    rw [hφ]
    ext q
    simp only [lcU, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Ioo]
    tauto
  rw [hset]
  exact (isOpen_Ioo.prod (isOpen_Ioo.prod (isOpen_Ioi.prod isOpen_Ioi))).preimage hcont

lemma isOpen_lcV : IsOpen lcV := by
  set ψ : ℝ × St → ℝ × ℝ × ℝ := fun p => (p.1, |p.2 0|, |p.2 1|) with hψ
  have hcont : Continuous ψ := by rw [hψ]; fun_prop
  have hset : lcV = ψ ⁻¹' (Set.Ioo (1 / 5 : ℝ) 1 ×ˢ
      ((Set.Ioi (1 / 5 : ℝ)) ×ˢ (Set.Ioi (1 / 5 : ℝ)))) := by
    rw [hψ]
    ext p
    simp only [lcV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Ioo]
    tauto
  rw [hset]
  exact (isOpen_Ioo.prod (isOpen_Ioi.prod isOpen_Ioi)).preimage hcont

/-- The zero bump is supported in the transition window. -/
lemma supp_zero_subset : Function.support (0 : ℝ → ℝ) ⊆
    Set.Icc (1 - 2 * tau) (1 - tau) := by
  intro x hx
  rw [Function.mem_support] at hx
  exact absurd rfl hx

lemma small_zero : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ 1 / 100 := by
  intro k hk s
  have h0 : iteratedDeriv k (0 : ℝ → ℝ) s = 0 := by
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
    split <;> simp
  rw [h0, abs_zero]; norm_num

/-- The Abel radicand of the unperturbed data is positive on the low region. -/
lemma lcU_krad_pos {q : ℝ × (ℝ × St)} (hq : q ∈ lcU) :
    0 < krad (0 : ℝ → ℝ) q.2.1 (-(q.2.2 0)) q.1 ∧
      0 < krad (0 : ℝ → ℝ) q.2.1 (q.2.2 1) q.1 := by
  obtain ⟨h1, h2, h3, h5⟩ := hq
  exact ⟨krad_pos_box supp_zero_subset small_zero (by norm_num) (le_of_lt h1.1)
      (le_of_lt h2.1) (le_of_lt h2.2) (le_of_lt h1.2) (by rw [abs_neg]; exact le_of_lt h3),
    krad_pos_box supp_zero_subset small_zero (by norm_num) (le_of_lt h1.1)
      (le_of_lt h2.1) (le_of_lt h2.2) (le_of_lt h1.2) (le_of_lt h5)⟩

lemma lcU_krad_pos_move {q : ℝ × (ℝ × St)} (hq : q ∈ lcU) {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) 1) :
    0 < krad (0 : ℝ → ℝ) q.2.1 (-(q.2.2 0)) (q.1 + τ * (q.2.1 - q.1)) ∧
      0 < krad (0 : ℝ → ℝ) q.2.1 (q.2.2 1) (q.1 + τ * (q.2.1 - q.1)) := by
  obtain ⟨h1, h2, h3, h5⟩ := hq
  have h1τ : (0:ℝ) ≤ 1 - τ := by linarith [hτ.2]
  have hsum : (1 - τ) + τ = (1:ℝ) := by ring
  have hcomb : (1 - τ) * q.1 + τ * q.2.1 ∈ Set.Ioo (1 / 5 : ℝ) 1 := by
    have := convex_Ioo (1 / 5 : ℝ) 1 h1 h2 h1τ hτ.1 hsum
    simpa [smul_eq_mul] using this
  have hmove : q.1 + τ * (q.2.1 - q.1) = (1 - τ) * q.1 + τ * q.2.1 := by ring
  have hlo : (1 / 5 : ℝ) < q.1 + τ * (q.2.1 - q.1) := by
    rw [hmove]; exact hcomb.1
  have hhi : q.1 + τ * (q.2.1 - q.1) < 1 := by
    rw [hmove]; exact hcomb.2
  refine ⟨krad_pos_box supp_zero_subset small_zero (by norm_num) (le_of_lt hlo)
    (le_of_lt h2.1) (le_of_lt h2.2) (by linarith) ?_,
    krad_pos_box supp_zero_subset small_zero (by norm_num) (le_of_lt hlo)
    (le_of_lt h2.1) (le_of_lt h2.2) (by linarith) ?_⟩
  · rw [abs_neg]; exact le_of_lt h3
  · exact le_of_lt h5

/-- The manifest kernel of the unperturbed data is `C^∞` on the low region. -/
theorem contDiffOn_lcU_ThetaM (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St) => KernelExt.ThetaM n 0 q.1 q.2.1 q.2.2) lcU :=
  Work.OddExistence.Manifest.contDiffOn_KernelExtThetaM_of_pos n contDiff_const isOpen_lcU
    (fun q hq => lcU_krad_pos hq) (fun q hq τ hτ => lcU_krad_pos_move hq hτ)

/-- The Abel denominator of the unperturbed data is positive on the low region (diagonal). -/
lemma lcV_Kden_pos {p : ℝ × St} (hp : p ∈ lcV) :
    0 < Kden (0 : ℝ → ℝ) p.1 p.1 (-(p.2 0)) ∧ 0 < Kden (0 : ℝ → ℝ) p.1 p.1 (p.2 1) := by
  obtain ⟨h1, h2, h4⟩ := hp
  have h1a : (0:ℝ) < p.1 := by linarith [h1.1]
  have h1b : p.1 ≤ 1 := le_of_lt h1.2
  rw [Kden_eq_sqrt_krad]
  refine ⟨Real.sqrt_pos.mpr ?_, Real.sqrt_pos.mpr ?_⟩
  · refine krad_pos_box supp_zero_subset small_zero (by norm_num) (le_of_lt h1.1)
      (le_of_lt h1.1) h1b h1b ?_
    rw [abs_neg]; exact le_of_lt h2
  · exact krad_pos_box supp_zero_subset small_zero (by norm_num) (le_of_lt h1.1)
      (le_of_lt h1.1) h1b h1b (le_of_lt h4)

/-- The manifest state datum of the unperturbed data is `C^∞` on the low region. -/
theorem contDiffOn_lcV_GoddM (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => KernelExt.GoddM n 0 p.1 p.2) lcV := by
  have hkvec := Work.OddVolterra.Existence.contDiffOn_KvecM_diag n contDiff_const (B := lcV)
    (fun p hp => (lcV_Kden_pos hp).1) (fun p hp => (lcV_Kden_pos hp).2)
  have hπ : (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹) = Real.pi :=
    Existence.abel_weight_integral
  have hdiag : (fun p : ℝ × St => KernelExt.GoddM n 0 p.1 p.2) =
      (fun p : ℝ × St =>
        ![p.2 0, p.2 1,
          -(Real.pi * (KernelExt.KvecM n 0 p.1 p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3)) 0),
          -(Real.pi * (KernelExt.KvecM n 0 p.1 p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3)) 1)]) := by
    funext p
    have h1 : ∀ i : Fin 2, KernelExt.G2M n 0 p.1 p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3) i =
        KernelExt.KvecM n 0 p.1 p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3) i *
          ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ :=
      Existence.G2M_diag n 0 p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3)
    funext i
    fin_cases i <;>
      simp only [KernelExt.GoddM, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
        h1, hπ] <;>
      ring
  rw [hdiag]
  refine contDiffOn_pi.mpr fun i => ?_
  fin_cases i
  · exact (Work.OddVolterra.Existence.contDiffOn_coord (B := lcV) 0)
  · exact (Work.OddVolterra.Existence.contDiffOn_coord (B := lcV) 1)
  · exact (contDiffOn_const.mul ((contDiffOn_pi.mp hkvec) 0)).neg
  · exact (contDiffOn_const.mul ((contDiffOn_pi.mp hkvec) 1)).neg

end

end Work.OddVolterra.WinData
