import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.window2_data
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.Existence.krad_pos_state_region

/-!
# The data fed to the long-interval Volterra engine on the transition window

This file fixes the *modified* data on which the long-interval fixed point engine
(`Work.VolterraLong`) is run to produce the window core of the odd transition-slope argument.

The paper's raw data (`Godd`, `Theta`, `Xi`) is not globally regular: the raw `Kvec` jumps
across the diagonal `σ = s` (it vanishes for `σ < s` and takes a non-zero diagonal value), the
source `Xi` is only regular on compacts inside `(0,1)`, and the state-differentiability of
`Godd` fails where the chord radicands vanish.  Following `Existence/window2_data.lean` we

* use the *manifest* (smooth) representatives `GoddM`, `ThetaM` of the kernels, which agree with
  the paper's kernels on the triangle `s ≤ σ` where the radicands are positive;
* cut the state data off to the window (`chiG`, `chiT`), so that all data has compact support
  and is smooth;
* replace the tail `∫_σ^{1}` of the paper's integral by the frozen tail
  `∫_{wC}^{1}` evaluated on the unperturbed state `baseState` (the bump `h` vanishes beyond
  `1 - τ = 9/10`, which is left of the splice point `wC = 19/20`, so the frozen tail is
  *independent* of `h`).

The `Θ`-datum needs one more modification: the manifest kernel `ThetaM` is smooth on the whole
window (there is no diagonal jump), but for the engine we may replace its values for `σ ≤ s` by
its diagonal value `ThetaM n h s s z` without changing the `σ`-integral (which runs over
`σ ∈ [s,1]`).  `ThetaClamp` does this, and `ThetaFed` additionally applies the cutoff `chiT`.

## Main definitions

* `thetaRegion`, `goddRegion` — the open regions on which the manifest data is smooth;
* `ThetaClamp`, `ThetaFed` — the clamped/cut-off `Θ`-datum fed to the engine.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- The open region of `(s,σ,z)` on which the manifest `Θ` is smooth: the slope cutoffs are
non-zero and the state is within `9/20` of the base state (so that `z 0, z 1 ≥ 0.25 > 1/5`). -/
def thetaRegion : Set ((ℝ × ℝ) × Work.OddVolterra.St) :=
  {p | |p.1.1 - Work.OddVolterra.Existence.wCenter| < 1 / 5 ∧
       |p.1.2 - Work.OddVolterra.Existence.wCenter| < 1 / 5 ∧
       ‖p.2 - Work.OddVolterra.baseState p.1.2‖ < 9 / 20}

/-- The open region of `(s,z)` on which the manifest `G` is smooth. -/
def goddRegion : Set (ℝ × Work.OddVolterra.St) :=
  {p | |p.1 - Work.OddVolterra.Existence.wCenter| < 1 / 5 ∧
       ‖p.2 - Work.OddVolterra.baseState p.1‖ < 9 / 20}

/-- The manifest `Θ` of the odd system, clamped at the diagonal: for `σ ≤ s` it takes its
diagonal value.  (The `σ`-integral of the system only runs over `σ ≥ s`, so this does not change
any solution.) -/
def ThetaClamp (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : Work.OddVolterra.St) : Work.OddVolterra.St :=
  Work.OddVolterra.KernelExt.ThetaM n h s (max s σ) z

/-- The `Θ`-datum fed to the long-interval engine: the clamped manifest kernel, cut off to the
window. -/
def ThetaFed (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : Work.OddVolterra.St) : Work.OddVolterra.St :=
  Work.OddVolterra.Existence.chiT s σ z • ThetaClamp n h s σ z

/-- The `G`-datum fed to the long-interval engine: the cut-off manifest kernel of
`Existence/window2_data.lean`. -/
def GoddFed (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : Work.OddVolterra.St) : Work.OddVolterra.St :=
  Work.OddVolterra.Existence.GoddW n h s z

/-- The source fed to the long-interval engine: the paper's `Ξ` plus the *frozen tail*
`∫_{wC}^{1} Θ`, cut off to the window (this is `Existence.XiW`). -/
def XiFed (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : Work.OddVolterra.St :=
  Work.OddVolterra.Existence.XiW n h s

/-- The radicand of the Abel denominator is positive on the whole region we use, without any
order condition on `(a,σ)`: with `|h^{(k)}| ≤ 1/100` (`k ≤ 1`), `σ + a > 1/10` and
`|t| ≥ 1/5` both factors of `krad h σ t a` have the sign of `t`. -/
lemma krad_pos_of_region {h : ℝ → ℝ}
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {σ t a : ℝ} (hσa : 1 / 10 < σ + a) (ht : 1 / 5 ≤ |t|) :
    0 < Work.OddVolterra.krad h σ t a := by
  have hh0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => hsmall 0 (by norm_num) x
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := by
    intro x
    simpa using hsmall 1 (by norm_num) x
  have hquotbd : |Work.OddVolterra.hquot h a σ| ≤ 1 / 100 :=
    Work.OddVolterra.Existence.abs_hquot_le_state hh1
  have hhl : |h σ + h a| ≤ 1 / 50 := by
    have h1 := abs_le.mp (hh0 σ)
    have h2 := abs_le.mp (hh0 a)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hsumlt : |h σ + h a| < (σ + a) * (1 / 5) := by
    have h2 : (1 : ℝ) / 50 < (σ + a) * (1 / 5) := by nlinarith [hσa]
    linarith
  rw [Work.OddVolterra.krad_apply]
  have hline : Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t
      = (σ + a) * t + (h σ + h a) := by
    unfold Work.OddVolterra.line; ring
  rw [hline]
  rcases lt_trichotomy t 0 with htn | htz | htp
  · have htle : t ≤ -(1 / 5) := by
      have h := ht; rw [abs_of_neg htn] at h; linarith
    have h1 : t + Work.OddVolterra.hquot h a σ < 0 := by
      linarith [(abs_le.mp hquotbd).2]
    have hbnd := abs_le.mp hhl
    have hmul : (σ + a) * t ≤ -((σ + a) * (1 / 5)) := by
      have h := mul_le_mul_of_nonneg_left htle (by linarith : (0:ℝ) ≤ σ + a)
      rwa [show (σ + a) * (-(1 / 5)) = -((σ + a) * (1 / 5)) by ring] at h
    have h2 : (σ + a) * t + (h σ + h a) < 0 := by linarith [hbnd.1]
    exact mul_pos_of_neg_of_neg h1 h2
  · rw [htz] at ht; norm_num at ht
  · have htge : (1 : ℝ) / 5 ≤ t := by
      have h := ht; rwa [abs_of_pos htp] at h
    have h1 : 0 < t + Work.OddVolterra.hquot h a σ := by
      linarith [(abs_le.mp hquotbd).1]
    have hbnd := abs_le.mp hhl
    have hmul : (σ + a) * (1 / 5) ≤ (σ + a) * t :=
      mul_le_mul_of_nonneg_left htge (by linarith : (0:ℝ) ≤ σ + a)
    have h2 : 0 < (σ + a) * t + (h σ + h a) := by
      have := le_abs_self (h σ + h a); linarith
    exact mul_pos h1 h2


/-! ## The window arithmetic and the identifications with the paper's data -/

lemma wA_eq : Work.OddVolterra.Existence.wA = 7 / 10 := rfl
lemma wC_eq : Work.OddVolterra.Existence.wC = 19 / 20 := rfl

lemma abs_sub_wCenter_le_of_mem {s : ℝ}
    (hs : s ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC) :
    |s - Work.OddVolterra.Existence.wCenter| ≤ 3 / 20 := by
  have h1 : (7 : ℝ) / 10 ≤ s := by
    have h := hs.1
    rw [Work.OddVolterra.Existence.wA_eq, Work.OddVolterra.tau] at h
    linarith
  have h2 : s ≤ 19 / 20 := by
    have h := hs.2
    rw [Work.OddVolterra.Existence.wC_eq, Work.OddVolterra.tau] at h
    linarith
  rw [abs_le, Work.OddVolterra.Existence.wCenter]
  constructor <;> linarith

/-- On the window the state cut-off is `1` near the base state. -/
lemma chiG_eq_one_of_mem {s : ℝ}
    (hs : s ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC)
    {z : Work.OddVolterra.St} (hz : ‖z - Work.OddVolterra.baseState s‖ ≤ 1 / 100) :
    Work.OddVolterra.Existence.chiG s z = 1 :=
  Work.OddVolterra.Existence.chiG_eq_one (abs_sub_wCenter_le_of_mem hs)
    (le_trans hz (by norm_num))

/-- On the window the `Θ` cut-off is `1` near the base state. -/
lemma chiT_eq_one_of_mem {s σ : ℝ}
    (hs : s ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC)
    (hσ : σ ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC)
    {z : Work.OddVolterra.St} (hz : ‖z - Work.OddVolterra.baseState σ‖ ≤ 1 / 100) :
    Work.OddVolterra.Existence.chiT s σ z = 1 :=
  Work.OddVolterra.Existence.chiT_eq_one (abs_sub_wCenter_le_of_mem hs)
    (abs_sub_wCenter_le_of_mem hσ) (le_trans hz (by norm_num))

/-- Near the base state the cut-off `G`-datum is the paper's `Godd`. -/
lemma GoddW_eq_Godd (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s : ℝ}
    (hs : s ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC)
    {z : Work.OddVolterra.St} (hz : ‖z - Work.OddVolterra.baseState s‖ ≤ 1 / 100) :
    Work.OddVolterra.Existence.GoddW n h s z = Work.OddVolterra.Godd n h s z := by
  rw [Work.OddVolterra.Existence.GoddW, chiG_eq_one_of_mem hs hz, one_smul]
  exact Work.OddVolterra.Window.GoddM_eq_Godd n hh s z

lemma seven_tenths_le_profileX {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX s := by
  have h1 : Commons.Geometry.Ulam.profileX 1 ≤ Commons.Geometry.Ulam.profileX s :=
    Commons.Geometry.Ulam.profileX_le_profileX' hs0 hs1
  have h2 : Commons.Geometry.Ulam.profileX 1 = 1 / Real.sqrt 2 := by
    simp only [Commons.Geometry.Ulam.profileX]; norm_num
  have h3 : Real.sqrt 2 < 10 / 7 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h4 : (7 : ℝ) / 10 < 1 / Real.sqrt 2 := by
    rw [lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    nlinarith [h3]
  rw [h2] at h1
  linarith

lemma seven_tenths_le_profileX_of_mem {σ : ℝ}
    (hσ : σ ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC) :
    (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX σ := by
  have h1 : (7 : ℝ) / 10 ≤ σ := by
    have h := hσ.1
    rw [Work.OddVolterra.Existence.wA_eq, Work.OddVolterra.tau] at h
    linarith
  have h2 : σ ≤ 1 := by
    have h := hσ.2
    rw [Work.OddVolterra.Existence.wC_eq, Work.OddVolterra.tau] at h
    linarith
  exact seven_tenths_le_profileX (by linarith) h2

lemma one_fifth_le_of_close_base {σ z0 : ℝ}
    (hσ : σ ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC)
    (hz : |z0 - Commons.Geometry.Ulam.profileX σ| ≤ 1 / 2) :
    (1 / 5 : ℝ) ≤ z0 := by
  have h1 := seven_tenths_le_profileX_of_mem hσ
  linarith [(abs_le.mp hz).1]

end

end Work.OddVolterra.Window
