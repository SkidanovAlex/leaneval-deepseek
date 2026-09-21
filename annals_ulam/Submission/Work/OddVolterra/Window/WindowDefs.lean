import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs

/-!
# The data of the truncated odd Volterra system on the transition window

This file fixes the *modified* (cut-off) data on which the long-interval fixed point engine
`Work.VolterraLong.volterra_long_exists` is run for the odd case of Ryabogin's theorem:

* `cs` is a `C^∞` bump on `ℝ` which equals `1` on `[7/10, 19/20]` and has support inside
  `(2/3, 1)`;
* `cz` is a `C^∞` bump on `ℝ` which equals `1` on `[-1/5, 1/5]` and vanishes off `(-2/5, 2/5)`;
* `chiG s z = cs s * cz ‖z - baseState s‖`, `chiT s σ z = cs s * cs σ * cz ‖z - baseState σ‖`;
* `GW n h s z = chiG s z • Godd n h s z`;
* `TW n h s σ z = chiT s σ z • (Θ n h s σ z` on the triangle `s < σ`, and the diagonal value
  `ΘM n h s s z` of the manifest representative on and below the diagonal`)` — the raw `Θ` jumps
  across the diagonal, and the continuation is invisible to the system (whose `σ`-integral only
  sees `σ ≥ s`);
* `XW n h s = cs s • (Ξ n h s + ∫_{19/20}^1 thetac n h s σ (baseState σ))`.

The point of the cut-offs is that the raw data `Godd`, `Theta`, `Xi` is only regular where the
Abel radicands are positive (on the state region of use this holds), while the engine asks for
*globally* continuous (resp. Lipschitz, differentiable) data.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra

/-! ## The constants -/

/-- The centre of the slope cut-off. -/
def wCenter : ℝ := 33 / 40

/-- The left end of the window, `1 - 3 τ`. -/
def wLeft : ℝ := 7 / 10

/-- The right end of the window, `1 - τ / 2`. -/
def wRight : ℝ := 19 / 20

lemma wLeft_eq : wLeft = 1 - 3 * tau := by norm_num [wLeft, tau]
lemma wRight_eq : wRight = 1 - tau / 2 := by norm_num [wRight, tau]
lemma wLeft_pos : 0 < wLeft := by norm_num [wLeft]
lemma wLeft_le_wRight : wLeft ≤ wRight := by norm_num [wLeft, wRight]
lemma wRight_lt_one : wRight < 1 := by norm_num [wRight]
lemma wRight_pos : 0 < wRight := by norm_num [wRight]
lemma one_sub_tau_lt_wRight : 1 - tau < wRight := by norm_num [tau, wRight]

/-! ## The bumps -/

/-- The bump in the slope variable: `= 1` on `|s - 33/40| ≤ 3/20`, support inside `(2/3, 1)`. -/
def cs : ContDiffBump wCenter := ⟨3 / 20, 4 / 25, by norm_num, by norm_num⟩

/-- The bump in the state variable: `= 1` on `|w| ≤ 1/5`. -/
def cz : ContDiffBump (0 : ℝ) := ⟨1 / 5, 2 / 5, by norm_num, by norm_num⟩

lemma cs_rIn : cs.rIn = 3 / 20 := rfl
lemma cs_rOut : cs.rOut = 4 / 25 := rfl
lemma cz_rIn : cz.rIn = 1 / 5 := rfl
lemma cz_rOut : cz.rOut = 2 / 5 := rfl

lemma cs_eq_one {s : ℝ} (hs : |s - wCenter| ≤ 3 / 20) : (cs : ℝ → ℝ) s = 1 := by
  refine ContDiffBump.one_of_mem_closedBall cs ?_
  rw [cs_rIn, Metric.mem_closedBall, Real.dist_eq]
  simpa [wCenter] using hs

lemma cs_eq_zero {s : ℝ} (hs : 4 / 25 ≤ |s - wCenter|) : (cs : ℝ → ℝ) s = 0 := by
  refine ContDiffBump.zero_of_le_dist cs ?_
  rw [cs_rOut, Real.dist_eq]
  simpa [wCenter] using hs

lemma cz_eq_one {w : ℝ} (hw : |w| ≤ 1 / 5) : (cz : ℝ → ℝ) w = 1 := by
  refine ContDiffBump.one_of_mem_closedBall cz ?_
  rw [cz_rIn, Metric.mem_closedBall, Real.dist_eq]
  simpa using hw

lemma cz_eq_zero {w : ℝ} (hw : 2 / 5 ≤ |w|) : (cz : ℝ → ℝ) w = 0 := by
  refine ContDiffBump.zero_of_le_dist cz ?_
  rw [cz_rOut, Real.dist_eq]
  simpa using hw

lemma cs_nonneg (s : ℝ) : 0 ≤ (cs : ℝ → ℝ) s := ContDiffBump.nonneg cs
lemma cs_le_one (s : ℝ) : (cs : ℝ → ℝ) s ≤ 1 := ContDiffBump.le_one cs
lemma cz_nonneg (w : ℝ) : 0 ≤ (cz : ℝ → ℝ) w := ContDiffBump.nonneg cz
lemma cz_le_one (w : ℝ) : (cz : ℝ → ℝ) w ≤ 1 := ContDiffBump.le_one cz

lemma abs_cs_le_one (s : ℝ) : |(cs : ℝ → ℝ) s| ≤ 1 := by
  rw [abs_of_nonneg (cs_nonneg s)]; exact cs_le_one s

lemma abs_cz_le_one (w : ℝ) : |(cz : ℝ → ℝ) w| ≤ 1 := by
  rw [abs_of_nonneg (cz_nonneg w)]; exact cz_le_one w

/-- On the window the slope cut-off is `1`. -/
lemma cs_eq_one_of_mem {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight) : (cs : ℝ → ℝ) s = 1 := by
  refine cs_eq_one ?_
  rw [abs_le]
  simp only [wLeft, wRight, wCenter] at hs ⊢
  constructor <;> linarith [hs.1, hs.2]

/-! ## The cut-off factors -/

/-- The cut-off of the state data. -/
def chiG (s : ℝ) (z : St) : ℝ := (cs : ℝ → ℝ) s * (cz : ℝ → ℝ) (‖z - baseState s‖)

/-- The cut-off of the `Θ` data. -/
def chiT (s σ : ℝ) (z : St) : ℝ :=
  (cs : ℝ → ℝ) s * (cs : ℝ → ℝ) σ * (cz : ℝ → ℝ) (‖z - baseState σ‖)

lemma abs_chiG_le_one (s : ℝ) (z : St) : |chiG s z| ≤ 1 := by
  rw [chiG, abs_mul]
  calc |(cs : ℝ → ℝ) s| * |(cz : ℝ → ℝ) (‖z - baseState s‖)| ≤ 1 * 1 :=
        mul_le_mul (abs_cs_le_one s) (abs_cz_le_one _) (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

lemma abs_chiT_le_one (s σ : ℝ) (z : St) : |chiT s σ z| ≤ 1 := by
  rw [chiT, abs_mul, abs_mul]
  calc |(cs : ℝ → ℝ) s| * |(cs : ℝ → ℝ) σ| * |(cz : ℝ → ℝ) (‖z - baseState σ‖)|
      ≤ 1 * 1 * 1 :=
        mul_le_mul (mul_le_mul (abs_cs_le_one s) (abs_cs_le_one σ) (abs_nonneg _) (by norm_num))
          (abs_cz_le_one _) (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

lemma chiG_eq_one_of_close {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight) {z : St}
    (hz : ‖z - baseState s‖ ≤ 1 / 5) : chiG s z = 1 := by
  rw [chiG, cs_eq_one_of_mem hs, cz_eq_one (by simpa using hz), one_mul]

lemma chiT_eq_one_of_close {s σ : ℝ} (hs : s ∈ Set.Icc wLeft wRight)
    (hσ : σ ∈ Set.Icc wLeft wRight) {z : St} (hz : ‖z - baseState σ‖ ≤ 1 / 5) :
    chiT s σ z = 1 := by
  rw [chiT, cs_eq_one_of_mem hs, cs_eq_one_of_mem hσ,
    cz_eq_one (by simpa using hz), one_mul, one_mul]

lemma cz_eq_zero_of_norm {w : ℝ} (hw : 2 / 5 ≤ w) : (cz : ℝ → ℝ) w = 0 :=
  cz_eq_zero (by rwa [abs_of_nonneg (by linarith)])

lemma chiT_eq_zero_of_far {s σ : ℝ} {z : St} (hz : 2 / 5 ≤ ‖z - baseState σ‖) :
    chiT s σ z = 0 := by
  rw [chiT, cz_eq_zero_of_norm hz, mul_zero]

lemma chiG_eq_zero_of_far {s : ℝ} {z : St} (hz : 2 / 5 ≤ ‖z - baseState s‖) :
    chiG s z = 0 := by
  rw [chiG, cz_eq_zero_of_norm hz, mul_zero]

/-- On the window, `chiT` is the state bump alone. -/
lemma chiT_eq_cz_of_mem {s σ : ℝ} (hs : s ∈ Set.Icc wLeft wRight)
    (hσ : σ ∈ Set.Icc wLeft wRight) (z : St) :
    chiT s σ z = (cz : ℝ → ℝ) (‖z - baseState σ‖) := by
  rw [chiT, cs_eq_one_of_mem hs, cs_eq_one_of_mem hσ, one_mul, one_mul]

/-- On the window, `chiG` is the state bump alone. -/
lemma chiG_eq_cz_of_mem {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight) (z : St) :
    chiG s z = (cz : ℝ → ℝ) (‖z - baseState s‖) := by
  rw [chiG, cs_eq_one_of_mem hs, one_mul]

/-! ## The modified data -/

/-- The modified state data: the paper's `𝐆`, cut off to the window. -/
def GW (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : St) : St := chiG s z • Godd n h s z

/-- The `Θ`-integrand on the triangle `s < σ`, continued on the diagonal and below it by the
diagonal value of the *manifest* (smooth) representative `ThetaM`.

Two facts force this choice.  First, the raw `Theta` jumps across the diagonal: for a first slope
argument strictly larger than the second the raw kernel `Kvec` collapses to `0` (its outer
`√(L_σ² - L_s²)` factor vanishes), so `s ↦ G2 n h s σ z` is locally constant for `s > σ`
while `G2` evaluated on the diagonal is `π • Kvec(s,s,z) ≠ 0`.  Second, the frozen value must be
the *limit* from the triangle, and for the raw `Theta` the value at the diagonal is Mathlib's
`deriv` of that jumping function, i.e. `0`, not the limit.  The manifest representative
`ThetaM = Theta` on the open triangle and its diagonal value *is* the limit. -/
def thetac (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : St) : St :=
  if s < σ then Theta n h s σ z else KernelExt.ThetaM n h s s z

/-- The modified `Θ` data: the paper's `𝚯` on the triangle `s ≤ σ`, continued below the diagonal
by its diagonal value, cut off to the window. -/
def TW (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : St) : St := chiT s σ z • thetac n h s σ z

/-- The modified source: the paper's `𝚵` plus the frozen tail `∫_{19/20}^1 Θ(·,σ,baseState σ)`,
cut off to the window. -/
def XW (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : St :=
  (cs : ℝ → ℝ) s •
    (Xi n h s + ∫ σ in wRight..(1 : ℝ), thetac n h s σ (baseState σ))


/-! ## A smooth (squared-distance) variant of the state cut-offs

The norm-based cut-offs `chiG`, `chiT` above are only *continuous* in the state: the sup-norm of
`z - baseState s` is not differentiable where the maximum is attained at two coordinates at once.
The long-interval engine however asks for data that is differentiable in the state, so the engine
is run on the variant below, where the state cut-off is the bump composed with the *squared*
Euclidean distance `wsq`, a polynomial in the state (hence `C^∞`).  The two variants agree
wherever they matter for the estimate: the squeeze `wsq ≤ 4 * ‖·‖² ≤ 4 * wsq` on `St` shows that
`chiG2 = 1` once `‖z - baseState s‖ ≤ 1/100` and `chiG2 = 0` once `‖z - baseState s‖ ≥ 2/5`. -/

/-- The squared Euclidean distance to the ball's state. -/
def wsq (s : ℝ) (z : St) : ℝ := ∑ i : Fin 4, (z i - baseState s i) ^ 2

lemma wsq_nonneg (s : ℝ) (z : St) : 0 ≤ wsq s z :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The sup-norm bound implies the squared-Euclidean bound. -/
lemma wsq_le_four_mul_sq_norm (s : ℝ) (z : St) : wsq s z ≤ 4 * ‖z - baseState s‖ ^ 2 := by
  rw [wsq]
  have h4 : ∀ i : Fin 4, (z i - baseState s i) ^ 2 ≤ ‖z - baseState s‖ ^ 2 := by
    intro i
    have h := norm_le_pi_norm (z - baseState s) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    have h' : |z i - baseState s i| ≤ |‖z - baseState s‖| := by rwa [abs_of_nonneg (norm_nonneg _)]
    exact sq_le_sq.mpr h'
  calc ∑ i : Fin 4, (z i - baseState s i) ^ 2 ≤ ∑ _i : Fin 4, ‖z - baseState s‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => h4 i)
    _ = 4 * ‖z - baseState s‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num

/-- The squared-Euclidean bound implies the sup-norm bound. -/
lemma sq_norm_le_wsq (s : ℝ) (z : St) : ‖z - baseState s‖ ^ 2 ≤ wsq s z := by
  have hW : 0 ≤ wsq s z := wsq_nonneg s z
  have hle : ‖z - baseState s‖ ≤ Real.sqrt (wsq s z) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (fun i => ?_)
    rw [Pi.sub_apply, Real.norm_eq_abs]
    have h1 : (z i - baseState s i) ^ 2 ≤ wsq s z :=
      Finset.single_le_sum (f := fun j : Fin 4 => (z j - baseState s j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    calc |z i - baseState s i| = Real.sqrt ((z i - baseState s i) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (wsq s z) := Real.sqrt_le_sqrt h1
  calc ‖z - baseState s‖ ^ 2 ≤ (Real.sqrt (wsq s z)) ^ 2 := by
        nlinarith [norm_nonneg (z - baseState s), Real.sqrt_nonneg (wsq s z)]
    _ = wsq s z := Real.sq_sqrt hW

/-- The bump of the squared-distance cut-off: `= 1` on `[0, 1/100]`, `= 0` on `[4/25, ∞)`. -/
def cz2 : ContDiffBump (0 : ℝ) := ⟨1 / 100, 4 / 25, by norm_num, by norm_num⟩

lemma cz2_rIn : cz2.rIn = 1 / 100 := rfl
lemma cz2_rOut : cz2.rOut = 4 / 25 := rfl

lemma cz2_eq_one {w : ℝ} (hw : |w| ≤ 1 / 100) : (cz2 : ℝ → ℝ) w = 1 := by
  refine ContDiffBump.one_of_mem_closedBall cz2 ?_
  rw [cz2_rIn, Metric.mem_closedBall, Real.dist_eq]
  simpa using hw

lemma cz2_eq_zero {w : ℝ} (hw : 4 / 25 ≤ |w|) : (cz2 : ℝ → ℝ) w = 0 := by
  refine ContDiffBump.zero_of_le_dist cz2 ?_
  rw [cz2_rOut, Real.dist_eq]
  simpa using hw

lemma cz2_nonneg (w : ℝ) : 0 ≤ (cz2 : ℝ → ℝ) w := ContDiffBump.nonneg cz2
lemma cz2_le_one (w : ℝ) : (cz2 : ℝ → ℝ) w ≤ 1 := ContDiffBump.le_one cz2

lemma abs_cz2_le_one (w : ℝ) : |(cz2 : ℝ → ℝ) w| ≤ 1 := by
  rw [abs_of_nonneg (cz2_nonneg w)]; exact cz2_le_one w

lemma cz2_eq_zero_of_le {w : ℝ} (hw : 4 / 25 ≤ w) : (cz2 : ℝ → ℝ) w = 0 :=
  cz2_eq_zero (by rwa [abs_of_nonneg (by linarith)])

lemma cz2_eq_one_of_le {w : ℝ} (hw : w ≤ 1 / 100) (hw0 : 0 ≤ w) : (cz2 : ℝ → ℝ) w = 1 :=
  cz2_eq_one (by rwa [abs_of_nonneg hw0])

/-- The smooth cut-off of the state data. -/
def chiG2 (s : ℝ) (z : St) : ℝ := (cs : ℝ → ℝ) s * (cz2 : ℝ → ℝ) (wsq s z)

/-- The smooth cut-off of the `Θ` data. -/
def chiT2 (s σ : ℝ) (z : St) : ℝ :=
  (cs : ℝ → ℝ) s * (cs : ℝ → ℝ) σ * (cz2 : ℝ → ℝ) (wsq σ z)

lemma abs_chiG2_le_one (s : ℝ) (z : St) : |chiG2 s z| ≤ 1 := by
  rw [chiG2, abs_mul]
  calc |(cs : ℝ → ℝ) s| * |(cz2 : ℝ → ℝ) (wsq s z)| ≤ 1 * 1 :=
        mul_le_mul (abs_cs_le_one s) (abs_cz2_le_one _) (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

lemma abs_chiT2_le_one (s σ : ℝ) (z : St) : |chiT2 s σ z| ≤ 1 := by
  rw [chiT2, abs_mul, abs_mul]
  calc |(cs : ℝ → ℝ) s| * |(cs : ℝ → ℝ) σ| * |(cz2 : ℝ → ℝ) (wsq σ z)| ≤ 1 * 1 * 1 :=
        mul_le_mul (mul_le_mul (abs_cs_le_one s) (abs_cs_le_one σ) (abs_nonneg _) (by norm_num))
          (abs_cz2_le_one _) (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

lemma chiG2_eq_one_of_sq_le {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight) {z : St}
    (hz : ‖z - baseState s‖ ≤ 1 / 100) : chiG2 s z = 1 := by
  have h0 : 0 ≤ wsq s z := wsq_nonneg s z
  have h1 : wsq s z ≤ 1 / 100 := by
    refine le_trans (wsq_le_four_mul_sq_norm s z) ?_
    nlinarith [norm_nonneg (z - baseState s)]
  rw [chiG2, cs_eq_one_of_mem hs, cz2_eq_one_of_le h1 h0, one_mul]

lemma chiG2_eq_zero_of_far {s : ℝ} {z : St} (hz : 2 / 5 ≤ ‖z - baseState s‖) :
    chiG2 s z = 0 := by
  have h1 : 4 / 25 ≤ wsq s z := by
    have := sq_norm_le_wsq s z
    nlinarith [norm_nonneg (z - baseState s)]
  rw [chiG2, cz2_eq_zero_of_le h1, mul_zero]

lemma chiT2_eq_zero_of_far {s σ : ℝ} {z : St} (hz : 2 / 5 ≤ ‖z - baseState σ‖) :
    chiT2 s σ z = 0 := by
  have h1 : 4 / 25 ≤ wsq σ z := by
    have := sq_norm_le_wsq σ z
    nlinarith [norm_nonneg (z - baseState σ)]
  rw [chiT2, cz2_eq_zero_of_le h1, mul_zero]

/-- The modified state data with the *smooth* state cut-off (used by the engine). -/
def GW2 (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : St) : St := chiG2 s z • Godd n h s z

/-- The modified `Θ` data with the *smooth* state cut-off (used by the engine). -/
def TW2 (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : St) : St :=
  chiT2 s σ z • (if s < σ then Theta n h s σ z else KernelExt.ThetaM n h s σ z)

end

end Work.OddVolterra.Window

