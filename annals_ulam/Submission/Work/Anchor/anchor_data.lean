import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Window.window_tail_glue
import Submission.Work.OddVolterra.KernelExt.JM_diag
import Submission.Work.OddVolterra.Existence.Godd_zero_diag
import Submission.Work.VolterraLong.Corollaries.Bump

/-!
# The modified data of the state-level anchor

The paper's odd Volterra system
`Godd n h s (Z s) = ∫_σ in s..1, Theta n h s σ (Z σ) dσ + Xi n h s`
is solved on the anchor window `[1/2, 19/20]` by the long-interval fixed-point engine
`Work.VolterraLong.volterra_long_exists_bump`.  The engine needs the data to be globally
continuous / Lipschitz / differentiable, which the paper's data is *not*: `Theta` is
discontinuous on the diagonal `σ = s`, and both `Godd` and `Theta` are wild for states far from
the base state.  Following `Work.OddVolterra.Existence.window2_data` we therefore replace the
data by

* `Gf  n h s z   := chiG s z • Godd n h s z`,
* `Thf n h s σ z := chiT s σ z • KernelExt.ThetaM n h s σ z` (the *manifest* smooth
  representative of `Theta`, which agrees with the paper's `Theta` for `σ > s`),
* `Xif n h s     := Xibase n s + cs s • (Xi n h s - Xi n 0 s)`,

with the cut-offs `cs` (in the slope variables), `cz` (in the state), and `Xibase n s` defined so
that the *base* identity `Gf n 0 s (baseState s) = ∫_σ in s..b, Thf n 0 s σ (baseState σ) dσ +
Xibase n s` holds by construction (this is the fix for the fact that the paper's identity is
false at `s = 1`, cf. `Work.OddVolterra/Existence/NOTES_anchor_assemble.md`).

On the window `[1/2, 19/20]` the cut-offs are `1`, and the state of a solution at level `≤ 1/100`
keeps `cz` at `1`, so the modified data agrees with the paper's data there.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.Anchor

open Work.OddVolterra

noncomputable section

/-- The left end of the anchor window. -/
def wl : ℝ := 1 / 2

/-- The right end of the anchor window: `1 - τ/2`. -/
def wr : ℝ := 19 / 20

lemma wl_eq : wl = 1 / 2 := rfl
lemma wr_eq : wr = 19 / 20 := rfl
lemma wl_pos : 0 < wl := by norm_num [wl]
lemma wl_le_wr : wl ≤ wr := by norm_num [wl, wr]
lemma wr_lt_one : wr < 1 := by norm_num [wr]
lemma wl_le_one : wl ≤ 1 := by norm_num [wl]
lemma one_sub_tau_lt_wr : 1 - tau < wr := by norm_num [wr, tau]

/-! ## The cut-offs -/

/-- The slope bump: `= 1` on `[1/2, 19/20]`, `= 0` off `(0.485, 0.965)`. -/
def cs : ContDiffBump (29 / 40 : ℝ) := ⟨9 / 40, 6 / 25, by norm_num, by norm_num⟩

/-- The state bump: `= 1` on `‖z‖ ≤ 1/5`, `= 0` for `‖z‖ ≥ 2/5`. -/
def cz : ContDiffBump (0 : ℝ) := ⟨1 / 5, 2 / 5, by norm_num, by norm_num⟩

lemma cs_rIn : cs.rIn = 9 / 40 := rfl
lemma cs_rOut : cs.rOut = 6 / 25 := rfl
lemma cz_rIn : cz.rIn = 1 / 5 := rfl
lemma cz_rOut : cz.rOut = 2 / 5 := rfl

lemma cs_eq_one {s : ℝ} (hs : |s - 29 / 40| ≤ 9 / 40) : (cs : ℝ → ℝ) s = 1 := by
  refine ContDiffBump.one_of_mem_closedBall cs ?_
  rw [cs_rIn, Metric.mem_closedBall, Real.dist_eq]
  simpa using hs

lemma cs_eq_zero {s : ℝ} (hs : 6 / 25 ≤ |s - 29 / 40|) : (cs : ℝ → ℝ) s = 0 := by
  refine ContDiffBump.zero_of_le_dist cs ?_
  rw [cs_rOut, Real.dist_eq]
  simpa using hs

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

/-- On the anchor window the slope cut-off is `1`. -/
lemma cs_eq_one_of_mem {s : ℝ} (hs : s ∈ Set.Icc wl wr) : (cs : ℝ → ℝ) s = 1 := by
  refine cs_eq_one ?_
  rw [abs_le]
  simp only [wl, wr] at hs
  constructor <;> linarith [hs.1, hs.2]

lemma cs_eq_zero_of_far {s : ℝ} (hs : s ∉ Set.Icc (0.485 : ℝ) (0.965 : ℝ)) :
    (cs : ℝ → ℝ) s = 0 := by
  refine cs_eq_zero ?_
  have h1 : s < 0.485 ∨ 0.965 < s := by
    rcases lt_or_ge s 0.485 with h | h
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge fun hc => hs ⟨h, hc⟩)
  rcases h1 with h | h
  · rw [abs_of_nonpos (by linarith : s - 29 / 40 ≤ 0)]; linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ s - 29 / 40)]; linarith

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

lemma chiG_eq_one_of_close {s : ℝ} (hs : s ∈ Set.Icc wl wr) {z : St}
    (hz : ‖z - baseState s‖ ≤ 1 / 5) : chiG s z = 1 := by
  rw [chiG, cs_eq_one_of_mem hs, cz_eq_one (by simpa using hz), one_mul]

lemma chiT_eq_one_of_close {s σ : ℝ} (hs : s ∈ Set.Icc wl wr) (hσ : σ ∈ Set.Icc wl wr)
    {z : St} (hz : ‖z - baseState σ‖ ≤ 1 / 5) : chiT s σ z = 1 := by
  rw [chiT, cs_eq_one_of_mem hs, cs_eq_one_of_mem hσ,
    cz_eq_one (by simpa using hz), one_mul, one_mul]

lemma chiT_eq_zero_of_far {s σ : ℝ} {z : St} (hz : 2 / 5 ≤ ‖z - baseState σ‖) :
    chiT s σ z = 0 := by
  rw [chiT, cz_eq_zero (by rw [abs_of_nonneg (norm_nonneg _)]; exact hz), mul_zero]

lemma chiG_eq_zero_of_far {s : ℝ} {z : St} (hz : 2 / 5 ≤ ‖z - baseState s‖) :
    chiG s z = 0 := by
  rw [chiG, cz_eq_zero (by rw [abs_of_nonneg (norm_nonneg _)]; exact hz), mul_zero]

/-- On the window, `chiT` is the state bump alone. -/
lemma chiT_eq_cz_of_mem {s σ : ℝ} (hs : s ∈ Set.Icc wl wr) (hσ : σ ∈ Set.Icc wl wr) (z : St) :
    chiT s σ z = (cz : ℝ → ℝ) (‖z - baseState σ‖) := by
  rw [chiT, cs_eq_one_of_mem hs, cs_eq_one_of_mem hσ, one_mul, one_mul]

lemma chiG_eq_cz_of_mem {s : ℝ} (hs : s ∈ Set.Icc wl wr) (z : St) :
    chiG s z = (cz : ℝ → ℝ) (‖z - baseState s‖) := by
  rw [chiG, cs_eq_one_of_mem hs, one_mul]

/-! ## The modified data -/

/-- The modified state data. -/
def Gf (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : St) : St := chiG s z • Godd n h s z

/-- The modified `Θ` data. -/
def Thf (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : St) : St :=
  chiT s σ z • Work.OddVolterra.KernelExt.ThetaM n h s σ z

/-- The base part of the modified source: the defect of the base state in the modified system at
`h = 0`, cut off to the window. -/
def Xibase (n : ℕ) (s : ℝ) : St :=
  (cs : ℝ → ℝ) s •
    (Gf n 0 s (baseState s) - ∫ σ in s..wr, Thf n 0 s σ (baseState σ))

/-- The modified source.

The first two terms are the standard perturbation of the source; the third is the *frozen tail*
correction.  With `Ξ h = Xi n h + ∫_σ in 19/20..1, 𝚯 n h (-) σ (baseState σ)` the perturbed
source is exactly the one for which the solution of the windowed system satisfies the paper's
system with the integral running up to `1`, while at `h = 0` the correction vanishes and the
`Xibase` term keeps the base identity true by construction.  (The tail integrand is the *uncut*
manifest `𝚯`, since the `σ`-cut-off `cs` vanishes beyond `0.965 > wr`.) -/
def Xif (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : St :=
  Xibase n s + (cs : ℝ → ℝ) s •
    ((Xi n h s - Xi n 0 s) +
      ∫ σ in wr..1, (Work.OddVolterra.KernelExt.ThetaM n h s σ (baseState σ) -
        Work.OddVolterra.KernelExt.ThetaM n 0 s σ (baseState σ)))

/-! ## The regions on which the manifest data is smooth, and the input package -/

/-- The region of the `(s,σ,state)` space on which the manifest `Θ` is smooth.  The `σ`-range is
wider than the `s`-range because the frozen tail `∫_σ in 19/20..1` is evaluated there. -/
def RegionT : Set (ℝ × ℝ × St) :=
  {p | p.1 ∈ Set.Ioo (481 / 1000 : ℝ) (97 / 100) ∧
    p.2.1 ∈ Set.Ioo (481 / 1000 : ℝ) (102 / 100) ∧
    ‖p.2.2 - baseState p.2.1‖ < 9 / 20}

/-- The region of the `(s,state)` space on which the paper's `Godd` is smooth. -/
def RegionG : Set (ℝ × St) :=
  {p | p.1 ∈ Set.Ioo (481 / 1000 : ℝ) (97 / 100) ∧ ‖p.2 - baseState p.1‖ < 9 / 20}

/-- The region of the slope line on which the paper's `Ξ` is smooth. -/
def RegionX : Set ℝ := Set.Ioo (481 / 1000 : ℝ) (97 / 100)

/-- **The estimates and regularity facts the anchor consumes.**  These are the contents of the
modules `Work.Anchor.Godd_close`, `Work.Anchor.ThetaM_close`, `Work.Anchor.Xi_close`,
`Work.Anchor.deriv_close`, `Work.Anchor.ThetaM_contDiffOn_wide`, `Work.Anchor.Godd_contDiffOn` and
`Work.Anchor.Xi_contDiffOn`; they are packaged here so that the assembly can be checked before
they are available. -/
structure AnchorInputs (n : ℕ) : Prop where
  /-- `Godd` is close to the unperturbed data, uniformly on the ball of radius `2/5` (the
  support of the state cut-off `chiG`); this is `Work.OddVolterra.Existence.aw_godd_close_ball`. -/
  godd_close : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ → ℝ,
      (∀ s : ℝ, |h s| ≤ δ) → (∀ s : ℝ, |deriv h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20 : ℝ), ∀ z : St,
        ‖z - baseState s‖ ≤ 2 / 5 →
        dist (Godd n h s z) (Godd n 0 s z) < ε
  /-- The manifest `Θ` is close to the unperturbed data. -/
  thetaM_close : ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      ∀ z ∈ Metric.closedBall (baseState σ) (1 / 2),
        ‖KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n 0 s σ z‖ ≤ C * δ
  /-- `Ξ` is close to the unperturbed source. -/
  xi_close : ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20 : ℝ),
        ‖Xi n h s - Xi n 0 s‖ ≤ C * δ
  /-- The differential of `Godd` is close to the linearisation at the base state. -/
  deriv_close : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20 : ℝ), ∀ z : St,
        ‖z - baseState s‖ ≤ 1 / 4 →
        ‖fderiv ℝ (fun w => Godd n h s w) z -
          fderiv ℝ (fun w => Godd n 0 s w) (baseState s)‖
          ≤ C₁ * ‖z - baseState s‖ + C₂ * δ
  /-- The manifest `Θ` is smooth on `RegionT`. -/
  thetaM_smooth : ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ × St => KernelExt.ThetaM n h p.1 p.2.1 p.2.2) RegionT
  /-- The paper's `Godd` is smooth on `RegionG`. -/
  godd_smooth : ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => Godd n h p.1 p.2) RegionG
  /-- The paper's `Ξ` is smooth on `RegionX`. -/
  xi_smooth : ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Xi n h s) RegionX

end

/-!
## Route for the engine instantiation (`Work.Anchor.engine_solution`)

* `hbase`: with `cs s = 1` on the window, `Xibase n s` is *defined* as the defect of
  `baseState` in the system `(Gf n 0, Thf n 0)`, so the engine's `hbase` holds by construction.
* `hA_spec`: `Gf n 0 s` agrees with `Godd n 0 s` on a neighbourhood of `baseState s` (`cs` is `1`
  and `cz` is locally constant there), so `fderiv (Gf n 0 s ·) (baseState s) =
  fderiv (Godd n 0 s ·) (baseState s)`; the latter family and its inverse norm bound are
  `Work.OddCurveB.Est.exists_linearization` with `a = wl`, `b = wr`.
* global `Continuous`/`Lipschitz`/`DifferentiableAt` of `Gf n h`, `Thf n h`: from the `C^∞`
  smoothness of the assembled data, which is the generic lemma
  "if `χ` is `C^∞` and vanishes off a closed `K ⊆ U` with `F` of class `C^∞` on the open `U`, then
  `χ • F` is `C^∞`", applied with `F = Godd n h` / `KernelExt.ThetaM n h` / `Xi n h` and the
  regions `RegionG`, `RegionT`, `RegionX` (this is what the `*_smooth` fields of
  `AnchorInputs` are for).  The Lipschitz constant of `Thf n h` in the state on the square is then
  `ContDiffOn.exists_lipschitzOnWith` on a large closed ball.
* `hΘc`: on the ball of radius `1/2` around `baseState σ` use `thetaM_close`; outside it `chiT`
  vanishes.
* `hGc`: `godd_close` and `|chiG| ≤ 1`.
* `hΞc`: `xi_close` (the `Xibase` terms cancel).
* `hder`: for `‖z - baseState s‖ < 1/4` the cut-off is locally constant, so
  `fderiv (Gf n h s) z = fderiv (Godd n h s) z` and `deriv_close` applies; for the remaining `z`
  in the ball of radius `1`, use a uniform bound on `‖fderiv (Gf n h s) z‖` (from the `C^∞`
  smoothness) and take `Cg` large.
* the smallness conditions on the engine's `ε` are met by the smallness of the `ε` of the
  conclusion, and `2 B (2 + (b-a)) e^{(4BL+1)(b-a)} ε ≤ 1/100`.
* the `C^∞` smoothness of the solution `Z` is
  `Commons.Analysis.Calculus.contDiffOn_of_continuous_volterra_fixedPoint`; its
  `hG_partial_inv` input follows from the injectivity modulus of `Godd n h s` on the ball of
  radius `1/2` (`Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat`), which
  makes `fderiv (Godd n h s) (Z s)` injective, hence (finite dimension) invertible.
-/

end Work.Anchor
