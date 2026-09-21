import Mathlib
import Submission.Work.Anchor.anchor_data

/-!
# The clamped data of the anchor engine

`Work.Anchor.engine_solution` runs the long-interval Volterra engine
`Work.VolterraLong.volterra_long_exists_eps` on the anchor window `[wl, wr] = [1/2, 19/20]`.

The paper's data `Gf`, `Thf` is only *locally* smooth, and the derivative of `Godd` is controlled
by `AnchorInputs.deriv_close` only on the ball of radius `1/4`.  We therefore replace the state
bump `cz (‖z - baseState s‖)` by a **product of coordinate bumps**:

`eng_phi` is a bump on `ℝ` with `rIn = 1/25`, `rOut = 1/4`, and

* `eng_chiG s z = cs s * ∏ i, eng_phi (z i - baseState s i)`,
* `eng_chiT s σ z = cs s * cs σ * ∏ i, eng_phi (z i - baseState σ i)`.

Because the number of coordinates is `4` and the sup-norm ball of radius `r` in `St = Fin 4 → ℝ`
is exactly the box `{z | ∀ i, |z i - baseState s i| ≤ r}`, this is a genuine radial cut-off in the
sup norm: it equals `1` on the ball of radius `1/25`, and it vanishes *together with all its
directional derivatives* strictly outside the ball of radius `1/4` (the first partial derivative
of a product of bumps with one factor at its outer radius `1/4` vanishes).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.Anchor

open Work.OddVolterra

noncomputable section

/-! ## The coordinate bump -/

/-- The one-dimensional bump of the clamped data: `1` on `|w| ≤ 1/25`, `0` for `|w| ≥ 1/4`. -/
def eng_phi : ContDiffBump (0 : ℝ) := ⟨1 / 25, 1 / 4, by norm_num, by norm_num⟩

lemma eng_phi_rIn : eng_phi.rIn = 1 / 25 := rfl
lemma eng_phi_rOut : eng_phi.rOut = 1 / 4 := rfl

lemma eng_phi_eq_one {r : ℝ} (hr : |r| ≤ 1 / 25) : (eng_phi : ℝ → ℝ) r = 1 := by
  refine ContDiffBump.one_of_mem_closedBall eng_phi ?_
  rw [eng_phi_rIn, Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact hr

lemma eng_phi_eq_zero {r : ℝ} (hr : 1 / 4 ≤ |r|) : (eng_phi : ℝ → ℝ) r = 0 := by
  refine ContDiffBump.zero_of_le_dist eng_phi ?_
  rw [eng_phi_rOut, Real.dist_eq, sub_zero]
  exact hr

lemma eng_phi_nonneg (r : ℝ) : 0 ≤ (eng_phi : ℝ → ℝ) r := ContDiffBump.nonneg eng_phi
lemma eng_phi_le_one (r : ℝ) : (eng_phi : ℝ → ℝ) r ≤ 1 := ContDiffBump.le_one eng_phi

lemma abs_eng_phi_le_one (r : ℝ) : |(eng_phi : ℝ → ℝ) r| ≤ 1 := by
  rw [abs_of_nonneg (eng_phi_nonneg r)]; exact eng_phi_le_one r

/-! ## The clamped data -/

/-- The state factor of the clamped `Godd` datum. -/
def eng_chiG (s : ℝ) (z : St) : ℝ :=
  (cs : ℝ → ℝ) s * ∏ i : Fin 4, (eng_phi : ℝ → ℝ) (z i - baseState s i)

/-- The state factor of the clamped `ThetaM` datum. -/
def eng_chiT (s σ : ℝ) (z : St) : ℝ :=
  (cs : ℝ → ℝ) s * (cs : ℝ → ℝ) σ *
    ∏ i : Fin 4, (eng_phi : ℝ → ℝ) (z i - baseState σ i)

/-- The clamped state data. -/
def eng_G (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : St) : St := eng_chiG s z • Godd n h s z

/-- The clamped `Θ` data. -/
def eng_Theta (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : St) : St :=
  eng_chiT s σ z • KernelExt.ThetaM n h s σ z

/-! ## Elementary norm facts -/

lemma coord_le_of_norm_le {x : St} {r : ℝ} (h : ‖x‖ ≤ r) (i : Fin 4) : |x i| ≤ r := by
  have h1 := norm_le_pi_norm x i
  rw [Real.norm_eq_abs] at h1
  exact le_trans h1 h

lemma norm_le_of_coord_le {x : St} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, |x i| ≤ r) : ‖x‖ ≤ r := by
  rw [pi_norm_le_iff_of_nonneg hr]
  intro i
  rw [Real.norm_eq_abs]
  exact h i

/-- If the product of the coordinate bumps does not vanish, the state lies in the ball of
radius `1/4`. -/
lemma norm_le_of_prod_eng_phi_ne_zero {x : St}
    (h : ∏ i : Fin 4, (eng_phi : ℝ → ℝ) (x i) ≠ 0) : ‖x‖ ≤ 1 / 4 := by
  refine norm_le_of_coord_le (by norm_num) (fun i => ?_)
  by_contra hc
  push Not at hc
  exact h (Finset.prod_eq_zero (Finset.mem_univ i) (eng_phi_eq_zero (le_of_lt hc)))

/-- Strictly outside the ball of radius `1/4` the product of the coordinate bumps vanishes. -/
lemma prod_eng_phi_eq_zero_of_lt {x : St} (h : 1 / 4 < ‖x‖) :
    ∏ i : Fin 4, (eng_phi : ℝ → ℝ) (x i) = 0 := by
  by_contra hc
  exact absurd (norm_le_of_prod_eng_phi_ne_zero hc) (not_le.mpr h)

lemma abs_prod_eng_phi_le_one (z : St) :
    |∏ i : Fin 4, (eng_phi : ℝ → ℝ) (z i)| ≤ 1 := by
  rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => eng_phi_nonneg _))]
  exact Finset.prod_le_one₀ (fun i _ => eng_phi_nonneg _) (fun i _ => eng_phi_le_one _)

lemma abs_eng_chiG_le_one (s : ℝ) (z : St) : |eng_chiG s z| ≤ 1 := by
  rw [eng_chiG, abs_mul]
  calc |(cs : ℝ → ℝ) s| * |∏ i : Fin 4, (eng_phi : ℝ → ℝ) (z i - baseState s i)| ≤ 1 * 1 :=
        mul_le_mul (abs_cs_le_one s) (abs_prod_eng_phi_le_one _) (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

lemma abs_eng_chiT_le_one (s σ : ℝ) (z : St) : |eng_chiT s σ z| ≤ 1 := by
  rw [eng_chiT, abs_mul, abs_mul]
  calc |(cs : ℝ → ℝ) s| * |(cs : ℝ → ℝ) σ|
        * |∏ i : Fin 4, (eng_phi : ℝ → ℝ) (z i - baseState σ i)| ≤ 1 * 1 * 1 :=
        mul_le_mul (mul_le_mul (abs_cs_le_one s) (abs_cs_le_one σ) (abs_nonneg _) (by norm_num))
          (abs_prod_eng_phi_le_one _) (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

/-! ## The clamped factors -/

/-- On the sup-norm ball of radius `1/25` the clamped factor is the slope bump alone. -/
lemma eng_chiG_eq_of_le {s : ℝ} {z : St} (hz : ‖z - baseState s‖ ≤ 1 / 25) :
    eng_chiG s z = (cs : ℝ → ℝ) s := by
  rw [eng_chiG]
  have h1 : ∏ i : Fin 4, (eng_phi : ℝ → ℝ) (z i - baseState s i) = 1 := by
    refine Finset.prod_eq_one (fun i _ => ?_)
    refine eng_phi_eq_one ?_
    have h2 := coord_le_of_norm_le hz i
    rw [Pi.sub_apply] at h2
    exact le_trans h2 (by norm_num)
  rw [h1, mul_one]

/-- On the sup-norm ball of radius `1/25` the clamped `Θ` factor is the slope bumps alone. -/
lemma eng_chiT_eq_of_le {s σ : ℝ} {z : St} (hz : ‖z - baseState σ‖ ≤ 1 / 25) :
    eng_chiT s σ z = (cs : ℝ → ℝ) s * (cs : ℝ → ℝ) σ := by
  rw [eng_chiT]
  have h1 : ∏ i : Fin 4, (eng_phi : ℝ → ℝ) (z i - baseState σ i) = 1 := by
    refine Finset.prod_eq_one (fun i _ => ?_)
    refine eng_phi_eq_one ?_
    have h2 := coord_le_of_norm_le hz i
    rw [Pi.sub_apply] at h2
    exact le_trans h2 (by norm_num)
  rw [h1, mul_one]

/-- Strictly outside the sup-norm ball of radius `1/4` the clamped `Godd` factor vanishes. -/
lemma eng_chiG_eq_zero {s : ℝ} {z : St} (hz : 1 / 4 < ‖z - baseState s‖) :
    eng_chiG s z = 0 := by
  rw [eng_chiG]
  have h3 : ∏ j : Fin 4, (eng_phi : ℝ → ℝ) (z j - baseState s j) = 0 := by
    simpa only [Pi.sub_apply] using prod_eng_phi_eq_zero_of_lt (x := z - baseState s) hz
  rw [h3, mul_zero]

/-- Strictly outside the sup-norm ball of radius `1/4` the clamped `Θ` factor vanishes. -/
lemma eng_chiT_eq_zero {s σ : ℝ} {z : St} (hz : 1 / 4 < ‖z - baseState σ‖) :
    eng_chiT s σ z = 0 := by
  rw [eng_chiT]
  have h3 : ∏ j : Fin 4, (eng_phi : ℝ → ℝ) (z j - baseState σ j) = 0 := by
    simpa only [Pi.sub_apply] using prod_eng_phi_eq_zero_of_lt (x := z - baseState σ) hz
  simp [h3]

lemma eng_Theta_eq_zero_of_lt {n : ℕ} {h : ℝ → ℝ} {s σ : ℝ} {z : St}
    (hz : 1 / 4 < ‖z - baseState σ‖) : eng_Theta n h s σ z = 0 := by
  rw [eng_Theta, eng_chiT_eq_zero hz, zero_smul]

lemma eng_G_eq_zero_of_lt {n : ℕ} {h : ℝ → ℝ} {s : ℝ} {z : St}
    (hz : 1 / 4 < ‖z - baseState s‖) : eng_G n h s z = 0 := by
  rw [eng_G, eng_chiG_eq_zero hz, zero_smul]

/-- On the ball of radius `1/50` the clamped data agrees with the paper's `Gf`. -/
lemma eng_G_eq_Gf {n : ℕ} {h : ℝ → ℝ} {s : ℝ} {z : St}
    (hz : ‖z - baseState s‖ ≤ 1 / 50) :
    eng_G n h s z = Gf n h s z := by
  have h1 : ‖z - baseState s‖ ≤ 1 / 25 := le_trans hz (by norm_num)
  have h2 : (cz : ℝ → ℝ) ‖z - baseState s‖ = 1 :=
    cz_eq_one (by rw [abs_of_nonneg (norm_nonneg _)]; linarith)
  rw [eng_G, eng_chiG_eq_of_le h1, Gf, chiG, h2, mul_one]

/-- On the ball of radius `1/50` the clamped data agrees with the paper's `Thf`. -/
lemma eng_Theta_eq_Thf {n : ℕ} {h : ℝ → ℝ} {s σ : ℝ} {z : St}
    (hz : ‖z - baseState σ‖ ≤ 1 / 50) :
    eng_Theta n h s σ z = Thf n h s σ z := by
  have h1 : ‖z - baseState σ‖ ≤ 1 / 25 := le_trans hz (by norm_num)
  have h2 : (cz : ℝ → ℝ) ‖z - baseState σ‖ = 1 :=
    cz_eq_one (by rw [abs_of_nonneg (norm_nonneg _)]; linarith)
  rw [eng_Theta, eng_chiT_eq_of_le h1, Thf, chiT, h2, mul_one]

/-! ## Regularity of the base state -/

lemma contDiff_profileX_eng : ContDiff ℝ (⊤ : ℕ∞) Commons.Geometry.Ulam.profileX := by
  unfold Commons.Geometry.Ulam.profileX
  apply ContDiff.div
  · exact contDiff_const
  · apply ContDiff.sqrt
    · fun_prop
    · intro x; positivity
  · intro x; exact ne_of_gt (Real.sqrt_pos_of_pos (by positivity))

lemma contDiff_deriv_profileX_eng :
    ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => deriv Commons.Geometry.Ulam.profileX s) := by
  have h := ContDiff.iterate_deriv (𝕜 := ℝ) 1 contDiff_profileX_eng
  simpa [Function.iterate_one] using h

lemma contDiff_baseState_eng : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => baseState s) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · simpa [baseState] using contDiff_profileX_eng
  · simpa [baseState] using contDiff_profileX_eng
  · simpa [baseState] using contDiff_deriv_profileX_eng
  · simpa [baseState] using contDiff_deriv_profileX_eng

lemma continuous_baseState_eng : Continuous (fun s : ℝ => baseState s) :=
  contDiff_baseState_eng.continuous

lemma continuousOn_baseState_Icc : ContinuousOn (fun s : ℝ => baseState s) (Set.Icc wl wr) :=
  continuous_baseState_eng.continuousOn

/-! ## The clamped cut-offs are globally smooth -/

lemma contDiff_eng_chiG_comp : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => eng_chiG p.1 p.2) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => (cs : ℝ → ℝ) p.1) :=
    (ContDiffBump.contDiff cs).comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × St => ∏ i : Fin 4, (eng_phi : ℝ → ℝ) (p.2 i - baseState p.1 i)) := by
    refine contDiff_prod (fun i _ => ?_)
    have hb : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => baseState p.1 i) :=
      (contDiff_apply ℝ _ i).comp (contDiff_baseState_eng.comp contDiff_fst)
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => p.2 i) :=
      (contDiff_apply ℝ _ i).comp contDiff_snd
    exact (ContDiffBump.contDiff eng_phi).comp (hc.sub hb)
  simpa only [eng_chiG] using h1.mul h2

lemma contDiff_eng_chiT_comp :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => eng_chiT p.1 p.2.1 p.2.2) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => (cs : ℝ → ℝ) p.1) :=
    (ContDiffBump.contDiff cs).comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => (cs : ℝ → ℝ) p.2.1) :=
    (ContDiffBump.contDiff cs).comp (contDiff_fst.comp contDiff_snd)
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × St => ∏ i : Fin 4, (eng_phi : ℝ → ℝ) (p.2.2 i - baseState p.2.1 i)) := by
    refine contDiff_prod (fun i _ => ?_)
    have hb : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => baseState p.2.1 i) :=
      (contDiff_apply ℝ _ i).comp (contDiff_baseState_eng.comp (contDiff_fst.comp contDiff_snd))
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => p.2.2 i) :=
      (contDiff_apply ℝ _ i).comp (contDiff_snd.comp contDiff_snd)
    exact (ContDiffBump.contDiff eng_phi).comp (hc.sub hb)
  simpa only [eng_chiT, mul_assoc] using h1.mul (h2.mul h3)

/-! ## The cut-off supports lie strictly inside the good regions -/

lemma isOpen_RegionG : IsOpen RegionG := by
  have h1 : IsOpen {p : ℝ × St | (481 : ℝ) / 1000 < p.1} :=
    isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {p : ℝ × St | p.1 < (97 : ℝ) / 100} :=
    isOpen_lt continuous_fst continuous_const
  have h3 : IsOpen {p : ℝ × St | ‖p.2 - baseState p.1‖ < (9 : ℝ) / 20} :=
    isOpen_lt (continuous_norm.comp (continuous_snd.sub
      (continuous_baseState_eng.comp continuous_fst))) continuous_const
  convert (h1.inter h2).inter h3 using 1
  ext p
  simp [RegionG, Set.mem_Ioo]

lemma isOpen_RegionT : IsOpen RegionT := by
  have h1 : IsOpen {p : ℝ × ℝ × St | (481 : ℝ) / 1000 < p.1} :=
    isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {p : ℝ × ℝ × St | p.1 < (97 : ℝ) / 100} :=
    isOpen_lt continuous_fst continuous_const
  have h3 : IsOpen {p : ℝ × ℝ × St | (481 : ℝ) / 1000 < p.2.1} :=
    isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
  have h4 : IsOpen {p : ℝ × ℝ × St | p.2.1 < (102 : ℝ) / 100} :=
    isOpen_lt (continuous_fst.comp continuous_snd) continuous_const
  have h5 : IsOpen {p : ℝ × ℝ × St | ‖p.2.2 - baseState p.2.1‖ < (9 : ℝ) / 20} :=
    isOpen_lt (continuous_norm.comp (continuous_snd.comp continuous_snd |>.sub
      (continuous_baseState_eng.comp (continuous_fst.comp continuous_snd)))) continuous_const
  convert ((h1.inter h2).inter (h3.inter h4)).inter h5 using 1
  ext p
  simp [RegionT, Set.mem_Ioo, and_assoc]

lemma tsupport_eng_chiG_subset : tsupport (fun p : ℝ × St => eng_chiG p.1 p.2) ⊆ RegionG := by
  have hclosed : IsClosed {p : ℝ × St |
      |p.1 - 29 / 40| ≤ 6 / 25 ∧ ‖p.2 - baseState p.1‖ ≤ 1 / 4} := by
    refine IsClosed.inter ?_ ?_
    · exact isClosed_le ((continuous_abs.comp (continuous_fst.sub continuous_const)))
        continuous_const
    · exact isClosed_le (continuous_norm.comp
        (continuous_snd.sub (continuous_baseState_eng.comp continuous_fst))) continuous_const
  have hsub : Function.support (fun p : ℝ × St => eng_chiG p.1 p.2) ⊆
      {p : ℝ × St | |p.1 - 29 / 40| ≤ 6 / 25 ∧ ‖p.2 - baseState p.1‖ ≤ 1 / 4} := by
    intro p hp
    have hp' : eng_chiG p.1 p.2 ≠ 0 := hp
    have hp1 : (cs : ℝ → ℝ) p.1 ≠ 0 := by
      intro h0
      exact hp' (by rw [eng_chiG, h0, zero_mul])
    have hp2 : ∏ i : Fin 4, (eng_phi : ℝ → ℝ) (p.2 i - baseState p.1 i) ≠ 0 := by
      intro h0
      exact hp' (by rw [eng_chiG, h0, mul_zero])
    refine ⟨?_, ?_⟩
    · by_contra h
      push Not at h
      exact hp1 (cs_eq_zero (le_of_lt h))
    · exact norm_le_of_prod_eng_phi_ne_zero (by
        simpa only [Pi.sub_apply] using hp2)
  intro p hp
  have hp' := closure_minimal hsub hclosed hp
  simp only [Set.mem_setOf_eq] at hp'
  exact ⟨⟨by linarith [abs_le.mp hp'.1], by linarith [abs_le.mp hp'.1]⟩,
    by linarith [hp'.2]⟩

lemma tsupport_eng_chiT_subset :
    tsupport (fun p : ℝ × ℝ × St => eng_chiT p.1 p.2.1 p.2.2) ⊆ RegionT := by
  have hclosed : IsClosed {p : ℝ × ℝ × St |
      |p.1 - 29 / 40| ≤ 6 / 25 ∧ |p.2.1 - 29 / 40| ≤ 6 / 25 ∧
        ‖p.2.2 - baseState p.2.1‖ ≤ 1 / 4} := by
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_le ((continuous_abs.comp (continuous_fst.sub continuous_const)))
        continuous_const
    · exact isClosed_le ((continuous_abs.comp ((continuous_fst.comp continuous_snd).sub
        continuous_const))) continuous_const
    · exact isClosed_le (continuous_norm.comp
        ((continuous_snd.comp continuous_snd).sub (continuous_baseState_eng.comp
          (continuous_fst.comp continuous_snd)))) continuous_const
  have hsub : Function.support (fun p : ℝ × ℝ × St => eng_chiT p.1 p.2.1 p.2.2) ⊆
      {p : ℝ × ℝ × St | |p.1 - 29 / 40| ≤ 6 / 25 ∧ |p.2.1 - 29 / 40| ≤ 6 / 25 ∧
        ‖p.2.2 - baseState p.2.1‖ ≤ 1 / 4} := by
    intro p hp
    have hp' : eng_chiT p.1 p.2.1 p.2.2 ≠ 0 := hp
    have hp1 : (cs : ℝ → ℝ) p.1 * (cs : ℝ → ℝ) p.2.1 ≠ 0 := by
      intro h0
      exact hp' (by rw [eng_chiT, h0, zero_mul])
    have hp2 : ∏ i : Fin 4, (eng_phi : ℝ → ℝ) (p.2.2 i - baseState p.2.1 i) ≠ 0 := by
      intro h0
      exact hp' (by rw [eng_chiT, mul_assoc, h0, mul_zero, mul_zero])
    obtain ⟨hcs, hcs'⟩ := mul_ne_zero_iff.mp hp1
    refine ⟨?_, ?_, ?_⟩
    · by_contra h
      push Not at h
      exact hcs (cs_eq_zero (le_of_lt h))
    · by_contra h
      push Not at h
      exact hcs' (cs_eq_zero (le_of_lt h))
    · exact norm_le_of_prod_eng_phi_ne_zero (by
        simpa only [Pi.sub_apply] using hp2)
  intro p hp
  have hp' := closure_minimal hsub hclosed hp
  simp only [Set.mem_setOf_eq] at hp'
  refine ⟨⟨by linarith [abs_le.mp hp'.1], by linarith [abs_le.mp hp'.1]⟩,
    ⟨by linarith [abs_le.mp hp'.2.1], by linarith [abs_le.mp hp'.2.1]⟩,
    by linarith [hp'.2.2]⟩

/-! ## Gluing a cut-off with a function smooth on a neighbourhood of its support -/

/-- If `f` is a cut-off whose support lies in an open set `U` on which `g` is `C^∞`, then the
product `f • g` is `C^∞` everywhere. -/
lemma eng_contDiff_smul_of_contDiffOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → ℝ} {g : X → E} {U : Set X} (hU : IsOpen U)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (hsub : tsupport f ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => f x • g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport f := fun h => hx (hsub h)
    have hmem : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx'
    refine (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with y hy
    have hy' : f y = 0 := by
      by_contra h
      exact hy (subset_tsupport f (Function.mem_support.mpr h))
    rw [hy', zero_smul]

/-! ## Global smoothness of the clamped data -/

/-- The clamped state data is globally `C^∞`. -/
theorem contDiff_eng_G (n : ℕ) (hn : 1 ≤ n) (H : AnchorInputs n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => eng_G n h p.1 p.2) := by
  have h := eng_contDiff_smul_of_contDiffOn (f := fun p : ℝ × St => eng_chiG p.1 p.2)
    (g := fun p : ℝ × St => Godd n h p.1 p.2) (U := RegionG) isOpen_RegionG
    contDiff_eng_chiG_comp (H.godd_smooth h hh hsmall) tsupport_eng_chiG_subset
  simpa only [eng_G] using h

/-- The clamped `Θ` data is globally `C^∞`. -/
theorem contDiff_eng_Theta (n : ℕ) (hn : 1 ≤ n) (H : AnchorInputs n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × St => eng_Theta n h p.1 p.2.1 p.2.2) := by
  have h := eng_contDiff_smul_of_contDiffOn
    (f := fun p : ℝ × ℝ × St => eng_chiT p.1 p.2.1 p.2.2)
    (g := fun p : ℝ × ℝ × St => KernelExt.ThetaM n h p.1 p.2.1 p.2.2) (U := RegionT)
    isOpen_RegionT contDiff_eng_chiT_comp (H.thetaM_smooth h hh hsmall) tsupport_eng_chiT_subset
  simpa only [eng_Theta] using h

end

end Work.Anchor
