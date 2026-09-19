import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Schwarz
import Submission.Commons.Analysis.Complex.rectIntegral_sub_inv_outside

noncomputable section

open Complex Metric Set Filter
open scoped ComplexConjugate Topology

namespace Commons.Analysis.Complex

namespace spick

/-- Classical automorphism of the unit disc: `c ↦ 0`, `0 ↦ c`, an involution of `𝔻`. -/
def discAut (c : ℂ) : ℂ → ℂ := fun w => (c - w) / (1 - conj c * w)

lemma discAut_normSq (c w : ℂ) :
    normSq (discAut c w) = (normSq c + normSq w - 2 * (c * conj w).re) /
      (1 + normSq c * normSq w - 2 * (c * conj w).re) := by
  unfold discAut
  rw [normSq_div]
  congr 1
  · rw [normSq_sub]
  · rw [normSq_sub (1) (conj c * w)]
    simp

lemma conj_mul_norm_lt_one {c x : ℂ} (hc : ‖c‖ < 1) (hx : ‖x‖ ≤ 1) : ‖conj c * x‖ < 1 := by
  calc ‖conj c * x‖ = ‖c‖ * ‖x‖ := by rw [norm_mul, Complex.norm_conj]
    _ < 1 := by
      have hc0 : 0 ≤ ‖c‖ := norm_nonneg c
      have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
      nlinarith

lemma den_normSq_pos {c w : ℂ} (hc : ‖c‖ < 1) (hw : ‖w‖ ≤ 1) :
    0 < 1 + normSq c * normSq w - 2 * (c * conj w).re := by
  have hden : 1 + normSq c * normSq w - 2 * (c * conj w).re = normSq (1 - conj c * w) := by
    rw [normSq_sub (1) (conj c * w)]
    simp
  rw [hden]
  exact Complex.normSq_pos.mpr (by
    intro hz
    have hn : ‖conj c * w‖ < 1 := conj_mul_norm_lt_one hc hw
    have h_eq : conj c * w = 1 := (sub_eq_zero.mp hz).symm
    have h_eq_norm : ‖conj c * w‖ = (1 : ℝ) := by rw [h_eq]; norm_num
    linarith)

lemma norm_le_one {c w : ℂ} (hc : ‖c‖ < 1) (hw : ‖w‖ ≤ 1) :
    ‖discAut c w‖ ≤ 1 := by
  have hnum_le_den : normSq c + normSq w - 2 * (c * conj w).re ≤
      1 + normSq c * normSq w - 2 * (c * conj w).re := by
    have hA : normSq c ≤ 1 := by
      have hc0 : 0 ≤ ‖c‖ := norm_nonneg c
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_le_one_iff_abs_le_one _).2 (by simpa [abs_of_nonneg hc0] using le_of_lt hc)
    have hB : normSq w ≤ 1 := by
      have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_le_one_iff_abs_le_one _).2 (by simpa [abs_of_nonneg hw0] using hw)
    have hprod : 0 ≤ (1 - normSq c) * (1 - normSq w) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have h1 : normSq (discAut c w) ≤ 1 := by
    rw [discAut_normSq]
    exact (div_le_one (den_normSq_pos hc hw)).mpr hnum_le_den
  have hsq : ‖discAut c w‖ ^ 2 ≤ 1 ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa using h1
  exact le_of_sq_le_sq hsq (by norm_num)

lemma norm_lt_one {c w : ℂ} (hc : ‖c‖ < 1) (hw : ‖w‖ < 1) :
    ‖discAut c w‖ < 1 := by
  have hnum_lt_den : normSq c + normSq w - 2 * (c * conj w).re <
      1 + normSq c * normSq w - 2 * (c * conj w).re := by
    have hA1 : normSq c < 1 := by
      have hc0 : 0 ≤ ‖c‖ := norm_nonneg c
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_lt_one_iff_abs_lt_one _).2 (by simpa [abs_of_nonneg hc0] using hc)
    have hB1 : normSq w < 1 := by
      have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_lt_one_iff_abs_lt_one _).2 (by simpa [abs_of_nonneg hw0] using hw)
    have hprod : 0 < (1 - normSq c) * (1 - normSq w) := mul_pos (by linarith) (by linarith)
    nlinarith
  have h1 : normSq (discAut c w) < 1 := by
    rw [discAut_normSq]
    exact (div_lt_one (den_normSq_pos hc (le_of_lt hw))).mpr hnum_lt_den
  have hsq : ‖discAut c w‖ ^ 2 < 1 ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa using h1
  simpa [abs_of_nonneg (norm_nonneg _)] using abs_lt_of_sq_lt_sq hsq (by norm_num)

lemma mapsTo_ball {c : ℂ} (hc : ‖c‖ < 1) :
    Set.MapsTo (discAut c) (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
  intro w hw
  rw [mem_ball_zero_iff] at hw ⊢
  exact norm_lt_one hc hw

lemma mapsTo_closedBall {c : ℂ} (hc : ‖c‖ < 1) :
    Set.MapsTo (discAut c) (Metric.closedBall (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1) := by
  intro w hw
  rw [mem_closedBall_zero_iff] at hw ⊢
  exact norm_le_one hc hw

lemma den_ne_zero {c x : ℂ} (hc : ‖c‖ < 1) (hx : ‖x‖ ≤ 1) : 1 - conj c * x ≠ 0 := by
  intro hz
  have hn := conj_mul_norm_lt_one hc hx
  have h_eq : conj c * x = 1 := (sub_eq_zero.mp hz).symm
  have h_eq_norm : ‖conj c * x‖ = (1 : ℝ) := by rw [h_eq]; norm_num
  linarith

lemma deriv_formula (c x : ℂ) (hx : 1 - conj c * x ≠ 0) :
    deriv (discAut c) x = ((normSq c - 1 : ℂ)) / (1 - conj c * x) ^ 2 := by
  unfold discAut
  change deriv ((fun w : ℂ => c - w) / (fun w : ℂ => 1 - conj c * w)) x =
    ((normSq c - 1 : ℂ)) / (1 - conj c * x) ^ 2
  rw [deriv_div]
  · have hnum : deriv (fun w : ℂ => c - w) x = -1 := by simp
    have hdenv : deriv (fun w : ℂ => 1 - conj c * w) x = -conj c := by simp
    rw [hnum, hdenv]
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  · fun_prop
  · fun_prop
  · exact hx

lemma differentiableAt (c x : ℂ) (hx : 1 - conj c * x ≠ 0) :
    DifferentiableAt ℂ (discAut c) x := by
  unfold discAut
  change DifferentiableAt ℂ ((fun w : ℂ => c - w) / (fun w : ℂ => 1 - conj c * w)) x
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact hx

lemma differentiableOn_ball {c : ℂ} (hc : ‖c‖ < 1) :
    DifferentiableOn ℂ (discAut c) (ball (0 : ℂ) 1) := by
  intro x hx
  rw [mem_ball_zero_iff] at hx
  exact (differentiableAt c x (den_ne_zero hc (le_of_lt hx))).differentiableWithinAt

lemma differentiableOn_closedBall {c : ℂ} (hc : ‖c‖ < 1) :
    DifferentiableOn ℂ (discAut c) (closedBall (0 : ℂ) 1) := by
  intro x hx
  rw [mem_closedBall_zero_iff] at hx
  exact (differentiableAt c x (den_ne_zero hc hx)).differentiableWithinAt

lemma hasDerivAt (c x : ℂ) (hx : 1 - conj c * x ≠ 0) :
    HasDerivAt (discAut c) (((normSq c - 1 : ℂ)) / (1 - conj c * x) ^ 2) x := by
  rw [← deriv_formula c x hx]
  exact (differentiableAt c x hx).hasDerivAt

lemma zero (c : ℂ) : discAut c 0 = c := by
  unfold discAut
  simp

lemma at_self (c : ℂ) : discAut c c = 0 := by
  unfold discAut
  simp

lemma normSq_lt_one_iff_norm {c : ℂ} : normSq c < 1 ↔ ‖c‖ < 1 := by
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    have h0 : 0 ≤ ‖c‖ := norm_nonneg c
    exact (abs_lt.mp ((sq_lt_one_iff_abs_lt_one ‖c‖).mp h)).2
  · intro h
    have h0 : 0 ≤ ‖c‖ := norm_nonneg c
    exact (sq_lt_one_iff_abs_lt_one ‖c‖).2 (by simpa [abs_of_nonneg h0] using h)

/-- norm of `(r : ℂ)` when `0 ≤ r` -/
lemma cnorm_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ = r := Complex.norm_of_nonneg hr

lemma cnorm_one_sub_normSq {b : ℂ} (hb : normSq b < 1) : ‖((1 - normSq b : ℝ) : ℂ)‖ = 1 - normSq b := by
  rw [Complex.norm_real]
  simpa [Real.norm_eq_abs] using (abs_of_nonneg (sub_nonneg.mpr (le_of_lt hb)) : |1 - normSq b| = 1 - normSq b)

lemma cnorm_normSq_sub_one {b : ℂ} (hb : normSq b < 1) : ‖((normSq b - 1 : ℝ) : ℂ)‖ = 1 - normSq b := by
  rw [Complex.norm_real]
  rw [Real.norm_eq_abs]
  rw [abs_of_neg (sub_neg.mpr hb)]
  ring

lemma one_sub_conj_mul (b : ℂ) : 1 - conj b * b = ((1 - normSq b : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self]
  norm_num

lemma norm_derivVal {b : ℂ} (hb : normSq b < 1) :
    ‖(((normSq b - 1 : ℂ)) / (1 - conj b * b) ^ 2)‖ = 1 / (1 - normSq b) := by
  rw [norm_div]
  have h1 : ‖(normSq b - 1 : ℂ)‖ = 1 - normSq b := by
    simpa using cnorm_normSq_sub_one hb
  have h3 : ‖(1 - conj b * b) ^ 2‖ = ‖(1 - conj b * b)‖ ^ 2 := by simp
  have h2 : ‖(1 - conj b * b) ^ 2‖ = (1 - normSq b) ^ 2 := by
    rw [h3, one_sub_conj_mul b, cnorm_one_sub_normSq hb]
  rw [h1, h2]
  field_simp [sub_ne_zero.mpr (ne_of_gt (sub_pos.mpr hb))]

end spick

/-- **Schwarz–Pick lemma**: a holomorphic self-map of the unit disc is a contraction for the
Poincaré metric; in derivative form at `z`:
`‖g'(z)‖ ≤ (1 - ‖g z‖²)/(1 - ‖z‖²)`. -/
theorem schwarzPick_norm_deriv {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1))
    (hgball : Set.MapsTo g (Metric.ball (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1))
    (hz : z ∈ Metric.ball (0 : ℂ) 1) (hgz : ‖g z‖ < 1) :
    ‖deriv g z‖ ≤ (1 - ‖g z‖ ^ 2) / (1 - ‖z‖ ^ 2) := by
  let M : ℂ → ℂ := spick.discAut z
  let N : ℂ → ℂ := spick.discAut (g z)
  let F : ℂ → ℂ := N ∘ g ∘ M
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hM_diff : DifferentiableOn ℂ M (ball (0 : ℂ) 1) := spick.differentiableOn_ball hz'
  have hM_ball : Set.MapsTo M (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := spick.mapsTo_ball hz'
  have hgM_diff : DifferentiableOn ℂ (g ∘ M) (ball (0 : ℂ) 1) :=
    DifferentiableOn.comp hg hM_diff hM_ball
  have hgM_closed : Set.MapsTo (g ∘ M) (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) :=
    hgball.comp hM_ball
  have hN_diff : DifferentiableOn ℂ N (closedBall (0 : ℂ) 1) :=
    spick.differentiableOn_closedBall hgz
  have hN_closed : Set.MapsTo N (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) :=
    spick.mapsTo_closedBall hgz
  have hF_diff : DifferentiableOn ℂ F (ball (0 : ℂ) 1) := by
    dsimp [F]
    exact DifferentiableOn.comp hN_diff hgM_diff hgM_closed
  have hF_maps : Set.MapsTo F (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    dsimp [F]
    exact hN_closed.comp hgM_closed
  have hF0 : F 0 = 0 := by
    dsimp [F, M, N]
    simp [spick.discAut]
  have hF_bound : ‖deriv F 0‖ ≤ 1 := by
    have hmaps' : Set.MapsTo F (ball (0 : ℂ) 1) (closedBall (F 0) 1) := by
      simpa [hF0] using hF_maps
    exact Complex.norm_deriv_le_one_of_mapsTo_ball hF_diff hmaps' (by norm_num)
  -- derivative of F at 0 via the chain rule
  have hzns : normSq z < 1 := spick.normSq_lt_one_iff_norm.mpr hz'
  have hbns : normSq (g z) < 1 := spick.normSq_lt_one_iff_norm.mpr hgz
  have hM0 : HasDerivAt M ((normSq z - 1 : ℂ)) 0 := by
    have h := spick.hasDerivAt z 0 (by norm_num : 1 - conj z * (0 : ℂ) ≠ 0)
    simpa [M] using h
  have hgAt0 : HasDerivAt g (deriv g z) (M 0) := by
    have hgAt : HasDerivAt g (deriv g z) z :=
      (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    simpa [M, spick.discAut] using hgAt
  have hgM0 : HasDerivAt (g ∘ M) (deriv g z * ((normSq z - 1 : ℂ))) 0 := by
    simpa using HasDerivAt.comp (0 : ℂ) hgAt0 hM0
  have hN0 : HasDerivAt N (((normSq (g z) - 1 : ℂ)) / (1 - conj (g z) * (g z)) ^ 2) ((g ∘ M) 0) := by
    have h := spick.hasDerivAt (g z) (g z) (spick.den_ne_zero hgz (le_of_lt hgz))
    simpa [N, M, spick.discAut] using h
  have hF0at : HasDerivAt F
      ((((normSq (g z) - 1 : ℂ)) / (1 - conj (g z) * (g z)) ^ 2) *
        (deriv g z * ((normSq z - 1 : ℂ)))) 0 := by
    dsimp [F]
    simpa using HasDerivAt.comp (0 : ℂ) hN0 hgM0
  have hFderiv : deriv F 0 =
      ((((normSq (g z) - 1 : ℂ)) / (1 - conj (g z) * (g z)) ^ 2) *
        (deriv g z * ((normSq z - 1 : ℂ)))) := hF0at.deriv
  have hnorm_eq : ‖deriv F 0‖ =
      ‖deriv g z‖ * (1 - normSq z) / (1 - normSq (g z)) := by
    rw [hFderiv]
    rw [norm_mul, norm_mul]
    rw [spick.norm_derivVal hbns]
    have hs : ‖((normSq z - 1 : ℂ))‖ = 1 - normSq z := by
      simpa using spick.cnorm_normSq_sub_one hzns
    rw [hs]
    field_simp [sub_ne_zero.mpr (ne_of_gt (sub_pos.mpr hbns))]
  have hmain : ‖deriv g z‖ * (1 - normSq z) / (1 - normSq (g z)) ≤ 1 := by
    rw [hnorm_eq] at hF_bound
    exact hF_bound
  have hq : 0 < 1 - normSq (g z) := sub_pos.mpr hbns
  have hp : 0 < 1 - normSq z := sub_pos.mpr hzns
  have hxq : ‖deriv g z‖ * (1 - normSq z) ≤ 1 - normSq (g z) := by
    simpa using (div_le_iff₀ hq).mp hmain
  have hx : ‖deriv g z‖ ≤ (1 - normSq (g z)) / (1 - normSq z) := by
    exact (le_div_iff₀ hp).mpr hxq
  simpa [Complex.normSq_eq_norm_sq] using hx

end Commons.Analysis.Complex