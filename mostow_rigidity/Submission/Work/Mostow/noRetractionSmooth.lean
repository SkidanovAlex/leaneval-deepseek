import Mathlib
import Submission.Work.Mostow.NoRetractionDefs
import Submission.Work.Mostow.detInterpExpansion
import Submission.Work.Mostow.lipschitzOnBallInterp
import Submission.Work.Mostow.imageInterpEqBall
import Submission.Work.Mostow.integralDetInterpEq
import Submission.Work.Mostow.detFDerivEqZero
import Submission.Work.Mostow.innerFDerivEqZero
import Submission.Work.Mostow.fderivInterp
import Submission.Work.Mostow.contDiffInterp
import Submission.Work.Mostow.bijectiveOfDetNeZero
import Submission.Work.Mostow.polyEqConstOfEventuallyEq

namespace Work.Mostow

open Metric MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-! ## Auxiliary facts about the linear interpolation `(1 - t) • id + t • f` -/

/-- If `f` is `C`-Lipschitz on the closed unit ball and `0 ≤ t ≤ 1` with `t * (1 + C) < 1`, then
the linear interpolation `x ↦ (1 - t) • x + t • f x` is injective on the closed unit ball. -/
theorem injOnInterpAux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (C t : ℝ)
    (hlip : ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1,
      ‖f x - f y‖ ≤ C * ‖x - y‖)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htC : t * (1 + C) < 1) :
    Set.InjOn (fun x => (1 - t) • x + t • f x) (closedBall (0 : E) 1) := by
  intro x hx y hy hxy
  have hsum : (1 - t) • (x - y) + t • (f x - f y) = 0 := by
    have h3 : (1 - t) • (x - y) + t • (f x - f y)
        = ((1 - t) • x + t • f x) - ((1 - t) • y + t • f y) := by
      rw [smul_sub, smul_sub]
      abel
    rw [h3]
    have h4 : (1 - t) • x + t • f x = (1 - t) • y + t • f y := hxy
    rw [h4, sub_self]
  have h1 : (1 - t) • (x - y) = -(t • (f x - f y)) := eq_neg_of_add_eq_zero_left hsum
  have hnorm : (1 - t) * ‖x - y‖ = t * ‖f x - f y‖ := by
    have h := congrArg norm h1
    rw [norm_smul, norm_neg, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t), abs_of_nonneg ht0] at h
    linarith
  have h2 : (1 - t) * ‖x - y‖ ≤ t * C * ‖x - y‖ := by
    rw [hnorm]
    calc t * ‖f x - f y‖ ≤ t * (C * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (hlip x hx y hy) ht0
      _ = t * C * ‖x - y‖ := by ring
  have h3 : (1 - t - t * C) * ‖x - y‖ ≤ 0 := by linarith
  have h4 : 0 < 1 - t - t * C := by linarith
  have h5 : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h5)

/-- The volume of the closed unit ball of `ℝⁿ` is positive. -/
theorem volume_closedBall_pos (n : ℕ) :
    0 < MeasureTheory.volume (closedBall (0 : E n) 1) := by
  have hle : MeasureTheory.volume (ball (0 : E n) 1) ≤
      MeasureTheory.volume (closedBall (0 : E n) 1) := measure_mono ball_subset_closedBall
  exact lt_of_lt_of_le (isOpen_ball.measure_pos _ ⟨0, by simp⟩) hle

/-- For `t > 0` small enough, `det ((1 - t) • 1 + t • fderiv ℝ f x)` is positive for every `x` in
the closed unit ball. -/
theorem existsPosDetInterpAux (n : ℕ) (f : E n → E n) (hf : ContDiff ℝ 1 f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, t ∈ Set.Ioo 0 ε → ∀ x ∈ closedBall (0 : E n) 1,
      0 < ((1 - t) • (1 : E n →L[ℝ] E n) + t • fderiv ℝ f x).det := by
  have hcont : Continuous fun p : ℝ × E n =>
      ((1 - p.1) • (1 : E n →L[ℝ] E n) + p.1 • fderiv ℝ f p.2).det := by
    refine ContinuousLinearMap.continuous_det.comp ?_
    exact ((continuous_const.sub continuous_fst).smul continuous_const).add
      (continuous_fst.smul ((hf.continuous_fderiv (by norm_num)).comp continuous_snd))
  set K : Set (ℝ × E n) := (Set.Icc (0:ℝ) 1 ×ˢ closedBall (0 : E n) 1) ∩
    {p | ((1 - p.1) • (1 : E n →L[ℝ] E n) + p.1 • fderiv ℝ f p.2).det ≤ 1/2} with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : E n) 1)).inter_right
      (isClosed_le hcont continuous_const)
  have hclosed : IsClosed (Prod.fst '' K) := (hKc.image continuous_fst).isClosed
  have h0 : (0 : ℝ) ∉ Prod.fst '' K := by
    rintro ⟨p, hp, hp0⟩
    have hle : ((1 - p.1) • (1 : E n →L[ℝ] E n) + p.1 • fderiv ℝ f p.2).det ≤ 1/2 := hp.2
    have hdet : ((1 - p.1) • (1 : E n →L[ℝ] E n) + p.1 • fderiv ℝ f p.2).det = 1 := by
      have hsimp : (1 - p.1) • (1 : E n →L[ℝ] E n) + p.1 • fderiv ℝ f p.2
          = (1 : E n →L[ℝ] E n) := by
        rw [hp0]
        ext v
        simp
      rw [hsimp, det_one_clm]
    rw [hdet] at hle
    norm_num at hle
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl 0 h0
  refine ⟨min ε 1, lt_min hε one_pos, fun t ht x hx => ?_⟩
  by_contra hle
  have ht1 : t ≤ 1 := le_of_lt (lt_of_lt_of_le ht.2 (min_le_right _ _))
  have hmem : t ∈ Prod.fst '' K :=
    ⟨(t, x), ⟨⟨⟨le_of_lt ht.1, ht1⟩, hx⟩, le_trans (not_lt.mp hle) (by norm_num)⟩, rfl⟩
  have htb : t ∈ ball (0 : ℝ) ε := by
    rw [mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.mpr ⟨by linarith [ht.1], lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  exact hball htb hmem

/-! ## The interpolation polynomial -/

/-- The coefficient functions of the interpolation polynomial, integrated over the closed unit
ball. -/
def coeff (n : ℕ) (f : E n → E n) (s : Finset (Fin n)) : ℝ :=
  ∫ x in closedBall (0 : E n) 1, phi_NoRetractionDefs n f s x

/-- The polynomial `t ↦ ∫_B det ((1 - t) • 1 + t • fderiv f)`. -/
def interpPoly (n : ℕ) (f : E n → E n) : Polynomial ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
    (Polynomial.X ^ s.card * (Polynomial.C 1 - Polynomial.X) ^ (n - s.card)) *
      Polynomial.C (coeff n f s)

theorem interpPoly_eval (n : ℕ) (f : E n → E n) (hf : ContDiff ℝ 1 f) (t : ℝ) :
    (interpPoly n f).eval t
      = ∫ x in closedBall (0 : E n) 1,
          ((1 - t) • (1 : E n →L[ℝ] E n) + t • fderiv ℝ f x).det := by
  have hint : ∀ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      IntegrableOn (fun x => t ^ s.card * (1 - t) ^ (n - s.card) * phi_NoRetractionDefs n f s x)
        (closedBall (0 : E n) 1) := by
    intro s _
    exact ((continuous_const.mul (continuous_phi n f hf s)).continuousOn).integrableOn_compact
      (isCompact_closedBall _ _)
  have hsplit : (∫ x in closedBall (0 : E n) 1,
        ((1 - t) • (1 : E n →L[ℝ] E n) + t • fderiv ℝ f x).det)
      = ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
          t ^ s.card * (1 - t) ^ (n - s.card) * coeff n f s := by
    have hpoint : ∀ x : E n,
        ((1 - t) • (1 : E n →L[ℝ] E n) + t • fderiv ℝ f x).det
          = ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
              t ^ s.card * (1 - t) ^ (n - s.card) * phi_NoRetractionDefs n f s x :=
      fun x => det_interp_op n (fderiv ℝ f x) t
    simp only [hpoint]
    rw [MeasureTheory.integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_const_mul]
    rfl
  rw [hsplit]
  rw [interpPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [coeff, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]

/-! ## Vanishing of `det (fderiv f)` -/

/-- `det (fderiv f)` vanishes on the open unit ball when `f` maps the closed unit ball into the unit
sphere. -/
theorem det_fderiv_eq_zero_on_ball (f : E n → E n) (hf : ContDiff ℝ 1 f)
    (hmaps : ∀ x ∈ closedBall (0 : E n) 1, f x ∈ sphere (0 : E n) 1) :
    ∀ x ∈ ball (0 : E n) 1, (fderiv ℝ f x).det = 0 := by
  intro x hx
  have hnorm1 : ∀ y ∈ ball (0 : E n) 1, ‖f y‖ = 1 := by
    intro y hy
    have h1 : f y ∈ sphere (0 : E n) 1 := hmaps y (ball_subset_closedBall hy)
    rw [mem_sphere, dist_eq_norm] at h1
    simpa using h1
  have hfx : f x ≠ 0 := by
    intro h0
    have := hnorm1 x hx
    rw [h0, norm_zero] at this
    norm_num at this
  refine detFDerivEqZero f hfx fun v => ?_
  exact innerFDerivEqZero f hf isOpen_ball hnorm1 x hx v

/-- `det (fderiv f)` vanishes on the closed unit ball when `f` maps the closed unit ball into the
unit sphere. -/
theorem det_fderiv_eq_zero_on_closedBall (f : E n → E n) (hf : ContDiff ℝ 1 f)
    (hmaps : ∀ x ∈ closedBall (0 : E n) 1, f x ∈ sphere (0 : E n) 1) :
    ∀ x ∈ closedBall (0 : E n) 1, (fderiv ℝ f x).det = 0 := by
  have hbo := det_fderiv_eq_zero_on_ball f hf hmaps
  have hcont : Continuous fun x : E n => (fderiv ℝ f x).det :=
    ContinuousLinearMap.continuous_det.comp (hf.continuous_fderiv (by norm_num))
  have hclosed : IsClosed {x : E n | (fderiv ℝ f x).det = 0} :=
    isClosed_eq hcont continuous_const
  have hdense : closedBall (0 : E n) 1 ⊆ closure (ball (0 : E n) 1) := by
    intro x hx
    rw [Metric.mem_closure_iff]
    intro e he
    have hxe : ‖x‖ ≤ 1 := by
      rwa [mem_closedBall, dist_zero_right] at hx
    set d : ℝ := min (e / 2) (1 / 2) with hd
    have hd0 : 0 < d := lt_min (by linarith) (by norm_num)
    have hde : d < e := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hd1 : d ≤ 1 := by linarith [min_le_right (e / 2) (1 / 2)]
    refine ⟨(1 - d) • x, ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - d)]
      have h1 : (1 - d) * ‖x‖ ≤ (1 - d) * 1 :=
        mul_le_mul_of_nonneg_left hxe (by linarith)
      have h2 : (1 - d) * 1 < 1 := by linarith
      linarith
    · rw [dist_eq_norm]
      have hsub : x - (1 - d) • x = d • x := by
        calc x - (1 - d) • x = (1 : ℝ) • x - (1 - d) • x := by rw [one_smul]
          _ = ((1 : ℝ) - (1 - d)) • x := (sub_smul 1 (1 - d) x).symm
          _ = d • x := by
              congr 1
              ring
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hd0)]
      have h1 : d * ‖x‖ ≤ d * 1 := mul_le_mul_of_nonneg_left hxe (le_of_lt hd0)
      linarith
  intro x hx
  exact closure_minimal (fun y hy => hbo y hy) hclosed (hdense hx)

/-- The linear interpolation of the derivative is positive on the ball and the interpolation is
injective and onto for sufficiently small positive `t`. -/
theorem exists_good_t (n : ℕ) (_hn : 1 ≤ n) (f : E n → E n) (hf : ContDiff ℝ 1 f)
    (hmaps : ∀ x ∈ closedBall (0 : E n) 1, f x ∈ sphere (0 : E n) 1)
    (hid : ∀ x ∈ sphere (0 : E n) 1, f x = x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, t ∈ Set.Ioo 0 ε →
      Set.InjOn (fun x => (1 - t) • x + t • f x) (closedBall (0 : E n) 1) ∧
      (fun x => (1 - t) • x + t • f x) '' closedBall (0 : E n) 1 = closedBall (0 : E n) 1 ∧
      (∀ x ∈ closedBall (0 : E n) 1,
        0 < ((1 - t) • (1 : E n →L[ℝ] E n) + t • fderiv ℝ f x).det) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ closedBall (0 : E n) 1, ‖fderiv ℝ f x‖ ≤ C :=
    (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn
      (hf.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨ε₁, hε₁, hpos⟩ := existsPosDetInterpAux n f hf
  refine ⟨min ε₁ (1 / (2 * (|C| + 1))), lt_min hε₁ (by positivity), fun t ht => ?_⟩
  have ht1' : t < 1 / (2 * (|C| + 1)) := lt_of_lt_of_le ht.2 (min_le_right _ _)
  have htε₁ : t ∈ Set.Ioo 0 ε₁ := ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hden : (0 : ℝ) < 2 * (|C| + 1) := by positivity
  have ht1 : t < 1 := by
    have hle : 1 / (2 * (|C| + 1)) ≤ 1 := by
      rw [div_le_one hden]
      linarith [abs_nonneg C]
    linarith
  have htC : t * (1 + C) < 1 := by
    have h2 : 1 + C ≤ |C| + 1 := by linarith [le_abs_self C]
    have h3 : 0 ≤ t := le_of_lt ht.1
    have h4 : t * (1 + C) ≤ t * (|C| + 1) := mul_le_mul_of_nonneg_left h2 h3
    have h5 : t * (|C| + 1) < (1 / (2 * (|C| + 1))) * (|C| + 1) :=
      mul_lt_mul_of_pos_right ht1' (by linarith [abs_nonneg C])
    have h6 : (1 / (2 * (|C| + 1))) * (|C| + 1) = 1 / 2 := by
      field_simp
    linarith
  have hlip := lipschitzOnBallInterp f C hf hC
  have hinj : Set.InjOn (fun x => (1 - t) • x + t • f x) (closedBall (0 : E n) 1) :=
    injOnInterpAux f C t hlip (le_of_lt ht.1) (le_of_lt ht1) htC
  have himg : (fun x => (1 - t) • x + t • f x) '' closedBall (0 : E n) 1
      = closedBall (0 : E n) 1 := by
    refine imageInterpEqBall f hf hmaps hid ht.1 ht1 fun x hx => ?_
    exact bijectiveOfDetNeZero _
      (ne_of_gt (hpos t htε₁ x (ball_subset_closedBall hx)))
  exact ⟨hinj, himg, fun x hx => hpos t htε₁ x hx⟩

/-- There is no `C¹` retraction of the closed unit ball of `ℝⁿ` (`n ≥ 1`) onto its boundary sphere:
no `C¹` map of `ℝⁿ` is the identity on the unit sphere while taking all values in the unit sphere.

Suggested proof (no Brouwer/degree theory needed, no Sard needed; `ContDiff ℝ 1` suffices):
`f_t := (1-t) • id + t • f` for `t ∈ [0,1]`. Since `f` is `C¹` its derivative is bounded on the
compact ball, so for small `t > 0`, `Df_t(x) = (1-t)I + t Df(x)` is invertible at every point of the
ball, hence `f_t` is an open map on the ball; and `f_t` is continuous on the closed ball with
`f_t x = x` on the sphere, so `f_t(ball)` is also closed in the ball (if `f_t(x_k) → y ∈ ball` then a
subsequence `x_k → x ∈ closedBall`; `x ∈ sphere` would give `f_t x = x ∈ sphere`, contradiction, so
`x ∈ ball`). The ball is connected, so `f_t(ball) = ball`. Hence by the change-of-variables formula
(`MeasureTheory.Measure.lintegral_abs_det_fderiv_eq_addHaar_image` / `map_withDensity_abs_det_fderiv_eq_addHaar`,
and `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, in `Mathlib/MeasureTheory/Function/Jacobian.lean`)
`∫_ball det (Df_t) = volume ball` for small `t` (the determinant is positive: it is positive near the
sphere where `f_t = id` and never vanishes). The left-hand side is a polynomial in `t`:
`det((1-t)I + tA) = Polynomial.eval t (Matrix.det M)` where `M` is the matrix over `ℝ[X]` with entries
`C 1 - C X` on the diagonal and `C X * Aᵢⱼ` off it, using `RingHom.map_det` for `Polynomial.eval`;
so `t ↦ ∫ det Df_t` is a polynomial that agrees with the constant `volume ball` on an interval,
hence is constant (a nonzero polynomial has finitely many roots). Evaluating at `t = 1`: `f` takes
values in the sphere so `‖f x‖² ≡ 1`, whence `⟨Df(x) v, f x⟩ = 0` for all `v`, `Df(x)` has rank `< n`
and `det Df ≡ 0`, giving `volume ball = 0`, absurd. -/
theorem noRetractionSmooth (n : ℕ) (hn : 1 ≤ n) :
    ¬ ∃ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ 1 f ∧ (∀ x ∈ closedBall 0 1, f x ∈ sphere 0 1) ∧
        ∀ x ∈ sphere 0 1, f x = x := by
  rintro ⟨f, hf, hmaps, hid⟩
  obtain ⟨ε, hε, hgood⟩ := exists_good_t n hn f hf hmaps hid
  have hR : (0 : ℝ) < (MeasureTheory.volume (closedBall (0 : E n) 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (volume_closedBall_pos n))
      (ne_of_lt (isCompact_closedBall (0 : E n) 1).measure_lt_top)
  have hpoly : ∀ t : ℝ, t ∈ Set.Ioo 0 ε →
      (interpPoly n f).eval t = (MeasureTheory.volume (closedBall (0 : E n) 1)).toReal := by
    intro t ht
    obtain ⟨hinj, himg, hpos⟩ := hgood t ht
    rw [interpPoly_eval n f hf t]
    exact integralDetInterpEq f hf (fun x => fderivInterp f hf t x) hinj himg hpos
  have hconst : interpPoly n f = Polynomial.C (MeasureTheory.volume (closedBall (0 : E n) 1)).toReal :=
    polyEqConstOfEventuallyEq _ _ ε hε hpoly
  have h1 : (interpPoly n f).eval 1 = 0 := by
    rw [interpPoly_eval n f hf 1]
    have hzero : ∀ x ∈ closedBall (0 : E n) 1,
        ((1 - (1:ℝ)) • (1 : E n →L[ℝ] E n) + (1:ℝ) • fderiv ℝ f x).det = (0 : ℝ) := by
      intro x hx
      have hsimp : (1 - (1:ℝ)) • (1 : E n →L[ℝ] E n) + (1:ℝ) • fderiv ℝ f x
          = fderiv ℝ f x := by
        rw [sub_self]
        ext v
        simp
      rw [hsimp]
      exact det_fderiv_eq_zero_on_closedBall f hf hmaps x hx
    rw [setIntegral_congr_fun (isClosed_closedBall.measurableSet) hzero]
    simp
  have hzero : (MeasureTheory.volume (closedBall (0 : E n) 1)).toReal = 0 := by
    rw [← h1, hconst]
    simp
  exact absurd hzero (ne_of_gt hR)

end

end Work.Mostow
