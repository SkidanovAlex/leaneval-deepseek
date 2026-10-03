import Mathlib
import Submission.Work.Horn.flower_defs

/-!
# `Work.Horn.petal_facts`

The algebra and the set geometry of the Leau–Fatou petals of a parabolic germ of order `q + 1`:
with `c = cc q a = -1/(q a)` the chart is `w = c/z^q`, the root disc is
`DM M = {s | M * normSq s < Re (c * conj s)} = ball (c/(2M)) (‖c‖/(2M))`, and the `j`-th petal is
`petal M j = rootFun j '' DM M`, the image of `DM M` under the `j`-th branch of the `q`-th root.

Everything is proved from the definitions of `Work.Horn.Flower` alone.  The only analytic input is
the open mapping theorem for `rootFun j` on `DM M` (`AnalyticOnNhd.is_constant_or_isOpen`), the
set `DM M` being a disc contained in `c • slitPlane` where `Complex.log` is analytic.
-/

namespace Work.Horn

open Work.Horn.Flower

namespace PetalFactsAux

/-! ## The constant `cc` and the `q`-th roots `zeta` of `cc` -/

lemma cc_ne_zero {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (ha : a ≠ 0) : cc q a ≠ 0 := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [cc]
  exact div_ne_zero (by norm_num) (mul_ne_zero hq0 ha)

lemma zeta_pow {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (ha : a ≠ 0) (j : Fin q) :
    (zeta q a j) ^ q = cc q a := by
  have hc : cc q a ≠ 0 := cc_ne_zero hq ha
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [zeta, ← Complex.exp_nat_mul]
  have h1 : (q : ℂ) * ((Complex.log (cc q a) + 2 * Real.pi * Complex.I * (j : ℂ)) / (q : ℂ))
      = Complex.log (cc q a) + 2 * Real.pi * Complex.I * (j : ℂ) := by
    field_simp
  rw [h1, Complex.exp_add, Complex.exp_log hc]
  have h2 : Complex.exp (2 * Real.pi * Complex.I * (j : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨(j : ℤ), by push_cast; ring⟩
  rw [h2, mul_one]

lemma zeta_ne_zero {q : ℕ} {a : ℂ} (j : Fin q) : zeta q a j ≠ 0 := by
  rw [zeta]; exact Complex.exp_ne_zero _

lemma zeta_ratio {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (i j : Fin q) :
    zeta q a i = zeta q a j *
      Complex.exp (2 * Real.pi * Complex.I * ((i : ℂ) - (j : ℂ)) / (q : ℂ)) := by
  rw [zeta, zeta, ← Complex.exp_add]
  congr 1
  field_simp
  ring

lemma zeta_eq_zero_idx {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (i : Fin q) :
    zeta q a i = zeta q a (⟨0, hq⟩ : Fin q) *
      Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) / (q : ℂ)) := by
  simpa using zeta_ratio (a := a) hq i (⟨0, hq⟩ : Fin q)

lemma zeta_inj {q : ℕ} {a : ℂ} (hq : 1 ≤ q) {i j : Fin q}
    (h : zeta q a i = zeta q a j) : i = j := by
  have hz0 : zeta q a (⟨0, hq⟩ : Fin q) ≠ 0 := zeta_ne_zero _
  have hi := zeta_eq_zero_idx (a := a) hq i
  have hj := zeta_eq_zero_idx (a := a) hq j
  have hcancel : Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) / (q : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / (q : ℂ)) := by
    rw [hi, hj] at h
    exact mul_left_cancel₀ hz0 h
  have hpow : ∀ n : ℕ, Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (q : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I / (q : ℂ)) ^ n := by
    intro n
    rw [← Complex.exp_nat_mul]; congr 1; ring
  rw [hpow i.val, hpow j.val] at hcancel
  exact Fin.ext ((Complex.isPrimitiveRoot_exp q (by omega)).pow_inj i.isLt j.isLt hcancel)

lemma zeta_ne_iff {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (i j : Fin q) :
    zeta q a i = zeta q a j ↔ i = j :=
  ⟨fun h => zeta_inj hq h, fun h => by rw [h]⟩

lemma zeta_surj {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (ha : a ≠ 0) (u : ℂ)
    (hu : u ^ q = cc q a) : ∃ j : Fin q, zeta q a j = u := by
  haveI : NeZero q := ⟨by omega⟩
  have hc : cc q a ≠ 0 := cc_ne_zero hq ha
  have hz0 : zeta q a (⟨0, hq⟩ : Fin q) ≠ 0 := zeta_ne_zero _
  have hpow1 : (u / zeta q a (⟨0, hq⟩ : Fin q)) ^ q = 1 := by
    rw [div_pow, zeta_pow hq ha, hu, div_self hc]
  obtain ⟨k, hklt, hk⟩ :=
    (Complex.isPrimitiveRoot_exp q (by omega : q ≠ 0)).eq_pow_of_pow_eq_one hpow1
  refine ⟨⟨k, hklt⟩, ?_⟩
  have hexp : Complex.exp (2 * Real.pi * Complex.I / (q : ℂ)) ^ k =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (q : ℂ)) := by
    rw [← Complex.exp_nat_mul]; congr 1; ring
  rw [hexp] at hk
  have hr := zeta_eq_zero_idx (a := a) hq (⟨k, hklt⟩ : Fin q)
  rw [hr, hk]
  exact mul_div_cancel₀ u hz0

/-! ## The root branches `rootFun` -/

lemma rootFun_ne_zero {q : ℕ} {a : ℂ} (j : Fin q) (s : ℂ) : rootFun q a j s ≠ 0 := by
  rw [rootFun]
  exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

lemma rootFun_pow {q : ℕ} {a : ℂ} {M : ℝ} (hq : 1 ≤ q) (hcc : cc q a ≠ 0)
    (hzpow : ∀ j : Fin q, (zeta q a j) ^ q = cc q a) {j : Fin q} {s : ℂ}
    (hs : s ∈ DM q a M) : (rootFun q a j s) ^ q = s := by
  have hs0 : s ≠ 0 := fun h => by
    rw [h] at hs; simp [DM, Complex.normSq] at hs
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsc : s / cc q a ≠ 0 := div_ne_zero hs0 hcc
  have hexp : (Complex.exp (Complex.log (s / cc q a) / (q : ℂ))) ^ q = s / cc q a := by
    rw [← Complex.exp_nat_mul]
    have h : (q : ℂ) * (Complex.log (s / cc q a) / (q : ℂ)) = Complex.log (s / cc q a) := by
      field_simp
    rw [h, Complex.exp_log hsc]
  rw [rootFun, mul_pow, hzpow j, hexp, mul_div_cancel₀ s hcc]

lemma rootFun_eq_of_pow_eq {q : ℕ} {a : ℂ} {M : ℝ} (hq : 1 ≤ q) (hcc : cc q a ≠ 0)
    (hzpow : ∀ j : Fin q, (zeta q a j) ^ q = cc q a)
    {j : Fin q} {s t : ℂ} (hs : s ∈ DM q a M) (ht : t ∈ DM q a M)
    (h : rootFun q a j s = rootFun q a j t) : s = t := by
  rw [← rootFun_pow hq hcc hzpow hs, h, rootFun_pow hq hcc hzpow ht]

lemma rootFun_inj_index {q : ℕ} {a : ℂ} (hziff : ∀ i j : Fin q, zeta q a i = zeta q a j ↔ i = j)
    {j k : Fin q} {s : ℂ} (h : rootFun q a j s = rootFun q a k s) : j = k := by
  have hE : Complex.exp (Complex.log (s / cc q a) / (q : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  rw [rootFun, rootFun] at h
  exact (hziff j k).mp (mul_right_cancel₀ hE h)

/-! ## The root disc `DM` -/

/-- `normSq c * Re (s/c) = Re (c * conj s)`. -/
lemma div_re_key {q : ℕ} {a : ℂ} (s : ℂ) :
    Complex.normSq (cc q a) * (s / cc q a).re = (cc q a * star s).re := by
  rcases eq_or_ne (cc q a) 0 with hc | hc
  · rw [hc]; simp
  · have hn : Complex.normSq (cc q a) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hc)
    rw [Complex.div_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    field_simp
    ring

/-- The defining inequality of `DM` is "inside the disc of diameter `[0, c/M]`". -/
lemma normSq_key {q : ℕ} {a : ℂ} {M : ℝ} (hM : 0 < M) (s : ℂ) :
    (M * Complex.normSq s < (cc q a * star s).re) ↔
      Complex.normSq (s - cc q a / ((2 : ℂ) * (M : ℂ))) <
        Complex.normSq (cc q a / ((2 : ℂ) * (M : ℂ))) := by
  have h2M : (2 : ℂ) * (M : ℂ) = ((2 * M : ℝ) : ℂ) := by rw [Complex.ofReal_mul]; norm_num
  have hden : Complex.normSq (((2 * M : ℝ)) : ℂ) = 4 * M ^ 2 := by
    rw [Complex.normSq_ofReal]; ring
  rw [h2M, Complex.normSq_sub, Complex.normSq_div, hden, Complex.normSq_apply]
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im]
  field_simp
  constructor <;> intro h <;> nlinarith [h]

lemma DM_eq_ball {q : ℕ} {a : ℂ} {M : ℝ} (hM : 0 < M) :
    DM q a M = Metric.ball (cc q a / (2 * M)) (‖cc q a‖ / (2 * M)) := by
  ext s
  rw [DM, Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm]
  have h2M : (2 : ℂ) * (M : ℂ) = ((2 * M : ℝ) : ℂ) := by rw [Complex.ofReal_mul]; norm_num
  have hnorm : ‖cc q a / ((2 : ℂ) * (M : ℂ))‖ = ‖cc q a‖ / (2 * M) := by
    rw [norm_div, h2M, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [← hnorm]
  have hsq : ‖s - cc q a / ((2 : ℂ) * (M : ℂ))‖ < ‖cc q a / ((2 : ℂ) * (M : ℂ))‖ ↔
      Complex.normSq (s - cc q a / ((2 : ℂ) * (M : ℂ))) <
        Complex.normSq (cc q a / ((2 : ℂ) * (M : ℂ))) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, sq_lt_sq,
      abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
  rw [hsq]
  exact normSq_key hM s

lemma DM_subset_ball {q : ℕ} {a : ℂ} {M : ℝ} (hM : 0 < M)
    (hDM : DM q a M = Metric.ball (cc q a / (2 * M)) (‖cc q a‖ / (2 * M))) :
    ∀ s ∈ DM q a M, ‖s‖ < ‖cc q a‖ / M := by
  intro s hs
  rw [hDM, Metric.mem_ball, dist_eq_norm] at hs
  have h2M : (2 : ℂ) * (M : ℂ) = ((2 * M : ℝ) : ℂ) := by rw [Complex.ofReal_mul]; norm_num
  have hnorm : ‖cc q a / ((2 : ℂ) * (M : ℂ))‖ = ‖cc q a‖ / (2 * M) := by
    rw [norm_div, h2M, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖s‖ ≤ ‖s - cc q a / ((2 : ℂ) * (M : ℂ))‖ + ‖cc q a / ((2 : ℂ) * (M : ℂ))‖ := by
    have h := norm_add_le (s - cc q a / ((2 : ℂ) * (M : ℂ))) (cc q a / ((2 : ℂ) * (M : ℂ)))
    rwa [sub_add_cancel] at h
  calc ‖s‖ ≤ ‖s - cc q a / ((2 : ℂ) * (M : ℂ))‖ + ‖cc q a / ((2 : ℂ) * (M : ℂ))‖ := h1
    _ = ‖s - cc q a / ((2 : ℂ) * (M : ℂ))‖ + ‖cc q a‖ / (2 * M) := by rw [hnorm]
    _ < ‖cc q a‖ / (2 * M) + ‖cc q a‖ / (2 * M) := by linarith
    _ = ‖cc q a‖ / M := by ring

/-- On the root disc the chart lands in the slit plane (so that `log` is analytic there). -/
lemma DM_slit {q : ℕ} {a : ℂ} {M : ℝ} (hM : 0 < M) {s : ℂ}
    (hs : s ∈ DM q a M) : s / cc q a ∈ Complex.slitPlane := by
  rcases eq_or_ne (cc q a) 0 with hc | hc
  · exfalso
    simp [DM, hc, Complex.normSq] at hs
    nlinarith [sq_nonneg s.re, sq_nonneg s.im, hM]
  · have hn : 0 < Complex.normSq (cc q a) := Complex.normSq_pos.mpr hc
    have h1 : 0 < (cc q a * star s).re :=
      lt_of_le_of_lt (mul_nonneg (le_of_lt hM) (Complex.normSq_nonneg s)) hs
    have h2 : 0 < Complex.normSq (cc q a) * (s / cc q a).re := by
      rw [div_re_key]; exact h1
    have h3 : 0 < (s / cc q a).re := (mul_pos_iff_of_pos_left hn).mp h2
    rw [Complex.mem_slitPlane_iff]; exact Or.inl h3

/-- `t * c ∈ DM` for `0 < t < 1/M`: the points of the diameter of the root disc. -/
lemma mem_DM_smul {q : ℕ} {a : ℂ} {M : ℝ} (hcc : cc q a ≠ 0)
    {t : ℝ} (ht : 0 < t) (htM : t * M < 1) : ((t : ℂ) * cc q a) ∈ DM q a M := by
  have hn : 0 < Complex.normSq (cc q a) := Complex.normSq_pos.mpr hcc
  have h1 : Complex.normSq ((t : ℂ) * cc q a) = t ^ 2 * Complex.normSq (cc q a) := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  have h2 : (cc q a * star ((t : ℂ) * cc q a)).re = t * Complex.normSq (cc q a) := by
    have h : star ((t : ℂ) * cc q a) = (t : ℂ) * star (cc q a) := by
      simp only [Complex.star_def]
      rw [map_mul, Complex.conj_ofReal]
    rw [h]
    have h2' : cc q a * ((t : ℂ) * star (cc q a)) = (t : ℂ) * (cc q a * star (cc q a)) := by
      ring
    rw [h2']
    simp only [Complex.star_def]
    rw [Complex.mul_conj]
    simp
  rw [DM, Set.mem_ofPred_eq, h1, h2]
  have key : (t * M) * (t * Complex.normSq (cc q a)) < 1 * (t * Complex.normSq (cc q a)) :=
    mul_lt_mul_of_pos_right htM (by positivity)
  nlinarith [key]

/-! ## The petals: openness, connectedness, accumulation at `0` -/

lemma petal_open {q : ℕ} {a : ℂ} {M : ℝ} (hq : 1 ≤ q) (ha : a ≠ 0) (hM : 0 < M)
    (hcc : cc q a ≠ 0)
    (hDM : DM q a M = Metric.ball (cc q a / (2 * M)) (‖cc q a‖ / (2 * M)))
    (hslit : ∀ s ∈ DM q a M, s / cc q a ∈ Complex.slitPlane)
    (hpow : ∀ (j : Fin q) (s : ℂ), s ∈ DM q a M → (rootFun q a j s) ^ q = s) :
    (∀ j : Fin q, IsOpen (petal q a M j)) ∧
    (∀ j : Fin q, IsConnected (petal q a M j)) ∧
    (∀ j : Fin q, (0 : ℂ) ∈ closure (petal q a M j)) := by
  have hcpos : 0 < ‖cc q a‖ := norm_pos_iff.mpr hcc
  have hball_open : IsOpen (DM q a M) := by rw [hDM]; exact Metric.isOpen_ball
  have hpreconn : IsPreconnected (DM q a M) := by
    rw [hDM]; exact (convex_ball _ _).isPreconnected
  have hnonempty : (DM q a M).Nonempty :=
    ⟨_, by rw [hDM]; exact Metric.mem_ball_self (div_pos hcpos (by positivity))⟩
  have hdiff : ∀ j : Fin q, DifferentiableOn ℂ (rootFun q a j) (DM q a M) := by
    intro j s hs
    have hsc : s / cc q a ∈ Complex.slitPlane := hslit s hs
    have hd1 : DifferentiableAt ℂ (fun t : ℂ => t / cc q a) s := differentiableAt_id.div_const _
    have hd2 : DifferentiableAt ℂ Complex.log (s / cc q a) := Complex.differentiableAt_log hsc
    have hd3 : DifferentiableAt ℂ (fun t : ℂ => Complex.log (t / cc q a) / (q : ℂ)) s :=
      (hd2.comp s hd1).div_const _
    have hd4 : DifferentiableAt ℂ
        (fun t : ℂ => Complex.exp (Complex.log (t / cc q a) / (q : ℂ))) s := hd3.cexp
    show DifferentiableWithinAt ℂ (fun t : ℂ => zeta q a j *
      Complex.exp (Complex.log (t / cc q a) / (q : ℂ))) (DM q a M) s
    exact (hd4.const_mul _).differentiableWithinAt
  have hnonconst : ∀ j : Fin q, ¬ ∃ w, ∀ z ∈ DM q a M, rootFun q a j z = w := by
    intro j ⟨w, hw⟩
    have h1 : ((1 / (2 * M) : ℝ)) * M < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity : (0 : ℝ) < 2 * M)]; linarith
    have h2 : ((1 / (4 * M) : ℝ)) * M < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity : (0 : ℝ) < 4 * M)]; linarith
    have hz1 := mem_DM_smul (q := q) (a := a) (M := M) hcc
      (by positivity : (0 : ℝ) < 1 / (2 * M)) h1
    have hz2 := mem_DM_smul (q := q) (a := a) (M := M) hcc
      (by positivity : (0 : ℝ) < 1 / (4 * M)) h2
    have e1 : ((1 / (2 * M) : ℝ) : ℂ) * cc q a = w ^ q := by rw [← hpow j _ hz1, hw _ hz1]
    have e2 : ((1 / (4 * M) : ℝ) : ℂ) * cc q a = w ^ q := by rw [← hpow j _ hz2, hw _ hz2]
    have heq : ((1 / (2 * M) : ℝ) : ℂ) * cc q a =
        ((1 / (4 * M) : ℝ) : ℂ) * cc q a := by rw [e1, e2]
    have hc : ((1 / (2 * M) : ℝ) : ℂ) = ((1 / (4 * M) : ℝ) : ℂ) := mul_right_cancel₀ hcc heq
    have hreal : (1 / (2 * M) : ℝ) = 1 / (4 * M) := by exact_mod_cast hc
    rw [div_eq_div_iff (by positivity : (2 * M : ℝ) ≠ 0) (by positivity : (4 * M : ℝ) ≠ 0),
      one_mul, one_mul] at hreal
    linarith
  have hopen : ∀ j : Fin q, IsOpen (petal q a M j) := by
    intro j
    rcases (hdiff j).analyticOnNhd hball_open |>.is_constant_or_isOpen hpreconn with hc | hop
    · exact absurd hc (hnonconst j)
    · exact hop _ (subset_refl _) hball_open
  have hconn : ∀ j : Fin q, IsConnected (petal q a M j) := fun j =>
    ⟨hnonempty.image _, hpreconn.image _ (hdiff j).continuousOn⟩
  refine ⟨hopen, hconn, fun j => ?_⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t : ℝ := min (1 / (2 * M)) (ε ^ q / (2 * ‖cc q a‖)) with htdef
  have htpos : 0 < t := lt_min (by positivity) (div_pos (pow_pos hε q) (by positivity))
  have htM : t * M < 1 := by
    have h1 : t ≤ 1 / (2 * M) := min_le_left _ _
    have h2 : t * M ≤ (1 / (2 * M)) * M := mul_le_mul_of_nonneg_right h1 (le_of_lt hM)
    have h3 : (1 / (2 * M)) * M = 1 / 2 := by field_simp
    linarith
  have htc : ((t : ℂ) * cc q a) ∈ DM q a M := mem_DM_smul hcc htpos htM
  have hnorm : ‖rootFun q a j ((t : ℂ) * cc q a)‖ ^ q = t * ‖cc q a‖ := by
    rw [← norm_pow, hpow j _ htc, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (le_of_lt htpos)]
  refine ⟨rootFun q a j ((t : ℂ) * cc q a), ⟨_, htc, rfl⟩, ?_⟩
  rw [dist_zero_left]
  have hlt : t * ‖cc q a‖ < ε ^ q := by
    have h2 : t ≤ ε ^ q / (2 * ‖cc q a‖) := min_le_right _ _
    have h3 : (ε ^ q / (2 * ‖cc q a‖)) * ‖cc q a‖ = ε ^ q / 2 := by field_simp
    calc t * ‖cc q a‖ ≤ (ε ^ q / (2 * ‖cc q a‖)) * ‖cc q a‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = ε ^ q / 2 := h3
      _ < ε ^ q := by linarith [pow_pos hε q]
  exact lt_of_pow_lt_pow_left₀ q (le_of_lt hε) (by rw [hnorm]; exact hlt)

/-! ## Disjointness, the union of the petals, and the basic descriptions -/

lemma disjoint_petal {q : ℕ} {a : ℂ} {M : ℝ} (hq : 1 ≤ q) (hcc : cc q a ≠ 0)
    (hzpow : ∀ j : Fin q, (zeta q a j) ^ q = cc q a)
    (hziff : ∀ i j : Fin q, zeta q a i = zeta q a j ↔ i = j)
    {i j : Fin q} (hij : i ≠ j) : Disjoint (petal q a M i) (petal q a M j) := by
  rw [Set.disjoint_left]
  rintro z ⟨s, hs, rfl⟩ ⟨t, ht, hzt⟩
  have h1 : s = (rootFun q a i s) ^ q := (rootFun_pow hq hcc hzpow hs).symm
  have h2 : t = (rootFun q a j t) ^ q := (rootFun_pow hq hcc hzpow ht).symm
  have hst : s = t := by
    calc s = (rootFun q a i s) ^ q := h1
      _ = (rootFun q a j t) ^ q := by rw [hzt]
      _ = t := h2.symm
  have hji : rootFun q a i s = rootFun q a j s := by
    rw [← hzt, hst]
  exact absurd (rootFun_inj_index hziff hji) hij

lemma not_mem_petal_zero {q : ℕ} {a : ℂ} {M : ℝ} (hq : 1 ≤ q) (hcc : cc q a ≠ 0)
    (hzpow : ∀ j : Fin q, (zeta q a j) ^ q = cc q a) (j : Fin q) :
    (0 : ℂ) ∉ petal q a M j := by
  rintro ⟨s, hs, hs0⟩
  have hsq : (rootFun q a j s) ^ q = 0 := by rw [hs0, zero_pow (by omega : q ≠ 0)]
  have : s = 0 := by rw [← rootFun_pow hq hcc hzpow hs, hsq]
  rw [this] at hs
  simp [DM, Complex.normSq] at hs

lemma petal_subset_bigPetal {q : ℕ} {a : ℂ} {M : ℝ} (hq : 1 ≤ q) (hcc : cc q a ≠ 0)
    (hzpow : ∀ j : Fin q, (zeta q a j) ^ q = cc q a) (j : Fin q) :
    petal q a M j ⊆ bigPetal q a M := by
  rintro z ⟨s, hs, rfl⟩
  show (rootFun q a j s) ^ q ∈ DM q a M
  rw [rootFun_pow hq hcc hzpow hs]
  exact hs

lemma petal_norm_pow_lt {q : ℕ} {a : ℂ} {M : ℝ} (hq : 1 ≤ q) (hcc : cc q a ≠ 0)
    (hzpow : ∀ j : Fin q, (zeta q a j) ^ q = cc q a)
    (hDMsub : ∀ s ∈ DM q a M, ‖s‖ < ‖cc q a‖ / M)
    (j : Fin q) {z : ℂ} (hz : z ∈ petal q a M j) : ‖z‖ ^ q < ‖cc q a‖ / M := by
  rcases hz with ⟨s, hs, rfl⟩
  rw [← norm_pow, rootFun_pow hq hcc hzpow hs]
  exact hDMsub s hs

lemma mem_petal_iff {q : ℕ} {a : ℂ} {M : ℝ} (hq : 1 ≤ q) (hcc : cc q a ≠ 0)
    (hzpow : ∀ j : Fin q, (zeta q a j) ^ q = cc q a) (j : Fin q) (z : ℂ) :
    z ∈ petal q a M j ↔ 0 < ‖z‖ ∧ z ^ q ∈ DM q a M ∧ rootFun q a j (z ^ q) = z := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨norm_pos_iff.mpr (rootFun_ne_zero j s), ?_, ?_⟩
    · rw [rootFun_pow hq hcc hzpow hs]; exact hs
    · rw [rootFun_pow hq hcc hzpow hs]
  · rintro ⟨_, hDM, hrf⟩
    exact ⟨z ^ q, hDM, hrf⟩

lemma iUnion_petal_eq_bigPetal {q : ℕ} {a : ℂ} {M : ℝ} (hq : 1 ≤ q) (ha : a ≠ 0) (hM : 0 < M)
    (hcc : cc q a ≠ 0)
    (hzpow : ∀ j : Fin q, (zeta q a j) ^ q = cc q a)
    (hpow : ∀ (j : Fin q) (s : ℂ), s ∈ DM q a M → (rootFun q a j s) ^ q = s)
    (hclass : ∀ u : ℂ, u ^ q = cc q a → ∃ j : Fin q, zeta q a j = u) :
    (⋃ j : Fin q, petal q a M j) = bigPetal q a M := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  apply Set.Subset.antisymm
  · intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨j, hj⟩
    exact petal_subset_bigPetal hq hcc hzpow j hj
  · intro z hz
    have hzq : z ^ q ∈ DM q a M := hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, zero_pow (by omega : q ≠ 0)] at hzq
      simp [DM, Complex.normSq] at hzq
    have hzq0 : z ^ q ≠ 0 := pow_ne_zero _ hz0
    set E : ℂ := Complex.exp (Complex.log (z ^ q / cc q a) / (q : ℂ)) with hEdef
    have hEne : E ≠ 0 := Complex.exp_ne_zero _
    have hE : E ^ q = z ^ q / cc q a := by
      rw [hEdef, ← Complex.exp_nat_mul]
      have h : (q : ℂ) * (Complex.log (z ^ q / cc q a) / (q : ℂ))
          = Complex.log (z ^ q / cc q a) := by field_simp
      rw [h, Complex.exp_log (div_ne_zero hzq0 hcc)]
    have hu : (z / E) ^ q = cc q a := by
      rw [div_pow, hE]
      field_simp
    obtain ⟨j, hj⟩ := hclass _ hu
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    exact ⟨z ^ q, hzq, by rw [rootFun, hj]; exact div_mul_cancel₀ z hEne⟩

end PetalFactsAux

open PetalFactsAux

theorem petal_facts {q : ℕ} {a : ℂ} {M : ℝ} (hq : 1 ≤ q) (ha : a ≠ 0)
    (hM : 0 < M) : Work.Horn.Flower.PetalFacts q a M := by
  have hcc : cc q a ≠ 0 := cc_ne_zero hq ha
  have hzpow : ∀ j : Fin q, (zeta q a j) ^ q = cc q a := fun j => zeta_pow hq ha j
  have hziff : ∀ i j : Fin q, zeta q a i = zeta q a j ↔ i = j := fun i j => zeta_ne_iff hq i j
  have hDM : DM q a M = Metric.ball (cc q a / (2 * M)) (‖cc q a‖ / (2 * M)) := DM_eq_ball hM
  have hDMsub : ∀ s ∈ DM q a M, ‖s‖ < ‖cc q a‖ / M := DM_subset_ball hM hDM
  have hslit : ∀ s ∈ DM q a M, s / cc q a ∈ Complex.slitPlane := fun s hs => DM_slit hM hs
  have hpow : ∀ (j : Fin q) (s : ℂ), s ∈ DM q a M → (rootFun q a j s) ^ q = s :=
    fun j s hs => rootFun_pow hq hcc hzpow hs
  obtain ⟨hopen, hconn, hclos⟩ := petal_open hq ha hM hcc hDM hslit hpow
  exact
    { cc_ne_zero := hcc
      DM_eq_ball := hDM
      DM_subset_ball := hDMsub
      zeta_pow := hzpow
      zeta_ne_zero := fun j => zeta_ne_zero j
      zeta_ne_iff := hziff
      rootFun_pow := hpow
      rootFun_ne_zero := fun j s _ => rootFun_ne_zero j s
      rootFun_eq_of_pow_eq :=
        fun j s t hs ht h => rootFun_eq_of_pow_eq hq hcc hzpow hs ht h
      rootFun_inj_index := fun j k s _ h => rootFun_inj_index hziff h
      isOpen_petal := hopen
      isConnected_petal := hconn
      disjoint_petal := fun i j hij => disjoint_petal hq hcc hzpow hziff hij
      not_mem_petal_zero := fun j => not_mem_petal_zero hq hcc hzpow j
      zero_mem_closure_petal := hclos
      petal_subset_bigPetal := fun j => petal_subset_bigPetal hq hcc hzpow j
      iUnion_petal_eq_bigPetal :=
        iUnion_petal_eq_bigPetal hq ha hM hcc hzpow hpow (fun u hu => zeta_surj hq ha u hu)
      petal_norm_pow_lt := fun j z hz => petal_norm_pow_lt hq hcc hzpow hDMsub j hz
      mem_petal_iff := fun j z => mem_petal_iff hq hcc hzpow j z }

end Work.Horn
