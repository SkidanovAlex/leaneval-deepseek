import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.flat.torus_localization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-!
# Properties of the periodised coefficient matrix `tmA`

We prove `Work.Diff.STE.B3.tmA_props`: the periodic matrix `tmA φ lam' γ = lam' • 1 +
per (φ · (γ - lam' • 1))` is bounded, has bounded first derivatives, is symmetric, is positive
definite with constant `lam'`, and is smooth and `1`-periodic, with constants depending only on
`R, c, Kr, Mφ`.

The key point is that `tsupport φ ⊆ Metric.ball 0 R` with `R ≤ 1/2` forces the translates
`φ (· + m)` to have pairwise disjoint supports (two points of `ball 0 R` at distance `< 2R ≤ 1`
cannot differ by a non-zero integer vector), so the periodisation has at most one non-vanishing
summand at every point.
-/

open scoped BigOperators

set_option maxHeartbeats 800000

/-! ## Auxiliary lemmas on the periodisation -/

lemma iVec_inj {n : ℕ} {m m' : Fin n → ℤ} (h : iVec m = iVec m') : m = m' := by
  funext i
  have h1 : ((m i : ℤ) : ℝ) = ((m' i : ℤ) : ℝ) := by
    have h2 := congrFun h i
    simpa using h2
  exact_mod_cast h1

/-- Two integer vectors cannot both translate `z` into `ball 0 R` when `R ≤ 1/2`. -/
lemma eq_of_mem_ball {n : ℕ} {R : ℝ} (hR : R ≤ 1 / 2) {z : Fin n → ℝ} {m m' : Fin n → ℤ}
    (h1 : z + iVec m ∈ Metric.ball 0 R) (h2 : z + iVec m' ∈ Metric.ball 0 R) : m = m' := by
  have h1' : ‖z + iVec m‖ < R := by
    have h := Metric.mem_ball.mp h1
    rwa [dist_zero_right] at h
  have h2' : ‖z + iVec m'‖ < R := by
    have h := Metric.mem_ball.mp h2
    rwa [dist_zero_right] at h
  have h3 : ‖iVec m - iVec m'‖ < 1 := by
    have h4 : iVec m - iVec m' = (z + iVec m) - (z + iVec m') := by ring
    rw [h4]
    have h5 := norm_sub_le (z + iVec m) (z + iVec m')
    linarith
  apply iVec_inj
  ext i
  have h5 : ‖(iVec m - iVec m') i‖ ≤ ‖iVec m - iVec m'‖ := norm_le_pi_norm _ _
  have h6 : (iVec m - iVec m') i = (((m - m') i : ℤ) : ℝ) := by
    simp [iVec, Pi.sub_apply]
  rw [h6, Real.norm_eq_abs] at h5
  have h7 : |((m - m') i : ℤ)| < (1 : ℤ) := by exact_mod_cast (lt_of_le_of_lt h5 h3)
  have h8 : (m - m') i = 0 := by
    have h9 := (abs_lt.mp h7).1
    have h10 := (abs_lt.mp h7).2
    omega
  have h9 : m i = m' i := by
    have : m i - m' i = 0 := by simpa using h8
    omega
  simp [h9]

/-- Two translates of a function supported in `ball 0 R`, `R ≤ 1/2`, cannot both be non-zero. -/
lemma eq_of_support_ball {n : ℕ} {f : (Fin n → ℝ) → ℝ} {R : ℝ} (hR : R ≤ 1 / 2)
    (hsupp : Function.support f ⊆ Metric.ball 0 R) {z : Fin n → ℝ} {m m' : Fin n → ℤ}
    (hm : f (z + iVec m) ≠ 0) (hm' : f (z + iVec m') ≠ 0) : m = m' :=
  eq_of_mem_ball hR (hsupp (Function.mem_support.mpr hm)) (hsupp (Function.mem_support.mpr hm'))

/-- If all the translates of `f` except the one indexed by `m` vanish at `z`, then the
periodisation at `z` is that single translate. -/
lemma tmPer_eq_of_unique {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (m : Fin n → ℤ)
    (h : ∀ m' ≠ m, f (z + iVec m') = 0) : tmPer f z = f (z + iVec m) := by
  rw [tmPer]
  rw [tsum_eq_single m (fun m' hm' => by rw [h m' hm']; simp)]
  simp

lemma tmPer_eq_of_support {n : ℕ} {f : (Fin n → ℝ) → ℝ} {R : ℝ} (hR : R ≤ 1 / 2)
    (hsupp : Function.support f ⊆ Metric.ball 0 R) (z : Fin n → ℝ) (m : Fin n → ℤ)
    (hm : f (z + iVec m) ≠ 0) : tmPer f z = f (z + iVec m) :=
  tmPer_eq_of_unique f z m (fun m' hm' => by
    by_contra hc
    exact hm' (eq_of_support_ball hR hsupp hc hm))

lemma abs_tmPer_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} {R B : ℝ} (hR : R ≤ 1 / 2)
    (hsupp : Function.support f ⊆ Metric.ball 0 R) (hB : ∀ w, |f w| ≤ B) (z : Fin n → ℝ) :
    |tmPer f z| ≤ B := by
  by_cases h : ∃ m, f (z + iVec m) ≠ 0
  · obtain ⟨m, hm⟩ := h
    rw [tmPer_eq_of_support hR hsupp z m hm]
    exact hB _
  · push_neg at h
    have hz : tmPer f z = 0 := by
      rw [tmPer_eq_of_unique f z 0 (fun m' _ => h m')]
      simpa using h 0
    rw [hz, abs_zero]
    exact le_trans (abs_nonneg (f 0)) (hB 0)

/-- The index of the (unique) non-vanishing translate of `φ` at `z`; junk value `0` if there is
no non-vanishing translate. -/
noncomputable def govIdx {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) : Fin n → ℤ := by
  classical
  exact if h : ∃ m, φ (z + iVec m) ≠ 0 then Classical.choose h else 0

lemma govIdx_spec {n : ℕ} {φ : (Fin n → ℝ) → ℝ} {R : ℝ} (hR : R ≤ 1 / 2)
    (hsupp : Function.support φ ⊆ Metric.ball 0 R) (z : Fin n → ℝ) :
    ∀ m' ≠ govIdx φ z, φ (z + iVec m') = 0 := by
  by_cases h : ∃ m, φ (z + iVec m) ≠ 0
  · intro m' hm'
    by_contra hc
    have hch : φ (z + iVec (Classical.choose h)) ≠ 0 := Classical.choose_spec h
    have heq : m' = Classical.choose h := eq_of_support_ball hR hsupp hc hch
    rw [govIdx, dif_pos h] at hm'
    exact hm' heq
  · intro m' _
    push_neg at h
    exact h m'

/-- The value of `tmA` at a point, in terms of the unique non-vanishing translate of `φ`. -/
lemma tmA_eq_govIdx {n : ℕ} {R lam' : ℝ} (φ : (Fin n → ℝ) → ℝ)
    (γ : (Fin n → ℝ) → Fin n → Fin n → ℝ) (hR : R ≤ 1 / 2)
    (hφsupp : Function.support φ ⊆ Metric.ball 0 R) (z : Fin n → ℝ) (p q : Fin n) :
    tmA φ lam' γ z p q = (if p = q then lam' else 0)
      + φ (z + iVec (govIdx φ z))
          * (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0)) := by
  show (if p = q then lam' else 0)
      + tmPer (fun w => φ w * (γ w p q - (if p = q then lam' else 0))) z = _
  rw [tmPer_eq_of_unique (fun w => φ w * (γ w p q - (if p = q then lam' else 0))) z
      (govIdx φ z) (fun m' hm' => by rw [govIdx_spec hR hφsupp z m' hm', zero_mul])]

/-- The ball `ball 0 R` with `R ≤ 1/2` is contained in the open unit cube. -/
lemma ball_subset_cube {n : ℕ} {R : ℝ} (hR : R ≤ 1 / 2) :
    Metric.ball (0 : Fin n → ℝ) R ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  intro z hz
  rw [Set.mem_pi]
  intro i _
  rw [Metric.mem_ball, dist_zero_right] at hz
  have h1 : |z i| ≤ ‖z‖ := by simpa using norm_le_pi_norm z i
  have h2 : ‖z‖ < 1 / 2 := lt_of_lt_of_le hz hR
  rw [Set.mem_Ioo]
  exact abs_lt.mp (lt_of_le_of_lt h1 h2)

/-- The periodisation of a smooth (real) function supported in the open unit cube is smooth. -/
lemma contDiff_tmPer {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (h : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    ContDiff ℝ (⊤ : ℕ∞) (tmPer f) :=
  (Work.Diff.STE.flat.periodization_re_contDiff_periodic f hf h).1

/-- The periodisation of a smooth (real) function supported in the open unit cube is
`1`-periodic. -/
lemma periodic_tmPer {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (h : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    Work.Diff.STE.Periodic1 (tmPer f) :=
  (Work.Diff.STE.flat.periodization_re_contDiff_periodic f hf h).2

/-- `pdR` is unaffected by subtracting a constant. -/
lemma pdR_sub_const {n : ℕ} (f : (Fin n → ℝ) → ℝ) (c : ℝ) (r : Fin n) (w : Fin n → ℝ) :
    pdR r (fun y => f y - c) w = pdR r f w := by
  simp only [pdR, fderiv_sub_const]

/-- The product rule for `pdR`. -/
lemma pdR_mul_eq {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {r : Fin n} {w : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f w) (hg : DifferentiableAt ℝ g w) :
    pdR r (fun x => f x * g x) w = f w * pdR r g w + g w * pdR r f w := by
  simp only [pdR]
  rw [show (fun x : Fin n → ℝ => f x * g x) = f * g from rfl, fderiv_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ## The summand of `tmA` -/

/-- The summand whose periodisation gives the `(p,q)` entry of `tmA`. -/
def gm {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (γ : (Fin n → ℝ) → Fin n → Fin n → ℝ) (lam' : ℝ)
    (p q : Fin n) (x : Fin n → ℝ) : ℝ :=
  φ x * (γ x p q - (if p = q then lam' else 0))

lemma support_gm_subset {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    {γ : (Fin n → ℝ) → Fin n → Fin n → ℝ} {lam' : ℝ} (p q : Fin n) :
    Function.support (gm φ γ lam' p q) ⊆ Function.support φ := by
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h0
  exact hx (by simp [gm, h0])

lemma tsupport_gm_subset {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    {γ : (Fin n → ℝ) → Fin n → Fin n → ℝ} {lam' : ℝ} (p q : Fin n) :
    tsupport (gm φ γ lam' p q) ⊆ tsupport φ :=
  closure_mono (support_gm_subset (γ := γ) (lam' := lam') p q)

lemma contDiff_gm {n : ℕ} {R lam' : ℝ} {φ : (Fin n → ℝ) → ℝ}
    {γ : (Fin n → ℝ) → Fin n → Fin n → ℝ} (p q : Fin n)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφts : tsupport φ ⊆ Metric.ball 0 R)
    (hγs : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => γ w p q) (Metric.ball 0 R)) :
    ContDiff ℝ (⊤ : ℕ∞) (gm φ γ lam' p q) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport φ
  · have hxb : x ∈ Metric.ball 0 R := hφts hx
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) φ x := hφ.contDiffAt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => γ w p q) x :=
      hγs.contDiffAt (Metric.isOpen_ball.mem_nhds hxb)
    exact h1.mul (h2.sub contDiffAt_const)
  · have hnb : (tsupport φ)ᶜ ∈ nhds x := (isClosed_tsupport φ).isOpen_compl.mem_nhds hx
    have heq : gm φ γ lam' p q =ᶠ[nhds x] (fun _ : Fin n → ℝ => (0 : ℝ)) :=
      Filter.eventually_of_mem hnb (fun y hy => by
        have hyφ : φ y = 0 := by
          by_contra hc
          exact hy (subset_tsupport φ (Function.mem_support.mpr hc))
        simp [gm, hyφ])
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq heq

lemma support_gm_subset_ball {n : ℕ} {R lam' : ℝ} {φ : (Fin n → ℝ) → ℝ}
    {γ : (Fin n → ℝ) → Fin n → Fin n → ℝ} (p q : Fin n)
    (hφsupp : Function.support φ ⊆ Metric.ball 0 R) :
    Function.support (gm φ γ lam' p q) ⊆ Metric.ball 0 R :=
  fun x hx => hφsupp (support_gm_subset (γ := γ) (lam' := lam') p q hx)

lemma abs_gm_le {n : ℕ} {R c Kr lam' : ℝ} {φ : (Fin n → ℝ) → ℝ}
    {γ : (Fin n → ℝ) → Fin n → Fin n → ℝ} (p q : Fin n) (hc : 0 < c) (hKr : 0 ≤ Kr)
    (hlam : 0 < lam') (hlamc : lam' ≤ c)
    (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1)
    (hφsupp : Function.support φ ⊆ Metric.ball 0 R)
    (hγb : ∀ z ∈ Metric.ball 0 R, ∀ p q, |γ z p q| ≤ Kr) :
    ∀ w, |gm φ γ lam' p q w| ≤ Kr + c := by
  intro w
  by_cases hw : φ w = 0
  · simp only [gm, hw, zero_mul, abs_zero]
    linarith
  · have hwb : w ∈ Metric.ball 0 R := hφsupp (Function.mem_support.mpr hw)
    have h1 : |φ w| ≤ 1 := by rw [abs_of_nonneg (hφ0 w)]; exact hφ1 w
    have hδ : |(if (p : Fin n) = q then lam' else 0)| ≤ lam' := by
      by_cases h : p = q
      · rw [if_pos h, abs_of_pos hlam]
      · rw [if_neg h, abs_zero]; linarith
    have h2 : |γ w p q - (if p = q then lam' else 0)| ≤ Kr + lam' :=
      calc |γ w p q - (if p = q then lam' else 0)|
          ≤ |γ w p q| + |(if p = q then lam' else 0)| := by
            rw [sub_eq_add_neg]
            calc |γ w p q + -(if p = q then lam' else 0)|
                ≤ |γ w p q| + |-(if p = q then lam' else 0)| := abs_add_le _ _
              _ = |γ w p q| + |(if p = q then lam' else 0)| := by rw [abs_neg]
        _ ≤ Kr + lam' := add_le_add (hγb w hwb p q) hδ
    calc |gm φ γ lam' p q w| = |φ w| * |γ w p q - (if p = q then lam' else 0)| := by
          simp only [gm, abs_mul]
      _ ≤ 1 * (Kr + lam') := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ ≤ Kr + c := by linarith

/-- The first partial derivatives of the summand `gm` are bounded by
`Mφ * (Kr + c) + Kr` (globally). -/
lemma abs_pdR_gm_le {n : ℕ} {R c Kr Mφ lam' : ℝ} {φ : (Fin n → ℝ) → ℝ}
    {γ : (Fin n → ℝ) → Fin n → Fin n → ℝ} (p q : Fin n)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1)
    (hφd : ∀ z r, |pdR r φ z| ≤ Mφ)
    (hφts : tsupport φ ⊆ Metric.ball 0 R)
    (hγs : ∀ p q, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => γ w p q) (Metric.ball 0 R))
    (hγb : ∀ z ∈ Metric.ball 0 R, ∀ p q, |γ z p q| ≤ Kr)
    (hγd : ∀ z ∈ Metric.ball 0 R, ∀ r p q, |pdR r (fun w => γ w p q) z| ≤ Kr)
    (hMφ : 0 ≤ Mφ) (hKr : 0 ≤ Kr) (hc : 0 < c) (hlam : 0 < lam') (hlamc : lam' ≤ c) :
    ∀ w r, |pdR r (gm φ γ lam' p q) w| ≤ Mφ * (Kr + c) + Kr := by
  intro w r
  have hBnn : (0 : ℝ) ≤ Mφ * (Kr + c) + Kr := by nlinarith
  by_cases hw : w ∈ tsupport (gm φ γ lam' p q)
  · have hwb : w ∈ Metric.ball 0 R := hφts (tsupport_gm_subset (γ := γ) (lam' := lam') p q hw)
    have hφdiff : DifferentiableAt ℝ φ w := hφ.contDiffAt.differentiableAt (by simp)
    have hγdiff : DifferentiableAt ℝ (fun y => γ y p q) w :=
      ((hγs p q).contDiffAt (Metric.isOpen_ball.mem_nhds hwb)).differentiableAt (by simp)
    have hγsub : DifferentiableAt ℝ (fun y => γ y p q - (if p = q then lam' else 0)) w :=
      hγdiff.sub_const _
    have hval : pdR r (gm φ γ lam' p q) w
        = φ w * pdR r (fun y => γ y p q) w
          + (γ w p q - (if p = q then lam' else 0)) * pdR r φ w := by
      rw [show gm φ γ lam' p q
            = fun y => φ y * (γ y p q - (if p = q then lam' else 0)) from rfl]
      rw [pdR_mul_eq (f := φ) (g := fun y => γ y p q - (if p = q then lam' else 0))
        (r := r) (w := w) hφdiff hγsub]
      rw [pdR_sub_const (f := fun y => γ y p q) (c := if p = q then lam' else 0) r w]
    rw [hval]
    have h1 : |pdR r (fun y => γ y p q) w| ≤ Kr := hγd w hwb r p q
    have h4 : |φ w| ≤ 1 := by rw [abs_of_nonneg (hφ0 w)]; exact hφ1 w
    have h2 : |pdR r φ w| ≤ Mφ := hφd w r
    have h3 : |γ w p q - (if p = q then lam' else 0)| ≤ Kr + c := by
      have hδ : |(if (p : Fin n) = q then lam' else 0)| ≤ c := by
        by_cases h : p = q
        · rw [if_pos h, abs_of_pos hlam]; exact hlamc
        · rw [if_neg h, abs_zero]; linarith
      calc |γ w p q - (if p = q then lam' else 0)|
          ≤ |γ w p q| + |(if p = q then lam' else 0)| := by
            rw [sub_eq_add_neg]
            calc |γ w p q + -(if p = q then lam' else 0)| ≤ |γ w p q| + |-(if p = q then lam' else 0)| :=
                  abs_add_le _ _
              _ = |γ w p q| + |(if p = q then lam' else 0)| := by rw [abs_neg]
        _ ≤ Kr + c := add_le_add (hγb w hwb p q) hδ
    calc |φ w * pdR r (fun y => γ y p q) w
            + (γ w p q - (if p = q then lam' else 0)) * pdR r φ w|
        ≤ |φ w * pdR r (fun y => γ y p q) w|
            + |(γ w p q - (if p = q then lam' else 0)) * pdR r φ w| := abs_add_le _ _
      _ = |φ w| * |pdR r (fun y => γ y p q) w|
            + |γ w p q - (if p = q then lam' else 0)| * |pdR r φ w| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * Kr + (Kr + c) * Mφ := by
          apply add_le_add
          · exact mul_le_mul h4 h1 (abs_nonneg _) (by norm_num)
          · exact mul_le_mul h3 h2 (abs_nonneg _) (by linarith)
      _ ≤ Mφ * (Kr + c) + Kr := by ring_nf; linarith
  · have hnb : (tsupport (gm φ γ lam' p q))ᶜ ∈ nhds w :=
      (isClosed_tsupport _).isOpen_compl.mem_nhds hw
    have hzero : pdR r (gm φ γ lam' p q) w = 0 := by
      have heq : gm φ γ lam' p q =ᶠ[nhds w] (fun _ : Fin n → ℝ => (0 : ℝ)) :=
        Filter.eventually_of_mem hnb (fun y hy => by
          by_contra hc
          exact hy (subset_tsupport _ (Function.mem_support.mpr hc)))
      simp only [pdR]
      rw [heq.fderiv_eq]
      rw [show (fun _ : Fin n → ℝ => (0 : ℝ)) = Function.const _ (0 : ℝ) from rfl,
        fderiv_const]
      rfl
    rw [hzero, abs_zero]
    exact hBnn

/-! ## The first partial derivative of a periodisation

The analytic core: a smooth function supported in `ball 0 R`, `R ≤ 1/2`, has a periodisation
whose partial derivatives are bounded by the bound on the partial derivatives of the function
itself. -/

/-- Near every point, the periodisation of a function supported in the open unit cube is a
finite sum of translates. -/
lemma tmPer_eventuallyEq_finset {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) (z : Fin n → ℝ) :
    ∃ S : Finset (Fin n → ℤ),
      (fun y => ∑ m ∈ S, f (y + iVec m)) =ᶠ[nhds z] tmPer f := by
  classical
  set N : Fin n → ℤ := fun i => ⌊|z i|⌋ + 2 with hN
  refine ⟨Fintype.piFinset (fun i => Finset.Icc (-(N i)) (N i)), ?_⟩
  have hBopen : IsOpen (Set.pi Set.univ (fun i : Fin n => Set.Ioo (z i - 1 / 2) (z i + 1 / 2))) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hzB : z ∈ Set.pi Set.univ (fun i : Fin n => Set.Ioo (z i - 1 / 2) (z i + 1 / 2)) := by
    rw [Set.mem_pi]
    intro i _
    rw [Set.mem_Ioo]
    constructor <;> linarith
  refine Filter.eventually_of_mem (hBopen.mem_nhds hzB) (fun y hy => ?_)
  have hyabs : ∀ i, |y i - z i| < 1 / 2 := by
    intro i
    have h := Set.mem_pi.mp hy i (Set.mem_univ i)
    rw [Set.mem_Ioo] at h
    rw [abs_lt]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hsuppC : Function.support (fun v : Fin n → ℝ => ((f v : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro v hv
    rw [Function.mem_support] at hv
    exact hsupp (by
      rw [Function.mem_support]
      intro h0
      exact hv (by rw [h0, Complex.ofReal_zero]))
  have hzero : ∀ m ∉ (Fintype.piFinset (fun i => Finset.Icc (-(N i)) (N i))),
      f (y + iVec m) = 0 := by
    intro m hm
    by_contra hc
    have h2 : (fun v : Fin n → ℝ => ((f v : ℝ) : ℂ)) (y + iVec m) ≠ 0 := by simpa using hc
    have h3 := abs_lt_floor_add_two_of_support hsuppC hyabs h2
    exact hm (by
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      have hi := h3 i
      simp only [hN] at hi ⊢
      have h4 := (abs_lt.mp hi).1
      have h5 := (abs_lt.mp hi).2
      constructor <;> omega)
  have hzeroC : ∀ m ∉ (Fintype.piFinset (fun i => Finset.Icc (-(N i)) (N i))),
      ((f (y + iVec m) : ℝ) : ℂ) = 0 := fun m hm => by rw [hzero m hm]; simp
  rw [tmPer, tsum_eq_sum hzeroC, ← Complex.ofReal_sum]
  simp

lemma tmPer_pdR_le_tsupport {n : ℕ} (f : (Fin n → ℝ) → ℝ) (R B : ℝ) (hR : R ≤ 1 / 2)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hts : tsupport f ⊆ Metric.ball 0 R)
    (hB : ∀ (w : Fin n → ℝ) (r : Fin n), |Work.Diff.STE.pdR r f w| ≤ B) :
    ∀ (z : Fin n → ℝ) (r : Fin n),
      |Work.Diff.STE.pdR r (Work.Diff.STE.B3.tmPer f) z| ≤ B := by
  intro z r
  have hsupp : Function.support f ⊆ Metric.ball 0 R := fun x hx => hts (subset_tsupport f hx)
  have hcube : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    fun x hx => ball_subset_cube hR (hsupp hx)
  obtain ⟨S, hS⟩ := tmPer_eventuallyEq_finset hcube z
  have hBnn : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hB z r)
  have hderiv : pdR r (tmPer f) z = ∑ m ∈ S, pdR r f (z + iVec m) := by
    have hsum : (fun y => ∑ m ∈ S, f (y + iVec m))
        = ∑ m ∈ S, (fun y => f (y + iVec m)) := by
      funext y
      rw [Finset.sum_apply]
    have h2 : fderiv ℝ (tmPer f) z = ∑ m ∈ S, fderiv ℝ (fun y => f (y + iVec m)) z := by
      rw [hS.symm.fderiv_eq, hsum]
      exact fderiv_sum (fun m _ => (hf.contDiffAt.differentiableAt (by simp)).comp z
        ((differentiable_id.differentiableAt).add_const _))
    have h3 : ∀ m, fderiv ℝ (fun y => f (y + iVec m)) z = fderiv ℝ f (z + iVec m) :=
      fun m => fderiv_comp_add_right (f := f) (x := z) (iVec m)
    simp only [pdR]
    rw [h2]
    rw [ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun m _ => by rw [h3 m])
  have hzerosupp : ∀ m, pdR r f (z + iVec m) ≠ 0 → z + iVec m ∈ tsupport f := by
    intro m hm
    by_contra hc
    have hnb : (tsupport f)ᶜ ∈ nhds (z + iVec m) := (isClosed_tsupport f).isOpen_compl.mem_nhds hc
    have heq : f =ᶠ[nhds (z + iVec m)] (fun _ : Fin n → ℝ => (0 : ℝ)) :=
      Filter.eventually_of_mem hnb (fun v hv => by
        by_contra h2
        exact hv (subset_tsupport f (Function.mem_support.mpr h2)))
    exact hm (by
      simp only [pdR]
      rw [heq.fderiv_eq]
      rw [show (fun _ : Fin n → ℝ => (0 : ℝ)) = Function.const _ (0 : ℝ) from rfl, fderiv_const]
      rfl)
  have hone : (S.filter (fun m => pdR r f (z + iVec m) ≠ 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact eq_of_mem_ball hR (hts (hzerosupp a ha.2)) (hts (hzerosupp b hb.2))
  have hstep : ∑ m ∈ S, |pdR r f (z + iVec m)|
      = ∑ m ∈ S.filter (fun m => pdR r f (z + iVec m) ≠ 0), |pdR r f (z + iVec m)| :=
    (Finset.sum_subset (Finset.filter_subset _ _) (fun m hmS hmT => by
      simp only [Finset.mem_filter, not_and, not_not] at hmT
      rw [hmT hmS, abs_zero])).symm
  rw [hderiv]
  calc |∑ m ∈ S, pdR r f (z + iVec m)| ≤ ∑ m ∈ S, |pdR r f (z + iVec m)| :=
        Finset.abs_sum_le_sum_abs (fun m => pdR r f (z + iVec m)) S
    _ = ∑ m ∈ S.filter (fun m => pdR r f (z + iVec m) ≠ 0), |pdR r f (z + iVec m)| := hstep
    _ ≤ ∑ m ∈ S.filter (fun m => pdR r f (z + iVec m) ≠ 0), B :=
        Finset.sum_le_sum (fun m _ => hB (z + iVec m) r)
    _ = B * ((S.filter (fun m => pdR r f (z + iVec m) ≠ 0)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ B * 1 := by
        apply mul_le_mul_of_nonneg_left _ hBnn
        exact_mod_cast hone
    _ = B := by ring

/-! ## Bounds for the double sums -/

lemma sum_ite_delta {n : ℕ} (lam' : ℝ) (ξ : Fin n → ℝ) :
    (∑ p, ∑ q, (if p = q then lam' else 0) * ξ p * ξ q) = lam' * ∑ p, (ξ p) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl]; ring
  · intro q _ hq
    rw [if_neg (fun h : p = q => hq h.symm)]
    simp
  · intro hp
    exact absurd (Finset.mem_univ p) hp

lemma sum_sum_add {n : ℕ} (u v : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    (∑ p, ∑ q, (u p q + v p q) * ξ p * ξ q)
      = (∑ p, ∑ q, u p q * ξ p * ξ q) + ∑ p, ∑ q, v p q * ξ p * ξ q := by
  have h1 : ∀ p q : Fin n, (u p q + v p q) * ξ p * ξ q
      = u p q * ξ p * ξ q + v p q * ξ p * ξ q := fun p q => by ring
  simp only [h1, Finset.sum_add_distrib]

lemma sum_sum_sub {n : ℕ} (u v : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    (∑ p, ∑ q, (u p q - v p q) * ξ p * ξ q)
      = (∑ p, ∑ q, u p q * ξ p * ξ q) - ∑ p, ∑ q, v p q * ξ p * ξ q := by
  have h1 : ∀ p q : Fin n, (u p q - v p q) * ξ p * ξ q
      = u p q * ξ p * ξ q - v p q * ξ p * ξ q := fun p q => by ring
  simp only [h1, Finset.sum_sub_distrib]

lemma sum_sum_smul {n : ℕ} (c : ℝ) (u : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    (∑ p, ∑ q, (c * u p q) * ξ p * ξ q) = c * ∑ p, ∑ q, u p q * ξ p * ξ q := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  ring

theorem tmA_props {n : ℕ} (R c Kr Mφ : ℝ) (hR : R ≤ 1 / 2) (hc : 0 < c) (hKr : 0 ≤ Kr)
    (hMφ : 0 ≤ Mφ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : (Fin n → ℝ) → ℝ) (γ : (Fin n → ℝ) → Fin n → Fin n → ℝ) (lam' : ℝ),
        0 < lam' → lam' ≤ c →
        ContDiff ℝ (⊤ : ℕ∞) φ → (∀ z, 0 ≤ φ z) → (∀ z, φ z ≤ 1) →
        (∀ z r, |Work.Diff.STE.pdR r φ z| ≤ Mφ) →
        tsupport φ ⊆ Metric.ball 0 R →
        (∀ p q, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => γ w p q) (Metric.ball 0 R)) →
        (∀ z ∈ Metric.ball 0 R, ∀ p q, γ z p q = γ z q p) →
        (∀ z ∈ Metric.ball 0 R, ∀ ξ : Fin n → ℝ,
          c * ∑ p, (ξ p) ^ 2 ≤ ∑ p, ∑ q, γ z p q * ξ p * ξ q) →
        (∀ z ∈ Metric.ball 0 R, ∀ p q, |γ z p q| ≤ Kr) →
        (∀ z ∈ Metric.ball 0 R, ∀ r p q,
          |Work.Diff.STE.pdR r (fun w => γ w p q) z| ≤ Kr) →
        (∀ z p q, |tmA φ lam' γ z p q| ≤ C) ∧
        (∀ z r p q, |Work.Diff.STE.pdR r (fun w => tmA φ lam' γ w p q) z| ≤ C) ∧
        (∀ z p q, tmA φ lam' γ z p q = tmA φ lam' γ z q p) ∧
        (∀ z ξ : Fin n → ℝ,
          lam' * ∑ p, (ξ p) ^ 2 ≤ ∑ p, ∑ q, tmA φ lam' γ z p q * ξ p * ξ q) ∧
        ContDiff ℝ (⊤ : ℕ∞) (tmA φ lam' γ) ∧
        Work.Diff.STE.Periodic1 (tmA φ lam' γ) := by
  refine ⟨max (2 * c + Kr) (Mφ * (Kr + c) + Kr), ?_, ?_⟩
  · exact le_trans (by linarith : (0 : ℝ) ≤ 2 * c + Kr) (le_max_left _ _)
  · intro φ γ lam' hlam hlamc hφ hφ0 hφ1 hφd hφts hγs hγsymm hγpos hγb hγd
    have hφsupp : Function.support φ ⊆ Metric.ball 0 R :=
      fun x hx => hφts (subset_tsupport φ hx)
    have hgmcube : ∀ p q : Fin n, Function.support (gm φ γ lam' p q) ⊆
        Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
      fun p q x hx => ball_subset_cube hR (hφsupp (support_gm_subset (γ := γ) (lam' := lam') p q hx))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (1) pointwise bound
      intro z p q
      rw [tmA_eq_govIdx φ γ hR hφsupp z p q]
      have hδ : |(if (p : Fin n) = q then lam' else 0)| ≤ lam' := by
        by_cases hpq : p = q
        · rw [if_pos hpq, abs_of_pos hlam]
        · rw [if_neg hpq, abs_zero]; linarith
      have hterm : |φ (z + iVec (govIdx φ z))
          * (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0))| ≤ Kr + lam' := by
        by_cases hw : φ (z + iVec (govIdx φ z)) = 0
        · simp only [hw, zero_mul, abs_zero]; linarith
        · have hwb : z + iVec (govIdx φ z) ∈ Metric.ball 0 R :=
            hφsupp (Function.mem_support.mpr hw)
          have h1 : |φ (z + iVec (govIdx φ z))| ≤ 1 := by
            rw [abs_of_nonneg (hφ0 _)]; exact hφ1 _
          have h2 : |γ (z + iVec (govIdx φ z)) p q
              - (if p = q then lam' else 0)| ≤ Kr + lam' :=
            calc |γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0)|
                ≤ |γ (z + iVec (govIdx φ z)) p q| + |(if p = q then lam' else 0)| := by
                  rw [sub_eq_add_neg]
                  calc |γ (z + iVec (govIdx φ z)) p q + -(if p = q then lam' else 0)|
                      ≤ |γ (z + iVec (govIdx φ z)) p q| + |-(if p = q then lam' else 0)| :=
                        abs_add_le _ _
                    _ = |γ (z + iVec (govIdx φ z)) p q| + |(if p = q then lam' else 0)| := by
                        rw [abs_neg]
              _ ≤ Kr + lam' := add_le_add (hγb _ hwb p q) hδ
          calc |φ (z + iVec (govIdx φ z))
                  * (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0))|
              = |φ (z + iVec (govIdx φ z))|
                  * |γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0)| := abs_mul _ _
            _ ≤ 1 * (Kr + lam') := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
            _ ≤ Kr + lam' := by linarith
      calc |(if p = q then lam' else 0)
              + φ (z + iVec (govIdx φ z))
                  * (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0))|
          ≤ |(if p = q then lam' else 0)|
              + |φ (z + iVec (govIdx φ z))
                  * (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0))| := abs_add_le _ _
        _ ≤ lam' + (Kr + lam') := add_le_add hδ hterm
        _ ≤ max (2 * c + Kr) (Mφ * (Kr + c) + Kr) :=
            le_trans (by linarith) (le_max_left _ _)
    · -- (2) first derivative bound
      intro z r p q
      have hmain : |pdR r (tmPer (gm φ γ lam' p q)) z| ≤ Mφ * (Kr + c) + Kr :=
        tmPer_pdR_le_tsupport (gm φ γ lam' p q) R (Mφ * (Kr + c) + Kr) hR
          (contDiff_gm p q hφ hφts (hγs p q))
          (fun x hx => hφts (tsupport_gm_subset (γ := γ) (lam' := lam') p q hx))
          (abs_pdR_gm_le p q hφ hφ0 hφ1 hφd hφts hγs hγb hγd hMφ hKr hc hlam hlamc) z r
      have heq : pdR r (fun w => tmA φ lam' γ w p q) z = pdR r (tmPer (gm φ γ lam' p q)) z := by
        rw [show gm φ γ lam' p q
              = fun y => φ y * (γ y p q - (if p = q then lam' else 0)) from rfl]
        simp only [tmA, pdR, fderiv_const_add]
      rw [heq]
      exact le_trans hmain (le_max_right _ _)
    · -- (3) symmetry
      intro z p q
      by_cases hpq : p = q
      · subst hpq; rfl
      · rw [tmA_eq_govIdx φ γ hR hφsupp z p q, tmA_eq_govIdx φ γ hR hφsupp z q p]
        by_cases hw : φ (z + iVec (govIdx φ z)) = 0
        · rw [if_neg hpq, if_neg (fun h : q = p => hpq h.symm), hw, zero_mul, zero_mul]
        · rw [if_neg hpq, if_neg (fun h : q = p => hpq h.symm),
            hγsymm _ (hφsupp (Function.mem_support.mpr hw)) p q]
    · -- (4) positive definiteness
      intro z ξ
      have hexp : (∑ p, ∑ q, tmA φ lam' γ z p q * ξ p * ξ q)
          = (∑ p, ∑ q, (if p = q then lam' else 0) * ξ p * ξ q)
            + φ (z + iVec (govIdx φ z))
              * (∑ p, ∑ q, (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0))
                  * ξ p * ξ q) := by
        have h1 : ∀ p q : Fin n, tmA φ lam' γ z p q
            = (if p = q then lam' else 0) + φ (z + iVec (govIdx φ z))
                * (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0)) :=
          fun p q => tmA_eq_govIdx φ γ hR hφsupp z p q
        simp only [h1]
        rw [sum_sum_add]
        rw [sum_sum_smul]
      rw [hexp, sum_ite_delta]
      have hkey : 0 ≤ φ (z + iVec (govIdx φ z))
          * (∑ p, ∑ q, (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0))
              * ξ p * ξ q) := by
        have hγm : (∑ p, ∑ q, (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0))
              * ξ p * ξ q)
            = (∑ p, ∑ q, γ (z + iVec (govIdx φ z)) p q * ξ p * ξ q)
              - lam' * ∑ p, (ξ p) ^ 2 := by
          rw [sum_sum_sub, sum_ite_delta]
        rw [hγm]
        by_cases hw : φ (z + iVec (govIdx φ z)) = 0
        · rw [hw, zero_mul]
        · have hwb : z + iVec (govIdx φ z) ∈ Metric.ball 0 R :=
            hφsupp (Function.mem_support.mpr hw)
          have hpos := hγpos _ hwb ξ
          have hnorm : (0 : ℝ) ≤ ∑ p, (ξ p) ^ 2 := Finset.sum_nonneg (fun p _ => sq_nonneg _)
          have : (0 : ℝ) ≤ (∑ p, ∑ q, γ (z + iVec (govIdx φ z)) p q * ξ p * ξ q)
              - lam' * ∑ p, (ξ p) ^ 2 := by nlinarith [hpos, hlamc, hnorm]
          exact mul_nonneg (hφ0 _) this
      linarith
    · -- (5) smoothness
      refine contDiff_pi' (fun p => contDiff_pi' (fun q => ?_))
      have hs : ContDiff ℝ (⊤ : ℕ∞) (tmPer (gm φ γ lam' p q)) :=
        contDiff_tmPer (contDiff_gm p q hφ hφts (hγs p q)) (hgmcube p q)
      have heq : (fun z => tmA φ lam' γ z p q)
          = fun z => (if p = q then lam' else 0) + tmPer (gm φ γ lam' p q) z := rfl
      rw [heq]
      exact contDiff_const.add hs
    · -- (6) periodicity
      intro i x
      ext p q
      have hper : Work.Diff.STE.Periodic1 (tmPer (gm φ γ lam' p q)) :=
        periodic_tmPer (contDiff_gm p q hφ hφts (hγs p q)) (hgmcube p q)
      have hval := hper i x
      have h1 : tmA φ lam' γ (x + Pi.single i 1) p q
          = (if p = q then lam' else 0) + tmPer (gm φ γ lam' p q) (x + Pi.single i 1) := rfl
      have h2 : tmA φ lam' γ x p q
          = (if p = q then lam' else 0) + tmPer (gm φ γ lam' p q) x := rfl
      rw [h1, h2, hval]

end Work.Diff.STE.B3
