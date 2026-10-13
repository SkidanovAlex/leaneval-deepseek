import Mathlib
import Submission.Work.WilE4.CAD.Defs
import Submission.Work.WilE4.CAD.seq_extract
import Submission.Work.WilE4.CAD.sign_stable_Icc
import Submission.Work.WilE4.CAD.sign_eval_abs_large
import Submission.Work.WilE4.CAD.exists_pos_sign_change_simple_root
import Submission.Work.WilE4.CAD.exists_sign_eq_of_simple_root

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open scoped Classical

variable {m k : ℕ}

/-! ## Elementary algebraic and analytic facts -/

/-- Coprime polynomials have no common root. -/
theorem isCoprime_no_common_root {f g : Polynomial ℝ} (h : IsCoprime f g) {y : ℝ}
    (hf : f.IsRoot y) (hg : g.IsRoot y) : False := by
  obtain ⟨a, b, hab⟩ := h
  have h1 : a.eval y * f.eval y + b.eval y * g.eval y = 1 := by
    have h2 := congrArg (fun p : Polynomial ℝ => p.eval y) hab
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] using h2
  simp only [Polynomial.IsRoot.def.mp hf, Polynomial.IsRoot.def.mp hg, mul_zero,
    add_zero] at h1
  exact one_ne_zero h1.symm

/-- A polynomial coprime to its derivative has no multiple root. -/
theorem isCoprime_derivative_root_ne_zero {f : Polynomial ℝ} (h : IsCoprime f f.derivative)
    {y : ℝ} (hf : f.IsRoot y) : f.derivative.eval y ≠ 0 := by
  intro h0
  obtain ⟨a, b, hab⟩ := h
  have h1 : a.eval y * f.eval y + b.eval y * f.derivative.eval y = 1 := by
    have h2 := congrArg (fun p : Polynomial ℝ => p.eval y) hab
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] using h2
  simp only [Polynomial.IsRoot.def.mp hf, h0, mul_zero, add_zero] at h1
  exact one_ne_zero h1.symm

/-- IVT: opposite signs at the endpoints give a root in between. -/
theorem exists_root_of_eval_mul_neg {f : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : f.eval a * f.eval b < 0) : ∃ y ∈ Set.Icc a b, f.IsRoot y := by
  rcases mul_neg_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h0 : (0 : ℝ) ∈ Set.Icc (f.eval b) (f.eval a) := ⟨le_of_lt h2, le_of_lt h1⟩
    obtain ⟨y, hy, hy'⟩ := intermediate_value_Icc' hab f.continuous.continuousOn h0
    exact ⟨y, hy, Polynomial.IsRoot.def.mpr hy'⟩
  · have h0 : (0 : ℝ) ∈ Set.Icc (f.eval a) (f.eval b) := ⟨le_of_lt h1, le_of_lt h2⟩
    obtain ⟨y, hy, hy'⟩ := intermediate_value_Icc hab f.continuous.continuousOn h0
    exact ⟨y, hy, Polynomial.IsRoot.def.mpr hy'⟩

/-- A continuous function non-zero on an open interval has constant sign there. -/
theorem sign_eq_of_nonzero_Ioo {g : ℝ → ℝ} (hg : Continuous g) {a b x y : ℝ}
    (hne : ∀ z ∈ Set.Ioo a b, g z ≠ 0) (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    SignType.sign (g x) = SignType.sign (g y) := by
  have hpos : 0 < g x * g y := by
    rcases lt_trichotomy (g x * g y) 0 with hlt | heq | hgt
    · exfalso
      have hmem : (0 : ℝ) ∈ Set.uIcc (g x) (g y) := by
        rcases mul_neg_iff.mp hlt with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [Set.uIcc_of_ge (le_of_lt (lt_trans h2 h1))]
          exact ⟨le_of_lt h2, le_of_lt h1⟩
        · rw [Set.uIcc_of_le (le_of_lt (lt_trans h1 h2))]
          exact ⟨le_of_lt h1, le_of_lt h2⟩
      obtain ⟨t, ht, ht0⟩ := intermediate_value_uIcc hg.continuousOn hmem
      have ht' : t ∈ Set.Ioo a b := by
        rcases le_total x y with hxy | hxy
        · rw [Set.uIcc_of_le hxy] at ht
          exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
        · rw [Set.uIcc_of_ge hxy] at ht
          exact ⟨lt_of_lt_of_le hy.1 ht.1, lt_of_le_of_lt ht.2 hx.2⟩
      exact hne t ht' ht0
    · exact absurd heq (mul_ne_zero (hne x hx) (hne y hy))
    · exact hgt
  rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [sign_pos h1, sign_pos h2]
  · rw [sign_neg h1, sign_neg h2]

/-- Finitely many polynomials, each non-zero at `y`, are simultaneously non-zero on a common
symmetric neighbourhood of `y`. -/
theorem exists_pos_eval_ne {s : Finset (Polynomial ℝ)} {y : ℝ}
    (h : ∀ p ∈ s, p.eval y ≠ 0) :
    ∃ δ > 0, ∀ p ∈ s, ∀ z, |z - y| < δ → p.eval z ≠ 0 := by
  classical
  revert h
  refine Finset.induction ?_ ?_ s
  · intro _
    exact ⟨1, one_pos, by simp⟩
  · intro a t hat ih h
    have ha : a.eval y ≠ 0 := h a (Finset.mem_insert_self a t)
    have ht : ∀ p ∈ t, p.eval y ≠ 0 := fun p hp => h p (Finset.mem_insert_of_mem hp)
    obtain ⟨δ₁, hδ₁, h₁⟩ := ih ht
    obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.mem_nhds_iff.mp
      ((Polynomial.continuous a).continuousAt.tendsto.eventually (isOpen_ne.mem_nhds ha))
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun p hp z hz => ?_⟩
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact h₂ (by rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hz (min_le_right _ _))
    · exact h₁ p hp' z (lt_of_lt_of_le hz (min_le_left _ _))

/-- The sign of a continuous function non-zero at a point is locally constant there. -/
theorem eventually_sign_eq_of_ne_zero {f : (Fin m → ℝ) → ℝ} {x : Fin m → ℝ}
    (hf : ContinuousAt f x) (hne : f x ≠ 0) :
    ∀ᶠ x' in 𝓝 x, SignType.sign (f x') = SignType.sign (f x) := by
  rcases lt_trichotomy (f x) 0 with hneg | hzero | hpos
  · exact (hf.tendsto.eventually (isOpen_Iio.mem_nhds hneg)).mono
      (fun x' hx' => by rw [sign_neg hx', sign_neg hneg])
  · exact absurd hzero hne
  · exact (hf.tendsto.eventually (isOpen_Ioi.mem_nhds hpos)).mono
      (fun x' hx' => by rw [sign_pos hx', sign_pos hpos])

/-- The sign of the limit of a sequence of constant sign is that sign. -/
theorem sign_eq_of_tendsto {u : ℕ → ℝ} {L : ℝ} (hu : Tendsto u atTop (𝓝 L)) (hL : L ≠ 0)
    {s : SignType} (hs : ∀ᶠ n in atTop, SignType.sign (u n) = s) : SignType.sign L = s := by
  have h1 : Tendsto (fun n => SignType.sign (u n)) atTop (𝓝 (SignType.sign L)) :=
    (continuousAt_sign_of_ne_zero hL).tendsto.comp hu
  have h2 : Tendsto (fun n => SignType.sign (u n)) atTop (𝓝 s) :=
    Filter.Tendsto.congr' (hs.mono fun n hn => hn.symm) tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

/-! ## Local openness of the realised-sign-vector set -/

/-- If a sign vector is realised at `x`, and the non-degeneracy conditions hold at `x`, then it is
realised for all `x'` near `x`. -/
theorem realized_nhds_of_realized {P : Fin k → MvPolynomial (Fin (m+1)) ℝ} {d : Fin k → ℕ}
    {x : Fin m → ℝ} (hgood : Good P d x) {v : Fin k → SignType} (hv : realized P x v) :
    ∀ᶠ x' in 𝓝 x, realized P x' v := by
  obtain ⟨y, hy⟩ := hv
  by_cases hJ : ∃ i, (q (P i) x).eval y = 0
  · obtain ⟨i₀, hi₀⟩ := hJ
    have huniq : ∀ i, (q (P i) x).eval y = 0 → i = i₀ := by
      intro i hi
      by_contra hne
      exact isCoprime_no_common_root (hgood.2.1 i i₀ hne)
        (Polynomial.IsRoot.def.mpr hi) (Polynomial.IsRoot.def.mpr hi₀)
    have hv0 : v i₀ = 0 := by rw [← hy i₀, hi₀, sign_zero]
    have hne : ∀ i, i ≠ i₀ → (q (P i) x).eval y ≠ 0 := fun i hi h => hi (huniq i h)
    obtain ⟨δ, hδ, hδ'⟩ := exists_pos_eval_ne
      (s := (Finset.univ.filter (fun i : Fin k => i ≠ i₀)).image (fun i => q (P i) x))
      (y := y) (by
        intro p hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        exact hne i (Finset.mem_filter.mp hi).2)
    have hsimple : (q (P i₀) x).derivative.eval y ≠ 0 :=
      isCoprime_derivative_root_ne_zero (hgood.2.2 i₀) (Polynomial.IsRoot.def.mpr hi₀)
    obtain ⟨z₁, hz₁d, hz₁s⟩ := exists_sign_eq_of_simple_root
      (Polynomial.IsRoot.def.mpr hi₀) hsimple SignType.neg (by decide) (ε := δ / 2) (by linarith)
    obtain ⟨z₂, hz₂d, hz₂s⟩ := exists_sign_eq_of_simple_root
      (Polynomial.IsRoot.def.mpr hi₀) hsimple SignType.pos (by decide) (ε := δ / 2) (by linarith)
    have hz₁neg : (q (P i₀) x).eval z₁ < 0 :=
      sign_eq_neg_one_iff.mp (by rw [hz₁s]; exact SignType.neg_eq_neg_one)
    have hz₂pos : 0 < (q (P i₀) x).eval z₂ :=
      sign_eq_one_iff.mp (by rw [hz₂s]; exact SignType.pos_eq_one)
    have hmem : ∀ i, i ≠ i₀ → q (P i) x ∈
        (Finset.univ.filter (fun i : Fin k => i ≠ i₀)).image (fun i => q (P i) x) :=
      fun i hi => Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    have hneIoo : ∀ i, i ≠ i₀ → ∀ t ∈ Set.Ioo (y - δ) (y + δ),
        (q (P i) x).eval t ≠ 0 := by
      intro i hi t ht
      exact hδ' (q (P i) x) (hmem i hi) t (by
        rw [abs_lt]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hW1 : ∀ᶠ x' in 𝓝 x, (q (P i₀) x').eval z₁ < 0 ∧ 0 < (q (P i₀) x').eval z₂ :=
      ((continuous_q_eval_fixed (P i₀) z₁).continuousAt.tendsto.eventually
          (isOpen_Iio.mem_nhds hz₁neg)).and
        ((continuous_q_eval_fixed (P i₀) z₂).continuousAt.tendsto.eventually
          (isOpen_Ioi.mem_nhds hz₂pos))
    have hstab : ∀ᶠ x' in 𝓝 x, ∀ i ∈ (Finset.univ.filter (fun i : Fin k => i ≠ i₀)),
        ∀ z ∈ Set.Icc (y - δ / 2) (y + δ / 2),
          SignType.sign ((q (P i) x').eval z) = v i := by
      refine (eventually_all_finset (Finset.univ.filter (fun i : Fin k => i ≠ i₀))).mpr
        fun i hi => ?_
      have hine : i ≠ i₀ := (Finset.mem_filter.mp hi).2
      have hyIoo : y ∈ Set.Ioo (y - δ) (y + δ) :=
        ⟨by linarith [hδ], by linarith [hδ]⟩
      have hne' : ∀ z ∈ Set.Icc (y - δ / 2) (y + δ / 2), (q (P i) x).eval z ≠ 0 := fun z hz =>
        hδ' (q (P i) x) (hmem i hine) z (by
          rw [abs_lt]
          exact ⟨by linarith [hz.1, hδ], by linarith [hz.2, hδ]⟩)
      refine (sign_stable_Icc (F := fun p : (Fin m → ℝ) × ℝ => (q (P i) p.1).eval p.2)
        (continuous_q_eval (P i)) hne').mono ?_
      intro x' hx' z hz
      have hzIoo : z ∈ Set.Ioo (y - δ) (y + δ) :=
        ⟨by linarith [hz.1, hδ], by linarith [hz.2, hδ]⟩
      rw [hx' z hz]
      exact (sign_eq_of_nonzero_Ioo (g := fun t => (q (P i) x).eval t)
        (Polynomial.continuous (q (P i) x)) (hneIoo i hine) (x := z) (y := y)
        hzIoo hyIoo).trans (hy i)
    refine (hW1.and hstab).mono fun x' hx' => ?_
    obtain ⟨⟨hz₁', hz₂'⟩, hstab'⟩ := hx'
    have hab : min z₁ z₂ ≤ max z₁ z₂ := min_le_max
    have hmul : (q (P i₀) x').eval (min z₁ z₂) * (q (P i₀) x').eval (max z₁ z₂) < 0 := by
      rcases le_total z₁ z₂ with h | h
      · rw [min_eq_left h, max_eq_right h]
        exact mul_neg_of_neg_of_pos hz₁' hz₂'
      · rw [min_eq_right h, max_eq_left h, mul_comm]
        exact mul_neg_of_neg_of_pos hz₁' hz₂'
    obtain ⟨r, hr, hrroot⟩ := exists_root_of_eval_mul_neg hab hmul
    have hminlt : y - δ / 2 < min z₁ z₂ :=
      lt_min (by linarith [(abs_lt.mp hz₁d).1]) (by linarith [(abs_lt.mp hz₂d).1])
    have hmaxlt : max z₁ z₂ < y + δ / 2 :=
      max_lt (by linarith [(abs_lt.mp hz₁d).2]) (by linarith [(abs_lt.mp hz₂d).2])
    have hrIoo : r ∈ Set.Ioo (y - δ / 2) (y + δ / 2) := ⟨lt_of_lt_of_le hminlt hr.1,
      lt_of_le_of_lt hr.2 hmaxlt⟩
    refine ⟨r, fun i => ?_⟩
    by_cases hi : i = i₀
    · subst hi
      rw [Polynomial.IsRoot.def.mp hrroot, sign_zero]
      exact hv0.symm
    · exact hstab' i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩) r
        ⟨le_of_lt hrIoo.1, le_of_lt hrIoo.2⟩
  · have hne : ∀ i, (q (P i) x).eval y ≠ 0 := fun i h => hJ ⟨i, h⟩
    refine ((Filter.eventually_all).mpr fun i =>
      (eventually_sign_eq_of_ne_zero ((continuous_q_eval_fixed (P i) y).continuousAt)
        (hne i)).mono (fun x' hx' => hx'.trans (hy i))).mono ?_
    exact fun x' hx' => ⟨y, hx'⟩

/-! ## Local closedness of the realised-sign-vector set -/

/-- Sequential closedness, limit-point case. -/
theorem realized_of_tendsto_bdd {P : Fin k → MvPolynomial (Fin (m+1)) ℝ} {d : Fin k → ℕ}
    {x : Fin m → ℝ} (hgood : ∀ᶠ x' in 𝓝 x, Good P d x')
    {a : ℕ → Fin m → ℝ} (ha : Tendsto a atTop (𝓝 x))
    {w : ℕ → ℝ} {w₀ : ℝ} (hw : Tendsto w atTop (𝓝 w₀))
    {v : Fin k → SignType}
    (hv : ∀ᶠ n in atTop, ∀ i, SignType.sign ((q (P i) (a n)).eval (w n)) = v i) :
    realized P x v := by
  have hxg : Good P d x := hgood.self_of_nhds
  have hlim : ∀ i, Tendsto (fun n => (q (P i) (a n)).eval (w n)) atTop
      (𝓝 ((q (P i) x).eval w₀)) := fun i =>
    ((continuous_q_eval (P i)).tendsto (x, w₀)).comp (ha.prodMk_nhds hw)
  have hsub : ∀ i, v i = 0 → (q (P i) x).eval w₀ = 0 := by
    intro i hi
    have hzero : ∀ᶠ n in atTop, (q (P i) (a n)).eval (w n) = 0 :=
      hv.mono fun n hn => sign_eq_zero_iff.mp (by rw [hn i, hi])
    have h2 : Tendsto (fun n => (q (P i) (a n)).eval (w n)) atTop (𝓝 0) :=
      Filter.Tendsto.congr' (hzero.mono fun n hn => hn.symm) tendsto_const_nhds
    exact tendsto_nhds_unique (hlim i) h2
  have hJs : ∀ i j, (q (P i) x).eval w₀ = 0 → (q (P j) x).eval w₀ = 0 → i = j := by
    intro i j hi hj
    by_contra hne
    exact isCoprime_no_common_root (hxg.2.1 i j hne)
      (Polynomial.IsRoot.def.mpr hi) (Polynomial.IsRoot.def.mpr hj)
  have hsign : ∀ i, (q (P i) x).eval w₀ ≠ 0 →
      SignType.sign ((q (P i) x).eval w₀) = v i := fun i hne =>
    sign_eq_of_tendsto (hlim i) hne (hv.mono fun n hn => hn i)
  by_cases hJZ : ∀ i, ((q (P i) x).eval w₀ = 0 ↔ v i = 0)
  · refine ⟨w₀, fun i => ?_⟩
    by_cases hi : v i = 0
    · rw [(hJZ i).mpr hi, sign_zero, hi]
    · exact hsign i (fun h => hi ((hJZ i).mp h))
  · obtain ⟨i₀, hi₀L, hi₀v⟩ : ∃ i, (q (P i) x).eval w₀ = 0 ∧ v i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hJZ fun i => ⟨hc i, hsub i⟩
    have huniqJ : ∀ i, (q (P i) x).eval w₀ = 0 → i = i₀ := fun i hi => hJs i i₀ hi hi₀L
    have hsimple : (q (P i₀) x).derivative.eval w₀ ≠ 0 :=
      isCoprime_derivative_root_ne_zero (hxg.2.2 i₀) (Polynomial.IsRoot.def.mpr hi₀L)
    have hsign_ne : ∀ i, i ≠ i₀ → SignType.sign ((q (P i) x).eval w₀) = v i :=
      fun i hi => hsign i (fun h => hi (huniqJ i h))
    obtain ⟨δ, hδ, hδ'⟩ := exists_pos_eval_ne
      (s := (Finset.univ.filter (fun i : Fin k => i ≠ i₀)).image (fun i => q (P i) x))
      (y := w₀) (by
        intro p hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        exact fun h0 => (Finset.mem_filter.mp hi).2 (huniqJ i h0))
    obtain ⟨z, hzd, hzs⟩ := exists_sign_eq_of_simple_root
      (Polynomial.IsRoot.def.mpr hi₀L) hsimple (v i₀) hi₀v (ε := δ / 2) (by linarith)
    refine ⟨z, fun i => ?_⟩
    by_cases hi : i = i₀
    · subst hi; exact hzs
    · have hmem : q (P i) x ∈ (Finset.univ.filter (fun i : Fin k => i ≠ i₀)).image
          (fun i => q (P i) x) :=
        Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      obtain ⟨hd1, hd2⟩ := abs_lt.mp hzd
      have hzIoo : z ∈ Set.Ioo (w₀ - δ) (w₀ + δ) :=
        ⟨by linarith, by linarith⟩
      have hwIoo : w₀ ∈ Set.Ioo (w₀ - δ) (w₀ + δ) :=
        ⟨by linarith, by linarith⟩
      rw [sign_eq_of_nonzero_Ioo (g := fun t => (q (P i) x).eval t)
        (Polynomial.continuous (q (P i) x))
        (fun t ht => hδ' (q (P i) x) hmem t (by
          rw [abs_lt]
          exact ⟨by linarith [ht.1], by linarith [ht.2]⟩))
        (x := z) (y := w₀) hzIoo hwIoo, hsign_ne i hi]

/-- Sequential closedness of the realised-sign-vector set, in general. -/
theorem realized_of_tendsto {P : Fin k → MvPolynomial (Fin (m+1)) ℝ} {d : Fin k → ℕ}
    {x : Fin m → ℝ} (hgood : ∀ᶠ x' in 𝓝 x, Good P d x')
    {a : ℕ → Fin m → ℝ} (ha : Tendsto a atTop (𝓝 x))
    {v : Fin k → SignType} (hv : ∀ n, realized P (a n) v) :
    realized P x v := by
  classical
  choose w hw using hv
  have hw' : ∀ᶠ n in atTop, ∀ i, SignType.sign ((q (P i) (a n)).eval (w n)) = v i :=
    Filter.Eventually.of_forall hw
  by_cases hbdd : ∃ M : ℝ, ∀ᶠ n in atTop, |w n| ≤ M
  · obtain ⟨M, hM⟩ := hbdd
    have hfreq : ∃ᶠ n in atTop, w n ∈ Set.Icc (-M) M :=
      (hM.mono fun n hn => abs_le.mp hn).frequently
    obtain ⟨w₀, _, φ, hφmono, hφlim⟩ :=
      (isCompact_Icc : IsCompact (Set.Icc (-M) M)).tendsto_subseq' hfreq
    exact realized_of_tendsto_bdd (P := P) (d := d) (x := x) hgood
      (ha.comp hφmono.tendsto_atTop) hφlim (hφmono.tendsto_atTop.eventually hw')
  · push_neg at hbdd
    have hR : ∀ i, ∃ R > 0, ∀ᶠ y in 𝓝 x, ∀ z : ℝ, R ≤ |z| →
        SignType.sign ((q (P i) y).eval z)
          = SignType.sign ((q (P i) y).coeff (d i)) * SignType.sign z ^ (d i) := fun i =>
      sign_eval_abs_large (fun y => q (P i) y) (continuous_q_coeff (P i))
        (hgood.mono fun y hy => hy.1 i)
    set Rtot : ℝ := 1 + ∑ i, Classical.choose (hR i) with hRtot
    have hRi_le : ∀ i, Classical.choose (hR i) ≤ Rtot := by
      intro i
      have h2 : Classical.choose (hR i) ≤ ∑ j, Classical.choose (hR j) :=
        Finset.single_le_sum (fun j _ => le_of_lt (Classical.choose_spec (hR j)).1)
          (Finset.mem_univ i)
      rw [hRtot]; linarith
    have hRm : ∀ i, ∀ᶠ y in 𝓝 x, ∀ z : ℝ, Rtot ≤ |z| →
        SignType.sign ((q (P i) y).eval z)
          = SignType.sign ((q (P i) y).coeff (d i)) * SignType.sign z ^ (d i) := fun i =>
      ((Classical.choose_spec (hR i)).2).mono fun y hy z hz => hy z (le_trans (hRi_le i) hz)
    have hcoeff : ∀ i, ∀ᶠ y in 𝓝 x,
        SignType.sign ((q (P i) y).coeff (d i)) = SignType.sign ((q (P i) x).coeff (d i)) := by
      intro i
      have hne : (q (P i) x).coeff (d i) ≠ 0 := by
        have h0 : (q (P i) x).natDegree = d i := hgood.self_of_nhds.1 i
        have hnz : (q (P i) x) ≠ 0 := by
          intro hz
          have hcc := hgood.self_of_nhds.2.2 i
          rw [hz, Polynomial.derivative_zero] at hcc
          exact not_isCoprime_zero_zero hcc
        rw [← h0]
        exact Polynomial.leadingCoeff_ne_zero.mpr hnz
      exact eventually_sign_eq_of_ne_zero (continuous_q_coeff (P i) (d i)).continuousAt hne
    have hB : ∀ᶠ n in atTop, ∀ i, SignType.sign ((q (P i) (a n)).coeff (d i))
        = SignType.sign ((q (P i) x).coeff (d i)) :=
      (Filter.eventually_all).mpr fun i => ha.eventually (hcoeff i)
    have hC : ∀ᶠ n in atTop, ∀ i, ∀ z : ℝ, Rtot ≤ |z| →
        SignType.sign ((q (P i) (a n)).eval z)
          = SignType.sign ((q (P i) (a n)).coeff (d i)) * SignType.sign z ^ (d i) :=
      (Filter.eventually_all).mpr fun i => ha.eventually (hRm i)
    have hev : ∀ᶠ n in atTop,
        (∀ i, SignType.sign ((q (P i) (a n)).eval (w n)) = v i) ∧
        (∀ i, SignType.sign ((q (P i) (a n)).coeff (d i))
          = SignType.sign ((q (P i) x).coeff (d i))) ∧
        (∀ i, ∀ z : ℝ, Rtot ≤ |z| → SignType.sign ((q (P i) (a n)).eval z)
          = SignType.sign ((q (P i) (a n)).coeff (d i)) * SignType.sign z ^ (d i)) :=
      (hw'.and (hB.and hC)).mono fun n h => ⟨h.1, h.2.1, h.2.2⟩
    obtain ⟨n₀, hD₀, hA₀, hB₀, hC₀⟩ :=
      (((hbdd Rtot).mono fun n h => le_of_lt h).and_eventually hev).exists
    refine ⟨w n₀, fun i => ?_⟩
    have h1 : SignType.sign ((q (P i) (a n₀)).eval (w n₀))
        = SignType.sign ((q (P i) (a n₀)).coeff (d i)) * SignType.sign (w n₀) ^ (d i) :=
      hC₀ i (w n₀) hD₀
    have h2 : SignType.sign ((q (P i) x).eval (w n₀))
        = SignType.sign ((q (P i) x).coeff (d i)) * SignType.sign (w n₀) ^ (d i) :=
      (Classical.choose_spec (hR i)).2.self_of_nhds (w n₀) (le_trans (hRi_le i) hD₀)
    rw [h2, ← hB₀ i, ← h1, hA₀ i]

/-- If a sign vector is not realised at `x` and the non-degeneracy conditions hold near `x`, it is
not realised on a neighbourhood of `x`. -/
theorem not_realized_nhds {P : Fin k → MvPolynomial (Fin (m+1)) ℝ} {d : Fin k → ℕ}
    {x : Fin m → ℝ} (hgood : ∀ᶠ x' in 𝓝 x, Good P d x') {v : Fin k → SignType}
    (hv : ¬ realized P x v) : ∀ᶠ x' in 𝓝 x, ¬ realized P x' v := by
  by_contra hcon
  obtain ⟨u, hu, huu⟩ := seq_extract (x₀ := x) (P := fun x' => ¬ realized P x' v) hcon
  exact hv (realized_of_tendsto hgood hu fun n => Classical.not_not.mp (huu n))

/-! ## Main theorem -/

/-- Local constancy of the set of realized sign vectors of a family of polynomials in the last
variable, under the non-degeneracy conditions (fixed degrees, squarefree members, no common roots
between distinct members). -/
theorem type_local {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m+1)) ℝ) (d : Fin k → ℕ)
    (x₀ : Fin m → ℝ)
    (hdeg : Filter.Eventually (fun x => ∀ i,
      ((MvPolynomial.finSuccEquiv ℝ m (P i)).map (MvPolynomial.eval x)).natDegree = d i) (nhds x₀))
    (hcop : Filter.Eventually (fun x => ∀ i j, i ≠ j →
      IsCoprime ((MvPolynomial.finSuccEquiv ℝ m (P i)).map (MvPolynomial.eval x))
        ((MvPolynomial.finSuccEquiv ℝ m (P j)).map (MvPolynomial.eval x))) (nhds x₀))
    (hsq : Filter.Eventually (fun x => ∀ i,
      IsCoprime ((MvPolynomial.finSuccEquiv ℝ m (P i)).map (MvPolynomial.eval x))
        (((MvPolynomial.finSuccEquiv ℝ m (P i)).map (MvPolynomial.eval x)).derivative)) (nhds x₀)) :
    Filter.Eventually (fun x => ∀ v : (Fin k → SignType),
      ((∃ y, ∀ i, SignType.sign
          (((MvPolynomial.finSuccEquiv ℝ m (P i)).map (MvPolynomial.eval x)).eval y) = v i) ↔
       (∃ y, ∀ i, SignType.sign
          (((MvPolynomial.finSuccEquiv ℝ m (P i)).map (MvPolynomial.eval x₀)).eval y) = v i))) (nhds x₀) := by
  have hgood_all : ∀ᶠ x in 𝓝 x₀, Good P d x :=
    (good_iff_eventual).mpr ⟨hdeg, hcop, hsq⟩
  obtain ⟨s, hs, hsmem⟩ := Filter.eventually_iff_exists_mem.mp hgood_all
  obtain ⟨ρ, hρ, hρs⟩ := Metric.mem_nhds_iff.mp hs
  have hx0 : x₀ ∈ Metric.ball x₀ ρ := Metric.mem_ball_self hρ
  have key : ∀ x ∈ Metric.ball x₀ ρ, ∀ v : Fin k → SignType,
      (realized P x v ↔ realized P x₀ v) := by
    intro x hx v
    set A : Set (Fin m → ℝ) := Metric.ball x₀ ρ ∩ {x' | realized P x' v} with hA
    have hgoodx : ∀ y ∈ Metric.ball x₀ ρ, ∀ᶠ x' in 𝓝 y, Good P d x' := fun y hy =>
      Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hy)
        fun x' hx' => hsmem x' (hρs hx')
    have hAopen : IsOpen A := by
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨hy, hyr⟩
      exact Filter.mem_of_superset
        (Filter.inter_mem
          (realized_nhds_of_realized (Filter.Eventually.self_of_nhds (hgoodx y hy)) hyr)
          (Metric.isOpen_ball.mem_nhds hy))
        fun x' hx' => ⟨hx'.2, hx'.1⟩
    have hBAopen : IsOpen (Metric.ball x₀ ρ \ A) := by
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨hy, hyA⟩
      have hyr : ¬ realized P y v := fun hrv => hyA ⟨hy, hrv⟩
      exact Filter.mem_of_superset
        (Filter.inter_mem (not_realized_nhds (hgoodx y hy) hyr)
          (Metric.isOpen_ball.mem_nhds hy))
        fun x' hx' => ⟨hx'.2, fun hmem => hx'.1 hmem.2⟩
    have hsub : Metric.ball x₀ ρ ⊆ A ∪ (Metric.ball x₀ ρ \ A) := fun y hy => by
      by_cases h : y ∈ A
      · exact Or.inl h
      · exact Or.inr ⟨hy, h⟩
    rcases Classical.em (realized P x₀ v) with hv0 | hv0
    · have hne : (Metric.ball x₀ ρ ∩ A).Nonempty := ⟨x₀, hx0, hx0, hv0⟩
      have hB := IsPreconnected.subset_left_of_subset_union hAopen hBAopen
        (Set.disjoint_left.mpr fun a ha hb => hb.2 ha) hsub hne Metric.isPreconnected_ball
      exact ⟨fun _ => hv0, fun _ => (hB hx).2⟩
    · have hne : (Metric.ball x₀ ρ ∩ (Metric.ball x₀ ρ \ A)).Nonempty :=
        ⟨x₀, hx0, hx0, fun h => hv0 h.2⟩
      have hB := IsPreconnected.subset_left_of_subset_union hBAopen hAopen
        (Set.disjoint_left.mpr fun a ha hb => ha.2 hb) (fun y hy => by
          rcases hsub hy with h | h
          · exact Or.inr h
          · exact Or.inl h) hne Metric.isPreconnected_ball
      exact ⟨fun hrv => absurd (hB hx) (fun hb => hb.2 ⟨hx, hrv⟩), fun h => absurd h hv0⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x₀ hρ) fun x hx v => key x hx v

end Work.WilE4.CAD
