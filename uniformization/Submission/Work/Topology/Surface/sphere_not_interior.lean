import Mathlib
import Submission.Work.Topology.Surface.windingWrapper

/-!
# A point of the unit circle is not an interior point of a chart of the disc

Let `z : ℂ` with `‖z‖ = 1`.  The main theorem `false_of_homeomorph_nhds_sphere` says that there is
**no** homeomorphism from a neighbourhood of `z` in the closed unit disc onto an open subset of `ℂ`.

The proof is the classical winding-number argument.  Take a small half-disc `V = ball z δ ∩ 𝔻̄`
inside the given neighbourhood.  The point `z` is a *boundary* point of the disc, so `V \ {z}` is
star-shaped with respect to `p = (1 - δ/2) • z` (`starShaped_punctured_disc`); in particular every
loop in `V \ {z}` is null-homotopic there.  On the other side, if `Φ` maps the neighbourhood onto
an open subset of `ℂ`, then a small round circle `σ` around `Φ z` lifts back along `Φ⁻¹` to a loop
in `V \ {z}`, and pushing the contraction of that loop forward along `Φ` exhibits `σ` as
null-homotopic in `ℂ \ {Φ z}`; by homotopy invariance of winding numbers (`HasArg`) the circle would
then have winding number zero about its own centre, which is false (`notHasArg_roundCircle`).
-/

namespace Work.Topology.Surface

open Set Metric

noncomputable section

/-! ## The round circle winds once around its centre -/

/-- If `exp (x * I) = 1` for a real `x`, then `x` is an integer multiple of `2 * π`. -/
lemma exists_int_of_exp_eq_one {x : ℝ} (h : Complex.exp (((x : ℝ) : ℂ) * Complex.I) = 1) :
    ∃ n : ℤ, x = 2 * Real.pi * n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have h2 := congrArg Complex.im hn
  have h3 : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  rw [h3] at h2
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, sub_zero, add_zero] at h2
  norm_num at h2
  linarith [h2]

/-- The round circle of radius `r` about `c` has winding number `± 1` about `c`, so it admits no
continuous `1`-periodic argument function. -/
theorem notHasArg_roundCircle (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ¬ Commons.Topology.Winding.HasArg (circleCurve c r) c := by
  rintro ⟨θ, hθc, hθper, hθrep⟩
  have hexp : ∀ t : ℝ, Complex.exp (((θ t : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    intro t
    have h1 : circleCurve c r t - c
        = (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
      simp [circleCurve]
    have hn : ‖circleCurve c r t - c‖
        = ‖(r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)‖ :=
      congrArg (fun w : ℂ => ‖w‖) h1
    have hnormreal : ‖(r : ℂ)‖ = r := by simp [hr.le]
    have hrw : (‖circleCurve c r t - c‖ : ℂ) = (r : ℂ) := by
      rw [hn, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hnormreal]
    have h := hθrep t
    rw [hrw] at h
    rw [h1] at h
    exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hr)) h).symm
  have hmem : ∀ t : ℝ, ∃ n : ℤ, θ t - 2 * Real.pi * t = 2 * Real.pi * n := by
    intro t
    apply exists_int_of_exp_eq_one
    rw [show (((θ t - 2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
        = ((θ t : ℝ) : ℂ) * Complex.I - (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_sub, hexp t, div_self (Complex.exp_ne_zero _)]
  set g : ℝ → ℝ := fun t => θ t - 2 * Real.pi * t with hg
  have hgcont : Continuous g := hθc.sub (continuous_const.mul continuous_id)
  have hgmem : ∀ t : ℝ, ∃ n : ℤ, g t = 2 * Real.pi * n := fun t => hmem t
  have hdisc : ∀ {x y : ℝ}, |x - y| < 2 * Real.pi →
      (∃ n : ℤ, x = 2 * Real.pi * n) → (∃ n : ℤ, y = 2 * Real.pi * n) → x = y := by
    intro x y hxy ⟨n1, h1⟩ ⟨n2, h2⟩
    have h3 : |2 * Real.pi * ((n1 : ℝ) - n2)| < 2 * Real.pi := by
      rw [show 2 * Real.pi * ((n1 : ℝ) - n2) = 2 * Real.pi * n1 - 2 * Real.pi * n2 by ring]
      rw [← h1, ← h2]; exact hxy
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h3
    have h4 : ((n1 : ℝ) - n2) = 0 := by
      by_contra hne
      have h5 : (n1 - n2 : ℤ) ≠ 0 := by
        intro hh
        have hh' : n1 = n2 := by omega
        exact hne (by rw [hh']; ring)
      have h6 : (1 : ℝ) ≤ |((n1 : ℝ) - n2)| := by
        have hsub : ((n1 : ℝ) - (n2 : ℝ)) = ((n1 - n2 : ℤ) : ℝ) := by push_cast; ring
        rw [hsub, ← Int.cast_abs, ← Int.cast_one]
        have hpos : (0 : ℤ) < |n1 - n2| := abs_pos.mpr h5
        exact_mod_cast (by omega : (1 : ℤ) ≤ |n1 - n2|)
      have h7 : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
      nlinarith [abs_nonneg ((n1 : ℝ) - n2)]
    rw [h1, h2]
    have : (n1 : ℝ) = n2 := by linarith
    rw [this]
  have hAclosed : IsClosed {t : ℝ | g t = g 0} := isClosed_eq hgcont continuous_const
  have hAopen : IsOpen {t : ℝ | g t = g 0} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    obtain ⟨ε, hε, hε'⟩ := Metric.continuousAt_iff.mp hgcont.continuousAt (2 * Real.pi) h2pi
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hε) ?_
    intro u hu
    have hu' : dist (g u) (g t) < 2 * Real.pi := hε' hu
    rw [Real.dist_eq] at hu'
    exact (hdisc hu' (hgmem u) (hgmem t)).trans ht
  have hAclopen : IsClopen {t : ℝ | g t = g 0} := ⟨hAclosed, hAopen⟩
  have huniv : (Set.univ : Set ℝ) ⊆ {t : ℝ | g t = g 0} :=
    isPreconnected_univ.subset_isClopen hAclopen ⟨0, Set.mem_univ 0, rfl⟩
  have h1 : g 1 = g 0 := huniv trivial
  have h2 : θ (1 : ℝ) = θ 0 := by simpa using hθper 0
  simp only [hg] at h1
  have h3 : θ 1 - 2 * Real.pi = θ 0 := by
    have := h1
    simp only [mul_one] at this
    linarith [this, h2]
  linarith [h2, h3, Real.pi_pos]

/-- The circle `circleCurve c r` is `1`-periodic. -/
lemma circleCurve_periodic (c : ℂ) (r : ℝ) : Function.Periodic (circleCurve c r) 1 := by
  intro t
  have h : Complex.exp (((2 * Real.pi * (t + 1) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨1, ?_⟩
    push_cast
    ring
  simp only [circleCurve]
  rw [h]

/-! ## The pierced disc is star-shaped -/

/-- **The pierced disc is star-shaped.**  For `‖z‖ = 1` and `0 < δ < 2`, the point
`p = (1 - δ/2) • z` sees every point of `(ball z δ ∩ 𝔻̄) \ {z}` without the segment meeting `z`. -/
theorem starShaped_punctured_disc {z : ℂ} (hz : ‖z‖ = 1) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 2) :
    ∀ w ∈ Metric.ball z δ ∩ Metric.closedBall (0 : ℂ) 1, w ≠ z → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (1 - s) • ((1 - δ / 2 : ℝ) • z) + s • w ∈ Metric.ball z δ ∩ Metric.closedBall (0 : ℂ) 1 ∧
        (1 - s) • ((1 - δ / 2 : ℝ) • z) + s • w ≠ z := by
  intro w hw hwne s hs
  obtain ⟨hwb, hwcb⟩ := hw
  obtain ⟨hs0, hs1⟩ := hs
  have hwnorm : ‖w‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hwcb
  have hpnorm : ‖((1 - δ / 2 : ℝ) • z : ℂ)‖ = 1 - δ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hz, mul_one]
  have hpball : ((1 - δ / 2 : ℝ) • z : ℂ) ∈ Metric.ball z δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : ((1 - δ / 2 : ℝ) • z : ℂ) - z = (-(δ / 2) : ℝ) • z := by
      module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < δ / 2),
      hz, mul_one]
    linarith
  have hpcb : ((1 - δ / 2 : ℝ) • z : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hpnorm]
    linarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (convex_ball z δ) hpball hwb (by linarith) hs0 (by ring)
  · exact (convex_closedBall (0 : ℂ) 1) hpcb hwcb (by linarith) hs0 (by ring)
  · intro hcontra
    have h1 : ‖(1 - s) • ((1 - δ / 2 : ℝ) • z : ℂ)‖
        = (1 - s) * ‖((1 - δ / 2 : ℝ) • z : ℂ)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s)]
    have h2 : ‖s • w‖ = s * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    have htri : ‖(1 - s) • ((1 - δ / 2 : ℝ) • z : ℂ) + s • w‖
        ≤ (1 - s) * ‖((1 - δ / 2 : ℝ) • z : ℂ)‖ + s * ‖w‖ := by
      rw [← h1, ← h2]
      exact norm_add_le _ _
    have hbound : (1 - s) * ‖((1 - δ / 2 : ℝ) • z : ℂ)‖ + s * ‖w‖
        ≤ 1 - (δ / 2) * (1 - s) := by
      have ha : (1 - s) * ‖((1 - δ / 2 : ℝ) • z : ℂ)‖ ≤ (1 - s) * (1 - δ / 2) :=
        mul_le_mul_of_nonneg_left (le_of_eq hpnorm) (by linarith)
      have hb : s * ‖w‖ ≤ s * 1 := mul_le_mul_of_nonneg_left hwnorm hs0
      nlinarith [ha, hb]
    have hle : (1 : ℝ) ≤ 1 - (δ / 2) * (1 - s) := by
      calc (1 : ℝ) = ‖z‖ := hz.symm
        _ = ‖(1 - s) • ((1 - δ / 2 : ℝ) • z : ℂ) + s • w‖ := by rw [hcontra]
        _ ≤ (1 - s) * ‖((1 - δ / 2 : ℝ) • z : ℂ)‖ + s * ‖w‖ := htri
        _ ≤ 1 - (δ / 2) * (1 - s) := hbound
    have hs_eq : s = 1 := by
      have h1' : (0 : ℝ) < δ / 2 := by linarith
      have h2' : (δ / 2) * (1 - s) ≤ 0 := by linarith
      have h3' : 1 - s ≤ 0 := by
        by_contra hc
        push Not at hc
        nlinarith
      linarith
    rw [hs_eq] at hcontra
    simp only [sub_self, zero_smul, one_smul, zero_add] at hcontra
    exact hwne hcontra

/-! ## The main theorem -/

/-- **No homeomorphism from a neighbourhood of a circle point to an open set.**  Let `‖z‖ = 1`,
`0 < δ < 2`, and let `N` be a set of the closed unit disc containing the half-disc
`ball z δ ∩ 𝔻̄`.  Then there is no homeomorphism from `N` onto an open subset `W` of `ℂ`.

(The hypothesis `hround` is the classical fact `notHasArg_roundCircle`, passed in so that this
theorem has no further dependencies.) -/
theorem false_of_homeomorph_nhds_sphere {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) 1) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ < 2) {N : Set ↥(Metric.closedBall (0 : ℂ) 1)}
    (hNV : ∀ w (hw : w ∈ Metric.ball z δ ∩ Metric.closedBall (0 : ℂ) 1),
      (⟨w, hw.2⟩ : ↥(Metric.closedBall (0 : ℂ) 1)) ∈ N)
    {W : Set ℂ} (hW : IsOpen W) (Φ : ↥N ≃ₜ ↥W)
    (hround : ∀ (c : ℂ) (r : ℝ), 0 < r →
      ¬ Commons.Topology.Winding.HasArg (circleCurve c r) c) : False := by
  have hz1 : ‖z‖ = 1 := by
    have h := Metric.mem_sphere.mp hz
    rwa [dist_eq_norm, sub_zero] at h
  set V : Set ℂ := Metric.ball z δ ∩ Metric.closedBall (0 : ℂ) 1 with hV
  have hzV : z ∈ V := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_self]; exact hδ
    · rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_eq hz1
  -- the parametrising map `V → ℂ`
  let f : ↥V → ℂ := fun y =>
    ((Φ (⟨⟨(y : ℂ), y.2.2⟩, hNV (y : ℂ) y.2⟩ : ↥N) : ↥W) : ℂ)
  set c₀ : ℂ := f ⟨z, hzV⟩ with hc₀
  have hfcont : Continuous f :=
    continuous_subtype_val.comp
      (Φ.continuous.comp (Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _))
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : (⟨⟨(a : ℂ), a.2.2⟩, hNV (a : ℂ) a.2⟩ : ↥N)
        = ⟨⟨(b : ℂ), b.2.2⟩, hNV (b : ℂ) b.2⟩ := by
      apply Φ.injective
      exact Subtype.ext hab
    refine Subtype.ext ?_
    have := congrArg (fun q : ↥N => ((q : ↥(Metric.closedBall (0 : ℂ) 1)) : ℂ)) h1
    simpa using this
  -- the range of `f` is open
  have hSopen : IsOpen {y : ↥N | (y : ℂ) ∈ Metric.ball z δ} :=
    Metric.isOpen_ball.preimage (continuous_subtype_val.comp continuous_subtype_val)
  have hrange : Set.range f
      = Subtype.val '' (Φ '' {y : ↥N | (y : ℂ) ∈ Metric.ball z δ}) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Φ (⟨⟨(y : ℂ), y.2.2⟩, hNV (y : ℂ) y.2⟩ : ↥N),
        ⟨⟨⟨(y : ℂ), y.2.2⟩, hNV (y : ℂ) y.2⟩, y.2.1, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨p, hp, hΦq⟩, rfl⟩
      refine ⟨⟨(p : ℂ), hp, p.1.2⟩, ?_⟩
      show ((Φ (⟨⟨(p : ℂ), p.1.2⟩, hNV (p : ℂ) ⟨hp, p.1.2⟩⟩ : ↥N) : ↥W) : ℂ) = (q : ℂ)
      rw [show (⟨⟨(p : ℂ), p.1.2⟩, hNV (p : ℂ) ⟨hp, p.1.2⟩⟩ : ↥N) = p from
        Subtype.ext (Subtype.ext rfl), hΦq]
  have hopen : IsOpen (Set.range f) := by
    rw [hrange]
    exact hW.isOpenMap_subtype_val _ (Φ.isOpenMap _ hSopen)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen c₀ ⟨⟨z, hzV⟩, rfl⟩
  -- the round circle about `c₀`
  have hnormρ2 : ‖(((ρ / 2 : ℝ)) : ℂ)‖ = ρ / 2 := by
    simp [show (0 : ℝ) ≤ ρ from le_of_lt hρ]
  set σ : ℝ → ℂ := circleCurve c₀ (ρ / 2) with hσ
  have hσsub : ∀ t, σ t - c₀
      = ((ρ / 2 : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    intro t
    have h : σ t = c₀ + ((ρ / 2 : ℝ) : ℂ)
        * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
      rw [hσ]; rfl
    rw [h, add_sub_cancel_left]
  have hσcont : Continuous σ := by
    have h : σ = fun t : ℝ => c₀ + ((ρ / 2 : ℝ) : ℂ)
        * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
      rw [hσ]; rfl
    rw [h]
    fun_prop
  have hσmem : ∀ t, σ t ∈ Set.range f := by
    intro t
    apply hρsub
    rw [Metric.mem_ball, dist_eq_norm, hσsub t, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [hnormρ2]
    linarith
  have hσne : ∀ t, σ t ≠ c₀ := by
    intro t h
    have hn : ‖σ t - c₀‖ = ρ / 2 := by
      rw [hσsub t, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hnormρ2]
    rw [h, sub_self, norm_zero] at hn
    linarith
  have hσW : ∀ t, σ t ∈ W := by
    intro t
    obtain ⟨y, hy⟩ := hσmem t
    rw [← hy]
    exact (Φ (⟨⟨(y : ℂ), y.2.2⟩, hNV (y : ℂ) y.2⟩ : ↥N) : ↥W).2
  have hτmem : ∀ t, (((Φ.symm ⟨σ t, hσW t⟩) : ↥N) : ℂ) ∈ V := by
    intro t
    obtain ⟨y, hy⟩ := hσmem t
    have hΦ : (⟨σ t, hσW t⟩ : ↥W) = Φ (⟨⟨(y : ℂ), y.2.2⟩, hNV (y : ℂ) y.2⟩ : ↥N) := by
      refine Subtype.ext ?_
      show σ t = ((Φ (⟨⟨(y : ℂ), y.2.2⟩, hNV (y : ℂ) y.2⟩ : ↥N) : ↥W) : ℂ)
      rw [← hy]
    have h2 : Φ.symm ⟨σ t, hσW t⟩ = (⟨⟨(y : ℂ), y.2.2⟩, hNV (y : ℂ) y.2⟩ : ↥N) := by
      rw [hΦ, Φ.symm_apply_apply]
    rw [h2]
    exact y.2
  let τ : ℝ → ↥V := fun t => ⟨((Φ.symm ⟨σ t, hσW t⟩ : ↥N) : ℂ), hτmem t⟩
  have hτcont : Continuous τ := by
    refine Continuous.subtype_mk ?_ hτmem
    exact (continuous_subtype_val.comp continuous_subtype_val).comp
      (Φ.symm.continuous.comp (Continuous.subtype_mk hσcont _))
  have hfτ : ∀ t, f (τ t) = σ t := by
    intro t
    have h1 : (⟨⟨((τ t : ↥V) : ℂ), (τ t : ↥V).2.2⟩,
        hNV ((τ t : ↥V) : ℂ) (τ t : ↥V).2⟩ : ↥N) = Φ.symm ⟨σ t, hσW t⟩ :=
      Subtype.ext (Subtype.ext rfl)
    show ((Φ (⟨⟨((τ t : ↥V) : ℂ), (τ t : ↥V).2.2⟩,
      hNV ((τ t : ↥V) : ℂ) (τ t : ↥V).2⟩ : ↥N) : ↥W) : ℂ) = σ t
    rw [h1, Φ.apply_symm_apply]
  -- the base point of the star-shapedness
  set p : ℂ := (1 - δ / 2 : ℝ) • z with hp
  have hpnorm : ‖p‖ = 1 - δ / 2 := by
    rw [hp, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hz1, mul_one]
  have hpV : p ∈ V := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have hsub : p - z = (-(δ / 2) : ℝ) • z := by
        rw [hp]
        module
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < δ / 2),
        hz1, mul_one]
      linarith
    · rw [Metric.mem_closedBall, dist_zero_right, hpnorm]
      linarith
  have hτne : ∀ t, ((τ t : ↥V) : ℂ) ≠ z := by
    intro t h
    have h2 : τ t = ⟨z, hzV⟩ := Subtype.ext h
    have h3 : σ t = c₀ := by rw [hc₀, ← hfτ t, h2]
    exact hσne t h3
  have hstar : ∀ t s, s ∈ Set.Icc (0 : ℝ) 1 →
      (1 - s) • p + s • ((τ t : ↥V) : ℂ) ∈ V ∧
        (1 - s) • p + s • ((τ t : ↥V) : ℂ) ≠ z := by
    intro t s hs
    have h := starShaped_punctured_disc hz1 hδ hδ2 ((τ t : ↥V) : ℂ) (τ t : ↥V).2 (hτne t) s hs
    simpa [hp, hV] using h
  -- the clamping variable
  let cl : ℝ → ℝ := fun s => max 0 (min 1 s)
  have hclcont : Continuous cl :=
    continuous_const.max (continuous_const.min continuous_id)
  have hclmem : ∀ s, cl s ∈ Set.Icc (0 : ℝ) 1 := by
    intro s
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  let Q : ℝ × ℝ → ↥N := fun q => ⟨⟨(1 - cl q.2) • p + cl q.2 • ((τ q.1 : ↥V) : ℂ),
      (hstar q.1 (cl q.2) (hclmem q.2)).1.2⟩, hNV _ (hstar q.1 (cl q.2) (hclmem q.2)).1⟩
  have hQcont : Continuous Q := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    have h1 : Continuous (fun q : ℝ × ℝ => cl q.2) := hclcont.comp continuous_snd
    have h2 : Continuous (fun q : ℝ × ℝ => ((τ q.1 : ↥V) : ℂ)) :=
      continuous_subtype_val.comp (hτcont.comp continuous_fst)
    exact ((continuous_const.sub h1).smul continuous_const).add (h1.smul h2)
  let K : ℝ × ℝ → ℂ := fun q => ((Φ (Q q) : ↥W) : ℂ)
  have hKcont : Continuous K := continuous_subtype_val.comp (Φ.continuous.comp hQcont)
  have hKper : ∀ t s, K (t + 1, s) = K (t, s) := by
    intro t s
    have hτper : τ (t + 1) = τ t := by
      refine Subtype.ext ?_
      have hσper : σ (t + 1) = σ t := by
        rw [hσ]; exact circleCurve_periodic c₀ (ρ / 2) t
      have h₁ : (⟨σ (t + 1), hσW (t + 1)⟩ : ↥W) = ⟨σ t, hσW t⟩ := Subtype.ext hσper
      show ((Φ.symm ⟨σ (t + 1), hσW (t + 1)⟩ : ↥N) : ℂ)
        = ((Φ.symm ⟨σ t, hσW t⟩ : ↥N) : ℂ)
      rw [h₁]
    have hQper : Q (t + 1, s) = Q (t, s) := by
      refine Subtype.ext (Subtype.ext ?_)
      show (1 - cl s) • p + cl s • ((τ (t + 1) : ↥V) : ℂ)
        = (1 - cl s) • p + cl s • ((τ t : ↥V) : ℂ)
      rw [hτper]
    show ((Φ (Q (t + 1, s)) : ↥W) : ℂ) = ((Φ (Q (t, s)) : ↥W) : ℂ)
    rw [hQper]
  have hKnz : ∀ q, K q ≠ c₀ := by
    rintro ⟨t, s⟩ h
    have h1 : Φ (Q (t, s)) = Φ (⟨⟨z, hzV.2⟩, hNV z hzV⟩ : ↥N) :=
      Subtype.ext (h.trans hc₀)
    have hQ : Q (t, s) = (⟨⟨z, hzV.2⟩, hNV z hzV⟩ : ↥N) := Φ.injective h1
    have hval : (1 - cl s) • p + cl s • ((τ t : ↥V) : ℂ) = z := by
      have hh := congrArg (fun q : ↥N => ((q : ↥(Metric.closedBall (0 : ℂ) 1)) : ℂ)) hQ
      show (↑(Q (t, s)) : ℂ) = z
      simpa using hh
    exact (hstar t (cl s) (hclmem s)).2 hval
  let F : ℝ × ℝ → ℂ := fun q => K q - c₀
  have hFcont : Continuous F := hKcont.sub continuous_const
  have hFper : ∀ t s, F (t + 1, s) = F (t, s) := by
    intro t s
    show K (t + 1, s) - c₀ = K (t, s) - c₀
    rw [hKper t s]
  have hFnz : ∀ t s, F (t, s) ≠ 0 := by
    intro t s h
    exact hKnz (t, s) (sub_eq_zero.mp h)
  have hiff := Commons.Topology.Winding.hasArg_homotopy_invariant hFcont hFper hFnz
  have hQ0 : ∀ t, Q (t, 0) = (⟨⟨p, hpV.2⟩, hNV p hpV⟩ : ↥N) := by
    intro t
    refine Subtype.ext (Subtype.ext ?_)
    show (1 - cl 0) • p + cl 0 • ((τ t : ↥V) : ℂ) = p
    simp [cl]
  have hF0const : (fun t => F (t, 0))
      = fun _ => ((Φ (⟨⟨p, hpV.2⟩, hNV p hpV⟩ : ↥N) : ↥W) : ℂ) - c₀ := by
    funext t
    show ((Φ (Q (t, 0)) : ↥W) : ℂ) - c₀ = ((Φ (⟨⟨p, hpV.2⟩, hNV p hpV⟩ : ↥N) : ↥W) : ℂ) - c₀
    rw [hQ0 t]
  have hLHS : Commons.Topology.Winding.HasArg (fun t => F (t, 0)) 0 := by
    rw [hF0const]
    refine ⟨fun _ => Complex.arg (((Φ (⟨⟨p, hpV.2⟩, hNV p hpV⟩ : ↥N) : ↥W) : ℂ) - c₀),
      continuous_const, fun t => rfl, fun t => ?_⟩
    simp only [sub_zero]
    exact (Complex.norm_mul_exp_arg_mul_I _).symm
  have hRHS : Commons.Topology.Winding.HasArg (fun t => F (t, 1)) 0 := hiff.mp hLHS
  have hQ1 : ∀ t, Q (t, 1) = (⟨⟨((τ t : ↥V) : ℂ), (τ t : ↥V).2.2⟩,
      hNV ((τ t : ↥V) : ℂ) (τ t : ↥V).2⟩ : ↥N) := by
    intro t
    refine Subtype.ext (Subtype.ext ?_)
    show (1 - cl 1) • p + cl 1 • ((τ t : ↥V) : ℂ) = ((τ t : ↥V) : ℂ)
    simp [cl]
  have hR1 : ∀ t, F (t, 1)
      = ((ρ / 2 : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    intro t
    show ((Φ (Q (t, 1)) : ↥W) : ℂ) - c₀ = _
    rw [hQ1 t]
    rw [show ((Φ (⟨⟨((τ t : ↥V) : ℂ), (τ t : ↥V).2.2⟩,
        hNV ((τ t : ↥V) : ℂ) (τ t : ↥V).2⟩ : ↥N) : ↥W) : ℂ) = f (τ t) from rfl]
    rw [hfτ t, hσsub t]
  have hfun : (fun t => F (t, 1))
      = fun t => ((ρ / 2 : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    funext t
    exact hR1 t
  rw [hfun] at hRHS
  refine hround c₀ (ρ / 2) (by linarith) ?_
  simpa only [Commons.Topology.Winding.HasArg, circleCurve, add_sub_cancel_left, sub_zero] using hRHS

end

/-! ## The antipodal (Borsuk) lemma for loops -/

noncomputable section

/-- If `x` and `y` are both integer multiples of `2 * π` and `|x - y| < 2 * π`, then `x = y`. -/
lemma eq_of_abs_sub_lt_two_pi {x y : ℝ} (h : |x - y| < 2 * Real.pi)
    {m n : ℤ} (hx : x = 2 * Real.pi * m) (hy : y = 2 * Real.pi * n) : x = y := by
  have h3 : |2 * Real.pi * ((m : ℝ) - n)| < 2 * Real.pi := by
    rw [show 2 * Real.pi * ((m : ℝ) - n) = 2 * Real.pi * m - 2 * Real.pi * n by ring]
    rw [← hx, ← hy]; exact h
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h3
  have h4 : ((m : ℝ) - n) = 0 := by
    by_contra hne
    have h5 : (m - n : ℤ) ≠ 0 := by
      intro hh
      have hh' : m = n := by omega
      exact hne (by rw [hh']; ring)
    have h6 : (1 : ℝ) ≤ |((m : ℝ) - n)| := by
      have hsub : ((m : ℝ) - (n : ℝ)) = ((m - n : ℤ) : ℝ) := by push_cast; ring
      rw [hsub, ← Int.cast_abs, ← Int.cast_one]
      have hpos : (0 : ℤ) < |m - n| := abs_pos.mpr h5
      exact_mod_cast (by omega : (1 : ℤ) ≤ |m - n|)
    have h7 : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [abs_nonneg ((m : ℝ) - n)]
  rw [hx, hy]
  have : (m : ℝ) = n := by linarith
  rw [this]

/-- **Borsuk's theorem for loops.**  A continuous, `1`-periodic, nowhere-zero curve that is
antipodally odd (`F (t + 1/2) = -F t`) admits no continuous `1`-periodic argument function: its
winding number about the origin is `±1`, not `0`. -/
theorem not_hasArg_of_antipodal {F : ℝ → ℂ} (hc : Continuous F) (hper : Function.Periodic F 1)
    (hnz : ∀ t, F t ≠ 0) (hodd : ∀ t, F (t + 1/2) = -F t) :
    ¬ Commons.Topology.Winding.HasArg F 0 := by
  rintro ⟨θ, hθc, hθper, hθrep⟩
  have hrepr : ∀ t : ℝ, F t
      = ((‖F t‖ : ℝ) : ℂ) * Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) := by
    intro t; simpa using hθrep t
  have hmod : ∀ t : ℝ, ‖F (t + 1/2)‖ = ‖F t‖ := fun t => by rw [hodd t, norm_neg]
  have hexp : ∀ t : ℝ, Complex.exp (((θ (t + 1/2) : ℝ) : ℂ) * Complex.I)
      = -Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) := by
    intro t
    have hr : ((‖F t‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hnz t))
    have h2 : ((‖F t‖ : ℝ) : ℂ) * Complex.exp (((θ (t + 1/2) : ℝ) : ℂ) * Complex.I)
        = -(((‖F t‖ : ℝ) : ℂ) * Complex.exp (((θ t : ℝ) : ℂ) * Complex.I)) := by
      have h := hrepr (t + 1/2)
      rw [hmod t, hodd t] at h
      have h1 : -F t
          = -(((‖F t‖ : ℝ) : ℂ) * Complex.exp (((θ t : ℝ) : ℂ) * Complex.I)) :=
        congrArg Neg.neg (hrepr t)
      rw [h1] at h
      exact h.symm
    have h2' : ((‖F t‖ : ℝ) : ℂ) * Complex.exp (((θ (t + 1/2) : ℝ) : ℂ) * Complex.I)
        = ((‖F t‖ : ℝ) : ℂ) * (-Complex.exp (((θ t : ℝ) : ℂ) * Complex.I)) := by
      rw [h2, mul_neg]
    exact mul_left_cancel₀ hr h2'
  have hpi : ∀ t : ℝ, Complex.exp ((((θ t + Real.pi) : ℝ) : ℂ) * Complex.I)
      = -Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [show ((((θ t + Real.pi) : ℝ)) : ℂ) * Complex.I
        = ((θ t : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hmem : ∀ t : ℝ, ∃ n : ℤ, θ (t + 1/2) - θ t - Real.pi = 2 * Real.pi * n := by
    intro t
    refine exists_int_of_exp_eq_one ?_
    rw [show (((θ (t + 1/2) - θ t - Real.pi : ℝ)) : ℂ) * Complex.I
        = ((θ (t + 1/2) : ℝ) : ℂ) * Complex.I
          - (((θ t + Real.pi : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_sub, hexp t, hpi t]
    exact div_self (neg_ne_zero.mpr (Complex.exp_ne_zero _))
  set ψ : ℝ → ℝ := fun t => θ (t + 1/2) - θ t - Real.pi with hψ
  have hψcont : Continuous ψ := by
    rw [hψ]
    exact ((hθc.comp (continuous_id.add continuous_const)).sub hθc).sub continuous_const
  have hψmem : ∀ t : ℝ, ∃ n : ℤ, ψ t = 2 * Real.pi * n := by
    intro t; simpa only [hψ] using hmem t
  have hAclosed : IsClosed {t : ℝ | ψ t = ψ 0} := isClosed_eq hψcont continuous_const
  have hAopen : IsOpen {t : ℝ | ψ t = ψ 0} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    obtain ⟨ε, hε, hε'⟩ := Metric.continuousAt_iff.mp hψcont.continuousAt (2 * Real.pi) h2pi
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hε) ?_
    intro u hu
    have hu' : dist (ψ u) (ψ t) < 2 * Real.pi := hε' hu
    rw [Real.dist_eq] at hu'
    obtain ⟨m, hm⟩ := hψmem u
    obtain ⟨n, hn⟩ := hψmem t
    exact (eq_of_abs_sub_lt_two_pi hu' hm hn).trans ht
  have huniv : (Set.univ : Set ℝ) ⊆ {t : ℝ | ψ t = ψ 0} :=
    isPreconnected_univ.subset_isClopen ⟨hAclosed, hAopen⟩ ⟨0, Set.mem_univ 0, rfl⟩
  obtain ⟨k, hk⟩ := hmem 0
  have hk' : ψ 0 = 2 * Real.pi * (k : ℝ) := by simpa only [hψ, zero_add] using hk
  have hψform1 : ψ (1/2 : ℝ) = θ 0 - θ (1/2 : ℝ) - Real.pi := by
    have h1 : (1/2 : ℝ) + 1/2 = 1 := by norm_num
    have hper0 : θ (1 : ℝ) = θ 0 := by simpa using hθper 0
    simp only [hψ, h1, hper0]
  have hψform0 : ψ 0 = θ (1/2 : ℝ) - θ 0 - Real.pi := by
    simp only [hψ, zero_add]
  have hkey0 : ψ (1/2 : ℝ) = ψ 0 := huniv (Set.mem_univ _)
  have hhalf : θ (1/2 : ℝ) = θ 0 := by
    rw [hψform1, hψform0] at hkey0
    linarith
  have hψhalf : ψ (1/2 : ℝ) = -Real.pi := by
    rw [hψform1, hhalf]
    ring
  have hkey2 : ψ (1/2 : ℝ) = 2 * Real.pi * (k : ℝ) := by rw [hkey0, hk']
  have hkreal : 2 * Real.pi * (k : ℝ) = -Real.pi := by
    rw [← hkey2, hψhalf]
  have h0 : Real.pi * (2 * (k : ℝ) + 1) = 0 := by
    have h := hkreal; ring_nf at h ⊢; linarith
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h Real.pi_ne_zero
  · have hreal : (2 : ℝ) * (k : ℝ) = -1 := by linarith
    have hint : (2 * k : ℤ) = -1 := by
      have hcast : ((2 * k : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast hcast
    omega

/-- **`HasArg` is closed in its base point.**  If the closed curve `f` has a periodic argument
based at `u` and `u` is not on the curve, then the same holds for every point `y` within a quarter
of the distance from `y` to the curve. -/
lemma hasArg_of_near {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f 1)
    {y u : ℂ} (hy : y ∉ Set.range f) (hu : u ∉ Set.range f)
    (harg : Commons.Topology.Winding.HasArg f u)
    (hclose : ‖y - u‖ < Metric.infDist y (Set.range f) / 4) :
    Commons.Topology.Winding.HasArg f y := by
  obtain ⟨θ, hθc, hθper, hθrep⟩ := harg
  have hK : IsCompact (Set.range f) :=
    Commons.Topology.Winding.isCompact_range_of_periodic hf hper
  have hne : (Set.range f).Nonempty := ⟨f 0, Set.mem_range_self 0⟩
  have hd : 0 < Metric.infDist y (Set.range f) :=
    (hK.isClosed.notMem_iff_infDist_pos hne).mp hy
  have h2 : ‖y - u‖ < Metric.infDist u (Set.range f) / 2 := by
    have h3 := Metric.infDist_le_infDist_add_dist (s := Set.range f) (x := y) (y := u)
    rw [dist_eq_norm] at h3
    linarith
  exact Commons.Topology.Curve.argument_lift_of_close hf hper hu hθc hθper hθrep h2

/-! ## Two-dimensional invariance of domain -/

/-- **Invariance of domain at the centre.**  If `g : ℂ → ℂ` is continuous on the closed unit disc
`𝔻` and injective there, then `g 0` is an interior point of `g '' 𝔻`. -/
theorem center_mem_interior_image {g : ℂ → ℂ}
    (hc : ContinuousOn g (Metric.closedBall (0 : ℂ) 1))
    (hinj : Set.InjOn g (Metric.closedBall (0 : ℂ) 1)) :
    g 0 ∈ interior (g '' Metric.closedBall (0 : ℂ) 1) := by
  by_contra hcon
  set D : Set ℂ := Metric.closedBall (0 : ℂ) 1 with hD
  have hinjD : Set.InjOn g D := hinj
  have hzeroD : (0 : ℂ) ∈ D := by
    simp only [hD, Metric.mem_closedBall, dist_self]
    norm_num
  have hcon' : g 0 ∉ interior (g '' D) := hcon
  have hclosure : g 0 ∈ closure ((g '' D)ᶜ) := by
    have h := interior_eq_compl_closure_compl (s := g '' D)
    rw [h] at hcon'
    exact not_not.mp hcon'
  -- the unit circle
  have hSeq : ∀ t : ℝ, circleCurve (0 : ℂ) 1 t
      = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    intro t; simp [circleCurve]
  set S : ℝ → ℂ := fun t => circleCurve (0 : ℂ) 1 t with hS
  have hScont : Continuous S := by
    rw [hS, show circleCurve (0 : ℂ) 1 = fun t : ℝ =>
        Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) from funext hSeq]
    fun_prop
  have hSnorm : ∀ t : ℝ, ‖S t‖ = 1 := by
    intro t
    simp only [hS, hSeq t, Complex.norm_exp_ofReal_mul_I]
  have hSper : ∀ t : ℝ, S (t + 1) = S t := by
    intro t
    rw [hS]
    exact circleCurve_periodic (0 : ℂ) 1 t
  have hShalf : ∀ t : ℝ, S (t + 1/2) = -S t := by
    intro t
    simp only [hS]
    rw [hSeq (t + 1/2), hSeq t,
      show ((2 * Real.pi * (t + 1/2) : ℝ) : ℂ) * Complex.I
        = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I by
          push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hSmem : ∀ t : ℝ, S t ∈ D := by
    intro t
    simp only [hD, Metric.mem_closedBall, dist_eq_norm, sub_zero, hSnorm t]
    norm_num
  have hSne : ∀ t : ℝ, S t ≠ 0 := by
    intro t h
    have h2 := hSnorm t
    rw [h, norm_zero] at h2
    norm_num at h2
  have hnegSmem : ∀ t : ℝ, -S t ∈ D := by
    intro t
    simp only [hD, Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_neg, hSnorm t]
    norm_num
  set γ : ℝ → ℂ := fun t => g (S t) with hγ
  have hγc : Continuous γ := by
    rw [hγ]
    exact hc.comp_continuous hScont hSmem
  have hγper : Function.Periodic γ 1 := by
    rw [hγ]
    exact fun t => congrArg g (hSper t)
  -- Step 1: outside `g '' D` the curve has a periodic argument
  have hasArg_far : ∀ y : ℂ, y ∉ g '' D → Commons.Topology.Winding.HasArg γ y := by
    intro y hy
    have hφmem : ∀ s : ℝ, min 1 (max 0 s) ∈ Set.Icc (0 : ℝ) 1 := fun s =>
      ⟨le_min (by norm_num) (le_max_left 0 s), min_le_left 1 (max 0 s)⟩
    have hφc : Continuous fun s : ℝ => (((min 1 (max 0 s) : ℝ)) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_const.min (continuous_const.max continuous_id))
    have hscal_mem : ∀ s t : ℝ, (((min 1 (max 0 s) : ℝ)) : ℂ) * S t ∈ D := by
      intro s t
      have hs := hφmem s
      have hnorm : ‖(((min 1 (max 0 s) : ℝ)) : ℂ)‖ = min 1 (max 0 s) := by
        simp [abs_of_nonneg hs.1]
      simp only [hD, Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul, hSnorm t,
        mul_one, hnorm]
      exact hs.2
    let H : ℝ × ℝ → ℂ := fun p => g ((((min 1 (max 0 p.2) : ℝ)) : ℂ) * S p.1) - y
    have hHcont : Continuous H := by
      refine Continuous.sub ?_ continuous_const
      refine hc.comp_continuous (Continuous.mul ?_ ?_) ?_
      · exact hφc.comp continuous_snd
      · exact hScont.comp continuous_fst
      · intro p; exact hscal_mem p.2 p.1
    have hHper : ∀ t s : ℝ, H (t + 1, s) = H (t, s) := by
      intro t s
      simp only [H]
      rw [hSper t]
    have hHnz : ∀ t s : ℝ, H (t, s) ≠ 0 := by
      intro t s h
      have h' : g ((((min 1 (max 0 s) : ℝ)) : ℂ) * S t) = y := by
        simpa only [H, sub_eq_zero] using h
      exact hy ⟨_, hscal_mem s t, h'⟩
    have hiff := Commons.Topology.Winding.hasArg_homotopy_invariant hHcont hHper hHnz
    have hconst : (fun t : ℝ => H (t, 0)) = fun _ : ℝ => g 0 - y := by
      funext t
      have h0 : min 1 (max 0 (0 : ℝ)) = 0 := by simp
      simp only [H, h0, Complex.ofReal_zero, zero_mul]
    have hLHS : Commons.Topology.Winding.HasArg (fun t : ℝ => H (t, 0)) 0 := by
      rw [hconst]
      refine ⟨fun _ => Complex.arg (g 0 - y), continuous_const, fun t => rfl, ?_⟩
      intro t
      simp only [sub_zero]
      exact (Complex.norm_mul_exp_arg_mul_I (g 0 - y)).symm
    have hH1 : ∀ t : ℝ, H (t, 1) = γ t - y := by
      intro t
      have h1 : min 1 (max 0 (1 : ℝ)) = 1 := by simp
      simp only [H, h1, Complex.ofReal_one, one_mul, hγ]
    have hR : Commons.Topology.Winding.HasArg (fun t : ℝ => H (t, 1)) 0 := hiff.mp hLHS
    have hfun : (fun t : ℝ => H (t, 1)) = fun t : ℝ => γ t - y := funext hH1
    rw [hfun] at hR
    unfold Commons.Topology.Winding.HasArg at hR ⊢
    simpa only [sub_zero] using hR
  -- Step 2-3: at `g 0` itself
  have hasArg_center : Commons.Topology.Winding.HasArg γ (g 0) := by
    have hg0range : g 0 ∉ Set.range γ := by
      rintro ⟨t, ht⟩
      have h1 : S t = 0 := hinjD (hSmem t) hzeroD ht
      exact hSne t h1
    have hK : IsCompact (Set.range γ) :=
      Commons.Topology.Winding.isCompact_range_of_periodic hγc hγper
    have hne : (Set.range γ).Nonempty := ⟨γ 0, Set.mem_range_self 0⟩
    have hd : 0 < Metric.infDist (g 0) (Set.range γ) :=
      (hK.isClosed.notMem_iff_infDist_pos hne).mp hg0range
    obtain ⟨u, huK, hucl⟩ :=
      Metric.mem_closure_iff.mp hclosure (Metric.infDist (g 0) (Set.range γ) / 4) (by positivity)
    have hu_range : u ∉ Set.range γ := by
      rintro ⟨t, ht⟩
      exact huK ⟨S t, hSmem t, ht⟩
    have hclose : ‖g 0 - u‖ < Metric.infDist (g 0) (Set.range γ) / 4 := by
      rw [dist_eq_norm] at hucl
      exact hucl
    exact hasArg_of_near hγc hγper hg0range hu_range (hasArg_far u huK) hclose
  -- Step 4: transfer to the antipodally odd curve
  set F : ℝ → ℂ := fun t => g (S t) - g (-S t) with hF
  have hFc : Continuous F := by
    simp only [hF]
    exact (hc.comp_continuous hScont hSmem).sub
      (hc.comp_continuous hScont.neg fun t => hnegSmem t)
  have hFper : Function.Periodic F 1 := by
    intro t
    simp only [hF, hSper t]
  have hFodd : ∀ t : ℝ, F (t + 1/2) = -F t := by
    intro t
    simp only [hF, hShalf t, neg_neg]
    ring
  have hFnz : ∀ t : ℝ, F t ≠ 0 := by
    intro t h
    have h1 : g (S t) = g (-S t) := by
      simpa only [hF, sub_eq_zero] using h
    have h2 : S t = -S t := hinjD (hSmem t) (hnegSmem t) h1
    have h3 : S t + S t = 0 := by
      have h4 : S t - (-S t) = 0 := sub_eq_zero.mpr h2
      rwa [sub_neg_eq_add] at h4
    have h5 : S t = 0 := by
      rw [← two_mul] at h3
      exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
    exact hSne t h5
  have harg_shift : Commons.Topology.Winding.HasArg (fun t : ℝ => F t) 0 := by
    have hφmem : ∀ s : ℝ, min 1 (max 0 s) ∈ Set.Icc (0 : ℝ) 1 := fun s =>
      ⟨le_min (by norm_num) (le_max_left 0 s), min_le_left 1 (max 0 s)⟩
    have hφc : Continuous fun s : ℝ => (((min 1 (max 0 s) : ℝ)) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_const.min (continuous_const.max continuous_id))
    set J : ℝ × ℝ → ℂ := fun p =>
      γ p.1 - g (-((((min 1 (max 0 p.2) : ℝ)) : ℂ) * S p.1)) with hJ
    have hJmem : ∀ p : ℝ × ℝ,
        -((((min 1 (max 0 p.2) : ℝ)) : ℂ) * S p.1) ∈ D := by
      intro p
      have hs := hφmem p.2
      have hnorm : ‖(((min 1 (max 0 p.2) : ℝ)) : ℂ)‖ = min 1 (max 0 p.2) := by
        simp [abs_of_nonneg hs.1]
      simp only [hD, Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_neg, norm_mul,
        hSnorm p.1, mul_one, hnorm]
      exact hs.2
    have hJcont : Continuous J := by
      refine Continuous.sub ?_ ?_
      · exact hγc.comp continuous_fst
      · refine hc.comp_continuous ?_ ?_
        · exact (Continuous.mul (hφc.comp continuous_snd) (hScont.comp continuous_fst)).neg
        · intro p; exact hJmem p
    have hJper : ∀ t s : ℝ, J (t + 1, s) = J (t, s) := by
      intro t s
      simp only [J, hγper t, hSper t]
    have hJnz : ∀ t s : ℝ, J (t, s) ≠ 0 := by
      intro t s h
      have h1 : g (S t) = g (-((((min 1 (max 0 s) : ℝ)) : ℂ) * S t)) := by
        simpa only [J, sub_eq_zero] using h
      have h2 : S t = -((((min 1 (max 0 s) : ℝ)) : ℂ) * S t) :=
        hinjD (hSmem t) (hJmem (t, s)) h1
      have h3 : S t + (((min 1 (max 0 s) : ℝ)) : ℂ) * S t = 0 := by
        have h4 : S t - (-((((min 1 (max 0 s) : ℝ)) : ℂ) * S t)) = 0 := sub_eq_zero.mpr h2
        rwa [sub_neg_eq_add] at h4
      have h5 : (((1 + min 1 (max 0 s) : ℝ)) : ℂ) * S t = 0 := by
        have h6 : S t + (((min 1 (max 0 s) : ℝ)) : ℂ) * S t
            = (((1 + min 1 (max 0 s) : ℝ)) : ℂ) * S t := by push_cast; ring
        rw [h6] at h3
        exact h3
      have h6 : (((1 + min 1 (max 0 s) : ℝ)) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by linarith [(hφmem s).1] : (1 + min 1 (max 0 s) : ℝ) ≠ 0)
      exact hSne t ((mul_eq_zero.mp h5).resolve_left h6)
    have hiff := Commons.Topology.Winding.hasArg_homotopy_invariant hJcont hJper hJnz
    have hJ0 : (fun t : ℝ => J (t, 0)) = fun t : ℝ => γ t - g 0 := by
      funext t
      have h0 : min 1 (max 0 (0 : ℝ)) = 0 := by simp
      simp only [J, h0, Complex.ofReal_zero, zero_mul, neg_zero, hγ]
    have hL : Commons.Topology.Winding.HasArg (fun t : ℝ => J (t, 0)) 0 := by
      rw [hJ0]
      unfold Commons.Topology.Winding.HasArg at hasArg_center ⊢
      simpa only [sub_zero] using hasArg_center
    have hJ1 : (fun t : ℝ => J (t, 1)) = fun t : ℝ => F t := by
      funext t
      have h1 : min 1 (max 0 (1 : ℝ)) = 1 := by simp
      simp only [J, hF, hγ, h1, Complex.ofReal_one, one_mul]
    have hR := hiff.mp hL
    rwa [hJ1] at hR
  exact absurd harg_shift (not_hasArg_of_antipodal hFc hFper hFnz hFodd)

/-- **Two-dimensional invariance of domain (disc form).**  The image of the open unit disc under a
map continuous and injective on the closed unit disc is contained in the interior of the image of
the closed unit disc. -/
theorem image_ball_subset_interior_image_closedBall {g : ℂ → ℂ}
    (hc : ContinuousOn g (Metric.closedBall (0 : ℂ) 1))
    (hinj : Set.InjOn g (Metric.closedBall (0 : ℂ) 1)) :
    g '' Metric.ball (0 : ℂ) 1 ⊆ interior (g '' Metric.closedBall (0 : ℂ) 1) := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := hw
  have hzn : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  set ρ : ℝ := (1 - ‖z‖) / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hzρ : ‖z‖ + ρ < 1 := by rw [hρ]; linarith
  have hnormρ : ‖((ρ : ℝ) : ℂ)‖ = ρ := by simp [abs_of_pos hρpos]
  have hmaps : ∀ u ∈ Metric.closedBall (0 : ℂ) 1,
      z + ((ρ : ℝ) : ℂ) * u ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro u hu
    have hun : ‖u‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hu
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    calc ‖z + ((ρ : ℝ) : ℂ) * u‖ ≤ ‖z‖ + ‖((ρ : ℝ) : ℂ) * u‖ := norm_add_le _ _
      _ = ‖z‖ + ρ * ‖u‖ := by rw [norm_mul, hnormρ]
      _ ≤ ‖z‖ + ρ * 1 := by
            have h := mul_le_mul_of_nonneg_left hun hρpos.le
            linarith
      _ ≤ 1 := by rw [mul_one]; linarith
  have hcont : ContinuousOn (fun u : ℂ => g (z + ((ρ : ℝ) : ℂ) * u))
      (Metric.closedBall (0 : ℂ) 1) :=
    hc.comp' (Continuous.continuousOn (by fun_prop)) hmaps
  have hinj' : Set.InjOn (fun u : ℂ => g (z + ((ρ : ℝ) : ℂ) * u))
      (Metric.closedBall (0 : ℂ) 1) := by
    intro u hu v hv huv
    have h := hinj (hmaps u hu) (hmaps v hv) huv
    have h2 : ((ρ : ℝ) : ℂ) * u = ((ρ : ℝ) : ℂ) * v := add_left_cancel h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hρpos)) h2
  have hcenter := center_mem_interior_image hcont hinj'
  have h0 : g (z + ((ρ : ℝ) : ℂ) * 0) = g z := by simp
  rw [h0] at hcenter
  have hsub : (fun u : ℂ => g (z + ((ρ : ℝ) : ℂ) * u)) '' Metric.closedBall (0 : ℂ) 1
      ⊆ g '' Metric.closedBall (0 : ℂ) 1 := by
    rintro v ⟨u, hu, rfl⟩
    exact ⟨z + ((ρ : ℝ) : ℂ) * u, hmaps u hu, rfl⟩
  exact interior_mono hsub hcenter

end

end Work.Topology.Surface
