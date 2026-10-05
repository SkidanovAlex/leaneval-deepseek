import Mathlib
import Submission.Work.RPB.Port.RMT.Main
import Submission.Work.RPB.B1a.hasPrimitives_of_isConnected_compl
import Submission.Work.RPB.B1a.invFunOn_holomorphic

namespace Work.RPB.B1a

open Complex Metric Set Filter

noncomputable section

/-- **Rotation normalisation.**  A holomorphic injection `Ψ` on the open unit disc can be
precomposed with a rotation `z ↦ c * z` (with `‖c‖ = 1`) of the disc so that the derivative at `0`
of the composite is a positive real.  The point is that `Ψ` injective and holomorphic on the disc
forces `deriv Ψ 0 ≠ 0`, so `Ψ` may be rescaled by the unit complex number `‖deriv Ψ 0‖ / deriv Ψ 0`.
The four non-derivative conjuncts are bookkeeping: the rotation is a bijection of the disc onto
itself, so it preserves differentiability, injectivity and the image. -/
private lemma unit_rot_normalization_aux {Ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ Ψ (Metric.ball 0 1))
    (hinj : Set.InjOn Ψ (Metric.ball 0 1)) :
    ∃ (c : ℂ) (a : ℝ), ‖c‖ = 1 ∧ 0 < a ∧
      DifferentiableOn ℂ (fun z => Ψ (c * z)) (Metric.ball 0 1) ∧
      Set.InjOn (fun z => Ψ (c * z)) (Metric.ball 0 1) ∧
      (fun z => Ψ (c * z)) '' Metric.ball 0 1 = Ψ '' Metric.ball 0 1 ∧
      deriv (fun z => Ψ (c * z)) 0 = (a : ℂ) := by
  set w₀ := deriv Ψ 0 with hw₀
  have hw₀ne : w₀ ≠ 0 :=
    deriv_ne_zero_of_inj isOpen_ball hd hinj (mem_ball_self one_pos)
  have hw₀pos : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀ne
  set c : ℂ := (‖w₀‖ : ℂ) / w₀ with hc_def
  have hcnorm : ‖c‖ = 1 := by
    rw [hc_def, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w₀),
      div_self (ne_of_gt hw₀pos)]
  have hcne : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hcnorm; exact one_ne_zero hcnorm.symm
  have hwc : w₀ * c = (‖w₀‖ : ℂ) := by
    rw [hc_def, mul_div_cancel₀ _ hw₀ne]
  have hcmaps : MapsTo (fun z : ℂ => c * z) (Metric.ball 0 1) (Metric.ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rwa [norm_mul, hcnorm, one_mul]
  refine ⟨c, ‖w₀‖, hcnorm, hw₀pos, ?_, ?_, ?_, ?_⟩
  · refine hd.comp ?_ hcmaps
    exact (differentiableOn_id.const_mul c : DifferentiableOn ℂ (fun z : ℂ => c * z) univ).mono
      (subset_univ _)
  · intro y1 hy1 y2 hy2 h
    exact mul_right_injective₀ hcne (hinj (hcmaps hy1) (hcmaps hy2) h)
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨c * z, hcmaps hz, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨c⁻¹ * y, ?_, ?_⟩
      · rw [mem_ball_zero_iff] at hy ⊢
        rwa [norm_mul, norm_inv, hcnorm, inv_one, one_mul]
      · show Ψ (c * (c⁻¹ * y)) = Ψ y
        rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul]
  · have hg : HasDerivAt (fun z : ℂ => c * z) c 0 := by
      simpa using (hasDerivAt_id (0:ℂ)).const_mul c
    have hd0 : DifferentiableAt ℂ Ψ 0 :=
      hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
    have hcomp : deriv (fun z : ℂ => Ψ (c * z)) 0 =
        deriv Ψ (c * 0) * deriv (fun z : ℂ => c * z) 0 :=
      deriv_comp (x := (0:ℂ)) (by simpa using hd0) hg.differentiableAt
    rw [hcomp, hg.deriv, mul_zero, ← hw₀, hwc]

-- Node N6, first half: the Riemann map itself, in the direction the conformal-map route consumes.
-- Let `D` be a bounded open connected subset of ℂ with connected complement (for the route, the
-- interior of a smooth Jordan curve).  Then there is a biholomorphism `Φ` from the open unit disc
-- onto `D`, normalised so that `deriv Φ 0` is a positive real.  The Riemann mapping result is
-- available in this workspace as the ported `RMT` (`Submission.Work.RPB.Port.RMT.Main`), which
-- produces a map `D → ball 0 1`; the content here is the inversion of that map plus the rotation
-- normalisation.  `D ≠ univ` follows from `Bornology.IsBounded D` and `IsConnected D` (which
-- supplies `D.Nonempty`).  The hypothesis `hasPrimitives D` of the ported `RMT` is exactly
-- `Work.RPB.B1a.hasPrimitives_of_isConnected_compl D hDo hDc hDb hDcc` (same conclusion, written
-- with `Set.EqOn`).
--
-- Hint for the prover (route, with the names that do the work).
-- (1) `obtain ⟨f, hfd, hfinj, hfim⟩ := RMT hDo hDc hDne hprim`, where
--     `hprim : hasPrimitives D` is `Work.RPB.B1a.hasPrimitives_of_isConnected_compl D hDo hDc hDb
--     hDcc` (the two conclusions are definitionally the same), and `hDne : D ≠ univ` comes from
--     `hDb` and `hDc.2` (`Bornology.IsBounded` of a nonempty set in ℂ).
-- (2) Set `Ψ := Function.invFunOn f D`.  For `w ∈ Metric.ball 0 1` one has `Ψ w ∈ D` and
--     `f (Ψ w) = w` (Mathlib: `Function.invFunOn_mem`, `Function.leftInvOn_invFunOn`,
--     `Function.rightInvOn_invFunOn`); conversely `Ψ (f z) = z` for `z ∈ D` by `hfinj`.
-- (3) Holomorphy of `Ψ` on `Metric.ball 0 1`: for `z ∈ D` the ported root-level result
--     `deriv_ne_zero_of_inj hDo hfd hfinj hz` gives `deriv f z ≠ 0`, so
--     `(hfd.differentiableAt (hDo.mem_nhds hz)).hasStrictDerivAt` has a local inverse at `f z`
--     (`HasStrictDerivAt.localInverse`, `HasStrictDerivAt.to_localInverse`), which agrees with `Ψ`
--     on a neighbourhood of `f z` because `f` is injective on `D`; conclude with
--     `DifferentiableAt.congr_of_eventuallyEq` / `DifferentiableOn.congr` and
--     `hfd.analyticAt`/`IsOpenMap` if the open-map route is handier.  (The inverse-function route is
--     the direct one; the ported file `Submission.Work.RPB.Port.RMT/DerivInj.lean` has the
--     `deriv_ne_zero_of_inj` input.)
-- (4) `Ψ '' Metric.ball 0 1 = D` from `hfim` and the two round-trip identities; `Set.InjOn Ψ
--     (Metric.ball 0 1)` from `hfinj`.
-- (5) Normalisation: if `w₀ := deriv Ψ 0` (nonzero because `Ψ` is injective on the ball, or from
--     the local inverse formula) pick `c` with `‖c‖ = 1` and `c * w₀ = ↑‖w₀‖` (e.g. `c := ↑‖w₀‖ /
--     w₀` normalised), put `Φ z := Ψ (c * z)`; then `deriv Φ 0 = c * w₀ = ↑‖w₀‖` with `‖w₀‖ > 0`
--     (`deriv_const_mul`/`deriv_comp_mul`), `Φ '' Metric.ball 0 1 = D` (`c • Metric.ball 0 1 =
--     Metric.ball 0 1` since `‖c‖ = 1`, use `Metric.smul_unit_ball`) and `Set.InjOn Φ` follows from
--     `Set.InjOn Ψ` and `mul_left_injective₀` (note `c ≠ 0`).
lemma riemannMap_exists (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (hDcc : IsConnected Dᶜ) :
    ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ (Metric.ball 0 1) ∧ Set.InjOn Φ (Metric.ball 0 1) ∧
      Φ '' Metric.ball 0 1 = D ∧ ∃ a : ℝ, 0 < a ∧ deriv Φ 0 = a := by
  -- `D` is bounded and nonempty, hence a proper subset of `ℂ`, as `RMT` requires.
  have hDne : D ≠ univ := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hDb
    intro h
    have hmem : ((max r 0 + 1 : ℝ) : ℂ) ∈ D := h ▸ Set.mem_univ _
    have h1 := hr hmem
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ max r 0 + 1)] at h1
    linarith [le_max_left r 0]
  -- Every holomorphic function on `D` has a primitive (Node N5).
  have hprim : hasPrimitives D :=
    Work.RPB.B1a.hasPrimitives_of_isConnected_compl D hDo hDc hDb hDcc
  -- The Riemann mapping theorem, in the direction `D → ball 0 1`.
  obtain ⟨f, hfd, hfinj, hfim⟩ := RMT hDo hDc hDne hprim
  -- The inverse `Ψ = (f|_D)⁻¹` is holomorphic on the disc, and a two-sided inverse of `f` on `D`.
  have hfdz : ∀ z ∈ D, deriv f z ≠ 0 := fun z hz => deriv_ne_zero_of_inj hDo hfd hfinj hz
  obtain ⟨hΨd, hΨleft, hΨright⟩ :=
    Work.RPB.B1a.invFunOn_holomorphic hDo hfd hfinj hfdz
  rw [hfim] at hΨd
  have himage : Function.invFunOn f D '' Metric.ball 0 1 = D := by
    rw [← hfim]
    exact Set.InjOn.invFunOn_image hfinj (subset_refl D)
  have hinj : Set.InjOn (Function.invFunOn f D) (Metric.ball 0 1) := by
    rw [← hfim]
    exact Function.invFunOn_injOn_image f D
  -- Normalise the derivative at `0` by rotating the disc.
  obtain ⟨c, a, hc, ha, hdΦ, hinjΦ, himgΦ, hderivΦ⟩ := unit_rot_normalization_aux hΨd hinj
  exact ⟨fun z => Function.invFunOn f D (c * z), hdΦ, hinjΦ, himgΦ.trans himage, a, ha, hderivΦ⟩

end

end Work.RPB.B1a
