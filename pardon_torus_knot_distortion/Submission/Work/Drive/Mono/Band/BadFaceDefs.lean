import Mathlib
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.Mono.Band.noTangency_data
import Submission.Work.Drive.Mono.ThinWidth.det_eq_zero_iff_parallel
import Submission.Work.Drive.Generic.ae_height_morse
import Submission.Work.Drive.Generic.fderiv_height_eq
import Submission.Work.Drive.Generic.fderiv_height_eq_zero_iff

/-!
# The "bad face" of the thin slab: vocabulary

For an immersion `Φ : ℝ × ℝ → ℝ³` with Gauss normal `normal Φ p = ∂₁Φ(p) ⨯ ∂₂Φ(p)` and a unit
direction `v`, this file introduces

* `projV Φ v p` — the component of `normal Φ p` orthogonal to `v`;
* `qV Φ v p` — its squared length;
* `rhoV Φ v p` — its unit direction (junk where it vanishes);
* `tiltDir a b θ` — the unit direction `cos θ • a + sin θ • b` of an orthonormal pair `a, b`.

The main theorem is `bad_iff`: for `Φ = par ψ`, an orthonormal triple `v, a, b` and the tilted
functional `ℓ = innerSL ℝ (tiltDir a b θ)`, the differential of the swept height `⟪ℓ, par ψ ·⟫` at
`p` is a multiple of the differential of the `v`-height **if and only if** the direction `rhoV` of
the normal is `± tiltDir a b θ`; equivalently, if and only if the normal lies in `span {v, n}` and
is not parallel to `v`.
-/

namespace Work.Drive.Mono.Band

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

open Work.Drive.Generic

/-- The component of the Gauss normal `N p = ∂₁Φ(p) ⨯ ∂₂Φ(p)` orthogonal to the direction `v`. -/
def projV (Φ : ℝ × ℝ → R3) (v : R3) (p : ℝ × ℝ) : R3 :=
  Work.Drive.Generic.normal Φ p - (inner ℝ v (Work.Drive.Generic.normal Φ p)) • v

/-- The squared length of `projV Φ v p`. -/
def qV (Φ : ℝ × ℝ → R3) (v : R3) (p : ℝ × ℝ) : ℝ := ‖projV Φ v p‖ ^ 2

/-- The unit direction of `projV Φ v p`; junk where `projV Φ v p = 0`. -/
def rhoV (Φ : ℝ × ℝ → R3) (v : R3) (p : ℝ × ℝ) : R3 :=
  (‖projV Φ v p‖)⁻¹ • projV Φ v p

/-- The tilted direction `cos θ • a + sin θ • b` of an orthonormal pair `a, b`. -/
def tiltDir (a b : R3) (θ : ℝ) : R3 := Real.cos θ • a + Real.sin θ • b

/-! ## Elementary linear algebra of `crossE` -/

/-- The Lagrange identity `⟪u ⨯ v, x ⨯ y⟫ = ⟪u,x⟫⟪v,y⟫ - ⟪u,y⟫⟪v,x⟫` for the cross product on
`R3`. -/
lemma inner_crossE_crossE (u v x y : R3) :
    inner ℝ (crossE u v) (crossE x y)
      = inner ℝ u x * inner ℝ v y - inner ℝ u y * inner ℝ v x := by
  rw [inner_eq_dotProduct, ofLp_crossE, ofLp_crossE, cross_dot_cross,
      inner_eq_dotProduct u x, inner_eq_dotProduct v y,
      inner_eq_dotProduct u y, inner_eq_dotProduct v x]

lemma crossE_add_right (a b c : R3) : crossE a (b + c) = crossE a b + crossE a c := by
  apply WithLp.ofLp_injective
  simp only [ofLp_crossE, WithLp.ofLp_add]
  exact map_add (crossProduct (WithLp.ofLp a)) (WithLp.ofLp b) (WithLp.ofLp c)

lemma crossE_smul_right (a : R3) (r : ℝ) (b : R3) : crossE a (r • b) = r • crossE a b := by
  apply WithLp.ofLp_injective
  simp only [ofLp_crossE, WithLp.ofLp_smul]
  exact map_smul (crossProduct (WithLp.ofLp a)) r (WithLp.ofLp b)

lemma crossE_neg_right (a b : R3) : crossE a (-b) = -crossE a b := by
  rw [← neg_one_smul ℝ b, crossE_smul_right, neg_one_smul]

lemma crossE_sub_right (a b c : R3) : crossE a (b - c) = crossE a b - crossE a c := by
  rw [sub_eq_add_neg, crossE_add_right, crossE_neg_right, sub_eq_add_neg]

lemma crossE_add_left (a b c : R3) : crossE (a + b) c = crossE a c + crossE b c := by
  apply WithLp.ofLp_injective
  simp only [ofLp_crossE, WithLp.ofLp_add]
  have h := map_add crossProduct (WithLp.ofLp a) (WithLp.ofLp b)
  have h2 := congrArg (fun L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ => L (WithLp.ofLp c)) h
  simpa only [LinearMap.add_apply] using h2

/-- **The orthogonal expansion in an orthonormal pair.**  If `‖v‖ = ‖n‖ = 1` and `⟪v,n⟫ = 0` then
every vector `X` is the sum of its three orthogonal projections onto `v`, `n` and `v ⨯ n`. -/
theorem crossExpansion {v n X : R3} (hv : ‖v‖ = 1) (hn : ‖n‖ = 1) (hvn : inner ℝ v n = 0) :
    inner ℝ v X • v + inner ℝ n X • n + inner ℝ (crossE v n) X • crossE v n = X := by
  have h2 : crossE X (crossE v n) = inner ℝ X n • v - inner ℝ v X • n := by
    rw [crossE_crossE]
  have h3 : crossE (crossE v n) v = n := by
    rw [crossE_anticomm, crossE_crossE]
    simp [hvn, hv]
  have h4 : crossE (crossE v n) n = -v := by
    rw [crossE_anticomm, crossE_crossE]
    simp [hvn, hn]
  have h5 : inner ℝ (crossE v n) (crossE v n) = 1 := by
    rw [inner_crossE_crossE, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hv, hn]
    have h0 : inner ℝ n v = 0 := by rw [real_inner_comm]; exact hvn
    rw [h0]
    norm_num
  have h1 : crossE (crossE v n) (crossE X (crossE v n))
      = inner ℝ (crossE v n) (crossE v n) • X - inner ℝ X (crossE v n) • crossE v n := by
    rw [crossE_crossE]
  rw [h2, crossE_sub_right, crossE_smul_right, crossE_smul_right, h3, h4, smul_neg] at h1
  rw [h5, one_smul, sub_neg_eq_add] at h1
  have hX : X = inner ℝ X n • n + inner ℝ v X • v + inner ℝ X (crossE v n) • crossE v n :=
    (eq_sub_iff_add_eq.mp h1).symm
  have hAC : inner ℝ v X • v + inner ℝ n X • n + inner ℝ (crossE v n) X • crossE v n
      = inner ℝ X n • n + inner ℝ v X • v + inner ℝ X (crossE v n) • crossE v n := by
    rw [real_inner_comm n X, real_inner_comm (crossE v n) X]; abel
  rw [hAC, ← hX]

/-- For an orthonormal pair `v, n`, the cross product `v ⨯ n` is a unit vector. -/
theorem norm_crossE {v n : R3} (hv : ‖v‖ = 1) (hn : ‖n‖ = 1) (hvn : inner ℝ v n = 0) :
    ‖crossE v n‖ = 1 := by
  have h : inner ℝ (crossE v n) (crossE v n) = 1 := by
    rw [inner_crossE_crossE, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hv, hn]
    have h0 : inner ℝ n v = 0 := by rw [real_inner_comm]; exact hvn
    rw [h0]
    norm_num
  have h2 : ‖crossE v n‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact h
  nlinarith [h2, norm_nonneg (crossE v n)]

/-- A vector orthogonal to `v ⨯ n` lies in the span of an orthonormal pair `v, n`. -/
theorem mem_span_of_inner_crossE_eq_zero {v n X : R3} (hv : ‖v‖ = 1) (hn : ‖n‖ = 1)
    (hvn : inner ℝ v n = 0) (h : inner ℝ (crossE v n) X = 0) :
    X ∈ Submodule.span ℝ ({v, n} : Set R3) := by
  have hX : X = inner ℝ v X • v + inner ℝ n X • n := by
    have h1 := crossExpansion (X := X) hv hn hvn
    rw [h, zero_smul, add_zero] at h1
    exact h1.symm
  rw [hX]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-! ## `projV`, `qV` and `rhoV` -/

/-- The decomposition of the Gauss normal into its component along `v` and its `v`-orthogonal
component. -/
theorem normal_eq_projV_add {Φ : ℝ × ℝ → R3} (v : R3) (p : ℝ × ℝ) :
    Work.Drive.Generic.normal Φ p = projV Φ v p + (inner ℝ v (Work.Drive.Generic.normal Φ p)) • v := by
  rw [projV]; abel

/-- `projV` is orthogonal to `v`. -/
theorem inner_projV_v {Φ : ℝ × ℝ → R3} {v : R3} (hv : ‖v‖ = 1) (p : ℝ × ℝ) :
    inner ℝ (projV Φ v p) v = 0 := by
  rw [projV, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv, one_pow,
    mul_one]
  exact sub_eq_zero.mpr (real_inner_comm _ _)

/-- `projV` vanishes exactly when the normal is parallel to `v`. -/
theorem projV_eq_zero_iff {Φ : ℝ × ℝ → R3} {v : R3} (hv : ‖v‖ = 1) (p : ℝ × ℝ) :
    projV Φ v p = 0 ↔ ∃ c : ℝ, Work.Drive.Generic.normal Φ p = c • v := by
  constructor
  · intro h
    refine ⟨inner ℝ v (Work.Drive.Generic.normal Φ p), ?_⟩
    have h2 := normal_eq_projV_add (Φ := Φ) v p
    rw [h, zero_add] at h2
    exact h2
  · rintro ⟨c, hc⟩
    rw [projV, hc, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
    norm_num

/-- `rhoV` is a unit vector when `projV` does not vanish. -/
theorem norm_rhoV {Φ : ℝ × ℝ → R3} {v : R3} {p : ℝ × ℝ} (hp : projV Φ v p ≠ 0) :
    ‖rhoV Φ v p‖ = 1 := by
  have h : ‖projV Φ v p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  rw [rhoV, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ h]

/-- If the direction of `projV` is a unit vector `w`, then `projV` is a *positive* multiple of
`w`. -/
theorem exists_pos_smul_of_rhoV_eq {Φ : ℝ × ℝ → R3} {v w : R3} {p : ℝ × ℝ}
    (hw : ‖w‖ = 1) (h : rhoV Φ v p = w) :
    ∃ c : ℝ, 0 < c ∧ projV Φ v p = c • w := by
  have hne : projV Φ v p ≠ 0 := by
    intro h0
    rw [rhoV, h0, norm_zero, inv_zero, zero_smul] at h
    have h1 : (0 : ℝ) = 1 := by rw [← hw, ← h]; norm_num
    exact zero_ne_one h1
  refine ⟨‖projV Φ v p‖, norm_pos_iff.mpr hne, ?_⟩
  rw [rhoV] at h
  have h2 := congrArg (fun x => ‖projV Φ v p‖ • x) h
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hne), one_smul] at h2
  rw [← h2]

/-- **The characterisation of `rhoV`.**  For a unit vector `w`, the direction of `projV` is `± w`
exactly when `projV` is a non-zero multiple of `w`. -/
theorem rhoV_eq_iff_smul {Φ : ℝ × ℝ → R3} {v w : R3} (hw : ‖w‖ = 1) (p : ℝ × ℝ) :
    (rhoV Φ v p = w ∨ rhoV Φ v p = -w) ↔
      ∃ c : ℝ, c ≠ 0 ∧ projV Φ v p = c • w := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; exact one_ne_zero hw.symm
  constructor
  · rintro (h | h)
    · obtain ⟨c, hc, hc'⟩ := exists_pos_smul_of_rhoV_eq hw h
      exact ⟨c, ne_of_gt hc, hc'⟩
    · obtain ⟨c, hc, hc'⟩ := exists_pos_smul_of_rhoV_eq (by rw [norm_neg]; exact hw) h
      refine ⟨-c, neg_ne_zero.mpr (ne_of_gt hc), ?_⟩
      rw [hc', smul_neg, neg_smul]
  · rintro ⟨c, hc, hc'⟩
    have hne : projV Φ v p ≠ 0 := by rw [hc']; exact smul_ne_zero hc hw0
    have hnorm : ‖projV Φ v p‖ = |c| := by rw [hc', norm_smul, hw, mul_one, Real.norm_eq_abs]
    have hval : rhoV Φ v p = ((|c|)⁻¹ * c) • w := by
      rw [rhoV, hnorm, hc', smul_smul]
    have hkey : (|c|)⁻¹ * c = 1 ∨ (|c|)⁻¹ * c = -1 := by
      rcases lt_trichotomy c 0 with h0 | h0 | h0
      · right
        rw [abs_of_neg h0, inv_neg, neg_mul, inv_mul_cancel₀ (ne_of_lt h0)]
      · exact absurd h0 hc
      · left
        rw [abs_of_pos h0, inv_mul_cancel₀ (ne_of_gt h0)]
    rw [hval]
    rcases hkey with hk | hk
    · left; rw [hk, one_smul]
    · right; rw [hk, neg_one_smul]

/-! ## The Gauss normal: orthogonality and smoothness -/

/-- The Gauss normal is orthogonal to the first partial derivative. -/
lemma inner_normal_d1 (Φ : ℝ × ℝ → R3) (p : ℝ × ℝ) :
    inner ℝ (Work.Drive.Generic.normal Φ p) (Work.Drive.Generic.d1 Φ p) = 0 := by
  rw [Work.Drive.Generic.normal]
  exact (real_inner_comm _ _).trans (Work.Drive.Generic.inner_crossE_left _ _)

/-- The Gauss normal is orthogonal to the second partial derivative. -/
lemma inner_normal_d2 (Φ : ℝ × ℝ → R3) (p : ℝ × ℝ) :
    inner ℝ (Work.Drive.Generic.normal Φ p) (Work.Drive.Generic.d2 Φ p) = 0 := by
  rw [Work.Drive.Generic.normal]
  exact (real_inner_comm _ _).trans (Work.Drive.Generic.inner_crossE_right _ _)

/-- The Gauss normal of a `C³` immersion is `C²`. -/
theorem contDiff_normal {Φ : ℝ × ℝ → R3} (hΦ : ContDiff ℝ 3 Φ) :
    ContDiff ℝ 2 (Work.Drive.Generic.normal Φ) := by
  have hderiv : ContDiff ℝ 2 (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ Φ p.1) p.2) :=
    hΦ.contDiff_fderiv_apply (m := 2) (by norm_num)
  have hL1 : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p, ((1, 0) : ℝ × ℝ))) := by fun_prop
  have hL2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p, ((0, 1) : ℝ × ℝ))) := by fun_prop
  have hd1 : ContDiff ℝ 2 (fun p : ℝ × ℝ => (fderiv ℝ Φ p) (1, 0)) := hderiv.comp hL1
  have hd2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => (fderiv ℝ Φ p) (0, 1)) := hderiv.comp hL2
  exact Work.Drive.Generic.contDiff_crossE_pair.comp (hd1.prodMk hd2)

/-- `projV` of a `C³` immersion is `C²`. -/
theorem contDiff_projV {Φ : ℝ × ℝ → R3} (hΦ : ContDiff ℝ 3 Φ) (v : R3) :
    ContDiff ℝ 2 (projV Φ v) := by
  have h1 := contDiff_normal hΦ
  have h2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => inner ℝ v (Work.Drive.Generic.normal Φ p)) := by
    have h := (innerSL ℝ v).contDiff.comp h1
    have heq : (⇑((innerSL ℝ) v)) ∘ (Work.Drive.Generic.normal Φ)
        = fun p : ℝ × ℝ => inner ℝ v (Work.Drive.Generic.normal Φ p) := by
      funext p
      rw [Function.comp_apply, innerSL_apply_apply]
    rwa [heq] at h
  unfold projV
  exact h1.sub (h2.smul contDiff_const)

/-- The parametrisation of the challenge is `C³`. -/
theorem par_contDiff_three (ψ : Submission.Diffeo) :
    ContDiff ℝ 3 (Work.BoxShrink.Pinch.par ψ) :=
  (Work.Smooth.Morse.param_contDiff ψ).of_le (WithTop.coe_le_coe.mpr le_top)

/-- The parametrisation of the challenge is an immersion. -/
theorem par_immersion (ψ : Submission.Diffeo) :
    ∀ p : ℝ × ℝ, Function.Injective (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p) := by
  intro p
  simpa only [Work.BoxShrink.Pinch.par_def, Work.Smooth.Morse.param] using
    (Work.Smooth.Morse.Immersion.isImmersion ψ p)

/-- The Gauss normal of the parametrisation of the challenge never vanishes. -/
theorem normal_par_ne_zero (ψ : Submission.Diffeo) (p : ℝ × ℝ) :
    Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p ≠ 0 :=
  Work.Drive.Generic.normal_ne_zero (par_contDiff_three ψ) (par_immersion ψ) p

/-! ## The determinant identity and the vanishing criterion -/

/-- **The determinant identity.**  The Jacobian determinant of the pair (height in the direction
`v`, height in the direction `n`) on the parameter plane is the scalar product of `v ⨯ n` with the
Gauss normal. -/
theorem det_identity (ψ : Submission.Diffeo) (v n : R3) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p (1, 0) *
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p (0, 1)
    - fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p (0, 1) *
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p (1, 0)
    = inner ℝ (Work.Drive.Generic.crossE v n)
        (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) := by
  rw [Work.Drive.Generic.fderiv_height_eq (par_contDiff_three ψ) v p (1, 0),
      Work.Drive.Generic.fderiv_height_eq (par_contDiff_three ψ) v p (0, 1),
      Work.Drive.Generic.fderiv_height_eq (par_contDiff_three ψ) n p (1, 0),
      Work.Drive.Generic.fderiv_height_eq (par_contDiff_three ψ) n p (0, 1),
      Work.Drive.Generic.normal, Work.Drive.Generic.d1, Work.Drive.Generic.d2,
      inner_crossE_crossE]

/-- **The vanishing criterion.**  The `v`-height on the parameter plane is critical at `p` exactly
where the Gauss normal is parallel to `v`. -/
theorem fderiv_par_height_eq_zero_iff_projV (ψ : Submission.Diffeo) {v : R3} (hv : ‖v‖ = 1)
    (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p = 0 ↔
      projV (Work.BoxShrink.Pinch.par ψ) v p = 0 := by
  constructor
  · intro h0
    have hvne : v ≠ 0 := by
      intro h; rw [h, norm_zero] at hv; exact one_ne_zero hv.symm
    obtain ⟨t, ht, ht'⟩ := Work.Drive.Generic.exists_smul_normal_of_crit (par_contDiff_three ψ)
      (par_immersion ψ) h0 hvne
    exact (projV_eq_zero_iff hv p).mpr
      ⟨t⁻¹, by rw [ht', smul_smul, inv_mul_cancel₀ ht, one_smul]⟩
  · intro h
    obtain ⟨c, hc⟩ := (projV_eq_zero_iff hv p).mp h
    have hcne : c ≠ 0 := by
      intro h0
      exact normal_par_ne_zero ψ p (by rw [hc, h0, zero_smul])
    have hv_eq : v = c⁻¹ • Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p := by
      rw [hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]
    rw [Work.Drive.Generic.fderiv_height_eq_zero_iff (par_contDiff_three ψ) v p]
    constructor
    · rw [hv_eq, real_inner_smul_left, inner_normal_d1, mul_zero]
    · rw [hv_eq, real_inner_smul_left, inner_normal_d2, mul_zero]

/-! ## The tilted direction -/

/-- `tiltDir a b θ` is a unit vector when `a, b` are orthonormal. -/
theorem norm_tiltDir {a b : R3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : inner ℝ a b = 0) (θ : ℝ) :
    ‖tiltDir a b θ‖ = 1 := by
  have hba : inner ℝ b a = 0 := by rw [real_inner_comm]; exact hab
  have h : inner ℝ (tiltDir a b θ) (tiltDir a b θ) = 1 := by
    simp only [tiltDir, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, ha, hb,
      hab, hba, mul_zero, mul_one, zero_mul, add_zero, zero_add, one_pow, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have h2 : ‖tiltDir a b θ‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact h
  nlinarith [h2, norm_nonneg (tiltDir a b θ)]

/-- `tiltDir a b θ` is orthogonal to `v` when `v` is orthogonal to `a` and `b`. -/
theorem inner_v_tiltDir {v a b : R3} (hva : inner ℝ v a = 0) (hvb : inner ℝ v b = 0) (θ : ℝ) :
    inner ℝ v (tiltDir a b θ) = 0 := by
  rw [tiltDir, inner_add_right, real_inner_smul_right, real_inner_smul_right, hva, hvb]
  ring

/-! ## The dictionary -/

/-- **The dictionary of the thin slab.**  For an orthonormal triple `v, a, b`, the differential of
the swept height `q ↦ ⟪tiltDir a b θ, par ψ q⟫` at `p` is a multiple of the differential of the
`v`-height if and only if the direction `rhoV` of the Gauss normal is `± tiltDir a b θ`. -/
theorem bad_iff (ψ : Submission.Diffeo) {v a b : R3} {θ : ℝ} {p : ℝ × ℝ}
    (hv : ‖v‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : inner ℝ a b = 0)
    (hva : inner ℝ v a = 0) (hvb : inner ℝ v b = 0) :
    (∃ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
        (innerSL ℝ (tiltDir a b θ))) p
        = t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p)
      ↔ (rhoV (Work.BoxShrink.Pinch.par ψ) v p = tiltDir a b θ ∨
          rhoV (Work.BoxShrink.Pinch.par ψ) v p = - tiltDir a b θ) := by
  have hn1 : ‖tiltDir a b θ‖ = 1 := norm_tiltDir ha hb hab θ
  have hvn : inner ℝ v (tiltDir a b θ) = 0 := inner_v_tiltDir hva hvb θ
  have hnne : tiltDir a b θ ≠ 0 := by
    intro h; rw [h, norm_zero] at hn1; exact one_ne_zero hn1.symm
  have hsw : Work.Drive.EpsForm.sweepHeight ψ (innerSL ℝ (tiltDir a b θ))
      = fun q : ℝ × ℝ => inner ℝ (tiltDir a b θ) (Work.BoxShrink.Pinch.par ψ q) :=
    Work.Drive.EpsForm.sweepHeight_innerSL ψ (tiltDir a b θ)
  rw [hsw]
  constructor
  · rintro ⟨t, ht⟩
    have hdet : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p (1, 0) *
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ (tiltDir a b θ) (Work.BoxShrink.Pinch.par ψ q)) p
          (0, 1)
      - fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p (0, 1) *
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ (tiltDir a b θ) (Work.BoxShrink.Pinch.par ψ q)) p
          (1, 0) = 0 := by
      rw [ht, smul_apply, smul_eq_mul, smul_apply, smul_eq_mul]
      ring
    have hcross : inner ℝ (Work.Drive.Generic.crossE v (tiltDir a b θ))
        (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 := by
      rw [← det_identity ψ v (tiltDir a b θ) p]
      exact hdet
    have hspan := mem_span_of_inner_crossE_eq_zero hv hn1 hvn hcross
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hspan
    have hproj : projV (Work.BoxShrink.Pinch.par ψ) v p = β • tiltDir a b θ := by
      rw [projV, ← hαβ]
      simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv, hvn,
        mul_zero, mul_one, zero_mul, add_zero, zero_add, one_pow]
      abel
    have hβ : β ≠ 0 := by
      intro hβ0
      have hproj0 : projV (Work.BoxShrink.Pinch.par ψ) v p = 0 := by rw [hproj, hβ0, zero_smul]
      have hdG0 : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p = 0 :=
        (fderiv_par_height_eq_zero_iff_projV ψ hv p).mpr hproj0
      have hdF0 : fderiv ℝ (fun q : ℝ × ℝ =>
          inner ℝ (tiltDir a b θ) (Work.BoxShrink.Pinch.par ψ q)) p = 0 := by
        rw [ht, hdG0, smul_zero]
      rw [Work.Drive.Generic.fderiv_height_eq_zero_iff (par_contDiff_three ψ)
        (tiltDir a b θ) p] at hdF0
      obtain ⟨h1, h2⟩ := hdF0
      have h1' : inner ℝ (Work.Drive.Generic.d1 (Work.BoxShrink.Pinch.par ψ) p)
          (tiltDir a b θ) = 0 := by rw [real_inner_comm]; exact h1
      have h2' : inner ℝ (Work.Drive.Generic.d2 (Work.BoxShrink.Pinch.par ψ) p)
          (tiltDir a b θ) = 0 := by rw [real_inner_comm]; exact h2
      have hcross2 : Work.Drive.Generic.crossE
          (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) (tiltDir a b θ) = 0 := by
        rw [Work.Drive.Generic.normal, Work.Drive.Generic.crossE_anticomm,
          Work.Drive.Generic.crossE_crossE, h2, h1']
        simp


      obtain ⟨c, hc⟩ := Work.Drive.Generic.exists_smul_of_crossE_eq_zero hcross2 hnne
      have h3 : inner ℝ (tiltDir a b θ)
          (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = c := by
        simp only [hc, real_inner_smul_right, real_inner_self_eq_norm_sq, hn1, mul_one, one_pow]
      have hvn' : inner ℝ (tiltDir a b θ) v = 0 := by rw [real_inner_comm]; exact hvn
      have h4 : inner ℝ (tiltDir a b θ)
          (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 := by
        rw [← hαβ, hβ0, zero_smul, add_zero, real_inner_smul_right, hvn', mul_zero]
      rw [h4] at h3
      exact normal_par_ne_zero ψ p (by rw [hc, h3.symm, zero_smul])
    exact (rhoV_eq_iff_smul hn1 p).mpr ⟨β, hβ, hproj⟩
  · intro h
    obtain ⟨c, hc0, hc⟩ := (rhoV_eq_iff_smul hn1 p).mp h
    have hcross : inner ℝ (Work.Drive.Generic.crossE v (tiltDir a b θ))
        (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 := by
      have hN : Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p ∈
          Submodule.span ℝ ({v, tiltDir a b θ} : Set R3) := by
        rw [Submodule.mem_span_pair]
        refine ⟨inner ℝ v (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p), c, ?_⟩
        conv_rhs => rw [normal_eq_projV_add v p, hc]
        abel
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hN
      rw [← hαβ, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_comm v (Work.Drive.Generic.crossE v (tiltDir a b θ)),
        Work.Drive.Generic.inner_crossE_left, mul_zero,
        real_inner_comm (tiltDir a b θ) (Work.Drive.Generic.crossE v (tiltDir a b θ)),
        Work.Drive.Generic.inner_crossE_right, mul_zero, add_zero]
    have hdet0 : fderiv ℝ (fun q : ℝ × ℝ =>
          inner ℝ (tiltDir a b θ) (Work.BoxShrink.Pinch.par ψ q)) p (1, 0) *
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p (0, 1)
      - fderiv ℝ (fun q : ℝ × ℝ =>
          inner ℝ (tiltDir a b θ) (Work.BoxShrink.Pinch.par ψ q)) p (0, 1) *
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p (1, 0) = 0 := by
      have h := det_identity ψ v (tiltDir a b θ) p
      rw [hcross] at h
      linear_combination -h
    have hdGne : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 := by
      intro h0
      have h1 := (fderiv_par_height_eq_zero_iff_projV ψ hv p).mp h0
      rw [hc] at h1
      exact (smul_ne_zero hc0 hnne) h1
    exact (Work.Drive.Mono.ThinWidth.det_eq_zero_iff_parallel
      (L := fderiv ℝ (fun q : ℝ × ℝ => inner ℝ (tiltDir a b θ)
        (Work.BoxShrink.Pinch.par ψ q)) p)
      (M := fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p)
      hdGne).mp hdet0

end

end Work.Drive.Mono.Band
