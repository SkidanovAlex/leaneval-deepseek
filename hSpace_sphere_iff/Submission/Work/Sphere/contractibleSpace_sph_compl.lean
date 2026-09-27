import Mathlib

open unitInterval

namespace Work.Sphere

/-- The ambient Euclidean space `ℝ^{n+1}`. -/
private abbrev eucl (n : ℕ) : Type := EuclideanSpace ℝ (Fin (n+1))

/-- The unit sphere `Sⁿ ⊂ ℝ^{n+1}`, as a set (hence also as a type). -/
private abbrev sphType (n : ℕ) : Set (eucl n) := Metric.sphere (0 : eucl n) 1

/-- The unit sphere with the point `p` removed. -/
private abbrev punct (n : ℕ) (p : sphType n) : Type := {x : sphType n // x ≠ p}

/-- **The unit sphere with one point removed is contractible.**  For a point `p` of the unit
sphere `Sⁿ ⊂ ℝ^{n+1}`, the complement is contractible: the normalised straight-line homotopy
`F(t,x) = ‖(1-t)x - t p‖⁻¹ • ((1-t)x - t p)` joins the identity (at `t = 0`, where `‖x‖ = 1`) to
the constant map at `-p` (at `t = 1`), and `(1-t)x - t p = 0` is impossible for `x ≠ p`, because
taking norms gives `|1-t| = |t|`, so `t = 1/2` and then `x = p`.

The conclusion is deliberately phrased as the `Prop` `Nonempty (ContractibleSpace …)` so that the
instance can be extracted with `Classical.choice` (the class itself cannot be a delegated
statement). -/
theorem contractibleSpace_sph_compl {n : ℕ}
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :
    Nonempty (ContractibleSpace {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 // x ≠ p}) := by
  change Nonempty (ContractibleSpace (punct n p))
  have hpnorm : ‖((p : sphType n) : eucl n)‖ = 1 := by
    have hmem := p.2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hmem
    exact hmem
  -- The (unnormalised) straight-line homotopy from `x` to `-p`.
  let U : I × punct n p → eucl n := fun z =>
    (1 - (z.1 : ℝ)) • (((z.2 : punct n p) : sphType n) : eucl n)
      - (z.1 : ℝ) • ((p : sphType n) : eucl n)
  have hUc : Continuous U := by
    dsimp only [U]; fun_prop
  have hU0 : ∀ x : punct n p, U (0, x) = (((x : punct n p) : sphType n) : eucl n) := by
    intro x; dsimp only [U]; simp
  have hU1 : ∀ x : punct n p, U (1, x) = -((p : sphType n) : eucl n) := by
    intro x; dsimp only [U]; simp
  -- The straight line from `x ≠ p` to `-p` never meets `0`.
  have hU_ne : ∀ z : I × punct n p, U z ≠ 0 := by
    rintro ⟨t, x⟩ h
    have hxnorm : ‖(((x : punct n p) : sphType n) : eucl n)‖ = 1 := by
      have hmem := (x.1).2
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hmem
      exact hmem
    have hpnorm' : ‖((p : sphType n) : eucl n)‖ = 1 := hpnorm
    have h' : (1 - (t:ℝ)) • (((x : punct n p) : sphType n) : eucl n)
        = (t:ℝ) • ((p : sphType n) : eucl n) := by
      have hh : (1 - (t:ℝ)) • (((x : punct n p) : sphType n) : eucl n)
          - (t:ℝ) • ((p : sphType n) : eucl n) = 0 := h
      exact sub_eq_zero.mp hh
    have hnorm : |1 - (t:ℝ)| = |(t:ℝ)| := by
      have hcong := congrArg (fun v : eucl n => ‖v‖) h'
      rw [norm_smul, norm_smul, hxnorm, hpnorm', mul_one, mul_one] at hcong
      simpa [Real.norm_eq_abs] using hcong
    have h1t : (1:ℝ) - (t:ℝ) = (t:ℝ) := by
      have h2 : (0:ℝ) ≤ 1 - (t:ℝ) := by linarith [t.2.2]
      have h3 : (0:ℝ) ≤ (t:ℝ) := t.2.1
      rw [abs_of_nonneg h2, abs_of_nonneg h3] at hnorm
      exact hnorm
    have ht0 : (t:ℝ) ≠ 0 := by intro ht; rw [ht] at h1t; linarith
    rw [h1t] at h'
    have hxp : (((x : punct n p) : sphType n) : eucl n) = ((p : sphType n) : eucl n) :=
      (smul_right_inj ht0).mp h'
    exact x.2 (Subtype.ext hxp)
  -- The normalised homotopy, landing on `Sⁿ`.
  let Φ : I × punct n p → eucl n := fun z => (‖U z‖)⁻¹ • U z
  have hΦc : Continuous Φ := by
    have h1 : Continuous fun z : I × punct n p => ‖U z‖ := hUc.norm
    have h2 : Continuous fun z : I × punct n p => (‖U z‖)⁻¹ :=
      h1.inv₀ (fun z => norm_ne_zero_iff.mpr (hU_ne z))
    dsimp only [Φ]
    exact h2.smul hUc
  have hΦmem : ∀ z : I × punct n p, Φ z ∈ sphType n := by
    intro z
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    dsimp only [Φ]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg (U z)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hU_ne z))]
  -- The normalised homotopy never meets `p` either.
  have hΦne : ∀ z : I × punct n p, Φ z ≠ (p : eucl n) := by
    rintro ⟨t, x⟩ h
    have hxne : (((x : punct n p) : sphType n) : eucl n) ≠ ((p : sphType n) : eucl n) :=
      fun hh => x.2 (Subtype.ext hh)
    have hcne : ‖U (t,x)‖ ≠ 0 := norm_ne_zero_iff.mpr (hU_ne (t,x))
    have hUp : U (t,x) = ‖U (t,x)‖ • ((p : sphType n) : eucl n) := by
      have hcong := congrArg (fun v : eucl n => ‖U (t,x)‖ • v) h
      dsimp only [Φ] at hcong
      rwa [smul_smul, mul_inv_cancel₀ hcne, one_smul] at hcong
    have hsplit : (1 - (t:ℝ)) • (((x : punct n p) : sphType n) : eucl n)
        = (‖U (t,x)‖ + (t:ℝ)) • ((p : sphType n) : eucl n) := by
      have h' : (1 - (t:ℝ)) • (((x : punct n p) : sphType n) : eucl n)
          = ‖U (t,x)‖ • ((p : sphType n) : eucl n) + (t:ℝ) • ((p : sphType n) : eucl n) :=
        sub_eq_iff_eq_add.mp hUp
      rw [h']
      exact (add_smul (‖U (t,x)‖) (t:ℝ) ((p : sphType n) : eucl n)).symm
    have hxnorm : ‖(((x : punct n p) : sphType n) : eucl n)‖ = 1 := by
      have hmem := (x.1).2
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hmem
      exact hmem
    have hpnorm' : ‖((p : sphType n) : eucl n)‖ = 1 := hpnorm
    have hnorm : |1 - (t:ℝ)| = |‖U (t,x)‖ + (t:ℝ)| := by
      have hcong := congrArg (fun v : eucl n => ‖v‖) hsplit
      rw [norm_smul, norm_smul, hxnorm, hpnorm', mul_one, mul_one] at hcong
      simpa [Real.norm_eq_abs] using hcong
    have h1 : (1:ℝ) - (t:ℝ) = ‖U (t,x)‖ + (t:ℝ) := by
      have h2 : (0:ℝ) ≤ 1 - (t:ℝ) := by linarith [t.2.2]
      have h3 : (0:ℝ) ≤ ‖U (t,x)‖ + (t:ℝ) := by linarith [t.2.1, norm_nonneg (U (t,x))]
      rw [abs_of_nonneg h2, abs_of_nonneg h3] at hnorm
      exact hnorm
    by_cases ht : (t:ℝ) = 1
    · rw [ht] at h1
      linarith [norm_nonneg (U (t,x))]
    · have h1t : (1:ℝ) - (t:ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
      have hxp : (1 - (t:ℝ)) • (((x : punct n p) : sphType n) : eucl n)
          = (1 - (t:ℝ)) • ((p : sphType n) : eucl n) := by
        rw [hsplit, h1]
      exact hxne ((smul_right_inj h1t).mp hxp)
  -- The target point `-p` of the contraction.
  let y : punct n p :=
    ⟨⟨-((p : sphType n) : eucl n), by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_neg]; exact hpnorm⟩,
      by
        intro hh
        have hv : -((p : sphType n) : eucl n) = ((p : sphType n) : eucl n) := Subtype.ext_iff.mp hh
        have hpne : ((p : sphType n) : eucl n) ≠ 0 := by
          intro h0; rw [h0, norm_zero] at hpnorm; exact zero_ne_one hpnorm
        have h2 : (2:ℝ) • ((p : sphType n) : eucl n) = 0 := by
          rw [two_smul]; exact neg_eq_iff_add_eq_zero.mp hv
        rcases (smul_eq_zero.mp h2) with h | h
        · norm_num at h
        · exact hpne h⟩
  let H : C(I × punct n p, punct n p) :=
    { toFun := fun z => ⟨⟨Φ z, hΦmem z⟩, fun hh => hΦne z (congrArg Subtype.val hh)⟩
      continuous_toFun := (hΦc.subtype_mk hΦmem).subtype_mk
        (fun z hh => hΦne z (congrArg Subtype.val hh)) }
  have H_zero : ∀ x : punct n p, H (0, x) = x := by
    intro x
    have hxnorm : ‖(((x : punct n p) : sphType n) : eucl n)‖ = 1 := by
      have hmem := (x.1).2
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hmem
      exact hmem
    apply Subtype.ext
    apply Subtype.ext
    show Φ (0, x) = (((x : punct n p) : sphType n) : eucl n)
    dsimp only [Φ]
    rw [hU0 x, hxnorm]
    simp
  have H_one : ∀ x : punct n p, H (1, x) = y := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    show Φ (1, x) = -((p : sphType n) : eucl n)
    dsimp only [Φ]
    rw [hU1 x]
    simp [hpnorm]
  refine ⟨(contractible_iff_id_nullhomotopic (punct n p)).mpr ⟨y, ⟨?_⟩⟩⟩
  exact { toContinuousMap := H, map_zero_left := fun x => H_zero x, map_one_left := fun x => H_one x }

end Work.Sphere
