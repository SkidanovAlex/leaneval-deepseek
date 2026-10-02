import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Locality of the ray parametrisation `(θ, t) ↦ rayPt θ t`

Off the filled Julia set `K c` the map `(θ, t) ↦ rayPt hN θ t` (`t > 1`) is a local
homeomorphism onto `(K c)ᶜ`: it is the composition of the (local) diffeomorphism
`(θ, t) ↦ t · exp (2πiθ)` of the exterior disc with the homeomorphism
`hN.e.symm : exteriorDisc ≃ₜ (K c)ᶜ` of the Böttcher coordinate.  The present file
records the concrete consequence that (the hypotheses are exactly those of the
target lemma) every point `z ∉ K c` sufficiently close to `rayPt θ₀ t₀` is of the
form `rayPt θ t` with `θ` close to `θ₀` and `t` close to `t₀`.

The formalisation is deliberately explicit: for `w ≠ 0` we exhibit the inverse
angle
`thetaOf θ₀ w = θ₀ + arg (w · exp (-2πiθ₀)) / (2π)`,
for which `‖w‖ · exp (2πi · thetaOf θ₀ w) = w` holds *globally*, and which is
continuous (indeed has the value `θ₀`) at `w = t₀ · exp (2πiθ₀)`.
-/

namespace Work.ELTop

open Complex
open Filter
open scoped Topology

/-- The angle of `w ∈ ℂ` obtained by rotating back by `-2πθ₀` and reading off the
argument: the left inverse of `w ↦ ‖w‖ · exp (2πi · θ₀)` near the ray of angle `θ₀`. -/
noncomputable def thetaOf (θ₀ : ℝ) (w : ℂ) : ℝ :=
  θ₀ + Complex.arg (w * Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * (θ₀ : ℂ) * Complex.I))) /
    (2 * Real.pi)

/-- The fundamental identity: the ray point of the angle `thetaOf θ₀ w` at level `‖w‖`
is `w` itself.  (Valid for every `w`, in particular on the whole exterior disc.) -/
lemma rayPoint_thetaOf (θ₀ : ℝ) (w : ℂ) :
    Work.Top.NakaneData.rayPoint (thetaOf θ₀ w) ‖w‖ = w := by
  set A : ℂ := ((2 * Real.pi : ℝ) : ℂ) * (θ₀ : ℂ) * Complex.I with hA
  set y : ℂ := w * Complex.exp (-A) with hy
  have hAre : (-A).re = 0 := by rw [hA]; simp
  have hnorm : ‖y‖ = ‖w‖ := by
    rw [hy, norm_mul, Complex.norm_exp, hAre, Real.exp_zero, mul_one]
  have harg : (thetaOf θ₀ w : ℝ) = θ₀ + Complex.arg y / (2 * Real.pi) := rfl
  rw [Work.Top.NakaneData.rayPoint, harg]
  have hexp : Complex.exp
        ((2 * (Real.pi : ℂ) * ((θ₀ + Complex.arg y / (2 * Real.pi) : ℝ) : ℂ)) * Complex.I)
      = Complex.exp A * Complex.exp (Complex.arg y * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hA]
    push_cast
    field_simp
  rw [hexp]
  have hE' : Complex.exp (-A) * Complex.exp A = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  calc ‖w‖ * (Complex.exp A * Complex.exp (Complex.arg y * Complex.I))
      = (‖w‖ * Complex.exp (Complex.arg y * Complex.I)) * Complex.exp A := by ring
    _ = (‖y‖ * Complex.exp (Complex.arg y * Complex.I)) * Complex.exp A := by rw [hnorm]
    _ = y * Complex.exp A := by rw [Complex.norm_mul_exp_arg_mul_I]
    _ = (w * Complex.exp (-A)) * Complex.exp A := by rw [hy]
    _ = w := by rw [mul_assoc, hE', mul_one]

/-- Rotating the ray point of angle `θ₀` at level `t₀` back by `-2πθ₀` gives the
positive real `t₀`. -/
lemma rayPoint_mul_exp_neg {θ₀ t₀ : ℝ} :
    Work.Top.NakaneData.rayPoint θ₀ t₀ *
      Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * (θ₀ : ℂ) * Complex.I)) = (t₀ : ℂ) := by
  rw [Work.Top.NakaneData.rayPoint]
  have hE : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (θ₀ : ℂ) * Complex.I) *
      Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * (θ₀ : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc t₀ * Complex.exp (2 * ↑Real.pi * ↑θ₀ * I) *
        Complex.exp (-(↑(2 * Real.pi) * ↑θ₀ * I))
      = (t₀ : ℂ) * (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (θ₀ : ℂ) * Complex.I) *
          Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * (θ₀ : ℂ) * Complex.I))) := by
        push_cast; ring
    _ = t₀ := by rw [hE, mul_one]

/-- At the ray point itself, `thetaOf` returns the defining angle. -/
lemma thetaOf_self {θ₀ t₀ : ℝ} (ht₀ : 0 < t₀) :
    thetaOf θ₀ (Work.Top.NakaneData.rayPoint θ₀ t₀) = θ₀ := by
  simp only [thetaOf, rayPoint_mul_exp_neg, Complex.arg_ofReal_of_nonneg ht₀.le, zero_div,
    add_zero]

/-- `thetaOf θ₀` is continuous at the ray point of angle `θ₀`. -/
lemma continuousAt_thetaOf {θ₀ t₀ : ℝ} (ht₀ : 0 < t₀) :
    ContinuousAt (thetaOf θ₀) (Work.Top.NakaneData.rayPoint θ₀ t₀) := by
  change ContinuousAt (fun w : ℂ => θ₀ + Complex.arg (w * Complex.exp
    (-(((2 * Real.pi : ℝ) : ℂ) * (θ₀ : ℂ) * Complex.I))) / (2 * Real.pi))
    (Work.Top.NakaneData.rayPoint θ₀ t₀)
  have hmem : Work.Top.NakaneData.rayPoint θ₀ t₀ *
      Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * (θ₀ : ℂ) * Complex.I)) ∈ Complex.slitPlane := by
    rw [rayPoint_mul_exp_neg, Complex.mem_slitPlane_iff]
    exact Or.inl (by simpa using ht₀)
  have hcont_mul : ContinuousAt
      (fun w : ℂ => w * Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * (θ₀ : ℂ) * Complex.I)))
      (Work.Top.NakaneData.rayPoint θ₀ t₀) :=
    continuousAt_id.mul continuousAt_const
  have hargcont : ContinuousAt
      (fun w : ℂ => Complex.arg (w * Complex.exp
        (-(((2 * Real.pi : ℝ) : ℂ) * (θ₀ : ℂ) * Complex.I))))
      (Work.Top.NakaneData.rayPoint θ₀ t₀) :=
    ContinuousAt.comp (g := Complex.arg)
      (f := fun w : ℂ => w * Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * (θ₀ : ℂ) * Complex.I)))
      (x := Work.Top.NakaneData.rayPoint θ₀ t₀)
      (Complex.continuousAt_arg hmem) hcont_mul
  have := (hargcont.div_const (2 * Real.pi)).const_add θ₀
  simpa using this

/-- **Locality of the ray parametrisation**, in the abstract `NakaneData` language. -/
theorem exists_rayPt_local_nakane {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    {θ₀ t₀ : ℝ} (ht₀ : 1 < t₀) {δθ δt : ℝ} (hδθ : 0 < δθ) (hδt : 0 < δt) :
    ∃ ε > 0, ∀ z : ℂ, z ∉ Mb → ‖z - Work.Top.NakaneData.rayPt hN θ₀ t₀‖ < ε →
      ∃ θ t : ℝ, |θ - θ₀| < δθ ∧ |t - t₀| < δt ∧
        z = Work.Top.NakaneData.rayPt hN θ t := by
  have ht₀pos : 0 < t₀ := by linarith
  have hnormw₀ : ‖Work.Top.NakaneData.rayPoint θ₀ t₀‖ = t₀ := by
    rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos ht₀pos]
  -- Continuity of the two coordinate functions at the base point `w₀`.
  have htendθ : Tendsto (thetaOf θ₀) (𝓝 (Work.Top.NakaneData.rayPoint θ₀ t₀))
      (𝓝 θ₀) := by
    have h : Tendsto (thetaOf θ₀) (𝓝 (Work.Top.NakaneData.rayPoint θ₀ t₀))
        (𝓝 (thetaOf θ₀ (Work.Top.NakaneData.rayPoint θ₀ t₀))) :=
      (continuousAt_thetaOf (θ₀ := θ₀) ht₀pos).tendsto
    rwa [thetaOf_self ht₀pos] at h
  have htendnorm : Tendsto (fun w : ℂ => ‖w‖) (𝓝 (Work.Top.NakaneData.rayPoint θ₀ t₀))
      (𝓝 t₀) := by
    have h : Tendsto (fun w : ℂ => ‖w‖) (𝓝 (Work.Top.NakaneData.rayPoint θ₀ t₀))
        (𝓝 ‖Work.Top.NakaneData.rayPoint θ₀ t₀‖) :=
      continuous_norm.continuousAt
    rwa [hnormw₀] at h
  have hev1 : ∀ᶠ w in 𝓝 (Work.Top.NakaneData.rayPoint θ₀ t₀),
      |thetaOf θ₀ w - θ₀| < δθ := by
    have h := Metric.tendsto_nhds.mp htendθ δθ hδθ
    simpa [Real.dist_eq] using h
  have hev2 : ∀ᶠ w in 𝓝 (Work.Top.NakaneData.rayPoint θ₀ t₀),
      |‖w‖ - t₀| < δt := by
    have h := Metric.tendsto_nhds.mp htendnorm δt hδt
    simpa [Real.dist_eq] using h
  obtain ⟨r₁, hr₁pos, hr₁⟩ := Metric.mem_nhds_iff.mp (hev1.and hev2)
  -- The control radius.
  have hhalf : 0 < (t₀ - 1) / 2 := by linarith
  have hrpos : 0 < min r₁ (min δt ((t₀ - 1) / 2)) := lt_min hr₁pos (lt_min hδt hhalf)
  -- The base point of the plane.
  set x₀ : ↥Mbᶜ := ⟨Work.Top.NakaneData.rayPt hN θ₀ t₀, hN.rayPt_notMem ht₀⟩ with hx₀def
  have hg : Continuous (fun p : ↥Mbᶜ => (hN.e p : ℂ)) :=
    continuous_subtype_val.comp hN.e.continuous
  have hgx : (hN.e x₀ : ℂ) = Work.Top.NakaneData.rayPoint θ₀ t₀ := by
    rw [← hN.he x₀]
    exact hN.Phi_rayPt ht₀
  have hV : (fun p : ↥Mbᶜ => (hN.e p : ℂ)) ⁻¹'
      Metric.ball (Work.Top.NakaneData.rayPoint θ₀ t₀) (min r₁ (min δt ((t₀ - 1) / 2)))
      ∈ 𝓝 x₀ :=
    hg.continuousAt.preimage_mem_nhds (by rw [hgx]; exact Metric.ball_mem_nhds _ hrpos)
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ε, hεpos, ?_⟩
  intro z hz hzdist
  have hp : dist (⟨z, hz⟩ : ↥Mbᶜ) x₀ < ε := by
    rw [Subtype.dist_eq]
    have hco : ((x₀ : ↥Mbᶜ) : ℂ) = Work.Top.NakaneData.rayPt hN θ₀ t₀ := rfl
    rw [hco]
    simpa [dist_eq_norm] using hzdist
  have hgp := hε hp
  have hd : dist (Φ z) (Work.Top.NakaneData.rayPoint θ₀ t₀) < min r₁ (min δt ((t₀ - 1) / 2)) := by
    have h := Metric.mem_ball.mp hgp
    change dist ((hN.e ⟨z, hz⟩ : ℂ)) (Work.Top.NakaneData.rayPoint θ₀ t₀)
      < min r₁ (min δt ((t₀ - 1) / 2)) at h
    rwa [← hN.he ⟨z, hz⟩] at h
  have hdist1 : dist (Φ z) (Work.Top.NakaneData.rayPoint θ₀ t₀) < r₁ :=
    lt_of_lt_of_le hd (min_le_left _ _)
  have hpair := hr₁ hdist1
  have htheta : |thetaOf θ₀ (Φ z) - θ₀| < δθ := hpair.1
  have htnorm : |‖Φ z‖ - t₀| < δt := hpair.2
  have hdistr : dist (Φ z) (Work.Top.NakaneData.rayPoint θ₀ t₀) < (t₀ - 1) / 2 :=
    lt_of_lt_of_le hd (le_trans (min_le_right _ _) (min_le_right _ _))
  have habs : |‖Φ z‖ - t₀| ≤ dist (Φ z) (Work.Top.NakaneData.rayPoint θ₀ t₀) := by
    simpa only [dist_eq_norm, hnormw₀] using
      abs_norm_sub_norm_le (Φ z) (Work.Top.NakaneData.rayPoint θ₀ t₀)
  have hgt1 : 1 < ‖Φ z‖ := by
    have h2 : |‖Φ z‖ - t₀| < (t₀ - 1) / 2 := lt_of_le_of_lt habs hdistr
    have h3 := (abs_lt.mp h2).1
    linarith
  refine ⟨thetaOf θ₀ (Φ z), ‖Φ z‖, htheta, htnorm, ?_⟩
  have hkey := rayPoint_thetaOf θ₀ (Φ z)
  have hwmem : Work.Top.NakaneData.rayPoint (thetaOf θ₀ (Φ z)) ‖Φ z‖ ∈
      Work.Top.exteriorDisc :=
    Work.Top.NakaneData.rayPoint_mem_exteriorDisc hgt1
  have hsub : hN.e (⟨z, hz⟩ : ↥Mbᶜ) =
      (⟨Work.Top.NakaneData.rayPoint (thetaOf θ₀ (Φ z)) ‖Φ z‖, hwmem⟩ :
        ↥Work.Top.exteriorDisc) := by
    apply Subtype.ext
    rw [← hN.he ⟨z, hz⟩]
    exact hkey.symm
  calc z = ((⟨z, hz⟩ : ↥Mbᶜ) : ℂ) := rfl
    _ = ((hN.e.symm (hN.e (⟨z, hz⟩ : ↥Mbᶜ)) : ↥Mbᶜ) : ℂ) := by
          rw [hN.e.symm_apply_apply]
    _ = ((hN.e.symm (⟨Work.Top.NakaneData.rayPoint (thetaOf θ₀ (Φ z)) ‖Φ z‖, hwmem⟩ :
          ↥Work.Top.exteriorDisc) : ↥Mbᶜ) : ℂ) := by rw [hsub]
    _ = Work.Top.NakaneData.rayPt hN (thetaOf θ₀ (Φ z)) ‖Φ z‖ := by
          rw [Work.Top.NakaneData.rayPt, dite_eq_left hgt1]

theorem exists_rayPt_local {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ₀ t₀ : ℝ} (ht₀ : 1 < t₀)
    {δθ δt : ℝ} (hδθ : 0 < δθ) (hδt : 0 < δt) :
    ∃ ε > 0, ∀ z : ℂ, z ∉ Work.EL.K c → ‖z - Work.EL.rayPt hN θ₀ t₀‖ < ε →
      ∃ θ t : ℝ, |θ - θ₀| < δθ ∧ |t - t₀| < δt ∧ z = Work.EL.rayPt hN θ t :=
  exists_rayPt_local_nakane hN ht₀ hδθ hδt

end Work.ELTop
