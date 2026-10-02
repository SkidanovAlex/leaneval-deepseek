/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The accumulation set of a dynamic ray is connected

For a parameter `c` with a Böttcher coordinate `φ : ℂ → ℂ` (`Work.ParamRays.IsDynBottcher c φ`)
and an inverse branch `Ψ` of `φ` on the exterior `{w | 1 < ‖w‖}` — continuous there, mapping into
the escaping set, with `φ (Ψ w) = w` — and with `φ` injective on the escaping set, the
accumulation set

`rayAccum c φ θ = ⋂_{ρ > 1} closure {z ∈ R_c(θ) : ‖φ z‖ ≤ ρ}`

of the dynamic ray `R_c(θ)` is **preconnected**.

The argument is elementary and does not use anything about the dynamics of `T_c` beyond the
injectivity of `φ` on the escaping set: with `e = e^{2πiθ}` the ray is parametrised by

`Z r = Ψ (r • e)`, `r > 1`,

so that the truncation at level `ρ` is `Z '' Ioc 1 ρ` (a continuous image of an interval, hence
connected) and `rayAccum c φ θ = ⋂_n closure (Z '' Ioc 1 (1 + 1/(n+1)))`.  Each `closure (Z '' Ioc 1 ρ)`
is compact (boundedness of the Böttcher sublevel of a ray) and preconnected, and the intersection
of a decreasing sequence of compact preconnected sets is preconnected
(`Work.Bottcher.ContractionAux.isPreconnected_iInter_of_antitone_isCompact`).

## Main results

* `Work.LandLeaves.rayParam`, `norm_rayParam_dir`, `continuousOn_rayParam` — the parametrisation of
  the ray by its Böttcher modulus.
* `Work.LandLeaves.exists_rayParam_of_mem_dynRay`, `trunc_eq_image_Ioc` — the ray and its
  truncations are the images of `Ioi 1` resp. `Ioc 1 ρ`.
* `Work.LandLeaves.isPreconnected_closure_trunc` — the closure of a truncation is preconnected.
* `Work.LandLeaves.preconnected_rayAccum` — the target.
-/
import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.isCompact_rayAccum
import Submission.Work.LandLeaves.bottcherInverse
import Submission.Work.Bottcher.ContractionAux.isPreconnected_iInter_of_antitone_isCompact

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Set
open Work.ParamRays (Escaping)

noncomputable section

/-! ## The parametrisation of a dynamic ray by its Böttcher modulus -/

/-- The point of the dynamic ray at angle `θ` and Böttcher modulus `r > 1`: the pullback
`Ψ (r • e^{2πiθ})` of the point of Böttcher modulus `r` on the radial line of angle `θ`. -/
def rayParam (Ψ : ℂ → ℂ) (θ : ℝ) : ℝ → ℂ :=
  fun r => Ψ ((r : ℂ) * Work.Landing.rayDirection θ)

@[simp]
theorem rayParam_apply (Ψ : ℂ → ℂ) (θ r : ℝ) :
    rayParam Ψ θ r = Ψ ((r : ℂ) * Work.Landing.rayDirection θ) := rfl

/-- The modulus of a point of the radial line: `‖r • e^{2πiθ}‖ = r` for `r > 0`. -/
theorem norm_rayParam_dir {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖(r : ℂ) * Work.Landing.rayDirection θ‖ = r := by
  rw [norm_mul, Work.Landing.Rays.norm_rayDirection, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]

/-- The parametrisation of the ray depends continuously on `r`, for `r > 1`. -/
theorem continuousOn_rayParam {Ψ : ℂ → ℂ} (hΨcont : ContinuousOn Ψ {w : ℂ | 1 < ‖w‖})
    (θ : ℝ) (ρ : ℝ) : ContinuousOn (rayParam Ψ θ) (Set.Ioc (1 : ℝ) ρ) := by
  have hf : Continuous fun r : ℝ => (r : ℂ) * Work.Landing.rayDirection θ :=
    Complex.continuous_ofReal.mul continuous_const
  have hcomp : ContinuousOn (fun r : ℝ => Ψ ((r : ℂ) * Work.Landing.rayDirection θ))
      (Set.Ioc (1 : ℝ) ρ) :=
    hΨcont.comp hf.continuousOn (fun r hr => by
      show 1 < ‖(r : ℂ) * Work.Landing.rayDirection θ‖
      rw [norm_rayParam_dir (lt_trans zero_lt_one hr.1) θ]
      exact hr.1)
  exact hcomp

/-! ## The ray and its truncations as images of intervals -/

/-- **Every point of the ray has a Böttcher modulus.**  A point `z` of the dynamic ray `R_c(θ)`
is the image under the inverse branch `Ψ` of the point `r • e^{2πiθ}`, `r > 1`, of the radial
line: `z = Ψ (φ z)`, by injectivity of `φ` on the escaping set, and `φ z` lies on the radial
line. -/
theorem exists_rayParam_of_mem_dynRay {c : ℂ} {φ Ψ : ℂ → ℂ}
    (hφinj : ∀ z w : ℂ, Escaping c z → Escaping c w → φ z = φ w → z = w)
    (hΨesc : ∀ w : ℂ, 1 < ‖w‖ → Escaping c (Ψ w))
    (hΨsec : ∀ w : ℂ, 1 < ‖w‖ → φ (Ψ w) = w)
    {θ : ℝ} {z : ℂ} (hz : z ∈ Work.Landing.dynRay c φ θ) :
    ∃ r : ℝ, 1 < r ∧ z = rayParam Ψ θ r := by
  rw [Work.Landing.dynRay, Set.mem_setOf_eq] at hz
  obtain ⟨hesc, hray⟩ := hz
  rw [Work.Landing.radialRay, Set.mem_setOf_eq] at hray
  obtain ⟨r, hr, hrw⟩ := hray
  have hnorm : 1 < ‖φ z‖ := by
    rw [hrw, norm_rayParam_dir (lt_trans zero_lt_one hr) θ]
    exact hr
  have hΨz : Ψ (φ z) = z := hφinj _ _ (hΨesc _ hnorm) hesc (hΨsec _ hnorm)
  refine ⟨r, hr, ?_⟩
  rw [rayParam_apply, ← hrw]
  exact hΨz.symm

/-- **The truncation of the ray at level `ρ` is the image of `Ioc 1 ρ`** under the
parametrisation `r ↦ Ψ (r • e^{2πiθ})`. -/
theorem trunc_eq_image_Ioc {c : ℂ} {φ Ψ : ℂ → ℂ}
    (hφinj : ∀ z w : ℂ, Escaping c z → Escaping c w → φ z = φ w → z = w)
    (hΨesc : ∀ w : ℂ, 1 < ‖w‖ → Escaping c (Ψ w))
    (hΨsec : ∀ w : ℂ, 1 < ‖w‖ → φ (Ψ w) = w) (θ : ℝ) (ρ : ℝ) :
    Work.Landing.trunc c φ θ ρ = rayParam Ψ θ '' Set.Ioc (1 : ℝ) ρ := by
  ext z
  constructor
  · intro hz
    rw [Work.Landing.mem_trunc] at hz
    obtain ⟨r, hr, hzr⟩ := exists_rayParam_of_mem_dynRay hφinj hΨesc hΨsec hz.1
    refine ⟨r, ⟨hr, ?_⟩, hzr.symm⟩
    have hφz : φ z = (r : ℂ) * Work.Landing.rayDirection θ := by
      rw [hzr, rayParam_apply,
        hΨsec _ (by rw [norm_rayParam_dir (lt_trans zero_lt_one hr) θ]; exact hr)]
    have : ‖φ z‖ = r := by rw [hφz, norm_rayParam_dir (lt_trans zero_lt_one hr) θ]
    linarith [hz.2]
  · rintro ⟨r, hr, rfl⟩
    rw [Work.Landing.mem_trunc]
    have hnorm : 1 < ‖(r : ℂ) * Work.Landing.rayDirection θ‖ := by
      rw [norm_rayParam_dir (lt_trans zero_lt_one hr.1) θ]
      exact hr.1
    constructor
    · rw [Work.Landing.dynRay, Set.mem_setOf_eq]
      refine ⟨hΨesc _ hnorm, ?_⟩
      rw [rayParam_apply, hΨsec _ hnorm, Work.Landing.radialRay, Set.mem_setOf_eq]
      exact ⟨r, hr.1, rfl⟩
    · rw [rayParam_apply, hΨsec _ hnorm, norm_rayParam_dir (lt_trans zero_lt_one hr.1) θ]
      exact hr.2

/-- **The closure of a truncation of a dynamic ray is preconnected**: it is the closure of the
continuous image of the interval `Ioc 1 ρ`. -/
theorem isPreconnected_closure_trunc {c : ℂ} {φ Ψ : ℂ → ℂ}
    (hφinj : ∀ z w : ℂ, Escaping c z → Escaping c w → φ z = φ w → z = w)
    (hΨesc : ∀ w : ℂ, 1 < ‖w‖ → Escaping c (Ψ w))
    (hΨsec : ∀ w : ℂ, 1 < ‖w‖ → φ (Ψ w) = w)
    (hΨcont : ContinuousOn Ψ {w : ℂ | 1 < ‖w‖}) (θ : ℝ) (ρ : ℝ) :
    IsPreconnected (closure (Work.Landing.trunc c φ θ ρ)) := by
  rw [trunc_eq_image_Ioc hφinj hΨesc hΨsec θ ρ]
  exact (IsPreconnected.image isPreconnected_Ioc (rayParam Ψ θ)
    (continuousOn_rayParam hΨcont θ ρ)).closure

/-! ## The target -/

/-- **The accumulation set of a dynamic ray is preconnected.**  It is the intersection of the
decreasing sequence of the closures of the truncations of the ray at the levels
`1 + 1/(n+1) ↘ 1`, each of which is compact and preconnected
(`isPreconnected_closure_trunc`, `isBounded_dynRay_sublevel`). -/
theorem preconnected_rayAccum {c : ℂ} {φ Ψ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ)
    (hφinj : ∀ z w : ℂ, Work.ParamRays.Escaping c z → Work.ParamRays.Escaping c w →
      φ z = φ w → z = w)
    (hΨesc : ∀ w : ℂ, 1 < ‖w‖ → Work.ParamRays.Escaping c (Ψ w))
    (hΨsec : ∀ w : ℂ, 1 < ‖w‖ → φ (Ψ w) = w)
    (hΨcont : ContinuousOn Ψ {w : ℂ | 1 < ‖w‖}) (θ : ℝ) :
    IsPreconnected (Work.Landing.rayAccum c φ θ) := by
  -- the levels `ρ n = 1 + 1/(n+1)`
  have hlevels : ∀ n : ℕ, (1 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by
    intro n
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hmono : ∀ n : ℕ,
      1 + 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 + 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    have h3 := one_div_le_one_div_of_le h1 h2
    linarith
  -- the levels are cofinal below any `σ > 1`
  have hcofinal : ∀ σ : ℝ, 1 < σ → ∃ n : ℕ, 1 + 1 / ((n : ℝ) + 1) ≤ σ := by
    intro σ hσ
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (σ - 1))
    have hpos : (0 : ℝ) < σ - 1 := by linarith
    have hN1 : (1 : ℝ) < (N : ℝ) * (σ - 1) := (div_lt_iff₀ hpos).mp hN
    have hN2 : (1 : ℝ) < ((N : ℝ) + 1) * (σ - 1) := by nlinarith
    have hpos2 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h3 : 1 / ((N : ℝ) + 1) ≤ σ - 1 := by
      rw [div_le_iff₀ hpos2]
      nlinarith
    exact ⟨N, by linarith⟩
  have heq : Work.Landing.rayAccum c φ θ
      = ⋂ n : ℕ, closure (Work.Landing.trunc c φ θ (1 + 1 / ((n : ℝ) + 1))) := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter.mpr fun n => ?_
      exact hx _ (hlevels n)
    · intro hx
      rw [Work.Landing.rayAccum_def, Set.mem_setOf_eq]
      intro σ hσ
      obtain ⟨n, hn⟩ := hcofinal σ hσ
      exact closure_mono (Work.Landing.trunc_mono hn) (Set.mem_iInter.mp hx n)
  rw [heq]
  refine Work.Bottcher.ContractionAux.isPreconnected_iInter_of_antitone_isCompact
    (A := fun n : ℕ => closure (Work.Landing.trunc c φ θ (1 + 1 / ((n : ℝ) + 1))))
    ?_ ?_ ?_
  · intro n
    exact (Work.Landing.Rays.isBounded_dynRay_sublevel hφ θ _).isCompact_closure
  · intro n
    exact isPreconnected_closure_trunc hφinj hΨesc hΨsec hΨcont θ _
  · intro n
    exact closure_mono (Work.Landing.trunc_mono (hmono n))

end

end Work.LandLeaves
