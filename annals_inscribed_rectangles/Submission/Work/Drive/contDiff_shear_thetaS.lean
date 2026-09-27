import Mathlib
import Submission.Work.Drive.encodedShear

/-!
# Joint smoothness of the box shear and of the level twist

`Work.Drive.shear q y` is the cross-shear of the parameter square used to perturb the
ends-clause genericity (`NOTES_LEAD_hodd_blockT6.md` §2.2): the composite of the two
triangular factors `shear₁`, `shear₂`, each of which moves one coordinate of `y` by
`coeff · hb` where the coefficient is an affine function of the *other* coordinate with
coefficients read off from the clamped parameter `ballClamp q`.  `Work.Drive.thetaS s x`
is the analogous twist of the level interval, `x + clamp1 s * hb x`.

This file proves that both are `C^∞` **jointly** in the parameter and in the point, i.e.

* `ContDiff ℝ ⊤ (fun p : 𝔼⁴ × 𝔼² => shear p.1 p.2)`,
* `ContDiff ℝ ⊤ (fun p : ℝ × ℝ => thetaS p.1 p.2)`,

which is the input the local parametric Sard lemma `Work.Drive.localSard_family_in_open`
needs from the reparametrisation (together with the invertibility of the parameter
derivative, which lives in the companion files of this lane).

The proof is a direct computation: the only two analytic ingredients are the smoothness of
`q ↦ ‖q‖²` (Mathlib's `contDiff_norm_sq`) and of `Real.sqrt` on the positive half-line,
which give `q ↦ (2√(1+‖q‖²))⁻¹`; everything else is arithmetic with the `ContDiff`
combinators, the two components having been separated by `contDiff_piLp`.

The auxiliary (private) definitions `shearA`, `shearB` are the two coordinate functions of
`shear`, which is what makes the componentwise argument of `contDiff_piLp` syntactically
clean.
-/

namespace Work.Drive

open scoped Manifold Topology

private abbrev Euc4 := EuclideanSpace ℝ (Fin 4)
private abbrev Euc2 := EuclideanSpace ℝ (Fin 2)

noncomputable section

/-! ## The elementary smooth bricks -/

/-- The parabola bump `hb x = x (1 - x)` is a polynomial, hence smooth. -/
private lemma contDiff_hb_aux : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hb := by
  have h : hb = fun x : ℝ => x * (1 - x) := rfl
  rw [h]
  exact contDiff_id.mul (contDiff_const.sub contDiff_id)

/-- The second component of the parameter pair, as a smooth function of the pair. -/
private lemma contDiff_snd_coord_aux (i : Fin 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Euc4 × Euc2 => p.2 i) :=
  (contDiff_piLp_apply 2 (i := i)).comp contDiff_snd

/-- The clamped parameter `ballClamp` is smooth in `q`: its `i`-th component is
`(2√(1+‖q‖²))⁻¹ * qᵢ`. -/
private lemma contDiff_fst_ballClamp_aux (i : Fin 4) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Euc4 × Euc2 => ballClamp p.1 i) := by
  have h1 : (fun q : Euc4 => ballClamp q i) = fun q => (2 * Real.sqrt (1 + ‖q‖ ^ 2))⁻¹ * q i := by
    funext q; simp [ballClamp]
  have hball : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : Euc4 => ballClamp q i) := by
    rw [h1]
    refine ContDiff.mul ?_ ?_
    · refine ContDiff.inv ?_ (fun q => ?_)
      · exact contDiff_const.mul
          (ContDiff.sqrt (contDiff_const.add (contDiff_norm_sq ℝ)) (fun q => by positivity))
      · have h2 : 0 < Real.sqrt (1 + ‖q‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
        positivity
    · exact (ContinuousLinearMap.proj i).contDiff.comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).contDiff
  exact hball.comp contDiff_fst

/-- The bump of a coordinate of the second component of the pair. -/
private lemma contDiff_snd_hb_aux (i : Fin 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Euc4 × Euc2 => hb (p.2 i)) :=
  contDiff_hb_aux.comp (contDiff_snd_coord_aux i)

/-! ## The two coordinate functions of the shear -/

/-- The first component of `shear q y`, i.e. of `shear₁ q y`:
`y₀ + (a₀(1-2y₁) + a₂ hb y₁) · hb y₀`. -/
private def shearA (p : Euc4 × Euc2) : ℝ :=
  p.2 0 + (ballClamp p.1 0 * (1 - 2 * p.2 1) + ballClamp p.1 2 * hb (p.2 1)) * hb (p.2 0)

/-- The second component of `shear q y`: `y₁` moved by
`(a₁(1-2·shearA) + a₃ hb shearA) · hb y₁` evaluated at the *first* coordinate of the
intermediate point `shear₁ q y`. -/
private def shearB (p : Euc4 × Euc2) : ℝ :=
  p.2 1 + (ballClamp p.1 1 * (1 - 2 * shearA p) + ballClamp p.1 3 * hb (shearA p)) * hb (p.2 1)

private lemma contDiff_shearA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) shearA := by
  have h : shearA = fun p : Euc4 × Euc2 =>
      p.2 0 + (ballClamp p.1 0 * (1 - 2 * p.2 1) + ballClamp p.1 2 * hb (p.2 1)) * hb (p.2 0) :=
    rfl
  rw [h]
  refine ContDiff.add (contDiff_snd_coord_aux 0) ?_
  refine ContDiff.mul (ContDiff.add ?_ ?_) (contDiff_snd_hb_aux 0)
  · exact (contDiff_fst_ballClamp_aux 0).mul
      (contDiff_const.sub (contDiff_const.mul (contDiff_snd_coord_aux 1)))
  · exact (contDiff_fst_ballClamp_aux 2).mul (contDiff_snd_hb_aux 1)

private lemma contDiff_shearB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) shearB := by
  have h : shearB = fun p : Euc4 × Euc2 =>
      p.2 1 + (ballClamp p.1 1 * (1 - 2 * shearA p) + ballClamp p.1 3 * hb (shearA p)) * hb (p.2 1) :=
    rfl
  rw [h]
  refine ContDiff.add (contDiff_snd_coord_aux 1) ?_
  refine ContDiff.mul (ContDiff.add ?_ ?_) (contDiff_snd_hb_aux 1)
  · exact (contDiff_fst_ballClamp_aux 1).mul
      (contDiff_const.sub (contDiff_const.mul contDiff_shearA))
  · exact (contDiff_fst_ballClamp_aux 3).mul (contDiff_hb_aux.comp contDiff_shearA)

/-! ## The clamped parameter of the line -/

private lemma contDiff_clamp1_aux : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) clamp1 := by
  have h : clamp1 = fun s : ℝ => (2 * Real.sqrt (1 + s ^ 2))⁻¹ * s := rfl
  rw [h]
  refine ContDiff.mul (ContDiff.inv ?_ (fun s => ?_)) contDiff_id
  · exact contDiff_const.mul
      (ContDiff.sqrt (contDiff_const.add (contDiff_id.pow 2)) (fun s => by positivity))
  · have hp : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
    positivity

/-! ## The theorem -/

theorem contDiff_shear_thetaS :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.shear p.1 p.2) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.Drive.thetaS p.1 p.2) := by
  constructor
  · -- `shear` is smooth as soon as its two components are, by `contDiff_piLp`
    rw [contDiff_piLp 2]
    intro i
    fin_cases i
    · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) shearA
      exact contDiff_shearA
    · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) shearB
      exact contDiff_shearB
  · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => p.2 + clamp1 p.1 * hb p.2)
    exact ContDiff.add contDiff_snd
      ((contDiff_clamp1_aux.comp contDiff_fst).mul (contDiff_hb_aux.comp contDiff_snd))

end

end Work.Drive
