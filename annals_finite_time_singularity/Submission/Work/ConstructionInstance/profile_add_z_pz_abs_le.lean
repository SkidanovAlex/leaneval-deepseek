import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.ConstructionInstance

/-! ## The `F_*` box: `|F_*(z,θ) + z ∂_z F_*(z,θ)| ≤ 20p`

The two `F_*` terms are combined *before* the triangle inequality: the sum collapses to
`p(Γ(θ)/c(p))·4z/(1+z)³`, which is bounded by `20p` uniformly in `z`. -/

/-- `F_*(z,θ) + z·∂_zF_*(z,θ) = p·(Γ(θ)/c(p))·4z/(1+z)³`. -/
theorem Fstar_add_zpz_eq {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {z θ : ℝ} (hz : -1 < z) :
    Work.Construction.Fstar p z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ
      = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (4 * z / (1 + z) ^ 3) := by
  have hDz : z * Work.Spaces.pz (Work.Construction.Fstar p) z θ
      = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (2 * z * (1 - z) / (1 + z) ^ 3) :=
    Work.Construction.Dz_Fstar_eq hp hz
  have hz1 : (1 + z) ^ 3 ≠ 0 := by
    have : (0 : ℝ) < 1 + z := by linarith
    positivity
  have hc : Work.Spaces.c p ≠ 0 := by
    have := (Work.Spaces.c_bounds p hp hp1).1; linarith
  rw [hDz, Work.Construction.Fstar, Work.FM.Fstar]
  field_simp
  ring

/-- **The `F_*` part of the `z`-derivative box.**  For `0 < p ≤ 1`, `z > 0`, `θ ∈ [0,π/2]`,
`|F_*(z,θ) + z∂_zF_*(z,θ)| ≤ 20p`. -/
theorem Fstar_add_zpz_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar p z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ|
      ≤ 20 * p := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hG0 : 0 ≤ Work.Spaces.Gam p θ := (Work.Spaces.Gam_bounds p θ hp hθ).1
  have hG1 : Work.Spaces.Gam p θ ≤ 1 := (Work.Spaces.Gam_bounds p θ hp hθ).2
  have hz1 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hgc0 : 0 ≤ Work.Spaces.Gam p θ / Work.Spaces.c p := div_nonneg hG0 hcpos.le
  have h1 : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
    rw [div_le_iff₀ hcpos]; nlinarith [hG1]
  have hfrac0 : 0 ≤ 4 * z / (1 + z) ^ 3 := by positivity
  have h2 : 4 * z / (1 + z) ^ 3 ≤ 1 := by
    rw [div_le_one hz1]
    nlinarith [sq_nonneg z, mul_nonneg (sq_nonneg z) hz.le]
  rw [Fstar_add_zpz_eq hp hp1 (by linarith)]
  calc |p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (4 * z / (1 + z) ^ 3)|
      = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (4 * z / (1 + z) ^ 3) :=
        abs_of_nonneg (mul_nonneg (mul_nonneg hp.le hgc0) hfrac0)
    _ ≤ p * 10 * 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h1 hp.le
        · exact h2
        · exact hfrac0
        · positivity
    _ = 10 * p := by ring
    _ ≤ 20 * p := by linarith [hp.le]

/-! ## Differentiability of `F_*` in `z` at fixed `θ` -/

/-- `z ↦ F_*(z,θ)` has derivative `∂_zF_*(z,θ)` for `z > -1`. -/
theorem hasDerivAt_Fstar_z {p : ℝ} (z θ : ℝ) (hz : -1 < z) :
    HasDerivAt (fun z' => Work.Construction.Fstar p z' θ)
      (Work.Spaces.pz (Work.Construction.Fstar p) z θ) z := by
  have h := (Work.FM.hasDerivAt_Fstar z hz).const_mul
    (p * (Work.Spaces.Gam p θ / Work.Spaces.c p))
  have hfun : (fun z' => Work.Construction.Fstar p z' θ)
      = fun z' => (p * (Work.Spaces.Gam p θ / Work.Spaces.c p)) * Work.FM.Fstar z' := by
    funext z'; rw [Work.Construction.Fstar]
  have hval : Work.Spaces.pz (Work.Construction.Fstar p) z θ
      = (p * (Work.Spaces.Gam p θ / Work.Spaces.c p)) * (2 * (1 - z) / (1 + z) ^ 3) := by
    rw [Work.Spaces.pz, hfun, deriv_const_mul_field, Work.FM.deriv_Fstar z hz]
  rw [hfun, hval]
  exact h

/-! ## Splitting `∂_zF` into `∂_zF_* + ∂_zg` -/

/-- **Splitting the `z`-derivative of the profile on the positive angular branch**:
for `θ ≥ 0`, differentiating `F = F_* + g` in `z` gives `∂_zF = ∂_zg + ∂_zF_*`.  The
hypothesis `hgdiff` (together with the differentiability of `F_*`) is what makes `g`
differentiable, so that `deriv` splits. -/
theorem pz_profile_eq_of_nonneg {p : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : -1 < z) (hθ : 0 ≤ θ)
    (hgdiff : HasDerivAt (fun z' => profile p g z' θ) (Work.Spaces.pz (profile p g) z θ) z) :
    Work.Spaces.pz (profile p g) z θ
      = Work.Spaces.pz g z θ + Work.Spaces.pz (Work.Construction.Fstar p) z θ := by
  have hF := hasDerivAt_Fstar_z (p := p) z θ hz
  have hsub := hgdiff.sub hF
  have hfun : ((fun z' => profile p g z' θ) - fun z' => Work.Construction.Fstar p z' θ)
      = fun z' => g z' θ := by
    funext z'; simp only [Pi.sub_apply]; rw [profile_of_nonneg hθ]; ring
  rw [hfun] at hsub
  have hd := hsub.deriv
  simp only [Work.Spaces.pz] at hd ⊢
  linarith [hd]

/-- **Splitting the `z`-derivative of the profile on the negative angular branch**:
for `θ < 0`, `F(z,θ) = -(F_*(z,-θ) + g(z,-θ))`, so
`∂_zF(z,θ) = -(∂_zg(z,-θ) + ∂_zF_*(z,-θ))`. -/
theorem pz_profile_eq_of_neg {p : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : -1 < z) (hθ : θ < 0)
    (hgdiff : HasDerivAt (fun z' => profile p g z' θ) (Work.Spaces.pz (profile p g) z θ) z) :
    Work.Spaces.pz (profile p g) z θ
      = -(Work.Spaces.pz g z (-θ) + Work.Spaces.pz (Work.Construction.Fstar p) z (-θ)) := by
  have hF := hasDerivAt_Fstar_z (p := p) z (-θ) hz
  have hEq : (fun z' => profile p g z' θ)
      = fun z' => -(Work.Construction.Fstar p z' (-θ) + g z' (-θ)) := by
    funext z'; rw [profile_of_neg (not_le.mpr hθ)]
  rw [hEq] at hgdiff
  have hneg : HasDerivAt (fun z' => Work.Construction.Fstar p z' (-θ) + g z' (-θ))
      (-(Work.Spaces.pz (profile p g) z θ)) z := by
    convert hgdiff.neg using 1
    funext z'; simp
  have hsub := hneg.sub hF
  have hfun : ((fun z' => Work.Construction.Fstar p z' (-θ) + g z' (-θ))
        - fun z' => Work.Construction.Fstar p z' (-θ)) = fun z' => g z' (-θ) := by
    funext z'; simp only [Pi.sub_apply]; ring
  rw [hfun] at hsub
  have hd := hsub.deriv
  simp only [Work.Spaces.pz] at hd ⊢
  linarith [hd]

/-! ## The `z`-derivative box -/

/-- **The `z`-derivative box of the profile.**  For `0 < p ≤ 1`, `z > 0`, `|θ| ≤ π/2`, with the
perturbation `g` bounded by `Cg` and its `z`-weighted derivative `z∂_z g` bounded by `Cg'`, and with
the profile `F = F_* + g` differentiable in `z` (hypothesis `hgdiff`, which is `HasDerivAt` with
the derivative *defined* to be `Work.Spaces.pz (profile p g) z θ`), we have

  `|F(z,θ) + z∂_zF(z,θ)| ≤ 20p + Cg + Cg'`.

The point of the statement is that the two `F_*` terms are combined *before* the triangle inequality:
`F_*(z,θ) + z∂_zF_*(z,θ) = p(Γ(θ)/c(p))·4z/(1+z)³`, which is bounded by `20p` uniformly in `z`,
whereas `|F_*|` and `|z∂_zF_*|` separately are bounded only by `20pΓ` and `5p`. -/
theorem profile_add_z_pz_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg Cg' : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hgdiff : ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' => profile p g z' θ) (Work.Spaces.pz (profile p g) z θ) z)
    {z θ : ℝ} (hz : 0 < z) (hθ : |θ| ≤ Real.pi / 2) :
    |profile p g z θ + z * Work.Spaces.pz (profile p g) z θ| ≤ 20 * p + Cg + Cg' := by
  have hz1 : -1 < z := by linarith
  -- the box for the perturbation `g`, on the positive branch
  have hgbox : ∀ φ : ℝ, φ ∈ Work.Spaces.Iθ →
      |g z φ + z * Work.Spaces.pz g z φ| ≤ Cg + Cg' := by
    intro φ hφ
    calc |g z φ + z * Work.Spaces.pz g z φ|
        ≤ |g z φ| + |z * Work.Spaces.pz g z φ| := abs_add_le _ _
      _ ≤ Cg + Cg' := add_le_add (hgbdd z φ hz.le hφ) (hg2 z φ hz.le hφ)
  rcases le_or_gt 0 θ with hθ0 | hθ0
  · -- positive branch
    have hθmem : θ ∈ Work.Spaces.Iθ :=
      ⟨hθ0, by rw [abs_of_nonneg hθ0] at hθ; exact hθ⟩
    have hsplit := pz_profile_eq_of_nonneg (p := p) (g := g) (z := z) (θ := θ) hz1 hθ0
      (hgdiff z θ hz)
    have hprof : profile p g z θ = Work.Construction.Fstar p z θ + g z θ := profile_of_nonneg hθ0
    have hkey : profile p g z θ + z * Work.Spaces.pz (profile p g) z θ
        = (Work.Construction.Fstar p z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ)
          + (g z θ + z * Work.Spaces.pz g z θ) := by
      rw [hprof, hsplit]; ring
    rw [hkey]
    calc |(Work.Construction.Fstar p z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ)
            + (g z θ + z * Work.Spaces.pz g z θ)|
        ≤ |Work.Construction.Fstar p z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ|
            + |g z θ + z * Work.Spaces.pz g z θ| := abs_add_le _ _
      _ ≤ 20 * p + (Cg + Cg') :=
          add_le_add (Fstar_add_zpz_abs_le hp hp1 hz hθmem) (hgbox θ hθmem)
      _ = 20 * p + Cg + Cg' := by ring
  · -- negative branch: reduce to `-θ > 0`
    have hθmem : -θ ∈ Work.Spaces.Iθ :=
      ⟨by linarith, by rw [abs_of_neg hθ0] at hθ; exact hθ⟩
    have hsplit := pz_profile_eq_of_neg (p := p) (g := g) (z := z) (θ := θ) hz1 hθ0
      (hgdiff z θ hz)
    have hprof : profile p g z θ
        = -(Work.Construction.Fstar p z (-θ) + g z (-θ)) := profile_of_neg (not_le.mpr hθ0)
    have hkey : profile p g z θ + z * Work.Spaces.pz (profile p g) z θ
        = -((Work.Construction.Fstar p z (-θ)
              + z * Work.Spaces.pz (Work.Construction.Fstar p) z (-θ))
            + (g z (-θ) + z * Work.Spaces.pz g z (-θ))) := by
      rw [hprof, hsplit]; ring
    rw [hkey, abs_neg]
    calc |(Work.Construction.Fstar p z (-θ) + z * Work.Spaces.pz (Work.Construction.Fstar p) z (-θ))
            + (g z (-θ) + z * Work.Spaces.pz g z (-θ))|
        ≤ |Work.Construction.Fstar p z (-θ) + z * Work.Spaces.pz (Work.Construction.Fstar p) z (-θ)|
            + |g z (-θ) + z * Work.Spaces.pz g z (-θ)| := abs_add_le _ _
      _ ≤ 20 * p + (Cg + Cg') :=
          add_le_add (Fstar_add_zpz_abs_le hp hp1 hz hθmem) (hgbox (-θ) hθmem)
      _ = 20 * p + Cg + Cg' := by ring

end Work.ConstructionInstance
