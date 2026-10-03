import Mathlib
import Submission.Work.KMTPlan.A6.MdlIwLow
import Submission.Work.Analysis.Paraproduct.LpNormZMod_logconvex

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Interpolation of the bilinear minor-arc estimate on `ℤ/Qℤ` (`bile` for `r ≥ 1`)

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022), Proposition `bile` for a general exponent `r ≥ 1`: the bilinear
average `A(f,g) = Q⁻¹ ∑_y f(x - y) g(x - P y)` on `ℤ/Qℤ`, restricted to the Ionescu--Wainger
minor-arc condition on one of the two inputs (`MdlIwMinorArc`), satisfies

* `‖A(f,g)‖_{L¹} ≤ ε ‖f‖_{L²} ‖g‖_{L²}`   (hypothesis `h1`)  and
* `‖A(f,g)‖_{L^{q₀}} ≤ C ‖f‖_{L²} ‖g‖_{L²}` (hypothesis `h2`, `1 < q₀`);

then for `θ ∈ [0,1]` and `1/r = θ/1 + (1 - θ)/q₀` one has the interpolated bound

`‖A(f,g)‖_{L^r} ≤ ε^θ C^{1-θ} ‖f‖_{L²} ‖g‖_{L²}`

(`bileInterpIw`).  The only ingredient is the log-convexity (Lyapunov/Hölder interpolation) of the
`L^p` norms on `ℤ/Qℤ`, `Work.Analysis.Paraproduct.LpNormZMod_logconvex`, applied to the *single*
function `u = A(f,g)`: the two hypotheses are norm bounds on that one function, so no operator
interpolation is involved, and the minor-arc condition is used only to invoke `h1`.
-/

namespace Work.KMTPlan.A6

open Work.Analysis.Concentration

/-- **The interpolation algebra.**  For `ε, C, A ≥ 0` and any real `θ`,
`(ε A)^θ (C A)^{1-θ} = ε^θ C^{1-θ} A` (the `θ + (1-θ) = 1` case of `x^{a+b} = x^a x^b`). -/
private lemma rpow_mul_absorb {ε C A θ : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    (ε * A) ^ θ * (C * A) ^ (1 - θ) = ε ^ θ * C ^ (1 - θ) * A := by
  rw [Real.mul_rpow hε hA, Real.mul_rpow hC hA]
  have hone : θ + (1 - θ) = 1 := by ring
  calc ε ^ θ * A ^ θ * (C ^ (1 - θ) * A ^ (1 - θ))
      = ε ^ θ * C ^ (1 - θ) * (A ^ θ * A ^ (1 - θ)) := by ring
    _ = ε ^ θ * C ^ (1 - θ) * A ^ (θ + (1 - θ)) := by
          rw [Real.rpow_add' hA (by rw [hone]; norm_num)]
    _ = ε ^ θ * C ^ (1 - θ) * A := by rw [hone, Real.rpow_one]

/-- **Lyapunov interpolation of the two `L^p` bounds of a single function.**  If `u : ZMod Q → ℂ`
satisfies `‖u‖_{L¹} ≤ ε A` and `‖u‖_{L^{q₀}} ≤ C A` with `A ≥ 0`, then for `θ ∈ [0,1]` and
`1/r = θ/1 + (1 - θ)/q₀`, `‖u‖_{L^r} ≤ ε^θ C^{1-θ} A`. -/
private lemma LpNormZMod_interp_of_bounds (Q : ℕ) [NeZero Q] {q₀ r θ ε C A : ℝ} (hq₀ : 1 < q₀)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hrel : 1 / r = θ / 1 + (1 - θ) / q₀)
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hA : 0 ≤ A) {u : ZMod Q → ℂ}
    (h1 : LpNormZMod Q 1 u ≤ ε * A) (h2 : LpNormZMod Q q₀ u ≤ C * A) :
    LpNormZMod Q r u ≤ ε ^ θ * C ^ (1 - θ) * A := by
  have hθ1' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hεA : 0 ≤ ε * A := mul_nonneg hε hA
  have hCA : 0 ≤ C * A := mul_nonneg hC hA
  calc LpNormZMod Q r u
      ≤ LpNormZMod Q 1 u ^ θ * LpNormZMod Q q₀ u ^ (1 - θ) :=
        Work.Analysis.Paraproduct.LpNormZMod_logconvex Q hq₀ hθ0 hθ1 hrel u
    _ ≤ (ε * A) ^ θ * (C * A) ^ (1 - θ) :=
        mul_le_mul (Real.rpow_le_rpow (LpNormZMod_nonneg Q 1 u) h1 hθ0)
          (Real.rpow_le_rpow (LpNormZMod_nonneg Q q₀ u) h2 hθ1')
          (Real.rpow_nonneg (LpNormZMod_nonneg Q q₀ u) _) (Real.rpow_nonneg hεA θ)
    _ = ε ^ θ * C ^ (1 - θ) * A := rpow_mul_absorb hε hC hA

theorem bileInterpIw (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] {ρ : ℝ} {l : ℕ}
    {q₀ r θ ε C : ℝ} (hq₀ : 1 < q₀) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hrel : 1 / r = θ / 1 + (1 - θ) / q₀) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (h1 : ∀ f g : ZMod Q → ℂ,
      (Work.KMTPlan.A6.MdlIwMinorArc ρ l Q f ∨ Work.KMTPlan.A6.MdlIwMinorArc ρ l Q g) →
      Work.Analysis.Concentration.LpNormZMod Q 1
          (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ ε * Work.Analysis.Concentration.LpNormZMod Q 2 f *
            Work.Analysis.Concentration.LpNormZMod Q 2 g)
    (h2 : ∀ f g : ZMod Q → ℂ,
      Work.Analysis.Concentration.LpNormZMod Q q₀
          (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ C * Work.Analysis.Concentration.LpNormZMod Q 2 f *
            Work.Analysis.Concentration.LpNormZMod Q 2 g) :
    ∀ f g : ZMod Q → ℂ,
      (Work.KMTPlan.A6.MdlIwMinorArc ρ l Q f ∨ Work.KMTPlan.A6.MdlIwMinorArc ρ l Q g) →
      Work.Analysis.Concentration.LpNormZMod Q r
          (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ ε ^ θ * C ^ (1 - θ) * Work.Analysis.Concentration.LpNormZMod Q 2 f *
            Work.Analysis.Concentration.LpNormZMod Q 2 g := by
  intro f g hfg
  have hA0 : 0 ≤ LpNormZMod Q 2 f * LpNormZMod Q 2 g :=
    mul_nonneg (LpNormZMod_nonneg Q 2 f) (LpNormZMod_nonneg Q 2 g)
  have h1' : LpNormZMod Q 1 (polyBilinearAverageZMod Polynomial.X P Q f g)
      ≤ ε * (LpNormZMod Q 2 f * LpNormZMod Q 2 g) := by
    calc LpNormZMod Q 1 (polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ ε * LpNormZMod Q 2 f * LpNormZMod Q 2 g := h1 f g hfg
      _ = ε * (LpNormZMod Q 2 f * LpNormZMod Q 2 g) := by ring
  have h2' : LpNormZMod Q q₀ (polyBilinearAverageZMod Polynomial.X P Q f g)
      ≤ C * (LpNormZMod Q 2 f * LpNormZMod Q 2 g) := by
    calc LpNormZMod Q q₀ (polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ C * LpNormZMod Q 2 f * LpNormZMod Q 2 g := h2 f g
      _ = C * (LpNormZMod Q 2 f * LpNormZMod Q 2 g) := by ring
  calc LpNormZMod Q r (polyBilinearAverageZMod Polynomial.X P Q f g)
      ≤ ε ^ θ * C ^ (1 - θ) * (LpNormZMod Q 2 f * LpNormZMod Q 2 g) :=
        LpNormZMod_interp_of_bounds (Q := Q) hq₀ hθ0 hθ1 hrel hε hC hA0 h1' h2'
    _ = ε ^ θ * C ^ (1 - θ) * LpNormZMod Q 2 f * LpNormZMod Q 2 g := by ring

end Work.KMTPlan.A6
