import Mathlib
import Submission.Work.Drive.Whitney.glAuxCoreDefs
import Submission.Work.Drive.Whitney.det_c0ZetaEtaFamily

/-!
# The determinant of `gU` on the square

For `m ≥ 3`, `u w ψ : ℝ × ℝ → ℝ^m` with `u ≠ 0` on the square `K = [0,1]²`, `φ = 1` on `K`
and `ψ ⊥ u` (pointwise), the determinant of the operator family `gU φ u w ψ` of
`glAuxCoreDefs` at a point `p ∈ K` is

  `(gAl + gC) + gLam * gTheta`,

where `gAl`, `gC`, `gLam`, `gTheta` are the auxiliary scalars of `glAuxCoreDefs`.

## Proof

Write `A = ‖u p‖²`, `a = ⟪w p, u p⟫/A`, `n = w p - a • u p`, `J = A⁻¹ • (u ⊗ n - n ⊗ u)`,
`Pu = A⁻¹ • (u ⊗ u)`, `z = gZ φ u w ψ p` and `χ = gChi φ u w ψ p`.  On the square `φ = 1` so
`gAm φ u p = A`, and `gU φ u w ψ p` is *literally* the operator
`a • 1 + J + (C - a • 1) * (1 - Pu)` of the master identity `det_c0ZetaEtaFamily` with `c₀ = 1`
and `C = 1 • (1 - Pu) + z ⊗ χ` (this is the bridge lemma `gU_eq_gUexp` below).  The master
identity then gives

  `det (gU φ u w ψ p) = a (1 + ⟪z, χ⟫) + ((1 + ⟪z, χ⟫) ‖n‖² - ⟪n, χ⟫ ⟪n, z⟫) / A`,

and the pure algebraic identity `det_alg` (with `z = gLam • ψ`, hence `⟪z, χ⟫ = gLam ⟪ψ, χ⟫` and
`⟪n, z⟫ = gLam ⟪n, ψ⟫`) rewrites this into `(a + N/A) + gLam ((a + N/A) ⟪ψ, χ⟫ - ⟪ψ, n⟫ ⟪χ, n⟫/A)`,
which is exactly `(gAl + gC) + gLam * gTheta`.

The hypotheses `hzu` (`ψ ⊥ u`) is used only through `inner ℝ z (u p) = 0` and
`inner ℝ (gChi …) (u p) = 0`, which are the two inputs of the master identity.
-/

namespace Work.Drive.Whitney

open scoped RealInnerProductSpace

variable {m : ℕ}

/-! ## The explicit form of the master identity -/

/-- The explicit form of the operator `a • 1 + J + (C - a • 1) * (1 - Pu)` of
`det_c0ZetaEtaFamily` (with `c₀ = 1`) as a function of the two vectors `uu`, `ww` and the extra
vectors `z`, `e`: `A := ‖uu‖²`, `a := ⟪ww,uu⟫/A`, `n := ww - a • uu`. -/
noncomputable def gUexp (uu ww z e : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (inner ℝ ww uu / ‖uu‖ ^ 2) • 1 +
    (1 / ‖uu‖ ^ 2) •
      (((innerSL ℝ) uu).smulRight (ww - (inner ℝ ww uu / ‖uu‖ ^ 2) • uu) -
        ((innerSL ℝ) (ww - (inner ℝ ww uu / ‖uu‖ ^ 2) • uu)).smulRight uu) +
    (((1:ℝ) • (1 - (1 / ‖uu‖ ^ 2) • ((innerSL ℝ) uu).smulRight uu) +
          ((innerSL ℝ) z).smulRight e -
        (inner ℝ ww uu / ‖uu‖ ^ 2) • 1) *
      (1 - (1 / ‖uu‖ ^ 2) • ((innerSL ℝ) uu).smulRight uu))

/-- The master identity `det_c0ZetaEtaFamily` with `c₀ = 1`, in the explicit form of `gUexp`. -/
lemma det_gUexp {m : ℕ} (hm : 3 ≤ m) (uu ww z e : EuclideanSpace ℝ (Fin m))
    (hu : uu ≠ 0) (hzu : inner ℝ z uu = 0) (heu : inner ℝ e uu = 0) :
    LinearMap.det ((gUexp uu ww z e).toLinearMap) =
      inner ℝ ww uu / ‖uu‖ ^ 2 * (1 + inner ℝ z e) +
        ((1 + inner ℝ z e) * ‖ww - (inner ℝ ww uu / ‖uu‖ ^ 2) • uu‖ ^ 2 -
          inner ℝ (ww - (inner ℝ ww uu / ‖uu‖ ^ 2) • uu) e *
            inner ℝ (ww - (inner ℝ ww uu / ‖uu‖ ^ 2) • uu) z) / ‖uu‖ ^ 2 := by
  have h := det_c0ZetaEtaFamily (m := m) hm uu ww z e 1 hu hzu heu
  simp only [] at h
  simpa only [one_pow, one_mul, mul_one, gUexp] using h

/-- The pure algebraic step of the computation: writing `P = ⟪ψ,χ⟫`, `Q = ⟪n,χ⟫`, `R = ⟪n,ψ⟫`,
the expression produced by the master identity (with `z = lam • ψ`, so that `⟪z,χ⟫ = lam P` and
`⟪n,z⟫ = lam R`) equals `(a + N/A) + lam ((a + N/A) P - R Q / A)`. -/
lemma det_alg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ψ nn χ : E) (A a N lam : ℝ) :
    a * (1 + lam * inner ℝ ψ χ) +
        ((1 + lam * inner ℝ ψ χ) * N - inner ℝ nn χ * (lam * inner ℝ nn ψ)) / A
      = (a + N / A) + lam * ((a + N / A) * inner ℝ ψ χ - inner ℝ ψ nn * inner ℝ χ nn / A) := by
  rw [real_inner_comm ψ nn, real_inner_comm χ nn]
  ring

/-! ## The bridge to `gU` and the main theorem -/

theorem det_gU_on_square {m : ℕ} (hm : 3 ≤ m) (φ : ℝ × ℝ → ℝ)
    (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (hφ1 : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, φ p = 1)
    (hu : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, u p ≠ 0)
    (hzu : ∀ p, inner ℝ (ψ p) (u p) = 0)
    (p : ℝ × ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) :
    LinearMap.det ((Work.Drive.Whitney.gU φ u w ψ p).toLinearMap) =
      (Work.Drive.Whitney.gAl φ u w p + Work.Drive.Whitney.gC φ u w p)
        + Work.Drive.Whitney.gLam φ u w ψ p * Work.Drive.Whitney.gTheta φ u w ψ p := by
  have hφp : φ p = 1 := hφ1 p hp
  have hup : u p ≠ 0 := hu p hp
  have hU2 : inner ℝ (u p) (u p) = ‖u p‖ ^ 2 := real_inner_self_eq_norm_sq (u p)
  have hAm_in : gAm φ u p = inner ℝ (u p) (u p) := by
    simp only [gAm, hφp, one_mul, sub_self, add_zero]
  have hup_ne : inner ℝ (u p) (u p) ≠ 0 := by
    rw [hU2]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hup)
  have hAm_ne : gAm φ u p ≠ 0 := by rw [hAm_in]; exact hup_ne
  have hAl : gAl φ u w p = inner ℝ (w p) (u p) / gAm φ u p := rfl
  have hAe : gAm φ u p = ‖u p‖ ^ 2 := hAm_in.trans hU2
  have hN : ‖gNn φ u w p‖ ^ 2 = gN φ u w p := by
    rw [gN, real_inner_self_eq_norm_sq]
  have hGZ : gZ φ u w ψ p = gLam φ u w ψ p • ψ p := rfl
  -- the two orthogonality inputs of the master identity
  have hna : inner ℝ (gNn φ u w p) (u p) = 0 := by
    rw [gNn, gAl, inner_sub_left, real_inner_smul_left, hAm_in]
    rw [div_mul_cancel₀ _ hup_ne, sub_self]
  have hchi_u : inner ℝ (gChi φ u w ψ p) (u p) = 0 := by
    rw [gChi, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hzu p, hna]
    ring
  have hzu_z : inner ℝ (gZ φ u w ψ p) (u p) = 0 := by
    rw [hGZ, real_inner_smul_left, hzu p, mul_zero]
  -- the bridge: `gU φ u w ψ p` is the explicit operator of the master identity
  have hGU : gU φ u w ψ p = gUexp (u p) (w p) (gZ φ u w ψ p) (gChi φ u w ψ p) := by
    simp only [gU, gUexp, gCfam, gJ, gPu, gAl, gNn, gAm, hφp,
      real_inner_self_eq_norm_sq, one_div, one_smul, one_mul, sub_self, add_zero]
  rw [hGU]
  rw [det_gUexp hm (u p) (w p) (gZ φ u w ψ p) (gChi φ u w ψ p) hup hzu_z hchi_u]
  -- the algebraic reduction of the right-hand side
  rw [← hAe, ← hAl, ← gNn, hN, hGZ, real_inner_smul_left, real_inner_smul_right]
  rw [det_alg (ψ := ψ p) (nn := gNn φ u w p) (χ := gChi φ u w ψ p)
    (A := gAm φ u p) (a := gAl φ u w p) (N := gN φ u w p) (lam := gLam φ u w ψ p)]
  rfl

end Work.Drive.Whitney
