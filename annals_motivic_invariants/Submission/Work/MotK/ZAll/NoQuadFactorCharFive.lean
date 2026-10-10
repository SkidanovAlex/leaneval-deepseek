import Mathlib
import Submission.Work.MotK.TGen.ZS2.shape_le_two
import Submission.Work.MotK.TGen.ZS3.shape_le_three
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000

open MvPolynomial

namespace Work.MotK.ZAll

/-- In characteristic `5`, the five-term quintic `f = a X₀⁵ + b X₀²X₁ + c X₀X₁³ + d X₁⁵ + e`
(with `a,d,e ≠ 0`) is not the product of a polynomial of total degree `≤ 2` and one of total
degree `≤ 3` unless the coefficient `c` of `X₀X₁³` vanishes.

This is the `(2,3)`-case core of `Work.MotK.TGen.ZElim2IrredCharAll` in characteristic `5`.
Proof route (CAS-verified).  Using the normal-form lemmas `Work.MotK.TGen.ZS2.shape_le_two` and
`Work.MotK.TGen.ZS3.shape_le_three` write `g = a₀X₀²+a₁X₀X₁+a₂X₁²+uX₀+vX₁+w` and
`h = A₃X₀³+B₂X₀²X₁+C₁X₀X₁²+D₀X₁³+A₂X₀²+B₁X₀X₁+C₀X₁²+A₁X₀+B₀X₁+P₀`.  The substitution
`X₀ ↦ T`, `X₁ ↦ λ·T` (with `λ` a formal variable) turns `g·h = f` into an identity in `(K[λ])[T]`;
comparing the `T⁵` coefficients and then the `λ`-coefficients gives the six equations
`a₀A₃ = a`, `a₀B₂+a₁A₃ = 0`, `a₀C₁+a₁B₂+a₂A₃ = 0`, `a₀D₀+a₁C₁+a₂B₂ = 0`, `a₁D₀+a₂C₁ = 0`,
`a₂D₀ = d`.  In characteristic `5` these force `a₀a₂+a₁² = 0` (so that `a₀X₀²+a₁X₀X₁+a₂X₁²` is
`a₀` times a square `(X₀+βX₁)²` with `β = a₁/(2a₀)`) and force `-A₃β³+B₂β²-C₁β+D₀ = 0`.  Hence the
substitution `X₀ ↦ -βX₁` kills the quadratic part of `g` and the cubic part of `h`, so the image
of `g·h` has degree `≤ 3`, while the image of `f` has `X₁⁴`-coefficient `-cβ`; since `β ≠ 0` this
forces `c = 0`. -/
theorem NoQuadFactorCharFive {K : Type} [Field K] (h5 : (5 : K) = 0) (a b c d e : K)
    (ha : a ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (g h : MvPolynomial (Fin 2) K)
    (hg : g.totalDegree ≤ 2) (hh : h.totalDegree ≤ 3)
    (hgh : g * h = MvPolynomial.C a * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(5:ℕ)
      + MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ) * MvPolynomial.X 1
      + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(3:ℕ)
      + MvPolynomial.C d * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(5:ℕ) + MvPolynomial.C e) :
    c = 0 := by
  -- normal forms for `g` and `h`
  obtain ⟨a0, a1, u, a2, v, w, hg_eq⟩ :=
    Work.MotK.TGen.ZS2.shape_le_two g hg (le_trans (MvPolynomial.degreeOf_le_totalDegree g 0) hg)
  obtain ⟨A3, B2, A2, C1, B1, A1, D0, C0, B0, P0, hh_eq⟩ :=
    Work.MotK.TGen.ZS3.shape_le_three h hh (le_trans (MvPolynomial.degreeOf_le_totalDegree h 0) hh)
  -- the coefficient polynomials of `g` and `h` (with `λ` playing the role of the second variable)
  let α2 : Polynomial K := Polynomial.C a0 + Polynomial.C a1 * Polynomial.X
    + Polynomial.C a2 * Polynomial.X ^(2:ℕ)
  let α1 : Polynomial K := Polynomial.C u + Polynomial.C v * Polynomial.X
  let α0 : Polynomial K := Polynomial.C w
  let β3 : Polynomial K := Polynomial.C A3 + Polynomial.C B2 * Polynomial.X
    + Polynomial.C C1 * Polynomial.X ^(2:ℕ) + Polynomial.C D0 * Polynomial.X ^(3:ℕ)
  let β2 : Polynomial K := Polynomial.C A2 + Polynomial.C B1 * Polynomial.X
    + Polynomial.C C0 * Polynomial.X ^(2:ℕ)
  let β1 : Polynomial K := Polynomial.C A1 + Polynomial.C B0 * Polynomial.X
  let β0 : Polynomial K := Polynomial.C P0
  -- the substitution `X₀ ↦ T`, `X₁ ↦ λ·T` into `(K[λ])[T]`
  set ψ : MvPolynomial (Fin 2) K →+* Polynomial (Polynomial K) :=
    MvPolynomial.eval₂Hom
      ((Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)).comp
        (Polynomial.C : K →+* Polynomial K))
      ![(Polynomial.X : Polynomial (Polynomial K)),
        Polynomial.C (Polynomial.X : Polynomial K) * Polynomial.X]
    with hψdef
  have hψg : ψ g = Polynomial.C α2 * Polynomial.X ^(2:ℕ) + Polynomial.C α1 * Polynomial.X
      + Polynomial.C α0 := by
    rw [hψdef, hg_eq]
    dsimp only [α2, α1, α0]
    simp only [map_add, map_mul, map_pow, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      RingHom.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.C_mul,
      Polynomial.C_pow, Polynomial.C_add]
    first | refl_ring1 | ring
  have hψh : ψ h = Polynomial.C β3 * Polynomial.X ^(3:ℕ) + Polynomial.C β2 * Polynomial.X ^(2:ℕ)
      + Polynomial.C β1 * Polynomial.X + Polynomial.C β0 := by
    rw [hψdef, hh_eq]
    dsimp only [β3, β2, β1, β0]
    simp only [map_add, map_mul, map_pow, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      RingHom.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.C_mul,
      Polynomial.C_pow, Polynomial.C_add]
    first | refl_ring1 | ring
  have hψf : ψ (MvPolynomial.C a * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(5:ℕ)
      + MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ) * MvPolynomial.X 1
      + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(3:ℕ)
      + MvPolynomial.C d * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(5:ℕ) + MvPolynomial.C e)
      = Polynomial.C (Polynomial.C a + Polynomial.C d * Polynomial.X ^(5:ℕ)) * Polynomial.X ^(5:ℕ)
        + Polynomial.C (Polynomial.C c * Polynomial.X ^(3:ℕ)) * Polynomial.X ^(4:ℕ)
        + Polynomial.C (Polynomial.C b * Polynomial.X) * Polynomial.X ^(3:ℕ)
        + Polynomial.C (Polynomial.C e) := by
    rw [hψdef]
    simp only [map_add, map_mul, map_pow, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      RingHom.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.C_mul,
      Polynomial.C_pow, Polynomial.C_add]
    first | refl_ring1 | ring
  have hprod : (Polynomial.C α2 * Polynomial.X ^(2:ℕ) + Polynomial.C α1 * Polynomial.X
        + Polynomial.C α0)
      * (Polynomial.C β3 * Polynomial.X ^(3:ℕ) + Polynomial.C β2 * Polynomial.X ^(2:ℕ)
        + Polynomial.C β1 * Polynomial.X + Polynomial.C β0)
      = Polynomial.C (α2 * β3) * Polynomial.X ^(5:ℕ)
        + Polynomial.C (α2 * β2 + α1 * β3) * Polynomial.X ^(4:ℕ)
        + Polynomial.C (α2 * β1 + α1 * β2 + α0 * β3) * Polynomial.X ^(3:ℕ)
        + Polynomial.C (α2 * β0 + α1 * β1 + α0 * β2) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (α1 * β0 + α0 * β1) * Polynomial.X
        + Polynomial.C (α0 * β0) := by
    simp only [Polynomial.C_mul, Polynomial.C_add]
    first | refl_ring1 | ring
  have hc5 : Polynomial.coeff (ψ g * ψ h) 5 = α2 * β3 := by
    rw [hψg, hψh, hprod]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  have hc5f : Polynomial.coeff (ψ (MvPolynomial.C a * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(5:ℕ)
      + MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ) * MvPolynomial.X 1
      + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(3:ℕ)
      + MvPolynomial.C d * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(5:ℕ) + MvPolynomial.C e)) 5
      = Polynomial.C a + Polynomial.C d * Polynomial.X ^(5:ℕ) := by
    rw [hψf]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X_pow, Polynomial.coeff_X]
    norm_num
  have hmul : ψ g * ψ h = ψ (g * h) := (map_mul ψ g h).symm
  have hgh' := congrArg ψ hgh
  have hkey : α2 * β3 = Polynomial.C a + Polynomial.C d * Polynomial.X ^(5:ℕ) := by
    rw [← hc5, hmul, hgh', hc5f]
  -- expand the product to read off the six coefficient equations
  have hexp : α2 * β3
      = Polynomial.C (a0 * A3) * Polynomial.X ^(0:ℕ)
        + Polynomial.C (a0 * B2 + a1 * A3) * Polynomial.X ^(1:ℕ)
        + Polynomial.C (a0 * C1 + a1 * B2 + a2 * A3) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (a0 * D0 + a1 * C1 + a2 * B2) * Polynomial.X ^(3:ℕ)
        + Polynomial.C (a1 * D0 + a2 * C1) * Polynomial.X ^(4:ℕ)
        + Polynomial.C (a2 * D0) * Polynomial.X ^(5:ℕ) := by
    dsimp only [α2, β3]
    simp only [Polynomial.C_mul, Polynomial.C_add]
    first | refl_ring1 | ring
  have hkey' : α2 * β3
      = Polynomial.C a * Polynomial.X ^(0:ℕ) + Polynomial.C d * Polynomial.X ^(5:ℕ) := by
    rw [pow_zero, mul_one]; exact hkey
  have hh := hkey'
  rw [hexp] at hh
  have e50 : a0 * A3 = a := by
    have h := congrArg (fun q : Polynomial K => Polynomial.coeff q 0) hh
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X_pow, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  have e41 : a0 * B2 + a1 * A3 = 0 := by
    have h := congrArg (fun q : Polynomial K => Polynomial.coeff q 1) hh
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X_pow, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  have e32 : a0 * C1 + a1 * B2 + a2 * A3 = 0 := by
    have h := congrArg (fun q : Polynomial K => Polynomial.coeff q 2) hh
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X_pow, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  have e23 : a0 * D0 + a1 * C1 + a2 * B2 = 0 := by
    have h := congrArg (fun q : Polynomial K => Polynomial.coeff q 3) hh
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X_pow, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  have e14 : a1 * D0 + a2 * C1 = 0 := by
    have h := congrArg (fun q : Polynomial K => Polynomial.coeff q 4) hh
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X_pow, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  have e05 : a2 * D0 = d := by
    have h := congrArg (fun q : Polynomial K => Polynomial.coeff q 5) hh
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X_pow, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  -- non-vanishing of the top coefficients
  have ha0 : a0 ≠ 0 := fun h0 => ha (by rw [← e50, h0, zero_mul])
  have ha2 : a2 ≠ 0 := fun h0 => hd (by rw [← e05, h0, zero_mul])
  have hA3 : A3 ≠ 0 := fun h0 => ha (by rw [← e50, h0, mul_zero])
  have hD0 : D0 ≠ 0 := fun h0 => hd (by rw [← e05, h0, mul_zero])
  -- `2 ≠ 0` in `K`
  have h2 : (2 : K) ≠ 0 := by
    intro h2
    have h : ((2 : K) + 2 + 1) = 0 := by rw [← h5]; norm_num
    rw [h2] at h
    exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using h)
  have h2a0 : (2 : K) * a0 ≠ 0 := mul_ne_zero h2 ha0
  -- auxiliary consequences of the top equations
  have e41a : a0 * a1 * a2 * B2 + a1 ^(2:ℕ) * a2 * A3 = 0 := by linear_combination (a1 * a2) * e41
  have e14a : a0 ^(2:ℕ) * a1 * D0 + a0 ^(2:ℕ) * a2 * C1 = 0 := by linear_combination (a0 ^(2:ℕ)) * e14
  have e32a : a0 ^(2:ℕ) * a2 * C1 + a0 * a1 * a2 * B2 + a0 * a2 ^(2:ℕ) * A3 = 0 := by
    linear_combination (norm := first | refl_ring1 | ring1) (a0 * a2) * e32
  have hi : a2 * A3 * (a0 * a2 - a1 ^(2:ℕ)) = a0 ^(2:ℕ) * a1 * D0 := by
    linear_combination (norm := first | refl_ring1 | ring1) e32a - e14a - e41a
  have e41b : a0 * a2 ^(2:ℕ) * B2 + a1 * a2 ^(2:ℕ) * A3 = 0 := by linear_combination (a2 ^(2:ℕ)) * e41
  have e14b : a0 * a1 ^(2:ℕ) * D0 + a0 * a1 * a2 * C1 = 0 := by linear_combination (a0 * a1) * e14
  have e23a : a0 ^(2:ℕ) * a2 * D0 + a0 * a1 * a2 * C1 + a0 * a2 ^(2:ℕ) * B2 = 0 := by
    linear_combination (norm := first | refl_ring1 | ring1) (a0 * a2) * e23
  have hii : a0 * D0 * (a0 * a2 - a1 ^(2:ℕ)) = a1 * a2 ^(2:ℕ) * A3 := by
    linear_combination (norm := first | refl_ring1 | ring1) e23a - e41b - e14b
  -- the quadratic part of `g` is a square
  have hC : a0 * a2 + a1 ^(2:ℕ) = 0 := by
    have hu2 : (a0 * a2 - a1 ^(2:ℕ)) ^(2:ℕ) = a0 * a2 * a1 ^(2:ℕ) := by
      have hmem : a0 * a2 * A3 * D0 * (a0 * a2 - a1 ^(2:ℕ)) ^(2:ℕ)
          = a0 * a2 * A3 * D0 * (a0 * a2 * a1 ^(2:ℕ)) := by
        linear_combination (norm := first | refl_ring1 | ring1) (a0 * D0 * (a0 * a2 - a1 ^(2:ℕ))) * hi + (a0 ^(2:ℕ) * a1 * D0) * hii
      exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 ha2) hA3) hD0) hmem
    have hsq : (a0 * a2 + a1 ^(2:ℕ)) ^(2:ℕ) = 0 := by
      have h : (a0 * a2 + a1 ^(2:ℕ)) ^(2:ℕ)
          = (a0 * a2 - a1 ^(2:ℕ)) ^(2:ℕ) + 4 * (a0 * a2 * a1 ^(2:ℕ)) := by ring
      rw [h, hu2]
      linear_combination (norm := first | refl_ring1 | ring1) (a0 * a2 * a1 ^(2:ℕ)) * h5
    exact sq_eq_zero_iff.mp hsq
  have ha1 : a1 ≠ 0 := by
    intro h1
    have h : a0 * a2 = 0 := by linear_combination hC - a1 * h1
    exact mul_ne_zero ha0 ha2 h
  -- `2a₁³A₃ = a₀³D₀`
  have h2D : 2 * a1 ^(3:ℕ) * A3 = a0 ^(3:ℕ) * D0 := by
    have h1 : -2 * a1 ^(3:ℕ) * a2 * A3 = -a0 ^(3:ℕ) * a2 * D0 := by
      linear_combination (norm := first | refl_ring1 | ring1) (a1) * hi + (a0 ^(2:ℕ) * D0 - a1 * a2 * A3) * hC
    exact mul_right_cancel₀ ha2 (by linear_combination (-1) * h1)
  -- the cubic part of `h` vanishes at `X₀ = -βX₁`
  have hβ5 : ∀ β : K, (2 : K) * a0 * β = a1 →
      -A3 * β ^(3:ℕ) + B2 * β ^(2:ℕ) - C1 * β + D0 = 0 := by
    intro β hβ2
    have h16 : (16 : K) ≠ 0 := by
      have h : (16 : K) = 2 ^(4:ℕ) := by norm_num
      rw [h]; exact pow_ne_zero 4 h2
    have hzero : 16 * a0 ^(3:ℕ) * a2 * (-A3 * β ^(3:ℕ) + B2 * β ^(2:ℕ) - C1 * β + D0) = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1)
        (-2 * a2 * A3 * ((2 * a0 * β) ^(2:ℕ) + (2 * a0 * β) * a1 + a1 ^(2:ℕ))
          + 4 * a0 * a2 * B2 * (2 * a0 * β + a1) - 8 * a0 ^(2:ℕ) * a2 * C1) * hβ2
        + (4 * a1 ^(2:ℕ) * a2) * e41 + (-(3 * a2)) * h2D + (-(8 * a0 ^(2:ℕ) * a1)) * e14
        + (8 * a0 ^(2:ℕ) * D0) * hC + (a0 ^(3:ℕ) * a2 * D0) * h5
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (mul_ne_zero (mul_ne_zero h16 (pow_ne_zero 3 ha0)) ha2)
    · exact h
  -- `g`'s quadratic part is `a₀` times a square
  have hquad : ∀ β : K, (2 : K) * a0 * β = a1 → a0 * β ^(2:ℕ) - a1 * β + a2 = 0 := by
    intro β hβ2
    have hkey2 : ((2 : K) * a0) ^(2:ℕ) * (a0 * β ^(2:ℕ) - a1 * β + a2) = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) (a0 * (2 * a0 * β + a1) - 2 * a0 * a1) * hβ2
        + (-a0) * hC + (a0 ^(2:ℕ) * a2) * h5
    exact (mul_eq_zero.mp hkey2).resolve_left (pow_ne_zero 2 h2a0)
  obtain ⟨β, hβdef⟩ : ∃ β : K, (2 : K) * a0 * β = a1 :=
    ⟨a1 / (2 * a0), by rw [mul_comm]; exact div_mul_cancel₀ a1 h2a0⟩
  have hβne : β ≠ 0 := by
    intro h0
    have h : a1 = 0 := by rw [← hβdef, h0, mul_zero]
    exact ha1 h
  have hqβ : a0 * β ^(2:ℕ) - a1 * β + a2 = 0 := hquad β hβdef
  have hcβ3 : -A3 * β ^(3:ℕ) + B2 * β ^(2:ℕ) - C1 * β + D0 = 0 := hβ5 β hβdef
  have hquadP : Polynomial.C a0 * Polynomial.C β ^(2:ℕ) - Polynomial.C a1 * Polynomial.C β
      + Polynomial.C a2 = 0 := by
    have h := congrArg Polynomial.C hqβ
    simp only [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_add, Polynomial.C_sub,
      Polynomial.C_neg, map_zero] at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  have hcubP : -Polynomial.C A3 * Polynomial.C β ^(3:ℕ) + Polynomial.C B2 * Polynomial.C β ^(2:ℕ)
      - Polynomial.C C1 * Polynomial.C β + Polynomial.C D0 = 0 := by
    have h := congrArg Polynomial.C hcβ3
    simp only [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_add, Polynomial.C_sub,
      Polynomial.C_neg, map_zero] at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  -- the substitution `X₀ ↦ -βX₁`, `X₁ ↦ X₁`
  let φ : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
    MvPolynomial.aeval ![Polynomial.C (-β) * Polynomial.X, Polynomial.X]
  have hφdef : φ = MvPolynomial.aeval ![Polynomial.C (-β) * Polynomial.X, Polynomial.X] := rfl
  have hφg : φ g = Polynomial.C (v - u * β) * Polynomial.X + Polynomial.C w := by
    rw [hφdef, hg_eq]
    simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.algebraMap_eq,
      Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg,
      Polynomial.C_1, Polynomial.C_0]
    linear_combination (norm := first | refl_ring1 | ring1) (Polynomial.X ^(2:ℕ)) * hquadP
  have hφh : φ h = Polynomial.C (A2 * β ^(2:ℕ) - B1 * β + C0) * Polynomial.X ^(2:ℕ)
      + Polynomial.C (B0 - A1 * β) * Polynomial.X + Polynomial.C P0 := by
    rw [hφdef, hh_eq]
    simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.algebraMap_eq,
      Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg,
      Polynomial.C_1, Polynomial.C_0]
    linear_combination (norm := first | refl_ring1 | ring1) (Polynomial.X ^(3:ℕ)) * hcubP
  have hφf : φ (MvPolynomial.C a * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(5:ℕ)
      + MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ) * MvPolynomial.X 1
      + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(3:ℕ)
      + MvPolynomial.C d * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(5:ℕ) + MvPolynomial.C e)
      = Polynomial.C (-(c * β)) * Polynomial.X ^(4:ℕ) + Polynomial.C (b * β ^(2:ℕ)) * Polynomial.X ^(3:ℕ)
        + Polynomial.C (d - a * β ^(5:ℕ)) * Polynomial.X ^(5:ℕ) + Polynomial.C e := by
    rw [hφdef]
    simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.algebraMap_eq,
      Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg,
      Polynomial.C_1, Polynomial.C_0]
    first | refl_ring1 | ring
  have hprod2 : (Polynomial.C (v - u * β) * Polynomial.X + Polynomial.C w)
      * (Polynomial.C (A2 * β ^(2:ℕ) - B1 * β + C0) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (B0 - A1 * β) * Polynomial.X + Polynomial.C P0)
      = Polynomial.C ((v - u * β) * (A2 * β ^(2:ℕ) - B1 * β + C0)) * Polynomial.X ^(3:ℕ)
        + Polynomial.C ((v - u * β) * (B0 - A1 * β) + w * (A2 * β ^(2:ℕ) - B1 * β + C0))
            * Polynomial.X ^(2:ℕ)
        + Polynomial.C ((v - u * β) * P0 + w * (B0 - A1 * β)) * Polynomial.X
        + Polynomial.C (w * P0) := by
    simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub]
    first | refl_ring1 | ring
  have hc4 : Polynomial.coeff (φ g * φ h) 4 = 0 := by
    rw [hφg, hφh, hprod2]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  have hc4f : Polynomial.coeff (φ (MvPolynomial.C a * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(5:ℕ)
      + MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ) * MvPolynomial.X 1
      + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(3:ℕ)
      + MvPolynomial.C d * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(5:ℕ) + MvPolynomial.C e)) 4
      = -(c * β) := by
    rw [hφf]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  have hmul2 : φ g * φ h = φ (g * h) := (map_mul φ g h).symm
  have hgh2 := congrArg φ hgh
  have hzero : -(c * β) = 0 := by
    rw [← hc4f, ← hgh2, ← hmul2]
    exact hc4
  have hcβ : c * β = 0 := neg_eq_zero.mp hzero
  exact (mul_eq_zero.mp hcβ).resolve_right hβne

end Work.MotK.ZAll
