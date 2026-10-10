import Mathlib
import Submission.Work.MotK.TGen.CruxAux
import Submission.Work.MotK.TGen.SdG5hHomogFac
import Submission.Work.MotK.TGen.SdG5hLinNorm
import Submission.Work.MotK.TGen.SdG5hQuadNorm
import Submission.Work.MotK.TGen.SdG5hLinearCase
import Submission.Work.MotK.TGen.SdG5hQuadEquations
import Submission.Work.MotK.TGen.SdG5hQuadAlg
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.Gg_reducible_disc`

`Gg g₁ g₂ g₃ g₄ g₅ = g₁x₀⁵ + g₂x₁⁵ + g₃x₂⁵ + g₄x₀²x₁x₂² + g₅x₀x₁³x₂`.  Over a field of
characteristic `≠ 5` and with `g₁, g₂, g₃ ≠ 0`, a *reducible* `Gg` forces the discriminant
relation `g₅² = 5 g₂ g₄`.

This is exactly the contrapositive of the crux `Gg_irreducible` of
`Submission/Work/MotK/TGen/SdG5hCrux.lean` (`g₅² ≠ 5 g₂ g₄ ⟹ Irreducible (Gg …)`), whose
statement is `private` there; the assembly is therefore reproduced here under the same names,
built only from the public ingredients `SdG5hHomogFac`, `SdG5hLinNorm`, `SdG5hQuadNorm`,
`SdG5hLinearCase`, `SdG5hQuadEquations` and `SdG5hQuadAlg`:

* a non-trivial factorization `Gg = F·H` has both factors homogeneous with
  `F.totalDegree + H.totalDegree = 5` (`SdG5hHomogFac`), so (up to swapping) one of them has
  degree `1` or `2`;
* the corresponding case (`SdG5hLinearCase`, respectively `SdG5hQuadEquations` + `SdG5hQuadAlg`
  after the normalizations `SdG5hLinNorm`/`SdG5hQuadNorm`) forces `g₅² = 5 g₂ g₄`.
-/

set_option maxHeartbeats 8000000
set_option autoImplicit false

namespace Work.MotK.TGen

open MvPolynomial

/-- Nilpotent elements of a field vanish. -/
private lemma isNilpotent_eq_zero_of_ne_zero {K : Type} [Field K] {x : K} (hx : x ≠ 0) :
    ¬ IsNilpotent x := by
  rintro ⟨n, hn⟩
  obtain ⟨u, hu⟩ := isUnit_iff_ne_zero.mpr hx
  have h1 : (↑u⁻¹ : K) ^ n * x ^ n = 0 := by rw [hn, mul_zero]
  rw [← hu, ← mul_pow, Units.inv_mul, one_pow] at h1
  exact one_ne_zero h1

private lemma isReduced_of_field (K : Type) [Field K] : IsReduced K :=
  ⟨fun x hx => by
    by_contra hx0
    exact isNilpotent_eq_zero_of_ne_zero hx0 hx⟩

/-- Evaluation of a ternary polynomial at the point `(1,0,0)`. -/
private noncomputable def ev100 {K : Type} [Field K] : MvPolynomial (Fin 3) K →ₐ[K] K :=
  MvPolynomial.aeval (fun i : Fin 3 => ![1, 0, 0] i)

/-- Evaluation of a ternary polynomial at the origin. -/
private noncomputable def ev0 {K : Type} [Field K] : MvPolynomial (Fin 3) K →ₐ[K] K :=
  MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))

private lemma ev100_Gg {K : Type} [Field K] (g1 g2 g3 g4 g5 : K) :
    ev100 (Gg g1 g2 g3 g4 g5) = g1 := by
  rw [ev100, Gg]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  norm_num

private lemma ev0_Gg {K : Type} [Field K] (g1 g2 g3 g4 g5 : K) :
    ev0 (Gg g1 g2 g3 g4 g5) = 0 := by
  rw [ev0, Gg]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  norm_num

private lemma ev0_C {K : Type} [Field K] (r : K) : ev0 (C r) = r := by
  rw [ev0, MvPolynomial.aeval_C]
  simp

/-- The evaluation at `(1,0,0)` reads off the `x₀`-coefficient of a homogeneous polynomial. -/
private lemma ev100_eq_coeff {K : Type} [Field K] (F : MvPolynomial (Fin 3) K) (d : ℕ)
    (hF : F.IsHomogeneous d) :
    ev100 F = F.coeff (Finsupp.single (0 : Fin 3) d) := by
  rw [ev100]
  conv_lhs => rw [MvPolynomial.as_sum F]
  rw [map_sum]
  have hdeg : ∀ v ∈ F.support, v.degree = d := by
    intro v hv
    have hv' : F.coeff v ≠ 0 := MvPolynomial.mem_support_iff.mp hv
    have hw : Finsupp.weight (1 : Fin 3 → ℕ) v = d := hF hv'
    rw [Finsupp.degree_eq_weight_one]
    exact hw
  have hzero : ∀ v : Fin 3 →₀ ℕ, v.degree = d → v ≠ Finsupp.single (0 : Fin 3) d →
      (MvPolynomial.aeval (fun i : Fin 3 => ![(1 : K), 0, 0] i))
        (MvPolynomial.monomial v (F.coeff v)) = 0 := by
    intro v hvd hvne
    have h1 : v 1 ≠ 0 ∨ v 2 ≠ 0 := by
      by_contra hcon
      simp only [not_or, not_not] at hcon
      refine hvne (Finsupp.ext fun i => ?_)
      fin_cases i
      · show v 0 = (Finsupp.single (0 : Fin 3) d) 0
        rw [Finsupp.single_eq_same]
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hvd
        omega
      · show v 1 = (Finsupp.single (0 : Fin 3) d) 1
        rw [Finsupp.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0)]
        exact hcon.1
      · show v 2 = (Finsupp.single (0 : Fin 3) d) 2
        rw [Finsupp.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0)]
        exact hcon.2
    rw [MvPolynomial.aeval_monomial]
    have hz : v.prod (fun n e => ![(1 : K), 0, 0] n ^ e) = 0 := by
      rw [Finsupp.prod_eq_zero_iff]
      rcases h1 with h1 | h1
      · exact ⟨1, Finsupp.mem_support_iff.mpr h1, by
          rw [show ![(1 : K), 0, 0] (1 : Fin 3) = 0 from by simp, zero_pow h1]⟩
      · exact ⟨2, Finsupp.mem_support_iff.mpr h1, by
          rw [show ![(1 : K), 0, 0] (2 : Fin 3) = 0 from by simp, zero_pow h1]⟩
    rw [hz, mul_zero]
  have h₁ : ∀ b ∈ F.support, b ≠ Finsupp.single (0 : Fin 3) d →
      (MvPolynomial.aeval (fun i : Fin 3 => ![(1 : K), 0, 0] i))
        (MvPolynomial.monomial b (F.coeff b)) = 0 :=
    fun v hv hvne => hzero v (hdeg v hv) hvne
  have h₂ : Finsupp.single (0 : Fin 3) d ∉ F.support →
      (MvPolynomial.aeval (fun i : Fin 3 => ![(1 : K), 0, 0] i))
        (MvPolynomial.monomial (Finsupp.single (0 : Fin 3) d)
          (F.coeff (Finsupp.single (0 : Fin 3) d))) = 0 := by
    intro hmem
    have h0 : F.coeff (Finsupp.single (0 : Fin 3) d) = 0 := by
      by_contra hc
      exact hmem (MvPolynomial.mem_support_iff.mpr hc)
    rw [h0]
    simp
  rw [Finset.sum_eq_single (Finsupp.single (0 : Fin 3) d) h₁ h₂]
  rw [MvPolynomial.aeval_monomial]
  have hz : (Finsupp.single (0 : Fin 3) d).prod (fun n e => ![(1 : K), 0, 0] n ^ e) = 1 := by
    rw [Finsupp.prod_single_index (a := (0 : Fin 3)) (b := d)
      (h := fun n e => ![(1 : K), 0, 0] n ^ e) (by simp)]
    simp
  rw [hz, mul_one]
  simp

/-- A polynomial of total degree `0` is a nonzero constant, hence a unit. -/
private lemma isUnit_of_totalDegree_zero {K : Type} [Field K] {p : MvPolynomial (Fin 3) K}
    (hp0 : p ≠ 0) (hp : p.totalDegree = 0) : IsUnit p := by
  haveI : IsReduced K := isReduced_of_field K
  have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  refine ⟨p.coeff 0, isUnit_iff_ne_zero.mpr ?_, hC⟩
  rintro h0
  exact hp0 (by rw [hC, h0, map_zero])

/-- **A homogeneous factor of degree `1` or `2` forces the discriminant relation.** -/
private theorem Gg_small_factor {K : Type} [Field K] (g1 g2 g3 g4 g5 : K) (h1 : g1 ≠ 0)
    (h2 : g2 ≠ 0) (h3 : g3 ≠ 0) (h5 : ringChar K ≠ 5) (G H : MvPolynomial (Fin 3) K)
    (hGhom : G.IsHomogeneous G.totalDegree) (hfac : G * H = Gg g1 g2 g3 g4 g5)
    (hd : G.totalDegree = 1 ∨ G.totalDegree = 2) : g5 ^ 2 = 5 * g2 * g4 := by
  have hφne : ev100 G ≠ 0 := by
    intro hG0
    have hGH : ev100 (G * H) = g1 := by rw [hfac]; exact ev100_Gg g1 g2 g3 g4 g5
    rw [map_mul, hG0, zero_mul] at hGH
    exact h1 hGH.symm
  have hc : G.coeff (Finsupp.single (0 : Fin 3) G.totalDegree) ≠ 0 := by
    rw [← ev100_eq_coeff G G.totalDegree hGhom]
    exact hφne
  rcases hd with hd | hd
  · -- the linear case
    obtain ⟨c, b, d, hc0, hGl⟩ := SdG5hLinNorm G (by rwa [hd] at hGhom) (by simpa [hd] using hc)
    have hfac2 : (X 0 + C b * X 1 + C d * X 2) * (C c * H) = Gg g1 g2 g3 g4 g5 := by
      rw [← hfac, hGl]; ring
    exact SdG5hLinearCase g1 g2 g3 g4 g5 b d h2 h3 (C c * H) hfac2
  · -- the quadratic case
    obtain ⟨c, p, q, r, s, t, hc0, hGq⟩ :=
      SdG5hQuadNorm G (by rwa [hd] at hGhom) (by simpa [hd] using hc)
    have hfac2 : quadF p q r s t * (C c * H) = Gg g1 g2 g3 g4 g5 := by
      rw [← hfac, hGq]; ring
    obtain ⟨hQ1, hG5, hD, hF2, hQ3, hE, hqt⟩ :=
      quadEquationsScalar g1 g2 g3 g4 g5 p q r s t (C c * H) hfac2
    have hp : p ≠ 0 := by
      rintro rfl
      rw [show (0 : K) ^ 3 * r - 2 * 0 * r ^ 2 = 0 from by ring, mul_zero, zero_add] at hF2
      exact h2 hF2
    have hq : q ≠ 0 := by
      rintro rfl
      rw [show (0 : K) ^ 3 * t - 2 * 0 * t ^ 2 = 0 from by ring, mul_zero, zero_add] at hqt
      exact h3 hqt
    have hQ1' : p ^ 4 - 3 * p ^ 2 * r + r ^ 2 = 0 := (mul_eq_zero.mp hQ1).resolve_left h1
    have hQ3' : p ^ 3 * s + 3 * p ^ 2 * q * r - 4 * p * r * s - 2 * q * r ^ 2 = 0 :=
      (mul_eq_zero.mp hQ3).resolve_left h1
    have hD' : g4 * q = g1 * (4 * p * q ^ 3 - 6 * p * q * t - 3 * q ^ 2 * s + 2 * s * t) := by
      rw [sub_eq_zero] at hD; exact hD.symm
    have hE' : g4 * s = g1 * (3 * p ^ 2 * q * t + 3 * p * q ^ 2 * s - 4 * p * s * t + q ^ 3 * r
        - 4 * q * r * t - 2 * q * s ^ 2) := by
      rw [sub_eq_zero] at hE; exact hE.symm
    have hF2' : g2 = g1 * (2 * p * r ^ 2 - p ^ 3 * r) := by
      linear_combination (norm := first | refl_ring1 | ring1) hF2
    have hG5' : g5 = -g1 * (4 * p ^ 3 * q - 3 * p ^ 2 * s - 6 * p * q * r + 2 * r * s) := by
      linear_combination (norm := first | refl_ring1 | ring1) hG5
    exact SdG5hQuadAlg h5 g1 g2 g3 g4 g5 p q r s t h1 h2 h3 (mul_ne_zero hp hq)
      hQ1' hQ3' hD' hE' hF2' hG5'

/-- **The general quintic is irreducible when `g₅² ≠ 5g₂g₄`.** -/
private theorem Gg_irreducible {K : Type} [Field K] (g1 g2 g3 g4 g5 : K) (h1 : g1 ≠ 0)
    (h2 : g2 ≠ 0) (h3 : g3 ≠ 0) (h5 : ringChar K ≠ 5) (hdisc : g5 ^ 2 ≠ 5 * g2 * g4) :
    Irreducible (Gg g1 g2 g3 g4 g5) := by
  haveI : IsReduced K := isReduced_of_field K
  have hG0 : Gg g1 g2 g3 g4 g5 ≠ 0 := by
    intro h0
    exact h1 (by rw [← ev100_Gg g1 g2 g3 g4 g5, h0, map_zero])
  refine ⟨?_, ?_⟩
  · intro hu
    obtain ⟨r, -, hPr⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced (σ := Fin 3)
      (P := Gg g1 g2 g3 g4 g5)).mp hu
    have hr : r = 0 := by
      have hh := congrArg ev0 hPr
      rw [ev0_Gg g1 g2 g3 g4 g5, ev0_C] at hh
      exact hh.symm
    exact hG0 (by rw [hPr, hr, map_zero])
  · intro F H hFH
    have hFac : F * H = Gg g1 g2 g3 g4 g5 := hFH.symm
    have hF0 : F ≠ 0 := fun hf => hG0 (by rw [← hFac, hf, zero_mul])
    have hH0 : H ≠ 0 := fun hf => hG0 (by rw [← hFac, hf, mul_zero])
    obtain ⟨hFhom, hHhom, hdeg5⟩ := SdG5hHomogFac g1 g2 g3 g4 g5 F H hF0 hH0 hFac
    by_cases hle : F.totalDegree ≤ 2
    · rcases Nat.eq_zero_or_pos F.totalDegree with h0 | hpos
      · exact Or.inl (isUnit_of_totalDegree_zero hF0 h0)
      · refine absurd (Gg_small_factor g1 g2 g3 g4 g5 h1 h2 h3 h5 F H hFhom hFac ?_) hdisc
        omega
    · have hgt : 2 < F.totalDegree := not_le.mp hle
      have hHle : H.totalDegree ≤ 2 := by omega
      rcases Nat.eq_zero_or_pos H.totalDegree with h0 | hpos
      · exact Or.inr (isUnit_of_totalDegree_zero hH0 h0)
      · refine absurd (Gg_small_factor g1 g2 g3 g4 g5 h1 h2 h3 h5 H F hHhom ((mul_comm H F).trans hFac) ?_) hdisc
        omega

theorem Gg_reducible_disc {K : Type} [Field K] (hk : ringChar K ≠ 5) (g1 g2 g3 g4 g5 : K) (h1 : g1 ≠ 0) (h2 : g2 ≠ 0) (h3 : g3 ≠ 0) (hred : ¬ Irreducible (Work.MotK.TGen.Gg g1 g2 g3 g4 g5)) : g5 ^ 2 = 5 * g2 * g4 := by
  by_contra hdisc
  exact hred (Gg_irreducible g1 g2 g3 g4 g5 h1 h2 h3 hk hdisc)

end Work.MotK.TGen
