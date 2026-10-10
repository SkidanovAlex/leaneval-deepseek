import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3.RulingX2

open Polynomial

/-- A monic polynomial cannot divide a nonzero polynomial of smaller `natDegree`. -/
lemma eq_zero_of_dvd_of_natDegree_lt {R : Type*} [Semiring R] {p q : R[X]} (hq : q.Monic)
    (hlt : p.natDegree < q.natDegree) (hdvd : q ∣ p) : p = 0 := by
  obtain ⟨w, rfl⟩ := hdvd
  by_cases hw : w = 0
  · simp [hw]
  · have h := hq.natDegree_mul' hw
    omega

/-- **The norm/unit step of the `(Φ,Γ,P̂)` route to `ZiasSliceNeTop`.**

Let `A` be a nontrivial commutative ring, `Φ = X ^ 2 + C α * X + C β` a *monic* quadratic and
`Γ = C D * X + C R`.  If the norm `R ^ 2 - α * R * D + β * D ^ 2` of `Γ` vanishes, then `(Φ, Γ)` is
not the unit ideal of `A[X]`.

Two equivalent proofs (both positively reviewed):

* *linear algebra.*  Since `Φ` is monic of degree two, `B := A[X] ⧸ (Φ)` is free of rank two over `A`
  with basis `1, X̄` and `X̄ ^ 2 = -α X̄ - β`.  In that basis, multiplication by `Γ̄` has matrix
  `![![R, -D * β], ![D, R - D * α]]`, whose determinant is `R ^ 2 - α * R * D + β * D ^ 2 = h`.
  If `(Φ, Γ) = ⊤` then `Γ̄` is a unit, so its determinant is a unit of `A`; but a unit of a
  nontrivial ring is not `0`, and `h = 0`.  This is the cleanest route
  (`LinearMap.toMatrix`, `Matrix.det_fin_two`, `Module.Free`, `IsUnit.map`).
* *the conjugate.*  In `B`, `Γ̄ * (C R - C (D * α) - C D * X) = 0` (expand and reduce `X ^ 2` using
  the relation); if `Γ̄` is a unit then `C R - C (D * α) - C D * X = 0` in `B`, and as it has degree
  `≤ 1 < 2` it is `0` in `A[X]`, so `D = 0` and `R = 0`, so `Γ = 0`, so `0 = 1` in the nontrivial
  ring `B`.

The corresponding three-generator statement — `P ∣ R ^ 2 - α * R * D + β * D ^ 2` and **`P` a
non-unit** imply `(P, Φ, Γ) ≠ ⊤` — is `span_three_quadratic_linear_ne_top` (dispatched); note that
`P ≠ 0` alone is NOT enough (`P = 1` gives the unit ideal: both reviewers of the first draft caught
this).  That is exactly the last step of the `(P̂, Φ, Γ)` route recorded in
`Submission/Work/MotC5N3/RulingX2/NOTES_ZSST.md`.-/
theorem span_quadratic_linear_ne_top {A : Type*} [CommRing A] [Nontrivial A] (α β D R : A)
    (h : R ^ 2 - α * R * D + β * D ^ 2 = 0) :
    Ideal.span ({(Polynomial.X ^ 2 + Polynomial.C α * Polynomial.X + Polynomial.C β : Polynomial A),
        Polynomial.C D * Polynomial.X + Polynomial.C R} : Set (Polynomial A)) ≠ ⊤ := by
  -- Write `Φ`, `Γ` and the conjugate `Ψ` of `Γ` in `A[X]/(Φ)`.
  intro htop
  set Φ : Polynomial A := X ^ 2 + C α * X + C β with hΦ
  set Γ : Polynomial A := C D * X + C R with hΓ
  set Ψ : Polynomial A := C (R - α * D) - C D * X with hΨ
  -- `Φ` is monic of `natDegree` two.
  have hΦmonic : Φ.Monic := by
    rw [hΦ]
    have hh := monic_X_pow_add (p := (C α * X + C β : Polynomial A)) (n := 2) degree_linear_lt
    simpa [add_assoc] using hh
  have hΦnatDeg : Φ.natDegree = 2 := by
    rw [hΦ]
    have hh := natDegree_quadratic (a := (1 : A)) (b := α) (c := β) one_ne_zero
    simpa using hh
  -- `Ψ` has `natDegree ≤ 1`.
  have hΨnatDeg : Ψ.natDegree ≤ 1 := by
    rw [hΨ]
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_C]
    refine max_le (by norm_num) ?_
    simpa using natDegree_C_mul_X_pow_le (D : A) 1
  -- The conjugation identity: `Γ * Ψ = -C (D ^ 2) * Φ`.
  have key : Γ * Ψ = -(C (D ^ 2)) * Φ := by
    rw [hΓ, hΨ, hΦ]
    have h' : (C D * X + C R : Polynomial A) * (C (R - α * D) - C D * X)
        + C (D ^ 2) * (X ^ 2 + C α * X + C β) = C (R ^ 2 - α * R * D + β * D ^ 2) := by
      simp only [map_sub, map_mul, map_add, map_pow]
      first | refl_ring1 | ring
    rw [h, map_zero] at h'
    rw [neg_mul, eq_neg_iff_add_eq_zero]
    exact h'
  -- Membership of `1` in the ideal, and Bézout coefficients.
  have htop' : Ideal.span ({Φ, Γ} : Set (Polynomial A)) = ⊤ := by
    simpa only [← hΦ, ← hΓ] using htop
  have hmem : (1 : Polynomial A) ∈ Ideal.span ({Φ, Γ} : Set (Polynomial A)) := by
    rw [htop']; exact Submodule.mem_top
  rw [Ideal.mem_span_pair] at hmem
  obtain ⟨p, q, hpq⟩ := hmem
  -- So `Φ ∣ Ψ`, and since `Ψ.natDegree < Φ.natDegree`, `Ψ = 0`.
  have hlt : Ψ.natDegree < Φ.natDegree := by rw [hΦnatDeg]; omega
  have hdiv : Φ ∣ Ψ := by
    refine ⟨p * Ψ - q * C (D ^ 2), ?_⟩
    calc Ψ = 1 * Ψ := by ring
      _ = (p * Φ + q * Γ) * Ψ := by rw [hpq]
      _ = p * Φ * Ψ + q * (Γ * Ψ) := by ring
      _ = p * Φ * Ψ + q * (-(C (D ^ 2)) * Φ) := by rw [key]
      _ = Φ * (p * Ψ - q * C (D ^ 2)) := by ring
  have hΨ0 : Ψ = 0 := eq_zero_of_dvd_of_natDegree_lt hΦmonic hlt hdiv
  -- Reading off the top two coefficients gives `D = 0` and `R = 0`, hence `Γ = 0`.
  have hD : D = 0 := by
    have h1 : Ψ.coeff 1 = 0 := by rw [hΨ0]; simp
    rw [hΨ] at h1
    simpa using h1
  have hR : R - α * D = 0 := by
    have h0 : Ψ.coeff 0 = 0 := by rw [hΨ0]; simp
    rw [hΨ] at h0
    simpa using h0
  have hR0 : R = 0 := by simpa [hD] using hR
  have hΓ0 : Γ = 0 := by simp [hΓ, hD, hR0]
  -- Then `p * Φ = 1`, so `Φ ∣ 1` with `(1).natDegree = 0 < 2 = Φ.natDegree`: contradiction.
  have hpΦ : p * Φ = 1 := by
    have hh := hpq
    rw [hΓ0, mul_zero, add_zero] at hh
    exact hh
  have hdiv1 : Φ ∣ (1 : Polynomial A) := ⟨p, by rw [mul_comm]; exact hpΦ.symm⟩
  have h1zero : (1 : Polynomial A) = 0 :=
    eq_zero_of_dvd_of_natDegree_lt hΦmonic (by rw [natDegree_one, hΦnatDeg]; norm_num) hdiv1
  exact one_ne_zero h1zero

end Work.MotC5N3.RulingX2
