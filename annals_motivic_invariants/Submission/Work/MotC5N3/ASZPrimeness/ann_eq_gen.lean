import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.ASZGC.Defs
import Submission.Work.MotAS.ASRulV2M.ASZQuadDetGen
import Submission.Work.MotAS.ASZElimP_irreducible
import Submission.Work.MotAS.ASZGC.not_dvd_D0
import Submission.Work.MotAS.aszDpQuad
import Submission.Work.MotC5N3.ASZPrimeness.ann_eq_aux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

/-!
# `Work.MotC5N3.ASZPrimeness.ann_eq_gen` — the colon statement `(P, D0) : (R0) ⊆ (P, D0, R0)`

For `K` a field of characteristic `5`, `a b g : K` with `a² - ab - b² ≠ 0` and
`g ∉ ℘(K) = {c⁵ - c}`, and `P := ASZElim.P a b g`, `D0 := ASZGC.D0 a b g`,
`R0 := ASZGC.R0 a b g ∈ K[X₀,X₁]`, the syzygy `s·R0 = u·P + v·D0` forces
`s ∈ (P, D0, R0)`.

## Structure

* `X0_unit_mod_D0` : `X 0` is a **unit modulo** `(D0)` — this is the `X 0`-decomposition
  `D0 = C(-(2(a+2b)^6)) + X 0 · M0` of `ann_eq_aux` (`D0_decomp`), whose constant term is a unit
  because `a + 2b ≠ 0` follows from `a² - ab - b² ≠ 0` in characteristic `5`.
* `PX0_mem_span_D0_R0sq` : `P·X 0 ∈ (D0, R0²)` — the transported determinant identity
  `R0² - D0·c0 = P·(C c · X 0)` of `ASZQuadDetGen` with `c ≠ 0`.
* `P_mem_span_D0_R0sq` : combining the two gives `P ∈ (D0, R0²)`.
* `R0_dvd_cancel` : `D0 ∣ R0·t → D0 ∣ t`, from `P ∈ (D0, R0²)` and
  `IsRelPrime D0 P` (`P` irreducible and `¬ P ∣ D0`).
* `ann_eq_gen` : the colon statement, from the cancellation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.MotC5N3.ASZPrimeness

open MvPolynomial

/-- **`X 0` is a unit modulo `(D0)`.**  From `D0 = C (-(2(a+2b)^6)) + X 0 · M0` with the constant
coefficient a unit (`a + 2b ≠ 0`), the element `M0 · (2(a+2b)^6)⁻¹` inverts `X 0` modulo `(D0)`. -/
theorem X0_unit_mod_D0 (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) :
    ∃ Y : MvPolynomial (Fin 2) K,
      MvPolynomial.X 0 * Y - 1 ∈
        Ideal.span ({Work.MotAS.ASZGC.D0 a b g} : Set (MvPolynomial (Fin 2) K)) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h2b : a + 2 * b ≠ 0 := by
    intro h0
    apply ha
    have h1 : a = -(2 * b) := by linear_combination h0
    rw [h1]
    linear_combination (norm := first | refl_ring1 | ring1) (b ^(2:ℕ)) * h5
  have hβ : Work.MotAS.aszQuBeta a b ≠ 0 := by
    intro h
    exact Work.MotAS.ASRulV2M.aszQuBeta_sq_ne_zero K a b ha (by rw [h]; ring)
  have ht : (2 : K) * (a + 2 * b) ^(6:ℕ) ≠ 0 := by
    have he : (2 : K) * (a + 2 * b) ^(6:ℕ)
        = Work.MotAS.aszQuBeta a b * (a + 2 * b) ^(2:ℕ) := by
      rw [Work.MotAS.aszQuBeta_eq a b]; ring
    rw [he]
    exact mul_ne_zero hβ (pow_ne_zero 2 h2b)
  refine ⟨M0 K a b g * MvPolynomial.C (((2 : K) * (a + 2 * b) ^(6:ℕ))⁻¹), ?_⟩
  rw [Ideal.mem_span_singleton]
  refine ⟨MvPolynomial.C (((2 : K) * (a + 2 * b) ^(6:ℕ))⁻¹), ?_⟩
  rw [D0_decomp]
  have hcc : MvPolynomial.C (-((2 : K) * (a + 2 * b) ^(6:ℕ)))
      * MvPolynomial.C (((2 : K) * (a + 2 * b) ^(6:ℕ))⁻¹)
        = (-1 : MvPolynomial (Fin 2) K) := by
    rw [← MvPolynomial.C_mul, neg_mul, mul_inv_cancel₀ ht, MvPolynomial.C_neg,
      MvPolynomial.C_1]
  have key : MvPolynomial.X 0
        * (M0 K a b g * MvPolynomial.C (((2 : K) * (a + 2 * b) ^(6:ℕ))⁻¹)) - 1
      = (MvPolynomial.C (-((2 : K) * (a + 2 * b) ^(6:ℕ))) + MvPolynomial.X 0 * M0 K a b g)
          * MvPolynomial.C (((2 : K) * (a + 2 * b) ^(6:ℕ))⁻¹) := by
    rw [add_mul, hcc]
    first | refl_ring1 | ring
  exact key

/-- **`P·X 0 ∈ (D0, R0²)`.**  The determinant identity of `ASZQuadDetGen`,
`C(β²)·R0² - Lt·R0·D0 + At·D0² = P·(C cq · X 0)`, exhibits `P·C cq·X 0` as an element of
`(D0, R0²)`; and `C cq` is invertible in `K[X₀,X₁]` because in characteristic `5`
`cq = -a¹⁵ - a¹⁰b⁵ - 2a⁵b¹⁰ + 2b¹⁵ = -(a + 2b)¹⁵` and `a + 2b ≠ 0` (from `ha`, since
`(a+2b)² = a² - ab - b²`). -/
theorem PX0_mem_span_D0_R0sq_own (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) :
    Work.MotAS.ASZElim.P a b g * MvPolynomial.X 0 ∈
      Ideal.span ({Work.MotAS.ASZGC.D0 a b g, (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ)} :
        Set (MvPolynomial (Fin 2) K)) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hsq : (a + 2 * b) ^(2:ℕ) = a ^(2:ℕ) - a * b - b ^(2:ℕ) := by
    have h : (a + 2 * b) ^(2:ℕ) - (a ^(2:ℕ) - a * b - b ^(2:ℕ)) = 5 * (a * b + b ^(2:ℕ)) := by ring
    rw [h5, zero_mul, sub_eq_zero] at h
    exact h
  have h2b : a + 2 * b ≠ 0 := fun h0 => ha (by rw [← hsq, h0]; ring)
  have hA : (a + 2 * b) ^(5:ℕ) = a ^(5:ℕ) + 2 * b ^(5:ℕ) := by
    have h : (a + 2 * b) ^(5:ℕ) - (a ^(5:ℕ) + 2 * b ^(5:ℕ))
        = 5 * (2 * a ^(4:ℕ) * b + 8 * a ^(3:ℕ) * b ^(2:ℕ) + 16 * a ^(2:ℕ) * b ^(3:ℕ) + 16 * a * b ^(4:ℕ)
            + 6 * b ^(5:ℕ)) := by ring
    rw [h5, zero_mul, sub_eq_zero] at h
    exact h
  have hcq0 : (-a ^(15:ℕ) - a ^(10:ℕ) * b ^(5:ℕ) - 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ) : K) ≠ 0 := by
    have hB : (-a ^(15:ℕ) - a ^(10:ℕ) * b ^(5:ℕ) - 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ) : K)
        = -((a + 2 * b) ^(15:ℕ)) := by
      have h : (-a ^(15:ℕ) - a ^(10:ℕ) * b ^(5:ℕ) - 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ) : K)
            + (a ^(5:ℕ) + 2 * b ^(5:ℕ)) ^(3:ℕ)
          = 5 * (a ^(10:ℕ) * b ^(5:ℕ) + 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ)) := by ring
      rw [h5, zero_mul, add_eq_zero_iff_eq_neg] at h
      rw [h, ← hA]
      first | refl_ring1 | ring
    rw [hB]
    exact neg_ne_zero.mpr (pow_ne_zero 15 h2b)
  have hscaled : MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))
        * (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ)
      - Work.MotAS.aszQuLt a b g * (Work.MotAS.ASZGC.R0 a b g) * (Work.MotAS.ASZGC.D0 a b g)
      + Work.MotAS.aszQuAt a b g * (Work.MotAS.ASZGC.D0 a b g) ^(2:ℕ)
      = Work.MotAS.ASZElim.P a b g
        * (MvPolynomial.C (-a ^(15:ℕ) - a ^(10:ℕ) * b ^(5:ℕ) - 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ))
            * MvPolynomial.X 0) := by
    rw [R0_eq_ziasGraphR, D0_eq_ziasGraphD0]
    exact Work.MotAS.ASRulV2M.aszQuadDet_ident K a b g
  have hCcq : MvPolynomial.C ((-a ^(15:ℕ) - a ^(10:ℕ) * b ^(5:ℕ) - 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ))⁻¹)
      * MvPolynomial.C (-a ^(15:ℕ) - a ^(10:ℕ) * b ^(5:ℕ) - 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ))
      = (1 : MvPolynomial (Fin 2) K) := by
    rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hcq0, MvPolynomial.C_1]
  have h1 : Work.MotAS.ASZElim.P a b g
        * (MvPolynomial.C (-a ^(15:ℕ) - a ^(10:ℕ) * b ^(5:ℕ) - 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ))
            * MvPolynomial.X 0)
      ∈ Ideal.span ({Work.MotAS.ASZGC.D0 a b g, (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ)} :
          Set (MvPolynomial (Fin 2) K)) := by
    refine Ideal.mem_span_pair.mpr
      ⟨Work.MotAS.aszQuAt a b g * Work.MotAS.ASZGC.D0 a b g
          - Work.MotAS.aszQuLt a b g * Work.MotAS.ASZGC.R0 a b g,
        MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ)), ?_⟩
    rw [← hscaled]
    first | refl_ring1 | ring
  have hprod : MvPolynomial.C ((-a ^(15:ℕ) - a ^(10:ℕ) * b ^(5:ℕ) - 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ))⁻¹)
        * (Work.MotAS.ASZElim.P a b g
          * (MvPolynomial.C (-a ^(15:ℕ) - a ^(10:ℕ) * b ^(5:ℕ) - 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ))
              * MvPolynomial.X 0))
      = Work.MotAS.ASZElim.P a b g * MvPolynomial.X 0 := by
    linear_combination (norm := first | refl_ring1 | ring1) (Work.MotAS.ASZElim.P a b g * MvPolynomial.X 0) * hCcq
  rw [← hprod]
  exact Ideal.mul_mem_left _ _ h1

/-- **`P ∈ (D0, R0²)`.**  Combine `P·X 0 ∈ (D0, R0²)` with the invertibility of `X 0` modulo
`(D0)`. -/
theorem P_mem_span_D0_R0sq (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) :
    Work.MotAS.ASZElim.P a b g ∈
      Ideal.span ({Work.MotAS.ASZGC.D0 a b g, (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ)} :
        Set (MvPolynomial (Fin 2) K)) := by
  obtain ⟨Y, hY⟩ := X0_unit_mod_D0 K a b g ha
  obtain ⟨η, hη⟩ := Ideal.mem_span_singleton.mp hY
  obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp (PX0_mem_span_D0_R0sq_own K a b g ha)
  have hX : MvPolynomial.X 0 * Y = 1 + Work.MotAS.ASZGC.D0 a b g * η := by
    linear_combination (norm := first | refl_ring1 | ring1) hη
  refine Ideal.mem_span_pair.mpr
    ⟨Y * r - Work.MotAS.ASZElim.P a b g * η, Y * s, ?_⟩
  calc (Y * r - Work.MotAS.ASZElim.P a b g * η) * Work.MotAS.ASZGC.D0 a b g
        + (Y * s) * (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ)
      = Y * (r * Work.MotAS.ASZGC.D0 a b g + s * (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ))
          - Work.MotAS.ASZElim.P a b g * η * Work.MotAS.ASZGC.D0 a b g := by ring
    _ = Y * (Work.MotAS.ASZElim.P a b g * MvPolynomial.X 0)
          - Work.MotAS.ASZElim.P a b g * η * Work.MotAS.ASZGC.D0 a b g := by rw [hrs]
    _ = Work.MotAS.ASZElim.P a b g * (MvPolynomial.X 0 * Y)
          - Work.MotAS.ASZElim.P a b g * η * Work.MotAS.ASZGC.D0 a b g := by ring
    _ = Work.MotAS.ASZElim.P a b g := by rw [hX]; ring

/-- **Cancellation of `D0` against `R0`.**  From `P ∈ (D0, R0²)` and `IsRelPrime D0 P`:
`D0 ∣ R0·t` implies `D0 ∣ P·t` (because `P = e·D0 + f·R0²`), hence `D0 ∣ t`. -/
theorem R0_dvd_cancel (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) (hg : ¬ ∃ c : K, c ^(5:ℕ) - c = g) :
    ∀ t : MvPolynomial (Fin 2) K,
      Work.MotAS.ASZGC.D0 a b g ∣ Work.MotAS.ASZGC.R0 a b g * t →
        Work.MotAS.ASZGC.D0 a b g ∣ t := by
  intro t ht
  obtain ⟨q, hq⟩ := ht
  obtain ⟨e, f, hef⟩ := Ideal.mem_span_pair.mp (P_mem_span_D0_R0sq K a b g ha)
  have hrel : IsRelPrime (Work.MotAS.ASZGC.D0 a b g) (Work.MotAS.ASZElim.P a b g) :=
    ((Work.MotAS.ASZElimP_irreducible K a b g ha hg).isRelPrime_iff_not_dvd.mpr
      (Work.MotAS.ASZGC.not_dvd_D0 K a b g ha hg)).symm
  have hPt : Work.MotAS.ASZGC.D0 a b g ∣ Work.MotAS.ASZElim.P a b g * t := by
    refine ⟨e * t + f * (Work.MotAS.ASZGC.R0 a b g * q), ?_⟩
    have key : (e * Work.MotAS.ASZGC.D0 a b g
          + f * (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ)) * t
        = e * Work.MotAS.ASZGC.D0 a b g * t
          + f * Work.MotAS.ASZGC.R0 a b g * (Work.MotAS.ASZGC.R0 a b g * t) := by ring
    rw [← hef, key, hq]
    first | refl_ring1 | ring
  exact IsRelPrime.dvd_of_dvd_mul_left hrel hPt

theorem ann_eq_gen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) (hg : ¬ ∃ c : K, c ^(5:ℕ) - c = g) :
    ∀ s : MvPolynomial (Fin 2) K,
      (∃ u v : MvPolynomial (Fin 2) K,
        s * Work.MotAS.ASZGC.R0 a b g
          = u * Work.MotAS.ASZElim.P a b g + v * Work.MotAS.ASZGC.D0 a b g) →
      s ∈ Ideal.span {Work.MotAS.ASZElim.P a b g, Work.MotAS.ASZGC.D0 a b g,
        Work.MotAS.ASZGC.R0 a b g} := by
  intro s hs
  obtain ⟨u, v, huv⟩ := hs
  obtain ⟨e, f, hef⟩ := Ideal.mem_span_pair.mp (P_mem_span_D0_R0sq K a b g ha)
  have hdiv : Work.MotAS.ASZGC.D0 a b g
      ∣ s - u * f * Work.MotAS.ASZGC.R0 a b g := by
    apply R0_dvd_cancel K a b g ha hg
    refine ⟨u * e + v, ?_⟩
    have k1 : Work.MotAS.ASZGC.R0 a b g
          * (s - u * f * Work.MotAS.ASZGC.R0 a b g)
        = s * Work.MotAS.ASZGC.R0 a b g
          - u * f * (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ) := by ring
    rw [k1, huv, ← hef]
    first | refl_ring1 | ring
  obtain ⟨γ, hγ⟩ := hdiv
  have hsub : ({Work.MotAS.ASZGC.D0 a b g, Work.MotAS.ASZGC.R0 a b g} :
        Set (MvPolynomial (Fin 2) K))
      ⊆ ({Work.MotAS.ASZElim.P a b g, Work.MotAS.ASZGC.D0 a b g,
          Work.MotAS.ASZGC.R0 a b g} : Set (MvPolynomial (Fin 2) K)) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  refine Ideal.span_mono hsub ?_
  exact Ideal.mem_span_pair.mpr ⟨γ, u * f, by linear_combination -hγ⟩

end Work.MotC5N3.ASZPrimeness
