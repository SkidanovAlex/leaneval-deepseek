import Mathlib
import Submission.Work.MotC5N3.ASZSatCertAll
import Submission.Work.MotAS.ASRulV2M.sat_mem_gen
import Submission.Work.MotAS.ASRulV2M.reduce_quad
import Submission.Work.MotAS.ASRulV2M.ASZQuadDetGen
import Submission.Work.MotC5N3.ASZPrimeness.ann_eq_aux
import Submission.Work.MotC5N3.ASZPrimeness.ann_eq_gen
import Submission.Work.MotC5N3.ASZPrimeness.syz_gen
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotC5N3.D0_regular_AS` — `D₀` is a non-zero-divisor modulo the AS chart ideal

Target: for `K` a field of characteristic `5`, `a b g : K` with `a² - ab - b² ≠ 0` and
`g ∉ ℘(K) = {c⁵ - c}`, and `D₀ = ASZGC.D0 a b g` (the `X 0`-coefficient of the graph element of the
AS residual chart ideal `Z = ZIAS a b g`),

`(rename Fin.succ D₀) · y ∈ Z  ⟹  y ∈ Z`.

## Route

Write `P = ASZElim.P a b g`, `D = ASZGC.D0 a b g`, `R = ASZGC.R0 a b g`,
`l = C (β²)⁻¹ · aszQuLt a b g`, `A = C (β²)⁻¹ · aszQuAt a b g` (`β = aszQuBeta a b`),
so that the monic-in-`X 0` quadratic `e = X 0² + rename l · X 0 + rename A` and the graph element
`G = rename D · X 0 + rename R` both lie in `Z` (`aszQuad_mem`, `D0_graph_mem`).

1. **`P ∈ (D, R²)`** (`ASZ_D0_cert`).  `aszQuadDet_ident` gives the characteristic-`5` identity
   `β² R² - Lt · R · D + At · D² = P · (C cq · X 0)`, `cq = -a¹⁵ - a¹⁰b⁵ - 2a⁵b¹⁰ + 2b¹⁵`,
   hence `cq · P · X 0 ∈ (D, R²)`.  The scalar `cq` is *non-zero*: `cq = -((a - 3b)(a + 2b)²)⁵`
   and `(a + 2b)(a - 3b) = a² - ab - b² ≠ 0` (`ASZcq_ne_zero`), so `C cq` is a unit.  Moreover
   `X 0` is a unit modulo `(D)` (`ASZPrimeness.X0_unit_mod_D0`), which removes the factor `X 0`.
2. **The colon statement** `(D, P) : (R) ⊆ (D, P, R)` (`ASZ_syz_ann`) follows: from
   `P = eD + fR²` one gets `D ∣ R·t ⟹ D ∣ P·t ⟹ D ∣ t` (`P` irreducible and `¬ P ∣ D`).
3. **The syzygy statement** (`ASZ_syz_gen`), deduced from 2 in the abstract form
   `ASZPrimeness.syz_abstract` together with the determinant identity (`syz_det`) and the
   two-variable regularity of `D` modulo `(P)` (`syz_reg`).
4. **Assembly.**  Reduce `y` modulo the monic quadratic `e` (`reduce_quad`), apply the elimination
   `Z ∩ K[X₁,X₂] = (P)` (`aszElim_dvd_of_le_sat`, fed by the saturation certificate `ASZSatCert`)
   to the `X 0`-free element `D·α - β·R ∈ Z`, apply 3, and exhibit
   `u - (w + t·X 0)·G = rename f₁ + rename f₂ · X 0 - t · rename D · e ∈ Z`.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.MotC5N3

/-- The scalar `cq = -a¹⁵ - a¹⁰b⁵ - 2a⁵b¹⁰ + 2b¹⁵` of `aszQuadDet_ident` is non-zero under
`a² - ab - b² ≠ 0`: in characteristic `5` it equals `-((a - 3b)(a + 2b)²)⁵`, and
`(a + 2b)(a - 3b) = a² - ab - b²`. -/
lemma ASZcq_ne_zero (K : Type) [Field K] [CharP K 5] (a b : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) :
    (-a ^(15:ℕ) - a ^(10:ℕ) * b ^(5:ℕ) - 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ) : K) ≠ 0 := by
  intro h0
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hid : ((a - 3 * b) * (a + 2 * b) ^(2:ℕ)) ^(5:ℕ)
      = -(-a ^(15:ℕ) - a ^(10:ℕ) * b ^(5:ℕ) - 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ))
        + 5 * (b * (a ^(14:ℕ) - 6 * a ^(13:ℕ) * b - 42 * a ^(12:ℕ) * b ^(2:ℕ) + 33 * a ^(11:ℕ) * b ^(3:ℕ)
            + 664 * a ^(10:ℕ) * b ^(4:ℕ) + 744 * a ^(9:ℕ) * b ^(5:ℕ) - 4524 * a ^(8:ℕ) * b ^(6:ℕ)
            - 11808 * a ^(7:ℕ) * b ^(7:ℕ) + 7072 * a ^(6:ℕ) * b ^(8:ℕ) + 59494 * a ^(5:ℕ) * b ^(9:ℕ)
            + 57984 * a ^(4:ℕ) * b ^(10:ℕ) - 71424 * a ^(3:ℕ) * b ^(11:ℕ) - 200448 * a ^(2:ℕ) * b ^(12:ℕ)
            - 165888 * a * b ^(13:ℕ) - 49766 * b ^(14:ℕ))) := by
    first | refl_ring1 | ring
  have hA : ((a - 3 * b) * (a + 2 * b) ^(2:ℕ)) ^(5:ℕ) = 0 := by
    rw [hid, h0, neg_zero, zero_add, h5, zero_mul]
  have hfac : a ^(2:ℕ) - a * b - b ^(2:ℕ) = (a + 2 * b) * (a - 3 * b) := by
    have h : (a + 2 * b) * (a - 3 * b) = a ^(2:ℕ) - a * b - b ^(2:ℕ) - 5 * b ^(2:ℕ) := by ring
    rw [h, h5, zero_mul, sub_zero]
  apply ha
  have hA0 : (a - 3 * b) * (a + 2 * b) ^(2:ℕ) = 0 := eq_zero_of_pow_eq_zero hA
  rcases mul_eq_zero.mp hA0 with h1 | h1
  · rw [hfac, h1, mul_zero]
  · have h2 : a + 2 * b = 0 := eq_zero_of_pow_eq_zero h1
    rw [hfac, h2, zero_mul]

/-- **`P · X 0 ∈ (D, R²)`.**  Directly from `aszQuadDet_ident`, which exhibits
`cq · P · X 0 = β² R² - Lt · R · D + At · D²`, together with the non-vanishing of `cq`. -/
lemma ASZ_PX0_mem (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) :
    Work.MotAS.ASZElim.P a b g * MvPolynomial.X 0 ∈
      Ideal.span ({Work.MotAS.ASZGC.D0 a b g, (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ)} :
        Set (MvPolynomial (Fin 2) K)) := by
  set cq : K := -a ^(15:ℕ) - a ^(10:ℕ) * b ^(5:ℕ) - 2 * a ^(5:ℕ) * b ^(10:ℕ) + 2 * b ^(15:ℕ) with hcq_def
  have hcq : cq ≠ 0 := by rw [hcq_def]; exact ASZcq_ne_zero K a b ha
  have hinv : MvPolynomial.C cq * MvPolynomial.C (cq⁻¹) = (1 : MvPolynomial (Fin 2) K) := by
    rw [← map_mul, mul_inv_cancel₀ hcq, map_one]
  have hid := Work.MotAS.ASRulV2M.aszQuadDet_ident K a b g
  rw [← ASZPrimeness.D0_eq_ziasGraphD0 K a b g,
      ← ASZPrimeness.R0_eq_ziasGraphR K a b g] at hid
  have key : MvPolynomial.C (cq⁻¹)
      * (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ)) * (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ)
        - Work.MotAS.aszQuLt a b g * Work.MotAS.ASZGC.R0 a b g * Work.MotAS.ASZGC.D0 a b g
        + Work.MotAS.aszQuAt a b g * (Work.MotAS.ASZGC.D0 a b g) ^(2:ℕ))
      = Work.MotAS.ASZElim.P a b g * MvPolynomial.X 0 := by
    rw [hid]
    calc MvPolynomial.C (cq⁻¹)
          * (Work.MotAS.ASZElim.P a b g * (MvPolynomial.C cq * MvPolynomial.X 0))
        = (MvPolynomial.C (cq⁻¹) * MvPolynomial.C cq)
          * (Work.MotAS.ASZElim.P a b g * MvPolynomial.X 0) := by ring
      _ = Work.MotAS.ASZElim.P a b g * MvPolynomial.X 0 := by
            rw [mul_comm (MvPolynomial.C (cq⁻¹)) (MvPolynomial.C cq), hinv, one_mul]
  refine Ideal.mem_span_pair.mpr ⟨MvPolynomial.C (cq⁻¹)
        * (Work.MotAS.aszQuAt a b g * Work.MotAS.ASZGC.D0 a b g
          - Work.MotAS.aszQuLt a b g * Work.MotAS.ASZGC.R0 a b g),
      MvPolynomial.C (cq⁻¹)
        * MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ)), ?_⟩
  rw [← key]
  first | refl_ring1 | ring

/-- **`P ∈ (D, R²)`.**  `P · X 0 ∈ (D, R²)` from `ASZ_PX0_mem` and `X 0` is a unit modulo `(D)`:
if `X 0 · Y = 1 + D · η` then `P = P·(X 0·Y) - P·(D·η)`. -/
lemma ASZ_D0_cert (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) :
    ∃ e f : MvPolynomial (Fin 2) K,
      Work.MotAS.ASZElim.P a b g
        = e * Work.MotAS.ASZGC.D0 a b g + f * (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ) := by
  obtain ⟨Y, hY⟩ := ASZPrimeness.X0_unit_mod_D0 K a b g ha
  obtain ⟨η, hη⟩ := Ideal.mem_span_singleton.mp hY
  have hX : MvPolynomial.X 0 * Y = 1 + Work.MotAS.ASZGC.D0 a b g * η := by
    rw [← hη]; ring
  have hmem := ASZ_PX0_mem K a b g ha
  have h1 : Work.MotAS.ASZElim.P a b g * (MvPolynomial.X 0 * Y)
      ∈ Ideal.span ({Work.MotAS.ASZGC.D0 a b g, (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ)} :
          Set (MvPolynomial (Fin 2) K)) := by
    have h := Ideal.mul_mem_right Y _ hmem
    rwa [mul_assoc] at h
  have h2 : Work.MotAS.ASZElim.P a b g * (Work.MotAS.ASZGC.D0 a b g * η)
      ∈ Ideal.span ({Work.MotAS.ASZGC.D0 a b g, (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ)} :
          Set (MvPolynomial (Fin 2) K)) :=
    Ideal.mul_mem_left _ _ (Ideal.mul_mem_right η _ (Ideal.subset_span (by simp)))
  have hmem' : Work.MotAS.ASZElim.P a b g
      ∈ Ideal.span ({Work.MotAS.ASZGC.D0 a b g, (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ)} :
          Set (MvPolynomial (Fin 2) K)) := by
    have hP : Work.MotAS.ASZElim.P a b g
        = Work.MotAS.ASZElim.P a b g * (MvPolynomial.X 0 * Y)
          - Work.MotAS.ASZElim.P a b g * (Work.MotAS.ASZGC.D0 a b g * η) := by
      rw [hX]; ring
    rw [hP]
    exact Ideal.sub_mem _ h1 h2
  obtain ⟨e, f, hef⟩ := Ideal.mem_span_pair.mp hmem'
  exact ⟨e, f, hef.symm⟩

/-- **The colon statement** `(D, P) : (R) ⊆ (D, P, R)`.  From `P = e·D + f·R²` (`ASZ_D0_cert`)
one has `D ∣ R·t ⟹ D ∣ P·t ⟹ D ∣ t` because `P` is irreducible and `¬ P ∣ D`. -/
lemma ASZ_syz_ann (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) (hg : ¬ ∃ c : K, c ^(5:ℕ) - c = g) :
    ∀ v : MvPolynomial (Fin 2) K,
      Work.MotAS.ASZGC.R0 a b g * v
          ∈ Ideal.span {Work.MotAS.ASZGC.D0 a b g, Work.MotAS.ASZElim.P a b g} →
        v ∈ Ideal.span ({Work.MotAS.ASZGC.R0 a b g} : Set (MvPolynomial (Fin 2) K))
            ⊔ Ideal.span {Work.MotAS.ASZGC.D0 a b g, Work.MotAS.ASZElim.P a b g} := by
  intro v hv
  obtain ⟨e, f, hA⟩ := ASZ_D0_cert K a b g ha
  have hirr : Irreducible (Work.MotAS.ASZElim.P a b g) :=
    Work.MotAS.ASZElimP_irreducible K a b g ha hg
  have hndvd : ¬ Work.MotAS.ASZElim.P a b g ∣ Work.MotAS.ASZGC.D0 a b g :=
    Work.MotAS.ASZGC.not_dvd_D0 K a b g ha hg
  have hrel : IsRelPrime (Work.MotAS.ASZGC.D0 a b g) (Work.MotAS.ASZElim.P a b g) :=
    (hirr.isRelPrime_iff_not_dvd.mpr hndvd).symm
  have hcancel : ∀ t : MvPolynomial (Fin 2) K,
      Work.MotAS.ASZGC.D0 a b g ∣ Work.MotAS.ASZGC.R0 a b g * t →
        Work.MotAS.ASZGC.D0 a b g ∣ t := by
    intro t ht
    obtain ⟨q, hq⟩ := ht
    have hPt : Work.MotAS.ASZElim.P a b g * t
        = Work.MotAS.ASZGC.D0 a b g
          * (e * t + f * Work.MotAS.ASZGC.R0 a b g * q) := by
      rw [hA]
      linear_combination (norm := first | refl_ring1 | ring1) (f * Work.MotAS.ASZGC.R0 a b g) * hq
    exact hrel.dvd_of_dvd_mul_left ⟨_, hPt⟩
  obtain ⟨u, w, huw⟩ := Ideal.mem_span_pair.mp hv
  have hexp : Work.MotAS.ASZGC.R0 a b g * (v - w * f * Work.MotAS.ASZGC.R0 a b g)
      = Work.MotAS.ASZGC.R0 a b g * v - w * f * (Work.MotAS.ASZGC.R0 a b g) ^(2:ℕ) := by
    first | refl_ring1 | ring
  have hstep : Work.MotAS.ASZGC.D0 a b g ∣
      Work.MotAS.ASZGC.R0 a b g * (v - w * f * Work.MotAS.ASZGC.R0 a b g) := by
    rw [hexp, ← huw, hA]
    exact ⟨w * e + u, by ring⟩
  have hdiv : Work.MotAS.ASZGC.D0 a b g ∣
      v - w * f * Work.MotAS.ASZGC.R0 a b g := hcancel _ hstep
  obtain ⟨γ, hγ⟩ := hdiv
  refine Submodule.mem_sup.mpr
    ⟨w * f * Work.MotAS.ASZGC.R0 a b g, ?_, γ * Work.MotAS.ASZGC.D0 a b g, ?_, ?_⟩
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · have : w * f * Work.MotAS.ASZGC.R0 a b g + γ * Work.MotAS.ASZGC.D0 a b g = v := by
      linear_combination (norm := first | refl_ring1 | ring1) (-1 : MvPolynomial (Fin 2) K) * hγ
    exact this

/-- **The syzygy statement** for the AS plane model: `D·u - R·v ∈ (P)` forces the syzygy to be
the obvious combination of `(u, v)` with the two generators `(−R, D)` and `(D·A, R − l·D)` of
`{(c,d) : D·c ≡ R·d (mod P)}`, the second one being consistent by the determinant identity. -/
lemma ASZ_syz_gen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) (hg : ¬ ∃ c : K, c ^(5:ℕ) - c = g) :
    ∀ u v : MvPolynomial (Fin 2) K,
      Work.MotAS.ASZGC.D0 a b g * u - Work.MotAS.ASZGC.R0 a b g * v
        ∈ Ideal.span {Work.MotAS.ASZElim.P a b g} →
      ∃ w t : MvPolynomial (Fin 2) K,
        (u - Work.MotAS.ASZGC.R0 a b g * w
            + Work.MotAS.ASZGC.D0 a b g
              * (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
                  * Work.MotAS.aszQuAt a b g) * t
          ∈ Ideal.span {Work.MotAS.ASZElim.P a b g})
        ∧ (v - Work.MotAS.ASZGC.D0 a b g * w
            - (Work.MotAS.ASZGC.R0 a b g
                - (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
                    * Work.MotAS.aszQuLt a b g) * Work.MotAS.ASZGC.D0 a b g) * t
          ∈ Ideal.span {Work.MotAS.ASZElim.P a b g}) := by
  intro u v huv
  have h := ASZPrimeness.syz_abstract (Work.MotAS.ASZElim.P a b g) (Work.MotAS.ASZGC.D0 a b g)
    (Work.MotAS.ASZGC.R0 a b g)
    (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹ * Work.MotAS.aszQuLt a b g)
    (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹ * Work.MotAS.aszQuAt a b g)
    (ASZPrimeness.syz_det K a b g ha hg) (ASZPrimeness.syz_reg K a b g ha hg)
    (ASZ_syz_ann K a b g ha hg) u v huv
  simpa using h

/-- **The graph coefficient `D₀` of the AS residual chart is a non-zero-divisor.**

Let `Z = ZIAS a b g` be the (chart part of the) residual curve ideal of the characteristic-`5`
Crauder–Katz link.  If `(rename Fin.succ D₀) · y ∈ Z`, then `y ∈ Z`: reduce `y` modulo the monic
quadratic `e = X 0² + l·X 0 + A ∈ Z` (`reduce_quad`), apply the elimination `Z ∩ K[X₁,X₂] = (P)`
(`aszElim_dvd_of_le_sat`, fed by the `D₀`-saturation certificate `ASZSatCert`), use the syzygy
statement `ASZ_syz_gen` and exhibit the explicit decomposition
`u - (w + t·X 0)·G = rename f₁ + rename f₂ · X 0 - t · rename D₀ · e`. -/
theorem D0_regular_AS (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) (hg : ¬ ∃ c : K, c ^(5:ℕ) - c = g) :
    ∀ y : MvPolynomial (Fin 3) K,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
          : MvPolynomial (Fin 3) K) * y ∈ Work.MotAS.ZIAS a b g →
        y ∈ Work.MotAS.ZIAS a b g := by
  intro y hy
  -- The `D₀`-saturation certificate gives `ZIAS ≤ SatAS`.
  have hZS : Work.MotAS.ZIAS a b g ≤ Work.MotAS.ASRulV2M.SatAS K a b g := by
    intro F hF
    obtain ⟨N, hN⟩ := ASZSatCert K a b g F hF
    rw [Work.MotAS.ASRulV2M.SatAS]
    exact Ideal.subset_span ⟨N, hN⟩
  -- The three explicit elements of `ZIAS` used below.
  have hE : (MvPolynomial.X 0 : MvPolynomial (Fin 3) K) ^(2:ℕ)
      + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
          * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g))
        * MvPolynomial.X 0
      + MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
          * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g)
      ∈ Work.MotAS.ZIAS a b g := Work.MotAS.ASRulV2M.aszQuad_mem K a b g ha
  have hGm : (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
        * MvPolynomial.X 0
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)
      ∈ Work.MotAS.ZIAS a b g := Work.MotAS.ASRulV2M.D0_graph_mem K a b g
  have hPm : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g)
      ∈ Work.MotAS.ZIAS a b g := Work.MotAS.ASZElimMem K a b g ha hg
  -- Reduce `y` modulo the monic-in-`X 0` quadratic `e`.
  obtain ⟨α, β, hαβ⟩ := Work.MotAS.ASRulV2M.reduce_quad
    (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹ * Work.MotAS.aszQuLt a b g)
    (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹ * Work.MotAS.aszQuAt a b g) y
  have hαβ' : y - (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) α
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * MvPolynomial.X 0)
      ∈ Ideal.span (singleton (MvPolynomial.X 0 ^(2:ℕ)
          + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
              * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g))
            * MvPolynomial.X 0
          + MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
              * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g))
        : Set (MvPolynomial (Fin 3) K)) := by
    simpa only [map_mul, MvPolynomial.rename_C] using hαβ
  have hspan_le : Ideal.span (singleton (MvPolynomial.X 0 ^(2:ℕ)
          + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
              * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g))
            * MvPolynomial.X 0
          + MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
              * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g))
        : Set (MvPolynomial (Fin 3) K)) ≤ Work.MotAS.ZIAS a b g :=
    Ideal.span_le.mpr (by rintro x rfl; exact hE)
  set u : MvPolynomial (Fin 3) K :=
    MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) α
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * MvPolynomial.X 0 with hu
  have hyu : y - u ∈ Work.MotAS.ZIAS a b g := by
    rw [hu]; exact hspan_le hαβ'
  -- `D̃ · u ∈ Z`.
  have hDu : (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
        * u ∈ Work.MotAS.ZIAS a b g := by
    have hsub : (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
        * (y - u) ∈ Work.MotAS.ZIAS a b g := Ideal.mul_mem_left _ _ hyu
    have heq : (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
          * u
        = (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) * y
          - (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
              * (y - u) := by ring
    rw [heq]
    exact Ideal.sub_mem _ hy hsub
  -- Hence `rename (D₀·α - β·R₀) ∈ Z`, and by elimination `P ∣ D₀·α - β·R₀`.
  have hmem2 : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
        (Work.MotAS.ASZGC.D0 a b g * α - β * Work.MotAS.ASZGC.R0 a b g)
      ∈ Work.MotAS.ZIAS a b g := by
    have hid1 : (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
          * u
        = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
            (Work.MotAS.ASZGC.D0 a b g * α - β * Work.MotAS.ASZGC.R0 a b g)
          + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β
              * ((MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
                  * MvPolynomial.X 0
                + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)) := by
      rw [hu]
      simp only [map_add, map_sub, map_mul]
      first | refl_ring1 | ring
    have h := hDu
    rw [hid1] at h
    have hsym : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
          (Work.MotAS.ASZGC.D0 a b g * α - β * Work.MotAS.ASZGC.R0 a b g)
        = (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
              (Work.MotAS.ASZGC.D0 a b g * α - β * Work.MotAS.ASZGC.R0 a b g)
            + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β
                * ((MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
                    * MvPolynomial.X 0
                  + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)))
          - MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β
              * ((MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
                  * MvPolynomial.X 0
                + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)) := by
      first | refl_ring1 | ring
    rw [hsym]
    exact Ideal.sub_mem _ h (Ideal.mul_mem_left _ _ hGm)
  have hdiv : Work.MotAS.ASZElim.P a b g ∣
      (Work.MotAS.ASZGC.D0 a b g * α - β * Work.MotAS.ASZGC.R0 a b g) :=
    Work.MotAS.ASRulV2M.aszElim_dvd_of_le_sat K a b g ha hg hZS _ hmem2
  -- The syzygy statement.  (`ASZ_syz_gen` expects the second term as `R₀ * β`, not `β * R₀`.)
  have hmem_span : Work.MotAS.ASZGC.D0 a b g * α - Work.MotAS.ASZGC.R0 a b g * β
      ∈ Ideal.span {Work.MotAS.ASZElim.P a b g} := by
    rw [Ideal.mem_span_singleton]
    have hswap : Work.MotAS.ASZGC.D0 a b g * α - Work.MotAS.ASZGC.R0 a b g * β
        = Work.MotAS.ASZGC.D0 a b g * α - β * Work.MotAS.ASZGC.R0 a b g := by ring
    rw [hswap]
    exact hdiv
  obtain ⟨w, t, hw, ht⟩ := ASZ_syz_gen K a b g ha hg α β hmem_span
  set Gg : MvPolynomial (Fin 3) K :=
    (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
        * MvPolynomial.X 0
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g) with hGg
  set Wg : MvPolynomial (Fin 3) K := MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) w with hWg
  set Tg : MvPolynomial (Fin 3) K := MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) t with hTg
  have hfinal : u - (Wg + Tg * MvPolynomial.X 0) * Gg
      = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
          (α - Work.MotAS.ASZGC.R0 a b g * w
            + Work.MotAS.ASZGC.D0 a b g
              * (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
                  * Work.MotAS.aszQuAt a b g) * t)
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
            (β - Work.MotAS.ASZGC.D0 a b g * w
              - (Work.MotAS.ASZGC.R0 a b g
                  - (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
                      * Work.MotAS.aszQuLt a b g) * Work.MotAS.ASZGC.D0 a b g) * t)
          * MvPolynomial.X 0
        - Tg * ((MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
            * ((MvPolynomial.X 0 : MvPolynomial (Fin 3) K) ^(2:ℕ)
              + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
                  * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g))
                * MvPolynomial.X 0
              + MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
                  * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g))) := by
    rw [hu, hGg, hWg, hTg]
    simp only [map_add, map_sub, map_mul, MvPolynomial.rename_C]
    first | refl_ring1 | ring
  have h1 : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
        (α - Work.MotAS.ASZGC.R0 a b g * w
          + Work.MotAS.ASZGC.D0 a b g
            * (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
                * Work.MotAS.aszQuAt a b g) * t)
      ∈ Work.MotAS.ZIAS a b g := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hw
    rw [hc, map_mul]
    exact Ideal.mul_mem_right _ _ hPm
  have h2 : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
          (β - Work.MotAS.ASZGC.D0 a b g * w
            - (Work.MotAS.ASZGC.R0 a b g
                - (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
                    * Work.MotAS.aszQuLt a b g) * Work.MotAS.ASZGC.D0 a b g) * t)
        * MvPolynomial.X 0 ∈ Work.MotAS.ZIAS a b g := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ht
    rw [hc, map_mul]
    exact Ideal.mul_mem_right (MvPolynomial.X 0) (Work.MotAS.ZIAS a b g)
      (Ideal.mul_mem_right (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) c)
        (Work.MotAS.ZIAS a b g) hPm)
  have h3 : Tg * ((MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
        * ((MvPolynomial.X 0 : MvPolynomial (Fin 3) K) ^(2:ℕ)
          + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
              * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g))
            * MvPolynomial.X 0
          + MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^(2:ℕ))⁻¹
              * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g)))
      ∈ Work.MotAS.ZIAS a b g :=
    Ideal.mul_mem_left (Work.MotAS.ZIAS a b g) Tg
      (Ideal.mul_mem_left (Work.MotAS.ZIAS a b g)
        (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) hE)
  have hdiff : u - (Wg + Tg * MvPolynomial.X 0) * Gg ∈ Work.MotAS.ZIAS a b g := by
    rw [hfinal]
    exact Ideal.sub_mem _ (Ideal.add_mem _ h1 h2) h3
  have huZ : u ∈ Work.MotAS.ZIAS a b g := by
    have hsum : (Wg + Tg * MvPolynomial.X 0) * Gg ∈ Work.MotAS.ZIAS a b g :=
      Ideal.mul_mem_left (Work.MotAS.ZIAS a b g) (Wg + Tg * MvPolynomial.X 0)
        (by rw [hGg]; exact hGm)
    have : u = (u - (Wg + Tg * MvPolynomial.X 0) * Gg) + (Wg + Tg * MvPolynomial.X 0) * Gg := by
      first | refl_ring1 | ring
    rw [this]
    exact Ideal.add_mem _ hdiff hsum
  have : y = u + (y - u) := by ring
  rw [this]
  exact Ideal.add_mem _ huZ hyu

end Work.MotC5N3
