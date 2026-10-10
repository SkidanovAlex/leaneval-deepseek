import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.ASZGC.Defs
import Submission.Work.MotAS.aszDpQuad
import Submission.Work.MotAS.ASRulV2M.ASZQuadDetGen
import Submission.Work.MotAS.ASZElimP_irreducible
import Submission.Work.MotAS.ASZGC.not_dvd_D0
import Submission.Work.MotC5N3.ASZRadicalIsPrime
import Submission.Work.MotC5N3.ASZPrimeness.D0Struct
import Submission.Work.MotC5N3.ASZPrimeness.syz_cert
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotC5N3.ASZPrimeness.syz_gen` — the syzygy of the AS (graph) plane model

The target is the "syzygy" statement for the AS residual plane model: writing `P = ASZElim.P`,
`D0 = ASZGC.D0`, `R0 = ASZGC.R0` (two-variable polynomials in the chart coordinates `X₁`, `X₂`),
`ℓ = (β²)⁻¹·Lt`, `A = (β²)⁻¹·At`, one has

  `D0·u - R0·v ∈ (P)  ⟹  ∃ w t,  (u - R0·w + D0·A·t ∈ (P)) ∧ (v - D0·w - (R0 - ℓ·D0)·t ∈ (P))`.

## Structure of the proof

The statement is a module statement over the domain `S = K[X₁,X₂]`, and it is reduced here to the
*mirror* **colon statement**

  `(ann)`  `R0·v ∈ (D0, P)  ⟹  v ∈ (R0) + (D0, P)`

together with the **determinant identity**

  `(det)`  `R0² - ℓ·R0·D0 + A·D0² ∈ (P)`

and the **regularity of `D0` modulo `(P)`**

  `(reg)`  `D0·x ∈ (P) ⟹ x ∈ (P)`.

The argument (carried out in any domain `T` in `syz_abstract` below) is elementary: from
`D0·u - R0·v = P·e` one gets `R0·v ∈ (D0,P)`, so `v = R0·b + a·D0 + c·P` by `(ann)`; substituting
and using `(det)` `R0² = ℓ·R0·D0 - A·D0² + P·f` gives
`D0·(u - R0·a - ℓ·R0·b + A·D0·b) = P·(f·b + R0·c + e)`, so `(reg)` yields
`u - R0·(a+ℓb) + D0·A·b ∈ (P)`, while the second congruence
`v - D0·(a+ℓb) - (R0 - ℓ·D0)·b = c·P` is immediate. Hence `(ann)` alone (with `(det)`, `(reg)`)
implies the target; conversely the target specialises to `(ann)`.

This is exactly the statement requested as `Work.MotAS.ASRulV2M.ann_eq_gen` (there phrased in the
two-variable quotient for the ideal `(P, D0)`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.MotC5N3.ASZPrimeness

open MvPolynomial

section General

variable {T : Type*} [CommRing T] [IsDomain T]

/-- **The abstract syzygy step.** -/
theorem syz_abstract (P D R l A : T)
    (hdet : R ^ 2 - l * R * D + A * D ^ 2 ∈ Ideal.span ({P} : Set T))
    (hreg : ∀ x : T, D * x ∈ Ideal.span ({P} : Set T) → x ∈ Ideal.span ({P} : Set T))
    (hann : ∀ v : T,
      R * v ∈ Ideal.span ({D, P} : Set T) →
        v ∈ Ideal.span ({R} : Set T) ⊔ Ideal.span ({D, P} : Set T))
    (u v : T) (huv : D * u - R * v ∈ Ideal.span ({P} : Set T)) :
    ∃ w t : T, u - R * w + D * A * t ∈ Ideal.span ({P} : Set T)
      ∧ v - D * w - (R - l * D) * t ∈ Ideal.span ({P} : Set T) := by
  have hP : P ∈ Ideal.span ({P} : Set T) := Ideal.subset_span (Set.mem_singleton P)
  have hD : D ∈ Ideal.span ({D, P} : Set T) := Ideal.subset_span (Set.mem_insert D {P})
  have hP' : P ∈ ({D, P} : Set T) := Set.mem_insert_of_mem D (Set.mem_singleton P)
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp huv
  -- `R * v ∈ (D,P)`
  have hsub : ({P} : Set T) ⊆ ({D, P} : Set T) := Set.singleton_subset_iff.mpr hP'
  have hRv : R * v ∈ Ideal.span ({D, P} : Set T) := by
    have h : R * v = D * u - (D * u - R * v) := by ring
    rw [h]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hD) (Ideal.span_mono hsub huv)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hann v hRv)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hy
  obtain ⟨a, c, hac⟩ := Ideal.mem_span_pair.mp hz
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton.mp hdet
  have h1 : D * u = R * v + P * e := by rw [← he]; ring
  have hv : v = R * b + (a * D + c * P) := by rw [← hyz, hb, hac]
  have hR2 : R ^ 2 = l * R * D - A * D ^ 2 + P * f := by rw [← hf]; ring
  have hkey : D * (u - R * a - l * R * b + A * D * b) = P * (f * b + R * c + e) := by
    have hDexpand : D * (u - R * a - l * R * b + A * D * b)
        = D * u - D * R * a - l * D * R * b + A * D ^ 2 * b := by ring
    rw [hDexpand, h1, hv]
    ring_nf
    rw [hR2]
    first | refl_ring1 | ring
  have hmem : D * (u - R * a - l * R * b + A * D * b) ∈ Ideal.span ({P} : Set T) := by
    rw [hkey]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton P))
  have hres := hreg _ hmem
  have hv' : v - D * (a + l * b) - (R - l * D) * b = c * P := by
    rw [hv]; ring
  refine ⟨a + l * b, b, ?_, ?_⟩
  · have hsame : u - R * (a + l * b) + D * A * b
        = (u - R * a - l * R * b + A * D * b) := by ring
    rw [hsame]; exact hres
  · rw [hv']
    exact Ideal.mul_mem_left _ _ hP

/-- **The mirror colon statement** `(R):(D) ⊆ (R, D·A)` follows from `(ann)` (given `(det)`,
`(reg)`); i.e. the two colon statements are equivalent. -/
theorem colon_dual (P D R l A : T)
    (hdet : R ^ 2 - l * R * D + A * D ^ 2 ∈ Ideal.span ({P} : Set T))
    (hreg : ∀ x : T, D * x ∈ Ideal.span ({P} : Set T) → x ∈ Ideal.span ({P} : Set T))
    (hann : ∀ v : T,
      R * v ∈ Ideal.span ({D, P} : Set T) →
        v ∈ Ideal.span ({R} : Set T) ⊔ Ideal.span ({D, P} : Set T)) :
    ∀ u : T, D * u ∈ Ideal.span ({R} : Set T) →
      u ∈ Ideal.span ({R, D * A} : Set T) ⊔ Ideal.span ({P} : Set T) := by
  intro u hu
  have hD : D ∈ Ideal.span ({D, P} : Set T) := Ideal.subset_span (Set.mem_insert D {P})
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hu
  have hRe : R * e ∈ Ideal.span ({D, P} : Set T) := by
    have h : R * e = D * u := by rw [he]
    rw [h]
    exact Ideal.mul_mem_right _ _ hD
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hann e hRe)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hy
  obtain ⟨a, c, hac⟩ := Ideal.mem_span_pair.mp hz
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton.mp hdet
  have h1 : D * u = R * e := by rw [he]
  have he' : e = R * b + (a * D + c * P) := by rw [← hyz, hb, hac]
  have hR2 : R ^ 2 = l * R * D - A * D ^ 2 + P * f := by rw [← hf]; ring
  have hP : P ∈ Ideal.span ({P} : Set T) := Ideal.subset_span (Set.mem_singleton P)
  have hkey : D * (u - R * a - l * R * b + A * D * b) = P * (f * b + R * c) := by
    have hDexpand : D * (u - R * a - l * R * b + A * D * b)
        = D * u - D * R * a - l * D * R * b + A * D ^ 2 * b := by ring
    rw [hDexpand, h1, he']
    ring_nf
    rw [hR2]
    first | refl_ring1 | ring
  have hmem : D * (u - R * a - l * R * b + A * D * b) ∈ Ideal.span ({P} : Set T) := by
    rw [hkey]
    exact Ideal.mul_mem_right _ _ hP
  have hres := hreg _ hmem
  refine Submodule.mem_sup.mpr
    ⟨R * (a + l * b) - (D * A) * b, ?_, u - R * a - l * R * b + A * D * b, hres, ?_⟩
  · exact Ideal.mem_span_pair.mpr ⟨a + l * b, -b, by ring⟩
  · first | refl_ring1 | ring

end General

/-! ## The three concrete inputs -/

/-- **The determinant identity** of the AS plane model. -/
theorem syz_det (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    (Work.MotAS.ASZGC.R0 a b g) ^ 2
      - (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuLt a b g)
          * (Work.MotAS.ASZGC.R0 a b g) * (Work.MotAS.ASZGC.D0 a b g)
      + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuAt a b g)
          * (Work.MotAS.ASZGC.D0 a b g) ^ 2
    ∈ Ideal.span {Work.MotAS.ASZElim.P a b g} := by
  have h := Work.MotAS.ASRulV2M.ASZQuadDetGen K a b g ha hg
  rwa [Work.MotC5N3.ziasGraphD0_eq K a b g, Work.MotC5N3.ziasGraphR_eq K a b g] at h

/-- **`D0` is a non-zero-divisor modulo the eliminant `(P)`** in the two-variable ring. -/
theorem syz_reg (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    ∀ x : MvPolynomial (Fin 2) K,
      Work.MotAS.ASZGC.D0 a b g * x ∈ Ideal.span {Work.MotAS.ASZElim.P a b g} →
        x ∈ Ideal.span {Work.MotAS.ASZElim.P a b g} := by
  intro x hx
  have hirr : Irreducible (Work.MotAS.ASZElim.P a b g) :=
    Work.MotAS.ASZElimP_irreducible K a b g ha hg
  have hndvd : ¬ Work.MotAS.ASZElim.P a b g ∣ Work.MotAS.ASZGC.D0 a b g :=
    Work.MotAS.ASZGC.not_dvd_D0 K a b g ha hg
  have hrel : IsRelPrime (Work.MotAS.ASZElim.P a b g) (Work.MotAS.ASZGC.D0 a b g) :=
    hirr.isRelPrime_iff_not_dvd.mpr hndvd
  exact Ideal.mem_span_singleton.mpr
    (hrel.dvd_of_dvd_mul_left (Ideal.mem_span_singleton.mp hx))

/-- **The colon statement** `(R0) : (D0, P) = (R0, D0, P)` of the AS plane model.  This is the
route of `GUIDE_ann_eq_gen.md`: the certificate `P = e·D0 + f·R0²` of `syz_cert` together with the
relative primality of `D0` and `P` gives the cancellation `D0 ∣ R0·t ⟹ D0 ∣ t`, which yields the
colon statement. -/
theorem syz_ann (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    ∀ v : MvPolynomial (Fin 2) K,
      Work.MotAS.ASZGC.R0 a b g * v
          ∈ Ideal.span {Work.MotAS.ASZGC.D0 a b g, Work.MotAS.ASZElim.P a b g} →
        v ∈ Ideal.span ({Work.MotAS.ASZGC.R0 a b g} : Set (MvPolynomial (Fin 2) K))
            ⊔ Ideal.span {Work.MotAS.ASZGC.D0 a b g, Work.MotAS.ASZElim.P a b g} := by
  intro v hv
  obtain ⟨e, f, hA⟩ := syz_cert K a b g ha hg
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
      = Work.MotAS.ASZGC.R0 a b g * v - w * f * (Work.MotAS.ASZGC.R0 a b g) ^ 2 := by
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

/-- **The syzygy statement.** -/
theorem syz_gen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    ∀ u v : MvPolynomial (Fin 2) K,
      Work.MotAS.ASZGC.D0 a b g * u - Work.MotAS.ASZGC.R0 a b g * v
        ∈ Ideal.span {Work.MotAS.ASZElim.P a b g} →
      ∃ w t : MvPolynomial (Fin 2) K,
        (u - Work.MotAS.ASZGC.R0 a b g * w
            + Work.MotAS.ASZGC.D0 a b g
              * (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuAt a b g) * t
          ∈ Ideal.span {Work.MotAS.ASZElim.P a b g})
        ∧ (v - Work.MotAS.ASZGC.D0 a b g * w
            - (Work.MotAS.ASZGC.R0 a b g
                - (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
                    * Work.MotAS.aszQuLt a b g) * Work.MotAS.ASZGC.D0 a b g) * t
          ∈ Ideal.span {Work.MotAS.ASZElim.P a b g}) := by
  intro u v huv
  have h := syz_abstract (Work.MotAS.ASZElim.P a b g) (Work.MotAS.ASZGC.D0 a b g)
    (Work.MotAS.ASZGC.R0 a b g)
    (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuLt a b g)
    (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuAt a b g)
    (syz_det K a b g ha hg) (syz_reg K a b g ha hg) (syz_ann K a b g ha hg) u v huv
  simpa using h

end Work.MotC5N3.ASZPrimeness
