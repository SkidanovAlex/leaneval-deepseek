import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.boxConstCalibB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.pairSlotPeelB1`

Two-slot peel of the centred box integral: for a kernel `w` depending only on the two
distinct slots `i ≠ j` of an `N = m + 2` particle configuration, the box integral factors
as the cube volume to the power of the remaining coordinates times the double cube
integral.

The two ingredients beyond the corpus are

* `abox_peel2_ins2` — the junk-tolerant two-slot peel of the centred box (the `ins2`
  measure-preserving insertion of `Q0Value`), and
* `MeasureTheory.integral_prod_mul` / `MeasureTheory.integral_prod` — the product
  factorization of a two-variable integrand (the second, Fubini, needs the integrability
  hypothesis `hint`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option maxHeartbeats 1000000

/-- **Junk-tolerant two-slot peel of the centred box** (the `ins2` insertion form of
`abox_peel2`): for an *arbitrary* integrand `F` the box integral is the integral over the
two isolated slots and the rest, against the product of the restricted measures.  No
measurability or integrability of `F` is required. -/
theorem abox_peel2_ins2 {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (m + 2)) (j' : Fin (m + 1))
    (F : X (m + 2) → ℝ) :
    (∫ x in abox (m + 2) ℓ, F x)
      = ∫ q : (kcE3 × kcE3) × X m, F (ins2 i j' q.1.1 q.1.2 q.2)
          ∂((((volume : Measure kcE3).restrict (acube ℓ)).prod
              ((volume : Measure kcE3).restrict (acube ℓ))).prod
            ((volume : Measure (X m)).restrict (abox m ℓ))) := by
  have h1 : MeasurePreserving (fun q : (kcE3 × kcE3) × X m =>
      kcInsN (m + 1) i (q.1.1, kcInsN m j' (q.1.2, q.2)))
      ((((volume : Measure kcE3).restrict (acube ℓ)).prod
          ((volume : Measure kcE3).restrict (acube ℓ))).prod
        ((volume : Measure (X m)).restrict (abox m ℓ)))
      ((volume : Measure (X (m + 2))).restrict (abox (m + 2) ℓ)) :=
    ins2_flat_mp (p := m) hℓ i j'
  have h2 : MeasurableEmbedding (fun q : (kcE3 × kcE3) × X m =>
      kcInsN (m + 1) i (q.1.1, kcInsN m j' (q.1.2, q.2))) := by
    have hfun : (fun q : (kcE3 × kcE3) × X m =>
        kcInsN (m + 1) i (q.1.1, kcInsN m j' (q.1.2, q.2)))
        = (⇑(kcInsN (m + 1) i)) ∘ (Prod.map id (⇑(kcInsN m j')))
            ∘ ⇑(MeasurableEquiv.prodAssoc) := by
      funext q
      rcases q with ⟨⟨y, z⟩, r⟩
      rfl
    rw [hfun]
    exact ((MeasurableEquiv.measurableEmbedding (kcInsN (m + 1) i)).comp
      ((MeasurableEmbedding.prodMap MeasurableEmbedding.id
          (MeasurableEquiv.measurableEmbedding (kcInsN m j'))).comp
        (MeasurableEquiv.measurableEmbedding MeasurableEquiv.prodAssoc)))
  exact (h1.integral_comp h2 F).symm

/-- **Two-slot peel of the centred box.**  For distinct slots `i j` of the `(m+2)`-particle
centred box and a kernel `w` integrable on `acube ℓ ×ˢ acube ℓ`, the box integral of
`x ↦ w (x i) (x j)` equals `(ℓ³)^m` times the double integral over the centred cube. -/
theorem abox_pair_peel {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (m + 2)) (hij : i ≠ j)
    {w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      w p.1 p.2) (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    ∫ x in Submission.BoseGases.abox (m + 2) ℓ, w (x i) (x j)
      = (ℓ ^ 3) ^ m * ∫ y in Submission.BoseGases.acube ℓ,
          ∫ z in Submission.BoseGases.acube ℓ, w y z := by
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
  let μc : Measure (EuclideanSpace ℝ (Fin 3)) :=
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)
  let νc : Measure (X m) := (volume : Measure (X m)).restrict (abox m ℓ)
  have hpeel := abox_peel2_ins2 (m := m) hℓ i j'
    (fun x : X (m + 2) => w (x i) (x j))
  have hp : ∀ q : (kcE3 × kcE3) × X m,
      w ((ins2 i j' q.1.1 q.1.2 q.2) i) ((ins2 i j' q.1.1 q.1.2 q.2) j) = w q.1.1 q.1.2 := by
    intro q
    rw [ins2_apply_i, ← hj', ins2_apply_succ]
  have h1 : (∫ q : (kcE3 × kcE3) × X m,
        w ((ins2 i j' q.1.1 q.1.2 q.2) i) ((ins2 i j' q.1.1 q.1.2 q.2) j)
          ∂((μc.prod μc).prod νc))
      = ∫ q : (kcE3 × kcE3) × X m, w q.1.1 q.1.2 ∂((μc.prod μc).prod νc) :=
    integral_congr_ae (Filter.Eventually.of_forall hp)
  have h2 : (∫ q : (kcE3 × kcE3) × X m, w q.1.1 q.1.2 ∂((μc.prod μc).prod νc))
      = (∫ p : kcE3 × kcE3, w p.1 p.2 ∂(μc.prod μc)) * (∫ r : X m, (1 : ℝ) ∂νc) := by
    have hrw : (fun q : (kcE3 × kcE3) × X m => w q.1.1 q.1.2)
        = fun q => (fun p : kcE3 × kcE3 => w p.1 p.2) q.1 * (fun _ : X m => (1 : ℝ)) q.2 := by
      funext q
      simp
    rw [hrw]
    exact MeasureTheory.integral_prod_mul (fun p : kcE3 × kcE3 => w p.1 p.2)
      (fun _ : X m => (1 : ℝ))
  have h3 : (∫ r : X m, (1 : ℝ) ∂νc) = (ℓ ^ 3) ^ m := by
    rw [MeasureTheory.integral_const]
    simp only [smul_eq_mul, mul_one]
    rw [MeasureTheory.measureReal_def]
    change (((volume : Measure (X m)).restrict (abox m ℓ)) Set.univ).toReal = (ℓ ^ 3) ^ m
    rw [Measure.restrict_apply_univ, abox_volume m ℓ hℓ.le,
      ENNReal.toReal_ofReal (pow_nonneg (pow_nonneg hℓ.le 3) m)]
  have hmeas : μc.prod μc
      = (volume : Measure (kcE3 × kcE3)).restrict (acube ℓ ×ˢ acube ℓ) := by
    change ((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure kcE3).restrict (acube ℓ)) = _
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod kcE3 kcE3]
  have h4 : (∫ p : kcE3 × kcE3, w p.1 p.2 ∂(μc.prod μc))
      = ∫ y in acube ℓ, ∫ z in acube ℓ, w y z := by
    have hInt : Integrable (fun p : kcE3 × kcE3 => w p.1 p.2) (μc.prod μc) := by
      rw [hmeas]
      exact hint
    have hF := MeasureTheory.integral_prod (μ := μc) (ν := μc)
      (f := fun p : kcE3 × kcE3 => w p.1 p.2) hInt
    simpa only [μc] using hF
  calc ∫ x in abox (m + 2) ℓ, w (x i) (x j)
      = ∫ q : (kcE3 × kcE3) × X m,
          w ((ins2 i j' q.1.1 q.1.2 q.2) i) ((ins2 i j' q.1.1 q.1.2 q.2) j)
            ∂((μc.prod μc).prod νc) := hpeel
    _ = ∫ q : (kcE3 × kcE3) × X m, w q.1.1 q.1.2 ∂((μc.prod μc).prod νc) := h1
    _ = (∫ p : kcE3 × kcE3, w p.1 p.2 ∂(μc.prod μc)) * (∫ r : X m, (1 : ℝ) ∂νc) := h2
    _ = (∫ y in acube ℓ, ∫ z in acube ℓ, w y z) * (ℓ ^ 3) ^ m := by rw [h3, h4]
    _ = (ℓ ^ 3) ^ m * ∫ y in acube ℓ, ∫ z in acube ℓ, w y z := by ring

theorem pairSlotPeelB1 {N : ℕ} (hN : 2 ≤ N) {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin N) (hij : i ≠ j)
    {w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      w p.1 p.2) (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    ∫ x in Submission.BoseGases.abox N ℓ, w (x i) (x j)
      = (ℓ ^ 3) ^ (N - 2) * ∫ x in Submission.BoseGases.abox 2 ℓ, w (x 0) (x 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  rw [abox_pair_peel (m := m) hℓ i j hij hint]
  have h2 : (∫ x in Submission.BoseGases.abox 2 ℓ, w (x 0) (x 1))
      = (ℓ ^ 3) ^ 0 * ∫ y in Submission.BoseGases.acube ℓ,
          ∫ z in Submission.BoseGases.acube ℓ, w y z :=
    abox_pair_peel (m := 0) hℓ (0 : Fin 2) (1 : Fin 2) (by decide) hint
  rw [h2]
  ring

end Work.BoseFixB1S
