import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB2.DvApriori.box_meanFree_mul_const_eq_zero
import Submission.Work.BoseFixB3.CS.Pieces.acube_setIntegral_iter_swap
import Submission.Work.BoseFixB3.CS.Pieces.pair_coord_integrable
import Submission.Work.BoseFixB3.CS.Pieces.peel_weighted
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.pp_sq_factor`

The two-slot factorisation of the squared condensate projection `PᵢPⱼΦ`: for `i ≠ j` and a
kernel `g` integrable for the product Lebesgue measure on `ℝ³ × ℝ³`,

  `∫_{abox n ℓ} (PᵢPⱼΦ)² · g(xᵢ,xⱼ) = (ℓ³)⁻¹(ℓ³)⁻¹ · (∫_{acube ℓ}∫_{acube ℓ} g) · ∫_{abox n ℓ} (PᵢPⱼΦ)²`.

The weight `(PᵢPⱼΦ)²` is invariant under changes of the slots `i` and `j`
(`aP_pair_const_in_i`, `aP_pair_const_in_j`), so the two slots can be peeled off one after the
other (`abox_peel_mp`, the measure-preserving insertion `kcInsN`), leaving the cube average of
`g` times the box integral of the weight.  The kernel is only used through its product
integrability (`hg`), which transfers to the box along the quasi-measure-preserving pair
evaluation `x ↦ (xᵢ,xⱼ)`.
-/

open MeasureTheory
open scoped Real Topology

namespace Work.BoseFixB3.CS.Pieces

set_option maxHeartbeats 1000000

noncomputable section

theorem pp_sq_factor {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) {i j : Fin n} (hij : i ≠ j)
    (g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hg : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      g z.1 z.2)) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2 * g (x i) (x j))
      = (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ *
          (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ, g a b) *
          (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2) := by
  by_cases hn2 : 2 ≤ n
  · obtain ⟨q, hq⟩ : ∃ q, n = q + 2 := ⟨n - 2, by omega⟩
    subst n
    -- the two slots `i` and `j = i.succAbove k`
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (x := j) (y := i) (Ne.symm hij)
    -- abbreviations
    let F : Submission.BoseGases.X (q + 2) → ℝ :=
      fun x => Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x
    let K : Submission.BoseGases.X (q + 2) → ℝ := fun x => (F x) ^ 2
    let K0 : Submission.BoseGases.X (q + 1) → ℝ :=
      fun r => K (Submission.BoseGases.kcInsN (q + 1) i (0, r))
    let K1 : Submission.BoseGases.X q → ℝ :=
      fun r => K0 (Submission.BoseGases.kcInsN q k (0, r))
    let Ghat : EuclideanSpace ℝ (Fin 3) → ℝ :=
      fun z => ∫ y in Submission.BoseGases.acube ℓ, g y z
    let nur : Measure (EuclideanSpace ℝ (Fin 3)) :=
      (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)
    let mu : Measure (Submission.BoseGases.X (q + 1)) :=
      (volume : Measure (Submission.BoseGases.X (q + 1))).restrict
        (Submission.BoseGases.abox (q + 1) ℓ)
    let mu2 : Measure (Submission.BoseGases.X q) :=
      (volume : Measure (Submission.BoseGases.X q)).restrict (Submission.BoseGases.abox q ℓ)
    -- continuity and invariance of the weight
    have hFc : Continuous F :=
      Submission.BoseGases.aP_continuous hℓ i (Submission.BoseGases.aP_continuous hℓ j hΦc)
    have hKc : Continuous K := by
      change Continuous fun x => (F x) ^ 2
      exact hFc.pow 2
    have hKi : ∀ (x : Submission.BoseGases.X (q + 2)) (z : EuclideanSpace ℝ (Fin 3)),
        K (Function.update x i z) = K x := by
      intro x z
      have h := Submission.BoseGases.aP_pair_const_in_i (ℓ := ℓ) hℓ hij hΦc x z
      change (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ)
            (Function.update x i z)) ^ 2
          = (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2
      rw [h]
    have hKj : ∀ (x : Submission.BoseGases.X (q + 2)) (z : EuclideanSpace ℝ (Fin 3)),
        K (Function.update x j z) = K x := by
      intro x z
      have h := Submission.BoseGases.aP_pair_const_in_j (ℓ := ℓ) hℓ hij hΦc x z
      change (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ)
            (Function.update x j z)) ^ 2
          = (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2
      rw [h]
    have hK0k : ∀ (r : Submission.BoseGases.X (q + 1)) (z : EuclideanSpace ℝ (Fin 3)),
        K0 (Function.update r k z) = K0 r := by
      intro r z
      change K (Submission.BoseGases.kcInsN (q + 1) i (0, Function.update r k z))
        = K (Submission.BoseGases.kcInsN (q + 1) i (0, r))
      rw [← Work.BoseFixB2.DvApriori.update_kcInsN_succAbove (m := q + 1) i k 0 z r, hk]
      exact hKj _ z
    have hKins : ∀ (y : EuclideanSpace ℝ (Fin 3)) (r : Submission.BoseGases.X (q + 1)),
        K (Submission.BoseGases.kcInsN (q + 1) i (y, r)) = K0 r := by
      intro y r
      change K (Submission.BoseGases.kcInsN (q + 1) i (y, r))
        = K (Submission.BoseGases.kcInsN (q + 1) i (0, r))
      rw [Submission.BoseGases.kcInsN_update_zero i y r]
      exact hKi _ y
    have hK0ins : ∀ (z : EuclideanSpace ℝ (Fin 3)) (r : Submission.BoseGases.X q),
        K0 (Submission.BoseGases.kcInsN q k (z, r)) = K1 r := by
      intro z r
      rw [Submission.BoseGases.kcInsN_update_zero k z r]
      exact hK0k _ z
    -- pointwise slot values of an insertion
    have hpt1 : ∀ (y : EuclideanSpace ℝ (Fin 3)) (r : Submission.BoseGases.X (q + 1)),
        (fun x : Submission.BoseGases.X (q + 2) => g (x i) (x j))
            (Submission.BoseGases.kcInsN (q + 1) i (y, r)) = g y (r k) := by
      intro y r
      show g ((Submission.BoseGases.kcInsN (q + 1) i (y, r)) i)
        ((Submission.BoseGases.kcInsN (q + 1) i (y, r)) j) = g y (r k)
      rw [Submission.BoseGases.kc_insN_apply_same, ← hk,
        Submission.BoseGases.kc_insN_apply_succ]
    have hpt1' : ∀ (y : EuclideanSpace ℝ (Fin 3)) (r : Submission.BoseGases.X (q + 1)),
        g ((Submission.BoseGases.kcInsN (q + 1) i (y, r)) i)
            ((Submission.BoseGases.kcInsN (q + 1) i (y, r)) j) = g y (r k) := by
      intro y r
      rw [Submission.BoseGases.kc_insN_apply_same, ← hk,
        Submission.BoseGases.kc_insN_apply_succ]
    -- the peel machinery at the two slots
    have hmp1 : MeasurePreserving (⇑(Submission.BoseGases.kcInsN (q + 1) i)) (nur.prod mu)
        ((volume : Measure (Submission.BoseGases.X (q + 2))).restrict
          (Submission.BoseGases.abox (q + 2) ℓ)) := by
      have h := MeasurePreserving.symm
        (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q + 2) =>
          EuclideanSpace ℝ (Fin 3)) i)
        (Submission.BoseGases.abox_peel_mp (n := q + 1) ℓ i)
      simpa [nur, mu, Submission.BoseGases.kcInsN] using h
    have hmp2 : MeasurePreserving (⇑(Submission.BoseGases.kcInsN q k)) (nur.prod mu2) mu := by
      have h := MeasurePreserving.symm
        (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q + 1) =>
          EuclideanSpace ℝ (Fin 3)) k)
        (Submission.BoseGases.abox_peel_mp (n := q) ℓ k)
      simpa [nur, mu2, mu, Submission.BoseGases.kcInsN] using h
    -- measurability of the kernel along the pair evaluation
    have hPairAe : AEStronglyMeasurable (fun x : Submission.BoseGases.X (q + 2) => g (x i) (x j))
        ((volume : Measure (Submission.BoseGases.X (q + 2))).restrict
          (Submission.BoseGases.abox (q + 2) ℓ)) := by
      have hqmp : Measure.QuasiMeasurePreserving
          (fun x : Submission.BoseGases.X (q + 2) => (x i, x j))
          (volume : Measure (Submission.BoseGases.X (q + 2)))
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            (volume : Measure (EuclideanSpace ℝ (Fin 3)))) := by
        have h := Work.BoseFixB2.Pot.quasiMeasurePreserving_pair_eval_aux
          (α := EuclideanSpace ℝ (Fin 3))
          (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) (n := q + 2) hij
        rwa [← MeasureTheory.volume_pi] at h
      exact (hg.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp).mono_measure
        Measure.restrict_le_self
    -- integrability on the box
    have hKint : IntegrableOn K (Submission.BoseGases.abox (q + 2) ℓ) volume :=
      hKc.continuousOn.integrableOn_compact (Submission.BoseGases.abox_compact (q + 2) hℓ)
    have hPairint : IntegrableOn (fun x : Submission.BoseGases.X (q + 2) => g (x i) (x j))
        (Submission.BoseGases.abox (q + 2) ℓ) volume :=
      pair_coord_integrable (ℓ := ℓ) hℓ hij hg
    obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact (q + 2) hℓ).exists_bound_of_continuousOn
      hKc.continuousOn
    have hKae : AEStronglyMeasurable K
        ((volume : Measure (Submission.BoseGases.X (q + 2))).restrict
          (Submission.BoseGases.abox (q + 2) ℓ)) :=
      hKc.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    have hKbdd : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X (q + 2))).restrict
        (Submission.BoseGases.abox (q + 2) ℓ)), ‖K x‖ ≤ C := by
      rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (q + 2) ℓ)]
      exact ae_of_all volume (fun x hx => hC x hx)
    have hKGint : IntegrableOn (fun x : Submission.BoseGases.X (q + 2) => K x * g (x i) (x j))
        (Submission.BoseGases.abox (q + 2) ℓ) volume :=
      (hPairint.mul_bdd hKae hKbdd).congr (ae_of_all _ (fun x => mul_comm _ _))
    -- the peeled form of the left-hand side
    have hInt1 : MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X (q + 1) =>
          K (Submission.BoseGases.kcInsN (q + 1) i p)
            * g ((Submission.BoseGases.kcInsN (q + 1) i p) i)
                ((Submission.BoseGases.kcInsN (q + 1) i p) j)) (nur.prod mu) := by
      have hiff := hmp1.integrable_comp (g := fun x : Submission.BoseGases.X (q + 2) =>
        K x * g (x i) (x j)) (hKae.mul hPairAe)
      exact hiff.mpr hKGint
    -- peel the slot `i`: the weight `K` drops to its zero-slot value `K0`
    have h1' : (∫ x in Submission.BoseGases.abox (q + 2) ℓ, K x * g (x i) (x j))
        = ∫ r : Submission.BoseGases.X (q + 1), K0 r * Ghat (r k) ∂mu := by
      have h := peel_weighted (hℓ := hℓ) (i := i) (K := K)
        (Ψ := fun x : Submission.BoseGases.X (q + 2) => g (x i) (x j)) hKi hInt1
      have hkey : ∀ r : Submission.BoseGases.X (q + 1),
          K (Submission.BoseGases.kcInsN (q + 1) i (0, r))
              * (∫ y in Submission.BoseGases.acube ℓ,
                  (fun x : Submission.BoseGases.X (q + 2) => g (x i) (x j))
                    (Submission.BoseGases.kcInsN (q + 1) i (y, r)))
            = K0 r * Ghat (r k) := by
        intro r
        rw [show (∫ y in Submission.BoseGases.acube ℓ,
              (fun x : Submission.BoseGases.X (q + 2) => g (x i) (x j))
                (Submission.BoseGases.kcInsN (q + 1) i (y, r)))
            = ∫ y in Submission.BoseGases.acube ℓ, g y (r k) from
              integral_congr_ae (ae_of_all _ (fun y => hpt1 y r))]
      rw [show (∫ x in Submission.BoseGases.abox (q + 2) ℓ, K x * g (x i) (x j))
          = ∫ x in Submission.BoseGases.abox ((q + 1) + 1) ℓ,
              K x * (fun x : Submission.BoseGases.X (q + 2) => g (x i) (x j)) x from rfl, h]
      exact integral_congr_ae (ae_of_all _ hkey)
    -- peel the slot `k`: the weight `K0` drops to `K1`
    have hInt2' : MeasureTheory.Integrable
        (fun r : Submission.BoseGases.X (q + 1) => K0 r * Ghat (r k)) mu := by
      refine hInt1.integral_prod_right.congr (ae_of_all _ (fun r => ?_))
      show (∫ y : EuclideanSpace ℝ (Fin 3),
            K (Submission.BoseGases.kcInsN (q + 1) i (y, r))
              * g ((Submission.BoseGases.kcInsN (q + 1) i (y, r)) i)
                  ((Submission.BoseGases.kcInsN (q + 1) i (y, r)) j) ∂nur)
          = K0 r * Ghat (r k)
      rw [show (∫ y : EuclideanSpace ℝ (Fin 3),
            K (Submission.BoseGases.kcInsN (q + 1) i (y, r))
              * g ((Submission.BoseGases.kcInsN (q + 1) i (y, r)) i)
                  ((Submission.BoseGases.kcInsN (q + 1) i (y, r)) j) ∂nur)
          = ∫ y : EuclideanSpace ℝ (Fin 3), K0 r * g y (r k) ∂nur from
            integral_congr_ae (ae_of_all _ (fun y => by
              show K (Submission.BoseGases.kcInsN (q + 1) i (y, r))
                  * g ((Submission.BoseGases.kcInsN (q + 1) i (y, r)) i)
                      ((Submission.BoseGases.kcInsN (q + 1) i (y, r)) j)
                = K0 r * g y (r k)
              rw [hKins y r, hpt1' y r]))]
      rw [MeasureTheory.integral_const_mul]
    have hInt2 : MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X q =>
          K0 (Submission.BoseGases.kcInsN q k p)
            * Ghat ((Submission.BoseGases.kcInsN q k p) k)) (nur.prod mu2) := by
      have hiff := hmp2.integrable_comp (g := fun r : Submission.BoseGases.X (q + 1) =>
        K0 r * Ghat (r k)) hInt2'.aestronglyMeasurable
      exact hiff.mpr hInt2'
    have h2' : (∫ r : Submission.BoseGases.X (q + 1), K0 r * Ghat (r k) ∂mu)
        = (∫ z in Submission.BoseGases.acube ℓ, Ghat z)
            * (∫ r : Submission.BoseGases.X q, K1 r ∂mu2) := by
      have h := peel_weighted (hℓ := hℓ) (i := k) (K := K0)
        (Ψ := fun r : Submission.BoseGases.X (q + 1) => Ghat (r k)) hK0k hInt2
      have hkey : ∀ r : Submission.BoseGases.X q,
          K0 (Submission.BoseGases.kcInsN q k (0, r))
              * (∫ y in Submission.BoseGases.acube ℓ,
                  (fun r : Submission.BoseGases.X (q + 1) => Ghat (r k))
                    (Submission.BoseGases.kcInsN q k (y, r)))
            = K1 r * (∫ y in Submission.BoseGases.acube ℓ, Ghat y) := by
        intro r
        rw [show (∫ y in Submission.BoseGases.acube ℓ,
              (fun r : Submission.BoseGases.X (q + 1) => Ghat (r k))
                (Submission.BoseGases.kcInsN q k (y, r)))
            = ∫ y in Submission.BoseGases.acube ℓ, Ghat y from
              integral_congr_ae (ae_of_all _ (fun y => by
                show Ghat ((Submission.BoseGases.kcInsN q k (y, r)) k) = Ghat y
                rw [Submission.BoseGases.kc_insN_apply_same]))]
      rw [show (∫ r : Submission.BoseGases.X (q + 1), K0 r * Ghat (r k) ∂mu)
          = ∫ x in Submission.BoseGases.abox (q + 1) ℓ,
              K0 x * (fun r : Submission.BoseGases.X (q + 1) => Ghat (r k)) x from rfl, h]
      rw [show (∫ r : Submission.BoseGases.X q,
            K0 (Submission.BoseGases.kcInsN q k (0, r))
              * (∫ y in Submission.BoseGases.acube ℓ,
                  (fun r : Submission.BoseGases.X (q + 1) => Ghat (r k))
                    (Submission.BoseGases.kcInsN q k (y, r))) ∂mu2)
          = ∫ r : Submission.BoseGases.X q,
              K1 r * (∫ y in Submission.BoseGases.acube ℓ, Ghat y) ∂mu2 from
            integral_congr_ae (ae_of_all _ hkey)]
      rw [MeasureTheory.integral_mul_const]
      ring
    have hLHSval : (∫ x in Submission.BoseGases.abox (q + 2) ℓ, K x * g (x i) (x j))
        = (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ, g a b)
            * (∫ r : Submission.BoseGases.X q, K1 r ∂mu2) := by
      rw [h1', h2']
      rw [show (∫ z in Submission.BoseGases.acube ℓ, Ghat z)
            * (∫ r : Submission.BoseGases.X q, K1 r ∂mu2)
          = (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ, g a b)
              * (∫ r : Submission.BoseGases.X q, K1 r ∂mu2) from by
        congr 1
        show (∫ z in Submission.BoseGases.acube ℓ, ∫ y in Submission.BoseGases.acube ℓ, g y z)
          = ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ, g a b
        exact (Work.BoseFixB3.CS.Pieces.acube_setIntegral_iter_swap ℓ g hg).symm]
    -- the peeled form of the weight integral
    have hInt3 : MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X (q + 1) =>
          (1 : ℝ) * K (Submission.BoseGases.kcInsN (q + 1) i p)) (nur.prod mu) := by
      have h1K : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (q + 2) =>
          (1 : ℝ) * K x) (Submission.BoseGases.abox (q + 2) ℓ) volume :=
        hKint.congr (ae_of_all _ (fun x => (one_mul (K x)).symm))
      have hiff := hmp1.integrable_comp (g := fun x : Submission.BoseGases.X (q + 2) =>
        (1 : ℝ) * K x) (hKae.const_mul 1)
      exact hiff.mpr h1K
    have hInt3' : MeasureTheory.Integrable
        (fun r : Submission.BoseGases.X (q + 1) => K0 r * ℓ ^ 3) mu := by
      refine hInt3.integral_prod_right.congr (ae_of_all _ (fun r => ?_))
      show (∫ y : EuclideanSpace ℝ (Fin 3),
            (1 : ℝ) * K (Submission.BoseGases.kcInsN (q + 1) i (y, r)) ∂nur)
          = K0 r * ℓ ^ 3
      rw [show (∫ y : EuclideanSpace ℝ (Fin 3),
            (1 : ℝ) * K (Submission.BoseGases.kcInsN (q + 1) i (y, r)) ∂nur)
          = ∫ y : EuclideanSpace ℝ (Fin 3), (1 : ℝ) * K0 r ∂nur from
            integral_congr_ae (ae_of_all _ (fun y => by
              show (1 : ℝ) * K (Submission.BoseGases.kcInsN (q + 1) i (y, r))
                = (1 : ℝ) * K0 r
              rw [hKins y r]))]
      rw [MeasureTheory.integral_const_mul, one_mul]
      show (∫ y : EuclideanSpace ℝ (Fin 3), K0 r ∂nur) = K0 r * ℓ ^ 3
      rw [show (∫ y : EuclideanSpace ℝ (Fin 3), K0 r ∂nur)
          = ∫ y in Submission.BoseGases.acube ℓ, K0 r from rfl,
        Submission.BoseGases.integral_const_acube ℓ hℓ]
    have hK0int : MeasureTheory.Integrable (fun r : Submission.BoseGases.X (q + 1) => K0 r) mu :=
      (integrable_mul_const_iff (c := (ℓ : ℝ) ^ 3)
        (isUnit_iff_ne_zero.mpr (pow_ne_zero 3 (ne_of_gt hℓ)))
        (fun r : Submission.BoseGases.X (q + 1) => K0 r)).mp hInt3'
    have hInt4 : MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X q =>
          (1 : ℝ) * K0 (Submission.BoseGases.kcInsN q k p)) (nur.prod mu2) := by
      have h1 : MeasureTheory.Integrable
          (fun r : Submission.BoseGases.X (q + 1) => (1 : ℝ) * K0 r) mu :=
        hK0int.congr (ae_of_all _ (fun r => (one_mul (K0 r)).symm))
      have hiff := hmp2.integrable_comp (g := fun r : Submission.BoseGases.X (q + 1) =>
        (1 : ℝ) * K0 r) h1.aestronglyMeasurable
      exact hiff.mpr h1
    have h3' : (∫ x in Submission.BoseGases.abox (q + 2) ℓ, K x)
        = ℓ ^ 3 * ∫ r : Submission.BoseGases.X (q + 1), K0 r ∂mu := by
      have h := peel_weighted (hℓ := hℓ) (i := i)
        (K := fun _ : Submission.BoseGases.X (q + 2) => (1 : ℝ)) (Ψ := K)
        (by intro x z; rfl) hInt3
      have hkey : ∀ r : Submission.BoseGases.X (q + 1),
          (1 : ℝ) * (∫ y in Submission.BoseGases.acube ℓ,
              K (Submission.BoseGases.kcInsN (q + 1) i (y, r)))
            = K0 r * ℓ ^ 3 := by
        intro r
        rw [one_mul]
        rw [show (∫ y in Submission.BoseGases.acube ℓ,
              K (Submission.BoseGases.kcInsN (q + 1) i (y, r)))
            = ∫ y in Submission.BoseGases.acube ℓ, K0 r from
              integral_congr_ae (ae_of_all _ (fun y => hKins y r))]
        rw [Submission.BoseGases.integral_const_acube ℓ hℓ]
      have h2 : (∫ r : Submission.BoseGases.X (q + 1),
            (1 : ℝ) * (∫ y in Submission.BoseGases.acube ℓ,
              K (Submission.BoseGases.kcInsN (q + 1) i (y, r)))
              ∂((volume : Measure (Submission.BoseGases.X (q + 1))).restrict
                (Submission.BoseGases.abox (q + 1) ℓ)))
          = ∫ r : Submission.BoseGases.X (q + 1), K0 r * ℓ ^ 3 ∂mu :=
        integral_congr_ae (ae_of_all _ hkey)
      rw [h2] at h
      rw [MeasureTheory.integral_mul_const] at h
      have h3 : (∫ x in Submission.BoseGases.abox (q + 2) ℓ, K x)
          = ∫ x in Submission.BoseGases.abox ((q + 1) + 1) ℓ,
              (fun _ : Submission.BoseGases.X (q + 2) => (1 : ℝ)) x * K x := by
        refine integral_congr_ae ?_
        filter_upwards with x
        exact (one_mul (K x)).symm
      have hfin : (∫ x in Submission.BoseGases.abox (q + 2) ℓ, K x)
          = (∫ r : Submission.BoseGases.X (q + 1), K0 r ∂mu) * ℓ ^ 3 := by
        rw [h3]
        exact h
      rw [hfin]
      ring
    have h4' : (∫ r : Submission.BoseGases.X (q + 1), K0 r ∂mu)
        = ℓ ^ 3 * ∫ r : Submission.BoseGases.X q, K1 r ∂mu2 := by
      have h := peel_weighted (hℓ := hℓ) (i := k)
        (K := fun _ : Submission.BoseGases.X (q + 1) => (1 : ℝ)) (Ψ := K0)
        (by intro x z; rfl) hInt4
      have hkey : ∀ r : Submission.BoseGases.X q,
          (1 : ℝ) * (∫ y in Submission.BoseGases.acube ℓ,
              K0 (Submission.BoseGases.kcInsN q k (y, r)))
            = K1 r * ℓ ^ 3 := by
        intro r
        rw [one_mul]
        rw [show (∫ y in Submission.BoseGases.acube ℓ,
              K0 (Submission.BoseGases.kcInsN q k (y, r)))
            = ∫ y in Submission.BoseGases.acube ℓ, K1 r from
              integral_congr_ae (ae_of_all _ (fun y => hK0ins y r))]
        rw [Submission.BoseGases.integral_const_acube ℓ hℓ]
      have h2 : (∫ r : Submission.BoseGases.X q,
            (1 : ℝ) * (∫ y in Submission.BoseGases.acube ℓ,
              K0 (Submission.BoseGases.kcInsN q k (y, r))) ∂mu2)
          = ∫ r : Submission.BoseGases.X q, K1 r * ℓ ^ 3 ∂mu2 :=
        integral_congr_ae (ae_of_all _ hkey)
      rw [h2] at h
      rw [MeasureTheory.integral_mul_const] at h
      have h3 : (∫ r : Submission.BoseGases.X (q + 1), K0 r ∂mu)
          = ∫ x in Submission.BoseGases.abox (q + 1) ℓ,
              (fun _ : Submission.BoseGases.X (q + 1) => (1 : ℝ)) x * K0 x := by
        refine integral_congr_ae ?_
        filter_upwards with x
        exact (one_mul (K0 x)).symm
      have hfin : (∫ r : Submission.BoseGases.X (q + 1), K0 r ∂mu)
          = (∫ r : Submission.BoseGases.X q, K1 r ∂mu2) * ℓ ^ 3 := by
        rw [h3]
        exact h
      rw [hfin]
      ring
    have hRHSval : (∫ x in Submission.BoseGases.abox (q + 2) ℓ, K x)
        = (ℓ ^ 3 * ℓ ^ 3) * (∫ r : Submission.BoseGases.X q, K1 r ∂mu2) := by
      rw [h3', h4']
      ring
    change (∫ x in Submission.BoseGases.abox (q + 2) ℓ, K x * g (x i) (x j))
        = (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ *
            (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ, g a b) *
            (∫ x in Submission.BoseGases.abox (q + 2) ℓ, K x)
    rw [hLHSval, hRHSval]
    have hℓ3 : (ℓ : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
    field_simp
  · exfalso
    have hn1 : n ≤ 1 := by omega
    have hsub : Subsingleton (Fin n) :=
      ⟨fun a b => Fin.ext (by have ha := a.isLt; have hb := b.isLt; omega)⟩
    exact hij (@Subsingleton.elim (Fin n) hsub i j)

end

end Work.BoseFixB3.CS.Pieces
