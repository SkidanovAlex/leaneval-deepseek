import ChallengeDeps
import Submission.Work.BoseFixB1.aesm_wSmallPair_pair
import Submission.Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre
import Submission.Work.BoseFixB1.integrableOn_slot_wSmallPair
import Submission.Work.BoseFixB1.wSmall1Pair_fibre_abs_le
import Submission.Work.BoseFixB1S.BoxPotFrag
import Submission.Work.SlotWord.chiSmallB_support_mem_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1M

open MeasureTheory
open scoped Real BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

-- `ℝ³` is the global notation of `Submission.Work.BoseKinLoc.Defs` (in the import cone),
-- already `EuclideanSpace ℝ (Fin 3)`; a local notation here would be ambiguous.

/-!
# `Work.BoseFixB1M.muPart_dlBox` — the `μ`-part of the localised potential word

The potential word of the sliding box is
`qLHSword ℓ μ (wSmallPair M ℓ d u v) (wSmallPair M ℓ d u (g₀ v h)) Φ`
(`Submission.Work.SmallBoxSliding.qLHSwordB`), whose `μ`-part is the integral

    ∫_{abox N ℓ} Φ(x)² · (−μ · Σᵢ ∫_{acube ℓ} w_{1,B(u)}(xᵢ,y) dy) .

The statement proved here rewrites this `μ`-part in terms of the *box projections*
`Pᵢ = boxPInd volA A i`, `Qᵢ = boxQInd volA A i` of the sliding box `A = dlBox ℓ d u`
(`volA = boxMass ℓ d u = |A|`), namely as

    −μ · ( Σᵢ boxMuP + 2 Σᵢ boxMuQP + Σᵢ boxMuQ ) ,

the three integrands being `(PᵢΦ)²`, `(QᵢΦ)(PᵢΦ)`, `(QᵢΦ)²` times the fibre
`w1Fibre ℓ w₁ (xᵢ)`.

The proof is the composition of two independent algebraic/measure-theoretic facts,
delegated and proved in companion modules:

* `Work.BoseFixB1M.muPartFib` — `∫ Φ²·(−μ Σᵢ fib(xᵢ)) = −μ Σᵢ boxMuPhi`,
  i.e. pulling the constant `−μ` out of the integral and exchanging the finite slot
  sum with the integral (this is the `hmu` block of `qLHSword_split`, without the
  continuity hypotheses: the localised fibre `w₁ = wSmallPair M ℓ d u (g₀ v h)` is
  only a.e. measurable and a.e. bounded);
* `Work.BoseFixB1M.boxMuSum` — `Σᵢ boxMuP + 2 Σᵢ boxMuQP + Σᵢ boxMuQ = Σᵢ boxMuPhi`,
  which is the pointwise identity `(Pᵢ + Qᵢ)² = 1_A(xᵢ)·Φ²` combined with the fact that
  the fibre vanishes off the support box `A` of the localised kernel.

The remaining work in this file is the *instantiation*: the a.e. strong measurability
and the uniform bound of the localised fibre on `acube ℓ` (from
`Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre` and
`Work.BoseFixB1.wSmall1Pair_fibre_abs_le`), the vanishing of the fibre off
`dlBox ℓ d u`, and the integrability of the three slot integrands on `abox N ℓ`
(the box projections are bounded by `max 0 ‖Φ‖_∞` and measurable).
-/

/-- Integrability on the box of a product `S x * F (x i)` where the slot factor `S` is a.e.
strongly measurable and a.e. bounded on `abox N ℓ`, and the fibre `F` is a.e. strongly
measurable on `acube ℓ` and bounded there. -/
private lemma integrableOn_abox_slot_mul {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {F : ℝ³ → ℝ}
    (hFm : AEStronglyMeasurable F (volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hC : ∀ z ∈ Submission.BoseGases.acube ℓ, |F z| ≤ C)
    {S : Submission.BoseGases.X N → ℝ}
    (hSm : AEStronglyMeasurable S (volume.restrict (Submission.BoseGases.abox N ℓ)))
    {B : ℝ} (hB : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox N ℓ)), |S x| ≤ B) :
    IntegrableOn (fun x : Submission.BoseGases.X N => S x * F (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
  have hAm : AEStronglyMeasurable (fun x : Submission.BoseGases.X N => S x * F (x i))
      (volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    hSm.mul (Submission.BoseGases.aem_comp_coord' i hFm)
  refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le) hAm (B * C) ?_
  have hB' : ∀ᵐ x ∂(volume : Measure (Submission.BoseGases.X N)),
      x ∈ Submission.BoseGases.abox N ℓ → |S x| ≤ B :=
    (ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)).mp hB
  rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
  filter_upwards [hB'] with x hx
  intro hmem
  have hFx : |F (x i)| ≤ C := hC (x i) (hmem i)
  have hSx : |S x| ≤ B := hx hmem
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hSx hFx (abs_nonneg _) (le_trans (abs_nonneg _) hSx)

/-- Pulling the constant `−μ` out of the integral and exchanging the finite slot sum with
the integral: the `μ`-part of the localised potential word is `−μ` times the slot sum of the
fibre weights. -/
private theorem muPartFib_aux {N : ℕ} {ℓ μ : ℝ}
    {w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ}
    (hInt : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) volume) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * (-μ * ∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))
      = -μ * (∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i) := by
  have h1 : (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * (-μ * ∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (-μ) * ((Φ x) ^ 2 * ∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [h1, MeasureTheory.integral_const_mul]
  congr 1
  calc
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * ∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))
        = ∫ x in Submission.BoseGases.abox N ℓ,
            ∑ i : Fin N, (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [Finset.mul_sum]
      _ = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i) :=
          MeasureTheory.integral_finsetSum _
            (fun i _ => by simpa [IntegrableOn] using hInt i)
      _ = ∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i := by
          simp only [Work.BoseFixB1S.boxMuPhi]

/-- The box-projection `μ`-sum identity: `Σᵢ boxMuP + 2 Σᵢ boxMuQP + Σᵢ boxMuQ = Σᵢ boxMuPhi`,
from the pointwise identity `(Pᵢ + Qᵢ)² = 1_A(xᵢ)·Φ²` and the vanishing of the fibre off `A`. -/
private theorem boxMuSum_aux {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    {w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hvan : ∀ z : EuclideanSpace ℝ (Fin 3),
      z ∉ A → Submission.BoseGases.w1Fibre ℓ w1 z = 0)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hIntP : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) volume)
    (hIntQP : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
          * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) volume)
    (hIntQ : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) volume) :
    (∑ i : Fin N, Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i)
      + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i)
      + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i)
      = ∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i := by
  have hper : ∀ i : Fin N,
      Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i
        + 2 * Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i
        + Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i
      = Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i := by
    intro i
    simp only [Work.BoseFixB1S.boxMuP, Work.BoseFixB1S.boxMuQP, Work.BoseFixB1S.boxMuQ,
      Work.BoseFixB1S.boxMuPhi]
    set fib : EuclideanSpace ℝ (Fin 3) → ℝ := Submission.BoseGases.w1Fibre ℓ w1 with hfibdef
    set P : Submission.BoseGases.X N → ℝ := Work.UBBInputs8.boxPInd volA A i Φ with hPdef
    set Q : Submission.BoseGases.X N → ℝ := Work.UBBInputs8.boxQInd volA A i Φ with hQdef
    have hPt : ∀ x : Submission.BoseGases.X N,
        P x + Q x = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x := by
      intro x
      rw [hPdef, hQdef]
      unfold Work.UBBInputs8.boxQInd
      ring
    have hkey : ∀ x : Submission.BoseGases.X N,
        P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i)) + Q x ^ 2 * fib (x i)
          = Φ x ^ 2 * fib (x i) := by
      intro x
      have hind : A.indicator (fun _ => (1 : ℝ)) (x i) ^ 2
          = A.indicator (fun _ => (1 : ℝ)) (x i) := by
        by_cases hx : x i ∈ A <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
      have hsq : A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x ^ 2
          = P x ^ 2 + 2 * (Q x * P x) + Q x ^ 2 := by
        calc A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x ^ 2
            = (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 := by rw [mul_pow, hind]
          _ = (P x + Q x) ^ 2 := by rw [hPt x]
          _ = P x ^ 2 + 2 * (Q x * P x) + Q x ^ 2 := by ring
      have hstep : (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x ^ 2) * fib (x i)
          = Φ x ^ 2 * fib (x i) := by
        by_cases hx : x i ∈ A
        · rw [Set.indicator_of_mem hx, one_mul]
        · have hf0 : fib (x i) = 0 := hvan (x i) hx
          rw [Set.indicator_of_notMem hx, hf0]
          ring
      calc P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i)) + Q x ^ 2 * fib (x i)
          = (P x ^ 2 + 2 * (Q x * P x) + Q x ^ 2) * fib (x i) := by ring
        _ = (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x ^ 2) * fib (x i) := by rw [hsq]
        _ = Φ x ^ 2 * fib (x i) := hstep
    have i1 : IntegrableOn (fun x : Submission.BoseGases.X N => P x ^ 2 * fib (x i))
        (Submission.BoseGases.abox N ℓ) volume := by
      simpa only [hPdef, hfibdef] using hIntP i
    have i2 : IntegrableOn (fun x : Submission.BoseGases.X N => Q x * P x * fib (x i))
        (Submission.BoseGases.abox N ℓ) volume := by
      simpa only [hPdef, hQdef, hfibdef] using hIntQP i
    have i2' : IntegrableOn (fun x : Submission.BoseGases.X N => 2 * (Q x * P x * fib (x i)))
        (Submission.BoseGases.abox N ℓ) volume := i2.const_mul 2
    have i3 : IntegrableOn (fun x : Submission.BoseGases.X N => Q x ^ 2 * fib (x i))
        (Submission.BoseGases.abox N ℓ) volume := by
      simpa only [hQdef, hfibdef] using hIntQ i
    have h12 : IntegrableOn (fun x : Submission.BoseGases.X N =>
        P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i)))
        (Submission.BoseGases.abox N ℓ) volume := i1.add i2'
    have h2G : 2 * (∫ x in Submission.BoseGases.abox N ℓ, Q x * P x * fib (x i))
        = ∫ x in Submission.BoseGases.abox N ℓ, 2 * (Q x * P x * fib (x i)) :=
      (MeasureTheory.integral_const_mul (2 : ℝ)
        (fun x : Submission.BoseGases.X N => Q x * P x * fib (x i))).symm
    have hA1 : (∫ x in Submission.BoseGases.abox N ℓ, P x ^ 2 * fib (x i))
          + (∫ x in Submission.BoseGases.abox N ℓ, 2 * (Q x * P x * fib (x i)))
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))) :=
      (MeasureTheory.integral_add i1 i2').symm
    have hA2 : (∫ x in Submission.BoseGases.abox N ℓ,
            (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))))
          + (∫ x in Submission.BoseGases.abox N ℓ, Q x ^ 2 * fib (x i))
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))) + Q x ^ 2 * fib (x i) :=
      (MeasureTheory.integral_add h12 i3).symm
    have hA3 : (∫ x in Submission.BoseGases.abox N ℓ,
            (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))) + Q x ^ 2 * fib (x i))
        = ∫ x in Submission.BoseGases.abox N ℓ, Φ x ^ 2 * fib (x i) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact hkey x
    linarith [h2G, hA1, hA2, hA3]
  have hLHS : (∑ i : Fin N, Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i)
        + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i)
        + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i)
      = ∑ i : Fin N, (Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i
          + 2 * Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i
          + Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hLHS]
  exact Finset.sum_congr rfl (fun i _ => hper i)

theorem muPart_dlBox {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 *
        (-μ * ∑ i : Fin N,
          Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmallPair M ℓ d u
            (Submission.BoseGases.g0 v h)) (x i)))
      = -μ * ((∑ i : Fin N, Work.BoseFixB1S.boxMuP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)) Φ i)
          + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)) Φ i)
          + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)) Φ i)) := by
  classical
  -- ### abbreviations for the localised kernel and the sliding box
  set W : ℝ³ → ℝ³ → ℝ := Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)
    with hWdef
  set A : Set ℝ³ := Submission.BoseGases.dlBox ℓ d u with hAdef
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolAdef
  have hAmeas : MeasurableSet A := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA_eq : volA = (volume A).toReal := by
    rw [hvolAdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  -- ### the localised fibre: a.e. strong measurability and uniform bound
  have hFm : AEStronglyMeasurable (Submission.BoseGases.w1Fibre ℓ W)
      (volume.restrict (Submission.BoseGases.acube ℓ)) := by
    have hint : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) volume :=
      Submission.BoseGases.g0_integrable hR0 hv_supp h
    have hm := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
      (f := Submission.BoseGases.g0 v h) hint.aestronglyMeasurable.aemeasurable
    exact hm
  have hCb : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |Submission.BoseGases.w1Fibre ℓ W z| ≤
        max 0 (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M *
          (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) /
            Work.SmallBoxSliding.smallConvLower M * (8 * Real.pi * BoseGases.a v))) := by
    intro z _
    refine le_trans ?_ (le_max_right _ _)
    have h := Work.BoseFixB1.wSmall1Pair_fibre_abs_le (v := v) (R0 := R0) hv_supp hR0 hv hvrad h
      hM hℓ hd hR hRχ u z
    simpa only [hWdef, Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair] using h
  -- ### the fibre vanishes off the support box of the localised kernel
  have hvan : ∀ z : ℝ³, z ∉ A → Submission.BoseGases.w1Fibre ℓ W z = 0 := by
    intro z hz
    have hz0 : (fun y : ℝ³ => W z y) = fun _ => (0 : ℝ) := by
      funext y
      have hc : Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
        by_contra hne
        exact hz (by
          rw [hAdef]
          exact Work.SlotWord.chiSmallB_support_mem_dlBox (M := M) hM hℓ hd (u := u) (x := z) hne)
      simp only [hWdef, Submission.BoseGases.wSmallPair, hc, zero_mul]
    simp only [Submission.BoseGases.w1Fibre, hz0, integral_zero]
  -- ### integrability of the four slot integrands on the box
  have hInt : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ W (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    exact Submission.BoseGases.integrableOn_slot_fibre hℓ i hFm hCb (hΦc.pow 2)
  obtain ⟨C₀, hC₀⟩ :=
    (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C := by
    intro x hx
    have h := hC₀ x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  have hPb : ∀ i : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C := by
    intro i x hx
    exact Work.BoseFixB1S.abs_boxPInd_le hℓ (by rw [hvolAdef]; exact hvol) hAmeas hvolA_eq hAc i hΦb x hx
  have hQb : ∀ i : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * C := by
    intro i x hx
    have hQx : Work.UBBInputs8.boxQInd volA A i Φ x
        = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
          - Work.UBBInputs8.boxPInd volA A i Φ x := rfl
    rw [hQx]
    have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases hxi : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - Work.UBBInputs8.boxPInd volA A i Φ x|
        ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
            + |Work.UBBInputs8.boxPInd volA A i Φ x| := abs_sub _ _
      _ ≤ 1 * |Φ x| + C := by
          refine add_le_add ?_ (hPb i x hx)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hind (abs_nonneg _)
      _ ≤ 2 * C := by
          have h := hΦb x hx
          linarith
  have hIntP : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ W (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    refine integrableOn_abox_slot_mul hℓ i hFm hCb
      ((Work.BoseFixB1S.measurable_boxPInd volA A hAmeas i hΦc.measurable).pow_const 2).aestronglyMeasurable
      (B := C ^ 2) ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    apply Filter.Eventually.of_forall
    intro x hx
    calc |(Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2|
        = |Work.UBBInputs8.boxPInd volA A i Φ x| ^ 2 := abs_pow _ 2
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hPb i x hx) 2
  have hIntQP : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
          * Submission.BoseGases.w1Fibre ℓ W (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    refine integrableOn_abox_slot_mul hℓ i hFm hCb
      (((Work.SlotWord.measurable_boxQInd volA A hAmeas i hΦc.measurable).mul
        (Work.BoseFixB1S.measurable_boxPInd volA A hAmeas i hΦc.measurable)).aestronglyMeasurable)
      (B := (2 * C) * C) ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [abs_mul]
    exact mul_le_mul (hQb i x hx) (hPb i x hx) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hQb i x hx))
  have hIntQ : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ W (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    refine integrableOn_abox_slot_mul hℓ i hFm hCb
      ((Work.SlotWord.measurable_boxQInd volA A hAmeas i hΦc.measurable).pow_const 2).aestronglyMeasurable
      (B := (2 * C) ^ 2) ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    apply Filter.Eventually.of_forall
    intro x hx
    calc |(Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2|
        = |Work.UBBInputs8.boxQInd volA A i Φ x| ^ 2 := abs_pow _ 2
      _ ≤ (2 * C) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hQb i x hx) 2
  -- ### assembly: the two halves of the identity
  have hboxes : (∑ i : Fin N, Work.BoseFixB1S.boxMuP volA ℓ A W Φ i)
      + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP volA ℓ A W Φ i)
      + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ volA ℓ A W Φ i)
      = ∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ W Φ i :=
    boxMuSum_aux hvan hIntP hIntQP hIntQ
  have hfib : (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * (-μ * ∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ W (x i)))
      = -μ * (∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ W Φ i) :=
    muPartFib_aux hInt
  rw [hfib]
  congr 1
  rw [hWdef] at hboxes ⊢
  rw [hvolAdef, hAdef] at hboxes ⊢
  exact hboxes.symm

end Work.BoseFixB1M
