import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseFixB1.perBoxF_flat
import Submission.Work.BoseFixB1PInd.lintegral_abox_peel
import Submission.Work.BoseFixB1S.FlatFib.fibMeasurableRep
import Submission.Work.BoseFixB1S.FlatFib.lintegralAbsAddConstEqTop
import Submission.Work.BoseFixB1S.boxConstCalibB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.FlatFib.flatFibSumEqZero` — the degenerate flat fibre sum

The flat-fibre identity `flatFibSum = (w1MassB/chiMass)·flatScountB`
(`Work.BoseFixB1S.flatFibreMeanFieldB1`) has a *degenerate* branch: when the localised
one-body fibre

    fib z := ∫ y in acube ℓ, wSmall1Pair h M ℓ d u z y

is **not** integrable on the sliding box `A = dlBox ℓ d u` (`∫⁻_A |fib| = ⊤`), the Bochner
integral `∫_{abox n ℓ} Φ² · Σᵢ fib(xᵢ)` is forced to vanish, for every state `Φ` which is
box-constant in every slot (`boxQInd volA A i Φ =ᵐ 0`, the flat branch's hypothesis).

The mathematical mechanism is this.  On the tube `{xᵢ ∈ A}` the box-constancy replaces `Φ` by
the slot-`i` fibre mean `m(x_{-i})`, and the *support* of the fibre `fib` is inside `A`; hence
the integrand equals `m(x_{-i})² · (fib(xᵢ) + C(x))`, where `C` collects the other slots.  So
the `ℝ≥0∞`-integral of the modulus is, by Tonelli along the slot `i`,

    ∫⁻_{x ∈ abox (n+1) ℓ} ‖Φ² Σⱼ fib(xⱼ)‖ ≥ ∫⁻_{x_{-i}} ofReal(m(x_{-i})²) · ⊤ ,

the inner factor being `⊤` because shifting the fibre by the (finite) other-slots sum cannot
make it integrable (`Work.BoseFixB1S.FlatFib.lintegralAbsAddConstEqTop`).  Integrability of the
integrand — the target's `hint` — therefore forces `m =ᵐ 0`, which by the box-constancy is
`1_A(xᵢ)Φ =ᵐ 0` for **every** slot `i`; and then every summand `Φ²fib(xᵢ)` vanishes a.e.
(on `{xᵢ ∈ A}` because `Φ =ᵐ 0`, off it because `fib(xᵢ) = 0`).

The paving of the argument:

* `Work.BoseFixB1S.FlatFib.fibMeasurableRep` — a globally measurable representative of `fib`;
* `Work.BoseFixB1S.FlatFib.lintegralAbsAddConstEqTop` — `∫⁻_A |f| = ⊤ ⟹ ∫⁻_A |f + c| = ⊤`
  on a finite-measure set;
* `Work.BoseFixB1S.FlatFib.boxQIndAeFlatPeel` — `boxQInd =ᵐ 0` read in the slot-`i` product
  coordinates (`kcInsN`);
* `Work.BoseFixB1S.FlatFib.tubeLintegralFactor` — the Tonelli factorisation of the tube
  integral into `∫⁻_{x_{-i}} ofReal(m²) · ⊤`;
* `Work.BoseFixB1S.FlatFib.fibMeanAeZeroOfPeel` — `m =ᵐ 0` transfers back to the slot mean;
* `Work.BoseFixB1S.FlatFib.slotVanishes` — the per-slot conclusion `1_A(xᵢ)Φ =ᵐ 0`.

Everything is stated for a general measurable `A ⊆ acube ℓ` of finite measure; the instantiation
`A = dlBox ℓ d u`, `volA = boxMass ℓ d u` is the target.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S.FlatFib

set_option maxHeartbeats 1000000
set_option autoImplicit false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. The slot-`i` product measure and the analytic pieces of the `⊤`-argument

`kcInsN k i` identifies the product of the one-particle cube with the `k`-particle box with the
`(k+1)`-particle box as measure spaces (`kcInsN_mp_abox`); the three theorems that follow are the
analytic pieces of the `⊤`-argument described in the module header.  (`boxQIndAeFlatPeel`,
`tubeLintegralFactor` and `fibMeanAeZeroOfPeel` are proved here; their companions
`fibMeasurableRep` and `lintegralAbsAddConstEqTop` are imported from their own modules.) -/

/-- **The slot insertion is measure preserving on the boxes**: `kcInsN k i` carries
`(volume↾acube ℓ) × (volume↾abox k ℓ)` to `volume↾abox (k+1) ℓ`. -/
theorem kcInsN_mp_abox {k : ℕ} {ℓ : ℝ} (i : Fin (k + 1)) :
    MeasurePreserving (⇑(Submission.BoseGases.kcInsN k i))
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.kcE3)).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict
          (Submission.BoseGases.abox k ℓ)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (k + 1))).restrict
        (Submission.BoseGases.abox (k + 1) ℓ)) := by
  have hpre : (Submission.BoseGases.kcInsN k i) ⁻¹' (Submission.BoseGases.abox (k + 1) ℓ)
      = Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox k ℓ := by
    ext p
    obtain ⟨y, r⟩ := p
    simp only [Set.mem_preimage, Set.mem_prod, Submission.BoseGases.mem_abox_iff]
    constructor
    · intro hp
      exact ⟨by simpa [Submission.BoseGases.kc_insN_apply_same] using hp i,
        fun j => by simpa [Submission.BoseGases.kc_insN_apply_succ] using hp (i.succAbove j)⟩
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj
        simpa [Submission.BoseGases.kc_insN_apply_same] using h1
      · rcases Fin.exists_succAbove_eq hj with ⟨j', hj'⟩
        rw [← hj']
        simpa [Submission.BoseGases.kc_insN_apply_succ] using h2 j'
  have hvol : (MeasureTheory.volume :
        MeasureTheory.Measure (Submission.BoseGases.kcE3 × Submission.BoseGases.X k)).restrict
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox k ℓ)
      = ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.kcE3)).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict
          (Submission.BoseGases.abox k ℓ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod (Submission.BoseGases.kcE3)
        (Submission.BoseGases.X k),
      ← MeasureTheory.Measure.prod_restrict]
  have h1 := (Submission.BoseGases.kc_mp_insN k i).restrict_preimage_emb
    (Submission.BoseGases.kcInsN k i).measurableEmbedding (Submission.BoseGases.abox (k + 1) ℓ)
  rw [hpre, hvol] at h1
  exact h1

theorem boxQIndAeFlatPeel {k : ℕ} {ℓ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} (volA : ℝ)
    (i : Fin (k + 1)) {Φ : Submission.BoseGases.X (k + 1) → ℝ}
    (hQae : Work.UBBInputs8.boxQInd volA A i Φ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (k + 1) ℓ)] 0) :
    ∀ᵐ q ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
            (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ))),
      q.1 ∈ A → Φ (Submission.BoseGases.kcInsN k i q)
        = (1 / volA) * ∫ z in A, Φ (Submission.BoseGases.kcInsN k i (z, q.2)) := by
  classical
  have h1 : ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.X (k + 1))).restrict (Submission.BoseGases.abox (k + 1) ℓ)),
      Work.UBBInputs8.boxQInd volA A i Φ x = 0 := by
    simpa only [Filter.EventuallyEq, Pi.zero_apply] using hQae
  have h2 : ∀ᵐ q ∂(((MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.kcE3)).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict
          (Submission.BoseGases.abox k ℓ))),
      Work.UBBInputs8.boxQInd volA A i Φ (Submission.BoseGases.kcInsN k i q) = 0 :=
    (kcInsN_mp_abox (ℓ := ℓ) i).quasiMeasurePreserving.ae h1
  filter_upwards [h2] with q hq
  intro hmem
  obtain ⟨t, r⟩ := q
  have hq' := hq
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd,
    Submission.BoseGases.kc_insN_apply_same] at hq'
  rw [Set.indicator_of_mem hmem] at hq'
  simp only [Submission.BoseGases.update_kcInsN, one_mul, mul_one, sub_eq_zero] at hq'
  exact hq'

theorem tubeLintegralFactor {k : ℕ} {ℓ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {m C : Submission.BoseGases.X k → ℝ} (hm : Measurable m) (hC : Measurable C)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfibm : Measurable fib)
    (htop : ∀ c : ℝ, ∫⁻ z in A, ENNReal.ofReal |fib z + c| = ⊤) :
    (∫⁻ q : Submission.BoseGases.kcE3 × Submission.BoseGases.X k,
        A.indicator (fun _ => (1 : ENNReal)) q.1
          * (ENNReal.ofReal ((m q.2) ^ 2) * ENNReal.ofReal |fib q.1 + C q.2|)
      ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ))))
      = ∫⁻ r in Submission.BoseGases.abox k ℓ, ENNReal.ofReal ((m r) ^ 2) * ⊤ := by
  classical
  -- the integrand is measurable
  have hgm : Measurable fun q : Submission.BoseGases.kcE3 × Submission.BoseGases.X k =>
      ENNReal.ofReal |fib q.1 + C q.2| :=
    ENNReal.continuous_ofReal.measurable.comp
      (((hfibm.comp measurable_fst).add (hC.comp measurable_snd)).abs)
  have hFm : Measurable fun q : Submission.BoseGases.kcE3 × Submission.BoseGases.X k =>
      A.indicator (fun _ => (1 : ENNReal)) q.1
        * (ENNReal.ofReal ((m q.2) ^ 2) * ENNReal.ofReal |fib q.1 + C q.2|) := by
    have h1 : Measurable fun q : Submission.BoseGases.kcE3 × Submission.BoseGases.X k =>
        A.indicator (fun _ => (1 : ENNReal)) q.1 :=
      (measurable_const.indicator hA).comp measurable_fst
    have h2 : Measurable fun q : Submission.BoseGases.kcE3 × Submission.BoseGases.X k =>
        ENNReal.ofReal ((m q.2) ^ 2) :=
      ENNReal.continuous_ofReal.measurable.comp ((hm.comp measurable_snd).pow_const 2)
    exact h1.mul (h2.mul hgm)
  -- the slot integral at fixed second coordinate
  have hinner : ∀ r : Submission.BoseGases.X k,
      (∫⁻ t : Submission.BoseGases.kcE3,
          A.indicator (fun _ => (1 : ENNReal)) t
            * (ENNReal.ofReal ((m r) ^ 2) * ENNReal.ofReal |fib t + C r|)
          ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
        = ENNReal.ofReal ((m r) ^ 2) * ⊤ := by
    intro r
    have hgr : Measurable fun t : Submission.BoseGases.kcE3 =>
        ENNReal.ofReal |fib t + C r| :=
      ENNReal.continuous_ofReal.measurable.comp ((hfibm.add_const (C r)).abs)
    have hpt : (fun t : Submission.BoseGases.kcE3 =>
          A.indicator (fun _ => (1 : ENNReal)) t
            * (ENNReal.ofReal ((m r) ^ 2) * ENNReal.ofReal |fib t + C r|))
        = fun t => ENNReal.ofReal ((m r) ^ 2) *
            (A.indicator (fun t => ENNReal.ofReal |fib t + C r|) t) := by
      funext t
      by_cases ht : t ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]
    rw [show (∫⁻ t : Submission.BoseGases.kcE3,
          A.indicator (fun _ => (1 : ENNReal)) t
            * (ENNReal.ofReal ((m r) ^ 2) * ENNReal.ofReal |fib t + C r|)
          ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
        = ∫⁻ t : Submission.BoseGases.kcE3, ENNReal.ofReal ((m r) ^ 2) *
            (A.indicator (fun t => ENNReal.ofReal |fib t + C r|) t)
          ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) from
        lintegral_congr (fun t => congrFun hpt t)]
    rw [lintegral_const_mul _ (hgr.indicator hA)]
    congr 1
    rw [lintegral_indicator hA]
    rw [Measure.restrict_restrict (μ := (MeasureTheory.volume :
      MeasureTheory.Measure (Submission.BoseGases.kcE3))) hA]
    rw [Set.inter_eq_self_of_subset_left hAc]
    exact htop (C r)
  -- Fubini: iterate the product integral in the order `(r, t)`
  rw [MeasureTheory.lintegral_prod
    (f := fun q : Submission.BoseGases.kcE3 × Submission.BoseGases.X k =>
      A.indicator (fun _ => (1 : ENNReal)) q.1
        * (ENNReal.ofReal ((m q.2) ^ 2) * ENNReal.ofReal |fib q.1 + C q.2|))
    hFm.aemeasurable]
  rw [MeasureTheory.lintegral_lintegral_swap
    (f := fun t : Submission.BoseGases.kcE3 => fun r : Submission.BoseGases.X k =>
      A.indicator (fun _ => (1 : ENNReal)) t
        * (ENNReal.ofReal ((m r) ^ 2) * ENNReal.ofReal |fib t + C r|))
    (by
      rw [show Function.uncurry (fun t : Submission.BoseGases.kcE3 =>
            fun r : Submission.BoseGases.X k =>
              A.indicator (fun _ => (1 : ENNReal)) t
                * (ENNReal.ofReal ((m r) ^ 2) * ENNReal.ofReal |fib t + C r|))
          = fun q : Submission.BoseGases.kcE3 × Submission.BoseGases.X k =>
              A.indicator (fun _ => (1 : ENNReal)) q.1
                * (ENNReal.ofReal ((m q.2) ^ 2) * ENNReal.ofReal |fib q.1 + C q.2|) from rfl]
      exact hFm.aemeasurable)]
  apply lintegral_congr
  intro r
  exact hinner r

theorem fibMeanAeZeroOfPeel {k : ℕ} {ℓ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} (volA : ℝ)
    (i : Fin (k + 1)) {Φ : Submission.BoseGases.X (k + 1) → ℝ}
    (hm : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ)),
      (1 / volA) * ∫ z in A, Φ (Submission.BoseGases.kcInsN k i (z, r)) = 0) :
    (fun x : Submission.BoseGases.X (k + 1) =>
        (1 / volA) * ∫ z in A, Φ (Function.update x i z))
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (k + 1) ℓ)] 0 := by
  classical
  set f : Submission.BoseGases.X (k + 1) → ℝ :=
    fun x => (1 / volA) * ∫ z in A, Φ (Function.update x i z) with hfdef
  set g : Submission.BoseGases.X k → ℝ :=
    fun r => (1 / volA) * ∫ z in A, Φ (Submission.BoseGases.kcInsN k i (z, r)) with hgdef
  -- the pointwise link between the two functions
  have hrel : ∀ q : Submission.BoseGases.kcE3 × Submission.BoseGases.X k,
      f (Submission.BoseGases.kcInsN k i q) = g q.2 := by
    rintro ⟨t, u⟩
    rw [hfdef, hgdef]
    show (1 / volA) * ∫ z in A, Φ (Function.update (Submission.BoseGases.kcInsN k i (t, u)) i z)
        = (1 / volA) * ∫ z in A, Φ (Submission.BoseGases.kcInsN k i (z, u))
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    simp only [Submission.BoseGases.update_kcInsN]
  -- `g` vanishes a.e. on the product measure
  have hprod : ∀ᵐ q ∂(((MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.kcE3)).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict
          (Submission.BoseGases.abox k ℓ))), g q.2 = 0 := by
    rw [MeasureTheory.ae_iff]
    have hB : {q : Submission.BoseGases.kcE3 × Submission.BoseGases.X k | ¬ (g q.2 = 0)}
        = Set.univ ×ˢ {r : Submission.BoseGases.X k | ¬ (g r = 0)} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
    rw [hB, MeasureTheory.Measure.prod_prod, MeasureTheory.ae_iff.mp hm]
    simp
  -- transfer back along the inverse insertion
  have hmp : MeasurePreserving (⇑(Submission.BoseGases.kcInsN k i))
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.kcE3)).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict
          (Submission.BoseGases.abox k ℓ)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (k + 1))).restrict
        (Submission.BoseGases.abox (k + 1) ℓ)) := kcInsN_mp_abox (ℓ := ℓ) i
  have hx := (MeasureTheory.MeasurePreserving.symm (Submission.BoseGases.kcInsN k i) hmp
    ).quasiMeasurePreserving.ae hprod
  filter_upwards [hx] with x hx
  have hfx : f x = g ((Submission.BoseGases.kcInsN k i).symm x).2 := by
    have h1 := hrel ((Submission.BoseGases.kcInsN k i).symm x)
    rwa [(Submission.BoseGases.kcInsN k i).apply_symm_apply x] at h1
  rw [hfx]
  simpa only [Pi.zero_apply] using hx

/-! ## 1. The per-slot vanishing of the flat value -/

/-- **Slot-`i` vanishing of the box-constant component.**  If `Φ` is box-constant in every slot
(`boxQInd volA A i Φ =ᵐ 0`) and the localised fibre is not integrable on `A`, then the tube part
`1_A(xᵢ)·Φ` of the state vanishes a.e. on the box.

The proof is the `⊤`-argument of the module header: peel the slot `i` out of the box, apply the
a.e. box-constancy on the tube `{xᵢ ∈ A}`, factor the resulting product integral by Tonelli, and
use that shifting the non-integrable fibre by the (finite) other-slots sum keeps it
non-integrable. -/
theorem slotVanishes {k : ℕ} {ℓ : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube ℓ) (volA : ℝ)
    (i : Fin (k + 1)) {Φ : Submission.BoseGases.X (k + 1) → ℝ} (hΦm : Measurable Φ)
    {fib : E3 → ℝ} (hfibm : Measurable fib)
    (hQae : Work.UBBInputs8.boxQInd volA A i Φ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (k + 1) ℓ)] 0)
    (htop : ∀ c : ℝ, ∫⁻ z in A, ENNReal.ofReal |fib z + c| = ⊤)
    (hfin : ∫⁻ x in Submission.BoseGases.abox (k + 1) ℓ,
        ‖Φ x ^ 2 * ∑ j : Fin (k + 1), fib (x j)‖ₑ < ∞) :
    (fun x : Submission.BoseGases.X (k + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (k + 1) ℓ)] 0 := by
  classical
  -- ### 0. abbreviations: the slot-`i` fibre mean and the other-slots sum
  set m : Submission.BoseGases.X k → ℝ :=
    fun r => (1 / volA) * ∫ z in A, Φ (Submission.BoseGases.kcInsN k i (z, r)) with hmdef
  set C : Submission.BoseGases.X k → ℝ := fun r => ∑ l : Fin k, fib (r l) with hCdef
  have hm_meas : Measurable m := by
    have h1 : Measurable (fun r : Submission.BoseGases.X k =>
        ∫ z in A, Φ (Function.update (Submission.BoseGases.kcInsN k i ((0 : E3), r)) i z)) :=
      (Work.BoseFixB1S.measurable_fibreMean A hA i hΦm).comp
        ((Submission.BoseGases.kcInsN k i).measurable.comp
          (Measurable.prodMk measurable_const measurable_id))
    have h2 : (fun r : Submission.BoseGases.X k =>
          ∫ z in A, Φ (Function.update (Submission.BoseGases.kcInsN k i ((0 : E3), r)) i z))
        = fun r => ∫ z in A, Φ (Submission.BoseGases.kcInsN k i (z, r)) := by
      funext r
      exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [Submission.BoseGases.update_kcInsN]))
    rw [hmdef]
    exact (h2 ▸ h1).const_mul (1 / volA)
  have hC_meas : Measurable C := by
    rw [hCdef]
    exact Finset.measurable_sum Finset.univ
      (fun l _ => hfibm.comp (measurable_pi_apply l))
  -- ### 1. measurability
  have hW_meas : Measurable (fun x : Submission.BoseGases.X (k + 1) =>
      Φ x ^ 2 * ∑ j : Fin (k + 1), fib (x j)) :=
    (hΦm.pow_const 2).mul (Finset.measurable_sum Finset.univ
      (fun j _ => hfibm.comp (measurable_pi_apply j)))
  have hG_meas : Measurable (fun x : Submission.BoseGases.X (k + 1) =>
      ‖Φ x ^ 2 * ∑ j : Fin (k + 1), fib (x j)‖ₑ) :=
    measurable_enorm.comp hW_meas
  -- ### 2. peel the slot `i` out of the box, and cut out the tube `{xᵢ ∈ A}`
  have hpeel := Work.BoseFixB1PInd.lintegral_abox_peel (n := k) (ℓ := ℓ) i hG_meas
  set T : Set (Submission.BoseGases.kcE3 × Submission.BoseGases.X k) := {q | q.1 ∈ A} with hTdef
  have hTmeas : MeasurableSet T := by
    rw [hTdef]
    exact hA.preimage measurable_fst
  have hTfin : ∫⁻ q in T, ‖Φ (Submission.BoseGases.kcInsN k i q) ^ 2 *
      ∑ j : Fin (k + 1), fib ((Submission.BoseGases.kcInsN k i q) j)‖ₑ
      ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ))) < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono_set (Set.subset_univ T)) ?_
    rw [Measure.restrict_univ, ← hpeel]
    exact hfin
  -- ### 3. the a.e. flatness and the pointwise sum identity
  have hflat := boxQIndAeFlatPeel (k := k) (ℓ := ℓ) (A := A) volA i hQae
  have hsum : ∀ q : Submission.BoseGases.kcE3 × Submission.BoseGases.X k,
      (∑ j : Fin (k + 1), fib ((Submission.BoseGases.kcInsN k i q) j)) = fib q.1 + C q.2 := by
    intro q
    obtain ⟨t, r⟩ := q
    rw [Fin.sum_univ_succAbove (fun j : Fin (k + 1) =>
        fib ((Submission.BoseGases.kcInsN k i (t, r)) j)) i,
      Submission.BoseGases.kc_insN_apply_same, hCdef]
    congr 1
    exact Finset.sum_congr rfl (fun l _ => by
      rw [Submission.BoseGases.kc_insN_apply_succ])
  -- ### 4. a.e. identity of the two tube integrands
  have hAe : ∀ᵐ q ∂(((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ))).restrict T),
      q.1 ∈ A := by
    filter_upwards [MeasureTheory.ae_restrict_mem hTmeas] with q hq
    rwa [hTdef] at hq
  have key : ∀ᵐ q ∂(((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ))).restrict T),
      ‖Φ (Submission.BoseGases.kcInsN k i q) ^ 2 *
          ∑ j : Fin (k + 1), fib ((Submission.BoseGases.kcInsN k i q) j)‖ₑ
        = ENNReal.ofReal ((m q.2) ^ 2) * ENNReal.ofReal |fib q.1 + C q.2| := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae hflat, hAe] with q hq hAq
    rw [hsum q, hq hAq, Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
      ENNReal.ofReal_mul (sq_nonneg _)]
  have hT1 : (∫⁻ q in T, ‖Φ (Submission.BoseGases.kcInsN k i q) ^ 2 *
        ∑ j : Fin (k + 1), fib ((Submission.BoseGases.kcInsN k i q) j)‖ₑ
      ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ))))
      = ∫⁻ q in T, (ENNReal.ofReal ((m q.2) ^ 2) * ENNReal.ofReal |fib q.1 + C q.2|)
      ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ))) :=
    lintegral_congr_ae key
  -- ### 5. the tube integral as the box-projected form of `tubeLintegralFactor`
  have hT2 : (∫⁻ q in T, (ENNReal.ofReal ((m q.2) ^ 2) * ENNReal.ofReal |fib q.1 + C q.2|)
      ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ))))
      = ∫⁻ q, A.indicator (fun _ => (1 : ENNReal)) q.1
          * (ENNReal.ofReal ((m q.2) ^ 2) * ENNReal.ofReal |fib q.1 + C q.2|)
      ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ))) := by
    calc ∫⁻ q in T, (ENNReal.ofReal ((m q.2) ^ 2) * ENNReal.ofReal |fib q.1 + C q.2|)
          ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
            (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ)))
        = ∫⁻ q, T.indicator (fun q => ENNReal.ofReal ((m q.2) ^ 2)
              * ENNReal.ofReal |fib q.1 + C q.2|) q
          ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
            (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ))) :=
          (lintegral_indicator hTmeas _).symm
      _ = ∫⁻ q, A.indicator (fun _ => (1 : ENNReal)) q.1
            * (ENNReal.ofReal ((m q.2) ^ 2) * ENNReal.ofReal |fib q.1 + C q.2|)
          ∂((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
            (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ))) := by
          apply lintegral_congr
          intro q
          by_cases hqT : q ∈ T
          · have hmem : q.1 ∈ A := by rwa [hTdef] at hqT
            simp only [Set.indicator_of_mem hqT, Set.indicator_of_mem hmem, one_mul]
          · have hmem : q.1 ∉ A := by rwa [hTdef] at hqT
            simp only [Set.indicator_of_notMem hqT, Set.indicator_of_notMem hmem, zero_mul]
  -- ### 6. finiteness forces `m =ᵐ 0`
  have hm_fin : (∫⁻ r in Submission.BoseGases.abox k ℓ, ENNReal.ofReal ((m r) ^ 2) * ⊤) < ∞ := by
    rw [← tubeLintegralFactor (k := k) (ℓ := ℓ) (A := A) hA hAc hm_meas hC_meas hfibm htop,
      ← hT2, ← hT1]
    exact hTfin
  have hm_zero : m =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ)] 0 := by
    have hmmeas : Measurable (fun r : Submission.BoseGases.X k =>
        ENNReal.ofReal ((m r) ^ 2) * ⊤) :=
      (ENNReal.continuous_ofReal.measurable.comp (hm_meas.pow_const 2)).mul_const ⊤
    filter_upwards [MeasureTheory.ae_lt_top hmmeas (ne_of_lt hm_fin)] with r hr
    by_contra hne
    have hpos : ENNReal.ofReal ((m r) ^ 2) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]
      exact sq_pos_of_ne_zero hne
    rw [ENNReal.mul_top hpos] at hr
    exact absurd hr (lt_irrefl ⊤)
  -- ### 7. transfer back to the slot mean and use the box-constancy
  have hm_ae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ)),
      (1 / volA) * ∫ z in A, Φ (Submission.BoseGases.kcInsN k i (z, r)) = 0 := by
    have h := hm_zero
    rw [hmdef] at h
    exact h
  have hF := fibMeanAeZeroOfPeel (k := k) (ℓ := ℓ) (A := A) volA i hm_ae
  have h1 : (fun x : Submission.BoseGases.X (k + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (k + 1) ℓ)]
      (fun x => A.indicator (fun _ => (1 : ℝ)) (x i) *
        ((1 / volA) * ∫ z in A, Φ (Function.update x i z))) := by
    filter_upwards [hQae] with x hx
    have hx' : A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
        - ((1 / volA) * ∫ z in A, Φ (Function.update x i z)) *
          A.indicator (fun _ => (1 : ℝ)) (x i) = 0 := by
      simpa only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Pi.zero_apply] using hx
    ring_nf at hx' ⊢
    linarith
  exact h1.trans (by
    filter_upwards [hF] with x hx
    rw [hx]
    simp)

/-! ## 2. The degenerate flat fibre sum vanishes -/

theorem flatFibSumEqZero {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hQae : ∀ i : Fin n, Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i Φ
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0)
    (hint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * ∑ i : Fin n,
        ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
      (Submission.BoseGases.abox n ℓ))
    (hSa : (∫⁻ z in Submission.BoseGases.dlBox ℓ d u,
        ENNReal.ofReal |∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u z y|) = ⊤) :
    Work.BoseFixB1.flatFibSum h M ℓ d u Φ = 0 := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [show Work.BoseFixB1.flatFibSum h M ℓ d u Φ
        = ∫ x in Submission.BoseGases.abox 0 ℓ,
            (Φ x) ^ 2 * ∑ i : Fin 0, ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y from rfl]
    simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    -- a globally measurable representative of the fibre
    obtain ⟨fib', hfibm, hfib'eq⟩ := fibMeasurableRep h hM hℓ hd u
    -- rewrite the flat fibre sum with `fib'` in place of the (only a.e. measurable) fibre
    have hflat : Work.BoseFixB1.flatFibSum h M ℓ d u Φ
        = ∫ x in Submission.BoseGases.abox (k + 1) ℓ,
            (Φ x) ^ 2 * ∑ j : Fin (k + 1), fib' (x j) := by
      rw [show Work.BoseFixB1.flatFibSum h M ℓ d u Φ
          = ∫ x in Submission.BoseGases.abox (k + 1) ℓ,
              (Φ x) ^ 2 * ∑ i : Fin (k + 1), ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y from rfl]
      apply integral_congr_ae
      filter_upwards with x
      congr 1
      exact Finset.sum_congr rfl (fun i _ => (hfib'eq (x i)).symm)
    rw [hflat]
    -- integrability of the rewritten integrand
    have hint' : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X (k + 1) => (Φ x) ^ 2 * ∑ j : Fin (k + 1), fib' (x j))
        (Submission.BoseGases.abox (k + 1) ℓ) := by
      refine hint.congr (Filter.Eventually.of_forall (fun x => ?_))
      show Φ x ^ 2 * (∑ i : Fin (k + 1), ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
          = Φ x ^ 2 * ∑ j : Fin (k + 1), fib' (x j)
      congr 1
      exact Finset.sum_congr rfl (fun i _ => (hfib'eq (x i)).symm)
    have hfin : ∫⁻ x in Submission.BoseGases.abox (k + 1) ℓ,
        ‖Φ x ^ 2 * ∑ j : Fin (k + 1), fib' (x j)‖ₑ < ∞ := hint'.hasFiniteIntegral
    -- the box data
    have hAmeas : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
      Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
    have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
      Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
    have hfinA : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
        (Submission.BoseGases.dlBox ℓ d u) ≠ ⊤ :=
      ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u)
    -- the non-integrability of `fib'` on `A`
    have htop' : ∫⁻ z in Submission.BoseGases.dlBox ℓ d u, ENNReal.ofReal |fib' z| = ⊤ := by
      rw [show (fun z : EuclideanSpace ℝ (Fin 3) => ENNReal.ofReal |fib' z|)
          = (fun z => ENNReal.ofReal |∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u z y|) from funext (fun z => by
        rw [hfib'eq z])]
      exact hSa
    have htop : ∀ c : ℝ, ∫⁻ z in Submission.BoseGases.dlBox ℓ d u,
        ENNReal.ofReal |fib' z + c| = ⊤ := fun c =>
      lintegralAbsAddConstEqTop hAmeas hfinA hfibm htop' c
    -- per-slot vanishing
    have hslot : ∀ i : Fin (k + 1), ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox (k + 1) ℓ)),
        (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) * Φ x = 0 :=
      fun i => slotVanishes hAmeas hAc (Work.SmallBoxSliding.boxMass ℓ d u) i
        hΦc.measurable hfibm (hQae i) htop hfin
    have hAll := (Finset.eventually_all (Finset.univ : Finset (Fin (k + 1)))).mpr
      (fun i _ => hslot i)
    apply integral_eq_zero_of_ae
    filter_upwards [hAll] with x hx
    by_cases hx0 : Φ x = 0
    · rw [hx0]
      simp
    · have hsum0 : (∑ j : Fin (k + 1), fib' (x j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hxj : x j ∉ Submission.BoseGases.dlBox ℓ d u := by
          intro hj
          have h1 := hx j (Finset.mem_univ j)
          rw [Set.indicator_of_mem hj, one_mul] at h1
          exact hx0 h1
        rw [hfib'eq (x j)]
        have hz : ∀ y : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x j) y = 0 :=
          fun y => Work.BoseFixB1S.wSmall1Pair_eq_zero_of_notMem_left hM hℓ hd u y hxj
        simp [hz]
      rw [hsum0, mul_zero]
      simp

end Work.BoseFixB1S.FlatFib
