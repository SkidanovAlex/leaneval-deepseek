import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.XSpow_slotExact_compl_vanish
import Submission.Work.BoseBoxFock.aPC_congr_ae
import Submission.Work.BoseBoxFock.boxSlotSum_measurable_bounded
import Submission.Work.BoseBoxFock.integrableOn_aPC_aPC
import Submission.Work.BoseBoxFock.slotProj1_aPC_absorb_self
import Submission.Work.BoseBoxFock.slotProj_finsetSum_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aPC_slotProj1_absorb` — the box mean is absorbed by the slot projection

The sibling `slotProj1_aPC_absorb_self` proves `P_i ∘ Q_i = P_i` for the single-slot projections
(`aPC ℓ i` is the box mean in the slot `i`, `slotProj1 e i` the projection of that slot onto the
span of the modes).  The target of this module is the **transposed** statement

    `aPC ℓ i (slotProj1 e i Ψ) =ᵐ aPC ℓ i Ψ`   (full Lebesgue measure),

i.e. `Q_i ∘ P_i = P_i`.  Together with `slotProj1_aPC_absorb_self` (same slot) and
`aPC_slotProj1_comm_ne` (different slots) this gives the commutation of the box mean with every
*single-slot* projection, which — via the peel
`slotProj e (insert i U) = slotProj1 e i ∘ slotProj e U` and the Möbius form of `slotExact` —
yields the commutation of `aPC ℓ i` with the whole `S`-sector `slotExact e S`: inputs (comm) and
(contr) of `FINDING_sector_XSpow_le_s11.md` §1/§3.

**Landed here (proved, `sorry`-free):** the target `aPC_slotProj1_absorb` itself, together with
its two ingredients `slotProj1_ae_eq_congr` (insensitivity of `slotProj1` to null modifications)
and `aPC_slotProj1_absorb_bdd` (the identity for everywhere bounded measurable states), and the
*transposed resolution of the identity*, which is the analytic heart of the target,

* `integral_acube_PV_eq` — `∫_{y ∈ acube ℓ} PV e y w dy = conj (e 0 w) · (c · ℓ³)`;
* `integral_acube_PV_eq_indicator` — the same identity in the form `= 1_{w ∈ acube ℓ}` a.e.

**The proof (landed).**  Unfold the two slot integrals, swap them by Fubini (the integrand is
supported in `acube × boxL`, its a.e. strong measurability is obtained by pulling the modes back
along the quasi-measure-preserving projections `Prod.fst`/`Prod.snd` and integrating the majorant
`(Σ_l ‖e l y‖ ‖e l w‖) · C` with `Integrable.mul_prod`), apply the transposed resolution, and use
`c · conj (e 0 w) = (ℓ³)⁻¹` on the cube.  The `L^∞` hypothesis is handled by the representative
trick (`exists_bdd_sm_repr_aux` of `slotProj_finsetSum_ae`, `ae_aPC_congr_vol` of
`integrableOn_aPC_aPC`, and `slotProj1_ae_eq_congr` from `prod_update_preimage_null'`).

**Trap.**  Do not add a continuity hypothesis on the modes: the consumer has only `hbdd`/`hsupp`,
and `slotProj_singleton_eq_slotProj1` (the existing identification `slotProj1 e i = slotProj e {i}`)
needs `Continuous`/`HasCompactSupport`, so it is **not** usable here.
-/

noncomputable section

open MeasureTheory
open Submission.BoseGases
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. A supported `L^∞` mode is integrable -/

/-- **A bounded function supported in the cube is integrable there** (`ℓ > 0`). -/
lemma integrable_mul_const_of_support_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {f : Sp → ℂ}
    (hf : MemLp f ⊤) (hfs : Function.support f ⊆ acube ℓ) (c : ℂ) :
    Integrable (fun y : Sp => f y * c) := by
  classical
  obtain ⟨M, hM0, hM⟩ := exists_ae_bound_of_memLp_top_aux hf
  refine Integrable.mono' (g := (acube ℓ).indicator (fun _ => M * ‖c‖)) ?_ ?_ ?_
  · refine (integrable_indicator_iff (acube_measurable ℓ)).mpr ?_
    exact integrableOn_const (acube_lt_top ℓ hℓ.le).ne
  · exact hf.aestronglyMeasurable.mul_const c
  · filter_upwards [hM] with y hy
    by_cases hys : y ∈ acube ℓ
    · rw [Set.indicator_of_mem hys, norm_mul]
      exact mul_le_mul hy (le_refl ‖c‖) (norm_nonneg _) hM0
    · rw [Set.indicator_of_notMem hys]
      have hz : f y = 0 := Function.notMem_support.mp (fun hmem => hys (hfs hmem))
      rw [hz, zero_mul, norm_zero]

/-! ## 2. The transposed resolution of the identity -/

/-- **The transposed resolution of the identity**: integrating the slot kernel in its *first*
argument returns the conjugate of the condensate mode times `c·ℓ³`
(`= ∫_{acube} Σ_l e l y · conj (e l w) dy`, collapsed with `integral_mode_acube`). -/
lemma integral_acube_PV_eq (ℓ : ℝ) (hℓ : 0 < ℓ) {m : ℕ} [NeZero m]
    {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {c : ℂ} (hcstar : star c * c = (ℓ ^ 3)⁻¹)
    (hcae : ∀ᵐ x ∂(volume : Measure Sp),
      e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    (w : Sp) :
    (∫ y in acube ℓ, PV e y w) = star (e 0 w) * (c * (((ℓ ^ 3 : ℝ)) : ℂ)) := by
  have hsupp' : ∀ l, Function.support (e l) ⊆ acube ℓ := by
    intro l
    rw [← boxL_eq_acube_of_pos hℓ]
    exact hsupp l
  have hint : ∀ l : Fin m, IntegrableOn (fun y : Sp => e l y * (starRingEnd ℂ) (e l w))
      (acube ℓ) := by
    intro l
    exact (integrable_mul_const_of_support_acube hℓ (hbdd l) (hsupp' l) _).integrableOn
  simp only [PV]
  have hswap : (∫ y in acube ℓ, ∑ l : Fin m, e l y * star (e l w))
      = ∑ l : Fin m, ∫ y in acube ℓ, e l y * star (e l w) :=
    MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun l : Fin m => fun y : Sp => e l y * star (e l w))
      (fun l _ => hint l)
  rw [hswap]
  have hcstar' : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ := by
    rwa [starRingEnd_apply]
  have hterm : ∀ l : Fin m, (∫ y in acube ℓ, e l y * star (e l w))
      = (if l = 0 then c * (((ℓ ^ 3 : ℝ)) : ℂ) else 0) * star (e l w) := by
    intro l
    rw [MeasureTheory.integral_mul_const,
      integral_mode_acube hℓ he hsupp hcae hcstar' l]
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  rw [Finset.sum_eq_single 0]
  · simp [mul_comm]
  · intro l _ hl
    rw [if_neg hl]
    simp
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin m)) h

/-- **The transposed resolution in indicator form**: a.e. in `w`, the first-argument integral of
the slot kernel is the indicator of the cube (the pinning `e 0 = c·θ_Λ` with `c·conj c = ℓ⁻³`). -/
lemma integral_acube_PV_eq_indicator (ℓ : ℝ) (hℓ : 0 < ℓ) {m : ℕ} [NeZero m]
    {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : Measure Sp), e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x)) :
    ∀ᵐ w ∂(volume : Measure Sp),
      (∫ y in acube ℓ, PV e y w) = (acube ℓ).indicator (fun _ => (1 : ℂ)) w := by
  classical
  obtain ⟨c, hcstar, hcae⟩ := hc
  have hcstarS : star c * c = ((((ℓ ^ 3 : ℝ))⁻¹ : ℝ) : ℂ) := by
    simpa only [starRingEnd_apply] using hcstar
  have hboxL : Work.BoseK15.corpusBox.boxL ℓ = acube ℓ := boxL_eq_acube_of_pos hℓ
  have hℓ3 : (((ℓ ^ 3 : ℝ)) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    exact pow_ne_zero 3 (ne_of_gt hℓ)
  have hpin : ∀ᵐ w ∂(volume : Measure Sp), w ∈ acube ℓ → e 0 w = c := by
    filter_upwards [hcae] with w hw hwmem
    rw [hw, thetaFun_eq_indicator hℓ, Set.indicator_of_mem hwmem, mul_one]
  have hout : ∀ᵐ w ∂(volume : Measure Sp), w ∉ acube ℓ → e 0 w = 0 := by
    filter_upwards with w hw
    by_contra hne
    exact hw (by rw [← hboxL]; exact hsupp 0 (Function.mem_support.mpr hne))
  filter_upwards [hpin, hout] with w hw1 hw2
  rw [integral_acube_PV_eq ℓ hℓ he hbdd hsupp hcstarS hcae w]
  by_cases hw : w ∈ acube ℓ
  · rw [Set.indicator_of_mem hw, hw1 hw]
    have hkey : star c * (c * (((ℓ ^ 3 : ℝ)) : ℂ)) = 1 := by
      rw [← mul_assoc, hcstarS, ← Complex.ofReal_mul,
        inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), Complex.ofReal_one]
    exact hkey
  · rw [Set.indicator_of_notMem hw, hw2 hw]
    simp


/-! ## 3. The pointwise identity for everywhere bounded measurable states -/

/-- **The absorption identity for everywhere bounded measurable states.** -/
theorem aPC_slotProj1_absorb_bdd (ℓ : ℝ) (hℓ : 0 < ℓ) {m : ℕ} [NeZero m]
    {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : Measure Sp), e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    {N : ℕ} (i : Fin N) {g : X N → ℂ} (hgm : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    ∀ x : X N, aPC ℓ i (slotProj1 e i g) x = aPC ℓ i g x := by
  classical
  intro x
  obtain ⟨C, hC⟩ := hgb
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hC 0)
  have hsupp' : ∀ l, Function.support (e l) ⊆ acube ℓ := by
    intro l
    rw [← boxL_eq_acube_of_pos hℓ]
    exact hsupp l
  have hint : ∀ l : Fin m, Integrable (fun y : Sp => ‖e l y‖) (volume : Measure Sp) := by
    intro l
    simpa using (integrable_mul_const_of_support_acube hℓ (hbdd l) (hsupp' l) 1).norm
  set F : Sp → Sp → ℂ := fun y w => PV e y w * g (Function.update x i w) with hF
  -- (A) integrability of the joint integrand
  have hInt : Integrable (Function.uncurry F)
      (Measure.prod ((volume : Measure Sp).restrict (acube ℓ)) (volume : Measure Sp)) := by
    refine Integrable.mono' (g := fun p : Sp × Sp =>
        (∑ l : Fin m, ‖e l p.1‖ * ‖e l p.2‖) * C) ?_ ?_ ?_
    · refine (integrable_finsetSum (s := Finset.univ)
        (f := fun l : Fin m => fun p : Sp × Sp => ‖e l p.1‖ * ‖e l p.2‖) ?_).mul_const C
      intro l _
      exact ((hint l).mono_measure Measure.restrict_le_self).mul_prod (hint l)
    · have hPV : AEMeasurable (fun p : Sp × Sp => PV e p.1 p.2)
          (Measure.prod ((volume : Measure Sp).restrict (acube ℓ)) (volume : Measure Sp)) := by
        have hfst : ∀ l : Fin m, AEMeasurable (fun p : Sp × Sp => e l p.1)
            (Measure.prod ((volume : Measure Sp).restrict (acube ℓ)) (volume : Measure Sp)) :=
          fun l => (((hbdd l).aestronglyMeasurable.aemeasurable).mono_measure
              Measure.restrict_le_self).comp_quasiMeasurePreserving
            Measure.quasiMeasurePreserving_fst
        have hsnd : ∀ l : Fin m, AEMeasurable (fun p : Sp × Sp => star (e l p.2))
            (Measure.prod ((volume : Measure Sp).restrict (acube ℓ)) (volume : Measure Sp)) :=
          fun l => (((hbdd l).aestronglyMeasurable).star.aemeasurable).comp_quasiMeasurePreserving
            Measure.quasiMeasurePreserving_snd
        have h0 := Finset.aemeasurable_sum (s := Finset.univ)
          (f := fun l : Fin m => fun p : Sp × Sp => e l p.1 * star (e l p.2))
          (μ := Measure.prod ((volume : Measure Sp).restrict (acube ℓ)) (volume : Measure Sp))
          (fun l _ => (hfst l).mul (hsnd l))
        have hfun : (∑ i : Fin m, fun p : Sp × Sp => e i p.1 * star (e i p.2))
            = fun p : Sp × Sp => ∑ i : Fin m, e i p.1 * star (e i p.2) := by
          funext p
          rw [Finset.sum_apply]
        simpa only [PV, hfun] using h0
      have hupd : Measurable (fun p : Sp × Sp => Function.update x i p.2) :=
        (measurable_update_pair i).comp (measurable_const.prodMk measurable_snd)
      exact (aestronglyMeasurable_iff_aemeasurable).mpr
        (hPV.mul ((hgm.comp hupd).aemeasurable))
    · filter_upwards with p
      show ‖PV e p.1 p.2 * g (Function.update x i p.2)‖
          ≤ (∑ l : Fin m, ‖e l p.1‖ * ‖e l p.2‖) * C
      rw [norm_mul]
      refine mul_le_mul ?_ (hC _) (norm_nonneg _) ?_
      · rw [PV]
        calc ‖∑ l : Fin m, e l p.1 * star (e l p.2)‖
            ≤ ∑ l : Fin m, ‖e l p.1 * star (e l p.2)‖ := norm_sum_le _ _
          _ = ∑ l : Fin m, ‖e l p.1‖ * ‖e l p.2‖ := by simp
      · exact Finset.sum_nonneg (fun l _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- (B) the Fubini swap
  have hswap : (∫ y in acube ℓ, ∫ w, F y w) = ∫ w, ∫ y in acube ℓ, F y w := by
    rw [show (∫ y in acube ℓ, ∫ w, F y w)
        = ∫ y, ∫ w, F y w ∂(volume : Measure Sp) ∂((volume : Measure Sp).restrict (acube ℓ))
        from rfl]
    rw [MeasureTheory.integral_integral_swap hInt]
  -- (C) the computation
  calc aPC ℓ i (slotProj1 e i g) x
      = ((1 / ℓ ^ 3 : ℝ) : ℂ) * (∫ y in acube ℓ, ∫ w, F y w) := by
        show (((1 / ℓ ^ 3 : ℝ)) : ℂ) * (∫ y in acube ℓ, ∫ w : Sp,
            PV e (Function.update x i y i) w
              * g (Function.update (Function.update x i y) i w))
          = ((1 / ℓ ^ 3 : ℝ) : ℂ) * (∫ y in acube ℓ, ∫ w, F y w)
        congr 1
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        simp only [Function.update_self, Function.update_idem, hF]
    _ = ((1 / ℓ ^ 3 : ℝ) : ℂ) * (∫ w, ∫ y in acube ℓ, F y w) := by rw [hswap]
    _ = ((1 / ℓ ^ 3 : ℝ) : ℂ) *
          (∫ w, (∫ y in acube ℓ, PV e y w) * g (Function.update x i w)) := by
        congr 1
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
        show (∫ y in acube ℓ, F y w)
            = (∫ y in acube ℓ, PV e y w) * g (Function.update x i w)
        rw [MeasureTheory.integral_mul_const]
    _ = ((1 / ℓ ^ 3 : ℝ) : ℂ) *
          (∫ w, ((acube ℓ).indicator (fun _ => (1 : ℂ)) w) * g (Function.update x i w)) := by
        congr 1
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [integral_acube_PV_eq_indicator ℓ hℓ he hbdd hsupp hc] with w hw
        rw [hw]
    _ = aPC ℓ i g x := by
        have h2 : (∫ w, ((acube ℓ).indicator (fun _ => (1 : ℂ)) w) * g (Function.update x i w))
            = ∫ w in acube ℓ, g (Function.update x i w) := by
          rw [← MeasureTheory.integral_indicator (acube_measurable ℓ)]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
          by_cases hw : w ∈ acube ℓ <;> simp [hw]
        rw [h2, aPC]

/-! ## 4. Insensitivity of `slotProj1` to null modifications -/

/-- **`slotProj1 e i` is insensitive to null modifications of the state.** -/
lemma slotProj1_ae_eq_congr {m N : ℕ} (e : Fin m → Sp → ℂ) (i : Fin N)
    {f g : X N → ℂ} (h : f =ᵐ[(volume : Measure (X N))] g) :
    slotProj1 e i f =ᵐ[(volume : Measure (X N))] slotProj1 e i g := by
  have hbad : (volume : Measure (X N)) {x | ¬ (f x = g x)} = 0 := MeasureTheory.ae_iff.mp h
  obtain ⟨D, hDsub, hDm, hD0⟩ := exists_measurable_superset_of_null hbad
  have hpre := prod_update_preimage_null' i hDm hD0
  have hae : ∀ᵐ p ∂(Measure.prod (volume : Measure (X N)) (volume : Measure Sp)),
      f (Function.update p.1 i p.2) = g (Function.update p.1 i p.2) := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ hpre
    intro p hp
    exact hDsub hp
  have hiter := Measure.ae_ae_of_ae_prod hae
  filter_upwards [hiter] with x hx
  simp only [slotProj1]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hx] with w hw
  rw [hw]

/-! ## 5. The target -/

/-- **The box mean is absorbed by the single-slot projection**: `aPC ℓ i ∘ slotProj1 e i = aPC ℓ i`
for every `L^∞` state, a.e. for the Lebesgue measure on the configuration space. -/
theorem aPC_slotProj1_absorb (ℓ : ℝ) (hℓ : 0 < ℓ) {m : ℕ} [NeZero m]
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (he : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    {N : ℕ} (i : Fin N) {Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΨ : MeasureTheory.MemLp Ψ ⊤) :
    (fun x => Work.BoseBoxFock.aPC ℓ i (Work.BoseBoxFock.slotProj1 e i Ψ) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
          (Fin N → EuclideanSpace ℝ (Fin 3)))]
      (fun x => Work.BoseBoxFock.aPC ℓ i Ψ x) := by
  classical
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    obtain ⟨g, C, hC0, hCb, hgsm, hgeq⟩ :=
      exists_bdd_sm_repr_aux (volume : Measure (Fin (n + 1) → Sp)) hΨ
    have hpoint : aPC ℓ i (slotProj1 e i g) = aPC ℓ i g :=
      funext (aPC_slotProj1_absorb_bdd ℓ hℓ he hbdd hsupp hc i hgsm.measurable ⟨C, hCb⟩)
    have h1 : (fun x => aPC ℓ i (slotProj1 e i Ψ) x)
        =ᵐ[(volume : Measure (Fin (n + 1) → Sp))] (fun x => aPC ℓ i (slotProj1 e i g) x) :=
      ae_aPC_congr_vol i (slotProj1_ae_eq_congr e i hgeq)
    have h2 : (fun x => aPC ℓ i (slotProj1 e i g) x)
        =ᵐ[(volume : Measure (Fin (n + 1) → Sp))] (fun x => aPC ℓ i g x) :=
      Filter.Eventually.of_forall (fun x => congrFun hpoint x)
    have h3 : (fun x => aPC ℓ i g x)
        =ᵐ[(volume : Measure (Fin (n + 1) → Sp))] (fun x => aPC ℓ i Ψ x) :=
      ae_aPC_congr_vol i hgeq.symm
    exact h1.trans (h2.trans h3)

end Work.BoseBoxFock
