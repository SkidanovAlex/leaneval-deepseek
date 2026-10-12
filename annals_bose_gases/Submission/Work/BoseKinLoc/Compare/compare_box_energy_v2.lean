import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseKinLoc.Compare.CompareV2Aux
import Submission.Work.BoseKinLoc.Compare.ham_expansion_v2
import Submission.Work.BoseKinLoc.Compare.momForm_fibre_aemeasurable_v2
import Submission.Work.BoseKinLoc.Compare.neuFrac_fibre_aemeasurable_v2
import Submission.Work.BoseKinLoc.Compare.potential_fubini_v2
import Submission.Work.BoseKinLoc.Kinetic.gapBare_fibre_aemeasurable
import Submission.Work.BoseKinLoc.Kinetic.mainWord_fibre_aemeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Compare

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
/-- **The Neumann word along the slot-`i` lift fibres is a.e. strongly measurable.**

`Work.BoseKinLoc.neuWord ℓ d εT u ψ = ½εT(dℓ)⁻²·Work.BoseKinLoc.neuFrac ℓ ((dℓ)⁻²) u (Q_uψ)`.  The a.e. strong measurability of
the Neumann fraction along the lifted fibres is `Compare.Work.BoseKinLoc.Compare.neuFrac_fibre_aemeasurable_v2`; the
passage from the bare fibre to its mean-free part `Q_uψ` is the additive-constant invariance of
`neuFrac` (`NeuFrac.neuFrac_add_const_of_integrableSq`), legitimate because the lift fibre is
continuous and compactly supported, hence square-integrable. -/
private theorem neuWord_liftFib_aemeasurable {n : ℕ} {ℓ L d εT : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hL : 0 < L) {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1)) :
    AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuWord ℓ d εT p.1 (Work.BoseKinLoc.liftFib n i Φ p.2))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (volume : Measure (Submission.BoseGases.X n))) := by
  have hℓd : (0 : ℝ) < d * ℓ := mul_pos hd hℓ
  have hcsΦ : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset (Submission.BoseGases.abox_compact (n + 1) hL)
      (isClosed_tsupport Φ) hsupp
  have hnf : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) p.1
          (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN n i (z, p.2))))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (volume : Measure (Submission.BoseGases.X n))) :=
    Work.BoseKinLoc.Compare.neuFrac_fibre_aemeasurable_v2 (ℓ := ℓ) (a2 := (d * ℓ) ^ (-2 : ℤ)) hℓ
      (zpow_pos hℓd _) hΦ hcsΦ i
  refine ((hnf.const_mul ((1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ)))).congr
    (Filter.Eventually.of_forall fun p => ?_)
  have hψm : Measurable (Work.BoseKinLoc.liftFib n i Φ p.2) :=
    (Work.BoseKinLoc.liftFib_contDiff hΦ i p.2).continuous.measurable
  have hψ2 : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.liftFib n i Φ p.2 z) ^ 2) :=
    Continuous.integrable_of_hasCompactSupport
      ((Work.BoseKinLoc.liftFib_contDiff hΦ i p.2).continuous.pow 2)
      ((Work.BoseKinLoc.liftFib_hasCompactSupport hL hsupp i p.2).comp_left (g := fun t : ℝ => t ^ 2)
        (by norm_num))
  have hbr := NeuFrac.neuFrac_add_const_of_integrableSq (ℓ := ℓ) (a2 := (d * ℓ) ^ (-2 : ℤ))
    (zpow_pos hℓd _) p.1 (Work.BoseKinLoc.liftFib n i Φ p.2)
    (-(Work.BSKinetic.bsMean ℓ p.1 (Work.BoseKinLoc.liftFib n i Φ p.2))) hψm hψ2
  simp only [Work.BoseKinLoc.neuWord]
  rw [show Work.BoseKinLoc.Qfree ℓ p.1 (Work.BoseKinLoc.liftFib n i Φ p.2)
        = (fun z : EuclideanSpace ℝ (Fin 3) =>
            Work.BoseKinLoc.liftFib n i Φ p.2 z
              + (-(Work.BSKinetic.bsMean ℓ p.1 (Work.BoseKinLoc.liftFib n i Φ p.2)))) from by
      funext z
      simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, sub_eq_add_neg],
    hbr]

/-- **FS `thm:CompareBoxEnergy` at finite volume** (the node-C headline at the decoupled
parameters).  The proof is the chain

`((L+ℓ)/ℓ)³·min 0 E_Λ(μ)·‖Φ‖² ≤ ∫_{u∈𝒰} ⟨Φ,H_{Λ(u)}(μ)Φ⟩
   = ∫_u Σᵢ𝒯_u^{(i)}(Φ) + ∫_u∫_x Φ²·(potential) ≤ ⟨Φ,𝓗 N v Φ⟩_{Ω} − μN(∫g)‖Φ‖²`,

where `𝒰 = coverBoxU ℓ L` is the support-adapted localisation region (volume `(L+ℓ)³/ℓ³`),
the first inequality is the fibre bound `hfib`, the middle identity is the peel
`slotForm_eq_fibre_integral` together with the potential Fubini, and the last inequality is the
kinetic localisation `hkin` (with `hIBP` rewriting the kinetic energy as `⟨Φ,−ΔᵢΦ⟩`). -/
theorem compare_box_energy_v2 {N : ℕ} {v g : ℝ³ → ℝ} {ℓ L μ d s εT b c₀ : ℝ}
    (Φ : Submission.BoseGases.X N → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsym : Submission.BoseGases.PermInvariant N Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L)
    (hℓ : 0 < ℓ) (hL : ℓ ≤ L) (hreg : Work.BoseKinLoc.KinRegime c₀ ℓ d s εT b)
    (hkin : (∫ u : ℝ³, Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)
        ≤ ∑ i : Fin N, ∫ x : Submission.BoseGases.X N, ∑ k : Fin 3,
            (fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2)
    (hfib : ∀ u : ℝ³,
        min 0 (Work.BoseKinLoc.EΛ v g ℓ μ d s εT b) *
            (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2)
          ≤ Work.BoseKinLoc.boxForm N v g ℓ μ d s εT b u Φ)
    (hpot : ∀ x : Submission.BoseGases.X N,
      (∫ u : ℝ³, Work.BoseKinLoc.potWordU N v g ℓ μ u x)
        = -μ * (N : ℝ) * (∫ y : ℝ³, g y)
          + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2))
    (hswap : MeasureTheory.Integrable (fun p : ℝ³ × Submission.BoseGases.X N =>
      (Φ p.2) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ p.1 p.2))
    (hvol : MeasureTheory.volume (Work.BoseKinLoc.coverU ℓ L) =
      ENNReal.ofReal ((L + ℓ) ^ 3 / ℓ ^ 3))
    (hIBP : (∑ i : Fin N, ∫ x : Submission.BoseGases.X N, ∑ k : Fin 3,
        (fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2)
      = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N L, (Φ x) *
          (- BoseGases.partialLaplacian i Φ x)) :
    ((L + ℓ) / ℓ) ^ 3 * min 0 (Work.BoseKinLoc.EΛ v g ℓ μ d s εT b) *
        (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2)
      ≤ (∫ x in Submission.BoseGases.abox N L, (Φ x) * (BoseGases.𝓗 N v Φ x))
        - μ * (N : ℝ) * (∫ y : ℝ³, g y) *
            (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2) := by
  classical
  -- ## 0. Basic facts
  have hLpos : 0 < L := lt_of_lt_of_le hℓ hL
  have hL0 : 0 ≤ L := le_of_lt hLpos
  have hcsΦ : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset (Submission.BoseGases.abox_compact N hLpos)
      (isClosed_tsupport Φ) hsupp
  have hΦ2 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => (Φ x) ^ 2) := by
    have hcont : Continuous (fun x : Submission.BoseGases.X N => (Φ x) ^ 2) := by fun_prop
    exact hcont.integrable_of_hasCompactSupport
      (hcsΦ.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
  have hΦzero : ∀ x : Submission.BoseGases.X N, x ∉ Submission.BoseGases.abox N L → Φ x = 0 :=
    fun x hx => by
      by_contra hne
      exact hx (support_subset_abox hsupp (by simpa [Function.mem_support] using hne))
  -- ## 1. The potential term: Fubini + FS `lem:LocPotential`
  obtain ⟨hIntV, hFub⟩ := potential_fubini_v2 (ℓ := ℓ) (μ := μ) hΦ2 hswap hpot
  -- ## 2. The Hamiltonian expansion
  have hHam := ham_expansion_v2 (L := L) hΦ hsupp hIntV
  -- ## 3. Restricted integrals of box-supported integrands
  have hVeq : (∫ x in Submission.BoseGases.abox N L, (Φ x) ^ 2 *
        (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)))
      = ∫ x : Submission.BoseGases.X N, (Φ x) ^ 2 *
        (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)) :=
    Work.BoseKinLoc.setIntegral_eq_integral_of_eq_zero_off (Submission.BoseGases.abox_measurable N L)
      (fun x hx => by rw [hΦzero x hx]; ring)
  have hKeq : (∫ x in Submission.BoseGases.abox N L, (Φ x) ^ 2)
      = ∫ x : Submission.BoseGases.X N, (Φ x) ^ 2 :=
    Work.BoseKinLoc.setIntegral_eq_integral_of_eq_zero_off (Submission.BoseGases.abox_measurable N L)
      (fun x hx => by rw [hΦzero x hx]; ring)
  -- ## 4. The right-hand side, split into its kinetic and potential parts
  have hRHS : (∫ x in Submission.BoseGases.abox N L, (Φ x) * (BoseGases.𝓗 N v Φ x))
        - μ * (N : ℝ) * (∫ y : ℝ³, g y) * (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2)
      = (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N L, (Φ x) *
            (- BoseGases.partialLaplacian i Φ x))
        + (∫ u : ℝ³, ∫ x : Submission.BoseGases.X N,
            (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x) := by
    rw [hHam, hVeq, hFub]
    ring
  -- ## 5. Integrability over the cover
  have hQint : MeasureTheory.Integrable (fun u : ℝ³ =>
      ∫ x : Submission.BoseGases.X N, (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x) :=
    hswap.integral_prod_left
  have hcover_meas : MeasurableSet (coverBoxU ℓ L) := measurableSet_coverBoxU hℓ hL0
  have hcover_fin : (volume : Measure (ℝ³)) (coverBoxU ℓ L) ≠ ⊤ := by
    rw [volume_coverBoxU hℓ hL0]
    exact ENNReal.ofReal_ne_top
  -- the kinetic word is integrable (uniformly bounded on a compactly supported region)
  have hLint : MeasureTheory.Integrable (fun u : ℝ³ => Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ) := by
    rcases N with _ | n
    · simp [Work.BoseKinLoc.kinForm]
    have hd : 0 < d := hreg.2.1
    obtain ⟨C, hC0, hCbd⟩ := Work.BoseKinLoc.Kinetic.fsT_bound_abs (ℓ := ℓ) (d := d) (s := s)
      (εT := εT) (b := b) hℓ hd
      (fun u ψ hψ hcsψ => Work.BoseKinLoc.Kinetic.momForm_le_box hℓ hd u hψ hcsψ)
    -- joint a.e. strong measurability of the uncurried kinetic word
    have hmeas : ∀ i : Fin (n + 1), AEStronglyMeasurable
        (fun p : ℝ³ × Submission.BoseGases.X n =>
          Work.BoseKinLoc.fsT ℓ d s εT b p.1 (liftFib n i Φ p.2))
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) := by
      intro i
      have h1 : AEStronglyMeasurable
          (fun p : ℝ³ × Submission.BoseGases.X n =>
            Work.BoseKinLoc.neuWord ℓ d εT p.1 (liftFib n i Φ p.2)) _ :=
        neuWord_liftFib_aemeasurable (ℓ := ℓ) (d := d) (εT := εT) hℓ hd hLpos hΦ hsupp i
      have h2 : AEStronglyMeasurable
          (fun p : ℝ³ × Submission.BoseGases.X n =>
            Work.BoseKinLoc.gapWord ℓ b p.1 (liftFib n i Φ p.2)) _ :=
        ((Work.BoseKinLoc.Kinetic.gapBare_fibre_aemeasurable (ℓ := ℓ) hΦ i).const_mul
          (b * ℓ ^ (-2 : ℤ))).congr (Filter.Eventually.of_forall fun p => by
            simp only [Work.BoseKinLoc.gapWord])
      have h3 : AEStronglyMeasurable
          (fun p : ℝ³ × Submission.BoseGases.X n =>
            Work.BoseKinLoc.momWord ℓ d εT b p.1 (liftFib n i Φ p.2)) _ :=
        ((momForm_fibre_aemeasurable_v2 (ℓ := ℓ) (d := d) hΦ i).const_mul
          (b * εT * (d * ℓ) ^ (-2 : ℤ))).congr (Filter.Eventually.of_forall fun p => by
            simp only [Work.BoseKinLoc.momWord])
      have h4 : AEStronglyMeasurable
          (fun p : ℝ³ × Submission.BoseGases.X n =>
            Work.BoseKinLoc.mainWord ℓ d s εT p.1 (liftFib n i Φ p.2)) _ :=
        Work.BoseKinLoc.Kinetic.mainWord_fibre_aemeasurable (ℓ := ℓ) (d := d) (s := s)
          (εT := εT) hΦ i
      refine (((h1.add h2).add h3).add h4).congr (Filter.Eventually.of_forall fun p => ?_)
      exact (Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b p.1 (liftFib n i Φ p.2)).symm
    -- joint integrability from the uniform bound
    have hFint : ∀ i : Fin (n + 1), MeasureTheory.Integrable
        (fun p : ℝ³ × Submission.BoseGases.X n =>
          Work.BoseKinLoc.fsT ℓ d s εT b p.1 (liftFib n i Φ p.2))
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) := by
      intro i
      have hind : MeasureTheory.Integrable (fun u : ℝ³ =>
          (coverBoxU ℓ L).indicator (fun _ => (1 : ℝ)) u) := by
        rw [integrable_indicator_iff hcover_meas]
        exact integrableOn_const hcover_fin
      have hMi : MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
          (∫ z : ℝ³, (liftFib n i Φ r z) ^ 2)
            + Work.BSKinetic.dSpace (liftFib n i Φ r)) :=
        Work.BoseKinLoc.integrable_liftFib_H1 hΦ hcsΦ i
      refine (hind.mul_prod (hMi.const_mul C)).mono' (hmeas i)
        (Filter.Eventually.of_forall fun p => ?_)
      obtain ⟨u, r⟩ := p
      by_cases hu : u ∈ coverBoxU ℓ L
      · rw [Set.indicator_of_mem hu, one_mul]
        have h := hCbd u (liftFib n i Φ r) (Work.BoseKinLoc.liftFib_contDiff hΦ i r)
          (Work.BoseKinLoc.liftFib_hasCompactSupport hLpos hsupp i r)
        simpa only [Real.norm_eq_abs, Work.BSKinetic.dSpace] using h
      · rw [Set.indicator_of_notMem hu, zero_mul]
        rw [Work.BoseKinLoc.fsT_liftFib_eq_zero_of_not_mem_coverBoxU hℓ hsupp i r hu, norm_zero]
    -- each slot form is integrable, and so is their sum
    have hLi : ∀ i : Fin (n + 1), MeasureTheory.Integrable (fun u : ℝ³ =>
        Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ) := by
      intro i
      refine (hFint i).integral_prod_left.congr (Filter.Eventually.of_forall fun u => ?_)
      exact (Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral hℓ
        (Work.BoseKinLoc.fsT ℓ d s εT b u) u i Φ).symm
    have hsum : MeasureTheory.Integrable (fun u : ℝ³ =>
        ∑ i : Fin (n + 1), Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u)
          ℓ u i Φ) := by
      have hstep : ∀ t : Finset (Fin (n + 1)), MeasureTheory.Integrable (fun u : ℝ³ =>
          ∑ i ∈ t, Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u)
            ℓ u i Φ) := by
        intro t
        induction t using Finset.induction_on with
        | empty => simpa using (integrable_zero (μ := volume) (f := fun _ : ℝ³ => (0 : ℝ)))
        | insert a t ha ih =>
            have hgoal : (fun u : ℝ³ => ∑ i ∈ insert a t,
                  Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ)
                = (fun u : ℝ³ => Work.BoseKinLoc.slotForm (n + 1)
                    (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u a Φ)
                  + (fun u : ℝ³ => ∑ i ∈ t, Work.BoseKinLoc.slotForm (n + 1)
                      (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ) := by
              funext u
              rw [Finset.sum_insert ha]
              rfl
            rw [hgoal]
            exact (hLi a).add ih
      exact hstep Finset.univ
    refine hsum.congr (Filter.Eventually.of_forall fun u => ?_)
    exact (Work.BoseKinLoc.kinForm_eq (n + 1) ℓ d s εT b u Φ).symm
  have hLA : MeasureTheory.IntegrableOn (fun u : ℝ³ =>
      Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ) (coverBoxU ℓ L) := hLint.integrableOn
  have hQA : MeasureTheory.IntegrableOn (fun u : ℝ³ =>
      ∫ x : Submission.BoseGases.X N, (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x)
      (coverBoxU ℓ L) := hQint.integrableOn
  have hboxA : MeasureTheory.IntegrableOn (fun u : ℝ³ =>
      Work.BoseKinLoc.boxForm N v g ℓ μ d s εT b u Φ) (coverBoxU ℓ L) := by
    rw [show (fun u : ℝ³ => Work.BoseKinLoc.boxForm N v g ℓ μ d s εT b u Φ)
        = (fun u : ℝ³ => Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)
          + (fun u : ℝ³ => ∫ x : Submission.BoseGases.X N,
              (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x) from by
      funext u
      rfl]
    exact hLA.add hQA
  have hconstA : MeasureTheory.IntegrableOn (fun _ : ℝ³ =>
      min 0 (Work.BoseKinLoc.EΛ v g ℓ μ d s εT b) * (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2))
      (coverBoxU ℓ L) :=
    integrableOn_const hcover_fin
  -- the restricted integrals extend to the whole space
  have hLext : (∫ u in coverBoxU ℓ L, Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)
      = ∫ u : ℝ³, Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ :=
    Work.BoseKinLoc.setIntegral_eq_integral_of_eq_zero_off hcover_meas
      (fun u hu => kinForm_eq_zero_of_not_mem_coverBoxU hℓ hsupp hu)
  have hQext : (∫ u in coverBoxU ℓ L, ∫ x : Submission.BoseGases.X N,
        (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x)
      = ∫ u : ℝ³, ∫ x : Submission.BoseGases.X N,
        (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x := by
    refine Work.BoseKinLoc.setIntegral_eq_integral_of_eq_zero_off hcover_meas (fun u hu => ?_)
    rw [show (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x) = fun _ => (0 : ℝ) from by
      funext x
      by_cases hx : x ∈ Submission.BoseGases.abox N L
      · rw [potWordU_eq_zero_of_not_mem_coverBoxU hℓ hx hu, mul_zero]
      · rw [hΦzero x hx]; ring]
    simp
  -- ## 6. The chain
  calc ((L + ℓ) / ℓ) ^ 3 * min 0 (Work.BoseKinLoc.EΛ v g ℓ μ d s εT b) *
        (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2)
      = ∫ u in coverBoxU ℓ L, min 0 (Work.BoseKinLoc.EΛ v g ℓ μ d s εT b) *
          (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2) := by
        rw [setIntegral_const, MeasureTheory.Measure.real_def, volume_coverBoxU_toReal hℓ hL0,
          div_pow, smul_eq_mul]
        ring
    _ ≤ ∫ u in coverBoxU ℓ L, Work.BoseKinLoc.boxForm N v g ℓ μ d s εT b u Φ :=
        integral_mono hconstA hboxA fun u => hfib u
    _ = (∫ u in coverBoxU ℓ L, Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)
        + ∫ u in coverBoxU ℓ L, ∫ x : Submission.BoseGases.X N,
            (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x := by
        unfold Work.BoseKinLoc.boxForm
        exact integral_add hLA hQA
    _ = (∫ u : ℝ³, Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)
        + ∫ u : ℝ³, ∫ x : Submission.BoseGases.X N,
            (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x := by
        rw [hLext, hQext]
    _ ≤ (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N L, (Φ x) *
            (- BoseGases.partialLaplacian i Φ x))
        + ∫ u : ℝ³, ∫ x : Submission.BoseGases.X N,
            (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x := by
        exact (add_le_add_iff_right (∫ u : ℝ³, ∫ x : Submission.BoseGases.X N,
            (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x)).mpr
          (hkin.trans (le_of_eq hIBP))
    _ = (∫ x in Submission.BoseGases.abox N L, (Φ x) * (BoseGases.𝓗 N v Φ x))
        - μ * (N : ℝ) * (∫ y : ℝ³, g y) * (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2) :=
        hRHS.symm

end Work.BoseKinLoc.Compare
