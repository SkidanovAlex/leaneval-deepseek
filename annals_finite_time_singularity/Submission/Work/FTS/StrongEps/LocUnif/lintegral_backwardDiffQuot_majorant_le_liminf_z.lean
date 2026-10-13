import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le
import Submission.Work.FTS.StrongEps.LocUnif.rho_bounds
import Submission.Work.FTS.StrongEps.LocUnif.tendsto_backward_diffQuot
import Submission.Work.FTS.StrongEps.LocUnif.ae_shift_preimage_sub
import Submission.Work.FTS.StrongEps.LocUnif.backwardDiffQuot_ioo_ae
import Submission.Work.FTS.StrongEps.LocUnif.aemeasurable_deriv_slice_of_contDiffOn
import Submission.Work.FTS.StrongEps.LocUnif.exists_scaling_const_seq
import Submission.Work.FTS.StrongEps.LocUnif.aemeasurable_comp_sub_of_aemeasurable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The majorant bound for the backward difference quotient of `W` (z-direction)

The `z`-direction instance of the assembly of
`Submission/Work/FTS/StrongEps/LocUnif/NOTES_assembly_final.md`, item 2: if `W` is the a.e.
pointwise limit of a family `V n` that is `C^1` in `z` on the open rectangle, and `ρ` is a
positive continuous weight on the closed rectangle, then the weighted `L²`-norm of the backward
difference quotients of `W` over the inner rectangle is bounded by the `liminf` of the weighted
`L²`-norms of the `z`-derivatives of `V n` over the outer rectangle — with no loss of constant
(the weight is compared inside the sliding window, where it converges to itself).

The proof applies Fatou's lemma three times: once to exchange the outer `liminf` over `j` with the
integral, once to pass from the difference quotients of `W` to those of `V n` (pointwise a.e.
convergence), and once to bound each difference quotient of `V n` by the mean of `∂_z V n` over
the sliding window (fundamental theorem of calculus plus Cauchy–Schwarz).  The finitely many
indices with `1/(j+1) ≥ a' - a`, for which the window would leave the outer rectangle, are
discarded at the start.
-/

noncomputable section

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 1000000

/-! ## Helper lemmas. -/

/-- For a box `[c,d]`, almost every point of it lies in the open interval `(c,d)`. -/
theorem lz_ae_mem_Ioo {c d : ℝ} :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc c d)), θ ∈ Set.Ioo c d := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  refine measure_mono_null (t := ({c} ∪ {d} : Set ℝ)) (fun θ hθ => ?_) ?_
  swap
  · rw [measure_union_null_iff]
    exact ⟨measure_singleton c, measure_singleton d⟩
  have h1 : θ ∈ Set.Icc c d := by
    by_contra h
    exact hθ fun hh => absurd hh h
  have h2 : θ ∉ Set.Ioo c d := fun hh => hθ fun _ => hh
  simp only [Set.mem_Icc] at h1
  simp only [Set.mem_Ioo] at h2
  simp only [Set.mem_union, Set.mem_singleton_iff]
  rcases lt_or_eq_of_le h1.1 with h | h
  · right
    by_contra hne
    exact h2 ⟨h, lt_of_le_of_ne h1.2 hne⟩
  · left; exact h.symm

/-- The `z`-slice of a function that is `C¹` on the open rectangle is `C¹`. -/
theorem lz_slice_sm {a b c d : ℝ} {u : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 (Function.uncurry u) (Set.Ioo a b ×ˢ Set.Ioo c d)) :
    ∀ θ ∈ Set.Ioo c d, ContDiffOn ℝ 1 (fun z => u z θ) (Set.Ioo a b) := by
  intro θ hθ
  have hlin : ContDiffOn ℝ 1 (fun z : ℝ => (z, θ)) (Set.Ioo a b) := by
    have h1 : ContDiff ℝ 1 (fun z : ℝ => (z, θ)) := by fun_prop
    exact h1.contDiffOn
  exact hsm.comp hlin (fun z hz => ⟨hz, hθ⟩)

/-- Restrictions of a.e. measurability to a smaller set. -/
theorem lz_aemeasurable_restrict_of_subset {A B : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hAB : A ⊆ B) (hf : AEMeasurable f (MeasureTheory.volume.restrict B)) :
    AEMeasurable f (MeasureTheory.volume.restrict A) := by
  obtain ⟨g, hgm, hgae⟩ := hf
  exact ⟨g, hgm, (MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hAB le_rfl)) hgae⟩

theorem lintegral_backwardDiffQuot_majorant_le_liminf_z {a a' b' b c d : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hcd : c < d)
    {ι : Type*} [Fintype ι] {ρ : ι → ℝ → ℝ → ℝ}
    (hρc : ∀ k, ContinuousOn (Function.uncurry (ρ k)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hρp : ∀ k, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < ρ k z θ)
    {V : ℕ → ι → ℝ → ℝ → ℝ} {W : ι → ℝ → ℝ → ℝ}
    (hVsm : ∀ n k, ContDiffOn ℝ 1 (Function.uncurry (V n k)) (Set.Ioo a b ×ˢ Set.Ioo c d))
    (hVc : ∀ n k, ContinuousOn (Function.uncurry (V n k)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hWmeas : ∀ k, MeasureTheory.AEStronglyMeasurable (Function.uncurry (W k))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hconv : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)), ∀ k,
      Filter.Tendsto (fun n => V n k p.1 p.2) Filter.atTop (nhds (W k p.1 p.2))) :
    ∫⁻ p in (Set.Icc a' b' ×ˢ Set.Icc c d),
        Filter.liminf (fun j : ℕ => ∑ k, ENNReal.ofReal
          (((W k p.1 p.2 - W k (p.1 - 1 / ((j : ℝ) + 1)) p.2) * ((j : ℝ) + 1)
            * ρ k p.1 p.2) ^ 2)) Filter.atTop
      ≤ Filter.liminf (fun n : ℕ => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d),
          ENNReal.ofReal (∑ k, (deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2))
          Filter.atTop := by
  classical
  set S : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d with hS
  set S' : Set (ℝ × ℝ) := Set.Icc a' b' ×ˢ Set.Icc c d with hS'
  have hSmeas : MeasurableSet S := by
    rw [hS]; exact measurableSet_Icc.prod measurableSet_Icc
  have hS'meas : MeasurableSet S' := by
    rw [hS']; exact measurableSet_Icc.prod measurableSet_Icc
  have hS'sub : S' ⊆ S := by
    rw [hS, hS']
    intro p hp
    simp only [Set.mem_prod, Set.mem_Icc] at hp ⊢
    exact ⟨⟨by linarith [hp.1.1, haa'], by linarith [hp.1.2, hb'b]⟩, hp.2⟩
  set hh : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hhh
  have hhpos : ∀ j, 0 < hh j := by intro j; rw [hhh]; positivity
  have hhtend : Tendsto hh Filter.atTop (nhds 0) := by
    rw [hhh]; simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  by_cases hne : Nonempty ι
  · by_cases hbox : a' ≤ b'
    swap
    · rw [hS', show (Set.Icc a' b' : Set ℝ) = ∅ from Set.Icc_eq_empty_iff.mpr hbox,
        Set.empty_prod]
      simp
    obtain ⟨C, hC1, hCratio, hCtend⟩ :=
        exists_scaling_const_seq (by linarith) hcd hne hρc hρp
    obtain ⟨J₀, hJ₀⟩ := Filter.eventually_atTop.mp
      (hhtend.eventually (Iio_mem_nhds (show (0 : ℝ) < a' - a by linarith)))
    set Y : ℕ → ℝ≥0∞ := fun n => ∫⁻ p in S,
      ENNReal.ofReal (∑ k, (deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2) with hY
    set L : ℝ≥0∞ := Filter.liminf Y Filter.atTop with hL
    set Aw : ℕ → ℝ × ℝ → ℝ≥0∞ := fun j' p => ∑ k, ENNReal.ofReal
      (((W k p.1 p.2 - W k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2) with hAw
    set Av : ℕ → ℕ → ℝ × ℝ → ℝ≥0∞ := fun j' n p => ∑ k, ENNReal.ofReal
      (((V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2) with hAv
    -- ### 0. basic facts
    have hshift : ∀ j' ≥ J₀, ∀ p, p ∈ S' → (p.1 - hh j', p.2) ∈ S := by
      intro j' hj' p hp
      simp only [hS, hS'] at hp ⊢
      simp only [Set.mem_prod, Set.mem_Icc] at hp ⊢
      exact ⟨⟨by linarith [hp.1.1, hJ₀ j' hj'], by linarith [hp.1.2, hhpos j']⟩, hp.2⟩
    have hhu : ∀ j' ≥ J₀, hh j' ≤ a' - a := fun j' hj' => le_of_lt (hJ₀ j' hj')
    -- ### 1. slice smoothness in `θ` (a.e.)
    have hslice : ∀ n k, ∀ θ ∈ Set.Ioo c d,
        ContDiffOn ℝ 1 (fun z => V n k z θ) (Set.Ioo a b) :=
      fun n k => lz_slice_sm (hVsm n k)
    have hu_sm : ∀ n k, ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc c d)),
        ContDiffOn ℝ 1 (fun z => V n k z θ) (Set.Ioo a b) :=
      fun n k => (lz_ae_mem_Ioo (c := c) (d := d)).mono fun θ hθ => hslice n k θ hθ
    -- ### 2. measurability of the `y`-integrands
    have hYsum : ∀ n k, AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2))
        (MeasureTheory.volume.restrict S) := by
      intro n k
      refine (aemeasurable_deriv_slice_of_contDiffOn (hVsm n k) (hρc k)).congr ?_
      filter_upwards with p
      congr 1
      ring
    have hY_eq : ∀ n, Y n = ∑ k, ∫⁻ p in S,
        ENNReal.ofReal ((deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2) := by
      intro n
      have h1 : Y n = ∫⁻ p in S, ∑ k,
          ENNReal.ofReal ((deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2) := by
        rw [hY]
        exact MeasureTheory.lintegral_congr
          (fun p => ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _))
      rw [h1]
      exact MeasureTheory.lintegral_finsetSum' Finset.univ fun k _ => hYsum n k
    -- ### 3. the left-hand side rewritten
    have hLHS : ∫⁻ p in S',
        Filter.liminf (fun j : ℕ => ∑ k, ENNReal.ofReal
          (((W k p.1 p.2 - W k (p.1 - 1 / ((j : ℝ) + 1)) p.2) * ((j : ℝ) + 1)
            * ρ k p.1 p.2) ^ 2)) Filter.atTop
        = ∫⁻ p in S', Filter.liminf (fun j => Aw j p) Filter.atTop := by
      refine lintegral_congr fun p => ?_
      refine Filter.liminf_congr (Filter.Eventually.of_forall fun j => ?_)
      rw [hAw]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hhh]
      have h1 : 1 / (1 / ((j : ℝ) + 1)) = (j : ℝ) + 1 := by simp only [one_div, inv_inv]
      rw [h1]
    -- ### 4. dropping the finitely many bad indices ``j < J₀``
    have hstep1 : ∫⁻ p in S', Filter.liminf (fun j => Aw j p) Filter.atTop
        ≤ ∫⁻ p in S', Filter.liminf (fun j => Aw (j + J₀) p) Filter.atTop := by
      refine lintegral_mono fun p => ?_
      rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
      refine iSup_le fun m => ?_
      refine le_trans ?_ (le_iSup (fun i => ⨅ j, ⨅ (_ : j ≥ i), Aw (j + J₀) p) m)
      refine le_iInf fun j => le_iInf fun hj => ?_
      exact (iInf_le (fun i => ⨅ (_ : i ≥ m), Aw i p) (j + J₀)).trans (iInf_le _ (by omega))
    -- ### 5. measurability of the `W`-integrands
    have hAw_sum : ∀ j' ≥ J₀, ∀ k, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (((W k p.1 p.2 - W k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2))
        (MeasureTheory.volume.restrict S') := by
      intro j' hj' k
      have hW1 : AEMeasurable (fun p : ℝ × ℝ => W k p.1 p.2)
          (MeasureTheory.volume.restrict S') :=
        lz_aemeasurable_restrict_of_subset hS'sub ((hWmeas k).aemeasurable)
      have hW2 : AEMeasurable (fun p : ℝ × ℝ => W k (p.1 - hh j') p.2)
          (MeasureTheory.volume.restrict S') :=
        aemeasurable_comp_sub_of_aemeasurable hSmeas hS'meas (hshift j' hj')
          (hWmeas k).aemeasurable
      have hρ' : AEMeasurable (fun p : ℝ × ℝ => ρ k p.1 p.2)
          (MeasureTheory.volume.restrict S') :=
        ((hρc k).mono hS'sub).aestronglyMeasurable hS'meas |>.aemeasurable
      have hnum : AEMeasurable (fun p : ℝ × ℝ =>
          (W k p.1 p.2 - W k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2)
          (MeasureTheory.volume.restrict S') :=
        ((hW1.sub hW2).mul aemeasurable_const).mul hρ'
      have hsq : AEMeasurable (fun p : ℝ × ℝ =>
          ((W k p.1 p.2 - W k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2)
          (MeasureTheory.volume.restrict S') :=
        hnum.pow (aemeasurable_const : AEMeasurable (fun _ : ℝ × ℝ => (2 : ℕ)) _)
      exact ENNReal.measurable_ofReal.comp_aemeasurable hsq
    have hAw_meas : ∀ j' ≥ J₀, AEMeasurable (Aw j')
        (MeasureTheory.volume.restrict S') := by
      intro j' hj'
      rw [hAw]
      refine (Finset.aemeasurable_sum Finset.univ (fun k _ => hAw_sum j' hj' k)).congr ?_
      filter_upwards with p
      simp only [Finset.sum_apply]
    have hstep2 : ∫⁻ p in S', Filter.liminf (fun j => Aw (j + J₀) p) Filter.atTop
        ≤ Filter.liminf (fun j => ∫⁻ p in S', Aw (j + J₀) p) Filter.atTop :=
      MeasureTheory.lintegral_liminf_le' fun j => hAw_meas (j + J₀) (by omega)
    -- ### 6. measurability of the `V`-integrands
    have hAv_sum : ∀ j' n k, j' ≥ J₀ → AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (((V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2))
        (MeasureTheory.volume.restrict S') := by
      intro j' n k hj'
      have hV1 : AEMeasurable (fun p : ℝ × ℝ => V n k p.1 p.2)
          (MeasureTheory.volume.restrict S') :=
        ((hVc n k).mono hS'sub).aestronglyMeasurable hS'meas |>.aemeasurable
      have hV2 : AEMeasurable (fun p : ℝ × ℝ => V n k (p.1 - hh j') p.2)
          (MeasureTheory.volume.restrict S') :=
        ((hVc n k).comp (((continuous_fst.sub continuous_const).prodMk continuous_snd).continuousOn)
          (hshift j' hj')).aestronglyMeasurable hS'meas |>.aemeasurable
      have hρ' : AEMeasurable (fun p : ℝ × ℝ => ρ k p.1 p.2)
          (MeasureTheory.volume.restrict S') :=
        ((hρc k).mono hS'sub).aestronglyMeasurable hS'meas |>.aemeasurable
      have hnum : AEMeasurable (fun p : ℝ × ℝ =>
          (V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2)
          (MeasureTheory.volume.restrict S') :=
        ((hV1.sub hV2).mul aemeasurable_const).mul hρ'
      have hsq : AEMeasurable (fun p : ℝ × ℝ =>
          ((V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2)
          (MeasureTheory.volume.restrict S') :=
        hnum.pow (aemeasurable_const : AEMeasurable (fun _ : ℝ × ℝ => (2 : ℕ)) _)
      exact ENNReal.measurable_ofReal.comp_aemeasurable hsq
    have hAv_meas : ∀ j' n, j' ≥ J₀ → AEMeasurable (Av j' n)
        (MeasureTheory.volume.restrict S') := by
      intro j' n hj'
      rw [hAv]
      refine (Finset.aemeasurable_sum Finset.univ (fun k _ => hAv_sum j' n k hj')).congr ?_
      filter_upwards with p
      simp only [Finset.sum_apply]
    -- ### 7. a.e. convergence and Fatou in `n`
    have hae_conv : ∀ j' ≥ J₀, ∀ᵐ p ∂(MeasureTheory.volume.restrict S'),
        ∀ k, (Tendsto (fun n => V n k p.1 p.2) Filter.atTop (nhds (W k p.1 p.2)) ∧
              Tendsto (fun n => V n k (p.1 - hh j') p.2) Filter.atTop
                (nhds (W k (p.1 - hh j') p.2))) := by
      intro j' hj'
      filter_upwards [MeasureTheory.ae_restrict_of_ae_restrict_of_subset hS'sub hconv,
        ae_shift_preimage_sub hSmeas hS'meas hconv (hshift j' hj')] with p hp1 hp2
      exact fun k => ⟨hp1 k, hp2 k⟩
    have hAw_eq : ∀ j' ≥ J₀, ∀ᵐ p ∂(MeasureTheory.volume.restrict S'),
        Aw j' p = Filter.liminf (fun n => Av j' n p) Filter.atTop := by
      intro j' hj'
      filter_upwards [hae_conv j' hj'] with p hp
      have hten : Tendsto (fun n => Av j' n p) Filter.atTop (nhds (Aw j' p)) := by
        rw [hAw, hAv]
        refine tendsto_finsetSum Finset.univ fun k _ => ?_
        have h1 : Tendsto (fun n => (V n k p.1 p.2 - V n k (p.1 - hh j') p.2)
            * (1 / hh j') * ρ k p.1 p.2) Filter.atTop
            (nhds ((W k p.1 p.2 - W k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2)) :=
          (((hp k).1.sub (hp k).2).mul_const (1 / hh j')).mul_const (ρ k p.1 p.2)
        exact ENNReal.tendsto_ofReal (h1.pow 2)
      exact hten.liminf_eq.symm
    have hFatou2 : ∀ j' ≥ J₀, ∫⁻ p in S', Aw j' p
        ≤ Filter.liminf (fun n => ∫⁻ p in S', Av j' n p) Filter.atTop := by
      intro j' hj'
      rw [MeasureTheory.lintegral_congr_ae (hAw_eq j' hj')]
      exact MeasureTheory.lintegral_liminf_le' fun n => hAv_meas j' n hj'
    -- ### 8. the per-`(j,n)` bound
    have hterm : ∀ j' ≥ J₀, ∀ n,
        ∫⁻ p in S', Av j' n p ≤ ENNReal.ofReal (C j') * Y n := by
      intro j' hj' n
      have hsplit : ∫⁻ p in S', Av j' n p = ∑ k, ∫⁻ p in S', ENNReal.ofReal
          (((V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2) := by
        rw [hAv]
        exact MeasureTheory.lintegral_finsetSum' Finset.univ fun k _ => hAv_sum j' n k hj'
      have hk : ∀ k, ∫⁻ p in S', ENNReal.ofReal
          (((V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal (C j') * ∫⁻ p in S,
              ENNReal.ofReal ((deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2) := by
        intro k
        refine (le_of_eq ?_).trans ((lz_diffQuot_backward_lintegral_le_ioo (a := a) (b := b)
          (a' := a') (b' := b') (c := c) (d := d) (h := hh j') (C := C j') (w := ρ k)
          (u := V n k)
          haa' hb'b (hhpos j') (hJ₀ j' hj') (hC1 j')
          (fun z hz θ hθ => hρp k z hz θ hθ)
          (fun z hz y hy θ hθ hzy => hCratio j' k z y θ hz hy hθ hzy)
          (hu_sm n k) (aemeasurable_deriv_slice_of_contDiffOn (hVsm n k) (hρc k))).trans
          (le_of_eq ?_))
        · refine lintegral_congr fun p => ?_
          congr 1
          ring
        · congr 1
          refine lintegral_congr fun p => ?_
          congr 1
          ring
      calc ∫⁻ p in S', Av j' n p
          = ∑ k, ∫⁻ p in S', ENNReal.ofReal
              (((V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2) :=
            hsplit
        _ ≤ ∑ k, ENNReal.ofReal (C j') * ∫⁻ p in S,
              ENNReal.ofReal ((deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2) :=
            Finset.sum_le_sum fun k _ => hk k
        _ = ENNReal.ofReal (C j') * ∑ k, ∫⁻ p in S,
              ENNReal.ofReal ((deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2) := by
            rw [Finset.mul_sum]
        _ = ENNReal.ofReal (C j') * Y n := by rw [← hY_eq n]
    -- ### 9. assembly
    have hA_le : ∀ j, ∫⁻ p in S', Aw (j + J₀) p ≤ ENNReal.ofReal (C (j + J₀)) * L := by
      intro j
      refine (hFatou2 (j + J₀) (by omega)).trans ?_
      have h1 : Filter.liminf (fun n => ∫⁻ p in S', Av (j + J₀) n p) Filter.atTop
          ≤ Filter.liminf (fun n => ENNReal.ofReal (C (j + J₀)) * Y n) Filter.atTop := by
        rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
        refine iSup_le fun m => ?_
        refine le_trans ?_ (le_iSup (fun m => ⨅ i, ⨅ (_ : i ≥ m),
          ENNReal.ofReal (C (j + J₀)) * Y i) m)
        refine le_iInf fun n => le_iInf fun hn => ?_
        exact (iInf_le (fun i => ⨅ (_ : i ≥ m), ∫⁻ p in S', Av (j + J₀) i p) n).trans
          ((iInf_le _ hn).trans (hterm (j + J₀) (by omega) n))
      have h2 : Filter.liminf (fun n => ENNReal.ofReal (C (j + J₀)) * Y n) Filter.atTop
          = ENNReal.ofReal (C (j + J₀)) * L := by
        rw [hL]
        exact ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top
      exact h1.trans (le_of_eq h2)
    have hstep3 : Filter.liminf (fun j => ∫⁻ p in S', Aw (j + J₀) p) Filter.atTop
        ≤ Filter.liminf (fun j => ENNReal.ofReal (C (j + J₀)) * L) Filter.atTop := by
      rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
      refine iSup_le fun m => ?_
      refine le_trans ?_ (le_iSup (fun i => ⨅ j, ⨅ (_ : j ≥ i),
        ENNReal.ofReal (C (j + J₀)) * L) m)
      refine le_iInf fun j => le_iInf fun hj => ?_
      exact (iInf_le (fun i => ⨅ (_ : i ≥ m), ∫⁻ p in S', Aw (i + J₀) p) j).trans
        ((iInf_le _ hj).trans (hA_le j))
    have hstep4 : Filter.liminf (fun j => ENNReal.ofReal (C (j + J₀)) * L) Filter.atTop = L := by
      have hctend : Tendsto (fun j => C (j + J₀)) Filter.atTop (nhds 1) :=
        hCtend.comp (tendsto_add_atTop_nat J₀)
      rcases eq_or_ne L ⊤ with hLtop | hLtop
      · rw [hLtop]
        have hconst : (fun j => ENNReal.ofReal (C (j + J₀)) * (⊤ : ℝ≥0∞)) = fun _ => ⊤ := by
          funext j
          exact ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by linarith [hC1 (j + J₀)]))
        rw [hconst, Filter.liminf_const]
      · have h2 : Tendsto (fun j => C (j + J₀) * L.toReal) Filter.atTop (nhds (1 * L.toReal)) :=
          hctend.mul_const L.toReal
        have h3 : Tendsto (fun j => ENNReal.ofReal (C (j + J₀)) * L) Filter.atTop (nhds L) := by
          have h4 := ENNReal.tendsto_ofReal h2
          rw [one_mul, ENNReal.ofReal_toReal hLtop] at h4
          refine h4.congr' ?_
          filter_upwards with j
          have hCpos : (0 : ℝ) ≤ C (j + J₀) := by linarith [hC1 (j + J₀)]
          rw [ENNReal.ofReal_mul hCpos, ENNReal.ofReal_toReal hLtop]
        rw [h3.liminf_eq]
    -- ### 10. the chain
    have hfinal : ∫⁻ p in S', Filter.liminf (fun j => Aw j p) Filter.atTop
        ≤ Filter.liminf (fun n => Y n) Filter.atTop :=
      calc ∫⁻ p in S', Filter.liminf (fun j => Aw j p) Filter.atTop
          ≤ ∫⁻ p in S', Filter.liminf (fun j => Aw (j + J₀) p) Filter.atTop := hstep1
        _ ≤ Filter.liminf (fun j => ∫⁻ p in S', Aw (j + J₀) p) Filter.atTop := hstep2
        _ ≤ Filter.liminf (fun j => ENNReal.ofReal (C (j + J₀)) * L) Filter.atTop := hstep3
        _ = L := hstep4
        _ = Filter.liminf (fun n => Y n) Filter.atTop := by rw [hL]
    rw [hLHS, hL]
    exact hfinal
  · haveI : IsEmpty ι := not_nonempty_iff.mp hne
    simp

end Work.FTS.StrongEps.LocUnif
