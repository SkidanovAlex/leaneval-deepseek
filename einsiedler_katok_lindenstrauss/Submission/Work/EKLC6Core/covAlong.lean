import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLRelCross.per_t_covariance
import Submission.Work.EKLRelCross.covariance_bad_measurable
import Submission.Work.EKLRelCross.CovarianceDefs
import Submission.Work.EKLRelCross.ae_covariant_shape_all
import Submission.Work.EKLComp.prove_X3

/-!
# `Work.EKLC6Core.covAlong` — the `A`-covariance along a *single* diagonal element

The entropy chain of `EKLC6Core` (`Covariant`, `log_mass_conjBox_eq_sum`, `atomInfo_ae_eq_aux`,
..., `HcondSig_eq_growth_free`) takes the hypothesis

`hcov : ACovariant ν X''`   (`∀ t : Fin 3 → ℝ, ...`, EKL (4) / Pisa 7.16)

which in the frozen contract `P_Leafwise` is available (clause (U7)) only for `IsAInvariant μ`.
Every *use* of `hcov` in that chain is, however, at `t`, at `-t`, or at an integer multiple of
`t`.  This file supplies that weaker hypothesis:

* `ACovariantAlong ν t X''` — the covariance at `z • t` for every `z : ℤ`, pointwise on `X''`;
* `acovariantAlong_of_leafwise` — it holds on a conull measurable set for **any** probability `μ`
  preserved by the single map `x ↦ aDiag t • x` (no `IsAInvariant`!), the content being
  `Work.EKLRelCross.per_t_covariance` (Pisa 7.16/7.17) at each integer multiple;
* `per_t_covariance_mp` — the per-parameter statement with the two `MeasurePreserving`
  hypotheses that the proof of `per_t_covariance` actually uses.

Nothing here mentions entropy; it is the covariance input of the entropy chain, in the form
matching the hypotheses of `EKLC6Core.ent_le_HcondSig_of_phi_generated` (a single `t`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The pointwise `A`-covariance at the parameters `z • t`, `z : ℤ`, on the set `X''`: the
predicate `Work.EKLC6Core.ACovariant` weakened to the integer multiples of one direction. -/
def ACovariantAlong (ν : X3 → Measure SL3) (t : Fin 3 → ℝ) (X'' : Set X3) : Prop :=
  ∀ (z : ℤ) (x : X3), x ∈ X'' → aDiag ((z : ℝ) • t) • x ∈ X'' →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ν (aDiag ((z : ℝ) • t) • x) =
        c • (ν x).map
          (fun g : SL3 => aDiag ((z : ℝ) • t) * g * (aDiag ((z : ℝ) • t))⁻¹)

/-- The inverse diagonal action preserves `μ` whenever the diagonal action does. -/
theorem measurePreserving_aDiag_neg {μ : Measure X3} {s : Fin 3 → ℝ}
    (h : MeasurePreserving (fun x : X3 => aDiag s • x) μ μ) :
    MeasurePreserving (fun x : X3 => aDiag (-s) • x) μ μ := by
  refine ⟨(continuous_const_smul _).measurable, ?_⟩
  have hcomp : (fun x : X3 => aDiag (-s) • x) ∘ (fun x : X3 => aDiag s • x) = id := by
    funext x
    simp only [Function.comp_apply, id_eq]
    rw [aDiag_neg_smul]
  calc μ.map (fun x : X3 => aDiag (-s) • x)
      = (μ.map (fun x : X3 => aDiag s • x)).map (fun x : X3 => aDiag (-s) • x) := by
        rw [h.map_eq]
    _ = μ.map ((fun x : X3 => aDiag (-s) • x) ∘ (fun x : X3 => aDiag s • x)) := by
        rw [Measure.map_map (continuous_const_smul _).measurable
          (continuous_const_smul _).measurable]
    _ = μ.map id := by rw [hcomp]
    _ = μ := Measure.map_id

/-- **Pisa 7.16/7.17 at a single parameter.**  `Work.EKLRelCross.per_t_covariance` with the
`A`-invariance of `μ` replaced by the two `MeasurePreserving` hypotheses that its proof actually
uses: at the contraction direction `t0` and at the parameter `s`. -/
theorem per_t_covariance_mp_cov {U : Subgroup SL3} (hU : IsHoro U)
    {μ : Measure X3} [IsProbabilityMeasure μ]
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    (t0 : Fin 3 → ℝ)
    (ht0 : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1) (s : Fin 3 → ℝ)
    (hs : MeasurePreserving (fun x : X3 => aDiag s • x) μ μ) :
    ∀ᵐ x ∂μ, (x ∈ X' ∧ aDiag s • x ∈ X' ∧ (∀ u ∈ U, u • x = x → u = 1) ∧
      (∀ u ∈ U, u • (aDiag s • x) = aDiag s • x → u = 1)) →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
        ν (aDiag s • x) = c • (ν x).map (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹) := by
  have hfam : ∀ R : ℝ, 0 < R → ∃ (ι : Type) (_ : Countable ι) (Z : ι → Set X3)
      (mm : ι → MeasurableSpace X3) (G : ι → Set X3),
      (∀ i, IsPlaqueAlgebra U (Z i) (mm i)) ∧ (∀ i, MeasurableSet (G i)) ∧
      (∀ i, G i ⊆ Z i) ∧
      (∀ i, ∀ x ∈ G i, V R ∩ (U : Set SL3) ⊆ shape (mm i) U x) ∧
      μ (⋃ i, G i)ᶜ = 0 :=
    fun R hR => Work.EKLRelCross.flower_family Work.EKLComp.prove_X3 μ U hU t0 ht0 hcontr R hR
  filter_upwards [Work.EKLRelCross.ae_covPt_of_flower (U := U) hU hL hfree hfam s hs] with x hx _
  exact hx

end Work.EKLC6Core

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The covariance along all integer multiples of a single direction.**  For a probability `μ`
preserved by `x ↦ aDiag t • x` and a leafwise system for `Uminus t` (the subgroup contracted by
that single element), there is a `μ`-conull measurable set `X''` on which the covariance holds at
every parameter `z • t`, `z : ℤ`. -/
theorem acovariantAlong_of_leafwise {μ : Measure X3} [IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ (Uminus t) ν X') :
    ∃ X'' : Set X3, X'' ⊆ X' ∧ MeasurableSet X'' ∧ μ X''ᶜ = 0 ∧
      ACovariantAlong ν t X'' := by
  classical
  haveI : StandardBorelSpace X3 := Work.EKLComp.X3Background.2.2.2.2
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hcontr : ∀ u ∈ Uminus t, Filter.Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) Filter.atTop (nhds 1) :=
    (uminus_isHoro t).2
  have hfree : ∀ᵐ x ∂μ, ∀ u ∈ Uminus t, u • x = x → u = 1 :=
    Work.EKLRelCross.ae_free_orbit Work.EKLComp.prove_X3 μ (Uminus t) hU t hmp hcontr
  -- a measurable conull set contained in the set of free points
  set N : Set X3 := {x | ¬ (∀ u ∈ Uminus t, u • x = x → u = 1)} with hNdef
  have hNnull : μ N = 0 := MeasureTheory.ae_iff.mp hfree
  set T : Set X3 := MeasureTheory.toMeasurable μ N with hTdef
  have hTmeas : MeasurableSet T := MeasureTheory.measurableSet_toMeasurable μ N
  have hTnull : μ T = 0 := (MeasureTheory.measure_toMeasurable (μ := μ) N).trans hNnull
  have hNT : N ⊆ T := MeasureTheory.subset_toMeasurable μ N
  -- the base set: domain of the leafwise system and free points
  set A : Set X3 := X' ∩ Tᶜ with hAdef
  have hAmeas : MeasurableSet A := hL.meas_dom.inter hTmeas.compl
  have hAnull : μ Aᶜ = 0 := by
    rw [hAdef, Set.compl_inter, compl_compl]
    exact measure_union_null hL.conull hTnull
  -- the bad set of the covariance, as a subset of `X₃ × (Fin 3 → ℝ)`
  set Bad : Set (X3 × (Fin 3 → ℝ)) := {p | p.1 ∈ X' ∧ aDiag p.2 • p.1 ∈ X' ∧
    ¬ ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ν (aDiag p.2 • p.1) = c • (ν p.1).map
        (fun g : SL3 => aDiag p.2 * g * (aDiag p.2)⁻¹)} with hBaddef
  have hBadmeas : MeasurableSet Bad := Work.EKLRelCross.covariance_bad_measurable hU hL
  -- a measure-preserving diagonal action returns points of a conull set to it
  have hvisit : ∀ s : Fin 3 → ℝ, MeasurePreserving (fun x : X3 => aDiag s • x) μ μ →
      ∀ S : Set X3, MeasurableSet S → μ Sᶜ = 0 → μ {x : X3 | aDiag s • x ∉ S} = 0 := by
    intro s hs S hS hSc
    have h1 : (fun x : X3 => aDiag s • x) ⁻¹' Sᶜ = {x : X3 | aDiag s • x ∉ S} := rfl
    rw [← h1, ← Measure.map_apply hs.measurable hS.compl, hs.map_eq]
    exact hSc
  -- measure preservation at every integer multiple of `t`
  have hMPnat : ∀ n : ℕ, MeasurePreserving (fun x : X3 => aDiag (n • t) • x) μ μ := by
    intro n
    have hfun : (fun x : X3 => aDiag (n • t) • x) = (fun x : X3 => aDiag t • x)^[n] := by
      rw [smul_iterate, Work.EKLRelCross.aDiag_nsmul]
    rw [hfun]
    exact hmp.iterate n
  have hMPz : ∀ z : ℤ, MeasurePreserving (fun x : X3 => aDiag ((z : ℝ) • t) • x) μ μ := by
    intro z
    by_cases hz : 0 ≤ z
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hz
      rw [hn]
      have hc : (((n : ℤ)) : ℝ) = (n : ℝ) := by push_cast; ring
      rw [hc, Nat.cast_smul_eq_nsmul]
      exact hMPnat n
    · have hz' : 0 ≤ -z := by omega
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hz'
      have hzn : z = -(n : ℤ) := by omega
      rw [hzn]
      have hc : ((-(n : ℤ) : ℤ) : ℝ) = -((n : ℝ)) := by push_cast; ring
      rw [hc, neg_smul, Nat.cast_smul_eq_nsmul]
      exact measurePreserving_aDiag_neg (hMPnat n)
  -- the good sets: on `G z` the covariance at `z • t` holds whenever both `x` and its image
  -- lie in `A`
  have hgood : ∀ z : ℤ, ∃ G : Set X3, MeasurableSet G ∧ μ Gᶜ = 0 ∧
      ∀ x ∈ G, x ∈ A → aDiag ((z : ℝ) • t) • x ∈ A →
        ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
          ν (aDiag ((z : ℝ) • t) • x) = c • (ν x).map
            (fun g : SL3 => aDiag ((z : ℝ) • t) * g * (aDiag ((z : ℝ) • t))⁻¹) := by
    intro z
    set s : Fin 3 → ℝ := (z : ℝ) • t with hsdef
    have hs : MeasurePreserving (fun x : X3 => aDiag s • x) μ μ := hMPz z
    have hper := per_t_covariance_mp_cov (U := Uminus t) hU hL t hmp hcontr hfree s hs
    -- the bad set of the a.e. statement
    have hBbadnull : μ {x : X3 | ¬ ((x ∈ X' ∧ aDiag s • x ∈ X' ∧
        (∀ u ∈ Uminus t, u • x = x → u = 1) ∧
        (∀ u ∈ Uminus t, u • (aDiag s • x) = aDiag s • x → u = 1)) →
        ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
          ν (aDiag s • x) = c • (ν x).map (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹))} = 0 :=
      MeasureTheory.ae_iff.mp hper
    have hBadzmeas : MeasurableSet {x : X3 | (x, s) ∈ Bad} :=
      hBadmeas.preimage (measurable_id.prod measurable_const)
    have hBadzsub : {x : X3 | (x, s) ∈ Bad} ⊆
        {x : X3 | ¬ ((x ∈ X' ∧ aDiag s • x ∈ X' ∧
          (∀ u ∈ Uminus t, u • x = x → u = 1) ∧
          (∀ u ∈ Uminus t, u • (aDiag s • x) = aDiag s • x → u = 1)) →
          ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
            ν (aDiag s • x) = c • (ν x).map (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹))} ∪ T ∪
        (fun x : X3 => aDiag s • x) ⁻¹' T := by
      intro x hx
      by_cases h1 : x ∈ T
      · exact Or.inl (Or.inr h1)
      · by_cases h2 : aDiag s • x ∈ T
        · exact Or.inr h2
        · have hxnT : x ∉ T := h1
          have hTxnT : aDiag s • x ∉ T := h2
          have hxnf : ∀ u ∈ Uminus t, u • x = x → u = 1 := by
            by_contra hc
            exact hxnT (hNT (by simpa only [hNdef, Set.mem_setOf_eq] using hc))
          have hTxnf : ∀ u ∈ Uminus t, u • (aDiag s • x) = aDiag s • x → u = 1 := by
            by_contra hc
            exact hTxnT (hNT (by simpa only [hNdef, Set.mem_setOf_eq] using hc))
          have hhyp : (x ∈ X' ∧ aDiag s • x ∈ X' ∧
              (∀ u ∈ Uminus t, u • x = x → u = 1) ∧
              (∀ u ∈ Uminus t, u • (aDiag s • x) = aDiag s • x → u = 1)) :=
            ⟨hx.1, hx.2.1, hxnf, hTxnf⟩
          exact Or.inl (Or.inl (fun himpl => hx.2.2 (himpl hhyp)))
    have hBadznull : μ {x : X3 | (x, s) ∈ Bad} = 0 := by
      have hTN : μ ((fun x : X3 => aDiag s • x) ⁻¹' T) = 0 := by
        rw [← Measure.map_apply hs.measurable hTmeas, hs.map_eq, hTnull]
      have h1 : μ ({x : X3 | ¬ ((x ∈ X' ∧ aDiag s • x ∈ X' ∧
          (∀ u ∈ Uminus t, u • x = x → u = 1) ∧
          (∀ u ∈ Uminus t, u • (aDiag s • x) = aDiag s • x → u = 1)) →
          ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
            ν (aDiag s • x) = c • (ν x).map (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹))} ∪ T ∪
          (fun x : X3 => aDiag s • x) ⁻¹' T) = 0 := by
        refine le_antisymm ?_ bot_le
        calc μ ({x : X3 | ¬ ((x ∈ X' ∧ aDiag s • x ∈ X' ∧
                (∀ u ∈ Uminus t, u • x = x → u = 1) ∧
                (∀ u ∈ Uminus t, u • (aDiag s • x) = aDiag s • x → u = 1)) →
                ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
                  ν (aDiag s • x) = c • (ν x).map
                    (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹))} ∪ T ∪
              (fun x : X3 => aDiag s • x) ⁻¹' T)
            ≤ μ ({x : X3 | ¬ ((x ∈ X' ∧ aDiag s • x ∈ X' ∧
                (∀ u ∈ Uminus t, u • x = x → u = 1) ∧
                (∀ u ∈ Uminus t, u • (aDiag s • x) = aDiag s • x → u = 1)) →
                ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
                  ν (aDiag s • x) = c • (ν x).map
                    (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹))} ∪ T) +
              μ ((fun x : X3 => aDiag s • x) ⁻¹' T) := measure_union_le _ _
          _ ≤ (μ {x : X3 | ¬ ((x ∈ X' ∧ aDiag s • x ∈ X' ∧
                (∀ u ∈ Uminus t, u • x = x → u = 1) ∧
                (∀ u ∈ Uminus t, u • (aDiag s • x) = aDiag s • x → u = 1)) →
                ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
                  ν (aDiag s • x) = c • (ν x).map
                    (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹))} + μ T) +
              μ ((fun x : X3 => aDiag s • x) ⁻¹' T) :=
              add_le_add (measure_union_le _ _) le_rfl
          _ = 0 := by rw [hBbadnull, hTnull, hTN]; simp
      exact le_antisymm (le_trans (MeasureTheory.measure_mono hBadzsub) (le_of_eq h1)) bot_le
    refine ⟨(A ∩ ((fun x : X3 => aDiag s • x) ⁻¹' A) ∩ {x : X3 | (x, s) ∈ Bad})ᶜ, ?_, ?_, ?_⟩
    · exact ((hAmeas.inter (hAmeas.preimage (continuous_const_smul _).measurable)).inter
        hBadzmeas).compl
    · rw [compl_compl]
      exact le_antisymm (le_trans (MeasureTheory.measure_mono Set.inter_subset_right)
        (le_of_eq hBadznull)) bot_le
    · intro x hx hxA hTA
      have hxnot : x ∉ A ∩ ((fun x : X3 => aDiag s • x) ⁻¹' A) ∩ {x : X3 | (x, s) ∈ Bad} := hx
      have hxBad : (x, s) ∉ Bad := by
        intro hcon
        exact hxnot (Set.mem_inter (Set.mem_inter hxA (by simpa only [Set.mem_preimage] using hTA))
          hcon)
      have hbad : ¬ (x ∈ X' ∧ aDiag s • x ∈ X' ∧ ¬ ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
          ν (aDiag s • x) = c • (ν x).map (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹)) := by
        simpa only [hBaddef, Set.mem_setOf_eq, not_exists] using hxBad
      rw [hsdef] at hbad
      by_contra hcon
      exact hbad ⟨hxA.1, hTA.1, hcon⟩
  choose G hGmeas hGnull hGprop using hgood
  refine ⟨A ∩ ⋂ z : ℤ, (((fun x : X3 => aDiag ((z : ℝ) • t) • x) ⁻¹' A) ∩ G z),
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hx.1.1
  · refine hAmeas.inter (MeasurableSet.iInter fun z => ?_)
    exact (hAmeas.preimage (continuous_const_smul _).measurable).inter (hGmeas z)
  · have hcompl : (A ∩ ⋂ z : ℤ, (((fun x : X3 => aDiag ((z : ℝ) • t) • x) ⁻¹' A) ∩ G z))ᶜ
        = Aᶜ ∪ ⋃ z : ℤ, (((fun x : X3 => aDiag ((z : ℝ) • t) • x) ⁻¹' A) ∩ G z)ᶜ := by
      rw [Set.compl_inter, Set.compl_iInter]
    rw [hcompl]
    refine measure_union_null hAnull (measure_iUnion_null fun z => ?_)
    rw [Set.compl_inter]
    exact measure_union_null (hvisit ((z : ℝ) • t) (hMPz z) A hAmeas hAnull) (hGnull z)
  · intro z x hx hTx
    obtain ⟨hxA, hxI⟩ := hx
    obtain ⟨hzA, hzG⟩ := Set.mem_iInter.mp hxI z
    exact hGprop z x hzG hxA hTx.1

end Work.EKLC6Core
