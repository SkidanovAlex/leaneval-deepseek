import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Sector.integrable_slotComb_prod
import Submission.Work.BoseKinLoc.Sector.potWordU_slotComb
import Submission.Work.SlotWord.slotSplit_integral_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Sector

open MeasureTheory

variable {N : ℕ}

/-! ## Helpers -/

private lemma acube_sub_acube_max (ℓ L : ℝ) :
    Submission.BoseGases.acube L ⊆ Submission.BoseGases.acube (max L ℓ) := by
  intro y hy
  rw [Submission.BoseGases.mem_acube_iff] at hy ⊢
  intro m
  exact ⟨by linarith [(hy m).1, le_max_left L ℓ], by linarith [(hy m).2, le_max_left L ℓ]⟩

private lemma abox_sub_abox_max (n : ℕ) (ℓ L : ℝ) :
    Submission.BoseGases.abox n L ⊆ Submission.BoseGases.abox n (max L ℓ) :=
  fun x hx i => acube_sub_acube_max ℓ L (hx i)

private lemma slotBox_measurable' {ι : Type*} [Fintype ι] {A : Set ℝ³} (h : MeasurableSet A) :
    MeasurableSet (Work.PerSector.slotBox (ι := ι) A) :=
  Work.PerSector.Work.PerSector.slotBox_measurable h

private lemma measurableSet_slotOutside (L ℓ : ℝ) (S : Finset (Fin N)) :
    MeasurableSet (Work.PerSector.slotOutside L (Submission.BoseGases.acube ℓ) S) :=
  Work.PerSector.Work.PerSector.slotBox_measurable
    ((Submission.BoseGases.acube_measurable L).inter
      (Submission.BoseGases.acube_measurable ℓ).compl)

private theorem setIntegral_slotBox_abox (S : Finset (Fin N)) (r : ℝ)
    (F : (Fin S.card → ℝ³) → ℝ) :
    (∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
        (Submission.BoseGases.acube r),
        F (fun m : Fin S.card => z ((slotIso S).symm m)))
      = ∫ x in Submission.BoseGases.abox S.card r, F x := by
  classical
  let ee : (Work.PerSector.SlotIn N S → ℝ³) ≃ᵐ (Fin S.card → ℝ³) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin S.card => ℝ³) (slotIso S)
  have hee : ∀ (z : Work.PerSector.SlotIn N S → ℝ³) (m : Fin S.card),
      ee z m = z ((slotIso S).symm m) := by
    intro z m
    have h1 := MeasurableEquiv.piCongrLeft_apply_apply (slotIso S)
      (β := fun _ : Fin S.card => ℝ³) z ((slotIso S).symm m)
    simpa using h1
  have hmp : MeasurePreserving ee volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin S.card => ℝ³) (slotIso S)
  have himg : ee '' (Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
        (Submission.BoseGases.acube r)) = Submission.BoseGases.abox S.card r := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩ k
      rw [hee z k]
      exact hz ((slotIso S).symm k)
    · intro hy
      refine ⟨fun i : Work.PerSector.SlotIn N S => y (slotIso S i), fun i => ?_, ?_⟩
      · exact hy (slotIso S i)
      · funext k
        rw [hee _ k]
        simp
  have key := hmp.setIntegral_image_emb ee.measurableEmbedding F
    (Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) (Submission.BoseGases.acube r))
  rw [himg] at key
  have hfun : (fun z : Work.PerSector.SlotIn N S → ℝ³ =>
      F (fun m : Fin S.card => z ((slotIso S).symm m))) = fun z => F (ee z) := by
    funext z
    congr 1
    exact funext fun m => (hee z m).symm
  rw [hfun]
  exact key.symm

/-- The potential-word integrand of the fibre at the reassembled configuration. -/
private lemma fibre_integrand_slotComb (S : Finset (Fin N)) {v g : ℝ³ → ℝ} {ℓ μ : ℝ}
    (hℓ : 0 < ℓ) (Ψ : Submission.BoseGases.X N → ℝ)
    (z : Work.PerSector.SlotIn N S → ℝ³) (y : Work.PerSector.SlotOut N S → ℝ³)
    (hy : ∀ j : Work.PerSector.SlotOut N S, y j ∉ Submission.BoseGases.acube ℓ) :
    (fibState S Ψ y (fun m : Fin S.card => z ((slotIso S).symm m))) ^ 2
        * Work.BoseKinLoc.potWordU S.card v g ℓ μ 0
            (fun m : Fin S.card => z ((slotIso S).symm m))
      = (Ψ (Work.PerSector.slotComb S z y)) ^ 2
        * Work.BoseKinLoc.potWordU N v g ℓ μ 0 (Work.PerSector.slotComb S z y) := by
  rw [potWordU_slotComb S hℓ z y hy]
  have hfib : fibState S Ψ y (fun m : Fin S.card => z ((slotIso S).symm m))
      = Ψ (Work.PerSector.slotComb S z y) := by
    rw [fibState_apply]
    have harg : (fun i : Work.PerSector.SlotIn N S =>
        (fun m : Fin S.card => z ((slotIso S).symm m)) (slotIso S i)) = z := by
      funext i
      simp
    rw [harg]
  rw [hfib]

/-- The `y`-slice identity: the in-box integral of the reassembled integrand is the fibre
integral over the `|S|`-particle box. -/
private lemma slice_eq_fibre (S : Finset (Fin N)) {v g : ℝ³ → ℝ} {ℓ μ : ℝ}
    (hℓ : 0 < ℓ) (Ψ : Submission.BoseGases.X N → ℝ)
    (y : Work.PerSector.SlotOut N S → ℝ³)
    (hy : ∀ j : Work.PerSector.SlotOut N S, y j ∉ Submission.BoseGases.acube ℓ) :
    (∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
        (Submission.BoseGases.acube ℓ),
        (Ψ (Work.PerSector.slotComb S z y)) ^ 2
          * Work.BoseKinLoc.potWordU N v g ℓ μ 0 (Work.PerSector.slotComb S z y))
      = ∫ ζ in Submission.BoseGases.abox S.card ℓ,
          (fibState S Ψ y ζ) ^ 2 * Work.BoseKinLoc.potWordU S.card v g ℓ μ 0 ζ := by
  trans ∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
        (Submission.BoseGases.acube ℓ),
        (fun ζ : Fin S.card → ℝ³ => (fibState S Ψ y ζ) ^ 2
          * Work.BoseKinLoc.potWordU S.card v g ℓ μ 0 ζ)
          (fun m : Fin S.card => z ((slotIso S).symm m))
  · refine setIntegral_congr_fun
      (slotBox_measurable' (Submission.BoseGases.acube_measurable ℓ)) (fun z _ => ?_)
    exact (fibre_integrand_slotComb S hℓ Ψ z y hy).symm
  · exact setIntegral_slotBox_abox S ℓ
      (fun ζ : Fin S.card → ℝ³ => (fibState S Ψ y ζ) ^ 2
        * Work.BoseKinLoc.potWordU S.card v g ℓ μ 0 ζ)

/-- **The sector decomposition of the whole-space potential integral.**  Let `Ψ` be a smooth state
supported in `abox N L` and let `0 < ℓ`, and suppose the whole-space potential integrand
`x ↦ Ψ x ^ 2 * potWordU N v g ℓ μ 0 x` is integrable (this is what makes every integral below an
honest Bochner integral — without it the whole-space integral is Mathlib's junk value `0` while the
fibre-side terms with `|S| ≤ 1` have no pair contribution and survive).  Then the integral of the
potential energy factorises over the slot sets `S : Finset (Fin N)` (the sets of particles lying in
the box `acube ℓ`), the outside configurations ranging over `acube (max L ℓ) ∩ (acube ℓ)ᶜ`:

`∫_x Ψ(x)² potWordU N v g ℓ μ 0 x = Σ_S ∫_y ∫_{z ∈ abox |S| ℓ} (fibState S Ψ y z)² potWordU |S| v g ℓ μ 0 z`,

and each outside integrand is integrable.  Proof: the slot sets partition the configuration space
(`Work.PerSector.iUnion_slotSet`), so the integral is the sum over `S` of the integral of
`1_{slotSet (acube ℓ) S}·f`; each of those vanishes off `abox N (max L ℓ)` (because `Ψ` does, as
`abox N L ⊆ abox N (max L ℓ)`), so the slot splitting
`Work.SlotWord.slotSplit_integral_slotBox` gives the iterated integral over `(z, y)`; on the domain
`z ∈ slotBox (acube ℓ)`, `y ∈ slotOutside` the potential word collapses (every slot outside `S`
carries a vanishing `chiU`-factor: `potWordU_slotComb`), `Ψ (slotComb S z y)` is `fibState S Ψ y`
at the re-indexed configuration, and the re-indexing `slotBox_setIntegral_slotIso` converts the
in-box integral over `SlotIn N S → ℝ³` into the integral over `abox |S| ℓ`.  The a.e.-in-`y` slice
integrability comes from Fubini (`integrable_slotComb_prod` + `Integrable.prod_left_ae`), which is
also what makes the outside integrand integrable (the two facts `potWordU_slotComb` and
`slotBox_setIntegral_slotIso` are sibling lemmas being proved in the same directory; if they are
not yet available, prove them privately here).  Namespace `Work.BoseKinLoc.Sector`; imports:
Mathlib, `Submission.Work.BoseKinLoc.Defs`, `Submission.Work.BoseKinLoc.Sector.fibre_defs_v3`,
`Submission.Work.PerSector.FibreResidual`, `Submission.Work.SlotWord.slotSplit_integral_slotBox`,
`Submission.Work.PerSector.slotMassENN_eq_fibre`. -/
theorem potIntegral_fibreSum {N : ℕ} {v g : ℝ³ → ℝ} {ℓ L μ : ℝ} (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox N L)
    (hint : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
      (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ (0 : ℝ³) x)) :
    ((∫ x : Submission.BoseGases.X N,
        (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ (0 : ℝ³) x)
      = ∑ S : Finset (Fin N),
          ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
            ∫ z in Submission.BoseGases.abox S.card ℓ,
              (fibState S Ψ y z) ^ 2
                * Work.BoseKinLoc.potWordU S.card v g ℓ μ (0 : ℝ³) z)
    ∧ (∀ S : Finset (Fin N),
        MeasureTheory.IntegrableOn
          (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
            ∫ z in Submission.BoseGases.abox S.card ℓ,
              (fibState S Ψ y z) ^ 2
                * Work.BoseKinLoc.potWordU S.card v g ℓ μ (0 : ℝ³) z)
          (Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S)) := by
  classical
  let BM : Set ℝ³ := Submission.BoseGases.acube ℓ
  let L' : ℝ := max L ℓ
  have hL' : L ≤ L' := le_max_left L ℓ
  have hℓL' : ℓ ≤ L' := le_max_right L ℓ
  have hℓ0 : 0 ≤ ℓ := le_of_lt hℓ
  have hBL' : BM ⊆ Submission.BoseGases.acube L' :=
    Submission.BoseGases.acube_mono hℓ0 hℓL'
  have hsub : Submission.BoseGases.abox N L ⊆ Submission.BoseGases.abox N L' :=
    abox_sub_abox_max N ℓ L
  have hΨ0 : ∀ x : Submission.BoseGases.X N, x ∉ Submission.BoseGases.abox N L → Ψ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hsupp (subset_tsupport Ψ (Function.mem_support.mpr hne)))
  -- the pieces are integrable
  have hIntS : ∀ S : Finset (Fin N),
      Integrable ((Work.PerSector.slotSet BM S).indicator
        (fun y : Submission.BoseGases.X N =>
          (Ψ y) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y)) :=
    fun S => hint.indicator
      (Work.PerSector.slotSet_measurable BM (Submission.BoseGases.acube_measurable ℓ) S)
  -- ## Step 1: the slot sets partition the configuration space
  have hstep1 : (∫ x : Submission.BoseGases.X N,
        (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 x)
      = ∑ S : Finset (Fin N), ∫ x : Submission.BoseGases.X N,
          (Work.PerSector.slotSet BM S).indicator
            (fun y : Submission.BoseGases.X N =>
              (Ψ y) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y) x := by
    have hpt : ∀ x : Submission.BoseGases.X N,
        (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 x
          = ∑ S : Finset (Fin N),
              (Work.PerSector.slotSet BM S).indicator
                (fun y : Submission.BoseGases.X N =>
                  (Ψ y) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y) x :=
      fun x => (Work.PerSector.sum_indicator_slotSet BM
        (fun y : Submission.BoseGases.X N =>
          (Ψ y) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y) x).symm
    calc (∫ x : Submission.BoseGases.X N,
          (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 x)
        = ∫ x : Submission.BoseGases.X N, ∑ S : Finset (Fin N),
            (Work.PerSector.slotSet BM S).indicator
              (fun y : Submission.BoseGases.X N =>
                (Ψ y) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y) x :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ∑ S : Finset (Fin N), ∫ x : Submission.BoseGases.X N,
            (Work.PerSector.slotSet BM S).indicator
              (fun y : Submission.BoseGases.X N =>
                (Ψ y) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y) x :=
          MeasureTheory.integral_finsetSum Finset.univ (fun S _ => hIntS S)
  -- ## Step 2: the slot pieces vanish off `abox N (max L ℓ)`
  have hstep2 : ∀ S : Finset (Fin N),
      (∫ x : Submission.BoseGases.X N, (Work.PerSector.slotSet BM S).indicator
            (fun y : Submission.BoseGases.X N =>
              (Ψ y) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y) x)
        = ∫ x in Submission.BoseGases.abox N L', (Work.PerSector.slotSet BM S).indicator
            (fun y : Submission.BoseGases.X N =>
              (Ψ y) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y) x := by
    intro S
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hx' : x ∉ Submission.BoseGases.abox N L := fun h => hx (hsub h)
      have h0 : (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 x = 0 := by
        simp [hΨ0 x hx']
      by_cases hmem : x ∈ Work.PerSector.slotSet BM S
      · rw [Set.indicator_of_mem hmem, h0]
      · rw [Set.indicator_of_notMem hmem])).symm
  -- ## Step 3: the slot splitting
  have hstep3 : ∀ S : Finset (Fin N),
      (∫ x in Submission.BoseGases.abox N L', (Work.PerSector.slotSet BM S).indicator
            (fun y : Submission.BoseGases.X N =>
              (Ψ y) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y) x)
        = ∫ y in Work.PerSector.slotOutside L' BM S,
            ∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) BM,
              (Work.PerSector.slotSet BM S).indicator
                (fun y : Submission.BoseGases.X N =>
                  (Ψ y) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y)
                (Work.PerSector.slotComb S z y) := by
    intro S
    exact Work.SlotWord.slotSplit_integral_slotBox (N := N) L' (B := BM) S hBL'
      (hIntS S).integrableOn.aestronglyMeasurable (hIntS S).integrableOn
      (fun x hx j => by
        have hxS : x ∈ Work.PerSector.slotSet BM S := by
          by_contra hc
          exact hx (Set.indicator_of_notMem hc _)
        exact fun hc => j.2 ((hxS j.1).mp hc))
      (fun x hx i => by
        have hxS : x ∈ Work.PerSector.slotSet BM S := by
          by_contra hc
          exact hx (Set.indicator_of_notMem hc _)
        exact (hxS i.1).mpr i.2)
  -- ## Step 4: the collapse of the word on the slot box
  have hstep4 : ∀ S : Finset (Fin N),
      (∫ y in Work.PerSector.slotOutside L' BM S,
            ∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) BM,
              (Work.PerSector.slotSet BM S).indicator
                (fun y : Submission.BoseGases.X N =>
                  (Ψ y) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 y)
                (Work.PerSector.slotComb S z y))
        = ∫ y in Work.PerSector.slotOutside L' BM S,
            ∫ ζ in Submission.BoseGases.abox S.card ℓ,
              (fibState S Ψ y ζ) ^ 2 * Work.BoseKinLoc.potWordU S.card v g ℓ μ 0 ζ := by
    intro S
    refine setIntegral_congr_fun (measurableSet_slotOutside L' ℓ S) (fun y hy => ?_)
    have hy' : ∀ j : Work.PerSector.SlotOut N S, y j ∉ BM :=
      (Work.PerSector.mem_slotOutside_iff.mp hy).2
    trans ∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) BM,
          (Ψ (Work.PerSector.slotComb S z y)) ^ 2
            * Work.BoseKinLoc.potWordU N v g ℓ μ 0 (Work.PerSector.slotComb S z y)
    · refine setIntegral_congr_fun
        (slotBox_measurable' (Submission.BoseGases.acube_measurable ℓ)) (fun z hz => ?_)
      exact Set.indicator_of_mem
        ((Work.PerSector.slotComb_mem_slotSet_iff BM S z y).mpr ⟨fun i => hz i, hy'⟩) _
    · exact slice_eq_fibre S hℓ Ψ y hy'
  have key : (∫ x : Submission.BoseGases.X N,
        (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 x)
      = ∑ S : Finset (Fin N),
          ∫ y in Work.PerSector.slotOutside L' BM S,
            ∫ ζ in Submission.BoseGases.abox S.card ℓ,
              (fibState S Ψ y ζ) ^ 2 * Work.BoseKinLoc.potWordU S.card v g ℓ μ 0 ζ := by
    rw [hstep1]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [hstep2 S, hstep3 S, hstep4 S]
  refine ⟨key, ?_⟩
  -- ## Part B: the outside integrand is integrable
  intro S
  have hpoint : ∀ y ∈ Work.PerSector.slotOutside L' BM S,
      (∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) BM,
          (Ψ (Work.PerSector.slotComb S z y)) ^ 2
            * Work.BoseKinLoc.potWordU N v g ℓ μ 0 (Work.PerSector.slotComb S z y))
        = ∫ ζ in Submission.BoseGases.abox S.card ℓ,
            (fibState S Ψ y ζ) ^ 2 * Work.BoseKinLoc.potWordU S.card v g ℓ μ 0 ζ :=
    fun y hy => slice_eq_fibre S hℓ Ψ y (Work.PerSector.mem_slotOutside_iff.mp hy).2
  have hle : ((MeasureTheory.volume : Measure (Work.PerSector.SlotIn N S → ℝ³)).restrict
        (Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) BM)).prod
      ((MeasureTheory.volume : Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
        (Work.PerSector.slotOutside L' BM S))
      ≤ ((MeasureTheory.volume : Measure (Work.PerSector.SlotIn N S → ℝ³)).restrict
        (Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
          (Submission.BoseGases.acube L'))).prod
      ((MeasureTheory.volume : Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
        (Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
          (Submission.BoseGases.acube L'))) :=
    MeasureTheory.Measure.prod_mono
      (MeasureTheory.Measure.restrict_mono (Work.PerSector.Work.PerSector.slotBox_mono hBL') le_rfl)
      (MeasureTheory.Measure.restrict_mono
        (Work.PerSector.Work.PerSector.slotBox_mono Set.inter_subset_left) le_rfl)
  have hIntBox : MeasureTheory.IntegrableOn
      (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
        ∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) BM,
          (Ψ (Work.PerSector.slotComb S z y)) ^ 2
            * Work.BoseKinLoc.potWordU N v g ℓ μ 0 (Work.PerSector.slotComb S z y))
      (Work.PerSector.slotOutside L' BM S) := by
    have hG := integrable_slotComb_prod L' S
      (hint.integrableOn (s := Submission.BoseGases.abox N L'))
    have hG' := hG.mono_measure hle
    have hres := hG'.integral_prod_right
    simpa only [MeasureTheory.IntegrableOn] using hres
  rw [MeasureTheory.IntegrableOn] at hIntBox ⊢
  refine hIntBox.congr ?_
  exact MeasureTheory.ae_restrict_of_forall_mem (measurableSet_slotOutside L' ℓ S) hpoint

end Work.BoseKinLoc.Sector
