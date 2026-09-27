import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.MaxLeafDefs
import Submission.Work.EKLComp.MaxLeafAux
import Submission.Work.EKLComp.free_ae
import Submission.Work.EKLComp.leafMeasure_proportional
import Submission.Work.EKLComp.exists_rat_badENN
import Submission.Work.EKLComp.besicovitch_intervals
import Submission.Work.EKLComp.besicovitch_maximal
import Submission.Work.EKLComp.measurableSet_badENN
import Submission.Work.EKLComp.frozen_subset_bad
import Submission.Work.EKLComp.atom_bad_bound
import Submission.Work.EKLComp.plaqueAlgebra_exists
import Submission.Work.EKLComp.condexp_atom_bound_borel

/-!
# C11a — the maximal inequality for leafwise measures (EKL (10), L06 Thm A.1)

Proof of `Work.EKLContract.P_MaxLeaf`.  The plan is documented in `MaxLeafDefs.lean`:

* `frozen_subset_bad` reduces the bad set of the frozen statement to the `ℝ≥0∞`-form `BadSet`;
* `exists_rat_badENN` + `measurableSet_badENN` exhibit the bad set as a countable union of
  measurable sets with *bounded rational* radii;
* `plaqueAlgebra_exists` supplies the plaque algebra `(Z, m)` and the good set `G` (L06 Lemma A.2);
* `atom_bad_bound` is the one-leaf Besicovitch estimate and `condexp_atom_bound` integrates it
  over `Z` using the `condexp` field of `IsLeafwise`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

noncomputable section

namespace Work.EKLComp

/-- `ballU hij r` is compact. -/
theorem maxLeaf_isCompact_ballU {i j : Fin 3} (hij : i ≠ j) (r : ℝ) :
    IsCompact (ballU hij r) :=
  isCompact_Icc.image (continuous_uij hij)

/-- **C11a, core.**  The maximal inequality with the Besicovitch constant supplied by the
covering hypothesis `hcover`. -/
theorem maxLeaf_core (N : ℕ) (hN : 0 < N)
    (hcover : ∀ (A : Set ℝ) (r : A → ℝ), (∀ a, 0 < r a) → (∃ ρ : ℝ, ∀ a, r a ≤ ρ) →
      ∃ s : Fin N → Set A,
        (∀ i, (s i).PairwiseDisjoint fun a => Metric.closedBall (a : ℝ) (r a)) ∧
        A ⊆ ⋃ i, ⋃ a ∈ s i, Metric.ball (a : ℝ) (r a))
    (i j : Fin 3) (hij : i ≠ j) (μ : Measure X3) [IsProbabilityMeasure μ]
    (hA : IsAInvariant μ) (ν : X3 → Measure SL3) (X' : Set X3)
    (hν : IsLeafwise μ (Uij hij) ν X') (f : X3 → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfint : Integrable f μ) (α : ℝ) (hα : 0 < α) :
    μ (X' ∩ FrozenBadSet i j hij ν f α) ≤ ENNReal.ofReal ((2 * (N : ℝ)) * (∫ x, f x ∂μ) / α) := by
  classical
  -- a "globally locally finite" modification of `ν`
  set ν' : X3 → Measure SL3 := fun x => if x ∈ X' then ν x else 0 with hν'def
  have hν'cc : ∀ g : CompactlySupportedContinuousMap SL3 ℝ,
      Measurable (fun x => ∫ y, g y ∂(ν' x)) := by
    intro g
    have h1 : Measurable (fun x => ∫ y, g y ∂(ν x)) := hν.measurable g
    have heq : (fun x => ∫ y, g y ∂(ν' x))
        = X'.piecewise (fun x => ∫ y, g y ∂(ν x)) (fun _ => 0) := by
      funext x
      by_cases hx : x ∈ X'
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]
        simp only [hν'def, if_pos hx]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
        simp only [hν'def, if_neg hx]
        simp
    rw [heq]
    exact Measurable.ite hν.meas_dom h1 measurable_const
  have hν'radon : ∀ x, IsFiniteMeasureOnCompacts (ν' x) := by
    intro x
    by_cases hx : x ∈ X'
    · simp only [hν'def, if_pos hx]; exact hν.radon x hx
    · simp only [hν'def, if_neg hx]; infer_instance
  have hmeasENN : ∀ r : ℝ, MeasurableSet {x : X3 | BadENN i j hij ν' f x α r} :=
    fun r => measurableSet_badENN i j hij ν' hν'cc hν'radon f hf α r
  -- the intersections of the bad sets with `X'` are measurable
  have hmeasRat' : ∀ rbar : ℝ, MeasurableSet (X' ∩ BadSetRat i j hij ν f α rbar) := by
    intro rbar
    have heq : X' ∩ BadSetRat i j hij ν f α rbar
        = ⋃ q : ℚ, (X' ∩ {x : X3 | 0 < q ∧ (q : ℝ) < rbar}
            ∩ {x : X3 | BadENN i j hij ν' f x α (q : ℝ)}) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, BadSetRat, Set.mem_iUnion]
      constructor
      · rintro ⟨hx, q, h1, h2, h3⟩
        refine ⟨q, ⟨hx, h1, h2⟩, ?_⟩
        have hx' : ν' x = ν x := by simp only [hν'def, if_pos hx]
        simpa only [BadENN, hx'] using h3
      · rintro ⟨q, ⟨hx, h1, h2⟩, h3⟩
        refine ⟨hx, q, h1, h2, ?_⟩
        have hx' : ν' x = ν x := by simp only [hν'def, if_pos hx]
        simpa only [BadENN, hx'] using h3
    rw [heq]
    refine MeasurableSet.iUnion fun q => ?_
    by_cases hq : 0 < q ∧ (q : ℝ) < rbar
    · have hset : (X' ∩ {x : X3 | 0 < q ∧ (q : ℝ) < rbar}) = X' := by
        ext x; constructor
        · intro h; exact h.1
        · intro h; exact ⟨h, hq⟩
      rw [hset]
      exact MeasurableSet.inter hν.meas_dom (hmeasENN (q : ℝ))
    · have hset : (X' ∩ {x : X3 | 0 < q ∧ (q : ℝ) < rbar}) = ∅ := by
        ext x; constructor
        · rintro ⟨-, h2⟩; exact absurd h2 hq
        · intro h; exact h.elim
      rw [hset, Set.empty_inter]
      exact MeasurableSet.empty
  set SRat : Set X3 := ⋃ n : ℕ, (X' ∩ BadSetRat i j hij ν f α ((n : ℝ) + 1)) with hSRat
  have hSRatmeas : MeasurableSet SRat := by
    rw [hSRat]
    exact MeasurableSet.iUnion fun n => hmeasRat' ((n : ℝ) + 1)
  have hSRatmono : Monotone fun n : ℕ => X' ∩ BadSetRat i j hij ν f α ((n : ℝ) + 1) := by
    intro m n hmn
    refine Set.inter_subset_inter_right _ fun x hx => ?_
    rcases hx with ⟨q, h1, h2, h3⟩
    exact ⟨q, h1, lt_of_lt_of_le h2 (by exact_mod_cast Nat.add_le_add_right hmn 1), h3⟩
  have hSsup : μ SRat = ⨆ n : ℕ, μ (X' ∩ BadSetRat i j hij ν f α ((n : ℝ) + 1)) := by
    rw [hSRat]
    exact Monotone.measure_iUnion (μ := μ)
      (s := fun n : ℕ => X' ∩ BadSetRat i j hij ν f α ((n : ℝ) + 1)) hSRatmono
  -- the frozen bad set inside `X'` is contained in `SRat`
  have hFB_sub : X' ∩ FrozenBadSet i j hij ν f α ⊆ SRat := by
    rintro x ⟨hxX, hxF⟩
    obtain ⟨r, hrpos, hr⟩ := hxF
    have hne : ∀ s : ℝ, 0 < s → ν x (ballU hij s) ≠ ⊤ := fun s _ =>
      ne_of_lt ((hν.radon x hxX).lt_top_of_isCompact (maxLeaf_isCompact_ballU hij s))
    have hbad : BadSet i j hij ν f α x :=
      frozen_subset_bad i j hij ν f hf hf0 α hα x hne ⟨r, hrpos, hr⟩
    obtain ⟨ρ, hρpos, hρ⟩ := hbad
    obtain ⟨q, hqpos, hqlt, hqbad⟩ :=
      exists_rat_badENN i j hij ν f hf hf0 x α ρ (ρ + 1) hα hne hρpos (lt_add_one ρ) hρ
    obtain ⟨n, hn⟩ := exists_nat_gt ρ
    refine Set.mem_iUnion.mpr ⟨n, hxX, q, hqpos, ?_, hqbad⟩
    have hn' : ρ ≤ (n : ℝ) := le_of_lt hn
    linarith
  have hμS : μ (X' ∩ FrozenBadSet i j hij ν f α) ≤ μ SRat := measure_mono hFB_sub
  -- choose the scale
  obtain ⟨n, hn⟩ : ∃ n : ℕ, μ SRat ≤ 2 * μ (X' ∩ BadSetRat i j hij ν f α ((n : ℝ) + 1)) := by
    by_cases hzero : μ SRat = 0
    · exact ⟨0, by rw [hzero]; exact bot_le⟩
    · have hpos : 0 < μ SRat := bot_lt_iff_ne_bot.mpr hzero
      have hlt : μ SRat / 2 < μ SRat :=
        ENNReal.half_lt_self (ne_of_gt hpos) (measure_ne_top _ _)
      obtain ⟨n, hn⟩ := lt_iSup_iff.mp (by rw [← hSsup]; exact hlt)
      refine ⟨n, ?_⟩
      have h2 : 2 * (μ SRat / 2) = μ SRat := by
        rw [two_mul, ENNReal.add_halves]
      calc μ SRat = 2 * (μ SRat / 2) := h2.symm
        _ ≤ 2 * μ (X' ∩ BadSetRat i j hij ν f α ((n : ℝ) + 1)) := by gcongr
  set rbar : ℝ := (n : ℝ) + 1 with hrbardef
  have hrbarpos : 0 < rbar := by rw [hrbardef]; positivity
  -- the final numerical assembly, with `ε → 0`
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (μ (X' ∩ FrozenBadSet i j hij ν f α)).toReal ≤
        2 * (N : ℝ) * (∫ x, f x ∂μ) / α + 2 * ε := by
    intro ε hε hε1
    obtain ⟨Z, G, m, hZfree, hplaque, hGmeas, hGZ, hGmeas_le, hball⟩ :=
      (show PlaqueAlgebraExists i j hij from
        plaqueAlgebra_exists_borel i j hij) μ hA ε rbar hε hrbarpos
    set Y : Set X3 := X' ∩ BadSetRat i j hij ν f α rbar with hY
    have hYmeas : @MeasurableSet X3 instMeasurableSpaceX3 Y := by
      rw [hY]; exact hmeasRat' rbar
    have hGb : @MeasurableSet X3 instMeasurableSpaceX3 G := hGmeas
    set Y'' : Set X3 := Y ∩ G with hY''
    have hY''meas : @MeasurableSet X3 instMeasurableSpaceX3 Y'' := hYmeas.inter hGb
    have hY''Z : Y'' ⊆ Z := fun x hx => hGZ hx.2
    have hY''sub : Y'' ⊆ X' ∩ Free i j hij := fun x hx => ⟨hx.1.1, hZfree (hGZ hx.2)⟩
    have hY''bad : ∀ y ∈ Y'', ∃ q : ℚ, 0 < q ∧ (q : ℝ) < rbar ∧
        BadENN i j hij ν f y α (q : ℝ) := fun y hy => hy.1.2
    have hY''ball : ∀ y ∈ Y'', ∀ u ∈ (ballU hij rbar : Set SL3), u • y ∈ atom m y :=
      fun y hy u hu => hball y hy.2 u hu
    have hpoint : ∀ x ∈ Z ∩ X', ENNReal.ofReal α *
        ν x {u : SL3 | u ∈ shape m (Uij hij) x ∧ u • x ∈ Y''}
        ≤ (N : ENNReal) * ∫⁻ u in shape m (Uij hij) x,
            ENNReal.ofReal (f (u • x)) ∂(ν x) :=
      fun x hx => atom_bad_bound N hcover i j hij μ ν X' hν f hf α rbar hrbarpos m Z
        hZfree hplaque Y'' hY''sub hY''bad hY''ball x hx.1 hx.2
    have hcon : α * (μ Y'').toReal ≤ (N : ℝ) * ∫ x, f x ∂μ :=
      condexp_atom_bound_borel N i j hij μ ν X' hν f hf hf0 hfint α hα Z Y''
        hY''meas hY''Z m hplaque hpoint
    -- measure bookkeeping: `Y''` is almost all of `Y`
    have hGG : μ Gᶜ ≤ ENNReal.ofReal ε := by
      have hε0 : (0 : ℝ) ≤ ε := le_of_lt hε
      have hcomp : μ Gᶜ = 1 - μ G := by
        rw [measure_compl (μ := μ) hGb (measure_ne_top _ _), measure_univ]
      have hsub : 1 - ENNReal.ofReal (1 - ε) = ENNReal.ofReal ε := by
        have h1 : ENNReal.ofReal (1 - (1 - ε)) = ENNReal.ofReal 1 - ENNReal.ofReal (1 - ε) :=
          ENNReal.ofReal_sub 1 (by linarith)
        have h2 : (1 : ℝ) - (1 - ε) = ε := by ring
        rw [h2, ENNReal.ofReal_one] at h1
        exact h1.symm
      calc μ Gᶜ = 1 - μ G := hcomp
        _ ≤ 1 - ENNReal.ofReal (1 - ε) := tsub_le_tsub_left hGmeas_le 1
        _ = ENNReal.ofReal ε := hsub
    have hYle : μ Y ≤ μ Y'' + ENNReal.ofReal ε := by
      have hsub : Y ⊆ Y'' ∪ Gᶜ := by
        intro x hx
        by_cases hxG : x ∈ G
        · exact Or.inl ⟨hx, hxG⟩
        · exact Or.inr hxG
      calc μ Y ≤ μ (Y'' ∪ Gᶜ) := measure_mono hsub
        _ ≤ μ Y'' + μ Gᶜ := measure_union_le _ _
        _ ≤ μ Y'' + ENNReal.ofReal ε := by gcongr
    -- real-valued estimates
    have hreal : (μ Y'').toReal ≤ (N : ℝ) * (∫ x, f x ∂μ) / α := by
      refine (le_div_iff₀ hα).mpr ?_
      linarith [hcon]
    have hYfin : (μ Y).toReal ≤ (μ Y'').toReal + ε := by
      have hne : μ Y'' + ENNReal.ofReal ε ≠ ⊤ := by
        simp only [ne_eq, ENNReal.add_eq_top, not_or]
        exact ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩
      have h1 : (μ Y).toReal ≤ (μ Y'' + ENNReal.ofReal ε).toReal :=
        ENNReal.toReal_mono hne hYle
      rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (le_of_lt hε)] at h1
      exact h1
    have hsb : (μ Y).toReal = (μ (X' ∩ BadSetRat i j hij ν f α rbar)).toReal := by
      rw [hY]
    calc (μ (X' ∩ FrozenBadSet i j hij ν f α)).toReal
        ≤ (μ SRat).toReal := ENNReal.toReal_mono (measure_ne_top _ _) hμS
      _ ≤ (2 * μ (X' ∩ BadSetRat i j hij ν f α rbar)).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hn
      _ = 2 * (μ (X' ∩ BadSetRat i j hij ν f α rbar)).toReal := by
          rw [ENNReal.toReal_mul]; norm_num
      _ = 2 * (μ Y).toReal := by rw [hsb]
      _ ≤ 2 * ((μ Y'').toReal + ε) := by linarith
      _ ≤ 2 * ((N : ℝ) * (∫ x, f x ∂μ) / α + ε) := by linarith
      _ = 2 * (N : ℝ) * (∫ x, f x ∂μ) / α + 2 * ε := by ring
  -- let `ε → 0`
  have hnum : (μ (X' ∩ FrozenBadSet i j hij ν f α)).toReal
      ≤ 2 * (N : ℝ) * (∫ x, f x ∂μ) / α := by
    by_contra hlt
    have hlt' : 2 * (N : ℝ) * (∫ x, f x ∂μ) / α
        < (μ (X' ∩ FrozenBadSet i j hij ν f α)).toReal := not_le.mp hlt
    set gap : ℝ := (μ (X' ∩ FrozenBadSet i j hij ν f α)).toReal
        - 2 * (N : ℝ) * (∫ x, f x ∂μ) / α with hgapdef
    have hgap : 0 < gap := by rw [hgapdef]; linarith
    set ε : ℝ := min (1 / 2) (gap / 4) with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]; exact lt_min (by norm_num) (by linarith)
    have hεle : ε ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
    have hεsmall : 2 * ε ≤ gap / 2 := by
      have h1 : ε ≤ gap / 4 := min_le_right _ _
      linarith
    have hk := key ε hεpos hεle
    have hgap' : 0 < (μ (X' ∩ FrozenBadSet i j hij ν f α)).toReal
        - 2 * (N : ℝ) * (∫ x, f x ∂μ) / α := by
      rw [hgapdef] at hgap; exact hgap
    have hle : 2 * (N : ℝ) * (∫ x, f x ∂μ) / α + 2 * ε
        ≤ (μ (X' ∩ FrozenBadSet i j hij ν f α)).toReal := by
      linarith [hgap', hεsmall]
    linarith [hk, hle]
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hnum

end Work.EKLComp

namespace Work.EKLComp

theorem prove_MaxLeaf : Work.EKLContract.P_MaxLeaf := by
  obtain ⟨N, hNpos, hN⟩ := besicovitch_intervals
  refine ⟨2 * (N : ℝ), by positivity, ?_⟩
  intro μ _ hA i j hij ν X' hν f hf hf0 hfint α hα
  exact maxLeaf_core N hNpos hN i j hij μ hA ν X' hν f hf hf0 hfint α hα

end Work.EKLComp
