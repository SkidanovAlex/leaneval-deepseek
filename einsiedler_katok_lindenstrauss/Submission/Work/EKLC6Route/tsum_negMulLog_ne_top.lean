import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLComp.C6EntropyBook
import Submission.Work.EKLC6Core.summable_mul_toReal_firstReturnSet_le_one
import Submission.Work.EKLC6Core.firstReturn_partition
import Submission.Work.EKLC6Core.neverReturnSet_null
import Submission.Work.EKLC6Route.L7Aux
import Submission.Work.EKLC6Route.piece_partition
import Submission.Work.EKLC6Route.piece_measurable
import Submission.Work.EKLC6Route.window_defs
import Submission.Work.EKLC6Route.tsum_S_eq_tsum_piece
import Submission.Work.EKLC6Route.exists_cellFinset
import Submission.Work.EKLC6Route.cellCount_le
import Submission.Work.EKLC6Route.tsum_jIdx_mass_Jset_le
import Submission.Work.EKLC6Route.L7EntropySelf

namespace Work.EKLC6Route

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The summand of the entropy series of the window partition: `s ↦ ofReal (negMulLog (μ s).toReal)`. -/
def entSummand (μ : MeasureTheory.Measure Work.EKLContract.X3) (s : Set Work.EKLContract.X3) :
    ℝ≥0∞ :=
  ENNReal.ofReal (Real.negMulLog ((μ s).toReal))

@[simp] theorem entSummand_empty (μ : MeasureTheory.Measure Work.EKLContract.X3) :
    entSummand μ ∅ = 0 := by
  simp [entSummand]

/-- `betaExp t ≥ 0`. -/
theorem betaExp_nonneg__tsum_negMulLog_ne_top (t : Fin 3 → ℝ) : 0 ≤ betaExp t := by
  have h := Finset.le_sup' (s := Finset.univ) (fun p : Fin 3 × Fin 3 => |t p.1 - t p.2|)
    (Finset.mem_univ ((0, 0) : Fin 3 × Fin 3))
  simpa [betaExp] using h

theorem tsum_negMulLog_ne_top {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Work.EKLC6Route.Window μ t)
    (hmp : MeasureTheory.MeasurePreserving (Work.EKLC6Route.Tm t) μ μ) :
    (∑' n : ℕ, ENNReal.ofReal (Real.negMulLog ((μ (w.S n)).toReal))) ≠ ⊤ := by
  classical
  -- ## 0. Basic facts
  have hW : MeasurableSet w.W := (piece_measurable w).1
  have hle1 : ∀ s : Set Work.EKLContract.X3, μ s ≤ 1 := fun s => by
    calc μ s ≤ μ Set.univ := measure_mono (Set.subset_univ s)
      _ = 1 := measure_univ
  have hent_le_one : ∀ s : Set Work.EKLContract.X3, entSummand μ s ≤ 1 := by
    intro s
    have h1 : (μ s).toReal ≤ 1 := by
      calc (μ s).toReal ≤ (1 : ℝ≥0∞).toReal :=
            ENNReal.toReal_mono ENNReal.one_ne_top (hle1 s)
        _ = 1 := by simp
    have h2 : Real.negMulLog ((μ s).toReal) ≤ 1 := by
      have h := Real.negMulLog_le_one_sub_self (x := (μ s).toReal) ENNReal.toReal_nonneg
      have hx : (0 : ℝ) ≤ (μ s).toReal := ENNReal.toReal_nonneg
      linarith
    calc entSummand μ s = ENNReal.ofReal (Real.negMulLog ((μ s).toReal)) := rfl
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h2
      _ = 1 := ENNReal.ofReal_one
  have hfr_meas : ∀ i : ℕ, MeasurableSet (Work.EKLC6Core.firstReturnSet t w.W i) :=
    (Work.EKLC6Core.firstReturn_partition (t := t) hW).1
  have hDmeas : ∀ (i : ℕ) (J : Option ℕ) (c : Fin 3 → Fin 3 → ℤ),
      MeasurableSet (w.D i J c) := by
    intro i J c
    have h := (piece_measurable w).2.2.2 (some (some (i, J, c)))
    exact h
  have hDdisj : ∀ (i : ℕ) (J : Option ℕ) (c : Fin 3 → Fin 3 → ℤ)
      (i' : ℕ) (J' : Option ℕ) (c' : Fin 3 → Fin 3 → ℤ),
      (i, J, c) ≠ (i', J', c') → Disjoint (w.D i J c) (w.D i' J' c') :=
    fun i J c i' J' c' h => Window.D_disjoint w hW h
  -- ## 1. The level/depth mass bounds
  have hlevel : ∀ i : ℕ,
      (∑' J : Option ℕ, ∑' c : Fin 3 → Fin 3 → ℤ, μ (w.D i J c))
        ≤ ENNReal.ofReal ((μ (Work.EKLC6Core.firstReturnSet t w.W i)).toReal) := by
    intro i
    rw [show (∑' J : Option ℕ, ∑' c : Fin 3 → Fin 3 → ℤ, μ (w.D i J c))
        = ∑' p : Option ℕ × (Fin 3 → Fin 3 → ℤ), μ (w.D i p.1 p.2) from
      (ENNReal.tsum_prod' (f := fun p : Option ℕ × (Fin 3 → Fin 3 → ℤ) =>
        μ (w.D i p.1 p.2))).symm]
    rw [← measure_iUnion
      (f := fun p : Option ℕ × (Fin 3 → Fin 3 → ℤ) => w.D i p.1 p.2)
      (by
        rintro ⟨J, c⟩ ⟨J', c'⟩ hne
        exact hDdisj i J c i J' c' (by
          intro hc; exact hne ((Prod.ext_iff.mp hc).2)))
      (fun p => hDmeas i p.1 p.2)]
    calc μ (⋃ p : Option ℕ × (Fin 3 → Fin 3 → ℤ), w.D i p.1 p.2)
        ≤ μ (Work.EKLC6Core.firstReturnSet t w.W i) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
          exact ((w.mem_D).1 hp).2.1
      _ = ENNReal.ofReal ((μ (Work.EKLC6Core.firstReturnSet t w.W i)).toReal) :=
          (ENNReal.ofReal_toReal
            (ne_top_of_le_ne_top ENNReal.one_ne_top (hle1 _))).symm
  have he0 : ∀ J : Option ℕ, 0 ≤ (μ (w.Jset J)).toReal := fun J => ENNReal.toReal_nonneg
  have hdepth : ∀ J : Option ℕ,
      (∑' i : ℕ, ∑' c : Fin 3 → Fin 3 → ℤ, μ (w.D i J c))
        ≤ ENNReal.ofReal ((μ (w.Jset J)).toReal) := by
    intro J
    rw [show (∑' i : ℕ, ∑' c : Fin 3 → Fin 3 → ℤ, μ (w.D i J c))
        = ∑' p : ℕ × (Fin 3 → Fin 3 → ℤ), μ (w.D p.1 J p.2) from
      (ENNReal.tsum_prod' (f := fun p : ℕ × (Fin 3 → Fin 3 → ℤ) =>
        μ (w.D p.1 J p.2))).symm]
    rw [← measure_iUnion
      (f := fun p : ℕ × (Fin 3 → Fin 3 → ℤ) => w.D p.1 J p.2)
      (by
        rintro ⟨i, c⟩ ⟨i', c'⟩ hne
        exact hDdisj i J c i' J c' (by
          intro hc
          have h1 : i = i' := (Prod.ext_iff.mp hc).1
          have h2 : (J, c) = (J, c') := (Prod.ext_iff.mp hc).2
          have h3 : c = c' := (Prod.ext_iff.mp h2).2
          exact hne (by rw [h1, h3])))
      (fun p => hDmeas p.1 J p.2)]
    calc μ (⋃ p : ℕ × (Fin 3 → Fin 3 → ℤ), w.D p.1 J p.2)
        ≤ μ (w.Jset J) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
          exact ((w.mem_D).1 hp).2.2.1
      _ = ENNReal.ofReal ((μ (w.Jset J)).toReal) :=
          (ENNReal.ofReal_toReal
            (ne_top_of_le_ne_top ENNReal.one_ne_top (hle1 _))).symm
  -- ## 2. The two summability inputs
  have hkac : (∑' i : ℕ, ENNReal.ofReal
      ((i : ℝ) * (μ (Work.EKLC6Core.firstReturnSet t w.W i)).toReal)) ≤ 1 :=
    (Work.EKLComp.kac_return_ineq (μ := μ) (t := t) hmp hW).1
  have hqsum : (∑' i : ℕ, ENNReal.ofReal
      ((μ (Work.EKLC6Core.firstReturnSet t w.W i)).toReal)) ≤ 2 := by
    rw [tsum_eq_zero_add' (f := fun i : ℕ =>
      ENNReal.ofReal ((μ (Work.EKLC6Core.firstReturnSet t w.W i)).toReal)) ENNReal.summable]
    have h0 : ENNReal.ofReal ((μ (Work.EKLC6Core.firstReturnSet t w.W 0)).toReal) ≤ 1 := by
      rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hle1 _))]
      exact hle1 _
    have htail : (∑' i : ℕ, ENNReal.ofReal
        ((μ (Work.EKLC6Core.firstReturnSet t w.W (i + 1))).toReal)) ≤ 1 := by
      have htoReal : ∀ i : ℕ, ENNReal.ofReal
          ((μ (Work.EKLC6Core.firstReturnSet t w.W (i + 1))).toReal)
          = μ (Work.EKLC6Core.firstReturnSet t w.W (i + 1)) :=
        fun i => ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hle1 _))
      rw [tsum_congr htoReal]
      rw [← measure_iUnion (f := fun i : ℕ => Work.EKLC6Core.firstReturnSet t w.W (i + 1))
        (fun i i' hii => (Work.EKLC6Core.firstReturn_partition (t := t) hW).2.2.1
          (i + 1) (i' + 1) (by omega) (by omega) (by omega))
        (fun i => hfr_meas (i + 1))]
      calc μ (⋃ i : ℕ, Work.EKLC6Core.firstReturnSet t w.W (i + 1)) ≤ μ Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    calc ENNReal.ofReal ((μ (Work.EKLC6Core.firstReturnSet t w.W 0)).toReal)
          + (∑' i : ℕ, ENNReal.ofReal
              ((μ (Work.EKLC6Core.firstReturnSet t w.W (i + 1))).toReal))
        ≤ 1 + 1 := add_le_add h0 htail
      _ = 2 := by norm_num
  -- ## 3. The entropy lemma
  have htriple : (∑' p : ℕ × (Option ℕ × (Fin 3 → Fin 3 → ℤ)),
      ENNReal.ofReal (Real.negMulLog ((μ (w.D p.1 p.2.1 p.2.2)).toReal))) ≠ ⊤ :=
    tsum_negMulLog_cellDepth_self (E := fun i J c => w.D i J c)
      (q := fun i => (μ (Work.EKLC6Core.firstReturnSet t w.W i)).toReal)
      (e := fun J => (μ (w.Jset J)).toReal)
      (D := fun i J c => w.D i J c)
      (C := fun i => Classical.choose (exists_cellFinset w.ρ w.hρ (gridLev t i) t))
      (N := fun i => cellCount t i)
      (c₀ := (7 : ℝ) ^ 9) (κ := 9 * betaExp t)
      hDmeas hDdisj (fun i => ENNReal.toReal_nonneg) hlevel hqsum hkac
      (fun J => ENNReal.toReal_nonneg) hdepth
      (tsum_jIdx_mass_Jset_le w)
      (fun i J c => le_rfl)
      (fun i => (Classical.choose_spec (exists_cellFinset w.ρ w.hρ (gridLev t i) t)).2.1)
      (fun i J c hc => by
        by_contra hne
        obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
        obtain ⟨-, -, hxJ, hxg, -⟩ := (w.mem_D).1 hx
        have hxW : w.θ x ∈ VtSet t ∩ Work.EKLContract.V w.ρ := by
          have h := Window.Jset_subset_W w J hxJ
          simp only [Window.W, chartSet, Set.mem_ofPred_eq] at h
          exact h.2.1
        have hmem := (Classical.choose_spec (exists_cellFinset w.ρ w.hρ (gridLev t i) t)).1
          (w.θ x) hxW
        rw [hxg] at hmem
        exact hc hmem)
      (fun i => (Classical.choose_spec (exists_cellFinset w.ρ w.hρ (gridLev t i) t)).2.2)
      (fun i => one_le_cellCount t i)
      (by positivity) (by have := betaExp_nonneg__tsum_negMulLog_ne_top t; positivity)
      (fun i => cellCount_le t i)
  -- ## 4. Reindex, split, conclude
  have hreindex : (∑' n : ℕ, entSummand μ (w.S n)) = ∑' p : Window.PIdx, entSummand μ (w.piece p) :=
    tsum_S_eq_tsum_piece w (entSummand μ) (entSummand_empty μ)
  have hsplit : (∑' p : Window.PIdx, entSummand μ (w.piece p)) ≤
      entSummand μ (w.piece none) + entSummand μ (w.piece (some none)) +
        ∑' q : ℕ × (Option ℕ × (Fin 3 → Fin 3 → ℤ)),
          entSummand μ (w.piece (some (some q))) := by
    have h1 := tsum_option_le (fun x : Option (Option (ℕ × (Option ℕ × (Fin 3 → Fin 3 → ℤ)))) =>
      entSummand μ (w.piece x))
    have h2 := tsum_option_le (fun x : Option (ℕ × (Option ℕ × (Fin 3 → Fin 3 → ℤ))) =>
      entSummand μ (w.piece (some x)))
    calc (∑' p : Window.PIdx, entSummand μ (w.piece p))
        ≤ entSummand μ (w.piece none) +
            ∑' x : Option (ℕ × (Option ℕ × (Fin 3 → Fin 3 → ℤ))), entSummand μ (w.piece (some x)) :=
          h1
      _ ≤ entSummand μ (w.piece none) + (entSummand μ (w.piece (some none)) +
            ∑' q : ℕ × (Option ℕ × (Fin 3 → Fin 3 → ℤ)), entSummand μ (w.piece (some (some q)))) :=
          add_le_add le_rfl h2
      _ = entSummand μ (w.piece none) + entSummand μ (w.piece (some none)) +
            ∑' q : ℕ × (Option ℕ × (Fin 3 → Fin 3 → ℤ)), entSummand μ (w.piece (some (some q))) := by
          rw [add_assoc]
  have htripleEnt : (∑' q : ℕ × (Option ℕ × (Fin 3 → Fin 3 → ℤ)),
      entSummand μ (w.piece (some (some q)))) ≠ ⊤ := by
    have hEq : ∀ q : ℕ × (Option ℕ × (Fin 3 → Fin 3 → ℤ)),
        entSummand μ (w.piece (some (some q)))
          = ENNReal.ofReal (Real.negMulLog ((μ (w.D q.1 q.2.1 q.2.2)).toReal)) := fun q => rfl
    rw [tsum_congr hEq]
    exact htriple
  have hmain : (∑' n : ℕ, entSummand μ (w.S n)) < ⊤ := by
    rw [hreindex]
    refine lt_of_le_of_lt hsplit ?_
    rw [ENNReal.add_lt_top, ENNReal.add_lt_top]
    exact ⟨⟨lt_of_le_of_lt (hent_le_one _) ENNReal.one_lt_top,
      lt_of_le_of_lt (hent_le_one _) ENNReal.one_lt_top⟩,
      lt_top_iff_ne_top.mpr htripleEnt⟩
  exact ne_of_lt hmain

end

end Work.EKLC6Route
