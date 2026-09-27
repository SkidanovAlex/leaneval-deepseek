import Mathlib
import Submission.Work.EKLComp.MaxLeafDefs
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Lemmas.Box1_Uij

/-!
# Rational radius for the bad set of `BadENN`

`BadENN i j hij ν f x α r` is the `ℝ≥0∞`-form bad condition at scale `r`:

  `ofReal α * ν x (ballU hij r) < ∫⁻ g in ballU hij r, ofReal (f (g • x)) ∂(ν x)`.

The point of the present file is that the bad condition at *any* radius `r > 0` can be
realised at a *rational* radius arbitrarily close to `r` (from the right, and below any
prescribed `rbar > r`).  Concretely, the set of radii at which the bad condition holds is
open to the right in `(0, ∞)`:

* the integral side `A(s) = ∫⁻_{ballU s} ofReal (f (· • x))` is monotone in `s`, so
  `A(s) ≥ A(r)` for `s ≥ r`;
* the measure side `B(s) = ofReal α * ν x (ballU s)` is continuous *from above* at `r > 0`
  (continuity from above of a finite measure on the decreasing family
  `ballU (r + 1/(n+1)) ↓ ballU r`), so `B(s)` stays strictly below any `δ ∈ (B(r), A(r))`
  for `s` close to `r`.

Since `ℚ` is dense, an interval `(r, r + η) ∩ (0, rbar)` contains a rational `q`, which gives
the desired witness.
-/

set_option linter.unusedVariables false

namespace Work.EKLComp

open MeasureTheory Filter Topology
open scoped ENNReal

/-- `s ↦ ballU hij s` is monotone. -/
private lemma ballU_mono {i j : Fin 3} (hij : i ≠ j) {s t : ℝ} (h : s ≤ t) :
    Work.EKLContract.ballU hij s ⊆ Work.EKLContract.ballU hij t := by
  dsimp only [Work.EKLContract.ballU]
  exact Set.image_mono (Set.Icc_subset_Icc (by linarith) h)

/-- `s ↦ u_ij(s)` is injective (the `(i,j)`-entry recovers `s`). -/
private lemma uij_injective {i j : Fin 3} (hij : i ≠ j) :
    Function.Injective (fun s : ℝ => Work.EKLContract.uij hij s) := by
  intro s t hst
  have h := congrArg (fun g : Work.EKLContract.SL3 =>
      (g : Matrix (Fin 3) (Fin 3) ℝ) i j) hst
  simpa only [Work.EKLContract.Lemmas.uij_apply_self] using h

/-- `ballU hij s` is Borel measurable (it is a compact image). -/
private lemma measurableSet_ballU {i j : Fin 3} (hij : i ≠ j) (s : ℝ) :
    MeasurableSet (Work.EKLContract.ballU hij s) :=
  (isCompact_Icc.image (Work.EKLContract.Lemmas.horoUij_cont hij)).isClosed.measurableSet

/-- The decreasing balls `ballU hij (r + 1/(n+1))` intersect in `ballU hij r`. -/
private lemma iInter_ballU {i j : Fin 3} (hij : i ≠ j) (r : ℝ) :
    (⋂ n : ℕ, Work.EKLContract.ballU hij (r + ((n : ℝ) + 1)⁻¹)) =
      Work.EKLContract.ballU hij r := by
  have hinj : Set.InjOn (fun s : ℝ => Work.EKLContract.uij hij s)
      (⋃ n : ℕ, Set.Icc (-(r + ((n : ℝ) + 1)⁻¹)) (r + ((n : ℝ) + 1)⁻¹)) :=
    (uij_injective hij).injOn
  have himg : (fun s : ℝ => Work.EKLContract.uij hij s) ''
        (⋂ n : ℕ, Set.Icc (-(r + ((n : ℝ) + 1)⁻¹)) (r + ((n : ℝ) + 1)⁻¹)) =
      (⋂ n : ℕ, (fun s : ℝ => Work.EKLContract.uij hij s) ''
        Set.Icc (-(r + ((n : ℝ) + 1)⁻¹)) (r + ((n : ℝ) + 1)⁻¹)) :=
    Set.InjOn.image_iInter_eq
      (s := fun n : ℕ => Set.Icc (-(r + ((n : ℝ) + 1)⁻¹)) (r + ((n : ℝ) + 1)⁻¹))
      (f := fun s : ℝ => Work.EKLContract.uij hij s) hinj
  have hIcc : (⋂ n : ℕ, Set.Icc (-(r + ((n : ℝ) + 1)⁻¹)) (r + ((n : ℝ) + 1)⁻¹)) =
      Set.Icc (-r) r := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx' : ∀ n : ℕ, -(r + ((n : ℝ) + 1)⁻¹) ≤ x ∧ x ≤ r + ((n : ℝ) + 1)⁻¹ :=
        Set.mem_iInter.mp hx
      refine ⟨?_, ?_⟩
      · have key : ∀ ε : ℝ, 0 < ε → -x ≤ r + ε := by
          intro ε hε
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
          have h1 := (hx' n).1
          have h2 : (1 : ℝ) / ((n : ℝ) + 1) = ((n : ℝ) + 1)⁻¹ := one_div _
          linarith [h1, h2, hn]
        linarith [le_of_forall_pos_le_add key]
      · have key : ∀ ε : ℝ, 0 < ε → x ≤ r + ε := by
          intro ε hε
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
          have h1 := (hx' n).2
          have h2 : (1 : ℝ) / ((n : ℝ) + 1) = ((n : ℝ) + 1)⁻¹ := one_div _
          linarith [h1, h2, hn]
        exact le_of_forall_pos_le_add key
    · intro x hx
      rw [Set.mem_iInter]
      intro n
      have hpos : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
      exact Set.Icc_subset_Icc (by linarith) (by linarith) hx
  dsimp only [Work.EKLContract.ballU]
  rw [← himg, hIcc]

/-- **Continuity from above** of `s ↦ ν (ballU hij s)` at `r > 0`, in the form of an infimum
over the sequence `r + 1/(n+1) ↓ r`. -/
private lemma iInf_measure_ballU {i j : Fin 3} (hij : i ≠ j)
    (μ : Measure Work.EKLContract.SL3) (r : ℝ)
    (hfin : μ (Work.EKLContract.ballU hij (r + 1)) ≠ ⊤) :
    μ (Work.EKLContract.ballU hij r) =
      ⨅ n : ℕ, μ (Work.EKLContract.ballU hij (r + ((n : ℝ) + 1)⁻¹)) := by
  rw [← iInter_ballU hij r]
  refine Antitone.measure_iInter
    (s := fun n : ℕ => Work.EKLContract.ballU hij (r + ((n : ℝ) + 1)⁻¹)) ?_ ?_ ?_
  · intro m n hmn
    refine ballU_mono hij ?_
    have hmn' : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_succ hmn)
    have h1 : ((n : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ := by
      simpa using one_div_le_one_div_of_le (show (0 : ℝ) < (m : ℝ) + 1 by positivity) hmn'
    linarith
  · intro n
    exact (measurableSet_ballU hij _).nullMeasurableSet
  · refine ⟨0, ?_⟩
    have h0 : r + (((0 : ℕ) : ℝ) + 1)⁻¹ = r + 1 := by norm_num
    rw [h0]
    exact hfin

/-- **The bad set is open to the right.**  If `BadENN` holds at radius `r > 0` then it holds
at every radius in `(r, r + η)` for some `η > 0`. -/
private lemma badENN_right_open {i j : Fin 3} (hij : i ≠ j)
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    (f : Work.EKLContract.X3 → ℝ) (x : Work.EKLContract.X3) (α : ℝ) (hα : 0 < α)
    (hfin : ∀ s : ℝ, 0 < s → ν x (Work.EKLContract.ballU hij s) ≠ ⊤)
    {r : ℝ} (hr : 0 < r) (hbad : BadENN i j hij ν f x α r) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, r < s → s < r + η →
      BadENN i j hij ν f x α s := by
  have hc0 : ENNReal.ofReal α ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hα
  have hctop : ENNReal.ofReal α ≠ ⊤ := ENNReal.ofReal_lt_top.ne
  have hnu := iInf_measure_ballU hij (ν x) r (hfin (r + 1) (by linarith))
  have hBinf : ENNReal.ofReal α * ν x (Work.EKLContract.ballU hij r) =
      ⨅ n : ℕ, ENNReal.ofReal α * ν x (Work.EKLContract.ballU hij (r + ((n : ℝ) + 1)⁻¹)) := by
    rw [hnu, ENNReal.mul_iInf_of_ne hc0 hctop]
  have hbad' : ENNReal.ofReal α * ν x (Work.EKLContract.ballU hij r) <
      ∫⁻ g in Work.EKLContract.ballU hij r, ENNReal.ofReal (f (g • x)) ∂(ν x) := hbad
  obtain ⟨δ, hδ1, hδ2⟩ := exists_between hbad'
  have hltinf : (⨅ n : ℕ, ENNReal.ofReal α *
      ν x (Work.EKLContract.ballU hij (r + ((n : ℝ) + 1)⁻¹))) < δ := by
    rw [← hBinf]; exact hδ1
  obtain ⟨n, hn⟩ := iInf_lt_iff.mp hltinf
  refine ⟨((n : ℝ) + 1)⁻¹, by positivity, ?_⟩
  intro s hrs hrslt
  unfold BadENN
  have hsle : s ≤ r + ((n : ℝ) + 1)⁻¹ := le_of_lt hrslt
  have hBle : ENNReal.ofReal α * ν x (Work.EKLContract.ballU hij s) ≤
      ENNReal.ofReal α * ν x (Work.EKLContract.ballU hij (r + ((n : ℝ) + 1)⁻¹)) :=
    mul_le_mul' le_rfl (measure_mono (ballU_mono hij hsle))
  have hAle : (∫⁻ g in Work.EKLContract.ballU hij r,
        ENNReal.ofReal (f (g • x)) ∂(ν x)) ≤
      (∫⁻ g in Work.EKLContract.ballU hij s,
        ENNReal.ofReal (f (g • x)) ∂(ν x)) :=
    lintegral_mono_set (ballU_mono hij (le_of_lt hrs))
  exact lt_of_lt_of_le (lt_of_le_of_lt hBle (lt_of_lt_of_le hn (le_of_lt hδ2))) hAle

theorem exists_rat_badENN (i j : Fin 3) (hij : i ≠ j)
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    (f : Work.EKLContract.X3 → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (x : Work.EKLContract.X3) (α r rbar : ℝ) (hα : 0 < α)
    (hfin : ∀ s : ℝ, 0 < s → ν x (Work.EKLContract.ballU hij s) ≠ ⊤)
    (hr : 0 < r) (hlt : r < rbar) (hbad : Work.EKLComp.BadENN i j hij ν f x α r) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < rbar ∧
      Work.EKLComp.BadENN i j hij ν f x α (q : ℝ) := by
  obtain ⟨η, hη, hgood⟩ := badENN_right_open hij ν f x α hα hfin hr hbad
  have hlt' : r < min (r + η) rbar := lt_min (by linarith) hlt
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt'
  refine ⟨q, ?_, ?_, ?_⟩
  · exact_mod_cast (lt_trans hr hq1)
  · exact lt_of_lt_of_le hq2 (min_le_right _ _)
  · exact hgood (q : ℝ) hq1 (lt_of_lt_of_le hq2 (min_le_left _ _))

end Work.EKLComp
