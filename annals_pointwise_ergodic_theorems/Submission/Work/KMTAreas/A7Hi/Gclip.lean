import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpAux
import Submission.Port.Aesm

namespace Work.KMTAreas.A7Hi

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

noncomputable section

/-- **The clipping set `core ∧ Farey(·, 0)` is a tail** (the `g`-side level `l₂`). -/
private lemma core_farey_iff_le_zeroG {ρ : ℝ} {C₀ : ℕ} {Cρc : ℝ} {l₁ l₂ k₁ k₂ : ℕ}
    {a : ℕ → NNReal} (hamono : Monotone a)
    (h : ∃ n, Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
      Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n) :
    ∃ n₀, ∀ n, (Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
      Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n) ↔ n₀ ≤ n := by
  classical
  refine ⟨Nat.find h, fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · by_contra hcon
    rw [not_le] at hcon
    exact Nat.find_min h hcon hn
  · exact ⟨Work.KMTAreas.A7.core_mono hamono hn (Nat.find_spec h).1,
      Work.KMTAreas.A7.farey_mono hamono hn (Nat.find_spec h).2⟩

/-- **Clipping the `g`-side low-pass variational estimate at the core-and-Farey scales.** -/
theorem lacunaryBumpLowpassClipBoundG (d : ℕ) (hd : 1 ≤ d) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (C₀ : ℕ) (Cρc Cρ : ℝ) (hCρpos : 0 < Cρ) (hCρc : Cρ ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ)
    (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (C : ℝ) (hCpos : 0 < C)
    (hLow : ∀ (k : ℤ) (l₂ : ℕ) (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (g : ℤ → ℂ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ k →
      (∀ n : ℕ, -((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
          (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₂ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm g p MeasureTheory.Measure.count) :
    ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (l l₁ l₂ k₁ k₂ : ℕ) (hl : l ≤ l₂) (g : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
            Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
          then Work.KMTAreas.A7.Tle ρ l
            (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (3 * C * (1 + (l₂ : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  intro a ha ha1 l l₁ l₂ k₁ k₂ hl g
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpT : p ≠ ⊤ := hptop.ne
  have hamono : Monotone a := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    have h2 : Λ < a (n + 1) / a n := ha n
    have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
    have h3 : a n ≤ Λ * a n := by
      simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
    exact le_trans h3 h1.le
  by_cases hne : ∃ n : ℕ,
      Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
  · obtain ⟨n₀, hn₀⟩ := core_farey_iff_le_zeroG (ρ := ρ) (C₀ := C₀) (Cρc := Cρc)
      (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂) (a := a) hamono hne
    have ha' : PointwiseErgodicTheorems.Lacunary Λ (fun m : ℕ => a (m + n₀)) := by
      intro m
      have h := ha (m + n₀)
      simpa [Nat.add_right_comm] using h
    have ha1' : ∀ m : ℕ, 1 ≤ a (m + n₀) := fun m => ha1 (m + n₀)
    have hGood : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (Work.KMTAreas.A7.fareyK Cρc ρ l₂) :=
      Work.KMTAreas.A7.goodMajorArcs_fareyK hCρc hCρpos.le hρ.le hl
    have hFarey₀ : Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n₀ := ((hn₀ n₀).mpr le_rfl).2
    have hnar : ∀ m : ℕ,
        -((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (m + n₀))))
          ≤ Work.KMTAreas.A7.fareyK Cρc ρ l₂ := by
      intro m
      have hfloor : Nat.floor (a n₀) ≤ Nat.floor (a (m + n₀)) :=
        Nat.floor_mono (hamono (Nat.le_add_left n₀ m))
      have hlog := Work.KMTAreas.A7.logN_monotone hfloor
      have hF : -(Work.Analysis.EndVar.logN (Nat.floor (a n₀)))
          ≤ Work.KMTAreas.A7.fareyK Cρc ρ l₂ := by
        simp only [Work.KMTAreas.A7.Farey] at hFarey₀
        simpa using hFarey₀
      have hlog0 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a (m + n₀))) :=
        Int.natCast_nonneg _
      have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
      nlinarith [hF, hlog, hlog0, hdZ]
    have hlow := hLow (Work.KMTAreas.A7.fareyK Cρc ρ l₂) l (fun m : ℕ => a (m + n₀)) ha' ha1' g hGood hnar
    have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
              Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
            then Work.KMTAreas.A7.Tle ρ l
              (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0)
        ≤ 3 * PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
              (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x) := by
      intro x
      have hrewrite : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
              Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
            then Work.KMTAreas.A7.Tle ρ l
              (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0)
          = fun n : ℕ => if n < n₀ then 0
              else Work.KMTAreas.A7.Tle ρ l
                (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (n - n₀ + n₀))) 0) g x := by
        funext n
        by_cases hn : n < n₀
        · have hnf : ¬ (Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
              Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n) :=
            fun hcon => absurd ((hn₀ n).mp hcon) (not_le.mpr hn)
          rw [if_neg hnf, if_pos hn]
        · have hle : n₀ ≤ n := le_of_not_gt hn
          have hf : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
              Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n := (hn₀ n).mpr hle
          rw [if_pos hf, if_neg hn, Nat.sub_add_cancel hle]
      rw [hrewrite]
      exact Submission.PointwiseErgodicTheorems.variationalNorm_prependZeros_le hr1 n₀
        (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
          (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x)
    have hmono : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
              Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
            then Work.KMTAreas.A7.Tle ρ l
              (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0))
          p MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ => (3 : ENNReal) *
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
                (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x)) p
          MeasureTheory.Measure.count :=
      MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpt
    have hconst : MeasureTheory.eLpNorm (fun x : ℤ => (3 : ENNReal) *
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
                (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x)) p
          MeasureTheory.Measure.count
        ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r
                (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
                  (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x)) p
          MeasureTheory.Measure.count :=
      le_of_eq (Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := (3 : ENNReal))
        (by norm_num) hp0 hpT)
    have hbound : 3 * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r
                (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
                  (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x)) p
          MeasureTheory.Measure.count
        ≤ 3 * (ENNReal.ofReal (C * (1 + (l : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm g p MeasureTheory.Measure.count) :=
      mul_le_mul_of_nonneg_left hlow zero_le
    have hArith : (3 : ENNReal) * (ENNReal.ofReal (C * (1 + (l : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm g p MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (3 * C * (1 + (l₂ : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
      have hA : 3 * (C * (1 + (l : ℝ)) ^ 2) ≤ 3 * C * (1 + (l₂ : ℝ)) ^ 2 := by
        have hl' : (l : ℝ) ≤ (l₂ : ℝ) := by exact_mod_cast hl
        have hsq : (1 + (l : ℝ)) ^ 2 ≤ (1 + (l₂ : ℝ)) ^ 2 := by nlinarith
        nlinarith [hsq, hCpos]
      have hthree : (3 : ENNReal) * ENNReal.ofReal (C * (1 + (l : ℝ)) ^ 2)
          ≤ ENNReal.ofReal (3 * C * (1 + (l₂ : ℝ)) ^ 2) := by
        rw [show (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        exact ENNReal.ofReal_le_ofReal hA
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hthree zero_le
    exact hmono.trans (hconst.trans (hbound.trans hArith))
  · have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
              Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
            then Work.KMTAreas.A7.Tle ρ l
              (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0)) = 0 := by
      funext x
      have hfam : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
              Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
            then Work.KMTAreas.A7.Tle ρ l
              (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0)
          = (0 : ℕ → ℂ) := by
        funext n
        rw [if_neg (fun hcon => hne ⟨n, hcon⟩)]
        rfl
      have h0 : PointwiseErgodicTheorems.variationalNorm r (0 : ℕ → ℂ) = 0 := by
        have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul
          (r := r) hr1 (0 : ℂ) (0 : ℕ → ℂ)
        simpa using h
      rw [hfam, h0]
      rfl
    rw [hzero, MeasureTheory.eLpNorm_zero]
    exact zero_le

end

end Work.KMTAreas.A7Hi
