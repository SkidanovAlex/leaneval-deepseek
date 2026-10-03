import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpAux
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

/-- **The clipping set `core ∧ Farey(·, 0)` is a tail.**  Both `core` and `Farey` are upward
closed in the scale index (`core_mono`, `farey_mono`), so the set of scales satisfying both is
`{n | n₀ ≤ n}` for its least element `n₀`.  (This is `core_and_farey_iff_le` with the Farey level
`k₁ = 0` used by the low-pass family `varphiN · 0`.) -/
private lemma core_farey_iff_le_zero {ρ : ℝ} {C₀ : ℕ} {Cρc : ℝ} {l₁ l₂ k₁ k₂ : ℕ}
    {a : ℕ → NNReal} (hamono : Monotone a)
    (h : ∃ n, core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ 0 a n) :
    ∃ n₀, ∀ n, (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ 0 a n) ↔ n₀ ≤ n := by
  classical
  refine ⟨Nat.find h, fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · by_contra hcon
    rw [not_le] at hcon
    exact Nat.find_min h hcon hn
  · exact ⟨core_mono hamono hn (Nat.find_spec h).1, farey_mono hamono hn (Nat.find_spec h).2⟩

/-- **Clipping the low-pass variational estimate at the core-and-Farey scales.**

The input `hLow` is the (delegated) low-pass estimate `lacunaryIWProjLowpassVar`: it bounds the
`r`-variation of the *unclipped* low-pass family `n ↦ Tle ρ l₁ (varphiN ⌊a n⌋ 0) f` whenever the
family is narrow at a level `k` with good major arcs.  The statement below is the *clipped*
version actually needed by the assembly: the family is replaced by its restriction to the scales
`core ∧ Farey` (which, since both predicates are upward closed, is a tail `{n₀ ≤ n}` of the index
set), and the multiplier is allowed to have height `l ≤ l₁`.

The only two ingredients are:
* the index shift: the clipped family is the tail of the family read along `a' m := a (m + n₀)`,
  so `hLow` can be applied to `a'` with the *same* narrowness level `k = fareyK Cρc ρ l₁`
  (`goodMajorArcs_fareyK` for the major-arc hypothesis, and monotonicity of `a` plus the Farey
  condition at `n₀` for the narrowness);
* the elementary clipping lemma `variationalNorm_prependZeros_le`, which costs a factor `3` —
  this is where the `3 * C` of the conclusion comes from.

The height `l ≤ l₁` is handled by applying `hLow` at the *parameter* `l` and using
`(1 + l) ^ 2 ≤ (1 + l₁) ^ 2`; the hypothesis `GoodMajorArcs ρ Cρ l (fareyK Cρc ρ l₁)` requires
exactly `l ≤ l₁`. -/
theorem lacunaryBumpLowpassClipBoundGen (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ)
    (Cρc Cρ : ℝ) (hCρpos : 0 < Cρ) (hCρc : Cρ ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ)
    (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (C : ℝ) (hCpos : 0 < C)
    (hLow : ∀ (k : ℤ) (l₁ : ℕ) (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ k →
      (∀ n : ℕ, -(Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
          (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (l l₁ l₂ k₁ k₂ : ℕ) (hl : l ≤ l₁) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
            Work.KMTAreas.A7.Farey Cρc ρ l₁ 0 a n
          then Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x else 0))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (3 * C * (1 + (l₁ : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  intro a ha ha1 l l₁ l₂ k₁ k₂ hl f
  classical
  -- `1 ≤ r`
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  -- `p ≠ 0` and `p ≠ ⊤`
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpT : p ≠ ⊤ := hptop.ne
  -- `a` is monotone
  have hamono : Monotone a := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    have h2 : Λ < a (n + 1) / a n := ha n
    have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
    have h3 : a n ≤ Λ * a n := by
      simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
    exact le_trans h3 h1.le
  by_cases hne : ∃ n : ℕ,
      core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ 0 a n
  · -- ## the nonempty case: the clipped set is the tail `{n₀ ≤ n}`
    obtain ⟨n₀, hn₀⟩ := core_farey_iff_le_zero (ρ := ρ) (C₀ := C₀) (Cρc := Cρc)
      (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂) (a := a) hamono hne
    -- the tail sequence is lacunary
    have ha' : PointwiseErgodicTheorems.Lacunary Λ (fun m : ℕ => a (m + n₀)) := by
      intro m
      have h := ha (m + n₀)
      simpa [Nat.add_right_comm] using h
    have ha1' : ∀ m : ℕ, 1 ≤ a (m + n₀) := fun m => ha1 (m + n₀)
    -- good major arcs at level `l`
    have hGood : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (fareyK Cρc ρ l₁) :=
      goodMajorArcs_fareyK hCρc hCρpos.le hρ.le hl
    -- narrowness of the tail sequence
    have hFarey₀ : Farey Cρc ρ l₁ 0 a n₀ := ((hn₀ n₀).mpr le_rfl).2
    have hnar : ∀ m : ℕ,
        -(Work.Analysis.EndVar.logN (Nat.floor (a (m + n₀)))) ≤ fareyK Cρc ρ l₁ := by
      intro m
      have hfloor : Nat.floor (a n₀) ≤ Nat.floor (a (m + n₀)) :=
        Nat.floor_mono (hamono (Nat.le_add_left n₀ m))
      have hlog := logN_monotone hfloor
      have hF : -(Work.Analysis.EndVar.logN (Nat.floor (a n₀))) ≤ fareyK Cρc ρ l₁ := by
        simp only [Farey] at hFarey₀
        simpa using hFarey₀
      linarith
    -- the low-pass estimate for the tail sequence
    have hlow := hLow (fareyK Cρc ρ l₁) l (fun m : ℕ => a (m + n₀)) ha' ha1' f hGood hnar
    -- ## the pointwise clipping inequality
    have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ 0 a n
            then Tle ρ l (varphiN (Nat.floor (a n)) 0) f x else 0)
        ≤ 3 * PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => Tle ρ l (varphiN (Nat.floor (a (m + n₀))) 0) f x) := by
      intro x
      have hrewrite : (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ 0 a n
            then Tle ρ l (varphiN (Nat.floor (a n)) 0) f x else 0)
          = fun n : ℕ => if n < n₀ then 0
              else Tle ρ l (varphiN (Nat.floor (a (n - n₀ + n₀))) 0) f x := by
        funext n
        by_cases hn : n < n₀
        · have hnf : ¬ (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ 0 a n) :=
            fun hcon => absurd ((hn₀ n).mp hcon) (not_le.mpr hn)
          rw [if_neg hnf, if_pos hn]
        · have hle : n₀ ≤ n := le_of_not_gt hn
          have hf : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ 0 a n := (hn₀ n).mpr hle
          rw [if_pos hf, if_neg hn, Nat.sub_add_cancel hle]
      rw [hrewrite]
      exact Submission.PointwiseErgodicTheorems.variationalNorm_prependZeros_le hr1 n₀
        (fun m : ℕ => Tle ρ l (varphiN (Nat.floor (a (m + n₀))) 0) f x)
    -- ## the `eLpNorm` assembly
    have hmono : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ 0 a n
            then Tle ρ l (varphiN (Nat.floor (a n)) 0) f x else 0)) p MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ => (3 : ENNReal) *
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => Tle ρ l (varphiN (Nat.floor (a (m + n₀))) 0) f x)) p
          MeasureTheory.Measure.count :=
      MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpt
    have hconst : MeasureTheory.eLpNorm (fun x : ℤ => (3 : ENNReal) *
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => Tle ρ l (varphiN (Nat.floor (a (m + n₀))) 0) f x)) p
          MeasureTheory.Measure.count
        ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r
                (fun m : ℕ => Tle ρ l (varphiN (Nat.floor (a (m + n₀))) 0) f x)) p
          MeasureTheory.Measure.count :=
      le_of_eq (Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := (3 : ENNReal))
        (by norm_num) hp0 hpT)
    have hbound : 3 * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r
                (fun m : ℕ => Tle ρ l (varphiN (Nat.floor (a (m + n₀))) 0) f x)) p
          MeasureTheory.Measure.count
        ≤ 3 * (ENNReal.ofReal (C * (1 + (l : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :=
      mul_le_mul_of_nonneg_left hlow zero_le
    have hArith : (3 : ENNReal) * (ENNReal.ofReal (C * (1 + (l : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (3 * C * (1 + (l₁ : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
      have hA : 3 * (C * (1 + (l : ℝ)) ^ 2) ≤ 3 * C * (1 + (l₁ : ℝ)) ^ 2 := by
        have hl' : (l : ℝ) ≤ (l₁ : ℝ) := by exact_mod_cast hl
        have hsq : (1 + (l : ℝ)) ^ 2 ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith
        nlinarith [hsq, hCpos]
      have hthree : (3 : ENNReal) * ENNReal.ofReal (C * (1 + (l : ℝ)) ^ 2)
          ≤ ENNReal.ofReal (3 * C * (1 + (l₁ : ℝ)) ^ 2) := by
        rw [show (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        exact ENNReal.ofReal_le_ofReal hA
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hthree zero_le
    exact hmono.trans (hconst.trans (hbound.trans hArith))
  · -- ## the empty case: the family vanishes identically
    have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ 0 a n
            then Tle ρ l (varphiN (Nat.floor (a n)) 0) f x else 0)) = 0 := by
      funext x
      have hfam : (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ 0 a n
            then Tle ρ l (varphiN (Nat.floor (a n)) 0) f x else 0) = (0 : ℕ → ℂ) := by
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

end Work.KMTAreas.A7
