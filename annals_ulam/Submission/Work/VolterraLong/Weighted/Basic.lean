import Submission.Work.VolterraLong.Defs

/-!
# The exponentially weighted supremum distance: basic API

Basic properties of `wdist lam Z W = sup_{s ∈ [a,b]} ‖Z s - W s‖ e^{-λ(b-s)}`:
its pointwise characterisation, nonnegativity, symmetry, and its equivalence
with the ordinary supremum distance (`e^{-λ(b-a)} ‖Z - W‖_∞ ≤ wdist ≤ ‖Z - W‖_∞`).
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace Work.VolterraLong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {a b : ℝ} {lam : ℝ}

private lemma exp_weight_le_one (hlam : 0 ≤ lam) (s : Set.Icc a b) :
    Real.exp (-(lam * (b - (s : ℝ)))) ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hlam (sub_nonneg.mpr s.2.2)))

lemma wdist_nonneg (Z W : BoundedContinuousFunction (Set.Icc a b) E) :
    0 ≤ wdist lam Z W := by
  by_cases hne : (Set.Icc a b : Set ℝ).Nonempty
  · obtain ⟨s₀, hs₀⟩ := hne
    have hcont : Continuous (fun s : Set.Icc a b =>
        ‖Z s - W s‖ * Real.exp (-(lam * (b - (s : ℝ))))) := by fun_prop
    have hbd : BddAbove (Set.range fun s : Set.Icc a b =>
        ‖Z s - W s‖ * Real.exp (-(lam * (b - (s : ℝ))))) := (isCompact_range hcont).bddAbove
    have hmem := le_csSup hbd (Set.mem_range_self (⟨s₀, hs₀⟩ : Set.Icc a b))
    have hnn : 0 ≤ ‖Z ⟨s₀, hs₀⟩ - W ⟨s₀, hs₀⟩‖ *
        Real.exp (-(lam * (b - (s₀ : ℝ)))) := by positivity
    rw [wdist]
    linarith
  · haveI : IsEmpty (Set.Icc a b) := ⟨fun s => hne ⟨s.1, s.2⟩⟩
    rw [wdist, Set.range_eq_empty_iff.mpr inferInstance, Real.sSup_empty]

lemma le_wdist (hlam : 0 ≤ lam) (Z W : BoundedContinuousFunction (Set.Icc a b) E)
    (s : Set.Icc a b) :
    ‖Z s - W s‖ * Real.exp (-(lam * (b - (s : ℝ)))) ≤ wdist lam Z W := by
  rw [wdist]
  apply le_csSup
  · exact ⟨dist Z W, by
      rintro y ⟨s', rfl⟩
      have h1 : ‖Z s' - W s'‖ ≤ dist Z W := by
        simpa [dist_eq_norm] using
          BoundedContinuousFunction.dist_coe_le_dist (f := Z) (g := W) s'
      have h2 : Real.exp (-(lam * (b - (s' : ℝ)))) ≤ 1 := exp_weight_le_one hlam s'
      have h3 := mul_le_mul h1 h2 (Real.exp_pos _).le (dist_nonneg : 0 ≤ dist Z W)
      simpa using h3⟩
  · exact ⟨s, rfl⟩

lemma wdist_le_iff (hab : a ≤ b) (hlam : 0 ≤ lam)
    (Z W : BoundedContinuousFunction (Set.Icc a b) E) {C : ℝ} :
    wdist lam Z W ≤ C ↔
      ∀ s : Set.Icc a b, ‖Z s - W s‖ * Real.exp (-(lam * (b - (s : ℝ)))) ≤ C := by
  constructor
  · intro h s
    exact (le_wdist hlam Z W s).trans h
  · intro h
    rw [wdist]
    apply csSup_le
    · exact ⟨_, Set.mem_range_self ⟨a, ⟨le_rfl, hab⟩⟩⟩
    · rintro y ⟨s, rfl⟩
      exact h s

lemma wdist_self (Z : BoundedContinuousFunction (Set.Icc a b) E) :
    wdist lam Z Z = 0 := by
  by_cases hne : (Set.Icc a b : Set ℝ).Nonempty
  · obtain ⟨s₀, hs₀⟩ := hne
    rw [wdist]
    apply le_antisymm _ _
    · apply csSup_le
      · exact ⟨_, Set.mem_range_self ⟨s₀, hs₀⟩⟩
      · rintro y ⟨s, rfl⟩
        simp
    · have hmem : ‖Z ⟨s₀, hs₀⟩ - Z ⟨s₀, hs₀⟩‖ *
          Real.exp (-(lam * (b - (s₀ : ℝ)))) ∈
          Set.range (fun s : Set.Icc a b => ‖Z s - Z s‖ *
            Real.exp (-(lam * (b - (s : ℝ))))) := Set.mem_range_self _
      have hbd : BddAbove (Set.range (fun s : Set.Icc a b => ‖Z s - Z s‖ *
          Real.exp (-(lam * (b - (s : ℝ)))))) := ⟨0, by rintro y ⟨s, rfl⟩; simp⟩
      simpa using le_csSup hbd hmem
  · haveI : IsEmpty (Set.Icc a b) := ⟨fun s => hne ⟨s.1, s.2⟩⟩
    rw [wdist, Set.range_eq_empty_iff.mpr inferInstance, Real.sSup_empty]

lemma wdist_comm (Z W : BoundedContinuousFunction (Set.Icc a b) E) :
    wdist lam Z W = wdist lam W Z := by
  rw [wdist, wdist]
  congr 1
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, by simp [norm_sub_rev]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, by simp [norm_sub_rev]⟩

lemma wdist_le_dist (hlam : 0 ≤ lam) (Z W : BoundedContinuousFunction (Set.Icc a b) E) :
    wdist lam Z W ≤ dist Z W := by
  by_cases hne : (Set.Icc a b : Set ℝ).Nonempty
  · obtain ⟨s₀, hs₀⟩ := hne
    rw [wdist]
    apply csSup_le
    · exact ⟨_, Set.mem_range_self ⟨s₀, hs₀⟩⟩
    · rintro y ⟨s, rfl⟩
      have h1 : ‖Z s - W s‖ ≤ dist Z W := by
        simpa [dist_eq_norm] using
          BoundedContinuousFunction.dist_coe_le_dist (f := Z) (g := W) s
      have h2 : Real.exp (-(lam * (b - (s : ℝ)))) ≤ 1 := exp_weight_le_one hlam s
      have h3 := mul_le_mul h1 h2 (Real.exp_pos _).le (dist_nonneg : 0 ≤ dist Z W)
      simpa using h3
  · haveI : IsEmpty (Set.Icc a b) := ⟨fun s => hne ⟨s.1, s.2⟩⟩
    rw [wdist, Set.range_eq_empty_iff.mpr inferInstance, Real.sSup_empty]
    exact dist_nonneg

lemma exp_mul_dist_le_wdist (hab : a ≤ b) (hlam : 0 ≤ lam)
    (Z W : BoundedContinuousFunction (Set.Icc a b) E) :
    Real.exp (-(lam * (b - a))) * dist Z W ≤ wdist lam Z W := by
  have hcpos : 0 < Real.exp (-(lam * (b - a))) := Real.exp_pos _
  have hwnn : 0 ≤ wdist lam Z W := wdist_nonneg Z W
  have hkey : dist Z W ≤ wdist lam Z W / Real.exp (-(lam * (b - a))) := by
    apply (BoundedContinuousFunction.dist_le (by positivity)).mpr
    intro s
    rw [dist_eq_norm, le_div_iff₀ hcpos]
    calc ‖Z s - W s‖ * Real.exp (-(lam * (b - a)))
        ≤ ‖Z s - W s‖ * Real.exp (-(lam * (b - (s : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Real.exp_le_exp]
          nlinarith [hlam, s.2.1, s.2.2]
      _ ≤ wdist lam Z W := le_wdist hlam Z W s
  calc Real.exp (-(lam * (b - a))) * dist Z W
      ≤ Real.exp (-(lam * (b - a))) * (wdist lam Z W /
          Real.exp (-(lam * (b - a)))) :=
        mul_le_mul_of_nonneg_left hkey hcpos.le
    _ = wdist lam Z W := by field_simp

lemma wdist_eq_zero_iff (hab : a ≤ b) (hlam : 0 ≤ lam)
    (Z W : BoundedContinuousFunction (Set.Icc a b) E) :
    wdist lam Z W = 0 ↔ Z = W := by
  constructor
  · intro h
    have hc : Real.exp (-(lam * (b - a))) * dist Z W ≤ wdist lam Z W :=
      exp_mul_dist_le_wdist hab hlam Z W
    have h2 : Real.exp (-(lam * (b - a))) * dist Z W ≤ 0 := by rw [h] at hc; exact hc
    have hpos : 0 < Real.exp (-(lam * (b - a))) := Real.exp_pos _
    have hdist : dist Z W = 0 := by
      by_contra hne
      have : 0 < dist Z W := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
      nlinarith
    apply BoundedContinuousFunction.ext
    intro s
    have := (BoundedContinuousFunction.dist_le (le_refl (0 : ℝ))).mp (le_of_eq hdist) s
    simpa [dist_eq_norm, sub_eq_zero] using this
  · rintro rfl
    exact wdist_self Z

end Work.VolterraLong
