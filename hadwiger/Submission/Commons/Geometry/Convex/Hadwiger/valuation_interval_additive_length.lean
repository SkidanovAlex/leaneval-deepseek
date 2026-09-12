import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.RCLike.Basic

namespace Commons.Geometry.Convex.Hadwiger

open Set

namespace AuxVL

/-- The canonical convex body with underlying set `[a, b]`, for `a ≤ b`. -/
noncomputable def intervalBody (a b : ℝ) (hab : a ≤ b) : ConvexBody ℝ :=
  ⟨Set.Icc a b, convex_Icc a b, isCompact_Icc, Set.nonempty_Icc.mpr hab⟩

@[simp] theorem intervalBody_coe (a b : ℝ) (hab : a ≤ b) :
    (intervalBody a b hab : Set ℝ) = Set.Icc a b := rfl

/-- A valuation taking the same value on convex bodies with the same underlying set. -/
theorem val_eq_of_set_eq (φ : ConvexBody ℝ → ℝ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    {A B : ConvexBody ℝ} (hAB : (A : Set ℝ) = (B : Set ℝ)) : φ A = φ B := by
  have hU : (A : Set ℝ) = (A : Set ℝ) ∪ (A : Set ℝ) := by ext x; simp
  have hI : (B : Set ℝ) = (A : Set ℝ) ∩ (A : Set ℝ) := by
    rw [hAB]
    ext x; simp
  have h := hadd A B A A hU hI
  linarith

/-- `[a, c] ∪ [b, d] = [a, d]` for `a ≤ b ≤ c ≤ d`. -/
theorem Icc_union {a b c d : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ d) :
    Set.Icc a c ∪ Set.Icc b d = Set.Icc a d := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact ⟨hx.1, le_trans hx.2 h₃⟩
    · exact ⟨le_trans h₁ hx.1, hx.2⟩
  · intro hx
    by_cases h : x ≤ c
    · left
      exact ⟨hx.1, h⟩
    · right
      exact ⟨le_trans h₂ (le_of_lt (lt_of_not_ge h)), hx.2⟩

/-- `[a, c] ∩ [b, d] = [b, c]` for `a ≤ b ≤ c ≤ d`. -/
theorem Icc_inter {a b c d : ℝ} (h₁ : a ≤ b) (_h₂ : b ≤ c) (h₃ : c ≤ d) :
    Set.Icc a c ∩ Set.Icc b d = Set.Icc b c := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.2.1, hx.1.2⟩
  · intro hx
    exact ⟨⟨le_trans h₁ hx.1, hx.2⟩, ⟨hx.1, le_trans hx.2 h₃⟩⟩

/-- A valuation vanishing on empty-interior bodies is zero on a point interval. -/
theorem intervalBody_point_zero (φ : ConvexBody ℝ → ℝ)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0) (a : ℝ) :
    φ (intervalBody a a le_rfl) = 0 := by
  refine hsimple (intervalBody a a le_rfl) ?_
  change interior (Set.Icc a a : Set ℝ) = ∅
  rw [interior_Icc]
  simp

end AuxVL

open AuxVL

theorem valuation_interval_additive_length
    (φ : ConvexBody ℝ → ℝ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    (htrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
        (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → φ A = φ B)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (Kts : ConvexBody ℝ) (hKts : (Kts : Set ℝ) = Set.Icc 0 (t + s))
    (Kt : ConvexBody ℝ) (hKt : (Kt : Set ℝ) = Set.Icc 0 t)
    (Ks : ConvexBody ℝ) (hKs : (Ks : Set ℝ) = Set.Icc 0 s) :
    φ Kts = φ Kt + φ Ks := by
  let f0t : ConvexBody ℝ := intervalBody 0 t ht
  let f0s : ConvexBody ℝ := intervalBody 0 s hs
  let f0ts : ConvexBody ℝ := intervalBody 0 (t + s) (add_nonneg ht hs)
  have hφKts : φ Kts = φ f0ts := by
    apply val_eq_of_set_eq φ hadd
    rw [hKts, intervalBody_coe]
  have hφKt : φ Kt = φ f0t := by
    apply val_eq_of_set_eq φ hadd
    rw [hKt, intervalBody_coe]
  have hφKs : φ Ks = φ f0s := by
    apply val_eq_of_set_eq φ hadd
    rw [hKs, intervalBody_coe]
  by_cases hst : s ≤ t
  · -- case s ≤ t
    let fst : ConvexBody ℝ := intervalBody s t hst
    let fs_ts : ConvexBody ℝ := intervalBody s (t + s) (le_trans hst (le_add_of_nonneg_right hs))
    let fss : ConvexBody ℝ := intervalBody s s le_rfl
    -- [0,t] = [0,s] ∪ [s,t]  and  [s,s] = [0,s] ∩ [s,t]
    have hU1 : (f0t : Set ℝ) = (f0s : Set ℝ) ∪ (fst : Set ℝ) := by
      change Set.Icc 0 t = Set.Icc 0 s ∪ Set.Icc s t
      exact (Icc_union hs le_rfl hst).symm
    have hI1 : (fss : Set ℝ) = (f0s : Set ℝ) ∩ (fst : Set ℝ) := by
      change Set.Icc s s = Set.Icc 0 s ∩ Set.Icc s t
      exact (Icc_inter hs le_rfl hst).symm
    have hie1 := hadd f0t fss f0s fst hU1 hI1
    have hφss : φ fss = 0 := intervalBody_point_zero φ hsimple s
    have hsplit_t : φ f0t = φ f0s + φ fst := by linarith
    -- [0,t+s] = [0,t] ∪ [s,t+s]  and  [s,t] = [0,t] ∩ [s,t+s]
    have hU2 : (f0ts : Set ℝ) = (f0t : Set ℝ) ∪ (fs_ts : Set ℝ) := by
      change Set.Icc 0 (t + s) = Set.Icc 0 t ∪ Set.Icc s (t + s)
      exact (Icc_union hs hst (le_add_of_nonneg_right hs)).symm
    have hI2 : (fst : Set ℝ) = (f0t : Set ℝ) ∩ (fs_ts : Set ℝ) := by
      change Set.Icc s t = Set.Icc 0 t ∩ Set.Icc s (t + s)
      exact (Icc_inter hs hst (le_add_of_nonneg_right hs)).symm
    have hie2 := hadd f0ts fst f0t fs_ts hU2 hI2
    -- φ [s, t+s] = φ [0, t] by translating back by s
    have hφstss : φ fs_ts = φ f0t := by
      apply htrans fs_ts f0t (-s)
      change Set.Icc 0 t = (fun x : ℝ => x + (-s)) '' Set.Icc s (t + s)
      ext x
      constructor
      · intro hx
        refine ⟨x + s, ?_, ?_⟩
        · constructor <;> linarith [hx.1, hx.2]
        · ring
      · rintro ⟨y, hy, rfl⟩
        constructor <;> linarith [hy.1, hy.2]
    have hmain : φ f0ts = φ f0t + φ f0s := by
      have hEq1 : φ fst = φ f0t - φ f0s := by linarith
      have hEq3 : φ f0ts + φ fst = φ f0t + φ f0t := by
        rw [hie2, hφstss]
      linarith
    calc
      φ Kts = φ f0ts := hφKts
      _ = φ f0t + φ f0s := hmain
      _ = φ Kt + φ Ks := by rw [← hφKt, ← hφKs]
  · -- case t ≤ s
    have hts : t ≤ s := le_of_not_ge hst
    let fts : ConvexBody ℝ := intervalBody t s hts
    let ft_ts : ConvexBody ℝ := intervalBody t (t + s) (le_add_of_nonneg_right hs)
    let ftt : ConvexBody ℝ := intervalBody t t le_rfl
    -- [0,s] = [0,t] ∪ [t,s]  and  [t,t] = [0,t] ∩ [t,s]
    have hU1 : (f0s : Set ℝ) = (f0t : Set ℝ) ∪ (fts : Set ℝ) := by
      change Set.Icc 0 s = Set.Icc 0 t ∪ Set.Icc t s
      exact (Icc_union ht le_rfl hts).symm
    have hI1 : (ftt : Set ℝ) = (f0t : Set ℝ) ∩ (fts : Set ℝ) := by
      change Set.Icc t t = Set.Icc 0 t ∩ Set.Icc t s
      exact (Icc_inter ht le_rfl hts).symm
    have hie1 := hadd f0s ftt f0t fts hU1 hI1
    have hφtt : φ ftt = 0 := intervalBody_point_zero φ hsimple t
    have hsplit_s : φ f0s = φ f0t + φ fts := by linarith
    -- [0,t+s] = [0,s] ∪ [t,t+s]  and  [t,s] = [0,s] ∩ [t,t+s]
    have hU2 : (f0ts : Set ℝ) = (f0s : Set ℝ) ∪ (ft_ts : Set ℝ) := by
      change Set.Icc 0 (t + s) = Set.Icc 0 s ∪ Set.Icc t (t + s)
      exact (Icc_union (a := 0) (b := t) (c := s) (d := t + s) ht hts (by linarith)).symm
    have hI2 : (fts : Set ℝ) = (f0s : Set ℝ) ∩ (ft_ts : Set ℝ) := by
      change Set.Icc t s = Set.Icc 0 s ∩ Set.Icc t (t + s)
      exact (Icc_inter (a := 0) (b := t) (c := s) (d := t + s) ht hts (by linarith)).symm
    have hie2 := hadd f0ts fts f0s ft_ts hU2 hI2
    -- φ [t, t+s] = φ [0, s] by translating back by t
    have hφttss : φ ft_ts = φ f0s := by
      apply htrans ft_ts f0s (-t)
      change Set.Icc 0 s = (fun x : ℝ => x + (-t)) '' Set.Icc t (t + s)
      ext x
      constructor
      · intro hx
        refine ⟨x + t, ?_, ?_⟩
        · constructor <;> linarith [hx.1, hx.2]
        · ring
      · rintro ⟨y, hy, rfl⟩
        constructor <;> linarith [hy.1, hy.2]
    have hmain : φ f0ts = φ f0s + φ f0t := by
      have hEq1 : φ fts = φ f0s - φ f0t := by linarith
      have hEq3 : φ f0ts + φ fts = φ f0s + φ f0s := by
        rw [hie2, hφttss]
      linarith
    calc
      φ Kts = φ f0ts := hφKts
      _ = φ f0s + φ f0t := hmain
      _ = φ Ks + φ Kt := by rw [← hφKs, ← hφKt]
      _ = φ Kt + φ Ks := by ring

end Commons.Geometry.Convex.Hadwiger