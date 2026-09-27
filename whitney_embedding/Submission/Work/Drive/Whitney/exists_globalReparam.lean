import Mathlib

/-!
# A smooth reparametrisation making a family globally independent

This file proves `Work.Drive.Whitney.exists_globalReparam`: if a smooth family of vectors
`S : ℝ → Fin r → EuclideanSpace ℝ (Fin m)` is linearly independent on `[a,b]`, then there is a
smooth `ψ : ℝ → ℝ` with `ψ = id` on `[a,b]` and `t ↦ S (ψ t)` linearly independent for *every* `t`.

The proof has three ingredients.

* Linear independence of a finite family is an **open** condition
  (`isOpen_setOfPred_linearIndependent`), so `U := {t | LinearIndependent ℝ (S t)}` is open and
  contains `[a,b]`; compactness of `[a,b]` gives `ε > 0` with `Icc (a - ε) (b + ε) ⊆ U` (via
  `IsCompact.exists_cthickening_subset_open`).
* A **smooth clamp** `ψ`, equal to the identity on `[a,b]` and with range in `[a - η, b + η]`
  (`η := ε / 2` here), built from `Real.smoothTransition`: with `χ` a two-sided smooth bump equal to
  `1` on `[a - η/2, b + η/2]` and vanishing off `(a - η, b + η)`, and `I` the smooth ramp from `a`
  to `b`, the function `ψ t = χ t * t + (1 - χ t) * I t` is smooth, is the identity where `χ = 1`,
  and — since it is a convex combination of `t` and `I t` with the weight `χ t` supported in
  `(a - η, b + η)` — takes all its values in `[a - η, b + η]`.
* Concatenation: `ψ` maps `ℝ` into the open set `U`, which is exactly what is needed.
-/

namespace Work.Drive.Whitney

/-- `Real.smoothTransition` vanishes on `(-∞, 0]`; consequently a positive value forces a positive
argument. -/
private lemma pos_of_smoothTransition_pos {x : ℝ} (h : 0 < Real.smoothTransition x) : 0 < x := by
  by_contra hx
  rw [not_lt] at hx
  rw [Real.smoothTransition.zero_of_nonpos hx] at h
  exact lt_irrefl 0 h

/-- A point lying strictly between `a - ε` and `b + ε` belongs to the `ε`-cthickening of `[a,b]`. -/
private lemma mem_cthickening_Icc {a b ε t : ℝ} (hab : a ≤ b) (hε : 0 ≤ ε)
    (h1 : a - ε < t) (h2 : t < b + ε) : t ∈ Metric.cthickening ε (Set.Icc a b) := by
  rcases le_or_gt t a with h | h
  · refine Metric.closedBall_subset_cthickening (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩) ε ?_
    rw [Metric.mem_closedBall, Real.dist_eq, abs_of_nonpos (by linarith)]
    linarith
  · rcases le_or_gt t b with h' | h'
    · refine Metric.closedBall_subset_cthickening (show t ∈ Set.Icc a b from ⟨h.le, h'⟩) ε ?_
      rw [Metric.mem_closedBall, dist_self]
      exact hε
    · refine Metric.closedBall_subset_cthickening (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩) ε ?_
      rw [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith

/-- **A smooth clamp.** For `a < b` and `η > 0` there is a smooth `ψ : ℝ → ℝ` with `ψ t = t` for
`t ∈ [a,b]` and `ψ t ∈ [a - η, b + η]` for every `t`. -/
private theorem exists_smooth_clamp {a b η : ℝ} (hab : a < b) (hη : 0 < η) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      (∀ t ∈ Set.Icc a b, ψ t = t) ∧ (∀ t : ℝ, a - η ≤ ψ t ∧ ψ t ≤ b + η) := by
  have h2η : (0 : ℝ) < η / 2 := by linarith
  have hba : (0 : ℝ) < b - a := by linarith
  -- the two-sided bump `χ` and the ramp `I`
  let χ₁ : ℝ → ℝ := fun t => Real.smoothTransition ((t - (a - η)) / (η / 2))
  let χ₂ : ℝ → ℝ := fun t => Real.smoothTransition (((b + η) - t) / (η / 2))
  let χ : ℝ → ℝ := fun t => χ₁ t * χ₂ t
  let ramp : ℝ → ℝ := fun t => Real.smoothTransition ((t - a) / (b - a))
  let I : ℝ → ℝ := fun t => a + ramp t * (b - a)
  let ψ : ℝ → ℝ := fun t => χ t * t + (1 - χ t) * I t
  have hχ₁nn : ∀ t, 0 ≤ χ₁ t := fun t => Real.smoothTransition.nonneg _
  have hχ₂nn : ∀ t, 0 ≤ χ₂ t := fun t => Real.smoothTransition.nonneg _
  have hχ₁le : ∀ t, χ₁ t ≤ 1 := fun t => Real.smoothTransition.le_one _
  have hχ₂le : ∀ t, χ₂ t ≤ 1 := fun t => Real.smoothTransition.le_one _
  have hχnn : ∀ t, 0 ≤ χ t := fun t => mul_nonneg (hχ₁nn t) (hχ₂nn t)
  have hχle : ∀ t, χ t ≤ 1 := fun t =>
    (mul_le_of_le_one_left (hχ₂nn t) (hχ₁le t)).trans (hχ₂le t)
  have hχ₁pos : ∀ t, 0 < χ₁ t → a - η < t := by
    intro t ht
    have h : 0 < (t - (a - η)) / (η / 2) := pos_of_smoothTransition_pos ht
    have := (div_pos_iff_of_pos_right h2η).1 h
    linarith
  have hχ₂pos : ∀ t, 0 < χ₂ t → t < b + η := by
    intro t ht
    have h : 0 < ((b + η) - t) / (η / 2) := pos_of_smoothTransition_pos ht
    have := (div_pos_iff_of_pos_right h2η).1 h
    linarith
  have hχχ₁ : ∀ t, 0 < χ t → 0 < χ₁ t := fun t ht => pos_of_mul_pos_left ht (hχ₂nn t)
  have hχχ₂ : ∀ t, 0 < χ t → 0 < χ₂ t := fun t ht => pos_of_mul_pos_right ht (hχ₁nn t)
  have hχlow : ∀ t, 0 ≤ χ t * (t - (a - η)) := by
    intro t
    rcases eq_or_lt_of_le (hχnn t) with h | h
    · simp [← h]
    · exact mul_nonneg h.le (sub_nonneg.mpr (hχ₁pos t (hχχ₁ t h)).le)
  have hχhigh : ∀ t, 0 ≤ χ t * ((b + η) - t) := by
    intro t
    rcases eq_or_lt_of_le (hχnn t) with h | h
    · simp [← h]
    · exact mul_nonneg h.le (sub_nonneg.mpr (hχ₂pos t (hχχ₂ t h)).le)
  have hχ_one : ∀ t, a - η / 2 ≤ t → t ≤ b + η / 2 → χ t = 1 := by
    intro t h1 h2
    have e1 : χ₁ t = 1 :=
      Real.smoothTransition.one_of_one_le ((one_le_div₀ h2η).2 (by linarith))
    have e2 : χ₂ t = 1 :=
      Real.smoothTransition.one_of_one_le ((one_le_div₀ h2η).2 (by linarith))
    show χ₁ t * χ₂ t = 1
    rw [e1, e2, mul_one]
  have hramp_nn : ∀ t, 0 ≤ ramp t := fun t => Real.smoothTransition.nonneg _
  have hramp_le : ∀ t, ramp t ≤ 1 := fun t => Real.smoothTransition.le_one _
  have hInn : ∀ t, a ≤ I t ∧ I t ≤ b := by
    intro t
    have h1 : I t = a + ramp t * (b - a) := rfl
    have h2 := hramp_nn t
    have h3 := hramp_le t
    rw [h1]
    constructor <;> nlinarith
  have hψ_id : ∀ t ∈ Set.Icc a b, ψ t = t := by
    intro t ht
    have h1 : a - η / 2 ≤ t := by linarith [ht.1]
    have h2 : t ≤ b + η / 2 := by linarith [ht.2]
    show χ t * t + (1 - χ t) * I t = t
    rw [hχ_one t h1 h2]
    ring
  have hψ_low : ∀ t, a - η ≤ ψ t := by
    intro t
    have h1 := hχlow t
    have h2 : 0 ≤ (1 - χ t) * (I t - (a - η)) :=
      mul_nonneg (by linarith [hχle t]) (by linarith [(hInn t).1])
    show a - η ≤ χ t * t + (1 - χ t) * I t
    nlinarith [h1, h2]
  have hψ_high : ∀ t, ψ t ≤ b + η := by
    intro t
    have h1 := hχhigh t
    have h2 : 0 ≤ (1 - χ t) * ((b + η) - I t) :=
      mul_nonneg (by linarith [hχle t]) (by linarith [(hInn t).2])
    show χ t * t + (1 - χ t) * I t ≤ b + η
    nlinarith [h1, h2]
  have hχ₁_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ₁ :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)
  have hχ₂_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ₂ :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)
  have hramp_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ramp :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)
  have hI_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) I :=
    (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => a)).add
      (hramp_sm.mul (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => b - a)))
  have hχ_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := hχ₁_sm.mul hχ₂_sm
  have hψ_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => χ t * t + (1 - χ t) * I t)
    refine (hχ_sm.mul (contDiff_id : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (id : ℝ → ℝ))).add ?_
    exact ((contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (1 : ℝ))).sub
      hχ_sm).mul hI_sm
  exact ⟨ψ, hψ_sm, hψ_id, fun t => ⟨hψ_low t, hψ_high t⟩⟩

/-- **A smooth reparametrisation making a family globally independent.**

If `S : ℝ → Fin r → EuclideanSpace ℝ (Fin m)` is smooth and linearly independent on `[a,b]`, there
is a smooth `ψ : ℝ → ℝ` which is the identity on `[a,b]` and for which `t ↦ S (ψ t)` is linearly
independent for *every* `t : ℝ`.
-/
theorem exists_globalReparam {m r : ℕ} {a b : ℝ} (hab : a < b)
    (S : ℝ → Fin r → EuclideanSpace ℝ (Fin m))
    (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hli : ∀ t ∈ Set.Icc a b, LinearIndependent ℝ (S t)) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      (∀ t ∈ Set.Icc a b, ψ t = t) ∧ (∀ t : ℝ, LinearIndependent ℝ (S (ψ t))) := by
  have hopen : IsOpen {f : Fin r → EuclideanSpace ℝ (Fin m) | LinearIndependent ℝ f} :=
    isOpen_setOfPred_linearIndependent
  have hU : IsOpen {t : ℝ | LinearIndependent ℝ (S t)} := hopen.preimage hS.continuous
  obtain ⟨ε, hεpos, hεsub⟩ :=
    isCompact_Icc.exists_cthickening_subset_open hU fun t ht => hli t ht
  obtain ⟨ψ, hψsm, hψid, hψb⟩ := exists_smooth_clamp hab (show (0 : ℝ) < ε / 2 by linarith)
  refine ⟨ψ, hψsm, hψid, fun t => hεsub ?_⟩
  exact mem_cthickening_Icc hab.le hεpos.le (by linarith [(hψb t).1]) (by linarith [(hψb t).2])

end Work.Drive.Whitney
