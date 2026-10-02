import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The local arc portion of the rays

This file proves `Work.ELRig.local_arc_portion_of_rays`: for a continuous curve
`γ : ℝ → ℂ` which is a lift of a circle map (`γ (s+1) = γ s + 1`) and for which the
"circle" `{s | dist (γ s) (γ s₀) = ρ}` of radius `ρ ∈ (0,1)` about `γ s₀` consists of at
most two points, the sublevel set `{s | dist (γ s) (γ s₀) < ρ}` is exactly an open interval
`(s₁, s₂)` around `s₀` and the two endpoints `s₁`, `s₂` lie on the circle of radius `ρ`.

The proof splits into a curve-independent real-analysis statement
(`exists_sublevel_interval`) and the coercivity of `s ↦ dist (γ s) (γ s₀)`
(`gamma_dist_coercive`), which reduces `γ` to a real curve via its periodicity.
-/

set_option linter.unusedVariables false

namespace Work.ELRig

open Set

/-! ## Periodicity of the lift `γ` -/

/-- The lift relation, iterated over natural numbers. -/
lemma gamma_add_nat {γ : ℝ → ℂ} (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) (n : ℕ) (s : ℝ) :
    γ (s + n) = γ s + n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hcast : (s + ((m : ℕ) : ℝ) + 1) = (s + ((m + 1 : ℕ) : ℝ)) := by push_cast; ring
    rw [← hcast, hper, ih]
    push_cast
    ring

/-- The lift relation, iterated over all integers. -/
lemma gamma_add_int {γ : ℝ → ℂ} (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) (n : ℤ) (s : ℝ) :
    γ (s + n) = γ s + n := by
  by_cases hn : 0 ≤ n
  · have h1 : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg hn)
    have h2 : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by exact_mod_cast (Int.toNat_of_nonneg hn)
    have key := gamma_add_nat hper n.toNat s
    rw [show s + (n : ℝ) = s + ((n.toNat : ℕ) : ℝ) by rw [h1], key, h2]
  · have hmn : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    have h1 : (((-n).toNat : ℕ) : ℝ) = -(n : ℝ) := by exact_mod_cast hmn
    have h2 : (((-n).toNat : ℕ) : ℂ) = -(n : ℂ) := by exact_mod_cast hmn
    have key := gamma_add_nat hper ((-n).toNat) (s + (n : ℝ))
    rw [show (s + (n : ℝ)) + (((-n).toNat : ℕ) : ℝ) = s by rw [h1]; ring] at key
    rw [h2] at key
    rw [key]; ring

/-! ## Coercivity: `dist (γ s) (γ s₀)` tends to infinity -/

/-- For a continuous lift `γ` of a circle map, the distance from `γ s₀` grows at least linearly:
there is `R` with `R ≤ |s| → ρ ≤ dist (γ s) (γ s₀)`. -/
lemma gamma_dist_coercive {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) (s₀ ρ : ℝ) (hρ : 0 < ρ) :
    ∃ R, ∀ s : ℝ, R ≤ |s| → ρ ≤ dist (γ s) (γ s₀) := by
  obtain ⟨x, -, hxmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one)
    hcont.norm.continuousOn
  set M : ℝ := ‖γ x‖ with hM
  refine ⟨ρ + M + 1 + ‖γ s₀‖ + 1, ?_⟩
  intro s hs
  set k : ℤ := ⌊s⌋ with hk
  set u : ℝ := s - (k : ℝ) with hudef
  have hk_le : (k : ℝ) ≤ s := by rw [hk]; exact Int.floor_le s
  have hk_lt : s < (k : ℝ) + 1 := by rw [hk]; exact Int.lt_floor_add_one s
  have hu0 : 0 ≤ u := by rw [hudef]; linarith
  have hu1 : u ≤ 1 := by rw [hudef]; linarith
  have hγs : γ s = γ u + (k : ℂ) := by
    have h := gamma_add_int hper k u
    rw [show u + (k : ℝ) = s by rw [hudef]; ring] at h
    exact h
  have habs : |s| - 1 ≤ |(k : ℝ)| := by
    rcases lt_or_ge s 0 with hs0 | hs0
    · have hk0 : (k : ℝ) < 0 := lt_of_le_of_lt hk_le hs0
      rw [abs_of_neg hs0, abs_of_neg hk0]; linarith
    · have hk0 : 0 ≤ (k : ℝ) := by
        rw [hk]; exact_mod_cast (Int.floor_nonneg.mpr hs0)
      rw [abs_of_nonneg hs0, abs_of_nonneg hk0]; linarith
  have hnorm : |(k : ℝ)| - M ≤ ‖γ s‖ := by
    rw [hγs]
    have htri : ‖(k : ℂ)‖ ≤ ‖γ u + (k : ℂ)‖ + ‖γ u‖ := by
      have h := norm_add_le (γ u + (k : ℂ)) (-(γ u))
      have hsimp : (γ u + (k : ℂ)) + (-(γ u)) = (k : ℂ) := by ring
      rw [hsimp, norm_neg] at h
      exact h
    have hkC : ‖(k : ℂ)‖ = |(k : ℝ)| := by
      have : (k : ℂ) = ((k : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    have hMu : ‖γ u‖ ≤ M := by
      rw [hM]
      exact hxmax ⟨hu0, hu1⟩
    rw [hkC] at htri
    linarith
  have hdist : ‖γ s‖ - ‖γ s₀‖ ≤ dist (γ s) (γ s₀) := by
    have h := abs_norm_sub_norm_le (γ s) (γ s₀)
    rw [dist_eq_norm]
    linarith [le_abs_self (‖γ s‖ - ‖γ s₀‖)]
  linarith

/-! ## The left and right endpoints of the sublevel component of `x₀` -/

/-- The **left endpoint** of the component of `{g < ρ}` containing `t`: it is the infimum of the
left endpoints of the intervals `[s, t]` mapped into `{g < ρ}`. -/
lemma exists_left_endpoint {g : ℝ → ℝ} {ρ R : ℝ} (hg : Continuous g)
    (hR : ∀ s : ℝ, g s < ρ → -R < s ∧ s < R) {t : ℝ} (ht : g t < ρ) :
    ∃ L : ℝ, L < t ∧ (∀ u : ℝ, L < u → u ≤ t → g u < ρ) ∧ ρ ≤ g L ∧ g L ≤ ρ := by
  set S : Set ℝ := {s | s ≤ t ∧ Set.Icc s t ⊆ {x | g x < ρ}} with hS
  have hSne : S.Nonempty := ⟨t, by
    rw [hS]
    refine ⟨le_refl t, ?_⟩
    intro x hx
    rw [Set.Icc_self] at hx
    rw [Set.mem_singleton_iff.mp hx]
    exact ht⟩
  have hSbdd : BddBelow S := ⟨-R, by
    rintro s hs
    rw [hS] at hs
    exact le_of_lt (hR s (hs.2 (Set.left_mem_Icc.mpr hs.1))).1⟩
  have hLt : sInf S < t := by
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp (isOpen_Iio.preimage hg) t ht
    have hmem : (t - ε / 2) ∈ S := by
      rw [hS]
      refine ⟨by linarith, ?_⟩
      intro u hu
      apply hεsub
      rw [Set.mem_Icc] at hu
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have := csInf_le hSbdd hmem
    linarith
  have hP1 : ∀ u : ℝ, sInf S < u → u ≤ t → g u < ρ := by
    intro u hLu hut
    obtain ⟨s, hsS, hsu⟩ := exists_lt_of_csInf_lt hSne hLu
    rw [hS] at hsS
    exact hsS.2 (Set.mem_Icc.mpr ⟨le_of_lt hsu, hut⟩)
  have hLnotA : ¬ g (sInf S) < ρ := by
    intro hLg
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp (isOpen_Iio.preimage hg) (sInf S) hLg
    have hmem : (sInf S - δ / 2) ∈ S := by
      rw [hS]
      refine ⟨by linarith, ?_⟩
      intro u hu
      rw [Set.mem_Icc] at hu
      rcases le_or_gt u (sInf S) with hule | hult
      · apply hδsub
        rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_lt]
        constructor <;> linarith
      · exact hP1 u hult hu.2
    have := csInf_le hSbdd hmem
    linarith
  have hle : g (sInf S) ≤ ρ := by
    have hsub : S ⊆ {x | g x ≤ ρ} := by
      rintro s hs
      rw [hS] at hs
      have : g s < ρ := hs.2 (Set.left_mem_Icc.mpr hs.1)
      exact le_of_lt this
    have hcl : sInf S ∈ closure {x | g x ≤ ρ} :=
      closure_mono hsub (csInf_mem_closure hSne hSbdd)
    rwa [IsClosed.closure_eq (isClosed_le hg continuous_const)] at hcl
  exact ⟨sInf S, hLt, hP1, le_of_not_gt hLnotA, hle⟩

/-- The **right endpoint** of the component of `{g < ρ}` containing `t`, obtained from
`exists_left_endpoint` by the reflection `s ↦ -s`. -/
lemma exists_right_endpoint {g : ℝ → ℝ} {ρ R : ℝ} (hg : Continuous g)
    (hR : ∀ s : ℝ, g s < ρ → -R < s ∧ s < R) {t : ℝ} (ht : g t < ρ) :
    ∃ U : ℝ, t < U ∧ (∀ u : ℝ, t ≤ u → u < U → g u < ρ) ∧ ρ ≤ g U ∧ g U ≤ ρ := by
  obtain ⟨L, hLt, hP1, hP2, hP3⟩ :=
    exists_left_endpoint (g := fun s => g (-s)) (hg.comp continuous_neg)
      (by
        intro s hs
        obtain ⟨h1, h2⟩ := hR (-s) hs
        exact ⟨by linarith, by linarith⟩)
      (t := -t) (by simpa using ht)
  refine ⟨-L, by linarith, ?_, ?_, ?_⟩
  · intro u htu huU
    have := hP1 (-u) (by linarith) (by linarith)
    simpa using this
  · simpa using hP2
  · simpa using hP3

/-! ## The sublevel set is a single interval -/

/-- Let `g : ℝ → ℝ` be continuous with `g x₀ < ρ` and `g s → ∞` as `|s| → ∞` (expressed as
`hbdd`), and suppose the level set `{g = ρ}` has at most two points (`htwo`).  Then
`{s | g s < ρ}` is exactly the open interval `(s₁, s₂)` with `s₁ < x₀ < s₂`, and `g s₁ = g s₂ = ρ`. -/
lemma exists_sublevel_interval {g : ℝ → ℝ} {ρ x₀ : ℝ}
    (hg : Continuous g) (hx : g x₀ < ρ)
    (hbdd : ∃ R : ℝ, ∀ s : ℝ, R ≤ |s| → ρ ≤ g s)
    (htwo : ∀ a b c : ℝ, g a = ρ → g b = ρ → g c = ρ → a = b ∨ a = c ∨ b = c) :
    ∃ s₁ s₂ : ℝ, s₁ < x₀ ∧ x₀ < s₂ ∧
      (∀ s : ℝ, g s < ρ → s ∈ Set.Icc s₁ s₂) ∧
      (∀ s ∈ Set.Icc s₁ s₂, s ≠ s₁ → s ≠ s₂ → g s < ρ) ∧
      g s₁ = ρ ∧ g s₂ = ρ := by
  obtain ⟨R, hR⟩ := hbdd
  have hR' : ∀ s : ℝ, g s < ρ → -R < s ∧ s < R := by
    intro s hs
    have : |s| < R := lt_of_not_ge (fun hle => absurd (hR s hle) (not_le.mpr hs))
    exact abs_lt.mp this
  obtain ⟨s₁, hs₁t, hs₁P, hs₁le, hs₁ge⟩ := exists_left_endpoint hg hR' hx
  obtain ⟨s₂, hs₂t, hs₂P, hs₂le, hs₂ge⟩ := exists_right_endpoint hg hR' hx
  have hs₁eq : g s₁ = ρ := le_antisymm hs₁ge hs₁le
  have hs₂eq : g s₂ = ρ := le_antisymm hs₂ge hs₂le
  refine ⟨s₁, s₂, hs₁t, hs₂t, ?_, ?_, hs₁eq, hs₂eq⟩
  · intro s hs
    rw [Set.mem_Icc]
    rcases lt_or_ge s s₁ with hslt | hle
    · obtain ⟨L, hLs, _, hLle, hLge⟩ := exists_left_endpoint hg hR' hs
      have hLeq : g L = ρ := le_antisymm hLge hLle
      have hL1 : L < s₁ := lt_trans hLs hslt
      rcases htwo L s₁ s₂ hLeq hs₁eq hs₂eq with h' | h' | h'
      · exact absurd h' (ne_of_lt hL1)
      · exact absurd h' (ne_of_lt (lt_trans hL1 (lt_trans hs₁t hs₂t)))
      · exact absurd h' (ne_of_lt (lt_trans hs₁t hs₂t))
    · rcases lt_or_ge s₂ s with hsgt | hle2
      · obtain ⟨U, hsU, _, hUle, hUge⟩ := exists_right_endpoint hg hR' hs
        have hUeq : g U = ρ := le_antisymm hUge hUle
        have hs₂U : s₂ < U := lt_trans hsgt hsU
        rcases htwo s₁ s₂ U hs₁eq hs₂eq hUeq with h' | h' | h'
        · exact absurd h' (ne_of_lt (lt_trans hs₁t hs₂t))
        · exact absurd h' (ne_of_lt (lt_trans (lt_trans hs₁t hs₂t) hs₂U))
        · exact absurd h' (ne_of_lt hs₂U)
      · exact ⟨hle, hle2⟩
  · intro s hs hne1 hne2
    rw [Set.mem_Icc] at hs
    rcases lt_trichotomy s x₀ with h | h | h
    · exact hs₁P s (lt_of_le_of_ne hs.1 (Ne.symm hne1)) (le_of_lt h)
    · rw [h]; exact hx
    · exact hs₂P s (le_of_lt h) (lt_of_le_of_ne hs.2 hne2)

/-! ## The target -/

theorem local_arc_portion_of_rays {γ : ℝ → ℂ} {s₀ ρ : ℝ} (hcont : Continuous γ)
    (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (htwo : ∀ a b c : ℝ, dist (γ a) (γ s₀) = ρ → dist (γ b) (γ s₀) = ρ →
      dist (γ c) (γ s₀) = ρ → a = b ∨ a = c ∨ b = c) :
    ∃ s₁ s₂ : ℝ, s₁ < s₀ ∧ s₀ < s₂ ∧
      (∀ s : ℝ, dist (γ s) (γ s₀) < ρ → s ∈ Set.Icc s₁ s₂) ∧
      (∀ s ∈ Set.Icc s₁ s₂, s ≠ s₁ → s ≠ s₂ → dist (γ s) (γ s₀) < ρ) ∧
      dist (γ s₁) (γ s₀) = ρ ∧ dist (γ s₂) (γ s₀) = ρ := by
  obtain ⟨R, hR⟩ := gamma_dist_coercive hcont hper s₀ ρ hρ
  have hx : dist (γ s₀) (γ s₀) < ρ := by rw [dist_self]; exact hρ
  exact exists_sublevel_interval (g := fun s => dist (γ s) (γ s₀)) (ρ := ρ) (x₀ := s₀)
    (hcont.dist continuous_const) hx ⟨R, hR⟩ htwo

end Work.ELRig
