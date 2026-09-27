import Mathlib
import Submission.Work.OneDim.Defs

/-!
# Parametrising an open interval of `ℝ` by `ℝ` itself

An open preconnected nonempty subset of `ℝ` is an open interval (possibly unbounded).  Such an
interval is diffeomorphic to `ℝ`: this file exhibits an explicit parametrisation `ρ : ℝ → s`
(depending on the boundedness of `s` below and above) and proves that `ρ` is injective, has range
exactly `s`, and is a local diffeomorphism.
-/

open scoped Manifold ContDiff
open Set Function

namespace Work.OneDim

noncomputable section

/-- If `s` is open, `c ∈ s` and `s` is bounded below, then `sInf s < c`. -/
theorem sInf_lt_of_mem {s : Set ℝ} (hopen : IsOpen s) {c : ℝ} (hc : c ∈ s)
    (hb : BddBelow s) : sInf s < c := by
  have hle : sInf s ≤ c := csInf_le hb hc
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hc)
    have hmem : c - δ/2 ∈ s := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      have h1 : c - δ / 2 - c = -(δ/2) := by ring
      rw [h1, abs_neg, abs_of_pos (by linarith)]
      linarith
    have h2 : sInf s ≤ c - δ/2 := csInf_le hb hmem
    rw [h] at h2
    linarith

/-- If `s` is open, `c ∈ s` and `s` is bounded above, then `c < sSup s`. -/
theorem lt_sSup_of_mem {s : Set ℝ} (hopen : IsOpen s) {c : ℝ} (hc : c ∈ s)
    (hb : BddAbove s) : c < sSup s := by
  have hle : c ≤ sSup s := le_csSup hb hc
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hc)
    have hmem : c + δ/2 ∈ s := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      have h1 : c + δ / 2 - c = δ/2 := by ring
      rw [h1, abs_of_pos (by linarith)]
      linarith
    have h2 : c + δ/2 ≤ sSup s := le_csSup hb hmem
    rw [h] at h2
    linarith

/-- A function `ρ : ℝ → ℝ` which maps bijectively onto the open set `s` and whose inverse is
smooth on `s` is a local diffeomorphism. -/
theorem isLocalDiffeomorph_of_inverse {ρ g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hρs : ∀ x, ρ x ∈ s) (hgρ : ∀ x, g (ρ x) = x) (hρg : ∀ y ∈ s, ρ (g y) = y)
    (hρ : ContDiff ℝ ∞ ρ) (hg : ContDiffOn ℝ ∞ g s) :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm ρ := by
  intro x
  let Φ : PartialDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ℝ ℝ sm :=
    { toPartialEquiv :=
        { toFun := ρ, invFun := g, source := univ, target := s,
          map_source' := fun y _ => hρs y,
          map_target' := fun y _ => trivial,
          left_inv' := fun y _ => hgρ y,
          right_inv' := fun y hy => hρg y hy }
      open_source := isOpen_univ
      open_target := hs
      contMDiffOn_toFun := by
        rw [contMDiffOn_univ, contMDiff_iff_contDiff]
        exact hρ
      contMDiffOn_invFun := by
        rw [contMDiffOn_iff_contDiffOn]
        exact hg }
  exact PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ (mem_univ x)

/-! ### Elementary identities for the fractional linear model `t ↦ (a + b eᵗ)/(1 + eᵗ)` -/

theorem frac_model_sub (a b t : ℝ) (hab : a < b) :
    (a + b * Real.exp t)/(1 + Real.exp t) - a = (b - a) * Real.exp t / (1 + Real.exp t) := by
  have h1 : (1 + Real.exp t) ≠ 0 := by positivity
  have h2 : b - a ≠ 0 := by linarith
  field_simp
  ring

theorem frac_model_sub' (a b t : ℝ) (hab : a < b) :
    b - (a + b * Real.exp t)/(1 + Real.exp t) = (b - a) / (1 + Real.exp t) := by
  have h1 : (1 + Real.exp t) ≠ 0 := by positivity
  have h2 : b - a ≠ 0 := by linarith
  field_simp
  ring

theorem frac_model_eq (a b c : ℝ) (hab : a < b) (h1 : a < c) (h2 : c < b) :
    (a + b * ((c - a)/(b - c)))/(1 + (c - a)/(b - c)) = c := by
  have hbc : b - c ≠ 0 := by linarith
  have hden : 1 + (c - a)/(b - c) ≠ 0 := by
    have : 0 < (c - a)/(b - c) := by positivity
    linarith
  rw [div_eq_iff hden]
  field_simp
  ring

/-! ### The four cases -/

/-- `s = univ`: the identity parametrises the line. -/
theorem exists_param_univ {s : Set ℝ} (hopen : IsOpen s) (hord : s.OrdConnected)
    (hne : s.Nonempty) (hnb : ¬ BddBelow s) (hna : ¬ BddAbove s) :
    ∃ ρ : ℝ → ℝ, Function.Injective ρ ∧ Set.range ρ = s ∧
      IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm ρ := by
  have hs : s = univ := by
    ext c
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨y, hy, hyc⟩ := not_bddBelow_iff.mp hnb c
      obtain ⟨z, hz, hcz⟩ := not_bddAbove_iff.mp hna c
      exact hord.out' hy hz (mem_Icc.mpr ⟨le_of_lt hyc, le_of_lt hcz⟩)
  have hρs : ∀ x : ℝ, id x ∈ s := by intro x; rw [hs]; trivial
  refine ⟨id, Function.injective_id, ?_, ?_⟩
  · rw [Set.range_id, hs]
  · apply isLocalDiffeomorph_of_inverse (ρ := id) (g := id) (s := s) hopen hρs
    · intro x; rfl
    · intro y hy; rfl
    · exact contDiff_id
    · rw [hs]; exact contDiffOn_id

/-- `s = Ioi (sInf s)`: the exponential parametrises a half-line. -/
theorem exists_param_Ioi {s : Set ℝ} (hopen : IsOpen s) (hord : s.OrdConnected)
    (hne : s.Nonempty) (hbb : BddBelow s) (hna : ¬ BddAbove s) :
    ∃ ρ : ℝ → ℝ, Function.Injective ρ ∧ Set.range ρ = s ∧
      IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm ρ := by
  have hρs : ∀ t, sInf s + Real.exp t ∈ s := by
    intro t
    have hlt : sInf s < sInf s + Real.exp t := by have := Real.exp_pos t; linarith
    obtain ⟨y, hy, hyc⟩ := (csInf_lt_iff hbb hne).mp hlt
    obtain ⟨z, hz, hcz⟩ := not_bddAbove_iff.mp hna (sInf s + Real.exp t)
    exact hord.out' hy hz (mem_Icc.mpr ⟨le_of_lt hyc, le_of_lt hcz⟩)
  refine ⟨fun t => sInf s + Real.exp t, ?_, ?_, ?_⟩
  · intro t1 t2 h
    have : Real.exp t1 = Real.exp t2 := by linarith
    exact Real.exp_injective this
  · ext c
    constructor
    · rintro ⟨t, rfl⟩
      exact hρs t
    · intro hc
      have hpos : 0 < c - sInf s := by have := sInf_lt_of_mem hopen hc hbb; linarith
      refine ⟨Real.log (c - sInf s), ?_⟩
      show sInf s + Real.exp (Real.log (c - sInf s)) = c
      rw [Real.exp_log hpos]; ring
  · apply isLocalDiffeomorph_of_inverse (ρ := fun t => sInf s + Real.exp t)
      (g := fun y => Real.log (y - sInf s)) (s := s) hopen hρs
    · intro t
      show Real.log (sInf s + Real.exp t - sInf s) = t
      rw [add_sub_cancel_left, Real.log_exp]
    · intro y hy
      have hpos : 0 < y - sInf s := by have := sInf_lt_of_mem hopen hy hbb; linarith
      show sInf s + Real.exp (Real.log (y - sInf s)) = y
      rw [Real.exp_log hpos]; ring
    · fun_prop
    · apply ContDiffOn.log
      · fun_prop
      · intro y hy
        have := sInf_lt_of_mem hopen hy hbb
        linarith

/-- `s = Iio (sSup s)`: a negative exponential parametrises a half-line. -/
theorem exists_param_Iio {s : Set ℝ} (hopen : IsOpen s) (hord : s.OrdConnected)
    (hne : s.Nonempty) (hnb : ¬ BddBelow s) (hba : BddAbove s) :
    ∃ ρ : ℝ → ℝ, Function.Injective ρ ∧ Set.range ρ = s ∧
      IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm ρ := by
  have hρs : ∀ t, sSup s - Real.exp (-t) ∈ s := by
    intro t
    have hlt : sSup s - Real.exp (-t) < sSup s := by have := Real.exp_pos (-t); linarith
    obtain ⟨z, hz, hcz⟩ := (lt_csSup_iff hba hne).mp hlt
    obtain ⟨y, hy, hyc⟩ := not_bddBelow_iff.mp hnb (sSup s - Real.exp (-t))
    exact hord.out' hy hz (mem_Icc.mpr ⟨le_of_lt hyc, le_of_lt hcz⟩)
  have hgρ : ∀ t, -(Real.log (sSup s - (sSup s - Real.exp (-t)))) = t := by
    intro t
    have h1 : sSup s - (sSup s - Real.exp (-t)) = Real.exp (-t) := by ring
    rw [h1, Real.log_exp]; ring
  have hg : ContDiffOn ℝ ∞ (fun y => -(Real.log (sSup s - y))) s := by
    apply ContDiffOn.neg
    apply ContDiffOn.log
    · fun_prop
    · intro y hy
      have := lt_sSup_of_mem hopen hy hba
      linarith
  refine ⟨fun t => sSup s - Real.exp (-t), ?_, ?_, ?_⟩
  · exact (Function.LeftInverse.injective (g := fun y => -(Real.log (sSup s - y))) hgρ)
  · ext c
    constructor
    · rintro ⟨t, rfl⟩
      exact hρs t
    · intro hc
      have hpos : 0 < sSup s - c := by have := lt_sSup_of_mem hopen hc hba; linarith
      refine ⟨-(Real.log (sSup s - c)), ?_⟩
      show sSup s - Real.exp (-(-(Real.log (sSup s - c)))) = c
      rw [neg_neg, Real.exp_log hpos]; ring
  · apply isLocalDiffeomorph_of_inverse (ρ := fun t => sSup s - Real.exp (-t))
      (g := fun y => -(Real.log (sSup s - y))) (s := s) hopen hρs hgρ
    · intro y hy
      have hpos : 0 < sSup s - y := by have := lt_sSup_of_mem hopen hy hba; linarith
      show sSup s - Real.exp (-(-(Real.log (sSup s - y)))) = y
      rw [neg_neg, Real.exp_log hpos]; ring
    · fun_prop
    · exact hg

/-- `s = Ioo (sInf s) (sSup s)`: a fractional linear exponential parametrises a bounded interval. -/
theorem exists_param_Ioo {s : Set ℝ} (hopen : IsOpen s) (hord : s.OrdConnected)
    (hne : s.Nonempty) (hbb : BddBelow s) (hba : BddAbove s) :
    ∃ ρ : ℝ → ℝ, Function.Injective ρ ∧ Set.range ρ = s ∧
      IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm ρ := by
  obtain ⟨x0, hx0⟩ := hne
  have ha_lt_x0 : sInf s < x0 := sInf_lt_of_mem hopen hx0 hbb
  have hx0_lt_b : x0 < sSup s := lt_sSup_of_mem hopen hx0 hba
  have hab : sInf s < sSup s := lt_trans ha_lt_x0 hx0_lt_b
  have hne' : s.Nonempty := ⟨x0, hx0⟩
  have hsub : ∀ t, (sInf s + sSup s * Real.exp t)/(1 + Real.exp t) - sInf s
      = (sSup s - sInf s) * Real.exp t / (1 + Real.exp t) := fun t => frac_model_sub _ _ _ hab
  have hsub' : ∀ t, sSup s - (sInf s + sSup s * Real.exp t)/(1 + Real.exp t)
      = (sSup s - sInf s) / (1 + Real.exp t) := fun t => frac_model_sub' _ _ _ hab
  have hmem : ∀ t, (sInf s + sSup s * Real.exp t)/(1 + Real.exp t) ∈ s := by
    intro t
    have hlt : sInf s < (sInf s + sSup s * Real.exp t)/(1 + Real.exp t) := by
      have h := hsub t
      have hpos : 0 < (sSup s - sInf s) * Real.exp t / (1 + Real.exp t) := by positivity
      linarith
    have hgt : (sInf s + sSup s * Real.exp t)/(1 + Real.exp t) < sSup s := by
      have h := hsub' t
      have hpos : 0 < (sSup s - sInf s) / (1 + Real.exp t) := by positivity
      linarith
    obtain ⟨y, hy, hyc⟩ := (csInf_lt_iff hbb hne').mp hlt
    obtain ⟨z, hz, hcz⟩ := (lt_csSup_iff hba hne').mp hgt
    exact hord.out' hy hz (mem_Icc.mpr ⟨le_of_lt hyc, le_of_lt hcz⟩)
  have hgρ : ∀ t, Real.log (((sInf s + sSup s * Real.exp t)/(1 + Real.exp t) - sInf s)
      / (sSup s - (sInf s + sSup s * Real.exp t)/(1 + Real.exp t))) = t := by
    intro t
    have key : ((sInf s + sSup s * Real.exp t)/(1 + Real.exp t) - sInf s)
        / (sSup s - (sInf s + sSup s * Real.exp t)/(1 + Real.exp t)) = Real.exp t := by
      rw [hsub t, hsub' t]
      have h1 : (1 + Real.exp t) ≠ 0 := by positivity
      have h2 : sSup s - sInf s ≠ 0 := by linarith
      field_simp
    rw [key, Real.log_exp]
  refine ⟨fun t => (sInf s + sSup s * Real.exp t)/(1 + Real.exp t), ?_, ?_, ?_⟩
  · exact Function.LeftInverse.injective (g := fun y => Real.log ((y - sInf s)/(sSup s - y))) hgρ
  · ext c
    constructor
    · rintro ⟨t, rfl⟩
      exact hmem t
    · intro hc
      have h1 : 0 < c - sInf s := by have := sInf_lt_of_mem hopen hc hbb; linarith
      have h2 : 0 < sSup s - c := by have := lt_sSup_of_mem hopen hc hba; linarith
      have hpos : 0 < (c - sInf s)/(sSup s - c) := by positivity
      refine ⟨Real.log ((c - sInf s)/(sSup s - c)), ?_⟩
      show (sInf s + sSup s * Real.exp (Real.log ((c - sInf s)/(sSup s - c))))
        / (1 + Real.exp (Real.log ((c - sInf s)/(sSup s - c)))) = c
      rw [Real.exp_log hpos]
      exact frac_model_eq _ _ _ hab (sInf_lt_of_mem hopen hc hbb) (lt_sSup_of_mem hopen hc hba)
  · apply isLocalDiffeomorph_of_inverse
      (g := fun y => Real.log ((y - sInf s)/(sSup s - y))) (s := s) hopen hmem hgρ
    · intro y hy
      have h1 : 0 < y - sInf s := by have := sInf_lt_of_mem hopen hy hbb; linarith
      have h2 : 0 < sSup s - y := by have := lt_sSup_of_mem hopen hy hba; linarith
      have hpos : 0 < (y - sInf s)/(sSup s - y) := by positivity
      show (sInf s + sSup s * Real.exp (Real.log ((y - sInf s)/(sSup s - y))))
        / (1 + Real.exp (Real.log ((y - sInf s)/(sSup s - y)))) = y
      rw [Real.exp_log hpos]
      exact frac_model_eq _ _ _ hab (sInf_lt_of_mem hopen hy hbb) (lt_sSup_of_mem hopen hy hba)
    · apply ContDiff.div
      · fun_prop
      · fun_prop
      · intro x; positivity
    · apply ContDiffOn.log
      · apply ContDiffOn.div
        · fun_prop
        · fun_prop
        · intro y hy
          have := lt_sSup_of_mem hopen hy hba
          linarith
      · intro y hy
        have h1 : 0 < y - sInf s := by have := sInf_lt_of_mem hopen hy hbb; linarith
        have h2 : 0 < sSup s - y := by have := lt_sSup_of_mem hopen hy hba; linarith
        positivity

/-- Every nonempty open preconnected subset of `ℝ` can be parametrised injectively by `ℝ` with a
local diffeomorphism. -/
theorem real_interval_parametrization {s : Set ℝ} (hopen : IsOpen s) (hconn : IsPreconnected s)
    (hne : s.Nonempty) :
    ∃ ρ : ℝ → ℝ, Function.Injective ρ ∧ Set.range ρ = s ∧
      IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
        Work.OneDim.sm ρ := by
  have hord : s.OrdConnected := hconn.ordConnected
  by_cases hbb : BddBelow s
  · by_cases hba : BddAbove s
    · exact exists_param_Ioo hopen hord hne hbb hba
    · exact exists_param_Ioi hopen hord hne hbb hba
  · by_cases hba : BddAbove s
    · exact exists_param_Iio hopen hord hne hbb hba
    · exact exists_param_univ hopen hord hne hbb hba

end

end Work.OneDim
