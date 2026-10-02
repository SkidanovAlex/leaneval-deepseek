import Mathlib
import Submission.Work.Bottcher.Contraction.isPreconnected_iInter_of_antitone_isCompact

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Asymptotics Set
open scoped Topology

/-- Auxiliary lemma: for a strictly positive antitone sequence of levels `a n ≤ δ₀` and a map `u`
continuous on `(0, δ₀]`, the intersection of the closed truncations `closure (u '' (0, a n])` is
compact, nonempty and preconnected.

Compactness is inherited from the compact space `X` (each truncation is closed).  Nonemptiness and
preconnectedness are Cantor's intersection theorem for the decreasing sequence of nonempty compact
preconnected sets: each truncation is the closure of the continuous image of the interval
`(0, a n]`, hence preconnected, and nonempty because `a n > 0`. -/
private theorem isCompact_nonempty_isPreconnected_iInter_closure_Ioc {X : Type*} [MetricSpace X]
    [CompactSpace X] {u : ℝ → X} {δ₀ : ℝ} (hu : ContinuousOn u (Set.Ioc 0 δ₀))
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ δ₀)
    (ha_anti : ∀ n, a (n + 1) ≤ a n) :
    IsCompact (⋂ n, closure (u '' Set.Ioc (0:ℝ) (a n))) ∧
      (⋂ n, closure (u '' Set.Ioc (0:ℝ) (a n))).Nonempty ∧
      IsPreconnected (⋂ n, closure (u '' Set.Ioc (0:ℝ) (a n))) := by
  have hsub : ∀ n, Set.Ioc (0:ℝ) (a n) ⊆ Set.Ioc (0:ℝ) δ₀ :=
    fun n _ ht => ⟨ht.1, le_trans ht.2 (ha_le n)⟩
  have hanti : ∀ n,
      closure (u '' Set.Ioc (0:ℝ) (a (n + 1))) ⊆ closure (u '' Set.Ioc (0:ℝ) (a n)) :=
    fun n => closure_mono (image_mono fun _ ht => ⟨ht.1, le_trans ht.2 (ha_anti n)⟩)
  have hne : ∀ n, (closure (u '' Set.Ioc (0:ℝ) (a n))).Nonempty := fun n =>
    closure_nonempty_iff.mpr
      ⟨u (a n / 2), a n / 2, by constructor <;> linarith [ha_pos n], rfl⟩
  have hpre : ∀ n, IsPreconnected (closure (u '' Set.Ioc (0:ℝ) (a n))) := fun n =>
    (IsPreconnected.image isPreconnected_Ioc u (hu.mono (hsub n))).closure
  refine ⟨(isClosed_iInter fun n => isClosed_closure).isCompact, ?_, ?_⟩
  · exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => closure (u '' Set.Ioc (0:ℝ) (a n))) hanti hne
      isClosed_closure.isCompact (fun _ => isClosed_closure)
  · exact Work.Bottcher.Contraction.isPreconnected_iInter_of_antitone_isCompact_general
      (fun _ => isClosed_closure.isCompact) hpre hanti

/-- Auxiliary lemma: the intersection over all levels `δ ∈ (0, δ₀]` equals the intersection over
any antitone sequence of levels `a n ∈ (0, δ₀]` which is cofinal below every level, i.e. with
`∀ δ ∈ (0, δ₀], ∃ n, a n ≤ δ`. -/
private theorem biInter_closure_eq_iInter_seq {X : Type*} [TopologicalSpace X] {u : ℝ → X}
    {δ₀ : ℝ} {a : ℕ → ℝ}
    (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ δ₀)
    (ha_cof : ∀ δ ∈ Set.Ioc (0:ℝ) δ₀, ∃ n, a n ≤ δ) :
    (⋂ δ ∈ Set.Ioc (0:ℝ) δ₀, closure (u '' Set.Ioc (0:ℝ) δ))
      = ⋂ n, closure (u '' Set.Ioc (0:ℝ) (a n)) := by
  ext x
  simp only [Set.mem_iInter]
  constructor
  · intro h n
    exact h (a n) ⟨ha_pos n, ha_le n⟩
  · intro h δ hδ
    obtain ⟨n, hn⟩ := ha_cof δ hδ
    have hsub' : Set.Ioc (0:ℝ) (a n) ⊆ Set.Ioc (0:ℝ) δ :=
      fun _ ht => ⟨ht.1, le_trans ht.2 hn⟩
    exact closure_mono (image_mono hsub') (h n)

/-- The set of cluster values at `0⁺` of a function continuous on `(0,δ₀]` with values in a compact
metric space is compact, nonempty and preconnected.
Hints: `C δ = closure (u '' Ioc 0 δ)` is closed (hence compact) and nonempty; the family is nested
and directed downwards, so the intersection is nonempty by the finite intersection property and
preconnected by separating two supposed pieces with disjoint open sets and using that some `C δ`
is then contained in their union. There is a sibling ℕ-indexed lemma
`Work.Bottcher.ContractionAux.isPreconnected_iInter_of_antitone_isCompact` to compare with. -/
theorem isCompact_nonempty_isPreconnected_limitSet {X : Type*} [MetricSpace X] [CompactSpace X]
    {u : ℝ → X} {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hu : ContinuousOn u (Set.Ioc 0 δ₀)) :
    IsCompact (⋂ δ ∈ Set.Ioc (0:ℝ) δ₀, closure (u '' Set.Ioc (0:ℝ) δ)) ∧
      (⋂ δ ∈ Set.Ioc (0:ℝ) δ₀, closure (u '' Set.Ioc (0:ℝ) δ)).Nonempty ∧
      IsPreconnected (⋂ δ ∈ Set.Ioc (0:ℝ) δ₀, closure (u '' Set.Ioc (0:ℝ) δ)) := by
  -- the cofinal, antitone sequence of levels `δ₀ / (n + 1) ↘ 0`
  have ha_pos : ∀ n : ℕ, (0:ℝ) < δ₀ / ((n : ℝ) + 1) := fun n => div_pos hδ₀ (by positivity)
  have ha_le : ∀ n : ℕ, δ₀ / ((n : ℝ) + 1) ≤ δ₀ := by
    intro n
    have h := div_le_div_of_nonneg_left (le_of_lt hδ₀) (show (0:ℝ) < 1 by norm_num)
      (show (1:ℝ) ≤ (n : ℝ) + 1 by linarith [show (0:ℝ) ≤ (n : ℝ) by positivity])
    simpa using h
  have ha_anti : ∀ n : ℕ, δ₀ / (((n + 1 : ℕ) : ℝ) + 1) ≤ δ₀ / ((n : ℝ) + 1) := by
    intro n
    have h := div_le_div_of_nonneg_left (le_of_lt hδ₀) (show (0:ℝ) < (n : ℝ) + 1 by positivity)
      (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 by push_cast; linarith)
    simpa using h
  have ha_cof : ∀ δ ∈ Set.Ioc (0:ℝ) δ₀, ∃ n : ℕ, δ₀ / ((n : ℝ) + 1) ≤ δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_gt (δ₀ / δ)
    refine ⟨N, ?_⟩
    have hδpos : 0 < δ := hδ.1
    have h1 : δ * (δ₀ / δ) = δ₀ := by field_simp
    have h2 : δ * (δ₀ / δ) < δ * ((N : ℝ) + 1) := by
      have : δ₀ / δ < (N : ℝ) + 1 := by linarith
      exact mul_lt_mul_of_pos_left this hδpos
    rw [h1] at h2
    rw [div_le_iff₀ (show (0:ℝ) < (N : ℝ) + 1 by positivity)]
    linarith
  rw [biInter_closure_eq_iInter_seq (u := u) ha_pos ha_le ha_cof]
  exact isCompact_nonempty_isPreconnected_iInter_closure_Ioc (u := u) hu ha_pos ha_le ha_anti

end Work.LandLeaves
