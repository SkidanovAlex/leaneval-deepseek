import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Theorem3Endgame

/-! # Shared base for the "order split" geometric core (file of the agent `orderSplit_chains`)

Hugelmeyer's Theorem 3, in the form needed for Theorem 1, says that the set

`Zc γ = (GoodC γ)ᶜ = {u : the configuration Möbius strip M of γ is disjoint from its rotation u·M}`

admits an "open half" `W` with `Zc γ = W ⊔ (-W)` and no three elements of `W` summing to `0`.
The proof of the paper goes through the total order `≺` on disjoint homologically nontrivial projective
planes in `ℝ × ℝP³`: take `W = {u ∈ Zc γ : M ≺ u·M}`.

The content of `W` that is actually used is a `ZMod 2`-valued "order" function `b` on `Zc γ`:

* `b` is locally constant (equivalently continuous, `ZMod 2` being discrete) — this is the openness of
  `W`, i.e. the fact that `≺` is an open condition;
* `b u + b (-u) = 1` — antisymmetry of `≺` (Hugelmeyer's Lemma 3);
* `b a = b c = 1 → b (a+c) = 1` whenever `a + c ∈ Zc γ` — transitivity of `≺` (Hugelmeyer's Lemma 4),
  used together with rotation-invariance of `≺`.

`ParityCore γ` below isolates exactly these three properties.  `orderSplitHolds_of_ParityCore` turns such
a `b` into `OrderSplitHolds γ`, so that all of Hugelmeyer's topology has to be used only to produce `b`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- The complement of the collision set `GoodC γ`: the set of angles `u` at which the configuration
Möbius strip `M` of `γ` (the image of `muOrd`) is disjoint from its rotation `u · M`.  This is the set
called `Z` in the paper's Theorem 3 endgame. -/
def Zc (γ : Circle → ℝ × ℝ) : Set UnitAddCircle := (Submission.Configuration.GoodC γ)ᶜ

lemma Zc_eq_compl (γ : Circle → ℝ × ℝ) :
    Zc γ = (Submission.Configuration.GoodC γ)ᶜ := rfl

/-- `GoodC γ` is invariant under `u ↦ -u`, hence so is its complement `Zc γ`. -/
theorem neg_mem_Zc {γ : Circle → ℝ × ℝ} {u : UnitAddCircle} (hu : u ∈ Zc γ) :
    -u ∈ Zc γ := by
  have hZ : Zc γ = -Zc γ := by
    unfold Zc
    rw [Set.compl_neg, ← Submission.Configuration.GoodC_neg γ]
  rw [hZ]
  exact Set.mem_neg.mpr (by simpa using hu)

/-- Every element of `ZMod 2` is `0` or `1`.  (Private: a colleague's `OrderDefs.lean` declares a lemma
of the same name in this namespace.) -/
private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- **The complete geometric input of the order split.**  On the set `Zc γ` of angles at which the
configuration Möbius strip `M` of `γ` misses its rotation `u · M`, the total order `≺` of Hugelmeyer's
Theorem 2 provides a locally constant (`ZMod 2`-valued) "side" function `b` with `b u = 1` iff
`M ≺ u · M`, which is antisymmetric and transitive under addition. -/
def ParityCore (γ : Circle → ℝ × ℝ) : Prop :=
  ∃ b : Zc γ → ZMod 2,
    Continuous b ∧
    (∀ (u : UnitAddCircle) (hu : u ∈ Zc γ), b ⟨u, hu⟩ + b ⟨-u, neg_mem_Zc hu⟩ = 1) ∧
    (∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ),
      b ⟨a, ha⟩ = 1 → b ⟨c, hc⟩ = 1 → ∀ (h : a + c ∈ Zc γ), b ⟨a + c, h⟩ = 1)

/-- **The order split from a mod-2 "side" function.**  If `b : Zc γ → ZMod 2` is locally constant,
antisymmetric, and transitive as in `ParityCore γ`, then `W := {u ∈ Zc γ : b u = 1}` is an open half of
`Zc γ`, disjoint from `-W`, and free of triples summing to `0`: precisely `OrderSplitHolds γ`. -/
theorem orderSplitHolds_of_ParityCore {γ : Circle → ℝ × ℝ} (hZ : IsOpen (Zc γ))
    (h : ParityCore γ) : Submission.Configuration.OrderSplitHolds γ := by
  obtain ⟨b, hcont, hanti, htrans⟩ := h
  set W : Set UnitAddCircle := {u : UnitAddCircle | ∃ hu : u ∈ Zc γ, b ⟨u, hu⟩ = 1} with hWdef
  have hWimg : W = Subtype.val '' (b ⁻¹' ({1} : Set (ZMod 2))) := by
    ext u
    constructor
    · rintro ⟨hu, hb⟩
      exact ⟨⟨u, hu⟩, hb, rfl⟩
    · rintro ⟨y, hy, hyu⟩
      obtain ⟨u', hu'⟩ := y
      have hyu' : u' = u := hyu
      subst hyu'
      exact ⟨hu', hy⟩
  have hWopen : IsOpen W := by
    rw [hWimg]
    exact hZ.isOpenMap_subtype_val _ (hcont.isOpen_preimage {1} (isOpen_discrete {1}))
  refine ⟨W, hWopen, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact hu.1
  · ext u
    constructor
    · intro hu
      rw [Set.mem_union]
      by_cases hb : b ⟨u, hu⟩ = 1
      · exact Or.inl ⟨hu, hb⟩
      · refine Or.inr ?_
        rw [Set.mem_neg]
        rcases zmod2_eq_zero_or_one (b ⟨u, hu⟩) with h0 | h1
        · refine ⟨neg_mem_Zc hu, ?_⟩
          have hh := hanti u hu
          rw [h0] at hh
          simpa using hh
        · exact absurd h1 hb
    · intro hu
      rcases hu with hu | hu
      · exact hu.1
      · rw [Set.mem_neg] at hu
        have h := neg_mem_Zc hu.1
        rw [neg_neg] at h
        exact h
  · rw [Set.disjoint_left]
    intro u huW huNW
    obtain ⟨hu, hb⟩ := huW
    rw [Set.mem_neg] at huNW
    obtain ⟨hnu, hnb⟩ := huNW
    have h1 := hanti u hu
    have heq : (⟨-u, neg_mem_Zc hu⟩ : Zc γ) = ⟨-u, hnu⟩ := Subtype.ext rfl
    rw [heq, hb, hnb] at h1
    have h3 : (1 : ZMod 2) + 1 = 0 := by decide
    rw [h3] at h1
    exact zero_ne_one h1
  · rintro a ⟨ha, hba⟩ b' ⟨hb', hbb⟩ c ⟨hc, hbc⟩ habc
    have hs : a + b' = -c := eq_neg_of_add_eq_zero_left habc
    have hmem : a + b' ∈ Zc γ := by
      rw [hs]
      exact neg_mem_Zc hc
    have h1 : b ⟨a + b', hmem⟩ = 1 := htrans a ha b' hb' hba hbb hmem
    have h2 := hanti c hc
    have heq : (⟨-c, neg_mem_Zc hc⟩ : Zc γ) = ⟨a + b', hmem⟩ := Subtype.ext hs.symm
    rw [heq] at h2
    rw [hbc, h1] at h2
    have h3 : (1 : ZMod 2) + 1 = 0 := by decide
    rw [h3] at h2
    exact zero_ne_one h2

end Work.Drive
