import Submission.Work.FeitSibley.Coherence.sum_deg_sq_scriptSR_sup
import Submission.Work.FeitSibley.Coherence.sum_deg_sq_scriptSR_of_le_S

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The degree-square sum over `𝒳₁ = 𝒮(S') \ 𝒮(S'Z)`

Peterfalvi II, Appendice XII, step (3): for a subgroup `Z ≤ Q₁` normalised by `H`, the sum of the
squares of the degrees of the characters in `𝒮(S')∖𝒮(S'Z)` is

`|D| · [S : S'] · (|Q₁| - |Q₁ : Z|)`,

which equals `|H : S'| - |H : S'Z|`.  This is the identity `Σ_{χ ∈ 𝒳₁} χ(1)² = |H/S'| - |H/S'Z|`
used in the source both for the divisibility `(3-1)` and in the final Feit-criterion step of (6).

It is the difference of the two degree-square sums already in the workspace
(`sum_deg_sq_scriptSR_of_le_S` at `R = S'` and `sum_deg_sq_scriptSR_sup` at `Q₂ = Z`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

variable {G : Type} [Group G] [Fintype G]

/-- `S' = [S,S] ≤ S`. -/
theorem FSScomm_le_S (h : Work.FeitSibley.FSData G) : FSScomm h ≤ h.S :=
  (Subgroup.commutator_le_sup h.S h.S).trans (le_of_eq (sup_idem h.S))

/-- **The degree-square sum over `𝒮(S') ∖ 𝒮(S'Z)`**, in `ℝ`. -/
theorem sum_deg_sq_scriptSR_sdiff_real (h : Work.FeitSibley.FSData G) {Z : Subgroup G}
    (hZQ1 : Z ≤ h.Q1) (hZn : h.H ≤ Subgroup.normalizer (Z : Set G)) :
    (∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Z),
      ((Work.CharCore.irrDeg χ : ℝ)) ^ 2)
      = (Nat.card h.D : ℝ) * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
          ((Nat.card h.Q1 : ℝ) - (Nat.card h.Q1 : ℝ) / (Nat.card ↥Z : ℝ)) := by
  classical
  have hsub : Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Z)
      ⊆ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) :=
    scriptSR_subset_of_le h le_sup_left
  have hsplit := Finset.sum_sdiff (f := fun χ : ↥h.H → ℂ => ((Work.CharCore.irrDeg χ : ℝ)) ^ 2)
    hsub
  have hA := sum_deg_sq_scriptSR_of_le_S h (FSScomm h) (FSScomm_le_S h)
    (H_le_normalizer_FSScomm h)
  have hB := sum_deg_sq_scriptSR_sup h Z hZQ1 hZn
  have hidx : ((((FSScomm h).subgroupOf h.S).index : ℕ) : ℝ)
      = (Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ) := by
    have hcard : Nat.card ↥((FSScomm h).subgroupOf h.S) = Nat.card ↥(FSScomm h) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (FSScomm_le_S h)).toEquiv
    have hmul := Subgroup.card_mul_index ((FSScomm h).subgroupOf h.S)
    rw [hcard] at hmul
    have hpos : (Nat.card (FSScomm h) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := ↥(FSScomm h))).ne'
    have hcast : ((Nat.card (FSScomm h) : ℝ)) * ((((FSScomm h).subgroupOf h.S).index : ℕ) : ℝ)
        = (Nat.card h.S : ℝ) := by exact_mod_cast hmul
    field_simp
    linarith [hcast]
  rw [show (∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Z),
        ((Work.CharCore.irrDeg χ : ℝ)) ^ 2)
      = (∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h),
          ((Work.CharCore.irrDeg χ : ℝ)) ^ 2)
        - (∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Z),
          ((Work.CharCore.irrDeg χ : ℝ)) ^ 2) from by linarith, hA, hB, hidx]
  ring

/-- **The degree-square sum over `𝒮(S') ∖ 𝒮(S'Z)`** (Peterfalvi II App. XII (3):
`Σ_{χ ∈ 𝒳₁} χ(1)² = |H : S'| - |H : S'Z|`). -/
theorem sum_deg_sq_scriptSR_sdiff (h : Work.FeitSibley.FSData G) {Z : Subgroup G}
    (hZQ1 : Z ≤ h.Q1) (hZn : h.H ≤ Subgroup.normalizer (Z : Set G)) :
    (∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Z),
      (Work.CharCore.irrDeg χ) ^ 2)
      = Nat.card h.D * (Nat.card h.S / Nat.card (FSScomm h)) *
          (Nat.card h.Q1 - Nat.card h.Q1 / Nat.card ↥Z) := by
  classical
  have hS'dvd : Nat.card (FSScomm h) ∣ Nat.card h.S := Subgroup.card_dvd_of_le (FSScomm_le_S h)
  have hZdvd : Nat.card ↥Z ∣ Nat.card h.Q1 := Subgroup.card_dvd_of_le hZQ1
  have hS'pos : (Nat.card (FSScomm h) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥(FSScomm h))).ne'
  have hZpos : (Nat.card ↥Z : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥Z)).ne'
  have hsum : ((∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Z),
        (Work.CharCore.irrDeg χ) ^ 2 : ℕ) : ℝ)
      = ∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Z),
        ((Work.CharCore.irrDeg χ : ℝ)) ^ 2 := by
    push_cast
    exact Finset.sum_congr rfl fun χ _ => by push_cast; ring
  refine Nat.cast_injective (R := ℝ) ?_
  rw [hsum, sum_deg_sq_scriptSR_sdiff_real h hZQ1 hZn]
  push_cast
  rw [Nat.cast_div hS'dvd hS'pos, Nat.cast_sub (Nat.div_le_self _ _), Nat.cast_div hZdvd hZpos]

end Work.FeitSibley.Coherence
