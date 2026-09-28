import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.MDBasic.finite_sets

/-!
# Definitions for the weighted cone-count `Work.HP.ballConeWeightedK`

Notation of the proof of `Work.HP.ballConeWeightedK`: for a lattice `L ⊆ ℤ^ι`, vectors
`v w : ι → ℝ`, `γ > 0` and radii `0 < Y ≤ T` we split the weighted sum

`S = Σ_{a ∈ L, a ≠ 0, ‖a‖ ≤ T, a ∈ 𝒞_v ∩ 𝒞_w} ‖a‖^{-k}`

into the *small* part `‖a‖ ≤ Y` (bounded crudely by the number of lattice points in the
ball of radius `Y`) and the *large* part `Y < ‖a‖ ≤ T` (estimated by summation by parts
against the counting function `coneCount`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open Finset

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Φ(t) = #{a ∈ L : ‖a‖ ≤ t ∧ a ∈ 𝒞_v^{(γ)} ∩ 𝒞_w^{(γ)}}`, the counting function of the cone
slice of the ball; it includes `a = 0`. -/
def coneCount (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ t : ℝ) : ℝ :=
  (({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}.ncard : ℕ) : ℝ)

/-- The set summed in the statement of `ballConeWeightedK`. -/
def fullSet (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ T : ℝ) : Set (ι → ℤ) :=
  {a | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}

/-- The lattice points of norm `≤ Y` in both cones (the "small" part). -/
def smallSet (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ Y : ℝ) : Set (ι → ℤ) :=
  {a | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ Y ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}

/-- The lattice points with `Y < ‖a‖ ≤ T` in both cones (the "large" part). -/
def largeSet (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ Y T : ℝ) : Set (ι → ℤ) :=
  {a | a ∈ L ∧ a ≠ 0 ∧ Y < eNorm a ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}

/-- The set whose cardinality appears in the error term of `ballConeWeightedK`. -/
def ballSet (L : Submodule ℤ (ι → ℤ)) (Y : ℝ) : Set (ι → ℤ) :=
  {a | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ Y}

/-! ## Finiteness -/

lemma finite_coneBall (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ t : ℝ) :
    ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} :
      Set (ι → ℤ)).Finite :=
  (MDBasic.finite_eNorm_le (ι := ι) t).subset fun a ha => ha.2.1

lemma finite_fullSet (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ T : ℝ) :
    (fullSet L v w γ T).Finite :=
  (MDBasic.finite_eNorm_le (ι := ι) T).subset fun a ha => ha.2.2.1

lemma finite_smallSet (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ Y : ℝ) :
    (smallSet L v w γ Y).Finite :=
  (MDBasic.finite_eNorm_le (ι := ι) Y).subset fun a ha => ha.2.2.1

lemma finite_largeSet (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ Y T : ℝ) :
    (largeSet L v w γ Y T).Finite :=
  (MDBasic.finite_eNorm_le (ι := ι) T).subset fun a ha => ha.2.2.2.1

lemma finite_ballSet (L : Submodule ℤ (ι → ℤ)) (Y : ℝ) : (ballSet L Y).Finite :=
  (MDBasic.finite_eNorm_le (ι := ι) Y).subset fun a ha => ha.2.2

/-! ## Elementary set facts -/

lemma fullSet_eq_union (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ Y T : ℝ) (hYT : Y ≤ T) :
    fullSet L v w γ T = smallSet L v w γ Y ∪ largeSet L v w γ Y T := by
  ext a
  simp only [fullSet, smallSet, largeSet, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hL, hne, hT, hc1, hc2⟩
    rcases le_or_gt (eNorm a) Y with h | h
    · exact Or.inl ⟨hL, hne, h, hc1, hc2⟩
    · exact Or.inr ⟨hL, hne, h, hT, hc1, hc2⟩
  · rintro (⟨hL, hne, hY, hc1, hc2⟩ | ⟨hL, hne, hY, hT, hc1, hc2⟩)
    · exact ⟨hL, hne, le_trans hY hYT, hc1, hc2⟩
    · exact ⟨hL, hne, hT, hc1, hc2⟩

lemma disjoint_small_large (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ Y T : ℝ) :
    Disjoint (smallSet L v w γ Y) (largeSet L v w γ Y T) := by
  rw [Set.disjoint_left]
  intro a ha hb
  simp only [smallSet, Set.mem_ofPred_eq] at ha
  simp only [largeSet, Set.mem_ofPred_eq] at hb
  exact absurd ha.2.2.1 (not_le.mpr hb.2.2.1)

/-- `coneCount` is monotone in the radius. -/
lemma coneCount_mono (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ : ℝ) {t t' : ℝ} (h : t ≤ t') :
    coneCount L v w γ t ≤ coneCount L v w γ t' := by
  have hsub : {a : ι → ℤ | a ∈ L ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} ⊆
      {a : ι → ℤ | a ∈ L ∧ eNorm a ≤ t' ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} :=
    fun a ha => ⟨ha.1, le_trans ha.2.1 h, ha.2.2.1, ha.2.2.2⟩
  have hle := Set.ncard_le_ncard hsub (finite_coneBall L v w γ t')
  simp only [coneCount]
  exact_mod_cast hle

end Work.HP
