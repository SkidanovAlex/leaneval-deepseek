import Submission.ZagierHoffmanProof.StepL196
import Submission.ZagierHoffmanProof.Basic
import Submission.ZagierHoffmanProof.StepL191
import Submission.ZagierHoffmanProof.StepL193
import Mathlib.LinearAlgebra.Dimension.Finite

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero Filter

/-!
# Step L197: ★ Theorems B and D at weight `w = 1`

The weight-one tuples are all of the shape `(1)`, so
`𝒯0 F 1 = 𝒯 F 1 = {ζ_A F (1)}`; with `ζ_A(1) ≠ 0` (StepL196) that gives the weight-`1`
instances of the transcendental Theorems B and D:

  * `theorem_B_one` : `LinearIndependent K (𝒯0 F 1) ∧ rank (𝒵 F 1) ≥ ncard (𝒯0 F 1)`;
  * `theorem_D_one` : `LinearIndependent K (𝒯 F 1) ∧ rank (𝒵 F 1) = d F 1` (using the
    rank upper bound from theorem_A, StepL193).

The general Theorems B/D remain ABP-gated (t-motives / the ABP criterion).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- A weight-one tuple is the singleton `(1)`. -/
lemma eq_single_one_of_weight_one {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = 1) :
    r = 1 ∧ ∀ i : Fin r, s i = 1 := by
  have hr : r ≤ weight r s := card_le_sum_pnat r s
  have hr1 : r = 1 := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      have hz : weight 0 s = 0 := by simp [weight]
      omega
    · omega
  subst hr1
  refine ⟨rfl, fun i => ?_⟩
  have h : weight 1 s = (s i : ℕ) := by
    show (∑ j : Fin 1, (s j : ℕ)) = (s i : ℕ)
    rw [Fin.sum_univ_one]
    exact congrArg (fun j : Fin 1 => (s j : ℕ)) (Subsingleton.elim _ i)
  rw [h] at hw
  exact Subtype.ext hw

/-- ★ `𝒯0 F 1 = {ζ_A F (1)}`: the only weight-one MZV with all entries `< q`. -/
theorem T0_one_eq : 𝒯0 F 1 = ({ζ_A F (single oneExp)} : Set (RatFunc.CompletionAtInfty F)) := by
  classical
  ext x
  constructor
  · intro hx
    rw [mem_𝒯0_iff F 1] at hx
    rcases hx with ⟨r, hr⟩
    rw [mem_𝒯0_aux_iff F 1 r] at hr
    rcases hr with ⟨s, h𝔖, hlt, rfl⟩
    have hw1 : weight (r : ℕ) s = 1 := (𝔖_w_mem_iff 1 (r : ℕ) s).mp h𝔖
    obtain ⟨hr1, hs1⟩ := eq_single_one_of_weight_one s hw1
    have hr1' : r = 1 := Subtype.ext hr1
    subst hr1'
    have hs : s = single oneExp := by
      funext i
      rw [hs1 i]
      rfl
    rw [hs]
    exact Set.mem_singleton _
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [mem_𝒯0_iff F 1]
    refine ⟨1, ?_⟩
    rw [mem_𝒯0_aux_iff F 1 1]
    refine ⟨(fun _ : Fin (((1 : ℕ+) : ℕ)) => oneExp), ?_, ?_, ?_⟩
    · show (∑ _i : Fin (((1 : ℕ+) : ℕ)), (1 : ℕ)) = 1
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    · intro i
      have h : ((fun _ : Fin (((1 : ℕ+) : ℕ)) => oneExp) i : ℕ) = 1 := rfl
      rw [h]
      have h2 := card_ge_two F
      omega
    · rfl

/-- ★ `𝒯 F 1 = {ζ_A F (1)}`: the only weight-one MZV in `𝒯_1`. -/
theorem T_one_eq : 𝒯 F 1 = ({ζ_A F (single oneExp)} : Set (RatFunc.CompletionAtInfty F)) := by
  classical
  ext x
  constructor
  · intro hx
    rw [mem_𝒯_iff F 1] at hx
    rcases hx with ⟨r, hr⟩
    rw [mem_𝒯_aux_iff F 1 r] at hr
    rcases hr with ⟨s, h𝔖, -, -, rfl⟩
    have hw1 : weight (r : ℕ) s = 1 := (𝔖_w_mem_iff 1 (r : ℕ) s).mp h𝔖
    obtain ⟨hr1, hs1⟩ := eq_single_one_of_weight_one s hw1
    have hr1' : r = 1 := Subtype.ext hr1
    subst hr1'
    have hs : s = single oneExp := by
      funext i
      rw [hs1 i]
      rfl
    rw [hs]
    exact Set.mem_singleton _
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine admissible_mem_𝒯 F 1 (by norm_num) (single oneExp) ?_ ?_
    · rw [weight_single]
      rfl
    · refine ⟨fun x hx => ?_, ?_⟩
      · have hx0 : x = 0 := by omega
        subst hx0
        have hp : pad0 (single oneExp) 0 = ((single oneExp) ⟨0, by omega⟩ : ℕ) :=
          pad0_of_lt (single oneExp) (by omega)
        rw [hp]
        show (1 : ℕ) ≤ Nat.card F
        have h := card_ge_two F
        omega
      · rintro ⟨hr1, hrk, hall, hlast⟩
        have hk : (1 : ℕ) ≤ 1 := hrk
        have hi : (⟨1 - 1, by omega⟩ : Fin 1) = ⟨0, by omega⟩ := Fin.ext (by simp)
        have hval : ((single oneExp) ⟨1 - 1, by omega⟩ : ℕ) = 1 := by
          rw [show ((single oneExp) ⟨1 - 1, by omega⟩ : ℕ+) = oneExp from rfl]
          rfl
        rw [hval] at hlast
        have hq := card_ge_two F
        omega

/-- The unique element of `𝒯0 F 1` is `ζ_A(1)`. -/
lemma coe_T0_one (i : 𝒯0 F 1) : (i : RatFunc.CompletionAtInfty F) = ζ_A F (single oneExp) := by
  simpa only [T0_one_eq F, Set.mem_singleton_iff] using i.2

/-- The unique element of `𝒯 F 1` is `ζ_A(1)`. -/
lemma coe_T_one (i : 𝒯 F 1) : (i : RatFunc.CompletionAtInfty F) = ζ_A F (single oneExp) := by
  simpa only [T_one_eq F, Set.mem_singleton_iff] using i.2

/-- The index type `↥(𝒯0 F 1)` is a subsingleton. -/
lemma subsingleton_T0_one : Subsingleton (𝒯0 F 1) :=
  ⟨fun a b => Subtype.ext (by rw [coe_T0_one F a, coe_T0_one F b])⟩

/-- The index type `↥(𝒯 F 1)` is a subsingleton. -/
lemma subsingleton_T_one : Subsingleton (𝒯 F 1) :=
  ⟨fun a b => Subtype.ext (by rw [coe_T_one F a, coe_T_one F b])⟩

/-- ★ `𝒯0 F 1` is linearly independent (it is the single nonzero value `ζ_A(1)`). -/
theorem linearIndependent_T0_one :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯0 F 1 → RatFunc.CompletionAtInfty F) := by
  haveI : Subsingleton (𝒯0 F 1) := subsingleton_T0_one F
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hsing : s = {i} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hi, fun j _ => Subsingleton.elim j i⟩
  rw [hsing, Finset.sum_singleton] at hsum
  rcases smul_eq_zero.mp hsum with h | h
  · exact h
  · exact absurd h (by rw [coe_T0_one F i]; exact zeta_one_ne_zero F)

/-- ★ `𝒯 F 1` is linearly independent (it is the single nonzero value `ζ_A(1)`). -/
theorem linearIndependent_T_one :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯 F 1 → RatFunc.CompletionAtInfty F) := by
  haveI : Subsingleton (𝒯 F 1) := subsingleton_T_one F
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hsing : s = {i} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hi, fun j _ => Subsingleton.elim j i⟩
  rw [hsing, Finset.sum_singleton] at hsum
  rcases smul_eq_zero.mp hsum with h | h
  · exact h
  · exact absurd h (by rw [coe_T_one F i]; exact zeta_one_ne_zero F)

/-- `ncard (𝒯0 F 1) = 1`. -/
theorem ncard_T0_one : Set.ncard (𝒯0 F 1) = 1 := by
  rw [T0_one_eq F]
  exact Set.ncard_singleton _

/-- `ncard (𝒯 F 1) = 1`. -/
theorem ncard_T_one : Set.ncard (𝒯 F 1) = 1 := by
  rw [T_one_eq F]
  exact Set.ncard_singleton _

/-- `𝒵 F 1` has positive rank (it contains the nonzero `ζ_A(1)`). -/
theorem rank_Z_one_pos : 0 < Module.rank (RatFunc F) (𝒵 F 1) := by
  rw [rank_pos_iff_exists_ne_zero]
  refine ⟨⟨ζ_A F (single oneExp), zeta_one_mem_Z F⟩, ?_⟩
  intro h
  exact zeta_one_ne_zero F (Subtype.ext_iff.mp h)

/-- `d F 1 = 1`. -/
theorem d_one : d F 1 = 1 := by
  have hq : 2 ≤ Nat.card F := card_ge_two F
  rw [d]
  rw [if_neg (by omega : ¬ (1 = 0))]
  rw [if_pos (by omega : 1 ≤ Nat.card F - 1)]
  norm_num

/-- ★★ THEOREM B at weight `w = 1`. -/
theorem theorem_B_one :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯0 F 1 → RatFunc.CompletionAtInfty F) ∧
      Module.rank (RatFunc F) (𝒵 F 1) ≥ Set.ncard (𝒯0 F 1) := by
  refine ⟨linearIndependent_T0_one F, ?_⟩
  rw [ncard_T0_one F]
  exact Cardinal.one_le_iff_ne_zero.mpr (ne_of_gt (rank_Z_one_pos F))

/-- ★★ THEOREM D at weight `w = 1`. -/
theorem theorem_D_one :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯 F 1 → RatFunc.CompletionAtInfty F) ∧
      Module.rank (RatFunc F) (𝒵 F 1) = d F 1 := by
  refine ⟨linearIndependent_T_one F, ?_⟩
  have hle : Module.rank (RatFunc F) (𝒵 F 1) ≤ d F 1 := (theorem_A_amb F 1).2
  refine le_antisymm hle ?_
  rw [d_one F]
  exact Cardinal.one_le_iff_ne_zero.mpr (ne_of_gt (rank_Z_one_pos F))

end ZagierHoffmanPositiveChar
