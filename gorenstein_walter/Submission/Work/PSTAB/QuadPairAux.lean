/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PSTAB area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.PSTAB.Defs

set_option autoImplicit false

/-!
# `Work.PSTAB.QuadPairAux` — the module-theoretic skeleton of `QuadPairSection`

Working vocabulary for `Work.PSTAB.QuadPairSection` (`Defs.lean`):

* `Work.PSTAB.RepInv ρ U` — the submodule `U` is stable under the representation `ρ`;
* `Work.PSTAB.mpob ρ U` — a maximal proper `ρ`-invariant submodule of `U` (`⊥` if none);
* `Work.PSTAB.invSer ρ` — the `ℕ`-indexed *chief series* of `V` as an `𝔽_p[L]`-module: starting
  from `⊤` and repeatedly taking `mpob`; it reaches `⊥` and every factor is a simple
  `𝔽_p[L]`-module;
* `Work.PSTAB.NSub ρ` — the normal subgroup of `L` consisting of the elements acting trivially on
  every factor of this series;
* `Work.PSTAB.NSub.pow_sub_one_eq_zero` — an element of `NSub ρ` acts unipotently
  (`(ρ g - 1)` is nilpotent).

All elementary facts are proved here; the two heavier pieces are stated in the companion modules
`Submission.Work.PSTAB.QuadPairFactor` (the quotient representation on a factor) and
`Submission.Work.PSTAB.NilpotentUnit` (the unipotent-orders lemma).
-/

namespace Work.PSTAB

variable {L : Type*} [Group L] {p : ℕ} [Fact p.Prime] {V : Type*}
  [AddCommGroup V] [Module (ZMod p) V] [Finite V]

/-- A submodule of `V` stable under the representation `ρ`. -/
def RepInv (ρ : Representation (ZMod p) L V) (U : Submodule (ZMod p) V) : Prop :=
  ∀ g : L, ∀ v ∈ U, ρ g v ∈ U

theorem repInv_top (ρ : Representation (ZMod p) L V) : RepInv ρ ⊤ :=
  fun _ _ _ => Submodule.mem_top

theorem repInv_bot (ρ : Representation (ZMod p) L V) : RepInv ρ ⊥ := by
  intro g v hv
  rw [Submodule.mem_bot] at hv ⊢
  rw [hv, map_zero]

/-- A maximal proper `ρ`-invariant submodule of `U`, or `⊥` if there is none. -/
noncomputable def mpob (ρ : Representation (ZMod p) L V) (U : Submodule (ZMod p) V) :
    Submodule (ZMod p) V := by
  classical
  by_cases h : ∃ W : Submodule (ZMod p) V, RepInv ρ W ∧ W < U
  · exact ((Set.toFinite {W : Submodule (ZMod p) V | RepInv ρ W ∧ W < U}).exists_maximal h).choose
  · exact ⊥

theorem mpob_spec {ρ : Representation (ZMod p) L V} {U : Submodule (ZMod p) V}
    (h : ∃ W : Submodule (ZMod p) V, RepInv ρ W ∧ W < U) :
    RepInv ρ (mpob ρ U) ∧ mpob ρ U < U ∧
      ∀ W : Submodule (ZMod p) V, RepInv ρ W → W < U → mpob ρ U ≤ W → W ≤ mpob ρ U := by
  classical
  have hspec :=
    ((Set.toFinite {W : Submodule (ZMod p) V | RepInv ρ W ∧ W < U}).exists_maximal h).choose_spec
  unfold mpob
  rw [dite_eq_left h]
  exact ⟨hspec.1.1, hspec.1.2, fun W hW hWU hm => hspec.2 ⟨hW, hWU⟩ hm⟩

theorem repInv_mpob (ρ : Representation (ZMod p) L V) (U : Submodule (ZMod p) V) :
    RepInv ρ (mpob ρ U) := by
  classical
  by_cases h : ∃ W : Submodule (ZMod p) V, RepInv ρ W ∧ W < U
  · exact (mpob_spec h).1
  · unfold mpob
    rw [dite_eq_right h]
    exact repInv_bot ρ

theorem mpob_le (ρ : Representation (ZMod p) L V) (U : Submodule (ZMod p) V) :
    mpob ρ U ≤ U := by
  classical
  by_cases h : ∃ W : Submodule (ZMod p) V, RepInv ρ W ∧ W < U
  · exact (mpob_spec h).2.1.le
  · unfold mpob
    rw [dite_eq_right h]
    exact bot_le

theorem mpob_bot (ρ : Representation (ZMod p) L V) : mpob ρ (⊥ : Submodule (ZMod p) V) = ⊥ := by
  classical
  unfold mpob
  rw [dite_eq_right]
  rintro ⟨W, _, hW⟩
  exact absurd hW not_lt_bot

theorem mpob_lt_of_ne_bot (ρ : Representation (ZMod p) L V) {U : Submodule (ZMod p) V}
    (hU : U ≠ ⊥) : mpob ρ U < U := by
  classical
  refine (mpob_spec ?_).2.1
  exact ⟨⊥, repInv_bot ρ, bot_lt_iff_ne_bot.mpr hU⟩

/-- Maximality of `mpob ρ U`: an invariant submodule between `mpob ρ U` and `U` is one of the
two. -/
theorem mpob_maximal (ρ : Representation (ZMod p) L V) {U : Submodule (ZMod p) V} (hU : U ≠ ⊥)
    {S : Submodule (ZMod p) V} (hS : RepInv ρ S) (hm : mpob ρ U ≤ S) (hSU : S ≤ U) :
    S = mpob ρ U ∨ S = U := by
  classical
  rcases lt_or_eq_of_le hSU with hlt | heq
  · left
    have h : ∃ W : Submodule (ZMod p) V, RepInv ρ W ∧ W < U :=
      ⟨⊥, repInv_bot ρ, bot_lt_iff_ne_bot.mpr hU⟩
    exact le_antisymm ((mpob_spec h).2.2 S hS hlt hm) hm
  · exact Or.inr heq

/-- The chief series of the `𝔽_p[L]`-module `V`: `⊤` followed by iterated `mpob`. -/
noncomputable def invSer (ρ : Representation (ZMod p) L V) : ℕ → Submodule (ZMod p) V
  | 0 => ⊤
  | n + 1 => mpob ρ (invSer ρ n)

theorem invSer_zero (ρ : Representation (ZMod p) L V) : invSer ρ 0 = ⊤ := rfl

theorem invSer_succ (ρ : Representation (ZMod p) L V) (n : ℕ) :
    invSer ρ (n + 1) = mpob ρ (invSer ρ n) := rfl

theorem repInv_invSer (ρ : Representation (ZMod p) L V) (n : ℕ) : RepInv ρ (invSer ρ n) := by
  induction n with
  | zero => rw [invSer_zero]; exact repInv_top ρ
  | succ n _ => rw [invSer_succ]; exact repInv_mpob ρ _

theorem invSer_le_self (ρ : Representation (ZMod p) L V) (n : ℕ) : invSer ρ (n + 1) ≤ invSer ρ n := by
  rw [invSer_succ]
  exact mpob_le ρ _

theorem invSer_antitone (ρ : Representation (ZMod p) L V) : Antitone (invSer ρ) :=
  antitone_nat_of_succ_le fun n => invSer_le_self ρ n

theorem invSer_lt_of_ne_bot (ρ : Representation (ZMod p) L V) {n : ℕ} (h : invSer ρ n ≠ ⊥) :
    invSer ρ (n + 1) < invSer ρ n := by
  rw [invSer_succ]
  exact mpob_lt_of_ne_bot ρ h

theorem invSer_exists_eq_bot (ρ : Representation (ZMod p) L V) : ∃ n : ℕ, invSer ρ n = ⊥ := by
  by_contra h
  push Not at h
  have hstrict : StrictAnti (invSer ρ) :=
    strictAnti_nat_of_succ_lt fun n => invSer_lt_of_ne_bot ρ (h n)
  have hinj : Function.Injective (invSer ρ) := hstrict.injective
  have : Finite ℕ := Finite.of_injective _ hinj
  exact (Infinite.not_finite (α := ℕ)) this

/-- An element of `L` acts trivially on every factor of the series `invSer ρ`. -/
def NFun (ρ : Representation (ZMod p) L V) (g : L) : Prop :=
  ∀ i : ℕ, ∀ v ∈ invSer ρ i, ρ g v - v ∈ invSer ρ (i + 1)

theorem nFun_one (ρ : Representation (ZMod p) L V) : NFun ρ 1 := by
  intro i v hv
  rw [map_one, Module.End.one_apply, sub_self]
  exact (invSer ρ (i + 1)).zero_mem

theorem NFun.mul {ρ : Representation (ZMod p) L V} {g h : L} (hg : NFun ρ g) (hh : NFun ρ h) :
    NFun ρ (g * h) := by
  intro i v hv
  have h1 : ρ h v - v ∈ invSer ρ (i + 1) := hh i v hv
  have h2 : ρ g (ρ h v - v) ∈ invSer ρ (i + 1) := repInv_invSer ρ (i + 1) g _ h1
  have h3 : ρ g v - v ∈ invSer ρ (i + 1) := hg i v hv
  have hsum : ρ g (ρ h v - v) + (ρ g v - v) ∈ invSer ρ (i + 1) :=
    (invSer ρ (i + 1)).add_mem h2 h3
  have heq : ρ (g * h) v - v = ρ g (ρ h v - v) + (ρ g v - v) := by
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel
  rwa [heq]

theorem NFun.inv {ρ : Representation (ZMod p) L V} {g : L} (hg : NFun ρ g) : NFun ρ g⁻¹ := by
  intro i v hv
  have h1 : ρ g v - v ∈ invSer ρ (i + 1) := hg i v hv
  have h2 : ρ g⁻¹ (ρ g v - v) ∈ invSer ρ (i + 1) := repInv_invSer ρ (i + 1) g⁻¹ _ h1
  have hneg : -ρ g⁻¹ (ρ g v - v) ∈ invSer ρ (i + 1) := (invSer ρ (i + 1)).neg_mem h2
  have hfix : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have heq : ρ g⁻¹ v - v = -ρ g⁻¹ (ρ g v - v) := by
    rw [map_sub, hfix]
    abel
  rwa [heq]

/-- The normal subgroup of `L` consisting of the elements acting trivially on every factor of the
chief series of `V`. -/
def NSub (ρ : Representation (ZMod p) L V) : Subgroup L where
  carrier := {g : L | NFun ρ g}
  mul_mem' := fun hg hh => hg.mul hh
  one_mem' := nFun_one ρ
  inv_mem' := fun hg => hg.inv

theorem mem_NSub {ρ : Representation (ZMod p) L V} {g : L} : g ∈ NSub ρ ↔ NFun ρ g := Iff.rfl

/-- An element of `NSub ρ` acts unipotently. -/
theorem NSub.pow_sub_one_eq_zero (ρ : Representation (ZMod p) L V) {g : L} (hg : g ∈ NSub ρ) :
    ∃ k : ℕ, ((ρ g : Module.End (ZMod p) V) - 1) ^ k = 0 := by
  obtain ⟨K, hK⟩ := invSer_exists_eq_bot ρ
  have hg' : NFun ρ g := hg
  refine ⟨K + 1, ?_⟩
  have key : ∀ (j : ℕ), ∀ v : V, (((ρ g : Module.End (ZMod p) V) - 1) ^ j) v ∈ invSer ρ j := by
    intro j
    induction j with
    | zero =>
      intro v
      rw [invSer_zero, pow_zero, Module.End.one_apply]
      exact Submodule.mem_top
    | succ j ih =>
      intro v
      have h1 : (((ρ g : Module.End (ZMod p) V) - 1) ^ j) v ∈ invSer ρ j := ih v
      have hkey : (((ρ g : Module.End (ZMod p) V) - 1) ^ (j + 1)) v
          = (ρ g - 1) ((((ρ g : Module.End (ZMod p) V) - 1) ^ j) v) := by
        rw [pow_succ', Module.End.mul_apply]
      rw [hkey, LinearMap.sub_apply, Module.End.one_apply]
      exact hg' j _ h1
  ext v
  have h := key (K + 1) v
  rw [show invSer ρ (K + 1) = ⊥ by rw [invSer_succ, hK, mpob_bot], Submodule.mem_bot] at h
  simpa using h

end Work.PSTAB
