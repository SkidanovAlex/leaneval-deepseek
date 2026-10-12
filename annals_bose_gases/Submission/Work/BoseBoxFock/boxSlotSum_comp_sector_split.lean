import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotSum_sector_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxSlotSum_comp_sector_split` — the sector split for a *composition*

`slotSum_sector_split` (`slotSum_sector_split.lean`) proves the block-diagonal (sector) splitting
of the quadratic form of a **single** first-quantised slot sum:

`∫ star Φ · boxSlotSum e T Φ = ∑_S ∫ star (slotExact e S Φ) · boxSlotSum e T (slotExact e S Φ)`

for `Φ` continuous with compact support.  The present file proves the same identity for a
**composition** `boxSlotSum e T₁ ∘ boxSlotSum e T₂`, which is what the box ↔ model bridge needs
when two one-body rows of the box Hamiltonian (`H2ndF`) are applied in succession.

The proof uses the same three ingredients as for a single slot sum, and the file is organised
accordingly:

* `boxSlotSum_slotProj1_comm` — the slot sum commutes with every one-slot projection
  `slotProj1 e i` (the local `have hcommA` of `slotSum_sector_split`, exported);
* `sector_split_general` — the abstract splitting: for **any** `B : (Xn n → ℂ) → (Xn n → ℂ)`
  which is regular (preserves measurability/boundedness), commutes with every `slotProj1`,
  kills the zero state, and distributes over the sector decomposition of `Φ`, the quadratic form
  of `B` splits over the sectors.  The proof is the script of `slotSum_sector_split` with
  `boxSlotSum e T` replaced by `B`; the two extra hypotheses replace the two facts (`boxSlotSum`
  is linear in the state, and `boxSlotSum e T 0 = 0`) which were previously proved inside that
  theorem;
* the target theorem is then a short instantiation: `hBreg` and `hBcomm` are
  `boxSlotSum_measurable_bounded` and `boxSlotSum_slotProj1_comm` applied twice, and `hBadd` is
  the pointwise sector decomposition of `boxSlotSum e T₂ Φ` pushed through the linearity
  `boxSlotSum_finset_sum` of `boxSlotSum` in its state argument.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory
open Work.BoseDict

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Commutation of a slot sum with the one-slot projection

This is the local `have hcommA` of `slotSum_sector_split`, exported as a theorem: the `j`-slot
operator of `boxSlotSum` is `boxSlotOf e e_l e_{l'} j`, which commutes with `slotProj1 e i` for
`i ≠ j` (`boxSlotOf_slotProj1_comm`) and is absorbed by it for `i = j`
(`slotProj1_boxSlotOf_self`, `boxSlotOf_slotProj1_self`); the finite sums are handled by
`slotProj1_finset_sum_fun` / `slotProj1_finset_sum_smul`. -/

theorem boxSlotSum_slotProj1_comm {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : Ω => star (e l z) * e l' z))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (Θ : (Fin n → Ω) → ℂ) (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    (i : Fin n) :
    slotProj1 e i (boxSlotSum e T Θ) = boxSlotSum e T (slotProj1 e i Θ) := by
  have hbox : ∀ (l l' : Fin m) (j : Fin n),
      Measurable (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) ∧
        ∃ C, ∀ x, ‖Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l)
          (Work.BoseB4.evec m l') j Θ x‖ ≤ C :=
    fun l l' j => boxSlotOf_measurable_bounded e he hec (Work.BoseB4.evec m l)
      (Work.BoseB4.evec m l') j Θ hΘm hΘb
  have hOpComm : ∀ j : Fin n, slotProj1 e i (slotOp e T j Θ) = slotOp e T j (slotProj1 e i Θ) := by
    intro j
    have hinner : ∀ (l : Fin m),
        Measurable (∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
        ∧ ∃ C, ∀ x, ‖(∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) x‖ ≤ C := by
      intro l
      constructor
      · have hmeas : Measurable (fun x : Fin n → Ω => ∑ l' : Fin m,
            T (Work.BoseB4.evec m l') l •
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x) := by
          refine Finset.measurable_sum _ (fun l' _ => ?_)
          exact ((hbox l l' j).1).const_smul (T (Work.BoseB4.evec m l') l)
        convert hmeas using 1
        funext x
        simp only [Finset.sum_apply, Pi.smul_apply]
      · choose Cb hCb using fun l' : Fin m => (hbox l l' j).2
        refine ⟨∑ l' : Fin m, |T (Work.BoseB4.evec m l') l| * max (Cb l') 0, fun x => ?_⟩
        rw [Finset.sum_apply]
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum (fun l' _ => ?_)
        simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((hCb l' x).trans (le_max_left _ _)) (abs_nonneg _)
    have hL : slotProj1 e i (slotOp e T j Θ)
        = ∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
            slotProj1 e i (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l)
              (Work.BoseB4.evec m l') j Θ) := by
      rw [slotOp]
      rw [slotProj1_finset_sum_fun e he hec i Finset.univ
        (fun l => ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
        (fun l => (hinner l).1) (fun l => (hinner l).2)]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [slotProj1_finset_sum_smul e he hec i Finset.univ
        (fun l' : Fin m => T (Work.BoseB4.evec m l') l)
        (fun l' => Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
        (fun l' => (hbox l l' j).1) (fun l' => (hbox l l' j).2)]
    have hR : slotOp e T j (slotProj1 e i Θ)
        = ∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
              (slotProj1 e i Θ) := rfl
    rw [hL, hR]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine Finset.sum_congr rfl (fun l' _ => ?_)
    by_cases hji : j = i
    · subst hji
      rw [slotProj1_boxSlotOf_self e l l' j he hec horth hint Θ hΘm hΘb]
      rw [boxSlotOf_slotProj1_self e l l' j he hec horth hint Θ hΘm hΘb]
    · rw [← boxSlotOf_slotProj1_comm e l l' i j (fun h => hji h.symm) he hec horth hint
        Θ hΘm hΘb]
  have hOp_m : ∀ j : Fin n, Measurable (slotOp e T j Θ) :=
    fun j => (slotOp_measurable_bounded e he hec T j Θ hΘm hΘb).1
  have hOp_b : ∀ j : Fin n, ∃ C, ∀ x, ‖slotOp e T j Θ x‖ ≤ C :=
    fun j => (slotOp_measurable_bounded e he hec T j Θ hΘm hΘb).2
  rw [boxSlotSum_eq_sum_slotOp e T Θ, boxSlotSum_eq_sum_slotOp e T (slotProj1 e i Θ),
    slotProj1_finset_sum_fun e he hec i Finset.univ (fun j => slotOp e T j Θ) hOp_m hOp_b]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hOpComm j]

/-! ## 2. The abstract sector split

`B` is an arbitrary map on states which is regular, commutes with every one-slot projection,
kills the zero state, and distributes over the sector decomposition of the given state `Φ`.  Then
the quadratic form of `B` on `Φ` splits over the sectors. -/

theorem sector_split_general {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (B : ((Fin n → Ω) → ℂ) → ((Fin n → Ω) → ℂ))
    (hBreg : ∀ Θ : (Fin n → Ω) → ℂ, Measurable Θ → (∃ C, ∀ x, ‖Θ x‖ ≤ C) →
      Measurable (B Θ) ∧ ∃ C, ∀ x, ‖B Θ x‖ ≤ C)
    (hBcomm : ∀ (Θ : (Fin n → Ω) → ℂ) (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
      (i : Fin n), slotProj1 e i (B Θ) = B (slotProj1 e i Θ))
    (hBzero : B (0 : (Fin n → Ω) → ℂ) = 0)
    (Φ : (Fin n → Ω) → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hBadd : ∀ x : Fin n → Ω, B Φ x = ∑ S : Finset (Fin n), B (slotExact e S Φ) x) :
    ∫ x, star (Φ x) * B Φ x
      = ∑ S : Finset (Fin n), ∫ x, star (slotExact e S Φ x) * B (slotExact e S Φ) x := by
  classical
  have hΦm : Measurable Φ := hΦ.measurable
  have hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C := hΦ.bounded_above_of_compact_support hΦc
  have hsec : ∀ S : Finset (Fin n),
      Measurable (slotExact e S Φ) ∧ (∃ C, ∀ x, ‖slotExact e S Φ x‖ ≤ C) ∧
        HasCompactSupport (slotExact e S Φ) :=
    fun S => slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  have hAsec : ∀ S : Finset (Fin n),
      Measurable (B (slotExact e S Φ)) ∧ (∃ C, ∀ x, ‖B (slotExact e S Φ) x‖ ≤ C) :=
    fun S => hBreg _ (hsec S).1 (hsec S).2.1
  -- (3) the sector projection fixes `B (slotExact e S' Φ)`
  have hkey : ∀ (S' : Finset (Fin n)) (Υ : (Fin n → Ω) → ℂ), Measurable Υ →
      (∃ C, ∀ x, ‖Υ x‖ ≤ C) →
      (∀ i : Fin n, slotProj1 e i Υ = if i ∈ S' then Υ else 0) → slotExact e S' Υ = Υ := by
    intro S' Υ hΥm hΥb hiii
    have hclass : ∀ T : Finset (Fin n), slotProj e T Υ = if T ⊆ S' then Υ else 0 := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        rw [if_pos (Finset.empty_subset S')]
        rw [slotProj_eq_slotInt_fun]
        exact slotInt_empty e Υ
      | insert a T' ha ih =>
        have hpeel : slotProj e (insert a T') Υ = slotProj1 e a (slotProj e T' Υ) := by
          have h := slotInt_peelMB e he hec (S := T') (i := a) ha Υ hΥm hΥb
          rw [Finset.union_singleton] at h
          rw [slotProj_eq_slotInt_fun]
          exact h
        rw [hpeel, ih]
        by_cases hTS : T' ⊆ S'
        · by_cases haS : a ∈ S'
          · have hins : insert a T' ⊆ S' := Finset.insert_subset haS hTS
            rw [if_pos hTS, hiii a, if_pos haS, if_pos hins]
          · have hins : ¬ (insert a T' ⊆ S') := fun hc => haS (Finset.insert_subset_iff.mp hc).1
            rw [if_pos hTS, hiii a, if_neg haS, if_neg hins]
        · have hins : ¬ (insert a T' ⊆ S') := fun hc => hTS (Finset.insert_subset_iff.mp hc).2
          rw [if_neg hTS, if_neg hins]
          exact slotProj1_zero e a
    have hexp : slotExact e S' Υ = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S' ⊆ T),
        (-1 : ℂ) ^ (T.card - S'.card) • slotProj e T Υ := rfl
    rw [hexp]
    rw [Finset.sum_eq_single S']
    · rw [hclass S', if_pos (Finset.Subset.refl S')]
      simp
    · intro T hT hTS
      rw [hclass T,
        if_neg (fun hc => hTS (Finset.Subset.antisymm hc (Finset.mem_filter.mp hT).2)), smul_zero]
    · intro hmem
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ S', Finset.Subset.refl S'⟩) hmem
  have hfix : ∀ S' : Finset (Fin n),
      slotExact e S' (B (slotExact e S' Φ)) = B (slotExact e S' Φ) := by
    intro S'
    refine hkey S' _ (hAsec S').1 (hAsec S').2 ?_
    intro i
    rw [hBcomm (slotExact e S' Φ) (hsec S').1 (hsec S').2.1 i]
    by_cases hi : i ∈ S'
    · rw [if_pos hi]
      have hfix1 : slotProj1 e i (slotExact e S' Φ) = slotExact e S' Φ := by
        rw [← slotProj_singleton_eq_slotProj1_cont e he hec i (slotExact e S' Φ) (hsec S').1
          (hsec S').2.1]
        exact sx_absorb e he hec horth {i} S' (Finset.singleton_subset_iff.mpr hi) Φ hΦm hΦb
      rw [hfix1]
    · rw [if_neg hi]
      have hfix0 : slotProj1 e i (slotExact e S' Φ) = 0 :=
        slotProj1_slotExact_eq_zero e he hec horth S' i hi Φ hΦm hΦb
      rw [hfix0, hBzero]
  -- (4) off-diagonal vanishing
  have hOD : ∀ S S' : Finset (Fin n), S ≠ S' →
      ∫ x, star (slotExact e S Φ x) * B (slotExact e S' Φ) x = 0 := by
    intro S S' hne
    have h := slotExact_orth_gen e he hec horth S S' Φ hΦ hΦc
      (B (slotExact e S' Φ)) (hAsec S').1 (hAsec S').2
    rw [hfix S'] at h
    rw [h, if_neg hne]
  -- (5) expand the LHS into the double sector sum
  have hL : ∫ x, star (Φ x) * B Φ x
      = ∑ S : Finset (Fin n), ∑ S' : Finset (Fin n),
          ∫ x, star (slotExact e S Φ x) * B (slotExact e S' Φ) x := by
    have hpt : ∀ x, star (Φ x) * B Φ x
        = star (∑ S : Finset (Fin n), slotExact e S Φ x)
          * (∑ S' : Finset (Fin n), B (slotExact e S' Φ) x) := by
      intro x
      have h1 : (Finset.sum Finset.univ (fun S : Finset (Fin n) => slotExact e S Φ x)) = Φ x := by
        have h2 : (Finset.sum Finset.univ (fun S : Finset (Fin n) => slotExact e S Φ)) x = Φ x :=
          congrFun (slotExact_sum_eq e Φ) x
        simpa only [Finset.sum_apply] using h2
      rw [h1, hBadd x]
    rw [show (∫ x, star (Φ x) * B Φ x)
        = ∫ x, star (∑ S : Finset (Fin n), slotExact e S Φ x)
            * (∑ S' : Finset (Fin n), B (slotExact e S' Φ) x) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_star_sum_mul_sum (Finset.univ : Finset (Finset (Fin n))) Finset.univ
      (fun S => slotExact e S Φ) (fun S' => B (slotExact e S' Φ))
      (fun S => (hsec S).2.2) (fun S => (hsec S).1) (fun S => (hsec S).2.1)
      (fun S => (hAsec S).1) (fun S => (hAsec S).2)]
  rw [hL]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_eq_single S]
  · intro S' _ hS'
    exact hOD S S' (fun h => hS' h.symm)
  · intro hS
    exact absurd (Finset.mem_univ S) hS

theorem boxSlotSum_comp_sector_split {m n : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (T₁ T₂ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) :
    ∫ x, star (Φ x) * Work.BoseDict.boxSlotSum e T₁ (Work.BoseDict.boxSlotSum e T₂ Φ) x
      = ∑ S : Finset (Fin n),
          ∫ x, star (Work.BoseBoxFock.slotExact e S Φ x)
            * Work.BoseDict.boxSlotSum e T₁
                (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x := by
  classical
  have hΦm : Measurable Φ := hΦ.measurable
  have hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C := hΦ.bounded_above_of_compact_support hΦc
  have hsec : ∀ S : Finset (Fin n),
      Measurable (slotExact e S Φ) ∧ (∃ C, ∀ x, ‖slotExact e S Φ x‖ ≤ C) ∧
        HasCompactSupport (slotExact e S Φ) :=
    fun S => slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  have hA2reg : ∀ S : Finset (Fin n),
      Measurable (boxSlotSum e T₂ (slotExact e S Φ)) ∧
        (∃ C, ∀ x, ‖boxSlotSum e T₂ (slotExact e S Φ) x‖ ≤ C) :=
    fun S => boxSlotSum_measurable_bounded e he hec T₂ (slotExact e S Φ) (hsec S).1 (hsec S).2.1
  -- regularity of the composite
  have hBreg : ∀ Θ : (Fin n → Ω) → ℂ, Measurable Θ → (∃ C, ∀ x, ‖Θ x‖ ≤ C) →
      Measurable (boxSlotSum e T₁ (boxSlotSum e T₂ Θ)) ∧
        ∃ C, ∀ x, ‖boxSlotSum e T₁ (boxSlotSum e T₂ Θ) x‖ ≤ C := by
    intro Θ hΘm hΘb
    obtain ⟨h1m, h1b⟩ := boxSlotSum_measurable_bounded e he hec T₂ Θ hΘm hΘb
    exact boxSlotSum_measurable_bounded e he hec T₁ (boxSlotSum e T₂ Θ) h1m h1b
  -- commutation of the composite with the one-slot projection
  have hBcomm : ∀ (Θ : (Fin n → Ω) → ℂ) (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
      (i : Fin n),
      slotProj1 e i (boxSlotSum e T₁ (boxSlotSum e T₂ Θ))
        = boxSlotSum e T₁ (boxSlotSum e T₂ (slotProj1 e i Θ)) := by
    intro Θ hΘm hΘb i
    obtain ⟨h1m, h1b⟩ := boxSlotSum_measurable_bounded e he hec T₂ Θ hΘm hΘb
    rw [boxSlotSum_slotProj1_comm e he hec horth hint T₁ (boxSlotSum e T₂ Θ) h1m h1b i,
      boxSlotSum_slotProj1_comm e he hec horth hint T₂ Θ hΘm hΘb i]
  -- the composite kills the zero state
  have hBzero : boxSlotSum e T₁ (boxSlotSum e T₂ (0 : (Fin n → Ω) → ℂ)) = 0 := by
    have h : boxSlotSum e T₁ (boxSlotSum e T₂ (fun _ : Fin n → Ω => (0 : ℂ)))
        = fun _ => 0 := by
      rw [boxSlotSum_zero e he hec T₂, boxSlotSum_zero e he hec T₁]
    exact h
  -- the composite distributes over the sector decomposition
  have hBadd : ∀ x : Fin n → Ω,
      boxSlotSum e T₁ (boxSlotSum e T₂ Φ) x
        = ∑ S : Finset (Fin n), boxSlotSum e T₁ (boxSlotSum e T₂ (slotExact e S Φ)) x := by
    intro x
    have hA2 : boxSlotSum e T₂ Φ
        = fun y : Fin n → Ω => ∑ S : Finset (Fin n), boxSlotSum e T₂ (slotExact e S Φ) y := by
      have hsum : (fun y : Fin n → Ω =>
          Finset.sum Finset.univ (fun S : Finset (Fin n) => (1 : ℂ) • slotExact e S Φ y))
            = Φ := by
        funext y
        have h1 : (Finset.sum Finset.univ (fun S : Finset (Fin n) => slotExact e S Φ)) y = Φ y :=
          congrFun (slotExact_sum_eq e Φ) y
        simpa only [one_smul, Finset.sum_apply] using h1
      calc boxSlotSum e T₂ Φ
          = boxSlotSum e T₂ (fun y : Fin n → Ω =>
              Finset.sum Finset.univ (fun S : Finset (Fin n) => (1 : ℂ) • slotExact e S Φ y)) :=
            congrArg (fun Ψ => boxSlotSum e T₂ Ψ) hsum.symm
        _ = fun y : Fin n → Ω => ∑ S : Finset (Fin n),
              (1 : ℂ) • boxSlotSum e T₂ (slotExact e S Φ) y :=
            boxSlotSum_finset_sum e he hec T₂ Finset.univ (fun _ => (1 : ℂ))
              (fun S => slotExact e S Φ) (fun S => (hsec S).1) (fun S => (hsec S).2.1)
        _ = fun y : Fin n → Ω => ∑ S : Finset (Fin n),
              boxSlotSum e T₂ (slotExact e S Φ) y := by
            funext y
            simp
    have hEq : (fun y : Fin n → Ω => Finset.sum Finset.univ (fun S : Finset (Fin n) =>
        (1 : ℂ) • boxSlotSum e T₂ (slotExact e S Φ) y)) = boxSlotSum e T₂ Φ := by
      funext y
      simp only [one_smul]
      exact (congrFun hA2 y).symm
    have h1 : boxSlotSum e T₁ (boxSlotSum e T₂ Φ) = boxSlotSum e T₁ (fun y : Fin n → Ω =>
        Finset.sum Finset.univ (fun S : Finset (Fin n) =>
          (1 : ℂ) • boxSlotSum e T₂ (slotExact e S Φ) y)) :=
      congrArg (fun Ψ => boxSlotSum e T₁ Ψ) hEq.symm
    have h2 : boxSlotSum e T₁ (fun y : Fin n → Ω =>
        Finset.sum Finset.univ (fun S : Finset (Fin n) =>
          (1 : ℂ) • boxSlotSum e T₂ (slotExact e S Φ) y))
        = fun x : Fin n → Ω => ∑ S : Finset (Fin n),
          (1 : ℂ) • boxSlotSum e T₁ (boxSlotSum e T₂ (slotExact e S Φ)) x :=
      boxSlotSum_finset_sum e he hec T₁ Finset.univ (fun _ => (1 : ℂ))
        (fun S => boxSlotSum e T₂ (slotExact e S Φ))
        (fun S => (hA2reg S).1) (fun S => (hA2reg S).2)
    rw [h1, h2]
    simp
  exact sector_split_general e he hec horth
    (fun Θ : (Fin n → Ω) → ℂ => boxSlotSum e T₁ (boxSlotSum e T₂ Θ))
    hBreg hBcomm hBzero Φ hΦ hΦc hBadd

end Work.BoseBoxFock
