/-
# A killing weight with a unique top occurrence prefix

This file proves `Work.ORLyndon.exists_killing_weight_occTerm_max`.

The level method for the `x`-component of the root Fox vector (`Work.ORLyndon.annAt_of_occTerm_lsig_max`
in `Submission/Work/ORLyndon/epsNeZeroDescent.lean`) asks for an **integer weight** `c : α → ℤ` which

* kills the relator, `Work.OROneRel.cohom c u = 1`, and
* separates the *occurrence prefixes* of `x^{±1}` in the defining word `Work.OROneRel.wordOf u` with a
  **unique strict maximum**: for every other occurrence `i`, the weight
  `Work.OROneRel.lsig c (occPref x (wordOf u) i)` is strictly smaller than the weight of the
  distinguished occurrence `i₀`.

This file supplies exactly that weight.  The hypothesis `hsep` says that no two occurrence prefixes
differ by a rational multiple of the exponent-sum vector `y ↦ Work.OROneRel.eps y u` of `u`; under
that hypothesis the general separating-weight lemma `Work.ORLyndon.exists_weight_unique_max` produces
the weight.

The only point that needs care is that `exists_weight_unique_max` is stated for a *finite* index type
of letters, while `α` is arbitrary here: the functions `y ↦ Work.OROneRel.wordEps y (occPref x L i)`
and `y ↦ Work.OROneRel.eps y u` are supported on the finite set `S` of letters occurring in
`Work.OROneRel.wordOf u`, so one restricts to `S`, obtains the weight there and extends it by `0`.
Since the letters outside `S` contribute `0` to *both* sides of the separation condition, the
hypothesis `hsep` over all of `α` is equivalent to its restriction to `S`.

The main work is then the bookkeeping which turns the `ℤ`-valued unique-maximum statement into the
statement about `Work.OROneRel.lsig` on the prefixes, via
`Work.ORLyndon.lsig_sum_wordEps` (`lsig c L = ∑ y, c y * wordEps y L`).
-/
import Mathlib
import Submission.Work.ORLyndon.occDefs
import Submission.Work.ORLyndon.lsig_sum_wordEps
import Submission.Work.ORLyndon.exists_weight_unique_max
import Submission.Work.OROneRel.cohom_mk

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u

namespace Work.ORLyndon

/-- The exponent sum of a letter vanishes on a word in which the letter does not occur. -/
private theorem wordEps_eq_zero_of_forall_fst_ne {α : Type u} (y : α) (L : List (α × Bool))
    (h : ∀ p ∈ L, p.1 ≠ y) : Work.OROneRel.wordEps y L = 0 := by
  simp only [Work.OROneRel.wordEps]
  apply List.sum_eq_zero
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  simp [h p hp]

variable {α : Type u} [DecidableEq α]

/-- **The combinatorial content of `exists_killing_weight_occTerm_max`, for an arbitrary word `L`
representing the relator.**

If `L` is the reduced word of `u` (hypothesis `hu`), if some occurrence of `x^{±1}` in `L` is
labelled by a non-zero occurrence sign, and if no two occurrence prefixes of `x^{±1}` differ by a
rational multiple of the exponent-sum vector of `u`, then there is an integer weight `c` killing `u`
(`Work.OROneRel.cohom c u = 1`) whose `lsig`-weight on the occurrence prefixes has a unique strict
maximum. -/
private theorem aux (L : List (α × Bool)) (x : α) (u : FreeGroup α)
    (hu : L = Work.OROneRel.wordOf u)
    (hex : ∃ i : Fin L.length, Work.ORLyndon.occSign x L i ≠ 0)
    (hsep : ∀ i j : Fin L.length,
      Work.ORLyndon.occSign x L i ≠ 0 → Work.ORLyndon.occSign x L j ≠ 0 → i ≠ j →
      ¬ ∃ lam : ℚ, ∀ y : α,
        (Work.OROneRel.wordEps y (Work.ORLyndon.occPref x L i) : ℚ)
          = (Work.OROneRel.wordEps y (Work.ORLyndon.occPref x L j) : ℚ)
            + lam * (Work.OROneRel.eps y u : ℚ)) :
    ∃ c : α → ℤ, Work.OROneRel.cohom c u = 1 ∧
      ∃ i₀ : Fin L.length,
        Work.ORLyndon.occSign x L i₀ ≠ 0 ∧
        ∀ i : Fin L.length,
          Work.ORLyndon.occSign x L i ≠ 0 → i ≠ i₀ →
          Work.OROneRel.lsig c (Work.ORLyndon.occPref x L i) <
            Work.OROneRel.lsig c (Work.ORLyndon.occPref x L i₀) := by
  classical
  -- `S` is the finite set of letters occurring in `L`; all the functions below are supported on it.
  set S : Finset α := (L.map Prod.fst).toFinset with hS
  have hSmem : ∀ p ∈ L, p.1 ∈ S := by
    intro p hp
    rw [hS]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hL0 : ∀ y : α, y ∉ S → Work.OROneRel.wordEps y L = 0 := by
    intro y hy
    refine wordEps_eq_zero_of_forall_fst_ne y L (fun p hp hpy => ?_)
    exact hy (by rw [hS, ← hpy]; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have hepsL : ∀ y : α, Work.OROneRel.eps y u = Work.OROneRel.wordEps y L := by
    intro y
    have h1 : Work.OROneRel.eps y u = Work.OROneRel.wordEps y (Work.OROneRel.wordOf u) := rfl
    rw [h1, ← hu]
  have hprefL : ∀ (i : Fin L.length) (y : α), y ∉ S →
      Work.OROneRel.wordEps y (Work.ORLyndon.occPref x L i) = 0 := by
    intro i y hy
    refine wordEps_eq_zero_of_forall_fst_ne y (Work.ORLyndon.occPref x L i) (fun p hp hpy => ?_)
    exact hy (hpy ▸ hSmem p (List.Sublist.subset (List.take_sublist _ L) hp))
  -- The separation hypothesis, restricted to the finite letter set `S`.
  have hsepX : ∀ i j : {i : Fin L.length // Work.ORLyndon.occSign x L i ≠ 0}, i ≠ j →
      ¬ ∃ lam : ℚ, ∀ y : {y : α // y ∈ S},
        (Work.OROneRel.wordEps (y:α) (Work.ORLyndon.occPref x L i.1) : ℚ)
          = (Work.OROneRel.wordEps (y:α) (Work.ORLyndon.occPref x L j.1) : ℚ)
            + lam * (Work.OROneRel.eps (y:α) u : ℚ) := by
    intro i j hij h
    obtain ⟨lam, hlam⟩ := h
    have hij' : i.1 ≠ j.1 := fun hh => hij (Subtype.ext hh)
    refine hsep i.1 j.1 i.2 j.2 hij' ⟨lam, fun y => ?_⟩
    by_cases hy : y ∈ S
    · exact hlam ⟨y, hy⟩
    · -- outside `S` both sides vanish, so the equation holds for every `lam`
      rw [hprefL i.1 y hy, hprefL j.1 y hy, hepsL y, hL0 y hy]
      ring
  have hne : Nonempty {i : Fin L.length // Work.ORLyndon.occSign x L i ≠ 0} := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨⟨i, hi⟩⟩
  haveI := hne
  obtain ⟨c₀, hc₀sum, i₀, hc₀max⟩ :=
    Work.ORLyndon.exists_weight_unique_max
      (X := {y : α // y ∈ S})
      (ι := {i : Fin L.length // Work.ORLyndon.occSign x L i ≠ 0})
      (fun i y => Work.OROneRel.wordEps (y:α) (Work.ORLyndon.occPref x L i.1))
      (fun y => Work.OROneRel.eps (y:α) u) hsepX
  -- Extend `c₀` to `α` by zero off `S`.
  let c : α → ℤ := fun y => if hy : y ∈ S then c₀ ⟨y, hy⟩ else 0
  have hcS : ∀ y : {y : α // y ∈ S}, c (y:α) = c₀ y := by
    intro y
    show (if hy' : (y:α) ∈ S then c₀ ⟨(y:α), hy'⟩ else 0) = c₀ y
    rw [dif_pos y.2]
  -- `c` kills `u`.
  have hlsig0 : Work.OROneRel.lsig c L = 0 := by
    have hcast : ((Work.OROneRel.lsig c L : ℤ) : ℚ) = 0 := by
      rw [Work.ORLyndon.lsig_sum_wordEps c L S hSmem]
      push_cast
      rw [Finset.sum_subtype S (fun y => Iff.rfl)
        (fun y => (c y : ℚ) * (Work.OROneRel.wordEps y L : ℚ))]
      have hcongr : (∑ y : {y : α // y ∈ S},
            (c (y:α) : ℚ) * (Work.OROneRel.wordEps (y:α) L : ℚ))
          = ∑ y : {y : α // y ∈ S},
              (c₀ y : ℚ) * (Work.OROneRel.eps (y:α) u : ℚ) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [hcS y, ← hepsL (y:α)]
      rw [hcongr]
      exact hc₀sum
    exact_mod_cast hcast
  have hcohom : Work.OROneRel.cohom c u = 1 := by
    have h1 : Work.OROneRel.cohom c u = Multiplicative.ofAdd (Work.OROneRel.lsig c L) := by
      conv_lhs => rw [← Work.OROneRel.mk_wordOf u]
      rw [Work.OROneRel.cohom_mk c (Work.OROneRel.wordOf u), hu]
    rw [h1, hlsig0]
    rfl
  -- The `lsig`-weight of a prefix is the corresponding `ℚ`-valued functional on `S`.
  have hlsigS : ∀ (j : Fin L.length),
      (Work.OROneRel.lsig c (Work.ORLyndon.occPref x L j) : ℚ)
        = ∑ y : {y : α // y ∈ S},
            (c₀ y : ℚ) * (Work.OROneRel.wordEps (y:α) (Work.ORLyndon.occPref x L j) : ℚ) := by
    intro j
    have hsub : ∀ p ∈ Work.ORLyndon.occPref x L j, p.1 ∈ S := by
      intro p hp
      exact hSmem p (List.Sublist.subset (List.take_sublist _ L) hp)
    have hcast : ((Work.OROneRel.lsig c (Work.ORLyndon.occPref x L j) : ℤ) : ℚ)
        = ∑ y ∈ S,
            (c y : ℚ) * (Work.OROneRel.wordEps y (Work.ORLyndon.occPref x L j) : ℚ) := by
      rw [Work.ORLyndon.lsig_sum_wordEps c (Work.ORLyndon.occPref x L j) S hsub]
      push_cast
      rfl
    rw [hcast, Finset.sum_subtype S (fun y => Iff.rfl)
      (fun y => (c y : ℚ) * (Work.OROneRel.wordEps y (Work.ORLyndon.occPref x L j) : ℚ))]
    apply Finset.sum_congr rfl
    intro y _
    rw [hcS y]
  refine ⟨c, hcohom, i₀.1, i₀.2, ?_⟩
  intro i hi hij
  have hji : (⟨i, hi⟩ : {i : Fin L.length // Work.ORLyndon.occSign x L i ≠ 0}) ≠ i₀ :=
    fun hh => hij (congrArg Subtype.val hh)
  have hmax := hc₀max ⟨i, hi⟩ hji
  have hstep : (0:ℚ) < (Work.OROneRel.lsig c (Work.ORLyndon.occPref x L i₀.1) : ℚ)
      - (Work.OROneRel.lsig c (Work.ORLyndon.occPref x L i) : ℚ) := by
    rw [hlsigS i₀.1, hlsigS i]
    rw [← Finset.sum_sub_distrib]
    refine lt_of_lt_of_eq hmax ?_
    apply Finset.sum_congr rfl
    intro y _
    ring
  have : (Work.OROneRel.lsig c (Work.ORLyndon.occPref x L i) : ℚ) <
      (Work.OROneRel.lsig c (Work.ORLyndon.occPref x L i₀.1) : ℚ) := by linarith
  exact_mod_cast this

/-- **A killing weight whose `lsig`-weight on the occurrence prefixes of `x` has a unique strict
maximum.**

Let `u : FreeGroup α` be a relator, `x : α` a letter occurring (with a non-zero occurrence sign, i.e.
as `x` or `x⁻¹`) in the reduced word of `u`, and suppose that no two occurrence prefixes of `x^{±1}`
in that word differ by a rational multiple of the exponent-sum vector `y ↦ eps y u` of `u`.  Then
there are integer weights `c : α → ℤ` with `cohom c u = 1` and a distinguished occurrence `i₀` of
`x^{±1}` whose prefix has *strictly larger* weight `lsig c` than the prefix of every other
occurrence. -/
theorem exists_killing_weight_occTerm_max {α : Type u} [DecidableEq α] (u : FreeGroup α) (x : α)
    (hex : ∃ i : Fin (Work.OROneRel.wordOf u).length,
      Work.ORLyndon.occSign x (Work.OROneRel.wordOf u) i ≠ 0)
    (hsep : ∀ i j : Fin (Work.OROneRel.wordOf u).length,
      Work.ORLyndon.occSign x (Work.OROneRel.wordOf u) i ≠ 0 →
      Work.ORLyndon.occSign x (Work.OROneRel.wordOf u) j ≠ 0 → i ≠ j →
      ¬ ∃ lam : ℚ, ∀ y : α,
        (Work.OROneRel.wordEps y (Work.ORLyndon.occPref x (Work.OROneRel.wordOf u) i) : ℚ)
          = (Work.OROneRel.wordEps y (Work.ORLyndon.occPref x (Work.OROneRel.wordOf u) j) : ℚ)
            + lam * (Work.OROneRel.eps y u : ℚ)) :
    ∃ c : α → ℤ, Work.OROneRel.cohom c u = 1 ∧
      ∃ i₀ : Fin (Work.OROneRel.wordOf u).length,
        Work.ORLyndon.occSign x (Work.OROneRel.wordOf u) i₀ ≠ 0 ∧
        ∀ i : Fin (Work.OROneRel.wordOf u).length,
          Work.ORLyndon.occSign x (Work.OROneRel.wordOf u) i ≠ 0 → i ≠ i₀ →
          Work.OROneRel.lsig c (Work.ORLyndon.occPref x (Work.OROneRel.wordOf u) i) <
            Work.OROneRel.lsig c (Work.ORLyndon.occPref x (Work.OROneRel.wordOf u) i₀) :=
  aux (Work.OROneRel.wordOf u) x u rfl hex hsep

end Work.ORLyndon
