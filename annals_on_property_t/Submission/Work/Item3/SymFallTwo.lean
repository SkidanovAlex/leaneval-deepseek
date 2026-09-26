import Submission.Work.Item3.SymStep
import Submission.Work.FallTwoExcess
import Submission.Work.FallTwoStep

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# SymFallTwo: the residual symmetric-energy Fall-II step, assembled

This module assembles the pin `SymEnergy.SymFallTwoEnergyStep n` — the last
combinatorial input of Nielsen's generation theorem `aut_nielsen`
(`SymEnergy.aut_nielsen_of_symFallTwoEnergyStep`) — from the pieces proved in
`SymStep`/`SymEnergy`/`SymDichotomy`/`DegenerateEven` and the Fall-II
witness/selection lemmas of `FallTwoStep`:

    symFallTwoEnergyStep (n) : SymFallTwoEnergyStep n

Given a **residual** state `α` (`NoEndCancel n α`) and a **Fall-II
configuration** (`FallTwoConfig α`):

    es[j-1].toWord = X ++ invRev A,  es[j].toWord = A ++ B  (|A| = |B|),
    es[j+1].toWord = invRev B ++ Z      (es = imageAggregate α m, j interior)

(the balanced factor `es[j]` being a basis image up to sign), the assembly
produces an elementary closure move `γ ∈ AutClosure n` with

    N (α * γ) = N α  ∧  eEnergySym (α * γ) < eEnergySym α,

where `eEnergySym` is the *symmetric* positional energy (`SymEnergy`).

The steps of the assembly:

1. **Excess bounds** (`A.length ≤ X.length`, `A.length ≤ Z.length`): a shorter
   excess would make the junction product `es[j-1]·es[j]` resp.
   `es[j]·es[j+1]` strictly shorter than one of its factors
   (`RowInvariant.excessLeftShortens` / `excessRightShortens`), which
   contradicts `NoEndCancel` (`ResidualBalanced.noEndCancel_no_*_strict`).
2. **Coordinate identification and distinctness**: each factor of the image
   aggregate is a basis image up to sign
   (`AggregateCoordinate.aggregate_factor_coordinate`); the neighbour
   coordinates differ from the balanced one `p` in all four sign combinations
   (`FallTwoStep.fallTwo_ne_left_plus`, `fallTwo_ne_left_mixed`,
   `fallTwo_ne_left_minus`, `AggregateCoordinate.witness_ne_left_plus`, and
   the right mirrors).
3. **Non-degeneracy**: the degenerate case `E A = E (invRev B) ∧
   E B = E (invRev A)` of the arithmetic dichotomy is impossible at a basis
   image (`DegenerateEven.degenerate_excluded`).
4. **The arithmetic dichotomy** `SymDichotomy.sym_energy_dichotomy` supplies
   one of the two classical cut-slide comparisons.
5. **Dispatch** over the two comparisons × the two or three orientation
   flags to one of the eight proved symmetric-energy steps
   (`SymStep.sym_energy_step_*`).

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## Closure membership of the four transvections -/

lemma rho_mem_closure' {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    rho i j hij ∈ AutClosure n :=
  Subgroup.subset_closure (rho_mem_AutGen n hij)

lemma lamNeg_mem_closure' {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    lamNeg i j hij ∈ AutClosure n := by
  have h : lam i j hij ∈ AutClosure n := lam_mem_closure hij
  have hinv : (lam i j hij)⁻¹ ∈ AutClosure n := (AutClosure n).inv_mem h
  rwa [lam_inv_eq] at hinv

/-! ## Excess bounds from residuality -/

/-- **Left excess bound.**  In a residual state, the left excess `X` of a
balanced factor cannot be shorter than the half `A`: otherwise
`excessLeftShortens` makes the junction product `es[j-1]·es[j]` strictly
shorter than `es[j]`, contradicting `NoEndCancel` at the two (distinct)
coordinates of the factors. -/
theorem left_excess_bound {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hnec : NoEndCancel n α)
    (es : List (FreeGroup (Fin n))) (himg : ImageAggregate α es) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hm : j - 1 < es.length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A) :
    A.length ≤ X.length := by
  by_contra h
  rw [not_le] at h
  have hstrict : FreeGroup.norm (es[j - 1] * es[j]) < FreeGroup.norm (es[j]) :=
    excessLeftShortens A B X (es[j]) hmid (es[j - 1]) hl h
  rcases aggregate_factor_coordinate α es himg hm with ⟨p, hp⟩
  rcases aggregate_factor_coordinate α es himg hj with ⟨q, hq⟩
  have hsub : (j - 1) + 1 = j := by omega
  have hjp : (j - 1) + 1 < es.length := by omega
  have hq' : es[(j - 1) + 1] = α (FreeGroup.of q) ∨
      es[(j - 1) + 1] = (α (FreeGroup.of q))⁻¹ := by
    simpa [hsub] using hq
  have hstrict' : FreeGroup.norm (es[j - 1] * es[(j - 1) + 1]) <
      FreeGroup.norm (es[(j - 1) + 1]) := by
    simpa [hsub] using hstrict
  have hpq : p ≠ q := strict_right_coord_ne α es hred (j := j - 1) hm hjp hp hq' hstrict'
  exact noEndCancel_no_right_strict α hnec hpq hp hq' hstrict'

/-- **Right excess bound.**  Mirror of `left_excess_bound`: the right excess
`Z` of a balanced factor cannot be shorter than the half `B`. -/
theorem right_excess_bound {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hnec : NoEndCancel n α)
    (es : List (FreeGroup (Fin n))) (himg : ImageAggregate α es) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hj1 : j + 1 < es.length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z) :
    A.length ≤ Z.length := by
  by_contra h
  rw [not_le] at h
  have hZB : Z.length < B.length := by rw [← hAB]; exact h
  have hstrict : FreeGroup.norm (es[j] * es[j + 1]) < FreeGroup.norm (es[j]) :=
    excessRightShortens A B Z (es[j]) hmid (es[j + 1]) hr hZB
  rcases aggregate_factor_coordinate α es himg hj with ⟨p, hp⟩
  rcases aggregate_factor_coordinate α es himg hj1 with ⟨q, hq⟩
  have hp' : es[(j + 1) - 1] = α (FreeGroup.of p) ∨
      es[(j + 1) - 1] = (α (FreeGroup.of p))⁻¹ := by
    simpa using hp
  have hstrict' : FreeGroup.norm (es[(j + 1) - 1] * es[j + 1]) <
      FreeGroup.norm (es[(j + 1) - 1]) := by
    simpa using hstrict
  have hpq : p ≠ q := strict_left_coord_ne α es hred (j := j + 1) hj1 (by omega) (by omega)
    hp' hq hstrict'
  exact noEndCancel_no_left_strict α hnec hpq hp' hq hstrict'

/-! ## The assembly -/

/-- **The residual symmetric-energy Fall-II step.**  In a residual state, every
Fall-II (balanced) configuration admits an elementary closure move that keeps
the total length `N` and strictly decreases the symmetric positional energy
`eEnergySym`. -/
theorem symFallTwoEnergyStep (n : ℕ) : SymFallTwoEnergyStep n := by
  intro α hres hF2
  classical
  rcases hF2 with ⟨m, j, hj, hj0, hj1, hconf, A, B, X, Z, hA, hAB, hX, hZ⟩
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have himg : ImageAggregate α es := by
    simpa [es] using imageAggregate_isImageAggregate α m
  have hred : SystemReduced es := by
    simpa [es] using SystemReduced_imageAggregate α m
  have hjE : j < es.length := by simpa [es] using hj
  have hj1E : j + 1 < es.length := by simpa [es] using hj1
  have hmE : j - 1 < es.length := by omega
  have hmid : (es[j]).toWord = A ++ B := by simpa [es] using hA
  have hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A := by simpa [es] using hX
  have hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z := by simpa [es] using hZ
  -- coordinates of the three factors
  rcases aggregate_factor_coordinate α es himg hjE with ⟨p, hp⟩
  rcases aggregate_factor_coordinate α es himg hmE with ⟨v, hv⟩
  rcases aggregate_factor_coordinate α es himg hj1E with ⟨u, hu⟩
  -- coordinate words
  have hppos : es[j] = α (FreeGroup.of p) → coordWord α p = A ++ B := fun hp' => by
    unfold coordWord
    rw [← hp']
    exact hmid
  have hpneg : es[j] = (α (FreeGroup.of p))⁻¹ →
      coordWord α p = FreeGroup.invRev B ++ FreeGroup.invRev A := fun hp' => by
    unfold coordWord
    have hrinv : (α (FreeGroup.of p)) = (es[j])⁻¹ := by rw [hp']; simp
    rw [hrinv, FreeGroup.toWord_inv, hmid, FreeGroup.invRev_append]
  have hvpos : es[j - 1] = α (FreeGroup.of v) →
      coordWord α v = X ++ FreeGroup.invRev A := fun hv' => by
    unfold coordWord
    rw [← hv']
    exact hl
  have hvneg : es[j - 1] = (α (FreeGroup.of v))⁻¹ →
      coordWord α v = A ++ FreeGroup.invRev X := fun hv' => by
    unfold coordWord
    have hrinv : (α (FreeGroup.of v)) = (es[j - 1])⁻¹ := by rw [hv']; simp
    rw [hrinv, FreeGroup.toWord_inv, hl, FreeGroup.invRev_append, FreeGroup.invRev_invRev]
  have hupos : es[j + 1] = α (FreeGroup.of u) →
      coordWord α u = FreeGroup.invRev B ++ Z := fun hu' => by
    unfold coordWord
    rw [← hu']
    exact hr
  have huneg : es[j + 1] = (α (FreeGroup.of u))⁻¹ →
      coordWord α u = FreeGroup.invRev Z ++ B := fun hu' => by
    unfold coordWord
    have hrinv : (α (FreeGroup.of u)) = (es[j + 1])⁻¹ := by rw [hu']; simp
    rw [hrinv, FreeGroup.toWord_inv, hr, FreeGroup.invRev_append, FreeGroup.invRev_invRev]
  -- distinctness of the witness coordinates
  have hvp : v ≠ p := by
    rcases hp with hp' | hp'
    · rcases hv with hv' | hv'
      · exact fallTwo_ne_left_plus α es hred hjE hmE A B X hAB hmid hl hp' hv'
      · exact fallTwo_ne_left_mixed α es hred hjE hj0 hmE hp' hv'
    · rcases hv with hv' | hv'
      · exact witness_ne_left_plus α es hred hjE hj0 hmE hp' hv'
      · exact fallTwo_ne_left_minus α es hred hjE hmE A B X hAB hmid hl hp' hv'
  have hup : u ≠ p := by
    rcases hp with hp' | hp'
    · rcases hu with hu' | hu'
      · exact fallTwo_ne_right_plus α es hred hjE hj1E A B Z hAB hmid hr hp' hu'
      · exact witness_ne_right_minus α es hred hjE hj1E hp' hu'
    · rcases hu with hu' | hu'
      · exact fallTwo_ne_right_mixed α es hred hjE hj1E hp' hu'
      · exact fallTwo_ne_right_minus α es hred hjE hj1E A B Z hAB hmid hr hp' hu'
  -- excess bounds
  have hXex : A.length ≤ X.length :=
    left_excess_bound α hres es himg hred hjE hj0 hmE A B X hAB hmid hl
  have hZex : A.length ≤ Z.length :=
    right_excess_bound α hres es himg hred hjE hj1E A B Z hAB hmid hr
  -- non-degeneracy of the pair of halves
  have hnd : ¬ (wordEnergy (ebase n) (lweight) A =
            wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) ∧
          wordEnergy (ebase n) (lweight) B =
            wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)) := by
    rintro ⟨h1, _⟩
    have hmk : FreeGroup.mk (A ++ B) = es[j] := by
      rw [← hmid]
      exact FreeGroup.mk_toWord (x := es[j])
    have hfac : FreeGroup.mk (A ++ B) = α (FreeGroup.of p) ∨
        FreeGroup.mk (A ++ B) = (α (FreeGroup.of p))⁻¹ := by
      rcases hp with hp' | hp'
      · exact Or.inl (by rw [hmk, hp'])
      · exact Or.inr (by rw [hmk, hp'])
    exact degenerate_excluded A B hAB h1 α hfac
  -- the arithmetic dichotomy
  have hd := sym_energy_dichotomy A B X Z hAB hXex hZex hnd
  rcases hd with hL | hR
  · -- left cut-slide
    rcases hp with hp' | hp'
    · rcases hv with hv' | hv'
      · exact ⟨rho v p hvp, rho_mem_closure' hvp,
          sym_energy_step_left_rho (α := α) (hres := hres) (hvp := hvp) (A := A) (B := B)
            (X := X) hAB (hppos hp') (hvpos hv') hL⟩
      · exact ⟨lamNeg v p hvp, lamNeg_mem_closure' hvp,
          sym_energy_step_left_lam (α := α) (hres := hres) (hvp := hvp) (A := A) (B := B)
            (X := X) hAB (hppos hp') (hvneg hv') hL⟩
    · rcases hv with hv' | hv'
      · exact ⟨rhoNeg v p hvp, rhoNeg_mem_closure hvp,
          sym_energy_step_left_rho_balminus (α := α) (hres := hres) (hvp := hvp) (A := A)
            (B := B) (X := X) hAB hL (hpneg hp') (hvpos hv')⟩
      · exact ⟨lam v p hvp, lam_mem_closure hvp,
          sym_energy_step_left_lam_balminus (α := α) (hres := hres) (hvp := hvp) (A := A)
            (B := B) (X := X) hAB hL (hpneg hp') (hvneg hv')⟩
  · -- right cut-slide
    rcases hp with hp' | hp'
    · rcases hu with hu' | hu'
      · exact ⟨lam u p hup, lam_mem_closure hup,
          sym_energy_step_right_lam (α := α) (hres := hres) (hup := hup) (A := A) (B := B)
            (Z := Z) hAB (hppos hp') (hupos hu') hR⟩
      · exact ⟨rhoNeg u p hup, rhoNeg_mem_closure hup,
          sym_energy_step_right_rho (α := α) (hres := hres) (hup := hup) (A := A) (B := B)
            (Z := Z) hAB hR (hppos hp') (huneg hu')⟩
    · rcases hu with hu' | hu'
      · exact ⟨lamNeg u p hup, lamNeg_mem_closure' hup,
          sym_energy_step_right_lam_balminus (α := α) (hres := hres) (hup := hup) (A := A)
            (B := B) (Z := Z) hAB hR (hpneg hp') (hupos hu')⟩
      · exact ⟨rho u p hup, rho_mem_closure' hup,
          sym_energy_step_right_rho_balminus (α := α) (hres := hres) (hup := hup) (A := A)
            (B := B) (Z := Z) hAB hR (hpneg hp') (huneg hu')⟩

end Submission.Nielsen
