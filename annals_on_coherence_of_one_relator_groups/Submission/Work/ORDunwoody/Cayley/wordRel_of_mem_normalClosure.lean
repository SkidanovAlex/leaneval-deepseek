/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The Cayley 2-complex of a finite presentation is simply connected

This file proves the central content of `Submission.Work.ORDunwoody.Cayley.Words`: if a word `w`
over the generators-with-sign of a finite presentation `P` of `G` represents an element of the
kernel of the quotient map `π : F_n → G` (equivalently, of the normal closure of the defining
relators), then `w` is `WordRel`-equivalent to the empty word.

## Strategy

The proof has two independent halves.

* *Free groups.*  Two words spell the same element of the free group exactly when they are related
  by deletion/insertion of adjacent inverse pairs, i.e. `FreeGroup.Red`; each `FreeGroup.Red.Step`
  is literally a `WordStep.red`, so `FreeGroup.mk u = FreeGroup.mk v` implies `WordRel P u v`.

* *The relators.*  Consider the set `S = {w | WordRel P w []}`.  It contains `[]`, is closed under
  concatenation, and is closed under conjugation by an arbitrary word (`wordRel_conjW`).  The set
  of `g : F_n` such that `g.toWord ∈ S` is therefore a subgroup of `F_n`
  (`goodSubgroup`); it is normal (`goodSubgroup_normal`, using `wordRel_conjW` again together with
  the fact established above that `WordRel` only depends on the free-group element), and it
  contains every defining relator (`WordRel.face_nil`).  Hence it contains the normal closure of
  the relators, and the result follows from `wordRel_of_mk_eq`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Cayley.Words

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Cayley

variable {G : Type u} [Group G]

/-! ## Free reduction is contained in `WordRel` -/

/-- The reversal-with-flip of a word.  This is `FreeGroup.invRev`: it spells the inverse free
group element of the word, and it is the word conjugated by which `WordRel` is stable. -/
def conjW {n : ℕ} (a : List (Fin n × Bool)) : List (Fin n × Bool) := (a.map swapLetter).reverse

theorem conjW_eq_invRev {P : FinPresentation G} (a : List (Fin P.n × Bool)) :
    conjW a = FreeGroup.invRev a := by
  simp [conjW, FreeGroup.invRev, swapLetter]

theorem conjW_cons {P : FinPresentation G} (x : Fin P.n × Bool) (a : List (Fin P.n × Bool)) :
    conjW (x :: a) = conjW a ++ [swapLetter x] := by
  simp [conjW, List.map_cons, List.reverse_cons]

/-- Every single free-reduction step is an elementary `WordStep.red`. -/
theorem wordRel_of_red_step {P : FinPresentation G} {L₁ L₂ : List (Fin P.n × Bool)}
    (h : FreeGroup.Red.Step L₁ L₂) : WordRel P L₁ L₂ := by
  cases h
  rename_i A B x b
  have key : WordStep P (A ++ (x, b) :: (x, !b) :: B) (A ++ B) := by
    have h1 : WordStep P ((x, b) :: swapLetter (x, b) :: B) B :=
      WordStep.red (P := P) [] B (x, b)
    have h2 := WordRel.step_append h1 A ([] : List (Fin P.n × Bool))
    simpa [swapLetter] using h2
  exact WordRel.step key

/-- `FreeGroup.Red` (reflexive-transitive closure of the reduction steps) is contained in
`WordRel`. -/
theorem wordRel_of_red {P : FinPresentation G} {L₁ L₂ : List (Fin P.n × Bool)}
    (h : FreeGroup.Red L₁ L₂) : WordRel P L₁ L₂ := by
  induction h with
  | refl => exact WordRel.refl _
  | tail hab hbc ih => exact ih.trans (wordRel_of_red_step hbc)

/-- **Words spelling the same element of the free group are `WordRel`.**  This is the free-group
word problem, transferred to `WordRel` through the reduction relation `FreeGroup.Red`. -/
theorem wordRel_of_mk_eq {P : FinPresentation G} {u v : List (Fin P.n × Bool)}
    (h : FreeGroup.mk u = FreeGroup.mk v) : WordRel P u v := by
  obtain ⟨L, h₁, h₂⟩ := FreeGroup.Red.exact.1 h
  exact (wordRel_of_red h₁).trans (wordRel_of_red h₂).symm

/-! ## The set `{w | WordRel P w []}` is closed under concatenation and conjugation -/

/-- `WordRel P · []` is closed under concatenation. -/
theorem wordRel_append_nil {P : FinPresentation G} {u v : List (Fin P.n × Bool)}
    (hu : WordRel P u []) (hv : WordRel P v []) : WordRel P (u ++ v) [] := by
  have := WordRel.append hu hv
  simpa using this

/-- Conjugation by a single generator-with-sign preserves `WordRel P · []`. -/
theorem wordRel_letter_conj {P : FinPresentation G} {u : List (Fin P.n × Bool)}
    (hu : WordRel P u []) (x : Fin P.n × Bool) :
    WordRel P (x :: (u ++ [swapLetter x])) [] := by
  have h₁ : WordRel P ([x] ++ (u ++ [swapLetter x])) ([x] ++ ([] ++ [swapLetter x])) :=
    WordRel.prepend_left (WordRel.append_right hu [swapLetter x]) [x]
  have h₂ : WordRel P ([x] ++ ([] ++ [swapLetter x])) [] := by
    have : ([x] ++ ([] ++ [swapLetter x]) : List (Fin P.n × Bool)) = [x, swapLetter x] := by simp
    rw [this]
    exact WordRel.step (WordStep.red (P := P) [] [] x)
  exact h₁.trans h₂

/-- Conjugation by an arbitrary word preserves `WordRel P · []`. -/
theorem wordRel_conjW {P : FinPresentation G} {u : List (Fin P.n × Bool)}
    (hu : WordRel P u []) (a : List (Fin P.n × Bool)) :
    WordRel P (a ++ u ++ conjW a) [] := by
  induction a with
  | nil => simpa [conjW] using hu
  | cons x a' ih =>
      have key : (x :: a') ++ u ++ conjW (x :: a')
          = x :: ((a' ++ u ++ conjW a') ++ [swapLetter x]) := by
        rw [conjW_cons]; simp [List.append_assoc]
      rw [key]
      exact wordRel_letter_conj ih x

/-! ## The subgroup of `F_n` generated by the relations -/

/-- A conjugate `a · z · a⁻¹` of the free-group element `z`, expressed through `FreeGroup.invRev`. -/
theorem mk_conjW {P : FinPresentation G} (a : List (Fin P.n × Bool)) (z : FreeGroup (Fin P.n)) :
    FreeGroup.mk (a ++ FreeGroup.toWord z ++ FreeGroup.invRev a)
      = FreeGroup.mk a * z * (FreeGroup.mk a)⁻¹ := by
  conv_lhs => rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
  rw [← FreeGroup.inv_mk, FreeGroup.mk_toWord]

/-- The subgroup of `F_n` consisting of the elements whose reduced word is `WordRel`-trivial. -/
def goodSubgroup (P : FinPresentation G) : Subgroup (FreeGroup (Fin P.n)) where
  carrier := {g | WordRel P (FreeGroup.toWord g) []}
  mul_mem' := by
    intro g h hg hh
    change WordRel P (FreeGroup.toWord (g * h)) []
    rw [FreeGroup.toWord_mul]
    have h1 : WordRel P (FreeGroup.toWord g ++ FreeGroup.toWord h)
        (FreeGroup.reduce (FreeGroup.toWord g ++ FreeGroup.toWord h)) :=
      wordRel_of_red FreeGroup.reduce.red
    have h2 : WordRel P (FreeGroup.toWord g ++ FreeGroup.toWord h) [] :=
      wordRel_append_nil hg hh
    exact h1.symm.trans h2
  one_mem' := by
    change WordRel P (FreeGroup.toWord 1) []
    rw [FreeGroup.toWord_one]
    exact WordRel.refl _
  inv_mem' := by
    intro g hg
    change WordRel P (FreeGroup.toWord g⁻¹) []
    rw [FreeGroup.toWord_inv, ← conjW_eq_invRev]
    have hclaim : WordRel P (conjW (FreeGroup.toWord g) ++ FreeGroup.toWord g) [] := by
      apply wordRel_of_mk_eq
      rw [← FreeGroup.mul_mk, conjW_eq_invRev, ← FreeGroup.inv_mk, FreeGroup.mk_toWord]
      simp [FreeGroup.one_eq_mk]
    have hcancel : WordRel P (conjW (FreeGroup.toWord g) ++ FreeGroup.toWord g)
        (conjW (FreeGroup.toWord g)) := by
      simpa using WordRel.prepend_left hg (conjW (FreeGroup.toWord g))
    exact hcancel.symm.trans hclaim

/-- `goodSubgroup P` is normal in `F_n`: it is closed under conjugation, by `wordRel_conjW`
together with `wordRel_of_mk_eq`. -/
theorem goodSubgroup_normal (P : FinPresentation G) : (goodSubgroup P).Normal where
  conj_mem := by
    intro n hn g
    change WordRel P (FreeGroup.toWord (g * n * g⁻¹)) []
    have hX : WordRel P (FreeGroup.toWord g ++ FreeGroup.toWord n
        ++ FreeGroup.invRev (FreeGroup.toWord g)) [] := wordRel_conjW hn (FreeGroup.toWord g)
    have hmk : FreeGroup.mk (FreeGroup.toWord g ++ FreeGroup.toWord n
        ++ FreeGroup.invRev (FreeGroup.toWord g))
        = FreeGroup.mk (FreeGroup.toWord (g * n * g⁻¹)) := by
      rw [mk_conjW, FreeGroup.mk_toWord]
      exact (FreeGroup.mk_toWord (x := g * n * g⁻¹)).symm
    exact (wordRel_of_mk_eq hmk).symm.trans hX

/-- Every defining relator lies in `goodSubgroup P`: it is the boundary of a `face` move. -/
theorem rel_subset_goodSubgroup (P : FinPresentation G) :
    (P.rel : Set (FreeGroup (Fin P.n))) ⊆ goodSubgroup P := by
  intro r hr
  exact WordRel.face_nil hr

/-- **The Cayley 2-complex of a finite presentation is simply connected at the level of words**:
a word representing an element of the kernel of `π` (the normal closure of the relators) is
`WordRel` to the empty word. -/
theorem wordRel_of_mem_normalClosure {G : Type u} [Group G] (P : FinPresentation G)
    {w : List (Fin P.n × Bool)}
    (h : FreeGroup.mk w ∈ Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin P.n)))) :
    WordRel P w [] := by
  haveI : (goodSubgroup P).Normal := goodSubgroup_normal P
  have hle : Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin P.n))) ≤ goodSubgroup P :=
    Subgroup.normalClosure_le_normal (rel_subset_goodSubgroup P)
  have hmem : WordRel P (FreeGroup.toWord (FreeGroup.mk w)) [] := hle h
  exact (wordRel_of_mk_eq (FreeGroup.mk_toWord (x := FreeGroup.mk w)).symm).trans hmem

end Work.ORDunwoody.Cayley
