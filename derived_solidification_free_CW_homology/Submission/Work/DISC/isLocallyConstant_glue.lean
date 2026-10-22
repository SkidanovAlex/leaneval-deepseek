import Mathlib
import Submission.Work.DISC.Defs

/-!
# AREA DISC — the "glue" of a null sequence is locally constant

Let `S` be a light profinite set, `M` an abelian group and `a : ℕ → LocallyConstant S M` a *null
sequence* (some `N` with `a n = 0` for all `n ≥ N`).  Then the function

`S × (ℕ ∪ {∞}) ⟶ M,  (s, n) ↦ a n s,  (s, ∞) ↦ 0`

is locally constant.

This is the topological heart of the "null sequence" model of the sections of `ΔM^P`
(`P = ℤ[ℕ ∪ {∞}]/ℤ[∞]`): the glued function is precisely the element of `ΔM(S × (ℕ∪{∞}))`
whose shift-difference is the sequence `a`, so that `ΔM(S × (ℕ∪{∞})) ≅ ΔM(S) ⊕` (null
sequences).  Note that the eventual-vanishing hypothesis is essential: at the point `∞` the
needed neighbourhood is the complement of the finite set `{n < N}`, which is only a
neighbourhood of `∞` because no term of the sequence beyond `N` contributes.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.DISC

open Set

variable {M : Type*} [Zero M]

/-- The complement of `{↑n : n < N}` is open in `OnePoint ℕ`: it is the complement of a finite
(hence compact and closed) set, and it is the standard neighbourhood of `∞` used to glue a sequence
that vanishes for `n ≥ N`. -/
lemma isOpen_compl_coe_range_lt (N : ℕ) :
    IsOpen (((↑) '' {n : ℕ | n < N})ᶜ : Set (OnePoint ℕ)) := by
  rw [OnePoint.isOpen_compl_image_coe]
  exact ⟨(Set.finite_Iio N).isClosed, (Set.finite_Iio N).isCompact⟩

/-- A singleton of `OnePoint ℕ` given by a natural number is open. -/
lemma isOpen_singleton_coe (n : ℕ) : IsOpen ({↑n} : Set (OnePoint ℕ)) := by
  rw [← Set.image_singleton]
  exact OnePoint.isOpen_image_coe.2 (isOpen_discrete ({n} : Set ℕ))

/-- A point of `((↑) '' {n : ℕ | n < N})ᶜ` is either `∞` or `↑n` with `N ≤ n`. -/
lemma eq_infty_or_ge_of_mem_compl_coe_range_lt {N : ℕ} {o : OnePoint ℕ}
    (ho : o ∈ ((↑) '' {n : ℕ | n < N})ᶜ) : o = ∞ ∨ ∃ n, N ≤ n ∧ o = ↑n := by
  induction o using OnePoint.rec with
  | infty => exact Or.inl rfl
  | coe n =>
    refine Or.inr ⟨n, ?_, rfl⟩
    by_contra h
    exact ho ⟨n, by simpa using not_le.mp h, rfl⟩

/-- **The glue of a null sequence is locally constant** (general form, for any topological space
`S` and any type `M` with a zero). -/
theorem isLocallyConstant_glue_of_eventually_zero {X : Type*} [TopologicalSpace X]
    (a : ℕ → LocallyConstant X M) (N : ℕ) (hN : ∀ n ≥ N, a n = 0) :
    IsLocallyConstant
      (fun p : X × OnePoint ℕ => OnePoint.elim p.2 (0 : M) (fun n => a n p.1)) := by
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨s, o⟩
  cases o with
  | infty =>
    -- near `∞` the function is constantly `0`: the complement of the finite set `{n < N}`
    -- is a neighbourhood of `∞` on which all the remaining terms vanish.
    refine ⟨(Set.univ : Set X) ×ˢ (((↑) '' {n : ℕ | n < N})ᶜ : Set (OnePoint ℕ)),
      isOpen_univ.prod (isOpen_compl_coe_range_lt N), ⟨trivial, ?_⟩, ?_⟩
    · exact OnePoint.infty_notMem_image_coe
    · rintro ⟨s', o'⟩ ⟨-, ho'⟩
      rcases eq_infty_or_ge_of_mem_compl_coe_range_lt ho' with rfl | ⟨m, hm, rfl⟩
      · rfl
      · simp [hN m hm]
  | coe n =>
    -- at `(s, ↑n)` with `n < N` we may use a neighbourhood on which the locally constant
    -- function `a n` is constant, times the open point `{↑n}`.
    refine ⟨{s' : X | a n s' = a n s} ×ˢ ({↑n} : Set (OnePoint ℕ)),
      ((a n).isLocallyConstant.isOpen_fiber (a n s)).prod (isOpen_singleton_coe n),
      ⟨rfl, rfl⟩, ?_⟩
    rintro ⟨s', o'⟩ ⟨hs', ho'⟩
    obtain rfl : o' = ↑n := by simpa using ho'
    simpa using hs'

theorem isLocallyConstant_glue (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ)
    (a : ℕ → LocallyConstant ↥S ↥M) (N : ℕ) (hN : ∀ n ≥ N, a n = 0) :
    IsLocallyConstant
      (fun p : ↥S × OnePoint ℕ => OnePoint.elim p.2 (0 : ↥M) (fun n => a n p.1)) := by
  exact isLocallyConstant_glue_of_eventually_zero a N hN

end Work.DISC
