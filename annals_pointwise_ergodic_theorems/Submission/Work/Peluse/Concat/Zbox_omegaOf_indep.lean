import Mathlib
import Submission.Work.Peluse.Concat.TransferDefs
import Submission.Work.Peluse.BoxNorm.boxNormPow_perm
import Submission.Work.Peluse.Concat.omegaOfEnum

/-!
# `Zbox` is independent of the enumeration of the sign patterns

`Work.Peluse.Concat.Zbox c D N ωOf f d` is the level-`2^s - 1` box norm of `f` with the direction
family `i ↦ c·(d·ωOf i)[D]`, where `ωOf : Fin (2^s - 1) → (Fin s → Bool)` is an enumeration of the
nonzero sign patterns (injective, never `0`).  This module records that the value does not depend on
which enumeration is used.

The two enumerations enumerate the *same* set of patterns (there are exactly `2^s - 1` nonzero
patterns — `Work.Peluse.Concat.card_ne_zero_bool_fun`), so they differ by a permutation `σ` of the
slots: `ωOf (σ i) = ωOf' i`.  Hence the two direction families are equal up to the permutation `σ`,
and the box sum — hence its modulus, the box-norm power `boxNormPow` — is invariant under
permuting the slots (`Work.Peluse.Track.boxSumPow_comp_bij_proved`).

The requested statement is the case `s = 2`; the argument is written for arbitrary `s` since nothing
in it is special to `s = 2`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

/-- **Two enumerations of the nonzero sign patterns differ by a permutation of the slots.**  If
`ωOf, ωOf' : Fin (2^s - 1) → (Fin s → Bool)` are injective and never take the value `0`, there is a
bijection `σ` of `Fin (2^s - 1)` with `ωOf (σ i) = ωOf' i` for every `i`.

Both enumerations are bijections onto the subtype of nonzero patterns, because that subtype has
`2^s - 1 = Fintype.card (Fin (2^s - 1))` elements
(`Work.Peluse.Concat.card_ne_zero_bool_fun`); `σ` is then the composition of the inverse of the
first with the second. -/
lemma exists_perm_of_omegaOf {s : ℕ} (ωOf ωOf' : Fin (2 ^ s - 1) → (Fin s → Bool))
    (h : Function.Injective ωOf) (h' : Function.Injective ωOf')
    (hn : ∀ i : Fin (2 ^ s - 1), ωOf i ≠ 0) (hn' : ∀ i : Fin (2 ^ s - 1), ωOf' i ≠ 0) :
    ∃ σ : Fin (2 ^ s - 1) → Fin (2 ^ s - 1),
      Function.Bijective σ ∧ ∀ i, ωOf (σ i) = ωOf' i := by
  classical
  have hcardE : Fintype.card (Fin (2 ^ s - 1)) = Fintype.card {ω : Fin s → Bool // ω ≠ 0} := by
    rw [Fintype.card_fin, card_ne_zero_bool_fun s]
  let fOf : Fin (2 ^ s - 1) → {ω : Fin s → Bool // ω ≠ 0} := fun i => ⟨ωOf i, hn i⟩
  have hbij : Function.Bijective fOf :=
    (Fintype.bijective_iff_injective_and_card fOf).mpr
      ⟨fun i j hij => h (Subtype.ext_iff.mp hij), hcardE⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin (2 ^ s - 1) → Fin (2 ^ s - 1),
      ∀ i, fOf (σ i) = (⟨ωOf' i, hn' i⟩ : {ω : Fin s → Bool // ω ≠ 0}) :=
    ⟨fun i => (hbij.2 ⟨ωOf' i, hn' i⟩).choose, fun i => (hbij.2 ⟨ωOf' i, hn' i⟩).choose_spec⟩
  have hval : ∀ i, ωOf (σ i) = ωOf' i := fun i => congrArg Subtype.val (hσ i)
  have hinj : Function.Injective σ := by
    intro i j hij
    have h1 := hval i
    rw [hij] at h1
    exact h' (h1.symm.trans (hval j))
  exact ⟨σ, ⟨hinj, Finite.surjective_of_injective hinj⟩, hval⟩

/-- **`Zbox` is independent of the enumeration of the nonzero sign patterns.** -/
lemma Zbox_omegaOf_indep_gen {s : ℕ} {c : ℤ} {D N : ℕ} {f : ℤ → ℂ} (d : Fin s → ℤ)
    (ωOf ωOf' : Fin (2 ^ s - 1) → (Fin s → Bool))
    (h : Function.Injective ωOf) (h' : Function.Injective ωOf')
    (hn : ∀ i : Fin (2 ^ s - 1), ωOf i ≠ 0) (hn' : ∀ i : Fin (2 ^ s - 1), ωOf' i ≠ 0) :
    Zbox c D N ωOf f d = Zbox c D N ωOf' f d := by
  obtain ⟨σ, hσbij, hσ⟩ := exists_perm_of_omegaOf ωOf ωOf' h h' hn hn'
  -- the two direction families agree up to the permutation `σ`
  have hdir : dirFam c D ωOf' d = fun i => dirFam c D ωOf d (σ i) := by
    funext i
    show Work.Peluse.arithIcc (c * dotZ (ωOf' i) d) D
        = Work.Peluse.arithIcc (c * dotZ (ωOf (σ i)) d) D
    rw [hσ i]
  -- the box sum is invariant under permuting the slots
  have hperm := Work.Peluse.Track.boxSumPow_comp_bij_proved (dirFam c D ωOf d)
    (Work.Peluse.symIcc N) f σ hσbij
  have hstep : Work.Peluse.boxNormPow (2 ^ s - 1) (dirFam c D ωOf' d) (Work.Peluse.symIcc N) f
      = Work.Peluse.boxNormPow (2 ^ s - 1) (dirFam c D ωOf d) (Work.Peluse.symIcc N) f := by
    rw [hdir]
    simpa only [Work.Peluse.boxNormPow] using congrArg (fun z : ℂ => ‖z‖) hperm
  simpa only [Zbox] using hstep.symm

theorem Zbox_omegaOf_indep {c : ℤ} {D N : ℕ} {f : ℤ → ℂ} (d : Fin 2 → ℤ)
    (ωOf ωOf' : Fin (2 ^ 2 - 1) → (Fin 2 → Bool))
    (h : Function.Injective ωOf) (h' : Function.Injective ωOf')
    (hn : ∀ i : Fin (2 ^ 2 - 1), ωOf i ≠ 0) (hn' : ∀ i : Fin (2 ^ 2 - 1), ωOf' i ≠ 0) :
    Work.Peluse.Concat.Zbox c D N ωOf f d = Work.Peluse.Concat.Zbox c D N ωOf' f d :=
  Zbox_omegaOf_indep_gen d ωOf ωOf' h h' hn hn'

end

end Work.Peluse.Concat
