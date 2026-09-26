import Submission.Work.Item3.SymDichotomy
import Submission.Commons.Data.Nat.ofDigits_injective_on_length
import Submission.Commons.GroupTheory.FreeGroup.abHom_mk_append_even
import Submission.Commons.GroupTheory.FreeGroup.aut_image_not_even

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# DegenerateEven: the degenerate half-pair of `FallTwoConfig` gives even exponent sums

The symmetric-energy dichotomy (`SymDichotomy.sym_energy_dichotomy`) fails
exactly in the *degenerate* case
`E A = E (invRev B) ∧ E B = E (invRev A)`, equivalently (digit injectivity)
`rankseq B = rev (rankseq A)`.  This module proves the *word-level* half of the
exclusion of that case: in the degenerate case every coordinate of the
abelianisation of `mk (A ++ B)` is **even** (each letter of `B` pairs with a
letter of `A` of the same generator, and `±1 + ±1` is even), which contradicts
the primitivity of the basis image `mk (A ++ B) = ± α (a_p)`.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- The energy of an inverse-reversed word is the digit encoding of the ranks of
the original word. -/
lemma invRev_reverse {n : ℕ} (B : List (Fin n × Bool)) :
    (FreeGroup.invRev B).reverse = B.map (fun l => (l.1, !l.2)) := by
  simp [FreeGroup.invRev]

lemma wordEnergy_invRev_eq_ofDigits {n : ℕ} (B : List (Fin n × Bool)) :
    wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
      = Nat.ofDigits (ebase n) (B.map lweight) := by
  rw [wordEnergy_eq_ofDigits, invRev_reverse, List.map_map]
  exact congrArg (Nat.ofDigits (ebase n))
    (congrArg (List.map · B) (funext (fun l => rfl)))

/-- Two words with the same rank sequence have the same generator sequence. -/
lemma map_fst_of_map_lweight {n : ℕ} {L L' : List (Fin n × Bool)}
    (h : L.map lweight = L'.map lweight) : L.map Prod.fst = L'.map Prod.fst := by
  have h1 : (L.map Prod.fst).map (fun i : Fin n => i.val + 1)
      = (L'.map Prod.fst).map (fun i : Fin n => i.val + 1) := by
    rw [List.map_map, List.map_map]
    exact h
  exact List.map_injective_iff.mpr (fun a b hab => Fin.ext (by simpa using hab)) h1

/-- **Degenerate case ⟹ even exponent sums.**  If `E A = E (invRev B)` with
`|A| = |B|`, then every coordinate of the abelianisation of `mk (A ++ B)` is
even. -/
theorem degenerate_even {n : ℕ} (A B : List (Fin n × Bool)) (hAB : A.length = B.length)
    (h : wordEnergy (ebase n) (lweight) A
            = wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)) (u : Fin n) :
    (2 : ℤ) ∣ (Commons.GroupTheory.FreeGroup.abHom n
      (FreeGroup.mk (A ++ B))).toAdd u := by
  rw [wordEnergy_eq_ofDigits, wordEnergy_invRev_eq_ofDigits] at h
  have hbnd1 : ∀ x ∈ A.reverse.map lweight, x < ebase n := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨l, _, rfl⟩
    exact lweight_lt_ebase l
  have hbnd2 : ∀ x ∈ B.map lweight, x < ebase n := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨l, _, rfl⟩
    exact lweight_lt_ebase l
  have hlen : (A.reverse.map lweight).length = (B.map lweight).length := by
    simp [hAB]
  have heq : A.reverse.map lweight = B.map lweight :=
    Commons.Data.Nat.ofDigits_injective_on_length (by unfold ebase; omega)
      hlen hbnd1 hbnd2 h
  have hrev : A.map lweight = (B.reverse).map lweight := by
    have hc := congrArg List.reverse heq
    simpa [List.reverse_reverse, List.map_reverse] using hc
  have hgen : A.map Prod.fst = (B.reverse).map Prod.fst :=
    map_fst_of_map_lweight hrev
  exact Commons.GroupTheory.FreeGroup.abHom_mk_append_even n A B hgen.symm u

/-- `abHom` of an inverse is the inverse of the abelianisation. -/
lemma abHom_inv_toAdd {n : ℕ} (x : FreeGroup (Fin n)) (u : Fin n) :
    (Commons.GroupTheory.FreeGroup.abHom n x⁻¹).toAdd u
      = -(Commons.GroupTheory.FreeGroup.abHom n x).toAdd u := by
  have h : Commons.GroupTheory.FreeGroup.abHom n x⁻¹
      = (Commons.GroupTheory.FreeGroup.abHom n x)⁻¹ :=
    (Commons.GroupTheory.FreeGroup.abHom n).map_inv x
  rw [h]
  simp

/-- **The degenerate case of the symmetric-energy dichotomy is impossible at a
basis image.**  If `mk (A ++ B)` is `± α (a_p)`, `|A| = |B|` and
`E A = E (invRev B)`, then every coordinate exponent sum of `mk (A ++ B)` is
even (`degenerate_even`), contradicting the primitivity of the basis image
`± α (a_p)` (`aut_image_not_even`). -/
theorem degenerate_excluded {n : ℕ} (A B : List (Fin n × Bool)) (hAB : A.length = B.length)
    (h : wordEnergy (ebase n) (lweight) A
            = wordEnergy (ebase n) (lweight) (FreeGroup.invRev B))
    {p : Fin n} (α : MulAut (FreeGroup (Fin n)))
    (hfac : FreeGroup.mk (A ++ B) = α (FreeGroup.of p) ∨
      FreeGroup.mk (A ++ B) = (α (FreeGroup.of p))⁻¹) :
    False := by
  obtain ⟨u, hu⟩ := Commons.GroupTheory.FreeGroup.aut_image_not_even n α p
  have h1 := degenerate_even A B hAB h u
  apply hu
  rcases hfac with hfac | hfac
  · rwa [hfac] at h1
  · have h2 : (Commons.GroupTheory.FreeGroup.abHom n (FreeGroup.mk (A ++ B))).toAdd u
        = -(Commons.GroupTheory.FreeGroup.abHom n (α (FreeGroup.of p))).toAdd u := by
      rw [hfac]
      exact abHom_inv_toAdd (α (FreeGroup.of p)) u
    rw [h2] at h1
    exact Int.dvd_neg.mp h1

end Submission.Nielsen
