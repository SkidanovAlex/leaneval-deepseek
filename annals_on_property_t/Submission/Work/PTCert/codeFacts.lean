import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.letterAction
import Submission.Work.PTCert.sigmaGroupFacts
import Submission.Work.PTCert.digitArith
import Submission.Work.PTCert.codeFactsAux.digitsRecon
import Submission.Work.PTCert.codeFactsAux.scFacts
import Submission.Work.PTCert.codeFactsAux.letterActionPerm
import Submission.Work.PTCert.codeFactsAux.actLBound
import Submission.Work.PTCert.codeFactsAux.pcFacts

namespace Work.PTCert

open Submission.PTCert

/-! ## Arithmetic of the packing `c = 32 * pc + sc` -/

lemma thirtytwo_div (a b : ℕ) (hb : b < 32) : (32 * a + b) / 32 = a := by
  rw [Nat.mul_add_div (by norm_num : 0 < 32), Nat.div_eq_of_lt hb, Nat.add_zero]

lemma thirtytwo_mod (a b : ℕ) (hb : b < 32) : (32 * a + b) % 32 = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

/-- The digit permutation of a valid code realises that code. -/
lemma exists_permOfPC (pc : ℕ) (h : validPC 5 pc = true) :
    ∃ p : Equiv.Perm (Fin 5), pcOf p = pc := by
  have hlt : ∀ i, i < 5 → pdig pc i < 5 := validPC_pdig_lt 5 pc h
  have hinj : ∀ i j, i < 5 → j < 5 → pdig pc i = pdig pc j → i = j := validPC_pdig_inj 5 pc h
  let f : Fin 5 → Fin 5 := fun i => ⟨pdig pc i.val, hlt i.val i.isLt⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    exact Fin.ext (hinj a.val b.val a.isLt b.isLt (congrArg Fin.val hab))
  let p : Equiv.Perm (Fin 5) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  have hpiv : ∀ i : Fin 5, (p i).val = pdig pc i.val := fun i => rfl
  have hpc_lt : pc < 8 ^ 5 := by
    rw [validPC, Bool.and_eq_true, Bool.and_eq_true] at h
    exact of_decide_eq_true h.2
  refine ⟨p, ?_⟩
  calc pcOf p = ∑ i : Fin 5, (p i).val * 8 ^ i.val := rfl
    _ = ∑ i : Fin 5, pdig pc i.val * 8 ^ i.val :=
        Finset.sum_congr rfl (fun i _ => by rw [hpiv i])
    _ = ∑ i ∈ Finset.range 5, (pc / 8 ^ i % 8) * 8 ^ i := by
        rw [Fin.sum_univ_eq_sum_range (fun i => pdig pc i * 8 ^ i) 5]
        exact Finset.sum_congr rfl (fun i _ => by rw [pdig_eq_div])
    _ = pc := (selfDigits (by norm_num : 2 ≤ 8) pc 5 hpc_lt).symm

/-- `permOfPC` inverts `pcOf` on valid codes. -/
lemma permOfPC_spec (pc : ℕ) (h : validPC 5 pc = true) : pcOf (permOfPC pc) = pc := by
  classical
  have hex := exists_permOfPC pc h
  rw [permOfPC, dif_pos hex]
  exact Classical.choose_spec hex

/-- `permOfPC` is a left inverse of `pcOf`. -/
lemma permOfPC_pcOf (p : Equiv.Perm (Fin 5)) : permOfPC (pcOf p) = p := by
  apply Work.PTCert.codeFactsAux.pcFacts.2.1
  rw [permOfPC_spec _ (Work.PTCert.codeFactsAux.pcFacts.2.2.1 p)]

/-! ## The main result -/

set_option linter.constructorNameAsVariable false in
theorem codeFacts : CodeFacts := by
  classical
  have hNB : NB1 5 = 81 := by norm_num [NB1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    have hpiv : ∀ i : Fin 5, (permOfPC (c / 32) i).val = pdig (c / 32) i.val :=
      Work.PTCert.codeFactsAux.pcFacts.2.2.2 (c / 32) hc
    have hact := Work.PTCert.codeFactsAux.letterActionPerm 5 (c / 32) (c % 32) (permOfPC (c / 32)) hc hpiv
    refine ⟨?_, ?_⟩
    · rw [SigmaFacts.mem_SigmaSet_iff]
      exact ⟨permOfPC (c / 32), scBits (c % 32), rfl⟩
    · intro k hk
      have hk' : k < NB1 5 := by rw [hNB]; exact hk
      have hlt := Work.PTCert.codeFactsAux.actLBound (c / 32) (c % 32) hc k hk
      exact ⟨hlt, hact k hk'⟩
  · intro σ hσ
    rw [SigmaFacts.mem_SigmaSet_iff] at hσ
    obtain ⟨p, s, rfl⟩ := hσ
    refine ⟨32 * pcOf p + scOf s, ?_, ?_⟩
    · rw [thirtytwo_div _ _ (Work.PTCert.codeFactsAux.scFacts.2.2 s)]
      exact Work.PTCert.codeFactsAux.pcFacts.2.2.1 p
    · rw [codeElt, thirtytwo_div _ _ (Work.PTCert.codeFactsAux.scFacts.2.2 s), thirtytwo_mod _ _ (Work.PTCert.codeFactsAux.scFacts.2.2 s),
        permOfPC_pcOf, Work.PTCert.codeFactsAux.scFacts.1 s]
  · intro p s
    refine ⟨Work.PTCert.codeFactsAux.pcFacts.2.2.1 p, Work.PTCert.codeFactsAux.scFacts.2.2 s, ?_⟩
    rw [codeElt, thirtytwo_div _ _ (Work.PTCert.codeFactsAux.scFacts.2.2 s), thirtytwo_mod _ _ (Work.PTCert.codeFactsAux.scFacts.2.2 s),
      permOfPC_pcOf, Work.PTCert.codeFactsAux.scFacts.1 s]
  · intro sc hsc
    exact Work.PTCert.codeFactsAux.scFacts.2.1 sc hsc
  · intro pc h i
    exact Work.PTCert.codeFactsAux.pcFacts.2.2.2 pc h i

end Work.PTCert
