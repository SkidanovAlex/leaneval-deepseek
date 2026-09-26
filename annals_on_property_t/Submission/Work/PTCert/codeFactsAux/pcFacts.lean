import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.digitArith
import Submission.Work.PTCert.codeFactsAux.digitsRecon
import Submission.Work.PTCert.letterAction

namespace Work.PTCert.codeFactsAux

open Submission.PTCert

/-! ## Base-`8` digit extraction for `pcOf`

`pcOf p` is the base-`8` number whose `i`-th digit is `p i`.  The bridge between the sum
`∑ i : Fin 5, (p i).val * 8^i` and a sum over `Finset.range 5` is the total function
`pdig5 p : ℕ → ℕ` (whose value outside `Fin 5` is irrelevant). -/

/-- The `j`-th base-`8` digit of the permutation `p`; `0` outside `Fin 5`. -/
def pdig5 (p : Equiv.Perm (Fin 5)) (j : ℕ) : ℕ := if h : j < 5 then (p ⟨j, h⟩).val else 0

lemma pdig5_lt (p : Equiv.Perm (Fin 5)) (j : ℕ) : pdig5 p j < 8 := by
  unfold pdig5
  split_ifs with h
  · exact lt_of_lt_of_le (p ⟨j, h⟩).isLt (by norm_num)
  · omega

lemma pdig5_self (p : Equiv.Perm (Fin 5)) (j : Fin 5) : pdig5 p j.val = (p j).val := by
  unfold pdig5
  rw [dif_pos j.isLt]

lemma pcOf_eq_sum (p : Equiv.Perm (Fin 5)) :
    pcOf p = ∑ j ∈ Finset.range 5, pdig5 p j * 8 ^ j := by
  rw [pcOf]
  rw [show (∑ i : Fin 5, (p i).val * 8 ^ i.val)
        = ∑ i : Fin 5, pdig5 p i.val * 8 ^ i.val from
    Finset.sum_congr rfl (fun i _ => by rw [pdig5_self p i])]
  exact Fin.sum_univ_eq_sum_range (fun j => pdig5 p j * 8 ^ j) 5

/-- The `i`-th base-`8` digit of `pcOf p` is `p i`. -/
lemma pdig_pcOf (p : Equiv.Perm (Fin 5)) (i : Fin 5) :
    pdig (pcOf p) i.val = (p i).val := by
  rw [pcOf_eq_sum p, pdig_eq_div,
    digits.sum_mul_pow_div_mod (b := 8) (d := pdig5 p) (n := 5) (i := i.val) (by norm_num)
      (fun j _ => pdig5_lt p j) i.isLt]
  exact pdig5_self p i

/-- `pcOf` is injective: it is the base-`8` expansion of the permutation. -/
lemma pcOf_injective : Function.Injective pcOf := by
  intro p q hpq
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [← pdig_pcOf p i, hpq, pdig_pcOf q i]

/-- `pcOf p` is a valid permutation code: its `5` digits are `< 5` and distinct, and it is
below `8 ^ 5`. -/
lemma validPC_pcOf (p : Equiv.Perm (Fin 5)) : validPC 5 (pcOf p) = true := by
  rw [validPC, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact List.all_eq_true.mpr (fun i hi => by
      rw [decide_eq_true_eq, pdig_pcOf p ⟨i, List.mem_range.mp hi⟩]
      exact (p ⟨i, List.mem_range.mp hi⟩).isLt)
  · exact List.all_eq_true.mpr (fun i hi => List.all_eq_true.mpr (fun j hj => by
      rw [Bool.or_eq_true]
      by_cases hij : i = j
      · exact Or.inl (beq_iff_eq.mpr hij)
      · refine Or.inr ?_
        rw [bne_iff_ne]
        intro hcon
        apply hij
        have hI : pdig (pcOf p) i = (p ⟨i, List.mem_range.mp hi⟩).val :=
          pdig_pcOf p ⟨i, List.mem_range.mp hi⟩
        have hJ : pdig (pcOf p) j = (p ⟨j, List.mem_range.mp hj⟩).val :=
          pdig_pcOf p ⟨j, List.mem_range.mp hj⟩
        have hfin : (⟨i, List.mem_range.mp hi⟩ : Fin 5) = ⟨j, List.mem_range.mp hj⟩ :=
          p.injective (Fin.ext (by rw [← hI, ← hJ]; exact hcon))
        simpa using congrArg Fin.val hfin))
  · rw [decide_eq_true_eq, pcOf_eq_sum p]
    exact digits.sum_mul_pow_lt_pow (by norm_num) (pdig5 p) 5 (fun j _ => pdig5_lt p j)

/-- An injective digit permutation realises its code: if the digits of `p` are the base-`8`
digits of `pc` then `pcOf p = pc` (digit reconstruction). -/
lemma pcOf_eq_of_digits (pc : ℕ) (p : Equiv.Perm (Fin 5))
    (hpiv : ∀ i : Fin 5, (p i).val = pdig pc i.val) (hpc : pc < 8 ^ 5) : pcOf p = pc := by
  rw [pcOf_eq_sum p]
  have hsum : (∑ j ∈ Finset.range 5, pdig5 p j * 8 ^ j)
      = ∑ j ∈ Finset.range 5, pc / 8 ^ j % 8 * 8 ^ j := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj5 : j < 5 := Finset.mem_range.mp hj
    have h1 : pdig5 p j = pc / 8 ^ j % 8 := by
      rw [pdig5, dif_pos hj5, hpiv ⟨j, hj5⟩, pdig_eq_div]
    rw [h1]
  rw [hsum]
  exact (selfDigits (by norm_num : 2 ≤ 8) pc 5 hpc).symm

/-- A valid code is below `8 ^ 5`. -/
lemma pc_lt_of_valid (pc : ℕ) (h : validPC 5 pc = true) : pc < 8 ^ 5 := by
  rw [validPC, Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

/-- The decoder `permOfPC` inverts `pcOf` on valid codes: it is the permutation whose digits
are those of `pc`. -/
lemma permOfPC_digits (pc : ℕ) (h : validPC 5 pc = true) (i : Fin 5) :
    (permOfPC pc i).val = pdig pc i.val := by
  classical
  have hlt : ∀ j, j < 5 → pdig pc j < 5 := validPC_pdig_lt 5 pc h
  have hinj : ∀ i j, i < 5 → j < 5 → pdig pc i = pdig pc j → i = j :=
    validPC_pdig_inj 5 pc h
  let f : Fin 5 → Fin 5 := fun i => ⟨pdig pc i.val, hlt i.val i.isLt⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    exact Fin.ext (hinj a.val b.val a.isLt b.isLt (congrArg Fin.val hab))
  let p : Equiv.Perm (Fin 5) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  have hpiv : ∀ i : Fin 5, (p i).val = pdig pc i.val := fun i => rfl
  have hpc_lt : pc < 8 ^ 5 := pc_lt_of_valid pc h
  have hpcOf : pcOf p = pc := pcOf_eq_of_digits pc p hpiv hpc_lt
  have hex : ∃ q : Equiv.Perm (Fin 5), pcOf q = pc := ⟨p, hpcOf⟩
  have hspec : pcOf (permOfPC pc) = pc := by
    rw [permOfPC, dif_pos hex]
    exact Classical.choose_spec hex
  have hperm : permOfPC pc = p := pcOf_injective (by rw [hspec, hpcOf])
  rw [hperm]
  exact hpiv i

/-- `permOfPC` is a right inverse of `pcOf` on valid codes: `pcOf (permOfPC pc) = pc`. -/
lemma permOfPC_spec (pc : ℕ) (h : validPC 5 pc = true) : pcOf (permOfPC pc) = pc :=
  pcOf_eq_of_digits pc (permOfPC pc) (fun i => permOfPC_digits pc h i) (pc_lt_of_valid pc h)

/-- `permOfPC` is a left inverse of `pcOf`. -/
lemma permOfPC_pcOf (p : Equiv.Perm (Fin 5)) : permOfPC (pcOf p) = p :=
  pcOf_injective (permOfPC_spec (pcOf p) (validPC_pcOf p))

/-- Facts about the base-8 permutation code `pcOf` and its decoder `permOfPC`.
`pcOf p = ∑ i : Fin 5, (p i).val * 8 ^ i.val`, `pdig pc i = pc >>> (3*i) % 8`,
`validPC r pc` = (all base-8 digits of `pc` below `r`) && (pairwise distinct digits) && `pc < 8^r`,
`permOfPC pc` = `Classical.choose` of `∃ p, pcOf p = pc` (and `1` if none).
Useful: `Work.PTCert.selfDigits` (n < b^k → n = ∑ i<k (n / b^i % b) * b^i) from digitsRecon,
`Work.PTCert.pdig_eq_div` (pdig pc i = pc / 8^i % 8), `Work.PTCert.digits.sum_mul_pow_div_mod`
(digit of a positional sum), `Work.PTCert.digits.sum_mul_pow_lt_pow`, and the helpers
`Work.PTCert.validPC_pdig_lt`, `Work.PTCert.validPC_pdig_inj` in letterAction.lean. -/
theorem pcFacts :
    (∀ (p : Equiv.Perm (Fin 5)) (i : Fin 5), Submission.PTCert.pdig (Submission.PTCert.pcOf p) i.val = (p i).val) ∧
    Function.Injective Submission.PTCert.pcOf ∧
    (∀ p : Equiv.Perm (Fin 5), Submission.PTCert.validPC 5 (Submission.PTCert.pcOf p) = true) ∧
    (∀ pc : ℕ, Submission.PTCert.validPC 5 pc = true →
      ∀ i : Fin 5, (Submission.PTCert.permOfPC pc i).val = Submission.PTCert.pdig pc i.val) :=
  ⟨pdig_pcOf, pcOf_injective, validPC_pcOf, permOfPC_digits⟩

end Work.PTCert.codeFactsAux
