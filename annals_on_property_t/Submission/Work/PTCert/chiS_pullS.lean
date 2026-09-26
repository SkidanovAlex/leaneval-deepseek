import Mathlib
import Submission.Work.PTCert.EntryDefs
import Submission.Work.PTCert.codeFactsAux.pcFacts
import Submission.Work.PTCert.codeFactsAux.digitsRecon

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D

/-! ## The pullback of a sign character along a permutation code

`pullS pc S` is the bit mask of `{i : Fin 5 | pdig pc i ∈ maskSet S}`.  Writing `q = permOfPC pc`
(for a valid code `pc` we have `(q i).val = pdig pc i`, `codeFactsAux/pcFacts.permOfPC_digits`),
the `i`-th bit of `pullS pc S` is the bit of `S` at the digit `pdig pc i`, hence
`maskSet (pullS pc S) = (maskSet S).image q.symm`.  Since `chiS` is a product over a `Finset`,
reindexing by the injective map `q.symm` gives `χ_{pullS pc S}(u) = χ_S (u ∘ q⁻¹)`. -/

/-- A right fold of additions over `List.range n` is the `Finset.range n`-sum. -/
private lemma foldr_range_add (g : ℕ → ℕ) (n a : ℕ) :
    (List.range n).foldr (fun i acc => acc + g i) a = a + ∑ i ∈ Finset.range n, g i := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldr_append, Finset.sum_range_succ]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [ih (a + g n)]
    ring

/-- `pullS pc S` is the base-`2` number whose `i`-th bit is the bit of `S` at `pdig pc i`. -/
private lemma pullS_eq_sum (pc S : ℕ) :
    pullS pc S = ∑ i ∈ Finset.range 5, (if sbit S (pdig pc i) = 1 then 1 else 0) * 2 ^ i := by
  unfold pullS
  rw [foldr_range_add (fun i => bif Nat.beq ((S >>> pdig pc i) % 2) 1 then 2 ^ i else 0) 5 0]
  simp only [zero_add]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [cond_eq_ite]
  by_cases h : sbit S (pdig pc i) = 1
  · rw [if_pos (by rw [Nat.beq_eq]; exact h), if_pos h, one_mul]
  · rw [if_neg (by rw [Nat.beq_eq]; exact h), if_neg h, zero_mul]

/-- The `i`-th bit of `pullS pc S` is the bit of `S` at the digit `pdig pc i`. -/
private lemma sbit_pullS (pc S : ℕ) (i : Fin 5) :
    sbit (pullS pc S) i.val = sbit S (pdig pc i.val) := by
  show (pullS pc S >>> i.val) % 2 = sbit S (pdig pc i.val)
  rw [pullS_eq_sum, Nat.shiftRight_eq_div_pow]
  have hd : ∀ j < 5, (if sbit S (pdig pc j) = 1 then 1 else 0) < 2 := by
    intro j _; split_ifs <;> norm_num
  rw [Work.PTCert.digits.sum_mul_pow_div_mod (b := 2) (by norm_num)
        (fun j => if sbit S (pdig pc j) = 1 then 1 else 0) 5 i.val hd i.isLt]
  by_cases h : sbit S (pdig pc i.val) = 1
  · rw [if_pos h, h]
  · have h2 : sbit S (pdig pc i.val) < 2 := Nat.mod_lt _ (by norm_num)
    rw [if_neg h]
    omega

/-- `maskSet` of `pullS pc S` is the image of `maskSet S` under `(permOfPC pc).symm`. -/
private lemma maskSet_pullS (pc : ℕ) (hpc : validPC 5 pc = true) (S : ℕ) :
    maskSet (m := 5) (pullS pc S) = (maskSet (m := 5) S).image (permOfPC pc).symm := by
  ext i
  rw [Finset.mem_image]
  simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨permOfPC pc i, ?_, ?_⟩
    · rw [Work.PTCert.codeFactsAux.permOfPC_digits pc hpc i]
      rw [sbit_pullS pc S i] at h
      exact h
    · exact (permOfPC pc).symm_apply_apply i
  · rintro ⟨j, hj, hji⟩
    rw [← hji]
    rw [sbit_pullS pc S ((permOfPC pc).symm j)]
    rw [← Work.PTCert.codeFactsAux.permOfPC_digits pc hpc ((permOfPC pc).symm j),
      Equiv.apply_symm_apply]
    exact hj

/-- `chiS` is invariant under reindexing the character set by an injective map. -/
private lemma chiS_image {m : ℕ} (S : Finset (Fin m)) (f : Fin m → Fin m) (hf : Function.Injective f)
    (u : Fin m → ZMod 2) : chiS (S.image f) u = chiS S (fun i => u (f i)) := by
  rw [chiS, chiS]
  exact Finset.prod_image (fun x _ y _ hxy => hf hxy)

/-- `pullS pc S` (KernelCert) is the bit mask of `{i : pdig pc i ∈ S}`; for a valid code `pc`,
`pdig pc i = (permOfPC pc i).val` (`codeFactsAux/pcFacts.permOfPC_digits`), so the pullback character
is `χ_{pullS pc S}(u) = χ_S (u ∘ q⁻¹)` with `q = permOfPC pc`. -/
theorem chiS_pullS (pc : ℕ) (hpc : validPC 5 pc = true) (S : ℕ) (hS : S < 32) (u : Fin 5 → ZMod 2) :
    chiS (maskSet (m := 5) (pullS pc S)) u =
      chiS (maskSet (m := 5) S) (fun i => u ((permOfPC pc).symm i)) := by
  rw [maskSet_pullS pc hpc S]
  exact chiS_image (maskSet (m := 5) S) (permOfPC pc).symm (permOfPC pc).symm.injective u

end Work.PTCert
