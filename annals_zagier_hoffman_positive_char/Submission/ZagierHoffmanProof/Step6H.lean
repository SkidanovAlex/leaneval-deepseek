import Submission.ZagierHoffmanProof.TupleIndP
import Submission.ZagierHoffmanProof.TpTrans
import Submission.ZagierHoffmanProof.Step3HShared
import Submission.ZagierHoffmanProof.TmFShared
import Submission.ZagierHoffmanProof.ACMplDatum
import Submission.Commons.FieldTheory.RatFunc.num_mul_prod_erase_denom
import Submission.Commons.FieldTheory.RatFunc.num_mul_prod_erase_denom_ne_zero

/-!
# Dac's Theorem 6.2: the `𝒯'`-induction (`TupleIndP`) — helper layer

This module prepares the induction step of Dac's Theorem 6.2 for the family `𝒯'_w` of tuples with
`q ∤ s_i` (the Anderson–Thakur datum `Q_j = H_{s_j}`), in the tuple-indexed form `TupleIndP`.

Here we collect the `H`-datum analogues of `TheoremB.lean`'s §2 helpers:

* `tmTup_entries_H` — the tuple read off a prefix `t ∈ tmI S` reproduces `t` as `tupleListHP`;
* `tmTup_nd_H` — its entries are not divisible by `q`;
* `mkCfH`/`mkCfH_apply` — the `Γ`-scaled coefficient function `A_i·∏_{i'≠i} γ_{i'}` of the (LD)
  transport `TpTrans.lseries_relationP`;
* the coefficient-membership and Frobenius-invariance of `mkCfH`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

universe u

variable {F : Type u} [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The exponent tuple read off a prefix: the `H`-datum -/

section TmTupH

variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}

lemma tmTup_entries_H (hentry : ∀ s ∈ S, ∀ x ∈ s, x.2 = ambH F x.1)
    (hpos : ∀ s ∈ S, ∀ x ∈ s, 1 ≤ x.1) (t : ↥(tmI S)) :
    tupleListHP F (tmTup (S := S) hpos t).2 = t.1 := by
  rw [tupleListHP]
  conv_rhs => rw [← List.ofFn_get (t.1)]
  congr 1
  funext j
  have h2 : (ambH F (t.1.get j).1) = (t.1.get j).2 := by
    obtain ⟨s, hs, hx⟩ := mem_tmI_entry F t.2 (List.get_mem t.1 j)
    rw [hentry s hs _ hx]
  exact Prod.ext rfl h2

lemma tmTup_inj_H (hentry : ∀ s ∈ S, ∀ x ∈ s, x.2 = ambH F x.1)
    (hpos : ∀ s ∈ S, ∀ x ∈ s, 1 ≤ x.1) {t t' : ↥(tmI S)}
    (h : tupleListHP F (tmTup (S := S) hpos t).2
      = tupleListHP F (tmTup (S := S) hpos t').2) : t = t' := by
  refine Subtype.ext ?_
  rw [← tmTup_entries_H (F := F) (hentry := hentry) (hpos := hpos) (S := S) (t := t)]
  rw [← tmTup_entries_H (F := F) (hentry := hentry) (hpos := hpos) (S := S) (t := t')]
  exact h

/-! ## §1b. `suffixExp` reads a list FORWARD (up to `ambH`-replacement of the entries) -/

lemma suffixList_length (L : List (ℕ × Polynomial (Ambient F))) :
    (suffixList F L).length = L.length := by
  simp [suffixList, tmCoe]

lemma tmCoe_length (L : List (ℕ × Polynomial (Ambient F))) :
    (tmCoe (K := Ambient F) L).length = L.length := by
  simp [tmCoe]

/-- `List.ofFn` of the reversed-`get` of a reversed list is the list itself. -/
lemma ofFn_get_rev_aux {β : Type*} (l : List β) :
    List.ofFn (fun j : Fin l.reverse.length => l.reverse.get j.rev) = l := by
  have hlen : l.reverse.length = l.length := by simp
  conv_lhs => rw [List.ofFn_congr hlen]
  conv_rhs => rw [← List.ofFn_get l]
  congr 1
  funext i
  rw [List.get_reverse' l (Fin.cast hlen.symm i).rev (by
    rw [Fin.val_rev]; omega)]
  congr 1
  apply Fin.ext
  simp only [Fin.val_rev, Fin.val_cast]
  omega

/-- ★ **`suffixExp F L hL` reads `L` forward**: `tupleListHP` of the exponent tuple of the suffix
datum is `L` itself, provided the entries of `L` are the `ambH`-polynomials of their exponents. -/
lemma tupleListHP_suffixExp (L : List (ℕ × Polynomial (Ambient F)))
    (hL : ∀ x ∈ L, 1 ≤ x.1) (hE : ∀ x ∈ L, x.2 = ambH F x.1) :
    tupleListHP F (suffixExp F L hL) = L := by
  have hgen : ∀ (g : ℕ × PowerSeries (Ambient F) → ℕ × Polynomial (Ambient F)),
      List.ofFn (fun j : Fin ((tmCoe (K := Ambient F) L).reverse.length) =>
        g (((tmCoe (K := Ambient F) L).reverse).get j.rev))
      = (tmCoe (K := Ambient F) L).map g := by
    intro g
    have h1 : List.ofFn (fun j : Fin ((tmCoe (K := Ambient F) L).reverse.length) =>
          g (((tmCoe (K := Ambient F) L).reverse).get j.rev))
        = List.ofFn (g ∘ fun j : Fin ((tmCoe (K := Ambient F) L).reverse.length) =>
            ((tmCoe (K := Ambient F) L).reverse).get j.rev) := rfl
    rw [h1, ← List.map_ofFn]
    congr 1
    exact ofFn_get_rev_aux (tmCoe (K := Ambient F) L)
  have hstep : tupleListHP F (suffixExp F L hL)
      = List.ofFn (fun j : Fin ((tmCoe (K := Ambient F) L).reverse.length) =>
          (fun x : ℕ × PowerSeries (Ambient F) => (x.1, ambH F x.1))
            (((tmCoe (K := Ambient F) L).reverse).get j.rev)) := rfl
  have h2 : List.ofFn (fun j : Fin ((tmCoe (K := Ambient F) L).reverse.length) =>
        (fun x : ℕ × PowerSeries (Ambient F) => (x.1, ambH F x.1))
          (((tmCoe (K := Ambient F) L).reverse).get j.rev))
      = (tmCoe (K := Ambient F) L).map (fun x : ℕ × PowerSeries (Ambient F) => (x.1, ambH F x.1)) :=
    hgen (fun x : ℕ × PowerSeries (Ambient F) => (x.1, ambH F x.1))
  have h3 : (tmCoe (K := Ambient F) L).map
      (fun x : ℕ × PowerSeries (Ambient F) => (x.1, ambH F x.1)) = L := by
    rw [tmCoe, List.map_map]
    trans L.map id
    · exact List.map_congr_left (fun x hx => Prod.ext rfl (hE x hx).symm)
    · exact List.map_id L
  exact hstep.trans (h2.trans h3)

lemma tupleListHP_length {n : ℕ} (𝔰 : Fin n → ℕ+) : (tupleListHP F 𝔰).length = n :=
  List.length_ofFn

lemma tupleListHP_get {n : ℕ} (𝔰 : Fin n → ℕ+) (j : Fin (tupleListHP F 𝔰).length) :
    (tupleListHP F 𝔰).get j
      = (((𝔰 (Fin.cast (tupleListHP_length 𝔰) j)) : ℕ),
          (ambH F (𝔰 (Fin.cast (tupleListHP_length 𝔰) j)) : Polynomial (Ambient F))) := by
  rw [List.get_ofFn]

lemma tmTup_nd_H (hnd : ∀ s ∈ S, ∀ x ∈ s, ¬ Nat.card F ∣ x.1)
    (hpos : ∀ s ∈ S, ∀ x ∈ s, 1 ≤ x.1) (t : ↥(tmI S))
    (j : Fin (tmTup (S := S) hpos t).1) :
    ¬ Nat.card F ∣ ((tmTup (S := S) hpos t).2 j : ℕ) := by
  show ¬ Nat.card F ∣ (t.1.get j).1
  obtain ⟨s, hs, hx⟩ := mem_tmI_entry F t.2 (List.get_mem t.1 j)
  exact hnd s hs _ hx

end TmTupH

/-! ## §2. Coefficient-wise membership for products of `F_q[θ]`-valued polynomials -/

lemma coeff_prod_mem_ambA0 {ι : Type*} (s : Finset ι) {p : ι → Polynomial (Ambient F)}
    (hp : ∀ i ∈ s, ∀ m, (p i).coeff m ∈ ambA F 0) :
    ∀ n, ((∏ i ∈ s, p i).coeff n) ∈ ambA F 0 := by
  classical
  revert hp
  induction s using Finset.induction with
  | empty =>
      intro _ n
      rw [Finset.prod_empty, Polynomial.coeff_one]
      split_ifs
      · exact ambA_one_mem F 0
      · exact ambA_zero_mem 0
  | insert a s ha ih =>
      intro hp n
      rw [Finset.prod_insert ha]
      exact coeff_mul_mem_ambA0 (hp a (Finset.mem_insert_self a s))
        (ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))) n

lemma coeff_gammaPolyTup_mem_ambA0 {n : ℕ} (𝔰 : Fin n → ℕ+) :
    ∀ m, (gammaPolyTup F 𝔰).coeff m ∈ ambA F 0 := by
  rw [gammaPolyTup]
  exact coeff_prod_mem_ambA0 _ (fun j _ m => mem_ambA_zero_of_mem_ambF
    (ambGammaPoly_coeff_mem F (𝔰 j : ℕ) m))

/-! ## §3. The `Γ`-scaled coefficient function of the (LD) transport -/

/-- The coefficient function of the `𝒯'`-datum: on `tupleListHP 𝔰_i` it is
`A_i·∏_{i'≠i} γ_{𝔰_{i'}}` (the `Γ`-scaling produced by `TpTrans.lseries_relationP`). -/
noncomputable def mkCfH {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι)
    (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+)
    (A : ι → Polynomial (Ambient F)) :
    List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F) :=
  fun t => if h : ∃ i ∈ T, tupleListHP F ((𝔰 i).2) = t then
      A (Classical.choose h)
        * ∏ i' ∈ Finset.univ.erase (Classical.choose h), gammaPolyTup F ((𝔰 i').2)
    else 0

lemma mkCfH_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Finset ι}
    {𝔰 : ι → Σ r : ℕ, Fin r → ℕ+} {A : ι → Polynomial (Ambient F)}
    (hlinj : ∀ i j, tupleListHP F ((𝔰 i).2) = tupleListHP F ((𝔰 j).2) → i = j)
    {i : ι} (hi : i ∈ T) :
    mkCfH (F := F) T 𝔰 A (tupleListHP F ((𝔰 i).2))
      = A i * ∏ i' ∈ Finset.univ.erase i, gammaPolyTup F ((𝔰 i').2) := by
  have hex : ∃ j ∈ T, tupleListHP F ((𝔰 j).2) = tupleListHP F ((𝔰 i).2) := ⟨i, hi, rfl⟩
  have hch : A (Classical.choose hex) * ∏ i' ∈ Finset.univ.erase (Classical.choose hex),
        gammaPolyTup F ((𝔰 i').2)
      = A i * ∏ i' ∈ Finset.univ.erase i, gammaPolyTup F ((𝔰 i').2) := by
    obtain ⟨hj, heq⟩ := Classical.choose_spec hex
    rw [hlinj _ i heq]
  rw [mkCfH, dif_pos hex]
  exact hch

lemma mkCfH_coeff_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Finset ι}
    {𝔰 : ι → Σ r : ℕ, Fin r → ℕ+}
    {A : ι → Polynomial (Ambient F)} (hA : ∀ i m, (A i).coeff m ∈ ambA F 0)
    {t : List (ℕ × Polynomial (Ambient F))} (ht : t ∈ T.image (fun i => tupleListHP F ((𝔰 i).2)))
    (m : ℕ) : (mkCfH (F := F) T 𝔰 A t).coeff m ∈ ambA F 0 := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
  rw [mkCfH]
  by_cases hex : ∃ j ∈ T, tupleListHP F ((𝔰 j).2) = tupleListHP F ((𝔰 i).2)
  · rw [dif_pos hex]
    exact coeff_mul_mem_ambA0 (fun m => hA _ m)
      (coeff_prod_mem_ambA0 _ (fun j _ m => coeff_gammaPolyTup_mem_ambA0 ((𝔰 j).2) m)) m
  · rw [dif_neg hex, Polynomial.coeff_zero]
    exact ambA_zero_mem 0

lemma mkCfH_frob {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Finset ι}
    {𝔰 : ι → Σ r : ℕ, Fin r → ℕ+}
    {A : ι → Polynomial (Ambient F)} (hA : ∀ i, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((A i : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((A i : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    {t : List (ℕ × Polynomial (Ambient F))} (ht : t ∈ T.image (fun i => tupleListHP F ((𝔰 i).2))) :
    frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((mkCfH (F := F) T 𝔰 A t : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((mkCfH (F := F) T 𝔰 A t : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
  rw [mkCfH]
  by_cases hex : ∃ j ∈ T, tupleListHP F ((𝔰 j).2) = tupleListHP F ((𝔰 i).2)
  · rw [dif_pos hex, Polynomial.coe_mul, frobTwist_mul, hA (Classical.choose hex),
      coe_prod_poly, frobTwist_prod]
    congr 1
    exact Finset.prod_congr rfl (fun j _ => frobTwist_gammaPolyTup F ((𝔰 j).2))
  · rw [dif_neg hex, Polynomial.coe_zero]
    ext n
    simp

end ZagierHoffmanPositiveChar
