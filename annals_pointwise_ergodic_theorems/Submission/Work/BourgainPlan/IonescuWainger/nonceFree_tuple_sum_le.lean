import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.SuperOrthoDefs
import Submission.Work.BourgainPlan.IonescuWainger.factorial_mul_powersetCard_sum_le
import Submission.Work.BourgainPlan.IonescuWainger.card_filter_image_eq_le
import Submission.Work.BourgainPlan.IonescuWainger.card_image_le_half_of_nonceFree
import Submission.Work.BourgainPlan.IonescuWainger.prod_le_image_sq_mul_sqrt_pow
import Submission.Work.BourgainPlan.IonescuWainger.sum_pow_div_factorial_le_exp

/-!
# Summing over nonce-free tuples

Tao (arXiv:2008.05066, §2, proof of `sys-ortho`(i)) expands `‖∑_{s∈S} f_s‖^{2r}` and discards
every `2r`-tuple of indices carrying a *nonce* (a value occurring exactly once); the tuples that
survive are the *nonce-free* ones.  This file bounds the total weight of the surviving tuples:

`∑_{q nonce-free} ∏_{k<r} a (q k).1 · a (q k).2 ≤ e · r^{2r} · (∑ a²)^r`.

The proof decomposes the sum over the image `B` of the tuple: every fibre of a nonce-free tuple has
at least two elements, so `2|B| ≤ 2r` and the `(2r - 2|B|)` "extra" entries contribute at most a
power of `√(∑a²)`, while the number of tuples with a given image `B` is at most `|B|^{2r}`.  Summing
over `B` of cardinality `b` and using the elementary-symmetric bound `b! · e_b(a²) ≤ (∑a²)^b`
produces the factor `∑_{b≤r} b^{2r}/b! ≤ e·r^{2r}`.
-/

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

open Finset
open scoped BigOperators

/-- A tuple of indices `s : κ → ι` is **nonce-free** when every value it takes is taken by at least
two of its entries, i.e. no value is a nonce.  For `κ = Fin r ⊕ Fin r` this is `NonceFreeTuple`
(see `nonceFreeTuple_iff`). -/
def NonceFreeSeq {κ ι : Type*} (s : κ → ι) : Prop := ∀ j : κ, ∃ k : κ, k ≠ j ∧ s k = s j

instance {κ ι : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι] :
    DecidablePred (NonceFreeSeq : (κ → ι) → Prop) :=
  fun s => by unfold NonceFreeSeq; infer_instance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The core estimate.**  For a finite index type `κ` with `2r` elements, the total weight
`∏_j a (s j)` of the nonce-free tuples `s : κ → ι` is at most `e · r^{2r} · (∑ a²)^r`. -/
theorem nonceFree_sum_le_aux {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r : ℕ) (hr : 1 ≤ r) (hκ : Fintype.card κ = 2 * r) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ s ∈ (Finset.univ : Finset (κ → ι)).filter (NonceFreeSeq : (κ → ι) → Prop), ∏ j, a (s j)
      ≤ Real.exp 1 * (r : ℝ) ^ (2 * r) * (∑ i, a i ^ 2) ^ r := by
  let S : ℝ := ∑ i, a i ^ 2
  let M : ℝ := Real.sqrt S
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (a i))
  have hMnn : 0 ≤ M := Real.sqrt_nonneg _
  have hMsq : M ^ 2 = S := Real.sq_sqrt hSnn
  have hMpow : ∀ b : ℕ, b ≤ r → M ^ (2 * (r - b)) = S ^ (r - b) := by
    intro b _
    rw [pow_mul, hMsq]
  have ha2nn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (a i) ^ 2 := fun i _ => sq_nonneg (a i)
  set T : Finset (κ → ι) := (Finset.univ : Finset (κ → ι)).filter (NonceFreeSeq : (κ → ι) → Prop)
    with hT
  set pw : Finset (Finset ι) := (Finset.univ : Finset ι).powerset with hpw
  -- ### Step 1: bound the contribution of the tuples with a fixed image `B`
  have hinner : ∀ B ∈ pw,
      (∑ s ∈ T.filter (fun s => Finset.univ.image s = B), ∏ j, a (s j))
        ≤ (B.card : ℝ) ^ (2 * r) * ((∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card))) := by
    intro B _
    have hHnn : 0 ≤ (∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card)) :=
      mul_nonneg (Finset.prod_nonneg (fun i _ => sq_nonneg (a i))) (pow_nonneg hMnn _)
    have hpt : ∀ s ∈ T.filter (fun s => Finset.univ.image s = B),
        ∏ j, a (s j) ≤ (∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card)) := by
      intro s hs
      rw [Finset.mem_filter] at hs
      obtain ⟨hsT, hsim⟩ := hs
      have hnf : NonceFreeSeq s := by
        rw [hT] at hsT
        exact (Finset.mem_filter.mp hsT).2
      have hle := prod_le_image_sq_mul_sqrt_pow r hκ a ha s hnf
      rw [hsim] at hle
      rwa [show Real.sqrt (∑ i, a i ^ 2) = M from rfl] at hle
    calc (∑ s ∈ T.filter (fun s => Finset.univ.image s = B), ∏ j, a (s j))
        ≤ ∑ _s ∈ T.filter (fun s => Finset.univ.image s = B),
            ((∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card))) := Finset.sum_le_sum hpt
      _ = ((T.filter (fun s => Finset.univ.image s = B)).card : ℝ) *
            ((∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (B.card : ℝ) ^ (2 * r) * ((∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card))) := by
          apply mul_le_mul_of_nonneg_right _ hHnn
          have hcard : (T.filter (fun s => Finset.univ.image s = B)).card
              ≤ B.card ^ Fintype.card κ := by
            refine le_trans (Finset.card_le_card ?_) (card_filter_image_eq_le B)
            refine Finset.filter_subset_filter _ ?_
            rw [hT]
            exact Finset.filter_subset _ _
          calc ((T.filter (fun s => Finset.univ.image s = B)).card : ℝ)
              ≤ ((B.card ^ Fintype.card κ : ℕ) : ℝ) := by exact_mod_cast hcard
            _ = (B.card : ℝ) ^ (2 * r) := by rw [Nat.cast_pow, hκ]
  -- ### Step 2: images of cardinality `> r` contribute nothing
  have hzero : ∀ B ∈ pw, B ∉ pw.filter (fun B => B.card ≤ r) →
      (∑ s ∈ T.filter (fun s => Finset.univ.image s = B), ∏ j, a (s j)) = 0 := by
    intro B hB hBnot
    rw [Finset.mem_filter] at hBnot
    have hgt : r < B.card := by
      by_contra hcon
      exact hBnot ⟨hB, not_lt.mp hcon⟩
    refine Finset.sum_eq_zero (fun s hs => by
      exfalso
      rw [Finset.mem_filter] at hs
      obtain ⟨hsT, hsim⟩ := hs
      have hnf : NonceFreeSeq s := by
        rw [hT] at hsT
        exact (Finset.mem_filter.mp hsT).2
      have hc := card_image_le_half_of_nonceFree s hnf
      rw [hsim, hκ] at hc
      omega)
  have hsum_eq : (∑ B ∈ pw, ∑ s ∈ T.filter (fun s => Finset.univ.image s = B), ∏ j, a (s j))
      = ∑ B ∈ pw.filter (fun B => B.card ≤ r),
          ∑ s ∈ T.filter (fun s => Finset.univ.image s = B), ∏ j, a (s j) :=
    (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
  have hstep : (∑ B ∈ pw.filter (fun B => B.card ≤ r),
        ∑ s ∈ T.filter (fun s => Finset.univ.image s = B), ∏ j, a (s j))
      ≤ ∑ B ∈ pw.filter (fun B => B.card ≤ r),
        ((B.card : ℝ) ^ (2 * r) * ((∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card)))) :=
    Finset.sum_le_sum (fun B hB => hinner B (Finset.mem_of_mem_filter B hB))
  -- ### Step 3: group the subsets by cardinality
  have hmaps2 : ∀ B ∈ pw.filter (fun B => B.card ≤ r), B.card ∈ Finset.range (r + 1) := by
    intro B hB
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.mem_filter.mp hB).2
  have hfib2 : (∑ b ∈ Finset.range (r + 1),
        ∑ B ∈ (pw.filter (fun B => B.card ≤ r)).filter (fun B => B.card = b),
          ((B.card : ℝ) ^ (2 * r) * ((∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card)))))
      = ∑ B ∈ pw.filter (fun B => B.card ≤ r),
          ((B.card : ℝ) ^ (2 * r) * ((∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card)))) :=
    Finset.sum_fiberwise_of_maps_to (s := pw.filter (fun B => B.card ≤ r))
      (t := Finset.range (r + 1)) (g := fun B => B.card) hmaps2 _
  have hb_bound : ∀ b ∈ Finset.range (r + 1),
      (∑ B ∈ (pw.filter (fun B => B.card ≤ r)).filter (fun B => B.card = b),
          ((B.card : ℝ) ^ (2 * r) * ((∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card)))))
        ≤ (b : ℝ) ^ (2 * r) * M ^ (2 * (r - b)) *
            (∑ B ∈ (Finset.univ : Finset ι).powersetCard b, ∏ i ∈ B, (a i) ^ 2) := by
    intro b hb
    have hble : b ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hc_nn : 0 ≤ (b : ℝ) ^ (2 * r) * M ^ (2 * (r - b)) :=
      mul_nonneg (pow_nonneg (Nat.cast_nonneg b) _) (pow_nonneg hMnn _)
    calc (∑ B ∈ (pw.filter (fun B => B.card ≤ r)).filter (fun B => B.card = b),
            ((B.card : ℝ) ^ (2 * r) * ((∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card)))))
        = ∑ B ∈ (pw.filter (fun B => B.card ≤ r)).filter (fun B => B.card = b),
            ((b : ℝ) ^ (2 * r) * M ^ (2 * (r - b)) * (∏ i ∈ B, (a i) ^ 2)) := by
          refine Finset.sum_congr rfl (fun B hB => ?_)
          have hc : B.card = b := (Finset.mem_filter.mp hB).2
          rw [hc]
          ring
      _ ≤ ∑ B ∈ (Finset.univ : Finset ι).powersetCard b,
            ((b : ℝ) ^ (2 * r) * M ^ (2 * (r - b)) * (∏ i ∈ B, (a i) ^ 2)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro B hB
            rw [Finset.mem_powersetCard]
            exact ⟨Finset.mem_powerset.mp
              (Finset.mem_of_mem_filter B (Finset.mem_of_mem_filter B hB)),
              (Finset.mem_filter.mp hB).2⟩
          · intro B _ _
            exact mul_nonneg hc_nn (Finset.prod_nonneg (fun i _ => sq_nonneg (a i)))
      _ = (b : ℝ) ^ (2 * r) * M ^ (2 * (r - b)) *
            (∑ B ∈ (Finset.univ : Finset ι).powersetCard b, ∏ i ∈ B, (a i) ^ 2) := by
          rw [Finset.mul_sum]
  -- ### Step 4: the powerset sums are controlled by `(∑ a²)^b / b!`
  have hG : ∀ b ∈ Finset.range (r + 1),
      (∑ B ∈ (Finset.univ : Finset ι).powersetCard b, ∏ i ∈ B, (a i) ^ 2)
        ≤ S ^ b / (b.factorial : ℝ) := by
    intro b _
    have hbpos : (0 : ℝ) < (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos b
    have hfac := factorial_mul_powersetCard_sum_le (Finset.univ : Finset ι) (fun i => (a i) ^ 2)
      ha2nn b
    have hSsum : (∑ i ∈ (Finset.univ : Finset ι), (a i) ^ 2) = S := rfl
    rw [hSsum] at hfac
    rw [le_div_iff₀ hbpos]
    calc (∑ B ∈ (Finset.univ : Finset ι).powersetCard b, ∏ i ∈ B, (a i) ^ 2)
            * (b.factorial : ℝ)
        = (b.factorial : ℝ)
            * (∑ B ∈ (Finset.univ : Finset ι).powersetCard b, ∏ i ∈ B, (a i) ^ 2) := by ring
      _ ≤ S ^ b := hfac
  have hb_sum : (∑ b ∈ Finset.range (r + 1), (b : ℝ) ^ (2 * r) * M ^ (2 * (r - b)) *
        (∑ B ∈ (Finset.univ : Finset ι).powersetCard b, ∏ i ∈ B, (a i) ^ 2))
      ≤ ∑ b ∈ Finset.range (r + 1), (b : ℝ) ^ (2 * r) * M ^ (2 * (r - b)) *
        (S ^ b / (b.factorial : ℝ)) := by
    refine Finset.sum_le_sum (fun b hb => ?_)
    refine mul_le_mul_of_nonneg_left (hG b hb) ?_
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg b) _) (pow_nonneg hMnn _)
  -- ### Step 5: simplify the summands and sum the exponential series
  have hterm : ∀ b ∈ Finset.range (r + 1),
      (b : ℝ) ^ (2 * r) * M ^ (2 * (r - b)) * (S ^ b / (b.factorial : ℝ))
        = (b : ℝ) ^ (2 * r) * (S ^ r / (b.factorial : ℝ)) := by
    intro b hb
    have hble : b ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have h1 : M ^ (2 * (r - b)) * S ^ b = S ^ r := by
      rw [hMpow b hble, ← pow_add, Nat.sub_add_cancel hble]
    calc (b : ℝ) ^ (2 * r) * M ^ (2 * (r - b)) * (S ^ b / (b.factorial : ℝ))
        = (b : ℝ) ^ (2 * r) * (M ^ (2 * (r - b)) * S ^ b) / (b.factorial : ℝ) := by ring
      _ = (b : ℝ) ^ (2 * r) * S ^ r / (b.factorial : ℝ) := by rw [h1]
      _ = (b : ℝ) ^ (2 * r) * (S ^ r / (b.factorial : ℝ)) := by ring
  have hfinal : (∑ b ∈ Finset.range (r + 1),
        (b : ℝ) ^ (2 * r) * (S ^ r / (b.factorial : ℝ)))
      = S ^ r * ∑ b ∈ Finset.range (r + 1), (b : ℝ) ^ (2 * r) / (b.factorial : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  -- ### Step 6: assemble
  have hfiber : (∑ B ∈ pw, ∑ s ∈ T.filter (fun s => Finset.univ.image s = B), ∏ j, a (s j))
      = ∑ s ∈ T, ∏ j, a (s j) := by
    refine Finset.sum_fiberwise_of_maps_to (s := T) (t := pw)
      (g := fun s : κ → ι => Finset.univ.image s) ?_ _
    intro s _
    rw [hpw, Finset.mem_powerset]
    exact Finset.subset_univ _
  calc (∑ s ∈ T, ∏ j, a (s j))
      = ∑ B ∈ pw, ∑ s ∈ T.filter (fun s => Finset.univ.image s = B), ∏ j, a (s j) :=
        hfiber.symm
    _ = ∑ B ∈ pw.filter (fun B => B.card ≤ r),
          ∑ s ∈ T.filter (fun s => Finset.univ.image s = B), ∏ j, a (s j) := hsum_eq
    _ ≤ ∑ B ∈ pw.filter (fun B => B.card ≤ r),
          ((B.card : ℝ) ^ (2 * r) * ((∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card)))) := hstep
    _ = ∑ b ∈ Finset.range (r + 1),
          ∑ B ∈ (pw.filter (fun B => B.card ≤ r)).filter (fun B => B.card = b),
            ((B.card : ℝ) ^ (2 * r) * ((∏ i ∈ B, (a i) ^ 2) * M ^ (2 * (r - B.card)))) :=
        hfib2.symm
    _ ≤ ∑ b ∈ Finset.range (r + 1), (b : ℝ) ^ (2 * r) * M ^ (2 * (r - b)) *
          (∑ B ∈ (Finset.univ : Finset ι).powersetCard b, ∏ i ∈ B, (a i) ^ 2) :=
        Finset.sum_le_sum hb_bound
    _ ≤ ∑ b ∈ Finset.range (r + 1), (b : ℝ) ^ (2 * r) * M ^ (2 * (r - b)) *
          (S ^ b / (b.factorial : ℝ)) := hb_sum
    _ = ∑ b ∈ Finset.range (r + 1), (b : ℝ) ^ (2 * r) * (S ^ r / (b.factorial : ℝ)) :=
        Finset.sum_congr rfl hterm
    _ = S ^ r * ∑ b ∈ Finset.range (r + 1), (b : ℝ) ^ (2 * r) / (b.factorial : ℝ) := hfinal
    _ ≤ S ^ r * (Real.exp 1 * (r : ℝ) ^ (2 * r)) :=
        mul_le_mul_of_nonneg_left (sum_pow_div_factorial_le_exp r hr) (pow_nonneg hSnn r)
    _ = Real.exp 1 * (r : ℝ) ^ (2 * r) * (∑ i, a i ^ 2) ^ r := by
        rw [show S = ∑ i, a i ^ 2 from rfl]
        ring

/-- **The nonce-free tuple sum.**  The total weight of the nonce-free tuples `q : Fin r → ι × ι`,
with respect to the weights `a ≥ 0`, is at most `e · r^{2r} · (∑ a²)^r`. -/
theorem nonceFree_tuple_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (hr : 1 ≤ r) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ q ∈ (Finset.univ : Finset (Fin r → ι × ι)).filter (NonceFreeTuple r),
        ∏ k : Fin r, a (q k).1 * a (q k).2
      ≤ Real.exp 1 * (r : ℝ) ^ (2 * r) * (∑ i, a i ^ 2) ^ r := by
  have hcard : Fintype.card (Fin r ⊕ Fin r) = 2 * r := by
    simp [Fintype.card_sum, two_mul]
  let e : (Fin r → ι × ι) ≃ (Fin r ⊕ Fin r → ι) :=
    (Equiv.arrowProdEquivProdArrow (Fin r) (fun _ => ι) (fun _ => ι)).trans
      (Equiv.sumArrowEquivProdArrow (Fin r) (Fin r) ι).symm
  have he : ∀ (q : Fin r → ι × ι) (j : Fin r ⊕ Fin r), e q j = tupleOf q j := by
    intro q j
    cases j with
    | inl k => rfl
    | inr k => rfl
  have hsum : (∑ q ∈ (Finset.univ : Finset (Fin r → ι × ι)).filter (NonceFreeTuple r),
        ∏ k : Fin r, a (q k).1 * a (q k).2)
      = ∑ s ∈ (Finset.univ : Finset (Fin r ⊕ Fin r → ι)).filter (NonceFreeSeq : (Fin r ⊕ Fin r → ι) → Prop),
          ∏ j, a (s j) := by
    refine Finset.sum_equiv e ?_ ?_
    · intro q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [nonceFreeTuple_iff]
      constructor
      · intro h j
        obtain ⟨k, hk, hjk⟩ := h j
        exact ⟨k, hk, by rw [he, he]; exact hjk⟩
      · intro h j
        obtain ⟨k, hk, hjk⟩ := h j
        exact ⟨k, hk, by simpa [he] using hjk⟩
    · intro q _
      rw [Fintype.prod_sum_type, Finset.prod_mul_distrib]
      simp only [he, tupleOf_inl, tupleOf_inr]
  rw [hsum]
  exact nonceFree_sum_le_aux r hr hcard a ha

end Work.BourgainPlan.IonescuWainger
