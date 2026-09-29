import Mathlib
import Submission.Work.ConvR.basic
import Submission.Work.DFT.phaseLin
import Submission.Work.SynFFT.yMulFacts
import Submission.Work.SynFFT.yMulLinear
import Submission.Work.ConvR.negaMulLin
import Submission.Work.ConvR.yMulNegMulAlt
import Submission.Work.ConvR.yCharSumConv

/-!
# The synthetic DFT diagonalises the convolution over `R = ℂ[y]/(y^r+1)`

This file proves `Work.ConvR.convIdentity`:

`convR r ts u v = M · G*((1/r)·(G u)·(G v))`,  `M = ∏ tᵢ`,

i.e. the normalised convolution `(1/(M r))·u∗v` over the group `∏ ℤ/tᵢ` with coefficients in
`R = ℂ[y]/(y^r+1)` is diagonalised by the synthetic DFT `HvdH.synDFT` (paper §2.3–2.4, and the
relation used in the proof of Proposition 3.4).

The proof is the ring-theoretic analogue of `Work.DFT.algebra.convolution` (the complex case):
expand both sides, move the powers of `y` through the products with
`Work.ConvR.yMulNegMul`, and collapse the `k`-sum with the synthetic character orthogonality
`Work.ConvR.yCharSumConv`.  The bilinearity of `HvdH.negaMul` (the product of `R`) is
`Work.ConvR.negaMulLin`, and the exponent bookkeeping uses `HvdH.synExp`'s symmetry
(`synExp_swap` below) together with `Work.DFT.subIdx_lt` and `Work.DFT.charSumConv_cond_iff_subIdx`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.ConvR

open HvdH

/-- `Σᵢ (2r/tᵢ)·jᵢ·kᵢ` is symmetric in the two digit lists. -/
private theorem synExp_swap (r : ℕ) (ts js ks : List ℕ) :
    HvdH.synExp r ts js ks = HvdH.synExp r ts ks js := by
  induction ts generalizing js ks with
  | nil => rfl
  | cons t ts ih =>
    cases js with
    | nil =>
      cases ks with
      | nil => rfl
      | cons k ks => rfl
    | cons j js =>
      cases ks with
      | nil => rfl
      | cons k ks =>
        simp only [HvdH.synExp]
        rw [ih js ks]
        congr 1
        ring_nf

/-- The body of `convIdentity`, with the three algebraic inputs (bilinearity of `negaMul`,
compatibility of `yMul` with the product, and the synthetic character orthogonality) as
hypotheses. -/
theorem convIdentity_core
    (hcomm : ∀ (r : ℕ) (a b : Fin r → ℂ), HvdH.negaMul r a b = HvdH.negaMul r b a)
    (hsl : ∀ (r : ℕ) (c : ℂ) (a b : Fin r → ℂ),
      HvdH.negaMul r (c • a) b = c • HvdH.negaMul r a b)
    (hsr : ∀ (r : ℕ) (c : ℂ) (a b : Fin r → ℂ),
      HvdH.negaMul r a (c • b) = c • HvdH.negaMul r a b)
    (hsuml : ∀ (r : ℕ) {ι : Type} (s : Finset ι) (f : ι → Fin r → ℂ) (b : Fin r → ℂ),
      HvdH.negaMul r (∑ i ∈ s, f i) b = ∑ i ∈ s, HvdH.negaMul r (f i) b)
    (hsumr : ∀ (r : ℕ) {ι : Type} (s : Finset ι) (a : Fin r → ℂ) (g : ι → Fin r → ℂ),
      HvdH.negaMul r a (∑ i ∈ s, g i) = ∑ i ∈ s, HvdH.negaMul r a (g i))
    (hy : ∀ (r : ℕ) (hr : 0 < r) (e : ℤ) (a b : Fin r → ℂ),
      HvdH.yMul r e (HvdH.negaMul r a b) = HvdH.negaMul r (HvdH.yMul r e a) b)
    (hc : ∀ (r : ℕ) (ts : List ℕ) (hr : HvdH.IsPow2 r) (hpos : ∀ t ∈ ts, 0 < t)
      (ht : ∀ t ∈ ts, t ∣ 2 * r) (j a b : Fin ts.prod) (W : Fin r → ℂ),
      (∑ k : Fin ts.prod, HvdH.yMul r (HvdH.synExp r ts (HvdH.digits ts j) (HvdH.digits ts k) -
          HvdH.synExp r ts (HvdH.digits ts a) (HvdH.digits ts k) -
          HvdH.synExp r ts (HvdH.digits ts b) (HvdH.digits ts k)) W) =
        if b = HvdH.subIdx ts j a then (ts.prod : ℂ) • W else 0)
    {r : ℕ} {ts : List ℕ} (hr : HvdH.IsPow2 r) (ht : ∀ t ∈ ts, t ∣ 2 * r) :
    ∀ u v : Fin ts.prod → Fin r → ℂ,
      HvdH.convR r ts u v = fun j c => (ts.prod : ℂ) *
        HvdH.synDFT r ts 1 (fun k c' => ((r : ℂ))⁻¹ *
          HvdH.negaMul r (HvdH.synDFT r ts (-1) u k) (HvdH.synDFT r ts (-1) v k) c') j c := by
  intro u v
  funext j
  -- ### basic hypotheses
  have hIsPow2 : HvdH.IsPow2 r := hr
  rcases hIsPow2 with ⟨k0, hk0, hrk⟩
  have hrpos : 0 < r := by rw [hrk]; positivity
  have hpos : ∀ t ∈ ts, 0 < t := by
    intro t hmem
    obtain ⟨m, hm⟩ := ht t hmem
    rcases Nat.eq_zero_or_pos t with h0 | hgt
    · exfalso; rw [h0, zero_mul] at hm; omega
    · exact hgt
  have hMpos : 0 < ts.prod := List.prod_pos hpos
  have hMnz : ((ts.prod : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hMpos)
  -- ### abbreviations
  let V : Fin ts.prod → Fin r → ℂ :=
    fun k => v ⟨HvdH.subIdx ts j k, Work.DFT.subIdx_lt ts hpos j k⟩
  let G1 : Fin ts.prod → Fin r → ℂ := fun k => HvdH.synDFT r ts (-1) u k
  let G2 : Fin ts.prod → Fin r → ℂ := fun k => HvdH.synDFT r ts (-1) v k
  let E : Fin ts.prod → Fin ts.prod → ℤ :=
    fun x y => HvdH.synExp r ts (HvdH.digits ts x) (HvdH.digits ts y)
  let Wv : Fin ts.prod → Fin r → ℂ := fun k => HvdH.synDFT r ts 1
    (fun k' c' => ((r : ℂ))⁻¹ * HvdH.negaMul r (G1 k') (G2 k') c') k
  show HvdH.convR r ts u v j = (ts.prod : ℂ) • Wv j
  -- ### helper lemmas from the `yMul` action
  have hcomp : ∀ (e e' : ℤ) (x : Fin r → ℂ),
      HvdH.yMul r (e + e') x = HvdH.yMul r e (HvdH.yMul r e' x) :=
    fun e e' x => (Work.SynFFT.yMulFacts r hrpos).1 e e' x
  have hymul_smul : ∀ (e : ℤ) (c : ℂ) (x : Fin r → ℂ),
      HvdH.yMul r e (c • x) = c • HvdH.yMul r e x :=
    fun e c x => (Work.SynFFT.yMulFacts r hrpos).2.2.2.1 e c x
  have hymul_sum : ∀ (e : ℤ) {ι : Type} (s : Finset ι) (f : ι → Fin r → ℂ),
      HvdH.yMul r e (∑ i ∈ s, f i) = ∑ i ∈ s, HvdH.yMul r e (f i) :=
    fun e _ s f => (Work.SynFFT.yMulLinear (ι := _) r).2 e s f
  -- symmetric pull-out of `y^e` from the second factor
  have hsym : ∀ (e : ℤ) (x y : Fin r → ℂ),
      HvdH.yMul r e (HvdH.negaMul r x y) = HvdH.negaMul r x (HvdH.yMul r e y) := by
    intro e x y
    calc HvdH.yMul r e (HvdH.negaMul r x y)
        = HvdH.yMul r e (HvdH.negaMul r y x) := by rw [hcomm r x y]
      _ = HvdH.negaMul r (HvdH.yMul r e y) x := hy r hrpos e y x
      _ = HvdH.negaMul r x (HvdH.yMul r e y) := hcomm r (HvdH.yMul r e y) x
  -- ### unfolding of the two sides
  have hV : ∀ k : Fin ts.prod,
      (fun c' => if h : HvdH.subIdx ts j k < ts.prod then
        v ⟨HvdH.subIdx ts j k, h⟩ c' else 0) = V k := by
    intro k; funext c'
    simp only [V]
    rw [dite_eq_left (Work.DFT.subIdx_lt ts hpos j k)]
  have hL : HvdH.convR r ts u v j
      = (1 / (((ts.prod * r : ℕ)) : ℂ)) •
          (∑ k : Fin ts.prod, HvdH.negaMul r (u k) (V k)) := by
    funext c
    simp only [HvdH.convR, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [hV k]
  have hGu : ∀ k : Fin ts.prod, G1 k
      = (1 / ((ts.prod : ℕ) : ℂ)) •
          (∑ a : Fin ts.prod, HvdH.yMul r (-(E k a)) (u a)) := by
    intro k
    funext c
    simp only [G1, HvdH.synDFT, E, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, neg_one_mul]
  have hGv : ∀ k : Fin ts.prod, G2 k
      = (1 / ((ts.prod : ℕ) : ℂ)) •
          (∑ b : Fin ts.prod, HvdH.yMul r (-(E k b)) (v b)) := by
    intro k
    funext c
    simp only [G2, HvdH.synDFT, E, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, neg_one_mul]
  have hWf : Wv j = (1 / ((ts.prod : ℕ) : ℂ)) •
      (∑ k : Fin ts.prod,
        HvdH.yMul r (E j k) (fun c' => ((r : ℂ))⁻¹ *
          HvdH.negaMul r (G1 k) (G2 k) c')) := by
    funext c
    simp only [Wv, HvdH.synDFT, E, G1, G2, one_mul, Pi.smul_apply, Finset.sum_apply,
      smul_eq_mul]
  have hWs : (∑ k : Fin ts.prod,
        HvdH.yMul r (E j k) (fun c' => ((r : ℂ))⁻¹ *
          HvdH.negaMul r (G1 k) (G2 k) c'))
      = (∑ k : Fin ts.prod,
        HvdH.yMul r (E j k) (((r : ℂ))⁻¹ • HvdH.negaMul r (G1 k) (G2 k))) :=
    Finset.sum_congr rfl fun k _ => rfl
  have hW : (ts.prod : ℂ) • Wv j
      = ∑ k : Fin ts.prod,
          HvdH.yMul r (E j k) (((r : ℂ))⁻¹ • HvdH.negaMul r (G1 k) (G2 k)) := by
    rw [hWf, hWs, smul_smul, mul_one_div, div_self hMnz, one_smul]
  -- ### the product expansion and the character sum
  have hbis : ∀ (k a b : Fin ts.prod),
      HvdH.yMul r (E j k)
          (HvdH.negaMul r (HvdH.yMul r (-(E k a)) (u a)) (HvdH.yMul r (-(E k b)) (v b)))
        = HvdH.yMul r (E j k - E k a - E k b) (HvdH.negaMul r (u a) (v b)) := by
    intro k a b
    rw [hsym (E j k) (HvdH.yMul r (-(E k a)) (u a)) (HvdH.yMul r (-(E k b)) (v b)),
      ← hcomp (E j k) (-(E k b)) (v b)]
    rw [← hsym (E j k + -(E k b)) (HvdH.yMul r (-(E k a)) (u a)) (v b)]
    rw [← hy r hrpos (-(E k a)) (u a) (v b)]
    rw [← hcomp (E j k + -(E k b)) (-(E k a)) (HvdH.negaMul r (u a) (v b))]
    congr 1
    ring
  have hprod : ∀ k : Fin ts.prod,
      HvdH.yMul r (E j k) (((r : ℂ))⁻¹ • HvdH.negaMul r (G1 k) (G2 k))
        = (((r : ℂ))⁻¹ * ((1 / ((ts.prod : ℕ) : ℂ)) * (1 / ((ts.prod : ℕ) : ℂ)))) •
            (∑ a : Fin ts.prod, ∑ b : Fin ts.prod,
              HvdH.yMul r (E j k - E k a - E k b) (HvdH.negaMul r (u a) (v b))) := by
    intro k
    rw [hymul_smul, hGu k, hGv k]
    rw [hsl r (1 / ((ts.prod : ℕ) : ℂ))
      (∑ a : Fin ts.prod, HvdH.yMul r (-(E k a)) (u a))
      ((1 / ((ts.prod : ℕ) : ℂ)) • ∑ b : Fin ts.prod, HvdH.yMul r (-(E k b)) (v b))]
    rw [hsr r (1 / ((ts.prod : ℕ) : ℂ))
      (∑ a : Fin ts.prod, HvdH.yMul r (-(E k a)) (u a))
      (∑ b : Fin ts.prod, HvdH.yMul r (-(E k b)) (v b))]
    rw [hymul_smul, hymul_smul, smul_smul, smul_smul]
    rw [hsuml r Finset.univ (fun a => HvdH.yMul r (-(E k a)) (u a))
      (∑ b : Fin ts.prod, HvdH.yMul r (-(E k b)) (v b))]
    rw [Finset.sum_congr rfl (fun a _ => hsumr r Finset.univ (HvdH.yMul r (-(E k a)) (u a))
      (fun b => HvdH.yMul r (-(E k b)) (v b)))]
    rw [hymul_sum (E j k) Finset.univ (fun a => ∑ b : Fin ts.prod,
      HvdH.negaMul r (HvdH.yMul r (-(E k a)) (u a)) (HvdH.yMul r (-(E k b)) (v b)))]
    rw [Finset.sum_congr rfl (fun a _ => hymul_sum (E j k) Finset.univ (fun b =>
      HvdH.negaMul r (HvdH.yMul r (-(E k a)) (u a)) (HvdH.yMul r (-(E k b)) (v b))))]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hbis k a b))]
    rw [show ((r : ℂ))⁻¹ * (1 / ((ts.prod : ℕ) : ℂ)) * (1 / ((ts.prod : ℕ) : ℂ))
        = ((r : ℂ))⁻¹ * ((1 / ((ts.prod : ℕ) : ℂ)) * (1 / ((ts.prod : ℕ) : ℂ))) from by
      ring]
  have hreorder :
      (∑ k : Fin ts.prod, (((r : ℂ))⁻¹ *
            ((1 / ((ts.prod : ℕ) : ℂ)) * (1 / ((ts.prod : ℕ) : ℂ)))) •
          (∑ a : Fin ts.prod, ∑ b : Fin ts.prod,
            HvdH.yMul r (E j k - E k a - E k b) (HvdH.negaMul r (u a) (v b))))
        = (((r : ℂ))⁻¹ * ((1 / ((ts.prod : ℕ) : ℂ)) * (1 / ((ts.prod : ℕ) : ℂ)))) •
          (∑ a : Fin ts.prod, ∑ b : Fin ts.prod, ∑ k : Fin ts.prod,
            HvdH.yMul r (E j k - E k a - E k b) (HvdH.negaMul r (u a) (v b))) := by
    have hsum : (∑ k : Fin ts.prod, ∑ a : Fin ts.prod, ∑ b : Fin ts.prod,
          HvdH.yMul r (E j k - E k a - E k b) (HvdH.negaMul r (u a) (v b)))
        = (∑ a : Fin ts.prod, ∑ b : Fin ts.prod, ∑ k : Fin ts.prod,
          HvdH.yMul r (E j k - E k a - E k b) (HvdH.negaMul r (u a) (v b))) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    rw [← Finset.smul_sum, hsum]
  have hchar : ∀ a b : Fin ts.prod,
      (∑ k : Fin ts.prod,
          HvdH.yMul r (E j k - E k a - E k b) (HvdH.negaMul r (u a) (v b)))
        = if b = HvdH.subIdx ts j a then (ts.prod : ℂ) • HvdH.negaMul r (u a) (v b) else 0 := by
    intro a b
    have hE : ∀ x y : Fin ts.prod,
        E x y = HvdH.synExp r ts (HvdH.digits ts y) (HvdH.digits ts x) := by
      intro x y
      simp only [E]
      exact synExp_swap r ts (HvdH.digits ts x) (HvdH.digits ts y)
    rw [Finset.sum_congr rfl (fun x _ => by rw [hE x a, hE x b])]
    exact hc r ts hr hpos ht j a b (HvdH.negaMul r (u a) (v b))
  have hcollapse : (∑ a : Fin ts.prod, ∑ b : Fin ts.prod,
        (if b = HvdH.subIdx ts j a then (ts.prod : ℂ) • HvdH.negaMul r (u a) (v b) else 0))
      = (ts.prod : ℂ) • (∑ a : Fin ts.prod, HvdH.negaMul r (u a) (V a)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hB : (ts.prod : ℂ) • HvdH.negaMul r (u a) (V a)
        = (ts.prod : ℂ) • HvdH.negaMul r (u a)
            (v ⟨HvdH.subIdx ts j a, Work.DFT.subIdx_lt ts hpos j a⟩) := rfl
    rw [hB]
    rw [Finset.sum_eq_single (⟨HvdH.subIdx ts j a, Work.DFT.subIdx_lt ts hpos j a⟩ : Fin ts.prod)]
    · simp
    · intro b _ hb
      have hne : (b : ℕ) ≠ HvdH.subIdx ts j a := fun h => hb (Fin.ext h)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- ### assembly
  have hscal : (1 / (((ts.prod * r : ℕ)) : ℂ))
      = (((r : ℂ))⁻¹ * ((1 / ((ts.prod : ℕ) : ℂ)) * (1 / ((ts.prod : ℕ) : ℂ))))
          * (ts.prod : ℂ) := by
    push_cast
    field_simp
  rw [hW, Finset.sum_congr rfl (fun k _ => hprod k), hreorder]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hchar a b)), hcollapse]
  rw [smul_smul, ← hscal, hL]

/-- The synthetic DFT diagonalises the convolution over `ℂ[y]/(y^r+1)`. -/
theorem convIdentity {r : ℕ} {ts : List ℕ} (hr : HvdH.IsPow2 r) (ht : ∀ t ∈ ts, t ∣ 2 * r) :
    ∀ u v : Fin ts.prod → Fin r → ℂ,
      HvdH.convR r ts u v = fun j c => (ts.prod : ℂ) *
        HvdH.synDFT r ts 1 (fun k c' => ((r : ℂ))⁻¹ *
          HvdH.negaMul r (HvdH.synDFT r ts (-1) u k) (HvdH.synDFT r ts (-1) v k) c') j c :=
  convIdentity_core Work.ConvR.negaMulLin.1 Work.ConvR.negaMulLin.2.2.2.1
    Work.ConvR.negaMulLin.2.2.2.2.1 Work.ConvR.negaMulLin.2.2.2.2.2.1
    Work.ConvR.negaMulLin.2.2.2.2.2.2 Work.ConvR.yMulNegMulAlt Work.ConvR.yCharSumConv hr ht

end Work.ConvR
