import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.PairSumCommon
import Submission.Work.FIArea4.pair_sum_le_Evar
import Submission.Work.FIArea4.Evar_le_trivial
import Submission.Work.FIArea4.Evar_eq_sum_clsSum
import Submission.Work.FIArea4.Vflip.Vcls_count_le_seven

/-!
# The small-modulus bound for the Jacobi-twisted variance (FI §11, `R*S < D`)

`Work.FIPlan.Vvar R S D β = Σ_{D < d ≤ 2D} E(d)` with the local variance (11.7)

`E(d) = Σ_{a < d} |Σ_{r̄s ≡ a (d)} β_{rs} (r/d')|²`

of `Submission/Work/FIArea4/Evar_le_trivial.lean`.  This file proves

`Vvar R S D β ≤ 33 · D · Σ_{r ≤ 2R, s ≤ 2S} ‖β r s‖²`  whenever  `R * S < D`

and the support of `β` consists of pairs with `(r, 2s) = 1` (the paper's (12.1) combined with the
restriction `d ≤ 2D`).

The mechanism is a double count of the *off-diagonal* contributions.  Expanding each class sum
squared, `E(d) = Σ_a |X_a|² = Σ_{p,q ∈ class a} β_p β̄_q (p₁|d')(q₁|d')`, the diagonal terms
`p = q` contribute at most `Σ‖β‖²` for each of the `D` moduli.  Off the diagonal, two distinct
pairs `p ≠ q` of a *single* class satisfy `d | p₁q₂ - q₁p₂ =: Δ`; because `(r, 2s) = 1` forces
`p, q` to be primitive (with `(p₁,p₂) = (q₁,q₂) = 1`), `Δ ≠ 0`, while
`|Δ| ≤ 8RS < 8D ≤ 8d`.  Hence the cofactor `|Δ|/d` is one of `1, …, 7` and each such `d` is
determined by it: a pair `(p,q)` can share a class for at most `7` moduli `d ∈ (D, 2D]`.  Summing
the matrix `(‖β_p‖‖β_q‖)_{p,q}` with this multiplicity and using Cauchy–Schwarz on the box
(`#box = 4RS < 4D`) gives `Vvar ≤ D·L2 + 7·4RS·L2 ≤ 29·D·L2 ≤ 33·D·L2`.
-/

set_option maxHeartbeats 1600000

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The box, the magnitude product and the class indicators -/

/-- The box `1 ≤ r ≤ 2R`, `1 ≤ s ≤ 2S` of the local variance, as a finset of pairs `(r,s)`. -/
def vBox (R S : ℕ) : Finset (ℕ × ℕ) := Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S)

/-- The magnitude product `‖β_p‖ ‖β_q‖` of a pair of pairs. -/
def wPair (β : ℕ → ℕ → ℂ) (p q : ℕ × ℕ) : ℝ := ‖β p.1 p.2‖ * ‖β q.1 q.2‖

/-- The indicator of "both `p` and `q` lie in the finset `u`". -/
def pairInd (u : Finset (ℕ × ℕ)) (p q : ℕ × ℕ) : ℝ := if p ∈ u ∧ q ∈ u then 1 else 0

/-- The indicator of "`p` and `q` lie in a common residue class modulo `d`". -/
def shareInd (R S d : ℕ) (p q : ℕ × ℕ) : ℝ :=
  if ∃ a ∈ Finset.range d, p ∈ EvarCls R S d a ∧ q ∈ EvarCls R S d a then 1 else 0

/-- The number of moduli `d ∈ (D, 2D]` for which `p` and `q` lie in a common residue class. -/
def shareCnt (R S D : ℕ) (p q : ℕ × ℕ) : ℕ :=
  ((Finset.Ioc D (2 * D)).filter
    (fun d => ∃ a ∈ Finset.range d, p ∈ EvarCls R S d a ∧ q ∈ EvarCls R S d a)).card

/-- The indicator of the diagonal `p = q`. -/
def diagInd (p q : ℕ × ℕ) : ℝ := if p = q then 1 else 0

lemma wPair_nonneg (β : ℕ → ℕ → ℂ) (p q : ℕ × ℕ) : 0 ≤ wPair β p q :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

lemma pairInd_nonneg (u : Finset (ℕ × ℕ)) (p q : ℕ × ℕ) : 0 ≤ pairInd u p q := by
  unfold pairInd; split <;> norm_num

lemma pairInd_le_one (u : Finset (ℕ × ℕ)) (p q : ℕ × ℕ) : pairInd u p q ≤ 1 := by
  unfold pairInd; split <;> norm_num

lemma pairInd_of {u : Finset (ℕ × ℕ)} {p q : ℕ × ℕ} (h : p ∈ u ∧ q ∈ u) :
    pairInd u p q = 1 := by
  unfold pairInd; exact if_pos h

lemma pairInd_of_not {u : Finset (ℕ × ℕ)} {p q : ℕ × ℕ} (h : ¬ (p ∈ u ∧ q ∈ u)) :
    pairInd u p q = 0 := by
  unfold pairInd; exact if_neg h

lemma shareInd_of {R S d : ℕ} {p q : ℕ × ℕ}
    (h : ∃ a ∈ Finset.range d, p ∈ EvarCls R S d a ∧ q ∈ EvarCls R S d a) :
    shareInd R S d p q = 1 := by
  unfold shareInd; exact if_pos h

lemma shareInd_of_not {R S d : ℕ} {p q : ℕ × ℕ}
    (h : ¬ ∃ a ∈ Finset.range d, p ∈ EvarCls R S d a ∧ q ∈ EvarCls R S d a) :
    shareInd R S d p q = 0 := by
  unfold shareInd; exact if_neg h

lemma diagInd_self (p : ℕ × ℕ) : diagInd p p = 1 := by
  unfold diagInd; exact if_pos rfl

lemma diagInd_of_ne {p q : ℕ × ℕ} (h : p ≠ q) : diagInd p q = 0 := by
  unfold diagInd; exact if_neg h

/-! ## The box -/

lemma mem_vBox {R S : ℕ} {p : ℕ × ℕ} :
    p ∈ vBox R S ↔ 1 ≤ p.1 ∧ p.1 ≤ 2 * R ∧ 1 ≤ p.2 ∧ p.2 ≤ 2 * S := by
  simp only [vBox, Finset.mem_product, Finset.mem_Icc]
  tauto

lemma card_vBox (R S : ℕ) : (vBox R S).card = 4 * R * S := by
  rw [vBox, Finset.card_product, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel,
    Nat.add_sub_cancel]
  ring

lemma EvarCls_subset_vBox (R S d a : ℕ) : EvarCls R S d a ⊆ vBox R S := by
  intro p hp
  rw [EvarCls] at hp
  obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpr, hps⟩ := Finset.mem_product.mp hp1
  rw [vBox, Finset.mem_product]
  exact ⟨Finset.filter_subset _ _ hpr, hps⟩

lemma p14L2_eq_sum_vBox (R S : ℕ) (β : ℕ → ℕ → ℂ) :
    p14L2 R S β = ∑ p ∈ vBox R S, Complex.normSq (β p.1 p.2) := by
  rw [p14L2, vBox, Finset.sum_product]

lemma p14L2_nonneg (R S : ℕ) (β : ℕ → ℕ → ℂ) : 0 ≤ p14L2 R S β := by
  rw [p14L2_eq_sum_vBox]
  exact Finset.sum_nonneg (fun p _ => Complex.normSq_nonneg _)

/-! ## Elementary sum lemmas -/

/-- The squared modulus of a sum, expanded: `‖Σ f‖² = Σ_{x,y} (f x · conj (f y)).re`. -/
lemma normSq_sum_expand {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.normSq (∑ x ∈ s, f x) = ∑ x ∈ s, ∑ y ∈ s, (f x * star (f y)).re := by
  rw [Complex.normSq_apply, Complex.re_sum, Complex.im_sum, Finset.sum_mul_sum,
    Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- For `u ⊆ v`, the double sum over `u × u` as a double sum over `v × v` weighted by the
indicator `pairInd u`. -/
lemma sum_sum_subset_pairInd (u v : Finset (ℕ × ℕ)) (h : u ⊆ v) (f : ℕ × ℕ → ℕ × ℕ → ℝ) :
    (∑ p ∈ u, ∑ q ∈ u, f p q) = ∑ p ∈ v, ∑ q ∈ v, f p q * pairInd u p q := by
  have hinner : ∀ p, (∑ q ∈ v, f p q * pairInd u p q) = pairInd u p p * ∑ q ∈ u, f p q := by
    intro p
    have h1 : (∑ q ∈ v, f p q * pairInd u p q)
        = ∑ q ∈ u, f p q * pairInd u p q := by
      refine (Finset.sum_subset h (fun q _ hq => ?_)).symm
      rw [pairInd_of_not (fun hc => hq hc.2), mul_zero]
    have h2 : (∑ q ∈ u, f p q * pairInd u p q)
        = ∑ q ∈ u, f p q * pairInd u p p := by
      refine Finset.sum_congr rfl (fun q hq => ?_)
      by_cases hp : p ∈ u
      · rw [pairInd_of ⟨hp, hq⟩, pairInd_of ⟨hp, hp⟩]
      · rw [pairInd_of_not (fun hc => hp hc.1), pairInd_of_not (fun hc => hp hc.1)]
    rw [h1, h2, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [Finset.sum_congr rfl (fun p _ => hinner p)]
  have h3 : (∑ p ∈ v, pairInd u p p * ∑ q ∈ u, f p q)
      = ∑ p ∈ u, pairInd u p p * ∑ q ∈ u, f p q := by
    refine (Finset.sum_subset h (fun p _ hp => ?_)).symm
    rw [pairInd_of_not (fun hc => hp hc.1), zero_mul]
  rw [h3]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [pairInd_of ⟨hp, hp⟩, one_mul]

/-! ## The Jacobi weight is bounded by `1` -/

lemma jw_norm_le_one (d r : ℕ) : ‖jw d r‖ ≤ 1 := by
  rw [jw]
  rcases jacobiSym.trichotomy (r : ℤ) (FIPlan.oddPart d) with h | h | h
  · rw [h]; simp
  · rw [h]; simp
  · rw [h]; simp

lemma norm_mul_jw_le (z : ℂ) (d r : ℕ) : ‖z * jw d r‖ ≤ ‖z‖ := by
  rw [norm_mul]
  calc ‖z‖ * ‖jw d r‖ ≤ ‖z‖ * 1 :=
        mul_le_mul_of_nonneg_left (jw_norm_le_one d r) (norm_nonneg z)
    _ = ‖z‖ := mul_one _

/-! ## The pointwise bound for a single class sum -/

/-- **The squared class sum is bounded by the box-double-sum of `‖β‖‖β‖`.**  Expanding the square
and using `|Re w| ≤ ‖w‖ ≤ ‖β_p‖‖β_q‖` (the Jacobi weight has modulus `≤ 1`). -/
lemma normSq_clsSum_le_box (R S d a : ℕ) (β : ℕ → ℕ → ℂ) :
    Complex.normSq (clsSum R S d β a) ≤
      ∑ p ∈ vBox R S, ∑ q ∈ vBox R S, wPair β p q * pairInd (EvarCls R S d a) p q := by
  rw [clsSum, normSq_sum_expand]
  have hsub : (∑ p ∈ EvarCls R S d a, ∑ q ∈ EvarCls R S d a, wPair β p q)
      = ∑ p ∈ vBox R S, ∑ q ∈ vBox R S,
          wPair β p q * pairInd (EvarCls R S d a) p q :=
    sum_sum_subset_pairInd _ _ (EvarCls_subset_vBox R S d a) (wPair β)
  calc ∑ p ∈ EvarCls R S d a, ∑ q ∈ EvarCls R S d a,
        ((β p.1 p.2 * jw d p.1) * star (β q.1 q.2 * jw d q.1)).re
      ≤ ∑ p ∈ EvarCls R S d a, ∑ q ∈ EvarCls R S d a, wPair β p q :=
        Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => ?_))
    _ = ∑ p ∈ vBox R S, ∑ q ∈ vBox R S,
          wPair β p q * pairInd (EvarCls R S d a) p q := hsub
  unfold wPair
  calc ((β p.1 p.2 * jw d p.1) * star (β q.1 q.2 * jw d q.1)).re
      ≤ ‖(β p.1 p.2 * jw d p.1) * star (β q.1 q.2 * jw d q.1)‖ := Complex.re_le_norm _
    _ = ‖β p.1 p.2 * jw d p.1‖ * ‖β q.1 q.2 * jw d q.1‖ := by rw [norm_mul, norm_star]
    _ ≤ ‖β p.1 p.2‖ * ‖β q.1 q.2‖ :=
          mul_le_mul (norm_mul_jw_le _ _ _) (norm_mul_jw_le _ _ _) (norm_nonneg _)
            (norm_nonneg _)

/-! ## Collapsing the residue-class sum

For a fixed modulus `d` the residue classes `EvarCls R S d a` (`a < d`) are pairwise disjoint, so a
pair `(p,q)` can lie in the same class for at most one `a`: the sum over `a` of the class indicator
is at most the indicator of the existence of such an `a`. -/

lemma card_filter_range_EvarCls_le_one (R S d : ℕ) (hd : 0 < d) (p q : ℕ × ℕ) :
    ((Finset.range d).filter
      (fun a => p ∈ EvarCls R S d a ∧ q ∈ EvarCls R S d a)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  by_contra hab
  have hdisj : Disjoint (EvarCls R S d a) (EvarCls R S d b) :=
    pairwiseDisjoint_EvarCls R S d hd ha.1 hb.1 hab
  rw [Finset.disjoint_left] at hdisj
  exact hdisj ha.2.1 hb.2.1

lemma sum_pairInd_le_shareInd (R S d : ℕ) (hd : 0 < d) (p q : ℕ × ℕ) :
    (∑ a ∈ Finset.range d, pairInd (EvarCls R S d a) p q) ≤ shareInd R S d p q := by
  by_cases hex : ∃ a ∈ Finset.range d, p ∈ EvarCls R S d a ∧ q ∈ EvarCls R S d a
  · rw [shareInd_of hex]
    have hA : ((Finset.range d).filter
        (fun a => p ∈ EvarCls R S d a ∧ q ∈ EvarCls R S d a)).card ≤ 1 :=
      card_filter_range_EvarCls_le_one R S d hd p q
    have h1 : (∑ a ∈ Finset.range d, pairInd (EvarCls R S d a) p q)
        = ∑ a ∈ (Finset.range d).filter
            (fun a => p ∈ EvarCls R S d a ∧ q ∈ EvarCls R S d a),
          pairInd (EvarCls R S d a) p q :=
      (Finset.sum_subset (Finset.filter_subset _ _) (fun a ha han => by
        rw [Finset.mem_filter] at han
        exact pairInd_of_not (fun hc => han ⟨ha, hc⟩))).symm
    have h2 : (∑ a ∈ (Finset.range d).filter
            (fun a => p ∈ EvarCls R S d a ∧ q ∈ EvarCls R S d a),
          pairInd (EvarCls R S d a) p q)
        = (((Finset.range d).filter
            (fun a => p ∈ EvarCls R S d a ∧ q ∈ EvarCls R S d a)).card : ℝ) := by
      rw [Finset.sum_congr rfl (fun a ha => pairInd_of (Finset.mem_filter.mp ha).2)]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1, h2]
    have hA' : (((Finset.range d).filter
        (fun a => p ∈ EvarCls R S d a ∧ q ∈ EvarCls R S d a)).card : ℝ) ≤ 1 := by
      exact_mod_cast hA
    linarith
  · rw [shareInd_of_not hex]
    refine le_of_eq ?_
    refine Finset.sum_eq_zero (fun a ha => ?_)
    exact pairInd_of_not (fun hc => hex ⟨a, ha, hc⟩)

/-! ## The local variance, bounded by a double sum over the box -/

lemma Evar_le_sum_box_indicator (R S d : ℕ) (β : ℕ → ℕ → ℂ) (hd : 0 < d) :
    FIPlan.Evar R S d β ≤
      ∑ p ∈ vBox R S, ∑ q ∈ vBox R S, wPair β p q * shareInd R S d p q := by
  rw [Evar_eq_sum_clsSum]
  calc ∑ a ∈ Finset.range d, Complex.normSq (clsSum R S d β a)
      ≤ ∑ a ∈ Finset.range d, ∑ p ∈ vBox R S, ∑ q ∈ vBox R S,
          wPair β p q * pairInd (EvarCls R S d a) p q :=
        Finset.sum_le_sum (fun a _ => normSq_clsSum_le_box R S d a β)
    _ = ∑ p ∈ vBox R S, ∑ q ∈ vBox R S, ∑ a ∈ Finset.range d,
          wPair β p q * pairInd (EvarCls R S d a) p q := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ p ∈ vBox R S, ∑ q ∈ vBox R S,
          wPair β p q * (∑ a ∈ Finset.range d, pairInd (EvarCls R S d a) p q) := by
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
        rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ vBox R S, ∑ q ∈ vBox R S, wPair β p q * shareInd R S d p q :=
        Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ =>
          mul_le_mul_of_nonneg_left (sum_pairInd_le_shareInd R S d hd p q)
            (wPair_nonneg β p q)))

/-! ## The variance as a double sum over pairs, with the number of moduli as multiplicity -/

lemma sum_shareInd_eq_shareCnt (R S D : ℕ) (p q : ℕ × ℕ) :
    (∑ d ∈ Finset.Ioc D (2 * D), shareInd R S d p q) = ((shareCnt R S D p q : ℕ) : ℝ) := by
  unfold shareInd shareCnt
  rw [Finset.sum_boole]

lemma Vvar_le_count (R S D : ℕ) (β : ℕ → ℕ → ℂ) :
    FIPlan.Vvar R S D β ≤
      ∑ p ∈ vBox R S, ∑ q ∈ vBox R S, wPair β p q * ((shareCnt R S D p q : ℕ) : ℝ) := by
  rw [FIPlan.Vvar]
  calc ∑ d ∈ Finset.Ioc D (2 * D), FIPlan.Evar R S d β
      ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ p ∈ vBox R S, ∑ q ∈ vBox R S,
          wPair β p q * shareInd R S d p q :=
        Finset.sum_le_sum (fun d hd =>
          Evar_le_sum_box_indicator R S d β (by
            have := (Finset.mem_Ioc.mp hd).1
            omega))
    _ = ∑ p ∈ vBox R S, ∑ q ∈ vBox R S, ∑ d ∈ Finset.Ioc D (2 * D),
          wPair β p q * shareInd R S d p q := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ p ∈ vBox R S, ∑ q ∈ vBox R S,
          wPair β p q * (∑ d ∈ Finset.Ioc D (2 * D), shareInd R S d p q) := by
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
        rw [Finset.mul_sum]
    _ = ∑ p ∈ vBox R S, ∑ q ∈ vBox R S, wPair β p q * ((shareCnt R S D p q : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
        rw [sum_shareInd_eq_shareCnt]

/-! ## The multiplicity bounds -/

lemma shareCnt_le_D (R S D : ℕ) (p q : ℕ × ℕ) : shareCnt R S D p q ≤ D := by
  unfold shareCnt
  calc ((Finset.Ioc D (2 * D)).filter _).card ≤ (Finset.Ioc D (2 * D)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = D := by rw [Nat.card_Ioc]; omega

lemma shareCnt_le_seven (R S D : ℕ) (β : ℕ → ℕ → ℂ) (p q : ℕ × ℕ)
    (hD : 1 ≤ D) (hRS : R * S < D)
    (hcop : ∀ r s, β r s ≠ 0 → Nat.Coprime r (2 * s))
    (hp : p ∈ vBox R S) (hq : q ∈ vBox R S)
    (hbp : β p.1 p.2 ≠ 0) (hbq : β q.1 q.2 ≠ 0) (hpq : p ≠ q) :
    shareCnt R S D p q ≤ 7 := by
  unfold shareCnt
  refine Vcls_count_le_seven R S D β p q hD hRS hcop ?_ ?_ hbp hbq hpq
  · rw [mem_vBox] at hp; exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp.1, hp.2.1⟩,
      Finset.mem_Icc.mpr ⟨hp.2.2.1, hp.2.2.2⟩⟩
  · rw [mem_vBox] at hq; exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hq.1, hq.2.1⟩,
      Finset.mem_Icc.mpr ⟨hq.2.2.1, hq.2.2.2⟩⟩

/-! ## The main theorem -/

lemma sum_wPair_self (R S : ℕ) (β : ℕ → ℕ → ℂ) :
    (∑ p ∈ vBox R S, wPair β p p) = p14L2 R S β := by
  rw [p14L2_eq_sum_vBox]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  unfold wPair
  rw [Complex.normSq_eq_norm_sq]
  ring

lemma sum_diagInd_mul (R S : ℕ) (β : ℕ → ℕ → ℂ) {p : ℕ × ℕ} (hp : p ∈ vBox R S) :
    (∑ q ∈ vBox R S, wPair β p q * diagInd p q) = wPair β p p := by
  have hmain : (∑ q ∈ vBox R S, wPair β p q * diagInd p q)
      = wPair β p p * diagInd p p :=
    Finset.sum_eq_single p (fun q _ hq => by rw [diagInd_of_ne (Ne.symm hq), mul_zero])
      (fun h => absurd hp h)
  rw [hmain, diagInd_self, mul_one]

lemma sum_wPair_eq_sq (R S : ℕ) (β : ℕ → ℕ → ℂ) :
    (∑ p ∈ vBox R S, ∑ q ∈ vBox R S, wPair β p q)
      = (∑ p ∈ vBox R S, ‖β p.1 p.2‖) ^ 2 := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  unfold wPair
  rw [Finset.mul_sum]

theorem Vvar_le_of_mul_lt_D (D R S : ℕ) (β : ℕ → ℕ → ℂ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hRS : R * S < D)
    (hcop : ∀ r s, β r s ≠ 0 → Nat.Coprime r (2 * s)) :
    Work.FIPlan.Vvar R S D β ≤ 33 * (D : ℝ) * Work.FIArea4.p14L2 R S β := by
  have hL2nn : (0 : ℝ) ≤ p14L2 R S β := p14L2_nonneg R S β
  have hpt : ∀ p ∈ vBox R S, ∀ q ∈ vBox R S,
      wPair β p q * ((shareCnt R S D p q : ℕ) : ℝ)
        ≤ (D : ℝ) * (wPair β p q * diagInd p q) + 7 * wPair β p q := by
    intro p hp q hq
    have hGnn : (0 : ℝ) ≤ wPair β p q := wPair_nonneg β p q
    by_cases hpq : p = q
    · have h1 : ((shareCnt R S D p q : ℕ) : ℝ) ≤ (D : ℝ) := by
        rw [hpq]
        exact_mod_cast shareCnt_le_D R S D q q
      have hdiag1 : diagInd p q = 1 := by rw [hpq]; exact diagInd_self q
      rw [hdiag1, mul_one]
      calc wPair β p q * ((shareCnt R S D p q : ℕ) : ℝ) ≤ wPair β p q * (D : ℝ) :=
            mul_le_mul_of_nonneg_left h1 hGnn
        _ ≤ (D : ℝ) * wPair β p q + 7 * wPair β p q := by nlinarith [hGnn]
    · rw [diagInd_of_ne hpq, mul_zero, mul_zero, zero_add]
      by_cases hb : β p.1 p.2 = 0 ∨ β q.1 q.2 = 0
      · have hz : wPair β p q = 0 := by
          rcases hb with hb | hb
          · unfold wPair; rw [hb, norm_zero, zero_mul]
          · unfold wPair; rw [hb, norm_zero, mul_zero]
        have hz2 : wPair β p q * ((shareCnt R S D p q : ℕ) : ℝ) = 0 := by rw [hz, zero_mul]
        rw [hz2]
        exact mul_nonneg (by norm_num) hGnn
      · simp only [not_or] at hb
        have h7 : ((shareCnt R S D p q : ℕ) : ℝ) ≤ 7 := by
          exact_mod_cast shareCnt_le_seven R S D β p q hD hRS hcop hp hq hb.1 hb.2 hpq
        calc wPair β p q * ((shareCnt R S D p q : ℕ) : ℝ) ≤ wPair β p q * 7 :=
              mul_le_mul_of_nonneg_left h7 hGnn
          _ = 7 * wPair β p q := by ring
  have hsum := Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => hpt p hp q hq))
  have hsplit : (∑ p ∈ vBox R S, ∑ q ∈ vBox R S,
        ((D : ℝ) * (wPair β p q * diagInd p q) + 7 * wPair β p q))
      = (∑ p ∈ vBox R S, ∑ q ∈ vBox R S, (D : ℝ) * (wPair β p q * diagInd p q))
        + ∑ p ∈ vBox R S, ∑ q ∈ vBox R S, 7 * wPair β p q := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_add_distrib]
  have hdiag : (∑ p ∈ vBox R S, ∑ q ∈ vBox R S, (D : ℝ) * (wPair β p q * diagInd p q))
      = (D : ℝ) * p14L2 R S β := by
    calc (∑ p ∈ vBox R S, ∑ q ∈ vBox R S, (D : ℝ) * (wPair β p q * diagInd p q))
        = ∑ p ∈ vBox R S, (D : ℝ) * (∑ q ∈ vBox R S, wPair β p q * diagInd p q) := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ p ∈ vBox R S, (D : ℝ) * wPair β p p := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [sum_diagInd_mul R S β hp]
      _ = (D : ℝ) * p14L2 R S β := by
          rw [← Finset.mul_sum, sum_wPair_self]
  have hfull : (∑ p ∈ vBox R S, ∑ q ∈ vBox R S, 7 * wPair β p q)
      = 7 * (∑ p ∈ vBox R S, ‖β p.1 p.2‖) ^ 2 := by
    calc (∑ p ∈ vBox R S, ∑ q ∈ vBox R S, 7 * wPair β p q)
        = 7 * ∑ p ∈ vBox R S, ∑ q ∈ vBox R S, wPair β p q := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [Finset.mul_sum]
      _ = 7 * (∑ p ∈ vBox R S, ‖β p.1 p.2‖) ^ 2 := by rw [sum_wPair_eq_sq]
  have hcs : (∑ p ∈ vBox R S, ‖β p.1 p.2‖) ^ 2 ≤ 4 * (R : ℝ) * (S : ℝ) * p14L2 R S β := by
    have h := sq_sum_le_card_mul_sum_sq (s := vBox R S)
      (f := fun p : ℕ × ℕ => ‖β p.1 p.2‖)
    rw [card_vBox] at h
    have h2 : (∑ p ∈ vBox R S, ‖β p.1 p.2‖ ^ 2) = p14L2 R S β := by
      rw [p14L2_eq_sum_vBox]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Complex.normSq_eq_norm_sq]
    rw [h2] at h
    have h3 : ((4 * R * S : ℕ) : ℝ) = 4 * (R : ℝ) * (S : ℝ) := by push_cast; ring
    rw [h3] at h
    exact h
  have hRSle : ((R : ℝ) * S) ≤ (D : ℝ) - 1 := by
    have h : R * S + 1 ≤ D := hRS
    have h' : ((R * S : ℕ) : ℝ) + 1 ≤ (D : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  calc Work.FIPlan.Vvar R S D β
      ≤ ∑ p ∈ vBox R S, ∑ q ∈ vBox R S, wPair β p q * ((shareCnt R S D p q : ℕ) : ℝ) :=
        Vvar_le_count R S D β
    _ ≤ ∑ p ∈ vBox R S, ∑ q ∈ vBox R S,
          ((D : ℝ) * (wPair β p q * diagInd p q) + 7 * wPair β p q) := hsum
    _ = (D : ℝ) * p14L2 R S β + 7 * (∑ p ∈ vBox R S, ‖β p.1 p.2‖) ^ 2 := by
        rw [hsplit, hdiag, hfull]
    _ ≤ (D : ℝ) * p14L2 R S β + 7 * (4 * (R : ℝ) * S * p14L2 R S β) := by
        have := mul_le_mul_of_nonneg_left hcs (by norm_num : (0 : ℝ) ≤ 7)
        linarith
    _ ≤ 33 * (D : ℝ) * p14L2 R S β := by
        have hkey : 28 * ((R : ℝ) * S) * p14L2 R S β
            ≤ 28 * ((D : ℝ) - 1) * p14L2 R S β := by
          have h1 : 28 * ((R : ℝ) * S) ≤ 28 * ((D : ℝ) - 1) := by linarith
          exact mul_le_mul_of_nonneg_right h1 hL2nn
        nlinarith [hkey, hL2nn]

end

end Work.FIArea4.Vflip
