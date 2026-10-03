import Mathlib
import Submission.Work.FIPlan.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The trivial bound for the local variance `E(d)` of Friedlander–Iwaniec (11.7)

`Work.FIPlan.Evar R S d α` is the local variance

`E(d) = Σ_{a < d} |Σ_{r̄s ≡ a (d)} α_{rs} (r/d')|²`,

where `d'` is the odd part of `d` and `(r/d')` is the Jacobi symbol (`Work.FIPlan.oddPart`).

This file proves the **trivial** (large-sieve-free) estimate for `E(d)`: whenever the support of
`α` consists of pairs with `gcd(r,d) = 1`, the residue classes `a ≡ s r^{-1} (mod d)` partition
the support, so Cauchy–Schwarz gives

`E(d) ≤ (4·R·S/d + 4·R + 4) · Σ_{r ≤ 2R} Σ_{s ≤ 2S} ‖α r s‖²`.

The mechanism is entirely elementary:

* each class sum is estimated by Cauchy–Schwarz against the number of pairs it contains, the
  Jacobi weight having modulus `≤ 1`;
* a class contains at most `2R·(2S/d + 1)` pairs (`s` is determined modulo `d` for each `r`);
* the classes partition the box `[1,2R] × [1,2S]`.

The number `4·R·S/d + 4·R + 4` dominates `2R·(2S/d+1)`, which is the paper's
`≪ (d^{-1}RS + R)` in its usable asymmetric form.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary ingredients -/

/-- **Cauchy–Schwarz for complex sums**: the squared modulus of a sum is at most the number of
terms times the sum of the squared moduli. -/
lemma normSq_sum_le_card_mul_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.normSq (∑ x ∈ s, f x) ≤ (s.card : ℝ) * ∑ x ∈ s, Complex.normSq (f x) := by
  rw [Complex.normSq_eq_norm_sq]
  calc ‖∑ x ∈ s, f x‖ ^ 2 ≤ (∑ x ∈ s, ‖f x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = (s.card : ℝ) * ∑ x ∈ s, Complex.normSq (f x) := by
        simp only [Complex.normSq_eq_norm_sq]

/-- The Jacobi symbol `j(n/d)` is `0`, `1` or `-1`, so multiplying by it does not increase
`Complex.normSq`. -/
lemma normSq_mul_jacobiSym_le (z : ℂ) (m : ℤ) (n : ℕ) :
    Complex.normSq (z * (jacobiSym m n : ℂ)) ≤ Complex.normSq z := by
  rw [Complex.normSq_mul]
  have hone : Complex.normSq ((jacobiSym m n : ℤ) : ℂ) ≤ 1 := by
    rcases jacobiSym.trichotomy m n with h | h | h
    · rw [h, Complex.normSq_intCast]; norm_num
    · rw [h, Complex.normSq_intCast]; norm_num
    · rw [h, Complex.normSq_intCast]; norm_num
  nlinarith [Complex.normSq_nonneg z]

/-- Splitting a sum over a filtered product into nested sums. -/
lemma sum_product_filter {α β M : Type*} [AddCommMonoid M]
    (s : Finset α) (t : Finset β) (p : α × β → Prop) [DecidablePred p] (f : α × β → M) :
    ∑ x ∈ (s ×ˢ t).filter p, f x = ∑ a ∈ s, ∑ b ∈ (t.filter (fun b => p (a,b))), f (a,b) := by
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_filter]

/-! ## The residue classes of the box -/

/-- The `r`'s in `[1, 2R]` that are coprime to `d` — the `r`-support of the inner sum of `Evar`. -/
def EvarR (R d : ℕ) : Finset ℕ := (Finset.Icc 1 (2 * R)).filter (fun r => Nat.Coprime r d)

/-- The pairs `(r,s)` of the box whose class `s·r⁻¹ (mod d)` equals `a`. -/
def EvarCls (R S d a : ℕ) : Finset (ℕ × ℕ) :=
  (EvarR R d ×ˢ Finset.Icc 1 (2 * S)).filter
    (fun p => (p.2 : ZMod d) = (p.1 : ZMod d) * (a : ZMod d))

lemma mem_EvarR {R d r : ℕ} :
    r ∈ EvarR R d ↔ r ∈ Finset.Icc 1 (2 * R) ∧ Nat.Coprime r d := by
  simp [EvarR]

lemma mem_EvarCls {R S d a : ℕ} {p : ℕ × ℕ} :
    p ∈ EvarCls R S d a ↔ p.1 ∈ EvarR R d ∧ p.2 ∈ Finset.Icc 1 (2 * S) ∧
      (p.2 : ZMod d) = (p.1 : ZMod d) * (a : ZMod d) := by
  simp only [EvarCls, Finset.mem_filter, Finset.mem_product]
  tauto

/-- A residue class of the box contains at most `2R·(2S/d + 1)` pairs: for each `r` the
integer `s ∈ [1,2S]` is determined modulo `d`, and `s ↦ s/d` is injective on a residue class. -/
lemma EvarCls_card_le (R S d a : ℕ) (_hd : 0 < d) :
    (EvarCls R S d a).card ≤ 2 * R * (2 * S / d + 1) := by
  have hmt : Set.MapsTo (fun p : ℕ × ℕ => (p.1, p.2 / d))
      ↑(EvarCls R S d a) ↑(EvarR R d ×ˢ Finset.range (2 * S / d + 1)) := by
    intro p hp
    rw [Finset.mem_coe, mem_EvarCls] at hp
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
    obtain ⟨hp1, hp2, -⟩ := hp
    refine ⟨hp1, ?_⟩
    have hle : p.2 ≤ 2 * S := (Finset.mem_Icc.mp hp2).2
    calc p.2 / d ≤ 2 * S / d := Nat.div_le_div_right hle
      _ < 2 * S / d + 1 := Nat.lt_succ_self _
  have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1, p.2 / d)) ↑(EvarCls R S d a) := by
    intro p hp q hq heq
    rw [Finset.mem_coe, mem_EvarCls] at hp hq
    obtain ⟨-, -, hpc⟩ := hp
    obtain ⟨-, -, hqc⟩ := hq
    have h1 : p.1 = q.1 := by simpa using congrArg Prod.fst heq
    have h2 : p.2 / d = q.2 / d := by simpa using congrArg Prod.snd heq
    have hmod : p.2 % d = q.2 % d := by
      rw [← ZMod.natCast_eq_natCast_iff' p.2 q.2 d, hpc, hqc, h1]
    have h2' : p.2 = q.2 :=
      calc p.2 = d * (p.2 / d) + p.2 % d := (Nat.div_add_mod p.2 d).symm
        _ = d * (q.2 / d) + p.2 % d := by rw [h2]
        _ = d * (q.2 / d) + q.2 % d := by rw [hmod]
        _ = q.2 := Nat.div_add_mod q.2 d
    exact Prod.ext h1 h2'
  have h2 := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (p.1, p.2 / d)) hmt hinj
  rw [Finset.card_product, Finset.card_range] at h2
  refine le_trans h2 (Nat.mul_le_mul_right _ ?_)
  calc (EvarR R d).card ≤ (Finset.Icc 1 (2 * R)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 * R := by rw [Nat.card_Icc]; omega

/-- Distinct residue classes are disjoint: a common pair `(r,s)` has `r` a unit modulo `d`, so
the congruence `s ≡ r a ≡ r b (mod d)` forces `a = b`. -/
lemma pairwiseDisjoint_EvarCls (R S d : ℕ) (_hd : 0 < d) :
    (↑(Finset.range d) : Set ℕ).PairwiseDisjoint (EvarCls R S d) := by
  intro a ha b hb hab
  show Disjoint (EvarCls R S d a) (EvarCls R S d b)
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [mem_EvarCls] at hp hq
  obtain ⟨hp1, -, hpa⟩ := hp
  obtain ⟨hq1, -, hqb⟩ := hq
  have hcop : Nat.Coprime p.1 d := (mem_EvarR.mp hp1).2
  have hu : IsUnit ((p.1 : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime p.1 d).mpr hcop
  have hcong : (a : ZMod d) = (b : ZMod d) := by
    apply hu.mul_left_cancel
    rw [← hpa, ← hqb]
  have hlt : a < d := by simpa using ha
  have hlt' : b < d := by simpa using hb
  have hmod : a = b := by
    have h := (ZMod.natCast_eq_natCast_iff' a b d).mp hcong
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt'] at h
  exact hab hmod

/-- The residue classes partition the box `EvarR R d ×ˢ [1,2S]`. -/
lemma sum_EvarCls_le (R S d : ℕ) (hd : 0 < d) (f : ℕ × ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∑ a ∈ Finset.range d, ∑ p ∈ EvarCls R S d a, f p
      ≤ ∑ p ∈ EvarR R d ×ˢ Finset.Icc 1 (2 * S), f p := by
  rw [← Finset.sum_biUnion (f := f) (pairwiseDisjoint_EvarCls R S d hd)]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.biUnion_subset.mpr (fun a _ => Finset.filter_subset _ _)) (fun p _ _ => hf p)

/-! ## The trivial bound -/

/-- **The trivial bound in raw form**: `E(d) ≤ 2R·(2S/d + 1)·Σ‖α r s‖²`. -/
lemma Evar_le_aux (R S d : ℕ) (α : ℕ → ℕ → ℂ) (hd : 0 < d) :
    Work.FIPlan.Evar R S d α ≤
      2 * (R : ℝ) * (2 * (S : ℝ) / (d : ℝ) + 1) *
        ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s) := by
  let C : ℝ := 2 * (R : ℝ) * (2 * (S : ℝ) / (d : ℝ) + 1)
  let T : ℝ := ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s)
  let β : ℕ × ℕ → ℂ := fun p => α p.1 p.2 * (jacobiSym (p.1 : ℤ) (Work.FIPlan.oddPart d) : ℂ)
  have hCnn : 0 ≤ C := by
    have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
    have : (0:ℝ) ≤ 2 * (S:ℝ) / (d:ℝ) + 1 := by positivity
    simp only [C]
    positivity
  have hTnn : 0 ≤ T := by
    simp only [T]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
  -- regroup `Evar` by residue class
  have hsplit : Work.FIPlan.Evar R S d α =
      ∑ a ∈ Finset.range d, Complex.normSq (∑ p ∈ EvarCls R S d a, β p) := by
    rw [Work.FIPlan.Evar]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [EvarCls, EvarR]
    refine Eq.symm ?_
    rw [sum_product_filter]
  -- Cauchy–Schwarz in each residue class
  have hper : ∀ a, Complex.normSq (∑ p ∈ EvarCls R S d a, β p)
      ≤ C * ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2) := by
    intro a
    have hcs := normSq_sum_le_card_mul_sum (EvarCls R S d a) β
    have hterm : ∑ p ∈ EvarCls R S d a, Complex.normSq (β p)
        ≤ ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2) := by
      refine Finset.sum_le_sum (fun p _ => ?_)
      simp only [β]
      exact normSq_mul_jacobiSym_le _ _ _
    have hcard : ((EvarCls R S d a).card : ℝ) ≤ C := by
      have h1 : ((EvarCls R S d a).card : ℝ) ≤ ((2 * R * (2 * S / d + 1) : ℕ) : ℝ) := by
        exact_mod_cast EvarCls_card_le R S d a hd
      have h2 : ((2 * R * (2 * S / d + 1) : ℕ) : ℝ) ≤ C := by
        have h3 : (((2 * S / d : ℕ)) : ℝ) ≤ 2 * (S : ℝ) / (d : ℝ) := by
          have h := (Nat.cast_div_le (m := 2 * S) (n := d) :
            (((2 * S / d : ℕ)) : ℝ) ≤ ((2 * S : ℕ) : ℝ) / (d : ℝ))
          push_cast at h
          exact h
        have h4 : (0:ℝ) ≤ 2 * (R:ℝ) := by positivity
        simp only [C]
        calc ((2 * R * (2 * S / d + 1) : ℕ) : ℝ)
            = 2 * (R:ℝ) * (((2 * S / d : ℕ) : ℝ) + 1) := by push_cast; ring
          _ ≤ 2 * (R:ℝ) * (2 * (S:ℝ) / (d:ℝ) + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) h4
      linarith
    calc Complex.normSq (∑ p ∈ EvarCls R S d a, β p)
        ≤ ((EvarCls R S d a).card : ℝ) * ∑ p ∈ EvarCls R S d a, Complex.normSq (β p) := hcs
      _ ≤ ((EvarCls R S d a).card : ℝ) * ∑ p ∈ EvarCls R S d a,
            Complex.normSq (α p.1 p.2) :=
          mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg _)
      _ ≤ C * ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2) :=
          mul_le_mul_of_nonneg_right hcard
            (Finset.sum_nonneg (fun p _ => Complex.normSq_nonneg _))
  -- the classes partition the box, and the box sits inside `[1,2R] × [1,2S]`
  have hpart : ∑ a ∈ Finset.range d, ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2)
      ≤ ∑ p ∈ EvarR R d ×ˢ Finset.Icc 1 (2 * S), Complex.normSq (α p.1 p.2) :=
    sum_EvarCls_le R S d hd (fun p : ℕ × ℕ => Complex.normSq (α p.1 p.2))
      (fun p => Complex.normSq_nonneg (α p.1 p.2))
  have hfin : ∑ p ∈ EvarR R d ×ˢ Finset.Icc 1 (2 * S), Complex.normSq (α p.1 p.2) ≤ T := by
    simp only [T]
    rw [Finset.sum_product]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun r _ _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
  calc Work.FIPlan.Evar R S d α
      = ∑ a ∈ Finset.range d, Complex.normSq (∑ p ∈ EvarCls R S d a, β p) := hsplit
    _ ≤ ∑ a ∈ Finset.range d, C * ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2) :=
        Finset.sum_le_sum (fun a _ => hper a)
    _ = C * ∑ a ∈ Finset.range d, ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2) := by
        rw [Finset.mul_sum]
    _ ≤ C * ∑ p ∈ EvarR R d ×ˢ Finset.Icc 1 (2 * S), Complex.normSq (α p.1 p.2) :=
        mul_le_mul_of_nonneg_left hpart hCnn
    _ ≤ C * T := mul_le_mul_of_nonneg_left hfin hCnn

/-- **The trivial (large-sieve-free) bound for the local variance `E(d)` of FI (11.7).**
`Work.FIPlan.Evar R S d α = Σ_{a < d} |Σ_{r̄s ≡ a (mod d)} α r s · (r/d')|²` with `d'` the odd
part of `d` (see `Submission/Work/FIPlan/Interface.lean`).  If the support of `α` consists of
pairs `(r,s)` with `gcd(r,d) = 1` (which makes the residue class `a ≡ s r^{-1} (mod d)` of every
supported pair unique, so that the classes partition the support), then

  `E(d) ≤ (4·R·S/d + 4·R + 4) · Σ_{r ≤ 2R} Σ_{s ≤ 2S} ‖α r s‖²`,

the paper's remark "`E(d) ≪ (d^{-1}RS + √(RS))‖α‖²`" in its usable asymmetric form. -/
theorem Evar_le_trivial (R S d : ℕ) (α : ℕ → ℕ → ℂ) (hd : 0 < d)
    (h : ∀ r s, α r s ≠ 0 → Nat.Coprime r d) :
    Work.FIPlan.Evar R S d α
      ≤ (4 * (R : ℝ) * S / d + 4 * (R : ℝ) + 4)
        * ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
            Complex.normSq (α r s) := by
  have _ := h
  have hmain := Evar_le_aux R S d α hd
  have hTnn : (0:ℝ) ≤ ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
      Complex.normSq (α r s) :=
    Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
  have hmono : 2 * (R : ℝ) * (2 * (S : ℝ) / (d : ℝ) + 1)
      ≤ 4 * (R : ℝ) * S / d + 4 * (R : ℝ) + 4 := by
    have hexp : 2 * (R : ℝ) * (2 * (S : ℝ) / (d : ℝ) + 1)
        = 4 * (R : ℝ) * S / d + 2 * (R : ℝ) := by
      ring
    rw [hexp]
    have h4 : 2 * (R : ℝ) ≤ 4 * (R : ℝ) + 4 := by
      have hR : (0:ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
      linarith
    linarith
  calc Work.FIPlan.Evar R S d α
      ≤ 2 * (R : ℝ) * (2 * (S : ℝ) / (d : ℝ) + 1)
          * ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
              Complex.normSq (α r s) := hmain
    _ ≤ (4 * (R : ℝ) * S / d + 4 * (R : ℝ) + 4)
          * ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
              Complex.normSq (α r s) :=
        mul_le_mul_of_nonneg_right hmono hTnn

end

end Work.FIArea4
