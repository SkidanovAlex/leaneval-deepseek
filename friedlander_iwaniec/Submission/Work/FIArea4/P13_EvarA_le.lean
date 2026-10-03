/-
# FI (13.3): monotonicity of the local variance under "enlarging the modulus"

The Friedlander–Iwaniec §13 argument ("enlarging moduli") rests on the *class-refinement*
monotonicity of the local variance (11.7): restricting the `r`-sum to `p ∤ r` and reducing the
modulus from `d p²` to `d` can only shrink the variance by the factor `p²`,

  `E_p(d) ≤ p² E(d p²)`   (FI (13.3)),

where `E_p(d)` is the `p ∤ r` part of `E(d)` (`Work.FIArea4.EvarA`) and `E(dp²)` is the full
local variance at the enlarged modulus `d p²` (`Work.FIPlan.Evar`).

The mechanism is the refinement of the residue-class partition of the box `[1,2R] × [1,2S]`:

* the class `a (mod d)` of a pair `(r,s)` with `p ∤ r` splits into the `p²` classes
  `b (mod d p²)` with `b ≡ a (mod d)`, namely `b ≡ s r⁻¹ (mod d p²)`;
* on these classes the Jacobi weight agrees: for `p ∤ r`, `oddPart (d p²) = oddPart d · oddPart p²`
  and `jacobiSym r (oddPart p²) = 1`, so `(r | oddPart (d p²)) = (r | oddPart d)`
  (the point of using the `p ∤ r` part);
* hence each class sum `X_a` of `E_p(d)` is the sum of the `p²` class sums `Y_b` of `E(dp²)`,
  and Cauchy–Schwarz in each class gives `|X_a|² ≤ p² Σ_{b ≡ a} |Y_b|²`.

Summing over `a < d` (the fibers `{b : b ≡ a (mod d)}` partition `range (d p²)`) yields the
claim.
-/
import Mathlib
import Submission.Work.FIArea4.P13Defs
import Submission.Work.FIArea4.PairSumCommon

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

set_option linter.style.haveILetI false

/-! ## The number-theoretic inputs -/

/-- `r` is coprime to `d p²` (for a prime `p`) exactly when it is coprime to `d` and `p ∤ r`. -/
lemma coprime_mul_prime_sq_iff (p : ℕ) (hp : p.Prime) (r d : ℕ) :
    Nat.Coprime r (d * p ^ 2) ↔ Nat.Coprime r d ∧ ¬ p ∣ r := by
  rw [Nat.coprime_mul_iff_right, Nat.coprime_pow_right_iff (by norm_num)]
  constructor
  · intro h; exact ⟨h.1, (hp.coprime_iff_not_dvd).mp h.2.symm⟩
  · intro h; exact ⟨h.1, (hp.coprime_iff_not_dvd).mpr h.2 |>.symm⟩

/-- `oddPart` is multiplicative. -/
lemma p13_oddPart_mul (a b : ℕ) :
    Work.FIPlan.oddPart (a * b) = Work.FIPlan.oddPart a * Work.FIPlan.oddPart b := by
  simp only [Work.FIPlan.oddPart]
  exact Nat.ordCompl_mul a b 2

lemma p13_oddPart_ne_zero {n : ℕ} (hn : n ≠ 0) : Work.FIPlan.oddPart n ≠ 0 := by
  simp only [Work.FIPlan.oddPart]
  exact (Nat.ordCompl_pos 2 hn).ne'

/-- `(r | oddPart (p²)) = 1` for `p` prime, `p ∤ r`: `oddPart (p²)` is `1` (for `p = 2`) or the
square `p²` (for `p` odd), and the Jacobi symbol on a square coprime to it is `1`. -/
lemma jacobiSym_oddPart_prime_sq (p r : ℕ) (hp : p.Prime) (hr : ¬ p ∣ r) :
    jacobiSym (r : ℤ) (Work.FIPlan.oddPart (p ^ 2)) = 1 := by
  rcases hp.eq_two_or_odd with h2 | hodd
  · subst h2
    have hf : ((2:ℕ)^2).factorization 2 = 2 := Nat.factorization_pow_self Nat.prime_two (n := 2)
    have ho : Work.FIPlan.oddPart ((2:ℕ)^2) = 1 := by
      rw [Work.FIPlan.oddPart, hf]; norm_num
    rw [ho, jacobiSym.one_right]
  · have hnot : ¬ 2 ∣ p ^ 2 := by
      intro hdvd
      have h1 : (p ^ 2) % 2 = 1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr hodd).pow)
      have h2 : (p ^ 2) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
      omega
    have hf : (p^2).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hnot
    have ho : Work.FIPlan.oddPart (p^2) = p^2 := by
      rw [Work.FIPlan.oddPart, hf]; simp
    rw [ho, jacobiSym.pow_right]
    have hnz : jacobiSym (r : ℤ) p ≠ 0 := by
      intro h0
      rw [jacobiSym.eq_zero_iff] at h0
      obtain ⟨-, hg⟩ := h0
      have hc : Nat.Coprime r p := (hp.coprime_iff_not_dvd).mpr hr |>.symm
      have hgcd : (r : ℤ).gcd (p : ℤ) = 1 := by
        rw [Int.gcd_natCast_natCast]; exact Nat.Coprime.gcd_eq_one hc
      exact hg hgcd
    rcases jacobiSym.trichotomy (r : ℤ) p with h | h | h
    · exact absurd h hnz
    · rw [h]; norm_num
    · rw [h]; norm_num

/-- **The class-refinement identity of the Jacobi weight**: for `p ∤ r`,
`(r | oddPart (d p²)) = (r | oddPart d)`. -/
lemma jw_prime_sq (p : ℕ) (hp : p.Prime) {d r : ℕ} (hd : 1 ≤ d) (hr : ¬ p ∣ r) :
    jw (d * p^2) r = jw d r := by
  unfold jw
  congr 1
  have hdne : d ≠ 0 := by omega
  haveI : NeZero (Work.FIPlan.oddPart d) := ⟨p13_oddPart_ne_zero hdne⟩
  haveI : NeZero (Work.FIPlan.oddPart (p^2)) := ⟨p13_oddPart_ne_zero (pow_ne_zero 2 hp.ne_zero)⟩
  rw [p13_oddPart_mul, jacobiSym.mul_right, jacobiSym_oddPart_prime_sq p r hp hr, mul_one]

/-! ## The refined classes -/

/-- The classes of `[1,2R] × [1,2S]` modulo `d p²` whose class `a (mod d)` is fixed. -/
def p13fib (d p a : ℕ) : Finset ℕ := (Finset.range (d * p^2)).filter (fun b => b % d = a)

/-- The class of the pair `q` modulo `M`, `b ≡ q.2 · q.1⁻¹ (mod M)`. -/
def p13idx (M : ℕ) (q : ℕ × ℕ) : ℕ := ((q.2 : ZMod M) * ((q.1 : ZMod M))⁻¹).val

/-- Mapping a pair of the `p ∤ r` part of the class `a (mod d)` to its class modulo `d p²`, the
value lies in `p13fib d p a` (modulus `d p²`, class `a` modulo `d`). -/
lemma p13idx_mem_fib (R S d p : ℕ) (hp : p.Prime) (hd : 1 ≤ d)
    (a : ℕ) (ha : a < d) (q : ℕ × ℕ)
    (hq : q ∈ (EvarCls R S d a).filter (fun q => ¬ p ∣ q.1)) :
    p13idx (d * p^2) q ∈ p13fib d p a := by
  obtain ⟨hqcls, hqnp⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqr, hqs, hqcond⟩ := mem_EvarCls.mp hqcls
  obtain ⟨-, hqcop⟩ := mem_EvarR.mp hqr
  have hMpos : 0 < d * p^2 := Nat.mul_pos (by omega) (pow_pos hp.pos 2)
  haveI : NeZero (d * p^2) := ⟨hMpos.ne'⟩
  rw [p13fib, Finset.mem_filter, Finset.mem_range]
  refine ⟨ZMod.val_lt _, ?_⟩
  have hmod1 : q.2 ≡ q.1 * a [MOD d] :=
    (ZMod.natCast_eq_natCast_iff q.2 (q.1 * a) d).mp (by rw [Nat.cast_mul]; exact hqcond)
  have hcopM : Nat.Coprime q.1 (d * p^2) :=
    (coprime_mul_prime_sq_iff p hp q.1 d).mpr ⟨hqcop, hqnp⟩
  set u := ((q.1 : ZMod (d * p^2))⁻¹).val with hu_def
  have hu : (u : ZMod (d * p^2)) = ((q.1 : ZMod (d * p^2)))⁻¹ := ZMod.natCast_zmod_val _
  have hprod : ((q.1 * u : ℕ) : ZMod (d * p^2)) = ((1 : ℕ) : ZMod (d * p^2)) := by
    rw [Nat.cast_mul, hu, ZMod.coe_mul_inv_eq_one q.1 hcopM, Nat.cast_one]
  have hmodprod : q.1 * u ≡ 1 [MOD d * p^2] :=
    (ZMod.natCast_eq_natCast_iff (q.1 * u) 1 (d * p^2)).mp hprod
  have hmodprodd : q.1 * u ≡ 1 [MOD d] :=
    Nat.ModEq.of_dvd (dvd_mul_right d (p^2)) hmodprod
  have hidx : p13idx (d * p^2) q ≡ q.2 * u [MOD d * p^2] := by
    apply (ZMod.natCast_eq_natCast_iff (p13idx (d*p^2) q) (q.2 * u) (d*p^2)).mp
    simp only [p13idx]
    rw [ZMod.natCast_zmod_val, Nat.cast_mul, hu]
  have hidxd : p13idx (d * p^2) q ≡ q.2 * u [MOD d] :=
    Nat.ModEq.of_dvd (dvd_mul_right d (p^2)) hidx
  have hstep : q.2 * u ≡ a [MOD d] := by
    have h3 : a * (q.1 * u) ≡ a * 1 [MOD d] := hmodprodd.mul_left a
    have heq : (q.1 * a) * u = a * (q.1 * u) := by ring
    have h2 : (q.1 * a) * u ≡ a [MOD d] := by rw [heq]; simpa using h3
    exact (hmod1.mul_right u).trans h2
  have hfinal := hidxd.trans hstep
  change p13idx (d * p^2) q % d = a % d at hfinal
  rwa [Nat.mod_eq_of_lt (by omega : a < d)] at hfinal

/-- The fiber of `p13idx` over `b` is exactly the class of `b` modulo `d p²`: the congruence
`s ≡ r b (mod d p²)` determines `b ≡ s r⁻¹ (mod d p²)` uniquely. -/
lemma p13idx_filter_eq (R S d p : ℕ) (hp : p.Prime) (hd : 1 ≤ d)
    (a b : ℕ) (ha : a < d) (hb : b ∈ p13fib d p a) :
    ((EvarCls R S d a).filter (fun q => ¬ p ∣ q.1)).filter (fun q => p13idx (d * p^2) q = b)
      = EvarCls R S (d * p^2) b := by
  rw [p13fib, Finset.mem_filter, Finset.mem_range] at hb
  obtain ⟨hb_lt, hb_mod⟩ := hb
  have hMpos : 0 < d * p^2 := Nat.mul_pos (by omega) (pow_pos hp.pos 2)
  haveI : NeZero (d * p^2) := ⟨hMpos.ne'⟩
  ext q
  constructor
  · intro h
    have h1 := (Finset.mem_filter.mp h).1
    have hidx := (Finset.mem_filter.mp h).2
    have hqcls := (Finset.mem_filter.mp h1).1
    have hqnp := (Finset.mem_filter.mp h1).2
    rw [mem_EvarCls] at hqcls
    obtain ⟨hqr, hqs, hqcond⟩ := hqcls
    rw [mem_EvarR] at hqr
    obtain ⟨hqI, hqcop⟩ := hqr
    have hcopM : Nat.Coprime q.1 (d * p^2) :=
      (coprime_mul_prime_sq_iff p hp q.1 d).mpr ⟨hqcop, hqnp⟩
    refine mem_EvarCls.mpr ⟨mem_EvarR.mpr ⟨hqI, hcopM⟩, hqs, ?_⟩
    have hbb : (b : ZMod (d*p^2)) = (q.2 : ZMod (d*p^2)) * ((q.1 : ZMod (d*p^2)))⁻¹ := by
      rw [← hidx]; simp only [p13idx, ZMod.natCast_zmod_val]
    rw [hbb]
    calc (q.2 : ZMod (d*p^2))
        = (q.2 : ZMod (d*p^2)) * 1 := (mul_one _).symm
      _ = (q.2 : ZMod (d*p^2)) * ((q.1:ZMod (d*p^2)) * (q.1:ZMod (d*p^2))⁻¹) := by
            rw [ZMod.coe_mul_inv_eq_one q.1 hcopM]
      _ = (q.1 : ZMod (d*p^2)) * ((q.2 : ZMod (d*p^2)) * (q.1 : ZMod (d*p^2))⁻¹) := by ring
  · intro h
    rw [mem_EvarCls, mem_EvarR] at h
    obtain ⟨⟨hqI, hqcopM⟩, hqs, hqcond⟩ := h
    obtain ⟨hqcopd, hqnp⟩ := (coprime_mul_prime_sq_iff p hp q.1 d).mp hqcopM
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨mem_EvarCls.mpr ⟨mem_EvarR.mpr ⟨hqI, hqcopd⟩, hqs, ?_⟩, hqnp⟩, ?_⟩
    · have h1 : (q.2 : ZMod d) = ((q.1 * b : ℕ) : ZMod d) := by
        apply (ZMod.natCast_eq_natCast_iff q.2 (q.1*b) d).mpr
        exact Nat.ModEq.of_dvd (dvd_mul_right d (p^2))
          ((ZMod.natCast_eq_natCast_iff q.2 (q.1*b) (d*p^2)).mp
            (by rw [Nat.cast_mul]; exact hqcond))
      rw [h1, Nat.cast_mul,
        show ((b:ℕ):ZMod d) = ((a:ℕ):ZMod d) from
          (ZMod.natCast_eq_natCast_iff b a d).mpr
            (by change b % d = a % d; rw [hb_mod, Nat.mod_eq_of_lt ha])]
    · have h2 : (q.2 : ZMod (d*p^2)) * ((q.1 : ZMod (d*p^2)))⁻¹ = (b : ZMod (d*p^2)) := by
        rw [hqcond]
        calc (q.1 : ZMod (d*p^2)) * (b : ZMod (d*p^2)) * ((q.1 : ZMod (d*p^2)))⁻¹
            = (b : ZMod (d*p^2)) * ((q.1 : ZMod (d*p^2)) * ((q.1 : ZMod (d*p^2)))⁻¹) := by ring
          _ = (b : ZMod (d*p^2)) := by rw [ZMod.coe_mul_inv_eq_one q.1 hqcopM, mul_one]
      simp only [p13idx, h2, ZMod.val_natCast, Nat.mod_eq_of_lt hb_lt]

/-! ## The class sum as a sum over the pair set `EvarCls` -/

/-- The class sum `EvarClsSum` of (11.7) written as a sum over the pair set `EvarCls`. -/
def clsSumSel (R S d : ℕ) (α : ℕ → ℕ → ℂ) (sel : ℕ → Prop) [DecidablePred sel] (a : ℕ) : ℂ :=
  ∑ q ∈ (EvarCls R S d a).filter (fun q => sel q.1), α q.1 q.2 * jw d q.1

lemma EvarClsSum_eq_clsSumSel (R S d : ℕ) (α : ℕ → ℕ → ℂ) (sel : ℕ → Prop) [DecidablePred sel]
    (a : ℕ) :
    EvarClsSum R S d α sel a = clsSumSel R S d α sel a := by
  conv_lhs => unfold EvarClsSum
  conv_rhs => rw [clsSumSel, EvarCls, EvarR, Finset.filter_filter, sum_product_filter,
      Finset.sum_filter]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases hc : Nat.Coprime r d
  · by_cases hs : sel r
    · rw [if_pos ⟨hc, hs⟩, if_pos hc]
      refine Finset.sum_congr ?_ (fun s _ => by simp only [jw])
      ext s; simp only [Finset.mem_filter, hs, and_true]
    · rw [if_neg (by tauto : ¬ (Nat.Coprime r d ∧ sel r)), if_pos hc]
      exact (Finset.sum_eq_zero (fun s hs' => absurd (Finset.mem_filter.mp hs').2.2 hs)).symm
  · rw [if_neg (fun h => hc h.1), if_neg hc]

/-! ## The fibers are the classes of the enlarged modulus -/

lemma p13fib_card_le (d p a : ℕ) (hd : 1 ≤ d) (ha : a < d) :
    (p13fib d p a).card ≤ p^2 := by
  have hpos : 0 < d := by omega
  have heq : p13fib d p a = (Finset.range (p^2)).image (fun c => d * c + a) := by
    ext b
    rw [p13fib, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · intro ⟨hb, hbmod⟩
      refine ⟨b / d, ?_, ?_⟩
      · rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hpos]
        calc b < d * p^2 := hb
          _ = p^2 * d := by ring
      · have h := Nat.div_add_mod b d
        rw [hbmod] at h
        omega
    · rintro ⟨c, hc, rfl⟩
      rw [Finset.mem_range] at hc
      refine ⟨?_, ?_⟩
      · have h1 : d * c + a < d * c + d := by omega
        have h2 : d * c + d = d * (c + 1) := by ring
        have h3 : d * (c + 1) ≤ d * p^2 := Nat.mul_le_mul_left d (by omega)
        omega
      · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  rw [heq, Finset.card_image_of_injective _ (fun x y hxy => ?_)]
  · simp
  · exact Nat.mul_left_cancel hpos (Nat.add_right_cancel hxy)

/-- **FI (13.3), class form**: the class sum of the `p ∤ r` part at modulus `d` is the sum of the
class sums at modulus `d p²` over the `p²` classes refining it. -/
lemma p13_refine (R S d p : ℕ) (α : ℕ → ℕ → ℂ) (hp : p.Prime) (hd : 1 ≤ d)
    (a : ℕ) (ha : a < d) :
    EvarClsSum R S d α (fun r => ¬ p ∣ r) a
      = ∑ b ∈ p13fib d p a, EvarClsSum R S (d * p^2) α (fun _ => True) b := by
  rw [EvarClsSum_eq_clsSumSel]
  have hrhs : (∑ b ∈ p13fib d p a, EvarClsSum R S (d * p^2) α (fun _ => True) b)
      = ∑ b ∈ p13fib d p a, clsSumSel R S (d * p^2) α (fun _ => True) b :=
    Finset.sum_congr rfl (fun b _ =>
      (EvarClsSum_eq_clsSumSel R S (d*p^2) α (fun _ => True) b))
  rw [hrhs]
  simp only [clsSumSel]
  have hfw := Finset.sum_fiberwise_of_maps_to
    (s := (EvarCls R S d a).filter (fun q => ¬ p ∣ q.1)) (t := p13fib d p a)
    (g := p13idx (d*p^2)) (p13idx_mem_fib R S d p hp hd a ha)
    (f := fun q => α q.1 q.2 * jw d q.1)
  rw [← hfw]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [p13idx_filter_eq R S d p hp hd a b ha hb]
  simp only [Finset.filter_true]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hqcopM : Nat.Coprime q.1 (d*p^2) := (mem_EvarR.mp (mem_EvarCls.mp hq).1).2
  have hqnp : ¬ p ∣ q.1 := ((coprime_mul_prime_sq_iff p hp q.1 d).mp hqcopM).2
  rw [jw_prime_sq p hp hd hqnp]

/-! ## The main estimate -/

/-- **FI (13.3)**: the `p ∤ r` part of the local variance at modulus `d` is at most `p²` times the
local variance at the enlarged modulus `d p²`. -/
theorem P13_EvarA_le (R S d p : ℕ) (α : ℕ → ℕ → ℂ) (hp : p.Prime) (hd : 1 ≤ d) :
    EvarA R S d p α ≤ (p : ℝ) ^ 2 * Work.FIPlan.Evar R S (d * p ^ 2) α := by
  have hstep : ∀ a ∈ Finset.range d,
      Complex.normSq (EvarClsSum R S d α (fun r => ¬ p ∣ r) a)
        ≤ (p : ℝ)^2 * ∑ b ∈ p13fib d p a,
            Complex.normSq (EvarClsSum R S (d*p^2) α (fun _ => True) b) := by
    intro a ha
    rw [p13_refine R S d p α hp hd a (Finset.mem_range.mp ha)]
    refine le_trans (normSq_sum_le_card_mul_sum _ _) ?_
    have hcard : ((p13fib d p a).card : ℝ) ≤ (p : ℝ)^2 := by
      have := p13fib_card_le d p a hd (Finset.mem_range.mp ha)
      exact_mod_cast this
    have hnn : 0 ≤ ∑ b ∈ p13fib d p a,
        Complex.normSq (EvarClsSum R S (d*p^2) α (fun _ => True) b) :=
      Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg _)
    exact mul_le_mul_of_nonneg_right hcard hnn
  calc EvarA R S d p α
      = ∑ a ∈ Finset.range d,
          Complex.normSq (EvarClsSum R S d α (fun r => ¬ p ∣ r) a) := rfl
    _ ≤ ∑ a ∈ Finset.range d, (p:ℝ)^2 * ∑ b ∈ p13fib d p a,
          Complex.normSq (EvarClsSum R S (d*p^2) α (fun _ => True) b) :=
        Finset.sum_le_sum hstep
    _ = (p:ℝ)^2 * ∑ a ∈ Finset.range d, ∑ b ∈ p13fib d p a,
          Complex.normSq (EvarClsSum R S (d*p^2) α (fun _ => True) b) := by
        rw [Finset.mul_sum]
    _ = (p:ℝ)^2 * ∑ b ∈ Finset.range (d*p^2),
          Complex.normSq (EvarClsSum R S (d*p^2) α (fun _ => True) b) := by
        congr 1
        have hmap : ∀ b ∈ Finset.range (d*p^2), b % d ∈ Finset.range d := by
          intro b hb
          rw [Finset.mem_range] at hb ⊢
          exact Nat.mod_lt _ (by omega)
        have hfw := Finset.sum_fiberwise_of_maps_to (s := Finset.range (d*p^2))
          (t := Finset.range d) (g := fun b => b % d) hmap
          (f := fun b => Complex.normSq (EvarClsSum R S (d*p^2) α (fun _ => True) b))
        conv_rhs => rw [← hfw]
        rfl
    _ = (p:ℝ)^2 * Work.FIPlan.Evar R S (d * p^2) α := by
        rw [Evar_eq_sum_clsSum_true]

end

end Work.FIArea4
