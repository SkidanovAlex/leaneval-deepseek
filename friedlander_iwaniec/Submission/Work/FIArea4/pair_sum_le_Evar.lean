/-
# The large-sieve step of *FI* §§11–12 and §15

For `1 ≤ d` and coefficient arrays `u, v` whose supports have first coordinate coprime to `d`,
the pair sum over the congruence `r₁s₂ ≡ r₂s₁ (mod d)` with the Jacobi weights `(r₁|d')(r₂|d')`
(`d' = oddPart d`) is bounded by the geometric mean of the two local variances `E(d)` of (11.7).

The proof is the class decomposition of the pair sum: assigning to a pair `(r,s)` the class
`a ≡ s·r⁻¹ (mod d)` (well defined because `r` is a unit modulo `d` on the support), the classes
`a` partition the box, and the condition `r₁s₂ ≡ r₂s₁` holds exactly when the two pairs lie in the
*same* class.  Hence the pair sum is `Σ_a X_a conj(Y_a)` with `X_a`, `Y_a` the class sums, which
are the summands of `Evar`; Cauchy–Schwarz finishes.

The auxiliary notions live in `Submission.Work.FIArea4.PairSumCommon`; `EvarR`, `EvarCls` and the
disjointness of the classes are from `Submission.Work.FIArea4.Evar_le_trivial`.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.PairSumCommon

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Cauchy–Schwarz for `Σ f a conj(g a)` -/

lemma pairSum_cauchy {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    ‖∑ a ∈ s, f a * star (g a)‖
      ≤ Real.sqrt (∑ a ∈ s, Complex.normSq (f a)) * Real.sqrt (∑ a ∈ s, Complex.normSq (g a)) := by
  have h1 : ‖∑ a ∈ s, f a * star (g a)‖ ≤ ∑ a ∈ s, ‖f a‖ * ‖g a‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun a _ => ?_))
    rw [norm_mul, norm_star]
  have h2 : (∑ a ∈ s, ‖f a‖ * ‖g a‖) ^ 2
      ≤ (∑ a ∈ s, ‖f a‖ ^ 2) * (∑ a ∈ s, ‖g a‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun a => ‖f a‖) (fun a => ‖g a‖)
  have hsq : ∀ h : ι → ℂ, (∑ a ∈ s, ‖h a‖ ^ 2) = ∑ a ∈ s, Complex.normSq (h a) :=
    fun h => Finset.sum_congr rfl (fun a _ => (Complex.normSq_eq_norm_sq _).symm)
  have hA : (0:ℝ) ≤ ∑ a ∈ s, ‖f a‖ * ‖g a‖ :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hB : (0:ℝ) ≤ ∑ a ∈ s, Complex.normSq (f a) :=
    Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)
  calc ‖∑ a ∈ s, f a * star (g a)‖ ≤ ∑ a ∈ s, ‖f a‖ * ‖g a‖ := h1
    _ = Real.sqrt ((∑ a ∈ s, ‖f a‖ * ‖g a‖) ^ 2) := (Real.sqrt_sq hA).symm
    _ ≤ Real.sqrt ((∑ a ∈ s, Complex.normSq (f a)) * (∑ a ∈ s, Complex.normSq (g a))) := by
        refine Real.sqrt_le_sqrt ?_
        rw [← hsq f, ← hsq g]
        exact h2
    _ = Real.sqrt (∑ a ∈ s, Complex.normSq (f a)) * Real.sqrt (∑ a ∈ s, Complex.normSq (g a)) :=
        Real.sqrt_mul hB _

/-! ### The classes `EvarCls` cover the box -/

/-- The residue classes `EvarCls R S d a` (`a < d`) cover the box `EvarR R d ×ˢ [1,2S]`: for `r`
coprime to `d` the congruence `s ≡ r a (mod d)` has the unique solution
`a ≡ s r⁻¹ (mod d)`.  The classes are pairwise disjoint by `pairwiseDisjoint_EvarCls`. -/
lemma EvarCls_cover (R S d : ℕ) (hd : 0 < d) :
    (Finset.range d).biUnion (EvarCls R S d) = EvarR R d ×ˢ Finset.Icc 1 (2 * S) := by
  have hne : NeZero d := ⟨hd.ne'⟩
  refine Subset.antisymm ?_ ?_
  · exact Finset.biUnion_subset.mpr (fun a _ => Finset.filter_subset _ _)
  · intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hpI, hcop⟩ := mem_EvarR.mp hp1
    rw [Finset.mem_biUnion]
    refine ⟨((p.2 : ZMod d) * ((p.1 : ZMod d))⁻¹).val, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    rw [mem_EvarCls]
    refine ⟨mem_EvarR.mpr ⟨hpI, hcop⟩, hp2, ?_⟩
    rw [ZMod.natCast_zmod_val, ← mul_assoc, mul_comm ((p.1 : ZMod d)) ((p.2 : ZMod d)),
      mul_assoc, ZMod.coe_mul_inv_eq_one p.1 hcop, mul_one]

/-- Two pairs of the box lie in the classes `a` and `b` exactly when the determinant congruence
`p₁q₂ ≡ q₁p₂ (mod d)` holds iff `a = b`: multiplication by the unit `p₁q₁` is injective modulo
`d`.  This is the identification of the pair-sum indicator with the class indicator. -/
lemma EvarCls_congr (R S d a b : ℕ) (ha : a < d) (hb : b < d) {p q : ℕ × ℕ}
    (hp : p ∈ EvarCls R S d a) (hq : q ∈ EvarCls R S d b) :
    (((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d)) ↔ a = b := by
  obtain ⟨hp1, -, hp2⟩ := mem_EvarCls.mp hp
  obtain ⟨hq1, -, hq2⟩ := mem_EvarCls.mp hq
  obtain ⟨-, hcop⟩ := mem_EvarR.mp hp1
  obtain ⟨-, hcoq⟩ := mem_EvarR.mp hq1
  have hup : IsUnit ((p.1 : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime p.1 d).mpr hcop
  have huq : IsUnit ((q.1 : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime q.1 d).mpr hcoq
  constructor
  · intro h
    have h' : (p.1 : ZMod d) * (q.2 : ZMod d) = (q.1 : ZMod d) * (p.2 : ZMod d) := by
      simpa only [Nat.cast_mul] using h
    rw [hq2, hp2] at h'
    have h2 : ((p.1 : ZMod d) * (q.1 : ZMod d)) * (b : ZMod d)
        = ((p.1 : ZMod d) * (q.1 : ZMod d)) * (a : ZMod d) := by
      have e1 : (p.1 : ZMod d) * (q.1 : ZMod d) * (b : ZMod d)
          = (p.1 : ZMod d) * ((q.1 : ZMod d) * (b : ZMod d)) := mul_assoc _ _ _
      have e2 : (q.1 : ZMod d) * ((p.1 : ZMod d) * (a : ZMod d))
          = (p.1 : ZMod d) * (q.1 : ZMod d) * (a : ZMod d) := by ring
      rw [e1, h', e2]
    have h3 : (b : ZMod d) = (a : ZMod d) := (hup.mul huq).mul_left_cancel h2
    have h4 : (a : ZMod d) = (b : ZMod d) := h3.symm
    have h5 := congrArg ZMod.val h4
    rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at h5
  · intro hab
    subst hab
    push_cast
    rw [hq2, hp2]
    ring

/-! ### `Evar` is the sum of the squared class sums -/

/-- `Evar` (11.7) as the sum over the residue classes `a < d` of the squared modulus of the class
sum `clsSum`: this is the identification of the summands of the local variance with the class
sums `X_a` of the large-sieve step. -/
lemma Evar_eq_sum_normSq_clsSum (R S d : ℕ) (α : ℕ → ℕ → ℂ) :
    Work.FIPlan.Evar R S d α = ∑ a ∈ Finset.range d, Complex.normSq (clsSum R S d α a) := by
  rw [Work.FIPlan.Evar]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  simp only [clsSum, jw, EvarCls, EvarR, sum_product_filter]

/-! ### The class decomposition of the pair sum -/

/-- **The class decomposition of the pair sum**: with `X_a = clsSum u a` and `Y_a = clsSum v a`
the class sums of the two coefficient arrays, the pair sum over `r₁s₂ ≡ r₂s₁ (mod d)` equals
`Σ_{a < d} X_a conj(Y_a)`.  The coprimality hypotheses on the supports remove the terms with `r`
not coprime to `d`, which are not represented in any class. -/
lemma pairSum_decomp (R S d : ℕ) (hd : 0 < d) (u v : ℕ → ℕ → ℂ)
    (hu : ∀ r s, u r s ≠ 0 → Nat.Coprime r d)
    (hv : ∀ r s, v r s ≠ 0 → Nat.Coprime r d) :
    pairSum R S d u v = ∑ a ∈ Finset.range d, clsSum R S d u a * star (clsSum R S d v a) := by
  have stepA : pairSum R S d u v
      = ∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
          ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
            pairTerm d u v (r1, s1) (r2, s2) := by
    simp only [pairSum, pairTerm]
    refine Finset.sum_congr rfl (fun r1 _ => ?_)
    refine Finset.sum_congr rfl (fun s1 _ => ?_)
    refine Finset.sum_congr rfl (fun r2 _ => ?_)
    refine Finset.sum_congr rfl (fun s2 _ => ?_)
    by_cases h : ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d)
    · rw [if_pos h, if_pos h]
      exact pairTerm_eq d u v r1 s1 r2 s2
    · rw [if_neg h, if_neg h]
  have stepA2 : (∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
          ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
            pairTerm d u v (r1, s1) (r2, s2))
      = ∑ p ∈ Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S),
          ∑ q ∈ Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S), pairTerm d u v p q := by
    refine (Finset.sum_product (Finset.Icc 1 (2*R)) (Finset.Icc 1 (2*S))
      (fun p : ℕ × ℕ => ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
        pairTerm d u v p (r2, s2))).symm.trans ?_
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact (Finset.sum_product (Finset.Icc 1 (2*R)) (Finset.Icc 1 (2*S))
      (fun q : ℕ × ℕ => pairTerm d u v p q)).symm
  have hERsub : EvarR R d ⊆ Finset.Icc 1 (2*R) := Finset.filter_subset _ _
  have stepB : (∑ p ∈ Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S),
          ∑ q ∈ Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S), pairTerm d u v p q)
      = ∑ p ∈ EvarR R d ×ˢ Finset.Icc 1 (2*S),
          ∑ q ∈ Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S), pairTerm d u v p q := by
    refine (Finset.sum_subset (Finset.product_subset_product hERsub (fun x hx => hx)) ?_).symm
    intro p hp hpE
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hnc : ¬ Nat.Coprime p.1 d :=
      fun hc => hpE (Finset.mem_product.mpr ⟨mem_EvarR.mpr ⟨hp1, hc⟩, hp2⟩)
    refine Finset.sum_eq_zero (fun q _ => ?_)
    have h0 : u p.1 p.2 = 0 := by by_contra hc; exact hnc (hu p.1 p.2 hc)
    by_cases hc : ((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d)
    · rw [pairTerm, if_pos hc, h0, zero_mul, zero_mul]
    · rw [pairTerm, if_neg hc]
  have stepB2 : (∑ p ∈ EvarR R d ×ˢ Finset.Icc 1 (2*S),
          ∑ q ∈ Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S), pairTerm d u v p q)
      = ∑ p ∈ EvarR R d ×ˢ Finset.Icc 1 (2*S),
          ∑ q ∈ EvarR R d ×ˢ Finset.Icc 1 (2*S), pairTerm d u v p q := by
    refine Finset.sum_congr rfl (fun p _ =>
      (Finset.sum_subset (Finset.product_subset_product hERsub (fun x hx => hx)) ?_).symm)
    intro q hq hqE
    rw [Finset.mem_product] at hq
    obtain ⟨hq1, hq2⟩ := hq
    have hnc : ¬ Nat.Coprime q.1 d :=
      fun hc => hqE (Finset.mem_product.mpr ⟨mem_EvarR.mpr ⟨hq1, hc⟩, hq2⟩)
    have h0 : v q.1 q.2 = 0 := by by_contra hc; exact hnc (hv q.1 q.2 hc)
    by_cases hc : ((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d)
    · rw [pairTerm, if_pos hc, h0, zero_mul, star_zero, mul_zero]
    · rw [pairTerm, if_neg hc]
  have hpart : ∀ F : ℕ × ℕ → ℂ,
      (∑ p ∈ EvarR R d ×ˢ Finset.Icc 1 (2*S), F p)
        = ∑ a ∈ Finset.range d, ∑ p ∈ EvarCls R S d a, F p := by
    intro F
    rw [← EvarCls_cover R S d hd]
    exact Finset.sum_biUnion (f := F) (pairwiseDisjoint_EvarCls R S d hd)
  have stepC : (∑ p ∈ EvarR R d ×ˢ Finset.Icc 1 (2*S),
          ∑ q ∈ EvarR R d ×ˢ Finset.Icc 1 (2*S), pairTerm d u v p q)
      = ∑ a ∈ Finset.range d, ∑ p ∈ EvarCls R S d a,
          ∑ b ∈ Finset.range d, ∑ q ∈ EvarCls R S d b,
            (if a = b then (u p.1 p.2 * jw d p.1) * star (v q.1 q.2 * jw d q.1) else 0) := by
    rw [hpart (fun p => ∑ q ∈ EvarR R d ×ˢ Finset.Icc 1 (2*S), pairTerm d u v p q)]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hpart (fun q => pairTerm d u v p q)]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have ha' : a < d := Finset.mem_range.mp ha
    have hb' : b < d := Finset.mem_range.mp hb
    have hc : (((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d)) ↔ a = b :=
      EvarCls_congr R S d a b ha' hb' hp hq
    by_cases hab : a = b
    · rw [pairTerm, if_pos (hc.mpr hab), if_pos hab]
    · rw [pairTerm, if_neg (fun h => hab (hc.mp h)), if_neg hab]
  have stepD : (∑ a ∈ Finset.range d, ∑ p ∈ EvarCls R S d a,
          ∑ b ∈ Finset.range d, ∑ q ∈ EvarCls R S d b,
            (if a = b then (u p.1 p.2 * jw d p.1) * star (v q.1 q.2 * jw d q.1) else 0))
      = ∑ a ∈ Finset.range d, ∑ p ∈ EvarCls R S d a, ∑ q ∈ EvarCls R S d a,
            (u p.1 p.2 * jw d p.1) * star (v q.1 q.2 * jw d q.1) := by
    refine Finset.sum_congr rfl (fun a ha => ?_)
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have ha' : a < d := Finset.mem_range.mp ha
    have h1 : ∀ b ∈ Finset.range d, b ≠ a →
        (∑ q ∈ EvarCls R S d b,
          (if a = b then (u p.1 p.2 * jw d p.1) * star (v q.1 q.2 * jw d q.1) else 0)) = 0 := by
      intro b _ hb
      refine Finset.sum_eq_zero (fun q _ => ?_)
      rw [if_neg (fun h : a = b => hb h.symm)]
    have h2 : a ∉ Finset.range d →
        (∑ q ∈ EvarCls R S d a,
          (if a = a then (u p.1 p.2 * jw d p.1) * star (v q.1 q.2 * jw d q.1) else 0)) = 0 :=
      fun hnot => absurd (Finset.mem_range.mpr ha') hnot
    rw [Finset.sum_eq_single a h1 h2]
    simp
  have stepE : (∑ a ∈ Finset.range d, ∑ p ∈ EvarCls R S d a, ∑ q ∈ EvarCls R S d a,
            (u p.1 p.2 * jw d p.1) * star (v q.1 q.2 * jw d q.1))
      = ∑ a ∈ Finset.range d, clsSum R S d u a * star (clsSum R S d v a) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_mul_sum]
    simp only [clsSum, star_sum]
  rw [stepA, stepA2, stepB, stepB2, stepC, stepD, stepE]

/-- **The large-sieve step of *FI* §§11–12 and §15.**  For `1 ≤ d`, coefficient arrays `u, v`
whose supports have `r` coprime to `d`, the pair sum over the congruence
`r₁s₂ ≡ r₂s₁ (mod d)` with the Jacobi weights `(r₁|d')(r₂|d')` (`d' = oddPart d`) is bounded by
the geometric mean of the two local variances `E(d)` of (11.7): grouping the pairs by the class
`a ≡ s r⁻¹ (mod d)` the pair sum is `Σ_a X_a conj(Y_a)` with `X_a = Σ_{r̄s≡a} u r s (r|d')` and
`Y_a = Σ_{r̄s≡a} v r s (r|d')`, so Cauchy–Schwarz gives
`|Σ_a X_a conj(Y_a)| ≤ (Σ_a |X_a|²)^{1/2}(Σ_a |Y_a|²)^{1/2}`. -/
theorem pair_sum_le_Evar (R S d : ℕ) (hd : 1 ≤ d) (u v : ℕ → ℕ → ℂ)
    (hu : ∀ r s, u r s ≠ 0 → Nat.Coprime r d)
    (hv : ∀ r s, v r s ≠ 0 → Nat.Coprime r d) :
    ‖∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
      ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
        (if ((r1*s2 : ℕ) : ZMod d) = ((r2*s1 : ℕ) : ZMod d) then
          u r1 s1 * star (v r2 s2) *
            ((jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
         else 0)‖
      ≤ Real.sqrt (Work.FIPlan.Evar R S d u) * Real.sqrt (Work.FIPlan.Evar R S d v) := by
  show ‖pairSum R S d u v‖
      ≤ Real.sqrt (Work.FIPlan.Evar R S d u) * Real.sqrt (Work.FIPlan.Evar R S d v)
  rw [pairSum_decomp R S d (by omega) u v hu hv, Evar_eq_sum_normSq_clsSum R S d u,
    Evar_eq_sum_normSq_clsSum R S d v]
  exact pairSum_cauchy (Finset.range d) (clsSum R S d u) (clsSum R S d v)

end

end Work.FIArea4
