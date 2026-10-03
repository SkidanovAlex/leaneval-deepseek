import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs
import Submission.Work.FIArea4.Vflip.count_coset_supp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The trivial bound for the dyadic dual variance `Wdyad`

`Work.FIArea4.Wdyad D R S γ` is the dual (large-sieve) form of the Jacobi-twisted variance over
the dyadic boxes `D < d ≤ 2D`, `R < r ≤ 2R`, `S < s ≤ 2S`:

`Wdyad D R S γ = Σ_{r,s} |Σ_{d,a} γ_{a d} M((d,a),(r,s))|²`,

where `M((d,a),(r,s)) = 1_{(r,d)=1} · 1_{s ≡ r a (d)} · (r | oddPart d)`.

This file proves the elementary "trivial" estimate

`Wdyad D R S γ ≤ C · (R S + D · min R S + D) · Σ_{d,a} ‖γ_{a d}‖²`,

with an explicit constant `C = 10`.  The proof is a two-step Cauchy–Schwarz (duality) argument:

* for fixed `d`, the map `γ ↦ (Σ_{d,a} γ M)_{(r,s)}` has classes indexed by `a < d` on which
  `M` is supported and which are pairwise disjoint (two classes meet only if `a = a'`), so the
  Cauchy–Schwarz inequality inside each class bounds the `a`-sum by `max_a #class(a) · ‖γ‖²`;
* the classes are precisely the pair sets counted by `Submission.Work.FIArea4.Vflip.count_coset_supp`,
  which gives `#class(a) ≤ 10 (RS/d + min R S + 1)`; summing over `d ∈ (D, 2D]` yields
  `Σ_d 10(RS/d + min R S + 1) ≤ 10 (RS + D min R S + D)`.

No analytic input (Poisson summation, character sums) is used — only finite Cauchy–Schwarz,
the disjointness of residue-class fibres, and a lattice-point count.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The class sum and the index set of pairs `(d,a)` -/

/-- `Ah D γ r s = Σ_{d ∈ (D,2D]} Σ_{a<d} γ a d · Mentry d a r s`, the class sum appearing
inside `Wdyad`. -/
def Ah (D : ℕ) (γ : ℕ → ℕ → ℂ) (r s : ℕ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, γ a d * Mentry d a r s

/-- The pairs `(d,a)` with `D < d ≤ 2D` and `a < d`, as a finset of `ℕ × ℕ`. -/
def pairIdx (D : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ioc D (2 * D)) ×ˢ Finset.range (2 * D)).filter (fun p => p.2 < p.1)

/-- Summation over `pairIdx D` is the nested sum `Σ_{d ∈ (D,2D]} Σ_{a<d}`. -/
lemma sum_pairIdx {M : Type*} [AddCommMonoid M] (D : ℕ) (F : ℕ → ℕ → M) :
    ∑ p ∈ pairIdx D, F p.1 p.2
      = ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, F d a := by
  unfold pairIdx
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, ha⟩; exact ha
  · intro ha
    exact ⟨by have := (Finset.mem_Ioc.mp hd).2; omega, ha⟩

/-! ## The residue-class fibres of the box -/

/-- The dyadic box `R < r ≤ 2R`, `S < s ≤ 2S`, as a finset of pairs. -/
def Wbox (R S : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc R (2 * R)) ×ˢ (Finset.Ioc S (2 * S))

/-- The class of pairs `(r,s)` of the box on which `Mentry d a r s` may be non-zero:
`(r,d) = 1` and `s ≡ r a (mod d)`. -/
def Wcls (R S d a : ℕ) : Finset (ℕ × ℕ) :=
  (Wbox R S).filter
    (fun p => Nat.Coprime p.1 d ∧ (p.2 : ZMod d) = (p.1 : ZMod d) * (a : ZMod d))

lemma mem_Wcls {R S d a : ℕ} {p : ℕ × ℕ} :
    p ∈ Wcls R S d a ↔ p.1 ∈ Finset.Ioc R (2 * R) ∧ p.2 ∈ Finset.Ioc S (2 * S) ∧
      Nat.Coprime p.1 d ∧ (p.2 : ZMod d) = (p.1 : ZMod d) * (a : ZMod d) := by
  simp only [Wcls, Wbox, Finset.mem_filter, Finset.mem_product]
  tauto

/-- `Mentry` has modulus at most `1`. -/
lemma normSq_Mentry_le_one (d a r s : ℕ) : Complex.normSq (Mentry d a r s) ≤ 1 := by
  unfold Mentry
  split_ifs with h
  · rcases jacobiSym.trichotomy (r : ℤ) (Work.FIPlan.oddPart d) with h0 | h0 | h0 <;>
      rw [h0] <;> simp
  · simp

/-- `Mentry` vanishes off the class of the pair. -/
lemma Mentry_eq_zero_of_not_mem (R S d a : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ Wbox R S) (h : p ∉ Wcls R S d a) : Mentry d a p.1 p.2 = 0 := by
  have hc : ¬ (Nat.Coprime p.1 d ∧ (p.2 : ZMod d) = (p.1 : ZMod d) * (a : ZMod d)) := by
    intro hcon
    exact h (Finset.mem_filter.mpr ⟨hp, hcon⟩)
  unfold Mentry
  rw [if_neg hc]

/-- Distinct classes are disjoint: a common pair has `r` invertible modulo `d`, so the
congruences `s ≡ r a` and `s ≡ r a'` force `a = a'`. -/
lemma Wcls_pairwiseDisjoint (R S d : ℕ) (_hd : 0 < d) :
    (↑(Finset.range d) : Set ℕ).PairwiseDisjoint (Wcls R S d) := by
  intro a ha b hb hab
  show Disjoint (Wcls R S d a) (Wcls R S d b)
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [mem_Wcls] at hp hq
  obtain ⟨-, -, hcop, hpa⟩ := hp
  obtain ⟨-, -, -, hpb⟩ := hq
  have hu : IsUnit ((p.1 : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime p.1 d).mpr hcop
  have hcong : (a : ZMod d) = (b : ZMod d) := by
    apply hu.mul_left_cancel
    rw [← hpa, ← hpb]
  have ha' : a < d := Finset.mem_range.mp ha
  have hb' : b < d := Finset.mem_range.mp hb
  have : a = b := by
    have h := (ZMod.natCast_eq_natCast_iff' a b d).mp hcong
    rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h
  exact hab this

/-- The classes partition the box, so a sum over the classes is bounded by the sum over the box. -/
lemma sum_Wcls_le (R S d : ℕ) (hd : 0 < d) (f : ℕ × ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∑ a ∈ Finset.range d, ∑ p ∈ Wcls R S d a, f p ≤ ∑ p ∈ Wbox R S, f p := by
  rw [← Finset.sum_biUnion (f := f) (Wcls_pairwiseDisjoint R S d hd)]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.biUnion_subset.mpr (fun a _ => Finset.filter_subset _ _)) (fun p _ _ => hf p)

/-! ## Elementary counting and Cauchy–Schwarz lemmas -/

/-- Cauchy–Schwarz for complex sums (cardinality form). -/
lemma normSq_sum_le_card_mul_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.normSq (∑ x ∈ s, f x) ≤ (s.card : ℝ) * ∑ x ∈ s, Complex.normSq (f x) := by
  rw [Complex.normSq_eq_norm_sq]
  calc ‖∑ x ∈ s, f x‖ ^ 2 ≤ (∑ x ∈ s, ‖f x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = (s.card : ℝ) * ∑ x ∈ s, Complex.normSq (f x) := by
        simp only [Complex.normSq_eq_norm_sq]

/-- Cauchy–Schwarz for complex sums (product form). -/
lemma normSq_sum_mul_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, f i * g i)
      ≤ (∑ i ∈ s, Complex.normSq (f i)) * (∑ i ∈ s, Complex.normSq (g i)) := by
  rw [Complex.normSq_eq_norm_sq]
  have h1 : ‖∑ i ∈ s, f i * g i‖ ≤ ∑ i ∈ s, ‖f i‖ * ‖g i‖ := by
    calc ‖∑ i ∈ s, f i * g i‖ ≤ ∑ i ∈ s, ‖f i * g i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖f i‖ * ‖g i‖ := by simp
  have h2 : (∑ i ∈ s, ‖f i‖ * ‖g i‖) ^ 2
      ≤ (∑ i ∈ s, ‖f i‖ ^ 2) * (∑ i ∈ s, ‖g i‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖f i‖) (fun i => ‖g i‖)
  calc ‖∑ i ∈ s, f i * g i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖ * ‖g i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i ∈ s, ‖f i‖ ^ 2) * (∑ i ∈ s, ‖g i‖ ^ 2) := h2
    _ = (∑ i ∈ s, Complex.normSq (f i)) * (∑ i ∈ s, Complex.normSq (g i)) := by
        simp only [Complex.normSq_eq_norm_sq]

/-- The class of pairs `(r,s)` of the box with `s ≡ r a (mod d)` has at most
`10 (RS/d + min R S + 1)` elements (imported lattice-point count). -/
lemma Wcls_card_le (R S d a : ℕ) (hR : 1 ≤ R) (hS : 1 ≤ S) (hd : 1 ≤ d) :
    (Wcls R S d a).card ≤ 10 * (R * S / d + min R S + 1) := by
  refine le_trans (Finset.card_le_card ?_)
    (Work.FIArea4.Vflip.count_coset_supp R S d a hR hS hd)
  intro p hp
  rw [mem_Wcls] at hp
  obtain ⟨hp1, hp2, -, hmod⟩ := hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp1, ?_⟩, ?_⟩
  · rw [Finset.mem_Ioc] at hp2 ⊢
    refine ⟨by have := Nat.div_le_self S 2; omega, ?_⟩
    have h : 2 * S ≤ 5 * S / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      omega
    omega
  · have h : (p.2 : ZMod d) = ((p.1 * a : ℕ) : ZMod d) := by
      rw [hmod, Nat.cast_mul]
    exact (ZMod.natCast_eq_natCast_iff' p.2 (p.1 * a) d).mp h

/-! ## The class bound for one modulus -/

/-- For a fixed modulus `d` the `a`-sum of squared class sums is bounded by
`K d · Σ_{r,s} ‖η r s‖²`, provided every class has at most `K d` elements. -/
lemma normSq_classsum_le (R S d : ℕ) (hd : 0 < d) (Kd : ℝ)
    (hKd : ∀ a ∈ Finset.range d, ((Wcls R S d a).card : ℝ) ≤ Kd) (η : ℕ × ℕ → ℂ) :
    ∑ a ∈ Finset.range d,
        Complex.normSq (∑ p ∈ Wbox R S, Mentry d a p.1 p.2 * η p)
      ≤ Kd * ∑ p ∈ Wbox R S, Complex.normSq (η p) := by
  have hKdnn : 0 ≤ Kd := by
    have h0 : 0 ∈ Finset.range d := Finset.mem_range.mpr hd
    have h1 := hKd 0 h0
    have h2 : (0 : ℝ) ≤ ((Wcls R S d 0).card : ℝ) := Nat.cast_nonneg _
    linarith
  have hper : ∀ a ∈ Finset.range d,
      Complex.normSq (∑ p ∈ Wbox R S, Mentry d a p.1 p.2 * η p)
        ≤ Kd * ∑ p ∈ Wcls R S d a, Complex.normSq (η p) := by
    intro a ha
    have hsub : Wcls R S d a ⊆ Wbox R S := Finset.filter_subset _ _
    have hzero : ∀ p ∈ Wbox R S, p ∉ Wcls R S d a → Mentry d a p.1 p.2 * η p = 0 := by
      intro p hp hp'
      rw [Mentry_eq_zero_of_not_mem R S d a hp hp', zero_mul]
    have hrew : ∑ p ∈ Wbox R S, Mentry d a p.1 p.2 * η p
        = ∑ p ∈ Wcls R S d a, Mentry d a p.1 p.2 * η p :=
      (Finset.sum_subset hsub hzero).symm
    rw [hrew]
    calc Complex.normSq (∑ p ∈ Wcls R S d a, Mentry d a p.1 p.2 * η p)
        ≤ ((Wcls R S d a).card : ℝ)
            * ∑ p ∈ Wcls R S d a, Complex.normSq (Mentry d a p.1 p.2 * η p) :=
          normSq_sum_le_card_mul_sum _ _
      _ ≤ ((Wcls R S d a).card : ℝ) * ∑ p ∈ Wcls R S d a, Complex.normSq (η p) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          refine Finset.sum_le_sum (fun p _ => ?_)
          rw [Complex.normSq_mul]
          calc Complex.normSq (Mentry d a p.1 p.2) * Complex.normSq (η p)
              ≤ 1 * Complex.normSq (η p) :=
                mul_le_mul_of_nonneg_right (normSq_Mentry_le_one d a p.1 p.2) (Complex.normSq_nonneg _)
            _ = Complex.normSq (η p) := one_mul _
      _ ≤ Kd * ∑ p ∈ Wcls R S d a, Complex.normSq (η p) :=
          mul_le_mul_of_nonneg_right (hKd a ha) (Finset.sum_nonneg (fun p _ => Complex.normSq_nonneg _))
  calc ∑ a ∈ Finset.range d, Complex.normSq (∑ p ∈ Wbox R S, Mentry d a p.1 p.2 * η p)
      ≤ ∑ a ∈ Finset.range d, Kd * ∑ p ∈ Wcls R S d a, Complex.normSq (η p) :=
        Finset.sum_le_sum hper
    _ = Kd * ∑ a ∈ Finset.range d, ∑ p ∈ Wcls R S d a, Complex.normSq (η p) := by
        rw [Finset.mul_sum]
    _ ≤ Kd * ∑ p ∈ Wbox R S, Complex.normSq (η p) :=
        mul_le_mul_of_nonneg_left
          (sum_Wcls_le R S d hd _ (fun p => Complex.normSq_nonneg _)) hKdnn

/-! ## The duality step -/

/-- **Trivial bound with an abstract class bound.**  If every class of every modulus
`d ∈ (D,2D]` has at most `K d` elements, then
`Wdyad D R S γ ≤ (Σ_{d} K d) · Σ_{d,a} ‖γ a d‖²`. -/
lemma Wdyad_le_class (D R S : ℕ) (hD : 1 ≤ D) (_hR : 1 ≤ R) (_hS : 1 ≤ S)
    (γ : ℕ → ℕ → ℂ) (K : ℕ → ℝ)
    (hK : ∀ d ∈ Finset.Ioc D (2 * D), ∀ a ∈ Finset.range d, ((Wcls R S d a).card : ℝ) ≤ K d) :
    Wdyad D R S γ ≤ (∑ d ∈ Finset.Ioc D (2 * D), K d) *
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
  set Sig : ℝ := ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)
    with hSig
  set NA : ℝ := ∑ p ∈ Wbox R S, Complex.normSq (Ah D γ p.1 p.2) with hNA
  set M : ℝ := ∑ d ∈ Finset.Ioc D (2 * D), K d with hM
  have hIocpos : ∀ d ∈ Finset.Ioc D (2 * D), 0 < d := by
    intro d hd
    have := (Finset.mem_Ioc.mp hd).1
    omega
  have hW : Wdyad D R S γ = NA := by
    rw [Wdyad, hNA, Wbox, Finset.sum_product]
    simp only [Ah]
  have hSig_nn : 0 ≤ Sig :=
    Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
  have hNA_nn : 0 ≤ NA := by
    rw [hNA]
    exact Finset.sum_nonneg (fun p _ => Complex.normSq_nonneg _)
  have hM_nn : 0 ≤ M := by
    rw [hM]
    refine Finset.sum_nonneg (fun d hd => ?_)
    have h0 : 0 ∈ Finset.range d := Finset.mem_range.mpr (hIocpos d hd)
    have h1 := hK d hd 0 h0
    have h2 : (0 : ℝ) ≤ ((Wcls R S d 0).card : ℝ) := Nat.cast_nonneg _
    linarith
  rcases eq_or_lt_of_le hNA_nn with hNA0 | hNApos
  · rw [hW, ← hNA0]
    exact mul_nonneg hM_nn hSig_nn
  · set η : ℕ × ℕ → ℂ := fun p => (starRingEnd ℂ) (Ah D γ p.1 p.2) with hη
    set Yq : ℕ × ℕ → ℂ := fun q => ∑ p ∈ Wbox R S, Mentry q.1 q.2 p.1 p.2 * η p with hYq
    have hηnorm : ∑ p ∈ Wbox R S, Complex.normSq (η p) = NA := by
      rw [hNA]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp only [hη, Complex.normSq_conj]
    have hcom : ((NA : ℝ) : ℂ) = ∑ p ∈ Wbox R S, Ah D γ p.1 p.2 * η p := by
      rw [hNA, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp only [hη]
      exact (Complex.mul_conj _).symm
    have hAh : ∀ p : ℕ × ℕ,
        Ah D γ p.1 p.2 = ∑ q ∈ pairIdx D, γ q.2 q.1 * Mentry q.1 q.2 p.1 p.2 := by
      intro p
      rw [Ah]
      exact (sum_pairIdx D (fun d a => γ a d * Mentry d a p.1 p.2)).symm
    have hfactor : ∑ p ∈ Wbox R S, Ah D γ p.1 p.2 * η p
        = ∑ q ∈ pairIdx D, γ q.2 q.1 * Yq q := by
      calc ∑ p ∈ Wbox R S, Ah D γ p.1 p.2 * η p
          = ∑ p ∈ Wbox R S,
              (∑ q ∈ pairIdx D, γ q.2 q.1 * Mentry q.1 q.2 p.1 p.2) * η p := by
            refine Finset.sum_congr rfl (fun p _ => ?_)
            rw [hAh p]
        _ = ∑ p ∈ Wbox R S, ∑ q ∈ pairIdx D,
              (γ q.2 q.1 * Mentry q.1 q.2 p.1 p.2) * η p := by
            refine Finset.sum_congr rfl (fun p _ => ?_)
            rw [Finset.sum_mul]
        _ = ∑ q ∈ pairIdx D, ∑ p ∈ Wbox R S,
              (γ q.2 q.1 * Mentry q.1 q.2 p.1 p.2) * η p := by
            rw [Finset.sum_comm]
        _ = ∑ q ∈ pairIdx D, γ q.2 q.1 * Yq q := by
            refine Finset.sum_congr rfl (fun q _ => ?_)
            rw [hYq, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun p _ => ?_)
            ring
    have hsig : ∑ q ∈ pairIdx D, Complex.normSq (γ q.2 q.1) = Sig := by
      rw [hSig]
      exact sum_pairIdx D (fun d a => Complex.normSq (γ a d))
    have hYsum : ∑ q ∈ pairIdx D, Complex.normSq (Yq q) ≤ M * NA := by
      have h1 : ∑ q ∈ pairIdx D, Complex.normSq (Yq q)
          = ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (Yq (d, a)) := by
        simpa using sum_pairIdx D (fun d a => Complex.normSq (Yq (d, a)))
      rw [h1]
      calc ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (Yq (d, a))
          ≤ ∑ d ∈ Finset.Ioc D (2 * D), K d * ∑ p ∈ Wbox R S, Complex.normSq (η p) := by
            refine Finset.sum_le_sum (fun d hd => ?_)
            simp only [hYq]
            exact normSq_classsum_le R S d (hIocpos d hd) (K d) (fun a ha => hK d hd a ha) η
        _ = M * ∑ p ∈ Wbox R S, Complex.normSq (η p) := by rw [hM, Finset.sum_mul]
        _ = M * NA := by rw [hηnorm]
    have hCS := normSq_sum_mul_le (pairIdx D) (fun q => γ q.2 q.1) (fun q => Yq q)
    have hval : Complex.normSq (∑ q ∈ pairIdx D, γ q.2 q.1 * Yq q) = NA ^ 2 := by
      rw [← hfactor, ← hcom, Complex.normSq_ofReal]
      ring
    rw [hval] at hCS
    rw [hsig] at hCS
    have hfin : NA ^ 2 ≤ NA * (M * Sig) := by
      calc NA ^ 2 ≤ Sig * ∑ q ∈ pairIdx D, Complex.normSq (Yq q) := hCS
        _ ≤ Sig * (M * NA) := mul_le_mul_of_nonneg_left hYsum hSig_nn
        _ = NA * (M * Sig) := by ring
    have hcancel : NA * NA ≤ NA * (M * Sig) := by nlinarith [hfin]
    have hle := le_of_mul_le_mul_left hcancel hNApos
    rw [hW]
    simpa only [hM, hSig] using hle

/-! ## Summing the class bound over the moduli -/

lemma sum_K_le (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (∑ d ∈ Finset.Ioc D (2 * D), ((10 * (R * S / d + min R S + 1) : ℕ) : ℝ))
      ≤ 10 * ((R : ℝ) * (S : ℝ) + (D : ℝ) * (min R S : ℝ) + (D : ℝ)) := by
  have hcard : (Finset.Ioc D (2 * D)).card = D := by rw [Nat.card_Ioc]; omega
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hmincast : ((min R S : ℕ) : ℝ) = (min R S : ℝ) := Nat.cast_min R S
  have hstep : ∀ d ∈ Finset.Ioc D (2 * D),
      ((10 * (R * S / d + min R S + 1) : ℕ) : ℝ)
        ≤ 10 * ((R : ℝ) * (S : ℝ) / (d : ℝ) + ((min R S : ℕ) : ℝ) + 1) := by
    intro d _
    have hcast : ((10 * (R * S / d + min R S + 1) : ℕ) : ℝ)
        = 10 * (((R * S / d : ℕ) : ℝ) + ((min R S : ℕ) : ℝ) + 1) := by push_cast; ring
    rw [hcast]
    have h1 : (((R * S / d : ℕ)) : ℝ) ≤ (R : ℝ) * (S : ℝ) / (d : ℝ) := by
      have := Nat.cast_div_le (α := ℝ) (m := R * S) (n := d)
      push_cast at this
      exact this
    linarith [h1, Nat.cast_nonneg (α := ℝ) (min R S)]
  have hdiv : ∑ d ∈ Finset.Ioc D (2 * D), (R : ℝ) * (S : ℝ) / (d : ℝ)
      ≤ (R : ℝ) * (S : ℝ) := by
    have hle : ∀ d ∈ Finset.Ioc D (2 * D),
        (R : ℝ) * (S : ℝ) / (d : ℝ) ≤ (R : ℝ) * (S : ℝ) / (D : ℝ) := by
      intro d hd
      have hdD : (D : ℝ) ≤ (d : ℝ) := by
        have := (Finset.mem_Ioc.mp hd).1
        exact_mod_cast (le_of_lt this)
      exact div_le_div_of_nonneg_left (by positivity) hDpos hdD
    calc ∑ d ∈ Finset.Ioc D (2 * D), (R : ℝ) * (S : ℝ) / (d : ℝ)
        ≤ ∑ _d ∈ Finset.Ioc D (2 * D), (R : ℝ) * (S : ℝ) / (D : ℝ) := Finset.sum_le_sum hle
      _ = (D : ℝ) * ((R : ℝ) * (S : ℝ) / (D : ℝ)) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ = (R : ℝ) * (S : ℝ) := by
          field_simp
  have hmin : ∑ _d ∈ Finset.Ioc D (2 * D), ((min R S : ℕ) : ℝ)
      = (D : ℝ) * ((min R S : ℕ) : ℝ) := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hone : ∑ _d ∈ Finset.Ioc D (2 * D), (1 : ℝ) = (D : ℝ) := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  calc ∑ d ∈ Finset.Ioc D (2 * D), ((10 * (R * S / d + min R S + 1) : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Ioc D (2 * D),
          10 * ((R : ℝ) * (S : ℝ) / (d : ℝ) + ((min R S : ℕ) : ℝ) + 1) := Finset.sum_le_sum hstep
    _ = 10 * ((∑ d ∈ Finset.Ioc D (2 * D), (R : ℝ) * (S : ℝ) / (d : ℝ))
            + (∑ _d ∈ Finset.Ioc D (2 * D), ((min R S : ℕ) : ℝ))
            + (∑ _d ∈ Finset.Ioc D (2 * D), (1 : ℝ))) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = 10 * ((∑ d ∈ Finset.Ioc D (2 * D), (R : ℝ) * (S : ℝ) / (d : ℝ))
            + (D : ℝ) * ((min R S : ℕ) : ℝ) + (D : ℝ)) := by rw [hmin, hone]
    _ = 10 * ((∑ d ∈ Finset.Ioc D (2 * D), (R : ℝ) * (S : ℝ) / (d : ℝ))
            + (D : ℝ) * (min R S : ℝ) + (D : ℝ)) := by rw [hmincast]
    _ ≤ 10 * ((R : ℝ) * (S : ℝ) + (D : ℝ) * (min R S : ℝ) + (D : ℝ)) := by
        linarith [hdiv]

/-! ## The trivial bound -/

theorem Wdyad_le_trivial :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      Work.FIArea4.Wdyad D R S γ ≤ C * ((R : ℝ) * (S : ℝ)
          + (D : ℝ) * (min R S : ℝ) + (D : ℝ))
        * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
  refine ⟨10, by norm_num, ?_⟩
  intro D R S γ hD hR hS
  have hKcls : ∀ d ∈ Finset.Ioc D (2 * D), ∀ a ∈ Finset.range d,
      ((Wcls R S d a).card : ℝ) ≤ ((10 * (R * S / d + min R S + 1) : ℕ) : ℝ) := by
    intro d hd a _
    have hd1 : 1 ≤ d := by have := (Finset.mem_Ioc.mp hd).1; omega
    have h := Wcls_card_le R S d a hR hS hd1
    exact_mod_cast h
  have h1 := Wdyad_le_class D R S hD hR hS γ
    (fun d => ((10 * (R * S / d + min R S + 1) : ℕ) : ℝ)) hKcls
  have h2 := sum_K_le D R S hD hR hS
  have hSig_nn : (0 : ℝ) ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      Complex.normSq (γ a d) :=
    Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
  calc Wdyad D R S γ
      ≤ (∑ d ∈ Finset.Ioc D (2 * D), ((10 * (R * S / d + min R S + 1) : ℕ) : ℝ)) *
          (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := h1
    _ ≤ (10 * ((R : ℝ) * (S : ℝ) + (D : ℝ) * (min R S : ℝ) + (D : ℝ))) *
          (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) :=
        mul_le_mul_of_nonneg_right h2 hSig_nn
    _ = 10 * ((R : ℝ) * (S : ℝ) + (D : ℝ) * (min R S : ℝ) + (D : ℝ))
          * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
        ring

end

end Work.FIArea4
