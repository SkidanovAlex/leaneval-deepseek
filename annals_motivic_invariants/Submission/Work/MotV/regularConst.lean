import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.Machinery
import Submission.Work.MotC2.Classification
import Submission.Work.MotV.regularConstAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

set_option linter.style.haveILetI false

namespace Work.MotV

noncomputable section

variable {N : Type*} [Field N] [IsAlgClosed N] [DecidableEq N]

/-- A constant has nonnegative order at every rational place: it lies in every place, and the
order of an element of a place is a natural number. -/
lemma le_ordOfPlace_algebraMap (E : WeierstrassCurve N) {S : Subalgebra N (MotC2.Func E)}
    (hS : MotC2.IsRatPlace E S) (c : N) :
    (0 : ℤ) ≤ ordOfPlace E S hS (algebraMap N (MotC2.Func E) c) := by
  unfold ordOfPlace
  rw [dite_eq_left (Subalgebra.algebraMap_mem S c)]
  exact Int.natCast_nonneg _

/-- The sum of the multiplicities of the roots of `p` over a finite set `S` containing all roots
of `p` is the degree of `p`.  Over an algebraically closed field every polynomial splits, so its
root multiset has `natDegree p` elements. -/
lemma rootsCount (p q : Polynomial N) (S : Finset N)
    (hp : p.roots.toFinset ⊆ S) (hq : q.roots.toFinset ⊆ S) :
    ∑ c ∈ S, (((p.roots.count c : ℕ) : ℤ) - ((q.roots.count c : ℕ) : ℤ))
      = ((p.natDegree : ℕ) : ℤ) - ((q.natDegree : ℕ) : ℤ) := by
  have hcountP : ∀ c, c ∉ p.roots.toFinset → p.roots.count c = 0 :=
    fun c hc => Multiset.count_eq_zero.mpr (fun hmem => hc (Multiset.mem_toFinset.mpr hmem))
  have hcountQ : ∀ c, c ∉ q.roots.toFinset → q.roots.count c = 0 :=
    fun c hc => Multiset.count_eq_zero.mpr (fun hmem => hc (Multiset.mem_toFinset.mpr hmem))
  have hsum_p : ∑ c ∈ S, ((p.roots.count c : ℕ) : ℤ) = ((p.natDegree : ℕ) : ℤ) := by
    conv_lhs => rw [← Finset.sum_subset hp (fun x _ hx => by rw [hcountP x hx]; rfl)]
    rw [← Nat.cast_sum, Multiset.toFinset_sum_count_eq (p.roots),
      (IsAlgClosed.splits p).natDegree_eq_card_roots]
  have hsum_q : ∑ c ∈ S, ((q.roots.count c : ℕ) : ℤ) = ((q.natDegree : ℕ) : ℤ) := by
    conv_lhs => rw [← Finset.sum_subset hq (fun x _ hx => by rw [hcountQ x hx]; rfl)]
    rw [← Nat.cast_sum, Multiset.toFinset_sum_count_eq (q.roots),
      (IsAlgClosed.splits q).natDegree_eq_card_roots]
  rw [Finset.sum_sub_distrib, hsum_p, hsum_q]

/-- The value of a function regular at the point at infinity: if `f` lies in the local ring
`infPlace E ⊆ N(E)` of the point at infinity then there is a constant `c : N` such that either
`f` *is* that constant, or `f - c` vanishes at infinity (has order at least one there).

Indeed `IsRatPlace` gives a bijection between `N` and the residue field `S ⧸ 𝔪` of the discrete
valuation ring `S = infPlace E`, realized by the constants; taking the preimage of the residue class
of `f` produces `c`, and `f - c ∈ 𝔪` is either zero or a non-unit, hence of order at least one. -/
lemma infValue (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) {f : MotC2.Func E}
    (hf : f ∈ MotC2.infPlace E) :
    ∃ c : N, f = algebraMap N (MotC2.Func E) c ∨
      1 ≤ ordOfPlace E (MotC2.infPlace E) H.infRat (f - algebraMap N (MotC2.Func E) c) := by
  obtain ⟨hDVR, hbij⟩ := H.infRat.1
  letI : IsDiscreteValuationRing ↥(MotC2.infPlace E) := hDVR
  obtain ⟨c, hc⟩ := hbij.2 (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(MotC2.infPlace E))
    (⟨f, hf⟩ : ↥(MotC2.infPlace E)))
  have hc' : Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(MotC2.infPlace E))
      (algebraMap N ↥(MotC2.infPlace E) c) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(MotC2.infPlace E))
        (⟨f, hf⟩ : ↥(MotC2.infPlace E)) := hc
  refine ⟨c, ?_⟩
  by_cases h : f = algebraMap N (MotC2.Func E) c
  · exact Or.inl h
  · right
    have hx : f - algebraMap N (MotC2.Func E) c ∈ MotC2.infPlace E :=
      Subalgebra.sub_mem _ hf (Subalgebra.algebraMap_mem _ c)
    have hx0 : f - algebraMap N (MotC2.Func E) c ≠ 0 := sub_ne_zero.mpr h
    have hmem : (⟨f, hf⟩ : ↥(MotC2.infPlace E)) - algebraMap N ↥(MotC2.infPlace E) c ∈
        IsLocalRing.maximalIdeal ↥(MotC2.infPlace E) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hc', sub_self]
    rw [one_le_ordOfPlace_iff H.infRat hx hx0]
    intro hunit
    exact (IsLocalRing.notMem_maximalIdeal.mpr hunit) hmem

/-- **No function regular everywhere has a positive order at infinity.**  A nonzero rational
function `f` on the elliptic curve which is regular at every rational place has nonpositive order
at the point at infinity: writing `f = a / b` with `a, b` in the affine coordinate ring, the fibre
sums of the orders give `mult_c (norm a) ≥ mult_c (norm b)` pointwise, hence
`deg (norm a) ≥ deg (norm b)`, while the order at infinity is `ord_∞ f = deg (norm b) -
deg (norm a)`. -/
lemma ordP_inf_le_zero (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (hFib : ∀ (a : CoordinateRing E), a ≠ 0 → ∀ c : N,
      ordSum E (fibrePlaces E c) (algebraMap (CoordinateRing E) (MotC2.Func E) a)
        = (((Algebra.norm (Polynomial N) a).roots.count c : ℕ) : ℤ))
    (hSupInf : ∀ (a : CoordinateRing E), a ≠ 0 →
      ordOfPlace E (MotC2.infPlace E) H.infRat
          (algebraMap (CoordinateRing E) (MotC2.Func E) a)
        = - ((Algebra.norm (Polynomial N) a).natDegree : ℤ))
    (f : MotC2.Func E) (hf : f ≠ 0) (hreg : ∀ Q : Place N E, 0 ≤ ordP E Q f) :
    ordP E ⟨MotC2.infPlace E, H.infRat⟩ f ≤ 0 := by
  obtain ⟨a, b, hb, hfeq⟩ := IsFractionRing.div_surjective (CoordinateRing E) f
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hB : algebraMap (CoordinateRing E) (MotC2.Func E) b ≠ 0 := fun h =>
    hb0 (IsFractionRing.injective (CoordinateRing E) (MotC2.Func E) (by simpa using h))
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hfeq
    exact hf hfeq.symm
  have hA : algebraMap (CoordinateRing E) (MotC2.Func E) a ≠ 0 := fun h =>
    ha0 (IsFractionRing.injective (CoordinateRing E) (MotC2.Func E) (by simpa using h))
  have hfeq' : f = algebraMap (CoordinateRing E) (MotC2.Func E) a *
      (algebraMap (CoordinateRing E) (MotC2.Func E) b)⁻¹ := by
    rw [← hfeq, div_eq_mul_inv]
  have hordQ : ∀ Q : Place N E, ordP E Q f =
      ordP E Q (algebraMap (CoordinateRing E) (MotC2.Func E) a) -
      ordP E Q (algebraMap (CoordinateRing E) (MotC2.Func E) b) := by
    intro Q
    simp only [ordP]
    rw [hfeq',
      H.ord_mul Q.1 Q.2 (algebraMap (CoordinateRing E) (MotC2.Func E) a)
        ((algebraMap (CoordinateRing E) (MotC2.Func E) b)⁻¹) hA (inv_ne_zero hB),
      H.ord_inv Q.1 Q.2 (algebraMap (CoordinateRing E) (MotC2.Func E) b) hB]
    first | refl_ring1 | ring
  have hfib : ∀ c₀ : N, ((Algebra.norm (Polynomial N) b).roots.count c₀ : ℤ) ≤
      ((Algebra.norm (Polynomial N) a).roots.count c₀ : ℤ) := by
    intro c₀
    have hsum : ordSum E (fibrePlaces E c₀) f =
        ordSum E (fibrePlaces E c₀) (algebraMap (CoordinateRing E) (MotC2.Func E) a) -
        ordSum E (fibrePlaces E c₀) (algebraMap (CoordinateRing E) (MotC2.Func E) b) := by
      simp only [ordSum]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun Q _ => hordQ Q)
    have hnn : (0 : ℤ) ≤ ordSum E (fibrePlaces E c₀) f :=
      Finset.sum_nonneg (fun Q _ => hreg Q)
    rw [hsum, hFib a ha0 c₀, hFib b hb0 c₀] at hnn
    omega
  set S : Finset N := (Algebra.norm (Polynomial N) a).roots.toFinset ∪
      (Algebra.norm (Polynomial N) b).roots.toFinset with hSdef
  have hsum_nonneg : (0 : ℤ) ≤ ∑ c₀ ∈ S,
      ((((Algebra.norm (Polynomial N) a).roots.count c₀ : ℕ) : ℤ) -
      (((Algebra.norm (Polynomial N) b).roots.count c₀ : ℕ) : ℤ)) := by
    refine Finset.sum_nonneg (fun c₀ _ => ?_)
    have := hfib c₀
    omega
  have hroots := rootsCount (Algebra.norm (Polynomial N) a) (Algebra.norm (Polynomial N) b) S
    (by rw [hSdef]; exact Finset.subset_union_left)
    (by rw [hSdef]; exact Finset.subset_union_right)
  rw [hroots] at hsum_nonneg
  have hdeg : ((Algebra.norm (Polynomial N) b).natDegree : ℤ) ≤
      ((Algebra.norm (Polynomial N) a).natDegree : ℤ) := by omega
  have hinf : ordP E ⟨MotC2.infPlace E, H.infRat⟩ f =
      ((Algebra.norm (Polynomial N) b).natDegree : ℤ) -
      ((Algebra.norm (Polynomial N) a).natDegree : ℤ) := by
    simp only [ordP]
    rw [hfeq',
      H.ord_mul (MotC2.infPlace E) H.infRat (algebraMap (CoordinateRing E) (MotC2.Func E) a)
        ((algebraMap (CoordinateRing E) (MotC2.Func E) b)⁻¹) hA (inv_ne_zero hB),
      H.ord_inv (MotC2.infPlace E) H.infRat (algebraMap (CoordinateRing E) (MotC2.Func E) b) hB,
      hSupInf a ha0, hSupInf b hb0]
    first | refl_ring1 | ring
  rw [hinf]
  omega

end

theorem regularConst {N : Type*} [Field N] [IsAlgClosed N] [DecidableEq N]
    (E : WeierstrassCurve N) [E.IsElliptic] (H : Work.MotV.H1Data N E)
    (hFib : ∀ (a : WeierstrassCurve.Affine.CoordinateRing E), a ≠ 0 → ∀ c : N,
      Work.MotV.ordSum E (Work.MotV.fibrePlaces E c)
          (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a)
        = (((Algebra.norm (Polynomial N) a).roots.count c : ℕ) : ℤ))
    (hSupInf : ∀ (a : WeierstrassCurve.Affine.CoordinateRing E), a ≠ 0 →
      Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) H.infRat
          (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a)
        = - ((Algebra.norm (Polynomial N) a).natDegree : ℤ))
    (f : Work.MotC2.Func E) (hf : f ≠ 0) (hreg : ∀ Q : Work.MotV.Place N E,
      0 ≤ Work.MotV.ordP E Q f) :
    ∃ c : N, algebraMap N (Work.MotC2.Func E) c = f := by
  have hfinf : f ∈ Work.MotC2.infPlace E :=
    (H.ord_nonneg (Work.MotC2.infPlace E) H.infRat f).mp
      (hreg ⟨Work.MotC2.infPlace E, H.infRat⟩)
  by_cases hconst : ∃ c : N, algebraMap N (Work.MotC2.Func E) c = f
  · exact hconst
  · push Not at hconst
    obtain ⟨c, hc | hc⟩ := infValue E H hfinf
    · exact absurd hc.symm (hconst c)
    · have hg0 : f - algebraMap N (Work.MotC2.Func E) c ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm (hconst c))
      have hreg' : ∀ Q : Work.MotV.Place N E,
          0 ≤ Work.MotV.ordP E Q (f - algebraMap N (Work.MotC2.Func E) c) := by
        intro Q
        have hsum_eq : f + -(algebraMap N (Work.MotC2.Func E) c) =
            f - algebraMap N (Work.MotC2.Func E) c := by ring
        have h1 := H.ord_add Q.1 Q.2 f (-(algebraMap N (Work.MotC2.Func E) c))
          (by rw [hsum_eq]; exact hg0)
        rw [hsum_eq] at h1
        have h3 : (0 : ℤ) ≤ Work.MotV.ordOfPlace E Q.1 Q.2 f := hreg Q
        have h2 : (0 : ℤ) ≤ Work.MotV.ordOfPlace E Q.1 Q.2
            (-(algebraMap N (Work.MotC2.Func E) c)) := by
          rw [← map_neg (algebraMap N (Work.MotC2.Func E)) c]
          exact le_ordOfPlace_algebraMap E Q.2 (-c)
        exact le_trans (le_min h3 h2) h1
      have hle := ordP_inf_le_zero E H hFib hSupInf
        (f - algebraMap N (Work.MotC2.Func E) c) hg0 hreg'
      have hle' : Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) H.infRat
          (f - algebraMap N (Work.MotC2.Func E) c) ≤ 0 := hle
      omega

end Work.MotV
