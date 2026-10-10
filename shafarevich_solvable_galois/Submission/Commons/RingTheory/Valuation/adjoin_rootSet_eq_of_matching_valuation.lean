import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.FieldTheory.Polynomial.separable_of_natDegree_le_card_rootSet
import Submission.Commons.RingTheory.Valuation.krasner_valuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Roots of `δ`-matching separable polynomials generate the same field

Let `F` be a field with a Henselian valuation subring `V`, let `L` be an algebraically closed
algebraic extension of `F` and let `W` be an extension of `V` to `L` (it is automatically the
unique one).  For monic `f₁, f₂ ∈ F[X]` with `f₁` separable, `deg f₂ ≤ deg f₁`, and a value
`δ > 0` separating the distinct roots of `f₁` in `L`, suppose that *every* root of `f₁` is
`δ`-close to a root of `f₂`.  Then the roots of `f₁` and of `f₂` generate the same subfield of
`L` over `F`.

The proof is Krasner's lemma in both directions (`krasner_valuation`).

* The matching hypothesis makes the assignment "root of `f₁` ↦ nearby root of `f₂`" injective:
  two roots of `f₁` matched to the same root of `f₂` would be at distance `< δ` from each other,
  contradicting the separation hypothesis by the ultrametric inequality.  Hence `f₂` has at least
  `deg f₁` distinct roots, so `deg f₂ = deg f₁` and `f₂` is separable, and the matching is a
  bijection.
* Each root of `f₂` is closer to its matched root of `f₁` than to any other root of `f₂`
  (again ultrametricity), so Krasner applies in the reverse direction as well.
-/

open Polynomial IntermediateField

namespace Commons.RingTheory.Valuation

set_option linter.style.haveILetI false

/-- **Ultrametric injectivity.**  If `a` and `b` are `δ`-separated and both lie at distance
`< δ` from `p`, then `a = b`.  (Two distinct points cannot both be closer to `p` than the
separation radius.) -/
private lemma valuation_eq_of_close {L : Type*} [Field L] (W : ValuationSubring L) {a b p : L}
    {δ : W.ValueGroup} (hδ : δ ≤ W.valuation (a - b)) (h1 : W.valuation (a - p) < δ)
    (h2 : W.valuation (b - p) < δ) : a = b := by
  by_contra hne
  have : W.valuation (a - b) < δ := by
    have hkey : a - b = (a - p) - (b - p) := by ring
    rw [hkey]
    calc W.valuation ((a - p) - (b - p))
        ≤ max (W.valuation (a - p)) (W.valuation (b - p)) := Valuation.map_sub _ _ _
      _ < δ := max_lt h1 h2
  exact (not_lt_of_ge hδ) this

/-- **Ultrametric isometry.**  If `a` and `b` are `δ`-separated, `a` is `< δ`-close to `p` and
`b` is `< δ`-close to `q`, then `p` and `q` are exactly as far apart as `a` and `b`. -/
private lemma valuation_sub_eq_of_close {L : Type*} [Field L] (W : ValuationSubring L)
    {a b p q : L} {δ : W.ValueGroup} (hδ : δ ≤ W.valuation (a - b))
    (h1 : W.valuation (a - p) < δ) (h2 : W.valuation (b - q) < δ) :
    W.valuation (p - q) = W.valuation (a - b) := by
  have hkey : p - q = (a - b) - ((a - p) - (b - q)) := by ring
  rw [hkey]
  refine Valuation.map_sub_eq_of_lt_left (v := W.valuation) (x := a - b)
    (y := (a - p) - (b - q)) ?_
  calc W.valuation ((a - p) - (b - q))
      ≤ max (W.valuation (a - p)) (W.valuation (b - q)) := Valuation.map_sub _ _ _
    _ < δ := max_lt h1 h2
    _ ≤ W.valuation (a - b) := hδ

theorem adjoin_rootSet_eq_of_matching_valuation {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed L] [Algebra.IsAlgebraic F L] (V : ValuationSubring F) [HenselianLocalRing V] (W : ValuationSubring L) (hW : W.comap (algebraMap F L) = V) {f₁ f₂ : Polynomial F} (h₁m : f₁.Monic) (h₁sep : f₁.Separable) (h₂m : f₂.Monic) (hdeg : f₂.natDegree ≤ f₁.natDegree) {δ : W.ValueGroup} (hδ0 : 0 < δ) (hδsep : ∀ γ ∈ f₁.rootSet L, ∀ γ' ∈ f₁.rootSet L, γ ≠ γ' → δ ≤ W.valuation (γ - γ')) (hmatch : ∀ α ∈ f₁.rootSet L, ∃ β ∈ f₂.rootSet L, W.valuation (α - β) < δ) : IntermediateField.adjoin F (f₁.rootSet L) = IntermediateField.adjoin F (f₂.rootSet L) := by
  classical
  -- the matching assignment, root of `f₁` ↦ nearby root of `f₂`
  let φ : f₁.rootSet L → f₂.rootSet L :=
    fun a => ⟨(hmatch a a.2).choose, (hmatch a a.2).choose_spec.1⟩
  have hφ : ∀ a : f₁.rootSet L, W.valuation ((a : L) - (φ a : L)) < δ :=
    fun a => (hmatch a a.2).choose_spec.2
  have hφinj : Function.Injective φ := by
    intro a b hab
    by_contra hne
    have hne' : (a : L) ≠ (b : L) := fun h => hne (Subtype.ext h)
    exact hne' (valuation_eq_of_close W (hδsep (a : L) a.2 (b : L) b.2 hne') (hφ a)
      (by rw [hab]; exact hφ b))
  have hcard1 : Fintype.card (f₁.rootSet L) = f₁.natDegree :=
    Polynomial.card_rootSet_eq_natDegree (K := L) h₁sep
      (IsAlgClosed.splits (f₁.map (algebraMap F L)))
  have hcard2le : Fintype.card (f₂.rootSet L) ≤ f₂.natDegree := by
    rw [Set.fintypeCard_eq_ncard]
    exact Polynomial.ncard_rootSet_le f₂ L
  have hcard2 : Fintype.card (f₂.rootSet L) = f₁.natDegree := by
    have h1 := Fintype.card_le_of_injective φ hφinj
    rw [hcard1] at h1
    omega
  have hf₂sep : f₂.Separable := by
    refine Commons.FieldTheory.Polynomial.separable_of_natDegree_le_card_rootSet
      (K := L) (f := f₂) h₂m.ne_zero
      (IsAlgClosed.splits (f₂.map (algebraMap F L))) ?_
    have hc : Fintype.card ↑((f₂.map (algebraMap F L)).rootSet L) =
        Fintype.card ↑(f₂.rootSet L) := by
      rw [Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard,
        Commons.FieldTheory.Polynomial.rootSet_map_eq]
    rw [hc, hcard2]
    exact hdeg
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφinj, by rw [hcard1, hcard2]⟩
  -- forward inclusion: roots of `f₁` lie in the field generated by the roots of `f₂`
  have hFE : IntermediateField.adjoin F (f₁.rootSet L) ≤
      IntermediateField.adjoin F (f₂.rootSet L) := by
    rw [IntermediateField.adjoin_le_iff]
    intro α hα
    have hαroot : (Polynomial.aeval α) f₁ = 0 := Polynomial.aeval_eq_zero_of_mem_rootSet hα
    have hdvd : minpoly F α ∣ f₁ := minpoly.dvd F α hαroot
    have hsepα : IsSeparable F α := Polynomial.Separable.of_dvd h₁sep hdvd
    have hβint : IsIntegral F (φ ⟨α, hα⟩ : L) :=
      ⟨f₂, h₂m, Polynomial.aeval_eq_zero_of_mem_rootSet (φ ⟨α, hα⟩).2⟩
    have hclose : ∀ α' : L, IsConjRoot F α α' → α ≠ α' →
        W.valuation (α - (φ ⟨α, hα⟩ : L)) < W.valuation (α - α') := by
      intro α' hconj hne
      -- conjugates of `α` over `F` are roots of `f₁`, hence `δ`-separated from `α`
      have hα' : α' ∈ f₁.rootSet L := by
        rw [Polynomial.mem_rootSet]
        refine ⟨h₁m.ne_zero, ?_⟩
        obtain ⟨g, hg⟩ := hdvd
        rw [hg, map_mul]
        have hz : (Polynomial.aeval α') (minpoly F α) = 0 := by
          rw [hconj]; exact minpoly.aeval F α'
        rw [hz, zero_mul]
      have hδ : δ ≤ W.valuation (α - α') := by
        have h := hδsep α' hα' α hα (Ne.symm hne)
        rwa [Valuation.map_sub_swap W.valuation α' α] at h
      exact lt_of_lt_of_le (hφ ⟨α, hα⟩) hδ
    have hres := krasner_valuation V W hW hsepα hβint hclose
    exact (IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr
        (IntermediateField.subset_adjoin F (f₂.rootSet L) (φ ⟨α, hα⟩).2))) hres
  -- reverse inclusion: roots of `f₂` lie in the field generated by the roots of `f₁`
  have hEF : IntermediateField.adjoin F (f₂.rootSet L) ≤
      IntermediateField.adjoin F (f₁.rootSet L) := by
    rw [IntermediateField.adjoin_le_iff]
    intro β hβ
    obtain ⟨a, ha⟩ := hbij.2 ⟨β, hβ⟩
    have haval : (φ a : L) = β := congrArg Subtype.val ha
    have hβroot : (Polynomial.aeval β) f₂ = 0 := Polynomial.aeval_eq_zero_of_mem_rootSet hβ
    have hdvd : minpoly F β ∣ f₂ := minpoly.dvd F β hβroot
    have hsepβ : IsSeparable F β := Polynomial.Separable.of_dvd hf₂sep hdvd
    have haint : IsIntegral F (a : L) := ⟨f₁, h₁m, Polynomial.aeval_eq_zero_of_mem_rootSet a.2⟩
    have hclose : ∀ β' : L, IsConjRoot F β β' → β ≠ β' →
        W.valuation (β - (a : L)) < W.valuation (β - β') := by
      intro β' hconj hne
      have hβ' : β' ∈ f₂.rootSet L := by
        rw [Polynomial.mem_rootSet]
        refine ⟨h₂m.ne_zero, ?_⟩
        obtain ⟨g, hg⟩ := hdvd
        rw [hg, map_mul]
        have hz : (Polynomial.aeval β') (minpoly F β) = 0 := by
          rw [hconj]; exact minpoly.aeval F β'
        rw [hz, zero_mul]
      obtain ⟨b, hb⟩ := hbij.2 ⟨β', hβ'⟩
      have hbval : (φ b : L) = β' := congrArg Subtype.val hb
      have hbne : (b : L) ≠ (a : L) := by
        intro h
        apply hne
        have hba : b = a := Subtype.ext h
        rw [← hbval, hba, haval]
      have hδab : δ ≤ W.valuation ((a : L) - (b : L)) :=
        hδsep (a : L) a.2 (b : L) b.2 (Ne.symm hbne)
      have h1 : W.valuation ((a : L) - β) < δ := by rw [← haval]; exact hφ a
      have h2 : W.valuation ((b : L) - β') < δ := by rw [← hbval]; exact hφ b
      have hkey : W.valuation (β - β') = W.valuation ((a : L) - (b : L)) :=
        valuation_sub_eq_of_close W hδab h1 h2
      have hδ' : δ ≤ W.valuation (β - β') := by rw [hkey]; exact hδab
      rw [Valuation.map_sub_swap W.valuation β (a : L)]
      exact lt_of_lt_of_le h1 hδ'
    have hres := krasner_valuation V W hW hsepβ haint hclose
    exact (IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr
        (IntermediateField.subset_adjoin F (f₁.rootSet L) a.2))) hres
  exact le_antisymm hFE hEF

end Commons.RingTheory.Valuation
