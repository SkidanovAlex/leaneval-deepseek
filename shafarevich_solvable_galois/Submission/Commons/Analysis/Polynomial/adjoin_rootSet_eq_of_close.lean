import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Submission.Commons.Analysis.Normed.eq_of_close
import Submission.Commons.Analysis.Normed.exists_root_separation
import Submission.Commons.Analysis.Normed.norm_sub_eq_of_close
import Submission.Commons.Analysis.Polynomial.exists_eps_forall_root_close
import Submission.Commons.FieldTheory.Polynomial.mem_adjoin_of_close
import Submission.Commons.FieldTheory.Polynomial.mem_rootSet_of_mem_roots_map
import Submission.Commons.FieldTheory.Polynomial.mem_roots_map_of_mem_rootSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Polynomial IntermediateField

namespace Commons.Analysis.Polynomial

set_option linter.style.haveILetI false

/-- The number of distinct roots of a polynomial in a field is at most its degree.
(Fintype form of `Polynomial.ncard_rootSet_le`.) -/
private lemma fintypeCard_rootSet_le_natDegree {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain B] [Algebra A B] (p : A[X]) : Fintype.card (p.rootSet B) ≤ p.natDegree := by
  have h := Polynomial.ncard_rootSet_le p B
  rwa [Set.fintypeCard_eq_ncard]

/-- **Matching lemma.**  Let `K` be a complete nontrivially normed field with ultrametric norm,
`L` an algebraically closed algebraic extension, and `f₁`, `f₂ ∈ K[X]` with `f₁` nonzero and
separable, `f₂` nonzero of degree at most `deg f₁`.  Suppose `δ > 0` separates the distinct
roots of `f₁` in `L` and every root of `f₁` has a root of `f₂` within distance `δ`.  Then the
roots of `f₁` and of `f₂` generate the same subfield of `L` over `K`.

The proof is Krasner's lemma in both directions.  The matching hypothesis makes the assignment
"root of `f₁` ↦ nearby root of `f₂`" injective, so `f₂` has at least `deg f₁` distinct roots
and, since `deg f₂ ≤ deg f₁`, exactly that many; consequently `f₂` is separable and the matching
is a bijection.  Each root of `f₂` is then closer to its matched root of `f₁` than to any other
root of `f₂` (ultrametricity), so Krasner applies in the reverse direction as well. -/
theorem adjoin_rootSet_eq_of_matching {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]
    [IsAlgClosed L]
    {f₁ f₂ : Polynomial K} (hf₁ : f₁.Separable) (hf₁0 : f₁ ≠ 0)
    (hf₂0 : f₂ ≠ 0) (hdeg : f₂.natDegree ≤ f₁.natDegree)
    {δ : ℝ}
    (hδsep : ∀ ⦃γ : L⦄, γ ∈ f₁.rootSet L → ∀ ⦃γ' : L⦄, γ' ∈ f₁.rootSet L →
      γ ≠ γ' → δ ≤ ‖γ - γ'‖)
    (hmatch : ∀ α ∈ f₁.rootSet L, ∃ β ∈ f₂.rootSet L, ‖α - β‖ < δ) :
    IntermediateField.adjoin K (f₁.rootSet L) = IntermediateField.adjoin K (f₂.rootSet L) := by
  classical
  haveI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  let φ : f₁.rootSet L → f₂.rootSet L :=
    fun a => ⟨(hmatch a a.2).choose, (hmatch a a.2).choose_spec.1⟩
  have hφ : ∀ a : f₁.rootSet L, ‖(a : L) - (φ a : L)‖ < δ :=
    fun a => (hmatch a a.2).choose_spec.2
  have hφinj : Function.Injective φ := by
    intro a b hab
    by_contra hne
    have hne' : (a : L) ≠ (b : L) := fun h => hne (Subtype.ext h)
    have hδab : δ ≤ ‖(a : L) - (b : L)‖ := hδsep a.2 b.2 hne'
    have h1 : ‖(a : L) - (φ a : L)‖ < δ := hφ a
    have h2 : ‖(b : L) - (φ a : L)‖ < δ := by
      rw [hab]
      exact hφ b
    exact hne' (Commons.Analysis.Normed.eq_of_close hδab h1 h2)
  have hcard1 : Fintype.card (f₁.rootSet L) = f₁.natDegree :=
    Polynomial.card_rootSet_eq_natDegree hf₁ (IsAlgClosed.splits _)
  have hcard2le : Fintype.card (f₂.rootSet L) ≤ f₂.natDegree :=
    fintypeCard_rootSet_le_natDegree f₂
  have hcard2 : Fintype.card (f₂.rootSet L) = f₁.natDegree := by
    have h1 := Fintype.card_le_of_injective φ hφinj
    rw [hcard1] at h1
    omega
  have hf₂deg : f₂.natDegree = f₁.natDegree := by omega
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφinj, by rw [hcard1, hcard2]⟩
  -- `f₂` is separable
  have harootscard : (f₂.aroots L).card = f₂.natDegree := by
    rw [Polynomial.aroots_def,
      ← Splits.natDegree_eq_card_roots (IsAlgClosed.splits (f₂.map (algebraMap K L))),
      Polynomial.natDegree_map]
  have htoFinset : (f₂.aroots L).toFinset.card = Fintype.card (f₂.rootSet L) := by
    rw [Set.fintypeCard_eq_ncard, Polynomial.rootSet_def, Set.ncard_coe_finset]
  have hnodup : (f₂.aroots L).Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]
    rw [htoFinset, harootscard, hf₂deg, hcard2]
  have hf₂sep : f₂.Separable :=
    (Polynomial.nodup_aroots_iff_of_splits hf₂0 (IsAlgClosed.splits _)).mp hnodup
  -- forward inclusion: every root of `f₁` lies in the field generated by the roots of `f₂`
  have hFE : IntermediateField.adjoin K (f₁.rootSet L) ≤
      IntermediateField.adjoin K (f₂.rootSet L) := by
    rw [IntermediateField.adjoin_le_iff]
    intro α hα
    let a : f₁.rootSet L := ⟨α, hα⟩
    have hβmem : (φ a : L) ∈ f₂.rootSet L := (φ a).2
    have hclose : ‖α - (φ a : L)‖ < δ := hφ a
    have hβroots : (φ a : L) ∈ (f₂.map (algebraMap K L)).roots :=
      Commons.FieldTheory.Polynomial.mem_roots_map_of_mem_rootSet hf₂0 hβmem
    have hαaeval : (Polynomial.aeval α) f₁ = 0 := Polynomial.aeval_eq_zero_of_mem_rootSet hα
    have hsp : ((minpoly K α).map (algebraMap K L)).Splits := IsAlgClosed.splits _
    have hcloser : ∀ γ ∈ f₁.rootSet L, γ ≠ α → ‖α - (φ a : L)‖ < ‖α - γ‖ := by
      intro γ hγ hne
      have : δ ≤ ‖α - γ‖ := hδsep hα hγ hne.symm
      linarith
    have hres := Commons.FieldTheory.Polynomial.mem_adjoin_of_close (f₁ := f₁) (f₂ := f₂)
      (α := α) (β := (φ a : L)) hf₁ hf₁0 hf₂0 hαaeval hβroots hsp hcloser
    exact (IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr (IntermediateField.subset_adjoin K (f₂.rootSet L) hβmem)))
      hres
  -- reverse inclusion: every root of `f₂` lies in the field generated by the roots of `f₁`
  have hEF : IntermediateField.adjoin K (f₂.rootSet L) ≤
      IntermediateField.adjoin K (f₁.rootSet L) := by
    rw [IntermediateField.adjoin_le_iff]
    intro β hβ
    obtain ⟨a, ha⟩ := hbij.2 ⟨β, hβ⟩
    have haval : (φ a : L) = β := congrArg Subtype.val ha
    have hclose : ‖(a : L) - β‖ < δ := by rw [← haval]; exact hφ a
    have hsep2 : ∀ γ ∈ f₂.rootSet L, γ ≠ β → ‖β - (a : L)‖ < ‖β - γ‖ := by
      intro γ hγ hne
      obtain ⟨b, hb⟩ := hbij.2 ⟨γ, hγ⟩
      have hbval : (φ b : L) = γ := congrArg Subtype.val hb
      have hbne : (b : L) ≠ (a : L) := by
        intro h
        apply hne
        have hba : b = a := Subtype.ext h
        rw [← hbval, hba, haval]
      have hδab : δ ≤ ‖(a : L) - (b : L)‖ := hδsep a.2 b.2 (Ne.symm hbne)
      have h2 : ‖(b : L) - γ‖ < δ := by rw [← hbval]; exact hφ b
      have key : δ ≤ ‖β - γ‖ := by
        rw [Commons.Analysis.Normed.norm_sub_eq_of_close hδab hclose h2]
        exact hδab
      rw [norm_sub_rev β (a : L)]
      exact lt_of_lt_of_le hclose key
    have hαaeval : (Polynomial.aeval β) f₂ = 0 := Polynomial.aeval_eq_zero_of_mem_rootSet hβ
    have hβroots : (a : L) ∈ (f₁.map (algebraMap K L)).roots :=
      Commons.FieldTheory.Polynomial.mem_roots_map_of_mem_rootSet hf₁0 a.2
    have hsp : ((minpoly K β).map (algebraMap K L)).Splits := IsAlgClosed.splits _
    have hres := Commons.FieldTheory.Polynomial.mem_adjoin_of_close (f₁ := f₂) (f₂ := f₁)
      (α := β) (β := (a : L)) hf₂sep hf₂0 hf₁0 hαaeval hβroots hsp hsep2
    exact (IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr (IntermediateField.subset_adjoin K (f₁.rootSet L) a.2)))
      hres
  exact le_antisymm hFE hEF

/-- **Root sets of close separable polynomials generate the same field.**
Let `K` be a complete nontrivially normed field with ultrametric norm and `f₁ ∈ K[X]` a nonzero
separable polynomial.  Then there is `ε > 0` such that for every `f₂ ∈ K[X]` with
`deg f₂ ≤ deg f₁` and `supNorm (f₁ - f₂) < ε`, the subfield of an algebraic closure of `K`
generated by the roots of `f₁` coincides with the subfield generated by the roots of `f₂`.

The proof takes `δ > 0` separating the distinct roots of `f₁` and the uniform threshold `ε`
from `exists_eps_forall_root_close` (shrunk further so that `f₂` keeps the degree of `f₁`),
and applies the matching lemma `adjoin_rootSet_eq_of_matching`. -/
theorem adjoin_rootSet_eq_of_close {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] (f₁ : Polynomial K) (hf₁0 : f₁ ≠ 0) (hf₁ : f₁.Separable) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f₂ : Polynomial K, f₂.natDegree ≤ f₁.natDegree →
      (f₁ - f₂).supNorm < ε →
      IntermediateField.adjoin K (f₁.rootSet (AlgebraicClosure K)) =
      IntermediateField.adjoin K (f₂.rootSet (AlgebraicClosure K)) := by
  letI : NontriviallyNormedField (AlgebraicClosure K) :=
    spectralNorm.nontriviallyNormedField K (AlgebraicClosure K)
  letI : NormedAlgebra K (AlgebraicClosure K) :=
    spectralNorm.normedAlgebra K (AlgebraicClosure K)
  have h_ext : ∀ k : K, ‖algebraMap K (AlgebraicClosure K) k‖ = ‖k‖ :=
    fun k => spectralNorm_extends k
  by_cases hdeg : f₁.natDegree = 0
  · -- `f₁` is a nonzero constant, hence has no roots; the same holds for every `f₂` of degree `≤ 0`
    refine ⟨1, one_pos, ?_⟩
    intro f₂ hf₂ _
    have h₁ : f₁ = C (f₁.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hdeg)
    have h₂ : f₂ = C (f₂.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by omega)
    rw [h₁, h₂, Polynomial.rootSet_C, Polynomial.rootSet_C]
  · have hf₁1 : 1 ≤ f₁.natDegree := Nat.one_le_iff_ne_zero.mpr hdeg
    obtain ⟨δ, hδpos, hδsep⟩ :=
      Commons.Analysis.Normed.exists_root_separation (K := K) (L := AlgebraicClosure K) f₁
    obtain ⟨ε₀, hε₀pos, hε₀⟩ := exists_eps_forall_root_close h_ext hf₁1 hδpos hδsep
    have hlcne : f₁.coeff f₁.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact fun h => hf₁0 (Polynomial.leadingCoeff_eq_zero.mp h)
    have hlcpos : 0 < ‖f₁.coeff f₁.natDegree‖ := norm_pos_iff.mpr hlcne
    refine ⟨min ε₀ ‖f₁.coeff f₁.natDegree‖, lt_min hε₀pos hlcpos, ?_⟩
    intro f₂ hf₂ hclose
    have hdeg2 : f₂.natDegree = f₁.natDegree :=
      Commons.FieldTheory.Polynomial.natDegree_eq_of_supNorm_lt f₁ f₂ _ hf₂ hlcpos le_rfl
        (lt_of_lt_of_le hclose (min_le_right _ _))
    have hf₂0 : f₂ ≠ 0 := by
      intro h
      rw [h, Polynomial.natDegree_zero] at hdeg2
      omega
    have hmatch : ∀ α ∈ f₁.rootSet (AlgebraicClosure K),
        ∃ β ∈ f₂.rootSet (AlgebraicClosure K), ‖α - β‖ < δ := by
      intro α hα
      have hclose' : (f₂ - f₁).supNorm < ε₀ := by
        rw [show f₂ - f₁ = -(f₁ - f₂) from (neg_sub f₁ f₂).symm, supNorm_neg]
        exact lt_of_lt_of_le hclose (min_le_left _ _)
      obtain ⟨β, hβroots, hβclose, _⟩ := hε₀ f₂ hf₂ hf₂0 hclose' hα
      exact ⟨β, Commons.FieldTheory.Polynomial.mem_rootSet_of_mem_roots_map hf₂0 hβroots,
        hβclose⟩
    exact adjoin_rootSet_eq_of_matching hf₁ hf₁0 hf₂0 hf₂ hδsep hmatch

end Commons.Analysis.Polynomial
