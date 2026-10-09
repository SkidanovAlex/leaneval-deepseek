import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_le_algebra
import Submission.Commons.RingTheory.Valuation.exists_monic_close_coeffs
import Submission.Commons.RingTheory.Valuation.valuation_le_iff_comap_eq
import Submission.Commons.RingTheory.Valuation.exists_monic_splits_separable_valuation
import Submission.Commons.RingTheory.Valuation.rootSet_subset_range_of_splits
import Submission.Commons.RingTheory.Valuation.close_coeffs_adjoin_le3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Polynomial

namespace Commons.RingTheory.Valuation

/-!
# F. K. Schmidt's theorem: two independent henselian valuations imply separable closedness

Let `F` be a field carrying two nontrivial henselian valuation subrings `C₁`, `C₂` which are
*independent* (no proper valuation subring of `F` contains both).  Then `F` is separably closed.

The proof follows F. K. Schmidt's argument in the form popularised for the Neukirch–Uchida
theorem.  Assume `p ∈ F[X]` is monic, irreducible and separable of degree `n ≥ 2`, and let
`L` be the algebraic closure of `F`.  Choose an extension `W₂` of `C₂` to `L` and a monic
separable polynomial `h ∈ F[X]` of degree `n` that splits over `F` (constructed from a non-unit
of `C₂`, see `exists_monic_splits_separable_valuation`).  The core lemma
`close_coeffs_adjoin_le3` then provides `c₁ c₂ ∈ F^×` such that any monic `g ∈ F[X]` of degree
`n` whose coefficients are `c₁`-close to those of `p` at `W₁` and `c₂`-close to those of `h`
at `W₂` satisfies `adjoin F (p.rootSet L) ≤ adjoin F (h.rootSet L)`.  The approximation theorem
for the independent valuations `C₁`, `C₂` (`exists_monic_close_coeffs`) yields such a `g`, and
since `h` splits over `F` its roots already lie in `F`, so every root of `p` lies in `F`.  Hence
`p` has a root in `F`, contradicting irreducibility of a polynomial of degree `≥ 2`.

-/

/-! ### The criterion -/

/-- If every monic separable irreducible polynomial over a field has degree one, then the
field is separably closed. -/
theorem isSepClosed_of_natDegree_eq_one (F : Type*) [Field F]
    (h : ∀ f : Polynomial F, f.Monic → f.Separable → Irreducible f → f.natDegree = 1) :
    IsSepClosed F := by
  refine IsSepClosed.of_exists_root F fun p hpmonic hpirr hpsep => ?_
  have hdeg : p.natDegree = 1 := h p hpmonic hpsep hpirr
  have hc : p.coeff 1 = 1 := by rw [← hdeg]; exact hpmonic.coeff_natDegree
  have hp : p = X + C (p.coeff 0) := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg)]
    rw [hc, C_1, one_mul]
  refine ⟨-(p.coeff 0), ?_⟩
  rw [hp]
  simp

/-! ### Main theorem -/

theorem isSepClosed_of_two_independent_henselian_alt {F : Type*} [Field F]
    (C₁ C₂ : ValuationSubring F) (h₁ : C₁ ≠ ⊤) (h₂ : C₂ ≠ ⊤)
    (hind : ∀ D : ValuationSubring F, C₁ ≤ D → C₂ ≤ D → D = ⊤)
    (hhen₁ : HenselianLocalRing C₁) (hhen₂ : HenselianLocalRing C₂) :
    IsSepClosed F := by
  haveI := hhen₁
  haveI := hhen₂
  refine isSepClosed_of_natDegree_eq_one F ?_
  intro p hpmonic hpsep hpirr
  by_contra hdeg1
  have hp0 : p ≠ 0 := hpirr.ne_zero
  have hn0 : p.natDegree ≠ 0 := by
    intro h
    obtain ⟨c, hc⟩ := natDegree_eq_zero.mp h
    have hc0 : c ≠ 0 := fun h0 => hp0 (by rw [← hc, h0]; simp)
    exact hpirr.not_isUnit (by rw [← hc]; exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
  have hn2 : 2 ≤ p.natDegree := by omega
  -- a nonzero element of the maximal ideal of `C₂`
  have hex : ∃ y : F, y ∉ C₂ := by
    by_contra h
    exact h₂ (_root_.eq_top_iff.mpr fun x _ => by
      by_contra hx
      exact h ⟨x, hx⟩)
  obtain ⟨y, hy⟩ := hex
  have hy0 : y ≠ 0 := fun h => hy (h ▸ C₂.zero_mem)
  have hyinv : y⁻¹ ∈ C₂ := (C₂.mem_or_inv_mem y).resolve_left hy
  have hval_gt : 1 < C₂.valuation y := by
    by_contra hle
    exact hy ((C₂.valuation_le_one_iff y).mp (le_of_not_gt hle))
  have hdy : C₂.valuation y⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hval_gt
  obtain ⟨h, hhm, hhs, hhsep, hhdeg, hhroot⟩ :=
    exists_monic_splits_separable_valuation C₂ y⁻¹ (inv_ne_zero hy0) hdy p.natDegree
      (by omega)
  -- work in the algebraic closure of `F`
  let L := AlgebraicClosure F
  obtain ⟨W₁, hW₁⟩ := exists_le_algebra (K := F) (L := L) C₁
  obtain ⟨W₂, hW₂⟩ := exists_le_algebra (K := F) (L := L) C₂
  have hW₁c : W₁.comap (algebraMap F L) = C₁ := by
    ext x; rw [_root_.ValuationSubring.mem_comap]; exact (hW₁ x).symm
  have hW₂c : W₂.comap (algebraMap F L) = C₂ := by
    ext x; rw [_root_.ValuationSubring.mem_comap]; exact (hW₂ x).symm
  obtain ⟨c₁, c₂, hc₁, hc₂, hcore⟩ :=
    close_coeffs_adjoin_le3 C₁ h₁ W₁ hW₁c C₂ h₂ W₂ hW₂c hpmonic hpsep hn2 hhm hhsep hhs
      (by rw [hhdeg])
  obtain ⟨g, hgm, hgdeg, hg₁, hg₂⟩ :=
    exists_monic_close_coeffs C₁ C₂ h₁ h₂ hind hpmonic hhm (by rw [hhdeg]) hc₁ hc₂
  have hg₁' : ∀ j : ℕ, W₁.valuation (algebraMap F L (g.coeff j - p.coeff j)) ≤
      W₁.valuation (algebraMap F L c₁) :=
    fun j => (valuation_le_iff_comap_eq C₁ W₁ hW₁c hc₁).mpr (le_of_lt (hg₁ j))
  have hg₂' : ∀ j : ℕ, W₂.valuation (algebraMap F L (g.coeff j - h.coeff j)) ≤
      W₂.valuation (algebraMap F L c₂) :=
    fun j => (valuation_le_iff_comap_eq C₂ W₂ hW₂c hc₂).mpr (le_of_lt (hg₂ j))
  have hle : IntermediateField.adjoin F (p.rootSet L) ≤ IntermediateField.adjoin F (h.rootSet L) :=
    hcore g hgm hgdeg hg₁' hg₂'
  -- the roots of `h` lie in `F`
  have hbot : IntermediateField.adjoin F (h.rootSet L) = ⊥ := by
    rw [eq_bot_iff]
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    show x ∈ (⊥ : IntermediateField F L)
    rw [IntermediateField.mem_bot]
    exact rootSet_subset_range_of_splits hhs x hx
  -- hence every root of `p` lies in `F`, so `p` has a root in `F`
  have hpbot : IntermediateField.adjoin F (p.rootSet L) ≤ ⊥ := le_trans hle (le_of_eq hbot)
  obtain ⟨x, hx⟩ : ∃ x : L, (aeval x) p = 0 := by
    have hsp : (p.map (algebraMap F L)).Splits := IsAlgClosed.splits _
    have hdegne : (p.map (algebraMap F L)).degree ≠ 0 := by
      rw [Polynomial.degree_map_eq_of_injective (algebraMap F L).injective,
        Polynomial.degree_eq_natDegree hp0]
      exact fun h => hn0 (WithBot.coe_eq_zero.mp h)
    obtain ⟨x, hx⟩ := hsp.exists_eval_eq_zero hdegne
    exact ⟨x, by rw [Polynomial.aeval_def, ← Polynomial.eval_map]; exact hx⟩
  have hxmem : x ∈ p.rootSet L := mem_rootSet.mpr ⟨hp0, hx⟩
  have hxadj : x ∈ IntermediateField.adjoin F (p.rootSet L) :=
    IntermediateField.subset_adjoin F (p.rootSet L) hxmem
  have hxbot : x ∈ (⊥ : IntermediateField F L) := hpbot hxadj
  rw [IntermediateField.mem_bot] at hxbot
  obtain ⟨a, ha⟩ := hxbot
  have hpa : p.IsRoot a := by
    have h2 : (aeval x) p = 0 := hx
    rw [← ha] at h2
    rw [Polynomial.aeval_def, Polynomial.eval₂_at_apply] at h2
    rw [Polynomial.IsRoot]
    exact (algebraMap F L).injective (by rw [h2, map_zero])
  have hdeg1' : p.degree = 1 := Polynomial.degree_eq_one_of_irreducible_of_root hpirr hpa
  have : p.natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some hdeg1'
  omega

end Commons.RingTheory.Valuation
