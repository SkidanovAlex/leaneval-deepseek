import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_root_separation_val
import Submission.Commons.RingTheory.Valuation.exists_algebraMap_valuation_lt_of_ne_top
import Submission.Commons.RingTheory.Valuation.adjoin_rootSet_eq_of_matching_valuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Coefficients close to `f` (for `W₁`) and to `h` (for `W₂`) force the roots of `f` into the
roots of `h`.

We prove `close_coeffs_adjoin_le3`: given two proper henselian valuation subrings `C₁`, `C₂` of
`F`, extensions `W₁`, `W₂` to an algebraically closed algebraic extension `L`, and monic
separable polynomials `f`, `h` of the same degree `n ≥ 2` over `F` with `h` split, there are
nonzero `c₁, c₂ ∈ F` such that every monic `g` of degree `n` with `g` coefficientwise
`W₁`-close to `f` (within `W₁.valuation (algebraMap c₁)`) and `W₂`-close to `h` (within
`W₂.valuation (algebraMap c₂)`) satisfies
`adjoin F (f.rootSet L) ≤ adjoin F (h.rootSet L)`.

The proof goes through the following chain of intermediate results.

* `exists_coeffs_close_root_close_aux`: coefficientwise closeness of two monic polynomials of the
  same degree forces every root of one to be close to a root of the other, with any prescribed
  closeness `δ > 0`.  The bound on the roots of `g` uses the "root bound" `W.valuation α ≤ A`
  that follows from `f` being monic, and the compatibility of the coefficients is turned into a
  bound on `W.valuation (aeval α g)` via the ultrametric inequality.

* `exists_close_coeffs_adjoin_eq`: for a *single* proper henselian valuation, sufficiently close
  monic polynomials generate the same root field.  This is `adjoin_rootSet_eq_of_matching_valuation`
  (Krasner's lemma in both directions) applied to the separation radius of `f` and the matching
  produced by the previous point.

* `close_coeffs_adjoin_le3`: the two-valuation statement is obtained by applying the single
  valuation statement twice, `adjoin F (f.rootSet L) = adjoin F (g.rootSet L)` and
  `adjoin F (h.rootSet L) = adjoin F (g.rootSet L)`.
-/

set_option linter.unusedVariables false

open Polynomial

namespace Commons.RingTheory.Valuation

/-- **Coefficient closeness implies root closeness.**

Let `V` be a proper henselian valuation subring of `F`, `W` an extension of `V` to an
algebraically closed algebraic extension `L`, and `f` a monic polynomial over `F` of degree
`≥ 2`.  For every positive `δ` in the value group of `W` there is a nonzero `c ∈ F` such that
every monic `g` of degree `deg f` whose coefficients are `W`-close to those of `f` within
`W.valuation (algebraMap c)` has the property that every root of `f` is `δ`-close to a root
of `g`. -/
private theorem exists_coeffs_close_root_close_aux {F L : Type*} [Field F] [Field L] [Algebra F L]
    [IsAlgClosed L] [Algebra.IsAlgebraic F L] (V : ValuationSubring F) (hV : V ≠ ⊤)
    [HenselianLocalRing V] (W : ValuationSubring L) (hW : W.comap (algebraMap F L) = V)
    {f : Polynomial F} (hfm : f.Monic) (hfd : 2 ≤ f.natDegree) {δ : W.ValueGroup} (hδ0 : 0 < δ) :
    ∃ c : F, c ≠ 0 ∧ ∀ g : Polynomial F, g.Monic → g.natDegree = f.natDegree →
      (∀ j : ℕ, W.valuation (algebraMap F L (g.coeff j - f.coeff j)) ≤
        W.valuation (algebraMap F L c)) →
      ∀ α ∈ f.rootSet L, ∃ β ∈ g.rootSet L, W.valuation (α - β) < δ := by
  classical
  set A0 : W.ValueGroup := (Finset.range (f.natDegree)).sup
      (fun j => W.valuation (algebraMap F L (f.coeff j))) with hA0
  set A : W.ValueGroup := A0 ⊔ 1 with hA
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one le_sup_right
  have hA0le : A0 ≤ A := le_sup_left
  have hAle1 : 1 ≤ A := le_sup_right
  obtain ⟨c, hc, hcval⟩ :=
    exists_algebraMap_valuation_lt_of_ne_top V hV W hW
      (inferInstance : Algebra.IsAlgebraic F L)
      (show 0 < δ ^ (f.natDegree) / A ^ (f.natDegree - 1) from
        div_pos (pow_pos hδ0 _) (pow_pos hApos _))
  refine ⟨c, hc, fun g hgm hgdeg hcl α hα => ?_⟩
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ β, β ∈ g.rootSet L → δ ≤ W.valuation (α - β)`
  have hαf : Polynomial.aeval α f = 0 := (Polynomial.mem_rootSet.mp hα).2
  -- Root bound: `W.valuation α ≤ A`
  have hαA : W.valuation α ≤ A := by
    rcases le_or_gt (W.valuation α) 1 with hle | hgt
    · exact le_trans hle hAle1
    · have hsum_aeval : Polynomial.aeval α f
          = ∑ j ∈ Finset.range (f.natDegree + 1), algebraMap F L (f.coeff j) * α ^ j := by
        rw [Polynomial.aeval_eq_sum_range]
        exact Finset.sum_congr rfl (fun j _ => by rw [Algebra.smul_def])
      have h1 : (∑ j ∈ Finset.range (f.natDegree + 1),
          algebraMap F L (f.coeff j) * α ^ j) = 0 := by
        rw [← hsum_aeval]; exact hαf
      rw [Finset.sum_range_succ] at h1
      have hlast : algebraMap F L (f.coeff f.natDegree) * α ^ f.natDegree = α ^ f.natDegree := by
        rw [hfm.coeff_natDegree, map_one, one_mul]
      rw [hlast] at h1
      have hpoweq : α ^ f.natDegree
          = - ∑ j ∈ Finset.range (f.natDegree), algebraMap F L (f.coeff j) * α ^ j := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact h1
      have hvalpow : W.valuation α ^ f.natDegree
          = W.valuation (∑ j ∈ Finset.range (f.natDegree),
              algebraMap F L (f.coeff j) * α ^ j) := by
        rw [← Valuation.map_pow, hpoweq, Valuation.map_neg]
      have hbound_sum : W.valuation (∑ j ∈ Finset.range (f.natDegree),
            algebraMap F L (f.coeff j) * α ^ j) ≤ A * W.valuation α ^ (f.natDegree - 1) := by
        refine Valuation.map_sum_le _ (fun j hj => ?_)
        rw [Valuation.map_mul, Valuation.map_pow]
        have hj' : j < f.natDegree := Finset.mem_range.mp hj
        have hcoeff_le : W.valuation (algebraMap F L (f.coeff j)) ≤ A :=
          le_trans (Finset.le_sup (f := fun j => W.valuation (algebraMap F L (f.coeff j))) hj)
            hA0le
        have hpow_le : W.valuation α ^ j ≤ W.valuation α ^ (f.natDegree - 1) :=
          pow_le_pow_right₀ hgt.le (by omega)
        exact le_trans
          (mul_le_mul_of_nonneg_right hcoeff_le
            (le_of_lt (pow_pos (lt_trans zero_lt_one hgt) j)))
          (mul_le_mul_of_nonneg_left hpow_le (le_of_lt hApos))
      have hpow_bound : W.valuation α ^ f.natDegree ≤ A * W.valuation α ^ (f.natDegree - 1) :=
        hvalpow.trans_le hbound_sum
      have hnmul : W.valuation α * W.valuation α ^ (f.natDegree - 1)
          ≤ A * W.valuation α ^ (f.natDegree - 1) := by
        have h1' : f.natDegree = (f.natDegree - 1) + 1 := by omega
        rw [h1', pow_succ'] at hpow_bound
        exact hpow_bound
      have hpos : 0 < W.valuation α ^ (f.natDegree - 1) :=
        pow_pos (lt_trans zero_lt_one hgt) _
      exact le_of_mul_le_mul_right hnmul hpos
  -- Product formula for `aeval α g`
  have hgsplits : (g.map (algebraMap F L)).Splits := IsAlgClosed.splits _
  have hae : Polynomial.aeval α g = ((g.aroots L).map (fun b => α - b)).prod :=
    hgsplits.aeval_eq_prod_aroots_of_monic hgm α
  have hval : W.valuation (Polynomial.aeval α g)
      = ((g.aroots L).map (fun b => W.valuation (α - b))).prod := by
    rw [hae]
    have hh := map_multiset_prod W.valuation ((g.aroots L).map (fun b => α - b))
    rw [hh, Multiset.map_map]
    rfl
  have hcard : ((g.aroots L).map (fun b => W.valuation (α - b))).card = f.natDegree := by
    rw [Multiset.card_map, Polynomial.aroots_def,
      Polynomial.splits_iff_card_roots.mp hgsplits,
      Polynomial.natDegree_map_eq_of_injective (algebraMap F L).injective, hgdeg]
  have hge : δ ^ f.natDegree ≤ W.valuation (Polynomial.aeval α g) := by
    rw [hval, ← hcard]
    exact Multiset.pow_card_le_prod (fun x hx => by
      obtain ⟨b, hb, hxb⟩ := Multiset.mem_map.mp hx
      rw [← hxb]
      exact hcon b (Polynomial.mem_rootSet.mpr
        ⟨hgm.ne_zero, (Polynomial.mem_aroots.mp hb).2⟩))
  -- Upper bound: `W.valuation (aeval α g) < δ ^ f.natDegree`
  have hcoeffN : ∀ N, f.natDegree ≤ N → (g - f).coeff N = 0 := by
    intro N hN
    rw [Polynomial.coeff_sub]
    rcases eq_or_lt_of_le hN with h | h
    · subst h
      have hfn : f.coeff f.natDegree = 1 := hfm.coeff_natDegree
      have hgn : g.coeff f.natDegree = 1 := by rw [← hgdeg]; exact hgm.coeff_natDegree
      rw [hgn, hfn, sub_self]
    · have hf : f.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt h
      have hg : g.coeff N = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hgdeg]; exact h)
      rw [hg, hf, sub_self]
  have hdeg_sub_lt : (g - f).natDegree < f.natDegree := by
    have hle : (g - f).natDegree ≤ f.natDegree - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      exact hcoeffN N (by omega)
    omega
  have hrepr : (g - f) = ∑ j ∈ Finset.range (f.natDegree),
      Polynomial.monomial j ((g - f).coeff j) := Polynomial.as_sum_range' (g - f) _ hdeg_sub_lt
  have haeval_sum : Polynomial.aeval α (g - f)
      = ∑ j ∈ Finset.range (f.natDegree), algebraMap F L ((g - f).coeff j) * α ^ j := by
    conv_lhs => rw [hrepr]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [Polynomial.aeval_monomial])
  have hsub : Polynomial.aeval α (g - f) = Polynomial.aeval α g := by
    rw [Polynomial.aeval_sub, hαf, sub_zero]
  have hterm : ∀ j ∈ Finset.range (f.natDegree),
      W.valuation (algebraMap F L ((g - f).coeff j) * α ^ j)
        ≤ W.valuation (algebraMap F L c) * A ^ (f.natDegree - 1) := by
    intro j hj
    rw [Valuation.map_mul, Valuation.map_pow]
    have hj' : j < f.natDegree := Finset.mem_range.mp hj
    have hc_le : W.valuation (algebraMap F L ((g - f).coeff j))
        ≤ W.valuation (algebraMap F L c) := by
      rw [Polynomial.coeff_sub]; exact hcl j
    have hpow : W.valuation α ^ j ≤ A ^ (f.natDegree - 1) :=
      le_trans (pow_le_pow_left₀ zero_le hαA j) (pow_le_pow_right₀ hAle1 (by omega))
    exact le_trans
      (mul_le_mul_of_nonneg_right hc_le (pow_nonneg zero_le j))
      (mul_le_mul_of_nonneg_left hpow zero_le)
  have hsumle : W.valuation (∑ j ∈ Finset.range (f.natDegree),
        algebraMap F L ((g - f).coeff j) * α ^ j)
      ≤ W.valuation (algebraMap F L c) * A ^ (f.natDegree - 1) :=
    Valuation.map_sum_le _ hterm
  have hbound : W.valuation (Polynomial.aeval α g) < δ ^ f.natDegree := by
    have h1 : W.valuation (Polynomial.aeval α g) = W.valuation (Polynomial.aeval α (g - f)) := by
      rw [hsub]
    rw [h1, haeval_sum]
    refine lt_of_le_of_lt hsumle ?_
    have hposA : 0 < A ^ (f.natDegree - 1) := pow_pos hApos _
    have := mul_lt_mul_of_pos_right hcval hposA
    rwa [show (δ ^ f.natDegree / A ^ (f.natDegree - 1)) * A ^ (f.natDegree - 1)
        = δ ^ f.natDegree from div_mul_cancel₀ _ (ne_of_gt hposA)] at this
  exact (not_le_of_gt hbound) hge

/-- **Single-valuation close coefficients generate the same root field.**

Let `V` be a proper henselian valuation subring of `F` and `W` an extension of `V` to an
algebraically closed algebraic extension `L`.  For a monic separable `f` of degree `≥ 2` there
is a nonzero `c ∈ F` such that every monic `g` of degree `deg f` whose coefficients are
`W`-close to those of `f` within `W.valuation (algebraMap c)` generates the same subfield of
`L` over `F` as `f` does. -/
theorem exists_close_coeffs_adjoin_eq {F L : Type*} [Field F] [Field L] [Algebra F L]
    [IsAlgClosed L] [Algebra.IsAlgebraic F L] (V : ValuationSubring F) (hV : V ≠ ⊤)
    [HenselianLocalRing V] (W : ValuationSubring L) (hW : W.comap (algebraMap F L) = V)
    {f : Polynomial F} (hfm : f.Monic) (hfsep : f.Separable) (hfd : 2 ≤ f.natDegree) :
    ∃ c : F, c ≠ 0 ∧ ∀ g : Polynomial F, g.Monic → g.natDegree = f.natDegree →
      (∀ j : ℕ, W.valuation (algebraMap F L (g.coeff j - f.coeff j)) ≤
        W.valuation (algebraMap F L c)) →
      IntermediateField.adjoin F (f.rootSet L) = IntermediateField.adjoin F (g.rootSet L) := by
  obtain ⟨δ, hδ0, hδsep⟩ := exists_root_separation_val W hfm.ne_zero
  obtain ⟨c, hc, hclose⟩ := exists_coeffs_close_root_close_aux V hV W hW hfm hfd hδ0
  refine ⟨c, hc, fun g hgm hgdeg hcl => ?_⟩
  exact adjoin_rootSet_eq_of_matching_valuation V W hW hfm hfsep hgm (le_of_eq hgdeg)
    hδ0 hδsep (hclose g hgm hgdeg hcl)

theorem close_coeffs_adjoin_le3 {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed L] [Algebra.IsAlgebraic F L] (C₁ : ValuationSubring F) (hC₁ : C₁ ≠ ⊤) [HenselianLocalRing C₁] (W₁ : ValuationSubring L) (hW₁ : W₁.comap (algebraMap F L) = C₁) (C₂ : ValuationSubring F) (hC₂ : C₂ ≠ ⊤) [HenselianLocalRing C₂] (W₂ : ValuationSubring L) (hW₂ : W₂.comap (algebraMap F L) = C₂) {f h : Polynomial F} (hfm : f.Monic) (hfsep : f.Separable) (hfdeg : 2 ≤ f.natDegree) (hhm : h.Monic) (hhsep : h.Separable) (hhs : h.Splits) (hhdeg : h.natDegree = f.natDegree) : ∃ c₁ c₂ : F, c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ ∀ g : Polynomial F, g.Monic → g.natDegree = f.natDegree → (∀ j : ℕ, W₁.valuation (algebraMap F L (g.coeff j - f.coeff j)) ≤ W₁.valuation (algebraMap F L c₁)) → (∀ j : ℕ, W₂.valuation (algebraMap F L (g.coeff j - h.coeff j)) ≤ W₂.valuation (algebraMap F L c₂)) → IntermediateField.adjoin F (f.rootSet L) ≤ IntermediateField.adjoin F (h.rootSet L) := by
  obtain ⟨c₁, hc₁, hmain₁⟩ := exists_close_coeffs_adjoin_eq C₁ hC₁ W₁ hW₁ hfm hfsep hfdeg
  obtain ⟨c₂, hc₂, hmain₂⟩ :=
    exists_close_coeffs_adjoin_eq C₂ hC₂ W₂ hW₂ hhm hhsep (by rw [hhdeg]; exact hfdeg)
  refine ⟨c₁, c₂, hc₁, hc₂, fun g hgm hgdeg hcl₁ hcl₂ => ?_⟩
  have h1 : IntermediateField.adjoin F (f.rootSet L) ≤ IntermediateField.adjoin F (g.rootSet L) :=
    (hmain₁ g hgm hgdeg hcl₁).le
  have h2 : IntermediateField.adjoin F (h.rootSet L) = IntermediateField.adjoin F (g.rootSet L) :=
    hmain₂ g hgm (hgdeg.trans hhdeg.symm) hcl₂
  calc IntermediateField.adjoin F (f.rootSet L)
      ≤ IntermediateField.adjoin F (g.rootSet L) := h1
    _ = IntermediateField.adjoin F (h.rootSet L) := h2.symm

end Commons.RingTheory.Valuation
