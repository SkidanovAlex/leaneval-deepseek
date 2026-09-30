import Mathlib
import Submission.Work.BW.finrank_subIdeal_false_defs
import Submission.Work.BW.char_linearIndependent
import Submission.Work.BW.finrank_subIdeal_true

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

noncomputable section

/-- Distinct classes of the torus box have representatives `repPt` whose difference is *not* an
integral combination of the rows of `M`: the class of `repPt d M c` modulo `rowLat N ρ M` is `c`
(`repPt_cls`), so equal classes would force `c = c'`. This is the pairwise distinctness hypothesis
of `char_linearIndependent` for the family `c ↦ repPt d M c`. -/
lemma repPt_class_ne {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    {c c' : clsSet d M} (hne : c ≠ c') :
    ¬ ∃ r : Fin ρ → ℤ, ∀ m, repPt d M c m - repPt d M c' m = ∑ j, r j * M j m := by
  rintro ⟨r, hr⟩
  apply hne
  have hmem : repPt d M c - repPt d M c' ∈ rowLat N ρ M := by
    rw [rowLat, Submodule.mem_span_range_iff_exists_fun]
    refine ⟨r, ?_⟩
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    exact (hr m).symm
  have hq : (Submodule.Quotient.mk (repPt d M c) : (Fin N → ℤ) ⧸ rowLat N ρ M)
      = Submodule.Quotient.mk (repPt d M c') := by
    rw [Submodule.Quotient.eq]
    exact hmem
  rw [repPt_cls d M c, repPt_cls d M c'] at hq
  exact Subtype.ext hq

/-- Evaluating the linear combination `∑ c, g c • xmono d M c` at the cone point over
`Fin.cons 0 y` (`y` the torus coordinates) gives the character combination
`∑ c, g c * ∏ m, y m ^ (repPt d M c m)`. Uses `eval_conePt_mono` and `repExp = Fin.cons 0 ∘ repPt`
(with `repPt` nonnegative, so the `ℕ`-exponents of `repExp` may be read as the integer exponents
of `repPt`). -/
lemma eval_conePt_sum_xmono {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (g : clsSet d M → ℂ) (y : Fin N → ℂ) :
    MvPolynomial.eval (conePt N (Fin.cons 0 y))
      (((∑ c, g c • xmono d M c : homPiece N d)) : MR N)
      = ∑ c, g c * ∏ m, y m ^ (repPt d M c m) := by
  have hcoe : (((∑ c, g c • xmono d M c : homPiece N d)) : MR N)
      = ∑ c, g c • ((xmono d M c : homPiece N d) : MR N) := by
    change (homPiece N d).subtype (∑ c, g c • xmono d M c) = _
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [map_smul]
    rfl
  rw [hcoe, map_sum]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [xmono_coe, MvPolynomial.smul_eval, eval_conePt_mono]
  congr 1
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, repExp_zero, repExp_succ, pow_zero, one_mul]
  refine Finset.prod_congr rfl ?_
  intro m _
  rw [← zpow_natCast (y m) ((repPt d M c m).toNat),
    Int.toNat_of_nonneg (repPt_nonneg d M c m)]

/-- The monomials `xmono d M c` (one per class `c` of the torus box `∏ᵢ [0, d_{i+1}]` modulo the row lattice `𝒵 = rowLat M`) are linearly independent modulo the graded piece `subPiece N ρ d M` of the vanishing ideal of `G' = {0} × ker 𝒵`: any `ℂ`-linear combination `∑ c, g c • xmono d M c` lying in `subPiece` has all coefficients `g c = 0`. Evaluate at `conePt N y` for `y ∈ InSub N ρ false M` (`subIdeal_vanish_false`, `eval_conePt_mono`), specialise to `y = Fin.cons 0 y'`, and apply `char_linearIndependent` using `clsOf_torPart_repExp`. -/
theorem xmono_linearIndependent {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (hM : PrimSys M) (g : clsSet d M → ℂ)
    (hg : (∑ c, g c • xmono d M c) ∈ subPiece N ρ d M) :
    ∀ c, g c = 0 := by
  refine char_linearIndependent_fintype M hM (fun c => repPt d M c) ?_ g ?_
  · intro c c' hne
    exact repPt_class_ne d M hne
  · intro y hy hyk
    have hIn : InSub N ρ false M (Fin.cons 0 y) := by
      refine ⟨?_, ?_, ?_⟩
      · intro _
        rfl
      · intro i
        simpa only [Fin.cons_succ] using hy i
      · intro j
        simpa only [Fin.cons_succ] using hyk j
    have hvanish : MvPolynomial.eval (conePt N (Fin.cons 0 y))
        (((∑ c, g c • xmono d M c : homPiece N d)) : MR N) = 0 :=
      subIdeal_vanish_false M hIn hg
    rw [← eval_conePt_sum_xmono d M g y]
    exact hvanish

end

end Work.BW
