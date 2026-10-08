/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# Bender §3.1: `Work.BSW.BSWS31Prop`

Bender, *The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235, §3.1
(`REFS/bender1974_bsw.txt`, p. 232).

For `x ∉ H^G` inverted by `t` (`H = C_G(t) = K⟨s⟩`), put `F = C_G(x)` and `M = N_G(F)`.  This
file assembles Bender's §3.1:

* (a) `F` is abelian of odd order and `C_G(a) = F` for every `a ∈ F#`, `i(x) = |F|`
  (`Work.BSW.Cases.S31core` + `Work.BSW.S3.S31setup.odd_card_centralizer_of_notMem_HG`);
* (b) `F` is TI with respect to its normalizer (`Work.BSW.S3.ti`);
* (c) the involutions of `M` are exactly the coset `tF`
  (`Work.BSW.S3.involutionsNormalizer`);
* (d) `M = F(K ⊓ M)`, `F ∩ K = 1`, and `K ⊓ M` acts fixed-point-freely on `F`;
* (f) `F` is a Hall subgroup coprime to `2k` (`Work.BSW.S3.hall`, `Work.BSW.S3.coprimeTwoK`).
-/
import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.S3.S31setup
import Submission.Work.BSW.S3.hall
import Submission.Work.BSW.S3.ti
import Submission.Work.BSW.S3.normalizerStruct
import Submission.Work.BSW.S3.involutionsNormalizer
import Submission.Work.BSW.S3.coprimeTwoK
import Submission.Work.BSW.Cases.Order.Setup
import Submission.Work.BSW.Cases.bswCompletionBase
import Submission.Work.BSW.Cases.S31core

namespace Work.BSW.S3

open Subgroup Work.GW2

theorem s31 : Work.BSW.BSWS31Prop := by
  intro G instG instFin t s K x h hx hinv
  have hcore := centralizer_eq_of_mem_centralizer h hx hinv
  have hodd := odd_card_centralizer_of_notMem_HG h hx
  have hmulc := isMulCommutative_centralizer h hx hinv
  have hiFn := card_centralizer_eq_iFn h hx hinv
  have hinfK := inf_K_centralizer_eq_bot h hx
  have hhall := hall (Subgroup.centralizer ({x} : Set G)) hcore
  -- (d) `K ⊓ M` acts fixed-point-freely on `F`
  have hfree : ∀ c ∈ K ⊓ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G),
      c ≠ 1 → ∀ a ∈ Subgroup.centralizer ({x} : Set G), c * a * c⁻¹ = a → a = 1 := by
    intro c hc hc1 a ha hconj
    by_contra ha1
    have hcF : c ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [← hcore a ha ha1, Subgroup.mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.mp hconj
    have hmem : c ∈ Subgroup.centralizer ({x} : Set G) ⊓ K := ⟨hcF, hc.1⟩
    rw [hinfK] at hmem
    exact hc1 (Subgroup.mem_bot.mp hmem)
  exact ⟨hmulc, hodd, hcore, ti hcore, hinfK, normalizerStruct h hx hinv, hfree,
    involutionsNormalizer h hx hinv, hiFn.symm, hhall, coprimeTwoK h hx hinv hhall⟩

end Work.BSW.S3
