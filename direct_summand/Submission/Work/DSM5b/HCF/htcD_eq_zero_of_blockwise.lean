import Mathlib
import Submission.Work.DSM5b.HCF.GenSurj
import Submission.Work.DSM5b.HCF.HtcAboveAux

/-!
# Blockwise vanishing of the honest tuple differential

For a coefficient system `𝒜` and a cochain `z` in degree `q` of the graded piece
`exactlyCoeff 𝒜 k` of the size filtration, the honest tuple differential `htcD q z`
vanishes as soon as *each* of its `k`-element blocks is a cocycle of the surjection
complex over the corresponding `k`-element subset.

This is the converse (in the degree-`q` case) of
`Work.DSM5b.HCF.gsurjD_zBlk_at`, which shows that the block of a cocycle is a cocycle
of the surjection complex.  The two facts are combined in
`Work.DSM5b.HCF.htcD_exact_above`.

The proof is a direct evaluation: at a tuple `τ : Fin (q+2) → ι`, either the range of
`τ` has exactly `k` elements — in which case the alternating sum is *literally* the
value of `gsurjD` at `τ` on the block of `z` (the two differ only in the proof of the
inclusion, which is irrelevant) — or the range does not have `k` elements, in which
case the coefficient module is a subsingleton and every summand vanishes.

Note that the hypothesis `hk : q + 1 = k` is not needed for this implication.
-/

namespace Work.DSM5b.HCF

universe u

theorem htcD_eq_zero_of_blockwise {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (k q : ℕ) (hk : q + 1 = k)
    (z : (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k).Htc q)
    (hblocks : ∀ (S₀ : Finset ι), S₀.card = k →
      Work.DSM5b.HCF.gsurjD (R := R) S₀ ((Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k).M S₀) q
        (fun σ : Work.DSM5b.HCF.GSurjIdx S₀ q =>
          (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k).res (le_of_eq σ.2) (z σ.1)) = 0) :
    Work.DSM5b.CoeffSys.htcD (R := R)
      (𝒜 := Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k) q z = 0 := by
  classical
  funext τ
  rw [Work.DSM5b.CoeffSys.htcD_apply]
  by_cases hτ : (Work.DSM5b.tupRng τ).card = k
  · -- The range of `τ` is a `k`-element block: compare with the value of `gsurjD`.
    have hb := congrFun (hblocks (Work.DSM5b.tupRng τ) hτ) ⟨τ, rfl⟩
    rw [Work.DSM5b.HCF.gsurjD_apply] at hb
    have hgoal : (∑ i : Fin (q + 2), (-1 : R) ^ (i : ℕ) •
          (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k).res (Work.DSM5b.tupRng_del_subset i τ)
            (z (Work.DSM5b.tupDel i τ)))
        = ∑ i : Fin (q + 2), (if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ) = Work.DSM5b.tupRng τ
            then (-1 : R) ^ (i : ℕ) •
              (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k).res (le_of_eq h) (z (Work.DSM5b.tupDel i τ))
            else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ) = Work.DSM5b.tupRng τ
      · -- The deletion keeps the range: the two summands differ only in the inclusion proof.
        rw [dif_pos h]
      · -- The deletion loses the range: the coefficient module is a subsingleton.
        rw [dif_neg h]
        have hc : (Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ)).card ≠ k := by
          intro hcon
          exact h (Finset.eq_of_subset_of_card_le (Work.DSM5b.tupRng_del_subset i τ)
            (by rw [hcon, hτ]))
        haveI := Work.DSM5b.HCF.subsingleton_coeff_exactlyCoeff 𝒜 k hc
        rw [Subsingleton.elim (z (Work.DSM5b.tupDel i τ)) 0, map_zero, smul_zero]
    exact hgoal.trans hb
  · -- The range of `τ` is not a `k`-element block: everything is a subsingleton.
    haveI := Work.DSM5b.HCF.subsingleton_coeff_exactlyCoeff 𝒜 k hτ
    exact Subsingleton.elim _ _

end Work.DSM5b.HCF
