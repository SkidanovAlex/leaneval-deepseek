/-
# The Young inequality for the variational norm over a countable `ℓ¹` combination

This file proves `Work.KMTAreas.A7.variationalNorm_tsum_conv`: the `r`-variational norm of the
pointwise sum of a `ℤ`-indexed family of sequences is dominated by the `ℓ¹`-weighted sum of the
variational norms,

  `V^r(∑'_j K j · u_j) ≤ ∑'_j ‖K j‖ · V^r(u_j)`,

the "Young inequality" that lets one pass from the variation of the pieces of a decomposition to
the variation of the sum.

The proof is the standard one, split into the two defining suprema of the variational norm:
* the pointwise supremum part is bounded by the unconditional inequality
  `‖∑'_j b_j‖ₑ ≤ ∑'_j ‖b_j‖ₑ`;
* the variation part is bounded by writing the vector of `N`-differences of the sum as the `tsum`
  of the vectors of the `N`-differences of the columns, for which summability in the `ℓ^r`-topology
  is obtained from the finiteness of the right-hand side.  This last step is the reason for the
  `by_cases` on the value of the right-hand side: if it is `⊤` the claim is trivial, and otherwise
  `‖g j n‖ ≤ V^r(g_j)` bounds every column by a summable one.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

open scoped ENNReal NNReal BigOperators

/-- Summability is transported by `WithLp.toLp` on a finite coordinate set (the topology of
`PiLp r (fun _ : Fin J => ℂ)` is the product topology, so `WithLp.toLp r` is a linear
homeomorphism). -/
private theorem summable_toLp_fin {ι : Type*} (r : NNReal) (J : ℕ)
    (v : ι → Fin J → ℂ) :
    Summable (fun j => WithLp.toLp r (v j)) ↔ Summable v := by
  constructor
  · intro hv
    have h := hv.map ((PiLp.continuousLinearEquiv r ℂ (fun _ : Fin J => ℂ)).toContinuousLinearMap)
      (by fun_prop)
    exact h.congr (fun j => rfl)
  · intro hv
    have h := hv.map ((PiLp.continuousLinearEquiv r ℂ (fun _ : Fin J => ℂ)).symm.toContinuousLinearMap)
      (by fun_prop)
    exact h.congr (fun j => rfl)

/-- The sum in a finite `PiLp` space is the `WithLp.toLp` of the coordinatewise sum: the
finite-dimensional continuous linear equivalence `PiLp.continuousLinearEquiv` transports `tsum`
from `Fin J → ℂ` to `WithLp r (Fin J → ℂ)`. -/
private theorem toLp_tsum_fin {ι : Type*} (r : NNReal) (J : ℕ) (v : ι → Fin J → ℂ)
    (hv : Summable v) :
    WithLp.toLp r (∑' j, v j) = ∑' j, WithLp.toLp r (v j) := by
  have _ := hv
  simpa using
    (PiLp.continuousLinearEquiv (r : ℝ≥0∞) ℂ (fun _ : Fin J => ℂ)).symm.map_tsum (f := v)

/-- **Young's inequality for the variational norm**, with a pointwise summability hypothesis: if
every column `j ↦ c j * w j n` is summable, then

  `V^r(n ↦ ∑'_j c j * w j n) ≤ ∑'_j ‖c j‖ · V^r(n ↦ w j n)`.

This is subadditivity of the variational norm together with positive homogeneity, for a countable
family of sequences. -/
private theorem variationalNorm_tsum_mul_le {r : NNReal} (hr : 1 ≤ r) (c : ℤ → ℂ)
    (w : ℤ → ℕ → ℂ) (hsum : ∀ n, Summable (fun j => c j * w j n)) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => ∑' j, c j * w j n)
      ≤ ∑' j, ‖c j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j) := by
  letI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  by_cases htop : (∑' j : ℤ, ‖c j‖ₑ *
      PointwiseErgodicTheorems.variationalNorm r (w j)) = ⊤
  · rw [htop]
    exact le_top
  · have hfin : (∑' j : ℤ, ‖c j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j)) < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    have hsup : (⨆ n, ‖∑' j, c j * w j n‖ₑ) ≤ ∑' j, ‖c j‖ₑ * (⨆ n, ‖w j n‖ₑ) := by
      refine iSup_le fun n => ?_
      refine (enorm_tsum_le_tsum_enorm (f := fun j => c j * w j n)).trans ?_
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [enorm_mul]
      exact mul_le_mul' le_rfl (le_iSup (fun n => ‖w j n‖ₑ) n)
    have hvar : Submission.PointwiseErgodicTheorems.varPart r (fun n => ∑' j, c j * w j n)
        ≤ ∑' j, ‖c j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j) := by
      refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
      set v : ℤ → Fin J → ℂ := fun j i => c j * (w j (N (i + 1)) - w j (N i)) with hv
      have hpoint : ∀ i : Fin J,
          (∑' j, c j * w j (N (i + 1))) - (∑' j, c j * w j (N i)) = ∑' j, v j i := by
        intro i
        refine (Summable.tsum_sub (hsum (N (i + 1))) (hsum (N i))).symm.trans
          (tsum_congr fun j => ?_)
        simp only [hv]
        ring
      have hbdd : ∀ j, ‖WithLp.toLp r (v j)‖ₑ
          ≤ ‖c j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j) := by
        intro j
        have hvj : v j = c j • (fun i : Fin J => w j (N (i + 1)) - w j (N i)) := by
          funext i
          simp only [hv, Pi.smul_apply, smul_eq_mul]
        have h1 : ‖WithLp.toLp r (v j)‖ₑ
            = ‖c j‖ₑ * ‖WithLp.toLp r
                (fun i : Fin J => w j (N (i + 1)) - w j (N i))‖ₑ := by
          rw [hvj, WithLp.toLp_smul, enorm_smul]
        rw [h1]
        refine mul_le_mul' le_rfl ?_
        rw [← ofReal_norm]
        exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))
      have hsu : (∑' j, ‖WithLp.toLp r (v j)‖ₑ) < ⊤ := by
        refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hbdd) ?_
        refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => ?_) hfin
        calc ‖c j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j)
            ≤ ‖c j‖ₑ * ((⨆ n, ‖w j n‖ₑ)
                + Submission.PointwiseErgodicTheorems.varPart r (w j)) :=
              mul_le_mul' le_rfl le_add_self
          _ = ‖c j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j) := by
              rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
      have hvS : Summable v :=
        (summable_toLp_fin r J v).mp
          (Summable.of_norm (tsum_enorm_ne_top_iff_summable_norm.mp (ne_of_lt hsu)))
      have hF : (fun i : Fin J => (∑' j, c j * w j (N (i + 1))) - (∑' j, c j * w j (N i)))
          = ∑' j, v j := by
        funext i
        rw [Pi.tsum_apply hvS]
        exact hpoint i
      calc ENNReal.ofReal ‖WithLp.toLp r
            (fun i : Fin J => (∑' j, c j * w j (N (i + 1))) - (∑' j, c j * w j (N i)))‖
          = ‖∑' j, WithLp.toLp r (v j)‖ₑ := by
              rw [hF, toLp_tsum_fin r J v hvS, ofReal_norm]
        _ ≤ ∑' j, ‖WithLp.toLp r (v j)‖ₑ := enorm_tsum_le_tsum_enorm
        _ ≤ ∑' j, ‖c j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j) :=
            ENNReal.tsum_le_tsum hbdd
    have hR : (∑' j : ℤ, ‖c j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j))
        = (∑' j, ‖c j‖ₑ * (⨆ n, ‖w j n‖ₑ))
          + (∑' j, ‖c j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j)) := by
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun j => by
        simp only [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add, mul_add]
    rw [hR, Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
    exact add_le_add hsup hvar

/-- **Young's inequality for the variational norm over `ℤ`.**  For an arbitrary family of
sequences `g : ℤ → ℕ → ℂ` and coefficients `c : ℤ → ℂ`,

  `V^r(n ↦ ∑'_j c j * g j n) ≤ ∑'_j ‖c j‖ · V^r(n ↦ g j n)`.

No summability hypothesis is needed: if the right-hand side is `⊤` the claim is trivial, and
otherwise `‖g j n‖ ≤ V^r(g_j)` for every `j`, so the finiteness of the right-hand side makes every
column `j ↦ c j * g j n` summable. -/
private theorem variationalNorm_tsum_le_gen (r : NNReal) (hr : 1 ≤ r) (c : ℤ → ℂ)
    (g : ℤ → ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ, c j * g j n)
      ≤ ∑' j : ℤ, ‖c j‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => g j n) := by
  by_cases htop : (∑' j : ℤ, ‖c j‖ₑ *
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => g j n)) = ⊤
  · rw [htop]
    exact le_top
  · refine variationalNorm_tsum_mul_le hr c g ?_
    intro n
    refine Summable.of_norm (tsum_enorm_ne_top_iff_summable_norm.mp (ne_of_lt ?_))
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => ?_) (lt_top_iff_ne_top.mpr htop)
    rw [enorm_mul]
    exact mul_le_mul' le_rfl
      (enorm_apply_le_variationalNorm (r := r) (fun n : ℕ => g j n) n)

theorem variationalNorm_tsum_conv {r : NNReal} (hr : 1 ≤ r) (K : ℤ → ℂ)
    (hK : Summable fun j : ℤ => ‖K j‖) (u : ℕ → ℤ → ℂ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' j : ℤ, K j * u n (x - j))
      ≤ ∑' j : ℤ, ENNReal.ofReal ‖K j‖ *
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n (x - j)) := by
  simpa only [ofReal_norm] using
    variationalNorm_tsum_le_gen r hr K (fun j n => u n (x - j))

end Work.KMTAreas.A7
