import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.Est1.T2algebra
import Submission.Work.BoseB7A.PH_subset_PHq_sub
import Submission.Work.BoseB7A.Prep
import Submission.Work.BoseB7A.kernel_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.Est1.OpZ_kappa` — the squeezed-commutator coefficient of `[Ã_s, b_q]`

`Est1.T2algebra.Atil_comp_bOp` gives the commutator

  `[Ã_s, b_q] = (α_q·ccrX s (−q) − β_{sk}·ccrX (−s) q) • 1`,   `β_{sk} = α_kα_{s-k}`,

and the estimate of `lem:EstimatesOnQ3-js` needs the *scalar in front* to be small
on the modes that occur: `s ∈ supp f_L`, `k ∈ P_H`, `q ∈ P_H^q`.  This module proves

  `|α_q·ccrX s (−q) − β_{sk}·ccrX (−s) q| ≤ 128·K₀²·𝓁·η`.

The proof is a two-term split.  Both commutator kernels carry the factor
`K₀η` (`Q3Kernel.ccrX_small`, applied at `(−q)` and at `(−s)`; the region `P_H^q`
is even and `f_L` is even).  Both Bogoliubov coefficients are `≤ 64K₀𝓁` on
`P_H^q`:

* `|α_q| ≤ 64K₀𝓁` directly (`kernel_basic`, FS `eq:alphaInPH`);
* `|β_{sk}| = |α_k||α_{s-k}| ≤ (64K₀𝓁)² ≤ 64K₀𝓁`, because `k ∈ P_Hset` lies in
  `P_Hq` (`PH_subset_PHq_sub`) and `s − k ∈ P_Hq` as well (same lemma), and
  `64K₀𝓁 ≤ 96K₀𝓁 ≤ 1` (`lille_threshold`).

Adding the two terms gives `64K₀²𝓁η + 64K₀²𝓁η = 128K₀²𝓁η`.  The whole
smallness is the diluteness `96K₀𝓁 ≤ 1`; the hypothesis `b₀ ≤ E.b` is part of the
interface and is not used.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A.Est1

set_option linter.unusedVariables false

theorem OpZ_kappa (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseB7A.Q3Kernel K₀ F T E →
        ∀ (s k q : Mode), E.fL s ≠ 0 → k ∈ F.PHset E → F.PHq E.KH E.aScat q →
          |E.alpha q * T.ccrX s (-q) - Work.BoseB7A.Est1.bA E s k * T.ccrX (-s) q|
            ≤ 128 * K₀ ^ 2 * E.lille * Work.BoseB7A.eta E := by
  obtain ⟨t₁, ht₁, hkb⟩ := Work.BoseB7A.kernel_basic K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, hph⟩ := Work.BoseB7A.PH_subset_PHq_sub K₀ b₀ hb₀
  obtain ⟨t₃, ht₃, hlil⟩ := Work.BoseB7A.lille_threshold K₀
  refine ⟨min t₁ (min t₂ t₃), lt_min ht₁ (lt_min ht₂ ht₃), ?_⟩
  intro Mode _ _ _ F T E hv htle hb hK s k q hfL hk hq
  have ht1 : hv.t ≤ t₁ := le_trans htle (min_le_left _ _)
  have ht2 : hv.t ≤ t₂ := le_trans htle (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht3 : hv.t ≤ t₃ := le_trans htle (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the `α`-bound of the kernel regime, and the two region facts
  obtain ⟨_, _, _, hαbd, _⟩ := hkb F T E hv ht1 hb hK
  obtain ⟨hPHq, hsubq⟩ := hph F T E hv ht2 hb hK
  -- `𝓁 ≥ 0`
  have hlille_nn : 0 ≤ E.lille := by
    have h1 : 0 < E.mu := Work.BoseB7.mu_pos E hv
    have h2 : 0 < E.aScat := hv.a_pos
    simp only [Work.BoseB7.Q3Env.lille, Work.BoseB7.lille]
    exact mul_nonneg (mul_nonneg (le_of_lt h1) (pow_nonneg (le_of_lt h2) 3)) (sq_nonneg _)
  -- the diluteness `96 K₀𝓁 ≤ 1`
  have hsmall96 : 96 * K₀ * E.lille ≤ 1 := by
    have h1 : 96 * max K₀ 0 * E.lille ≤ 1 := hlil E hv ht3
    have h2 : K₀ ≤ max K₀ 0 := le_max_left _ _
    nlinarith [h1, h2, hlille_nn]
  have hkP : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
  have hkq : F.PHq E.KH E.aScat k := hPHq k hkP
  have hskq : F.PHq E.KH E.aScat (s - k) := hsubq s k hfL hk
  have hqneg : F.PHq E.KH E.aScat (-q) := by
    simpa only [Work.BoseB7.FockData.PHq, F.kmom_neg, norm_neg] using hq
  have hfLneg : E.fL (-s) ≠ 0 := by
    rw [hK.fL_even s]; exact hfL
  -- the three coefficient bounds of `kernel_basic`
  have hαq : |E.alpha q| ≤ 64 * K₀ * E.lille := hαbd q hq
  have hαk : |E.alpha k| ≤ 64 * K₀ * E.lille := hαbd k hkq
  have hαsk : |E.alpha (s - k)| ≤ 64 * K₀ * E.lille := hαbd (s - k) hskq
  have hpos64 : 0 ≤ 64 * K₀ * E.lille := le_trans (abs_nonneg _) hαq
  have hle64 : 64 * K₀ * E.lille ≤ 1 := by nlinarith [hsmall96, hpos64]
  -- `|β_{sk}| ≤ 64 K₀𝓁`
  have hbA : |bA E s k| ≤ 64 * K₀ * E.lille := by
    have h1 : |bA E s k| = |E.alpha k| * |E.alpha (s - k)| := by
      simp only [bA, abs_mul]
    have h2 : |E.alpha k| * |E.alpha (s - k)| ≤ (64 * K₀ * E.lille) * (64 * K₀ * E.lille) :=
      mul_le_mul hαk hαsk (abs_nonneg _) hpos64
    have h3 : (64 * K₀ * E.lille) * (64 * K₀ * E.lille) ≤ 64 * K₀ * E.lille := by
      nlinarith [hpos64, hle64]
    rw [h1]; linarith
  -- the two commutator kernels
  have hc1 : |T.ccrX s (-q)| ≤ K₀ * eta E := hK.ccrX_small s (-q) hfL hqneg
  have hc2 : |T.ccrX (-s) q| ≤ K₀ * eta E := hK.ccrX_small (-s) q hfLneg hq
  have hterm1 : |E.alpha q| * |T.ccrX s (-q)| ≤ (64 * K₀ * E.lille) * (K₀ * eta E) :=
    mul_le_mul hαq hc1 (abs_nonneg _) hpos64
  have hterm2 : |bA E s k| * |T.ccrX (-s) q| ≤ (64 * K₀ * E.lille) * (K₀ * eta E) :=
    mul_le_mul hbA hc2 (abs_nonneg _) hpos64
  calc |E.alpha q * T.ccrX s (-q) - bA E s k * T.ccrX (-s) q|
      ≤ |E.alpha q * T.ccrX s (-q)| + |bA E s k * T.ccrX (-s) q| := abs_sub _ _
    _ = |E.alpha q| * |T.ccrX s (-q)| + |bA E s k| * |T.ccrX (-s) q| := by
        rw [abs_mul, abs_mul]
    _ ≤ (64 * K₀ * E.lille) * (K₀ * eta E) + (64 * K₀ * E.lille) * (K₀ * eta E) :=
        add_le_add hterm1 hterm2
    _ = 128 * K₀ ^ 2 * E.lille * eta E := by ring

end Work.BoseB7A.Est1
