import ChallengeDeps
import Submission.Work.BoseFixB1.sbWordSectorAdditiveAdm
import Submission.Work.BoseFixB1.sectorFPpartition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.PerSectorSmooth` — the per-sector statement at the **smooth**
# density, and its exact assembly back to the frozen target

This module replaces the refuted sharp-count residual `Work.BoseFixB1B.PerBoxSectorBoundG`
(whose `F`-weight was read at the *smooth* volume `chiMass` while FS read it at the *true* box
volume `boxMass`; `chiMass/boxMass → 0` on slabs, making it `1/χ̂` times stronger than FS's
`thm:smallbox` — see `FINDING_perBoxSectorBoundG_FALSE.md`, `FINDING_perSectorBoundG_FALSE.md`)
by the statement that is **localisable without any volume mismatch**.

## The statement

`PerSectorSmooth v h R` says: there are `ε₀ > 0`, `0 < c`, `0 ≤ C` such that for every admissible
`μ`, every `n`, every smooth symmetric box state `Φ`, every `u ∈ goodSet ℓ d μ` and every
occupancy sector `k ∈ {0,…,n}` of `B(u) = dlBox ℓ d u`,

    c·(∬w_{1,B(u)})·∫_{abox n ℓ} Φ_k²·F(t)  −  ½μ²·(∬w_{1,B(u)})·m_k  −  C·bErr·m_k
      ≤  sbKin v μ M u Φ_k  +  sbPot h μ u Φ_k ,

where

* `Φ_k = sectorPiece B k Φ` is the `k`-th occupancy sector piece
  (`Σ_k Φ_k(x)² = Φ(x)²` pointwise, `Work.FockBridge.sum_sectorPiece_sq`),
* `m_k = sectorMass ℓ B Φ k = ∫_{abox n ℓ} Φ_k²`,
* `t(x) = nCountB M ℓ d u x / chiMass M ℓ d u` is the **global smooth density** — a function of
  the *configuration alone*, independent of `k`,
* `F = psiWeight 1 μ = μ(t−μ)²/(t+μ)`,
* `bErr v R μ u = μ²(a v)((R/(ℓd))² + K_B³(μ(a v)³)^{1/2})·chiMass + μ(a v)` is *exactly* the
  frozen target's error bracket per unit norm (`PerBoxNames.bErr`),
* the RHS is the frozen localised word **of the sector piece** (`sbKin` = FS `eq:appTB`,
  `sbPot` = FS `eq:HBU` at the localised kernels).

## Why this is the right localisation (and why the sharp-count form was not)

Two *proved* facts make the assembly exact — and neither survives replacing the smooth density
`t` by the sharp index count `k/|B|`:

* **the exact partition** `Σ_k ∫ Φ_k²·F(t) = ∫ Φ²·F(t)`, valid because `F(t)` is a function of
  the configuration alone and does not know the sector index `k` (`sum_sectorPiece_sq`, pointwise);
* **sector additivity of the word**, `Work.BoseFixB1.sbWordSectorAdditiveAdm` (**PROVED**):
  `sbWord = Σ_k (sbKin(Φ_k) + sbPot(Φ_k))`.

Summing the per-sector inequality over `k` therefore reproduces the frozen target
`Work.BoseFixB1.PerBoxF` **with the same `c₁ = c` and the same `C`** — no bridge, no `K₀`, no
sharp count (see `perBoxFWeight_of_perSectorSmooth` below).  This is the direct re-run of FS
`thm:smallbox` at the **smooth kernels**, as `PERBOXF_ANALYSIS.md` §16 prescribes, with FS's
group decomposition available inside each fixed-`k` sector.

## What a prover should use

* `Work.BoseFixB1B.gapAtAll` (**PROVED**, every threshold `γ > 0`): states with
  `n₊(B) ≥ γ·n·‖Φ‖²` are already handled *without* any localisation hypothesis, so only the
  near-condensate regime needs the mean-field analysis;
* `Work.BoseFixB1.potsplit_localised_of_memLp` / `Work.BoseFixB1S.bqPotsplit` (**PROVED**): the
  localised potsplit `qLHSwordB = boxQSum`;
* `Work.BoseFixB1.boxQ0_ge_a0MainBox` (**PROVED**) with
  `Work.BoseFixB1.boxM1G_le_boxQ0_sub_a0MainLocBox`, `boxQ0_value`, `a0MainLocBox_slack`
  (`Submission/Work/BoseFixB1/boxQSum_ge_a0Main_add_A2.lean`, which also proves the whole
  four-pattern collapse `boxPInd_QInd_eq_means`, `pair_leftover_eq_means`,
  `pair_integral_reduce`): the per-box `A₀`-step, stated at the **box** volume `bV = boxMass`;
* `Work.BoseFixB1.perBoxF_pieces.sbKin_ge_mu_av_cnPlus` (**PROVED**): FS `eq:appgapestimate`,
  the `ε_T`-gap payment of `n₊`;
* `Work.BoseFixB1S.boxFlatSqJensen` (**PROVED**): `S² − S ≤ I·Pc`, the box Cauchy–Schwarz.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The per-sector statement at the smooth density** — FS `thm:smallbox` read on a single
occupancy sector `k` of the sliding box `B(u)`, with the `F`-weight at the *global* smooth
density `t = nCountB/chiMass` (a function of the configuration alone).  See the module docstring
for the reading of the objects and for the two proved facts that make its assembly exact. -/
def PerSectorSmooth (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (bSide v μ))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ goodSet (bSide v μ) (bD v μ) μ →
        ∀ k ∈ Finset.range (n + 1),
          c * (bW v h μ u *
              (∫ x in abox n (bSide v μ),
                (sectorPiece (bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
                  psiWeight 1 μ (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
                    / chiMass (bM v μ) (bSide v μ) (bD v μ) u)))
          - (1 / 2) * μ ^ 2 * bW v h μ u
              * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k
          - C * bErr v R μ u * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k
        ≤ sbKin (v := v) μ (bM v μ) u (sectorPiece (bA v μ u) k (Φ : X n → ℝ))
          + sbPot h μ u (sectorPiece (bA v μ u) k (Φ : X n → ℝ))

/-- **The assembly**: the per-sector statement at the smooth density implies the frozen target's
exact `∃ ε₀ c₁ C`-conclusion, **with the same `c₁` and `C`**.

Summing the per-sector inequality over `k ∈ {0,…,n}` gives

    c·(∬w_{1,B})·Σ_k ∫ Φ_k²F(t) − ½μ²(∬w_{1,B})·Σ_k m_k − C·bErr·Σ_k m_k
      ≤ Σ_k (sbKin(Φ_k) + sbPot(Φ_k)) ,

and the three identities `Σ_k ∫Φ_k²F(t) = ∫Φ²F(t)` (`sum_sectorPiece_sq`, pointwise, since `F(t)`
does not depend on `k`), `Σ_k m_k = ‖Φ‖²` (`Work.BoseFixB1B.sectorMass_sum`) and
`Σ_k (sbKin(Φ_k) + sbPot(Φ_k)) = sbWord` (`Work.BoseFixB1.sbWordSectorAdditiveAdm`) turn this into
`PerBoxF v h R c C μ n Φ u`. -/
theorem perBoxFWeight_of_perSectorSmooth {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hper : PerSectorSmooth v h R) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u := by
  obtain ⟨ε₀s, c, C, hε₀s, hc0, hC0, hmain⟩ := hper
  obtain ⟨ε₀w, hε₀w, hadd⟩ := sbWordSectorAdditiveAdm h hv hv1 hvrad hR hv_supp hav
  refine ⟨min ε₀s ε₀w, c, C, lt_min hε₀s hε₀w, hc0, hC0, fun μ hAdm n Φ u hu => ?_⟩
  have hAdms : Adm v ε₀s μ := Adm.mono (ε₀' := min ε₀s ε₀w) (ε₀ := ε₀s) hAdm (min_le_left _ _)
  have hAdmw : Adm v ε₀w μ := Adm.mono (ε₀' := min ε₀s ε₀w) (ε₀ := ε₀w) hAdm (min_le_right _ _)
  have hℓ : 0 < bSide v μ := adm_ell_pos hAdm
  have hd : 0 < bD v μ := adm_d_pos hAdm
  have hM : 1 ≤ bM v μ := by
    change 1 ≤ Work.BoseBox.mValue
    decide
  -- ## the per-sector inequalities, summed
  have hterm : (∑ k ∈ Finset.range (n + 1),
        (c * (bW v h μ u * (∫ x in abox n (bSide v μ),
            (sectorPiece (bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
              psiWeight 1 μ (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
                / chiMass (bM v μ) (bSide v μ) (bD v μ) u)))
          - (1 / 2) * μ ^ 2 * bW v h μ u
              * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k
          - C * bErr v R μ u * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k))
      ≤ ∑ k ∈ Finset.range (n + 1),
          (sbKin (v := v) μ (bM v μ) u (sectorPiece (bA v μ u) k (Φ : X n → ℝ))
            + sbPot h μ u (sectorPiece (bA v μ u) k (Φ : X n → ℝ))) :=
    Finset.sum_le_sum fun k hk => hmain μ hAdms n Φ u hu k hk
  -- ## the four rewrites
  -- (i) the `F`-partition (delegated bookkeeping: pointwise partition + integral/sum exchange)
  have hFint := Work.BoseFixB1.sectorFPpartition (v := v) (μ := μ) hAdm.1 n Φ u
  -- (ii) the mass sum and (iii) the word additivity
  have hmass : (∑ k ∈ Finset.range (n + 1),
        sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k)
      = Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
    simpa only [bSide, bA, bD, Work.BoseFixB1B.PBB, Work.BoseFixB1B.PBℓ,
      Work.BoseFixB1B.PBd] using Work.BoseFixB1B.sectorMass_sum (v := v) (μ := μ) Φ u
  have hword : sbWord h μ u (Φ : X n → ℝ)
      = ∑ k ∈ Finset.range (n + 1),
          (sbKin (v := v) μ (bM v μ) u (sectorPiece (bA v μ u) k (Φ : X n → ℝ))
            + sbPot h μ u (sectorPiece (bA v μ u) k (Φ : X n → ℝ))) := by
    simpa only [sbKin, sbPot, bA, bD, bM, bSide, Work.BoseFixB1B.PBB, Work.BoseFixB1B.PBℓ,
      Work.BoseFixB1B.PBd, Work.BoseFixB1B.PBM, Work.BoseFixB1B.PBeT]
      using hadd μ hAdmw n Φ u
  -- ## assemble: pull the constants out of the sums, then the three identities
  have hsub : (∑ k ∈ Finset.range (n + 1),
        (c * (bW v h μ u * (∫ x in abox n (bSide v μ),
            (sectorPiece (bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
              psiWeight 1 μ (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
                / chiMass (bM v μ) (bSide v μ) (bD v μ) u)))
          - (1 / 2) * μ ^ 2 * bW v h μ u
              * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k
          - C * bErr v R μ u * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k))
      = (∑ k ∈ Finset.range (n + 1),
            c * (bW v h μ u * (∫ x in abox n (bSide v μ),
                (sectorPiece (bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
                  psiWeight 1 μ (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
                    / chiMass (bM v μ) (bSide v μ) (bD v μ) u))))
        - (∑ k ∈ Finset.range (n + 1), (1 / 2) * μ ^ 2 * bW v h μ u
              * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k)
        - (∑ k ∈ Finset.range (n + 1), C * bErr v R μ u
              * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hA : (∑ k ∈ Finset.range (n + 1),
          c * (bW v h μ u * (∫ x in abox n (bSide v μ),
              (sectorPiece (bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
                psiWeight 1 μ (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
                  / chiMass (bM v μ) (bSide v μ) (bD v μ) u))))
      = c * (bW v h μ u * (∫ x in abox n (bSide v μ), (Φ x) ^ 2 * psiWeight 1 μ
            (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
              / chiMass (bM v μ) (bSide v μ) (bD v μ) u))) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hFint]
  have hB : (∑ k ∈ Finset.range (n + 1), (1 / 2) * μ ^ 2 * bW v h μ u
          * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k)
      = (1 / 2) * μ ^ 2 * bW v h μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
    rw [← Finset.mul_sum, hmass]
  have hD : (∑ k ∈ Finset.range (n + 1), C * bErr v R μ u
          * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k)
      = C * bErr v R μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
    rw [← Finset.mul_sum, hmass]
  rw [← hword] at hterm
  have hgoal : c * (bW v h μ u * (∫ x in abox n (bSide v μ), (Φ x) ^ 2 * psiWeight 1 μ
        (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
          / chiMass (bM v μ) (bSide v μ) (bD v μ) u)))
      - (1 / 2) * μ ^ 2 * bW v h μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
      - C * bErr v R μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
      ≤ sbWord h μ u (Φ : X n → ℝ) := by
    rw [← hA, ← hB, ← hD, ← hsub]
    exact hterm
  unfold Work.BoseFixB1.PerBoxF
  simp only [bW, bErr, bSide, bD, bM, bA] at hgoal
  exact le_of_eq_of_le (by ring) hgoal


end Work.BoseFixB1
