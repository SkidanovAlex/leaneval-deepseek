import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxWords_eq_zero_of_eq_zero_on_abox
import Submission.Work.BoseFixB2.Polar.wordB_box_local
import Submission.Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxWords_eq_zero_of_bI_eq_zero`

The per-box words `bFlat` (`= S = Σᵢ∫(P_{B,i}Φ)²`), `bQ` (`= n₊ = Σᵢ∫(Q_{B,i}Φ)²`) and
`bA2` (FS's pairing word at the box projections) all vanish as soon as the boxed `L²`-mass
`bI v μ Φ = ∫_{abox n (bSide v μ)} Φ²` does.

## Mathematics

`bI = 0` is the vanishing of the `L²`-norm of `Φ` on the analysis box `abox n ℓ`
(`ℓ = bSide v μ`), which is the *same* box that all three words are integrated over.  Since
`Φ` is continuous and the integrand `Φ²` is nonnegative, `bI = 0` forces `Φ ≡ 0` on the box
(pointwise, not only a.e. — this is the content of
`Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero`, which uses that the closed box is
the closure of its interior).  The box projections `P_{B,i}` and `Q_{B,i}` are built from the
box indicator `1_{B(u)}` and the box mean `|B|⁻¹∫_{B(u)} x_{i←z}dz`; because
`B(u) = dlBox ℓ d u ⊆ acube ℓ`, replacing the `i`-th coordinate of a configuration of `abox n ℓ`
by a point of `B(u)` keeps it inside the box, where `Φ` vanishes.  Hence every integrand above
is *pointwise* zero on `abox n ℓ`, and the three words vanish
(`Work.BoseFixB1.boxWords_eq_zero_of_eq_zero_on_abox`).  The `ℓ ≤ 0` case is degenerate: then
the box is a null set (`ℓ < 0`: empty; `ℓ = 0`: the single point `0`, which is null for
`n ≥ 1`), so all the defining integrals vanish *regardless* of `hI`, and for `n = 0` all sums
are empty.

Nothing here uses any property of the potential `v` or of the parameter `μ`; the hypothesis
`h : ScatSol v` only fixes the `w₁`-kernel appearing in `bA2`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1

/-- The sliding box `B(u) = dlBox ℓ d u` sits inside the analysis cube `acube ℓ`
(definitionally: it is the intersection with `acube ℓ`). -/
lemma bA_subset_acube (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    bA v μ u ⊆ Submission.BoseGases.acube (bSide v μ) :=
  Set.inter_subset_left

theorem boxWords_eq_zero_of_bI_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (h : Work.UBB.ScatSol v) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hI : Work.BoseFixB1.bI v μ Φ = 0) :
    Work.BoseFixB1.bFlat v μ Φ u = 0 ∧ Work.BoseFixB1.bQ v μ Φ u = 0
      ∧ Work.BoseFixB1.bA2 v h μ Φ u = 0 := by
  have hAc : bA v μ u ⊆ Submission.BoseGases.acube (bSide v μ) := bA_subset_acube v μ u
  rcases lt_or_ge (0 : ℝ) (bSide v μ) with hpos | hnonpos
  · -- positive box side: `bI = 0` makes `Φ` vanish pointwise on the box
    have h0 : ∀ y, y ∈ Submission.BoseGases.abox n (bSide v μ) → Φ y = 0 :=
      Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero hpos hΦ.continuous
        (by
          show Work.BoseKinLoc.sqNormB n (bSide v μ) Φ = 0
          rw [Work.BoseKinLoc.sqNormB]
          exact hI)
    obtain ⟨h1, h2, -, h3, -⟩ :=
      boxWords_eq_zero_of_eq_zero_on_abox (N := n) (a := bSide v μ) (volA := bV v μ u)
        (A := bA v μ u) hAc
        (Submission.BoseGases.wSmall1Pair h (bM v μ) (bSide v μ) (bD v μ) u)
        (fun _ => 0) (fun _ => 0) h0
    exact ⟨h1, h2, h3⟩
  · -- degenerate box side `ℓ ≤ 0`: the configuration box is a null set
    have hℓ : bSide v μ ≤ 0 := hnonpos
    rcases n with _ | m
    · -- no particles: every sum is empty
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [bFlat, bQ, bA2, Work.BoseFixB1S.boxFlatCount, Work.BoseFixB1S.boxQCount,
          Work.BoseFixB1.boxA2, Submission.BoseGases.pairSet]
    · -- at least one particle: `abox (m+1) ℓ` is null, so all its integrals vanish
      have hvol : (volume : Measure (Submission.BoseGases.X (m + 1)))
          (Submission.BoseGases.abox (m + 1) (bSide v μ)) = 0 :=
        Work.BoseFixB2.Polar.abox_volume_eq_zero_of_one_le_of_nonpos (m + 1)
          (Nat.le_add_left 1 m) _ hℓ
      refine ⟨?_, ?_, ?_⟩
      · show Work.BoseFixB1S.boxFlatCount (bV v μ u) (bSide v μ) (bA v μ u) Φ = 0
        rw [Work.BoseFixB1S.boxFlatCount]
        exact Finset.sum_eq_zero (fun i _ => setIntegral_measure_zero _ hvol)
      · show Work.BoseFixB1S.boxQCount (bV v μ u) (bSide v μ) (bA v μ u) Φ = 0
        rw [Work.BoseFixB1S.boxQCount]
        exact Finset.sum_eq_zero (fun i _ => setIntegral_measure_zero _ hvol)
      · show Work.BoseFixB1.boxA2 (bSide v μ) (bV v μ u) (bA v μ u) _ Φ = 0
        rw [Work.BoseFixB1.boxA2]
        exact Finset.sum_eq_zero (fun p _ => setIntegral_measure_zero _ hvol)

end Work.BoseFixB1
