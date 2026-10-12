import ChallengeDeps
import Submission.Work.KinPSuperadd.slotEB_perState_of_blockSuperadd
import Submission.Work.KinPSuperadd.slotSplit_kinWord
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `KinPSuperadd.Engine` — the FS grouping theorem, isolated

FS's grouping trick (`n = m·n′ + n″`) for the small-box ground energy reduces to
TWO structural facts about the energy's **kinetic word** `K`:

* `SlotSplit s K` (`Defs.lean`) — `K` decomposes over the particle-group
  decomposition (the slice form of "`K` is a sum of one-particle forms over the
  particles");
* the **Rayleigh inequality** `slotEB s μ w w₁ K N · ‖Ψ‖² ≤ blockE s μ w w₁ K N Ψ`
  for smooth `Ψ` — which is the defining property of the infimum `slotEB`,
  available for every word that is bounded below.

`slotEB_superadd_of_slotSplit` below is the whole mechanism: those two facts,
plus the (already proved, in `Work.SmallBoxSuperadd` / `SboxESlice`) block split
of the potential word and its nonnegativity on the cross-group pairs, give

    slotEB K N₁ + slotEB K N₂ ≤ slotEB K (N₁ + N₂) .

The corpus's own `SboxEB.eB_superadd_chosen` is the instance at
`K := kinWord`; `eB_superadd_via_engine` below *derives* it from the engine
(sanity check that the engine's hypotheses are satisfiable in the delivered
setting).  The instance at the faithful one-particle-sum transcription of FS's
`𝒯_B` is `Superadd.diagKinPeB_superadd`; the instance that does NOT exist is the
corpus's `kinPWord` (`Obstruction.not_slotSplit_modePGen`,
`Obstruction.not_slotSplit_pModeContent`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.KinPSuperadd

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **THE GROUPING THEOREM (FS's `e_B(n,μ) ≥ m·e_B(n′,μ) + e_B(n″,μ)`
mechanism, isolated).**  For any kinetic word `K` that is block-splittable
(`SlotSplit s K`) and whose `eB`-level infimum satisfies the Rayleigh inequality,
the small-box ground energy is superadditive in the particle number. -/
theorem slotEB_superadd_of_slotSplit {s μ : ℝ} (hs : 0 < s) {w w1 : ℝ³ → ℝ³ → ℝ}
    (hw : ∀ x y, 0 ≤ w x y)
    {K : ∀ N : ℕ, (X N → ℝ) → ℝ} (hK : SlotSplit s K)
    (hRay : ∀ (N : ℕ) (Ψ : X N → ℝ), ContDiff ℝ ∞ Ψ →
      slotEB s μ w w1 K N * (∫ x in abox N s, (Ψ x) ^ 2) ≤ blockE s μ w w1 K N Ψ)
    (hPot1 : ∀ ⦃N1 N2 : ℕ⦄ (Φ : X (N1 + N2) → ℝ), ContDiff ℝ ∞ Φ →
      IntegrableOn (fun x : X (N1 + N2) =>
        (Φ x) ^ 2 * qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x)
        (abox (N1 + N2) s) volume)
    (hPot2 : ∀ ⦃N1 N2 : ℕ⦄ (Φ : X (N1 + N2) → ℝ), ContDiff ℝ ∞ Φ →
      IntegrableOn (fun x : X (N1 + N2) =>
        (Φ x) ^ 2 * qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x)
        (abox (N1 + N2) s) volume)
    (hPot : ∀ ⦃N1 N2 : ℕ⦄ (Φ : X (N1 + N2) → ℝ), ContDiff ℝ ∞ Φ →
      IntegrableOn (fun x : X (N1 + N2) =>
        (Φ x) ^ 2 * qLHSden (N1 + N2) s μ w w1 x)
        (abox (N1 + N2) s) volume)
    (N1 N2 : ℕ) :
    slotEB s μ w w1 K N1 + slotEB s μ w w1 K N2 ≤ slotEB s μ w w1 K (N1 + N2) := by
  haveI : Nonempty (CSBox (N1 + N2) s) := nonempty_CSBox (N1 + N2) hs
  unfold slotEB
  refine le_ciInf (fun Φ : CSBox (N1 + N2) s => ?_)
  rw [le_div_iff₀ Φ.sq_pos]
  exact slotEB_perState hw hK hRay hPot1 hPot2 hPot Φ.contDiff

/-- **THE GROUPING THEOREM, SHARP FORM.**  The same conclusion with the ONE-SIDED
hypothesis `BlockSuperadd s K` (the inequality the grouping actually consumes)
plus the slice-integrability of the kinetic word.  `SlotSplit ⟹ BlockSuperadd`
(`SlotSplit.blockSuperadd`), so this is strictly more general than
`slotEB_superadd_of_slotSplit`; in particular it is the form whose hypothesis is
REFUTED for the `modeP` words
(`Obstruction.not_blockSuperadd_modePGen`,
`Obstruction.not_blockSuperadd_pModeContent`). -/
theorem slotEB_superadd_of_blockSuperadd {s μ : ℝ} (hs : 0 < s) {w w1 : ℝ³ → ℝ³ → ℝ}
    (hw : ∀ x y, 0 ≤ w x y)
    {K : ∀ N : ℕ, (X N → ℝ) → ℝ} (hK : BlockSuperadd s K)
    (hInt1 : ∀ ⦃N1 N2 : ℕ⦄ (Φ : X (N1 + N2) → ℝ), ContDiff ℝ ∞ Φ →
      IntegrableOn (fun wv : X N2 => K N1 (fun u => Φ (mergeBlock N1 N2 (u, wv))))
        (abox N2 s) volume)
    (hInt2 : ∀ ⦃N1 N2 : ℕ⦄ (Φ : X (N1 + N2) → ℝ), ContDiff ℝ ∞ Φ →
      IntegrableOn (fun uv : X N1 => K N2 (fun wv => Φ (mergeBlock N1 N2 (uv, wv))))
        (abox N1 s) volume)
    (hRay : ∀ (N : ℕ) (Ψ : X N → ℝ), ContDiff ℝ ∞ Ψ →
      slotEB s μ w w1 K N * (∫ x in abox N s, (Ψ x) ^ 2) ≤ blockE s μ w w1 K N Ψ)
    (hPot1 : ∀ ⦃N1 N2 : ℕ⦄ (Φ : X (N1 + N2) → ℝ), ContDiff ℝ ∞ Φ →
      IntegrableOn (fun x : X (N1 + N2) =>
        (Φ x) ^ 2 * qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x)
        (abox (N1 + N2) s) volume)
    (hPot2 : ∀ ⦃N1 N2 : ℕ⦄ (Φ : X (N1 + N2) → ℝ), ContDiff ℝ ∞ Φ →
      IntegrableOn (fun x : X (N1 + N2) =>
        (Φ x) ^ 2 * qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x)
        (abox (N1 + N2) s) volume)
    (hPot : ∀ ⦃N1 N2 : ℕ⦄ (Φ : X (N1 + N2) → ℝ), ContDiff ℝ ∞ Φ →
      IntegrableOn (fun x : X (N1 + N2) =>
        (Φ x) ^ 2 * qLHSden (N1 + N2) s μ w w1 x)
        (abox (N1 + N2) s) volume)
    (N1 N2 : ℕ) :
    slotEB s μ w w1 K N1 + slotEB s μ w w1 K N2 ≤ slotEB s μ w w1 K (N1 + N2) := by
  haveI : Nonempty (CSBox (N1 + N2) s) := nonempty_CSBox (N1 + N2) hs
  unfold slotEB
  refine le_ciInf (fun Φ : CSBox (N1 + N2) s => ?_)
  rw [le_div_iff₀ Φ.sq_pos]
  exact slotEB_perState_of_blockSuperadd hw hK hInt1 hInt2 hRay hPot1 hPot2 hPot Φ.contDiff

/-- **Consistency with the corpus.**  The engine, instantiated at the corpus's
own word `kinWord`, reproduces `SboxEB.eB_superadd_chosen`: the FS grouping
trick for the DELIVERED small-box energy is an instance of
`slotEB_superadd_of_slotSplit`.  (This is the sanity check that the engine's
hypotheses — `SlotSplit`, Rayleigh, the potential integrability — are exactly
the corpus's, and are satisfiable in the delivered setting.) -/
theorem eB_superadd_via_engine {N1 N2 : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) :
    eB N1 s μ v h + eB N2 s μ v h ≤ eB (N1 + N2) s μ v h := by
  have key := slotEB_superadd_of_slotSplit (s := s) (μ := μ) hs
    (w := wPairC s v) (w1 := wPairC s (g0 v h)) (wPairC_nonneg hv_nonneg s)
    (slotSplit_kinWord s)
    (fun N Ψ hΨ => by
      have h1 := sboxE_mul_le_chosen (N := N) hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ hΨ
      rw [slotEB_kinWord_eq_eB N s μ v h, blockE_eq]
      simpa only [sboxE] using h1)
    (fun N1 N2 Φ hΦ =>
      chosen_qLHSden1_integrableOn hs hR hv_nonneg hvrad hv_memL1 hv_supp h hRs hΦ.continuous)
    (fun N1 N2 Φ hΦ =>
      chosen_qLHSden2_integrableOn hs hR hv_nonneg hvrad hv_memL1 hv_supp h hRs hΦ.continuous)
    (fun N1 N2 Φ hΦ =>
      chosen_qLHSden_integrableOn hs hR hv_nonneg hvrad hv_memL1 hv_supp h hRs hΦ.continuous)
    N1 N2
  rwa [slotEB_kinWord_eq_eB N1 s μ v h, slotEB_kinWord_eq_eB N2 s μ v h,
       slotEB_kinWord_eq_eB (N1 + N2) s μ v h] at key

end Work.KinPSuperadd
