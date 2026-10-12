import ChallengeDeps
import Submission.Work.KinPSuperadd.Engine
import Submission.Work.KinPSuperadd.rayleigh_diagSlotWord
import Submission.Work.KinPSuperadd.slotSplit_cnPlus
import Submission.Work.KinPSuperadd.slotSplit_pDiagForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `KinPSuperadd.Superadd` — the grouping trick for the faithful (`pDiagForm`) word

`Work.SmallBoxA0`'s SESSION-290 report names the ONE open obligation of the
re-pointed (`𝒯_B`, `kinPWord`) small-box energy: the FS grouping trick
`e_B(n) ≥ m·e_B(n′) + e_B(n″)` needs the kinetic word to DECOMPOSE over the
particle-group decomposition, and the corpus's `kinPWord` — built from `modeP`,
a square of a sum over the particles — does not
(`Obstruction.not_slotSplit_modePGen`, `Obstruction.not_slotSplit_pModeContent`).

This module resolves the obligation in the only way it can be resolved: it
IDENTIFIES the correct word and proves the grouping theorem for it.

* `slotSplit_diagSlotWord` — the faithful transcription of FS's one-particle
  `𝒯_B = Q_Bχ_B[√−Δ−c]₊²χ_BQ_B`, namely the sum-of-squares word
  `diagSlotWord s c₀ cgap = cgap·cnPlus + pDiagForm s (fsKinCoeff c₀)`
  (`pDiagForm = Σ_i (one-particle form of slot i)`, the corpus's
  `Σ_i Q_iχ_iF(√−Δ_i)χ_iQ_i`), IS block-splittable.  (From the PROVED
  `slotSplit_cnPlus` and `slotSplit_pDiagForm` by `SlotSplit.add`/`const_mul`.)
* `slotEB_superadd_diagSlotWord` — hence its `eB`-level ground energy is
  superadditive in the particle number, by the ENGINE
  (`Engine.slotEB_superadd_of_slotSplit`), with the Rayleigh hypothesis supplied
  by `rayleigh_diagSlotWord` and the potential-side integrability by the
  corpus's `chosen_qLHSden{,1,2}_integrableOn`.
* `diagKinPeBAt_superadd`, `diagKinPeB_superadd`, `diagKinPeB_group_superadd` —
  the same in the `Work.SmallBoxA0.kinPeB` indexing, including the
  `n = m·n′ + n″` group form.

So: **the FS grouping trick IS available for the faithful transcription of FS's
`𝒯_B`, and it is exactly the `modeP` square-of-a-sum transcription that
obstructs it.**
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.KinPSuperadd

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The faithful (`pDiagForm`) small-box ground energy at a GENERAL particle
count `N` (the `slotEB` of `diagSlotWord`; `diagKinPeB n` is this at `N = n+1`). -/
noncomputable def diagKinPeBAt (N : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) : ℝ :=
  slotEB s μ (wPairC s v) (wPairC s (g0 v h)) (diagSlotWord s c₀ cgap) N

/-- `diagKinPeB n` is `diagKinPeBAt` at `N = n+1` (definitional). -/
lemma diagKinPeB_eq_at (n : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) :
    diagKinPeB n s μ v h c₀ cgap = diagKinPeBAt (n + 1) s μ v h c₀ cgap := rfl

/-- **The faithful word is block-splittable.**  `diagSlotWord s c₀ cgap =
cgap·cnPlus + pDiagForm s (fsKinCoeff c₀)`: a sum of ONE-particle forms over the
particles (`cnPlus = Σ_i ‖Q_iΦ‖²` and `pDiagForm = Σ_i (one-particle form of
slot i)`), hence `SlotSplit`. -/
theorem slotSplit_diagSlotWord (s c₀ cgap : ℝ) (hcgap : 0 ≤ cgap)
    (hint : ∀ (M : ℕ) (Ψ : X M → ℝ), ContDiff ℝ ∞ Ψ →
      Integrable (fun p : ℝ³ => fsKinCoeff c₀ ‖p‖ * ∑ i : Fin M, (s ^ 3)⁻¹ *
        ∫ x in abox M s, ‖pSlotAmp s p Ψ i x‖ ^ 2)) :
    SlotSplit s (diagSlotWord s c₀ cgap) := by
  have h1 : SlotSplit s (fun N (Φ : X N → ℝ) => cgap * cnPlus s Φ) :=
    (slotSplit_cnPlus s).const_mul cgap
  have h2 : SlotSplit s (fun N (Φ : X N → ℝ) => pDiagForm s (fsKinCoeff c₀) Φ) :=
    slotSplit_pDiagForm s (fsKinCoeff c₀) (fsKinCoeff_nonneg c₀) hint
  exact h1.add h2

/-- **The grouping theorem for the faithful word**: its `eB`-level ground
energy is superadditive in the particle number — the FS group trick. -/
theorem slotEB_superadd_diagSlotWord {N1 N2 : ℕ} {s R μ c₀ cgap : ℝ} {v : ℝ³ → ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) (hcgap : 0 ≤ cgap)
    (hint : ∀ (M : ℕ) (Ψ : X M → ℝ), ContDiff ℝ ∞ Ψ →
      Integrable (fun p : ℝ³ => fsKinCoeff c₀ ‖p‖ * ∑ i : Fin M, (s ^ 3)⁻¹ *
        ∫ x in abox M s, ‖pSlotAmp s p Ψ i x‖ ^ 2)) :
    diagKinPeBAt N1 s μ v h c₀ cgap + diagKinPeBAt N2 s μ v h c₀ cgap
      ≤ diagKinPeBAt (N1 + N2) s μ v h c₀ cgap :=
  slotEB_superadd_of_slotSplit (s := s) (μ := μ) hs
    (w := wPairC s v) (w1 := wPairC s (g0 v h)) (wPairC_nonneg hv_nonneg s)
    (slotSplit_diagSlotWord s c₀ cgap hcgap hint)
    (fun N Ψ hΨ =>
      rayleigh_diagSlotWord hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ hcgap hint hΨ)
    (fun N1 N2 Φ hΦ =>
      chosen_qLHSden1_integrableOn hs hR hv_nonneg hvrad hv_memL1 hv_supp h hRs hΦ.continuous)
    (fun N1 N2 Φ hΦ =>
      chosen_qLHSden2_integrableOn hs hR hv_nonneg hvrad hv_memL1 hv_supp h hRs hΦ.continuous)
    (fun N1 N2 Φ hΦ =>
      chosen_qLHSden_integrableOn hs hR hv_nonneg hvrad hv_memL1 hv_supp h hRs hΦ.continuous)
    N1 N2

/-- **The FS grouping trick at the `Work.SmallBoxA0.kinPeB` indexing.**  The
faithful small-box ground energy is superadditive in the particle number:
`diagKinPeB n₁ + diagKinPeB n₂ ≤ diagKinPeB (n₁+n₂+1)`. -/
theorem diagKinPeB_superadd {n1 n2 : ℕ} {s R μ c₀ cgap : ℝ} {v : ℝ³ → ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) (hcgap : 0 ≤ cgap)
    (hint : ∀ (M : ℕ) (Ψ : X M → ℝ), ContDiff ℝ ∞ Ψ →
      Integrable (fun p : ℝ³ => fsKinCoeff c₀ ‖p‖ * ∑ i : Fin M, (s ^ 3)⁻¹ *
        ∫ x in abox M s, ‖pSlotAmp s p Ψ i x‖ ^ 2)) :
    diagKinPeB n1 s μ v h c₀ cgap + diagKinPeB n2 s μ v h c₀ cgap
      ≤ diagKinPeB (n1 + n2 + 1) s μ v h c₀ cgap := by
  have hkey := slotEB_superadd_diagSlotWord (N1 := n1 + 1) (N2 := n2 + 1)
    hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ hcgap hint
  rw [diagKinPeB_eq_at n1, diagKinPeB_eq_at n2, diagKinPeB_eq_at (n1 + n2 + 1)]
  have hidx : n1 + n2 + 1 + 1 = n1 + 1 + (n2 + 1) := by omega
  rw [hidx]
  exact hkey

/-- **The `n = m·n′ + n″` group form** for the faithful word, in the
`diagKinPeBAt` indexing: `m` groups of `N′` particles plus a remainder of `N″`
particles. -/
theorem diagKinPeBAt_group_superadd {m N' N'' : ℕ} {s R μ c₀ cgap : ℝ} {v : ℝ³ → ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) (hcgap : 0 ≤ cgap)
    (hint : ∀ (M : ℕ) (Ψ : X M → ℝ), ContDiff ℝ ∞ Ψ →
      Integrable (fun p : ℝ³ => fsKinCoeff c₀ ‖p‖ * ∑ i : Fin M, (s ^ 3)⁻¹ *
        ∫ x in abox M s, ‖pSlotAmp s p Ψ i x‖ ^ 2)) :
    (m : ℝ) * diagKinPeBAt N' s μ v h c₀ cgap + diagKinPeBAt N'' s μ v h c₀ cgap
      ≤ diagKinPeBAt (m * N' + N'') s μ v h c₀ cgap := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hn : (m + 1) * N' + N'' = (m * N' + N'') + N' := by ring
      have hsa := slotEB_superadd_diagSlotWord (N1 := m * N' + N'') (N2 := N')
        hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ hcgap hint
      have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num [Nat.cast_add]
      have hl : ((m + 1 : ℕ) : ℝ) * diagKinPeBAt N' s μ v h c₀ cgap
            + diagKinPeBAt N'' s μ v h c₀ cgap
          = (m : ℝ) * diagKinPeBAt N' s μ v h c₀ cgap
            + diagKinPeBAt N'' s μ v h c₀ cgap
            + diagKinPeBAt N' s μ v h c₀ cgap := by
        rw [hc]; ring
      rw [hl, hn]
      nlinarith [ih, hsa]

/-! ## The one-sided (`BlockSuperadd`) instances

These are the sharp form of the grouping requirement
(`BlockSuperadd.blockSuperadd`), for the words the chapter treats. -/

/-- The delivered honest box kinetic satisfies the sharp one-sided
superadditivity. -/
theorem blockSuperadd_kinWord (s : ℝ) :
    BlockSuperadd s (fun N Φ => kinWord N s Φ) :=
  (slotSplit_kinWord s).blockSuperadd

/-- The excited count satisfies the sharp one-sided superadditivity. -/
theorem blockSuperadd_cnPlus (s : ℝ) :
    BlockSuperadd s (fun N (Φ : X N → ℝ) => cnPlus s Φ) :=
  (slotSplit_cnPlus s).blockSuperadd

/-- **The faithful word satisfies the sharp one-sided superadditivity** — the
inequality the FS grouping argument consumes. -/
theorem blockSuperadd_diagSlotWord (s c₀ cgap : ℝ) (hcgap : 0 ≤ cgap)
    (hint : ∀ (M : ℕ) (Ψ : X M → ℝ), ContDiff ℝ ∞ Ψ →
      Integrable (fun p : ℝ³ => fsKinCoeff c₀ ‖p‖ * ∑ i : Fin M, (s ^ 3)⁻¹ *
        ∫ x in abox M s, ‖pSlotAmp s p Ψ i x‖ ^ 2)) :
    BlockSuperadd s (diagSlotWord s c₀ cgap) :=
  (slotSplit_diagSlotWord s c₀ cgap hcgap hint).blockSuperadd

end Work.KinPSuperadd
