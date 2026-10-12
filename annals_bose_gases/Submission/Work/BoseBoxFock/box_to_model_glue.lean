import ChallengeDeps
import Submission.Work.BoseBoxFock.FRK.lowBandSqrt
import Submission.Work.BoseBoxFock.PotContactChem_holds
import Submission.Work.BoseBoxFock.PotCubicFreeU_exists
import Submission.Work.BoseBoxFock.PotPairRows_exists
import Submission.Work.BoseBoxFock.frkKin4Assemble
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.box_to_model_assembled` — the target, assembled (v2 route, `G`-credited)

The target `Work.BoseBoxFock.box_to_model` (`Submission/Work/BoseBoxFock/box_to_model.lean`,
statement frozen) begins `∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), …`, i.e. the lattice cut-off `Nmin` is
**ours to choose**.  This file assembles the target.

## The route (BF3c v2, the reserve transfer)

`Work.BoseBoxFock.frkCore` ("PART B — the reserve transfer") runs the whole row comparison at the
**strong** kinetic reserve `b/4 − b/100` on the `cnPlus` slot and credits the potential side with
the same amount `γ = b/4 − b/100` (the `G`-versions `FRK.FormRowKin4`, `FRK.FormW2BpotG`,
`FRK.PotCubicG`).  The two credits cancel in the proved `FRK.RowB_of_kin4_potG`, so

    box_to_model = box_to_model_assembled
      ⟸ box_to_model_of_row (PROVED, `assembly_of_row.lean`) + RowB_exists
    RowB_exists ⟸ FormRowKin4_holds_assembled (PROVED, `frkKin4Assemble.lean` —
                     the dictionary D4 + the two one-body rows)
                + FormW2BpotG_exists (PROVED, `frkCore.lean`)
                + RowB_of_kin4_potG (PROVED, `frkCore.lean`)
    FormW2BpotG_exists ⟸ PotContactChem_holds (PROVED)
                        + PotChiLin_exists (PROVED)
                        + PotPairRows_exists        ← leaf
                        + PotCubicG_exists (below)
                        + PotGroupsIntegrable_holds (PROVED, inside `FormW2BpotG_exists`)
    PotCubicG_exists ⟸ PotCubicFreeU_exists        ← leaf (the corrected cubic dictionary,
                        `k`-sum over `Finset.univ`, `k = 0` kept)
                      + FRK.potCubicZeroCell_exists ← leaf (the dropped `k = 0` lattice cell,
                        paid by `γℓ⁻²cnPlus` at `γ = 3/400`)
                      + FRK.lowBandSqrt_exists (PROVED) —
                        the low band `k ∉ F.PHset E`, FS `lem:Q3-splitting2` in the √-currency
                        (the low band `k ∉ F.PHset E`, FS `lem:Q3-splitting2` in the
                        √-currency `K·a·ℓ⁻³·√(2μℓ³𝓜#LB)`; raised to `max K 1` by the PROVED
                        `FRK.LowBandSqrt_mono_K`
                      + FRK.lowBandSqrtArith_exists (PROVED) at `2·max K 1`
                      (the two split the credit `b/4 − b/100 = 3/200` as `3/400` + `3/400`)

⚠ **Why the `G`-route and not the frozen `PotCubic`.**  FS prove the cubic low band with the error
`err₂ = C·a·n·(n₊/ℓ³)K_H^{-3/2}K_𝓜^{1/2} = C√X·ℓ⁻²n₊` (`err2_scale_identity`), which they absorb in
the *kinetic gap*; it is **not** bounded by `errKafz` for any fixed `C` (`err₂/errKafz ≍
2a³t^{-0.2423} → ∞` as `t = μa³ → 0`, see `FINDING_BF3c_s25_cubicAllowance.md` §2.2).  Hence the
frozen `PotGroupDefs.PotCubic` (`allowance = ½errKafz`) is not provable, while `FRK.PotCubicG`
(allowance `½errKafz + γℓ⁻²cnPlus`) is exactly FS's statement.  The γ-credit is *transferred from
the kinetic reserve*, so it cancels in `RowB_of_kin4_potG` and nothing extra reaches the target.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **The cubic row `FRK.PotCubicG` at a chosen cut-off** — the corrected dictionary
`FRK.PotCubicFreeU` (`k`-sum over **all** lattice labels, `k = 0` included) + the dropped `k = 0`
zero cell `FRK.PotCubicZeroCell` (paid by the gap `γℓ⁻²cnPlus`, `γ = 3/400`) + the low band
`FRK.LowBandSqrt` (`k ∉ PHset`, FS `lem:Q3-splitting2` in the √-currency). -/
theorem PotCubicG_exists (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      FRK.PotCubicG v h fc fu R J Nmin ε₀ C := by
  obtain ⟨Nmin, ε₁, C₁, hε₁, hC₁, hfree⟩ :=
    PotCubicFreeU_exists v h hv hv1 hvrad hR hv_supp hav fc fu J hB3
  obtain ⟨ε₃, C₃, hε₃, hC₃, hzero⟩ :=
    FRK.potCubicZeroCell_exists v h hv hv1 hvrad hR hv_supp hav fc fu J Nmin (γ := 3 / 400)
      (by norm_num)
  obtain ⟨ε₂, K, hε₂, hS⟩ :=
    FRK.lowBandSqrt_exists v h hv hv1 hvrad hR hv_supp hav fc fu J hB3 Nmin
  -- raise the √-currency constant to `max K 1` so that `LowBandSqrtArith` at `2·max K 1 ≥ 1`
  -- applies (`FRK.LowBandSqrtArith` needs its constant `≥ 1`)
  have hS' : FRK.LowBandSqrt v h fc fu J Nmin ε₂ (max K 1) :=
    FRK.LowBandSqrt_mono_K hav (le_max_left K 1) hS
  obtain ⟨ε₄, hε₄, hA⟩ :=
    FRK.lowBandSqrtArith_exists v h hav fc fu Nmin (2 * max K 1)
      (by linarith [le_max_right K 1])
  refine ⟨Nmin, min (min ε₁ ε₂) (min ε₃ ε₄), C₁ + C₃,
    lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄), add_nonneg hC₁ hC₃, ?_⟩
  exact FRK.PotCubicG_of_freeU_zero_sqrt v h hav fc fu R J Nmin ε₁ ε₂ ε₃ ε₄ C₁ C₃ (max K 1)
    (3 / 400) (le_trans zero_le_one (le_max_right K 1)) (le_refl _) hfree hzero hS' hA

/-- **`RowB` with the lattice cut-off chosen** (the v2 `G`-route). -/
theorem RowB_exists (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.RowB v h fc fu R J Nmin ε₀ C := by
  obtain ⟨Nmin, hpot⟩ :=
    FRK.FormW2BpotG_exists v h hv hv1 hvrad hR hv_supp hav fc fu J hB3
      ⟨fun _ => 0,
        PotContactChem_holds v h hv hv1 hvrad hR hv_supp hav fc fu J hB3 (fun _ => 0)⟩
      (PotChiLin_exists v h hv hv1 hvrad hR hv_supp hav fc fu J hB3)
      (PotPairRows_exists v h hv hv1 hvrad hR hv_supp hav fc fu J hB3)
      (PotCubicG_exists v h hv hv1 hvrad hR hv_supp hav fc fu J hB3)
  exact ⟨Nmin,
    FRK.RowB_of_kin4_potG v h hv hv1 hvrad hR hv_supp hav fc fu J hB3 Nmin
      (FormRowKin4_holds_assembled v h hav fc fu R J Nmin) hpot⟩

/-- **The target of `Submission/Work/BoseBoxFock/box_to_model.lean`, assembled** — the
`∃ Nmin`-repair of the previous (false) instantiation at `Nmin ≡ 0`. -/
theorem box_to_model_assembled (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ)
    (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ HM : ∀ μ : ℝ, HonestModes v μ, (∀ μ, Nmin μ ≤ (HM μ).N) →
        ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
          J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
          ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
            (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
            0 < Work.BoseBoxFix.normB v μ n Φ →
            Work.BoseBoxFix.IsLowB v h J μ n Φ →
            Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
              (Φ : Submission.BoseGases.X n → ℝ) →
            ∃ Ψ : Work.BoseB4.RealFock (HM μ).m, Ψ ≠ 0 ∧
              ExcWindow (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
                (BoseGases.a v) μ) n Ψ ∧
              Work.BoseB4.bomb (HM μ).m Ψ (H2ndHon v h fc fu HM μ Ψ)
                ≤ (Work.BoseBoxFix.wordB v h μ n Φ / Work.BoseBoxFix.normB v μ n Φ
                    + Work.BoseFixR.errKafz v R μ C)
                    * Work.BoseB4.bomb (HM μ).m Ψ Ψ :=
  Work.BoseBoxFock.box_to_model_of_row v h hv hv1 hvrad hR hv_supp hav fc fu J hB3
    (RowB_exists v h hv hv1 hvrad hR hv_supp hav fc fu J hB3)

end Work.BoseBoxFock
