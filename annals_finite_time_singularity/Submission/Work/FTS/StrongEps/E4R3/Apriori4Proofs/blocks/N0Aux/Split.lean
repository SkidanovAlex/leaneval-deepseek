/-
# `N0Aux.Split` — the `N₀`-split, its `ℋ⁶`-honesty, and the sub-additivity of `HkSq`

The block `blkN0 α w = N0 α (F_* + w) w` of the semi-tame estimate is the sum of the seven
pieces of `H6Pair6Aux.H6N0Aux/N0row_defs`:

  `N0 α (F_*+w) w = NA1 α + NP3 α w + NP4a α w + NP4b α w + NP5a α w + NP5b α w + NP6 α w`

on the open quadrant (this is `N0_eq_sum` of `Construction.Terms` together with the halves
identities `N04_eq_halves`/`N05_eq_halves` of the transported factor `F = F_* + w`, which hold
pointwise on the open quadrant because `F_*` and `w` are `C^∞` there).

This module records

* the pointwise additivity of `∂_θ` and `D_z` along `F_* + w` on the open quadrant;
* the split identity `N0_split_open`;
* `SmoothOpen` and `HkMem α 6` of `N0 α (F_* + w) w` for `ClassC α w` (using the pieces'
  memberships `hkmem_N0pieces_own` and `FstarI12H6` and the `Q0`-congruence of `HkMem`);
* the `HkSq`-sub-additivity helper `hkSq_sum7_le` for the nested seven-fold sum.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.hkmem_pieces_own
import Submission.Work.FTS.StrongPersist.H6Rows.FstarI12H6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0PieceHelpers
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Construction.Terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The full profile `F = F_* + w`. -/
abbrev Ft (α : ℝ) (w : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Construction.Ftot α w

/-- The nested seven-fold sum of the pieces of `N₀`. -/
def sum7 (a b c d e f g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => a z θ + (b z θ + (c z θ + (d z θ + (e z θ + (f z θ + g z θ)))))

/-- **`∂_θ(F_* + w) = ∂_θF_* + ∂_θw` on the open quadrant.** -/
theorem pth_Ftot (α : ℝ) {w : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α))
    (hw : Work.FTS.EllipticEst.SmoothOpen w) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (Ft α w) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth w z θ := by
  intro z θ hQ
  have hz : 0 < z := hQ.1
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := hQ.2
  have h1 : DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ :=
    ((hF.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have h2 : DifferentiableAt ℝ (fun θ' => w z θ') θ :=
    ((hw.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  simp only [Ft, Work.Spaces.pth, Work.Construction.Ftot]
  rw [show (fun θ' => Work.Construction.Fstar α z θ' + w z θ')
      = (fun θ' => Work.Construction.Fstar α z θ') + (fun θ' => w z θ') from rfl]
  exact deriv_add h1 h2

/-- **`D_z(F_* + w) = D_zF_* + D_zw` on the open quadrant.** -/
theorem Dz_Ftot (α : ℝ) {w : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α))
    (hw : Work.FTS.EllipticEst.SmoothOpen w) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (Ft α w) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz w z θ := by
  intro z θ hQ
  have hz : 0 < z := hQ.1
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := hQ.2
  have h1 : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar α z' θ) z :=
    ((hF.curry_z hθ).differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have h2 : DifferentiableAt ℝ (fun z' => w z' θ) z :=
    ((hw.curry_z hθ).differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  simp only [Ft, Work.Spaces.Dz, Work.Spaces.pz, Work.Construction.Ftot]
  rw [show (fun z' => Work.Construction.Fstar α z' θ + w z' θ)
      = (fun z' => Work.Construction.Fstar α z' θ) + (fun z' => w z' θ) from rfl]
  rw [deriv_add h1 h2]
  ring

/-- **The split of `N₀` into its seven pieces, on the open quadrant.** -/
theorem N0_split_open (α : ℝ) {w : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α))
    (hw : Work.FTS.EllipticEst.SmoothOpen w) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Ft α w) w z θ
        = NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ + (NP4b α w z θ
            + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))))) := by
  intro z θ hQ
  have hpth := pth_Ftot α hF hw z θ hQ
  have hDz := Dz_Ftot α hF hw z θ hQ
  simp only [Work.Construction.N0, Work.Construction.N01, Work.Construction.N02,
    Work.Construction.N03, Work.Construction.N04a, Work.Construction.N04b,
    Work.Construction.N05a, Work.Construction.N05b, Work.Construction.N06,
    Work.FTS.StrongPersist.H6Pair6Aux.NA1, Work.FTS.StrongPersist.H6Pair6Aux.NA4,
    Work.FTS.StrongPersist.H6Pair6Aux.NA5, Work.FTS.StrongPersist.H6Pair6Aux.NA6,
    Work.FTS.StrongPersist.H6Pair6Aux.NP3, Work.FTS.StrongPersist.H6Pair6Aux.NP4a,
    Work.FTS.StrongPersist.H6Pair6Aux.NP4b, Work.FTS.StrongPersist.H6Pair6Aux.NP5a,
    Work.FTS.StrongPersist.H6Pair6Aux.NP5b, Work.FTS.StrongPersist.H6Pair6Aux.NP6,
    Work.Spaces.Dth, Work.Construction.Ftot]
  rw [hpth, hDz]
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Construction.s2]
  ring

/-! ## The `HkSq`-sub-additivity of the nested seven-fold sum -/

/-- **`HkSq` of the nested seven-fold sum**: six applications of `HkSq_add_le_open`, hence a
factor `2^6 = 64`. -/
theorem hkSq_sum7_le {α : ℝ} {k : ℕ} (hα : 0 < α)
    {f₁ f₂ f₃ f₄ f₅ f₆ f₇ : ℝ → ℝ → ℝ}
    (hs₁ : Work.FTS.EllipticEst.SmoothOpen f₁) (hs₂ : Work.FTS.EllipticEst.SmoothOpen f₂)
    (hs₃ : Work.FTS.EllipticEst.SmoothOpen f₃) (hs₄ : Work.FTS.EllipticEst.SmoothOpen f₄)
    (hs₅ : Work.FTS.EllipticEst.SmoothOpen f₅) (hs₆ : Work.FTS.EllipticEst.SmoothOpen f₆)
    (hs₇ : Work.FTS.EllipticEst.SmoothOpen f₇)
    (hm₁ : Work.Spaces.HkMem α k f₁) (hm₂ : Work.Spaces.HkMem α k f₂)
    (hm₃ : Work.Spaces.HkMem α k f₃) (hm₄ : Work.Spaces.HkMem α k f₄)
    (hm₅ : Work.Spaces.HkMem α k f₅) (hm₆ : Work.Spaces.HkMem α k f₆)
    (hm₇ : Work.Spaces.HkMem α k f₇) :
    Work.Spaces.HkSq α k (fun z θ => f₁ z θ + (f₂ z θ + (f₃ z θ + (f₄ z θ
        + (f₅ z θ + (f₆ z θ + f₇ z θ))))))
      ≤ 64 * (Work.Spaces.HkSq α k f₁ + Work.Spaces.HkSq α k f₂ + Work.Spaces.HkSq α k f₃
          + Work.Spaces.HkSq α k f₄ + Work.Spaces.HkSq α k f₅ + Work.Spaces.HkSq α k f₆
          + Work.Spaces.HkSq α k f₇) := by
  have hs67 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f₆ z θ + f₇ z θ) := hs₆.add hs₇
  have hm67 : Work.Spaces.HkMem α k (fun z θ => f₆ z θ + f₇ z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α k hs₆ hs₇ hm₆ hm₇
  have hs567 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => f₅ z θ + (f₆ z θ + f₇ z θ)) := hs₅.add hs67
  have hm567 : Work.Spaces.HkMem α k (fun z θ => f₅ z θ + (f₆ z θ + f₇ z θ)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α k hs₅ hs67 hm₅ hm67
  have hs4567 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ))) := hs₄.add hs567
  have hm4567 : Work.Spaces.HkMem α k (fun z θ => f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α k hs₄ hs567 hm₄ hm567
  have hs34567 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => f₃ z θ + (f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ)))) := hs₃.add hs4567
  have hm34567 : Work.Spaces.HkMem α k
      (fun z θ => f₃ z θ + (f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ)))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α k hs₃ hs4567 hm₃ hm4567
  have hs234567 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => f₂ z θ + (f₃ z θ + (f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ))))) := hs₂.add hs34567
  have hm234567 : Work.Spaces.HkMem α k
      (fun z θ => f₂ z θ + (f₃ z θ + (f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ))))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α k hs₂ hs34567 hm₂ hm34567
  have h1 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hs₆ hs₇ hm₆ hm₇
  have h2 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hs₅ hs67 hm₅ hm67
  have h3 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hs₄ hs567 hm₄ hm567
  have h4 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hs₃ hs4567 hm₃ hm4567
  have h5 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hs₂ hs34567 hm₂ hm34567
  have h6 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hs₁ hs234567 hm₁ hm234567
  have nn : ∀ g : ℝ → ℝ → ℝ, 0 ≤ Work.Spaces.HkSq α k g := fun g =>
    Work.Spaces.HkSq_nonneg α k g
  have hchain : Work.Spaces.HkSq α k
      (fun z θ => f₁ z θ + (f₂ z θ + (f₃ z θ + (f₄ z θ
        + (f₅ z θ + (f₆ z θ + f₇ z θ))))))
      ≤ 2 * (Work.Spaces.HkSq α k f₁
          + 2 * (Work.Spaces.HkSq α k f₂
            + 2 * (Work.Spaces.HkSq α k f₃
              + 2 * (Work.Spaces.HkSq α k f₄
                + 2 * (Work.Spaces.HkSq α k f₅
                  + 2 * (Work.Spaces.HkSq α k f₆ + Work.Spaces.HkSq α k f₇)))))) := by
    refine le_trans h6 ?_
    have a2 : Work.Spaces.HkSq α k
        (fun z θ => f₃ z θ + (f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ))))
        ≤ 2 * (Work.Spaces.HkSq α k f₃
            + 2 * (Work.Spaces.HkSq α k f₄
              + 2 * (Work.Spaces.HkSq α k f₅
                + 2 * (Work.Spaces.HkSq α k f₆ + Work.Spaces.HkSq α k f₇)))) := by
      refine le_trans h4 ?_
      linarith [h1, h2, h3, nn f₄, nn f₅, nn f₆, nn f₇]
    have a1 : Work.Spaces.HkSq α k
        (fun z θ => f₂ z θ + (f₃ z θ + (f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ)))))
        ≤ 2 * (Work.Spaces.HkSq α k f₂
            + 2 * (Work.Spaces.HkSq α k f₃
              + 2 * (Work.Spaces.HkSq α k f₄
                + 2 * (Work.Spaces.HkSq α k f₅
                  + 2 * (Work.Spaces.HkSq α k f₆ + Work.Spaces.HkSq α k f₇))))) := by
      refine le_trans h5 ?_
      linarith [a2, nn f₂, nn f₃]
    linarith [a1, nn f₁, nn f₂, nn f₃, nn f₄, nn f₅, nn f₆, nn f₇]
  refine le_trans hchain ?_
  linarith [nn f₁, nn f₂, nn f₃, nn f₄, nn f₅, nn f₆, nn f₇]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
