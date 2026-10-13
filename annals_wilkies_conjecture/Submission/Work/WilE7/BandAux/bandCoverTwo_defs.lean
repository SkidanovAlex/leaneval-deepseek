/-
  WilE7 (`Work.WilE7.BandAux.bandCoverTwo_defs`): the parametrisation of the two-strata band.

  This is the two-strata analogue of the parametrisation `bandPhi`/`bandH` of
  `Work.WilE7.BandAux.bandComponent`.  In the one-strata band `bandS3 Z S` the second and the
  fourth block of an ambient point both lie on sheets of the *same* stratum `S`; here they lie
  on sheets of two *different* strata `S₁`, `S₂`.  Consequently the parametrisation carries two
  independent sheet maps

    `g₁ : C → ℝ^{m+1}`  (for the lower level, i.e. the sheet of `S₁`)
    `g₂ : C → ℝ^{m+1}`  (for the upper level, i.e. the sheet of `S₂`)

  and the vertical band over the base component of `Z` is cut by the two levels `g₁` and `g₂`.

  The file only contains definitions (and their `rfl`-characterisations); the continuity of the
  parametrisation, the preconnectedness of the band and the coverage statement are separate.
-/
import Mathlib
import Submission.Work.WilE7.BandAux.BandDefsTwo
import Submission.Work.WilE7.BandAux.bandComponent

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.BandAux
open Work.WilE7 WilkiesDesign WilkiesDesign.E

/-- The parametrisation `Φ(q) = bandPt q.1 (g₁ (π q.1)) (g₂ (π q.1)) q.2` of an ambient point
of the band, for two arbitrary sheet maps `g₁ g₂ : ℝ^p → ℝ^{m+1}`. -/
noncomputable def bandPhiGen {p m : ℕ} (g₁ g₂ : (Fin p → ℝ) → (Fin (m + 1) → ℝ)) :
    ((Fin (p + (m + 1)) → ℝ) × ℝ) → Fin (bandDim p m) → ℝ :=
  fun q => bandPt q.1 (g₁ (projFirst p (m + 1) q.1)) (g₂ (projFirst p (m + 1) q.1)) q.2

theorem bandPhiGen_apply {p m : ℕ} (g₁ g₂ : (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (q : (Fin (p + (m + 1)) → ℝ) × ℝ) :
    bandPhiGen g₁ g₂ q = bandPt q.1 (g₁ (projFirst p (m + 1) q.1))
      (g₂ (projFirst p (m + 1) q.1)) q.2 := rfl

/-- The parametrisation of the two-strata band between the sheet `s₁ i` (lower level) and the
sheet `s₂ j` (upper level). -/
noncomputable def bandPhiTwo {p m k₁ k₂ : ℕ}
    (s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (i : Fin k₁) (j : Fin k₂) :
    ((Fin (p + (m + 1)) → ℝ) × ℝ) → Fin (bandDim p m) → ℝ :=
  bandPhiGen (s₁ i) (s₂ j)

theorem bandPhiTwo_apply {p m k₁ k₂ : ℕ}
    (s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (i : Fin k₁) (j : Fin k₂)
    (q : (Fin (p + (m + 1)) → ℝ) × ℝ) :
    bandPhiTwo s₁ s₂ i j q = bandPt q.1 (s₁ i (projFirst p (m + 1) q.1))
      (s₂ j (projFirst p (m + 1) q.1)) q.2 := rfl

/-- The vertical band over the base component `bandZc Z u₀`, between the level of the sheet
`s₁ i` and the level of the sheet `s₂ j`. -/
noncomputable def bandHtwo {p m k₁ k₂ : ℕ} (Z : SemiPf (p + (m + 1)))
    (s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (i : Fin k₁) (j : Fin k₂)
    (u₀ : Fin (p + (m + 1)) → ℝ) : Set ((Fin (p + (m + 1)) → ℝ) × ℝ) :=
  {q | q.1 ∈ bandZc Z u₀ ∧ bandLevel s₁ i q.1 < (q.2 : EReal) ∧
    (q.2 : EReal) < bandLevel s₂ j q.1}

theorem bandHtwo_mem_iff {p m k₁ k₂ : ℕ} {Z : SemiPf (p + (m + 1))}
    {s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    {s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} {i : Fin k₁} {j : Fin k₂}
    {u₀ : Fin (p + (m + 1)) → ℝ} {q : (Fin (p + (m + 1)) → ℝ) × ℝ} :
    q ∈ bandHtwo Z s₁ s₂ i j u₀ ↔
      (q.1 ∈ bandZc Z u₀ ∧ bandLevel s₁ i q.1 < (q.2 : EReal) ∧
        (q.2 : EReal) < bandLevel s₂ j q.1) := Iff.rfl

end Work.WilE7.BandAux
