/-
  Area E7 / E2B, node `gcaseRefineP2`: **the sheet data of the `G`-branch**.

  In the `G`-branch of the per-base-cell refinement the base cell `b` avoids the `π_n`-images of the
  whole `Σ`-family (`GHyp`), so the cells over `b` have to be cut by the level functions of the
  *active* candidates (those members of `P.Cand` whose `π_n`-image captures `b`).

  `GSheets` bundles the active subfamily of `P.Cand` together with the sheet provision
  `E2Pkg.hSheet` for it (the `kk`/`s` data of the covering of `αSet S` over `b`), the candidate
  facts (`CandSpec`), and the completeness of the subfamily (`E2_activeFamily`).  It is the common
  input of the four pieces of the `G`-branch:

  * `E2B.gcaseSheetsData`     — produces the structure from `E2Pkg.hSheet`/`E2_activeFamily`;
  * `E2B.gcaseTrichotomyData` — the trichotomy and the level dichotomy of the sheets
    (`CoreStep.gcase_sheets`);
  * `E2B.gcaseProducer`       — the level family `TT` and the cells `cfs b TT` (`E2Pkg.hGcell`);
  * `E2B.gcaseVertCompat`     — the vertical row over a piece of dimension `K+1`
    (`Endgame.gcase_vertical_cell`).
-/
import Mathlib
import Submission.Work.WilE7.Endgame.E2B.Pkg

namespace Work.WilE7.Endgame.E2B

set_option autoImplicit false
noncomputable section
open Classical

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair)

/-- The active candidates of the `G`-branch and the sheets covering them over `b`. -/
structure GSheets {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ}
    {X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)}
    {Y : Fin l → WilkiesDesign.E.SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    (b : Set (Fin n → ℝ)) where
  /-- the number of active candidates -/
  r : ℕ
  /-- the active candidates -/
  S : Fin r → WilkiesDesign.E.Stratum 0 (n + (m + 1))
  hScand : ∀ t, S t ∈ P.Cand
  hSact : ∀ t, b ⊆ WilkiesDesign.E.projFirst n (m + 1) '' absSet (S t)
  hSgood : ∀ t, (S t).Good
  hSfmt : ∀ t, (S t).X.fmt ≤ c.Ac
  hSdeg : ∀ t, (S t).deg ≤ c.Dq.eval D
  hSrank : ∀ t z, z ∈ (S t).X.set → projRank (S t) z = n + (m + 1) - (S t).j
  /-- the sheets -/
  kc : Fin r → ℕ
  hkpos : ∀ t, 0 < kc t
  sc : (t : Fin r) → Fin (kc t) → (Fin n → ℝ) → (Fin (m + 1) → ℝ)
  hcont : ∀ t j, ContinuousOn (sc t j) b
  hinj : ∀ t x, x ∈ b → Function.Injective fun j => sc t j x
  hsub : ∀ t j x, x ∈ b → Fin.append x (sc t j x) ∈ absSet (S t)
  hcov : ∀ t z, z ∈ absSet (S t) → WilkiesDesign.E.projFirst n (m + 1) z ∈ b →
    ∃ j, sc t j (WilkiesDesign.E.projFirst n (m + 1) z) = WilkiesDesign.E.projSnd n (m + 1) z
  hcard : ∀ t x, x ∈ b →
    (WilkiesDesign.E.fiber (absSet (S t)) x).ncard = kc t
  hcle : ∀ t, kc t ≤ c.Ps.eval (c.Dq.eval D)
  /-- every active member of `P.Cand` occurs in the family -/
  hcomplete : ∀ T ∈ P.Cand, b ⊆ WilkiesDesign.E.projFirst n (m + 1) '' absSet T →
    ∃ t, S t = T
  /-- the family is a subfamily of `P.Cand`, hence no longer -/
  hlenc : r ≤ P.Cand.length

end
end Work.WilE7.Endgame.E2B
