import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.isCompact_rayAccum
import Submission.Work.Bottcher.ContractionAux.isPreconnected_iInter_of_antitone_isCompact
import Submission.Work.SeedDyn.Main
import Submission.Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher
import Submission.Work.ELTop.landsN_iff_landsAt
import Submission.Work.Top.continuousOn_rayPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The accumulation set of a dynamic ray is preconnected

For a parameter `c` with a Böttcher coordinate `φ` of the antiholomorphic quadratic family
`T_c(z) = z̄² + c`, the accumulation set `rayAccum c φ θ` of the dynamic ray at angle `θ` is a
continuum.  The statement is the "first half" of the direct (Milnor 18.10) route to the landing
theorem: together with `rayAccum_nonempty` it says that the accumulation set of every ray is a
nonempty compact connected set, so that a two-point accumulation set is the only obstruction to
landing.

The proof is the classical one, split into the two standard ingredients.

* **The truncated rays have connected closure.**  Via the dynamical Böttcher *homeomorphism*
  `Work.Top.NakaneData (filledJulia c) (dynPhi c)` (`Work.SeedDyn.dynB`), the truncation of the
  ray `R_c(θ)` at level `ρ` is the image of the level interval `(1, ρ]` under the continuous
  parametrisation `t ↦ rayPt hN θ t` (`Work.ELTop.rayPiece_eq_image`), hence preconnected; the
  closure of a preconnected set is preconnected.
* **A nested intersection of continua is a continuum.**  Writing `ρ_n = 1 + 1/(n+1) ↓ 1`,
  `rayAccum c φ θ = ⋂_n closure (rayPiece hN θ 0 (ρ_n))`
  (`Work.ELTop.rayAccum_eq_closure`), each term is compact (it lies in the compact sublevel set
  `{pot ≤ log ρ_n}`, `Work.Top.NakaneData.isCompact_le_potential`) and preconnected, and the
  family is antitone.  The conclusion is the standard theorem
  `Work.Bottcher.ContractionAux.isPreconnected_iInter_of_antitone_isCompact`.

Finally, the result is transferred from the canonical coordinate `dynPhiOf c` to an arbitrary
Böttcher coordinate `φ` by uniqueness (`Work.ParamRays.isDynBottcher_unique`) together with
`Work.Landing.rayAccum_congr`; the hypothesis `IsDynBottcher c φ` itself forces `c` to lie in the
mandelbar (`Work.LandLeaves.dynBottcherOnlyOnMandelbar`), which is where the homeomorphism is
available.
-/

noncomputable section

open Classical Set
open scoped Topology

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Mandelbar)

/-! ## The level sequence `ρ_n = 1 + 1/(n+1)` -/

/-- The decreasing level sequence `ρ_n = 1 + 1/(n+1) ↓ 1` used to write the accumulation set of a
ray as a countable nested intersection. -/
def levelSeq (n : ℕ) : ℝ := 1 + 1 / ((n : ℝ) + 1)

theorem one_lt_levelSeq (n : ℕ) : 1 < levelSeq n := by
  have h : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  simp only [levelSeq]
  linarith

theorem levelSeq_succ_le (n : ℕ) : levelSeq (n + 1) ≤ levelSeq n := by
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
  have h3 := one_div_le_one_div_of_le h1 h2
  simp only [levelSeq]
  linarith

theorem levelSeq_le_of_one_div_lt {ρ : ℝ} {n : ℕ} (h : 1 / ((n : ℝ) + 1) ≤ ρ - 1) :
    levelSeq n ≤ ρ := by
  simp only [levelSeq]
  linarith

/-! ## Monotonicity of the ray pieces -/

/-- The ray piece between levels `0` and `R` grows with `R`. -/
theorem rayPiece_mono {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (β : ℝ) {R R' : ℝ}
    (hR : 1 < R) (hRR' : R ≤ R') :
    Work.EL.rayPiece hN β 0 R ⊆ Work.EL.rayPiece hN β 0 R' := by
  rw [Work.ELTop.rayPiece_eq_image hN hR,
    Work.ELTop.rayPiece_eq_image hN (lt_of_lt_of_le hR hRR')]
  exact Set.image_mono (fun t ht => ⟨ht.1, le_trans ht.2 hRR'⟩)

/-! ## The truncated rays have preconnected closure -/

/-- The closure of the ray piece between levels `0` and `R` (`1 < R`) is preconnected: the piece
is the image of the interval `(1,R]` under the continuous level parametrisation of the ray. -/
theorem isPreconnected_closure_rayPiece {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (β : ℝ) {R : ℝ} (hR : 1 < R) :
    IsPreconnected (closure (Work.EL.rayPiece hN β 0 R)) := by
  rw [Work.ELTop.rayPiece_eq_image hN hR]
  exact (IsPreconnected.image isPreconnected_Ioc (fun t : ℝ => Work.EL.rayPt hN β t)
    ((Work.Top.continuousOn_rayPt hN β).mono (fun t ht => ht.1))).closure

/-! ## The accumulation set as a countable nested intersection -/

/-- The accumulation set of the ray at angle `θ` is the nested intersection of the closures of the
ray pieces at the levels `1 + 1/(n+1) ↓ 1`. -/
theorem rayAccum_eq_iInter_closure_rayPiece {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) :
    Work.Landing.rayAccum c φ θ
      = ⋂ n : ℕ, closure (Work.EL.rayPiece hN θ 0 (levelSeq n)) := by
  rw [Work.ELTop.rayAccum_eq_closure hN θ]
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · intro h n
    exact h _ (one_lt_levelSeq n)
  · intro h ρ hρ
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ρ - 1 by linarith)
    exact closure_mono
      (rayPiece_mono hN θ (one_lt_levelSeq n) (levelSeq_le_of_one_div_lt hn.le)) (h n)

/-! ## Preconnectedness -/

/-- **The accumulation set of a dynamic ray is preconnected**, for the dynamical Nakane datum
`hN : Work.EL.DynB c φ`. -/
theorem isPreconnected_rayAccum_of_dynB {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) :
    IsPreconnected (Work.Landing.rayAccum c φ θ) := by
  rw [rayAccum_eq_iInter_closure_rayPiece hN θ]
  refine Work.Bottcher.ContractionAux.isPreconnected_iInter_of_antitone_isCompact
    (A := fun n => closure (Work.EL.rayPiece hN θ 0 (levelSeq n))) ?_ ?_ ?_
  · intro n
    refine (Work.EL.isCompact_le_pot hN (Real.log (levelSeq n))).of_isClosed_subset
      isClosed_closure ?_
    refine closure_minimal (fun z hz => ?_)
      (Work.EL.isCompact_le_pot hN (Real.log (levelSeq n))).isClosed
    exact ((Work.ELTop.mem_rayPiece_iff hN θ 0 (levelSeq n) z).mp hz).2.2
  · intro n
    exact isPreconnected_closure_rayPiece hN θ (one_lt_levelSeq n)
  · intro n
    exact closure_mono (rayPiece_mono hN θ (one_lt_levelSeq (n + 1)) (levelSeq_succ_le n))

/-! ## The statement -/

/-- **The accumulation set of a dynamic ray is preconnected.**  For every parameter `c` carrying a
Böttcher coordinate `φ` and every angle `θ`, the accumulation set `rayAccum c φ θ` of the dynamic
ray `R_c(θ)` is preconnected — the first half of the fact that it is a continuum. -/
theorem isPreconnected_rayAccum {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) (θ : ℝ) :
    IsPreconnected (Work.Landing.rayAccum c φ θ) := by
  have hc : c ∈ Mandelbar := Work.LandLeaves.dynBottcherOnlyOnMandelbar c ⟨φ, hφ⟩
  have hN : Work.ELPull.DynB c := Work.SeedDyn.dynB hc
  have hψ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    Work.ParamRays.isDynBottcher_dynPhiOf ⟨φ, hφ⟩
  rw [Work.Landing.rayAccum_congr
    (fun w hw => Work.ParamRays.isDynBottcher_unique hφ hψ hw) θ]
  exact isPreconnected_rayAccum_of_dynB hN θ

end Work.LandLeaves
