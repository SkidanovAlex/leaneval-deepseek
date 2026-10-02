/-
# EL nest, part 1: the interface of the two nests

Area `Submission/Work/ELNest/` (EL part 3).  This file fixes the interface: the data and the
geometric facts about rays, pair sides and ray polygons that the nest arguments consume and that
are delivered by the neighbouring areas.

The vocabulary is that of the shared module `Work.EL` (`Submission/Work/ELTop/Defs.lean`).  The
coordinate system is: for a parameter `c`,

* `d : Work.EL.RootParabolic c` is the input bundle of the `F` side, containing the Böttcher
  coordinate `φ`, the Böttcher data `hN : DynB c φ`, the parabolic point `z₁`, its period and
  multiplier, the landing of the two root rays and the orbit portrait;
* `fl : FlowerData c d.z₁` is the Leau–Fatou flower at `z₁` (contract §4, FatouCoord);
* `P0` is the `α`-pair `(α₁, α₂) = (371, 404)/1023` landing at `z₁`, `Qp n` is the level-`n`
  pair `(βₙ', βₙ + 1)` of the nest at `z₁` (contract §5, certificate C5/C6);
* `Za n`, `Zb n`, `Zc n` are the level-`n` arm pairs of the nest at `b₂` (certificate C4/C7);
* `g` and `g6` are the inverse branches of `F c = f_c^{10}` and `f_c^6` used by the two nests.

Provenance of the fields (all are exports of ELTop / ELPull / FatouCoord, see `NOTES.md`):
`SP`, `Pa_far` (the local picture at the parabolic point, HS §2 and the L-wake portrait),
`side_disj`, `nest_side` (T6), `QmemK`, `DmemK` (T2' and the boundedness of `K`), `pbQ`, `pbD`,
`g_left`, `g_mem`, `g_diff` (ELPull's `polyPullback`), `pot_F`, `pot_f6` (the scaling of the
Böttcher potential).
-/
import Mathlib
import Submission.Work.ELNest.Defs
import Submission.Work.ELRig.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c : ℂ}

/-- **The two nests.**  All fields are statements about the concrete objects of `Defs.lean` and
of `Work.EL`; the geometric ones are the exports of the neighbouring EL areas listed in the
header of this file. -/
structure NestData (c : ℂ) where
  /-- the root-parabolic input bundle. -/
  d : RootParabolic c
  /-- the Leau--Fatou flower at `z₁`. -/
  fl : FlowerData c d.z₁
  /-- the reference level of the two nests. -/
  L : ℝ
  /-- the reference level is above `1`. -/
  hL : 1 < L
  /-- the `α`-pair. -/
  P0 : CoPair d.hN
  P0a : P0.a = alpha1
  P0b : P0.b = alpha2
  P0y : P0.y = d.z₁
  /-- the level-`n` pair of the nest at `z₁`. -/
  Qp : ℕ → CoPair d.hN
  Qpa : ∀ n, (Qp n).a = bAng' n
  Qpb : ∀ n, (Qp n).b = bAng n + 1
  /-- the level-`n` pair of the arm `A`. -/
  Za : ℕ → CoPair d.hN
  Zaa : ∀ n, (Za n).a = armA1 n
  Zab : ∀ n, (Za n).b = armA2 n
  /-- the level-`n` pair of the arm `B`. -/
  Zb : ℕ → CoPair d.hN
  Zba : ∀ n, (Zb n).a = armB1 n
  Zbb : ∀ n, (Zb n).b = armB2 n
  /-- the level-`n` pair of the arm `C`. -/
  Zc : ℕ → CoPair d.hN
  Zca : ∀ n, (Zc n).a = armC1 n
  Zcb : ∀ n, (Zc n).b = armC2 n + 1
  /-- the inverse branch of `F c = f_c^{10}` on `Q̂₀`. -/
  g : ℂ → ℂ
  /-- the inverse branch of `f_c^6` on `Δ̂₀`. -/
  g6 : ℂ → ℂ

  --the branch point `b₂` and its tripod
  /-- the branch point `b₂`. -/
  b2 : ℂ
  /-- the three tripod rays land at `b₂`. -/
  b2_lands : LandsN d.hN (22 / 63) b2 ∧ LandsN d.hN (25 / 63) b2 ∧ LandsN d.hN (37 / 63) b2
  /-- the ray of angle `22/63 + 1` (the same ray) lands at `b₂`. -/
  b2_lands' : LandsN d.hN (22 / 63 + 1) b2
  /-- `b₂` is fixed by `f_c²` (`Tsq c b₂ = b₂`). -/
  b2_fix : Work.Landing.Tsq c b2 = b2
  /-- `b₂` is not an interior point of the filled Julia set. -/
  b2_not_int : b2 ∉ interior (K c)
  /-- `b₂` lies in every level of the nest at `b₂`. -/
  b2_mem_D : ∀ n, b2 ∈ polyRegion [Za n, Zb n, Zc n] (Dlev L n)
  /-- the nest at `b₂` is decreasing (certificate C4: the level-`n+1` polygon lies inside the
  level-`n` region). -/
  Dnest_sub : ∀ n, polyRegion [Za (n + 1), Zb (n + 1), Zc (n + 1)] (Dlev L (n + 1))
    ⊆ polyRegion [Za n, Zb n, Zc n] (Dlev L n)
  /-- the first level of the nest at `b₂` is strictly inside the level-`0` region (certificate
  C4, the finite check at level `1`). -/
  Dnest_cl : closure (polyRegion [Za 1, Zb 1, Zc 1] (Dlev L 1))
    ⊆ polyRegion [Za 0, Zb 0, Zc 0] (Dlev L 0)
  /-- `f_c^6` is injective near `b₂` (its derivative at `b₂` does not vanish, since the critical
  orbit lies in the interior of `K c` while `b₂` does not). -/
  b2_locInj : ∃ ρ > 0, Set.InjOn (F6 c) (Metric.ball b2 ρ)
  /-- the landing point of the level-`n` arm-`A` pair (the cut point of the arm `A`) lies in `A`. -/
  cutA_mem : ∀ n, (Za n).y ∈ Work.EL.Tripod.armA
    { y := b2, lands₁ := b2_lands.1, lands₂ := b2_lands.2.1, lands₃ := b2_lands.2.2,
      lands₁' := b2_lands' }
  /-- the landing point of the level-`n` arm-`B` pair lies in the arm `B`. -/
  cutB_mem : ∀ n, (Zb n).y ∈ Work.EL.Tripod.armB
    { y := b2, lands₁ := b2_lands.1, lands₂ := b2_lands.2.1, lands₃ := b2_lands.2.2,
      lands₁' := b2_lands' }
  /-- the landing point of the level-`n` arm-`C` pair lies in the arm `C`. -/
  cutC_mem : ∀ n, (Zc n).y ∈ Work.EL.Tripod.armC
    { y := b2, lands₁ := b2_lands.1, lands₂ := b2_lands.2.1, lands₃ := b2_lands.2.2,
      lands₁' := b2_lands' }

  --### The local picture at `z₁` (HS §2, R-a1)

  /-- **Side preservation `SP`** (R-a1): in the far-left half-plane of the repelling coordinate,
  the side of the `α`-pair is preserved by the shift `w ↦ w + 1`, i.e. by `F c` on `Ψ`-images.
  This is the conclusion of `Work.ELRig.sidePreserve_core` (the crossing-parity core of
  `NOTES_LEAD_mandelbar_residuals.md` §3.2(d), live) and it *replaces* the earlier field
  `band : ∃ R, ∀ w, w.re < -R → fl.Ψ w ∈ pairSideNear P0`, which is **false**: by `Ψ_ends`
  (the far-left, large-`|Im|` region maps into the attracting petal `Pa`) together with
  `Pa_far` (`Pa ⊆ pairSide P0`) and `side_disj` it would put far-left points in both sides of the
  `α`-pair.  See `NOTES_LEAD_mandelbar_ledger.md` §6 and `NOTES_LEAD_mandelbar_residuals.md`
  §0.5/§3.3. -/
  SP : ∃ R : ℝ, ∀ u : ℂ, u.re < -R →
    (fl.Ψ u ∈ pairSide P0 ↔ fl.Ψ (u + 1) ∈ pairSide P0)
  /-- the two-sidedness of the `α`-pair (`Work.EL.PairSides`, supplied by
  `Work.ELTop.pairSides`): the complement of the pair curve is the disjoint union of the two
  sides.  It is what makes `z₁` a point of the closure of the near side (`frontier_near`) and what
  turns "not on the far side, not on the curve" into "on the near side" in the restated
  `g_eq_localInverse` and `tendsto_iterate_g`. -/
  sides_P0 : PairSides d.hN P0
  /-- the attracting petal lies on the wake side of the `α`-pair (the portrait `Pa_far`). -/
  Pa_far : fl.Pa ⊆ pairSide P0
  /-- the two sides of the `α`-pair are disjoint (T6). -/
  side_disj : Disjoint (pairSide P0) (pairSideNear P0)
  /-- the pair curve of the `α`-pair is invariant under `F c`. -/
  curveF : F c '' pairCurve P0 = pairCurve P0

  --### Sides, NEST and the regions (T2', T6)

  /-- **NEST** (T6), *orientation-complete* form: if the whole *near arc* of `P` is contained in
  the near arc of `Q` (as sets of angles, `{θ | InArc θ P.b (P.a + 1)} ⊆ {θ | InArc θ Q.b
  (Q.a + 1)}`), and the two pair curves are disjoint, then the near side of `P` is contained in
  the near side of `Q`.

  (The former form of this field asked only that the two *angles* of `P` lie in the near arc of
  `Q`; that does not determine the orientation of `(P.a, P.b)`, and the statement is in fact
  **false** at `c₀` — take `P` the `α`-pair and `Q = Qp n`.  See
  `Submission/Work/ELAssembly/NOTES_FALSE_nest_side.md`; the corrected statement is what
  `Work.ELAssembly.nest_side_of_nearArc` proves, and it is what the single consumer
  `Work.ELNest.NestData.Q_succ_subset` needs, via `InArc_bAng_nest`.) -/
  nest_side : ∀ (P Q : CoPair d.hN),
    (∀ θ : ℝ, InArc θ P.b (P.a + 1) → InArc θ Q.b (Q.a + 1)) →
    Disjoint (pairCurve P) (pairCurve Q) → pairSideNear P ⊆ pairSideNear Q
  /-- **T2'** for the nest at `z₁`: the region is the intersection of the near sides of its two
  boundary pairs with the sublevel set of the potential. -/
  Qmem : ∀ n, polyRegion [P0, Qp n] (Qlev L n)
    = pairSideNear P0 ∩ pairSideNear (Qp n) ∩ {z | pot d.hN z < Real.log (Qlev L n)}
  /-- **T2'** for the nest at `b₂`. -/
  Dmem : ∀ n, polyRegion [Za n, Zb n, Zc n] (Dlev L n)
    = pairSideNear (Za n) ∩ pairSideNear (Zb n) ∩ pairSideNear (Zc n)
        ∩ {z | pot d.hN z < Real.log (Dlev L n)}
  /-- the list `[P0, Qp n]` is an admissible ray polygon (its angles are strictly cyclically
  ordered and the two landing points are distinct). -/
  Q_adm : ∀ n, PolyAdmissible [P0, Qp n]
  /-- the list `[Za n, Zb n, Zc n]` is an admissible ray polygon. -/
  D_adm : ∀ n, PolyAdmissible [Za n, Zb n, Zc n]
  /-- the pair curves of the nest at `z₁` are pairwise disjoint. -/
  Qp_disj : ∀ m n, m ≠ n → Disjoint (pairCurve (Qp m)) (pairCurve (Qp n))
  /-- `z₁` lies on the near side of every level-`n` pair. -/
  z1_near_Q : ∀ n, d.z₁ ∈ pairSideNear (Qp n)
  /-- the level-`0` pair of the nest is a pull-back of the pair landing at `f^4 z₁`
  (certificate C5 with the portrait). -/
  base_shift : F c ((Qp 0).y) = (LeanEval.ComplexAnalysis.Tantibar c)^[4] d.z₁
  -- NOTE (2026-09-28, area ELAssembly): the field
  -- `Qnear0 : Metric.ball d.z₁ (‖(Qp 0).y - d.z₁‖ / 2) ⊆ pairSideNear (Qp 0)` has been
  -- **deleted**: it had no consumer anywhere in the workspace and is not needed by the
  -- assembly (`Submission/Work/ELAssembly/NOTES.md` §0.5).
  /-- no level-`n` pair of the `z₁`-nest lands at `z₁`. -/
  Qne : ∀ n, (Qp n).y ≠ d.z₁

  --### The pull-back (ELPull, `polyPullback`)

  /-- **`polyPullback`** for the nest at `z₁`. -/
  pbQ : ∀ n, Set.BijOn (F c) (polyRegion [P0, Qp (n + 1)] (Qlev L (n + 1)))
    (polyRegion [P0, Qp n] (Qlev L n))
  /-- **`polyPullback`** for the nest at `b₂`. -/
  pbD : ∀ n, Set.BijOn (F6 c) (polyRegion [Za (n + 1), Zb (n + 1), Zc (n + 1)] (Dlev L (n + 1)))
    (polyRegion [Za n, Zb n, Zc n] (Dlev L n))
  /-- `g` is a right inverse of `F c` on `Q̂₀`. -/
  g_left : ∀ z ∈ polyRegion [P0, Qp 0] (Qlev L 0), F c (g z) = z
  /-- `g` maps `Q̂₀` into `Q̂₁`. -/
  g_mem : ∀ z ∈ polyRegion [P0, Qp 0] (Qlev L 0), g z ∈ polyRegion [P0, Qp 1] (Qlev L 1)
  /-- `g` is holomorphic. -/
  g_diff : DifferentiableOn ℂ g (polyRegion [P0, Qp 0] (Qlev L 0))
  /-- `g6` is a right inverse of `f_c^6` on `Δ̂₀`. -/
  g6_left : ∀ z ∈ polyRegion [Za 0, Zb 0, Zc 0] (Dlev L 0), F6 c (g6 z) = z
  /-- `g6` maps `Δ̂₀` into `Δ̂₁`. -/
  g6_mem : ∀ z ∈ polyRegion [Za 0, Zb 0, Zc 0] (Dlev L 0),
    g6 z ∈ polyRegion [Za 1, Zb 1, Zc 1] (Dlev L 1)
  /-- `g6` is holomorphic. -/
  g6_diff : DifferentiableOn ℂ g6 (polyRegion [Za 0, Zb 0, Zc 0] (Dlev L 0))
  /-- the potential is multiplied by the degree `1024` under `F c`. -/
  pot_F : ∀ z, pot d.hN (F c z) = 1024 * pot d.hN z
  /-- the potential is multiplied by the degree `64` under `f_c^6`. -/
  pot_f6 : ∀ z, pot d.hN (F6 c z) = 64 * pot d.hN z

namespace NestData

variable (S : NestData c)

/-- The tripod at `b₂`, assembled from the fields of `NestData`. -/
def tripod : Work.EL.Tripod S.d.hN where
  y := S.b2
  lands₁ := S.b2_lands.1
  lands₂ := S.b2_lands.2.1
  lands₃ := S.b2_lands.2.2
  lands₁' := S.b2_lands'

/-- The arm `A` of the tripod at `b₂`. -/
def armA : Set ℂ := Work.EL.Tripod.armA S.tripod

/-- The arm `B` of the tripod at `b₂`. -/
def armB : Set ℂ := Work.EL.Tripod.armB S.tripod

/-- The arm `C` of the tripod at `b₂`. -/
def armC : Set ℂ := Work.EL.Tripod.armC S.tripod

/-- The cut point of the arm `A` at level `n`: the landing point of the level-`n` arm pair. -/
def cutA (n : ℕ) : ℂ := (S.Za n).y

/-- The cut point of the arm `B` at level `n`. -/
def cutB (n : ℕ) : ℂ := (S.Zb n).y

/-- The cut point of the arm `C` at level `n`. -/
def cutC (n : ℕ) : ℂ := (S.Zc n).y

/-- `Q̂ₙ`: the level-`n` region of the nest at `z₁`. -/
def Q (n : ℕ) : Set ℂ := polyRegion [S.P0, S.Qp n] (Qlev S.L n)

/-- `Δ̂ₙ`: the level-`n` region of the nest at `b₂`. -/
def D (n : ℕ) : Set ℂ := polyRegion [S.Za n, S.Zb n, S.Zc n] (Dlev S.L n)

theorem Q_zero : S.Q 0 = polyRegion [S.P0, S.Qp 0] (Qlev S.L 0) := rfl

theorem mem_Q_iff {n : ℕ} {z : ℂ} : z ∈ S.Q n ↔ z ∈ polyRegion [S.P0, S.Qp n] (Qlev S.L n) :=
  Iff.rfl

theorem mem_D_iff {n : ℕ} {z : ℂ} :
    z ∈ S.D n ↔ z ∈ polyRegion [S.Za n, S.Zb n, S.Zc n] (Dlev S.L n) := Iff.rfl

end NestData

end Work.ELNest
