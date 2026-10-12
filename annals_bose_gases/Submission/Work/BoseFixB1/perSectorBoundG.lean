import ChallengeDeps
import Submission.Work.BoseFixB1.PerBoxResidualG
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.perSectorBoundG` — the **termwise** refinement of
# `PerBoxSectorBoundG`, and the assembly back to it

Holder of `Work.BoseFixB1.perBoxFWeight_holds` (FS `thm:smallbox` at the sliding box).  The
target file's proof rests on the single upstream residual `Work.BoseFixB1B.PerBoxSectorBoundG`
(`Submission/Work/BoseFixB1/perBoxSectorBoundG.lean`), which is the *mixture* form

    Σ_k m_k·T(k) ≤ sbWord ,      m_k = sectorMass (PBℓ v μ) (PBB v μ u) Φ k ,

with `T(k) = (c·psiWeight 1 μ (k/PBV) − (½−c)μ²)·PBW − C(μ²(a v)·PBΓ·PBW + μ(a v))` and
`sbWord = sbKin + qLHSwordB` the frozen localised word.

This module performs the **standard FS decomposition of that residual**: it replaces the mixture
by its *termwise* (per occupancy sector) form `PerSectorBoundG`, which is the shape in which the
upstream sector/fibre chapter states its residual (`Work.FockBridge.PerSectorBound`, whose
sector-additivity half is *proved*: `qLHSword_eq_sum_sectorPiece`,
`cnPlusBoxInd_eq_sum_sectorPiece`, `tBwordInd_eq_sum_sectorPiece`).

`perBoxSectorBoundG_of_pieces` below is the (short) assembly: termwise bound + sector additivity
⟹ the mixture residual.  It is a complete, `sorry`-free proof.

## The two pieces, and *why* the additivity is `Adm`-restricted

* **`PerSectorBoundG`** — the analytic residual, *termwise in the sector index* `k`.  **This is
  the piece to delegate.**
* **`SbWordSectorAdditive v h ε₀`** — the *bookkeeping*: under `Adm v ε₀ μ`, the frozen word is the
  sum of the words of its sector pieces.  **Also delegatable, and purely mechanical.**

⚠️ The `Adm`-restriction on `SbWordSectorAdditive` is **not** cosmetic: the potential half
`qLHSwordB h M ℓ d μ u Φ = ∫ qLHSden·Φ²` is a *signed* Bochner integral, so splitting it over the
finitely many occupancy sectors is legitimate only under the integrability of every summand; a
previous run proved (and documented in
`Submission/Work/BoseFixB1/FINDING_sbWordSectorAdditive_needs_integrable.md`) that this
integrability is **not** derivable from the six standing hypotheses of Theorem 1.2 alone: for
`μ → 0` the cutoff `ℓd = (a v)(μ(a v)³)^{−157/323}` blows up and the localised kernels become
unbounded on the faces of their supports.  The diluteness regime `Adm v ε₀ μ` is exactly what
supplies it (the same restriction the sibling `Work.BoseFixB1S.wordB1_eq_sum_sectorPiece` carries,
and the same trap recorded in `BoseFixB1B/FINDING_potGapAdditivityStratum.md`).
The consumer below applies the identity only under `Adm`, so the restriction costs nothing.

## Why this is the right split

The mixture form `PerBoxSectorBoundG` conjoins the analytic content with the sector bookkeeping,
which makes it impossible to attack (or even to state to a prover) the analytic half alone.  The
two pieces above are independent: `SbWordSectorAdditive` needs no analysis at all, and
`PerSectorBoundG` is exactly the termwise statement that `Work.FockBridge.PerSectorBound` and the
`Work.SlotWord`/`Work.FibreWord` chapters are organised around.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge
open Work.BoseFixB1B

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The two pieces -/

/-- **The termwise (per occupancy sector) refinement of `PerBoxSectorBoundG`** — FS
`thm:smallbox` read at the *count* of each `B(u)`-occupancy sector, on the good set `G`.

There are `ε₀ > 0`, `0 < c ≤ 1/4` and `C ≥ 0` such that for every admissible `μ`, every `n`,
every smooth symmetric box state `Φ` and every `u ∈ G`, and every sector index `k ≤ n`,

    m_k·T(k)  ≤  tBwordBInd n ℓ d ε_T (dsℓ)⁻¹ u Φ_k  +  qLHSwordB h M ℓ d μ u Φ_k ,

where `Φ_k = 1_{n_{B(u)} = k}·Φ` is the `k`-th occupancy sector piece of `Φ`,
`m_k = ∫ Φ_k²` its mass, and

    T(k) = (c·F(k/|B(u)|) − (½−c)μ²)·∬w_{1,B(u)} − C·(μ²(a v)Γ|B(u)| + μ(a v)) ,

`F = psiWeight 1 μ`, `|B(u)| = chiMass M ℓ d u` (`= PBV`), `∬w_{1,B(u)} = PBW`,
`Γ = PBΓ v μ = K_B³(μ(a v)³)^{1/2}`.

This is the *sharpest* form of the residual (`Work.FockBridge.PerSectorBound` is the same
inequality with the state's density `dens N L` in place of the chemical potential `μ`, and with
the background `½μ²` in place of `(½−c)μ²` — see
`FINDING_perSectorBoundG_split.md` §2 for why the latter difference is *not* cosmetic): the
right-hand side is a *single* per-box word of the sector piece, hence directly comparable with the
delivered count-indexed bound `Work.BlockBound4.diagWeBAt k`. -/
def PerSectorBoundG (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
        ∀ k ∈ Finset.range (n + 1),
          sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k *
              ((c * psiWeight 1 μ ((k : ℝ) / PBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
                - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                    + μ * (_root_.BoseGases.a v)))
            ≤ Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
                  (sbCut μ (_root_.BoseGases.a v)) u
                  (sectorPiece (PBB v μ u) k (Φ : X n → ℝ))
              + qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
                  (sectorPiece (PBB v μ u) k (Φ : X n → ℝ))

/-- **Sector additivity of the frozen localised word, under the diluteness regime.**  For every
admissible `μ`, the word `sbWord = sbKin + sbPot` is exactly the sum, over the
`B(u)`-occupancy sectors, of the words of the sector pieces:

    sbWord h μ u Φ = Σ_{k ≤ n} [ tBwordBInd n ℓ d ε_T (dsℓ)⁻¹ u Φ_k + qLHSwordB h M ℓ d μ u Φ_k ] .

*The `Adm v ε₀ μ` binder is load-bearing* (see the module docstring): the potential half is a
signed Bochner integral and needs the integrability of each summand, which the regime supplies.
Beyond that the statement is *locality*: the box projections `Q_{B,i}` and the two-factor window
`χ_{B(u)}` only see the occupancy sectors.  In the upstream chapter it is reduced to nothing
analytic by `Work.FockBridge.tBwordInd_eq_sum_sectorPiece` (gap half:
`cnPlusBoxInd_eq_sum_sectorPiece`; spectral half: `tBdiagSlotInd_eq_sum_sectorPiece`) and
`Work.FockBridge.qLHSword_eq_sum_sectorPiece`; what has to be supplied here is the *discharge* of
their `Integrable`/`IntegrableOn` side conditions in the regime (the corpus's suppliers are
`Work.UBBInputs8.A.integrable_qLHSBIntegrand_box`,
`Work.SlotWord.integrableOn_slotPiece_sq_qLHSden`, `Work.BoseFixB1.abs_wSmallPair_le`,
`Work.SmallBoxSliding.abs_wSmall1Pair_le`, `Work.SmallBoxSliding.w1Fibre_bdd`) and the
`Fin`/`Finset.range` rearrangement. -/
def SbWordSectorAdditive (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
      (u : EuclideanSpace ℝ (Fin 3)),
      sbWord h μ u (Φ : X n → ℝ)
        = ∑ k ∈ Finset.range (n + 1),
            (Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
                (sbCut μ (_root_.BoseGases.a v)) u
                (sectorPiece (PBB v μ u) k (Φ : X n → ℝ))
              + qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
                (sectorPiece (PBB v μ u) k (Φ : X n → ℝ)))

/-! ## 2. The assembly -/

/-- `Adm` is monotone in the diluteness threshold.  (Local copy of
`Work.BoseFixB1B.Adm_mono'`, inserted because this file uses it but does not import the module
that defines it; kept `private` so that no name is exported.  Blocking-build repair.) -/
private lemma adm_mono_local {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε ε' μ : ℝ}
    (h : Work.BoseBoxFix.Adm v ε μ) (hε : ε ≤ ε') : Work.BoseBoxFix.Adm v ε' μ :=
  ⟨h.1, le_trans h.2.1 hε, h.2.2⟩

/-- **The mixture residual from the termwise residual + the sector additivity.**  Termwise
summation only: `Σ_k m_kT(k) ≤ Σ_k word_k = sbWord`; the compatibility thresholds are merged by
`min`. -/
theorem perBoxSectorBoundG_of_pieces {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {R : ℝ} {ε₀a : ℝ} (hε₀a : 0 < ε₀a)
    (hadd : SbWordSectorAdditive v h ε₀a)
    (hper : PerSectorBoundG v h R) : PerBoxSectorBoundG v h R := by
  obtain ⟨ε₀p, c, C, hε₀p, hc0, hc14, hC0, hmain⟩ := hper
  refine ⟨min ε₀a ε₀p, c, C, lt_min hε₀a hε₀p, hc0, hc14, hC0, fun μ hAdm n Φ u hu => ?_⟩
  have hAdmA : Work.BoseBoxFix.Adm v ε₀a μ := adm_mono_local hAdm (min_le_left _ _)
  have hAdmp : Work.BoseBoxFix.Adm v ε₀p μ := adm_mono_local hAdm (min_le_right _ _)
  have hterm : (∑ k ∈ Finset.range (n + 1),
        sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k *
            ((c * psiWeight 1 μ ((k : ℝ) / PBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
              - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                  + μ * (_root_.BoseGases.a v))))
      ≤ ∑ k ∈ Finset.range (n + 1),
          (Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
              (sbCut μ (_root_.BoseGases.a v)) u
              (sectorPiece (PBB v μ u) k (Φ : X n → ℝ))
            + qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
              (sectorPiece (PBB v μ u) k (Φ : X n → ℝ))) :=
    Finset.sum_le_sum fun k hk => hmain μ hAdmp n Φ u hu k hk
  have hadd' := hadd μ hAdmA n Φ u
  linarith [hterm, hadd']

end Work.BoseFixB1
