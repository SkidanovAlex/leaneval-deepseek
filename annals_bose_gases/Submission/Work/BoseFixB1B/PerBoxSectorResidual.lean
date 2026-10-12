import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BSKinetic.Decomp.bsOneBody_eq_zero_of_far
import Submission.Work.BSKinetic.Decomp.continuous_bsOneBody
import Submission.Work.BSKinetic.FarBump.Defs
import Submission.Work.BSKinetic.FarBump.oneBody_pos_of_low_freq_bound
import Submission.Work.BSKinetic.bsOneBody_eq_dirichlet
import Submission.Work.BSKinetic.cnPlus_eq_slotSum
import Submission.Work.BSKinetic.familyBigKin_eq_slotFamily
import Submission.Work.BSKinetic.familyFormUnproj_eq_kernelForm
import Submission.Work.BSKinetic.familyForm_zero_eq
import Submission.Work.BSKinetic.tBwordBInd_slotSwap_and_integrable
import Submission.Work.BSKinetic.tsupport_bsWin_subset_bsBox
import Submission.Work.BoseFixB1.perBoxF_pieces
import Submission.Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime
import Submission.Work.BoseFixB1.w1MassB_nonneg
import Submission.Work.BoseFixB1B.Local
import Submission.Work.FockBridge.SectorAdditive
import Submission.Work.FockBridge.SectorZero
import Submission.Work.FockBridge.convexOn_dlDensityCoeff
import Submission.Work.FockBridge.integrableOn_sectorPiece_sq
import Submission.Work.FockBridge.sectorMassENN_ne_top_of_continuous
import Submission.Work.FockBridge.sum_tBamp_normSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.PerBoxSectorResidual` — the sector form of FS `thm:smallbox`

This module fixes the **single analytic residual** on which
`Work.BoseFixB1B.perBoxPointwise` (the `F`-weighted per-box bound at the sliding box
`B(u)` on the interior `I₋`) is reduced, together with the elementary bookkeeping
identities that the reduction uses (so that the reduction itself is proved in
`Submission/Work/BoseFixB1B/perBoxPointwise.lean`).

## The reduction (why the sector form is the right residual)

The frozen per-box statement `Work.BoseFixB1.PerBoxF` at `u` says

    c₁·W(u)·∫_{abox n ℓ}Φ²·F(n_{B(u)}(x)/|B(u)|) − ½μ²·W(u)·‖Φ‖²
      − C·(μ²(a v)Γ'(u)·|B(u)| + μ(a v))·‖Φ‖²
    ≤ sbWord h μ u Φ ,

where `W(u) = w1MassB h M ℓ d u = ∬ w_{1,B(u)}`, `|B(u)| = chiMass M ℓ d u`,
`F = psiWeight 1 μ` and `Γ'(u) = (R/(dℓ))² + K_B³(μ(a v)³)^{1/2}`.

FS obtain this by splitting the state into the **occupancy sectors** of the box `B(u)`
(`n_{B(u)} = Σ_i 1_{B(u)}(x_i)` is a multiplication operator commuting with `H_{B(u)}`,
`final_v2.tex` l. 3658–3662), applying `thm:smallbox` on each sector `k` at the **count**
`k`, and paying the `F`-weight by the *convexity* of `F` (FS `eq:Rconvex`,
`final_v2.tex` l. 4114–4135 — the *proved* Jensen layer of `Submission.Work.FockBridge`).
For the corpus's smooth cutoff `χ_{B(u)}` the corresponding statement is the
**`PerBoxSectorBound`** below, whose per-state content is FS `thm:smallbox` at the
localised kernels (the corpus's named residual `Work.FockBridge.PerSectorBound` /
`FockSectorBridge`, read at the frozen FS parameters, without the low-state hypothesis
and restricted to the interior `I₋`).

## The elementary half (proved elsewhere, used by the reduction)

* `Work.FockBridge.sum_sectorMass_eq_sqNorm` : `Σ_k m_k = ‖Φ‖²`;
* `Work.FockBridge.sectorPiece` : the Fock decomposition `Φ = Σ_k Φ_k`;
* `Work.BoseFixB1B.psiWeight_le_mul_add` (in `Submission/Work/BoseFixB1B/Local.lean`)
  : `F(t) ≤ (8C+8)(F(s) + μ²)` for `0 ≤ t ≤ C s` — the count ↔ density comparison;
* `Work.BoseFixB1B.sectorMass_sum_eq` (below, elementary) : the sector masses sum;
* the pointwise count bound `chiSmallB M ℓ d u x ≤ chiSupAbs·chiSmallDecay M` of
  `Work.SmallBoxSliding.abs_chiSmallB_le` (below as `nCountB_le`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The frozen parameters as abbreviations -/

/-- FS's big-box side at `(μ, v)`: `ℓ = sideAt μ (a v)`. -/
abbrev PBℓ (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)

/-- FS's `d` at `(μ, v)`. -/
abbrev PBd (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d

/-- FS's `M` at `(μ, v)`. -/
abbrev PBM (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℕ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M

/-- FS's `K_B` at `(μ, v)`. -/
abbrev PBKB (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB

/-- FS's `ε_T` at `(μ, v)`. -/
abbrev PBeT (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT

/-- The localised cutoff mass `|B(u)| = ∫ χ_{B(u)}²` at `(μ, v)`. -/
abbrev PBV (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ := chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u

/-- The localised kernel mass `∬ w_{1,B(u)}` at `(μ, v)`. -/
abbrev PBW {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.BoseFixB1.w1MassB h (PBM v μ) (PBℓ v μ) (PBd v μ) u

/-- The sliding box `B(u)` at `(μ, v)`. -/
abbrev PBB (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : Set (EuclideanSpace ℝ (Fin 3)) := dlBox (PBℓ v μ) (PBd v μ) u

/-- FS's `K_B³(μ(a v)³)^{1/2}` at `(μ, v)`. -/
abbrev PBΓ (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ := dlGamma (PBKB v μ) μ (_root_.BoseGases.a v)

/-- The universal `χ_{B(u)}`-sup bound factor: `|χ_{B(u)}| ≤ ν` with
`ν := chiSupAbs · chiSmallDecay M` (`Work.SmallBoxSliding.abs_chiSmallB_le`). -/
abbrev PBν (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ := chiSupAbs * chiSmallDecay (PBM v μ)

/-! ## 2. The residual: FS `thm:smallbox` on each occupancy sector of `B(u)` -/

/-- **The sector (mixture) form of FS `thm:smallbox` at the sliding box `B(u)`** — the
analytic residual of `Work.BoseFixB1B.perBoxPointwise`.

There are `ε₀ > 0`, `0 < c ≤ 1/4` and `C ≥ 0` such that for every admissible `μ`, every
`n`, every smooth symmetric box state `Φ` and every `u ∈ I₋`:

    Σ_k m_k·[(c·F(k/|B(u)|) − (½ − c)μ²)·∬w_{1,B(u)}
              − C·(μ²(a v)Γ_B·∬w_{1,B(u)} + μ(a v))]  ≤  sbWord h μ u Φ ,

summed over the `B(u)`-occupancy sectors `k ∈ {0,…,n}`, where

* `m_k = ∫_{1_{n_{B(u)} = k}}Φ²` is the mass of the count-`k` sector
  (`Work.FockBridge.sectorMass`, the Fock/particle-number decomposition of the
  state, `final_v2.tex` l. 3658);
* `F = psiWeight 1 μ` is FS's `F(t) = μ(t−μ)²/(t+μ)` (`final_v2.tex` l. 4121) at the
  *count density* `k/|B(u)|`, `|B(u)| = chiMass M ℓ d u` (the `χ_{B(u)}²`-mass);
* `Γ_B = K_B³(μ(a v)³)^{1/2}` (`Work.FockBridge.dlGamma`, FS's `K_B³(μa³)^{1/2}`);
* `sbWord h μ u Φ` is the frozen localised word
  (`Work.BoseFixB1.sbWord = sbKin + sbPot`, FS `eq:appTB` + `eq:HBU`).

This is FS `thm:smallbox` (`final_v2.tex` l. 3907) read at the *counting operator*
`n_{B(u)} = Σ_i 1_{B(u)}(x_i)` — the corpus's own named residual
`Work.FockBridge.PerSectorBound`/`FockSectorBridge`/`SectorBridgeAt`, at the frozen FS
parameters, restricted to the interior `I₋` and with the low-state hypothesis dropped
(the per-box bound holds for every state).

Two *free* freedoms relative to FS's own `thm:smallbox` shape are used deliberately:

* the mass normalisation is the **actual localised mass** `∬w_{1,B(u)} = w1MassB h M ℓ d u`
  rather than the nominal `8π(a v)|B(u)|` — this is what makes both sides of the
  reduction carry the *same* mass factor, so that the `−½μ²∬w₁` backgrounds cancel
  exactly (FS's own bookkeeping in `thm:aprioriHLambda`);
* the background coefficient is `½ − c` instead of `½` — a *strictly weaker* claim (in the
  FS regime one has the sharp mass normalisation `w1MassB ≤ C(a v)chiMass`,
  `Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime`, so the `½`-shape follows from the
  `(½ − c)`-shape with enlarged constants).

The analytic content is the per-`k` potential-side `lm:appinteractionestimate`/`A₀`
mean-field evaluation at the localised kernels `wSmallPair`/`wSmall1Pair` together with
FS's `eq:appgapestimate` payment of the excited count by the gap term — i.e. exactly the
`hsum`/`FockSectorBridge` residual of `Submission.Work.FockBridge`, whose proved half
(the sector partition, the Jensen/mixture layer, the sector-additivity pieces, the count
identity `Σ_k k m_k = n_{B(u)}`) is already in the corpus. -/
def PerBoxSectorBound (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ interiorSet (PBℓ v μ) (PBd v μ) μ →
          (∑ k ∈ Finset.range (n + 1),
              sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k *
                ((c * psiWeight 1 μ ((k : ℝ) / PBV v μ u) - (1 / 2 - c) * μ ^ 2)
                    * PBW h μ u
                  - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                      + μ * (_root_.BoseGases.a v))))
            ≤ Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ)

/-! ## 3. The elementary bookkeeping used by the reduction -/

/-- **The sector masses sum to the box norm**: `Σ_k m_k = ‖Φ‖²` for a smooth box state
(`Work.FockBridge.sum_sectorMass_eq_sqNorm` at the box `B(u)` of the sliding geometry). -/
theorem sectorMass_sum {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : EuclideanSpace ℝ (Fin 3)) :
    ∑ k ∈ Finset.range (n + 1),
        sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
      = Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
  have := sum_sectorMass_eq_sqNorm (N := n) (PBℓ v μ) (B := PBB v μ u)
    (Work.SmallBoxSliding.measurableSet_dlBox (PBℓ v μ) (PBd v μ) u)
    (Φ.contDiff.continuous.measurable)
    (sectorMassENN_ne_top_of_continuous (N := n) (L := PBℓ v μ) Φ.contDiff.continuous)
  rw [this]
  rfl

/-! ## 1. `M = 48` and the constant `χ`-bound -/

/-- `Adm` is monotone in the diluteness threshold. -/
lemma Adm_mono' {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε ε' μ : ℝ} (h : Adm v ε μ)
    (hε : ε ≤ ε') : Adm v ε' μ :=
  ⟨h.1, le_trans h.2.1 hε, h.2.2⟩

/-- FS's regularity parameter is the fixed `M = mValue = 48`. -/
lemma PBM_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) :
    PBM v μ = Work.BoseBox.mValue := rfl

lemma one_le_PBM (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : 1 ≤ PBM v μ := by
  rw [PBM_eq]; decide

/-- The `χ_{B(u)}`-sup bound `PBν` is independent of `μ`. -/
lemma PBν_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) :
    PBν v μ = chiSupAbs * chiSmallDecay Work.BoseBox.mValue := by
  rw [PBν, PBM_eq]

lemma PBν_nonneg (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : 0 ≤ PBν v μ :=
  mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg _)

/-! ## 2. The support of the localised cutoff and the pointwise count bound -/

/-- **The localised cutoff is supported in the sliding box**: `χ_{B(u)}(z) ≠ 0` forces
`z ∈ B(u) = dlBox ℓ d u`. -/
lemma chiSmallB_mem_dlBox {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {M : ℕ} (hM : 1 ≤ M)
    (u z : EuclideanSpace ℝ (Fin 3)) (hz : chiSmallB M ℓ d u z ≠ 0) :
    z ∈ dlBox ℓ d u := by
  have hfac : chiSmallB M ℓ d u z = chiScale ℓ z * chiSmall M ((ℓ * d)⁻¹ • z - u) := rfl
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have h1 : chiScale ℓ z ≠ 0 := fun h => hz (by rw [hfac, h, zero_mul])
  have h2 : chiSmall M ((ℓ * d)⁻¹ • z - u) ≠ 0 := fun h => hz (by rw [hfac, h, mul_zero])
  have hbase : chiSmallBase M ((ℓ * d)⁻¹ • z - u) ≠ 0 := by
    intro hb
    exact h2 (by rw [chiSmall, hb]; simp)
  have hcoord : ∀ j : Fin 3, |(((ℓ * d)⁻¹ • z - u).ofLp j)| ≤ 1 / 2 :=
    fun j => chiSmallBase_support_mem_abs_le hM hbase j
  refine ⟨chiScale_mem_acube hℓ h1, ?_⟩
  change z - (ℓ * d) • u ∈ acube (ℓ * d)
  rw [mem_acube_iff]
  intro j
  rw [Set.mem_Icc]
  have h := hcoord j
  have hrew2 : ((ℓ * d)⁻¹ • z - u) = (ℓ * d)⁻¹ • (z - (ℓ * d) • u) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hld), one_smul]
  have hrew : ((ℓ * d)⁻¹ • z - u).ofLp j = (ℓ * d)⁻¹ * (z - (ℓ * d) • u).ofLp j := by
    rw [hrew2]; simp [PiLp.smul_apply]
  rw [hrew, abs_mul, abs_of_pos (inv_pos.mpr hld)] at h
  have h2' : |(z - (ℓ * d) • u).ofLp j| ≤ ℓ * d / 2 := by
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hld)
    have hsimp : ℓ * d * ((ℓ * d)⁻¹ * |(z - (ℓ * d) • u).ofLp j|)
        = |(z - (ℓ * d) • u).ofLp j| := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hld), one_mul]
    rw [hsimp] at hmul
    linarith [hmul]
  exact ⟨by linarith [(abs_le.mp h2').1], by linarith [(abs_le.mp h2').2]⟩

/-- **The pointwise count bound on a sector**: on the `B(u)`-occupancy sector `k` the smooth
count is at most `ν²k`. -/
lemma nCountB_le_sectorSet {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hℓ : 0 < PBℓ v μ) (hd : 0 < PBd v μ) {n : ℕ} (u : EuclideanSpace ℝ (Fin 3)) {x : X n}
    {k : ℕ} (hx : x ∈ sectorSet (PBB v μ u) k) :
    Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x ≤ (PBν v μ) ^ 2 * (k : ℝ) := by
  have hM : 1 ≤ PBM v μ := one_le_PBM v μ
  have hν0 : 0 ≤ PBν v μ := PBν_nonneg v μ
  have hslot : ∀ i : Fin n,
      (chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u (x i)) ^ 2
        ≤ (PBν v μ) ^ 2 * (PBB v μ u).indicator (fun _ => (1 : ℝ)) (x i) := by
    intro i
    by_cases hi : x i ∈ PBB v μ u
    · rw [Set.indicator_of_mem hi, mul_one]
      have h1 : |chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u (x i)| ≤ PBν v μ := by
        have ha := Work.SmallBoxSliding.abs_chiSmallB_le (M := PBM v μ) (ℓ := PBℓ v μ)
          (d := PBd v μ) hM u (x i)
        have hb : chiSmall (PBM v μ) ((PBℓ v μ * PBd v μ)⁻¹ • x i - u)
            ≤ chiSmallDecay (PBM v μ) := by
          have h' := chiSmall_decay_coord_le_decay hM ((PBℓ v μ * PBd v μ)⁻¹ • x i - u)
          rwa [abs_of_nonneg (chiSmall_nonneg (PBM v μ) _)] at h'
        calc |chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u (x i)|
            ≤ chiSupAbs * chiSmall (PBM v μ) ((PBℓ v μ * PBd v μ)⁻¹ • x i - u) := ha
          _ ≤ chiSupAbs * chiSmallDecay (PBM v μ) :=
              mul_le_mul_of_nonneg_left hb chiSupAbs_nonneg
          _ = PBν v μ := rfl
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hν0] using h1)
    · have hzero : chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u (x i) = 0 := by
        by_contra hne
        exact hi (chiSmallB_mem_dlBox hℓ hd hM u (x i) hne)
      rw [Set.indicator_of_notMem hi, mul_zero, hzero]; simp
  calc Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x
      = ∑ i : Fin n, (chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u (x i)) ^ 2 := rfl
    _ ≤ ∑ i : Fin n, (PBν v μ) ^ 2 * (PBB v μ u).indicator (fun _ => (1 : ℝ)) (x i) :=
        Finset.sum_le_sum fun i _ => hslot i
    _ = (PBν v μ) ^ 2 * ∑ i : Fin n, (PBB v μ u).indicator (fun _ => (1 : ℝ)) (x i) := by
        rw [Finset.mul_sum]
    _ = (PBν v μ) ^ 2 * boxCount (PBB v μ u) x := by
        rw [boxCount_eq_sum_indicator]
    _ = (PBν v μ) ^ 2 * (k : ℝ) := by
        rw [boxCount_eq_of_mem_sectorSet (PBB v μ u) hx]

lemma nCountB_nonneg' {v : EuclideanSpace ℝ (Fin 3) → ℝ} (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (x : X n) :
    0 ≤ Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x := by
  rw [Work.BoseFixB1.nCountB]
  positivity

/-! ## 3. The count ↔ density bridge (the smooth `F`-weight vs the sector sum) -/

/-- **The count ↔ density bridge**: the smooth `F`-weight integral is dominated by the
sector mixture of the *count*-indexed `F`-weights, up to the universal constant
`K₀ = 8ν² + 8` and the `μ²·‖Φ‖²` term of FS's `F`-growth bound. -/
theorem countDensityBridge {v : EuclideanSpace ℝ (Fin 3) → ℝ} (_h : Work.UBB.ScatSol v)
    {μ : ℝ} (hμ : 0 < μ) (hℓ : 0 < PBℓ v μ) (hd : 0 < PBd v μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
    (u : EuclideanSpace ℝ (Fin 3)) :
    (∫ x in abox n (PBℓ v μ),
        (Φ x) ^ 2 * psiWeight 1 μ
          (Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x / PBV v μ u))
      ≤ (8 * (PBν v μ) ^ 2 + 8) *
          ((∑ k ∈ Finset.range (n + 1),
              sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k *
                psiWeight 1 μ ((k : ℝ) / PBV v μ u))
            + μ ^ 2 * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) := by
  classical
  set B : Set (EuclideanSpace ℝ (Fin 3)) := PBB v μ u with hB
  set V : ℝ := PBV v μ u with hV
  set ν : ℝ := PBν v μ with hν
  set K₀ : ℝ := 8 * ν ^ 2 + 8 with hK
  have hBmeas : MeasurableSet B := Work.SmallBoxSliding.measurableSet_dlBox _ _ _
  have hV0 : 0 ≤ V := hV ▸ chiMass_nonneg _ _ _ _
  have hK0 : 0 ≤ K₀ := by rw [hK]; positivity
  -- the pointwise bound
  have hpt : ∀ x : X n, (Φ x) ^ 2 * psiWeight 1 μ
        (Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x / V)
      ≤ ∑ k ∈ Finset.range (n + 1), (sectorPiece B k (Φ : X n → ℝ) x) ^ 2 *
          (K₀ * (psiWeight 1 μ ((k : ℝ) / V) + μ ^ 2)) := by
    intro x
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (sectorPiece B k (Φ : X n → ℝ) x) ^ 2 * psiWeight 1 μ
            (Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x / V)
          ≤ (sectorPiece B k (Φ : X n → ℝ) x) ^ 2 *
              (K₀ * (psiWeight 1 μ ((k : ℝ) / V) + μ ^ 2)) := by
      intro k _
      by_cases hk : x ∈ sectorSet B k
      · have hcount : Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x
            ≤ ν ^ 2 * (k : ℝ) := by
          have hk' : x ∈ sectorSet (PBB v μ u) k := hB ▸ hk
          have h := nCountB_le_sectorSet (v := v) (μ := μ) hℓ hd u (k := k) hk'
          simpa [hν] using h
        have hts : Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x / V
            ≤ ν ^ 2 * ((k : ℝ) / V) := by
          rw [div_eq_mul_inv, div_eq_mul_inv,
            show ν ^ 2 * ((k : ℝ) * V⁻¹) = (ν ^ 2 * (k : ℝ)) * V⁻¹ by ring]
          exact mul_le_mul_of_nonneg_right hcount (inv_nonneg.mpr hV0)
        have hF := psiWeight_le_mul_add (μ := μ) (t := Work.BoseFixB1.nCountB (PBM v μ)
              (PBℓ v μ) (PBd v μ) u x / V) (s := (k : ℝ) / V) (C := ν ^ 2) hμ
          (div_nonneg (nCountB_nonneg' μ u x) hV0) (div_nonneg (Nat.cast_nonneg k) hV0)
          (sq_nonneg ν) hts
        have : psiWeight 1 μ (Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x / V)
            ≤ K₀ * (psiWeight 1 μ ((k : ℝ) / V) + μ ^ 2) := by
          simpa [hK, hν] using hF
        exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
      · rw [sectorPiece, Set.indicator_of_notMem hk]; simp
    calc (Φ x) ^ 2 * psiWeight 1 μ
            (Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x / V)
        = (∑ k ∈ Finset.range (n + 1), (sectorPiece B k (Φ : X n → ℝ) x) ^ 2) *
            psiWeight 1 μ
              (Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x / V) := by
          rw [sum_sectorPiece_sq]
      _ = ∑ k ∈ Finset.range (n + 1), (sectorPiece B k (Φ : X n → ℝ) x) ^ 2 *
            psiWeight 1 μ
              (Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x / V) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ k ∈ Finset.range (n + 1), (sectorPiece B k (Φ : X n → ℝ) x) ^ 2 *
            (K₀ * (psiWeight 1 μ ((k : ℝ) / V) + μ ^ 2)) := Finset.sum_le_sum hterm
  -- the integral comparison
  have hΦ2int : IntegrableOn (fun x : X n => (Φ x) ^ 2) (abox n (PBℓ v μ)) :=
    ContinuousOn.integrableOn_compact (abox_compact n hℓ) ((Φ.contDiff.continuous.pow 2).continuousOn)
  have hfin : (∫⁻ x in abox n (PBℓ v μ), ENNReal.ofReal (((Φ : X n → ℝ) x) ^ 2)) ≠ ⊤ :=
    sectorMassENN_ne_top_of_continuous (N := n) (L := PBℓ v μ) Φ.contDiff.continuous
  have hIntR : IntegrableOn (fun x : X n => ∑ k ∈ Finset.range (n + 1),
      (sectorPiece B k (Φ : X n → ℝ) x) ^ 2 *
        (K₀ * (psiWeight 1 μ ((k : ℝ) / V) + μ ^ 2))) (abox n (PBℓ v μ)) := by
    refine integrable_finsetSum _ (fun k _ => ?_)
    exact (integrableOn_sectorPiece_sq (N := n) (L := PBℓ v μ) hBmeas Φ.contDiff.continuous k).mul_const _
  refine integral_mono_of_nonneg (ae_of_all _ (fun x => mul_nonneg (sq_nonneg _)
    (psiWeight_nonneg hμ (div_nonneg (nCountB_nonneg' μ u x) hV0)))) hIntR (ae_of_all _ hpt) |>.trans ?_
  rw [integral_finsetSum]
  swap
  · intro k _
    exact (integrableOn_sectorPiece_sq (N := n) (L := PBℓ v μ) hBmeas Φ.contDiff.continuous k).mul_const _
  refine le_of_eq ?_
  rw [show (∑ k ∈ Finset.range (n + 1), ∫ x in abox n (PBℓ v μ),
        (sectorPiece B k (Φ : X n → ℝ) x) ^ 2 *
          (K₀ * (psiWeight 1 μ ((k : ℝ) / V) + μ ^ 2)))
      = ∑ k ∈ Finset.range (n + 1),
          (K₀ * (psiWeight 1 μ ((k : ℝ) / V) + μ ^ 2)) *
            sectorMass (PBℓ v μ) B (Φ : X n → ℝ) k from ?_]
  · rw [← sectorMass_sum (v := v) (μ := μ) Φ u]
    conv_rhs => rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_mul_const,
      ← sectorMass_eq_integral_sectorPiece (PBℓ v μ) hBmeas Φ.contDiff.continuous.measurable k
        (sectorMassENN_ne_top_of_ne_top (PBℓ v μ) B (Φ : X n → ℝ) k hfin)]
    ring

/-! ## 4. The reduction: from the sector residual to `PerBoxF` -/

/-- **The pointwise linear algebra of the reduction** (no analysis): from the sector residual's
summed inequality, the count ↔ density bridge, the mass normalisation and the mass sum, the
frozen `PerBoxF` inequality follows with `c₁ := c/K₀`, `C := C_res·(C_W·max(a v) 1 + 1)`. -/
lemma perBoxArithSum {ι : Type*} (s : Finset ι) (m Fk : ι → ℝ)
    {c C C_W K₀ μ aV W V A Mn sb ΓB Γ' : ℝ}
    (hμ : 0 < μ) (haV : 0 < aV) (hV : 0 ≤ V) (hW0 : 0 ≤ W) (hMn : 0 ≤ Mn)
    (hΓ0B : 0 ≤ ΓB) (hΓle : ΓB ≤ Γ') (hc0 : 0 < c) (hK0 : 0 < K₀)
    (hC0 : 0 ≤ C) (hCW0 : 0 ≤ C_W)
    (hA : A ≤ K₀ * ((∑ k ∈ s, m k * Fk k) + μ ^ 2 * Mn))
    (hS : (∑ k ∈ s, m k * ((c * Fk k - (1 / 2 - c) * μ ^ 2) * W
              - C * (μ ^ 2 * aV * ΓB * W + μ * aV))) ≤ sb)
    (hsum : (∑ k ∈ s, m k) = Mn)
    (hWle : W ≤ C_W * aV * V) :
    (c / K₀) * (W * A) - (1 / 2) * μ ^ 2 * W * Mn
      - C * (C_W * max aV 1 + 1) * ((μ ^ 2 * aV * Γ' * V) * Mn + μ * aV * Mn) ≤ sb := by
  have hKne : K₀ ≠ 0 := ne_of_gt hK0
  have hΓ0' : 0 ≤ Γ' := le_trans hΓ0B hΓle
  have hmax0 : 0 ≤ max aV 1 := le_trans (le_of_lt haV) (le_max_left aV 1)
  have hkey : ΓB * W ≤ (C_W * max aV 1 + 1) * (Γ' * V) := by
    have h1 : ΓB * W ≤ Γ' * W := mul_le_mul_of_nonneg_right hΓle hW0
    have h2 : Γ' * W ≤ Γ' * (C_W * aV * V) := mul_le_mul_of_nonneg_left hWle hΓ0'
    have h3 : C_W * aV * V ≤ C_W * max aV 1 * V := by
      have ha : aV ≤ max aV 1 := le_max_left _ _
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hCW0) hV
      linarith [h]
    have h4 : Γ' * (C_W * aV * V) ≤ Γ' * (C_W * max aV 1 * V) :=
      mul_le_mul_of_nonneg_left h3 hΓ0'
    have h5 : Γ' * (C_W * max aV 1 * V) ≤ (C_W * max aV 1 + 1) * (Γ' * V) := by
      have h6 : C_W * max aV 1 ≤ C_W * max aV 1 + 1 := by linarith
      have h7 := mul_le_mul_of_nonneg_right h6 (mul_nonneg hΓ0' hV)
      have h8 : Γ' * (C_W * max aV 1 * V) = (C_W * max aV 1) * (Γ' * V) := by ring
      linarith [h7, h8]
    linarith [h1, h2, h4, h5]
  have herr : C * ((μ ^ 2 * aV * ΓB * W) + μ * aV) * Mn
      ≤ C * (C_W * max aV 1 + 1) * ((μ ^ 2 * aV * Γ' * V) * Mn + μ * aV * Mn) := by
    have h1 : (1 : ℝ) ≤ C_W * max aV 1 + 1 := by linarith [mul_nonneg hCW0 hmax0]
    have h2 : μ ^ 2 * aV * ΓB * W ≤ (C_W * max aV 1 + 1) * (μ ^ 2 * aV * Γ' * V) := by
      have hcoef : 0 ≤ μ ^ 2 * aV := by positivity
      have h := mul_le_mul_of_nonneg_left hkey hcoef
      calc μ ^ 2 * aV * ΓB * W ≤ μ ^ 2 * aV * ((C_W * max aV 1 + 1) * (Γ' * V)) := by
            linarith [h]
        _ = (C_W * max aV 1 + 1) * (μ ^ 2 * aV * Γ' * V) := by ring
    have h3 : μ * aV ≤ (C_W * max aV 1 + 1) * (μ * aV) :=
      le_mul_of_one_le_left (by positivity) h1
    have h4 : μ ^ 2 * aV * ΓB * W + μ * aV
        ≤ (C_W * max aV 1 + 1) * (μ ^ 2 * aV * Γ' * V + μ * aV) := by
      calc μ ^ 2 * aV * ΓB * W + μ * aV
          ≤ (C_W * max aV 1 + 1) * (μ ^ 2 * aV * Γ' * V) + (C_W * max aV 1 + 1) * (μ * aV) :=
            add_le_add h2 h3
        _ = (C_W * max aV 1 + 1) * (μ ^ 2 * aV * Γ' * V + μ * aV) := by ring
    have h5 : C * (μ ^ 2 * aV * ΓB * W + μ * aV)
        ≤ (C * (C_W * max aV 1 + 1)) * (μ ^ 2 * aV * Γ' * V + μ * aV) := by
      have h := mul_le_mul_of_nonneg_left h4 hC0
      have h6 : C * ((C_W * max aV 1 + 1) * (μ ^ 2 * aV * Γ' * V + μ * aV))
          = (C * (C_W * max aV 1 + 1)) * (μ ^ 2 * aV * Γ' * V + μ * aV) := by ring
      linarith [h, h6]
    have h6 := mul_le_mul_of_nonneg_right h5 hMn
    have h7 : (C * (C_W * max aV 1 + 1)) * (μ ^ 2 * aV * Γ' * V + μ * aV) * Mn
        = C * (C_W * max aV 1 + 1) * ((μ ^ 2 * aV * Γ' * V) * Mn + μ * aV * Mn) := by ring
    linarith [h6, h7]
  have hterm1 : (c / K₀) * (W * A) ≤ c * W * ((∑ k ∈ s, m k * Fk k) + μ ^ 2 * Mn) := by
    have hcK : K₀ * (c / K₀) = c := by field_simp
    have h1 : A * (c / K₀) ≤ c * ((∑ k ∈ s, m k * Fk k) + μ ^ 2 * Mn) := by
      calc A * (c / K₀) ≤ (K₀ * ((∑ k ∈ s, m k * Fk k) + μ ^ 2 * Mn)) * (c / K₀) :=
            mul_le_mul_of_nonneg_right hA (div_nonneg hc0.le hK0.le)
        _ = c * ((∑ k ∈ s, m k * Fk k) + μ ^ 2 * Mn) := by
            rw [mul_assoc, mul_comm ((∑ k ∈ s, m k * Fk k) + μ ^ 2 * Mn) (c / K₀),
              ← mul_assoc, hcK]
    calc (c / K₀) * (W * A) = W * (A * (c / K₀)) := by ring
      _ ≤ W * (c * ((∑ k ∈ s, m k * Fk k) + μ ^ 2 * Mn)) := mul_le_mul_of_nonneg_left h1 hW0
      _ = c * W * ((∑ k ∈ s, m k * Fk k) + μ ^ 2 * Mn) := by ring
  have hexp : (∑ k ∈ s, m k * ((c * Fk k - (1 / 2 - c) * μ ^ 2) * W
        - C * (μ ^ 2 * aV * ΓB * W + μ * aV)))
      = (∑ k ∈ s, (c * W) * (m k * Fk k)) - (∑ k ∈ s, ((1 / 2 - c) * μ ^ 2 * W) * m k)
        - (∑ k ∈ s, (C * (μ ^ 2 * aV * ΓB * W + μ * aV)) * m k) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hexp] at hS
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum] at hS
  nlinarith [hterm1, hS, herr, hC0, hC0, hCW0, hmax0, hV, hΓ0', hΓ0B, hMn, sq_nonneg μ,
    mul_nonneg (sq_nonneg μ) (le_of_lt haV), mul_nonneg hC0 hCW0,
    mul_nonneg (mul_nonneg hC0 hCW0) hmax0]

/-- **The reduction**: the sector/mixture form of FS `thm:smallbox` (the residual
`PerBoxSectorBound`, `Submission/Work/BoseFixB1B/perBoxSectorBound_holds.lean`) implies the
frozen `F`-weighted per-box bound `Work.BoseFixB1.PerBoxF` on the interior `I₋`, with the
constants `c₁ := c/K₀`, `C := C_res·(C_W·max(a v) 1 + 1)` and
`ε₀ := min ε₀_res ε₀_mass`. -/
theorem perBoxPointwise_of_sectorBound {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hb : PerBoxSectorBound v h R) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u := by
  obtain ⟨ε₀s, c, C, hε₀s, hc0, hc14, hC0, hmain⟩ := hb
  obtain ⟨ε₀w, C_W, hε₀w, hCW0, hWb⟩ :=
    Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) (h := h) hv hvrad hR hv_supp
  have hν0 : 0 < chiSupAbs * chiSmallDecay Work.BoseBox.mValue := by
    have hM48 : 1 ≤ Work.BoseBox.mValue := by rw [Work.BoseBox.mValue]; norm_num
    have h1 : 0 < chiSupAbs := by
      rw [chiSupAbs]
      exact inv_pos.mpr (Real.sqrt_pos.mpr chiNormSq_pos)
    have h2 : 0 < chiSmallDecay Work.BoseBox.mValue := by
      rw [chiSmallDecay, chiSmallNormFactor]
      exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (chiSmallNormSq_pos hM48))) (by positivity)
    exact mul_pos h1 h2
  refine ⟨min ε₀s ε₀w, c / (8 * (chiSupAbs * chiSmallDecay Work.BoseBox.mValue) ^ 2 + 8),
    C * (C_W * max (_root_.BoseGases.a v) 1 + 1), lt_min hε₀s hε₀w,
    div_pos hc0 (by positivity), by positivity, ?_⟩
  intro μ hAdm n Φ u hu
  have hAs : Work.BoseBoxFix.Adm v ε₀s μ := Adm_mono' hAdm (min_le_left _ _)
  have hAw : Work.BoseBoxFix.Adm v ε₀w μ := Adm_mono' hAdm (min_le_right _ _)
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hWle := hWb μ hAw u
  have hbridge := countDensityBridge h hμ hℓ hd Φ u
  have hres := hmain μ hAs n Φ u hu
  have hsum := sectorMass_sum (v := v) (μ := μ) Φ u
  have hm0 : 0 ≤ PBW h μ u :=
    Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hnorm0 : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg _
  have hΓ0 : 0 ≤ PBΓ v μ := by
    rw [PBΓ, dlGamma]
    have h1 : 0 ≤ (paramsAt μ (_root_.BoseGases.a v)).KB := le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)
    have h2 : 0 ≤ μ * (_root_.BoseGases.a v) ^ 3 := by positivity
    exact mul_nonneg (pow_nonneg h1 3) (Real.rpow_nonneg h2 _)
  have hΓle : PBΓ v μ ≤ (R / (PBℓ v μ * PBd v μ)) ^ 2 + PBΓ v μ := by
    have : 0 ≤ (R / (PBℓ v μ * PBd v μ)) ^ 2 := sq_nonneg _
    linarith
  have hνeq : PBν v μ = chiSupAbs * chiSmallDecay Work.BoseBox.mValue := PBν_eq v μ
  have key := perBoxArithSum (s := Finset.range (n + 1))
    (m := fun k : ℕ => sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k)
    (Fk := fun k : ℕ => psiWeight 1 μ ((k : ℝ) / PBV v μ u))
    (c := c) (C := C) (C_W := C_W) (K₀ := 8 * (chiSupAbs * chiSmallDecay Work.BoseBox.mValue) ^ 2 + 8)
    (μ := μ) (aV := _root_.BoseGases.a v) (W := PBW h μ u) (V := PBV v μ u)
    (A := ∫ x in abox n (PBℓ v μ), (Φ x) ^ 2 * psiWeight 1 μ
      (Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x / PBV v μ u))
    (Mn := Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ))
    (sb := Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ))
    (ΓB := PBΓ v μ) (Γ' := (R / (PBℓ v μ * PBd v μ)) ^ 2 + PBΓ v μ)
    hμ (Work.BoseFixB1.adm_a_pos hAdm) (chiMass_nonneg _ _ _ _) hm0 hnorm0 hΓ0 hΓle hc0
    (by positivity) hC0 hCW0 (by simpa [hνeq] using hbridge) hres hsum hWle
  unfold Work.BoseFixB1.PerBoxF
  exact key

end Work.BoseFixB1B
