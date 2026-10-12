import ChallengeDeps
import Submission.Work.BoseFixB1B.PerBoxSectorResidual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
-- NOTE (my request's lead agent, fix of an import cycle): the line
--   `import Submission.Work.BoseFixB1B.perBoxPointwise`
-- was REMOVED here: it is redundant.  The only declaration of that module this file uses is
-- `Work.BoseFixB1B.sectorMass_sum`, which is *also* defined in `PerBoxSectorResidual`
-- (imported just above, same namespace), and the import made the whole `PerBoxSectorBoundG`
-- chain (this file, `perSectorBoundG`, `perSectorBoundG_excited`, `perSectorBoundG_condensed`,
-- `sbWordSectorAdditiveAdm`, `perSectorBoundG_holds`) *cyclically* depend on
-- `Submission.Work.BoseFixB1B.perBoxPointwise`, which in turn must import
-- `Work.BoseFixB1B.perBoxSectorBound_holds` in order to consume `PerBoxSectorBound`.  With the
-- import removed the cycle disappears and `Work.BoseFixB1B.perBoxPointwise` can be wired to the
-- chain (see the docstring of `Submission/Work/BoseFixB1B/perBoxPointwise.lean`).

/-!
# `Submission.Work.BoseFixB1.PerBoxResidualG` — the sector residual of FS `thm:smallbox`
# at the **good set** `G` (this chapter's single analytic input)

`Work.BoseFixB1B.PerBoxSectorBound` (`Submission/Work/BoseFixB1B/PerBoxSectorResidual.lean`) is
FS `thm:smallbox` read at the counting operator `n_{B(u)} = Σᵢ1_{B(u)}(xᵢ)`, on the **interior**
`I₋ = interiorSet ℓ d μ` (the truncated box `B(u) = dlBox ℓ d u` has all sides `≥ 2μ^{-1/3}`).
Its implication for the frozen target `Work.BoseFixB1.PerBoxF` is *proved* there and in
`Submission/Work/BoseFixB1B/perBoxPointwise.lean`
(`Work.BoseFixB1B.perBoxPointwise_of_sectorBound`), with the count ↔ density bridge
`Work.BoseFixB1B.countDensityBridge` and the pure arithmetic `Work.BoseFixB1B.perBoxArithSum`.

The frozen target, however, quantifies over the whole **good set**
`G = goodSet ℓ d μ = {u : ‖(ℓd)•u‖_∞ ≤ ½ℓ(1+d) − μ^{-1/3}}`, which contains `I₋` strictly.
`u ∈ G ∖ I₋` is exactly the band in which the truncated box `B(u)` has a side in
`[μ^{-1/3}, 2μ^{-1/3})`; FS's `thm:smallbox` covers those boxes too (its standing hypothesis is
only `λ₁(u) ≥ μ^{-1/3}`, which *is* the definition of `G`), and `G` is precisely the set on which
FS's mass law `eq:w1>` is valid (`λ₁(u) ≫ R` ⟹ the cutoff support of `B(u)` is fatter than
`supp g₀`, which is what `FINDING_w1MassB_ge_const_mul_chiMass.md` shows fails for general `u`).

This module therefore records the residual in its **`G`-form**, which is the form the frozen
target needs:

    PerBoxSectorBoundG v h R  :  ∃ ε₀ c C, 0 < ε₀ ∧ 0 < c ∧ c ≤ ¼ ∧ 0 ≤ C ∧
      ∀ μ, Adm v ε₀ μ → ∀ n Φ u, u ∈ goodSet ℓ d μ →
        Σ_k m_k·[(c·F(k/|B(u)|) − (½−c)μ²)·∬w_{1,B(u)}
                  − C·(μ²(a v)·K_B³(μ(a v)³)^{1/2}·∬w_{1,B(u)} + μ(a v))]  ≤  sbWord h μ u Φ,

where the sum runs over the `B(u)`-occupancy sectors `k ∈ {0,…,n}`, `m_k` is the `Φ²`-mass of
the sector `k`, `F = psiWeight 1 μ = μ(t−μ)²/(t+μ)`, `|B(u)| = chiMass M ℓ d u` and
`sbWord = sbKin + sbPot` is the frozen localised word.

Nothing new is proved here: the definition, its relation to the frozen statement and the two
helper facts (`sectorMassG_sum`, the `sectorMass_of_G` restriction) are recorded so
that the residual can be dispatched as one lemma and consumed without ambiguity.  The reduction
itself is `Submission/Work/BoseFixB1/perBoxFWeight_holds.lean`
(`perBoxFWeight_of_sectorBoundG`).

## ROUTE (for a prover: read this before starting)

The residual is **FS `thm:smallbox` (`Papers/fournais_solovej/final_v2.tex` l. 3907–4065) read at
the counting operator** `n_{B(u)} = Σᵢ1_{B(u)}(xᵢ)`, summed over the occupancy sectors of
`B(u) = dlBox ℓ d u` (FS l. 3658–3662 and l. 4114–4135).  FS's proof uses, in order:

1. **the localised potsplit** (`eq:potsplit` at the small box, FS l. 3690–3730) —
   **PROVED** in this workspace: `Work.BoseFixB1.potsplit_localised_of_memLp`
   (`Submission/Work/BoseFixB1/potsplit_localised_memLp.lean`) and, at the box-projected words,
   `Work.BoseFixB1S.bqPotsplit` (`qLHSword = boxQSum`, sorry-free) with the vocabulary of
   `Submission/Work/BoseFixB1S/BoxQWords.lean`;
2. **FS `lm:appinteractionestimate`** (`eq:SmallsimpleQs`/`eq:A0`): the potential side dominates
   `A₀ + A₂ − Ca(μ + n₀|B|⁻¹)n₊`.  The *reduced* `A₀`-step (`boxQ0 ≥ a0MainLocBox`) is **PROVED**
   as `Work.BoseFixB1.boxQ0_ge_a0MainBox` (`Submission/Work/BoseFixB1/boxQ0_ge_a0MainBox.lean`),
   with the quantitative slack `Work.BoseFixB1.boxM1G_le_boxQ0_sub_a0MainLocBox` and the exact
   identities `a0MainLocBox_slack`, `boxQ0_sub_a0MainLocBox_eq` of
   `Submission/Work/BoseFixB1/boxQSum_ge_a0Main_add_A2.lean` (whose file ALSO proves the whole
   *pattern collapse* of the four two-slot patterns `A,B,C,D` onto the slot means);
   the full statement is being proved at `Work.BoseFixB1.lm_appinteraction_localised`
   (`Submission/Work/BoseFixB1/lm_appinteraction_localised.lean`) — import it if it has landed;
3. **the box Cauchy–Schwarz `S² − S ≤ Pc`** — **PROVED** as
   `Work.BoseFixB1S.boxFlatSqJensen` (`Submission/Work/BoseFixB1S/boxFlatSqJensen.lean`); this is
   the `hcS2` gate of step 2;
4. **FS `lm:appbogolubov`** (`eq:refinedaprioribog`, `eq:simpleaprioribog`): the spectral column
   plus `A₂` dominates `−½(1+o(1))ĝω(0)((n+1)n/|B|²)∫χ_B²`.  The *global*-box version is
   **PROVED** (`Work.SmallBoxA0.lm_appbogolubov_pWord_explicitC`,
   `Submission/Work/SmallBoxA0/lm_appbogolubov_pWord_explicitC.lean`, with the whole D1 layer
   `SmallBoxD1Final.lm_appbogolubov_pWord_holds`); the faithful statement at the sliding box is
   `Work.BoseFixB1.localised_lm_appbogolubov`
   (`Submission/Work/BoseFixB1/localised_lm_appbogolubov.lean`, currently `sorry`).
   **WARNING (a trap that has already cost one delegation):** the mass factor of this lemma is
   `(particle number + 1) × (particle number)` — the *scalar* particle count coming from
   `[b_p,b_p†] ≤ n₀|B|⁻¹∫χ_B² ≤ n|B|⁻¹∫χ_B²` — and NOT the state's condensate count squared.
   The variant with `(bFlat+1)·bFlat` (the frozen `Work.BoseFixB1.boxA2_add_spectral_ge_bogoliubovMain`)
   is **FALSE**: `S²` is quartic in the state while `bSpectral`, `bA2` are quadratic, so the free
   scaling `Φ ↦ tΦ` kills the payer and the statement collapses to a *linear* bound with an
   `n`-independent coefficient — see `FINDING_lm_appbogolubov_localised_FALSE.md`.  In the
   *sector* reading of the residual the scalar is the **sector count** `k`, and `(k+1)k` is
   quadratic in `k` on both sides — which is exactly why the residual is stated sector-wise;
5. **FS `lm:w2>w1`** (`eq:w1>`, `eq:w>g`, `eq:wepsilong`, FS l. 3857–3905): the mass comparisons
   `M₁ ≥ 8π(a v)(1−o(1))χ` and `M₂ ≥ ¾M₁ + ((1+ε)ĝω(0)+εa)χ`.  The corpus has the *weak*
   comparison `M₁ ≤ M₂` (`Work.BoseFixB1.w1MassB_le_w2MassB_localised`) and the *upper* mass law
   `M₁ ≤ C_W(a v)χ` (`Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime`, PROVED); the *lower*
   law is FALSE for general `u` (`Work.BoseFixB1/FINDING_w1MassB_ge_const_mul_chiMass.md`) and is
   exactly what `u ∈ goodSet` buys (`λ₁(u) ≥ μ^{-1/3} ≫ R`);
6. **FS `eq:appgapestimate`** (FS l. 3965–3978): the `ε_T`-gap column pays every fixed multiple of
   `μ(a v)n₊` — **PROVED** as `Work.BoseFixB1.perBoxF_pieces.sbKin_ge_mu_av_cnPlus`, with the
   threshold arithmetic `Work.BoseFixB1.gapRegime_of_adm` and the *unconditional* gap branch
   `Work.BoseFixB1B.gapAtAll` (`Submission/Work/BoseFixB1B/gapAtAll.lean`);
7. **the sector decomposition**: the potentials/kinetic words and `nCountB` are diagonal in the
   occupancy sectors, and FS's `F` is convex (`eq:Rconvex`).  The corpus's pieces are
   `Work.FockBridge.{sectorSet, sectorPiece, sectorMass, sum_sectorPiece_sq,
   qLHSword_eq_sum_sectorPiece, cnPlusBoxInd_eq_sum_sectorPiece, sectorMass_sum,
   densityBridge_of_sectorMix, mixture_dlThreshold}` plus
   `Work.BoseFixB1B.{countDensityBridge, perBoxArithSum}` — the *downstream* half (from this
   residual to the frozen target) is already proved in `perBoxFWeight_of_sectorBoundG`.

**REFUTED FORM (read before using this residual).**  The residual as stated above — with the
`F`-weight read at the **smooth volume** `chiMass`, i.e. `psiWeight 1 μ ((k:ℝ)/chiMass)` — is
**FALSE**.  FS read `thm:smallbox` at `n/|B|` with `|B|` the **true box volume** `boxMass`, and
`chiMass/boxMass =: χ̂` tends to `0` on the slabs of the good set: the `M`-th-power face decay of
`chiSmall M` gives `χ̂ ≤ C_M(λ₁/(ℓd))^{2M} ≈ 10^{58}t^{31}` at `λ₁ = 2μ^{-1/3}`, so the
`chiMass`-form is `1/χ̂` times stronger wherever `χ̂ < 1`, while the words `tBwordBInd` (which
normalise by the true volume `boxMass`) are unchanged.  Verdicts and write-ups:
`FINDING_perBoxSectorBoundG_FALSE.md`, `FINDING_perSectorBoundG_FALSE.md`.  The same defect is
inherited by the `I₋`-chain `Work.BoseFixB1B.PerBoxSectorBound` /
`Work.BoseFixB1B.perBoxPointwise_of_sectorBound`.

**The shape of the repair.**  The reduction `perBoxFWeight_of_sectorBoundG` (this file's sibling in
`perBoxFWeight_holds.lean`) is *proved* and sound; it needs `F(t_smooth) ≤ K₀(F(s) + μ²)` with a
**uniform** `K₀`, where `s` is the residual's density argument.
* With `s = k/chiMass` the ratio `t_smooth/s = nCountB/k ≤ ν²` is uniform — but `s` itself is
  wrong, by the factor `1/χ̂` computed above.
* With `s = k/boxMass` the argument is right (it is FS's own, and it is what the words normalise
  by) but the ratio becomes `(nCountB/k)·(boxMass/chiMass) = typ(χ_B²)/avg(χ_B²)` — the **profile
  ratio**, bounded when the state is spread over the box but not when it sits at the peak of
  `χ_B`.  This is the same obstruction as `FINDING_wSmall1Pair_fibre_ge_chiB.md` and
  `DESIGN_chiB_proj_le_mix.md` §1: the corpus's `chiBump` is `Classical.choice`-opaque, so no
  profile statement is available.
Hence the sound route for the frozen target is the **direct re-run of FS `thm:smallbox` at the
*smooth* kernels** (`PERBOXF_ANALYSIS.md` §16 already concluded this).  What makes that re-run
localisable is *proved*: `Work.BoseFixB1.sbWordSectorAdditiveAdm`
(`tBwordBInd` + `qLHSwordB` are exactly the sector sum of the sector pieces) together with the
*exact partition* `∫Φ²F(t) = Σ_k ∫Φ_k²F(t)` (valid because `t = nCountB/chiMass` is a function of
the configuration alone, independent of `k`) — so a per-sector statement at the **smooth** density
with the **`½μ²`** background sums back to the frozen target *with the same `c₁` and `C`*, with no
bridge, no `K₀` and no sharp count.

**Hard-learned constraint (why the residual was stated sector-wise; it has cost five
delegations).**  FS `lm:appinteractionestimate`'s credit is `C·a(v)·(μ + n₀|B|⁻¹)·n₊` with
`n₀ = ΣᵢP_{B,i}` an **operator**; every *state-level* rendering that replaces it by the product
of first moments, `C·a(v)·(μ + S/V)·Q` with `S = boxFlatCount`, is **FALSE** — the missing
`⟨n₀n₊⟩ − ⟨n₀⟩⟨n₊⟩` is a positive variance, and the relaxation is only harmless after FS's
**group decomposition** (`n = m n' + n''`, `final_v2.tex` l. 3953–3990, `n' ∈ [C_nμ|B|,
(C_n+1)μ|B|)`), which produces the *scalar* bound `(n₀+1)/|B| ≲ μ` and hence the credit
`C aμ n₊` alone.  That grouping is available at a **fixed particle number** (i.e. on an occupancy
sector of `B(u)`, or on the `k`-particle boxes FS apply `thm:smallbox` to) and *not* for an
arbitrary state — which is why the three state-level targets `Work.BoseFixB1.boxQSum_ge_a0Main_add_A2`,
`Work.BoseFixB1.boxA2_add_spectral_ge_bogoliubovMain` and `Work.BoseFixB1.localised_lm_appbogolubov`
(all three `sorry`-carrying on disk) were each **declared FALSE** by their provers:
see `FINDING_boxQSum_rung4_FALSE` / `FINDING_lm_appbogolubov_localised_FALSE.md` /
`FINDING_localisedB_route8.md`.  **Do not attempt a state-level re-run of FS's chain.**

**Traps (already paid for by this chapter — do not repeat).**

* Any statement whose left side contains `(bFlat/bV − μ)²·bM1` is **quartic** in `Φ` while the
  rest is quadratic, hence FALSE (`Φ ≡ c`, `c → ∞`): see
  `FINDING_boxSquare_le_boxQSum_add_spectral.md`, `FINDING_perBoxMF_square_false.md`.  The
  residual above avoids this: its `F` is evaluated at the **count** `k/chiMass` (degree 0), so
  both sides are homogeneous of degree 2 (implicitly, per sector mass).
* The smooth count `nCountB/chiMass` and the sharp count `k/chiMass` differ by the fixed factor
  `ν²·chiMass/boxMass`-shaped; never identify them (that is `nCountB_le_sectorSet` +
  `psiWeight_le_mul_add`, both PROVED).
* The `F`-weight must NOT be replaced by the linear bound `F(t) ≤ μ(t+μ)`: at `t ≈ μ` the truth
  is `F = 0` and the linear bound misses by `2c` (`PERBOXF_ANALYSIS.md` §SESSION-3 FINDING).
* Parenthesise every big-operator body: `∑ i, f i + g i` does not bind `i` in the trailing term.
* `S² − S ≤ Pc` (`hcS2`) is load-bearing: without it the flat state with `S > 1` violates the
  `A₀`-step for every `C`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The sector (mixture) form of FS `thm:smallbox` at the sliding box `B(u)`, on the good set
`G`** — the single analytic residual of the frozen target `Work.BoseFixB1.perBoxFWeight_holds`.

This is `Work.BoseFixB1B.PerBoxSectorBound` with the hypothesis `u ∈ interiorSet ℓ d μ` weakened
to `u ∈ goodSet ℓ d μ` (the frozen statement's quantifier).  See the module docstring for the
reading of the objects. -/
def PerBoxSectorBoundG (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (R : ℝ) : Prop :=
  ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
          (∑ k ∈ Finset.range (n + 1),
              sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k *
                ((c * psiWeight 1 μ ((k : ℝ) / PBV v μ u) - (1 / 2 - c) * μ ^ 2)
                    * PBW h μ u
                  - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                      + μ * (_root_.BoseGases.a v))))
            ≤ Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ)

/-- **The `G`-form implies the `I₋`-form** (`I₋ = interiorSet ⊆ goodSet`): the `G`-form is the
strictly *stronger* assertion, so any `I₋`-restricted auxiliary result (in particular the proved
`Work.BoseFixB1B.perBoxPointwise_of_sectorBound`) is available to a prover of the `G`-form. -/
theorem perBoxSectorBound_of_G {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {R : ℝ} (hb : PerBoxSectorBoundG v h R) :
    PerBoxSectorBound v h R := by
  obtain ⟨ε₀, c, C, hε₀, hc0, hc14, hC0, hmain⟩ := hb
  refine ⟨ε₀, c, C, hε₀, hc0, hc14, hC0, fun μ hAdm n Φ u hu => ?_⟩
  exact hmain μ hAdm n Φ u (interiorSet_subset_goodSet hAdm.1 hu)

/-- **The sector masses sum to the box norm**, in the `G`-vocabulary (verbatim
`Work.BoseFixB1B.sectorMass_sum`; the statement is independent of the set of `u` considered). -/
theorem sectorMassG_sum {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : EuclideanSpace ℝ (Fin 3)) :
    ∑ k ∈ Finset.range (n + 1),
        sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
      = Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) :=
  sectorMass_sum Φ u

end Work.BoseFixB1B
