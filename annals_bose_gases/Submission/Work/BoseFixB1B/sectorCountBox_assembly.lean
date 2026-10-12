import ChallengeDeps
import Submission.Work.BoseFixB1.boxMass_pos_of_goodSet
import Submission.Work.BoseFixB1B.fsStepEFinalArith
import Submission.Work.BoseFixB1B.sbWord_descent_atSizes
import Submission.Work.BoseFixB1B.sectorCountBoxDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.sectorCountBox_assembly` — FS Step E's descent at the count

This module carries out the **`m ≥ 1` step of FS's descent** for
`Work.BoseFixB1B.SectorCountSmallboxBox` (`final_v2.tex` 3960–4050):

    boxLHS h c C μ n u ≤ sbWord h μ u Φ        (`c = 1/20`),

for an in-box, normalised `n`-particle state, from the two *group bounds* on the slice energies:

* `hB1` (the `m` groups of `n'` particles):  `(1/18)·μ·(N/|B|)·W·∫Ψ² ≤ sbWord_{N}(Ψ)` —
  FS's positive group bound (`e_B(n′,μ) ≥ (1/18)μ(n′/|B|)∬w_{1,B}`, obtained from their
  intermediate estimate `e_B(n′) ≥ ⅛(μ−n′/|B|)²∬w₁ − Cμa(n′/|B|)∫χ_B²` by choosing `C_n` large);
* `hB2` (the `n''` group): the *intermediate* count form
  `[¼(N/|B| − μ)²·W − ½μ²·W − C(μ²aΓ_B W + μa)]·∫Ψ² ≤ sbWord_N(Ψ)`.

Both are homogeneous in `∫Ψ²`, which is what makes the state-level descent work: the grouping
(`Work.BoseFixB1B.sbWord_slice_superadd_regime_holds`) bounds `sbWord_n(Φ)` by the slice integrals,
`Work.BoseFixB1B.sbWord_descent_grouped` iterates it to

    (m·g₁ + g₂)·∫Φ² ≤ sbWord_n(Φ),      g₁ = (1/18)μ(n′/V)W,  g₂ = ¼(n″/V−μ)²W − ½μ²W − C(…) ,

and `Work.BoseFixB1B.fsStepEFinalArith` is exactly FS's final line
`c((ρ−μ)²/(1+ρ/μ) + μ²) ≤ ¼(ρ″−μ)² + (1/18)μ(ρ−ρ″)` (with `c = 1/20`, `ρ′ ≥ 2μ`), i.e.
`boxLHS(n) ≤ m·g₁ + g₂`.

The remaining inputs of the target are therefore purely analytic and *small-n*: `hB1` and `hB2`
for `n ≤ 2C_nμ|B|` (plus the `m = 0` case, which needs the target itself at `n < C_nμ|B|`) — all
of them the same rung as FS `lm:appinteractionestimate` + `lm:appbogolubov` at the sliding box
(the Bogoliubov port).  See `FINDING_sectorCountBox_grouping_session.md`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.UBB Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **In-box support** of an `N`-particle state at the sliding box `B(u)`: a.e. all particles are
in `B(u)`.  This is the target's own `boxSupp` (`Submission.Work.BoseFixB1B.boxSupp`), in the
`PBB`-vocabulary. -/
def InBox (v : E3 → ℝ) (μ : ℝ) (u : E3) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ) : Prop :=
  ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N (PBℓ v μ))),
    Ψ x ≠ 0 → ∀ i : Fin N, x i ∈ PBB v μ u

/-- **The `m ≥ 1` step of FS's descent at the count.**  From the two group bounds `hB1`, `hB2`
(at the group sizes `n'`, `n''` of a decomposition `n = m·n' + n''`, `m ≥ 1`, `n'' < n'`,
`n'/|B| ≥ 2μ`), the target's inequality holds at `n` with `c = 1/20`. -/
theorem sectorCountBox_descent_step {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hR16 : R ≤ PBℓ v μ * PBd v μ / 16) (hRχ : R ≤ PBℓ v μ * Submission.BoseGases.chiR0)
    (u : E3) (hu : u ∈ goodSet (PBℓ v μ) (PBd v μ) μ) (C : ℝ)
    {n n' n'' m : ℕ} (hN : n = m * n' + n'') (hm : 1 ≤ m) (hn'' : n'' < n')
    (h2μ : 2 * μ ≤ (n' : ℝ) / PBBV v μ u)
    (hB1 : ∀ (Ψ : Submission.BoseGases.X n' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ → InBox v μ u Ψ →
      (1 / 18) * μ * ((n' : ℝ) / PBBV v μ u) * PBW h μ u
          * (∫ x in Submission.BoseGases.abox n' (PBℓ v μ), (Ψ x) ^ 2)
        ≤ Work.BoseFixB1.sbWord h μ u Ψ)
    (hB2 : ∀ (Ψ : Submission.BoseGases.X n'' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ → InBox v μ u Ψ →
      ((1 / 4) * (((n'' : ℝ) / PBBV v μ u) - μ) ^ 2 * PBW h μ u - (1 / 2) * μ ^ 2 * PBW h μ u
          - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
              + μ * (_root_.BoseGases.a v)))
          * (∫ x in Submission.BoseGases.abox n'' (PBℓ v μ), (Ψ x) ^ 2)
        ≤ Work.BoseFixB1.sbWord h μ u Ψ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hin : InBox v μ u Φ)
    (hnorm : (∫ x in Submission.BoseGases.abox n (PBℓ v μ), (Φ x) ^ 2) = 1) :
    boxLHS h (1 / 20) C μ n u ≤ Work.BoseFixB1.sbWord h μ u Φ := by
  subst hN
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hV : 0 < PBBV v μ u := by
    rw [PBBV]
    exact Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hW : 0 ≤ PBW h μ u :=
    Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓ hd u
  -- ## the iterated descent (the `m` groups of `n'` and the group of `n''`)
  have hdesc : ((m : ℝ) * ((1 / 18) * μ * ((n' : ℝ) / PBBV v μ u) * PBW h μ u)
        + ((1 / 4) * (((n'' : ℝ) / PBBV v μ u) - μ) ^ 2 * PBW h μ u
            - (1 / 2) * μ ^ 2 * PBW h μ u
            - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                + μ * (_root_.BoseGases.a v))))
        * (∫ x in Submission.BoseGases.abox (m * n' + n'') (PBℓ v μ), (Φ x) ^ 2)
      ≤ Work.BoseFixB1.sbWord h μ u Φ := by
    have key := Work.BoseFixB1B.sbWord_descent_atSizes h hv hv1 hvrad hR hv_supp hav hAdm
      hR16 hRχ u
      ((1 / 18) * μ * ((n' : ℝ) / PBBV v μ u) * PBW h μ u)
      ((1 / 4) * (((n'' : ℝ) / PBBV v μ u) - μ) ^ 2 * PBW h μ u
          - (1 / 2) * μ ^ 2 * PBW h μ u
          - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
              + μ * (_root_.BoseGases.a v)))
      hB1 hB2 hΦ hin
    exact key
  rw [hnorm, mul_one] at hdesc
  -- ## FS's final arithmetic
  have hρ''0 : 0 ≤ (n'' : ℝ) / PBBV v μ u := div_nonneg (Nat.cast_nonneg _) hV.le
  have hρ''ρ' : (n'' : ℝ) / PBBV v μ u < (n' : ℝ) / PBBV v μ u := by
    have hlt : (n'' : ℝ) < (n' : ℝ) := by exact_mod_cast hn''
    exact div_lt_div_of_pos_right hlt hV
  have hρ : ((m * n' + n'' : ℕ) : ℝ) / PBBV v μ u
      = (m : ℝ) * ((n' : ℝ) / PBBV v μ u) + (n'' : ℝ) / PBBV v μ u := by
    push_cast
    ring
  have harith := fsStepEFinalArith (μ := μ) (ρ := ((m * n' + n'' : ℕ) : ℝ) / PBBV v μ u)
    (ρ' := (n' : ℝ) / PBBV v μ u) (ρ'' := (n'' : ℝ) / PBBV v μ u) (c := 1 / 20) (m := m)
    hμ hm (by norm_num) (by norm_num) h2μ hρ''0 hρ''ρ' hρ
  -- ## assembly: `boxLHS(n) ≤ m·g₁ + g₂ ≤ sbWord`
  have hmn : (1 / 18) * μ * ((((m * n' + n'' : ℕ) : ℝ) / PBBV v μ u
        - (n'' : ℝ) / PBBV v μ u))
      = (m : ℝ) * ((1 / 18) * μ * ((n' : ℝ) / PBBV v μ u)) := by
    rw [hρ]; ring
  have hmain : boxLHS h (1 / 20) C μ (m * n' + n'') u
      ≤ (m : ℝ) * ((1 / 18) * μ * ((n' : ℝ) / PBBV v μ u) * PBW h μ u)
        + ((1 / 4) * (((n'' : ℝ) / PBBV v μ u) - μ) ^ 2 * PBW h μ u
            - (1 / 2) * μ ^ 2 * PBW h μ u
            - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                + μ * (_root_.BoseGases.a v))) := by
    have hL : boxLHS h (1 / 20) C μ (m * n' + n'') u
        = (1 / 20 * (((((m * n' + n'' : ℕ) : ℝ) / PBBV v μ u - μ) ^ 2
              / (1 + ((m * n' + n'' : ℕ) : ℝ) / PBBV v μ u / μ)) + μ ^ 2)) * PBW h μ u
          - (1 / 2) * μ ^ 2 * PBW h μ u
          - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
              + μ * (_root_.BoseGases.a v)) := by
      rw [boxLHS, psiWeight]
      ring
    rw [hL]
    have hmul := mul_le_mul_of_nonneg_right harith hW
    nlinarith [hmul, hmn]

  linarith [hmain, hdesc]

end Work.BoseFixB1B
