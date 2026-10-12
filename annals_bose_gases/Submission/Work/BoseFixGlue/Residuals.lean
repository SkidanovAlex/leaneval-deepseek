import ChallengeDeps
import Submission.Work.BoseFixGlue.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Residuals` — the C-side inputs of the wiring

The wiring `Work.BoseFixGlue.HBoxGSymStateScaled_of_LHYBoxB` feeds FS's localisation comparison
`Work.BoseKinLoc.Compare.compare_box_energy_v2` with a state supported in the centred box
`abox N L` (`N` free, `ℓ(μ) ≤ L`).  That theorem takes five hypotheses beyond the state's
regularity (`hkin`, `hfib`, `hpot`, `hswap`, `hIBP`), and this module packages the four that
cannot be produced from `LHYBoxB` alone into a single named predicate

* `CompareInputs v h` — "the C-side inputs at FS's parameters, uniformly in small diluteness".

Its clauses, in the order of `compare_box_energy_v2`'s hypotheses, are

1. `kin`: the `N`-body kinetic localisation (FS `lem:LocKinEn` lifted to `N` particles) — from
   `Work.BoseKinLoc.KineticLocalisation` (= FS `lem:LocKinEn`, proved for some `c₀ > 0` in
   `Work.BoseKinLoc.Kinetic.kinetic_localisation`) through `Kinetic/fibre_lift.lean` /
   `Kinetic/fibre_lift_general.lean` (the `N`-body lifting);
2. `fibre`: the fibre/box bound (FS `thm:CompareBoxEnergy`'s `H_{Λ,u}(μ) ≥ E_Λ(μ)` on the
   symmetric sector) — BoseKinLoc's `Sector/fibre_bound_v3`, which is the *only* genuinely open
   clause, and whose `hEo`/`hEi` bounded-below inputs are supplied by `LHYBoxB`
   (`EΛ_lower_bound_of_LHYBoxB` in `Work.BoseFixGlue.EΛBound` gives `EΛ ≥ ℓ³Λ`;
   `hEo_of_LHYBoxB` / `hEi_of_LHYBoxB` give them in the exact form of the residual);
3. `swap`: joint `(u,x)`-integrability of `Φ²·potWordU` (the Fubini input of FS
   `lem:LocPotential`; see `Compare/FINDINGS.md` §2);
4. `pot`: the pointwise-in-`x` potential identity FS `lem:LocPotential`
   (`Work.BoseKinLoc.Pot.pot_average`, proved) — the clause records it in the form
   `compare_box_energy_v2` consumes.

`hvol` (the volume of the localisation region) and `hIBP` (the Green identity) are *not*
residuals: they are proved in the chapter (`Work.BoseKinLoc.Volume.volume_coverU` and
`Work.BoseFixGlue.green_identity`).
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixGlue

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The C-side inputs -/

/-- **The C-side inputs of FS's localisation comparison, at FS's parameters.**

There is `ε₀ > 0` such that for every admissible chemical potential `μ`
(`Adm v ε₀ μ`: `0 < μ`, `μ (a v)³ ≤ ε₀`, FS `sec:params`), every particle number `N`, every
box side `L ≥ ℓ(μ)` and every smooth symmetric state `Φ` supported in the centred box
`abox N L`, the four inputs of `compare_box_energy_v2` hold at the projected parameters
`ℓ(μ) = ℓB v μ`, `d = dB v μ`, `s = sB v μ`, `ε_T = eTB v μ`, `b = bB v μ`,
`g = g0 v h`, `μ = μ`:

* the kinetic lifting (`kin`),
* the fibre bound (`fibre`),
* the joint potential integrability (`swap`),
* FS `lem:LocPotential` (`pot`).

This is exactly `compare_box_energy_v2`'s hypothesis list (with `c₀` left to the caller), so
the wiring's job is: discharge the arithmetic, the translation to the centred box and the
final absorption; the four clauses above are the residual C-side content. -/
def CompareInputs (v : ℝ³ → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (N : ℕ) (L : ℝ), ℓB v μ ≤ L → ∀ Φ : X N → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) Φ → PermInvariant N Φ → tsupport Φ ⊆ abox N L →
        (∫ u : ℝ³, kinForm N (ℓB v μ) (dB v μ) (sB v μ) (eTB v μ) (bB v μ) u Φ)
          ≤ ∑ i : Fin N, ∫ x : X N, ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir N i k)) ^ 2
      ∧ (∀ u : ℝ³, min 0 (EΛ v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ))
              * (∫ x : X N, (Φ x) ^ 2)
            ≤ boxForm N v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) u Φ)
      ∧ Integrable (fun p : ℝ³ × X N =>
            (Φ p.2) ^ 2 * potWordU N v (g0 v h) (ℓB v μ) μ p.1 p.2)
      ∧ (∀ x : X N, (∫ u : ℝ³, potWordU N v (g0 v h) (ℓB v μ) μ u x)
            = -μ * (N : ℝ) * (∫ y : ℝ³, g0 v h y)
              + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2))

/-! ## 2. The individual clauses as separate predicates

They are the exact decomposition of `CompareInputs` offered to the provers of the C nodes. -/

/-- The kinetic lifting clause (FS `lem:LocKinEn` at `N` particles). -/
def KinInput (v : ℝ³ → ℝ) (ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ → ∀ (N : ℕ) (L : ℝ), ℓB v μ ≤ L → ∀ Φ : X N → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) Φ → PermInvariant N Φ → tsupport Φ ⊆ abox N L →
      (∫ u : ℝ³, kinForm N (ℓB v μ) (dB v μ) (sB v μ) (eTB v μ) (bB v μ) u Φ)
        ≤ ∑ i : Fin N, ∫ x : X N, ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir N i k)) ^ 2

/-- The fibre-bound clause (FS `thm:CompareBoxEnergy`'s `H_{Λ,u}(μ) ≥ E_Λ(μ)`). -/
def FibreInput (v : ℝ³ → ℝ) (h : ScatSol v) (ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ → ∀ (N : ℕ) (L : ℝ), ℓB v μ ≤ L → ∀ Φ : X N → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) Φ → PermInvariant N Φ → tsupport Φ ⊆ abox N L →
      ∀ u : ℝ³, min 0 (EΛ v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ))
            * (∫ x : X N, (Φ x) ^ 2)
          ≤ boxForm N v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) u Φ

/-- The joint `(u,x)`-integrability clause (the Fubini input of FS `lem:LocPotential`). -/
def SwapInput (v : ℝ³ → ℝ) (h : ScatSol v) (ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ → ∀ (N : ℕ) (L : ℝ), ℓB v μ ≤ L → ∀ Φ : X N → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) Φ → PermInvariant N Φ → tsupport Φ ⊆ abox N L →
      Integrable (fun p : ℝ³ × X N =>
        (Φ p.2) ^ 2 * potWordU N v (g0 v h) (ℓB v μ) μ p.1 p.2)

/-- FS `lem:LocPotential` (pointwise in the configuration). -/
def PotInput (v : ℝ³ → ℝ) (h : ScatSol v) (ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ → ∀ (N : ℕ) (L : ℝ), ℓB v μ ≤ L → ∀ Φ : X N → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) Φ → PermInvariant N Φ → tsupport Φ ⊆ abox N L →
      ∀ x : X N, (∫ u : ℝ³, potWordU N v (g0 v h) (ℓB v μ) μ u x)
        = -μ * (N : ℝ) * (∫ y : ℝ³, g0 v h y)
          + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)

/-- `CompareInputs` decomposes into its four clauses. -/
theorem compareInputs_of_parts {v : ℝ³ → ℝ} {h : ScatSol v} {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hkin : KinInput v ε₀) (hfib : FibreInput v h ε₀) (hswap : SwapInput v h ε₀)
    (hpot : PotInput v h ε₀) : CompareInputs v h :=
  ⟨ε₀, hε₀, fun μ hμ N L hL Φ hΦ hsym hsupp =>
    ⟨hkin μ hμ N L hL Φ hΦ hsym hsupp, hfib μ hμ N L hL Φ hΦ hsym hsupp,
      hswap μ hμ N L hL Φ hΦ hsym hsupp, hpot μ hμ N L hL Φ hΦ hsym hsupp⟩⟩

/-! ## 3. The four clauses of `CompareInputs` at a *smaller* threshold

Monotonicity in `ε₀` (only used to combine the individual children's thresholds). -/

lemma KinInput.mono {v : ℝ³ → ℝ} {ε ε' : ℝ} (h : KinInput v ε) (hle : ε' ≤ ε) : KinInput v ε' :=
  fun μ hμ => h μ ⟨hμ.1, le_trans hμ.2.1 hle, hμ.2.2⟩

lemma FibreInput.mono {v : ℝ³ → ℝ} {h : ScatSol v} {ε ε' : ℝ} (hf : FibreInput v h ε)
    (hle : ε' ≤ ε) : FibreInput v h ε' :=
  fun μ hμ => hf μ ⟨hμ.1, le_trans hμ.2.1 hle, hμ.2.2⟩

lemma SwapInput.mono {v : ℝ³ → ℝ} {h : ScatSol v} {ε ε' : ℝ} (hs : SwapInput v h ε)
    (hle : ε' ≤ ε) : SwapInput v h ε' :=
  fun μ hμ => hs μ ⟨hμ.1, le_trans hμ.2.1 hle, hμ.2.2⟩

lemma PotInput.mono {v : ℝ³ → ℝ} {h : ScatSol v} {ε ε' : ℝ} (hp : PotInput v h ε)
    (hle : ε' ≤ ε) : PotInput v h ε' :=
  fun μ hμ => hp μ ⟨hμ.1, le_trans hμ.2.1 hle, hμ.2.2⟩

end Work.BoseFixGlue
