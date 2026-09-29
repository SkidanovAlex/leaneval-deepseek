import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.RedProj.Basic
import Submission.Work.TMComp.RedProj.FourierAux
import Submission.Work.TMComp.RedProj.ClaimA
import Submission.Work.TMComp.RedProj.ClaimB
import Submission.Work.TMComp.RedProj.Extract
import Submission.Work.TMComp.RedProj.KEnum
import Submission.Work.TMComp.RedProj.Part1
import Submission.Work.TMComp.RedProj.part2_compact
import Submission.Work.TMComp.RedProj.differentiableOn_intervalIntegral_kernel
import Submission.Work.TMComp.RedProj.coboundary_of_conjugacy
import Submission.Work.TMComp.prove_RealCartan
import Submission.Work.TMComp.RedProj.mAnalytic_assembly
import Submission.Work.TMComp.RedC8.prove_Kotani
import Submission.Work.TMComp.RedC7T.dioph_consumers
import Submission.Work.TMComp.RedC7T.mAnalytic_dioph
import Submission.Work.TMC7Core.Bridge.P_BJ_transfer
import Submission.Work.TMComp.RedC7T.dbj_dioph_final

/-! Guidance from the project lead (the requester):

Component C11 (P_Reducibility) of the Ten Martini formalisation. The FROZEN statement is Work.TMContract.P_Reducibility (Submission/Work/TMContract/Components.lean; definitions in TMContract/Defs.lean; read TMContract/README.md). The proof route for C11 is in Submission/Work/TMPlan/ROUTE_LEAD.md (find the section for C11); the source is Avila–Jitomirskaya, The Ten Martini Problem (arXiv math/0503363), plus the references ROUTE_LEAD cites. Any other component's P_* that ROUTE_LEAD lists as an input for C11 may be taken as a HYPOTHESIS inside your proof only if P_Reducibility's own statement takes it; otherwise prove what you need. Decompose into lemmas right away and dispatch them in parallel with request_lemma (request_review first if unsure a statement is true). Keep every build small; no hour-long files.
-/

/-!
# C11 (`P_Reducibility`) — assembly — **COMPLETE**

The frozen component C11 (`Work.TMComp.prove_Reducibility`) is proved, with `#print axioms = [propext, Classical.choice, Quot.sound]`; the import closure of
this module contains no incomplete proof.

## Final wiring

The frozen statement is obtained from the rational tower `S1` alone:

```
prove_Reducibility = prove_Reducibility_of_RatTowerLower RedC7T.ratTowerLower
```

via the **Diophantine case of C7**, `RedC7T.D_BJ_dioph_uncond` (in
`Submission/Work/TMComp/RedC7T/dbj_dioph_final.lean`):

* `S1` is `RedC7T.RatTowerLower`, the finite rational tower, instantiated from its proved
  instance `Work.TMComp.C7Aux.TowerV3.rat_tower_lower_v3`
  (`Submission/Work/TMComp/C7Aux/Fresh/RTLv3.lean`; statement verified identical in the
  scratch check that used to live in `RedC7T/`).
* `RedC7T.D_BJ_dioph` (`RedC7T/pbj_dioph.lean`) is my Case II (Diophantine) assembly of C7:
  continued-fraction chain (`Scale.conv_chain_rational`, which takes the given `DiophBelow`
  constant), `Scale.base_pairing_bd` (the frozen base scale with level and pairing),
  `Scale.persists_level_pairing`, `Scale.spectral_continuity`, `Scale.psi_upper`,
  `Scale.lyapAvg_lipschitz` (the crude *fixed-scale* transfer) and `Solutions.rat_bound`, with
  the single non-elementary input `S1` (the tower) and no Liouville case.
* `C8` is `RedC8.prove_Kotani` (my independent fork, in `RedC8/`);
  `C9` at Diophantine frequencies is `RedC7T.mAnalytic_dioph` with the `_dioph` consumers
  (`RedC7T/dioph_consumers.lean`); `C10` is `prove_RealCartan`; the elementary components used
  inside `D_BJ_dioph` are `prove_OpBasics`, `prove_LEBasics`, `prove_Schnol`.

Everything else in this file (`part2_of`, `prove_Reducibility_of*`, the `RedProj/*` machinery)
is unchanged; the alternative wirings through `P_BJ` (`prove_BJ`,
`Work.TMC7Core.P_BJ`) are kept as fallbacks. -/

/-!
# C11 (`P_Reducibility`) — assembly (history)

## Session update (2026-09-29, evening): C7 route redirected by the lead — stand down

The project lead redirected component C7 (`Submission/Work/TMC7Core/C7_INPUTS_LEAD.md`): the
former target of the C7 chain, `TMC7Core.Scale.p_bj_of_inputs` (`Scale/pbj_assembly.lean`,
axiom-clean), needs two inputs (`Scale.alpha_lipschitz`, `Scale.E_uniform`) which are not
elementary — and the quantitative convergence rate on which `E_uniform` rested
(`Scale.excess_rate`, `Scale/amo_excess_bound`) is **false** (disproof in `C7_INPUTS_LEAD.md`
§1.1: at `λ = 1/2`, `α₀ = 0`, `E₀ = 3`, `rat_bound` + `spectral_continuity` + the crude
Lipschitz bound contradict any rate uniform in `α` near a rational, because `α ↦ L(α,E)` is
discontinuous at rationals).  A joint Lipschitz bound of the form
`|L_N(α,E) - L_N(α',E')| ≤ C₁N|α-α'| + C₂|E-E'|` was explored here (and delegated); the lead
has retired that route as well: `P(ω,E,N) := 2L_{2N} - L_N`, `ψ := L - P`, and the C7 owner is
now proving the **dichotomy** `Work.TMC7Core.p_bj_of_dichotomy` from six elementary lemmas
S0–S6 (Case I: Liouville closeness `|α - a/q| < e^{-b*q}` at scale `N₀ ≍ q`, where the crude
exponential `lyapAvg_lipschitz` constant suffices; Case II: the Diophantine case, whose
rational side needs a *finite* avalanche tower at the rational frequency closed by
`Scale/rat_excess_rate_explicit`).

**Two extra lemmas in this file make the closure robust** (neither is a `P_BJ` provider —
both *consume* existing inputs):

* `prove_Reducibility_of_TMC7Core_P_BJ : Work.TMC7Core.P_BJ → P_Reducibility` — one application
  of the already-proved bridge `Work.TMC7Core.Bridge.P_BJ_transfer` plus the Diophantine route;
  use it if the C7 owner lands `Work.TMC7Core.p_bj_of_dichotomy` but has not (yet) updated the
  frozen component file;
* `prove_Reducibility_of_D_BJ_dioph` (from an earlier session) — the Diophantine case suffices.

**Therefore this file is wired, as requested, to the single component stub
`Work.TMComp.prove_BJ`** (`Submission/Work/TMComp/prove_BJ.lean`), which the C7 owner will
discharge.  That stub is no longer needed for this file: see `prove_Reducibility_of_RatTowerLower`
that stub (`python3 _stat_red.py Submission.Work.TMComp.prove_Reducibility`).

## C9 via a fork (`RedProj/aks_section.lean` + `RedProj/mAnalytic_assembly.lean`)

`Work.TMComp.RedProj.mAnalytic_of_BJ_Kotani : P_BJ → P_Kotani → P_mAnalytic` is a verbatim
fork of C9's assembly (`Submission/Work/TMComp/prove_mAnalytic.lean`) in the namespace
`Work.TMComp.RedProj`, whose only difference is that the three analytic inputs
`MAnalytic` still owes are replaced by their copies proved in `Submission/Work/RedProj/`:

| `MAnalytic` (C9's chain) | proved copy (`Submission/Work/RedProj/`) |
|---|---|
| `amoM_strip_cayley` | `Work.RedProj.amoM_cayley_strip` |
| `propagate_smallness` | `Work.RedProj.growth_propagation` |
| `separately_holomorphic_real_analytic` | `Work.RedProj.separately_holomorphic_analytic` |

(plus the equivariance/analyticity lemmas `Work.RedProj.polarK_*` used by the polar-factor
route).  All of them are axiom-clean, so the fork removes C9's file from the closure
altogether.  If C9's own file is completed first, the equivalent wiring

```lean
  prove_Reducibility_of_mAnalytic Work.TMComp.prove_mAnalytic
```

may be used instead and the fork dropped; the statements of the two versions of C9 are
identical (verified with `#check`).
-/

open MeasureTheory Filter Topology Set

set_option autoImplicit false

noncomputable section

namespace Work.TMComp

open Work.TMContract

theorem prove_Reducibility : Work.TMContract.P_Reducibility := by
  exact RedProj.prove_Reducibility_of_dioph
    RedProj.differentiableOn_intervalIntegral_kernel
    (fun α hα φ hφc hφp O c hO hper hdet hconj =>
      RedProj.coboundary_of_conjugacy α hα φ hφc hφp O c hO hper hdet hconj)
    (RedC7T.mAnalytic_dioph RedC7T.D_BJ_dioph_uncond RedC8.prove_Kotani)
    prove_RealCartan

/-- Part 2 of `P_Reducibility`: the compact dichotomy of `RedProj.part2_compact` on all of
`(a,b)`. -/
theorem part2_of
    (hhol : ∀ (F : ℂ × ℂ → ℂ) (Δ : Set ℂ) (ρ : ℝ), IsOpen Δ → 0 < ρ →
      DifferentiableOn ℂ F {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ} → ∀ k : ℤ,
      DifferentiableOn ℂ (fun z : ℂ => ∫ x in (0 : ℝ)..1,
        F (z, (x : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))) Δ)
    (hcob : ∀ (α : ℝ), Irrational α → ∀ (φ : ℝ → ℝ), Continuous φ →
      (∀ x, φ (x + 1) = φ x) → ∀ (O : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ) →
      (∀ x, O (x + 1) = O x) → (∀ x, (O x).det = 1) →
      (∀ x, O (x + α) * rot (φ x) = rot c * O x) →
      ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
        ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x)
    (h9 : P_mAnalytic) (h10 : P_RealCartan) :
    ∀ (α b₀ : ℝ), Irrational α → DiophBelow α b₀ → ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      ∀ a b : ℝ, a < b → Set.Ioo a b ⊆ amoSpec α lam →
        volume (RedSet α lam ∩ Set.Ioo a b) = 0 ∨
          ∃ c d : ℝ, c < d ∧ Set.Ioo c d ⊆ RedSet α lam ∩ Set.Ioo a b := by
  intro α b₀ hα hD lam h0 h1 a b hab hspec
  by_cases hcase : ∃ c d : ℝ, a < c ∧ c ≤ d ∧ d < b ∧
      (∃ c' d' : ℝ, c' < d' ∧ Set.Ioo c' d' ⊆ RedSet α lam ∩ Set.Ioo a b)
  · refine Or.inr ?_
    obtain ⟨c, d, _, _, _, c', d', hlt, hsub⟩ := hcase
    exact ⟨c', d', hlt, hsub⟩
  · refine Or.inl ?_
    refine RedProj.volume_eq_zero_of_compact_null (RedSet α lam) a b hab ?_
    intro c d hac hcd hdb
    rcases RedProj.part2_compact hhol hcob h9 h10 α b₀ lam hα hD h0 h1 a b hab hspec
      c d hac hcd hdb with h | ⟨c', d', hlt, hsub⟩
    · exact h
    · exact absurd ⟨c, d, hac, hcd, hdb, ⟨c', d', hlt, hsub⟩⟩ hcase

/-- `P_Reducibility` from its two inputs and the two isolated analytic facts. -/
theorem prove_Reducibility_of
    (hhol : ∀ (F : ℂ × ℂ → ℂ) (Δ : Set ℂ) (ρ : ℝ), IsOpen Δ → 0 < ρ →
      DifferentiableOn ℂ F {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ} → ∀ k : ℤ,
      DifferentiableOn ℂ (fun z : ℂ => ∫ x in (0 : ℝ)..1,
        F (z, (x : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))) Δ)
    (hcob : ∀ (α : ℝ), Irrational α → ∀ (φ : ℝ → ℝ), Continuous φ →
      (∀ x, φ (x + 1) = φ x) → ∀ (O : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ) →
      (∀ x, O (x + 1) = O x) → (∀ x, (O x).det = 1) →
      (∀ x, O (x + α) * rot (φ x) = rot c * O x) →
      ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
        ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x)
    (h9 : P_mAnalytic) (h10 : P_RealCartan) : P_Reducibility :=
  ⟨fun α hα hD => RedProj.reducible_of_dioph_all h9 α hα hD,
    part2_of hhol hcob h9 h10⟩

/-- `P_Reducibility` from its two component inputs and AJ Lemma 4.1 (1) ⇒ (2); the
holomorphy of tube parameter integrals is supplied by
`RedProj.differentiableOn_intervalIntegral_kernel`. -/
theorem prove_Reducibility_of_hcob
    (hcob : ∀ (α : ℝ), Irrational α → ∀ (φ : ℝ → ℝ), Continuous φ →
      (∀ x, φ (x + 1) = φ x) → ∀ (O : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ) →
      (∀ x, O (x + 1) = O x) → (∀ x, (O x).det = 1) →
      (∀ x, O (x + α) * rot (φ x) = rot c * O x) →
      ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
        ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x)
    (h9 : P_mAnalytic) (h10 : P_RealCartan) : P_Reducibility :=
  prove_Reducibility_of RedProj.differentiableOn_intervalIntegral_kernel hcob h9 h10

/-- `P_Reducibility` from the two component inputs `C9` and `C10`: all of C11's own
machinery is now in place (Claim A, Claim B, part 1, the compact part 2, the two analytic
lemmas). -/
theorem prove_Reducibility_of_components (h9 : P_mAnalytic) (h10 : P_RealCartan) :
    P_Reducibility :=
  prove_Reducibility_of RedProj.differentiableOn_intervalIntegral_kernel
    (fun α hα φ hφc hφp O c hO hper hdet hconj =>
      RedProj.coboundary_of_conjugacy α hα φ hφc hφp O c hO hper hdet hconj)
    h9 h10

/-- `P_Reducibility` from component C9 alone: component C10 (`P_RealCartan`) is proved in
`Submission.Work.TMComp.prove_RealCartan`. -/
theorem prove_Reducibility_of_mAnalytic (h9 : P_mAnalytic) : P_Reducibility :=
  prove_Reducibility_of_components h9 prove_RealCartan

/-- `P_Reducibility` from the **Diophantine** case of C7 alone.

The consumer files `RedC7T/dioph_consumers.lean` re-prove `RedProj/Part1.lean` and
`RedProj/part2_compact.lean` with C9 restricted to frequencies satisfying `DiophBelow α b₀`
for some `b₀ > 0` (which is what `P_Reducibility`'s two conjuncts actually assume), and
`RedC7T.mAnalytic_dioph` supplies that restricted C9 from the Diophantine case of `P_BJ` and
Kotani.  So C11 follows from `D_BJ_dioph`:

`∀ α lam b₀, Irrational α → 0 < b₀ → DiophBelow α b₀ → lam ≠ 0 → ∀ E ∈ amoSpec α lam,
  lyap α lam (E : ℂ) = max 0 (Real.log |lam|)`.

Instantiating it with the component `prove_BJ` gives the same closure as
before, but the remaining obligation is now only the Diophantine case of C7. -/
theorem prove_Reducibility_of_D_BJ_dioph
    (hD : ∀ (α lam : ℝ) (b₀ : ℝ), Irrational α → 0 < b₀ → DiophBelow α b₀ → lam ≠ 0 →
      ∀ E ∈ amoSpec α lam, lyap α lam (E : ℂ) = max 0 (Real.log |lam|)) :
    P_Reducibility :=
  RedProj.prove_Reducibility_of_dioph
    RedProj.differentiableOn_intervalIntegral_kernel
    (fun α hα φ hφc hφp O c hO hper hdet hconj =>
      RedProj.coboundary_of_conjugacy α hα φ hφc hφp O c hO hper hdet hconj)
    (RedC7T.mAnalytic_dioph hD RedC8.prove_Kotani)
    prove_RealCartan


/-- **`P_Reducibility` from the rational tower `S1` alone** (the finite rational tower of the
lead's C7 design, `RedC7T.RatTowerLower`), through the *Diophantine* case of C7 proved in
`RedC7T.D_BJ_dioph`.

Its inputs are

* `S1` (`RedC7T.RatTowerLower`, statementally identical to `Work.TMC7Core.Scale.rat_tower_lower`
  and `Work.TMComp.C7Aux.rat_tower_lower`), the finite rational tower at a rational frequency;
* C8 `P_Kotani` -- `RedC8.prove_Kotani` (proved here);
* C9 restricted to Diophantine frequencies -- `RedC7T.mAnalytic_dioph` with the `_dioph`
  consumers of `RedC7T/dioph_consumers.lean`;
* C10 `P_RealCartan` -- `prove_RealCartan` (proved here);
* the elementary components `prove_OpBasics`, `prove_LEBasics`, `prove_Schnol` (proved in the
  tree), used inside `RedC7T.D_BJ_dioph`.

No use is made of `Work.TMC7Core.P_BJ` or of any non-Diophantine (Liouville) case of C7. -/
theorem prove_Reducibility_of_RatTowerLower (hS1 : RedC7T.RatTowerLower) : P_Reducibility :=
  prove_Reducibility_of_D_BJ_dioph (RedC7T.D_BJ_dioph hS1)


end Work.TMComp
