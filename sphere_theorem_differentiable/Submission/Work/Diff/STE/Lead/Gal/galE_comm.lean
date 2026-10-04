import Mathlib
import Submission.Work.Diff.STE.B3.ENormB_pair_J_commutator_v2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.Gal

/-- **The order-`k` Friedrichs adjointness of `D.J ρ ε`** (the "commutator (F)" of the STE design,
SESSION 10; the unique missing input of the a priori energy estimate
`Work.Diff.STE.Lead.Gal.galE_apriori`).

`D.ENormB_pair k` is the physical `Hᵏ` pairing of the localised chart components (`B3/Comp.lean`),
`D.J ρ ε` the chartwise Friedrichs mollifier, `k` the energy level.  Claim: `D.J ρ ε` is self-adjoint
for the `Hᵏ` pairing *up to an error losing exactly one derivative*:

`|E_k (J f) u − E_k f (J u)| ≤ C √(E_{k-1} f + E_0 f) · √(E_k u)`,

with `C` independent of `ε ∈ (0,1]` and of `f, u`.

PROOF ROUTE (settled; read the long headers of
`Submission/Work/Diff/STE/B3/ENormB_pair_J_commutator.lean` §1–§4 and of the `_v2` sibling, which
record the verified reduction and the traps):
the proved reduction `ENormB_pair_J_commutator_eq_BPair` turns the target into the *commutator
pairing* `|D.BPair ([Qk D k , D.J ρ ε] f) u| ≤ C √(D.ENormB (k-1) f + D.ENormB 0 f) √(D.ENormB k u)`
(`Qk D k` = the `k`-th power of the flat Laplacian lifted to sections, `B3/QkDef.lean`).
[That reduction asks for `C^∞` components of `D.J ρ ε f` and `Qk D k f`; derive them from the
component smoothness of `f` by the *span* picture `D.J ρ ε f = Σ_z c z • jSym D ε z`
(`J_eq_sum_index`, needing `hρ0` and `hε`) together with the proved component smoothness of the
family members, or via `Work.Diff.STE.Lead.R_J_contDiff`; alternatively redo the reduction with
`BPair_Rstar_of_integrable` + integrability.]  Then expand over the chart pairs `(i,j)` with
`L_{ij} = R i ∘ Rstar j` the chart transfer (`B3/bump_expansion_fixed.lean`, proved: the transfer is
`G · (u ∘ T)` with `G` smooth and `T` a smooth transition).  Two ingredient families:

1. **the flat Friedrichs gain.**  For `S_ε = trunc ρ ε` and a smooth compactly supported `c`, the
   multiplier of `[S_ε, M_c]` is `ĉ (m-n) · (ρ (ε m) − ρ (ε n))`; because `ρ` is *smooth* and
   *supported in `{|y|² ≤ 2}`*, `|ρ (ε m) − ρ (ε n)| ≤ min (2, ‖∇ρ‖ ε |m-n|)` jointly with the
   Peetre-type bound `ε ≤ √2 ⟨m-n⟩ / ⟨n⟩` whenever the difference is nonzero (use `|ε m| ≤ √2` and
   `⟨m⟩ ≤ ⟨m-n⟩ ⟨n⟩`).  Hence the kernel is `≤ C ⟨m-n⟩^N |ĉ (m-n)| / ⟨n⟩` uniformly in `ε ≤ 1`, and
   Schur's test gives the order `−1` gain.  Tools: `friedrichs_pointwise`, `CSq_trunc_sub_le`,
   `CSq_STruncC_sub`, `CSq_conv_le`, `CSq_period_comp_arg_le_of_isOpen`.
2. **the cross-chart transfer.**  `∂^l` commutes with the transfer up to order `l-1` (chain rule for
   `u ∘ T`, `CSq_period_deriv_comp_arg_le`); the *isometry defect* `(1 − |Dσ|^{2k})`-type terms that
   appear in the commutator are harmless in the *pairing*: they multiply the high-order factor of one
   side and are paired with the low-order norm of the other, which is exactly the required
   `√(E_{k-1} f + E_0 f) · √(E_k u)` distribution of the derivatives (do not try to bound the second
   half by `‖f‖_k ‖u‖_{k-1}`; move a derivative from the low-order factor to the high-order one, as
   in the design's "one integration by parts per multi-index" remark).

TRAPS: (i) the strong `L²` norm form of the commutator bound is FALSE — only the pairing form holds;
(ii) for merely bounded (non-smooth or non-supported) `ρ` the statement is FALSE — the hypotheses
`hρs` and `hρ0` are essential and are exactly those of the consumer `Lead/gal_uniform_v2`;
(iii) do not confuse `Qk D k h` with its component family. -/
theorem galE_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (k : ℕ) (hk : Module.finrank ℝ E < 2 * k) (hk1 : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ (f u : Work.Diff.STE.Bil (I := I) (M := M)),
          (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
            ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b)) →
          (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
            ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b)) →
          |D.ENormB_pair k (D.J ρ ε f) u - D.ENormB_pair k f (D.J ρ ε u)|
            ≤ C * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f) * Real.sqrt (D.ENormB k u) :=
  -- lead 2026-10-02: alias of the single owner H2731 (identical statement)
  Work.Diff.STE.B3.ENormB_pair_J_commutator_v2 (I := I) (M := M) D ρ hρ hρ0 hρs hρ1 k hk hk1

end Work.Diff.STE.Lead.Gal
