import Mathlib
import Submission.Diff.Interfaces
import Submission.Diff.ODE
import Submission.Work.Diff.ODE.flow_smooth
import Submission.Work.Diff.ODE.flow_smooth_icc
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.D.chartData_metric
import Submission.Work.Diff.STE.C2.ricci_of_deTurck
import Submission.Work.Diff.STE.Lead.J_norm_le
import Submission.Work.Diff.STE.Lead.J_tendsto
import Submission.Work.Diff.STE.Lead.gal_uniform_v2
import Submission.Work.Diff.STE.Lead.deTurck_limit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.

The full lead design is below and also in REFS/NOTES_LEAD_P1_STE.md. Follow its layers A–D; file Layer A pieces (pure torus Fourier lemmas, exact statements) in parallel right away, and C1/C2 in parallel with A/B.

# LEAD DESIGN: short-time existence (P1 linear/quasilinear parabolic theory + P2 DeTurck). Target ≤ 200K lines.

Contract: `ShortTimeExistence I M`. For every smooth metric g₀ there is T > 0 and a smooth Ricci flow G on [0,T) with G 0 = g₀.
Hypotheses available: LCSmooth, LCVariation. M is compact, T2 and boundaryless.

## Decision: Friedrichs-mollifier energy method, all analysis on the flat torus via Fourier series
Not Schauder, not a heat-kernel parametrix, not Galerkin eigenfunctions. Mathlib has multi-dimensional Fourier series on
`UnitAddTorus d` with Parseval (`mFourierCoeff`, `hasSum_sq_mFourierCoeff`, `hasSum_mFourier_series_apply_of_summable`),
Picard–Lindelöf in finite dimensions, and Arzelà–Ascoli. Every estimate below is a sum over ℤⁿ.
Why this works: the Ricci–DeTurck operator has SCALAR principal part g^{cd}∂_c∂_d acting on every component. So
L²/Hᵏ energy estimates close (Gårding with a scalar symbol), and a finite-rank mollifier J_ε turns the PDE into a
finite-dimensional ODE with ε-uniform estimates.
NOT NEEDED: Hölder spaces, Schauder estimates, heat kernels, spectral theory, Rellich on general domains, weak solutions,
boundary problems, uniqueness of Ricci flow.

## Layer A: torus toolkit (functions u : (Fin n → ℝ) → (Fin m → ℝ), C^∞ and 1-periodic in each coordinate)
Write û(k) for the Fourier coefficients (k ∈ ℤⁿ, via the unit cube or transfer to UnitAddTorus), ⟨k⟩² = 1 + Σ kᵢ²,
and ‖u‖ₛ² = Σ_k ⟨k⟩^{2s} |û(k)|² (s ∈ ℕ).
A1  (∂ᵢu)^(k) = 2πi kᵢ û(k); for smooth u, |û(k)| ≤ C_N ⟨k⟩^{−N} for all N (so every series converges).
A2  Parseval: ∫_{[0,1]ⁿ} |u|² = Σ |û|²; periodic integration by parts ∫ ∂ᵢf = 0.
A3  Equivalence: c‖u‖ₛ² ≤ Σ_{|α|≤s} ‖∂^α u‖²_{L²} ≤ C‖u‖ₛ².
A4  Sobolev: s > n/2 + j ⇒ sup |∂^α u| ≤ C‖u‖ₛ for |α| ≤ j. Proof: Cauchy–Schwarz with Σ⟨k⟩^{−2(s−j)} < ∞.
A5  Interpolation: ‖u‖ₛ² ≤ ‖u‖_{s−r} ‖u‖_{s+r} (Hölder on the Fourier side), and the tail bound Σ_{|k|>N} ≤ ⟨N⟩^{−2r}‖u‖²_{s+r}.
A6  Algebra: s > n/2 ⇒ ‖uv‖ₛ ≤ C‖u‖ₛ‖v‖ₛ (Peetre ⟨k⟩^s ≤ 2^s ⟨k−l⟩^s⟨l⟩^s plus Young on ℤⁿ).
A7  Moser (tame): ‖uv‖ₛ ≤ C(‖u‖_∞‖v‖ₛ + ‖u‖ₛ‖v‖_∞). Composition: for smooth Φ(x,y), ‖Φ(·,u)‖ₛ ≤ C(Φ, ‖u‖_∞)(1 + ‖u‖ₛ).
    Proof via Gagliardo–Nirenberg ‖∂^i u‖_{L^{2s/i}} ≤ C‖u‖_∞^{1−i/s} ‖u‖ₛ^{i/s}. Nirenberg's integration-by-parts proof works on the torus.
A8  Mollifier: ρ ∈ C_c^∞(ℝⁿ), even, 0 ≤ ρ ≤ 1, ρ = 1 on |ξ| ≤ 1, supp in |ξ| ≤ 2. S_ε u = Σ ρ(εk) û(k) e^{2πik·x}.
    Its range is FINITE-dimensional, it is self-adjoint in L², ‖S_ε u‖ₛ ≤ ‖u‖ₛ and ‖S_ε u − u‖ₛ ≤ Cε‖u‖_{s+1}.
    FRIEDRICHS: for smooth periodic a, ‖[a, S_ε] ∂ᵢ u‖ₛ ≤ C(a, s)‖u‖ₛ uniformly in ε ∈ (0,1].
    Proof: kernel (ρ(εk) − ρ(εl)) â(k−l) 2πi lᵢ. Where it is nonzero, min(ε|k|, ε|l|) ≤ 2, and |ρ(εk) − ρ(εl)| ≤ ε‖∇ρ‖∞|k−l|,
    so the kernel is bounded by C|k−l|²|â(k−l)|. Then Schur/Young on ℤⁿ with Peetre.
A9  Gårding for a scalar principal part: A(x) ∈ Sym(n) smooth periodic with A ≥ λ·I. For every multi-index α:
    ⟨∂^α(A^{cd}∂_c∂_d u), ∂^α u⟩_{L²} ≤ −λ‖∇∂^α u‖² + C(‖A‖_{C^{|α|+1}}) ‖u‖²_{|α|}·(1 + …).
    This is integration by parts plus the commutator [∂^α, A]. Also state the tame version (A7 on the coefficient).

## Layer B: sections on M (only Sym²T*M is needed; do it for this bundle)
B1  Atlas. A finite family (α = 1..N) of extended charts κ_α : U_α → (−1/4, 1/4)ⁿ, smooth θ_α with support in U_α,
    Σ θ_α² = 1, and a g̃-orthonormal frame on U_α (Gram–Schmidt of the coordinate frame). Here g̃ = g₀ is the background metric.
    This is the only place compactness is used.
B2  Components. R_α h := x ↦ θ_α·√μ_α·(h(e_a, e_b))_{ab} ∘ κ_α⁻¹, extended by 0 and periodised: a smooth periodic
    ℝ^{n×n}-valued function. μ_α is the g̃-volume density. R_α* is its L²(g̃)-adjoint (explicit formula). Σ_α R_α* R_α = id.
    ‖h‖ₖ² := Σ_α ‖R_α h‖ₖ². Transfer A4, A5, A6, A7 to M (charts overlap with smooth transition maps).
B3  J_ε := Σ_α R_α* S_ε R_α. It is self-adjoint in L²(M, g̃), satisfies 0 ≤ J_ε ≤ 1, has FINITE rank, and ‖J_ε h‖ₖ ≤ C‖h‖ₖ.
    For every first-order differential operator P with smooth coefficients, ‖[P, J_ε] h‖ₖ ≤ C‖h‖ₖ (from A8).
    Also J_ε h → h in H^{k−1}.

## Layer C: the DeTurck operator (P2, geometric)
C1  P(g) := −2 Ric(g) + L_{W(g)} g with W(g) = tr_g(∇^g − ∇^{g̃}), i.e. W^k = g^{ij}(Γ(g)^k_ij − Γ̃^k_ij).
    STRUCTURE LEMMA: in any chart, P(g)_ab = g^{cd} ∂_c∂_d g_ab + N_ab(x, g, ∂g), with N smooth on
    {g positive definite} × ℝ^{n³}. In the orthonormal-frame components R_α the same holds with a new smooth N.
    Proof: Ric_ab = −½ g^{cd}∂_c∂_d g_ab + ½(g_ac ∂_b Γ^c + g_bc ∂_a Γ^c) + (lower), with Γ^c = g^{pq}Γ^c_pq.
    The Lie-derivative term cancels the ∂Γ^c terms. See Topping's lecture notes ch. 5 / Chow–Knopf ch. 3 (Ricci–DeTurck).
C2  Pull-back. For a smooth DeTurck solution ĝ on [0,τ] with field W(t) = W(ĝ(t)), solve ∂ₜφ_t = −W(t)∘φ_t, φ₀ = id.
    This is a time-dependent ODE on compact M: global on [0,τ], φ_t diffeomorphisms, jointly smooth. The seeded library's
    ChartFlowJoint / ChartFlowVar has the smooth-dependence pattern.
    Then G(t) = φ_t* ĝ(t) satisfies ∂ₜG = −2 Ric(G), using naturality Ric(φ*g) = φ* Ric(g).
    Naturality of lcOf under diffeomorphisms is a lemma of its own (T-area style).

## Layer D: the quasilinear existence (P1 core)
D1  The ODE. With u₀ = g₀ (components) and ε fixed, solve u' = J_ε P(J_ε u), u(0) = u₀.
    Write u = u₀ + v with v in the finite-dimensional range of J_ε. Picard–Lindelöf applies while J_ε u stays positive definite.
D2  Uniform energy bound (k > n/2 + 3 fixed).
    d/dt ‖u‖ₖ² = 2⟨u, J P(J u)⟩ₖ = 2⟨J u, P(J u)⟩ₖ + (commutators, B3) ≤ −λ‖Ju‖²_{k+1} + C(‖u‖ₖ, λ⁻¹).
    Use A9 and A7. The good term absorbs everything. Hence there are τ, B > 0 depending only on ‖g₀‖ₖ and λ₀ = min eig(g₀),
    such that for every ε the solution exists on [0,τ] with ‖u‖ₖ ≤ B and J u ≥ λ₀/2. Ellipticity persists because
    ‖u(t) − u₀‖_{C⁰} ≤ C t (from ‖u'‖_{k−2} ≤ C and A4).
D3  Tame persistence. For k' > k: d/dt ‖u‖²_{k'} ≤ C(k', B)(1 + ‖u‖²_{k'}). So every Hᵏ' norm is bounded on the SAME [0,τ].
D4  Limit. The family is bounded in C([0,τ]; H^{k'}) for every k' and Lipschitz into H^{k'−2}.
    Uniqueness for the DeTurck system: the L² energy of the difference of two solutions obeys Grönwall.
    Hence u_ε converges as ε → 0 (compactness A5 + uniqueness, or a Cauchy estimate on differences).
    The limit ĝ is C^∞ in x, the equation gives C^∞ in t (∂ₜ^j expressed by x-derivatives), and ĝ(0) = g₀. It solves ∂ₜĝ = P(ĝ).
D5  Then C2 gives the Ricci flow. The within-[0,T) derivative at t = 0 is included in joint smoothness on Ico.

## Size estimate (lines)
A 30–50K; B 25–45K; C1 15–30K; C2 20–40K; D 40–70K. Total 130–235K, central ~180K. Risks:
- The bundle bookkeeping in B2 (tangent coordinate changes).
- Tame estimates (A7).
- ODE flows on M with smooth dependence (C2).
If A7 turns out too costly: prove D3 via the linear equation satisfied by ∂^α u (difference quotients on the torus).
-/

namespace Work.Diff.STE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **A Friedrichs profile on `ℝⁿ`**: a smooth function `ρ` with `‖ρ y‖ ≤ 1` for all `y`, `ρ 0 = 1`,
and `ρ y = 0` whenever `2 < ∑ i, (y i)^2`.

(We take `ρ` to be Mathlib's bump function centred at `0`, equal to `1` on the closed ball of radius
`√(2/max n 1)` and supported in the concentric open ball of twice that radius; the radius is chosen so
that the Euclidean condition `2 < ∑ yᵢ²` forces `‖y‖ ≥ rOut` — note that `‖·‖` on `Fin n → ℝ` is the
sup norm, so the bound `∑ yᵢ² ≤ n‖y‖²` is what converts one into the other.) -/
lemma exists_friedrichs_profile (n : ℕ) :
    ∃ ρ : (Fin n → ℝ) → ℝ, (∀ y, ‖ρ y‖ ≤ 1) ∧
      (∀ y, 2 < ∑ i, (y i) ^ 2 → ρ y = 0) ∧
      ContDiff ℝ ((⊤ : ℕ∞)) ρ ∧ ρ 0 = 1 := by
  classical
  have h2 : (0 : ℝ) < 2 / (max n 1 : ℝ) := by positivity
  set rOut : ℝ := Real.sqrt (2 / (max n 1 : ℝ)) with hrOut
  have hrOut_pos : 0 < rOut := Real.sqrt_pos.mpr h2
  have hrOut_sq : rOut ^ 2 = 2 / (max n 1 : ℝ) := Real.sq_sqrt h2.le
  set rIn : ℝ := rOut / 2 with hrIn
  have hrIn_pos : 0 < rIn := by positivity
  have hlt : rIn < rOut := by rw [hrIn]; linarith
  let B : ContDiffBump (0 : Fin n → ℝ) := ⟨rIn, rOut, hrIn_pos, hlt⟩
  refine ⟨fun y => B y, ?_, ?_, ContDiffBump.contDiff B, ?_⟩
  · intro y
    have h0 : 0 ≤ B y := ContDiffBump.nonneg' (f := B) y
    have h1 : B y ≤ 1 := ContDiffBump.le_one (f := B) (x := y)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  · intro y hy
    by_contra hne
    have hmem : y ∈ Function.support B := by
      rw [Function.mem_support]
      exact fun h => hne h
    rw [ContDiffBump.support_eq] at hmem
    rw [Metric.mem_ball, dist_zero_right] at hmem
    have hb : ∀ i : Fin n, (y i) ^ 2 ≤ ‖y‖ ^ 2 := by
      intro i
      have h1 : |y i| ≤ ‖y‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
      nlinarith [abs_nonneg (y i), sq_abs (y i), sq_nonneg (‖y‖), h1]
    have hsum : ∑ i, (y i) ^ 2 ≤ (n : ℝ) * ‖y‖ ^ 2 := by
      calc ∑ i : Fin n, (y i) ^ 2 ≤ ∑ _i : Fin n, ‖y‖ ^ 2 :=
            Finset.sum_le_sum fun i _ => hb i
        _ = (n : ℝ) * ‖y‖ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnsq : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
    have hnle : (n : ℝ) ≤ (max n 1 : ℝ) := by exact_mod_cast le_max_left n 1
    have hmax_pos : (0 : ℝ) < (max n 1 : ℝ) := by positivity
    have hsq : ‖y‖ ^ 2 < rOut ^ 2 := by nlinarith [norm_nonneg y, hmem]
    have hstep : (n : ℝ) * ‖y‖ ^ 2 < (max n 1 : ℝ) * rOut ^ 2 := by
      calc (n : ℝ) * ‖y‖ ^ 2 ≤ (max n 1 : ℝ) * ‖y‖ ^ 2 := by nlinarith
        _ < (max n 1 : ℝ) * rOut ^ 2 := mul_lt_mul_of_pos_left hsq hmax_pos
    rw [hrOut_sq] at hstep
    have hmax : (max n 1 : ℝ) * (2 / (max n 1 : ℝ)) = 2 := by
      field_simp
    rw [hmax] at hstep
    linarith
  · refine ContDiffBump.one_of_mem_closedBall (f := B) (x := 0) ?_
    exact Metric.mem_closedBall_self (x := (0 : Fin n → ℝ)) (ε := B.rIn) hrIn_pos.le

theorem short_time_existence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    ShortTimeExistence I M := by
  intro g₀
  -- ## 0. The Layer B3 data and the Friedrichs profile
  obtain ⟨ι₀, hι₀, hD⟩ := Work.Diff.STE.exists_B3Data (I := I) (M := M) hLC g₀
  letI : Fintype ι₀ := hι₀
  obtain ⟨D⟩ := hD
  obtain ⟨ρ, hρb, hρ0, hρs, hρ1⟩ := exists_friedrichs_profile (Module.finrank ℝ E)
  have hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner) :=
    Work.Diff.STE.D.chartData_metric (I := I) g₀
  -- ## 1. The two global properties of the Friedrichs mollifier (lead contracts)
  have hJN : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h :=
    fun k => Work.Diff.STE.Lead.J_norm_le (I := I) (M := M) D ρ hρb hρ0 hρs hρ1 k
  have hJT : ∀ (k : ℕ) (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h →
      Filter.Tendsto (fun ε => D.BNorm k (D.J ρ ε h - h))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    fun k h hh => Work.Diff.STE.Lead.J_tendsto (I := I) (M := M) D ρ hρb hρ0 hρs hρ1 k h hh
  -- ## 2. Uniform Galerkin existence on a common interval
  -- (`GalUniform` was corrected on 2026-10-02 to the small-`ε` form `∃ ε₀ > 0, ∀ ε ∈ (0,ε₀]`,
  -- because the `∀ ε ∈ (0,1]` form is false at `ε = 1`; the corrected statement is `gal_uniform_v2`.)
  have hGU : Submission.Diff.STEGal.GalUniform hLC D ρ :=
    Work.Diff.STE.Lead.gal_uniform_v2 (I := I) (M := M) D ρ hρb hρ0 hρs hρ1 hLC hg hJN hJT
  -- ## 3. The limit ε → 0: a DeTurck solution on `[0,τ]`
  obtain ⟨τ, hτ, G, hG0, hJoint, hWsm, heq⟩ :=
    Work.Diff.STE.Lead.deTurck_limit (I := I) (M := M) D ρ hρb hρ0 hρs hρ1 hLC hLV hg hJN hJT hGU
  -- ## 4. The DeTurck pull-back (Layer C2): a genuine Ricci flow
  -- `hFlow : SmoothFlowIcc I M` is the ODE contract, proved in
  -- `Submission/Work/Diff/ODE/flow_smooth_icc.lean` from the global contract `SmoothFlow` (proved in
  -- `Submission/Work/Diff/ODE/flow_smooth.lean`).
  obtain ⟨G', hG'flow, hG'0⟩ :=
    Work.Diff.STE.C2.ricci_of_deTurck (I := I) (M := M) hLC hLV
      (Work.Diff.ODE.flow_smooth_icc (I := I) (M := M)
        (Work.Diff.ODE.flow_smooth (I := I) (M := M)))
      G (fun t y => Work.Diff.STE.DeTurck.deTurckVec (G t) g₀ y) τ hτ hJoint hWsm heq
  exact ⟨τ, hτ, G', hG'flow, by rw [hG'0, hG0]⟩

end Work.Diff.STE
