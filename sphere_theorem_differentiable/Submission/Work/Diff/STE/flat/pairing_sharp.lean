/-
# The sharp-level reduction of `Work.Diff.STE.flat.energy_apriori`

This file isolates the *only* missing analytic input of the a priori estimate
`Work.Diff.STE.flat.energy_apriori` (file `…/flat/energy_apriori.lean`) and proves the reduction of
the target from it.

## The structure of the proof

* `energy_deriv_local` (proved, `…/flat/energy_deriv_local.lean`) computes the time derivative of
  the energy `σ ↦ ENormSqFull k (seriesFunM (c σ))` along a box-supported Galerkin trajectory as
  the *static* pairing
  `2 * Σ_{i,j} (Σ_{l : Fin k → Fin n} L2re (∂^l (Φ ∘ jet)) (∂^l u) + L2re (Φ ∘ jet) (u))`
  evaluated at the current time (`u = seriesFunM (c t)`, `Φ ∘ jet = fun x => Φ (x, jetM u x)`).
  It needs only the box support (finiteness), the smoothness/periodicity of the nonlinearity along
  the current slice and the Fourier-coefficient form of the ODE.
* `gronwall_Ico` (proved, in `energy_apriori.lean`) turns a differential inequality
  `deriv E ≤ C * (1 + E)` on `Ico 0 T` into the exponential bound of the target.

What is *not* yet available is the sharp static estimate `PairingBoundSharp` below: under the
hypothesis `ENormSqFull k u ≤ B²` (with the sharp threshold `n + 4 < 2k`) the pairing is bounded by
a constant (depending only on `n, k, Φ, lam, B` -- uniformly in the Galerkin order `N` and in the
trajectory).  Once that is proved, `energy_apriori` is
`energy_apriori_of_pairing_sharp … (pairing_bound_sharp …)`.

## Why the *constant* form is the right interface

The hypothesis `ENormSqFull k (seriesFunM (c t)) ≤ B²` is available at *every* time of the
trajectory, so every term of the pairing whose every factor is priced at a level `≤ k` is bounded
by a constant, and only factors priced at level `k+1` (the one derivative produced by integrating
the principal part by parts) must be absorbed against the Gårding dissipation
`-λ' * ENormSqM (k+1) u`.  This is why the sharp threshold is exactly `n+4 < 2k` (i.e.
`k > n/2 + 2`): it is what makes the Hölder exponent allocation feasible for the commutator and
Faà di Bruno terms of the pairing.

## The proof plan for `PairingBoundSharp` (the remaining gap)

Write `u = seriesFunM c` and use `Work.Diff.STE.flat.Phi_decomp_smooth` (the ellipticity gives
`det (reMat (u x)) ≠ 0`, so the DeTurck decomposition applies pointwise):

  `Φ (x, jetM u x) = Σ_{ab} symInvC c a b x * ∂_a∂_b u x + Nfun (x, jetP c x)`.

Then `pairSharp = P_gard + P_comm + P_N + P_zero`:

* **`P_gard`** — the `a = 0` part of the Leibniz expansion of `∂^l (symInvC * ∂_a∂_b u)`, i.e.
  `Σ_{ab} Σ_{|l| = k} L2re ((symInvC c a b) * ∂_a∂_b (∂^l u_ij)) (∂^l u_ij)`.  This is exactly
  the shape of the proved `Work.Diff.STE.flat.garding_vec_const`, which needs only the *first*
  derivative bound `|pdR i (symInvR c a b)| ≤ K₁` besides smoothness, periodicity, symmetry and the
  ellipticity of the symmetrised inverse metric (the four facts at the sharp level are the delegated
  `Work.Diff.STE.flat.symInv_garding_bounds`).  It yields
  `P_gard ≤ -(λ'/2) ENormSqM (k+1) u + C ENormSqM k u ≤ -(λ'/2) ENormSqM (k+1) u + C'`.
* **`P_comm`** — the rest of the Leibniz expansion (`pdList_mul_sub`, `commutator_defs.splits`):
  terms `(∂^a F) * (∂^{k-a+2} u)` paired with `∂^k u`, `1 ≤ a ≤ k`, `F = symInvC c a' b'`.
  Bound each by the *two-factor* Hölder with real exponents `α = 1/(2p)`, `β = 1/(2q)`,
  `α + β = 1/2`: the coefficient factor in `L^{2p}` (price `a + n/2 - nα + 1 ≤ k`, delegated
  `Work.Diff.STE.flat.symInv_deriv_Lp_bound`, hence a *constant*) times the `u`-factor in `L^{2q}`
  (price `(k-a+2) + n/2 - nβ ≤ k+1`, from the sharp Sobolev
  `Work.Diff.STE.flat.Sobolev.rnorm_seriesFun_rpow_le` plus the weight trading
  `CSq s (pdList q F) ≤ C CSq (s+|q|) F` and `CSq_le_ENormSq`), so at most a constant times
  `√(1 + ENormSqM (k+1) u)`; then `√(1+E_{k+1}) ≤ ε E_{k+1} + C_ε`, and `∂^l u` is bounded by `B`.
  Such exponents exist because `max(0, (a+n/2+1-k)/n) ≤ (a-1)/n` is equivalent to `n/2 + 2 ≤ k`,
  which is the hypothesis `Fintype.card (Fin n) + 4 < 2 k`.  Endpoints: `a = k` is the case `p = 1`
  (`L²` for the coefficient, price exactly `k`), `a = 1` the case `q = 1` together with the sup
  bound `|pdR i (symInvR)| ≤ C`.
* **`P_N`** — `Σ_{ij} Σ_l L2re (∂^l (Nfun (·, jetP c ·))_ij) (∂^l u_ij)`, bounded by
  Cauchy–Schwarz in `l` as `Σ_{ij} √(ENormSq k (N_ij)) * √(ENormSq k u_ij)`
  `≤ n² B √(C (1 + ENormSqM (k+1) u))`, using the delegated
  `Work.Diff.STE.flat.Nfun_CSq_level_bound` (composition with the *sup bounded* vector `(u, ∂u)`,
  which is why the level `k+1` appears) plus `ENormSq_seriesFun_le`; absorb the square root.
* **`P_zero`** — `Σ_{ij} |L2re (Φ (·, jetM u ·)_ij) (u_ij)| ≤ n² sup‖Φ (·, jetM u ·)‖ √(E_0)`, a
  constant: the principal part via `sup |symInvC| * ‖∂_a∂_b u‖_{L²}` with
  `ENormSq 2 u ≤ C CSq 2 c ≤ C CSq k c ≤ C (1+E_k)`, the lower order part via `sup |Nfun|`.

The finitely many absorbed terms are summed with a common `ε` along the finitely many exponents
`α`, and the four estimates are added; `λ'/8` of dissipation remains, so `pairSharp ≤ C`.  All
constants are uniform in `N` and `c` because the box support makes `seriesFunM c` a *finite*
trigonometric polynomial and no estimate uses the number of modes.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.energy_deriv_local
import Submission.Work.Diff.STE.flat.Phi_decomp_smooth
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.gronwall_linear_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory BigOperators Filter

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

/-- The static level-`k` pairing of the flat DeTurck nonlinearity along a box-supported coefficient
family.  This is the expression computed as the time derivative of `ENormSqFull k (seriesFunM ·)`
by `Work.Diff.STE.flat.energy_deriv_local`. -/
noncomputable def pairSharp (n : ℕ) (k : ℕ) (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (c : (Fin n → ℤ) → MatC n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    ((∑ l : Fin k → Fin n,
        L2re (pdVec k l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
          (pdVec k l (fun x => seriesFunM c x i j)))
      + L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
          (fun x => seriesFunM c x i j))

/-- **The missing sharp static estimate.**  Under the sharp threshold `Fintype.card (Fin n) + 4 <
2 * k` the level-`k` pairing of the DeTurck nonlinearity is bounded by a constant as soon as the
level-`k` energy is bounded by `B²`, uniformly in the Galerkin order `N` and in the coefficient
family `c`.  The bound is *uniform* in `N` because the box support makes `seriesFunM c` a finite
trigonometric polynomial and every estimate below is proved with constants independent of the
number of modes; the hypothesis `ENormSqFull k ≤ B²` (available at every time of the trajectory)
turns every factor priced at a level `≤ k` into a constant. -/
def PairingBoundSharp (n : ℕ) (k : ℕ) (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hshape : IsDeTurckNonlin Φ) (lam : ℝ) (B : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
    (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
    ENormSqFull k (seriesFunM c) ≤ B ^ 2 →
    (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat (seriesFunM c x) i j * v i * v j) →
    pairSharp n k Φ c ≤ C

/-- **The a priori estimate from the sharp static pairing bound.**  The Grönwall step, with the
derivative of the energy supplied by `Work.Diff.STE.flat.energy_deriv_local`. -/
theorem energy_apriori_of_pairing_sharp {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (k : ℕ) (lam : ℝ) (hlam : 0 < lam) (B : ℝ)
    (hpair : PairingBoundSharp n k Φ hshape lam B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Tc : ℝ) (hc : 0 < Tc) (N : ℕ) (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
          HasDerivAt (fun s => c s k' i j)
            (Work.Diff.STE.fourierCoeff (fun x =>
              Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c t)) ≤ B ^ 2) →
        ∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c t))
            ≤ (Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c 0)) + 1)
                * Real.exp (C * t) - 1 := by
  classical
  obtain ⟨Cp, hCp, hpair'⟩ := hpair
  obtain ⟨hΦsm, Nfun, hNsm, hNdec, hNper⟩ := hshape
  refine ⟨2 * Cp + 1, by positivity, ?_⟩
  intro Tc hc N c hderiv hsupp hell hen
  -- the energy functional and the formally differentiated pairing
  set E : ℝ → ℝ := fun σ => Work.Diff.STE.Flat.ENormSqFull k
    (Work.Diff.STE.Flat.seriesFunM (c σ)) with hE
  set E' : ℝ → ℝ := fun σ => 2 * pairSharp n k Φ (c σ) with hE'def
  -- moment summability of the coefficients, from the box support
  have hmom : ∀ (σ : ℝ) (i j : Fin n) (M : ℕ),
      Summable (fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ M * ‖c σ m i j‖) :=
    fun σ i j M => Work.Diff.STE.flat.summable_moment_box (c σ) (hsupp σ) i j M
  -- the derivative of the energy, at every time of the interval
  have hderivE : ∀ t ∈ Set.Ico (0 : ℝ) Tc, HasDerivAt E (E' t) t := by
    intro t ht
    obtain ⟨_, hfsm, hfper⟩ := Work.Diff.STE.flat.Phi_decomp_smooth (c := c t) Φ Nfun hNdec
      hNsm hNper hΦsm hlam (hell t ht) (fun i j M => hmom t i j M)
    have hfsmM : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x)) :=
      contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => hfsm i j))
    have hfperM : Work.Diff.STE.Periodic1
        (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x)) := by
      intro i x
      funext i' j'
      exact hfper i' j' i x
    have h := Work.Diff.STE.flat.energy_deriv_local (k := k) (N := N) c
      (fun σ k' => hsupp σ k')
      (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x))
      hfsmM hfperM (hderiv t ht)
    have hE't : E' t = 2 * pairSharp n k Φ (c t) := rfl
    rw [hE, hE't]
    simpa [pairSharp] using h
  -- the pairing bound gives the differential inequality
  have hineq : ∀ t ∈ Set.Ico (0 : ℝ) Tc, E' t ≤ (2 * Cp + 1) * (1 + E t) := by
    intro t ht
    have hb : pairSharp n k Φ (c t) ≤ Cp :=
      hpair' N (c t) (hsupp t) (hen t ht) (hell t ht)
    have hnn : 0 ≤ E t := by
      rw [hE]
      exact Work.Diff.STE.flat.ENormSqFull_nonneg k _
    have hE't : E' t = 2 * pairSharp n k Φ (c t) := rfl
    rw [hE't]
    nlinarith [hb, hCp, hnn]
  have hgoal : ∀ t ∈ Set.Ico (0 : ℝ) Tc,
      E t ≤ (E 0 + 1) * Real.exp ((2 * Cp + 1) * t) - 1 := by
    intro t ht
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Ico (0 : ℝ) Tc :=
      fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    exact Work.Diff.STE.gronwall_linear_bound (by positivity)
      (fun s hs => (hderivE s (hsub hs)).hasDerivWithinAt)
      (fun s hs => hineq s (hsub hs)) le_rfl t ⟨ht.1, le_rfl⟩
  intro t ht
  have := hgoal t ht
  simpa [hE] using this

end Work.Diff.STE.flat
