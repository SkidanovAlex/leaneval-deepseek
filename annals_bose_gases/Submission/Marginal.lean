import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.ProductBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Uniform marginal-cost bound for the Dirichlet box energies.

GOAL (single deliverable lemma `exists_marginal_bound`): for `0 ≤ v`,
`MemLp v 1` and a cut-off density `ρmax ≥ 0`, there is a constant
`M ≥ 0` such that for every box of side `L ≥ 1` and every `N, k : ℕ` with
`(N : ℝ) + k ≤ ρmax · L³`,

    boxEnergy (N + k) L v - boxEnergy N L v ≤ (k : ℝ) · M .

i.e. adding `k` particles to an admissible `N`-particle box costs at most
`k·M` of energy, uniformly in the box.  (Classically the marginal cost of a
boson is bounded by the one-particle kinetic `O(1/L²) ≤ O(1)` plus the
pair-interaction with at most `ρmax·L³` particles, each pair bounded by
`‖φ‖∞²·‖v‖₁ = O(1/L³)`.)

PROOF ROUTE (all ingredients already in the corpus — do NOT re-prove the
deep lemmas, reuse them):

STEP 1 — one-step marginal via a product trial state.  For `L ≥ 1`, let
`φ := oneParticle L` (`Submission.OneParticle`).  The bundle
`OneParticleFacts L := oneParticle_facts (hL : 1 ≤ L)` supplies exactly the
interface of `Submission.ProductState`:

    contDiff : ContDiff ℝ ∞ φ        (oneParticle_contDiff)
    tsupp    : tsupport φ ⊆ interior (cube L)
    norm     : (∫ x : ℝ³, (φ x)^2) = 1
    sq_bound : ∀ x, (φ x)^2 ≤ supC / L^3        (sp := supC / L^3)
    kin_bound: ∫ |φ·Δφ| ≤ kinC / L^2            (A := ∫|φ·Δφ|)

`Submission.ProductState.boxQuot_add_one` says: for ANY `Φn : CInfty0Box n L`,
with `Φ1 := oneState (φ := φ) hφc hφts hφnorm` (a `CInfty0Box 1 L` state) and
`Ψ := psProdState Φn Φ1 : CInfty0Box (n+1) L`,

    boxQuot (n+1) L v Ψ ≤ boxQuot n L v Φn + A + (n:ℝ)·sp·B ,

where `B := ∫ |v| = vL1 v`, `A := ∫|φ·Δφ|`, `sp := supC/L³`.
(Note: `boxQuot_add_one` needs `0 < L`; get it from `1 ≤ L`.)

Upper bounds (L ≥ 1): `A ≤ kinC/L² ≤ kinC` and
`(n:ℝ)·sp·B ≤ ρmax·supC·B` when `(n:ℝ)+1 ≤ ρmax·L³` (then `n ≤ ρmax·L³`).
So with `M₀ := kinC + ρmax·supC·(vL1 v)`:  boxQuot(n+1,trial) ≤ boxQuot n Φn + M₀.

STEP 2 — pass to the ground states.  `boxEnergy = ⨅ boxQuot`
(`boxEnergy_eq_ciInf_boxQuot`, in `Submission.SubaddVol`).  For `0 ≤ v` the
quotients are bounded below by `0` (so the infimum is a genuine csInf over a
nonempty bounded-below set — nonemptyness: `nonempty_CInfty0Box 0 L` or
`nonempty_CInfty0Box n L`; see `BoxMonotone.nonempty_CInfty0Box`); hence
`boxEnergy N L v` is the infimum of `{boxQuot N L v Φ | Φ}` and is
approached from above: for every `ε > 0` there is `Φn : CInfty0Box n L` with
`boxQuot n L v Φn ≤ boxEnergy n L v + ε` (use
`csInf_lt_iff` / `exists_lt_of_csInf_lt` with `a := boxEnergy n L v + ε`,
nonemptiness and bounded-belowness).  Combine with the STEP-1 trial bound and
`boxEnergy ≤ boxQuot` of the trial state
(use `csInf_le`, or `ProductBound.boxEnergy_le_of_boxQuot_le`); conclude for
every `ε > 0`:
    boxEnergy (n+1) L v - boxEnergy n L v ≤ M₀ + ε ,
then let ε → 0 (`le_of_forall_pos_le_add`) to get the one-step bound
    boxEnergy (n+1) L v - boxEnergy n L v ≤ M₀
for every `L ≥ 1`, `n` with `(n:ℝ)+1 ≤ ρmax·L³`.

STEP 3 — telescope.  For `N, k` with `(N:ℝ)+k ≤ ρmax·L³`, apply the one-step
bound at each `j = N, …, N+k−1` (each satisfies `(j:ℝ)+1 ≤ (N:ℝ)+k ≤ ρmax·L³`)
and sum:
    boxEnergy (N+k) L v - boxEnergy N L v = Σ_{j=N}^{N+k-1} (E(j+1)-E(j))
        ≤ k·M₀ .
(Even if individual differences are negative this telescoping is valid: write
the difference as a telescoping sum of `Finset.sum_range` and bound termwise.)
Deliver `M := M₀` with `0 ≤ M` (show `0 ≤ kinC`, `0 ≤ supC`, `0 ≤ vL1 v`,
`0 ≤ ρmax`).

HYPOTHESES USED: `hv : 0 ≤ v` only for the quotient lower bound (infimum
regularity) and `hv1 : MemLp v 1` for integrability of `|v|`; no support or
radiality assumptions on `v` are needed.  Do NOT change the statement of
`exists_marginal_bound`.  Add any helper lemmas you need above it.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

-- `haveI` below is deliberate: `le_ciInf` needs the instance in the local context.
set_option linter.style.haveILetI false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Uniform one-step marginal-cost bound: adding one particle to an admissible
`n`-particle box of side `L ≥ 1` costs at most `M`. -/
lemma exists_marginal_one {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    {ρmax : ℝ} (hρmax : 0 ≤ ρmax) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ⦃L : ℝ⦄, 1 ≤ L → ∀ n : ℕ, (n : ℝ) + 1 ≤ ρmax * L ^ 3 →
      boxEnergy (n + 1) L v - boxEnergy n L v ≤ M := by
  let M : ℝ := kinC + ρmax * supC * vL1 v
  have hB0 : 0 ≤ vL1 v := by
    unfold vL1
    exact integral_nonneg (fun x => abs_nonneg (v x))
  have hkin0 : 0 ≤ kinC := by
    unfold kinC
    exact div_nonneg (integral_nonneg (fun x : ℝ³ => abs_nonneg (unitBump x * Δ (unitBump) x)))
      (le_of_lt unitNorm_pos)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    have hsup0 : 0 ≤ supC := supC_nonneg
    have hρsup : 0 ≤ ρmax * supC := mul_nonneg hρmax hsup0
    have hρsupB : 0 ≤ ρmax * supC * vL1 v := mul_nonneg hρsup hB0
    linarith
  refine ⟨M, hM0, ?_⟩
  intro L hL n hn
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have facts := oneParticle_facts (L := L) hL
  let φ : ℝ³ → ℝ := oneParticle L
  let sp : ℝ := supC / L ^ 3
  have hLnonneg : 0 ≤ L := by linarith
  have hsp0 : 0 ≤ sp := by
    dsimp [sp]
    exact div_nonneg facts.supC_nonneg (pow_nonneg hLnonneg 3)
  have hφc : ContDiff ℝ ∞ φ := by dsimp [φ]; exact facts.contDiff
  have hφts : tsupport φ ⊆ interior (cube L) := by dsimp [φ]; exact facts.tsupp
  have hφnorm : (∫ x : ℝ³, (φ x) ^ 2) = 1 := by dsimp [φ]; exact facts.norm
  have hφsq : ∀ x : ℝ³, (φ x) ^ 2 ≤ sp := by
    intro x
    dsimp [φ, sp]
    exact facts.sq_bound x
  -- n ≤ ρmax * L^3 from the hypothesis
  have hnLe : (n : ℝ) ≤ ρmax * L ^ 3 := by linarith
  have hspB0 : 0 ≤ (supC / L ^ 3) * vL1 v := mul_nonneg (div_nonneg facts.supC_nonneg (pow_nonneg hLnonneg 3)) hB0
  have hnsp : (n : ℝ) * (supC / L ^ 3) * vL1 v ≤ ρmax * supC * vL1 v := by
    have hmul := mul_le_mul_of_nonneg_right hnLe hspB0
    have hL3ne : L ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hLpos)
    have hmul' : (n : ℝ) * ((supC / L ^ 3) * vL1 v) ≤ (ρmax * L ^ 3) * ((supC / L ^ 3) * vL1 v) := by
      simpa [mul_assoc] using hmul
    have hcancel : (ρmax * L ^ 3) * ((supC / L ^ 3) * vL1 v) = ρmax * supC * vL1 v := by
      field_simp [hL3ne]
    calc
      (n : ℝ) * (supC / L ^ 3) * vL1 v = (n : ℝ) * ((supC / L ^ 3) * vL1 v) := by ring
      _ ≤ (ρmax * L ^ 3) * ((supC / L ^ 3) * vL1 v) := hmul'
      _ = ρmax * supC * vL1 v := hcancel
  have hAkin : (∫ x : ℝ³, |φ x * Δ φ x|) ≤ kinC := by
    have h1leL2 : (1 : ℝ) ≤ L ^ 2 := by
      have h01 : (0 : ℝ) ≤ 1 := by norm_num
      simpa using (pow_le_pow_left₀ h01 hL 2)
    have hL2pos : 0 < L ^ 2 := pow_pos hLpos 2
    have hb := facts.kin_bound
    calc
      (∫ x : ℝ³, |φ x * Δ φ x|) ≤ kinC / L ^ 2 := by simpa [φ] using hb
      _ ≤ kinC := by
        rw [div_le_iff₀ hL2pos]
        calc
          kinC = kinC * 1 := by ring
          _ ≤ kinC * L ^ 2 := mul_le_mul_of_nonneg_left h1leL2 hkin0
  -- one-step trial-state estimate, for every state Φn
  have hstep : ∀ Φn : CInfty0Box n L, boxEnergy (n + 1) L v ≤ boxQuot n L v Φn + M := by
    intro Φn
    let Φ1 : CInfty0Box 1 L := oneState (φ := φ) hφc hφts hφnorm
    let Ψ : CInfty0Box (n + 1) L := psProdState Φn Φ1
    have hbdd : BddBelow (Set.range (boxQuot (n + 1) L v)) := by
      refine ⟨0, ?_⟩
      rintro y ⟨Φ, rfl⟩
      exact boxQuot_nonneg hLpos hv Φ
    have hinfle : boxEnergy (n + 1) L v ≤ boxQuot (n + 1) L v Ψ := by
      rw [boxEnergy_eq_ciInf_boxQuot]
      exact ciInf_le hbdd Ψ
    have hqa := boxQuot_add_one (n := n) (L := L) (v := v) (φ := φ) (sp := sp)
      hLpos hv1 hsp0 hφc hφts hφsq hφnorm Φn
    have hqa' : boxQuot (n + 1) L v Ψ ≤ boxQuot n L v Φn +
        (∫ x : ℝ³, |φ x * Δ φ x|) + (n : ℝ) * sp * vL1 v := by
      simpa [Ψ, Φ1, sp, vL1] using hqa
    have hbig : boxQuot (n + 1) L v Ψ ≤ boxQuot n L v Φn + M := by
      have hright : (∫ x : ℝ³, |φ x * Δ φ x|) + (n : ℝ) * sp * vL1 v ≤ M := by
        dsimp [sp, M]
        have hnsp' : (n : ℝ) * (supC / L ^ 3) * vL1 v ≤ ρmax * supC * vL1 v := hnsp
        linarith
      linarith
    calc
      boxEnergy (n + 1) L v ≤ boxQuot (n + 1) L v Ψ := hinfle
      _ ≤ boxQuot n L v Φn + M := hbig
  -- pass to the infimum
  have hle : ∀ Φn : CInfty0Box n L, boxEnergy (n + 1) L v - M ≤ boxQuot n L v Φn := by
    intro Φn
    linarith [hstep Φn]
  have hinf : boxEnergy (n + 1) L v - M ≤ boxEnergy n L v := by
    rw [boxEnergy_eq_ciInf_boxQuot (N := n) (L := L) (v := v)]
    haveI : Nonempty (CInfty0Box n L) := nonempty_CInfty0Box n hLpos
    exact le_ciInf hle
  linarith

lemma exists_marginal_bound {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    {ρmax : ℝ} (hρmax : 0 ≤ ρmax) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ⦃L : ℝ⦄, 1 ≤ L → ∀ {N k : ℕ}, (N : ℝ) + k ≤ ρmax * L ^ 3 →
      boxEnergy (N + k) L v - boxEnergy N L v ≤ (k : ℝ) * M := by
  rcases exists_marginal_one (v := v) hv hv1 (ρmax := ρmax) hρmax with ⟨M, hM0, hone⟩
  refine ⟨M, hM0, ?_⟩
  intro L hL N k hNk
  let g : ℕ → ℝ := fun j => boxEnergy (N + j) L v
  have hstep : ∀ j : ℕ, j < k → g (j + 1) - g j ≤ M := by
    intro j hj
    have hnat : (N + j : ℕ) + 1 ≤ N + k := by
      have h2 : N + (j + 1) ≤ N + k := Nat.add_le_add_left (Nat.succ_le_of_lt hj) N
      simpa [Nat.add_assoc] using h2
    have hc1 : ((N + j : ℕ) : ℝ) + 1 ≤ ((N + k : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hc2 : ((N + k : ℕ) : ℝ) = (N : ℝ) + (k : ℝ) := by exact Nat.cast_add N k
    have hcond : ((N + j : ℕ) : ℝ) + 1 ≤ ρmax * L ^ 3 := by
      linarith
    have hone' := hone (L := L) hL (N + j) hcond
    change boxEnergy (N + (j + 1)) L v - boxEnergy (N + j) L v ≤ M
    exact hone'
  calc
    boxEnergy (N + k) L v - boxEnergy N L v
        = ∑ i ∈ Finset.range k, (g (i + 1) - g i) := by
            change g k - g 0 = ∑ i ∈ Finset.range k, (g (i + 1) - g i)
            rw [Finset.sum_range_sub g k]
    _ ≤ ∑ i ∈ Finset.range k, M := by
            exact Finset.sum_le_sum (fun i hi => hstep i (Finset.mem_range.mp hi))
    _ = (k : ℝ) * M := by simp
