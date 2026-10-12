import ChallengeDeps
import Submission.Work.SecondOrder.Reduce.QuadForm
import Submission.Work.SecondOrder.State.bogKernel_symm
import Submission.Work.SecondOrder.State.continuous_pairState
import Submission.Work.TrialState.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/SecondOrder` — the reductions to the named residual

This module connects the quasi-free (pair-excited) family of `Defs.lean` to the
chapter's target, the TrialState residual
`Work.TrialState.SecondOrderUpperBound`.

## The chain

* `secondOrderUpperBound_of_pairFamily` — **the family reduction**: the abstract
  TrialState residual follows from its restriction to the pair-excited family
  `pairState N ψ wt G` (`PairFamilyBound`).  The content is that a pair state is
  an admissible state (continuous and normalized); the reduction is what turns
  "∃ an arbitrary state" into "∃ a member of an explicit family";
* `pairFamilyBound_of_quasiFreeBound` — **the concrete reduction**: the
  pair-family residual follows from its restriction to the *concrete* squeezing
  family `quasiFreeState N s c r hr ω` (uniform condensate `orbConst s`,
  exponential weight `c^m/(2^m m!)`, cutoff scattering pair kernel);
* `secondOrderUpperBound_of_quasiFree` — the composite;
* `pairFamilyBound_of_contDiff` — smooth data give admissible pair states, so
  `PairFamilyBound` is stated with the weakest regularity request.

So `SecondOrderUpperBound` is reduced to a statement about an explicitly defined
family (squeezing amplitude `c`, condensate amplitude `s`, cutoff `r`) of
quasi-free states, whose energy is (by `Reduce/integral_pairStateSq_mul_*`) a
one- and two-body configuration integral.

## Statement hygiene (`NOTES.md` §2)

* `not_secondOrderUpperBound_zero` — the TrialState residual
  `SecondOrderUpperBound` is **false at `N = 0`**: the energy word of the empty
  sector vanishes identically, so the residual needs `1 ≤ N` (or a non-positive
  threshold).  `SecondOrderUpperBound'` is the hypothesis-corrected form;
* `secondOrderUpperBound_of_v_eq_zero` — the residual *is* satisfiable
  (non-vacuous), with the constant state, in the zero-potential case;
* `secondOrderUpperBound_mono` — monotone in the constant `C` (the second-order
  term is an error term, so a larger constant is easier).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.SecondOrder

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Integration of constants over the box -/

/-- Integral of a constant over the `N`-particle centred box: `c · (ℓ³)^N`. -/
lemma integral_const_abox (N : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) (c : ℝ) :
    (∫ _x in abox N ℓ, c) = c * (ℓ ^ 3) ^ N := by
  have h1 : (∫ _x in abox N ℓ, c)
      = (((volume : Measure (X N)).restrict (abox N ℓ)).real Set.univ) • c := by
    simpa using (MeasureTheory.integral_const (μ := (volume : Measure (X N)).restrict (abox N ℓ))
      (c := c))
  rw [h1, MeasureTheory.measureReal_def, Measure.restrict_apply_univ]
  rw [abox_volume N ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  ring

/-! ## The family reduction -/

/-- **The family reduction.**  `TrialState.SecondOrderUpperBound` follows from
its restriction `PairFamilyBound` to the quasi-free (pair-excited) family: a
pair state is a continuous normalized state, and on it `pairStateE` is exactly
the energy word of the residual. -/
theorem secondOrderUpperBound_of_pairFamily {N : ℕ} {ℓ μ C : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hb : PairFamilyBound N ℓ μ C v h) :
    TrialState.SecondOrderUpperBound N ℓ μ C v h := by
  obtain ⟨psi, wt, G, _hsym, hcont, hnorm, hE⟩ := hb
  exact ⟨pairState N psi wt G, hcont, by simpa [pairStateZ] using hnorm,
    by simpa [pairStateE] using hE⟩

/-- **The concrete reduction.**  The pair-family residual follows from the
concrete squeezing residual `QuasiFreeBound`: the kernel `bogKernel r hr ω` is
symmetric whenever the scattering solution `ω` is radial
(`State.bogKernel_symm`). -/
theorem pairFamilyBound_of_quasiFreeBound {N : ℕ} {ℓ μ C : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hb : QuasiFreeBound N ℓ μ C v h) :
    PairFamilyBound N ℓ μ C v h := by
  obtain ⟨s, c, r, hr, hcont, hnorm, hE⟩ := hb
  refine ⟨TrialState.orbConst s, bogWeight c, bogKernel r hr (Classical.choose h),
    fun x y => State.bogKernel_symm r hr (Classical.choose_spec h).1 x y, hcont, ?_, ?_⟩
  · simpa [pairStateZ, quasiFreeState] using hnorm
  · simpa [pairStateE, quasiFreeState] using hE

/-- The composite reduction of the chapter's target. -/
theorem secondOrderUpperBound_of_quasiFree {N : ℕ} {ℓ μ C : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hb : QuasiFreeBound N ℓ μ C v h) :
    TrialState.SecondOrderUpperBound N ℓ μ C v h :=
  secondOrderUpperBound_of_pairFamily (pairFamilyBound_of_quasiFreeBound hb)

/-- Conversely, a family residual built from *smooth* data is a `PairFamilyBound`
(with the weakest, i.e. continuity, regularity request): the composite state of
smooth ingredients is continuous (`State.continuous_pairState`). -/
theorem pairFamilyBound_of_contDiff {N : ℕ} {ℓ μ C : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    {ψ : ℝ³ → ℝ} {wt : ℕ → ℝ} {G : ℝ³ → ℝ³ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hG : ContDiff ℝ ∞ (fun p : ℝ³ × ℝ³ => G p.1 p.2))
    (hsym : ∀ x y : ℝ³, G x y = G y x)
    (hnorm : pairStateZ N ℓ ψ wt G = 1)
    (hE : pairStateE N ℓ μ v h ψ wt G
      ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) :
    PairFamilyBound N ℓ μ C v h :=
  ⟨ψ, wt, G, hsym, State.continuous_pairState (wt := wt) hψ.continuous hG.continuous, hnorm, hE⟩

/-! ## Monotonicity in the constant -/

/-- A larger second-order constant makes the residual easier (the second-order
term is an error term of negative sign in the threshold):  if `C ≤ C'` then
`SecondOrderUpperBound` with `C` implies `SecondOrderUpperBound` with `C'`. -/
theorem secondOrderUpperBound_mono {N : ℕ} {ℓ μ C C' : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ) (ha : 0 ≤ a v) (hC : C ≤ C')
    (hS : TrialState.SecondOrderUpperBound N ℓ μ C v h) :
    TrialState.SecondOrderUpperBound N ℓ μ C' v h := by
  obtain ⟨Φ, hc, hnorm, hE⟩ := hS
  refine ⟨Φ, hc, hnorm, le_trans hE ?_⟩
  have hnu : 0 ≤ (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hpos : 0 ≤ 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 := by positivity
  have hkey : 1 - C' * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
      ≤ 1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hC hnu]
  have hb := neg_le_neg (mul_le_mul_of_nonneg_left hkey hpos)
  simpa [neg_mul] using hb

/-! ## Statement hygiene: the residual is false in the empty sector -/

/-- **`SecondOrderUpperBound` is false at `N = 0`.**  In the empty particle
sector every state has vanishing energy word (`kinWord` and `qLHSword` are
empty sums), so the residual would require the threshold
`-4πμ²(a v)ℓ³(1 - C(μ(a v)³)^{1/2})` to be `≥ 0`.  Hence a consumer of the
TrialState residual must either take `1 ≤ N` or ensure that the threshold is
non-positive; `SecondOrderUpperBound'` records the corrected form. -/
theorem not_secondOrderUpperBound_zero {ℓ μ C : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hpos : 0 < 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) :
    ¬ TrialState.SecondOrderUpperBound 0 ℓ μ C v h := by
  rintro ⟨Φ, _hc, _hnorm, hE⟩
  have hk : kinWord (N := 0) ℓ Φ = 0 := by simp [kinWord]
  have hq : qLHSword (N := 0) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ = 0 := by
    unfold qLHSword
    simp [pairSet]
  rw [hk, hq, zero_add] at hE
  linarith

/-! ## Statement hygiene: the residual is satisfiable -/

/-- The scattering length of the zero potential vanishes. -/
lemma a_zero : a (fun _ : ℝ³ => 0) = 0 := by
  by_cases h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w (fun _ : ℝ³ => 0)
  · rw [Submission.BoseGases.a_eq_integral_of_exists _ h]
    have hz : (fun x : ℝ³ => (fun _ : ℝ³ => 0) x * (1 - (Classical.choose h) x)) = fun _ => 0 := by
      funext x
      simp
    rw [hz, integral_zero, mul_zero]
  · exact Submission.BoseGases.a_eq_zero_of_not_exists _ h

/-- **The residual holds, with every constant, in the zero-potential case.**
Take `Φ` the constant state `(ℓ^{-3/2})^N` on the box: it is continuous, box
normalized (`integral_const_abox`), its kinetic word vanishes (constant
function) and both potential kernels vanish because `v ≡ 0`; the threshold is
`0` because `a 0 = 0`.  This shows that the residual of the chapter is not
vacuous. -/
theorem secondOrderUpperBound_of_v_eq_zero {N : ℕ} {ℓ μ C : ℝ} (hℓ : 0 < ℓ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w (fun _ : ℝ³ => 0)) :
    TrialState.SecondOrderUpperBound N ℓ μ C (fun _ : ℝ³ => 0) h := by
  set c : ℝ := (Real.sqrt (ℓ ^ 3))⁻¹ with hc
  have hℓ3 : 0 < ℓ ^ 3 := by positivity
  have hcsq : c ^ 2 = (ℓ ^ 3)⁻¹ := by
    rw [hc, inv_pow, Real.sq_sqrt hℓ3.le]
  refine ⟨fun _ : X N => c ^ N, continuous_const, ?_, ?_⟩
  · have hsplit : ∀ x : X N, (c ^ N) ^ 2 = (c ^ 2) ^ N := by
      intro x
      rw [← pow_mul, ← pow_mul, mul_comm]
    show (∫ _x in abox N ℓ, (c ^ N) ^ 2) = 1
    rw [funext hsplit]
    rw [integral_const_abox N ℓ hℓ ((c ^ 2) ^ N)]
    rw [hcsq, inv_pow]
    field_simp
  · have hw : wPairC ℓ (fun _ : ℝ³ => 0) = fun _ _ : ℝ³ => 0 := by
      funext x y
      simp [wPairC, wPair, wScaled, chiScale]
    have hg0 : g0 (fun _ : ℝ³ => 0) h = fun _ : ℝ³ => 0 := by
      funext x
      simp [g0]
    have hk : kinWord N ℓ (fun _ : X N => c ^ N) = 0 := by
      simp [kinWord]
    have hq : qLHSword (N := N) ℓ μ (wPairC ℓ (fun _ : ℝ³ => 0))
        (wPairC ℓ (g0 (fun _ : ℝ³ => 0) h)) (fun _ : X N => c ^ N) = 0 := by
      unfold qLHSword w1Fibre
      rw [hg0, hw]
      simp
    show kinWord N ℓ (fun _ : X N => c ^ N)
        + qLHSword (N := N) ℓ μ (wPairC ℓ (fun _ : ℝ³ => 0))
            (wPairC ℓ (g0 (fun _ : ℝ³ => 0) h)) (fun _ : X N => c ^ N) ≤ _
    rw [hk, hq, zero_add]
    have haz : a (fun _ : ℝ³ => 0) = 0 := a_zero
    rw [haz]
    norm_num

/-! ## The corrected residual and the consumer shape -/

/-- The hypothesis-corrected residual implies the consumer's `hEgc` shape (the
`eq:aprioriPsi` bound with constant `J`), for every admissible diluteness
window `ε` and `J ≥ C`.  This is `TrialState.aprioriPsi_of_secondOrder` with the
hypotheses that `SecondOrderUpperBound` provably needs (`1 ≤ N`,
`μ(a v)³ ≤ ε`). -/
theorem exists_hEgc_of_secondOrder' {N : ℕ} {ℓ μ C J ε : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hN : 1 ≤ N) (hμa : μ * (a v) ^ 3 ≤ ε)
    (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ) (ha : 0 ≤ a v) (hC : 0 ≤ C) (hCJ : C ≤ J)
    (hS : SecondOrderUpperBound' N ℓ μ C ε v h) :
    ∃ Φ : X N → ℝ, Continuous Φ ∧ (∫ x in abox N ℓ, (Φ x) ^ 2) = 1 ∧
      kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
        ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
  refine TrialState.aprioriPsi_of_secondOrder h hℓ hμ ha hC hCJ ?_
  exact hS hN hμa

/-! ## The dilute-regime chain and the consumer-facing theorem -/

/-- `PairFamilyBound'` follows from `QuasiFreeBound'`. -/
theorem pairFamilyBound'_of_quasiFreeBound' {N : ℕ} {ℓ μ C ε : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hb : QuasiFreeBound' N ℓ μ C ε v h) : PairFamilyBound' N ℓ μ C ε v h :=
  fun hN hε => pairFamilyBound_of_quasiFreeBound (hb hN hε)

/-- `SecondOrderUpperBound'` follows from `PairFamilyBound'`. -/
theorem secondOrderUpperBound'_of_pairFamilyBound' {N : ℕ} {ℓ μ C ε : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hb : PairFamilyBound' N ℓ μ C ε v h) : SecondOrderUpperBound' N ℓ μ C ε v h :=
  fun hN hε => secondOrderUpperBound_of_pairFamily (hb hN hε)

/-- **The chapter's consumer-facing theorem.**  From the concrete quasi-free
residual in the dilute window (`QuasiFreeBound'`), one obtains the exact `hEgc`
shape of `APrioriSkeleton.APrioriData`: a normalized continuous state whose
`H_Λ(μ)` energy is at most `−4πμ²(a v)ℓ³(1 − J(μ(a v)³)^{1/2})`, for every
`J ≥ C`.  This is the wiring a consumer needs: only `QuasiFreeBound'` (the
ESY/Yau–Yin variational computation) and the threshold arithmetic remain. -/
theorem exists_hEgc_of_quasiFreeBound' {N : ℕ} {ℓ μ C J ε : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hN : 1 ≤ N) (hε : μ * (a v) ^ 3 ≤ ε)
    (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ) (ha : 0 ≤ a v) (hC : 0 ≤ C) (hCJ : C ≤ J)
    (hS : QuasiFreeBound' N ℓ μ C ε v h) :
    ∃ Φ : X N → ℝ, Continuous Φ ∧ (∫ x in abox N ℓ, (Φ x) ^ 2) = 1 ∧
      kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
        ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
  refine TrialState.aprioriPsi_of_secondOrder h hℓ hμ ha hC hCJ ?_
  exact secondOrderUpperBound'_of_pairFamilyBound'
    (pairFamilyBound'_of_quasiFreeBound' hS) hN hε

/-- **Consumer version for the quadratic-form residual.**  `PairFormBound`
(the energy condition stated for the finite quadratic form of the matching
amplitudes) implies `PairFamilyBound`, hence the TrialState residual, hence the
`hEgc` shape — for every `J ≥ C`. -/
theorem exists_hEgc_of_pairFormBound {N : ℕ} {ℓ μ C J : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hμ : 0 ≤ μ) (ha : 0 ≤ a v) (hC : 0 ≤ C) (hCJ : C ≤ J)
    (hb : Reduce.PairFormBound N ℓ μ C v h) :
    ∃ Φ : X N → ℝ, Continuous Φ ∧ (∫ x in abox N ℓ, (Φ x) ^ 2) = 1 ∧
      kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
        ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) :=
  TrialState.aprioriPsi_of_secondOrder h hℓ.le hμ ha hC hCJ
    (secondOrderUpperBound_of_pairFamily (Reduce.pairFamilyBound_of_pairFormBound h hℓ hb))

/-- The quadratic-form residual gives the corrected residual
`SecondOrderUpperBound'` in the dilute window. -/
theorem secondOrderUpperBound'_of_pairFormBound {N : ℕ} {ℓ μ C ε : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hb : ∀ _hN : 1 ≤ N, ∀ _hε : μ * (a v) ^ 3 ≤ ε,
      Reduce.PairFormBound N ℓ μ C v h) :
    SecondOrderUpperBound' N ℓ μ C ε v h :=
  fun hN hε => secondOrderUpperBound_of_pairFamily
    (Reduce.pairFamilyBound_of_pairFormBound h hℓ (hb hN hε))

end Work.SecondOrder
