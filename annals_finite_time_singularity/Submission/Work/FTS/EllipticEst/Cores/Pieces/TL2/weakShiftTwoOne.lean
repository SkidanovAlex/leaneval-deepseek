/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TL2/weakShiftTwoOne`: the class shift `EllWeakPos α k → EllWeakPos α (k-1)` along `D_z`

The target of this file is

```
Work.FTS.EllipticEst.Cores.Pieces.TL2.weakShiftTwoOne :
  ∀ {α : ℝ} {k : ℕ}, 2 ≤ k → ∀ {F Ψ : ℝ → ℝ → ℝ},
    TT.EllWeakPos α k F Ψ → TT.EllWeakPos α (k - 1) (D_z F) (D_z Ψ)
```

i.e. the *radially differentiated data* of the weak hypothesis class are again a datum of the
class, one level down.  This is the class-level input of the induction step of Elgindi's
Proposition `prop:Hk` (the paper's §"General `ℋ^k` case"): the shifted data are consumed at level
`k - 1 ≥ 1`.

## The nine fields, and where each comes from

`EllWeakPos` is a conjunction of nine statements about the pair `(F, Ψ)`; all nine are preserved:

* **equation**: `bslOp α` commutes with `D_z` (`TT.bslOp_DzIter_eq`), so
  `bslOp α (D_z^jΨ) = D_z^jF` on the open quadrant;
* **Dirichlet data** `Ψ(z,0) = Ψ(z,π/2) = 0`: preserved by `TT.DzIter_zero_at_zero` and
  `TT.DzIter_zero_at_pi_half`;
* **moment conditions** `F_*(D_zF) = 0` and `F_*(D_zΨ) = 0`: supplied by the *proved* siblings
  `remov.Fstar_DzIter_one_F_ge_two` (which needs `2 ≤ k`: the chain rule at `j = 0, 1` plus the
  continuity of `B₁`) and `remov.Fstar_DzIter_one_Psi`.  These two are the only inputs of the
  file that are not bookkeeping;
* **smoothness** on the open quadrant: `SmoothOpen.DzIter`;
* **`ℋ^{k-1}`-membership of the three fields** `F`, `z²∂_zzΨ`, `∂_θθΨ`: from the pointwise
  domination `HkIntegrand α (k-1) (D_z g) ≤ (k + k²)·HkIntegrand α k g` on the closed quadrant
  `Iz × Iθ` (`HkIntegrand_Dz_shift_le_Iz`) through the domination criterion
  `Work.FTS.LocData.HkMem_of_majorant`.  Two structural identities are needed to recognise
  `D_z(z²∂_zzΨ)` and `D_z(∂_θθΨ)` as `z²∂_zz(D_zΨ)` and `∂_θθ(D_zΨ)`:
  `DzAmgm.ZsqPz2Comm` and `Dz_pthIter_two_comm`.

## Traps handled here (do not "simplify" them away)

* `Work.FTS.EllipticEst.remov.Step.HkIntegrand_shift_le` of `remov/EllEstUnifStepAux` cannot be used: its hypothesis
  `ContDiffOn ℝ ⊤ (uncurry f) Qd` is *analyticity* in this Mathlib (`⊤ : ℕ∞ω` is the analytic
  order), whereas `EllWeakPos` only supplies `C^∞` on the open quadrant.  The shift bound is
  therefore re-proved here at the genuine smooth order (`HkIntegrand_Dz_shift_le`), which is why
  `DzAmgm.DthIterDzCommOpen` (the `C^∞`-version of `D_θ^i ∘ D_z = D_z ∘ D_θ^i`) is imported.
* The domination criterion available on this (poison-free) import cone,
  `Work.FTS.LocData.HkMem_of_majorant`, asks for the pointwise bounds on the **closed** quadrant
  `Iz × Iθ`, while the shift identity `mixed j i (D_z f) = mixed (j+1) i f` is only available at
  *interior* angles.  The two boundary angles are handled by the structural vanishing
  `HkIntegrand α k f z θ = 0` whenever `sin(2θ) = 0`
  (`HkIntegrand_eq_zero_of_sin_eq_zero`, `HkIntegrand_eq_zero_at_zero`,
  `HkIntegrand_eq_zero_at_pi_half`): every mixed slot carries the factor `sin(2θ)` (its outermost
  `D_θ` is `sin(2θ)·∂_θ`) and every radial slot carries `Zu = w/sin(2θ)^{η/2}`, and the
  exponent `η/2 ≠ 0` makes `0^{η/2} = 0` under Lean's conventions `x/0 = 0`, `0^y = 0` for
  `y ≠ 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDescent
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_Psi
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Blocks.HkMem_of_majorant_aesm
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Pieces.TL2

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Bookkeeping around the open quadrant -/

/-- **`z²·g` is `C^∞` on the open quadrant as soon as `g` is.**  (The open-quadrant version of
`SmoothOpen.zsq_mul`, which is not on this import cone.) -/
theorem smoothOpen_zsq_mul' {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * g z θ) := by
  have hz2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_fst (𝕜 := ℝ) (n := Work.Stability.smoothOrder)
      (s := Work.FTS.EllipticEst.Q0)).pow 2
  refine (hz2.mul hg).congr ?_
  intro p hp
  rfl

/-- **The source of the weak class is `C^∞` on the open quadrant.**  On `Q0` it agrees with
`bslOp α Ψ`, which is `C^∞` there by `SmoothOpen_bslOp_of_smoothOpen`. -/
theorem SmoothOpen_of_bslOp_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ) heq

/-- The shifted mixed slots, at the genuine smooth order: for `f` of class `C^∞` on the open
quadrant and `(z,θ)` in the open quadrant, `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`.
This is `D_z`-commutation with `D_θ^i` (`DthIterDzCommOpen`) followed by
`D_z^j (D_z g) = D_z^{j+1} g` and the local congruence of iterated `D_z` on the open quadrant. -/
theorem mixed_Dz_shift_eq {j i : ℕ} (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Work.FTS.EllipticEst.remov.Step.Qd :=
    Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen f hg i
  have hpt : (z, θ) ∈ Work.FTS.EllipticEst.remov.Step.Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Work.FTS.EllipticEst.remov.Step.DzIter_congr_of_isOpen Work.FTS.EllipticEst.remov.Step.isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Work.FTS.EllipticEst.remov.Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-! ## The pointwise shift bound for `HkIntegrand` -/

/-- **The pointwise `D_z`-shift bound at interior angles.**
Every slot of `HkIntegrand α (k-1) (D_z f)` is a slot of `HkIntegrand α k f` (up to the
commutation of `D_z` with `D_θ^i`), and each single slot is dominated by the whole integrand;
counting `k` radial and `k·k` mixed slots gives the factor `k + k²`. -/
theorem HkIntegrand_Dz_shift_le (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Work.FTS.EllipticEst.remov.Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Work.FTS.EllipticEst.remov.Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Work.FTS.EllipticEst.remov.Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2 := by
      unfold Work.FTS.EllipticEst.remov.Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Work.FTS.EllipticEst.remov.Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Work.FTS.EllipticEst.remov.Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_Dz_shift_eq f hz hθ hg]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Zsum k f z θ + Work.FTS.EllipticEst.remov.Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

/-! ## The two boundary angles of `Iθ`

`HkIntegrand` vanishes identically at `θ = 0` and at `θ = π/2`: the mixed slots carry the factor
`sin(2θ)` (their outermost `D_θ` is `sin(2θ)·∂_θ`, and the radial iterates of a function which
vanishes identically in `z` at a fixed angle vanish at that angle too), and the radial slots
carry the factor `Zu = w/sin(2θ)^{η/2}`. -/

/-- A `D_θ`-iterate of order `≥ 1` vanishes wherever `sin(2θ) = 0`. -/
theorem DthIter_eq_zero_of_sin_eq_zero {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsin : Real.sin (2 * θ) = 0) {i : ℕ} (hi : 1 ≤ i) :
    ∀ z : ℝ, Work.Spaces.DthIter i f z θ = 0 := by
  intro z
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, hsin, zero_mul]

/-- Radial iterates of a function that vanishes identically in `z` at a fixed angle vanish at
that angle. -/
theorem DzIter_eq_zero_at_theta {h : ℝ → ℝ → ℝ} {θ : ℝ} (hh : ∀ z, h z θ = 0) :
    ∀ (j : ℕ) (z : ℝ), Work.Spaces.DzIter j h z θ = 0 := by
  intro j
  induction j with
  | zero => intro z; exact hh z
  | succ j ih =>
      intro z
      show z * Work.Spaces.pz (Work.Spaces.DzIter j h) z θ = 0
      simp only [Work.Spaces.pz]
      have hzero : (fun z' => Work.Spaces.DzIter j h z' θ) = fun _ => (0 : ℝ) := funext ih
      rw [hzero, deriv_const]
      ring

/-- A mixed slot of angular order `i ≥ 1` vanishes wherever `sin(2θ) = 0`. -/
theorem mixed_eq_zero_of_sin_eq_zero {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsin : Real.sin (2 * θ) = 0) {i : ℕ} (hi : 1 ≤ i) (j : ℕ) (z : ℝ) :
    Work.Spaces.mixed j i f z θ = 0 :=
  DzIter_eq_zero_at_theta (DthIter_eq_zero_of_sin_eq_zero hsin hi) j z

/-- **`HkIntegrand` vanishes at both boundary angles**, for every `f`, `k` and `α`. -/
theorem HkIntegrand_eq_zero_of_sin_eq_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {θ : ℝ}
    (hsin : Real.sin (2 * θ) = 0) (z : ℝ) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  have hZu : Work.FTS.EllipticEst.remov.Step.Zu z θ = 0 := by
    have h0 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [hsin]
      exact Real.zero_rpow (by norm_num [Work.Spaces.eta])
    simp only [Work.FTS.EllipticEst.remov.Step.Zu, Work.Spaces.w]
    rw [h0, div_zero]
  have hZ : Work.FTS.EllipticEst.remov.Step.Zsum k f z θ = 0 := by
    unfold Work.FTS.EllipticEst.remov.Step.Zsum
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hZu]
    ring
  have hM : Work.FTS.EllipticEst.remov.Step.Msum α k f z θ = 0 := by
    unfold Work.FTS.EllipticEst.remov.Step.Msum
    refine Finset.sum_eq_zero (fun i _ => ?_)
    refine Finset.sum_eq_zero (fun j _ => ?_)
    by_cases hc : (1 ≤ i ∧ i + j ≤ k)
    · rw [if_pos hc, mixed_eq_zero_of_sin_eq_zero hsin hc.1 j z]
      ring
    · rw [if_neg hc]
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq, hZ, hM, add_zero]

/-- `HkIntegrand` vanishes at `θ = 0`. -/
theorem HkIntegrand_eq_zero_at_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α k f z 0 = 0 :=
  HkIntegrand_eq_zero_of_sin_eq_zero α k f (by simp) z

/-- `HkIntegrand` vanishes at `θ = π/2`. -/
theorem HkIntegrand_eq_zero_at_pi_half (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α k f z (Real.pi / 2) = 0 := by
  refine HkIntegrand_eq_zero_of_sin_eq_zero α k f ?_ z
  have h2 : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
  rw [h2, Real.sin_pi]

/-- **The pointwise `D_z`-shift bound on the closed quadrant `Iz × Iθ`.**  At interior angles
this is `HkIntegrand_Dz_shift_le`; at the two boundary angles both sides vanish; and at `z = 0`
both sides vanish for every angle. -/
theorem HkIntegrand_Dz_shift_le_Iz (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
        ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
  · subst h0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst α (k - 1) (Work.Spaces.Dz f) θ,
      Work.FTS.LocData.HkIntegrand_zero_fst α k f θ, mul_zero]
  · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).1 with hθ0 | hθ0'
    · rw [← hθ0, HkIntegrand_eq_zero_at_zero α (k - 1) (Work.Spaces.Dz f) z,
        HkIntegrand_eq_zero_at_zero α k f z, mul_zero]
    · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).2 with hθpi | hθpi'
      · rw [hθpi, HkIntegrand_eq_zero_at_pi_half α (k - 1) (Work.Spaces.Dz f) z,
          HkIntegrand_eq_zero_at_pi_half α k f z, mul_zero]
      · exact HkIntegrand_Dz_shift_le α hk f hz0 ⟨hθ0', hθpi'⟩ hg

/-- **Membership form of the `D_z`-shift**: if `f` is `C^∞` on the open quadrant and in
`ℋ^k` (`k ≥ 1`), then `D_z f ∈ ℋ^{k-1}`.  This is the domination lemma
`Work.FTS.LocData.HkMem_of_majorant` applied to the pointwise bound
`HkIntegrand_Dz_shift_le_Iz`. -/
theorem HkMem_Dz_shift {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz f) := by
  refine Work.FTS.LocData.HkMem_of_majorant α (k - 1) (f := Work.Spaces.Dz f)
    (M := fun z θ => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
    ?_ ?_ ?_ ?_
  · exact (Work.FTS.EllipticEst.SmoothOpen.Dz hf).continuousOn_HkIntegrand α (k - 1)
  · intro z hz
    exact (hmem.1 z hz).const_mul _
  · show MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
    simpa only [MeasureTheory.integral_const_mul] using hmem.2.const_mul _
  · intro z hz θ hθ
    exact HkIntegrand_Dz_shift_le_Iz α hk f hf z hz θ hθ

/-! ## Commutation of `D_z` with `∂_θ²` -/

/-- **`∂_z` commutes with `∂_θ²` on the open quadrant**: Clairaut's theorem applied twice
(the first step with `∂_θ Ψ` as the function, the second by congruence on the open set). -/
theorem pz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) := by
  intro z θ hz hθ hlt
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      ContDiffAt ℝ 2 (Function.uncurry Ψ) (z', θ') := fun z' θ' hz' hθ' hlt' =>
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨ 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hlt'⟩))
  have hcd_pth : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) (z, θ) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pth Ψ)).mp
      (Work.FTS.EllipticEst.SmoothOpen.pth hΨ) 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.pz_pth_comm (f := Work.Spaces.pth Ψ) hcd_pth
  have hagree : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pz (Work.Spaces.pth Ψ))
      (Work.Spaces.pth (Work.Spaces.pz Ψ)) :=
    fun z' θ' hz' hθ' hlt' => Work.Spaces.pz_pth_comm (f := Ψ) (hcd z' θ' hz' hθ' hlt')
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Ψ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
      (fun p hp => by
        obtain ⟨z', θ'⟩ := p
        exact hagree z' θ' hp.1 hp.2.1 hp.2.2) hmem
  show Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact h1.trans h2

/-- **`D_z` commutes with `∂_θ²` on the open quadrant.**  Since `D_z f = z·∂_z f` and the
factor `z` does not depend on `θ`, the plain commutation `pz_pthIter_two_comm` gives the
identity for `D_z` as well. -/
theorem Dz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)) := by
  have hplain := pz_pthIter_two_comm hΨ
  have hmul : Work.Spaces.pth (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pz Ψ z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ
    rw [deriv_const_mul_field]
  have hstep : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ := by
    have h2 : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
        = Work.Spaces.pth (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ) := by
      rw [← hmul]
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
    rw [h2]
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
    rw [deriv_const_mul_field]
  intro z θ hz hθ hlt
  show z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ) z θ
  rw [hstep, hplain z θ hz hθ hlt]

/-! ## The assembly -/

/-- **The assembly of the shift, given the two moment conditions.**

All nine fields of `EllWeakPos α (k-1) (D_z F) (D_z Ψ)` are produced here except the two moment
conditions, which are supplied as explicit hypotheses:

* the equation is preserved because `bslOp` commutes with `D_z`
  (`Work.FTS.EllipticEst.TT.bslOp_DzIter_eq`);
* the Dirichlet data are preserved (`Work.FTS.EllipticEst.TT.DzIter_zero_at_zero`,
  `..._pi_half`);
* the smoothness is preserved (`SmoothOpen.DzIter`);
* the `ℋ`-membership of the three fields follows from the pointwise domination
  `HkIntegrand α (k-1) (D_z g) ≤ ((k:ℝ)+(k:ℝ)*(k:ℝ)) * HkIntegrand α k g`
  (`HkIntegrand_Dz_shift_le_Iz`, at the genuine `C^∞` order, via
  `Work.FTS.LocData.HkMem_of_majorant`) for `g ∈ {F, z²∂_zzΨ, ∂_θθΨ}`;
* the auxiliary identities needed are `pthIter 2 (D_z Ψ) = D_z (pthIter 2 Ψ)`
  (`Dz_pthIter_two_comm`) and `z² ∂_zz(D_z Ψ) = D_z (z² ∂_zzΨ)`
  (`Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm`), both pointwise on the open quadrant. -/
theorem EllWeakPos_DzIter_one_shift_of_moments {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hmomF : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0)
    (hmomΨ : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen h
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    SmoothOpen_of_bslOp_eq hSΨ (fun z θ hz hθ hlt => h.1 z hz θ hθ hlt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation commutes with `D_z`
    exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.1
  · -- the Dirichlet data at `θ = 0`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.zero
  · -- the Dirichlet data at `θ = π/2`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.pi_half
  · -- the source moment condition
    exact hmomF
  · -- the solution moment condition
    exact hmomΨ
  · -- smoothness on the open quadrant is preserved by `D_z`
    intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DzIter 1 Ψ)).mp
      (Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen_DzIter h 1) n
  · -- `D_z F ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz F) :=
      HkMem_Dz_shift hk hSF h.memF
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hmem
  · -- `z² ∂_zz(D_z Ψ) ∈ ℋ^{k-1}`
    have hG : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      smoothOpen_zsq_mul' (Work.FTS.EllipticEst.SmoothOpen.pzIter hSΨ 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      HkMem_Dz_shift hk hG h.memA
    have hEqOn := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hSΨ 1 0
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact (hEqOn (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
      from ⟨hz, hθ⟩)).symm
  · -- `∂_θθ(D_z Ψ) ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
      HkMem_Dz_shift hk (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2) h.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact Dz_pthIter_two_comm hSΨ z θ hz hθ.1 hθ.2
  · -- `ℋ^{k-1}`-honesty of the diagonal second-order term of the shifted datum:
    -- `z ∂_z∂_θθ(D_zΨ) = D_z (D_z ∂_θθΨ)`, and `∂_θθ` commutes with `D_z`.
    have hZ : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))) :=
      HkMem_Dz_shift hk
        (Work.FTS.EllipticEst.SmoothOpen.Dz
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2))
        h.memZPth2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hZ ?_
    intro z hz θ hθ
    show Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) z θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
    have hpe : Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ :=
      Work.Spaces.pz_congr_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
        (Work.EllipticEst.H2W.pthIter2_DzIter_comm hSΨ 1) ⟨hz, hθ⟩
    rw [hpe, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    rfl


/-- **The `D_z`-shift of the weak hypothesis class.**

This is the instance of `EllWeakPos_DzIter_one_shift_of_moments` for `2 ≤ k`: here both moment
conditions are available from the *proved* lemmas `Fstar_DzIter_one_F_ge_two` (the `F`-half, via
the chain rule at `j = 0, 1` and the continuity of `F_*(D_z F)`) and `Fstar_DzIter_one_Psi` (the
`Ψ`-half, by the first-order difference-quotient argument), so the statement is complete. -/
theorem EllWeakPos_DzIter_one_shift_two_le {α : ℝ} {k : ℕ} (hk : 2 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  EllWeakPos_DzIter_one_shift_of_moments (by omega) h
    (Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two hk h)
    (Work.FTS.EllipticEst.remov.Fstar_DzIter_one_Psi (by omega) h)

theorem weakShiftTwoOne {α : ℝ} {k : ℕ} (hk : 2 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  EllWeakPos_DzIter_one_shift_two_le hk h

end Work.FTS.EllipticEst.Cores.Pieces.TL2
