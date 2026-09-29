/-
# `expLocAEpos_of_regFamily`: the patching step of C16 (AJ §9)

The multiscale regularity output `P_RegFamily` (AJ §9, Lemmas 9.4/9.5) says that for
`DiophBelow α b₀` and `lam > e^{16 b₀/9}`, outside the null set `Theta α` of phases every
generalized eigenfunction with `u 0 ≠ 0` gives rise to a regularity family
`RegFamily α lam θ E` (all sufficiently large sites are `(L₁, ≥q)`-regular for every `q`).

This file turns that into the a.e. exponential localisation statement `ExpLocAEpos`:

* `regular_step_data` turns the regularity family at scale `q` into the one-step Poisson
  contraction `‖u z‖ ≤ wl z ‖u(left z)‖ + wr z ‖u(right z)‖` at every site `z > b`, with
  children at distance `≥ q/40 + 1` and step weights `≤ exp (-(L₁ · (distance - 1)))`;
* `tree_estimate` (AJ §9.1 block-resolvent expansion, in abstract branching-system form)
  then propagates this contraction along the `2^s`-branching tree and yields exponential
  decay at the rate `(L₁ q/40 − log 2)/(q/40 + 1) > 0`, which is positive exactly when
  `40 log 2 < L₁ q` — a condition we are free to satisfy, since `RegFamily` supplies *every*
  scale `q > 0`;
* a.e. phase has *all* its translates `θ + y α` outside `Theta α` (`Basic.theta_null` plus
  translation invariance of Lebesgue measure), and since a nonzero solution cannot vanish on
  all of `{n ≤ 0}`, we may translate `u` to a *nonpositive* site `y ≤ 0` with `u y ≠ 0`, so
  `P_RegFamily` applies at the shifted phase and its decay on `k ≥ 0` transfers back to `u`
  on all of `k ≥ 0`.
-/
import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.theta_null
import Submission.Work.TMC16Core.Basic.genEigen_mem_spec
import Submission.Work.TMC16Core.Basic.genEigen_translate
import Submission.Work.TMC16Core.Basic.poisson_bound
import Submission.Work.TMC16Core.Basic.patching
import Submission.Work.TMC16Core.Basic.expDecay_of_eventual

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC16Core.Main

/-- The exceptional set `Theta α` is invariant (in measure) under the translations
`θ ↦ θ + y α`, `y : ℤ`.  Consequently, if `Theta α` is null, then a.e. phase `θ` has
*every* translate `θ + y α` outside `Theta α` (a countable intersection of full measure
sets). -/
theorem ae_forall_shift_notMem_Theta {α : ℝ}
    (hnull : (MeasureTheory.volume : Measure ℝ) (Work.TMC16Core.Theta α) = 0) :
    ∀ᵐ θ ∂(MeasureTheory.volume : Measure ℝ),
      ∀ y : ℤ, θ + (y : ℝ) * α ∉ Work.TMC16Core.Theta α := by
  have h : (MeasureTheory.volume : Measure ℝ)
      (⋃ y : ℤ, {θ : ℝ | θ + (y : ℝ) * α ∈ Work.TMC16Core.Theta α}) = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro y
    have hpre := MeasureTheory.measure_preimage_add_right (MeasureTheory.volume : Measure ℝ)
      ((y : ℝ) * α) (Work.TMC16Core.Theta α)
    have hset : (fun h : ℝ => h + (y : ℝ) * α) ⁻¹' Work.TMC16Core.Theta α
        = {θ : ℝ | θ + (y : ℝ) * α ∈ Work.TMC16Core.Theta α} := rfl
    rw [hset] at hpre
    rw [hpre, hnull]
  rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with θ hθ y hy
  exact hθ (Set.mem_iUnion.mpr ⟨y, hy⟩)

/-- A nonzero formal solution of the almost Mathieu equation cannot vanish on all of
`{n ≤ 0}`: the recurrence `u_{n+1} = (E − v_n) u_n − u_{n−1}` propagates `u = 0` forward
from `u 0 = u (−1) = 0`.  Hence there is a *nonpositive* site where `u` does not vanish. -/
theorem exists_nonpos_ne_zero {α lam θ E : ℝ} {u : ℤ → ℂ} (hu_ne : u ≠ 0)
    (hu_eq : ∀ n : ℤ, Work.TMC16Core.amoAct α lam θ u n = (E : ℂ) * u n) :
    ∃ y : ℤ, y ≤ 0 ∧ u y ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_ne_iff] at hcon
  apply hu_ne
  funext n
  by_cases hn : n ≤ 0
  · exact hcon n hn
  · have hn' : 0 < n := by omega
    have hbase0 : u 0 = 0 := hcon 0 le_rfl
    have hbasem1 : u (-1) = 0 := hcon (-1) (by norm_num)
    have hnonneg : ∀ m : ℕ, u (m : ℤ) = 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h j ih =>
        rcases j with _ | m
        · simpa using hbase0
        · have hm : u ((m : ℤ)) = 0 := ih m (Nat.lt_succ_self m)
          have hm1 : u ((m : ℤ) - 1) = 0 := by
            rcases m with _ | m
            · simpa using hbasem1
            · have hcast : (((m + 1 : ℕ) : ℤ)) - 1 = (m : ℤ) := by omega
              rw [hcast]
              exact ih m (by omega)
          have heq := hu_eq (m : ℤ)
          simp only [Work.TMC16Core.amoAct] at heq
          rw [hm, hm1] at heq
          have hzero : u ((m : ℤ) + 1) = 0 := by simpa using heq
          rwa [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by omega] at hzero
    have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn')
    rw [← hcast]
    exact hnonneg n.toNat

/-- **One-step patching data (AJ §9).**  From the regularity family at scale `q` we extract
two maps `left`, `right` (the neighbours, outside the interval, of its two endpoints) and
weights `wl`, `wr` with:

* `left z` and `right z` are at distance `≥ q/40 + 1` from `z` (`IsRegularBig`'s `1/40`
  margins together with `x₁ ≤ z ≤ x₂`, the extra `1` being the step from an endpoint to the
  neighbouring site outside the interval);
* the weights are bounded by `exp (-(L₁ · (distance - 1)))` (the Green's function bounds);
* at every active site `z > b`, `u` satisfies the one-step Poisson contraction
  `‖u z‖ ≤ wl z ‖u (left z)‖ + wr z ‖u (right z)‖`.

This is the input of the abstract branching estimate `Basic.tree_estimate`. -/
theorem regular_step_data {α lam : ℝ} {θ : ℝ} {E : ℂ} {L₁ q b : ℝ} {u : ℤ → ℂ}
    (hfam : ∀ y : ℤ, b < (y : ℝ) →
      Work.TMC16Core.IsRegularBig α lam θ E L₁ q y)
    (hsol : Work.TMC16Core.IsFormalSol α lam θ E u) :
    ∃ (left right : ℤ → ℤ) (wl wr : ℤ → ℝ),
      (∀ z : ℤ, 0 ≤ wl z) ∧ (∀ z : ℤ, 0 ≤ wr z) ∧
      (∀ z : ℤ, q / 40 + 1 ≤ (((z - left z : ℤ)) : ℝ)) ∧
      (∀ z : ℤ, q / 40 + 1 ≤ (((right z - z : ℤ)) : ℝ)) ∧
      (∀ z : ℤ, wl z ≤ Real.exp (-(L₁ * ((((z - left z : ℤ)) : ℝ) - 1)))) ∧
      (∀ z : ℤ, wr z ≤ Real.exp (-(L₁ * ((((right z - z : ℤ)) : ℝ) - 1)))) ∧
      (∀ z : ℤ, b < (z : ℝ) → ‖u z‖ ≤ wl z * ‖u (left z)‖ + wr z * ‖u (right z)‖) := by
  classical
  -- cutoff used for the (irrelevant) data at inactive sites
  set N : ℤ := ⌈q / 40⌉ + 1 with hNdef
  have hNq : q / 40 ≤ ((N : ℤ) : ℝ) := by
    have h1 : q / 40 ≤ (((⌈q / 40⌉ : ℤ)) : ℝ) := Int.le_ceil (q / 40)
    have h2 : (((N : ℤ)) : ℝ) = (((⌈q / 40⌉ : ℤ)) : ℝ) + 1 := by
      rw [hNdef]; push_cast; ring
    rw [h2]; linarith
  -- the two endpoints of the regularity interval, chosen for every site
  let A : ℤ → ℤ := fun z => if h : b < (z : ℝ) then Classical.choose (hfam z h) else z - N
  let B : ℤ → ℤ := fun z =>
    if h : b < (z : ℝ) then Classical.choose (Classical.choose_spec (hfam z h)) else z + N
  have hspec : ∀ z : ℤ, ∀ hz : b < (z : ℝ),
      A z ≤ z ∧ z ≤ B z ∧
      (40 : ℝ) * (((z - A z : ℤ)) : ℝ) ≥ q ∧
      (40 : ℝ) * (((B z - z : ℤ)) : ℝ) ≥ q ∧
      (Work.TMC16Core.dirMat α lam (θ + ((A z : ℝ)) * α) E
          ((B z - A z + 1).toNat)).det ≠ 0 ∧
      ‖Work.TMC16Core.G α lam θ E (A z) (B z) z (A z)‖
        < Real.exp (-(L₁ * (((z - A z : ℤ)) : ℝ))) ∧
      ‖Work.TMC16Core.G α lam θ E (A z) (B z) z (B z)‖
        < Real.exp (-(L₁ * (((B z - z : ℤ)) : ℝ))) := by
    intro z hz
    have hA : A z = Classical.choose (hfam z hz) := by simp only [A, dif_pos hz]
    have hB : B z = Classical.choose (Classical.choose_spec (hfam z hz)) := by
      simp only [B, dif_pos hz]
    have h := Classical.choose_spec (Classical.choose_spec (hfam z hz))
    rw [hA, hB]
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := h
    exact ⟨g1, g2, le_trans g3 g4, le_trans g3 g5, g6, g7, g8⟩
  have hcastL : ∀ z : ℤ, (((z - (A z - 1) : ℤ)) : ℝ) = ((z - A z : ℤ) : ℝ) + 1 := by
    intro z; push_cast; ring
  have hcastR : ∀ z : ℤ, (((B z + 1 - z : ℤ)) : ℝ) = ((B z - z : ℤ) : ℝ) + 1 := by
    intro z; push_cast; ring
  refine ⟨(fun z : ℤ => A z - 1), (fun z : ℤ => B z + 1),
    (fun z : ℤ => if h : b < (z : ℝ) then ‖Work.TMC16Core.G α lam θ E (A z) (B z) z (A z)‖
      else Real.exp (-(L₁ * (N : ℝ)))),
    (fun z : ℤ => if h : b < (z : ℝ) then ‖Work.TMC16Core.G α lam θ E (A z) (B z) z (B z)‖
      else Real.exp (-(L₁ * (N : ℝ)))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `wl ≥ 0`
    intro z
    by_cases h : b < (z : ℝ)
    · simp only [dif_pos h]; positivity
    · simp only [dif_neg h]; positivity
  · -- `wr ≥ 0`
    intro z
    by_cases h : b < (z : ℝ)
    · simp only [dif_pos h]; positivity
    · simp only [dif_neg h]; positivity
  · -- distance from `z` to the left child
    intro z
    by_cases h : b < (z : ℝ)
    · have hs := hspec z h
      have h2 : q / 40 ≤ ((z - A z : ℤ) : ℝ) := by linarith [hs.2.2.1]
      simp only [dif_pos h, hcastL z]
      linarith
    · have h1 : z - (A z - 1) = N + 1 := by simp only [A, dif_neg h]; ring
      simp only [dif_neg h]
      rw [h1]
      push_cast
      linarith
  · -- distance from `z` to the right child
    intro z
    by_cases h : b < (z : ℝ)
    · have hs := hspec z h
      have h2 : q / 40 ≤ ((B z - z : ℤ) : ℝ) := by linarith [hs.2.2.2.1]
      simp only [dif_pos h, hcastR z]
      linarith
    · have h1 : B z + 1 - z = N + 1 := by simp only [B, dif_neg h]; ring
      simp only [dif_neg h]
      rw [h1]
      push_cast
      linarith
  · -- decay bound for `wl`
    intro z
    by_cases h : b < (z : ℝ)
    · have hs := hspec z h
      have h7 := hs.2.2.2.2.2.1
      have hc : ((((z - A z : ℤ)) : ℝ) + 1) - 1 = ((z - A z : ℤ) : ℝ) := by ring
      simp only [dif_pos h, hcastL z]
      rw [hc]
      exact le_of_lt h7
    · have h1 : z - (A z - 1) = N + 1 := by simp only [A, dif_neg h]; ring
      simp only [dif_neg h]
      rw [h1]
      push_cast
      simp
  · -- decay bound for `wr`
    intro z
    by_cases h : b < (z : ℝ)
    · have hs := hspec z h
      have h8 := hs.2.2.2.2.2.2
      have hc : ((((B z - z : ℤ)) : ℝ) + 1) - 1 = ((B z - z : ℤ) : ℝ) := by ring
      simp only [dif_pos h, hcastR z]
      rw [hc]
      exact le_of_lt h8
    · have h1 : B z + 1 - z = N + 1 := by simp only [B, dif_neg h]; ring
      simp only [dif_neg h]
      rw [h1]
      push_cast
      simp
  · -- the one-step Poisson contraction
    intro z hz
    have hs := hspec z hz
    have hp := Work.TMC16Core.Basic.poisson_bound (x₁ := A z) (x₂ := B z) (y := z)
      hsol hs.2.2.2.2.1 hs.1 hs.2.1
    simp only [dif_pos hz]
    exact hp

theorem expLocAEpos_of_regFamily (h0 : Work.TMC16Core.P_UniqErg) (h1 : Work.TMC16Core.P_OpBasics)
    (h4 : Work.TMC16Core.P_LEBasics) (h7 : Work.TMC16Core.P_BJ_dioph)
    (hReg : Work.TMC16Core.P_RegFamily) :
    ∀ α b₀ lam : ℝ, Irrational α → 0 ≤ b₀ → Work.TMC16Core.DiophBelow α b₀ →
      Real.exp (16 * b₀ / 9) < lam → Work.TMC16Core.ExpLocAEpos α lam := by
  intro α b₀ lam hα hb₀ hdioph hlam
  -- a.e. phase has all its translates outside `Theta α`
  have hae := ae_forall_shift_notMem_Theta (Work.TMC16Core.Basic.theta_null α hα)
  rw [Work.TMC16Core.ExpLocAEpos]
  filter_upwards [hae] with θ hθ E u hu
  obtain ⟨hu_ne, hu_eq, C₀, hC₀⟩ := hu
  -- translate the solution to a nonpositive site where it does not vanish
  obtain ⟨y, hy0, hyne⟩ := exists_nonpos_ne_zero hu_ne hu_eq
  have hu' : Work.TMC16Core.IsGenEigen α lam θ E u := ⟨hu_ne, hu_eq, C₀, hC₀⟩
  have hv : Work.TMC16Core.IsGenEigen α lam (θ + (y : ℝ) * α) E (fun n => u (n + y)) :=
    Work.TMC16Core.Basic.genEigen_translate y hu'
  have hv0 : (fun n : ℤ => u (n + y)) 0 ≠ 0 := by simpa using hyne
  -- `E` is a generalized eigenvalue, hence in the spectrum
  have hE : E ∈ Work.TMC16Core.amoSpec α lam :=
    Work.TMC16Core.Basic.genEigen_mem_spec h1 hα hu'
  -- `P_RegFamily` at the shifted phase
  obtain ⟨L₁, hL₁, hfam⟩ :=
    hReg α b₀ lam hα hb₀ hdioph hlam E hE (θ + (y : ℝ) * α) (hθ y)
      (fun n => u (n + y)) hv hv0
  -- pick a scale satisfying the counting condition of the patching lemma
  obtain ⟨q, hq, hcount⟩ : ∃ q : ℝ, 0 < q ∧ 200 * L₁ + 200 * Real.log 2 < L₁ * q := by
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨(200 * L₁ + 200 * Real.log 2 + 1) / L₁, div_pos (by linarith) hL₁, ?_⟩
    rw [mul_div_cancel₀ _ (ne_of_gt hL₁)]
    linarith
  obtain ⟨b, hb⟩ := hfam q hq
  -- polynomial bound for the translate
  have hCpos : 0 < max C₀ 1 * (1 + |(y : ℝ)|) :=
    mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (by positivity)
  have hvpol : ∀ n : ℤ,
      ‖(fun n : ℤ => u (n + y)) n‖ ≤ (max C₀ 1 * (1 + |(y : ℝ)|)) * (1 + |(n : ℝ)|) := by
    intro n
    have h1n := hC₀ (n + y)
    have hxy : (1 : ℝ) + |(((n + y : ℤ)) : ℝ)| ≤ (1 + |(y : ℝ)|) * (1 + |(n : ℝ)|) := by
      have habs : |((n : ℝ) + (y : ℝ))| ≤ |(n : ℝ)| + |(y : ℝ)| := abs_add_le _ _
      have hcast : (((n + y : ℤ)) : ℝ) = (n : ℝ) + (y : ℝ) := by push_cast; ring
      rw [hcast]
      nlinarith [abs_nonneg (n : ℝ), abs_nonneg (y : ℝ)]
    have hmaxpos : (0 : ℝ) ≤ max C₀ 1 := le_trans zero_le_one (le_max_right _ _)
    calc ‖u (n + y)‖ ≤ C₀ * (1 + |(((n + y : ℤ)) : ℝ)|) := h1n
      _ ≤ max C₀ 1 * ((1 + |(y : ℝ)|) * (1 + |(n : ℝ)|)) :=
          mul_le_mul (le_max_left _ _) hxy (by positivity) hmaxpos
      _ = max C₀ 1 * (1 + |(y : ℝ)|) * (1 + |(n : ℝ)|) := by ring
  have hvsol : Work.TMC16Core.IsFormalSol α lam (θ + (y : ℝ) * α) ((E : ℝ) : ℂ)
      (fun n => u (n + y)) := hv.2.1
  -- the patching estimate (AJ §9.1) for the translate
  obtain ⟨K, hK⟩ := Work.TMC16Core.Basic.patching hL₁ hq hCpos hcount
    (fun y' hy' => hb y' hy') hvsol hvpol
  -- transfer the estimate back to `u`: for `k ≥ K + y` we have `k - y ≥ K ≥ 0`, and
  -- `y ≤ 0` makes `exp ((4 L₁/5) y) ≤ 1`
  have hcl : 0 < 4 * L₁ / 5 := by linarith
  have hev : ∃ K' : ℝ, ∀ k : ℤ, K' ≤ (k : ℝ) →
      ‖u k‖ ≤ Real.exp (-((4 * L₁ / 5) * (k : ℝ))) := by
    refine ⟨K + (y : ℝ), fun k hk => ?_⟩
    have hkK : K ≤ (((k - y : ℤ)) : ℝ) := by
      have h1 : K + (y : ℝ) ≤ (k : ℝ) := hk
      push_cast
      linarith
    have h2 := hK (k - y) hkK
    rw [show k - y + y = k from by ring] at h2
    have hcast : (((k - y : ℤ)) : ℝ) = (k : ℝ) - (y : ℝ) := by push_cast; ring
    rw [hcast] at h2
    have hy : (y : ℝ) ≤ 0 := by exact_mod_cast hy0
    have hexpy : Real.exp ((4 * L₁ / 5) * (y : ℝ)) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [hcl, hy]
    calc ‖u k‖ ≤ Real.exp (-(4 * L₁ / 5) * ((k : ℝ) - (y : ℝ))) := h2
      _ = Real.exp (-((4 * L₁ / 5) * (k : ℝ))) * Real.exp ((4 * L₁ / 5) * (y : ℝ)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-((4 * L₁ / 5) * (k : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left hexpy (Real.exp_pos _).le
      _ = Real.exp (-((4 * L₁ / 5) * (k : ℝ))) := by ring
  -- finitely many sites below `K + y` are absorbed by the polynomial bound
  obtain ⟨K', hK'⟩ := hev
  exact Work.TMC16Core.Basic.expDecay_of_eventual hcl hC₀ hK'

end Work.TMC16Core.Main
