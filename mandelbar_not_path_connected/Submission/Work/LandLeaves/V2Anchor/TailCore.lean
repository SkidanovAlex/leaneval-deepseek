import Mathlib
import Submission.Work.LandLeaves.V2Anchor.Helpers
import Submission.Work.LandLeaves.fundamental_bead_shrink
import Submission.Work.LandLeaves.image_subset_paramRay_of_connected
import Submission.Work.ELTop.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-! Clash-free copy of `exists_backward_orbit_tail_core` (see `V2Anchor/Helpers.lean`): the
original imports `AnchorHelpers` for the level sequence and the ray-level lemmas, which are
declared here under `Work.LandLeaves.V2Anchor`. -/

/-!
# The backward orbit of beads through a repelling point

This is the *core* of the backward-orbit construction of the landing theorem for a repelling
periodic point `y` of the antiholomorphic quadratic family `T_c`.

Suppose `g` is the contracting local inverse branch of `τ = (T_c)^{2k}` on the ball
`B(y, r')` (`τ (g w) = w`, `‖g w - y‖ ≤ κ‖w - y‖`, `κ < 1`), and that one *fundamental bead*
`R(θ₀)|[r₀, r₀^{4^k}]` of the dynamical ray of angle `θ₀` lies in `B(y, r')`
(`hseed`).  Then there is a sequence of angles `θ : ℕ → ℝ` with `θ 0 = θ₀`, with
`4^k θ (n+1) ≡ θ n (mod 1)` (`θ` is a backward orbit of the angle-doubling map), and such that
the level window `[λ(m), λ(m)^{4^k}]` of the `n`-th ray lies in `B(y, κ^m r')` for every
`m ≤ n` — the *uniform* window estimate which makes the rays shrink to `y`.

Route: the `g`-image of a bead in `B(y, r')` is again contained in a single ray
(`image_subset_paramRay_of_connected`), with the angle transformation `4^k θ' = θ + m`; the
one-step bead bound (`step_bead_subset`) shows the window of the new ray again lies in
`B(y, r')`; and reading the identity `rayPt (θ n) s = g^[m] (rayPt (θ (n-m)) (s^{D^m}))` on the
windows together with the contraction of `g` gives the bound `κ^m r'`.
-/

namespace Work.LandLeaves.V2Anchor

noncomputable section

open Classical Filter Set
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

set_option linter.unusedVariables false

variable {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}

/-! ## Elementary facts about beads -/

private theorem bead_preconnected {hN : Work.EL.DynB c φ} {θ a b : ℝ} (ha : 1 < a) :
    IsPreconnected (Work.EL.rayPt hN θ '' Set.Icc a b) := by
  have hcont : ContinuousOn (fun t : ℝ => Work.EL.rayPt hN θ t) (Set.Icc a b) :=
    (Work.Top.continuousOn_rayPt hN θ).mono (fun t ht => lt_of_lt_of_le ha ht.1)
  exact isPreconnected_Icc.image _ hcont

private theorem bead_subset_paramRay {hN : Work.EL.DynB c φ} {θ a b : ℝ} (ha : 1 < a) :
    Work.EL.rayPt hN θ '' Set.Icc a b ⊆ Work.EL.paramRay hN θ := by
  rintro _ ⟨s, hs, rfl⟩
  exact Work.EL.rayPt_mem_paramRay hN (lt_of_lt_of_le ha hs.1)

private theorem bead_subset_Kc {hN : Work.EL.DynB c φ} {θ a b : ℝ} (ha : 1 < a) :
    Work.EL.rayPt hN θ '' Set.Icc a b ⊆ (Work.EL.K c)ᶜ :=
  fun z hz => Work.EL.paramRay_subset_compl hN θ (bead_subset_paramRay ha hz)

/-- If `w` is not in the filled Julia set and `τ (g w) = w`, then `g w` is not in the filled
Julia set either (`K c` is forward invariant under `τ`). -/
private theorem notMem_K_of_g {g : ℂ → ℂ} {w : ℂ}
    (hw : w ∉ Work.EL.K c) (h : (Tantibar c)^[2 * k] (g w) = w) : g w ∉ Work.EL.K c := by
  intro hgw
  have h2 := K_iterate_mem hgw (2 * k)
  rw [h] at h2
  exact hw h2

/-- Iterated contraction estimate. -/
private theorem iterate_contract {g : ℂ → ℂ} {κ r' : ℝ} {y : ℂ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcontr : ∀ w : ℂ, ‖w - y‖ ≤ r' → ‖g w - y‖ ≤ κ * ‖w - y‖)
    {w : ℂ} (hw : ‖w - y‖ ≤ r') (j : ℕ) :
    ‖(g^[j]) w - y‖ ≤ κ ^ j * ‖w - y‖ := by
  induction j with
  | zero => simp
  | succ i ih =>
      have hκnn : (0:ℝ) ≤ κ := hκ0
      have hκpow : κ ^ i * ‖w - y‖ ≤ r' := by
        have h1 : κ ^ i ≤ 1 := pow_le_one₀ hκnn hκ1
        nlinarith [norm_nonneg (w - y)]
      rw [Function.iterate_succ_apply']
      calc ‖g ((g^[i]) w) - y‖ ≤ κ * ‖(g^[i]) w - y‖ :=
            hcontr _ (le_trans ih hκpow)
        _ ≤ κ * (κ ^ i * ‖w - y‖) := by
            exact mul_le_mul_of_nonneg_left ih hκnn
        _ = κ ^ (i + 1) * ‖w - y‖ := by rw [pow_succ]; ring

/-! ## The one-step bead bound -/

/-- **The one-step bead bound.**  If the bead `R(θ)|[λ(n), r₀^D]` lies in the ball `B(y,r')`, then
the `g`-image of that bead is contained in a single ray `R(θ')`, and the bead
`R(θ')|[λ(n+1), r₀^D]` again lies in `B(y,r')`. -/
private theorem step_bead_subset
    {g : ℂ → ℂ} {r' κ ε r₀ ρ : ℝ} {D : ℕ} {hN : Work.EL.DynB c φ}
    (hφ : Work.ParamRays.IsDynBottcher c φ)
    (hr' : 0 < r') (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hcontr : ∀ w : ℂ, ‖w - y‖ ≤ r' → ‖g w - y‖ ≤ κ * ‖w - y‖)
    (hright : ∀ w : ℂ, ‖w - y‖ ≤ r' → (Tantibar c)^[2 * k] (g w) = w)
    (hD2 : 2 ≤ D) (hDeq : D = 4 ^ k)
    (hr₀ : 1 < r₀) (hr₀ρ : r₀ < ρ)
    (hρshr : ∀ θ t : ℝ, 1 < t → t < ρ → ∀ s₁ s₂ : ℝ, t ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t ^ D →
      ‖Work.EL.rayPt hN θ s₂ - Work.EL.rayPt hN θ s₁‖ ≤ ε)
    (hεsmall : ε + κ * r' < r')
    (n : ℕ) (θ θ' : ℝ)
    (hθ : Work.EL.rayPt hN θ '' Set.Icc (lvlSeq r₀ D n) (r₀ ^ D) ⊆ Metric.ball y r')
    (himg : g '' (Work.EL.rayPt hN θ '' Set.Icc (lvlSeq r₀ D n) (r₀ ^ D)) ⊆
      Work.EL.paramRay hN θ') :
    Work.EL.rayPt hN θ' '' Set.Icc (lvlSeq r₀ D (n + 1)) (r₀ ^ D) ⊆ Metric.ball y r' := by
  intro z hz
  obtain ⟨s, hs, rfl⟩ := hz
  rw [Metric.mem_ball, dist_eq_norm]
  have hr₀nn : 0 ≤ r₀ := le_of_lt (lt_trans zero_lt_one hr₀)
  have hDne : D ≠ 0 := by omega
  have hs1 : 1 < s := lt_of_lt_of_le (lvlSeq_one_lt hr₀ hD2 (n + 1)) hs.1
  have hspos : 0 ≤ s := le_of_lt (lt_trans zero_lt_one hs1)
  by_cases hsle : s ≤ r₀
  · -- `s ≤ r₀`: the point is the `g`-image of a point of the old bead
    have hpowmem : s ^ D ∈ Set.Icc (lvlSeq r₀ D n) (r₀ ^ D) := by
      refine ⟨?_, pow_le_pow_left₀ hspos hsle D⟩
      rw [← lvlSeq_pow hr₀nn hDne n]
      exact pow_le_pow_left₀ (le_of_lt (lt_trans zero_lt_one (lvlSeq_one_lt hr₀ hD2 (n + 1)))) hs.1 D
    have hsD1 : 1 < s ^ D := one_lt_pow₀ hs1 (by omega)
    set w : ℂ := Work.EL.rayPt hN θ (s ^ D) with hw
    have hwK : w ∉ Work.EL.K c := Work.EL.rayPt_notMem_K hN hsD1
    have hwball : w ∈ Metric.ball y r' := hθ ⟨s ^ D, hpowmem, rfl⟩
    have hwd : ‖w - y‖ ≤ r' := le_of_lt (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hwball)
    have hgwK : g w ∉ Work.EL.K c := notMem_K_of_g hwK (hright w hwd)
    have hgwP : g w ∈ Work.EL.paramRay hN θ' := himg ⟨w, ⟨s ^ D, hpowmem, rfl⟩, rfl⟩
    have hlevw : ‖φ w‖ = s ^ D := by rw [hw]; exact norm_phi_rayPt hsD1
    have hlev : ‖φ (g w)‖ = s := by
      have hp := norm_phi_g hφ hright hwd hgwK
      rw [hlevw, hDeq] at hp
      exact (pow_left_inj₀ (norm_nonneg _) hspos (by positivity : 4 ^ k ≠ 0)).mp hp
    rw [← eq_rayPt_of_level hgwK hs1 hgwP hlev]
    calc ‖g w - y‖ ≤ κ * ‖w - y‖ := hcontr w hwd
      _ ≤ κ * r' := mul_le_mul_of_nonneg_left hwd hκ0
      _ < r' := by nlinarith [hr']
  · -- `r₀ < s`: use the base point and the shrinking of the fundamental bead
    push Not at hsle
    have hbasemem : r₀ ^ D ∈ Set.Icc (lvlSeq r₀ D n) (r₀ ^ D) := by
      refine ⟨?_, le_refl _⟩
      calc lvlSeq r₀ D n ≤ lvlSeq r₀ D 0 := lvlSeq_mono hr₀ hD2 (Nat.zero_le n)
        _ = r₀ := lvlSeq_zero r₀ D
        _ ≤ r₀ ^ D := by
            calc r₀ = r₀ ^ 1 := (pow_one _).symm
              _ ≤ r₀ ^ D := pow_le_pow_right₀ (le_of_lt hr₀) (by omega)
    set w₀ : ℂ := Work.EL.rayPt hN θ (r₀ ^ D) with hw₀
    have hw₀K : w₀ ∉ Work.EL.K c := Work.EL.rayPt_notMem_K hN (one_lt_pow₀ hr₀ (by omega))
    have hw₀ball : w₀ ∈ Metric.ball y r' := hθ ⟨r₀ ^ D, hbasemem, rfl⟩
    have hw₀d : ‖w₀ - y‖ ≤ r' :=
      le_of_lt (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw₀ball)
    have hgw₀K : g w₀ ∉ Work.EL.K c := notMem_K_of_g hw₀K (hright w₀ hw₀d)
    have hgw₀P : g w₀ ∈ Work.EL.paramRay hN θ' := himg ⟨w₀, ⟨r₀ ^ D, hbasemem, rfl⟩, rfl⟩
    have hlev₀w : ‖φ w₀‖ = r₀ ^ D := by
      rw [hw₀]; exact norm_phi_rayPt (one_lt_pow₀ hr₀ (by omega))
    have hlev₀ : ‖φ (g w₀)‖ = r₀ := by
      have hp := norm_phi_g hφ hright hw₀d hgw₀K
      rw [hlev₀w, hDeq] at hp
      exact (pow_left_inj₀ (norm_nonneg _) hr₀nn (by positivity : 4 ^ k ≠ 0)).mp hp
    have hbase : Work.EL.rayPt hN θ' r₀ = g w₀ :=
      (eq_rayPt_of_level hgw₀K hr₀ hgw₀P hlev₀).symm
    have hbased : ‖Work.EL.rayPt hN θ' r₀ - y‖ ≤ κ * r' := by
      rw [hbase]
      calc ‖g w₀ - y‖ ≤ κ * ‖w₀ - y‖ := hcontr w₀ hw₀d
        _ ≤ κ * r' := mul_le_mul_of_nonneg_left hw₀d hκ0
    have hshrink := hρshr θ' r₀ hr₀ hr₀ρ r₀ s le_rfl (le_of_lt hsle) hs.2
    calc ‖Work.EL.rayPt hN θ' s - y‖
        ≤ ‖Work.EL.rayPt hN θ' s - Work.EL.rayPt hN θ' r₀‖ + ‖Work.EL.rayPt hN θ' r₀ - y‖ := by
          rw [show Work.EL.rayPt hN θ' s - y
              = (Work.EL.rayPt hN θ' s - Work.EL.rayPt hN θ' r₀)
                + (Work.EL.rayPt hN θ' r₀ - y) from by ring]
          exact norm_add_le _ _
      _ ≤ ε + κ * r' := add_le_add hshrink hbased
      _ < r' := hεsmall

/-! ## The backward orbit -/

/-- **The backward orbit of beads, with the uniform window estimate.**  This is the target
statement with the exponent `D` kept general (it is instantiated at `D = 4 ^ k`). -/
private theorem exists_backward_orbit_tail_core_aux {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hN : Work.EL.DynB c φ)
    (hrep : Work.Landing.IsRepelling c k y)
    {r' κ ε ρ r₀ : ℝ} {g : ℂ → ℂ} {D : ℕ}
    (hr' : 0 < r') (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hgy : g y = y) (hcont : ContinuousOn g (Metric.ball y r'))
    (hcontr : ∀ w : ℂ, ‖w - y‖ ≤ r' → ‖g w - y‖ ≤ κ * ‖w - y‖)
    (hright : ∀ w : ℂ, ‖w - y‖ ≤ r' →
      (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (g w) = w)
    (hεsmall : ε + κ * r' < r')
    (hD2 : 2 ≤ D) (hDeq : D = 4 ^ k)
    (hρshr : ∀ θ t : ℝ, 1 < t → t < ρ → ∀ s₁ s₂ : ℝ, t ≤ s₁ → s₁ ≤ s₂ →
      s₂ ≤ t ^ D → ‖Work.EL.rayPt hN θ s₂ - Work.EL.rayPt hN θ s₁‖ ≤ ε)
    (hr₀ : 1 < r₀) (hr₀ρ : r₀ < ρ) {θ₀ : ℝ}
    (hseed : Work.EL.rayPt hN θ₀ '' Set.Icc r₀ (r₀ ^ D) ⊆ Metric.ball y r') :
    ∃ θ : ℕ → ℝ, θ 0 = θ₀ ∧
      (∀ n : ℕ, ∃ m : ℤ, (4 : ℝ) ^ k * θ (n + 1) = θ n + m) ∧
      (∀ m n : ℕ, m ≤ n → ∀ s : ℝ,
        s ∈ Set.Icc (lvlSeq r₀ D m) ((lvlSeq r₀ D m) ^ D) →
        ‖Work.EL.rayPt hN (θ n) s - y‖ ≤ κ ^ m * r') := by
  classical
  have hDne : D ≠ 0 := by omega
  let P : ℕ → ℝ → Prop := fun n θ =>
    Work.EL.rayPt hN θ '' Set.Icc (lvlSeq r₀ D n) (r₀ ^ D) ⊆ Metric.ball y r'
  have hP0 : P 0 θ₀ := by
    show Work.EL.rayPt hN θ₀ '' Set.Icc (lvlSeq r₀ D 0) (r₀ ^ D) ⊆ Metric.ball y r'
    rw [lvlSeq_zero]
    exact hseed
  have branchEx : ∀ (n : ℕ) (θ : ℝ), P n θ → ∃ θ' : ℝ,
      (g '' (Work.EL.rayPt hN θ '' Set.Icc (lvlSeq r₀ D n) (r₀ ^ D)) ⊆
        Work.EL.paramRay hN θ') ∧
      (∃ m : ℤ, (4 : ℝ) ^ k * θ' = θ + m) := by
    intro n θ hθ
    have h1 : 1 < lvlSeq r₀ D n := lvlSeq_one_lt hr₀ hD2 n
    obtain ⟨θ', hθ', hm⟩ := image_subset_paramRay_of_connected (hN := hN) hφ hrep hr'
      hgy hcont hright (C := Work.EL.rayPt hN θ '' Set.Icc (lvlSeq r₀ D n) (r₀ ^ D))
      (bead_subset_Kc h1) hθ (bead_preconnected h1) (bead_subset_paramRay h1)
    exact ⟨θ', hθ', hm⟩
  let stepFun : ∀ (n : ℕ), {θ : ℝ // P n θ} → {θ' : ℝ // P (n+1) θ'} := fun n a =>
    ⟨Classical.choose (branchEx n a.1 a.2),
     step_bead_subset hφ hr' hκ0 hκ1 hcontr hright hD2 hDeq hr₀ hr₀ρ hρshr hεsmall n a.1
       (Classical.choose (branchEx n a.1 a.2)) a.2
       (Classical.choose_spec (branchEx n a.1 a.2)).1⟩
  let aux : (n : ℕ) → {θ : ℝ // P n θ} := fun n =>
    Nat.rec (motive := fun n => {θ : ℝ // P n θ}) ⟨θ₀, hP0⟩ (fun m ih => stepFun m ih) n
  let θf : ℕ → ℝ := fun n => (aux n).1
  have hPf : ∀ n, P n (θf n) := fun n => (aux n).2
  have aux_succ : ∀ n, aux (n+1) = stepFun n (aux n) := fun n => rfl
  have branch_rel : ∀ n, g '' (Work.EL.rayPt hN (θf n) '' Set.Icc (lvlSeq r₀ D n) (r₀ ^ D))
      ⊆ Work.EL.paramRay hN (θf (n+1)) := by
    intro n
    have hval : θf (n+1) = Classical.choose (branchEx n (θf n) (hPf n)) := by
      show (aux (n+1)).1 = _
      rw [aux_succ n]
    rw [hval]
    exact (Classical.choose_spec (branchEx n (θf n) (hPf n))).1
  have branch_cong : ∀ n, ∃ m : ℤ, (4 : ℝ) ^ k * θf (n + 1) = θf n + m := by
    intro n
    have hval : θf (n+1) = Classical.choose (branchEx n (θf n) (hPf n)) := by
      show (aux (n+1)).1 = _
      rw [aux_succ n]
    rw [hval]
    exact (Classical.choose_spec (branchEx n (θf n) (hPf n))).2
  -- one-step relation between the rays
  have Crel : ∀ n, 1 ≤ n → ∀ s : ℝ, lvlSeq r₀ D n ≤ s → s ≤ r₀ →
      Work.EL.rayPt hN (θf n) s = g (Work.EL.rayPt hN (θf (n-1)) (s ^ D)) := by
    intro n hn s hs1 hs2
    have hs1' : 1 < s := lt_of_lt_of_le (lvlSeq_one_lt hr₀ hD2 n) hs1
    have hsD1 : 1 < s ^ D := one_lt_pow₀ hs1' (by omega)
    have hmem : s ^ D ∈ Set.Icc (lvlSeq r₀ D (n-1)) (r₀ ^ D) := by
      constructor
      · have h := lvlSeq_pow (le_of_lt (lt_trans zero_lt_one hr₀)) hDne (n-1)
        rw [show n - 1 + 1 = n from by omega] at h
        rw [← h]
        exact pow_le_pow_left₀ (le_of_lt (lt_trans zero_lt_one (lvlSeq_one_lt hr₀ hD2 n))) hs1 D
      · exact pow_le_pow_left₀ (le_of_lt (lt_trans zero_lt_one hs1')) hs2 D
    set w : ℂ := Work.EL.rayPt hN (θf (n-1)) (s ^ D) with hw
    have hwK : w ∉ Work.EL.K c := Work.EL.rayPt_notMem_K hN hsD1
    have hwball : w ∈ Metric.ball y r' := hPf (n-1) ⟨s ^ D, hmem, rfl⟩
    have hwd : ‖w - y‖ ≤ r' := le_of_lt (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hwball)
    have hgwK : g w ∉ Work.EL.K c := notMem_K_of_g hwK (hright w hwd)
    have hgwP : g w ∈ Work.EL.paramRay hN (θf n) := by
      have h1 := branch_rel (n-1)
      rw [show n - 1 + 1 = n from by omega] at h1
      exact h1 ⟨w, ⟨s ^ D, hmem, rfl⟩, rfl⟩
    have hlevw : ‖φ w‖ = s ^ D := by rw [hw]; exact norm_phi_rayPt hsD1
    have hlev : ‖φ (g w)‖ = s := by
      have hp := norm_phi_g hφ hright hwd hgwK
      rw [hlevw, hDeq] at hp
      exact (pow_left_inj₀ (norm_nonneg _) (le_of_lt (lt_trans zero_lt_one hs1'))
        (by positivity : 4 ^ k ≠ 0)).mp hp
    exact (eq_rayPt_of_level hgwK hs1' hgwP hlev).symm
  -- the window relation
  have Drel : ∀ m n : ℕ, m ≤ n → ∀ s : ℝ,
      s ∈ Set.Icc (lvlSeq r₀ D m) (lvlSeq r₀ D m ^ D) →
      Work.EL.rayPt hN (θf n) s = (g^[m]) (Work.EL.rayPt hN (θf (n - m)) (s ^ (D ^ m))) := by
    intro m
    induction m with
    | zero =>
        intro n _ s _
        simp
    | succ m ih =>
        intro n hm s hs
        have hn1 : 1 ≤ n := by omega
        have hm1 : m ≤ n - 1 := by omega
        have hs1 : 1 < s :=
          lt_of_lt_of_le (lvlSeq_one_lt hr₀ hD2 (m+1)) hs.1
        have hsDmem : s ^ D ∈ Set.Icc (lvlSeq r₀ D m) (lvlSeq r₀ D m ^ D) := by
          have h2 : (lvlSeq r₀ D (m+1)) ^ D = lvlSeq r₀ D m :=
            lvlSeq_pow (le_of_lt (lt_trans zero_lt_one hr₀)) hDne m
          have hs2' : s ≤ lvlSeq r₀ D m := by rw [← h2]; exact hs.2
          refine ⟨?_, pow_le_pow_left₀ (le_of_lt (lt_trans zero_lt_one hs1)) hs2' D⟩
          have h := lvlSeq_pow (le_of_lt (lt_trans zero_lt_one hr₀)) hDne m
          rw [← h]
          exact pow_le_pow_left₀ (le_of_lt (lt_trans zero_lt_one
            (lvlSeq_one_lt hr₀ hD2 (m+1)))) hs.1 D
        have hlow : lvlSeq r₀ D n ≤ s := le_trans (lvlSeq_mono hr₀ hD2 hm) hs.1
        have hupper : s ≤ r₀ := by
          have h2 : (lvlSeq r₀ D (m+1)) ^ D = lvlSeq r₀ D m :=
            lvlSeq_pow (le_of_lt (lt_trans zero_lt_one hr₀)) hDne m
          have hs2' : s ≤ lvlSeq r₀ D m := by rw [← h2]; exact hs.2
          exact le_trans hs2' (lvlSeq_le_r₀ hr₀ hD2 m)
        have hC := Crel n hn1 s hlow hupper
        have ihh := ih (n-1) hm1 (s ^ D) hsDmem
        rw [hC, ihh, Function.iterate_succ_apply']
        have hidx : n - 1 - m = n - (m + 1) := by omega
        have hexp : (s ^ D) ^ (D ^ m) = s ^ (D ^ (m + 1)) := by
          rw [← pow_mul, ← pow_succ']
        rw [hidx, hexp]
  -- the uniform bound on the windows
  have hwin : ∀ m n : ℕ, m ≤ n → ∀ s : ℝ,
      s ∈ Set.Icc (lvlSeq r₀ D m) (lvlSeq r₀ D m ^ D) →
      ‖Work.EL.rayPt hN (θf n) s - y‖ ≤ κ ^ m * r' := by
    intro m n hmn s hs
    rw [Drel m n hmn s hs]
    have hs1 : 1 < s := lt_of_lt_of_le (lvlSeq_one_lt hr₀ hD2 m) hs.1
    have hlow : r₀ ≤ s ^ (D ^ m) := by
      have h := lvlSeq_pow_pow (le_of_lt (lt_trans zero_lt_one hr₀)) hDne 0 m
      rw [Nat.zero_add, lvlSeq_zero] at h
      rw [← h]
      exact pow_le_pow_left₀ (le_of_lt (lt_trans zero_lt_one (lvlSeq_one_lt hr₀ hD2 m))) hs.1 (D ^ m)
    have hup : s ^ (D ^ m) ≤ r₀ ^ D := by
      have h2 : (lvlSeq r₀ D m ^ D) ^ (D ^ m) = r₀ ^ D := by
        rw [← pow_mul, Nat.mul_comm D (D ^ m), pow_mul]
        have h := lvlSeq_pow_pow (le_of_lt (lt_trans zero_lt_one hr₀)) hDne 0 m
        rw [Nat.zero_add] at h
        rw [h, lvlSeq_zero]
      rw [← h2]
      exact pow_le_pow_left₀ (le_of_lt (lt_trans zero_lt_one hs1)) hs.2 (D ^ m)
    have hsmem : s ^ (D ^ m) ∈ Set.Icc (lvlSeq r₀ D (n - m)) (r₀ ^ D) :=
      ⟨le_trans (le_trans (lvlSeq_mono hr₀ hD2 (Nat.zero_le (n - m)))
        (le_of_eq (lvlSeq_zero r₀ D))) hlow, hup⟩
    have hwball : Work.EL.rayPt hN (θf (n - m)) (s ^ (D ^ m)) ∈ Metric.ball y r' :=
      hPf (n - m) ⟨s ^ (D ^ m), hsmem, rfl⟩
    have hwd : ‖Work.EL.rayPt hN (θf (n - m)) (s ^ (D ^ m)) - y‖ ≤ r' :=
      le_of_lt (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hwball)
    calc ‖(g^[m]) (Work.EL.rayPt hN (θf (n - m)) (s ^ (D ^ m))) - y‖
        ≤ κ ^ m * ‖Work.EL.rayPt hN (θf (n - m)) (s ^ (D ^ m)) - y‖ :=
          iterate_contract hκ0 (le_of_lt hκ1) hcontr hwd m
      _ ≤ κ ^ m * r' := mul_le_mul_of_nonneg_left hwd (pow_nonneg hκ0 m)
  exact ⟨θf, by show (aux 0).1 = θ₀; rfl, branch_cong, hwin⟩

/-! ## The requested statement -/

theorem exists_backward_orbit_tail_core {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hN : Work.EL.DynB c φ)
    (hrep : Work.Landing.IsRepelling c k y)
    {r' κ ε ρ r₀ : ℝ} {g : ℂ → ℂ}
    (hr' : 0 < r') (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hgy : g y = y) (hcont : ContinuousOn g (Metric.ball y r'))
    (hcontr : ∀ w : ℂ, ‖w - y‖ ≤ r' → ‖g w - y‖ ≤ κ * ‖w - y‖)
    (hright : ∀ w : ℂ, ‖w - y‖ ≤ r' →
      (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (g w) = w)
    (hεsmall : ε + κ * r' < r')
    (hρshr : ∀ θ t : ℝ, 1 < t → t < ρ → ∀ s₁ s₂ : ℝ, t ≤ s₁ → s₁ ≤ s₂ →
      s₂ ≤ t ^ (4 ^ k) → ‖Work.EL.rayPt hN θ s₂ - Work.EL.rayPt hN θ s₁‖ ≤ ε)
    (hr₀ : 1 < r₀) (hr₀ρ : r₀ < ρ) {θ₀ : ℝ}
    (hseed : Work.EL.rayPt hN θ₀ '' Set.Icc r₀ (r₀ ^ (4 ^ k)) ⊆ Metric.ball y r') :
    ∃ θ : ℕ → ℝ, θ 0 = θ₀ ∧
      (∀ n : ℕ, ∃ m : ℤ, (4 : ℝ) ^ k * θ (n + 1) = θ n + m) ∧
      (∀ m n : ℕ, m ≤ n → ∀ s : ℝ,
        s ∈ Set.Icc (Work.LandLeaves.V2Anchor.lvlSeq r₀ (4 ^ k) m)
            ((Work.LandLeaves.V2Anchor.lvlSeq r₀ (4 ^ k) m) ^ (4 ^ k)) →
        ‖Work.EL.rayPt hN (θ n) s - y‖ ≤ κ ^ m * r') := by
  have hk : 0 < k := hrep.1.1
  have hD2 : 2 ≤ 4 ^ k := by
    calc (2:ℕ) ≤ 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hk
  exact exists_backward_orbit_tail_core_aux hφ hN hrep hr' hκ0 hκ1 hgy hcont hcontr hright
    hεsmall hD2 rfl hρshr hr₀ hr₀ρ hseed

end

end Work.LandLeaves.V2Anchor

