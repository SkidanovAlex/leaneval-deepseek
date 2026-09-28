import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Sig2.schmidt_bound
import Submission.Work.HP.MDEstimates.ball_count_R0
import Submission.Work.HP.Vero.finrank_latOrth
import Submission.Work.HP.FM4.two_pow_between
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.dyadic_summation
import Submission.Work.HP.DiagDefs
import Submission.Work.HP.rk_le_card
import Submission.Work.HP.lam_basic
import Submission.Work.HP.ballCount_le_pow_rk
import Submission.Work.HP.inv_le_dyadic_shell
import Submission.Work.HP.dyadic_ball_weight_sum

/-!
# `Work.HP.latOrth_inv_sum_le`

For a type `ι` with `3 ≤ card ι` there is a constant `K = K(ι) > 0` such that for every
nonzero `c : ι → ℤ` and every `A ≥ 1`

`Σ_{0 < ‖a‖ ≤ A, a ∈ Λ_c} ‖a‖⁻¹ ≤ K · A^{card ι - 2}`,   `Λ_c = {y ∈ ℤ^ι : ⟨c,y⟩ = 0}`.

*Combinatorics.* `Λ_c` is a sublattice of `ℤ^ι` of rank `card ι - 1` (`Vero.finrank_latOrth`),
and every sublattice of `ℤ^ι` has its point count in a ball controlled by
`#{v ∈ L : ‖v‖ ≤ T} ≤ K₀ (T+1)^{rk L}` (`ballCount_le_pow_rk`, from Schmidt's bound and the
fact that all successive minima are `≥ 1`).  Splitting the sum along the dyadic shells
`(A/2^{j+1}, A/2^j]` of the radius and using `∑_{v ∈ Λ_c, ‖v‖ ≤ A/2^j} 1 ≤ K₀ (A/2^j + 1)^{rk L}`
turns it into `∑_j 2^{j+1}/A · (A/2^j + 1)^{card ι - 1}`, which is `≪ A^{card ι - 2}`.
`inv_le_dyadic_shell` is the pointwise shell majorant and `dyadic_ball_weight_sum` the arithmetic
summation; they are combined by the sandwich lemma `inv_sum_le_of_ballCount`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Finset

namespace Work.HP

/-- Dyadic shell sandwich: given a uniform lattice-point bound
`#{v ∈ L : ‖v‖ ≤ T} ≤ C (T+1)^r` (and the arithmetic input `hK₃b`), the weighted sum
`∑_{0 < ‖a‖ ≤ A, a ∈ L} 1/‖a‖` is `≪ A^{r-1}`, for `r ≥ 2` and `A ≥ 1`. -/
lemma inv_sum_le_of_ballCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (_hr : 2 ≤ r) (K₃ : ℝ)
    (hK₃b : ∀ A : ℝ, 1 ≤ A →
      (∑ j ∈ Finset.range (dyIdx A + 1), ((2 : ℝ) ^ (j + 1) / A) * (A / (2 : ℝ) ^ j + 1) ^ r)
        ≤ K₃ * A ^ (r - 1))
    (C : ℝ) (hC : 0 < C) (L : Submodule ℤ (ι → ℤ))
    (hcount : ∀ T : ℝ, 0 ≤ T → (ballCount L T : ℝ) ≤ C * (T + 1) ^ r) :
    ∀ A : ℝ, 1 ≤ A →
      (∑ᶠ a ∈ ({a : ι → ℤ | a ∈ L ∧ 0 < eNorm a ∧ eNorm a ≤ A} : Set (ι → ℤ)), 1 / eNorm a)
        ≤ K₃ * C * A ^ (r - 1) := by
  intro A hA
  classical
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA
  set S : Set (ι → ℤ) := {a : ι → ℤ | a ∈ L ∧ 0 < eNorm a ∧ eNorm a ≤ A} with hS
  have hmemS : ∀ a : ι → ℤ, a ∈ S ↔ (a ∈ L ∧ 0 < eNorm a ∧ eNorm a ≤ A) := by
    intro a; rw [hS]; simp
  have hSfin : S.Finite := by
    rw [hS]
    exact (MDBasic.finite_eNorm_le A).subset (fun v hv => hv.2.2)
  rw [finsum_mem_of_finite S hSfin]
  have key : ∀ (u : Finset (ι → ℤ)) (T : ℝ), 0 ≤ T →
      (∀ a ∈ u, a ∈ L ∧ eNorm a ≤ T) → (u.card : ℝ) ≤ C * (T + 1) ^ r := by
    intro u T hT hu
    have hsub : (↑u : Set (ι → ℤ)) ⊆ ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T} : Set (ι → ℤ)) := by
      intro a ha
      exact hu a (Finset.mem_coe.mp ha)
    have hfin : ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T} : Set (ι → ℤ)).Finite :=
      (MDBasic.finite_eNorm_le T).subset (fun v hv => hv.2)
    have h1 : (↑u : Set (ι → ℤ)).ncard
        ≤ ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T} : Set (ι → ℤ)).ncard :=
      Set.ncard_le_ncard hsub hfin
    have h2 : (↑u : Set (ι → ℤ)).ncard = u.card := by simp
    rw [h2] at h1
    have h3 : ((({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T} : Set (ι → ℤ)).ncard : ℕ) : ℝ)
        ≤ C * (T + 1) ^ r := by
      simpa [ballCount] using hcount T hT
    exact le_trans (by exact_mod_cast h1) h3
  have hstep1 : ∑ a ∈ hSfin.toFinset, 1 / eNorm a ≤
      ∑ a ∈ hSfin.toFinset, ∑ j ∈ Finset.range (dyIdx A + 1),
        ((2 : ℝ) ^ (j + 1) / A) *
          (if eNorm a ≤ A / (2 : ℝ) ^ j then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum (fun a ha => ?_)
    obtain ⟨_haL, ha0, haA⟩ := (hmemS a).mp ((hSfin.mem_toFinset).mp ha)
    have hane : a ≠ 0 := by
      intro h
      rw [h] at ha0
      simp [eNorm] at ha0
    exact inv_le_dyadic_shell hA (one_le_eNorm hane) haA
  have hstep2 : ∑ a ∈ hSfin.toFinset, ∑ j ∈ Finset.range (dyIdx A + 1),
        ((2 : ℝ) ^ (j + 1) / A) *
          (if eNorm a ≤ A / (2 : ℝ) ^ j then (1 : ℝ) else 0)
      = ∑ j ∈ Finset.range (dyIdx A + 1), ((2 : ℝ) ^ (j + 1) / A) *
          (((hSfin.toFinset).filter (fun a => eNorm a ≤ A / (2 : ℝ) ^ j)).card : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : (∑ a ∈ hSfin.toFinset, ((2 : ℝ) ^ (j + 1) / A) *
          (if eNorm a ≤ A / (2 : ℝ) ^ j then (1 : ℝ) else 0))
        = ((2 : ℝ) ^ (j + 1) / A) *
          (((hSfin.toFinset).filter (fun a => eNorm a ≤ A / (2 : ℝ) ^ j)).card : ℝ) := by
      have h1 : (∑ a ∈ hSfin.toFinset, ((2 : ℝ) ^ (j + 1) / A) *
            (if eNorm a ≤ A / (2 : ℝ) ^ j then (1 : ℝ) else 0))
          = ∑ a ∈ hSfin.toFinset,
            (if eNorm a ≤ A / (2 : ℝ) ^ j then (1 : ℝ) else 0) *
              ((2 : ℝ) ^ (j + 1) / A) :=
        Finset.sum_congr rfl (fun a _ => mul_comm _ _)
      rw [h1, ← Finset.sum_mul, Finset.sum_boole, mul_comm]
    exact hj
  have hstep3 : ∑ j ∈ Finset.range (dyIdx A + 1), ((2 : ℝ) ^ (j + 1) / A) *
          (((hSfin.toFinset).filter (fun a => eNorm a ≤ A / (2 : ℝ) ^ j)).card : ℝ)
      ≤ ∑ j ∈ Finset.range (dyIdx A + 1), ((2 : ℝ) ^ (j + 1) / A) *
          (C * (A / (2 : ℝ) ^ j + 1) ^ r) := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    have h2jpos : (0:ℝ) < (2:ℝ)^j := by positivity
    have hfac : (0:ℝ) ≤ (2 : ℝ) ^ (j + 1) / A := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hfac
    have hTj : 0 ≤ A / (2 : ℝ) ^ j := le_of_lt (div_pos hApos h2jpos)
    have hu : ∀ a ∈ (hSfin.toFinset).filter (fun a => eNorm a ≤ A / (2 : ℝ) ^ j),
        a ∈ L ∧ eNorm a ≤ A / (2 : ℝ) ^ j := by
      intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨haT, haj⟩ := ha
      obtain ⟨haL, _, _⟩ := (hmemS a).mp ((hSfin.mem_toFinset).mp haT)
      exact ⟨haL, haj⟩
    exact key _ _ hTj hu
  have hstep4 : ∑ j ∈ Finset.range (dyIdx A + 1), ((2 : ℝ) ^ (j + 1) / A) *
          (C * (A / (2 : ℝ) ^ j + 1) ^ r)
      = C * ∑ j ∈ Finset.range (dyIdx A + 1), ((2 : ℝ) ^ (j + 1) / A) *
          (A / (2 : ℝ) ^ j + 1) ^ r := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  calc ∑ a ∈ hSfin.toFinset, 1 / eNorm a
      ≤ ∑ a ∈ hSfin.toFinset, ∑ j ∈ Finset.range (dyIdx A + 1),
        ((2 : ℝ) ^ (j + 1) / A) *
          (if eNorm a ≤ A / (2 : ℝ) ^ j then (1 : ℝ) else 0) := hstep1
    _ = ∑ j ∈ Finset.range (dyIdx A + 1), ((2 : ℝ) ^ (j + 1) / A) *
          (((hSfin.toFinset).filter (fun a => eNorm a ≤ A / (2 : ℝ) ^ j)).card : ℝ) := hstep2
    _ ≤ ∑ j ∈ Finset.range (dyIdx A + 1), ((2 : ℝ) ^ (j + 1) / A) *
          (C * (A / (2 : ℝ) ^ j + 1) ^ r) := hstep3
    _ = C * ∑ j ∈ Finset.range (dyIdx A + 1), ((2 : ℝ) ^ (j + 1) / A) *
          (A / (2 : ℝ) ^ j + 1) ^ r := hstep4
    _ ≤ C * (K₃ * A ^ (r - 1)) := mul_le_mul_of_nonneg_left (hK₃b A hA) hC.le
    _ = K₃ * C * A ^ (r - 1) := by ring

theorem latOrth_inv_sum_le (ι : Type) [Fintype ι] [DecidableEq ι] (h3 : 3 ≤ Fintype.card ι) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c : ι → ℤ), c ≠ 0 → ∀ A : ℝ, 1 ≤ A →
      (∑ᶠ a ∈ ({a : ι → ℤ | a ∈ latOrth c ∧ 0 < eNorm a ∧ eNorm a ≤ A} : Set (ι → ℤ)),
          1 / eNorm a) ≤ K * A ^ (Fintype.card ι - 2) := by
  classical
  obtain ⟨K₁, hK₁pos, hK₁⟩ := ballCount_le_pow_rk (ι := ι)
  have hr : 2 ≤ Fintype.card ι - 1 := by omega
  obtain ⟨K₃, hK₃pos, hK₃⟩ := dyadic_ball_weight_sum (Fintype.card ι - 1) hr
  refine ⟨K₃ * K₁, mul_pos hK₃pos hK₁pos, ?_⟩
  intro c hc A hA
  have hrk : rk (latOrth c) = Fintype.card ι - 1 := by
    show Module.finrank ℤ (latOrth c) = Fintype.card ι - 1
    exact Vero.finrank_latOrth c hc
  have hcount : ∀ T : ℝ, 0 ≤ T →
      (ballCount (latOrth c) T : ℝ) ≤ K₁ * (T + 1) ^ (Fintype.card ι - 1) := by
    intro T hT
    have h := hK₁ (latOrth c) T hT
    rwa [hrk] at h
  have hmain := inv_sum_le_of_ballCount (Fintype.card ι - 1) hr K₃ hK₃ K₁ hK₁pos
    (latOrth c) hcount A hA
  have hexp : (Fintype.card ι - 1) - 1 = Fintype.card ι - 2 := by omega
  rw [hexp] at hmain
  exact hmain

end Work.HP
