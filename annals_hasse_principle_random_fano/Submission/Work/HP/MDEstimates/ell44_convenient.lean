import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.Q44Child.latZero_bound
import Submission.Work.HP.Sig2.num_lattices_of
import Submission.Work.HP.pair_counts
import Submission.Work.HP.Q44Child.quartic_zero_bound
import Submission.Work.HP.Q44Child.gam_rank
import Submission.Work.HP.Q44Child.lam_attained
import Submission.Work.HP.MDBasic.mem_Gam_iff
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.prim_lat_window_finite
import Submission.Work.HP.ballCount_le_pow_rk
import Submission.Work.HP.minkowski_upper
import Submission.Work.HP.dmin_le_exists_prim
import Submission.Work.HP.lam_basic
import Submission.Work.HP.PairsAux
import Submission.Work.HP.MDEstimates.reducible_forms
import Submission.Work.HP.MDEstimates.latT_sum
import Submission.Work.HP.MDEstimates.ell44_arith
import Submission.Work.HP.MDEstimates.latS_sum_irred
import Submission.Work.HP.Lat.card_Mon

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
noncomputable section

namespace Work.HP.MDEstimates

open Work.HP

/-- The set of candidate witness vectors: the nonzero forms of norm at most `M`. -/
def witSet (M : ℝ) : Set (Mon 4 4 → ℤ) := {c | c ≠ 0 ∧ eNorm c ≤ M}

/-- `ℓ^{(1)}(Z;Δ,M)` is at most the pair count `ℓ_{3,4}(Z,Z;Δ)`. -/
theorem ell44_le_ellXY (Z Δ M : ℝ) : ell44 1 Z Δ M ≤ ellXY 4 3 Z Z Δ := by
  classical
  rw [ell44, ellXY]
  refine Set.ncard_le_ncard ?_ ?_
  · intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  · refine Set.Finite.subset ((MDBasic.finite_eNorm_le Z).prod (MDBasic.finite_eNorm_le Z)) ?_
    intro p hp
    exact ⟨hp.2.1, hp.2.2.1⟩

/-- The crude bound `ℓ^{(1)}(Z;Δ,M) ≪ Z⁶Δ³(log 2Δ)²`, valid for every `M ≥ 1`. -/
theorem ell44_one_crude :
    ∃ K : ℝ, 0 < K ∧ ∀ Z Δ M : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ M →
      (ell44 1 Z Δ M : ℝ) ≤ K * Z ^ 6 * Δ ^ 3 * Real.log (2 * Δ) ^ 2 := by
  obtain ⟨K, hKpos, hK⟩ := pair_counts 4 (by norm_num) 3 (by norm_num) (by norm_num)
  refine ⟨K, hKpos, ?_⟩
  intro Z Δ M hZ hΔ hM
  have h1 := hK Z Z Δ hZ hZ hΔ
  have h2 : (ell44 1 Z Δ M : ℝ) ≤ (ellXY 4 3 Z Z Δ : ℝ) := by
    exact_mod_cast ell44_le_ellXY Z Δ M
  refine le_trans h2 (le_trans h1 ?_)
  have e1 : (4 - 1 : ℕ) = 3 := by norm_num
  have e2 : (2 * min (3 - 2) 1 : ℕ) = 2 := by norm_num
  rw [e1, e2]
  have heq : K * Z ^ 3 * Z ^ 3 * Δ ^ 3 * Real.log (2 * Δ) ^ 2
      = K * Z ^ 6 * Δ ^ 3 * Real.log (2 * Δ) ^ 2 := by ring
  rw [heq]

/-- If `λ₁(Gam 4 4 x y) ≤ M` there is a nonzero witness `c ∈ Gam 4 4 x y` of norm `≤ M`. -/
theorem exists_witness {x y : Fin 5 → ℤ} {M : ℝ} (h : lam (Gam 4 4 x y) 1 ≤ M) :
    ∃ c : Mon 4 4 → ℤ, c ∈ Gam 4 4 x y ∧ c ≠ 0 ∧ eNorm c ≤ M := by
  have h1 : (1 : ℕ) ≤ rk (Gam 4 4 x y) := le_trans (by norm_num) (Q44Child.gam_rank x y)
  obtain ⟨f, hfL, hfI, hfb⟩ := Q44Child.lamAttained_aux (Gam 4 4 x y) h1
  exact ⟨f 0, hfL 0, hfI.ne_zero 0, le_trans (hfb 0) h⟩

/-- The number of candidate witnesses is `≪ M^{70}` (the coefficient space has dimension
`N_{4,4} = 70`). -/
theorem witSet_ncard_le :
    ∃ K : ℝ, 0 < K ∧ ∀ M : ℝ, 1 ≤ M → ((witSet M).ncard : ℝ) ≤ K * M ^ 70 := by
  refine ⟨5 ^ 70, by positivity, ?_⟩
  intro M hM
  have hbox : (witSet M).ncard ≤ (Fintype.piFinset
      (fun _ : Mon 4 4 => Finset.Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ))).card := by
    rw [← Set.ncard_coe_finset (Fintype.piFinset
      (fun _ : Mon 4 4 => Finset.Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ)))]
    refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
    intro c hc
    simp only [Finset.mem_coe, Fintype.mem_piFinset] at hc ⊢
    intro m
    have h2 : ((|c m| : ℤ) : ℝ) ≤ (⌈M⌉₊ : ℝ) := by
      have h3 : ((|c m| : ℤ) : ℝ) = |((c m : ℤ) : ℝ)| := Int.cast_abs
      rw [h3]
      exact le_trans (le_trans (MDBasic.abs_apply_le_eNorm c m) hc.2) (Nat.le_ceil M)
    exact Finset.mem_Icc.mpr (abs_le.mp (by exact_mod_cast h2))
  have hcard : ((Fintype.piFinset (fun _ : Mon 4 4 => Finset.Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ))).card)
      = (2 * ⌈M⌉₊ + 1) ^ 70 := by
    rw [Fintype.card_piFinset]
    have h1 : ∀ m : Mon 4 4, (Finset.Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ)).card = (2 * ⌈M⌉₊ + 1) := by
      intro m
      rw [Int.card_Icc]
      omega
    rw [Finset.prod_congr rfl (fun m _ => h1 m), Finset.prod_const, Finset.card_univ,
      Work.HP.Lat.card_Mon]
    rw [show Nat.choose 8 4 = 70 from by decide]
  have h1 : ((2 * ⌈M⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * M := by
    have h2 : (⌈M⌉₊ : ℝ) ≤ M + 1 := by
      have := Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ M); linarith
    push_cast
    linarith
  have h2 : (((Fintype.piFinset (fun _ : Mon 4 4 => Finset.Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ))).card : ℕ) : ℝ)
      ≤ 5 ^ 70 * M ^ 70 := by
    rw [hcard]
    have h3 : ((2 * ⌈M⌉₊ + 1 : ℕ) : ℝ) ^ 70 ≤ (5 * M) ^ 70 :=
      pow_le_pow_left₀ (by positivity) h1 70
    calc (((2 * ⌈M⌉₊ + 1) ^ 70 : ℕ) : ℝ) = ((2 * ⌈M⌉₊ + 1 : ℕ) : ℝ) ^ 70 := by push_cast; ring
      _ ≤ (5 * M) ^ 70 := h3
      _ = 5 ^ 70 * M ^ 70 := by rw [mul_pow]
  exact le_trans (by exact_mod_cast hbox) h2

/-- The relevant number of lattice points of `L` at which `c` vanishes. -/
def NZ (Z : ℝ) (c : Mon 4 4 → ℤ) (L : Submodule ℤ (Fin 5 → ℤ)) : ℕ :=
  {x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z ∧ formEval 4 4 c x = 0}.ncard

lemma NZ_finite (Z : ℝ) (c : Mon 4 4 → ℤ) (L : Submodule ℤ (Fin 5 → ℤ)) :
    ({x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z ∧ formEval 4 4 c x = 0} :
      Set (Fin 5 → ℤ)).Finite :=
  (MDBasic.finite_eNorm_le Z).subset (fun x hx => hx.2.1)

/-- In the S-case (`c` vanishes on `L`) the count `NZ` is the ball count. -/
lemma NZ_eq_ball {Z : ℝ} {c : Mon 4 4 → ℤ} {L : Submodule ℤ (Fin 5 → ℤ)}
    (h : c ∈ vanishOn L) : NZ Z c L = ballCount L Z := by
  have hsets : {x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z ∧ formEval 4 4 c x = 0}
      = {x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z} := by
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, (mem_vanishOn.mp h) ⟨x, hx.1⟩⟩⟩
  rw [NZ, ballCount, hsets]

/-- In the T-case (`c` does not vanish on `L`) the count `NZ` is controlled by `latZero_bound`. -/
lemma NZ_sq_le_c0 {Z : ℝ} (hZ : 1 ≤ Z) {C0 : ℝ} (hC0 : 0 < C0)
    (hC0b : ∀ (L : Submodule ℤ (Fin 5 → ℤ)), rk L = 3 → ∀ c ∉ vanishOn L, ∀ Z : ℝ, 1 ≤ Z →
      (({x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z ∧ formEval 4 4 c x = 0} : Set (Fin 5 → ℤ)).ncard : ℝ)
        ≤ C0 * (1 + Z / lam L 1) * (1 + Z / lam L 2))
    (c : Mon 4 4 → ℤ) (L : Submodule ℤ (Fin 5 → ℤ)) (hrk : rk L = 3) (h : c ∉ vanishOn L) :
    (NZ Z c L : ℝ) ^ 2
      ≤ C0 ^ 2 * ((1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2) := by
  have hl1 : (0:ℝ) ≤ lam L 1 := le_of_lt (lam_pos L (le_refl 1) (by rw [hrk]; norm_num))
  have hl2 : (0:ℝ) ≤ lam L 2 := le_of_lt (lam_pos L (by norm_num) (by rw [hrk]; norm_num))
  have h1 : (NZ Z c L : ℝ) ≤ C0 * (1 + Z / lam L 1) * (1 + Z / lam L 2) := hC0b L hrk c h Z hZ
  have h3 : (0:ℝ) ≤ C0 * (1 + Z / lam L 1) * (1 + Z / lam L 2) := by positivity
  have h4 : (NZ Z c L : ℝ) ^ 2 ≤ (C0 * (1 + Z / lam L 1) * (1 + Z / lam L 2)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
  have h5 : (C0 * (1 + Z / lam L 1) * (1 + Z / lam L 2)) ^ 2
      = C0 ^ 2 * ((1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2) := by ring
  linarith [h4, h5 ▸ h4]

-- (lead 09-28: latS_sum_red_ph / ell44_main_bound / ell44_convenient removed from the submission: the (4,4) bound is taken from Work.HP.quartic44, proved sorry-free.)
end Work.HP.MDEstimates
