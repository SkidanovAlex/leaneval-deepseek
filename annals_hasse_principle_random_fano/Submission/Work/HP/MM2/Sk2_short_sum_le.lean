import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.DegSq.ball_sum_inv_pow
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.ceil_logb_bounds
import Submission.Work.HP.box_card

/-!
# `Work.HP.MM2.Sk2_short_sum_le`

The short-vector sum `∑_{0 ≠ a ∈ L, ‖a‖ ≤ A} 1/‖a‖²` of an arbitrary sublattice `L ⊆ ℤ^ι`
is `≪ A^{|ι| - 2}`, uniformly in `L`.

Only `L ⊆ ℤ^ι` is used: the lattice points form a subset of the integral points of the ball
of radius `A`, and these are estimated by a dyadic shell decomposition.  The `1/‖a‖²` weight
is absorbed by the shell count `#{x : (ι → ℤ) | ‖x‖ ≤ 2^j} ≤ 5^{|ι|} · 2^{j|ι|}`, leaving the
geometric sum `∑_{j ≤ log₂ A} 2^{j(|ι|-2)} ≪ A^{|ι|-2}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Finset

namespace Work.HP.MM2

open Work.HP

/-! ## Generic ball counting over an arbitrary finite index type -/

/-- A finset of integer vectors of Euclidean norm at most `t` has at most `(2t+3)^{card ι}`
elements: every coordinate lies in `[-⌈t⌉, ⌈t⌉]`. -/
lemma box_count_le_gen {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset (ι → ℤ)) (t : ℝ)
    (ht : 0 ≤ t) :
    ((s.filter (fun x => eNorm x ≤ t)).card : ℝ) ≤ (2 * t + 3) ^ Fintype.card ι := by
  have hsub : s.filter (fun x => eNorm x ≤ t) ⊆
      Fintype.piFinset (fun _ : ι => Finset.Icc (-(Nat.ceil t : ℤ)) (Nat.ceil t : ℤ)) := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro i
    have hxe : eNorm x ≤ t := (Finset.mem_filter.mp hx).2
    have h1 : |(x i : ℝ)| ≤ t := le_trans (MDBasic.abs_apply_le_eNorm x i) hxe
    have h2 : |((x i : ℤ) : ℝ)| ≤ ((Nat.ceil t : ℤ) : ℝ) := le_trans h1 (Nat.le_ceil t)
    rw [Finset.mem_Icc]
    exact ⟨by exact_mod_cast (abs_le.mp h2).1, by exact_mod_cast (abs_le.mp h2).2⟩
  have hcard_le : ((s.filter (fun x => eNorm x ≤ t)).card : ℝ)
      ≤ ((Fintype.piFinset
            (fun _ : ι => Finset.Icc (-(Nat.ceil t : ℤ)) (Nat.ceil t : ℤ))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hboxcard : ((Fintype.piFinset
        (fun _ : ι => Finset.Icc (-(Nat.ceil t : ℤ)) (Nat.ceil t : ℤ))).card : ℝ)
      = (2 * ((Nat.ceil t : ℕ) : ℝ) + 1) ^ Fintype.card ι := by
    simpa using (box_card (ι := ι) (Nat.ceil t)).1
  have hkey : 2 * ((Nat.ceil t : ℕ) : ℝ) + 1 ≤ 2 * t + 3 := by
    have h := Nat.ceil_lt_add_one ht
    linarith
  calc ((s.filter (fun x => eNorm x ≤ t)).card : ℝ)
      ≤ ((Fintype.piFinset
            (fun _ : ι => Finset.Icc (-(Nat.ceil t : ℤ)) (Nat.ceil t : ℤ))).card : ℝ) := hcard_le
    _ = (2 * ((Nat.ceil t : ℕ) : ℝ) + 1) ^ Fintype.card ι := hboxcard
    _ ≤ (2 * t + 3) ^ Fintype.card ι := pow_le_pow_left₀ (by positivity) hkey _

/-- Dyadic count bound: `#{x ∈ S : ‖x‖ ≤ 2^j} ≤ 5^{n} · 2^{jn}`, `n = card ι`. -/
lemma card_le_ball_pow_gen {ι : Type} [Fintype ι] [DecidableEq ι] (j : ℕ)
    (S : Finset (ι → ℤ)) :
    ((S.filter (fun x => eNorm x ≤ (2:ℝ)^j)).card : ℝ)
      ≤ 5 ^ Fintype.card ι * (2:ℝ)^(j * Fintype.card ι) := by
  have h0 : (0:ℝ) ≤ (2:ℝ)^j := by positivity
  have h := box_count_le_gen S ((2:ℝ)^j) h0
  have h2 : (2 * (2:ℝ)^j + 3) ≤ 5 * (2:ℝ)^j := by
    have h1 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    linarith
  calc ((S.filter (fun x => eNorm x ≤ (2:ℝ)^j)).card : ℝ)
      ≤ (2 * (2:ℝ)^j + 3) ^ Fintype.card ι := h
    _ ≤ (5 * (2:ℝ)^j) ^ Fintype.card ι := pow_le_pow_left₀ (by positivity) h2 _
    _ = 5 ^ Fintype.card ι * (2:ℝ)^(j * Fintype.card ι) := by rw [mul_pow, ← pow_mul]

/-- The finset-level dyadic shell bound for `1/‖x‖²`. -/
lemma finset_sum_inv_sq_shell {ι : Type} [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (J : ℕ) {R : ℝ} (hRJ : R ≤ (2:ℝ)^J)
    (S : Finset (ι → ℤ)) (hS : ∀ x ∈ S, x ≠ 0 ∧ eNorm x ≤ R) :
    (∑ x ∈ S, 1 / eNorm x ^ 2)
      ≤ 4 * 5 ^ Fintype.card ι
          * ∑ j ∈ Finset.range (J+1), (2:ℝ)^(j * (Fintype.card ι - 2)) := by
  have step1 : (∑ x ∈ S, 1 / eNorm x ^ 2)
      ≤ ∑ x ∈ S, (2:ℝ)^2 * ∑ j ∈ Finset.range (J+1),
        (if eNorm x ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*2)) else 0) :=
    Finset.sum_le_sum (fun x hx =>
      DegSq.inv_pow_shell_le 2 J (by norm_num) (DegSq.one_le_eNorm (hS x hx).1)
        (le_trans (hS x hx).2 hRJ))
  have step4 : ∀ j ∈ Finset.range (J+1),
      (∑ x ∈ S, (if eNorm x ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*2)) else 0))
        = ((1/2:ℝ)^(j*2)) * ((S.filter (fun x => eNorm x ≤ (2:ℝ)^j)).card : ℝ) := by
    intro j _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hper : ∀ j, ((1/2:ℝ)^(j*2)) * (5 ^ Fintype.card ι * (2:ℝ)^(j * Fintype.card ι))
      = 5 ^ Fintype.card ι * (2:ℝ)^(j * (Fintype.card ι - 2)) := by
    intro j
    calc ((1/2:ℝ)^(j*2)) * (5 ^ Fintype.card ι * (2:ℝ)^(j * Fintype.card ι))
        = 5 ^ Fintype.card ι * (((1/2:ℝ)^(j*2)) * (2:ℝ)^(j * Fintype.card ι)) := by ring
      _ = 5 ^ Fintype.card ι * (2:ℝ)^(j * (Fintype.card ι - 2)) := by
          rw [DegSq.half_pow_mul_two_pow (k := 2) (n := Fintype.card ι) (j := j) hcard]
  calc (∑ x ∈ S, 1 / eNorm x ^ 2)
      ≤ ∑ x ∈ S, (2:ℝ)^2 * ∑ j ∈ Finset.range (J+1),
          (if eNorm x ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*2)) else 0) := step1
    _ = (2:ℝ)^2 * ∑ x ∈ S, ∑ j ∈ Finset.range (J+1),
          (if eNorm x ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*2)) else 0) :=
        (Finset.mul_sum _ _ _).symm
    _ = (2:ℝ)^2 * ∑ j ∈ Finset.range (J+1), ∑ x ∈ S,
          (if eNorm x ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*2)) else 0) := by rw [Finset.sum_comm]
    _ = (2:ℝ)^2 * ∑ j ∈ Finset.range (J+1),
          ((1/2:ℝ)^(j*2)) * ((S.filter (fun x => eNorm x ≤ (2:ℝ)^j)).card : ℝ) := by
        congr 1
        exact Finset.sum_congr rfl step4
    _ ≤ (2:ℝ)^2 * ∑ j ∈ Finset.range (J+1),
          ((1/2:ℝ)^(j*2)) * (5 ^ Fintype.card ι * (2:ℝ)^(j * Fintype.card ι)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by positivity)
        intro j _
        exact mul_le_mul_of_nonneg_left (card_le_ball_pow_gen j S) (by positivity)
    _ = (2:ℝ)^2 * (5 ^ Fintype.card ι
          * ∑ j ∈ Finset.range (J+1), (2:ℝ)^(j * (Fintype.card ι - 2))) := by
        congr 1
        rw [Finset.sum_congr rfl (fun j _ => hper j), ← Finset.mul_sum]
    _ = 4 * 5 ^ Fintype.card ι
          * ∑ j ∈ Finset.range (J+1), (2:ℝ)^(j * (Fintype.card ι - 2)) := by
        ring

/-- Finsum form of the shell bound over the nonzero lattice points of the ball. -/
lemma ball_finsum_inv_sq_shell {ι : Type} [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (J : ℕ) {R : ℝ} (hRJ : R ≤ (2:ℝ)^J) :
    (∑ᶠ x ∈ ({v : ι → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (ι → ℤ)), 1 / eNorm x ^ 2)
      ≤ 4 * 5 ^ Fintype.card ι
          * ∑ j ∈ Finset.range (J+1), (2:ℝ)^(j * (Fintype.card ι - 2)) := by
  let S : Set (ι → ℤ) := {v | v ≠ 0 ∧ eNorm v ≤ R}
  have hsub : S ⊆ ((Fintype.piFinset
      (fun _ : ι => Finset.Icc (-(Nat.ceil R : ℤ)) (Nat.ceil R : ℤ))) : Set (ι → ℤ)) := by
    intro v hv
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 : |(v i : ℝ)| ≤ eNorm v := MDBasic.abs_apply_le_eNorm v i
    have h2 : |(v i : ℝ)| ≤ R := le_trans h1 hv.2
    have h3 : |(v i : ℝ)| ≤ (Nat.ceil R : ℝ) := le_trans h2 (Nat.le_ceil R)
    exact ⟨by exact_mod_cast (abs_le.mp h3).1, by exact_mod_cast (abs_le.mp h3).2⟩
  have hsupp : Function.support (Set.indicator S (fun x : ι → ℤ => 1 / eNorm x ^ 2))
      ⊆ ((Fintype.piFinset
      (fun _ : ι => Finset.Icc (-(Nat.ceil R : ℤ)) (Nat.ceil R : ℤ))) : Set (ι → ℤ)) := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxT
    exact hx (Set.indicator_of_notMem (fun hxS => hxT (hsub hxS)) _)
  show (∑ᶠ x ∈ S, 1 / eNorm x ^ 2) ≤ _
  rw [finsum_mem_def S (fun x : ι → ℤ => 1 / eNorm x ^ 2),
      finsum_eq_finsetSum_of_support_subset _ hsupp]
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter]
  exact finset_sum_inv_sq_shell hcard J hRJ _
    (fun x hx => (Finset.mem_filter.mp hx).2)

/-- The ball sum `∑_{0 ≠ x ∈ ℤ^ι, ‖x‖ ≤ R} 1/‖x‖²` is `≪ R^{|ι|-2}` for `R ≥ 1`. -/
lemma ball_finsum_inv_sq_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (h3 : 3 ≤ Fintype.card ι) {R : ℝ} (hR : 1 ≤ R) :
    (∑ᶠ x ∈ ({v : ι → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (ι → ℤ)), 1 / eNorm x ^ 2)
      ≤ 4 * 5 ^ Fintype.card ι * 4 ^ (Fintype.card ι - 2) * R ^ (Fintype.card ι - 2) := by
  have hcard : 2 ≤ Fintype.card ι := by omega
  have hd : 1 ≤ Fintype.card ι - 2 := by omega
  have hRJ : R ≤ (2:ℝ)^⌈Real.logb 2 R⌉₊ := (ceil_logb_bounds hR).1
  have h2R : (2:ℝ)^⌈Real.logb 2 R⌉₊ ≤ 2 * R := (ceil_logb_bounds hR).2
  have hmain := ball_finsum_inv_sq_shell hcard ⌈Real.logb 2 R⌉₊ hRJ
  have hgeom : (∑ j ∈ Finset.range (⌈Real.logb 2 R⌉₊+1),
        (2:ℝ)^(j * (Fintype.card ι - 2)))
      ≤ (2:ℝ)^((Fintype.card ι - 2) * (⌈Real.logb 2 R⌉₊+1)) :=
    DegSq.geom_sum_two_pow_le (d := Fintype.card ι - 2) (J := ⌈Real.logb 2 R⌉₊) hd
  have hdJ : (2:ℝ)^((Fintype.card ι - 2) * (⌈Real.logb 2 R⌉₊+1))
      = ((2:ℝ)^(⌈Real.logb 2 R⌉₊+1))^(Fintype.card ι - 2) := by
    rw [← pow_mul]
    congr 1
    ring
  have h2J1 : (2:ℝ)^(⌈Real.logb 2 R⌉₊+1) ≤ 4 * R := by
    rw [pow_succ']
    nlinarith [h2R, hR]
  have hpow : ((2:ℝ)^(⌈Real.logb 2 R⌉₊+1))^(Fintype.card ι - 2)
      ≤ 4 ^ (Fintype.card ι - 2) * R ^ (Fintype.card ι - 2) := by
    calc ((2:ℝ)^(⌈Real.logb 2 R⌉₊+1))^(Fintype.card ι - 2)
        ≤ (4 * R)^(Fintype.card ι - 2) := pow_le_pow_left₀ (by positivity) h2J1 _
      _ = 4 ^ (Fintype.card ι - 2) * R ^ (Fintype.card ι - 2) := by rw [mul_pow]
  calc (∑ᶠ x ∈ ({v : ι → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (ι → ℤ)), 1 / eNorm x ^ 2)
      ≤ 4 * 5 ^ Fintype.card ι
          * ∑ j ∈ Finset.range (⌈Real.logb 2 R⌉₊+1),
              (2:ℝ)^(j * (Fintype.card ι - 2)) := hmain
    _ ≤ 4 * 5 ^ Fintype.card ι * (2:ℝ)^((Fintype.card ι - 2) * (⌈Real.logb 2 R⌉₊+1)) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 4 * 5 ^ Fintype.card ι * ((2:ℝ)^(⌈Real.logb 2 R⌉₊+1))^(Fintype.card ι - 2) := by
        rw [hdJ]
    _ ≤ 4 * 5 ^ Fintype.card ι * (4 ^ (Fintype.card ι - 2) * R ^ (Fintype.card ι - 2)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 4 * 5 ^ Fintype.card ι * 4 ^ (Fintype.card ι - 2) * R ^ (Fintype.card ι - 2) := by
        ring

/-- Monotonicity in the lattice: dropping the constraint `a ∈ L` only enlarges the sum. -/
lemma finsum_lattice_le_ball {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (A : ℝ) :
    (∑ᶠ a ∈ ({a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ A} : Set (ι → ℤ)), 1 / eNorm a ^ 2)
      ≤ (∑ᶠ a ∈ ({a : ι → ℤ | a ≠ 0 ∧ eNorm a ≤ A} : Set (ι → ℤ)), 1 / eNorm a ^ 2) := by
  have hSfin : ({a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ A} : Set (ι → ℤ)).Finite :=
    (MDBasic.finite_eNorm_le A).subset (fun a ha => ha.2.2)
  have hBfin : ({a : ι → ℤ | a ≠ 0 ∧ eNorm a ≤ A} : Set (ι → ℤ)).Finite :=
    (MDBasic.finite_eNorm_le A).subset (fun a ha => ha.2)
  have h1 := finsum_mem_eq_finite_toFinset_sum (fun a : ι → ℤ => 1 / eNorm a ^ 2) hSfin
  have h2 := finsum_mem_eq_finite_toFinset_sum (fun a : ι → ℤ => 1 / eNorm a ^ 2) hBfin
  rw [h1, h2]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx
    obtain ⟨hxL, hx0, hxe⟩ := hSfin.mem_toFinset.mp hx
    exact hBfin.mem_toFinset.mpr ⟨hx0, hxe⟩
  · intro x _ _
    exact div_nonneg zero_le_one (sq_nonneg (eNorm x))

theorem Sk2_short_sum_le (ι : Type) [Fintype ι] [DecidableEq ι] (h3 : 3 ≤ Fintype.card ι) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (A : ℝ), 1 ≤ A →
      (∑ᶠ a ∈ ({a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ Work.HP.eNorm a ≤ A} : Set (ι → ℤ)),
          1 / Work.HP.eNorm a ^ 2)
        ≤ K * A ^ (Fintype.card ι - 2) := by
  refine ⟨4 * 5 ^ (Fintype.card ι) * 4 ^ (Fintype.card ι - 2), by positivity, ?_⟩
  intro L A hA
  calc (∑ᶠ a ∈ ({a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ A} : Set (ι → ℤ)), 1 / eNorm a ^ 2)
      ≤ (∑ᶠ a ∈ ({a : ι → ℤ | a ≠ 0 ∧ eNorm a ≤ A} : Set (ι → ℤ)), 1 / eNorm a ^ 2) :=
        finsum_lattice_le_ball L A
    _ ≤ 4 * 5 ^ (Fintype.card ι) * 4 ^ (Fintype.card ι - 2) * A ^ (Fintype.card ι - 2) :=
        ball_finsum_inv_sq_le h3 hA

end Work.HP.MM2
