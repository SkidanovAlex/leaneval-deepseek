import Mathlib.Computability.Reduce
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB4.thetaExp_lattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.K15R.LevelDefs` — the `ℓ^∞` level of a lattice index

The lattice sums of FS §10 (`lem:EstimateIntegral`) run over the momenta
`Work.BoseB4.vec n = 2π n` (`n : Fin 3 → ℤ`), with weights `‖vec n‖^{-p}`.  The
crude ball count `card_le_of_vec_norm_le` (`#S ≤ (ρ/π+1)^3` for `‖vec n‖ ≤ ρ`) is
*not* good enough for them: it carries linear and quadratic terms in `ρ`, so a
dyadic-shell decomposition acquires a spurious `log R`.

The right elementary device is the `ℓ^∞` **level** of a lattice index,

    `lev n = max_i |n_i|`   (`lev : (Fin 3 → ℤ) → ℕ`),

because the level shells are *exactly* countable: the `ℤ³`-cube
`cube m = ∏_i [-m, m]` of side `2m+1` has `(2m+1)^3` points, so its boundary
shell `{lev = m} = cube m \ cube (m-1)` has `(2m+1)^3 - (2m-1)^3 = 24m^2 + 2`
points — *quadratic*, with no lower-order junk.  Since the two norms compare by
`2π · lev n ≤ ‖vec n‖ ≤ 2π√3 · lev n`, every radial lattice sum becomes a sum over
*levels*:

    `∑_{n ∈ S} ‖vec n‖^{-p} ≤ ∑_{m=M_0}^{M_1} 26 m^2 (2πm)^{-p}`,

and this is what the chapter's momentum sums evaluate.

## Contents

* `lev`, `lev_eq_zero_iff`, `natAbs_le_lev`, `le_lev_of_forall`,
  `exists_natAbs_eq_lev`, `one_le_lev_of_ne_zero`;
* the norm comparison `two_pi_mul_lev_le_norm_vec`,
  `norm_vec_le_two_pi_sqrt_three_mul_lev` and the two corollaries
  `lev_le_of_norm_le`, `le_lev_of_norm_le`;
* `cube`, `mem_cube_iff`, `card_cube`, `card_filter_lev_le` — the shell count
  `#{n ∈ S | lev n = m} ≤ 26 m^2` for `m ≥ 1`;
* `sum_le_level_range` — the general level decomposition
  `∑_{n ∈ S} f n ≤ ∑_{m ∈ Icc M_0 M_1} 26 m^2 G m` for `f n ≤ G (lev n)`.

To convert a real bound `(lev n : ℝ) ≤ ρ` (or `ρ ≤ (lev n : ℝ)`) into a *natural*
bound one uses `Nat.le_floor` (`n ≤ ⌊r⌋ ↔ (n : α) ≤ r`) resp. `Nat.ceil_le`
(`⌈r⌉₊ ≤ n ↔ r ≤ n`); the constants `26` and the explicit ones below are crude on
purpose (only existence of a constant is ever consumed).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7AK.K15R

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The level and its elementary API -/

/-- **The `ℓ^∞` level of a lattice index**: the largest absolute value of a
coordinate of `n : Fin 3 → ℤ`.  The point of this function is that its shells
`{lev = m}` are exactly countable (`26 m^2` points suffice). -/
def lev (n : Fin 3 → ℤ) : ℕ := max (n 0).natAbs (max (n 1).natAbs (n 2).natAbs)

lemma natAbs_le_lev (n : Fin 3 → ℤ) (i : Fin 3) : (n i).natAbs ≤ lev n := by
  fin_cases i <;> simp only [lev]
  · exact Nat.le_max_left _ _
  · exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  · exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

lemma le_lev_of_forall (n : Fin 3 → ℤ) (m : ℕ) (h : ∀ i, (n i).natAbs ≤ m) :
    lev n ≤ m := by
  simp only [lev]
  exact Nat.max_le.mpr ⟨h 0, Nat.max_le.mpr ⟨h 1, h 2⟩⟩

/-- The level vanishes exactly on the origin. -/
lemma lev_eq_zero_iff (n : Fin 3 → ℤ) : lev n = 0 ↔ n = 0 := by
  constructor
  · intro h
    funext i
    have h1 : (n i).natAbs ≤ lev n := natAbs_le_lev n i
    rw [h] at h1
    exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp h1)
  · rintro rfl
    simp [lev]

lemma one_le_lev_of_ne_zero (n : Fin 3 → ℤ) (hn : n ≠ 0) : 1 ≤ lev n :=
  Nat.one_le_iff_ne_zero.mpr fun h => hn ((lev_eq_zero_iff n).mp h)

/-- Some coordinate of `n` attains the level. -/
lemma exists_natAbs_eq_lev (n : Fin 3 → ℤ) : ∃ i, (n i).natAbs = lev n := by
  rcases max_choice (n 0).natAbs (max (n 1).natAbs (n 2).natAbs) with h | h
  · exact ⟨0, by simp only [lev]; exact h.symm⟩
  · rcases max_choice (n 1).natAbs (n 2).natAbs with h2 | h2
    · exact ⟨1, by simp only [lev]; rw [h, h2]⟩
    · exact ⟨2, by simp only [lev]; rw [h, h2]⟩

/-- `|z|` of an integer is the cast of its `natAbs`. -/
lemma natAbs_cast_real (z : ℤ) : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
  rcases Int.natAbs_eq z with h | h
  · rw [h]; simp
  · rw [h]; simp

lemma natAbs_le_nat_iff (z : ℤ) (m : ℕ) : z.natAbs ≤ m ↔ -(m : ℤ) ≤ z ∧ z ≤ (m : ℤ) := by
  rw [← Int.ofNat_le, ← Int.abs_eq_natAbs, abs_le]

/-! ## 2. The two norms -/

/-- The lower bound `2π·lev n ≤ ‖vec n‖`: the coordinate attaining the level
gives `|vec n i| = 2π lev n`. -/
lemma two_pi_mul_lev_le_norm_vec (n : Fin 3 → ℤ) :
    2 * Real.pi * (lev n : ℝ) ≤ ‖Work.BoseB4.vec n‖ := by
  obtain ⟨i, hi⟩ := exists_natAbs_eq_lev n
  have h1 : |Work.BoseB4.vec n i| ≤ ‖Work.BoseB4.vec n‖ := by
    simpa using PiLp.norm_apply_le (Work.BoseB4.vec n) i
  rw [show Work.BoseB4.vec n i = 2 * Real.pi * (n i : ℝ) from rfl, abs_mul,
    abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)] at h1
  rw [show |(n i : ℝ)| = ((n i).natAbs : ℝ) from (natAbs_cast_real (n i)).symm, hi] at h1
  exact h1

/-- The upper bound `‖vec n‖ ≤ 2π√3·lev n`. -/
lemma norm_vec_le_two_pi_sqrt_three_mul_lev (n : Fin 3 → ℤ) :
    ‖Work.BoseB4.vec n‖ ≤ 2 * Real.pi * Real.sqrt 3 * (lev n : ℝ) := by
  set y : ℝ := 2 * Real.pi * (lev n : ℝ) with hy
  have hpt : ∀ i : Fin 3, (Work.BoseB4.vec n).ofLp i ^ 2 ≤ y ^ 2 := by
    intro i
    have h1 : |(n i : ℝ)| ≤ (lev n : ℝ) := by
      rw [← natAbs_cast_real (n i)]
      exact_mod_cast natAbs_le_lev n i
    have h3 : |(Work.BoseB4.vec n).ofLp i| ≤ y := by
      have hvec : (Work.BoseB4.vec n).ofLp i = (2 * Real.pi) * (n i : ℝ) := rfl
      rw [hvec, abs_mul (2 * Real.pi) (n i : ℝ),
        abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity), hy]
      nlinarith [Real.pi_pos, h1]
    calc (Work.BoseB4.vec n).ofLp i ^ 2 = |(Work.BoseB4.vec n).ofLp i| ^ 2 :=
          (sq_abs ((Work.BoseB4.vec n).ofLp i)).symm
      _ ≤ y ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hsum : ∑ i, (Work.BoseB4.vec n).ofLp i ^ 2 ≤ 3 * y ^ 2 := by
    calc ∑ i, (Work.BoseB4.vec n).ofLp i ^ 2 ≤ ∑ _i : Fin 3, y ^ 2 :=
          Finset.sum_le_sum (fun i _ => hpt i)
      _ = 3 * y ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have hsq : ‖Work.BoseB4.vec n‖ ^ 2 ≤ (2 * Real.pi * Real.sqrt 3 * (lev n : ℝ)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine hsum.trans (le_of_eq ?_)
    rw [hy]
    have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [h3]
  have hfin := sq_le_sq.mp hsq
  rw [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * Real.sqrt 3 * (lev n : ℝ))] at hfin
  exact hfin

/-- **Upper-bound corollary**: if `‖vec n‖ ≤ R` then `lev n ≤ R/(2π)`. -/
lemma lev_le_of_norm_le {n : Fin 3 → ℤ} {R : ℝ} (h : ‖Work.BoseB4.vec n‖ ≤ R) :
    (lev n : ℝ) ≤ R / (2 * Real.pi) := by
  have h2 := le_trans (two_pi_mul_lev_le_norm_vec n) h
  rw [le_div_iff₀ (by positivity)]
  linarith [Real.pi_pos]

/-- **Lower-bound corollary**: if `R ≤ ‖vec n‖` then `R/(2π√3) ≤ lev n`. -/
lemma le_lev_of_norm_le {n : Fin 3 → ℤ} {R : ℝ} (h : R ≤ ‖Work.BoseB4.vec n‖) :
    R / (2 * Real.pi * Real.sqrt 3) ≤ (lev n : ℝ) := by
  have h2 := le_trans h (norm_vec_le_two_pi_sqrt_three_mul_lev n)
  rw [div_le_iff₀ (by positivity)]
  linarith [Real.pi_pos, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)]

/-! ## 3. The cube and the shell count -/

/-- The lattice cube `∏_i [-m, m] ⊆ ℤ³` of side `2m+1`. -/
def cube (m : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(m : ℤ)) (m : ℤ))

lemma mem_cube_iff (n : Fin 3 → ℤ) (m : ℕ) : n ∈ cube m ↔ lev n ≤ m := by
  rw [cube, Fintype.mem_piFinset]
  constructor
  · intro h
    exact le_lev_of_forall n m (fun i => (natAbs_le_nat_iff (n i) m).mpr (by
      have := h i
      rwa [Finset.mem_Icc] at this))
  · intro h i
    rw [Finset.mem_Icc]
    exact (natAbs_le_nat_iff (n i) m).mp (le_trans (natAbs_le_lev n i) h)

lemma card_cube (m : ℕ) : (cube m).card = (2 * m + 1) ^ 3 := by
  rw [cube, Fintype.card_piFinset]
  simp only [Int.card_Icc]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h : ((m : ℤ) + 1 - (-(m : ℤ))).toNat = 2 * m + 1 := by
    have h2 : (m : ℤ) + 1 - (-(m : ℤ)) = ((2 * m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h2, Int.toNat_natCast]
  rw [h]

lemma cube_subset (m : ℕ) : cube (m - 1) ⊆ cube m := by
  intro n hn
  rw [mem_cube_iff] at hn ⊢
  omega

/-- **The shell count.**  A set of lattice indices of level exactly `m ≥ 1` has at
most `26 m^2` elements (the shell `{lev = m} = cube m \ cube (m-1)` of the lattice
cube has `24m^2+2`). -/
lemma card_filter_lev_le (S : Finset (Fin 3 → ℤ)) (m : ℕ) (hm : 1 ≤ m) :
    (S.filter (fun n => lev n = m)).card ≤ 26 * m ^ 2 := by
  have hsub : S.filter (fun n => lev n = m) ⊆ cube m \ cube (m - 1) := by
    intro n hn
    rw [Finset.mem_sdiff, Finset.mem_filter] at *
    refine ⟨(mem_cube_iff n m).mpr (le_of_eq hn.2), ?_⟩
    intro hc
    rw [mem_cube_iff] at hc
    omega
  have hcubeid : (2 * m - 1) ^ 3 + (24 * m ^ 2 + 2) = (2 * m + 1) ^ 3 := by
    have hcast' : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
    have hcubeZ : (((2 * (m - 1) + 1 : ℕ) : ℤ)) ^ 3 + (24 * (m : ℤ) ^ 2 + 2)
        = (2 * (m : ℤ) + 1) ^ 3 := by
      push_cast
      rw [Nat.cast_sub hm]
      ring
    rw [hcast'] at *
    exact_mod_cast hcubeZ
  calc (S.filter (fun n => lev n = m)).card
      ≤ (cube m \ cube (m - 1)).card := Finset.card_le_card hsub
    _ = (cube m).card - (cube (m - 1)).card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (cube_subset m)]
    _ = (2 * m + 1) ^ 3 - (2 * (m - 1) + 1) ^ 3 := by rw [card_cube, card_cube]
    _ ≤ 26 * m ^ 2 := by
        have h2 : 2 * (m - 1) + 1 = 2 * m - 1 := by omega
        rw [h2, Nat.sub_eq_of_eq_add
          (show (2 * m + 1) ^ 3 = (24 * m ^ 2 + 2) + (2 * m - 1) ^ 3 by omega)]
        have hm2 : 1 ≤ m ^ 2 := by nlinarith
        nlinarith

/-! ## 4. The level decomposition -/

/-- **The level decomposition.**  Any summand `f` bounded above by `G ∘ lev` on a
finite lattice set `S`, all of whose levels lie in `[M₀, M₁]` with `M₀ ≥ 1`, is
bounded by `∑_{m=M₀}^{M₁} 26 m^2 G m`. -/
lemma sum_le_level_range (f : (Fin 3 → ℤ) → ℝ) (G : ℕ → ℝ) (S : Finset (Fin 3 → ℤ))
    (M₀ M₁ : ℕ) (h0 : 1 ≤ M₀)
    (hpoint : ∀ n ∈ S, f n ≤ G (lev n))
    (hlo : ∀ n ∈ S, M₀ ≤ lev n) (hhi : ∀ n ∈ S, lev n ≤ M₁)
    (hGnn : ∀ m, 0 ≤ G m) :
    ∑ n ∈ S, f n ≤ ∑ m ∈ Finset.Icc M₀ M₁, (26 * (m : ℝ) ^ 2) * G m := by
  have h1 : ∑ n ∈ S, f n ≤ ∑ n ∈ S, G (lev n) := Finset.sum_le_sum hpoint
  have hC : ∑ n ∈ S, G (lev n) ≤
      ∑ n ∈ S, ∑ m ∈ Finset.Icc M₀ M₁, (if lev n = m then G m else 0) := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hmem : lev n ∈ Finset.Icc M₀ M₁ := Finset.mem_Icc.mpr ⟨hlo n hn, hhi n hn⟩
    have hs := Finset.single_le_sum
      (s := Finset.Icc M₀ M₁) (f := fun m => if lev n = m then G m else 0)
      (fun m _ => by split_ifs with h; exact hGnn m; exact le_refl 0) hmem
    rwa [if_pos rfl] at hs
  have hA : ∑ m ∈ Finset.Icc M₀ M₁, ∑ n ∈ S.filter (fun n => lev n = m), G m
      = ∑ m ∈ Finset.Icc M₀ M₁, (S.filter (fun n => lev n = m)).card • G m := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_const]
  have hD : ∑ m ∈ Finset.Icc M₀ M₁, (S.filter (fun n => lev n = m)).card • G m
      ≤ ∑ m ∈ Finset.Icc M₀ M₁, (26 * (m : ℝ) ^ 2) * G m := by
    refine Finset.sum_le_sum (fun m hm => ?_)
    have hm1 : 1 ≤ m := le_trans h0 (Finset.mem_Icc.mp hm).1
    have hcard : ((S.filter (fun n => lev n = m)).card : ℝ) ≤ 26 * (m : ℝ) ^ 2 := by
      exact_mod_cast card_filter_lev_le S m hm1
    calc (S.filter (fun n => lev n = m)).card • G m
        = ((S.filter (fun n => lev n = m)).card : ℝ) * G m := by rw [nsmul_eq_mul]
      _ ≤ (26 * (m : ℝ) ^ 2) * G m := mul_le_mul_of_nonneg_right hcard (hGnn m)
  calc ∑ n ∈ S, f n ≤ ∑ n ∈ S, G (lev n) := h1
    _ ≤ ∑ n ∈ S, ∑ m ∈ Finset.Icc M₀ M₁, (if lev n = m then G m else 0) := hC
    _ = ∑ m ∈ Finset.Icc M₀ M₁, ∑ n ∈ S, (if lev n = m then G m else 0) := Finset.sum_comm
    _ = ∑ m ∈ Finset.Icc M₀ M₁, ∑ n ∈ S.filter (fun n => lev n = m), G m := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.sum_filter]
    _ = ∑ m ∈ Finset.Icc M₀ M₁, (S.filter (fun n => lev n = m)).card • G m := hA
    _ ≤ ∑ m ∈ Finset.Icc M₀ M₁, (26 * (m : ℝ) ^ 2) * G m := hD

end Work.BoseB7AK.K15R
