/-
# `Work.FTS.GalBasis.cc.PsiCutBounds` — the uniform derivative bounds of `cutA` and `cutB`

The uniform-in-`N` bounds on the iterated derivatives of the two one-dimensional steps

  `cutA N z = s((N+1) z - 1) · s(2 - z/(N+1))`,   `cutB N θ = s((N+1) θ - 1) · s((N+1)(π/2-θ) - 1)`

(`s = Real.smoothTransition`) that the fifth conjunct of `psiCut_spec` needs.  The
rescaled-variable reductions and the one-variable Leibniz rules live in `PsiCutDeriv`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.GalBasis.cc.PsiCutDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The affine coefficient `u ↦ u - c` -/

/-! ## The two radial factors of `cutA` -/

/-- The first radial factor of `cutA N` with `λ = N+1`. -/
def cutA1 (lam : ℝ) : ℝ → ℝ → ℝ := fun z _ => Real.smoothTransition (lam * z - 1)

/-- The second radial factor of `cutA N` with `λ = N+1`. -/
def cutA2 (lam : ℝ) : ℝ → ℝ → ℝ := fun z _ => Real.smoothTransition (2 - z / lam)

theorem cutA_eq (N : ℕ) :
    (fun z (_ : ℝ) => cutA N z)
      = fun z θ => cutA1 ((N : ℝ) + 1) z θ * cutA2 ((N : ℝ) + 1) z θ := by
  funext z θ
  simp only [cutA, cutA1, cutA2]

theorem DzIter_cutA1 (lam : ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (cutA1 lam) z θ
      = Eiter j (fun u => u + 1) Real.smoothTransition (lam * z - 1) := by
  have h1 : cutA1 lam = (fun z (_ : ℝ) => Real.smoothTransition (lam * z + (-1))) := by
    funext z θ
    simp only [cutA1, sub_eq_add_neg]
  rw [h1, DzIter_affine Real.smoothTransition lam (-1) j contDiff_smoothTransition z θ]
  have h2 : (fun u : ℝ => u - (-1)) = fun u : ℝ => u + 1 := by funext u; ring
  have h3 : lam * z + (-1) = lam * z - 1 := by ring
  rw [h2, h3]

theorem DzIter_cutA2 (lam : ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (cutA2 lam) z θ
      = Eiter j (fun u => u - 2) Real.smoothTransition (2 - z / lam) := by
  have h1 : cutA2 lam = (fun z (_ : ℝ) => Real.smoothTransition ((-1 / lam) * z + 2)) := by
    funext z θ
    simp only [cutA2]
    congr 1
    ring
  rw [h1, DzIter_affine Real.smoothTransition (-1 / lam) 2 j contDiff_smoothTransition z θ]
  have h3 : (-1 / lam) * z + 2 = 2 - z / lam := by ring
  rw [h3]

/-- The one-variable form of `DzIter_cutA1`. -/
theorem DzIter1_cutA1 (lam : ℝ) (j : ℕ) (z : ℝ) :
    DzIter1 j (fun z' => cutA1 lam z' 0) z
      = Eiter j (fun u => u + 1) Real.smoothTransition (lam * z - 1) := by
  have h := DzIter_const_apply j (fun z' => cutA1 lam z' 0) z 0
  rw [← h]
  exact DzIter_cutA1 lam j z 0

/-- The one-variable form of `DzIter_cutA2`. -/
theorem DzIter1_cutA2 (lam : ℝ) (j : ℕ) (z : ℝ) :
    DzIter1 j (fun z' => cutA2 lam z' 0) z
      = Eiter j (fun u => u - 2) Real.smoothTransition (2 - z / lam) := by
  have h := DzIter_const_apply j (fun z' => cutA2 lam z' 0) z 0
  rw [← h]
  exact DzIter_cutA2 lam j z 0

/-! ## The affine coefficient `u ↦ u - c` -/

theorem deriv_sub_const_eq (c u : ℝ) : deriv (fun u : ℝ => u - c) u = 1 := by
  simpa using ((hasDerivAt_id u).sub_const c).deriv

theorem deriv_sub_const_fun (c : ℝ) : deriv (fun u : ℝ => u - c) = fun _ => (1 : ℝ) := by
  funext u; exact deriv_sub_const_eq c u

/-- All positive iterated derivatives of a constant vanish. -/
theorem iteratedDeriv_const_zero (m : ℕ) (hm : 1 ≤ m) :
    ∀ c : ℝ, iteratedDeriv m (fun _ : ℝ => c) = fun _ => (0 : ℝ) := by
  induction m with
  | zero => intro c; omega
  | succ m ih =>
      intro c
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        rw [iteratedDeriv_one]
        funext u; simp
      · rw [iteratedDeriv_succ']
        have hd : deriv (fun _ : ℝ => c) = fun _ => (0 : ℝ) := by funext u; simp
        rw [hd]
        exact ih hpos 0

theorem iteratedDeriv_affine_sub (c : ℝ) :
    iteratedDeriv 1 (fun u : ℝ => u - c) = fun _ => (1 : ℝ) := by
  rw [iteratedDeriv_one]
  exact deriv_sub_const_fun c

theorem iteratedDeriv_affine_sub2 (c : ℝ) :
    iteratedDeriv 2 (fun u : ℝ => u - c) = fun _ => (0 : ℝ) := by
  have e : iteratedDeriv 2 (fun u : ℝ => u - c)
      = iteratedDeriv 1 (deriv (fun u : ℝ => u - c)) :=
    iteratedDeriv_succ' (n := 1) (f := fun u : ℝ => u - c)
  rw [e, deriv_sub_const_fun c]
  exact iteratedDeriv_const_zero 1 le_rfl 1

theorem iteratedDeriv_affine_sub3 (c : ℝ) :
    iteratedDeriv 3 (fun u : ℝ => u - c) = fun _ => (0 : ℝ) := by
  have e : iteratedDeriv 3 (fun u : ℝ => u - c)
      = iteratedDeriv 2 (deriv (fun u : ℝ => u - c)) :=
    iteratedDeriv_succ' (n := 2) (f := fun u : ℝ => u - c)
  rw [e, deriv_sub_const_fun c]
  exact iteratedDeriv_const_zero 2 (by norm_num) 1

theorem iteratedDeriv_sub_const_le {c : ℝ} (hc : |c| ≤ 2) :
    ∀ m ≤ 3, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m (fun u : ℝ => u - c) u| ≤ 3 := by
  intro m hm u hu
  have hu1 : |u| ≤ 1 := by rw [abs_of_nonneg hu.1]; exact hu.2
  have hbase : |u - c| ≤ 3 :=
    (abs_sub_le_iff).mpr
      ⟨by linarith [(abs_le.mp hc).1, (abs_le.mp hu1).2],
       by linarith [(abs_le.mp hc).2, (abs_le.mp hu1).1]⟩
  interval_cases m
  · simpa only [iteratedDeriv_zero] using hbase
  · simp only [iteratedDeriv_affine_sub c]; norm_num
  · simp only [iteratedDeriv_affine_sub2 c]; norm_num
  · simp only [iteratedDeriv_affine_sub3 c]; norm_num

/-! ## The bound for the linear coefficient -/

theorem Eiter_lin_bound {B : ℝ} (hB : 0 < B)
    (hφ : ∀ m : ℕ, m ≤ 4 → ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv m Real.smoothTransition u| ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, |c| ≤ 2 → ∀ k : ℕ, k ≤ 4 → ∀ u : ℝ,
      |Eiter k (fun u : ℝ => u - c) Real.smoothTransition u| ≤ K := by
  have hBnn : ∀ m : ℕ, (0 : ℝ) ≤ (fun _ : ℕ => B) m := fun m => le_of_lt hB
  set K : ℝ := (∑ k ∈ Finset.range 5, Cbnd (fun _ : ℕ => (3 : ℝ)) (fun _ : ℕ => B) k 0) + 1 with hKdef
  have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range 5, Cbnd (fun _ : ℕ => (3 : ℝ)) (fun _ : ℕ => B) k 0 :=
    Finset.sum_nonneg (fun k _ => Cbnd_nonneg (fun m => by norm_num) hBnn k 0)
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hKone : (1 : ℝ) ≤ K := by rw [hKdef]; linarith
  refine ⟨K, hKpos, ?_⟩
  intro c hc k hk u
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · have hb := Eiter_deriv_bound (ρ := fun u : ℝ => u - c) (f := Real.smoothTransition)
      (M := fun _ : ℕ => (3 : ℝ)) (B := fun _ : ℕ => B) (fun m => by norm_num) hBnn
      (contDiff_sub_const c) contDiff_smoothTransition (iteratedDeriv_sub_const_le hc)
      (fun m hm u hu => hφ m hm u hu) k 0 (by omega) u hu
    have hb' : |Eiter k (fun u : ℝ => u - c) Real.smoothTransition u| ≤
        Cbnd (fun _ : ℕ => (3 : ℝ)) (fun _ : ℕ => B) k 0 := by
      simpa only [iteratedDeriv_zero] using hb
    have hle : Cbnd (fun _ : ℕ => (3 : ℝ)) (fun _ : ℕ => B) k 0 ≤
        ∑ k' ∈ Finset.range 5, Cbnd (fun _ : ℕ => (3 : ℝ)) (fun _ : ℕ => B) k' 0 :=
      Finset.single_le_sum (fun i _ => Cbnd_nonneg (fun m => by norm_num) hBnn i 0)
        (Finset.mem_range.mpr (by omega))
    rw [hKdef]
    linarith
  · have hlt : u < 0 ∨ 1 < u := by
      rcases lt_or_ge u 0 with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge fun h1 => hu ⟨h, h1⟩)
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp only [Eiter_zero]
      rcases hlt with h | h
      · rw [Real.smoothTransition.zero_of_nonpos h.le, abs_zero]
        exact le_of_lt hKpos
      · rw [Real.smoothTransition.one_of_one_le h.le, abs_one]
        exact hKone
    · rcases hlt with h | h
      · rw [Eiter_eq_zero_of_open_const (U := Set.Iio 0) isOpen_Iio h
            (fun w hw => by rw [Real.smoothTransition.zero_of_nonpos hw.le,
              Real.smoothTransition.zero_of_nonpos h.le]) k hkpos u h]
        rw [abs_zero]
        exact le_of_lt hKpos
      · rw [Eiter_eq_zero_of_open_const (U := Set.Ioi 1) isOpen_Ioi h
            (fun w hw => by rw [Real.smoothTransition.one_of_one_le hw.le,
              Real.smoothTransition.one_of_one_le h.le]) k hkpos u h]
        rw [abs_zero]
        exact le_of_lt hKpos

/-! ## The uniform bound for `cutA` -/

theorem Zbound : ∃ K : ℝ, 0 < K ∧ ∀ (N j : ℕ), j ≤ 4 → ∀ z θ : ℝ,
    |Work.Spaces.DzIter j (fun z' (_ : ℝ) => cutA N z') z θ| ≤ K := by
  obtain ⟨B, hBpos, hB⟩ := iteratedDeriv_smoothTransition_bound
  obtain ⟨K1, hK1pos, hK1⟩ := Eiter_lin_bound hBpos hB
  refine ⟨16 * K1 ^ 2 + 1, by positivity, ?_⟩
  intro N j hj z θ
  have hcf1 : ∀ n : ℕ, ContDiff ℝ n (fun z : ℝ => cutA1 ((N : ℝ) + 1) z 0) := by
    intro n
    have h : (fun z : ℝ => cutA1 ((N : ℝ) + 1) z 0)
        = fun z => Real.smoothTransition (((N : ℝ) + 1) * z - 1) := rfl
    rw [h]
    exact (Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hcf2 : ∀ n : ℕ, ContDiff ℝ n (fun z : ℝ => cutA2 ((N : ℝ) + 1) z 0) := by
    intro n
    have h : (fun z : ℝ => cutA2 ((N : ℝ) + 1) z 0)
        = fun z => Real.smoothTransition (2 - z / ((N : ℝ) + 1)) := rfl
    rw [h]
    exact (Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp
      (contDiff_const.sub (contDiff_id.div_const ((N : ℝ) + 1)))
  have hs : ∑ a ∈ Finset.range (j + 1), ((j.choose a : ℕ) : ℝ) ≤ 16 := by
    have h1 : ∑ a ∈ Finset.range (j + 1), j.choose a = 2 ^ j := Nat.sum_range_choose j
    have h2 : (∑ a ∈ Finset.range (j + 1), ((j.choose a : ℕ) : ℝ)) = ((2 ^ j : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, h1]
    rw [h2]
    calc ((2 ^ j : ℕ) : ℝ) ≤ ((2 ^ 4 : ℕ) : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num) hj
      _ = 16 := by norm_num
  have hterm : ∀ a ∈ Finset.range (j + 1),
      |(j.choose a : ℝ) * (DzIter1 a (fun z : ℝ => cutA1 ((N : ℝ) + 1) z 0) z
        * DzIter1 (j - a) (fun z : ℝ => cutA2 ((N : ℝ) + 1) z 0) z)| ≤
        (j.choose a : ℝ) * (K1 * K1) := by
    intro a ha
    have ha4 : a ≤ 4 := by have := Finset.mem_range.mp ha; omega
    have hja4 : j - a ≤ 4 := by omega
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j.choose a : ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_mul]
    refine mul_le_mul ?_ ?_ (abs_nonneg _) (le_of_lt hK1pos)
    · rw [DzIter1_cutA1]
      have h2 : (fun u : ℝ => u + 1) = fun u : ℝ => u - (-1) := by funext u; ring
      rw [h2]
      exact hK1 (-1) (by norm_num) a ha4 (((N : ℝ) + 1) * z - 1)
    · rw [DzIter1_cutA2]
      exact hK1 2 (by norm_num) (j - a) hja4 (2 - z / ((N : ℝ) + 1))
  have hcutA : cutA N = fun z => cutA1 ((N : ℝ) + 1) z 0 * cutA2 ((N : ℝ) + 1) z 0 := by
    funext z; simp only [cutA, cutA1, cutA2]
  rw [DzIter_const_apply j (cutA N) z θ, hcutA]
  calc |DzIter1 j (fun z' => cutA1 ((N : ℝ) + 1) z' 0 * cutA2 ((N : ℝ) + 1) z' 0) z|
      = |∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
          (DzIter1 a (fun z' => cutA1 ((N : ℝ) + 1) z' 0) z
            * DzIter1 (j - a) (fun z' => cutA2 ((N : ℝ) + 1) z' 0) z)| := by
        rw [DzIter1_mul j hcf1 hcf2]
    _ ≤ ∑ a ∈ Finset.range (j + 1), |(j.choose a : ℝ) *
          (DzIter1 a (fun z' => cutA1 ((N : ℝ) + 1) z' 0) z
            * DzIter1 (j - a) (fun z' => cutA2 ((N : ℝ) + 1) z' 0) z)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * (K1 * K1) := Finset.sum_le_sum hterm
    _ = (∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)) * (K1 * K1) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ 16 * (K1 * K1) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ ≤ 16 * K1 ^ 2 + 1 := by nlinarith [hK1pos]

/-! ## The two angular factors of `cutB` -/

/-- The first angular factor of `cutB N` with `λ = N+1`. -/
def cutB1 (lam : ℝ) : ℝ → ℝ → ℝ := fun _ θ => Real.smoothTransition (lam * θ - 1)

/-- The second angular factor of `cutB N` with `λ = N+1`. -/
def cutB2 (lam : ℝ) : ℝ → ℝ → ℝ :=
  fun _ θ => Real.smoothTransition (lam * (Real.pi / 2 - θ) - 1)

theorem cutB_eq (N : ℕ) :
    (fun _ (θ : ℝ) => cutB N θ)
      = fun z θ => cutB1 ((N : ℝ) + 1) z θ * cutB2 ((N : ℝ) + 1) z θ := by
  funext z θ
  simp only [cutB, cutB1, cutB2]

theorem contDiff_cutB1_slice (lam z : ℝ) : ∀ n : ℕ, ContDiff ℝ n (fun θ : ℝ => cutB1 lam z θ) := by
  intro n
  have h : (fun θ : ℝ => cutB1 lam z θ) = fun θ => Real.smoothTransition (lam * θ - 1) := rfl
  rw [h]
  exact (Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem contDiff_cutB2_slice (lam z : ℝ) : ∀ n : ℕ, ContDiff ℝ n (fun θ : ℝ => cutB2 lam z θ) := by
  intro n
  have h : (fun θ : ℝ => cutB2 lam z θ)
      = fun θ => Real.smoothTransition (lam * (Real.pi / 2 - θ) - 1) := rfl
  rw [h]
  exact (Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp
    ((contDiff_const.mul (contDiff_const.sub contDiff_id)).sub contDiff_const)

theorem DthIter_cutB1 (lam : ℝ) (hlam : lam ≠ 0) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (cutB1 lam) z θ
      = Eiter i (rhoM lam) Real.smoothTransition (lam * θ - 1) := by
  have h1 : cutB1 lam = (fun _ (θ' : ℝ) => Real.smoothTransition (lam * θ' + (-1))) := by
    funext z θ'
    simp only [cutB1, sub_eq_add_neg]
  rw [h1, DthIter_affine Real.smoothTransition lam (-1) hlam i contDiff_smoothTransition z θ]
  have h2 : (fun u : ℝ => lam * Real.sin (2 * ((u - (-1)) / lam))) = rhoM lam := by
    funext u
    simp only [rhoM]
    rw [show (2 * ((u - (-1)) / lam)) = 2 * (u + 1) / lam from by ring]
  have h3 : lam * θ + (-1) = lam * θ - 1 := by ring
  rw [h2, h3]

/-- The one-variable form of `DthIter_cutB1`. -/
theorem DthIter1_cutB1 (lam : ℝ) (hlam : lam ≠ 0) (i : ℕ) (θ : ℝ) :
    DthIter1 i (fun θ' => cutB1 lam 0 θ') θ
      = Eiter i (rhoM lam) Real.smoothTransition (lam * θ - 1) := by
  have h := DthIter_const_apply i (fun θ' => cutB1 lam 0 θ') 0 θ
  rw [← h]
  exact DthIter_cutB1 lam hlam i 0 θ

/-- The iterates of `E_ρ` for the negated coefficient pick up the sign `(-1)^k`. -/
theorem Eiter_neg {ρ f : ℝ → ℝ} (hρ : ∀ n : ℕ, ContDiff ℝ n ρ)
    (hf : ∀ n : ℕ, ContDiff ℝ n f) :
    ∀ k : ℕ, Eiter k (fun u => -ρ u) f = fun u => (-1) ^ k * Eiter k ρ f u := by
  intro k
  induction k with
  | zero => funext u; simp
  | succ k ih =>
      rw [Eiter_succ, ih, Eiter_succ, Eop]
      funext u
      have hd : deriv (fun u : ℝ => (-1) ^ k * Eiter k ρ f u)
          = fun u => (-1) ^ k * deriv (Eiter k ρ f) u := by
        funext u
        exact deriv_const_mul _
          (((contDiff_Eiter hρ hf k 1).differentiable (by norm_num)).differentiableAt)
      rw [hd]
      simp only [Eop, Pi.mul_apply]
      ring

theorem DthIter_cutB2 (lam : ℝ) (hlam : 1 ≤ lam) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (cutB2 lam) z θ
      = (-1) ^ i * Eiter i (rhoM lam) Real.smoothTransition (lam * (Real.pi / 2 - θ) - 1) := by
  have hne : lam ≠ 0 := by linarith
  have hne' : -lam ≠ 0 := by linarith
  have h1 : cutB2 lam
      = (fun _ (θ' : ℝ) => Real.smoothTransition ((-lam) * θ' + (lam * (Real.pi / 2) - 1))) := by
    funext z θ'
    simp only [cutB2]
    congr 1
    ring
  rw [h1, DthIter_affine Real.smoothTransition (-lam) (lam * (Real.pi / 2) - 1) hne' i
    contDiff_smoothTransition z θ]
  have hcoef : (fun u : ℝ => (-lam) * Real.sin (2 * ((u - (lam * (Real.pi / 2) - 1)) / (-lam))))
      = fun u : ℝ => - rhoM lam u := by
    funext u
    have harg : 2 * ((u - (lam * (Real.pi / 2) - 1)) / (-lam))
        = Real.pi - 2 * (u + 1) / lam := by
      field_simp
      ring
    rw [harg, Real.sin_pi_sub]
    simp only [rhoM]
    ring
  have harg2 : (-lam) * θ + (lam * (Real.pi / 2) - 1) = lam * (Real.pi / 2 - θ) - 1 := by ring
  rw [hcoef, harg2, Eiter_neg (contDiff_rhoM lam) contDiff_smoothTransition i]

/-- The one-variable form of `DthIter_cutB2`. -/
theorem DthIter1_cutB2 (lam : ℝ) (hlam : 1 ≤ lam) (i : ℕ) (θ : ℝ) :
    DthIter1 i (fun θ' => cutB2 lam 0 θ') θ
      = (-1) ^ i * Eiter i (rhoM lam) Real.smoothTransition
          (lam * (Real.pi / 2 - θ) - 1) := by
  have h := DthIter_const_apply i (fun θ' => cutB2 lam 0 θ') 0 θ
  rw [← h]
  exact DthIter_cutB2 lam hlam i 0 θ

/-! ## The derivatives of `ρ_λ` -/

theorem hasDerivAt_two_mul_add (lam u : ℝ) :
    HasDerivAt (fun u : ℝ => 2 * (u + 1) / lam) (2 / lam) u := by
  have h1 : HasDerivAt (fun u : ℝ => 2 * (u + 1)) 2 u := by
    have h := ((hasDerivAt_id u).const_mul 2).add_const 2
    simpa [mul_add, mul_one] using h
  exact h1.div_const lam

theorem deriv_rhoM_eq (lam : ℝ) (hlam : lam ≠ 0) :
    deriv (rhoM lam) = fun u => 2 * Real.cos (2 * (u + 1) / lam) := by
  funext u
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (2 * (u + 1) / lam))
      (Real.cos (2 * (u + 1) / lam) * (2 / lam)) u :=
    (Real.hasDerivAt_sin _).comp u (hasDerivAt_two_mul_add lam u)
  have hmul : HasDerivAt (fun u : ℝ => lam * Real.sin (2 * (u + 1) / lam))
      (lam * (Real.cos (2 * (u + 1) / lam) * (2 / lam))) u := hsin.const_mul lam
  show deriv (fun u : ℝ => lam * Real.sin (2 * (u + 1) / lam)) u = _
  rw [hmul.deriv]
  field_simp

theorem deriv2_rhoM_eq (lam : ℝ) (hlam : lam ≠ 0) :
    deriv (deriv (rhoM lam)) = fun u => -(4 / lam) * Real.sin (2 * (u + 1) / lam) := by
  rw [deriv_rhoM_eq lam hlam]
  funext u
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (2 * (u + 1) / lam))
      (-(Real.sin (2 * (u + 1) / lam)) * (2 / lam)) u :=
    (Real.hasDerivAt_cos _).comp u (hasDerivAt_two_mul_add lam u)
  have hmul : HasDerivAt (fun u : ℝ => 2 * Real.cos (2 * (u + 1) / lam))
      (2 * (-(Real.sin (2 * (u + 1) / lam)) * (2 / lam))) u := hcos.const_mul 2
  rw [hmul.deriv]
  ring

theorem deriv3_rhoM_eq (lam : ℝ) (hlam : lam ≠ 0) :
    deriv (deriv (deriv (rhoM lam)))
      = fun u => -(8 / lam ^ 2) * Real.cos (2 * (u + 1) / lam) := by
  rw [deriv2_rhoM_eq lam hlam]
  funext u
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (2 * (u + 1) / lam))
      (Real.cos (2 * (u + 1) / lam) * (2 / lam)) u :=
    (Real.hasDerivAt_sin _).comp u (hasDerivAt_two_mul_add lam u)
  have hmul : HasDerivAt (fun u : ℝ => -(4 / lam) * Real.sin (2 * (u + 1) / lam))
      (-(4 / lam) * (Real.cos (2 * (u + 1) / lam) * (2 / lam))) u :=
    hsin.const_mul (-(4 / lam))
  rw [hmul.deriv]
  ring

theorem iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  have e : iteratedDeriv 2 f = iteratedDeriv 1 (deriv f) := iteratedDeriv_succ' (n := 1) (f := f)
  rw [e, iteratedDeriv_one]

theorem iteratedDeriv_three_eq (f : ℝ → ℝ) :
    iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  have e : iteratedDeriv 3 f = iteratedDeriv 2 (deriv f) := iteratedDeriv_succ' (n := 2) (f := f)
  rw [e, iteratedDeriv_two_eq]

theorem rhoM_iteratedDeriv_le (lam : ℝ) (hlam : 1 ≤ lam) :
    ∀ m ≤ 3, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m (rhoM lam) u| ≤ 8 := by
  have hne : lam ≠ 0 := by linarith
  have hpos : 0 < lam := by linarith
  intro m hm u hu
  interval_cases m
  · simp only [iteratedDeriv_zero]
    unfold rhoM
    have hu1 : (0 : ℝ) ≤ u + 1 := by linarith [hu.1]
    have hxnn : 0 ≤ 2 * (u + 1) / lam := by positivity
    calc |lam * Real.sin (2 * (u + 1) / lam)|
        = lam * |Real.sin (2 * (u + 1) / lam)| := by rw [abs_mul, abs_of_pos hpos]
      _ ≤ lam * |2 * (u + 1) / lam| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs hpos.le
      _ = lam * (2 * (u + 1) / lam) := by rw [abs_of_nonneg hxnn]
      _ = 2 * (u + 1) := by field_simp
      _ ≤ 8 := by linarith [hu.2]
  · rw [iteratedDeriv_one, deriv_rhoM_eq lam hne, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := abs_cos_le_one (2 * (u + 1) / lam)
    linarith
  · rw [iteratedDeriv_two_eq (rhoM lam), deriv2_rhoM_eq lam hne]
    have h4 : |4 / lam| ≤ 4 := by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 / lam), div_le_iff₀ hpos]
      linarith
    calc |-(4 / lam) * Real.sin (2 * (u + 1) / lam)|
        = |4 / lam| * |Real.sin (2 * (u + 1) / lam)| := by rw [abs_mul, abs_neg]
      _ ≤ 4 * 1 := mul_le_mul h4 (abs_sin_le_one _) (abs_nonneg _) (by norm_num)
      _ ≤ 8 := by norm_num
  · rw [iteratedDeriv_three_eq (rhoM lam), deriv3_rhoM_eq lam hne]
    have h8 : |8 / lam ^ 2| ≤ 8 := by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 / lam ^ 2),
        div_le_iff₀ (by positivity : (0 : ℝ) < lam ^ 2)]
      nlinarith
    calc |-(8 / lam ^ 2) * Real.cos (2 * (u + 1) / lam)|
        = |8 / lam ^ 2| * |Real.cos (2 * (u + 1) / lam)| := by rw [abs_mul, abs_neg]
      _ ≤ 8 * 1 := mul_le_mul h8 (abs_cos_le_one _) (abs_nonneg _) (by norm_num)
      _ ≤ 8 := by norm_num

/-! ## The bound for the `ρ_λ` coefficient -/

theorem Eiter_rhoM_bound {B : ℝ} (hB : 0 < B)
    (hφ : ∀ m : ℕ, m ≤ 4 → ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv m Real.smoothTransition u| ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ lam : ℝ, 1 ≤ lam → ∀ k : ℕ, k ≤ 4 → ∀ u : ℝ,
      |Eiter k (rhoM lam) Real.smoothTransition u| ≤ K := by
  have hBnn : ∀ m : ℕ, (0 : ℝ) ≤ (fun _ : ℕ => B) m := fun m => le_of_lt hB
  set K : ℝ := (∑ k ∈ Finset.range 5,
      Cbnd (fun _ : ℕ => (8 : ℝ)) (fun _ : ℕ => B) k 0) + 1 with hKdef
  have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range 5,
      Cbnd (fun _ : ℕ => (8 : ℝ)) (fun _ : ℕ => B) k 0 :=
    Finset.sum_nonneg (fun k _ => Cbnd_nonneg (fun m => by norm_num) hBnn k 0)
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hKone : (1 : ℝ) ≤ K := by rw [hKdef]; linarith
  refine ⟨K, hKpos, ?_⟩
  intro lam hlam k hk u
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · have hb := Eiter_deriv_bound (ρ := rhoM lam) (f := Real.smoothTransition)
      (M := fun _ : ℕ => (8 : ℝ)) (B := fun _ : ℕ => B) (fun m => by norm_num) hBnn
      (contDiff_rhoM lam) contDiff_smoothTransition
      (fun m hm u hu => rhoM_iteratedDeriv_le lam hlam m hm u hu)
      (fun m hm u hu => hφ m hm u hu) k 0 (by omega) u hu
    have hb' : |Eiter k (rhoM lam) Real.smoothTransition u| ≤
        Cbnd (fun _ : ℕ => (8 : ℝ)) (fun _ : ℕ => B) k 0 := by
      simpa only [iteratedDeriv_zero] using hb
    have hle : Cbnd (fun _ : ℕ => (8 : ℝ)) (fun _ : ℕ => B) k 0 ≤
        ∑ k' ∈ Finset.range 5, Cbnd (fun _ : ℕ => (8 : ℝ)) (fun _ : ℕ => B) k' 0 :=
      Finset.single_le_sum (fun i _ => Cbnd_nonneg (fun m => by norm_num) hBnn i 0)
        (Finset.mem_range.mpr (by omega))
    rw [hKdef]
    linarith
  · have hlt : u < 0 ∨ 1 < u := by
      rcases lt_or_ge u 0 with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge fun h1 => hu ⟨h, h1⟩)
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp only [Eiter_zero]
      rcases hlt with h | h
      · rw [Real.smoothTransition.zero_of_nonpos h.le]
        simpa using le_of_lt hKpos
      · rw [Real.smoothTransition.one_of_one_le h.le, abs_one]
        exact hKone
    · rcases hlt with h | h
      · rw [Eiter_eq_zero_of_open_const (U := Set.Iio 0) isOpen_Iio h
            (fun w hw => by rw [Real.smoothTransition.zero_of_nonpos hw.le,
              Real.smoothTransition.zero_of_nonpos h.le]) k hkpos u h]
        simpa using le_of_lt hKpos
      · rw [Eiter_eq_zero_of_open_const (U := Set.Ioi 1) isOpen_Ioi h
            (fun w hw => by rw [Real.smoothTransition.one_of_one_le hw.le,
              Real.smoothTransition.one_of_one_le h.le]) k hkpos u h]
        rw [abs_zero]
        exact le_of_lt hKpos

/-! ## The uniform bound for `cutB` -/

theorem Tbound : ∃ K : ℝ, 0 < K ∧ ∀ (N i : ℕ), i ≤ 4 → ∀ z θ : ℝ,
    |Work.Spaces.DthIter i (fun (_ : ℝ) θ' => cutB N θ') z θ| ≤ K := by
  obtain ⟨B, hBpos, hB⟩ := iteratedDeriv_smoothTransition_bound
  obtain ⟨K1, hK1pos, hK1⟩ := Eiter_rhoM_bound hBpos hB
  refine ⟨16 * K1 ^ 2 + 1, by positivity, ?_⟩
  intro N i hi z θ
  have hL1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hL0 : ((N : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < (N : ℝ) + 1)
  have hs : ∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) ≤ 16 := by
    have h1 : ∑ a ∈ Finset.range (i + 1), i.choose a = 2 ^ i := Nat.sum_range_choose i
    have h2 : (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) = ((2 ^ i : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, h1]
    rw [h2]
    calc ((2 ^ i : ℕ) : ℝ) ≤ ((2 ^ 4 : ℕ) : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num) hi
      _ = 16 := by norm_num
  have hcf1 : ∀ n : ℕ, ContDiff ℝ n (fun θ : ℝ => cutB1 ((N : ℝ) + 1) 0 θ) :=
    contDiff_cutB1_slice _ 0
  have hcf2 : ∀ n : ℕ, ContDiff ℝ n (fun θ : ℝ => cutB2 ((N : ℝ) + 1) 0 θ) :=
    contDiff_cutB2_slice _ 0
  have hterm : ∀ a ∈ Finset.range (i + 1),
      |(i.choose a : ℝ) * (DthIter1 a (fun θ : ℝ => cutB1 ((N : ℝ) + 1) 0 θ) θ
        * DthIter1 (i - a) (fun θ : ℝ => cutB2 ((N : ℝ) + 1) 0 θ) θ)| ≤
        (i.choose a : ℝ) * (K1 * K1) := by
    intro a ha
    have ha4 : a ≤ 4 := by have := Finset.mem_range.mp ha; omega
    have hia4 : i - a ≤ 4 := by omega
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i.choose a : ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_mul]
    refine mul_le_mul ?_ ?_ (abs_nonneg _) (le_of_lt hK1pos)
    · rw [DthIter1_cutB1 ((N : ℝ) + 1) hL0]
      exact hK1 ((N : ℝ) + 1) hL1 a ha4 (((N : ℝ) + 1) * θ - 1)
    · rw [DthIter1_cutB2 ((N : ℝ) + 1) hL1, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul]
      exact hK1 ((N : ℝ) + 1) hL1 (i - a) hia4 (((N : ℝ) + 1) * (Real.pi / 2 - θ) - 1)
  have hcutB : cutB N = fun θ => cutB1 ((N : ℝ) + 1) 0 θ * cutB2 ((N : ℝ) + 1) 0 θ := by
    funext θ; simp only [cutB, cutB1, cutB2]
  rw [DthIter_const_apply i (cutB N) z θ, hcutB]
  calc |DthIter1 i (fun θ' => cutB1 ((N : ℝ) + 1) 0 θ' * cutB2 ((N : ℝ) + 1) 0 θ') θ|
      = |∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
          (DthIter1 a (fun θ' => cutB1 ((N : ℝ) + 1) 0 θ') θ
            * DthIter1 (i - a) (fun θ' => cutB2 ((N : ℝ) + 1) 0 θ') θ)| := by
        rw [DthIter1_mul i hcf1 hcf2]
    _ ≤ ∑ a ∈ Finset.range (i + 1), |(i.choose a : ℝ) *
          (DthIter1 a (fun θ' => cutB1 ((N : ℝ) + 1) 0 θ') θ
            * DthIter1 (i - a) (fun θ' => cutB2 ((N : ℝ) + 1) 0 θ') θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) * (K1 * K1) := Finset.sum_le_sum hterm
    _ = (∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)) * (K1 * K1) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ 16 * (K1 * K1) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ ≤ 16 * K1 ^ 2 + 1 := by nlinarith [hK1pos]


end Work.FTS.GalBasis.cc
