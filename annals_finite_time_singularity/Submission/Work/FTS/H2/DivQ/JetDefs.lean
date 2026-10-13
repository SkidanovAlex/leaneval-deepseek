/-
Copyright: work module for the Elgindi finite-time singularity project.

# The interval `[0, xNear]`, the smooth neighbourhood `U`, and the "bounded jet" predicate

This file collects the vocabulary used in `aCoeff_bounds.lean`:

* `U = (-3/4, 3/4)`, an open neighbourhood of `[0, xNear]` on which `kappa = cos(arcsin ·)` is
  smooth (recall `xNear = sin(π/4) = √2/2 < 3/4`);
* the elementary bounds on `xNear`; `kappa_eq_sqrt`, `contDiffOn_kappa`;
* `JetBdd K g C`, the statement that `g` is smooth on `U`, `C ≥ 0`, and the first `K + 1`
  derivatives of `g` are bounded by `C` on `[0, xNear]`, together with the closure lemmas
  (sum, product, derivative, constant) which are the engine of the induction in
  `aCoeff_bounds`;
* `genCoeff`, the common recursion of `bCoeff` and `aCoeff` (`bCoeff` is the instance with
  initial datum `1`, `aCoeff` the instance with initial datum `2κ`).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Submission.Work.FTS.H2.DivQ.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false

/-! ### Basic facts about `xNear` and the neighbourhood `U` -/

/-- An open neighbourhood of the interval `[0, xNear]` on which `κ` is smooth: since
`xNear = √2/2 < 3/4`, the interval `(-3/4,3/4)` works. -/
def U : Set ℝ := Set.Ioo (-(3 / 4)) (3 / 4)

lemma xNear_nonneg : 0 ≤ xNear := by
  rw [xNear, Real.sin_pi_div_four]
  positivity

lemma xNear_pos : 0 < xNear := by
  rw [xNear, Real.sin_pi_div_four]
  positivity

lemma xNear_lt : xNear < 3 / 4 := by
  rw [xNear, Real.sin_pi_div_four]
  have h2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3 / 2)]
    norm_num
  linarith

lemma xNear_le_one : xNear ≤ 1 := by linarith [xNear_lt]

lemma U_isOpen : IsOpen U := isOpen_Ioo

lemma zero_mem_U : (0 : ℝ) ∈ U := ⟨by norm_num, by norm_num⟩

lemma xNear_mem_U : xNear ∈ U := ⟨by linarith [xNear_nonneg], xNear_lt⟩

lemma Icc_subset_U : Set.Icc (0 : ℝ) xNear ⊆ U := fun _ hx =>
  ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩

/-! ### `κ = cos(arcsin ·)` on `U` -/

lemma two_mul_thetaOf (x : ℝ) : 2 * thetaOf x = Real.arcsin x := by
  rw [thetaOf]; ring

lemma kappa_eq_cos_arcsin (x : ℝ) : kappa x = Real.cos (Real.arcsin x) := by
  rw [kappa, two_mul_thetaOf]

/-- On `[-1,1]` (indeed everywhere, by the junk-value convention for `arcsin`) the function `κ`
is `√(1 - x²)`. -/
lemma kappa_eq_sqrt (x : ℝ) : kappa x = Real.sqrt (1 - x ^ 2) := by
  rw [kappa_eq_cos_arcsin, Real.cos_arcsin]

/-- `κ` is smooth on the neighbourhood `U` of `[0,xNear]`. -/
lemma contDiffOn_kappa : ContDiffOn ℝ ⊤ kappa U := by
  have hsub : U ⊆ ({-1, 1} : Set ℝ)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h1 : ContDiffOn ℝ ⊤ Real.arcsin U :=
    (Real.contDiffOn_arcsin (n := ⊤)).mono hsub
  have h2 : ContDiffOn ℝ ⊤ (fun x => Real.cos (Real.arcsin x)) U :=
    Real.contDiff_cos.comp_contDiffOn h1
  exact h2.congr fun x _ => kappa_eq_cos_arcsin x

/-! ### The bounded-jet predicate -/

/-- `JetBdd K g C` says that `g` is smooth on the neighbourhood `U` of `[0, xNear]`, that
`C ≥ 0`, and that on `[0, xNear]` the first `K+1` derivatives of `g` are bounded by `C`. -/
def JetBdd (K : ℕ) (g : ℝ → ℝ) (C : ℝ) : Prop :=
  ContDiffOn ℝ ⊤ g U ∧ 0 ≤ C ∧ ∀ k ≤ K, ∀ x ∈ Set.Icc (0 : ℝ) xNear, |iteratedDeriv k g x| ≤ C

lemma JetBdd.jet_smooth {K : ℕ} {g : ℝ → ℝ} {C : ℝ} (h : JetBdd K g C) :
    ContDiffOn ℝ ⊤ g U := h.1

lemma JetBdd.jet_nonneg {K : ℕ} {g : ℝ → ℝ} {C : ℝ} (h : JetBdd K g C) : 0 ≤ C := h.2.1

lemma JetBdd.jet_bound {K : ℕ} {g : ℝ → ℝ} {C : ℝ} (h : JetBdd K g C) :
    ∀ k ≤ K, ∀ x ∈ Set.Icc (0 : ℝ) xNear, |iteratedDeriv k g x| ≤ C := h.2.2

lemma JetBdd.jet_mono {K K' : ℕ} (hKK : K' ≤ K) {g : ℝ → ℝ} {C : ℝ} (h : JetBdd K g C) :
    JetBdd K' g C :=
  ⟨h.1, h.2.1, fun k hk => h.2.2 k (le_trans hk hKK)⟩

lemma JetBdd.jet_le {K : ℕ} {g : ℝ → ℝ} {C D : ℝ} (h : JetBdd K g C) (hCD : C ≤ D) :
    JetBdd K g D :=
  ⟨h.1, le_trans h.2.1 hCD, fun k hk x hx => le_trans (h.2.2 k hk x hx) hCD⟩

lemma smooth_contDiffAt {f : ℝ → ℝ} (hf : ContDiffOn ℝ ⊤ f U) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) xNear) (k : ℕ) : ContDiffAt ℝ (k : WithTop ℕ∞) f x :=
  (hf.contDiffAt (U_isOpen.mem_nhds (Icc_subset_U hx))).of_le le_top

lemma JetBdd.jet_add {K : ℕ} {f g : ℝ → ℝ} {Cf Cg : ℝ} (hf : JetBdd K f Cf)
    (hg : JetBdd K g Cg) : JetBdd K (f + g) (Cf + Cg) := by
  refine ⟨hf.1.add hg.1, by linarith [hf.2.1, hg.2.1], ?_⟩
  intro k hk x hx
  rw [iteratedDeriv_add (smooth_contDiffAt hf.1 hx k) (smooth_contDiffAt hg.1 hx k)]
  exact (abs_add_le _ _).trans (add_le_add (hf.2.2 k hk x hx) (hg.2.2 k hk x hx))

lemma JetBdd.jet_const (K : ℕ) (c : ℝ) : JetBdd K (fun _ : ℝ => c) |c| := by
  refine ⟨contDiffOn_const, abs_nonneg c, ?_⟩
  intro k hk x hx
  rw [iteratedDeriv_const]
  split_ifs <;> simp

lemma JetBdd.jet_zero (K : ℕ) : JetBdd K (fun _ : ℝ => (0 : ℝ)) 0 := by
  refine ⟨contDiffOn_const, le_refl 0, ?_⟩
  intro k hk x hx
  simp

lemma JetBdd.jet_deriv {K : ℕ} {f : ℝ → ℝ} {C : ℝ} (hf : JetBdd (K + 1) f C) :
    JetBdd K (deriv f) C := by
  refine ⟨hf.1.deriv_of_isOpen U_isOpen (m := ⊤) (by simp), hf.2.1, ?_⟩
  intro k hk x hx
  have hiter : iteratedDeriv k (deriv f) x = iteratedDeriv (k + 1) f x := by
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
      Function.iterate_succ_apply]
  rw [hiter]
  exact hf.2.2 (k + 1) (by omega) x hx

/-- The identity function has bounded jets on `[0,xNear]`, with bound `1`. -/
lemma JetBdd.jet_id (K : ℕ) : JetBdd K (fun x : ℝ => x) 1 := by
  have hd1 : deriv (fun x : ℝ => x) = fun _ => (1 : ℝ) := funext fun x => deriv_id x
  have hd0 : deriv (0 : ℝ → ℝ) = 0 := funext fun x => deriv_const x 0
  have hiter0 : ∀ k : ℕ, deriv^[k] (0 : ℝ → ℝ) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, hd0, ih]
  have hd11 : deriv (fun _ : ℝ => (1 : ℝ)) = 0 := funext fun x => deriv_const x 1
  have hdd : deriv (deriv (fun x : ℝ => x)) = 0 := by rw [hd1, hd11]
  have h2 : ∀ k : ℕ, deriv^[Nat.succ (Nat.succ k)] (fun x : ℝ => x) = 0 := by
    intro k
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    rw [hdd, hiter0 k]
  refine ⟨contDiffOn_id, by norm_num, ?_⟩
  intro k hk x hx
  rcases k with _ | k
  · rw [iteratedDeriv_zero]
    rw [abs_of_nonneg hx.1]
    linarith [hx.2, xNear_le_one]
  · rcases k with _ | k
    · rw [iteratedDeriv_one]
      rw [hd1]
      norm_num
    · rw [iteratedDeriv_eq_iterate]
      rw [h2 k]
      norm_num

lemma JetBdd.jet_mul {K : ℕ} {f g : ℝ → ℝ} {Cf Cg : ℝ} (hf : JetBdd K f Cf)
    (hg : JetBdd K g Cg) : JetBdd K (f * g) ((2 : ℝ) ^ K * Cf * Cg) := by
  refine ⟨hf.1.mul hg.1,
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) K) hf.2.1) hg.2.1, ?_⟩
  intro k hk x hx
  rw [iteratedDeriv_mul (n := k) (smooth_contDiffAt hf.1 hx k) (smooth_contDiffAt hg.1 hx k)]
  calc |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * iteratedDeriv i f x *
        iteratedDeriv (k - i) g x|
      ≤ ∑ i ∈ Finset.range (k + 1),
          |(k.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (k - i) g x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cf * Cg := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : |iteratedDeriv i f x| ≤ Cf := hf.2.2 i (le_trans hik hk) x hx
        have h2 : |iteratedDeriv (k - i) g x| ≤ Cg :=
          hg.2.2 (k - i) (le_trans (Nat.sub_le _ _) hk) x hx
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (k.choose i))]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (k.choose i))) h2
          (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg (k.choose i)) hf.2.1)
    _ = (2 : ℝ) ^ k * Cf * Cg := by
        have hsum : (∑ i ∈ Finset.range (k + 1), ((k.choose i : ℕ) : ℝ)) = (2 : ℝ) ^ k := by
          rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
          norm_num
        rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
    _ ≤ (2 : ℝ) ^ K * Cf * Cg := by
        have h : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hk
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hf.2.1) hg.2.1

lemma JetBdd.jet_const_mul {K : ℕ} {f : ℝ → ℝ} {C : ℝ} (c : ℝ) (hf : JetBdd K f C) :
    JetBdd K (fun x => c * f x) ((2 : ℝ) ^ K * |c| * C) :=
  JetBdd.jet_mul (JetBdd.jet_const K c) hf

/-! ### A compactness bound: smooth on `U` implies bounded jets on `[0,xNear]` -/

lemma contDiffOn_iterate_deriv {f : ℝ → ℝ} (hf : ContDiffOn ℝ ⊤ f U) (k : ℕ) :
    ContDiffOn ℝ ⊤ (deriv^[k] f) U := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
      have h : ContDiffOn ℝ ⊤ (deriv (deriv^[k] f)) U :=
        ih.deriv_of_isOpen U_isOpen (m := ⊤) (by simp)
      simpa [Function.iterate_succ_apply'] using h

theorem exists_jetBdd_of_contDiffOn (K : ℕ) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ⊤ f U) :
    ∃ C : ℝ, JetBdd K f C := by
  have hbdd : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Set.Icc (0 : ℝ) xNear, |iteratedDeriv k f x| ≤ C := by
    intro k
    have hcont : ContinuousOn (fun x => iteratedDeriv k f x) (Set.Icc (0 : ℝ) xNear) := by
      have h := ((contDiffOn_iterate_deriv hf k).continuousOn).mono Icc_subset_U
      simpa [iteratedDeriv_eq_iterate] using h
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    exact ⟨max C 0, le_max_right _ _, fun x hx => le_trans (by simpa using hC x hx) (le_max_left _ _)⟩
  choose C hC using hbdd
  refine ⟨(∑ k ∈ Finset.range (K + 1), C k) + 1, hf,
    add_nonneg (Finset.sum_nonneg fun i _ => (hC i).1) zero_le_one, ?_⟩
  intro k hk x hx
  have hmem : k ∈ Finset.range (K + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)
  have hle : C k ≤ ∑ k ∈ Finset.range (K + 1), C k :=
    Finset.single_le_sum (fun i _ => (hC i).1) hmem
  calc |iteratedDeriv k f x| ≤ C k := (hC k).2 x hx
    _ ≤ (∑ k ∈ Finset.range (K + 1), C k) + 1 := by linarith

/-! ### The common recursion `genCoeff` -/

/-- The recursion shared by `bCoeff` (`init = 1`) and `aCoeff` (`init = 2κ`): the coefficients
of the expansion of `G^i (init · u)`, where the recursion step is the one of the `x`-form of
`D_θ`. -/
def genCoeff (init : ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, j => fun x => if j = 0 then init x else 0
  | (i + 1), j => fun x =>
      2 * kappa x * (x * deriv (genCoeff init i j) x + (j : ℝ) * genCoeff init i j x)
        + (if j = 0 then 0 else 2 * kappa x * genCoeff init i (j - 1) x)

end Work.FTS.H2.DivQ
