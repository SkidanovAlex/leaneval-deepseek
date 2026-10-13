import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Series.eFamEneAux
import Submission.Work.FTS.PhiStar.Series.eFamSupDefs
import Submission.Work.FTS.PhiStar.Series.eFamSupAux.ug_bound
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Growth of the iterated derivatives of the Gegenbauer family `eFam`

`eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)` is a trigonometric polynomial of degree `2m+2`
solving the singular Sturm–Liouville equation

  `(cos θ · f')' = (1/cos θ - M cos θ) · f`,   `M = eM m = (2m+2)(2m+3)`,

equivalently `f'' = tan θ · f' + (sec²θ - M) · f` on `(0, π/2)`.  On a compact subinterval
`[θ₁, θ₂] ⊂ (0, π/2)` the coefficients `tan` and `sec²` are smooth with *bounded* derivatives,
so differentiating the equation `k` times bounds `f^{(k+2)}` by the lower derivatives plus the
single term `-M f^{(k)}`.  With the two base bounds `|f| ≤ 3(m+1)` and `|f'| ≤ C(m+1)²` this
closes by induction on `k` with the exponents `k+1`, which is the claimed
`|f^{(j)}| ≤ C (m+1)^{j+1}`.

The two base bounds are taken here from the *radial energy* machinery of
`Series.eFamSupDefs` (`|eFam m θ| ≤ √(Npsi m)` from `Series.eFam_sup_le`, and the new
`abs_deriv_eFam_le` below, which converts the bound `|(ug m)'| ≤ Npsi m` supplied by
`ene_le` into a bound for the `θ`-derivative of `eFam m`).  This keeps the module's import
closure disjoint from `Series.Deleg.psiAngDefs` (the two modules of the tree that both declare
`Work.FTS.PhiStar.Series.Deleg.gC_abs_bound` cannot be imported together).
-/

namespace Work.FTS.PhiStar.Honesty.CptQSmooth.CleanAng

set_option maxHeartbeats 1000000

open scoped Real
open Work.FTS.PhiStar.Gegenbauer (eFam gC)

/-! ## 1. Smoothness of every finite order -/

/-- The Gegenbauer polynomials `gC k` are smooth of every finite order (the recurrence is built
from products, linear combinations and division by a constant). -/
lemma contDiff_gC_nat : ∀ k n : ℕ, ContDiff ℝ n (gC k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
    intro n
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    exact contDiff_const
  | one =>
    intro n
    rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl]
    exact contDiff_const.mul contDiff_id
  | more k ih1 ih2 =>
    intro n
    rw [show gC (k + 2) = (fun x =>
        (2 * ((k : ℝ) + 5 / 2) * x * gC (k + 1) x
          - ((k : ℝ) + 3) * gC k x) / ((k : ℝ) + 2)) from rfl]
    exact (((contDiff_const.mul contDiff_id).mul (ih2 n)).sub
      (contDiff_const.mul (ih1 n))).div_const _

/-- `eFam m = cos · (gC (2m+1) ∘ sin)` is smooth of every finite order. -/
lemma contDiff_eFam_nat (m n : ℕ) : ContDiff ℝ n (eFam m) := by
  rw [show eFam m = fun θ => Real.cos θ * gC (2 * m + 1) (Real.sin θ) from rfl]
  exact Real.contDiff_cos.mul ((contDiff_gC_nat (2 * m + 1) n).comp Real.contDiff_sin)

/-! ## 2. Calculus of `iteratedDeriv` -/

lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

lemma iteratedDeriv_deriv_apply (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv n (deriv f) x = iteratedDeriv (n + 1) f x := by
  rw [iteratedDeriv_succ']

lemma iteratedDeriv_two_add (k : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv (k + 2) f = iteratedDeriv k (iteratedDeriv 2 f) := by
  rw [show k + 2 = k + 1 + 1 by omega, iteratedDeriv_succ', iteratedDeriv_succ',
    ← iteratedDeriv_two_eq f]

/-! ## 3. The Leibniz expansion of the differentiated equation -/

/-- The `k`-fold derivative of the right-hand side `a·f' + b·f - c·f` of a second order
equation, expanded by the Leibniz rule. -/
lemma iteratedDeriv_ode_expand {f a b : ℝ → ℝ} {c : ℝ} {k : ℕ} {x : ℝ}
    (ha : ContDiffAt ℝ k a x) (hb : ContDiffAt ℝ k b x) (hd : ContDiffAt ℝ k (deriv f) x)
    (hf : ContDiffAt ℝ k f x) :
    iteratedDeriv k (a * deriv f + b * f - (fun _ : ℝ => c) * f) x
      = (∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℝ) * (iteratedDeriv i a x * iteratedDeriv (k - i) (deriv f) x))
        + (∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℝ) * (iteratedDeriv i b x * iteratedDeriv (k - i) f x))
        - c * iteratedDeriv k f x := by
  rw [iteratedDeriv_sub (f := a * deriv f + b * f) (g := (fun _ : ℝ => c) * f)
        ((ha.mul hd).add (hb.mul hf)) ((contDiffAt_const (c := c)).mul hf)]
  rw [iteratedDeriv_add (f := a * deriv f) (g := b * f) (ha.mul hd) (hb.mul hf)]
  rw [iteratedDeriv_mul (f := a) (g := deriv f) ha hd,
      iteratedDeriv_mul (f := b) (g := f) hb hf]
  rw [show ((fun _ : ℝ => c) * f) = fun x => c * f x from rfl]
  rw [iteratedDeriv_const_mul (c := c) (n := k) (f := f) hf]
  ring_nf

/-! ## 4. The second order equation for `eFam m` -/

/-- The equation `f'' = tan θ f' + (sec²θ - M) f` for `f = eFam m` on the open interval
`(0, π/2)`, written as an identity of functions. -/
lemma eFam_ode_eqOn (m : ℕ) :
    Set.EqOn (iteratedDeriv 2 (eFam m))
      ((fun θ : ℝ => Real.tan θ) * deriv (eFam m)
        + (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) * eFam m
        - (fun _ : ℝ => Work.FTS.PhiStar.Series.eM m) * eFam m)
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  rw [iteratedDeriv_two_eq, Work.FTS.PhiStar.Series.eFam_deriv2_eq m θ hcos]
  ring

/-- The `tan`-sum of the Leibniz expansion of `f^{(k+2)}`:
`∑_{i≤k} C(k,i) (tan)^{(i)}(θ) f^{(k+1-i)}(θ)`. -/
noncomputable def tanSum (k : ℕ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * (iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ * iteratedDeriv (k + 1 - i) f θ)

/-- The `sec²`-sum of the Leibniz expansion of `f^{(k+2)}`:
`∑_{i≤k} C(k,i) (sec²)^{(i)}(θ) f^{(k-i)}(θ)`. -/
noncomputable def secSum (k : ℕ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * (iteratedDeriv i (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) θ * iteratedDeriv (k - i) f θ)

/-- **The differentiated equation.**  For `θ ∈ (0, π/2)`,

  `f^{(k+2)}(θ) = tanSum k f θ + secSum k f θ - M f^{(k)}(θ)`. -/
lemma eFam_iteratedDeriv_ode (m k : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    iteratedDeriv (k + 2) (eFam m) θ
      = tanSum k (eFam m) θ + secSum k (eFam m) θ
        - Work.FTS.PhiStar.Series.eM m * iteratedDeriv k (eFam m) θ := by
  rw [tanSum, secSum]
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hf : ContDiffAt ℝ k (eFam m) θ := (contDiff_eFam_nat m k).contDiffAt
  have hd : ContDiffAt ℝ k (deriv (eFam m)) θ :=
    ((contDiff_eFam_nat m (k + 1)).deriv' (n := (k : ℕ∞))).contDiffAt
  have ha : ContDiffAt ℝ k (fun θ : ℝ => Real.tan θ) θ := Real.contDiffAt_tan.mpr hcos
  have hb : ContDiffAt ℝ k (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) θ := by
    rw [show (fun θ : ℝ => 1 / (Real.cos θ) ^ 2)
        = (fun _ : ℝ => (1 : ℝ)) / (fun θ : ℝ => (Real.cos θ) ^ 2) from rfl]
    exact (contDiffAt_const (c := (1 : ℝ))).div (Real.contDiff_cos.contDiffAt.pow 2)
      (pow_ne_zero 2 hcos)
  have hEq : iteratedDeriv k (iteratedDeriv 2 (eFam m)) θ
      = iteratedDeriv k ((fun θ : ℝ => Real.tan θ) * deriv (eFam m)
          + (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) * eFam m
          - (fun _ : ℝ => Work.FTS.PhiStar.Series.eM m) * eFam m) θ :=
    (eFam_ode_eqOn m).iteratedDeriv_of_isOpen isOpen_Ioo k hθ
  rw [iteratedDeriv_two_add k (eFam m), hEq,
      iteratedDeriv_ode_expand (f := eFam m) (a := fun θ : ℝ => Real.tan θ)
        (b := fun θ : ℝ => 1 / (Real.cos θ) ^ 2) (c := Work.FTS.PhiStar.Series.eM m)
        (k := k) (x := θ) ha hb hd hf]
  have hs : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ
          * iteratedDeriv (k - i) (deriv (eFam m)) θ))
      = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ
          * iteratedDeriv (k + 1 - i) (eFam m) θ)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [iteratedDeriv_deriv_apply (k - i) (eFam m) θ, show k - i + 1 = k + 1 - i by omega]
  rw [hs]

/-! ## 5. Bounds for the derivatives of the coefficients on a compact subinterval -/

/-- Derivatives of a function which is smooth of every order on an open set are bounded on any
closed subinterval. -/
lemma exists_bound_iteratedDeriv_of_contDiffOn {g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n g s) {A B : ℝ} (hsub : Set.Icc A B ⊆ s) :
    ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Icc A B, |iteratedDeriv i g θ| ≤ C := by
  intro i
  have hcont : ContinuousOn (iteratedDeriv i g) (Set.Icc A B) := by
    have h1 : ContinuousOn (iteratedDerivWithin i g s) s :=
      (hg i).continuousOn_iteratedDerivWithin le_rfl hs.uniqueDiffOn
    exact (h1.congr (iteratedDerivWithin_of_isOpen hs).symm).mono hsub
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  refine le_trans ?_ (le_max_left C 0)
  simpa [Real.norm_eq_abs] using hC θ hθ

/-- The derivatives of `tan` are bounded on `[A, B] ⊂ (0, π/2)`. -/
lemma exists_bound_iteratedDeriv_tan {A B : ℝ} (hA : 0 < A) (hB : B < Real.pi / 2) :
    ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Icc A B,
      |iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ| ≤ C := by
  refine exists_bound_iteratedDeriv_of_contDiffOn (s := Set.Ioo (A / 2) (Real.pi / 2)) isOpen_Ioo ?_ ?_
  · intro n
    have hcos : ∀ θ ∈ Set.Ioo (A / 2) (Real.pi / 2), Real.cos θ ≠ 0 := by
      intro θ hθ
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hA, Real.pi_pos], hθ.2⟩)
    refine ContDiffOn.congr ?_ (fun θ _ => Real.tan_eq_sin_div_cos θ)
    exact ContDiffOn.div Real.contDiff_sin.contDiffOn Real.contDiff_cos.contDiffOn hcos
  · intro θ hθ
    exact ⟨by linarith [hθ.1, hA], lt_of_le_of_lt hθ.2 hB⟩

/-- The derivatives of `sec²` are bounded on `[A, B] ⊂ (0, π/2)`. -/
lemma exists_bound_iteratedDeriv_secsq {A B : ℝ} (hA : 0 < A) (hB : B < Real.pi / 2) :
    ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Icc A B,
      |iteratedDeriv i (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) θ| ≤ C := by
  refine exists_bound_iteratedDeriv_of_contDiffOn (s := Set.Ioo (A / 2) (Real.pi / 2)) isOpen_Ioo ?_ ?_
  · intro n
    have hcos : ∀ θ ∈ Set.Ioo (A / 2) (Real.pi / 2), (Real.cos θ) ^ 2 ≠ 0 := by
      intro θ hθ
      have hc : Real.cos θ ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hA, Real.pi_pos], hθ.2⟩)
      exact pow_ne_zero 2 hc
    refine ContDiffOn.congr
      (ContDiffOn.div (contDiffOn_const (c := (1 : ℝ)))
        (Real.contDiff_cos.contDiffOn.pow 2) hcos) ?_
    intro θ _
    rfl
  · intro θ hθ
    exact ⟨by linarith [hθ.1, hA], lt_of_le_of_lt hθ.2 hB⟩

/-! ## 6. The arithmetic of the two base bounds -/

lemma cos_sq_pos_of {B : ℝ} (hB : 0 < B) (hB2 : B < Real.pi / 2) : 0 < Real.cos B ^ 2 := by
  have h : 0 < Real.cos B := Real.cos_pos_of_mem_Ioo ⟨by linarith [hB, Real.pi_pos], hB2⟩
  positivity

/-- `√((2m+2)(2m+3)) ≤ 3(m+1)`. -/
lemma sqrt_Npsi_le (m : ℕ) :
    Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ≤ 3 * ((m : ℝ) + 1) := by
  have hp : (0 : ℝ) ≤ 3 * ((m : ℝ) + 1) := by positivity
  rw [← Real.sqrt_sq hp]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

/-- `(2m+2)(2m+3) ≤ 6(m+1)²`. -/
lemma Npsi_le_six (m : ℕ) :
    (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3) ≤ 6 * ((m : ℝ) + 1) ^ 2 := by
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

/-- `eM m ≤ 6(m+1)²`. -/
lemma eM_le_six (m : ℕ) :
    Work.FTS.PhiStar.Series.eM m ≤ 6 * ((m : ℝ) + 1) ^ 2 := by
  rw [Work.FTS.PhiStar.Series.eM]
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

lemma eM_nonneg (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Series.eM m := by
  rw [Work.FTS.PhiStar.Series.eM]
  positivity

end Work.FTS.PhiStar.Honesty.CptQSmooth.CleanAng
