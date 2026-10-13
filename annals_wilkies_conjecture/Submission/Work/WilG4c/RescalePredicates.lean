/-
  WilG4c — §5.3: the rescaling `z ↦ q + z/K` preserves the family predicates.

  The reduction `StepLip` applies the F-lemma to a family pulled back along the affine
  substitution `z ↦ q + z/K`, which maps the open cube into the sub-cube `[q, q + 1/K]`.
  This file records that this substitution preserves the three predicates used by the
  reduction:

  * `LipOnCube F C` becomes `LipOnCube G 1` because the substitution contracts distances by
    `1/K` and `C ≤ K`;
  * `ValuesIn01 Λ F` becomes `ValuesIn01 Λ G` because the substitution maps the open cube
    into itself;
  * `YBound F r` becomes `YBound G r` because the substitution acts on the `y`-variables by
    the affine map `y ↦ c + y/K`, and the chain rule for the iterated derivative of a
    composition with a *continuous linear equivalence* (available in Mathlib without any
    differentiability assumption) combined with `‖(K⁻¹ : ℝ) • 1‖ ≤ 1` gives the bound.

  The last point is the content of `norm_iteratedFDeriv_comp_add_smul_le` below.
-/
import Mathlib
import Submission.Work.WilG4c.LipDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The rescaled point stays in the cube -/

/-- `x ↦ q₀ + x/K` maps `I = (0,1)` into itself when `q₀ ≥ 0` and `q₀ + 1/K ≤ 1`. -/
private lemma rescale_mem_I {K : ℕ} (hK : 1 ≤ K) (q₀ x : ℝ) (hq₀ : 0 ≤ q₀)
    (hq₁ : q₀ + 1 / (K : ℝ) ≤ 1) (hx : x ∈ I) : q₀ + x / (K : ℝ) ∈ I := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  obtain ⟨hx0, hx1⟩ := hx
  refine ⟨?_, ?_⟩
  · have h : 0 < x / (K : ℝ) := div_pos hx0 hKpos
    linarith
  · have h : x / (K : ℝ) < 1 / (K : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_lt_mul_of_pos_right hx1 (inv_pos.mpr hKpos)
    linarith

/-- Coordinatewise form of `rescale_mem_I`: `x ↦ q + x/K` maps the open cube into itself. -/
private lemma rescale_mem_openCube {N : ℕ} {K : ℕ} (hK : 1 ≤ K) (q : Fin N → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j + 1 / (K : ℝ) ≤ 1) (x : Fin N → ℝ)
    (hx : x ∈ openCube N) : (fun j => q j + x j / (K : ℝ)) ∈ openCube N := by
  intro j
  exact rescale_mem_I hK (q j) (x j) (hq0 j) (hq1 j) (hx j)

/-! ## 2. Multiplication by `1/K` as a continuous linear equivalence -/

/-- Multiplication by `1/K` on `ℝ^N`, as a continuous linear equivalence. -/
private noncomputable def scaleEquiv (N K : ℕ) (hK : 1 ≤ K) :
    (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearEquiv.ofHomothety (σ := RingHom.id ℝ)
    (LinearEquiv.smulOfNeZero ℝ (Fin N → ℝ) ((K : ℝ)⁻¹)
      (inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))))
    ((K : ℝ)⁻¹) (inv_pos.mpr (by exact_mod_cast hK))
    (fun x => by
      rw [LinearEquiv.smulOfNeZero_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)])

private lemma scaleEquiv_apply (N K : ℕ) (hK : 1 ≤ K) (y : Fin N → ℝ) :
    scaleEquiv N K hK y = fun i => y i / (K : ℝ) := by
  ext i
  change ((K : ℝ)⁻¹ • y) i = y i / (K : ℝ)
  rw [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

/-- `‖(K⁻¹ • id)‖ ≤ 1` for `K ≥ 1`. -/
private lemma scaleEquiv_norm (N K : ℕ) (hK : 1 ≤ K) :
    ‖(scaleEquiv N K hK : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun x => ?_)
  have hx : (scaleEquiv N K hK : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) x = ((K : ℝ)⁻¹) • x := rfl
  rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul]
  exact mul_le_of_le_one_left (norm_nonneg x) (inv_le_one_of_one_le₀ (by exact_mod_cast hK))

/-! ## 3. The chain rule for the affine substitution `y ↦ c + e y` -/

/-- The iterated derivative of `y ↦ g (c + e y)`, where `e` is a continuous linear
equivalence, is the iterated derivative of `g` at `c + e y` composed with `e` in every
variable.  No differentiability of `g` is needed: the corresponding Mathlib lemma for the
composition with a linear equivalence on the right is unconditional. -/
private lemma iteratedFDeriv_comp_add_smul_equiv {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : E ≃L[ℝ] E) (c : E) (g : E → ℝ) (m : ℕ) (y : E) :
    iteratedFDeriv ℝ m (fun y => g (c + e y)) y =
      (iteratedFDeriv ℝ m g (c + e y)).compContinuousLinearMap
        (fun _ : Fin m => (e : E →L[ℝ] E)) := by
  have hcomp := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right e (fun z : E => g (c + z))
    uniqueDiffOn_univ (Set.mem_univ (e y)) m
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hcomp
  rw [show (fun y : E => g (c + e y)) = (fun z : E => g (c + z)) ∘ (e : E → E) from rfl,
    hcomp, iteratedFDeriv_comp_add_left m c (e y)]

/-- Norm of a multilinear map composed with `m` copies of one linear map. -/
private lemma norm_compCLM_const_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (g : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℝ) (A : E →L[ℝ] E) :
    ‖g.compContinuousLinearMap (fun _ : Fin m => A)‖ ≤ ‖g‖ * ‖A‖ ^ m := by
  have h := g.norm_compContinuousLinearMap_le (fun _ : Fin m => A)
  simpa [Finset.prod_const] using h

/-- Norm form of the chain rule above: if the linear part is a contraction (`‖e‖ ≤ 1`), the
substitution does not increase the operator norm of the iterated derivative. -/
private lemma norm_iteratedFDeriv_comp_add_smul_le {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : E ≃L[ℝ] E) (he : ‖(e : E →L[ℝ] E)‖ ≤ 1) (c : E) (g : E → ℝ)
    (m : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ m (fun y => g (c + e y)) y‖ ≤ ‖iteratedFDeriv ℝ m g (c + e y)‖ := by
  rw [iteratedFDeriv_comp_add_smul_equiv]
  calc ‖(iteratedFDeriv ℝ m g (c + e y)).compContinuousLinearMap
          (fun _ : Fin m => (e : E →L[ℝ] E))‖
      ≤ ‖iteratedFDeriv ℝ m g (c + e y)‖ * ‖(e : E →L[ℝ] E)‖ ^ m :=
        norm_compCLM_const_le m _ _
    _ ≤ ‖iteratedFDeriv ℝ m g (c + e y)‖ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact pow_le_one₀ (norm_nonneg _) he
    _ = ‖iteratedFDeriv ℝ m g (c + e y)‖ := mul_one _

/-! ## 4. The `y`-slice of the rescaled family -/

/-- The rescaled point is the concatenation of `q₀ + x/K` with `c + y/K`, where `c` is the
tail of `q`. -/
private lemma rescale_pt {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (q : Fin (n + 1) → ℝ) (x : ℝ)
    (y : Fin n → ℝ) :
    (fun j : Fin (n + 1) => q j + (pt x y) j / (K : ℝ))
      = pt (q 0 + x / (K : ℝ))
          ((fun i : Fin n => q i.succ) + scaleEquiv n K hK y) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [pt]
  | succ i => simp [pt, scaleEquiv_apply]

/-! ## 5. The main lemma -/

theorem RescalePredicates {k : ℕ} (n p : ℕ) (K : ℕ) (hK : 1 ≤ K) (q : Fin (n + 1) → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j + 1 / (K : ℝ) ≤ 1)
    (F : Work.WilkG4c.Family k p (n + 1)) (r : ℕ) (C : ℝ) (hC : 1 ≤ C) (hCK : C ≤ (K : ℝ))
    (Λ : Set (Fin p → ℝ)) (hY : Work.WilkG4c.YBound F r) (hLip : Work.WilkG4c.LipOnCube F C)
    (hval : Work.WilkG4c.ValuesIn01 Λ F) :
    Work.WilkG4c.YBound (fun i l z => F i l (fun j => q j + z j / (K : ℝ))) r ∧
      Work.WilkG4c.LipOnCube (fun i l z => F i l (fun j => q j + z j / (K : ℝ))) 1 ∧
      Work.WilkG4c.ValuesIn01 Λ (fun i l z => F i l (fun j => q j + z j / (K : ℝ))) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  refine ⟨?_, ?_, ?_⟩
  · -- `YBound`: contract the `y`-variables by `1/K` and shift by the tail of `q`.
    intro i l x hx m hm y hy
    have hxI : q 0 + x / (K : ℝ) ∈ I :=
      rescale_mem_I hK (q 0) x (hq0 0) (hq1 0) hx
    have hyc : ((fun i : Fin n => q i.succ) + scaleEquiv n K hK y) ∈ openCube n := by
      simpa [openCube, scaleEquiv_apply, Pi.add_apply] using
        (rescale_mem_openCube hK (fun i : Fin n => q i.succ) (fun i => hq0 i.succ)
          (fun i => hq1 i.succ) y hy)
    have hbound : ‖iteratedFDeriv ℝ m (slice (F i l) (q 0 + x / (K : ℝ)))
        ((fun i : Fin n => q i.succ) + scaleEquiv n K hK y)‖ ≤ 1 :=
      hY i l (q 0 + x / (K : ℝ)) hxI m hm _ hyc
    have hfun : slice (fun z : Fin (n + 1) → ℝ => F i l (fun j => q j + z j / (K : ℝ))) x
        = fun y : Fin n → ℝ => slice (F i l) (q 0 + x / (K : ℝ))
            ((fun i : Fin n => q i.succ) + scaleEquiv n K hK y) := by
      funext y
      show F i l (fun j => q j + (pt x y) j / (K : ℝ))
        = F i l (pt (q 0 + x / (K : ℝ))
            ((fun i : Fin n => q i.succ) + scaleEquiv n K hK y))
      rw [rescale_pt]
    rw [hfun]
    exact le_trans (norm_iteratedFDeriv_comp_add_smul_le (scaleEquiv n K hK)
      (scaleEquiv_norm n K hK) (fun i : Fin n => q i.succ)
      (slice (F i l) (q 0 + x / (K : ℝ))) m y) hbound
  · -- `LipOnCube`: the substitution contracts distances by the factor `1/K`, and `C ≤ K`.
    intro i l z z' hz hz'
    have hz1 : (fun j : Fin (n + 1) => q j + z j / (K : ℝ)) ∈ openCube (n + 1) :=
      rescale_mem_openCube hK q hq0 hq1 z hz
    have hz2 : (fun j : Fin (n + 1) => q j + z' j / (K : ℝ)) ∈ openCube (n + 1) :=
      rescale_mem_openCube hK q hq0 hq1 z' hz'
    have hdist : dist (fun j : Fin (n + 1) => q j + z j / (K : ℝ))
        (fun j : Fin (n + 1) => q j + z' j / (K : ℝ)) = dist z z' / (K : ℝ) := by
      have h1 : (fun j : Fin (n + 1) => q j + z j / (K : ℝ))
          - (fun j : Fin (n + 1) => q j + z' j / (K : ℝ)) = (K : ℝ)⁻¹ • (z - z') := by
        ext j; simp [div_eq_inv_mul, smul_eq_mul]; ring
      rw [dist_eq_norm, dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hKpos)]
      rw [div_eq_mul_inv, mul_comm]
    have hchain := hLip i l _ _ hz1 hz2
    have hCK' : C / (K : ℝ) ≤ 1 := (div_le_one hKpos).mpr hCK
    calc |F i l (fun j => q j + z j / (K : ℝ)) - F i l (fun j => q j + z' j / (K : ℝ))|
        ≤ C * dist (fun j : Fin (n + 1) => q j + z j / (K : ℝ))
            (fun j : Fin (n + 1) => q j + z' j / (K : ℝ)) := hchain
      _ = C * (dist z z' / (K : ℝ)) := by rw [hdist]
      _ = (C / (K : ℝ)) * dist z z' := by ring
      _ ≤ 1 * dist z z' := by
          have h0 : (0 : ℝ) ≤ dist z z' := dist_nonneg
          exact mul_le_mul_of_nonneg_right hCK' h0
  · -- `ValuesIn01`: the rescaled point is again a point of the cube.
    intro i l hl w hw
    have hw' : (fun j => q j + w j / (K : ℝ)) ∈ openCube (n + 1) :=
      rescale_mem_openCube hK q hq0 hq1 w hw
    exact hval i l hl _ hw'

end Work.WilkG4c

/-! ## 6. The same theorem under the path-derived name

The module lives at `Submission/Work/WilG4c/RescalePredicates.lean`, so the workspace
naming convention for this area is `Work.WilG4c`.  The statement above was handed to us
spelled inside `namespace Work.WilkG4c`; we keep that declaration and expose the identical
theorem under the convention name as well, so that both spellings resolve. -/

namespace Work.WilG4c

theorem RescalePredicates {k : ℕ} (n p : ℕ) (K : ℕ) (hK : 1 ≤ K) (q : Fin (n + 1) → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j + 1 / (K : ℝ) ≤ 1)
    (F : Work.WilkG4c.Family k p (n + 1)) (r : ℕ) (C : ℝ) (hC : 1 ≤ C) (hCK : C ≤ (K : ℝ))
    (Λ : Set (Fin p → ℝ)) (hY : Work.WilkG4c.YBound F r) (hLip : Work.WilkG4c.LipOnCube F C)
    (hval : Work.WilkG4c.ValuesIn01 Λ F) :
    Work.WilkG4c.YBound (fun i l z => F i l (fun j => q j + z j / (K : ℝ))) r ∧
      Work.WilkG4c.LipOnCube (fun i l z => F i l (fun j => q j + z j / (K : ℝ))) 1 ∧
      Work.WilkG4c.ValuesIn01 Λ (fun i l z => F i l (fun j => q j + z j / (K : ℝ))) :=
  Work.WilkG4c.RescalePredicates n p K hK q hq0 hq1 F r C hC hCK Λ hY hLip hval

end Work.WilG4c
