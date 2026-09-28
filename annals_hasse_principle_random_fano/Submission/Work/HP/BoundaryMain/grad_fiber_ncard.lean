import Mathlib
import Submission.Work.HP.BoundaryMain.bm_defs
import Submission.Work.HP.GradDecomp.gradF_decomp
import Submission.Work.HP.GradCount.ncard_spec_le
import Submission.Work.HP.tau_basic
import Submission.Work.HP.BoundaryMain.spec_box_finite
import Submission.Work.HP.BoundaryMain.spec_box_ncard_abs

/-!
# `Work.HP.BoundaryMain.grad_fiber_ncard`

Fix a point `y` with `y j ≠ 0`, a bound `C > 0` and the "free part" `f` of a coefficient vector
(the entries outside the `n+1` special monomials `x_j^{d-1} x_i`).  We count the special-coefficient
vectors `c : Fin (n+1) → ℤ` that arise from an integer coefficient vector `a` whose gradient at `y`
has norm at most `C` and whose free part is `f`.

The `n+1` equations `∂_k f_a(y) = 0` decompose (see `Work.HP.GradDecomp.gradF_decomp`) into `n`
equations `c k · y_j^{d-1} = -∂_k f_f(y)` for `k ≠ j`, each confining `c k` to an interval of
length `2C/|y_j|^{d-1}`, and one equation
`c j · d y_j^{d-1} + (d-1) y_j^{d-2} ∑_{i≠j} c i y i = -∂_j f_f(y)`, confining `c j` to an interval
of length `2C/(d |y_j|^{d-1})`.  Counting gives
`(2C/|y_j|^{d-1} + 2)^n · (2C/(d |y_j|^{d-1}) + 2)`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.BoundaryMain

open Work.HP

/-- The set of "special-coefficient" vectors `c` coming from an integer vector `a` with
`rNorm (∇f_a(y)) ≤ C`, special part `c` and free part `f`, is contained in the affine box
`|c k · y_j^{d-1} + ∂_k f_f (y)| ≤ C` (`k ≠ j`) together with the single affine inequality
`|c j · d y_j^{d-1} + ∑_{i≠j} (d-1) y_j^{d-2} y i · c i + ∂_j f_f(y)| ≤ C`. -/
theorem grad_fiber_subset (d n : ℕ) (hd1 : 1 ≤ d) (hd2 : 2 ≤ d) (C : ℝ)
    (y : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (hyj : y j ≠ 0) (f : Mon d n → ℤ) :
    ({c : Fin (n + 1) → ℤ | ∃ a : Mon d n → ℤ,
        rNorm (gradVec d n (toR a) y) ≤ C ∧
        (fun i => a (smon d n hd1 j i)) = c ∧
        zeroSInt d n hd1 j a = f} : Set (Fin (n + 1) → ℤ))
      ⊆ ({c : Fin (n + 1) → ℤ |
        (∀ k : Fin (n + 1), k ≠ j →
            |(c k : ℝ) * (y j ^ (d - 1)) + gradF d n (toR f) y k| ≤ C) ∧
        |(c j : ℝ) * ((d : ℝ) * y j ^ (d - 1))
            + ∑ i ∈ Finset.univ.erase j, (((d : ℝ) - 1) * y j ^ (d - 2) * y i) * (c i : ℝ)
            + gradF d n (toR f) y j| ≤ C}) := by
  intro c hc
  obtain ⟨a, hgrad, hceq, hfeq⟩ := hc
  have hc_eq : ∀ i, c i = a (smon d n hd1 j i) := fun i => (congrFun hceq i).symm
  have hzf : zeroS d n hd1 j (toR a) = toR f := by
    rw [← toR_zeroSInt d n hd1 j a, hfeq]
  have hcoord : ∀ k, |gradF d n (toR a) y k| ≤ C := fun k =>
    (abs_apply_le_rNorm (gradVec d n (toR a) y) k).trans hgrad
  have hb2 : ∀ i, (toR a) (smon d n hd1 j i) = (c i : ℝ) := by
    intro i; rw [hc_eq i]; rfl
  constructor
  · intro k hkj
    have hd := GradDecomp.gradF_decomp d n hd1 hd2 (toR a) y j k
    rw [if_neg hkj] at hd
    rw [hzf] at hd
    rw [hb2 k] at hd
    have hd' : gradF d n (toR a) y k = (c k : ℝ) * y j ^ (d - 1) + gradF d n (toR f) y k := by
      rw [hd]; ring
    rw [← hd']
    exact hcoord k
  · have hd := GradDecomp.gradF_decomp d n hd1 hd2 (toR a) y j j
    rw [if_pos rfl] at hd
    rw [hzf] at hd
    simp_rw [hb2] at hd
    rw [show y j ^ (d - 2) * ((d : ℝ) * (c j : ℝ) * y j
          + ((d : ℝ) - 1) * ∑ i ∈ Finset.univ.erase j, (c i : ℝ) * y i)
        = (c j : ℝ) * ((d : ℝ) * y j ^ (d - 1))
          + ∑ i ∈ Finset.univ.erase j, (((d : ℝ) - 1) * y j ^ (d - 2) * y i) * (c i : ℝ) from by
      have hpow : y j ^ (d - 2) * y j = y j ^ (d - 1) := by
        rw [← pow_succ]; congr 1; omega
      have h1 : y j ^ (d - 2) * ((d : ℝ) * (c j : ℝ) * y j)
          = (c j : ℝ) * ((d : ℝ) * y j ^ (d - 1)) := by
        rw [show y j ^ (d - 2) * ((d : ℝ) * (c j : ℝ) * y j)
              = ((d : ℝ) * (c j : ℝ)) * (y j ^ (d - 2) * y j) by ring, hpow]
        ring
      have h2 : y j ^ (d - 2) * (((d : ℝ) - 1) * ∑ i ∈ Finset.univ.erase j, (c i : ℝ) * y i)
          = ∑ i ∈ Finset.univ.erase j, (((d : ℝ) - 1) * y j ^ (d - 2) * y i) * (c i : ℝ) := by
        rw [show y j ^ (d - 2) * (((d : ℝ) - 1) * ∑ i ∈ Finset.univ.erase j, (c i : ℝ) * y i)
              = (((d : ℝ) - 1) * y j ^ (d - 2))
                  * (∑ i ∈ Finset.univ.erase j, (c i : ℝ) * y i) by ring,
            Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi; ring
      rw [mul_add, h1, h2]] at hd
    have hgoal : |(c j : ℝ) * ((d : ℝ) * y j ^ (d - 1))
          + ∑ i ∈ Finset.univ.erase j, (((d : ℝ) - 1) * y j ^ (d - 2) * y i) * (c i : ℝ)
          + gradF d n (toR f) y j|
        = |gradF d n (toR a) y j| := by
      rw [hd]; congr 1; ring
    rw [hgoal]
    exact hcoord j

theorem grad_fiber_ncard (d n : ℕ) (hd1 : 1 ≤ d) (hd2 : 2 ≤ d) (C : ℝ) (hC : 0 < C)
    (y : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (hyj : y j ≠ 0) (f : Work.HP.Mon d n → ℤ) :
    (({c : Fin (n + 1) → ℤ | ∃ a : Work.HP.Mon d n → ℤ,
        Work.HP.rNorm (Work.HP.gradVec d n (Work.HP.toR a) y) ≤ C ∧
        (fun i => a (Work.HP.smon d n hd1 j i)) = c ∧
        Work.HP.BoundaryMain.zeroSInt d n hd1 j a = f} : Set (Fin (n + 1) → ℤ)).ncard : ℝ)
      ≤ (2 * C / |y j| ^ (d - 1) + 2) ^ n * (2 * C / ((d : ℝ) * |y j| ^ (d - 1)) + 2) := by
  classical
  set uu : ℝ := y j ^ (d - 1) with huu
  set vv : ℝ := (d : ℝ) * y j ^ (d - 1) with hvv
  set AA : Fin (n + 1) → ℝ := fun k => gradF d n (toR f) y k with hAA
  set ww : Fin (n + 1) → ℝ := fun i => ((d : ℝ) - 1) * y j ^ (d - 2) * y i with hww
  have hyjpow : y j ^ (d - 1) ≠ 0 := pow_ne_zero _ hyj
  have hu : uu ≠ 0 := by rw [huu]; exact hyjpow
  have hv : vv ≠ 0 := by
    rw [hvv]
    exact mul_ne_zero (by exact_mod_cast (by omega : d ≠ 0)) hyjpow
  have hsub := grad_fiber_subset d n hd1 hd2 C y j hyj f
  have hsub' : ({c : Fin (n + 1) → ℤ | ∃ a : Mon d n → ℤ,
        rNorm (gradVec d n (toR a) y) ≤ C ∧
        (fun i => a (smon d n hd1 j i)) = c ∧
        zeroSInt d n hd1 j a = f} : Set (Fin (n + 1) → ℤ))
      ⊆ ({c : Fin (n + 1) → ℤ |
        (∀ k : Fin (n + 1), k ≠ j → |(c k : ℝ) * uu + AA k| ≤ C) ∧
        |(c j : ℝ) * vv + ∑ i ∈ Finset.univ.erase j, ww i * (c i : ℝ) + AA j| ≤ C}) := by
    intro c hc
    have h := hsub hc
    simp only [huu, hvv, hAA, hww, Set.mem_ofPred_eq] at h ⊢
    exact h
  have hfin : ({c : Fin (n + 1) → ℤ |
        (∀ k : Fin (n + 1), k ≠ j → |(c k : ℝ) * uu + AA k| ≤ C) ∧
        |(c j : ℝ) * vv + ∑ i ∈ Finset.univ.erase j, ww i * (c i : ℝ) + AA j| ≤ C} :
        Set (Fin (n + 1) → ℤ)).Finite :=
    spec_box_finite n j uu vv C hu hv ww AA
  have hbnd := spec_box_ncard_abs n j uu vv C hu hv (le_of_lt hC) ww AA
  calc (({c : Fin (n + 1) → ℤ | ∃ a : Mon d n → ℤ,
        rNorm (gradVec d n (toR a) y) ≤ C ∧
        (fun i => a (smon d n hd1 j i)) = c ∧
        zeroSInt d n hd1 j a = f} : Set (Fin (n + 1) → ℤ)).ncard : ℝ)
      ≤ (({c : Fin (n + 1) → ℤ |
        (∀ k : Fin (n + 1), k ≠ j → |(c k : ℝ) * uu + AA k| ≤ C) ∧
        |(c j : ℝ) * vv + ∑ i ∈ Finset.univ.erase j, ww i * (c i : ℝ) + AA j| ≤ C} :
        Set (Fin (n + 1) → ℤ)).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub' hfin
    _ ≤ (2 * C / |uu| + 2) ^ n * (2 * C / |vv| + 2) := hbnd
    _ = (2 * C / |y j| ^ (d - 1) + 2) ^ n * (2 * C / ((d : ℝ) * |y j| ^ (d - 1)) + 2) := by
        have huabs : |uu| = |y j| ^ (d - 1) := by rw [huu, abs_pow]
        have hvabs : |vv| = (d : ℝ) * |y j| ^ (d - 1) := by
          rw [hvv, abs_mul, abs_of_nonneg (Nat.cast_nonneg d), abs_pow]
        rw [huabs, hvabs]

end Work.HP.BoundaryMain
