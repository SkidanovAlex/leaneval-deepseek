import Mathlib
import Submission.Work.Peluse.MajorArc.Defs

/-!
# Reindexing the correlation of Peluse's dual function

The pointwise ergodic theorem of Krause–Mirek–Tao uses Peluse's Corollary 3.8 for the dual
function `F₂(x) = E_{y ∈ [M]} f₀ (x - P y) f₁ (x + y - P y)` of the progression
`(u, u + y, u + P y)`.  In the major-arc analysis of `Work.Peluse.majorarc` one needs the
identity

`∑_x F₂(x) e (β x) = (1/M) ∑_{y ∈ [M]} e (β P y) ∑_{u ∈ [-N,N]} f₀(u) e (β u) f₁ (u + y)`

for `f₀`, `f₁` supported in `[-N,N]` and `M ≤ N`.  Both sides are the same double sum over
`(y, u)`, read either as a sum over `x = u + P y` (left) or over `(y, u)` (right); the (finite)
support of `f₀` lets us cut the `x`-sum down to the box `[-dSup P N M, dSup P N M]` and the
`u`-sum down to `[-N, N]`.

## Main result

* `corrReindex` — the identity above, in the exact form requested by `Work.Peluse.majorarc`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

/-! ## Two elementary reindexing lemmas -/

/-- A sum over `Icc (1 : ℤ) (M : ℤ)` is the same as a sum over `Icc 1 M` (via the cast), which
lets us compare the `ℤ`-indexed sums of `majorarc` with the `ℕ`-indexed sums of `dualFn`. -/
private lemma sum_Icc_intCast (M : ℕ) (G : ℤ → ℂ) :
    (∑ y ∈ Finset.Icc 1 M, G (y : ℤ)) = ∑ z ∈ Finset.Icc (1 : ℤ) (M : ℤ), G z := by
  refine Finset.sum_bij (fun y (_ : y ∈ Finset.Icc 1 M) => (y : ℤ)) ?_ ?_ ?_ ?_
  · intro y hy
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hy
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · intro a _ b _ h
    exact_mod_cast h
  · intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.mp hz
    have hz0 : (0 : ℤ) ≤ z := by linarith
    refine ⟨z.toNat, ?_, Int.toNat_of_nonneg hz0⟩
    exact Finset.mem_Icc.mpr ⟨(Int.le_toNat hz0).mpr hz1, Int.toNat_le.mpr hz2⟩
  · intro y _
    rfl

/-- **The reindexing step, one `y` at a time.**  For `y ∈ [1, M]`,

`∑_{x ∈ [-dSup P N M, dSup P N M]} f₀ (x - P y) f₁ (x + y - P y) e (β x)
  = e (β P y) ∑_{u ∈ [-N,N]} f₀ u e (β u) f₁ (u + y)`.

The substitution is `u = x - P y`; the box `[-dSup, dSup]` contains `[-N,N] + P y` because
`|P y| ≤ polySup P M` on `[0, M]`, and outside the box the first factor `f₀ (x - P y)` vanishes. -/
private lemma inner_reindex (N M : ℕ) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ) (β : ℝ)
    (hs0 : SupportIn f₀ N) {y : ℤ} (hy0 : 0 ≤ y) (hyM : y ≤ (M : ℤ)) :
    (∑ x ∈ Finset.Icc (-(dSup P N M : ℤ)) (dSup P N M : ℤ),
        (f₀ (x - P.eval y) * f₁ (x + y - P.eval y)) * ee (β * (x : ℝ)))
      = ee (β * ((P.eval y : ℤ) : ℝ)) *
        ∑ u ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (f₀ u * ee (β * (u : ℝ))) * f₁ (u + y) := by
  set X : Finset ℤ := Finset.Icc (-(dSup P N M : ℤ)) (dSup P N M : ℤ) with hX
  set U : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hU
  set Py : ℤ := P.eval y with hPy
  set c : ℂ := ee (β * (Py : ℝ)) with hc
  -- the translated box `U + P y` still sits inside `X`
  have hsub : U.image (fun u => u + Py) ⊆ X := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx
    rw [hX, ← hux]
    obtain ⟨hu1, hu2⟩ := Finset.mem_Icc.mp hu
    have huabs : |u| ≤ (N : ℤ) := by rw [abs_le]; exact ⟨hu1, hu2⟩
    have hPyabs : |Py| ≤ (polySup P M : ℤ) := by
      rw [hPy]; exact Work.Peluse.Tools.eval_abs_le_polySup P hy0 hyM
    have habs : |u + Py| ≤ ((dSup P N M : ℕ) : ℤ) := by
      calc |u + Py| ≤ |u| + |Py| := abs_add_le _ _
        _ ≤ (N : ℤ) + (polySup P M : ℤ) := add_le_add huabs hPyabs
        _ = ((dSup P N M : ℕ) : ℤ) := by rw [dSup]; push_cast; ring
    exact Finset.mem_Icc.mpr (abs_le.mp habs)
  -- and the terms of `X` outside `U + P y` vanish
  have hvan : ∀ x ∈ X, x ∉ U.image (fun u => u + Py) →
      (f₀ (x - Py) * f₁ (x + y - Py)) * ee (β * (x : ℝ)) = 0 := by
    intro x _ hxnot
    have hxmem : x - Py ∉ U := fun h => hxnot (Finset.mem_image.mpr ⟨x - Py, h, by ring⟩)
    rw [hU] at hxmem
    have hxmem' : ¬ (( -(N : ℤ) ≤ x - Py) ∧ (x - Py ≤ (N : ℤ))) :=
      fun hcon => hxmem (Finset.mem_Icc.mpr hcon)
    have hne : N < (x - Py).natAbs := by
      rcases not_and_or.mp hxmem' with h | h
      · have hlt : x - Py < -(N : ℤ) := not_le.mp h
        have h' : (N : ℤ) < |x - Py| := by
          have : (N : ℤ) < -(x - Py) := by linarith
          linarith [neg_le_abs (x - Py)]
        rw [Int.abs_eq_natAbs] at h'
        exact_mod_cast h'
      · have hlt : (N : ℤ) < x - Py := not_le.mp h
        have h' : (N : ℤ) < |x - Py| := by linarith [le_abs_self (x - Py)]
        rw [Int.abs_eq_natAbs] at h'
        exact_mod_cast h'
    rw [hs0 (x - Py) hne, zero_mul, zero_mul]
  -- reindex `x = u + P y`
  have hmem : ∑ x ∈ U.image (fun u => u + Py),
        (f₀ (x - Py) * f₁ (x + y - Py)) * ee (β * (x : ℝ))
      = ∑ u ∈ U, (f₀ ((u + Py) - Py) * f₁ ((u + Py) + y - Py)) * ee (β * ((u + Py : ℤ) : ℝ)) :=
    Finset.sum_image (s := U) (g := fun u : ℤ => u + Py)
      (f := fun x : ℤ => (f₀ (x - Py) * f₁ (x + y - Py)) * ee (β * (x : ℝ)))
      (fun a _ b _ h => add_right_cancel h)
  -- simplify the summand and factor out `e (β P y)`
  have hpoint : ∀ u ∈ U, (f₀ ((u + Py) - Py) * f₁ ((u + Py) + y - Py)) * ee (β * ((u + Py : ℤ) : ℝ))
      = c * ((f₀ u * ee (β * (u : ℝ))) * f₁ (u + y)) := by
    intro u _
    have h1 : (u + Py) - Py = u := by ring
    have h2 : (u + Py) + y - Py = u + y := by ring
    have h3 : β * (((u + Py : ℤ)) : ℝ) = β * (u : ℝ) + β * (Py : ℝ) := by push_cast; ring
    rw [h1, h2, h3, ee_add, hc]
    ring
  calc ∑ x ∈ X, (f₀ (x - Py) * f₁ (x + y - Py)) * ee (β * (x : ℝ))
      = ∑ x ∈ U.image (fun u => u + Py),
          (f₀ (x - Py) * f₁ (x + y - Py)) * ee (β * (x : ℝ)) :=
        (Finset.sum_subset hsub hvan).symm
    _ = ∑ u ∈ U, (f₀ ((u + Py) - Py) * f₁ ((u + Py) + y - Py)) * ee (β * ((u + Py : ℤ) : ℝ)) := hmem
    _ = ∑ u ∈ U, c * ((f₀ u * ee (β * (u : ℝ))) * f₁ (u + y)) :=
        Finset.sum_congr rfl (fun u hu => hpoint u hu)
    _ = c * ∑ u ∈ U, (f₀ u * ee (β * (u : ℝ))) * f₁ (u + y) := (Finset.mul_sum U _ c).symm

/-! ## The requested identity -/

theorem corrReindex (N M : ℕ) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ) (β : ℝ)
    (hM : 1 ≤ M) (hMN : M ≤ N) (hs0 : Work.Peluse.SupportIn f₀ N) (hs1 : Work.Peluse.SupportIn f₁ N) :
    (∑' x : ℤ, Work.Peluse.dualFn M P f₀ f₁ x *
        Complex.exp (2 * Real.pi * Complex.I * β * x))
      = ((M : ℂ))⁻¹ * ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ),
          Work.Peluse.ee (β * ((P.eval y : ℤ) : ℝ)) *
            ∑ u ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
              (f₀ u * Work.Peluse.ee (β * (u : ℝ))) * f₁ (u + y) := by
  -- rewrite the character `exp (2 π i β x)` as `ee (β x)`
  have hexp : ∀ x : ℤ, Complex.exp (2 * Real.pi * Complex.I * β * x) = ee (β * (x : ℝ)) :=
    fun x => by rw [exp_mul_eq_ee]
  simp only [hexp]
  -- `dualFn` is supported in the box `[-dSup P N M, dSup P N M]`, so the `tsum` is this box sum
  set X : Finset ℤ := Finset.Icc (-(dSup P N M : ℤ)) (dSup P N M : ℤ) with hX
  have hsupp : ∀ x : ℤ, x ∉ X → dualFn M P f₀ f₁ x * ee (β * (x : ℝ)) = 0 := by
    intro x hx
    rw [hX] at hx
    have hx' : ¬ (( -(dSup P N M : ℤ) ≤ x) ∧ (x ≤ (dSup P N M : ℤ))) :=
      fun hcon => hx (Finset.mem_Icc.mpr hcon)
    have hDx : ((dSup P N M : ℕ) : ℤ) < |x| := by
      rcases not_and_or.mp hx' with h | h
      · have hlt : x < -(dSup P N M : ℤ) := not_le.mp h
        have h2 : ((dSup P N M : ℕ) : ℤ) < -x := by linarith
        linarith [neg_le_abs x]
      · have hlt : (dSup P N M : ℤ) < x := not_le.mp h
        linarith [le_abs_self x]
    have hnat : dSup P N M < x.natAbs := by
      have := hDx
      rw [Int.abs_eq_natAbs] at this
      exact_mod_cast this
    rw [Tools.dualFn_supportIn (show 0 < M by omega) P f₀ f₁ hs0 hs1 hMN x hnat, zero_mul]
  rw [tsum_eq_sum (s := X) hsupp]
  -- expand `dualFn`, swap the two finite sums, and reindex each `y`-slice
  have hmain : ∑ x ∈ X, dualFn M P f₀ f₁ x * ee (β * (x : ℝ))
      = (M : ℂ)⁻¹ * ∑ y ∈ Finset.Icc 1 M,
          ee (β * ((P.eval (y : ℤ) : ℤ) : ℝ)) *
            ∑ u ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (f₀ u * ee (β * (u : ℝ))) * f₁ (u + (y : ℤ)) := by
    have h1 : ∑ x ∈ X, dualFn M P f₀ f₁ x * ee (β * (x : ℝ))
        = (M : ℂ)⁻¹ * ∑ x ∈ X, (∑ y ∈ Finset.Icc 1 M,
              f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))) * ee (β * (x : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [dualFn]
      ring
    rw [h1]
    congr 1
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    obtain ⟨hy1, hy2⟩ := Finset.mem_Icc.mp hy
    have hy0 : (0 : ℤ) ≤ (y : ℤ) := by exact_mod_cast (Nat.zero_le y)
    have hyM : (y : ℤ) ≤ (M : ℤ) := by exact_mod_cast hy2
    rw [hX]
    exact inner_reindex N M P f₀ f₁ β hs0 hy0 hyM
  rw [hmain]
  -- convert the `ℤ`-indexed sum on the right into the `ℕ`-indexed sum we produced
  congr 1
  exact (sum_Icc_intCast M (fun z : ℤ => ee (β * ((P.eval z : ℤ) : ℝ)) *
      ∑ u ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (f₀ u * ee (β * (u : ℝ))) * f₁ (u + z)))

end

end Work.Peluse
