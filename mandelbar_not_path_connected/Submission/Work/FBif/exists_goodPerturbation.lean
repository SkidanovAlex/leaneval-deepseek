import Mathlib
import Submission.Work.FBif.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Polynomial

namespace Work.FBif

/-! ## The auxiliary polynomial `M` and two elementary facts about it

Write `z_j = T_c^j z₁` for the points of the parabolic cycle and `z̄_j` for their complex
conjugates.  Following Hubbard–Schleicher we set

`M = ∏_{j<4} (X - z̄_j)^2`   (degree `8`).

The hypothesis `z_j ≠ z₄` for `j ≤ 3` guarantees that `M` does not vanish at `z̄₄`
(`auxM_eval_ne_zero`) — the only non-degeneracy the construction needs — and `M` is divisible by
each of the four double factors (`auxM_dvd`). -/

/-- The auxiliary polynomial `M = ∏_{j<4} (X - z̄_j)^2` of Hubbard–Schleicher's Lemma 3.4. -/
noncomputable def auxM (c z₁ : ℂ) : ℂ[X] :=
  ∏ j ∈ Finset.range 4, (X - C (star (cyclePt c z₁ j))) ^ 2

/-- If the four cycle points `z₀, …, z₃` avoid `z₄`, then `M(z̄₄) ≠ 0`. -/
lemma auxM_eval_ne_zero (c z₁ : ℂ)
    (hdist : ∀ j : ℕ, j ≤ 3 → cyclePt c z₁ j ≠ cyclePt c z₁ 4) :
    (auxM c z₁).eval (star (cyclePt c z₁ 4)) ≠ 0 := by
  rw [auxM, Polynomial.eval_prod]
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have hj3 : j ≤ 3 := by
    have : j < 4 := Finset.mem_range.mp hj
    omega
  have hne : star (cyclePt c z₁ j) ≠ star (cyclePt c z₁ 4) :=
    fun h => hdist j hj3 (star_injective h)
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact pow_ne_zero 2 (sub_ne_zero.mpr hne.symm)

/-- `M` is divisible by `(X - z̄_j)^2` for `j ≤ 3`. -/
lemma auxM_dvd (c z₁ : ℂ) {j : ℕ} (hj : j ≤ 3) :
    (X - C (star (cyclePt c z₁ j))) ^ 2 ∣ auxM c z₁ := by
  rw [auxM]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))

/-- A polynomial `p` whose derivative vanishes at `a` has `p - p(a)` divisible by `(X - a)^2`:
the elementary "double root" criterion, in the form needed for the second-order vanishing of the
perturbation at `z₄`. -/
lemma sq_dvd_sub_C_eval {p : ℂ[X]} {a : ℂ} (h : p.derivative.eval a = 0) :
    (X - C a) ^ 2 ∣ p - C (p.eval a) := by
  set q := p - C (p.eval a) with hq
  by_cases hq0 : q = 0
  · rw [hq0]; exact dvd_zero _
  · rw [← le_rootMultiplicity_iff hq0]
    show 1 < q.rootMultiplicity a
    rw [one_lt_rootMultiplicity_iff_isRoot hq0]
    constructor
    · simp [Polynomial.IsRoot, hq]
    · simp [Polynomial.IsRoot, hq, h]

/-- **The perturbing antipolynomial of HS Lemma 3.4 exists.**  Assume `T⁴ z₁` is different from
`z₁, T z₁, T² z₁, T³ z₁` (true for the parabolic cycle of a root-parabolic parameter, see
`Work.EL.RootParabolic.cyclePt_ne_four`).  Then for any prescribed nonzero value `v` there is an
antipolynomial `q = P(z̄)` that vanishes to second order at `z₁, T z₁, T² z₁, T³ z₁`, vanishes to
second order at `T⁴ z₁` up to the value, and satisfies `q (T⁴ z₁) = v`.

Explicitly, with `M := ∏_{j≤3} (X - z̄_j)²` (degree `8`, and `M(z̄₄) ≠ 0` by the hypothesis),
`A₀ := v / M(z̄₄) ≠ 0` and `B₀ := -A₀ M'(z̄₄)/M(z̄₄)`, the polynomial `P := A₀ M + B₀ M (X - z̄₄)`
(degree `9`) works. -/
theorem exists_goodPerturbation (c : ℂ) (z₁ : ℂ) {v : ℂ} (hv : v ≠ 0)
    (hdist : ∀ j : ℕ, j ≤ 3 → cyclePt c z₁ j ≠ cyclePt c z₁ 4) :
    ∃ q : ℂ → ℂ, GoodPerturbation c z₁ q ∧ q (cyclePt c z₁ 4) = v := by
  have hm : (auxM c z₁).eval (star (cyclePt c z₁ 4)) ≠ 0 := auxM_eval_ne_zero c z₁ hdist
  set A₀ : ℂ := v / (auxM c z₁).eval (star (cyclePt c z₁ 4)) with hA₀
  set B₀ : ℂ := -A₀ * ((auxM c z₁).derivative.eval (star (cyclePt c z₁ 4))) /
      (auxM c z₁).eval (star (cyclePt c z₁ 4)) with hB₀
  set P : ℂ[X] := C A₀ * auxM c z₁ +
      C B₀ * (auxM c z₁ * (X - C (star (cyclePt c z₁ 4)))) with hP
  -- `P` takes the prescribed value `v` at `z̄₄`
  have hPval : P.eval (star (cyclePt c z₁ 4)) = v := by
    rw [hP]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, sub_self, mul_zero, add_zero]
    rw [hA₀, div_mul_cancel₀ _ hm]
  -- and `P - v` has a double root at `z̄₄`
  have hPderiv : P.derivative.eval (star (cyclePt c z₁ 4)) = 0 := by
    have hB₀m : B₀ * (auxM c z₁).eval (star (cyclePt c z₁ 4)) =
        -(A₀ * (auxM c z₁).derivative.eval (star (cyclePt c z₁ 4))) := by
      rw [hB₀, div_mul_cancel₀ _ hm]; ring
    rw [hP, derivative_add, derivative_C_mul, derivative_C_mul, derivative_mul,
      derivative_X_sub_C, mul_one]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, sub_self, mul_zero, zero_add]
    rw [hB₀m]
    ring
  refine ⟨fun z => P.eval (star z), ?_, ?_⟩
  · refine ⟨P, fun z => rfl, ?_, ?_, ?_⟩
    · intro j hj
      have h1 := auxM_dvd c z₁ hj
      rw [hP]
      exact dvd_add (dvd_mul_of_dvd_right h1 (C A₀))
        (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h1 (X - C (star (cyclePt c z₁ 4)))) (C B₀))
    · exact sq_dvd_sub_C_eval hPderiv
    · show P.eval (star (cyclePt c z₁ 4)) ≠ 0
      rw [hPval]; exact hv
  · exact hPval

end Work.FBif
