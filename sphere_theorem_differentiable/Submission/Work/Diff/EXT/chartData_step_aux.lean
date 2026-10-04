import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.EXT.chartMat_det_ne_zero
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Generic local jet-calculus lemmas for the chart-data a priori estimate (`EXT`)

This module collects the small, reusable, *purely analytic* lemmas used by
`Work.Diff.EXT.chartData_step` and by the lemmas about the chart data of a Ricci flow family that
feed into it.  Everything here is stated for functions on a normed space `E`; no manifold
structure is used.

The main point of the "local" formulations (`_at`) is that the *bounds* on the jets are only
available at a single point `x`, while the corresponding Mathlib lemmas
(`norm_iteratedFDeriv_mul_le`, `iteratedFDeriv_sum_apply`, ...) are global.  The local versions are
obtained from the global (or `Within`, on an open neighbourhood) statements by the standard trick:
`ContDiffAt` gives a neighbourhood on which the functions are smooth, and on an *open* set the
`Within` jets coincide with the ambient ones (`iteratedFDerivWithin_of_isOpen`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- On an *open* set the `Within` jets agree with the ambient ones: pointwise form of
`iteratedFDerivWithin_of_isOpen`. -/
theorem iteratedFDerivWithin_eq_of_isOpen {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s) (n : ℕ) :
    iteratedFDerivWithin ℝ n f s x = iteratedFDeriv ℝ n f x :=
  iteratedFDerivWithin_of_isOpen n hs hx

/-- Norm form of `iteratedFDerivWithin_eq_of_isOpen`. -/
theorem norm_iteratedFDerivWithin_eq_of_isOpen {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n f s x‖ = ‖iteratedFDeriv ℝ n f x‖ := by
  rw [iteratedFDerivWithin_eq_of_isOpen hs hx n]

/-- **Local Leibniz bound.**  If `f` and `g` are smooth at `x` and all their iterated Fréchet
derivatives at `x` up to order `n` are bounded by `C`, then the `n`-th iterated Fréchet derivative
of the product is bounded by the Leibniz binomial sum. -/
theorem norm_iteratedFDeriv_mul_le_at {f g : E → ℝ} {x : E} {n : ℕ} {C : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (hCf : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hCg : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C * C := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hCf 0 (Nat.zero_le n))
  obtain ⟨u, hu_mem, hu⟩ := hf.contDiffOn (m := (n : ℕ∞ω)) (by simp)
    (by intro h; exact absurd (WithTop.coe_inj.mp h) WithTop.coe_ne_top)
  obtain ⟨v, hv_mem, hv⟩ := hg.contDiffOn (m := (n : ℕ∞ω)) (by simp)
    (by intro h; exact absurd (WithTop.coe_inj.mp h) WithTop.coe_ne_top)
  obtain ⟨t, htu, htopen, hxt⟩ := _root_.mem_nhds_iff.mp (Filter.inter_mem hu_mem hv_mem)
  have hft : ContDiffOn ℝ (↑n : ℕ∞ω) f t := hu.mono (fun z hz => (htu hz).1)
  have hgt : ContDiffOn ℝ (↑n : ℕ∞ω) g t := hv.mono (fun z hz => (htu hz).2)
  have hmain := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (N := (↑n : ℕ∞ω)) hft hgt
    htopen.uniqueDiffOn hxt (n := n) le_rfl
  have hrew : ∀ (i : ℕ) (φ : E → ℝ),
      ‖iteratedFDerivWithin ℝ i φ t x‖ = ‖iteratedFDeriv ℝ i φ x‖ := fun i φ => by
    rw [iteratedFDerivWithin_eq_of_isOpen htopen hxt i]
  calc ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖
      = ‖iteratedFDerivWithin ℝ n (fun y => f y * g y) t x‖ :=
        (hrew n _).symm
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * ‖iteratedFDerivWithin ℝ i f t x‖
          * ‖iteratedFDerivWithin ℝ (n - i) g t x‖ := hmain
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
        refine Finset.sum_congr rfl fun i hi => by rw [hrew i f, hrew (n - i) g]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C * C := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
        have h2 : ‖iteratedFDeriv ℝ (n - i) g x‖ ≤ C := hCg (n - i) (by omega)
        have h3 : ‖iteratedFDeriv ℝ i f x‖ ≤ C := hCf i hi'
        have h4 : ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ ≤ C * C :=
          mul_le_mul h3 h2 (norm_nonneg _) hC0
        calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖
            = (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i f x‖
                * ‖iteratedFDeriv ℝ (n - i) g x‖) := by ring
          _ ≤ (n.choose i : ℝ) * (C * C) := mul_le_mul_of_nonneg_left h4 h1
          _ = (n.choose i : ℝ) * C * C := by ring

/-- **Local sum bound.**  A finite sum of functions all of whose `n`-th iterated Fréchet
derivatives at `x` are bounded by `C` has its `n`-th derivative bounded by `(card) * C`. -/
theorem norm_iteratedFDeriv_sum_le_at {ι : Type*} {s : Finset ι} {φ : ι → E → ℝ}
    {x : E} {n : ℕ} {C : ℝ} (hφ : ∀ i ∈ s, ContDiffAt ℝ (⊤ : ℕ∞) (φ i) x)
    (hC : ∀ i ∈ s, ‖iteratedFDeriv ℝ n (φ i) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y => ∑ i ∈ s, φ i y) x‖ ≤ s.card * C := by
  have h1 : (fun y : E => ∑ i ∈ s, φ i y) = (∑ i ∈ s, φ i) := by
    funext y
    rw [Finset.sum_apply]
  have hsum : iteratedFDeriv ℝ n (fun y => ∑ i ∈ s, φ i y) x
      = ∑ i ∈ s, iteratedFDeriv ℝ n (φ i) x := by
    rw [h1]
    exact iteratedFDeriv_sum_apply (u := s) (f := φ) (x := x) (n := n)
      (fun i hi => (hφ i hi).of_le (by simp))
  calc ‖iteratedFDeriv ℝ n (fun y => ∑ i ∈ s, φ i y) x‖
      = ‖∑ i ∈ s, iteratedFDeriv ℝ n (φ i) x‖ := by rw [hsum]
    _ ≤ ∑ i ∈ s, ‖iteratedFDeriv ℝ n (φ i) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, C := Finset.sum_le_sum hC
    _ = s.card * C := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Evaluation of a `CLM`-valued jet at a fixed vector.** -/
theorem iteratedFDeriv_clm_apply_const {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Ψ : E → (F →L[ℝ] G)} {x : E} {n : ℕ} {ζ : F}
    (hΨ : ContDiffAt ℝ (⊤ : ℕ∞) Ψ x) (v : Fin n → E) :
    (iteratedFDeriv ℝ n Ψ x v) ζ = iteratedFDeriv ℝ n (fun y => Ψ y ζ) x v := by
  have h := (ContinuousLinearMap.apply ℝ G ζ).iteratedFDeriv_comp_left
    (𝕜 := ℝ) (f := Ψ) hΨ (i := n) (by simp)
  have h2 := congrArg (fun T : E [×n]→L[ℝ] G => T v) h
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply] at h2
  exact h2.symm

/-- **Uniform constant over a finite range of orders.**  If for every `m ≤ k` a property `P m`
holds with some nonnegative constant, and `P m` is monotone in the constant, then a *single*
constant works for all `m ≤ k`. -/
theorem exists_uniform_bound_of_le {P : ℕ → ℝ → Prop}
    (hmono : ∀ m C C', P m C → C ≤ C' → P m C') :
    ∀ k, (∀ m ≤ k, ∃ C, 0 ≤ C ∧ P m C) → ∃ C, 0 ≤ C ∧ ∀ m ≤ k, P m C := by
  intro k
  induction k with
  | zero =>
      intro h
      obtain ⟨C, hC, hP⟩ := h 0 le_rfl
      exact ⟨C, hC, fun m hm => by rw [Nat.le_zero.mp hm]; exact hP⟩
  | succ k ih =>
      intro h
      obtain ⟨C₁, hC₁, hP₁⟩ := ih (fun m hm => h m (by omega))
      obtain ⟨C₂, hC₂, hP₂⟩ := h (k + 1) le_rfl
      refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun m hm => ?_⟩
      rcases lt_or_eq_of_le hm with hlt | heq
      · exact hmono m C₁ _ (hP₁ m (by omega)) (le_max_left _ _)
      · rw [heq]; exact hmono _ C₂ _ hP₂ (le_max_right _ _)

/-- **Unfolding of the recursion defining `aCovArr` at a successor order**: the chart derivative of
`aCovArr m` in the direction `d` is the next covariant derivative `aCovArr (m+1)` plus the
Christoffel corrections of the *background* connection `cGam (G 0)` in all `m + 3` tensor slots. -/
theorem fderiv_aCovArr_eq (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (m : ℕ)
    (d : Fin (Module.finrank ℝ E)) (v : Fin m → Fin (Module.finrank ℝ E))
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    fderiv ℝ (fun y' : E => aCovArr (I := I) (M := M) G x₀ t m v i j k y') y
        (Work.Diff.GE.cBasis (E := E) d)
      = aCovArr (I := I) (M := M) G x₀ t (m + 1) (Fin.cons d v) i j k y
        + ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p (v r) d)
              * (aCovArr (I := I) (M := M) G x₀ t m (Function.update v r p) i j k) y
        + ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p i d)
              * (aCovArr (I := I) (M := M) G x₀ t m v p j k) y
        + ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p j d)
              * (aCovArr (I := I) (M := M) G x₀ t m v i p k) y
        + ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p k d)
              * (aCovArr (I := I) (M := M) G x₀ t m v i j p) y := by
  have h : aCovArr (I := I) (M := M) G x₀ t (m + 1) (Fin.cons d v) i j k y
      = fderiv ℝ (fun y' : E => aCovArr (I := I) (M := M) G x₀ t m v i j k y') y
            (Work.Diff.GE.cBasis (E := E) d)
        - ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p (v r) d)
              * (aCovArr (I := I) (M := M) G x₀ t m (Function.update v r p) i j k) y
        - ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p i d)
              * (aCovArr (I := I) (M := M) G x₀ t m v p j k) y
        - ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p j d)
              * (aCovArr (I := I) (M := M) G x₀ t m v i p k) y
        - ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p k d)
              * (aCovArr (I := I) (M := M) G x₀ t m v i j p) y := by
    simp only [aCovArr, Fin.cons_zero, Fin.cons_succ]
  linarith [h]

/-- The coordinate functionals of `Module.finBasis` evaluated on `Module.finBasis`. -/
theorem finBasis_coord_finBasis (i j : Fin (Module.finrank ℝ E)) :
    (Module.finBasis ℝ E).coord i (Module.finBasis ℝ E j) = if i = j then (1 : ℝ) else 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- **The connection coefficients at time `t` versus time `0`.**  The chart array of the lowered
connection difference, contracted with the inverse metric, is exactly the difference of the
Christoffel symbols.  This is pure algebra: it only uses that `GramInv` is the inverse of
`GramM` (i.e. that the determinant does not vanish) and the definition of `aComp`. -/
theorem cGam_eq_cGam0_add (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (y : E)
    (hdet : (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)).det ≠ 0)
    (l i j : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) l i j
      = Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) l i j
        + ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k * aComp G x₀ t y i j k := by
  have hInv : Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y)
      * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) = 1 := by
    rw [Work.Diff.GE.GramInv]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have hstep : ∀ m : Fin (Module.finrank ℝ E),
      (∑ k : Fin (Module.finrank ℝ E),
        Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k
          * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) k m) = if l = m then 1 else 0 := by
    intro m
    have h := congrFun (congrFun hInv l) m
    rwa [Matrix.mul_apply, Matrix.one_apply] at h
  have hΔ : (∑ k : Fin (Module.finrank ℝ E),
        Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k * aComp G x₀ t y i j k)
      = Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) l i j
        - Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) l i j := by
    calc (∑ k : Fin (Module.finrank ℝ E),
          Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k * aComp G x₀ t y i j k)
        = ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k
              * ∑ m : Fin (Module.finrank ℝ E),
                  Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) k m
                    * (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) m i j
                        - Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) m i j) := rfl
      _ = ∑ m : Fin (Module.finrank ℝ E),
            (∑ k : Fin (Module.finrank ℝ E),
              Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k
                * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) k m)
              * (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) m i j
                  - Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) m i j) := by
          have h1 : ∀ k : Fin (Module.finrank ℝ E),
              Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k
                * (∑ m : Fin (Module.finrank ℝ E),
                    Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) k m
                      * (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) m i j
                          - Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) m i j))
                = ∑ m : Fin (Module.finrank ℝ E),
                    (Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k
                      * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) k m)
                      * (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) m i j
                          - Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) m i j) := by
            intro k
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun m _ => by ring
          simp only [h1]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m _ => (Finset.sum_mul ..).symm
      _ = Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) l i j
            - Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) l i j := by
          rw [Finset.sum_eq_single l]
          · rw [hstep l]; simp
          · intro m _ hm
            have hzero : (if l = m then (1 : ℝ) else 0) = 0 :=
              if_neg (fun h : l = m => hm h.symm)
            rw [hstep m, hzero, zero_mul]
          · intro hl; exact absurd (Finset.mem_univ l) hl
  linarith [hΔ]

/-- **Leibniz bound with a single constant for all orders `≤ k`.**  If `f` and `g` have all their
iterated Fréchet derivatives at `x` up to order `k` bounded by `B`, then the `m`-th derivative of
the product (`m ≤ k`) is bounded by `2 ^ k * B * B`. -/
theorem norm_iteratedFDeriv_mul_le_at_le {f g : E → ℝ} {x : E} {k m : ℕ} {B : ℝ}
    (hmk : m ≤ k) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (hB0 : 0 ≤ B) (hCf : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f x‖ ≤ B)
    (hCg : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => f y * g y) x‖ ≤ (2 : ℝ) ^ k * B * B := by
  refine le_trans (norm_iteratedFDeriv_mul_le_at (E := E) (n := m) (C := B) hf hg
    (fun i hi => hCf i (le_trans hi hmk)) (fun i hi => hCg i (le_trans hi hmk))) ?_
  have h2 : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = (2 : ℝ) ^ m := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    norm_num
  have h1 : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B * B)
      = (2 : ℝ) ^ m * B * B := by
    rw [← h2]
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [h1]
  have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hmk
  nlinarith [hpow, hB0, mul_nonneg hB0 hB0]

/-- **The Gram matrix of the coordinate frame is non-singular** at every chart coordinate in the
target of the chart at `x₀`. -/
theorem gramM_det_ne_zero_target [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)).det ≠ 0 := by
  have h : Matrix.of (chartMatFun (I := I) (M := M) (G t) x₀ y)
      = Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) := by
    ext i j
    rw [Matrix.of_apply]
    rfl
  rw [← h]
  exact chartMat_det_ne_zero (I := I) (M := M) (G t) x₀ hy

/-- **Local additivity bound.**  If `f` and `g` are smooth at `x` and both have `n`-th iterated
Fréchet derivative at `x` bounded by `C`, then so does their sum, with bound `2 * C`. -/
theorem norm_iteratedFDeriv_add_le_at {f g : E → ℝ} {x : E} {n : ℕ} {C : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (hCf : ‖iteratedFDeriv ℝ n f x‖ ≤ C) (hCg : ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y => f y + g y) x‖ ≤ 2 * C := by
  have h2 : (fun y : E => f y + g y)
      = fun y : E => ∑ i : Fin 2, (if i = (0 : Fin 2) then f else g) y := by
    funext y
    rw [Fin.sum_univ_two]
    simp
  rw [h2]
  have hφsm : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => (if i = (0 : Fin 2) then f else g) y) x := by
    intro i _
    by_cases hi : i = 0
    · simpa [hi] using hf
    · simpa [hi] using hg
  have hφC : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      ‖iteratedFDeriv ℝ n (fun y : E => (if i = (0 : Fin 2) then f else g) y) x‖ ≤ C := by
    intro i _
    by_cases hi : i = 0
    · simpa [hi] using hCf
    · simpa [hi] using hCg
  have hmain := norm_iteratedFDeriv_sum_le_at (E := E) (s := (Finset.univ : Finset (Fin 2)))
    (φ := fun i y => (if i = (0 : Fin 2) then f else g) y) (x := x) (n := n) (C := C)
    hφsm hφC
  simpa using hmain


/-- **Additive local jet bound.**  If `f` and `g` are smooth at `x` with `n`-th jet bounds `C` and
`D`, then the `n`-th jet of the sum is bounded by `C + D`. -/
theorem norm_iteratedFDeriv_add_le_at₂ {f g : E → ℝ} {x : E} {n : ℕ} {C D : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (hCf : ‖iteratedFDeriv ℝ n f x‖ ≤ C) (hCg : ‖iteratedFDeriv ℝ n g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (fun y => f y + g y) x‖ ≤ C + D := by
  have h2 : (fun y : E => f y + g y)
      = fun y : E => ∑ i : Fin 2, (if i = (0 : Fin 2) then f else g) y := by
    funext y
    rw [Fin.sum_univ_two]
    simp
  rw [h2]
  have hsum : iteratedFDeriv ℝ n (fun y : E =>
        ∑ i : Fin 2, (if i = (0 : Fin 2) then f else g) y) x
      = ∑ i : Fin 2, iteratedFDeriv ℝ n (if i = (0 : Fin 2) then f else g) x := by
    have h1 : (fun y : E => ∑ i : Fin 2, (if i = (0 : Fin 2) then f else g) y)
        = (∑ i : Fin 2, (if i = (0 : Fin 2) then f else g)) := by
      funext y
      rw [Finset.sum_apply]
    rw [h1]
    exact iteratedFDeriv_sum_apply (u := Finset.univ)
      (f := fun i : Fin 2 => if i = (0 : Fin 2) then f else g) (x := x) (n := n)
      (fun i _ => by
        by_cases hi : i = 0
        · simpa [hi] using hf.of_le (by simp)
        · simpa [hi] using hg.of_le (by simp))
  rw [hsum]
  calc ‖∑ i : Fin 2, iteratedFDeriv ℝ n (if i = (0 : Fin 2) then f else g) x‖
      ≤ ∑ i : Fin 2, ‖iteratedFDeriv ℝ n (if i = (0 : Fin 2) then f else g) x‖ := norm_sum_le _ _
    _ = ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n g x‖ := by
        rw [Fin.sum_univ_two]
        simp
    _ ≤ C + D := add_le_add hCf hCg

/-- **Five-term additive local jet bound**: a common bound `C` for the five summands gives the
bound `16 * C` for the sum (used to reassemble the Christoffel corrections of `aCovArr`). -/
theorem norm_iteratedFDeriv_add5_le_at {f1 f2 f3 f4 f5 : E → ℝ} {x : E} {n : ℕ} {C : ℝ}
    (h1 : ContDiffAt ℝ (⊤ : ℕ∞) f1 x) (h2 : ContDiffAt ℝ (⊤ : ℕ∞) f2 x)
    (h3 : ContDiffAt ℝ (⊤ : ℕ∞) f3 x) (h4 : ContDiffAt ℝ (⊤ : ℕ∞) f4 x)
    (h5 : ContDiffAt ℝ (⊤ : ℕ∞) f5 x)
    (hC1 : ‖iteratedFDeriv ℝ n f1 x‖ ≤ C) (hC2 : ‖iteratedFDeriv ℝ n f2 x‖ ≤ C)
    (hC3 : ‖iteratedFDeriv ℝ n f3 x‖ ≤ C) (hC4 : ‖iteratedFDeriv ℝ n f4 x‖ ≤ C)
    (hC5 : ‖iteratedFDeriv ℝ n f5 x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y => f1 y + f2 y + f3 y + f4 y + f5 y) x‖ ≤ 16 * C := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hC1
  have h12 : ‖iteratedFDeriv ℝ n (fun y => f1 y + f2 y) x‖ ≤ 2 * C :=
    norm_iteratedFDeriv_add_le_at (f := f1) (g := f2) h1 h2 hC1 hC2
  have h123 : ‖iteratedFDeriv ℝ n (fun y => f1 y + f2 y + f3 y) x‖ ≤ 4 * C := by
    have h := norm_iteratedFDeriv_add_le_at (f := fun y => f1 y + f2 y) (g := f3)
      (C := 2 * C) (ContDiffAt.add h1 h2) h3 h12 (le_trans hC3 (by linarith))
    calc ‖iteratedFDeriv ℝ n (fun y => f1 y + f2 y + f3 y) x‖
        = ‖iteratedFDeriv ℝ n ((fun y => f1 y + f2 y) + f3) x‖ := rfl
      _ ≤ 2 * (2 * C) := h
      _ = 4 * C := by ring
  have h1234 : ‖iteratedFDeriv ℝ n (fun y => f1 y + f2 y + f3 y + f4 y) x‖ ≤ 8 * C := by
    have h := norm_iteratedFDeriv_add_le_at (f := fun y => f1 y + f2 y + f3 y) (g := f4)
      (C := 4 * C) (ContDiffAt.add (ContDiffAt.add h1 h2) h3) h4 h123
      (le_trans hC4 (by linarith))
    calc ‖iteratedFDeriv ℝ n (fun y => f1 y + f2 y + f3 y + f4 y) x‖
        = ‖iteratedFDeriv ℝ n ((fun y => f1 y + f2 y + f3 y) + f4) x‖ := rfl
      _ ≤ 2 * (4 * C) := h
      _ = 8 * C := by ring
  have h := norm_iteratedFDeriv_add_le_at (f := fun y => f1 y + f2 y + f3 y + f4 y) (g := f5)
    (C := 8 * C) (ContDiffAt.add (ContDiffAt.add (ContDiffAt.add h1 h2) h3) h4) h5
    h1234 (le_trans hC5 (by linarith))
  calc ‖iteratedFDeriv ℝ n (fun y => f1 y + f2 y + f3 y + f4 y + f5 y) x‖
      = ‖iteratedFDeriv ℝ n ((fun y => f1 y + f2 y + f3 y + f4 y) + f5) x‖ := rfl
    _ ≤ 2 * (8 * C) := h
    _ = 16 * C := by ring

/-- **Local jet bound for `scalar • vector`.**  If the scalar factor has all its jets up to `n`
bounded by `C` and the vector factor by `D`, the `n`-th jet of the product is bounded by
`2 ^ n * C * D`. -/
theorem norm_iteratedFDeriv_smul_le_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ} {g : E → F} {x : E} {n : ℕ} {C D : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (hCf : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hCg : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (fun y => f y • g y) x‖ ≤ (2 : ℝ) ^ n * C * D := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hCf 0 (Nat.zero_le n))
  obtain ⟨u, hu_mem, hu⟩ := hf.contDiffOn (m := (n : ℕ∞ω)) (by simp)
    (by intro h; exact absurd (WithTop.coe_inj.mp h) WithTop.coe_ne_top)
  obtain ⟨v, hv_mem, hv⟩ := hg.contDiffOn (m := (n : ℕ∞ω)) (by simp)
    (by intro h; exact absurd (WithTop.coe_inj.mp h) WithTop.coe_ne_top)
  obtain ⟨t, htu, htopen, hxt⟩ := _root_.mem_nhds_iff.mp (Filter.inter_mem hu_mem hv_mem)
  have hft : ContDiffOn ℝ (↑n : ℕ∞ω) f t := hu.mono (fun z hz => (htu hz).1)
  have hgt : ContDiffOn ℝ (↑n : ℕ∞ω) g t := hv.mono (fun z hz => (htu hz).2)
  have hmain := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (N := (↑n : ℕ∞ω)) hft hgt
    htopen.uniqueDiffOn hxt (n := n) le_rfl
  calc ‖iteratedFDeriv ℝ n (fun y => f y • g y) x‖
      = ‖iteratedFDerivWithin ℝ n (fun y => f y • g y) t x‖ :=
        (norm_iteratedFDerivWithin_eq_of_isOpen htopen hxt n (f := fun y => f y • g y)).symm
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * ‖iteratedFDerivWithin ℝ i f t x‖
          * ‖iteratedFDerivWithin ℝ (n - i) g t x‖ := hmain
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
        refine Finset.sum_congr rfl fun i hi => by
          rw [norm_iteratedFDerivWithin_eq_of_isOpen htopen hxt i (f := f),
            norm_iteratedFDerivWithin_eq_of_isOpen htopen hxt (n - i) (f := g)]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C * D := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
        have h2 := hCf i hi'
        have h3 := hCg (n - i) (by omega)
        have h4 : ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ ≤ C * D :=
          mul_le_mul h2 h3 (norm_nonneg _) hC0
        calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖
              * ‖iteratedFDeriv ℝ (n - i) g x‖
            = (n.choose i : ℝ)
              * (‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) := by ring
          _ ≤ (n.choose i : ℝ) * (C * D) := mul_le_mul_of_nonneg_left h4 h1
          _ = (n.choose i : ℝ) * C * D := by ring
    _ = (2 : ℝ) ^ n * C * D := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have h2 : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
          rw [← Nat.cast_sum, Nat.sum_range_choose]
          norm_num
        rw [h2]

/-- **Jet bounds for finite products.**  A finite product of functions all of whose jets up to
order `k` are bounded by `B` has bounded jets (with a constant depending on `k`, `B` and the
cardinality). -/
theorem exists_jets_finset_prod_bound {ι : Type*} (k : ℕ) (s : Finset ι) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ι → E → ℝ) (x : E),
      (∀ i ∈ s, ContDiffAt ℝ (⊤ : ℕ∞) (f i) x) →
      (∀ i ∈ s, ∀ m ≤ k, ‖iteratedFDeriv ℝ m (f i) x‖ ≤ B) →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ∏ i ∈ s, f i y) x ∧
        (∀ m ≤ k, ‖iteratedFDeriv ℝ m (fun y => ∏ i ∈ s, f i y) x‖ ≤ C) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, fun f x hf hb => ⟨contDiffAt_const, fun m hm => ?_⟩⟩
      have hempty : (fun y : E => ∏ i ∈ (∅ : Finset ι), f i y) = fun _ => (1 : ℝ) := by
        funext y
        simp
      rw [hempty]
      by_cases hm0 : m = 0
      · subst hm0
        simp
      · rw [iteratedFDeriv_const_of_ne hm0]
        simp
  | insert a s ha ih =>
      obtain ⟨Cs, hCs0, ihs⟩ := ih
      set B' : ℝ := max 1 (max B Cs) with hB'def
      have hB'0 : 0 ≤ B' := le_trans zero_le_one (le_max_left _ _)
      have hBB' : B ≤ B' := le_trans (le_max_left B Cs) (le_max_right 1 (max B Cs))
      have hCsB' : Cs ≤ B' := le_trans (le_max_right B Cs) (le_max_right 1 (max B Cs))
      refine ⟨(2 : ℝ) ^ k * B' * B', by positivity, fun f x hf hb => ?_⟩
      have hfa : ContDiffAt ℝ (⊤ : ℕ∞) (f a) x := hf a (Finset.mem_insert_self _ _)
      have hfs : ∀ i ∈ s, ContDiffAt ℝ (⊤ : ℕ∞) (f i) x := fun i hi =>
        hf i (Finset.mem_insert_of_mem hi)
      have hba : ∀ m ≤ k, ‖iteratedFDeriv ℝ m (f a) x‖ ≤ B' := fun m hm =>
        le_trans (hb a (Finset.mem_insert_self _ _) m hm) hBB'
      have hbs : ∀ i ∈ s, ∀ m ≤ k, ‖iteratedFDeriv ℝ m (f i) x‖ ≤ B' := fun i hi m hm =>
        le_trans (hb i (Finset.mem_insert_of_mem hi) m hm) hBB'
      obtain ⟨hsmS, hS⟩ := ihs f x hfs (fun i hi m hm => hb i (Finset.mem_insert_of_mem hi) m hm)
      have h1 : (fun y : E => ∏ i ∈ insert a s, f i y) = fun y => f a y * ∏ i ∈ s, f i y := by
        funext y
        rw [Finset.prod_insert ha]
      refine ⟨?_, fun m hm => ?_⟩
      · rw [h1]
        exact ContDiffAt.mul hfa hsmS
      · rw [h1]
        exact norm_iteratedFDeriv_mul_le_at_le (k := k) (m := m) (B := B') hm hfa hsmS hB'0
          hba (fun i hi => le_trans (hS i hi) hCsB')

/-- **Jet bounds for the reciprocal of a scalar function bounded below.**  If `g` is smooth at `x`
with `c ≤ g x` and all its jets up to order `k` at `x` bounded by `B`, then the jets of `1/g` are
bounded by a constant depending on `k`, `c`, `B`. -/
theorem exists_bound_inv_jets (k : ℕ) (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : E → ℝ) (x : E), ContDiffAt ℝ (⊤ : ℕ∞) g x → c ≤ g x →
      (∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ B) →
      ∀ m ≤ k, ‖iteratedFDeriv ℝ m (fun y => (g y)⁻¹) x‖ ≤ C := by
  have key : ∀ m ≤ k, ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ (g : E → ℝ) (x : E),
      ContDiffAt ℝ (⊤ : ℕ∞) g x → c ≤ g x → (∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ B) →
      ∀ i ≤ m, ‖iteratedFDeriv ℝ i (fun y => (g y)⁻¹) x‖ ≤ Cm := by
    intro m
    induction m with
    | zero =>
        intro _
        refine ⟨max c⁻¹ 1, ?_, ?_⟩
        · exact le_trans (inv_nonneg.mpr hc.le) (le_max_left _ _)
        · intro g x hg hcx hBg i hi
          have hi0 : i = 0 := Nat.le_zero.mp hi
          subst hi0
          rw [norm_iteratedFDeriv_zero]
          have hg0 : 0 < g x := lt_of_lt_of_le hc hcx
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hg0)]
          exact le_trans (inv_anti₀ hc hcx) (le_max_left _ _)
    | succ m ih =>
        intro hmk
        obtain ⟨Cm, hCm0, hCm⟩ := ih (by omega)
        set C' : ℝ := max Cm c⁻¹ with hC'def
        have hC'0 : 0 ≤ C' := le_trans hCm0 (le_max_left _ _)
        have hCmC' : Cm ≤ C' := le_max_left _ _
        refine ⟨max Cm ((2 : ℝ) ^ k * ((2 : ℝ) ^ k * C' * C') * B), ?_, ?_⟩
        · exact le_trans hCm0 (le_max_left Cm _)
        · intro g x hg hcx hBg i hi
          rcases lt_or_eq_of_le hi with hlt | heq
          · exact le_trans (hCm g x hg hcx hBg i (by omega)) (le_max_left _ _)
          · subst heq
            have hle : ((1 : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top
            obtain ⟨u, hu_mem, huon⟩ := hg.contDiffOn (m := ((1 : ℕ) : ℕ∞ω)) hle
              (by intro h; exact absurd h (by simp))
            obtain ⟨o, huo, hoopen, hxo⟩ := _root_.mem_nhds_iff.mp hu_mem
            have huon' : ContDiffOn ℝ ((1 : ℕ) : ℕ∞ω) g o := huon.mono huo
            have hg0 : g x ≠ 0 := ne_of_gt (lt_of_lt_of_le hc hcx)
            have hid : fderiv ℝ (fun y => (g y)⁻¹) =ᶠ[𝓝 x]
                fun y => (-((g y) ^ 2)⁻¹) • fderiv ℝ g y := by
              filter_upwards [hoopen.mem_nhds hxo, hg.continuousAt.eventually_ne hg0]
                with y hyo hyne
              have hdw : DifferentiableWithinAt ℝ g o y :=
                (huon'.differentiableOn (by norm_num)) y hyo
              have hdgy : DifferentiableAt ℝ g y :=
                hdw.differentiableAt (hoopen.mem_nhds hyo)
              have h1 : (fun y' : E => (g y')⁻¹) = (fun z : ℝ => z⁻¹) ∘ g := rfl
              rw [h1, fderiv_comp y (differentiableAt_inv hyne) hdgy, fderiv_inv]
              ext v
              rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
                smul_apply, smul_eq_mul, smul_eq_mul]
              ring
            have hjet : ‖iteratedFDeriv ℝ (m + 1) (fun y => (g y)⁻¹) x‖
                = ‖iteratedFDeriv ℝ m (fun y => (-((g y) ^ 2)⁻¹) • fderiv ℝ g y) x‖ := by
              rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun y => (g y)⁻¹) (n := m)]
              exact congrArg _ ((Filter.EventuallyEq.iteratedFDeriv ℝ hid m).eq_of_nhds)
            rw [hjet]
            have hneg : (fun y : E => (-((g y) ^ 2)⁻¹) • fderiv ℝ g y)
                = -(fun y : E => ((g y) ^ 2)⁻¹ • fderiv ℝ g y) := by
              funext y
              rw [Pi.neg_apply, neg_smul]
            rw [hneg, iteratedFDeriv_neg]
            simp only [Pi.neg_apply, norm_neg]
            have hscalar : ∀ i' ≤ m, ‖iteratedFDeriv ℝ i' (fun y => ((g y) ^ 2)⁻¹) x‖
                ≤ (2 : ℝ) ^ k * C' * C' := by
              intro i' hi'
              have h1 : (fun y : E => ((g y) ^ 2)⁻¹) = fun y => (g y)⁻¹ * (g y)⁻¹ := by
                funext y
                rw [← inv_pow, pow_two]
              rw [h1]
              refine le_trans (norm_iteratedFDeriv_mul_le_at_le (k := i') (m := i') le_rfl
                (hg.inv hg0) (hg.inv hg0) hC'0 ?_ ?_) ?_
              · intro j hj
                exact le_trans (hCm g x hg hcx hBg j (by omega)) hCmC'
              · intro j hj
                exact le_trans (hCm g x hg hcx hBg j (by omega)) hCmC'
              · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                  (pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (by omega : i' ≤ k))
                  (by positivity)) (by positivity)
            have hsmP : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => ((g y) ^ 2)⁻¹) x := by
              refine (hg.pow 2).inv ?_
              show (g x) ^ 2 ≠ 0
              exact pow_ne_zero 2 hg0
            refine le_trans (norm_iteratedFDeriv_smul_le_at (n := m)
              (C := (2 : ℝ) ^ k * C' * C') (D := B)
              hsmP (hg.fderiv_right (by simp)) hscalar ?_) ?_
            · intro j hj
              rw [norm_iteratedFDeriv_fderiv]
              exact hBg (j + 1) (by omega)
            · refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (by omega : m ≤ k))
                (by positivity))
                hB) ?_
              exact le_max_right _ _
  obtain ⟨Ck, hCk0, hCk⟩ := key k le_rfl
  exact ⟨Ck, hCk0, fun g x hg hcx hBg m hm => hCk g x hg hcx hBg m hm⟩

end Work.Diff.EXT
