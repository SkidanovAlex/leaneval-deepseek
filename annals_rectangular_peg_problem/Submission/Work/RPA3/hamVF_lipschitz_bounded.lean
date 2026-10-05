import Mathlib
import Submission.Work.RPA3.A3Defs
import Submission.Work.RPCore.Flow.clampedField_bounds

/-!
# The Hamiltonian vector field of a compactly supported periodic Hamiltonian

Let `H : ℝ → PS → ℝ` be `C⁴`, `2π`-periodic in the angle `q₂`, vanishing for `|t| ≥ T` and for
`|q₁| + |p₁| + |p₂| ≥ R`.  Then the field

`Φ (t, x) = X_{H t} x = hamVF (H t) x`

is globally Lipschitz (as a function of `(t,x)`) and globally bounded.

Both are consequences of the same compactness statement `bounded_of_periodic_of_eq_on_slab`: `Φ`
and `fderiv Φ` are continuous, `2π`-periodic in `q₂`, and vanish off the support slab
`{|q₁| + |p₁| + |p₂| > R}`; off the strip `|t| ≥ T` the field (and, at `|t| > T`, its derivative)
vanishes outright.  The Lipschitz bound is then the mean value inequality applied to the uniform
bound on `fderiv Φ`.
-/

open scoped ContDiff Topology
open Filter

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

theorem hamVF_lipschitz_bounded (H : ℝ → Work.RPA3.PS → ℝ)
    (hsmooth : ContDiff ℝ 4 (fun z : ℝ × Work.RPA3.PS => H z.1 z.2))
    (hper : ∀ t x, H t (Work.RPA3.Tk 1 x) = H t x)
    (hT : ∃ T, ∀ t x, T ≤ |t| → H t x = 0)
    (hR : ∃ R, ∀ t x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| → H t x = 0) :
    (∃ K : NNReal, LipschitzWith K (fun p : ℝ × Work.RPA3.PS => Work.RPA3.hamVF (H p.1) p.2)) ∧
      (∃ M : ℝ, ∀ t x, ‖Work.RPA3.hamVF (H t) x‖ ≤ M) := by
  classical
  obtain ⟨T, hT⟩ := hT
  obtain ⟨R, hR⟩ := hR
  -- The uncurried Hamiltonian and the field `Φ = X_H`.
  set U : ℝ × PS → ℝ := fun z => H z.1 z.2 with hUdef
  have hU : ContDiff ℝ 4 U := hsmooth
  have hUfun : ∀ t : ℝ, (fun y : PS => U (t, y)) = H t := by
    intro t; funext y; simp [hUdef]
  set Φ : ℝ × PS → PS := fun z => hamVF (fun y : PS => U (z.1, y)) z.2 with hΦdef
  have hΦeq : Φ = fun p : ℝ × PS => hamVF (H p.1) p.2 := by
    funext p
    show hamVF (fun y : PS => U (p.1, y)) p.2 = hamVF (H p.1) p.2
    rw [hUfun p.1]
  -- `Φ` is `C³`.
  have hΦ : ContDiff ℝ 3 Φ := Work.RPCore.Flow.contDiff_hamVF_partial 3 U hU
  -- The additive form of the angle shift, for `Work.RPA3.Tk`.
  have hTk_add : ∀ x : PS, Tk 1 x = x + Work.RPCore.Flow.tkShift := by
    intro x; ext <;> simp [Tk, Work.RPCore.Flow.tkShift]
  -- `Φ` is `2π`-periodic in `q₂`.
  have hΦper : ∀ z : ℝ × PS, Φ (z.1, Tk 1 z.2) = Φ z := by
    intro z
    have hWd : Differentiable ℝ (fun y : PS => U (z.1, y)) := by
      have hc : ContDiff ℝ 4 (fun y : PS => (z.1, y)) :=
        (contDiff_const : ContDiff ℝ 4 (fun _ : PS => z.1)).prodMk contDiff_id
      exact (hU.comp hc).differentiable (by norm_num)
    show hamVF (fun y : PS => U (z.1, y)) (Tk 1 z.2) = hamVF (fun y : PS => U (z.1, y)) z.2
    exact Work.RPCore.Flow.hamVF_eq_of_Tk hWd (fun y => hper z.1 y) z.2
  -- `Φ` vanishes strictly outside the support slab of `H`.
  have hΦsupp : ∀ z : ℝ × PS, R < |z.2.1.1| + |z.2.2.1| + |z.2.2.2| → Φ z = 0 := by
    intro z hz
    have hcont : Continuous fun y : PS => |y.1.1| + |y.2.1| + |y.2.2| := by fun_prop
    have hopen : {y : PS | R < |y.1.1| + |y.2.1| + |y.2.2|} ∈ 𝓝 z.2 :=
      (isOpen_lt continuous_const hcont).mem_nhds hz
    have hev : (fun y : PS => U (z.1, y)) =ᶠ[𝓝 z.2] 0 := by
      filter_upwards [hopen] with y hy
      simpa [hUdef] using hR z.1 y hy.le
    show hamVF (fun y : PS => U (z.1, y)) z.2 = 0
    exact Work.RPCore.Flow.hamVF_eq_zero_of_eventuallyEq_zero hev
  -- `‖Φ‖` is bounded on the strip `{|t| ≤ T}`.
  obtain ⟨M0, hM00, hM0⟩ :=
    Work.RPCore.Flow.bounded_of_periodic_of_eq_on_slab Φ hΦ.continuous hΦper hΦsupp T
  -- Off the strip `Φ` vanishes identically, so `‖Φ‖` is globally bounded by `M0`.
  have hbound : ∃ M : ℝ, ∀ t x, ‖hamVF (H t) x‖ ≤ M := by
    refine ⟨M0, fun t x => ?_⟩
    have hval : hamVF (H t) x = Φ (t, x) := by rw [hΦeq]
    rw [hval]
    by_cases ht : |t| ≤ T
    · exact hM0 (t, x) ht
    · have hzero : Φ (t, x) = 0 := by
        show hamVF (fun y : PS => U (t, y)) x = 0
        rw [hUfun t]
        have hHt : H t = fun _ => (0 : ℝ) := funext (fun y => hT t y (not_le.mp ht).le)
        rw [hHt]
        simp [hamVF]
      rw [hzero, norm_zero]
      exact hM00
  -- The derivative `fderiv Φ` is `2π`-periodic in `q₂`.
  have hΦdiff : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hgper : ∀ z : ℝ × PS, fderiv ℝ Φ (z.1, Tk 1 z.2) = fderiv ℝ Φ z := by
    intro z
    have hshift : ∀ w : ℝ × PS, Φ (w + (0, Work.RPCore.Flow.tkShift)) = Φ w := by
      rintro ⟨w1, w2⟩
      have hT : (w1, w2) + ((0 : ℝ), Work.RPCore.Flow.tkShift) = (w1, Tk 1 w2) := by
        rw [hTk_add w2]; simp
      rw [hT]
      exact hΦper (w1, w2)
    have h2 := Work.RPCore.Flow.fderiv_eq_of_periodic Φ hΦdiff hshift z
    have hz : z + ((0 : ℝ), Work.RPCore.Flow.tkShift) = (z.1, Tk 1 z.2) := by
      rw [hTk_add z.2]; ext <;> simp
    rw [hz] at h2
    exact h2
  -- `fderiv Φ` vanishes strictly outside the support slab of `H`.
  have hgsupp : ∀ z : ℝ × PS, R < |z.2.1.1| + |z.2.2.1| + |z.2.2.2| →
      fderiv ℝ Φ z = 0 := by
    intro z hz
    have hcont : Continuous fun y : ℝ × PS => |y.2.1.1| + |y.2.2.1| + |y.2.2.2| := by fun_prop
    have hopen : {y : ℝ × PS | R < |y.2.1.1| + |y.2.2.1| + |y.2.2.2|} ∈ 𝓝 z :=
      (isOpen_lt continuous_const hcont).mem_nhds hz
    have hev : Φ =ᶠ[𝓝 z] 0 := by
      filter_upwards [hopen] with y hy
      exact hΦsupp y hy
    rw [hev.fderiv_eq]
    simp
  -- `‖fderiv Φ‖` is bounded on the strip `{|t| ≤ T}`.
  obtain ⟨K0, hK00, hK0⟩ :=
    Work.RPCore.Flow.bounded_of_periodic_of_eq_on_slab (fderiv ℝ Φ)
      (hΦ.continuous_fderiv (by norm_num)) hgper hgsupp T
  -- Off the strip `fderiv Φ` vanishes, so the bound is global.
  have hfderiv_bound : ∀ z : ℝ × PS, ‖fderiv ℝ Φ z‖ ≤ K0 := by
    intro z
    by_cases ht : |z.1| ≤ T
    · exact hK0 z ht
    · have hev : Φ =ᶠ[𝓝 z] 0 := by
        have hcont : Continuous fun y : ℝ × PS => |y.1| := by fun_prop
        have hopen : {y : ℝ × PS | T < |y.1|} ∈ 𝓝 z :=
          (isOpen_lt continuous_const hcont).mem_nhds (not_le.mp ht)
        filter_upwards [hopen] with y hy
        show Φ y = 0
        show hamVF (fun x : PS => U (y.1, x)) y.2 = 0
        rw [hUfun y.1]
        have hHt : H y.1 = fun _ => (0 : ℝ) := funext (fun x => hT y.1 x (le_of_lt hy))
        rw [hHt]
        simp [hamVF]
      rw [hev.fderiv_eq]
      simp only [fderiv_zero, Pi.zero_apply, norm_zero]
      exact hK00
  let K : NNReal := ⟨K0, hK00⟩
  have hK : (K : ℝ) = K0 := rfl
  have hlip : LipschitzWith K Φ := by
    refine LipschitzWith.of_dist_le_mul (K := K) ?_
    intro x y
    have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := Φ)
      (fun z _ => hΦdiff z) (fun z _ => hfderiv_bound z) (Set.mem_univ y) (Set.mem_univ x)
    rw [hK]
    simpa only [dist_eq_norm] using h
  refine ⟨⟨K, ?_⟩, hbound⟩
  exact hΦeq ▸ hlip

end Work.RPA3
