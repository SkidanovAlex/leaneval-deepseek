import Mathlib
import Submission.Work.KMTAreas.A8Trilinear

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `Work.KMTAreas.A8.lam_family`

The analytic family of area A8: for a bilinear operator `T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ`
(merely bilinear, additive and homogeneous over finitely supported functions) and a family of
finitely supported test objects `psi x`, the trilinear form

`lam T psi u v h = ∑ₓ ⟨T u v (·) x, psi x⟩ h x`

(is `Work.KMTAreas.lam`) is specialized to the analytic families
`u = analyticFamily f (a₀) (a₁) z`, etc.  This file proves that the resulting function of `z` is
entire and bounded on the closed vertical strip `0 ≤ Re z ≤ 1`.

The proof is the standard "finite support + level-set expansion" argument:

* `lam_expansion` expands `lam T psi u v h`, for `u`, `v`, `h` supported in the finsets
  `sf`, `sg`, `sh`, into the finite triple sum over the "level sets" of the three functions:
  the `z`-dependence sits entirely in the elementary entire factors `phasePow (f y) (…)`;
  the remaining factor `pair (fun n => T δ_y δ_w n x) (psi x)` is a constant (a finite sum,
  hence a complex number).

* `differentiable_lam_decomp` and `bddAbove_lam_decomp` then read off entireness and the
  boundedness on the strip from the explicit finite expansion, using the pointwise bound
  `norm_phasePow_expFamily_le_of_re_mem` on the elementary factors.

* `lam_family` is the conjunction of the two, the form requested as the interface of area A8.
-/

namespace Work.KMTAreas.A8

open Work.Analysis.InverseTheory (FinSupp)

/-! ## Linear algebra of `pair` -/

/-- `pair` is additive over a finite pointwise `ℂ`-linear combination of sequences. -/
lemma pair_finset_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (a : ι → ℕ → ℂ)
    (l : ℕ →₀ ℂ) :
    pair (∑ i ∈ s, c i • a i) l = ∑ i ∈ s, c i * pair (a i) l := by
  classical
  induction s using Finset.induction with
  | empty => simp [pair]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, pair_add, pair_smul, ih]

/-- `pair` is additive over a finite double pointwise `ℂ`-linear combination of sequences. -/
lemma pair_sum_sum_smul {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ι → κ → ℂ)
    (a : ι → κ → ℕ → ℂ) (l : ℕ →₀ ℂ) :
    pair (∑ i ∈ s, ∑ j ∈ t, c i j • a i j) l
      = ∑ i ∈ s, ∑ j ∈ t, c i j * pair (a i j) l := by
  classical
  induction s using Finset.induction with
  | empty => simp [pair]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, pair_add, pair_finset_sum_smul, ih]

/-! ## The expansion of `lam` over finite supports -/

variable {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ}

/-- **The expansion of `lam` over the finite supports of its arguments.**  If `u`, `v`, `w`
vanish off the finsets `sf`, `sg`, `sh`, then `lam T psi u v w` is the finite triple sum over
those supports of `(u y * v z) * ⟨T δ_y δ_z (·) x, psi x⟩ * w x`.  The bilinearity of `T`
(`T_eq_sum_delta`) and the linearity of `pair` turn the (a priori infinite) series of `lam`
into this finite sum. -/
lemma lam_expansion
    (hlin₁ : ∀ f f' g (c : ℂ), FinSupp f → FinSupp f' → FinSupp g →
      T (f + c • f') g = T f g + c • T f' g)
    (hlin₂ : ∀ f g g' (c : ℂ), FinSupp f → FinSupp g → FinSupp g' →
      T f (g + c • g') = T f g + c • T f g')
    (psi : ℤ → (ℕ →₀ ℂ)) (u v w : ℤ → ℂ) (sf sg sh : Finset ℤ)
    (hu : ∀ x ∉ sf, u x = 0) (hv : ∀ x ∉ sg, v x = 0) (hw : ∀ x ∉ sh, w x = 0) :
    lam T psi u v w = ∑ x ∈ sh, ∑ y ∈ sf, ∑ z ∈ sg,
      (u y * v z) * pair (fun n => T (delta y) (delta z) n x) (psi x) * w x := by
  classical
  have hu' : FinSupp u := ⟨sf, hu⟩
  have hv' : FinSupp v := ⟨sg, hv⟩
  have hw' : FinSupp w := ⟨sh, hw⟩
  rw [lam_of_finSupp hu' hv' hw']
  rw [tsum_eq_sum (s := sh) (fun x hx => by rw [hw x hx, mul_zero])]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hpair : pair (fun n => T u v n x) (psi x)
      = ∑ y ∈ sf, ∑ z ∈ sg, (u y * v z) *
        pair (fun n => T (delta y) (delta z) n x) (psi x) := by
    have hT := T_eq_sum_delta hlin₁ hlin₂ u v sf sg hu hv
    have hTx : (fun n => T u v n x)
        = ∑ y ∈ sf, ∑ z ∈ sg,
            (u y * v z) • (fun n => T (delta y) (delta z) n x) := by
      funext n
      have h1 := congrFun (congrFun hT n) x
      rw [h1]
      simp only [Finset.sum_apply, Pi.smul_apply]
    rw [hTx, pair_sum_sum_smul]
  rw [hpair]
  simp only [Finset.sum_mul]

/-! ## The analytic families -/

/-- The analytic family of a function vanishing at `x` vanishes at `x`. -/
lemma analyticFamily_eq_zero_of {f : ℤ → ℂ} {x : ℤ} (hx : f x = 0) (t₀ t₁ z : ℂ) :
    Work.Analysis.Interpolation.analyticFamily f t₀ t₁ z x = 0 := by
  simp only [Work.Analysis.Interpolation.analyticFamily]
  rw [hx, Work.Analysis.Interpolation.phasePow_zero_left]

/-- The finitely-supported analytic family of a finitely supported function is finitely
supported. -/
lemma finSupp_analyticFamily {f : ℤ → ℂ} (hf : FinSupp f) (t₀ t₁ z : ℂ) :
    FinSupp (Work.Analysis.Interpolation.analyticFamily f t₀ t₁ z) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, fun x hx => analyticFamily_eq_zero_of (hs x hx) t₀ t₁ z⟩

/-! ## The two analytic inputs, from an explicit decomposition -/

/-- If `z ↦ lam T psi (F z) (G z) (H z)` admits the explicit finite decomposition into the
elementary entire factors `phasePow`, then it is entire. -/
lemma differentiable_lam_decomp {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ} (psi : ℤ → (ℕ →₀ ℂ))
    (f g h : ℤ → ℂ) (sf sg sh : Finset ℤ) (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ)
    (hdecomp : ∀ z : ℂ, lam T psi
        (Work.Analysis.Interpolation.analyticFamily f (a₀ : ℂ) (a₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily g (b₀ : ℂ) (b₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily h (c₀ : ℂ) (c₁ : ℂ) z)
      = ∑ x ∈ sh, ∑ y ∈ sf, ∑ w ∈ sg,
          (Work.Analysis.Interpolation.phasePow (f y)
              (Work.Analysis.Interpolation.expFamily (a₀ : ℂ) (a₁ : ℂ) z)
            * Work.Analysis.Interpolation.phasePow (g w)
              (Work.Analysis.Interpolation.expFamily (b₀ : ℂ) (b₁ : ℂ) z))
          * (pair (fun n => T (delta y) (delta w) n x) (psi x))
          * Work.Analysis.Interpolation.phasePow (h x)
              (Work.Analysis.Interpolation.expFamily (c₀ : ℂ) (c₁ : ℂ) z)) :
    Differentiable ℂ (fun z : ℂ => lam T psi
        (Work.Analysis.Interpolation.analyticFamily f (a₀ : ℂ) (a₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily g (b₀ : ℂ) (b₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily h (c₀ : ℂ) (c₁ : ℂ) z)) := by
  have hfun : (fun z : ℂ => lam T psi
        (Work.Analysis.Interpolation.analyticFamily f (a₀ : ℂ) (a₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily g (b₀ : ℂ) (b₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily h (c₀ : ℂ) (c₁ : ℂ) z))
      = fun z : ℂ => ∑ x ∈ sh, ∑ y ∈ sf, ∑ w ∈ sg,
          (Work.Analysis.Interpolation.phasePow (f y)
              (Work.Analysis.Interpolation.expFamily (a₀ : ℂ) (a₁ : ℂ) z)
            * Work.Analysis.Interpolation.phasePow (g w)
              (Work.Analysis.Interpolation.expFamily (b₀ : ℂ) (b₁ : ℂ) z))
          * (pair (fun n => T (delta y) (delta w) n x) (psi x))
          * Work.Analysis.Interpolation.phasePow (h x)
              (Work.Analysis.Interpolation.expFamily (c₀ : ℂ) (c₁ : ℂ) z) := by
    funext z
    exact hdecomp z
  rw [hfun]
  refine Work.Analysis.Interpolation.differentiable_sum_sum_sum sh sf sg _ ?_
  intro x _ y _ w _
  exact (((Work.Analysis.Interpolation.differentiable_phasePow_expFamily (f y) (a₀ : ℂ)
        (a₁ : ℂ)).mul
      (Work.Analysis.Interpolation.differentiable_phasePow_expFamily (g w) (b₀ : ℂ)
        (b₁ : ℂ))).mul
      (differentiable_const _)).mul
    (Work.Analysis.Interpolation.differentiable_phasePow_expFamily (h x) (c₀ : ℂ) (c₁ : ℂ))

/-- If `z ↦ lam T psi (F z) (G z) (H z)` admits the explicit finite decomposition into the
elementary factors `phasePow`, then its modulus is bounded on the closed vertical strip
`0 ≤ Re z ≤ 1`: the explicit bound is the finite triple sum of the products of the pointwise
bounds `max 1 (max (‖·‖^a₀) (‖·‖^a₁))` of the elementary factors with the fixed constants
`‖⟨T δ_y δ_w (·) x, psi x⟩‖`. -/
lemma bddAbove_lam_decomp {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ} (psi : ℤ → (ℕ →₀ ℂ))
    (f g h : ℤ → ℂ) (sf sg sh : Finset ℤ) (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ)
    (hdecomp : ∀ z : ℂ, lam T psi
        (Work.Analysis.Interpolation.analyticFamily f (a₀ : ℂ) (a₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily g (b₀ : ℂ) (b₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily h (c₀ : ℂ) (c₁ : ℂ) z)
      = ∑ x ∈ sh, ∑ y ∈ sf, ∑ w ∈ sg,
          (Work.Analysis.Interpolation.phasePow (f y)
              (Work.Analysis.Interpolation.expFamily (a₀ : ℂ) (a₁ : ℂ) z)
            * Work.Analysis.Interpolation.phasePow (g w)
              (Work.Analysis.Interpolation.expFamily (b₀ : ℂ) (b₁ : ℂ) z))
          * (pair (fun n => T (delta y) (delta w) n x) (psi x))
          * Work.Analysis.Interpolation.phasePow (h x)
              (Work.Analysis.Interpolation.expFamily (c₀ : ℂ) (c₁ : ℂ) z)) :
    BddAbove ((norm ∘ fun z : ℂ => lam T psi
        (Work.Analysis.Interpolation.analyticFamily f (a₀ : ℂ) (a₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily g (b₀ : ℂ) (b₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily h (c₀ : ℂ) (c₁ : ℂ) z))
      '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  have hfun : (fun z : ℂ => lam T psi
        (Work.Analysis.Interpolation.analyticFamily f (a₀ : ℂ) (a₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily g (b₀ : ℂ) (b₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily h (c₀ : ℂ) (c₁ : ℂ) z))
      = fun z : ℂ => ∑ x ∈ sh, ∑ y ∈ sf, ∑ w ∈ sg,
          (Work.Analysis.Interpolation.phasePow (f y)
              (Work.Analysis.Interpolation.expFamily (a₀ : ℂ) (a₁ : ℂ) z)
            * Work.Analysis.Interpolation.phasePow (g w)
              (Work.Analysis.Interpolation.expFamily (b₀ : ℂ) (b₁ : ℂ) z))
          * (pair (fun n => T (delta y) (delta w) n x) (psi x))
          * Work.Analysis.Interpolation.phasePow (h x)
              (Work.Analysis.Interpolation.expFamily (c₀ : ℂ) (c₁ : ℂ) z) := by
    funext z
    exact hdecomp z
  rw [hfun]
  refine Work.Analysis.Interpolation.bddAbove_image_norm_of_le
    (M := ∑ x ∈ sh, ∑ y ∈ sf, ∑ w ∈ sg,
      ((max 1 (max (‖f y‖ ^ a₀) (‖f y‖ ^ a₁)))
          * (max 1 (max (‖g w‖ ^ b₀) (‖g w‖ ^ b₁))))
        * ‖pair (fun n => T (delta y) (delta w) n x) (psi x)‖
        * (max 1 (max (‖h x‖ ^ c₀) (‖h x‖ ^ c₁)))) ?_
  intro z hz
  have hzre : z.re ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
  have hterm : ∀ x ∈ sh, ∀ y ∈ sf, ∀ w ∈ sg,
      ‖(Work.Analysis.Interpolation.phasePow (f y)
            (Work.Analysis.Interpolation.expFamily (a₀ : ℂ) (a₁ : ℂ) z)
          * Work.Analysis.Interpolation.phasePow (g w)
            (Work.Analysis.Interpolation.expFamily (b₀ : ℂ) (b₁ : ℂ) z))
        * (pair (fun n => T (delta y) (delta w) n x) (psi x))
        * Work.Analysis.Interpolation.phasePow (h x)
            (Work.Analysis.Interpolation.expFamily (c₀ : ℂ) (c₁ : ℂ) z)‖
      ≤ ((max 1 (max (‖f y‖ ^ a₀) (‖f y‖ ^ a₁)))
          * (max 1 (max (‖g w‖ ^ b₀) (‖g w‖ ^ b₁))))
        * ‖pair (fun n => T (delta y) (delta w) n x) (psi x)‖
        * (max 1 (max (‖h x‖ ^ c₀) (‖h x‖ ^ c₁))) := by
    intro x _ y _ w _
    have hbf : 0 ≤ max 1 (max (‖f y‖ ^ a₀) (‖f y‖ ^ a₁)) :=
      le_trans zero_le_one (le_max_left 1 _)
    have hbg : 0 ≤ max 1 (max (‖g w‖ ^ b₀) (‖g w‖ ^ b₁)) :=
      le_trans zero_le_one (le_max_left 1 _)
    simp only [norm_mul]
    exact mul_le_mul
      (mul_le_mul
        (mul_le_mul
          (Work.Analysis.Interpolation.norm_phasePow_expFamily_le_of_re_mem (c := f y) hzre)
          (Work.Analysis.Interpolation.norm_phasePow_expFamily_le_of_re_mem (c := g w) hzre)
          (norm_nonneg _) hbf)
        le_rfl (norm_nonneg _) (mul_nonneg hbf hbg))
      (Work.Analysis.Interpolation.norm_phasePow_expFamily_le_of_re_mem (c := h x) hzre)
      (norm_nonneg _) (mul_nonneg (mul_nonneg hbf hbg) (norm_nonneg _))
  exact Work.Analysis.Interpolation.norm_triple_sum_le sh sf sg _ _ hterm

/-! ## The target -/

theorem lam_family {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ}
    (hlin₁ : ∀ f f' g (c : ℂ), Work.Analysis.InverseTheory.FinSupp f →
      Work.Analysis.InverseTheory.FinSupp f' → Work.Analysis.InverseTheory.FinSupp g →
      T (f + c • f') g = T f g + c • T f' g)
    (hlin₂ : ∀ f g g' (c : ℂ), Work.Analysis.InverseTheory.FinSupp f →
      Work.Analysis.InverseTheory.FinSupp g → Work.Analysis.InverseTheory.FinSupp g' →
      T f (g + c • g') = T f g + c • T f g')
    (psi : ℤ → (ℕ →₀ ℂ)) (f g h : ℤ → ℂ)
    (hf : Work.Analysis.InverseTheory.FinSupp f) (hg : Work.Analysis.InverseTheory.FinSupp g)
    (hh : Work.Analysis.InverseTheory.FinSupp h) (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ) :
    Differentiable ℂ (fun z : ℂ => Work.KMTAreas.lam T psi
        (Work.Analysis.Interpolation.analyticFamily f (a₀ : ℂ) (a₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily g (b₀ : ℂ) (b₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily h (c₀ : ℂ) (c₁ : ℂ) z)) ∧
    BddAbove ((norm ∘ fun z : ℂ => Work.KMTAreas.lam T psi
        (Work.Analysis.Interpolation.analyticFamily f (a₀ : ℂ) (a₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily g (b₀ : ℂ) (b₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily h (c₀ : ℂ) (c₁ : ℂ) z))
      '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  obtain ⟨sf, hsf⟩ := hf
  obtain ⟨sg, hsg⟩ := hg
  obtain ⟨sh, hsh⟩ := hh
  have hdecomp : ∀ z : ℂ, Work.KMTAreas.lam T psi
        (Work.Analysis.Interpolation.analyticFamily f (a₀ : ℂ) (a₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily g (b₀ : ℂ) (b₁ : ℂ) z)
        (Work.Analysis.Interpolation.analyticFamily h (c₀ : ℂ) (c₁ : ℂ) z)
      = ∑ x ∈ sh, ∑ y ∈ sf, ∑ w ∈ sg,
          (Work.Analysis.Interpolation.phasePow (f y)
              (Work.Analysis.Interpolation.expFamily (a₀ : ℂ) (a₁ : ℂ) z)
            * Work.Analysis.Interpolation.phasePow (g w)
              (Work.Analysis.Interpolation.expFamily (b₀ : ℂ) (b₁ : ℂ) z))
          * (Work.KMTAreas.pair (fun n => T (Work.KMTAreas.delta y) (Work.KMTAreas.delta w) n x)
              (psi x))
          * Work.Analysis.Interpolation.phasePow (h x)
              (Work.Analysis.Interpolation.expFamily (c₀ : ℂ) (c₁ : ℂ) z) := by
    intro z
    rw [lam_expansion hlin₁ hlin₂ psi
      (Work.Analysis.Interpolation.analyticFamily f (a₀ : ℂ) (a₁ : ℂ) z)
      (Work.Analysis.Interpolation.analyticFamily g (b₀ : ℂ) (b₁ : ℂ) z)
      (Work.Analysis.Interpolation.analyticFamily h (c₀ : ℂ) (c₁ : ℂ) z) sf sg sh
      (fun x hx => analyticFamily_eq_zero_of (hsf x hx) _ _ _)
      (fun x hx => analyticFamily_eq_zero_of (hsg x hx) _ _ _)
      (fun x hx => analyticFamily_eq_zero_of (hsh x hx) _ _ _)]
    simp only [Work.Analysis.Interpolation.analyticFamily]
  exact ⟨differentiable_lam_decomp psi f g h sf sg sh a₀ a₁ b₀ b₁ c₀ c₁ hdecomp,
    bddAbove_lam_decomp psi f g h sf sg sh a₀ a₁ b₀ b₁ c₀ c₁ hdecomp⟩

end Work.KMTAreas.A8
