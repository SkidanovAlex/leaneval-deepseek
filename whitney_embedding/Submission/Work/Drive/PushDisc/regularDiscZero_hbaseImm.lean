import Mathlib
import Submission.Work.Drive.PushDisc.regularDiscDefs
import Submission.Work.Drive.PushDisc.lensBump_fderiv

/-!
# `regularDiscZero_hbaseImm`

The base map `Δ₀ = regularDiscZero D A B g δ` of the lens construction of the lead's `L0` is an
*immersion along the directions in which the four lens bumps degenerate*.

At a point `p` of the closed lens `lens`, a direction `UW ∈ ℝ²` is called *bump-degenerate* when
`UW.1 * ∂ₓ (lensBump ρ k) p + UW.2 * ∂_y (lensBump ρ k) p = 0` for all four bumps `k`.  The claim
is that `Δ₀` has non-zero derivative at `p` in every such direction:
`UW.1 • ∂ₓΔ₀ p + UW.2 • ∂_yΔ₀ p ≠ 0` for `UW ≠ 0`.

This is exactly the hypothesis `hbaseImm` of `Work.Drive.PushDisc.exists_goodLensParam` (used there
through `badImm_subset_iUnion`): a direction in which the perturbation `Σ_k lensBump ρ k • v k` can
be killed must be a direction in which the base `Δ₀` is already immersive, so that the perturbed map
`lensMap Δ₀ ρ v` remains immersive there.

The mathematics is one observation.  With `F = lensBump ρ (0,0)` the four bumps are the four
multiples

    bump (0,0) = F,  bump (0,1) = (1+x) F,  bump (1,0) = (1+arch x - y) F,
    bump (1,1) = (1+x)(1+arch x - y) F,

where `F = lensChi ρ x * (1-x²) * y * (arch x - y)`.  Hence a bump-degenerate direction is `0`
whenever `F ≠ 0`, i.e. on the *open* lens.  On the boundary of the lens `F = 0` and:

* on the bottom edge `y = 0` the degenerate directions are the `x`-direction, where `Δ₀` restricts
  to `A` (so its derivative is `fderiv A x 1 ≠ 0` by `hAderiv`);
* on the top edge `y = arch x` they are the multiples of `(1, -2x)`, the tangent direction of the
  graph of `arch`, along which `Δ₀` restricts to `B` (so its derivative is `fderiv B x 1 ≠ 0` by
  `hBderiv`);
* at the two corners `(±1, 0)` the condition is empty and the two vectors `∂ₓΔ₀ = fderiv A (±1) 1`
  and `∂_yΔ₀ = g (±1)` are linearly independent by `hindNeg`/`hindPos`.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff ENNReal
open Set Metric MeasureTheory Topology Filter

noncomputable section

/-! ## Elementary facts about the model data -/

/-- The derivative of a map on `ℝ × ℝ` in a direction, expanded in the two coordinate directions. -/
private lemma fderiv_pair_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (p : ℝ × ℝ) (UW : ℝ × ℝ) :
    fderiv ℝ f p UW = UW.1 • fderiv ℝ f p (1, 0) + UW.2 • fderiv ℝ f p (0, 1) := by
  have hsplit : UW = UW.1 • ((1, 0) : ℝ × ℝ) + UW.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  conv_lhs => rw [hsplit]
  rw [map_add, map_smul, map_smul]

/-- `deriv arch x = -2x`. -/
private lemma deriv_arch (x : ℝ) : deriv arch x = -2 * x := by
  rw [show arch = fun z : ℝ => 1 - z ^ 2 from rfl]
  rw [deriv_const_sub]
  have h : deriv (fun z : ℝ => z ^ 2) x = 2 * x := by
    have hh : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x ^ (2 - 1)) x := by
      simpa using hasDerivAt_pow 2 x
    rw [hh.deriv]; ring
  rw [h]; ring

/-- `arch` is differentiable. -/
private lemma differentiableAt_arch (x : ℝ) : DifferentiableAt ℝ arch x := by
  show DifferentiableAt ℝ (fun z : ℝ => 1 - z ^ 2) x
  fun_prop

/-- `arch` has derivative `-2x`. -/
private lemma hasDerivAt_arch (x : ℝ) : HasDerivAt arch (-2 * x) x := by
  have h := (differentiableAt_arch x).hasDerivAt
  rwa [deriv_arch] at h

/-- `deriv (fun t => lensZeta 0 t u) y = u - 2y`. -/
private lemma deriv_lensZeta0_right (u y : ℝ) :
    deriv (fun t : ℝ => lensZeta 0 t u) y = u - 2 * y := by
  rw [show (fun t : ℝ => lensZeta 0 t u) = fun t : ℝ => t * (u - t) from by
    funext t; rw [lensZeta_zero_fun]]
  have h2 : HasDerivAt (fun t : ℝ => u - t) (-1) y := by
    rw [show (-1 : ℝ) = 0 - 1 by norm_num]
    exact (hasDerivAt_const y u).sub (hasDerivAt_id y)
  have h : HasDerivAt (fun t : ℝ => t * (u - t)) (1 * (u - y) + y * (-1)) y :=
    (hasDerivAt_id y).mul h2
  rw [h.deriv]; ring

/-- `deriv (fun t => lensZeta 0 y t) u = y`. -/
private lemma deriv_lensZeta0_left (y u : ℝ) :
    deriv (fun t : ℝ => lensZeta 0 y t) u = y := by
  rw [show (fun t : ℝ => lensZeta 0 y t) = fun t : ℝ => y * (t - y) from by
    funext t; rw [lensZeta_zero_fun]]
  rw [deriv_const_mul _ (by fun_prop)]
  rw [deriv_sub_const]
  rw [show deriv (fun t : ℝ => t) u = 1 from by
    simp [show (fun t : ℝ => t) = id from rfl, deriv_id]]
  ring

/-- The four bumps are four explicit multiples of `lensBump ρ (0,0)`. -/
private lemma lensBump_zero_one_eq (ρ : ℝ) :
    lensBump ρ (0,1) = fun q : ℝ × ℝ => (1 + q.1) * lensBump ρ (0,0) q := by
  funext q
  simp only [lensBump, lensZeta_zero_fun, lensAlpha_zero_fun, lensAlpha_one_fun]
  ring

/-- The four bumps are four explicit multiples of `lensBump ρ (0,0)`. -/
private lemma lensBump_one_zero_eq (ρ : ℝ) :
    lensBump ρ (1,0) = fun q : ℝ × ℝ => (1 + arch q.1 - q.2) * lensBump ρ (0,0) q := by
  funext q
  simp only [lensBump, lensZeta_zero_fun, lensZeta_one_fun, lensAlpha_zero_fun]
  ring

/-- `fderiv (fun q => 1 + q.1) p UW = UW.1`. -/
private lemma fderiv_one_add_fst (p UW : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => (1 : ℝ) + q.1) p UW = UW.1 := by
  rw [fderiv_const_add, fderiv_fst]; rfl

/-- `(1 + arch · - ·)` is differentiable. -/
private lemma differentiableAt_coef (p : ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => 1 + arch q.1 - q.2) p := by
  have h1 : DifferentiableAt ℝ (fun q : ℝ × ℝ => arch q.1) p := by
    show DifferentiableAt ℝ (fun q : ℝ × ℝ => 1 - q.1 ^ 2) p
    fun_prop
  exact ((h1.const_add 1).sub (by fun_prop))

/-- `fderiv (fun q => 1 + arch q.1 - q.2) (x,y) UW = -2x UW.1 - UW.2`. -/
private lemma fderiv_coef_pair (x y : ℝ) (UW : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => 1 + arch q.1 - q.2) (x, y) UW = -2 * x * UW.1 - UW.2 := by
  have hd1 : DifferentiableAt ℝ (fun q : ℝ × ℝ => 1 + arch q.1) (x,y) := by
    have h : DifferentiableAt ℝ (fun q : ℝ × ℝ => arch q.1) (x,y) := by
      show DifferentiableAt ℝ (fun q : ℝ × ℝ => 1 - q.1 ^ 2) (x,y)
      fun_prop
    exact h.const_add 1
  have hd2 : DifferentiableAt ℝ (fun q : ℝ × ℝ => q.2) (x,y) := by fun_prop
  have hsub := fderiv_fun_sub (𝕜 := ℝ) hd1 hd2
  have h1 : fderiv ℝ (fun q : ℝ × ℝ => 1 + arch q.1) (x,y)
      = fderiv ℝ (fun q : ℝ × ℝ => arch q.1) (x,y) := fderiv_const_add 1
  have h2 : fderiv ℝ (fun q : ℝ × ℝ => arch q.1) (x,y)
      = (fderiv ℝ arch x).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    rw [show (fun q : ℝ × ℝ => arch q.1) = arch ∘ Prod.fst from rfl]
    have hg : DifferentiableAt ℝ arch (Prod.fst (x, y)) := by
      show DifferentiableAt ℝ (fun z : ℝ => 1 - z ^ 2) (Prod.fst (x, y))
      fun_prop
    have hf : DifferentiableAt ℝ (Prod.fst : ℝ × ℝ → ℝ) (x, y) := differentiableAt_fst
    rw [fderiv_comp (x,y) (f := (Prod.fst : ℝ × ℝ → ℝ)) hg hf, fderiv_fst]
  have h3 : fderiv ℝ (fun q : ℝ × ℝ => q.2) (x,y) = ContinuousLinearMap.snd ℝ ℝ ℝ := fderiv_snd
  rw [hsub, h1, h2, h3]
  simp only [sub_apply, ContinuousLinearMap.comp_apply]
  rw [fderiv_eq_smul_deriv, deriv_arch]
  simp [smul_eq_mul]
  ring

/-- The `(1,0)`-partial derivative of `lensBump ρ (0,0)`. -/
private lemma fderiv_lensBump00_one_zero {ρ : ℝ} (hρ : 0 < ρ) (x y : ℝ) :
    fderiv ℝ (lensBump ρ (0,0)) (x,y) (1,0)
      = deriv (fun t : ℝ => lensChi ρ t * lensAlpha 0 t) x * (y * (arch x - y))
        + lensChi ρ x * (1 - x ^ 2) * (-2 * x) * y := by
  obtain ⟨h1, _⟩ := lensBump_fderiv hρ (0,0) (x,y)
  rw [h1, deriv_arch, deriv_lensZeta0_left, lensZeta_zero_fun, lensAlpha_zero_fun]

/-- The `(0,1)`-partial derivative of `lensBump ρ (0,0)`. -/
private lemma fderiv_lensBump00_zero_one {ρ : ℝ} (hρ : 0 < ρ) (x y : ℝ) :
    fderiv ℝ (lensBump ρ (0,0)) (x,y) (0,1)
      = lensChi ρ x * (1 - x ^ 2) * (arch x - 2 * y) := by
  obtain ⟨_, h2⟩ := lensBump_fderiv hρ (0,0) (x,y)
  rw [h2, deriv_lensZeta0_right, lensAlpha_zero_fun]

/-! ## The main theorem -/

theorem regularDiscZero_hbaseImm {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ)
    {A B g : ℝ → EuclideanSpace ℝ (Fin (2 * n))} {D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A) (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hDbot : ∀ x, D (x, 0) = A x) (hDtop : ∀ x, D (x, 1) = B x)
    (hgval : ∀ x, arch x • g x = B x - A x)
    (hAderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, fderiv ℝ A x 1 ≠ 0)
    (hBderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, fderiv ℝ B x 1 ≠ 0)
    (hindNeg : LinearIndependent ℝ ![fderiv ℝ A (-1) 1, g (-1)])
    (hindPos : LinearIndependent ℝ ![fderiv ℝ A 1 1, g 1]) :
    ∀ p ∈ lens, ∀ UW : ℝ × ℝ, UW ≠ 0 →
      (∀ k : Fin 2 × Fin 2,
        UW.1 * fderiv ℝ (lensBump ρ k) p (1, 0) + UW.2 * fderiv ℝ (lensBump ρ k) p (0, 1) = 0) →
      UW.1 • (fderiv ℝ (regularDiscZero D A B g δ) p) (1, 0)
        + UW.2 • (fderiv ℝ (regularDiscZero D A B g δ) p) (0, 1) ≠ 0 := by
  intro p hp UW hUW hprem
  obtain ⟨x, y⟩ := p
  simp only [lens, Set.mem_ofPred_eq] at hp
  obtain ⟨hxle, hy0, hya⟩ := hp
  set Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)) := regularDiscZero D A B g δ with hΔ₀
  have hΔsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀ := by
    rw [hΔ₀]; exact contDiff_regularDiscZero hD hA hB hg hδ
  have hΔdiff : ∀ q : ℝ × ℝ, DifferentiableAt ℝ Δ₀ q :=
    fun q => (hΔsm.contDiffAt (x := q)).differentiableAt (by simp)
  have hAdiff : ∀ q : ℝ, DifferentiableAt ℝ A q :=
    fun q => (hA.contDiffAt (x := q)).differentiableAt (by simp)
  have hBdiff : ∀ q : ℝ, DifferentiableAt ℝ B q :=
    fun q => (hB.contDiffAt (x := q)).differentiableAt (by simp)
  -- `Δ₀` restricts to `A` on the bottom edge and to `B` on the top edge
  have hbot_fderiv : ∀ t : ℝ, fderiv ℝ Δ₀ (t, 0) (1,0) = fderiv ℝ A t 1 := by
    intro t
    have hφ : HasDerivAt (fun s : ℝ => (s, (0:ℝ))) (1, 0) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t 0)
    have hcomp := (hΔdiff (t,0)).hasFDerivAt.comp_hasDerivAt t hφ
    have heq : (Δ₀ ∘ fun s : ℝ => (s, (0:ℝ))) = A := by
      funext s
      rw [Function.comp_apply, hΔ₀]
      exact regularDiscZero_bot hDbot s
    rw [heq] at hcomp
    exact hcomp.unique ((hAdiff t).hasFDerivAt.hasDerivAt)
  have htop_fderiv : ∀ t : ℝ, fderiv ℝ Δ₀ (t, arch t) (1, -2*t) = fderiv ℝ B t 1 := by
    intro t
    have hφ : HasDerivAt (fun s : ℝ => (s, arch s)) (1, -2*t) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_arch t)
    have hcomp := (hΔdiff (t, arch t)).hasFDerivAt.comp_hasDerivAt t hφ
    have heq : (Δ₀ ∘ fun s : ℝ => (s, arch s)) = B := by
      funext s
      rw [Function.comp_apply, hΔ₀]
      exact regularDiscZero_top hδ hgval hDtop s
    rw [heq] at hcomp
    exact hcomp.unique ((hBdiff t).hasFDerivAt.hasDerivAt)
  -- at the two corners, `Δ₀ (x,·)` is the chord `A x + · • g x`
  have hcorner_fderiv : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      fderiv ℝ Δ₀ (s, 0) (0,1) = g s := by
    intro s hs
    have hφ : HasDerivAt (fun t : ℝ => (s, t)) (0, 1) 0 :=
      (hasDerivAt_const 0 s).prodMk (hasDerivAt_id 0)
    have hcomp := (hΔdiff (s, 0)).hasFDerivAt.comp_hasDerivAt 0 hφ
    have hθ : lensTheta δ s = 0 := by
      rcases hs with rfl | rfl
      · exact lensTheta_eq_zero hδ (by norm_num; linarith [hδ])
      · exact lensTheta_eq_zero hδ (by norm_num; linarith [hδ])
    have heq : (Δ₀ ∘ fun t : ℝ => (s, t)) = fun t : ℝ => A s + t • g s := by
      funext t
      rw [Function.comp_apply, hΔ₀]
      simp only [regularDiscZero]
      rw [show discCorr D A B g δ (s, t) = 0 from by simp [discCorr, hθ]]
      simp
    rw [heq] at hcomp
    have hgd : HasDerivAt (fun t : ℝ => A s + t • g s) (g s) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • g s) ((1:ℝ) • g s) 0 :=
        (hasDerivAt_id 0).smul_const (g s)
      have h2 : HasDerivAt (fun t : ℝ => A s + t • g s) ((1:ℝ) • g s) 0 :=
        h1.const_add (A s)
      simpa using h2
    exact hcomp.unique hgd
  -- the premise, in directional form
  have hdir : ∀ k : Fin 2 × Fin 2, fderiv ℝ (lensBump ρ k) (x,y) UW = 0 := by
    intro k
    rw [fderiv_pair_apply (lensBump ρ k) (x,y) UW, smul_eq_mul, smul_eq_mul]
    exact hprem k
  rw [← fderiv_pair_apply Δ₀ (x,y) UW]
  intro hG0
  -- the two explicit partials of `F = lensBump ρ (0,0)`
  have hFXval : fderiv ℝ (lensBump ρ (0,0)) (x,y) (1,0)
      = deriv (fun t : ℝ => lensChi ρ t * lensAlpha 0 t) x * (y * (arch x - y))
        + lensChi ρ x * (1 - x ^ 2) * (-2 * x) * y := fderiv_lensBump00_one_zero hρ x y
  have hFYval : fderiv ℝ (lensBump ρ (0,0)) (x,y) (0,1)
      = lensChi ρ x * (1 - x ^ 2) * (arch x - 2 * y) := fderiv_lensBump00_zero_one hρ x y
  -- the relations coming from `bump (0,1) = (1+x) F` and `bump (1,0) = (1+arch x - y) F`
  have hrel01 : fderiv ℝ (lensBump ρ (0,1)) (x,y) UW
      = (1 + x) * fderiv ℝ (lensBump ρ (0,0)) (x,y) UW
        + lensBump ρ (0,0) (x,y) * UW.1 := by
    rw [lensBump_zero_one_eq,
      fderiv_fun_mul (𝕜 := ℝ) (by fun_prop)
        ((contDiff_lensBump ρ (0,0)).contDiffAt.differentiableAt (by simp))]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [fderiv_one_add_fst]
  have hrel10 : fderiv ℝ (lensBump ρ (1,0)) (x,y) UW
      = (1 + arch x - y) * fderiv ℝ (lensBump ρ (0,0)) (x,y) UW
        + lensBump ρ (0,0) (x,y) * (-2 * x * UW.1 - UW.2) := by
    rw [lensBump_one_zero_eq,
      fderiv_fun_mul (𝕜 := ℝ) (differentiableAt_coef (x,y))
        ((contDiff_lensBump ρ (0,0)).contDiffAt.differentiableAt (by simp))]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [fderiv_coef_pair]
  have hF1 : lensBump ρ (0,0) (x,y) * UW.1 = 0 := by
    have h := hrel01
    rw [hdir (0,1), hdir (0,0)] at h
    linarith
  have hF2 : lensBump ρ (0,0) (x,y) * (-2 * x * UW.1 - UW.2) = 0 := by
    have h := hrel10
    rw [hdir (1,0), hdir (0,0)] at h
    linarith
  have hFp : lensBump ρ (0,0) (x,y) = 0 := by
    by_contra hne
    have h1 : UW.1 = 0 := (mul_eq_zero.mp hF1).resolve_left hne
    have h2 : UW.2 = 0 := by
      have h := (mul_eq_zero.mp hF2).resolve_left hne
      rw [h1] at h
      simpa using h
    exact hUW (by rw [Prod.ext_iff]; simp [h1, h2])
  have hFp' : lensChi ρ x * (1 - x ^ 2) * (y * (arch x - y)) = 0 := by
    have h := hFp
    simp only [lensBump, lensZeta_zero_fun, lensAlpha_zero_fun] at h
    exact h
  have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_Icc]
    exact abs_le.mp hxle
  rcases eq_or_ne y 0 with hy | hy
  · -- bottom edge
    have h0 : fderiv ℝ (lensBump ρ (0,0)) (x,y) (1,0) = 0 := by
      rw [hFXval, hy]; ring
    by_cases hxlt : |x| < 1
    · -- interior of the bottom edge: the degenerate direction is the `x`-direction
      have hypos : 0 < arch x := arch_pos hxlt
      have hχ : lensChi ρ x ≠ 0 := ne_of_gt (lensChi_pos_of_abs_lt_one hρ hxlt)
      have hFYne : fderiv ℝ (lensBump ρ (0,0)) (x,y) (0,1) ≠ 0 := by
        rw [hFYval, hy]
        simp only [mul_zero, sub_zero]
        exact mul_ne_zero (mul_ne_zero hχ (ne_of_gt hypos)) (ne_of_gt hypos)
      have hUW2 : UW.2 = 0 := by
        have h := hdir (0,0)
        rw [fderiv_pair_apply (lensBump ρ (0,0)) (x,y) UW, smul_eq_mul, smul_eq_mul, h0] at h
        simp only [mul_zero, zero_add] at h
        exact (mul_eq_zero.mp h).resolve_right hFYne
      have hUW1 : UW.1 ≠ 0 := by
        intro h1; exact hUW (by rw [Prod.ext_iff]; simp [h1, hUW2])
      have hG10 : fderiv ℝ Δ₀ (x,y) (1,0) = fderiv ℝ A x 1 := by
        rw [show (x,y) = (x, (0:ℝ)) from by rw [Prod.ext_iff]; exact ⟨rfl, hy⟩]
        exact hbot_fderiv x
      have hAne : fderiv ℝ A x 1 ≠ 0 := hAderiv x hxIcc
      rw [fderiv_pair_apply Δ₀ (x,y) UW, hUW2, hG10] at hG0
      simp only [zero_smul, add_zero] at hG0
      rcases smul_eq_zero.mp hG0 with h | h
      · exact hUW1 h
      · exact hAne h
    · -- at the corners `(±1, 0)` the degenerate directions are all of `ℝ²`
      have hxabs : |x| = 1 := le_antisymm hxle (le_of_not_gt hxlt)
      have hxpm : x = 1 ∨ x = -1 := by
        have h2 : x ^ 2 = 1 := by rw [← sq_abs, hxabs]; norm_num
        exact sq_eq_one_iff.mp h2
      have hG10 : fderiv ℝ Δ₀ (x,y) (1,0) = fderiv ℝ A x 1 := by
        rw [show (x,y) = (x, (0:ℝ)) from by rw [Prod.ext_iff]; exact ⟨rfl, hy⟩]
        exact hbot_fderiv x
      have hG01 : fderiv ℝ Δ₀ (x,y) (0,1) = g x := by
        rw [show (x,y) = (x, (0:ℝ)) from by rw [Prod.ext_iff]; exact ⟨rfl, hy⟩]
        exact hcorner_fderiv x hxpm
      rw [fderiv_pair_apply Δ₀ (x,y) UW, hG10, hG01] at hG0
      rcases hxpm with rfl | rfl
      · rcases LinearIndependent.pair_iff.mp hindPos UW.1 UW.2 hG0 with ⟨h1, h2⟩
        exact hUW (by rw [Prod.ext_iff]; simp [h1, h2])
      · rcases LinearIndependent.pair_iff.mp hindNeg UW.1 UW.2 hG0 with ⟨h1, h2⟩
        exact hUW (by rw [Prod.ext_iff]; simp [h1, h2])
  · -- top edge: `y = arch x` and the degenerate directions are the multiples of `(1, -2x)`
    have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
    have harchpos : 0 < arch x := lt_of_lt_of_le hypos hya
    have hxlt : |x| < 1 := by
      have h2 : x ^ 2 < 1 := by
        have h3 : (0:ℝ) < 1 - x ^ 2 := by simpa [arch] using harchpos
        linarith
      rw [abs_lt]
      exact ⟨by nlinarith [h2], by nlinarith [h2]⟩
    have hyu : y = arch x := by
      have hχ : lensChi ρ x ≠ 0 := ne_of_gt (lensChi_pos_of_abs_lt_one hρ hxlt)
      have hb : (1 : ℝ) - x ^ 2 ≠ 0 := ne_of_gt harchpos
      rcases mul_eq_zero.mp hFp' with h | h
      · exact absurd h (mul_ne_zero hχ hb)
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hy
        · linarith
    have hbu : lensChi ρ x * (1 - x ^ 2) * arch x ≠ 0 :=
      mul_ne_zero (mul_ne_zero (ne_of_gt (lensChi_pos_of_abs_lt_one hρ hxlt)) (ne_of_gt harchpos))
        (ne_of_gt harchpos)
    have hUW2 : UW.2 = -2 * x * UW.1 := by
      have h := hdir (0,0)
      rw [fderiv_pair_apply (lensBump ρ (0,0)) (x,y) UW, smul_eq_mul, smul_eq_mul,
        hFXval, hFYval, hyu] at h
      have key : (lensChi ρ x * (1 - x ^ 2) * arch x) * (2 * x * UW.1 + UW.2) = 0 := by
        linear_combination -h
      rcases mul_eq_zero.mp key with hk | hk
      · exact absurd hk hbu
      · linarith
    have hUW1 : UW.1 ≠ 0 := by
      intro h1; exact hUW (by rw [Prod.ext_iff]; simp [h1, hUW2])
    have hUWform : UW = UW.1 • ((1, -2 * x) : ℝ × ℝ) := by
      rw [Prod.ext_iff]
      constructor
      · simp
      · show UW.2 = UW.1 * (-2 * x)
        rw [hUW2]; ring
    have htop : fderiv ℝ Δ₀ (x,y) (1, -2 * x) = fderiv ℝ B x 1 := by
      rw [show (x,y) = (x, arch x) from by rw [Prod.ext_iff]; exact ⟨rfl, hyu⟩]
      exact htop_fderiv x
    have hBne : fderiv ℝ B x 1 ≠ 0 := hBderiv x hxIcc
    rw [hUWform, map_smul, htop] at hG0
    rcases smul_eq_zero.mp hG0 with h | h
    · exact hUW1 h
    · exact hBne h

end

end Work.Drive.PushDisc
