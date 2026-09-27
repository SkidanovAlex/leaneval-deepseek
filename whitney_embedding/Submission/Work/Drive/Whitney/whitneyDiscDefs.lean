import Mathlib
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Projection.Defs

/-!
# The smooth Whitney disc of a bigon: the construction data

This file sets up the explicit data used by `Work.Drive.Whitney.whitneyDiscSmooth`: the
straight-line interpolation `baseDisc` of the two arcs of the bigon, the four bumps `discBump`
used for the generic translation, and the "bad sets" of translation parameters.

The final disc is `discMap v = baseDisc + ∑ k, (discBump k) • (v k)` for a translation parameter
`v` chosen outside the bad sets (avoidance of `f '' M`, injectivity, and the transversality
conditions at `u = 0` and `u = 1`).
-/

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Set Metric
open scoped ENNReal Topology

noncomputable section

/-- The affine reparametrisation of the unit interval: `sigR x = (x+1)/2`. -/
def sigR (x : ℝ) : ℝ := (x + 1) / 2

/-- The first `u`-bump: `u (1-u)`. -/
def uBump (u : ℝ) : ℝ := u * (1 - u)

/-- The second `u`-bump: `u (1-u)^2`. -/
def uBump2 (u : ℝ) : ℝ := u * (1 - u) ^ 2

/-- The `u`-bumps indexed by `Fin 2`. -/
def uBeta (i : Fin 2) (u : ℝ) : ℝ := if i = 0 then uBump u else uBump2 u

lemma uBeta_apply (i : Fin 2) (u : ℝ) :
    uBeta i u = if i = 0 then uBump u else uBump2 u := rfl

@[simp] lemma uBeta_zero_fun : uBeta 0 = uBump := by
  funext u; rw [uBeta_apply, if_pos rfl]

@[simp] lemma uBeta_one_fun : uBeta 1 = uBump2 := by
  funext u; rw [uBeta_apply, if_neg (by decide : (1 : Fin 2) ≠ 0)]

lemma uBeta_ne_zero_fun {i : Fin 2} (h : i ≠ 0) : uBeta i = uBump2 := by
  funext u; rw [uBeta_apply, if_neg h]

/-- The angle used for the `x`-bumps. -/
def xAngle (x : ℝ) : ℝ := Real.pi / 4 * (1 + x)

/-- The `x`-bumps indexed by `Fin 2`: a nonvanishing radially injective pair on `(-1,1)`
vanishing at `±1`. -/
def xAlpha (j : Fin 2) (x : ℝ) : ℝ :=
  (1 - x ^ 2) * (if j = 0 then Real.cos (xAngle x) else Real.sin (xAngle x))

lemma xAlpha_apply (j : Fin 2) (x : ℝ) :
    xAlpha j x = (1 - x ^ 2) * (if j = 0 then Real.cos (xAngle x) else Real.sin (xAngle x)) :=
  rfl

@[simp] lemma xAlpha_zero_fun : xAlpha 0 = fun x => (1 - x ^ 2) * Real.cos (xAngle x) := by
  funext x; rw [xAlpha_apply, if_pos rfl]

@[simp] lemma xAlpha_one_fun : xAlpha 1 = fun x => (1 - x ^ 2) * Real.sin (xAngle x) := by
  funext x; rw [xAlpha_apply, if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- The four bumps used for the generic translation. -/
def discBump (k : Fin 2 × Fin 2) (p : ℝ × ℝ) : ℝ := uBeta k.1 p.2 * xAlpha k.2 p.1

lemma contDiff_uBeta (i : Fin 2) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uBeta i) := by
  by_cases h : i = 0
  · rw [h, uBeta_zero_fun]; unfold uBump; fun_prop
  · rw [uBeta_ne_zero_fun h]; unfold uBump2; fun_prop

lemma contDiff_xAlpha (j : Fin 2) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xAlpha j) := by
  by_cases h : j = 0
  · rw [h, xAlpha_zero_fun]; unfold xAngle; fun_prop
  · have hj : j = 1 := by omega
    rw [hj, xAlpha_one_fun]; unfold xAngle; fun_prop

lemma contDiff_discBump (k : Fin 2 × Fin 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (discBump k) := by
  rw [show discBump k = fun p : ℝ × ℝ => uBeta k.1 p.2 * xAlpha k.2 p.1 from rfl]
  exact ((contDiff_uBeta k.1).comp contDiff_snd).mul ((contDiff_xAlpha k.2).comp contDiff_fst)

lemma uBump_zero : uBump 0 = 0 := by simp [uBump]
lemma uBump_one : uBump 1 = 0 := by simp [uBump]
lemma uBump2_zero : uBump2 0 = 0 := by simp [uBump2]
lemma uBump2_one : uBump2 1 = 0 := by simp [uBump2]

lemma uBeta_eq_zero (i : Fin 2) : uBeta i 0 = 0 := by
  by_cases h : i = 0
  · rw [h, uBeta_zero_fun]; exact uBump_zero
  · rw [uBeta_ne_zero_fun h]; exact uBump2_zero

lemma uBeta_eq_one (i : Fin 2) : uBeta i 1 = 0 := by
  by_cases h : i = 0
  · rw [h, uBeta_zero_fun]; exact uBump_one
  · rw [uBeta_ne_zero_fun h]; exact uBump2_one

lemma uBeta_pos {i : Fin 2} {u : ℝ} (h0 : 0 < u) (h1 : u < 1) : 0 < uBeta i u := by
  by_cases h : i = 0
  · rw [h, uBeta_zero_fun]; simp only [uBump]; nlinarith
  · rw [uBeta_ne_zero_fun h]; simp only [uBump2]
    have : 0 < 1 - u := by linarith
    positivity

lemma uBeta_pair_inj {u v : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (h : uBeta 0 u = uBeta 0 v) (h' : uBeta 1 u = uBeta 1 v) : u = v := by
  simp only [uBeta_zero_fun, uBeta_one_fun, uBump, uBump2] at h h'
  nlinarith [h, h', mul_pos hu0 (by linarith : 0 < 1 - u),
    mul_pos hv0 (by linarith : 0 < 1 - v)]

lemma xAngle_mem {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    xAngle x ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hp := Real.pi_pos
  constructor <;> simp only [xAngle] <;> nlinarith [hx.1, hx.2]

/-- The `x`-bumps do not both vanish in the open interval. -/
lemma xAlpha_ne_zero {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    xAlpha 0 x ≠ 0 ∨ xAlpha 1 x ≠ 0 := by
  have h1x : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hθ := xAngle_mem hx
  left
  rw [xAlpha_zero_fun]
  exact mul_ne_zero (ne_of_gt h1x)
    (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩))

/-- Radial separation of the `x`-bumps: two interior points of `(-1,1)` whose values are
positively proportional are equal. -/
lemma xAlpha_radial {x y : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ∈ Set.Ioo (-1 : ℝ) 1)
    {c : ℝ} (hc : 0 < c) (h0 : xAlpha 0 y = c * xAlpha 0 x)
    (h1 : xAlpha 1 y = c * xAlpha 1 x) : x = y := by
  have h1x : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have h1y : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have hθx := xAngle_mem hx
  have hθy := xAngle_mem hy
  have hcx : Real.cos (xAngle x) ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθx.1], hθx.2⟩)
  have hcy : Real.cos (xAngle y) ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθy.1], hθy.2⟩)
  simp only [xAlpha_zero_fun, xAlpha_one_fun] at h0 h1
  have e1 : (1 - y ^ 2) * (Real.sin (xAngle y) * Real.cos (xAngle x))
      = (c * (1 - x ^ 2)) * (Real.sin (xAngle x) * Real.cos (xAngle x)) := by
    rw [show (1 - y ^ 2) * (Real.sin (xAngle y) * Real.cos (xAngle x))
        = ((1 - y ^ 2) * Real.sin (xAngle y)) * Real.cos (xAngle x) by ring, h1]
    ring
  have e2 : (1 - y ^ 2) * (Real.sin (xAngle x) * Real.cos (xAngle y))
      = (c * (1 - x ^ 2)) * (Real.sin (xAngle x) * Real.cos (xAngle x)) := by
    rw [show (1 - y ^ 2) * (Real.sin (xAngle x) * Real.cos (xAngle y))
        = Real.sin (xAngle x) * ((1 - y ^ 2) * Real.cos (xAngle y)) by ring, h0]
    ring
  have hsin : Real.sin (xAngle y) * Real.cos (xAngle x)
      = Real.sin (xAngle x) * Real.cos (xAngle y) := by
    have h3 := e1.trans e2.symm
    exact mul_left_cancel₀ (ne_of_gt h1y) h3
  have htan : Real.tan (xAngle y) = Real.tan (xAngle x) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, div_eq_div_iff hcy hcx]
    linarith [hsin]
  have hθ : xAngle y = xAngle x :=
    Real.tan_inj_of_lt_of_lt_pi_div_two (by linarith [hθy.1, Real.pi_pos])
      (by linarith [hθy.2]) (by linarith [hθx.1, Real.pi_pos]) (by linarith [hθx.2]) htan
  simp only [xAngle] at hθ
  have hp : (Real.pi / 4 : ℝ) ≠ 0 := by positivity
  have h1 : (1 : ℝ) + y = 1 + x := mul_left_cancel₀ hp hθ
  linarith

/-- **The four bumps separate points of the open square.** -/
lemma discBump_sep {p q : ℝ × ℝ} (hp : p ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)
    (hq : q ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)
    (h : ∀ k : Fin 2 × Fin 2, discBump k p = discBump k q) : p = q := by
  have hp1 : p.1 ∈ Set.Ioo (-1 : ℝ) 1 := hp.1
  have hp2 : p.2 ∈ Set.Ioo (0 : ℝ) 1 := hp.2
  have hq2 : q.2 ∈ Set.Ioo (0 : ℝ) 1 := hq.2
  by_cases hx : p.1 = q.1
  · obtain ⟨j, hj⟩ : ∃ j : Fin 2, xAlpha j p.1 ≠ 0 := by
      rcases xAlpha_ne_zero hp1 with h' | h'
      · exact ⟨0, h'⟩
      · exact ⟨1, h'⟩
    have key : ∀ i : Fin 2, uBeta i p.2 = uBeta i q.2 := by
      intro i
      have hh := h (i, j)
      simp only [discBump] at hh
      rw [show xAlpha j q.1 = xAlpha j p.1 from by rw [← hx]] at hh
      exact mul_right_cancel₀ hj hh
    have hu : p.2 = q.2 := uBeta_pair_inj hp2.1 hp2.2 hq2.1 hq2.2 (key 0) (key 1)
    exact Prod.ext hx hu
  · exfalso
    have ha := uBeta_pos hp2.1 hp2.2 (i := 0)
    have hb := uBeta_pos hq2.1 hq2.2 (i := 0)
    have hc : 0 < uBeta 0 p.2 / uBeta 0 q.2 := div_pos ha hb
    have h0 := h (0, 0)
    have h1 := h (0, 1)
    simp only [discBump] at h0 h1
    have e0 : xAlpha 0 q.1 = (uBeta 0 p.2 / uBeta 0 q.2) * xAlpha 0 p.1 := by
      field_simp
      linarith [h0]
    have e1 : xAlpha 1 q.1 = (uBeta 0 p.2 / uBeta 0 q.2) * xAlpha 1 p.1 := by
      field_simp
      linarith [h1]
    exact hx (xAlpha_radial hp1 hq.1 hc e0 e1)

/-! ## The disc and the bad sets -/

/-- The straight-line interpolation of the two arcs of the bigon. -/
def baseDisc {n : ℕ} {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin (2 * n)) :=
  (1 - p.2) • f (γ₁ (sigR p.1)) + p.2 • f (γ₂ (sigR p.1))

/-- The generic translation of the interpolation by the four bumps. -/
def discPert {n : ℕ} (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (p : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin (2 * n)) :=
  ∑ k : Fin 2 × Fin 2, (discBump k p) • v k

/-- The candidate Whitney disc. -/
def discMap {n : ℕ} {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (p : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin (2 * n)) :=
  baseDisc f γ₁ γ₂ p + discPert v p

/-- The open square on which the disc must be injective and off `f '' M`. -/
def discSq : Set (ℝ × ℝ) := Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1

lemma sigR_mem_iff {x : ℝ} : sigR x ∈ Set.Icc (0 : ℝ) 1 ↔ x ∈ Set.Icc (-1 : ℝ) 1 := by
  simp only [sigR, Set.mem_Icc]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma sigR_neg_one : sigR (-1) = 0 := by simp [sigR]
lemma sigR_one : sigR 1 = 1 := by simp [sigR]

/-- `baseDisc` on the lower edge is the first arc. -/
lemma baseDisc_bot {n : ℕ} {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (γ₁ γ₂ : ℝ → M) (x : ℝ) : baseDisc f γ₁ γ₂ (x, 0) = f (γ₁ (sigR x)) := by
  simp [baseDisc]

/-- `baseDisc` on the upper edge is the second arc. -/
lemma baseDisc_top {n : ℕ} {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (γ₁ γ₂ : ℝ → M) (x : ℝ) : baseDisc f γ₁ γ₂ (x, 1) = f (γ₂ (sigR x)) := by
  simp [baseDisc]

lemma discBump_eq_zero_bot (k : Fin 2 × Fin 2) (x : ℝ) : discBump k (x, 0) = 0 := by
  obtain ⟨i, j⟩ := k
  simp only [discBump, uBeta, uBump, uBump2]
  by_cases hi : i = 0
  · rw [if_pos hi]; ring
  · rw [if_neg hi]; ring

lemma discBump_eq_zero_top (k : Fin 2 × Fin 2) (x : ℝ) : discBump k (x, 1) = 0 := by
  obtain ⟨i, j⟩ := k
  simp only [discBump, uBeta, uBump, uBump2]
  by_cases hi : i = 0
  · rw [if_pos hi]; ring
  · rw [if_neg hi]; ring

lemma discBump_eq_zero_left (k : Fin 2 × Fin 2) (u : ℝ) : discBump k ((-1 : ℝ), u) = 0 := by
  obtain ⟨i, j⟩ := k
  simp only [discBump, xAlpha]
  by_cases hj : j = 0
  · rw [if_pos hj]; ring
  · rw [if_neg hj]; ring

lemma discBump_eq_zero_right (k : Fin 2 × Fin 2) (u : ℝ) : discBump k ((1 : ℝ), u) = 0 := by
  obtain ⟨i, j⟩ := k
  simp only [discBump, xAlpha]
  by_cases hj : j = 0
  · rw [if_pos hj]; ring
  · rw [if_neg hj]; ring

lemma discPert_zero_u {n : ℕ} (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (x : ℝ) :
    discPert v (x, 0) = 0 := by
  simp only [discPert]
  exact Finset.sum_eq_zero fun k _ => by rw [discBump_eq_zero_bot, zero_smul]

lemma discPert_one_u {n : ℕ} (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (x : ℝ) :
    discPert v (x, 1) = 0 := by
  simp only [discPert]
  exact Finset.sum_eq_zero fun k _ => by rw [discBump_eq_zero_top, zero_smul]

lemma discPert_left {n : ℕ} (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (u : ℝ) :
    discPert v ((-1 : ℝ), u) = 0 := by
  simp only [discPert]
  exact Finset.sum_eq_zero fun k _ => by rw [discBump_eq_zero_left, zero_smul]

lemma discPert_right {n : ℕ} (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (u : ℝ) :
    discPert v ((1 : ℝ), u) = 0 := by
  simp only [discPert]
  exact Finset.sum_eq_zero fun k _ => by rw [discBump_eq_zero_right, zero_smul]


/-! ## The `u`-derivatives of the bumps and the bad sets -/

/-- The `u`-derivative of the bump `k` at `(x, 0)`. -/
def bumpU (k : Fin 2 × Fin 2) (x : ℝ) : ℝ := fderiv ℝ (discBump k) (x, 0) (0, 1)

/-- The `u`-derivative of the bump `k` at `(x, 1)`. -/
def bumpU1 (k : Fin 2 × Fin 2) (x : ℝ) : ℝ := fderiv ℝ (discBump k) (x, 1) (0, 1)

section Derivatives

/-- The `(0,1)`-directional derivative of a map of the plane is the derivative along the second
coordinate. -/
lemma fderiv_snd_eq_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × ℝ → F) (x u : ℝ) (hG : DifferentiableAt ℝ G (x, u)) :
    fderiv ℝ G (x, u) (0, 1) = deriv (fun t : ℝ => G (x, t)) u := by
  have hg : HasDerivAt (fun t : ℝ => (x, t)) ((0, 1) : ℝ × ℝ) u := by
    have h1 : HasDerivAt (fun _ : ℝ => x) (0 : ℝ) u := hasDerivAt_const u x
    have h2 : HasDerivAt (fun t : ℝ => t) (1 : ℝ) u := hasDerivAt_id u
    exact h1.prodMk h2
  have h := hG.hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => (x, t)) (x := u) hg
  exact h.deriv.symm

lemma differentiableAt_discBump (k : Fin 2 × Fin 2) (x u : ℝ) :
    DifferentiableAt ℝ (discBump k) (x, u) := by
  have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => uBeta k.1 p.2) (x, u) :=
    ((contDiff_uBeta k.1).differentiable (by simp)).differentiableAt.comp (x := (x, u))
      differentiableAt_snd
  have h2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => xAlpha k.2 p.1) (x, u) :=
    ((contDiff_xAlpha k.2).differentiable (by simp)).differentiableAt.comp (x := (x, u))
      differentiableAt_fst
  exact h1.mul h2

lemma hasDerivAt_uBump_zero : HasDerivAt uBump 1 0 := by
  have h : HasDerivAt (fun u : ℝ => u * (1 - u)) (1 * (1 - 0) + 0 * (0 - 1)) 0 :=
    (hasDerivAt_id (0:ℝ)).mul ((hasDerivAt_const (x := (0:ℝ)) (1:ℝ)).sub (hasDerivAt_id 0))
  norm_num at h
  exact h

lemma hasDerivAt_uBump2_zero : HasDerivAt uBump2 1 0 := by
  have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) (0 : ℝ) := by
    have h : HasDerivAt ((fun _ : ℝ => (1:ℝ)) - id) (0 - 1) 0 :=
      (hasDerivAt_const (x := (0:ℝ)) (1:ℝ)).sub (hasDerivAt_id 0)
    have hfun : ((fun _ : ℝ => (1:ℝ)) - id) = fun u : ℝ => 1 - u := rfl
    rw [hfun] at h
    norm_num at h
    exact h
  have h : HasDerivAt (fun u : ℝ => u * (1 - u) ^ 2)
      (1 * (1 - 0) ^ 2 + 0 * (2 * (1 - 0) ^ (2-1) * (-1))) 0 :=
    (hasDerivAt_id (0:ℝ)).mul (h1.pow 2)
  norm_num at h
  exact h

lemma hasDerivAt_uBump_one : HasDerivAt uBump (-1) 1 := by
  have h : HasDerivAt (fun u : ℝ => u * (1 - u)) (1 * (1 - 1) + 1 * (0 - 1)) 1 :=
    (hasDerivAt_id (1:ℝ)).mul ((hasDerivAt_const (x := (1:ℝ)) (1:ℝ)).sub (hasDerivAt_id 1))
  norm_num at h
  exact h

lemma hasDerivAt_uBump2_one : HasDerivAt uBump2 0 1 := by
  have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) (1 : ℝ) := by
    have h : HasDerivAt ((fun _ : ℝ => (1:ℝ)) - id) (0 - 1) 1 :=
      (hasDerivAt_const (x := (1:ℝ)) (1:ℝ)).sub (hasDerivAt_id 1)
    have hfun : ((fun _ : ℝ => (1:ℝ)) - id) = fun u : ℝ => 1 - u := rfl
    rw [hfun] at h
    norm_num at h
    exact h
  have h : HasDerivAt (fun u : ℝ => u * (1 - u) ^ 2)
      (1 * (1 - 1) ^ 2 + 1 * (2 * (1 - 1) ^ (2-1) * (-1))) 1 :=
    (hasDerivAt_id (1:ℝ)).mul (h1.pow 2)
  norm_num at h
  exact h

lemma hasDerivAt_uBeta_zero (i : Fin 2) : HasDerivAt (uBeta i) 1 0 := by
  by_cases h : i = 0
  · rw [h, uBeta_zero_fun]; exact hasDerivAt_uBump_zero
  · rw [uBeta_ne_zero_fun h]; exact hasDerivAt_uBump2_zero

lemma deriv_uBeta_zero (i : Fin 2) : deriv (uBeta i) 0 = 1 :=
  (hasDerivAt_uBeta_zero i).deriv

lemma deriv_uBeta_one (i : Fin 2) : deriv (uBeta i) 1 = if i = 0 then -1 else 0 := by
  by_cases h : i = 0
  · rw [if_pos h, h, uBeta_zero_fun]; exact hasDerivAt_uBump_one.deriv
  · rw [if_neg h, uBeta_ne_zero_fun h]; exact hasDerivAt_uBump2_one.deriv

lemma bumpU_eq (k : Fin 2 × Fin 2) (x : ℝ) : bumpU k x = xAlpha k.2 x := by
  rw [bumpU, fderiv_snd_eq_deriv _ x 0 (differentiableAt_discBump k x 0)]
  have hfun : (fun t : ℝ => discBump k (x, t)) = fun t : ℝ => uBeta k.1 t * xAlpha k.2 x := by
    funext t; rfl
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => uBeta k.1 t * xAlpha k.2 x) (1 * xAlpha k.2 x) 0 :=
    (hasDerivAt_uBeta_zero k.1).mul_const (xAlpha k.2 x)
  rw [h1.deriv]
  ring

lemma bumpU1_eq (k : Fin 2 × Fin 2) (x : ℝ) :
    bumpU1 k x = if k.1 = 0 then -xAlpha k.2 x else 0 := by
  rw [bumpU1, fderiv_snd_eq_deriv _ x 1 (differentiableAt_discBump k x 1)]
  have hfun : (fun t : ℝ => discBump k (x, t)) = fun t : ℝ => uBeta k.1 t * xAlpha k.2 x := by
    funext t; rfl
  rw [hfun]
  by_cases h : k.1 = 0
  · rw [if_pos h, h, uBeta_zero_fun]
    have h1 : HasDerivAt (fun t : ℝ => uBump t * xAlpha k.2 x) (-1 * xAlpha k.2 x) 1 :=
      hasDerivAt_uBump_one.mul_const (xAlpha k.2 x)
    rw [h1.deriv]; ring
  · rw [if_neg h, uBeta_ne_zero_fun h]
    have h1 : HasDerivAt (fun t : ℝ => uBump2 t * xAlpha k.2 x) (0 * xAlpha k.2 x) 1 :=
      hasDerivAt_uBump2_one.mul_const (xAlpha k.2 x)
    rw [h1.deriv]; ring

/-- The bump `(0,0)` does not vanish on the open square. -/
lemma discBump_zero_ne {p : ℝ × ℝ} (hp : p ∈ discSq) : discBump (0, 0) p ≠ 0 := by
  have hp1 : p.1 ∈ Set.Ioo (-1 : ℝ) 1 := hp.1
  have hp2 : p.2 ∈ Set.Ioo (0 : ℝ) 1 := hp.2
  have hθ := xAngle_mem hp1
  have hb : uBeta 0 p.2 ≠ 0 := by
    rw [uBeta_zero_fun]
    simp only [uBump]
    exact mul_ne_zero (ne_of_gt hp2.1) (ne_of_gt (by linarith [hp2.2] : (0:ℝ) < 1 - p.2))
  have ha : xAlpha 0 p.1 ≠ 0 := by
    rw [xAlpha_zero_fun]
    exact mul_ne_zero (by nlinarith [hp1.1, hp1.2])
      (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩))
  rw [show discBump (0,0) p = uBeta 0 p.2 * xAlpha 0 p.1 from rfl]
  exact mul_ne_zero hb ha

/-- The `u`-derivative of the bump `(0,0)` at `(x,0)` does not vanish in the open interval. -/
lemma bumpU_zero_ne {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : bumpU (0, 0) x ≠ 0 := by
  rw [bumpU_eq]
  rw [xAlpha_zero_fun]
  have hθ := xAngle_mem hx
  exact mul_ne_zero (by nlinarith [hx.1, hx.2])
    (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩))

/-- The `u`-derivative of the bump `(0,0)` at `(x,1)` does not vanish in the open interval. -/
lemma bumpU1_zero_ne {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : bumpU1 (0, 0) x ≠ 0 := by
  rw [bumpU1_eq]
  simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte]
  rw [xAlpha_zero_fun]
  have hθ := xAngle_mem hx
  exact neg_ne_zero.mpr (mul_ne_zero (by nlinarith [hx.1, hx.2])
    (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)))

lemma exists_bumpU_ne_zero {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ k : Fin 2 × Fin 2, bumpU k x ≠ 0 := by
  rcases xAlpha_ne_zero hx with h | h
  · exact ⟨(0, 0), by rw [bumpU_eq]; exact h⟩
  · exact ⟨(0, 1), by rw [bumpU_eq]; exact h⟩

lemma exists_bumpU1_ne_zero {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ k : Fin 2 × Fin 2, bumpU1 k x ≠ 0 := by
  rcases xAlpha_ne_zero hx with h | h
  · refine ⟨(0, 0), ?_⟩
    rw [bumpU1_eq]
    simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte]
    exact neg_ne_zero.mpr h
  · refine ⟨(0, 1), ?_⟩
    rw [bumpU1_eq]
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, ↓reduceIte]
    exact neg_ne_zero.mpr h

end Derivatives

section BadSets

open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]

/-- Parameters `v` for which the disc meets `f '' M` inside the open square. -/
def badAvoid (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) :
    Set ((Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) :=
  {v | ∃ p ∈ discSq, ∃ y : M, discMap f γ₁ γ₂ v p = f y}

/-- Parameters `v` for which the disc fails to be injective on the open square. -/
def badInj (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) :
    Set ((Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) :=
  {v | ∃ p ∈ discSq, ∃ q ∈ discSq, p ≠ q ∧ discMap f γ₁ γ₂ v p = discMap f γ₁ γ₂ v q}

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- Parameters `v` for which the disc is *not* transverse to `f '' M` at the lower edge. -/
def badTransBot (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) :
    Set ((Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) :=
  {v | ∃ x ∈ Set.Ioo (-1 : ℝ) 1,
    (f (γ₂ (sigR x)) - f (γ₁ (sigR x)) + ∑ k, (bumpU k x) • v k) ∈
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (γ₁ (sigR x))).range}

/-- Parameters `v` for which the disc is *not* transverse to `f '' M` at the upper edge. -/
def badTransTop (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) :
    Set ((Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) :=
  {v | ∃ x ∈ Set.Ioo (-1 : ℝ) 1,
    (f (γ₂ (sigR x)) - f (γ₁ (sigR x)) + ∑ k, (bumpU1 k x) • v k) ∈
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (γ₂ (sigR x))).range}

end BadSets

end

end Work.Drive.Whitney
