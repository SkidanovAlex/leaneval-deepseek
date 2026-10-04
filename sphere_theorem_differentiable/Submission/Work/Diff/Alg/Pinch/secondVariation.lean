import Mathlib
import Submission.Work.Diff.Alg.Pinch.Qop
import Submission.Work.Diff.Alg.q2p_transform
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second variation of the isotropic-curvature functional at a degenerate direction

`Work.Diff.Alg.Pinch.secondVariation` (Brendle–Schoen, *Manifolds with 1/4-pinched curvature are
space forms*, §2): if an algebraic curvature tensor `R` has nonnegative complex sectional curvature
(`InPIC2 R`) and the isotropic curvature of the decomposable bivector `ζ ∧ η` vanishes, then the
isotropic-curvature form is nonnegative on the whole tangent space of the cone of decomposable
bivectors at `ζ ∧ η`, i.e. on every `u ∧ η + ζ ∧ v`.

The proof is a second-variation argument.  Write `A = ζ ∧ η`, `W = u ∧ η + ζ ∧ v`, `Z = u ∧ v`, and
consider the decomposable family `X_s = (ζ + s u) ∧ (η + s v) = A + s W + s² Z` (`s ∈ ℂ`).  Since
`InPIC2 R` says exactly that `X ↦ (Φ X (conj X)).re` is nonnegative on decomposable bivectors, the
function `ψ(s) = (Φ (X_s) (conj X_s)).re` is nonnegative on all of `ℂ`.  Expanding `ψ` bilinearly,

`ψ(s) = |s|² E + |s|⁴ F + ` (terms of angular type `s̄`, `s̄²`, `s s̄²` and their conjugates),

where `E = (Φ W (conj W)).re` is the quantity to be bounded and `F = (Φ Z (conj Z)).re`.  Summing the
four values `s = t, -t, i t, -i t` kills all the angular terms and gives `4 t² E + 4 t⁴ F ≥ 0`, i.e.
`E + t² F ≥ 0` for every `t > 0`; letting `t → 0` (with `F ≥ 0` known separately) yields `E ≥ 0`.

The bridge from `InPIC2` to the nonnegativity of `Φ` on decomposable bivectors is the identity
`Phi R (a ∧ b) (conj (c ∧ d)) = 4 * cR4 R a b (conj c) (conj d)` combined with
`(cR4 R ζ η (conj ζ) (conj η)).re = EFunC R ζ η` (`Work.Diff.Alg.cR4_re`).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg
open Work.Diff.Alg (cR4)

variable {n : ℕ}

/-! ## Expanding `Phi` on wedges -/

/-- Componentwise `star` commutes with the wedge. -/
theorem bar_wedgeF (ζ η : Fin n → ℂ) : bar (wedgeF ζ η) = wedgeF (star ζ) (star η) := by
  funext p
  simp only [bar, wedgeF, Pi.star_apply]
  rw [star_sub, star_mul, star_mul]
  ring

/-- `Phi` as a four-fold sum over the individual indices. -/
theorem Phi_quad (R : Curv4 n) (X Y : Fin n × Fin n → ℂ) :
    Phi R X Y = ∑ a, ∑ b, ∑ c, ∑ d, (R a b c d : ℂ) * X (a, b) * Y (c, d) := by
  simp only [Phi, Fintype.sum_prod_type]

/-- An algebraic curvature tensor is symmetric under the flip of both pairs. -/
theorem IsAlgCurv_antisym_both {R : Curv4 n} (hR : IsAlgCurv R) (i j k l : Fin n) :
    R j i l k = R i j k l := by
  rw [hR.1 i j l k, Work.Diff.Alg.Q2P.IsAlgCurv_antisym₃₄ hR i j k l]
  ring

/-- `Phi` on a wedge against the conjugate wedge is `4` times the complexified algebraic
curvature tensor: `Φ (a ∧ b) (conj (c ∧ d)) = 4 R(a, b, c̄, d̄)`. -/
theorem Phi_wedge_cR4 (R : Curv4 n) (hR : IsAlgCurv R) (a b c d : Fin n → ℂ) :
    Phi R (wedgeF a b) (bar (wedgeF c d)) = 4 * cR4 R a b (star c) (star d) := by
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l, (R i j k l : ℂ) * (a i * b j) * (star c k * star d l))
      = ∑ i, ∑ j, ∑ k, ∑ l, (R i j k l : ℂ) * a i * b j * star c k * star d l := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  have h2 : (∑ i, ∑ j, ∑ k, ∑ l, (R i j k l : ℂ) * (a i * b j) * (star c l * star d k))
      = - (∑ i, ∑ j, ∑ k, ∑ l, (R i j k l : ℂ) * (a i * b j) * (star c k * star d l)) := by
    rw [Work.Diff.Alg.sum4_swap34C
          (fun i j k l => (R i j k l : ℂ) * (a i * b j) * (star c l * star d k))]
    rw [show (∑ i, ∑ j, ∑ k, ∑ l, (R i j l k : ℂ) * (a i * b j) * (star c k * star d l))
        = ∑ i, ∑ j, ∑ k, ∑ l, -((R i j k l : ℂ) * (a i * b j) * (star c k * star d l)) from by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro l _
      rw [Work.Diff.Alg.Q2P.IsAlgCurv_antisym₃₄ hR i j k l]
      push_cast
      ring]
    simp only [Finset.sum_neg_distrib]
  have h3 : (∑ i, ∑ j, ∑ k, ∑ l, (R i j k l : ℂ) * (a j * b i) * (star c k * star d l))
      = - (∑ i, ∑ j, ∑ k, ∑ l, (R i j k l : ℂ) * (a i * b j) * (star c k * star d l)) := by
    rw [Work.Diff.Alg.sum4_swap12C
          (fun i j k l => (R i j k l : ℂ) * (a j * b i) * (star c k * star d l))]
    rw [show (∑ i, ∑ j, ∑ k, ∑ l, (R j i k l : ℂ) * (a i * b j) * (star c k * star d l))
        = ∑ i, ∑ j, ∑ k, ∑ l, -((R i j k l : ℂ) * (a i * b j) * (star c k * star d l)) from by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro l _
      rw [hR.1 i j k l]
      push_cast
      ring]
    simp only [Finset.sum_neg_distrib]
  have h4 : (∑ i, ∑ j, ∑ k, ∑ l, (R i j k l : ℂ) * (a j * b i) * (star c l * star d k))
      = ∑ i, ∑ j, ∑ k, ∑ l, (R i j k l : ℂ) * (a i * b j) * (star c k * star d l) := by
    rw [Work.Diff.Alg.sum4_swap12C
          (fun i j k l => (R i j k l : ℂ) * (a j * b i) * (star c l * star d k))]
    rw [Work.Diff.Alg.sum4_swap34C
          (fun i j k l => (R j i k l : ℂ) * (a i * b j) * (star c l * star d k))]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [IsAlgCurv_antisym_both hR i j k l]
  rw [bar_wedgeF, Phi_quad]
  simp only [wedgeF]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [h1, h2, h3, h4, cR4]
  simp only [Pi.star_apply]
  ring_nf

/-- `InPIC2 R` gives nonnegativity of `Φ` on every decomposable bivector. -/
theorem Phi_wedge_nonneg (R : Curv4 n) (hR : IsAlgCurv R) (hPIC : InPIC2 R) (a b : Fin n → ℂ) :
    0 ≤ (Phi R (wedgeF a b) (bar (wedgeF a b))).re := by
  have key : (Phi R (wedgeF a b) (bar (wedgeF a b))).re = 4 * Work.Diff.Alg.Q2P.EFunC R a b := by
    rw [Phi_wedge_cR4 R hR a b a b, Complex.mul_re, Work.Diff.Alg.cR4_re R hR a b]
    norm_num
  rw [key]
  exact mul_nonneg (by norm_num) ((Work.Diff.Alg.Q2P.inPIC2_iff_c R).mp hPIC a b)

/-! ## Linearity of `wedgeF` and of `Phi` -/

theorem wedgeF_add₁ (a a' b : Fin n → ℂ) : wedgeF (a + a') b = wedgeF a b + wedgeF a' b := by
  funext p; simp only [wedgeF, Pi.add_apply]; ring

theorem wedgeF_add₂ (a b b' : Fin n → ℂ) : wedgeF a (b + b') = wedgeF a b + wedgeF a b' := by
  funext p; simp only [wedgeF, Pi.add_apply]; ring

theorem wedgeF_smul₁ (c : ℂ) (a b : Fin n → ℂ) : wedgeF (c • a) b = c • wedgeF a b := by
  funext p; simp only [wedgeF, Pi.smul_apply, smul_eq_mul]; ring

theorem wedgeF_smul₂ (c : ℂ) (a b : Fin n → ℂ) : wedgeF a (c • b) = c • wedgeF a b := by
  funext p; simp only [wedgeF, Pi.smul_apply, smul_eq_mul]; ring

theorem Phi_add_left (R : Curv4 n) (X Y Z : Fin n × Fin n → ℂ) :
    Phi R (X + Y) Z = Phi R X Z + Phi R Y Z := by
  simp only [Phi, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro q _
  ring

theorem Phi_add_right (R : Curv4 n) (X Y Z : Fin n × Fin n → ℂ) :
    Phi R X (Y + Z) = Phi R X Y + Phi R X Z := by
  simp only [Phi, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro q _
  ring

theorem Phi_smul_left (R : Curv4 n) (c : ℂ) (X Y : Fin n × Fin n → ℂ) :
    Phi R (c • X) Y = c * Phi R X Y := by
  simp only [Phi, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro q _
  ring

theorem Phi_smul_right (R : Curv4 n) (c : ℂ) (X Y : Fin n × Fin n → ℂ) :
    Phi R X (c • Y) = c * Phi R X Y := by
  simp only [Phi, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro q _
  ring

/-! ## The two-parameter family of decomposable bivectors -/

/-- `(ζ + s u) ∧ (η + s v) = ζ∧η + s (u∧η + ζ∧v) + s² (u∧v)`. -/
theorem wedgeF_shift (ζ η u v : Fin n → ℂ) (s : ℂ) :
    wedgeF (ζ + s • u) (η + s • v)
      = wedgeF ζ η + s • (wedgeF u η + wedgeF ζ v) + (s * s) • wedgeF u v := by
  simp only [wedgeF_add₁, wedgeF_add₂, wedgeF_smul₁, wedgeF_smul₂]
  module

/-- Bilinear expansion of `Φ` on the three-term family. -/
theorem Phi_family (R : Curv4 n) (A W Z : Fin n × Fin n → ℂ) (s : ℂ) :
    Phi R (A + s • W + (s*s) • Z) (bar (A + s • W + (s*s) • Z))
      = Phi R A (bar A) + star s * Phi R A (bar W) + star (s*s) * Phi R A (bar Z)
      + s * Phi R W (bar A) + (s * star s) * Phi R W (bar W) + (s * star (s*s)) * Phi R W (bar Z)
      + (s*s) * Phi R Z (bar A) + ((s*s) * star s) * Phi R Z (bar W)
      + ((s*s) * star (s*s)) * Phi R Z (bar Z) := by
  have hbar : bar (A + s • W + (s*s) • Z) = bar A + star s • bar W + star (s*s) • bar Z := by
    rw [bar_add, bar_add, bar_smul, bar_smul]
  rw [hbar]
  simp only [Phi_add_left, Phi_add_right, Phi_smul_left, Phi_smul_right]
  ring

/-! ## The second variation -/

theorem secondVariation (n : ℕ) (R : Submission.Diff.Alg.Curv4 n)
    (hR : Submission.Diff.Alg.IsAlgCurv R) (hPIC : Submission.Diff.Alg.InPIC2 R)
    (ζ η u v : Fin n → ℂ)
    (h0 : Work.Diff.Alg.Pinch.Phi R (Work.Diff.Alg.Pinch.wedgeF ζ η) (Work.Diff.Alg.Pinch.bar (Work.Diff.Alg.Pinch.wedgeF ζ η)) = 0) :
    0 ≤ (Work.Diff.Alg.Pinch.Phi R (Work.Diff.Alg.Pinch.wedgeF u η + Work.Diff.Alg.Pinch.wedgeF ζ v)
          (Work.Diff.Alg.Pinch.bar (Work.Diff.Alg.Pinch.wedgeF u η + Work.Diff.Alg.Pinch.wedgeF ζ v))).re := by
  set A : Fin n × Fin n → ℂ := wedgeF ζ η with hA
  set W : Fin n × Fin n → ℂ := wedgeF u η + wedgeF ζ v with hW
  set Z : Fin n × Fin n → ℂ := wedgeF u v with hZ
  have h0' : Phi R A (bar A) = 0 := by rw [hA]; exact h0
  have hYs : ∀ s : ℂ, wedgeF (ζ + s • u) (η + s • v) = A + s • W + (s*s) • Z := by
    intro s
    rw [wedgeF_shift ζ η u v s, ← hA, ← hW, ← hZ]
  -- bilinear expansion of the family, with the `Phi R A (bar A) = 0` term dropped
  have hexp : ∀ s : ℂ,
      Phi R (wedgeF (ζ + s • u) (η + s • v)) (bar (wedgeF (ζ + s • u) (η + s • v)))
      = star s * Phi R A (bar W) + star (s*s) * Phi R A (bar Z)
      + s * Phi R W (bar A) + (s * star s) * Phi R W (bar W) + (s * star (s*s)) * Phi R W (bar Z)
      + (s*s) * Phi R Z (bar A) + ((s*s) * star s) * Phi R Z (bar W)
      + ((s*s) * star (s*s)) * Phi R Z (bar Z) := by
    intro s
    rw [hYs s, Phi_family R A W Z s, h0']
    ring
  -- summing the four values `t, -t, i t, -i t` kills every angular term, leaving `4 t² E + 4 t⁴ F`
  have hidgen : ∀ t : ℝ,
      (Phi R (wedgeF (ζ + (t:ℂ) • u) (η + (t:ℂ) • v))
            (bar (wedgeF (ζ + (t:ℂ) • u) (η + (t:ℂ) • v)))).re
      + (Phi R (wedgeF (ζ + (-(t:ℂ)) • u) (η + (-(t:ℂ)) • v))
            (bar (wedgeF (ζ + (-(t:ℂ)) • u) (η + (-(t:ℂ)) • v)))).re
      + (Phi R (wedgeF (ζ + ((t:ℂ) * Complex.I) • u) (η + ((t:ℂ) * Complex.I) • v))
            (bar (wedgeF (ζ + ((t:ℂ) * Complex.I) • u) (η + ((t:ℂ) * Complex.I) • v)))).re
      + (Phi R (wedgeF (ζ + (-((t:ℂ) * Complex.I)) • u) (η + (-((t:ℂ) * Complex.I)) • v))
            (bar (wedgeF (ζ + (-((t:ℂ) * Complex.I)) • u) (η + (-((t:ℂ) * Complex.I)) • v)))).re
      = 4 * t^2 * (Phi R W (bar W)).re + 4 * t^4 * (Phi R Z (bar Z)).re := by
    intro t
    rw [hexp (t:ℂ), hexp (-(t:ℂ)), hexp ((t:ℂ) * Complex.I), hexp (-((t:ℂ) * Complex.I))]
    simp only [Complex.add_re, Complex.mul_re]
    simp
    ring
  have hgen : ∀ t : ℝ,
      0 ≤ (Phi R (wedgeF (ζ + (t:ℂ) • u) (η + (t:ℂ) • v))
            (bar (wedgeF (ζ + (t:ℂ) • u) (η + (t:ℂ) • v)))).re
      + (Phi R (wedgeF (ζ + (-(t:ℂ)) • u) (η + (-(t:ℂ)) • v))
            (bar (wedgeF (ζ + (-(t:ℂ)) • u) (η + (-(t:ℂ)) • v)))).re
      + (Phi R (wedgeF (ζ + ((t:ℂ) * Complex.I) • u) (η + ((t:ℂ) * Complex.I) • v))
            (bar (wedgeF (ζ + ((t:ℂ) * Complex.I) • u) (η + ((t:ℂ) * Complex.I) • v)))).re
      + (Phi R (wedgeF (ζ + (-((t:ℂ) * Complex.I)) • u) (η + (-((t:ℂ) * Complex.I)) • v))
            (bar (wedgeF (ζ + (-((t:ℂ) * Complex.I)) • u) (η + (-((t:ℂ) * Complex.I)) • v)))).re :=
    fun t => add_nonneg
      (add_nonneg (add_nonneg (Phi_wedge_nonneg R hR hPIC _ _) (Phi_wedge_nonneg R hR hPIC _ _))
        (Phi_wedge_nonneg R hR hPIC _ _))
      (Phi_wedge_nonneg R hR hPIC _ _)
  -- hence `E + t² F ≥ 0` for every `t > 0`
  have hEgen : ∀ t : ℝ, 0 < t → 0 ≤ (Phi R W (bar W)).re + t^2 * (Phi R Z (bar Z)).re := by
    intro t ht
    have h1 := hgen t
    rw [hidgen t] at h1
    have h2 : (0:ℝ) < 4 * t^2 := by positivity
    have heq : ((Phi R W (bar W)).re + t^2 * (Phi R Z (bar Z)).re) * (4 * t^2)
        = 4 * t^2 * (Phi R W (bar W)).re + 4 * t^4 * (Phi R Z (bar Z)).re := by ring
    rw [← heq] at h1
    exact nonneg_of_mul_nonneg_left h1 h2
  have hF : 0 ≤ (Phi R Z (bar Z)).re := by rw [hZ]; exact Phi_wedge_nonneg R hR hPIC u v
  -- `F ≥ 0` and `E + t² F ≥ 0` for all `t > 0` give `E ≥ 0`
  have hmain : ∀ ε : ℝ, 0 < ε → 0 ≤ (Phi R W (bar W)).re + ε := by
    intro ε hε
    rcases lt_or_ge (Phi R W (bar W)).re 0 with hEneg | hE0
    · rcases eq_or_lt_of_le hF with hz | hp
      · have h1 := hEgen 1 one_pos
        rw [← hz] at h1
        nlinarith
      · have hpos : 0 < -(Phi R W (bar W)).re / (2 * (Phi R Z (bar Z)).re) :=
          div_pos (by linarith) (by linarith)
        have ht : 0 < Real.sqrt (-(Phi R W (bar W)).re / (2 * (Phi R Z (bar Z)).re)) :=
          Real.sqrt_pos.mpr hpos
        have h := hEgen (Real.sqrt (-(Phi R W (bar W)).re / (2 * (Phi R Z (bar Z)).re))) ht
        rw [Real.sq_sqrt hpos.le] at h
        have h2 : -(Phi R W (bar W)).re / (2 * (Phi R Z (bar Z)).re) * (Phi R Z (bar Z)).re
            = -(Phi R W (bar W)).re / 2 := by field_simp
        nlinarith
    · linarith
  exact le_of_forall_pos_le_add hmain

end Work.Diff.Alg.Pinch
