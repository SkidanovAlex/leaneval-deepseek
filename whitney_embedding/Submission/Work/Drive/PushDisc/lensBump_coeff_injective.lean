import Mathlib
import Submission.Work.Drive.PushDisc.lensRegularDefs

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff ENNReal
open Set Metric MeasureTheory Topology Filter

/-!
# Injectivity of the bump-coefficient map

For `p` in the open lens `lensOpen` the map

    (U, W) ↦ (k ↦ U * ∂ₓ(lensBump k)(p) + W * ∂_y(lensBump k)(p))

from `ℝ × ℝ` to `(Fin 2 × Fin 2) → ℝ` is injective, i.e. the four gradients
`∇(lensBump ρ k)(p)` span `ℝ²`.

The proof uses two multiplicative relations between the four bumps, valid *everywhere*
(not only on the lens):

* `lensBump ρ (0,1) = (1 + x) * lensBump ρ (0,0)`,
* `lensBump ρ (1,0) = (1 + arch x - y) * lensBump ρ (0,0)`,

where `x = p.1`, `y = p.2` (and the third relation `lensBump ρ (1,1) = (1+x) * lensBump ρ (1,0)`
is not needed).  Writing `d_k = fderiv ℝ (lensBump ρ k) p`, the product rule and
`ach'`-freeness of the multipliers give

* `d_{01} = (1+x) • d_{00} + (bump 00 p) • fst`,
* `d_{10} = (1+arch x - y) • d_{00} + (bump 00 p) • (fderiv (1 + arch ·₁ - ·₂) p)`,
  whose `(0,1)`-component is `-1`.

So if `V` is in the kernel of all four functionals, then
`0 = d_{01}(V) = (1+x) * 0 + bump 00 p * V.1` gives `V.1 = 0`
(`bump 00 p > 0` on the open lens), and then
`0 = d_{10}(V) = (bump 00 p) * (fderiv (1 + arch ·₁ - ·₂) p V) = -(bump 00 p) * V.2`
gives `V.2 = 0`.
-/

section Helpers

/-- `arch` is smooth. -/
lemma contDiff_arch : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) arch := by
  rw [show arch = fun x : ℝ => 1 - x ^ 2 from rfl]
  fun_prop

lemma differentiableAt_arch (x : ℝ) : DifferentiableAt ℝ arch x :=
  contDiff_arch.contDiffAt.differentiableAt (by simp)

/-- The `(0,1)`-bump is the `(0,0)`-bump times `1 + x`. -/
lemma lensBump_zero_one_eq (ρ : ℝ) (q : ℝ × ℝ) :
    lensBump ρ (0, 1) q = (1 + q.1) * lensBump ρ (0, 0) q := by
  simp only [lensBump, lensAlpha_one_fun, lensAlpha_zero_fun]; ring

/-- The `(1,0)`-bump is the `(0,0)`-bump times `1 + arch x - y`. -/
lemma lensBump_one_zero_eq (ρ : ℝ) (q : ℝ × ℝ) :
    lensBump ρ (1, 0) q = (1 + arch q.1 - q.2) * lensBump ρ (0, 0) q := by
  simp only [lensBump, lensAlpha_zero_fun, lensZeta_one_fun, lensZeta_zero_fun]; ring

/-- `fderiv` of the multiplier `(x, y) ↦ 1 + x` is the first projection. -/
lemma fderiv_one_add_fst (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => (1 : ℝ) + q.1) p = ContinuousLinearMap.fst ℝ ℝ ℝ := by
  have : (fun q : ℝ × ℝ => (1 : ℝ) + q.1) = fun q => (1 : ℝ) + Prod.fst q := rfl
  rw [this, fderiv_const_add, fderiv_fst]

/-- The `y`-derivative of the multiplier `(x, y) ↦ 1 + arch x - y` is `-1`. -/
lemma fderiv_h_apply (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => (1 : ℝ) + arch q.1 - q.2) p (0, 1) = -1 := by
  have hfa : DifferentiableAt ℝ (fun q : ℝ × ℝ => (1 : ℝ) + arch q.1) p := by
    show DifferentiableAt ℝ (fun q : ℝ × ℝ => (1 : ℝ) + (1 - q.1 ^ 2)) p
    fun_prop
  have h1 : (fun q : ℝ × ℝ => (1 : ℝ) + arch q.1 - q.2)
      = (fun q : ℝ × ℝ => ((1 : ℝ) + arch q.1)) - Prod.snd := rfl
  rw [h1, fderiv_sub hfa (by fun_prop), sub_apply]
  have h2 : fderiv ℝ (fun q : ℝ × ℝ => (1 : ℝ) + arch q.1) p
      = fderiv ℝ (fun q : ℝ × ℝ => arch q.1) p :=
    fderiv_const_add (1 : ℝ)
  have h3 : (fun q : ℝ × ℝ => arch q.1) = arch ∘ Prod.fst := rfl
  rw [h2, h3, fderiv_comp p (differentiableAt_arch p.1) (by fun_prop), fderiv_fst, fderiv_snd]
  simp

/-- The `(0,1)`-bump's derivative is `(1+x)` times the `(0,0)`-bump's plus the first projection. -/
lemma fderiv_lensBump_zero_one (ρ : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (lensBump ρ (0, 1)) p
      = (1 + p.1) • fderiv ℝ (lensBump ρ (0, 0)) p
        + (lensBump ρ (0, 0) p) • (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
  have hfun : lensBump ρ (0, 1) = fun q : ℝ × ℝ => (1 + q.1) * lensBump ρ (0, 0) q :=
    funext fun q => lensBump_zero_one_eq ρ q
  rw [hfun, fderiv_fun_mul (c := fun q : ℝ × ℝ => (1 : ℝ) + q.1)
      (d := lensBump ρ (0, 0)) (x := p) (by fun_prop)
      ((contDiff_lensBump ρ (0, 0)).contDiffAt.differentiableAt (by simp)),
    fderiv_one_add_fst]

/-- Evaluated form of `fderiv_lensBump_zero_one`. -/
lemma fderiv_lensBump_zero_one_apply (ρ : ℝ) (p V : ℝ × ℝ) :
    fderiv ℝ (lensBump ρ (0, 1)) p V
      = (1 + p.1) * fderiv ℝ (lensBump ρ (0, 0)) p V + (lensBump ρ (0, 0) p) * V.1 := by
  rw [fderiv_lensBump_zero_one, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  rfl

/-- The `(1,0)`-bump's derivative. -/
lemma fderiv_lensBump_one_zero (ρ : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (lensBump ρ (1, 0)) p
      = (1 + arch p.1 - p.2) • fderiv ℝ (lensBump ρ (0, 0)) p
        + (lensBump ρ (0, 0) p) • (fderiv ℝ (fun q : ℝ × ℝ => (1 : ℝ) + arch q.1 - q.2) p) := by
  have hfun : lensBump ρ (1, 0) = fun q : ℝ × ℝ => (1 + arch q.1 - q.2) * lensBump ρ (0, 0) q :=
    funext fun q => lensBump_one_zero_eq ρ q
  have hfd : DifferentiableAt ℝ (fun q : ℝ × ℝ => (1 : ℝ) + arch q.1 - q.2) p := by
    show DifferentiableAt ℝ (fun q : ℝ × ℝ => (1 : ℝ) + (1 - q.1 ^ 2) - q.2) p
    fun_prop
  rw [hfun, fderiv_fun_mul (c := fun q : ℝ × ℝ => (1 : ℝ) + arch q.1 - q.2)
      (d := lensBump ρ (0, 0)) (x := p) hfd
      ((contDiff_lensBump ρ (0, 0)).contDiffAt.differentiableAt (by simp))]

/-- Evaluated form of `fderiv_lensBump_one_zero`. -/
lemma fderiv_lensBump_one_zero_apply (ρ : ℝ) (p V : ℝ × ℝ) :
    fderiv ℝ (lensBump ρ (1, 0)) p V
      = (1 + arch p.1 - p.2) * fderiv ℝ (lensBump ρ (0, 0)) p V
        + (lensBump ρ (0, 0) p)
            * (fderiv ℝ (fun q : ℝ × ℝ => (1 : ℝ) + arch q.1 - q.2) p V) := by
  rw [fderiv_lensBump_one_zero, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]

/-- The `(0,0)`-bump is strictly positive on the open lens. -/
lemma lensBump_zero_zero_pos {ρ : ℝ} (hρ : 0 < ρ) {p : ℝ × ℝ} (hp : p ∈ lensOpen) :
    0 < lensBump ρ (0, 0) p := by
  have hx : |p.1| < 1 := hp.1
  have hy0 : 0 < p.2 := hp.2.1
  have hy1 : p.2 < arch p.1 := hp.2.2
  simp only [lensBump]
  rw [lensAlpha_zero_fun, lensZeta_zero_fun]
  have hc := lensChi_pos_of_abs_lt_one hρ hx
  have ha : 0 < 1 - p.1 ^ 2 := by rw [abs_lt] at hx; nlinarith [hx.1, hx.2]
  have hz : 0 < p.2 * (arch p.1 - p.2) := mul_pos hy0 (by linarith)
  exact mul_pos (mul_pos hc ha) hz

/-- The value of a linear functional on `ℝ × ℝ` is its value on the two basis vectors. -/
lemma fderiv_eq_pair (f : ℝ × ℝ → ℝ) (p V : ℝ × ℝ) :
    fderiv ℝ f p V = V.1 * fderiv ℝ f p (1, 0) + V.2 * fderiv ℝ f p (0, 1) := by
  have hsplit : V = V.1 • (1, 0) + V.2 • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  conv_lhs => rw [hsplit]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

end Helpers

theorem lensBump_coeff_injective {ρ : ℝ} (hρ : 0 < ρ) {p : ℝ × ℝ} (hp : p ∈ lensOpen) :
    Function.Injective (fun UW : ℝ × ℝ => fun k : Fin 2 × Fin 2 =>
      UW.1 * fderiv ℝ (lensBump ρ k) p (1, 0) + UW.2 * fderiv ℝ (lensBump ρ k) p (0, 1)) := by
  have hBpos : 0 < lensBump ρ (0, 0) p := lensBump_zero_zero_pos hρ hp
  -- The kernel of the four functionals is trivial.
  have hker : ∀ V : ℝ × ℝ,
      (∀ k : Fin 2 × Fin 2, fderiv ℝ (lensBump ρ k) p V = 0) → V = 0 := by
    intro V hV
    have hV00 : fderiv ℝ (lensBump ρ (0, 0)) p V = 0 := hV (0, 0)
    have hV01 : fderiv ℝ (lensBump ρ (0, 1)) p V = 0 := hV (0, 1)
    have hV10 : fderiv ℝ (lensBump ρ (1, 0)) p V = 0 := hV (1, 0)
    have hU : V.1 = 0 := by
      have h := fderiv_lensBump_zero_one_apply ρ p V
      rw [hV01, hV00] at h
      have h2 : lensBump ρ (0, 0) p * V.1 = 0 := by linarith
      exact (mul_eq_zero.mp h2).resolve_left (ne_of_gt hBpos)
    have hW : V.2 = 0 := by
      have h := fderiv_lensBump_one_zero_apply ρ p V
      rw [hV10, hV00] at h
      have h2 : lensBump ρ (0, 0) p
          * fderiv ℝ (fun q : ℝ × ℝ => (1 : ℝ) + arch q.1 - q.2) p V = 0 := by linarith
      have h3 : fderiv ℝ (fun q : ℝ × ℝ => (1 : ℝ) + arch q.1 - q.2) p V = 0 :=
        (mul_eq_zero.mp h2).resolve_left (ne_of_gt hBpos)
      have h4 := fderiv_eq_pair (fun q : ℝ × ℝ => (1 : ℝ) + arch q.1 - q.2) p V
      rw [h3, fderiv_h_apply p, hU] at h4
      linarith
    exact Prod.ext hU hW
  intro UW UW' h
  have hzero : ∀ k : Fin 2 × Fin 2, fderiv ℝ (lensBump ρ k) p (UW - UW') = 0 := by
    intro k
    have hk : fderiv ℝ (lensBump ρ k) p UW = fderiv ℝ (lensBump ρ k) p UW' := by
      have h1 : UW.1 * fderiv ℝ (lensBump ρ k) p (1, 0)
            + UW.2 * fderiv ℝ (lensBump ρ k) p (0, 1)
          = UW'.1 * fderiv ℝ (lensBump ρ k) p (1, 0)
            + UW'.2 * fderiv ℝ (lensBump ρ k) p (0, 1) :=
        congrFun h k
      rw [← fderiv_eq_pair (lensBump ρ k) p UW,
        ← fderiv_eq_pair (lensBump ρ k) p UW'] at h1
      exact h1
    rw [map_sub, hk, sub_self]
  exact sub_eq_zero.mp (hker (UW - UW') hzero)

end Work.Drive.PushDisc
