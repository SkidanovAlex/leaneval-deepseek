import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Leibniz rule for the mixed operator with a radial and an angular factor

`Work.Spaces.mixed b a = D_z^b D_θ^a` (`D_z = z ∂_z`, `D_θ = sin(2θ) ∂_θ`).  For a product

  `(z,θ) ↦ X z * (γ θ * f z θ)`

of a *radial* factor `X` which is only `C^6` on `(0,∞)` (so not smooth on the closed quadrant and
therefore outside the derivation-like API of `Work.Spaces`, which is stated for classes smooth on
a *neighbourhood* of the closed quadrant or for analytic data), an *angular* factor `γ` which is
smooth on the open quadrant, and a datum `f` smooth on the open quadrant, the iterated mixed
derivative splits as a double binomial convolution:

`D_z^b D_θ^a (X·γ·f) = Σ_{k ≤ b} Σ_{i ≤ a} C(b,k)·C(a,i)·(D_z^k X)·(D_θ^i γ)·(D_z^{b-k}D_θ^{a-i} f)`.

The proof is the composition of the two available Leibniz rules:

* `Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul` splits off the radial factor `X` (all
  the resulting `z`-derivatives fall on `X` and `f`, none on `γ`);
* `thetaOnlyLeibniz` (below) splits the angular factor `γ` off the remaining mixed derivative.

The second rule is the pair Leibniz rule `Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed` for the
open quadrant, in which the factor `γ` only depends on `θ`: all the `D_z`-derivatives of `γ̃` with
positive order vanish (`mixed_zindep_zero`), so the double sum collapses to a single one.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-! ## `z`-independent data -/

/-- If `u` does not depend on `z`, then nor does any of its `D_θ`-iterates. -/
lemma DthIter_zindep {u : ℝ → ℝ → ℝ} (h : ∀ z z' θ, u z θ = u z' θ) :
    ∀ x z z' θ, Work.Spaces.DthIter x u z θ = Work.Spaces.DthIter x u z' θ := by
  intro x
  induction x with
  | zero => exact fun z z' θ => h z z' θ
  | succ n ih =>
      intro z z' θ
      show Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter n u) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter n u) z' θ
      congr 1
      show deriv (fun θ' => Work.Spaces.DthIter n u z θ') θ
        = deriv (fun θ' => Work.Spaces.DthIter n u z' θ') θ
      congr 1
      funext θ'
      exact ih z z' θ'

/-- The iterate of `Zop u = z u'` vanishes on constants (in positive order). -/
private lemma Zop_iterate_const_succ (y : ℕ) (c : ℝ) :
    Work.Spaces.Zop^[y + 1] (fun _ : ℝ => c) = fun _ => 0 := by
  induction y with
  | zero =>
      funext z
      simp [Work.Spaces.Zop, deriv_const]
  | succ y ih =>
      rw [Function.iterate_succ_apply', ih]
      funext z
      simp [Work.Spaces.Zop, deriv_const]

/-- All the mixed derivatives `D_z^y D_θ^x u` with `y ≥ 1` of a `z`-independent `u` vanish. -/
lemma mixed_zindep_zero {u : ℝ → ℝ → ℝ} (h : ∀ z z' θ, u z θ = u z' θ) :
    ∀ y, 1 ≤ y → ∀ x z θ, Work.Spaces.mixed y x u z θ = 0 := by
  intro y hy x z θ
  have hz : (fun z' => Work.Spaces.DthIter x u z' θ) = fun _ => Work.Spaces.DthIter x u z θ := by
    funext z'
    exact DthIter_zindep h x z' z θ
  have h1 : Work.Spaces.DzIter y (Work.Spaces.DthIter x u) z θ
      = Work.Spaces.Zop^[y] (fun z' => Work.Spaces.DthIter x u z' θ) z :=
    congrFun (Work.Spaces.Zop_slice y (Work.Spaces.DthIter x u) θ) z
  show Work.Spaces.DzIter y (Work.Spaces.DthIter x u) z θ = 0
  rw [h1, hz]
  obtain ⟨k, rfl⟩ : ∃ k, y = k + 1 := ⟨y - 1, by omega⟩
  rw [Zop_iterate_const_succ]

/-! ## The Leibniz rule for an angular factor -/

/-- **Leibniz rule for a `θ`-only factor.**  For `γ` smooth on the open quadrant (viewed as
`(z,θ) ↦ γ θ`) and a datum `f` smooth on the open quadrant,

`D_z^j D_θ^a (γ·f) = Σ_{i ≤ a} C(a,i)·(D_θ^i γ)·(D_z^j D_θ^{a-i} f)` on `Q0`.

This is the pair Leibniz rule `leibniz_open_mixed` in which all the terms with a positive number
of `z`-derivatives on `γ` are killed by `mixed_zindep_zero`. -/
lemma thetaOnlyLeibniz {γ : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hγ : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => γ θ))
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ (j a : ℕ) (z θ : ℝ), 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j a (fun z θ => γ θ * f z θ) z θ
        = ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ)
            * (Work.Spaces.DthIter i (fun _ θ : ℝ => γ θ) z θ
                * Work.Spaces.mixed j (a - i) f z θ) := by
  intro j a z θ hz hθ0 hθ1
  have h := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j a (fun _ θ : ℝ => γ θ) f hγ hf
    z θ hz hθ0 hθ1
  rw [h]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, tsub_zero]
    rfl
  · intro y hy hy0
    have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy0
    have hzero : Work.Spaces.mixed y x (fun _ θ : ℝ => γ θ) z θ = 0 :=
      mixed_zindep_zero (fun z z' θ => rfl) y hy1 x z θ
    rw [hzero]
    ring
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos j)) h0

/-! ## The main lemma -/

theorem mixedRadialThetaMul {X : ℝ → ℝ} {γ : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hγ : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => γ θ))
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ (b a : ℕ), b ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => X z * (γ θ * f z θ)) z θ
        = ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
            ((b.choose k : ℝ) * (a.choose i : ℝ))
              * (Work.Elliptic.DzdIter k X z
                  * (Work.Spaces.DthIter i (fun _ θ : ℝ => γ θ) z θ
                      * Work.Spaces.mixed (b - k) (a - i) f z θ)) := by
  intro b a hb z θ hz hθ0 hθ1
  have hF : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => γ θ * f z θ) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun x : ℝ × ℝ => γ x.2 * f x.1 x.2)
      Work.FTS.EllipticEst.Q0
    exact hγ.mul hf
  have h1 := Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul (X := X)
    (f := fun z θ : ℝ => γ θ * f z θ) hX hF b a hb z θ hz hθ0 hθ1
  rw [h1]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [thetaOnlyLeibniz hγ hf (b - k) a z θ hz hθ0 hθ1]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  ring

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
