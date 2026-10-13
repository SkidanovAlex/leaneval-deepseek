/-
Copyright: work module for the Elgindi finite-time singularity project.

# Leibniz rules for a product with a radial factor

`Work.FTS.GalFields.Norm.radLeibniz` records the two Leibniz (binomial) expansions of the
radial operator `D_z = z ∂_z` applied to a product `(z, θ) ↦ R z · u z θ` in which the first
factor is radial (`R : ℝ → ℝ`, only `C⁵` on `(0,∞)` — the regularity of the profiles of
this chapter) and the second is `C^∞` on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen u`):

* `D_z^i (R · u) z θ = ∑_{b ≤ i} C(i,b) · (D_z^b R)(z) · D_z^{i-b} u z θ` for `i ≤ 4`;
* `D_z^j D_θ^i (R · u) z θ = ∑_{b ≤ j} C(j,b) · (D_z^b R)(z) · D_z^{j-b} D_θ^i u z θ`
  for `i ≥ 1`, `i + j ≤ 4` (all the `θ`-derivatives fall on `u`, because `R` does not
  depend on `θ`).

The abstract iterated Leibniz rule of the workspace
(`Work.Spaces.DerivLike.iterate_mul`) requires both factors to be `C^∞` on the whole
half-line, which the radial factor of the chapter is not.  The graded version used here is
proved by hand, exactly as `Work.FTS.Nonlinear.Pieces.RNP.row19.Lop_iter_mul_of_contDiffOn`
does for the angular operator `Lop = sin(2θ) ∂_θ`:

* `contDiffOn_Zop_iter_nat` — a `C^{b+k}` function has `C^k` `Zop`-iterates of order `b`
  (this is what supplies the differentiability of the terms in the induction step);
* `Zop_iter_mul_aux` — the induction on the order, with the Pascal reindexing
  `Work.Spaces.leibniz_step`.

The two expansions are then read off on the `z`-slices, via
`Work.FTS.LocData.Zop_iterate_slice` (`(fun z => D_z^i f z θ) = Zop^[i] (fun z => f z θ)`)
and the identification `Zop^[b] R = Work.Elliptic.DzdIter b R`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.DerivLikeDefs
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.GalFields.Norm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The one-variable operator `Zop u = z u'`: graded smoothness -/

/-- A `C^{n+1}` function on an open set has a `C^n` derivative there. -/
theorem contDiffOn_deriv_of_succ_V {u : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V) {n : ℕ}
    (hu : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) u V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (deriv u) V := by
  have hfd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fderiv ℝ u) V :=
    hu.fderiv_of_isOpen hV (by simp)
  have hev : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun z : ℝ => (fderiv ℝ u z) 1) V :=
    hfd.clm_apply contDiffOn_const
  refine hev.congr (fun z _ => ?_)
  rw [fderiv_apply_one_eq_deriv]

/-- Iterating `Zop u = z u'` raises the smoothness order: a `C^{b+k}` function has `C^k`
`Zop`-iterates of order `b`. -/
theorem contDiffOn_Zop_iter_nat {u : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V) :
    ∀ (b k : ℕ), ContDiffOn ℝ (((b + k : ℕ)) : WithTop ℕ∞) u V →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Work.Spaces.Zop^[b] u) V := by
  intro b
  induction b with
  | zero =>
      intro k hu
      simpa using hu
  | succ b ih =>
      intro k hu
      have hu' : ContDiffOn ℝ (((b + (k + 1) : ℕ)) : WithTop ℕ∞) u V :=
        hu.of_le (Nat.cast_le.mpr (by omega : b + (k + 1) ≤ (b + 1) + k))
      have h1 := ih (k + 1) hu'
      have h2 : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (deriv (Work.Spaces.Zop^[b] u)) V :=
        contDiffOn_deriv_of_succ_V hV h1
      have h3 : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞)
          (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z) V :=
        (contDiff_id.contDiffOn).mul h2
      rw [Function.iterate_succ_apply']
      change ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞)
        (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z) V
      exact h3

/-- The `z`-slice of a `SmoothOpen` datum at an interior angle is `C^n` on `(0,∞)`, for
every finite order `n` (the finite-order form of `SmoothOpen.curry_z`, whose order is the
infinite `Stability.smoothOrder`). -/
theorem curry_z_nat_of_smoothOpen {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (n : ℕ) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun z => F z θ) (Set.Ioi (0 : ℝ)) := by
  have hφ : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun z : ℝ => (z, θ)) (Set.Ioi (0 : ℝ)) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (0 : ℝ)) Work.FTS.EllipticEst.Q0 :=
    fun z hz => ⟨hz, hθ⟩
  refine ((hF.forall n).comp hφ hmap).congr (fun z _ => rfl)

/-- A `C^{b+1}` function has a differentiable `Zop`-iterate of order `b` on `V`. -/
theorem differentiableAt_Zop_iter_le {u : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V) {N b : ℕ}
    (hu : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) u V) (hb : b + 1 ≤ N) {z : ℝ} (hz : z ∈ V) :
    DifferentiableAt ℝ (Work.Spaces.Zop^[b] u) z := by
  have h1 : ContDiffOn ℝ (((b + 1 : ℕ)) : WithTop ℕ∞) u V := hu.of_le (Nat.cast_le.mpr hb)
  have h2 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (Work.Spaces.Zop^[b] u) V :=
    contDiffOn_Zop_iter_nat hV b 1 h1
  exact (h2.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hz)

/-! ## The graded Leibniz rule for `Zop` -/

/-- The `a`-th term of the Leibniz sum, differentiated: the factor `z` of `Zop` turns the
two product-rule halves into the `(a+1)`-st and the `(j-a+1)`-st `Zop`-iterate. -/
theorem Zop_deriv_term (u v : ℝ → ℝ) (z : ℝ) (j a : ℕ)
    (ha : DifferentiableAt ℝ (Work.Spaces.Zop^[a] u) z)
    (hb : DifferentiableAt ℝ (Work.Spaces.Zop^[j - a] v) z) :
    z * deriv (fun z' => (j.choose a : ℝ)
        * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[j - a] v z')) z =
      (j.choose a : ℝ)
        * (Work.Spaces.Zop^[a + 1] u z * Work.Spaces.Zop^[j - a] v z
            + Work.Spaces.Zop^[a] u z * Work.Spaces.Zop^[j - a + 1] v z) := by
  have hfun2 : (fun z' => (j.choose a : ℝ)
        * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[j - a] v z'))
      = (fun y => (j.choose a : ℝ)
        * ((Work.Spaces.Zop^[a] u * Work.Spaces.Zop^[j - a] v) y)) := rfl
  rw [hfun2, deriv_const_mul (j.choose a : ℝ) (ha.mul hb), deriv_mul ha hb,
    Function.iterate_succ_apply' Work.Spaces.Zop a u,
    Function.iterate_succ_apply' Work.Spaces.Zop (j - a) v,
    show Work.Spaces.Zop (Work.Spaces.Zop^[a] u) z
      = z * deriv (Work.Spaces.Zop^[a] u) z from rfl,
    show Work.Spaces.Zop (Work.Spaces.Zop^[j - a] v) z
      = z * deriv (Work.Spaces.Zop^[j - a] v) z from rfl]
  ring

/-- **The graded iterated Leibniz rule for `Zop u = z u'`**: on an open set `V` where both
factors are only `C^{i+1}`, the `i`-th iterate of `Zop` on the product is the binomial
convolution of the iterates of the factors. -/
theorem Zop_iter_mul_aux (i : ℕ) :
    ∀ (u v : ℝ → ℝ) (V : Set ℝ), IsOpen V →
      ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) u V →
      ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) v V →
      Set.EqOn (Work.Spaces.Zop^[i] (u * v))
        (fun z => ∑ a ∈ Finset.range (i + 1),
          (i.choose a : ℝ) * (Work.Spaces.Zop^[a] u z * Work.Spaces.Zop^[i - a] v z)) V := by
  induction i with
  | zero =>
      intro u v V hV hu hv z hz
      simp [Function.iterate_zero_apply]
  | succ i ih =>
      intro u v V hV hu hv z hz
      dsimp only
      rw [Function.iterate_succ_apply']
      have hu' : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) u V :=
        hu.of_le (Nat.cast_le.mpr (by omega : i + 1 ≤ i + 2))
      have hv' : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) v V :=
        hv.of_le (Nat.cast_le.mpr (by omega : i + 1 ≤ i + 2))
      have hih := ih u v V hV hu' hv'
      have hFa : ∀ a ≤ i, DifferentiableAt ℝ (Work.Spaces.Zop^[a] u) z := fun a ha =>
        differentiableAt_Zop_iter_le hV hu' (by omega : a + 1 ≤ i + 1) hz
      have hGb : ∀ b ≤ i, DifferentiableAt ℝ (Work.Spaces.Zop^[b] v) z := fun b hb =>
        differentiableAt_Zop_iter_le hV hv' (by omega : b + 1 ≤ i + 1) hz
      have hmem : ∀ a ∈ Finset.range (i + 1), DifferentiableAt ℝ
          (fun z' => (i.choose a : ℝ)
            * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[i - a] v z')) z := by
        intro a ha
        exact (((hFa a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))).mul
          (hGb (i - a) (Nat.sub_le i a))).const_mul _
      have hfun : (fun z' => ∑ a ∈ Finset.range (i + 1),
            (i.choose a : ℝ) * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[i - a] v z'))
          = ∑ a ∈ Finset.range (i + 1),
            (fun z' => (i.choose a : ℝ)
              * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[i - a] v z')) := by
        funext z'
        rw [Finset.sum_apply]
      have hderiv : deriv (Work.Spaces.Zop^[i] (u * v)) z
          = deriv (fun z' => ∑ a ∈ Finset.range (i + 1),
              (i.choose a : ℝ)
                * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[i - a] v z')) z :=
        (hih.deriv hV) hz
      have hkey : Work.Spaces.Zop (Work.Spaces.Zop^[i] (u * v)) z
          = ∑ a ∈ Finset.range (i + 1), z
              * deriv (fun z' => (i.choose a : ℝ)
                * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[i - a] v z')) z := by
        show z * deriv (Work.Spaces.Zop^[i] (u * v)) z
          = ∑ a ∈ Finset.range (i + 1), z
              * deriv (fun z' => (i.choose a : ℝ)
                * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[i - a] v z')) z
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [hkey]
      trans ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
          (Work.Spaces.Zop^[a + 1] u z * Work.Spaces.Zop^[i - a] v z
            + Work.Spaces.Zop^[a] u z * Work.Spaces.Zop^[i - a + 1] v z)
      · exact Finset.sum_congr rfl (fun a ha => Zop_deriv_term u v z i a
          (hFa a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
          (hGb (i - a) (Nat.sub_le i a)))
      · exact Work.Spaces.leibniz_step i (fun b => Work.Spaces.Zop^[b] u z)
          (fun b => Work.Spaces.Zop^[b] v z)

/-- The graded iterated Leibniz rule for `Zop`, pointwise form. -/
theorem Zop_iter_mul_contDiffOn {i : ℕ} {u v : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V)
    (hu : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) u V)
    (hv : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) v V) :
    ∀ z ∈ V, Work.Spaces.Zop^[i] (u * v) z
      = ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)
          * (Work.Spaces.Zop^[a] u z * Work.Spaces.Zop^[i - a] v z) :=
  Zop_iter_mul_aux i u v V hV hu hv

/-! ## Two unconditional identities -/

/-- `deriv` is scalar homogeneous **unconditionally** (Mathlib's `deriv_const_mul` needs
differentiability): if `f` is not differentiable at `x` then neither is `c · f` for `c ≠ 0`,
so both sides are `0`. -/
theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

/-- `D_θ^i` commutes with multiplication by a factor depending only on `z`.  No smoothness
is needed: the only ingredient is the unconditional scalar linearity of `deriv`. -/
theorem DthIter_zmul_rad (i : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => a z * f z θ)
      = fun z θ => a z * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [Work.Spaces.DthIter_succ] at ih ⊢
      rw [ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_uncond]
      ring

/-- The `Zop`-iterates of a one-variable function are the `DzdIter`s of `Work.Elliptic`. -/
theorem Zop_iter_eq_DzdIter (b : ℕ) (r : ℝ → ℝ) :
    Work.Spaces.Zop^[b] r = Work.Elliptic.DzdIter b r := by
  induction b with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Work.Elliptic.DzdIter_succ]
      rfl

/-! ## The two Leibniz rules for a radial factor -/

theorem radLeibniz {R : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hR : ContDiffOn ℝ 5 R (Set.Ioi 0)) (hu : Work.FTS.EllipticEst.SmoothOpen u) :
    (∀ i : ℕ, i ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.DzIter i (fun z θ => R z * u z θ) z θ
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b R z * Work.Spaces.DzIter (i - b) u z θ)) ∧
    (∀ (i j : ℕ), 1 ≤ i → i + j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
        ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.mixed j i (fun z θ => R z * u z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b R z * Work.Spaces.mixed (j - b) i u z θ)) := by
  constructor
  · intro i hi z hz θ hθ
    have hR' : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) R (Set.Ioi (0 : ℝ)) :=
      hR.of_le (Nat.cast_le.mpr (by omega : i + 1 ≤ 5))
    have hB : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) (fun z => u z θ) (Set.Ioi (0 : ℝ)) :=
      curry_z_nat_of_smoothOpen hu hθ (i + 1)
    have hL : Work.Spaces.DzIter i (fun z θ => R z * u z θ) z θ
        = Work.Spaces.Zop^[i] (R * fun z => u z θ) z :=
      congrFun (Work.FTS.LocData.Zop_iterate_slice i (fun z θ => R z * u z θ) θ) z
    have hR2 : Work.Spaces.Zop^[i] (R * fun z => u z θ) z
        = ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)
            * (Work.Spaces.Zop^[a] R z * Work.Spaces.Zop^[i - a] (fun z => u z θ) z) :=
      Zop_iter_mul_contDiffOn isOpen_Ioi hR' hB z hz
    rw [hL, hR2]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [Zop_iter_eq_DzdIter b R,
      ← congrFun (Work.FTS.LocData.Zop_iterate_slice (i - b) u θ) z]
  · intro i j hi hij z hz θ hθ
    have hR' : ContDiffOn ℝ (((j + 1 : ℕ)) : WithTop ℕ∞) R (Set.Ioi (0 : ℝ)) :=
      hR.of_le (Nat.cast_le.mpr (by omega : j + 1 ≤ 5))
    have hB : ContDiffOn ℝ (((j + 1 : ℕ)) : WithTop ℕ∞)
        (fun z => Work.Spaces.DthIter i u z θ) (Set.Ioi (0 : ℝ)) :=
      curry_z_nat_of_smoothOpen (hu.DthIter i) hθ (j + 1)
    have hDth : Work.Spaces.DthIter i (fun z θ => R z * u z θ)
        = fun z θ => R z * Work.Spaces.DthIter i u z θ := DthIter_zmul_rad i R u
    have hL : Work.Spaces.mixed j i (fun z θ => R z * u z θ) z θ
        = Work.Spaces.Zop^[j] (R * fun z => Work.Spaces.DthIter i u z θ) z := by
      show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => R z * u z θ)) z θ
        = Work.Spaces.Zop^[j] (R * fun z => Work.Spaces.DthIter i u z θ) z
      rw [hDth]
      exact congrFun (Work.FTS.LocData.Zop_iterate_slice j
        (fun z θ => R z * Work.Spaces.DthIter i u z θ) θ) z
    have hR2 : Work.Spaces.Zop^[j] (R * fun z => Work.Spaces.DthIter i u z θ) z
        = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)
            * (Work.Spaces.Zop^[a] R z
              * Work.Spaces.Zop^[j - a] (fun z => Work.Spaces.DthIter i u z θ) z) :=
      Zop_iter_mul_contDiffOn isOpen_Ioi hR' hB z hz
    rw [hL, hR2]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hmix : Work.Spaces.mixed (j - b) i u
        = Work.Spaces.DzIter (j - b) (Work.Spaces.DthIter i u) := rfl
    rw [Zop_iter_eq_DzdIter b R,
      ← congrFun (Work.FTS.LocData.Zop_iterate_slice (j - b) (Work.Spaces.DthIter i u) θ) z,
      hmix]

end Work.FTS.GalFields.Norm
