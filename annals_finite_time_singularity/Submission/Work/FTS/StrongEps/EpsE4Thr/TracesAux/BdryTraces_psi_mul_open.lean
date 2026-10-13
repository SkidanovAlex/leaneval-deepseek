import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TracesAux

set_option maxHeartbeats 1600000

/-! ## A factor which depends only on `z` is `SmoothOpen`

`Work.FTS.EllipticEst.SmoothOpen` is genuine `C^∞` (the order `Work.Stability.smoothOrder`) on
the open quadrant `Q0 = (0,∞) × (0,π/2)`.  A function of `z` alone which is `C^∞` on `(0,∞)`
therefore belongs to it. -/

theorem smoothOpen_zOnly {ψ : ℝ → ℝ} (hψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => ψ z) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  exact (hψ n).comp contDiff_fst.contDiffOn
    (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-! ## `Zop = z ∂_z` as a derivation on the smooth functions of `(0,∞)`

This is `Work.FTS.LocData.Zop_DerivLike_smoothZd` with the strip `(-1,∞)` replaced by the
half-line `(0,∞)` — the base set on which `SmoothOpen` gives slice smoothness. -/

/-- The functions of one variable which are `C^∞` on `(0,∞)` in the genuine smooth order
`Work.Stability.smoothOrder = ((⊤ : ℕ∞) : ℕ∞ω)`, *not* in the analytic order `⊤`. -/
def SmoothZsm0 (u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder u (Set.Ioi 0)

/-- `SmoothZsm0` is closed under `+`, `*` and scalar multiples. -/
theorem SmoothZsm0_FunClass : Work.Spaces.FunClass SmoothZsm0 where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun p => c * A p) (Set.Ioi 0)
    exact ContDiffOn.const_smul c hA

/-- **`Zop u = fun z => z · u'(z)`** is a derivation-like operator on the functions `C^∞` on
`(0,∞)`, in the exact sense of `Work.Spaces.DerivLike`. -/
theorem Zop_DerivLike_smoothZ0 :
    Work.Spaces.DerivLike (Set.Ioi (0 : ℝ)) SmoothZsm0 Work.Spaces.Zop where
  add := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    show Work.Spaces.Zop (A + B) z = Work.Spaces.Zop A z + Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    show Work.Spaces.Zop (A * B) z = Work.Spaces.Zop A z * B z + A z * Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    intro z hz
    show Work.Spaces.Zop A z = Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [h.deriv isOpen_Ioi hz]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (fderiv ℝ A) (Set.Ioi 0) :=
      hA.fderiv_of_isOpen isOpen_Ioi (by simp)
    have hev : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (fderiv ℝ A z) 1)
        (Set.Ioi 0) :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z : ℝ => z * (fderiv ℝ A z) 1) (Set.Ioi 0) :=
      (contDiff_id.contDiffOn).mul hev
    refine hfun.congr (fun z hz => ?_)
    show Work.Spaces.Zop A z = z * (fderiv ℝ A z) 1
    simp only [Work.Spaces.Zop]
    rw [fderiv_apply_one_eq_deriv]
  smul := fun c A hA => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    show Work.Spaces.Zop (fun p => c * A p) z = c * Work.Spaces.Zop A z
    simp only [Work.Spaces.Zop]
    rw [deriv_const_mul c hA']
    ring

/-! ## Two elementary facts about `D_θ` and a `z`-only factor -/

/-- `deriv` is scalar homogeneous **unconditionally**, unlike Mathlib's `deriv_const_mul`,
which needs differentiability: if `f` is not differentiable at `x` then neither is `c * f`
for `c ≠ 0`, so both sides are `0`. -/
private theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
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

/-- `D_θ^i` commutes with multiplication by a factor depending only on `z`.  No smoothness is
needed: the only ingredient is the unconditional scalar linearity of `deriv`. -/
private theorem DthIter_zmul0 (i : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
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

/-! ## The Leibniz expansion with a `z`-only factor, on the open quadrant -/

/-- **Leibniz expansion (open quadrant) of a mixed derivative of a product with a `z`-only
factor.**  For `ψ : ℝ → ℝ` of class `C^∞` on `(0,∞)` and `x` of class `SmoothOpen`, and for
`z > 0`, `θ ∈ (0,π/2)`,
`D_z^j D_θ^i(ψ·x)(z,θ) = ∑_{b ≤ j} C(j,b)·(Zop^b ψ)(z)·(D_z^{j-b}D_θ^i x)(z,θ)`.

`D_θ^i` commutes with the `z`-only factor (`DthIter_zmul0`, no smoothness needed), which reduces
the claim to the single-operator Leibniz rule for `Zop` on the `z`-slice; there both factors are
`C^∞` on `(0,∞)` (`SmoothZsm0`), so `Work.Spaces.DerivLike.iterate_mul` applies with the
instance `Zop_DerivLike_smoothZ0`, and `Work.FTS.LocData.Zop_iterate_slice` identifies the
iterates of `Zop` with the slices of the `D_z`-iterates. -/
theorem mixed_zmul_zOnly (j i : ℕ) (ψ : ℝ → ℝ) (x : ℝ → ℝ → ℝ)
    (hψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioi 0))
    (hx : Work.FTS.EllipticEst.SmoothOpen x)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.mixed j i (fun z θ : ℝ => ψ z * x z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (Work.Spaces.Zop^[b] ψ z * Work.Spaces.mixed (j - b) i x z θ) := by
  have hψs : SmoothZsm0 ψ := by
    show ContDiffOn ℝ Work.Stability.smoothOrder ψ (Set.Ioi 0)
    exact contDiffOn_iff_forall_nat_le.mpr (fun m _ => hψ m)
  have hxs : SmoothZsm0 (fun z : ℝ => Work.Spaces.DthIter i x z θ) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.Spaces.DthIter i x z θ) (Set.Ioi 0)
    exact (hx.DthIter i).curry_z hθ
  have key := (Work.Spaces.DerivLike.iterate_mul Zop_DerivLike_smoothZ0 SmoothZsm0_FunClass
    j hψs hxs) hz
  have hL : Work.Spaces.mixed j i (fun z θ : ℝ => ψ z * x z θ) z θ
      = Work.Spaces.Zop^[j] (ψ * (fun z : ℝ => Work.Spaces.DthIter i x z θ)) z := by
    rw [Work.Spaces.mixed, DthIter_zmul0 i ψ x]
    exact congrFun (Work.FTS.LocData.Zop_iterate_slice j
      (fun z θ => ψ z * Work.Spaces.DthIter i x z θ) θ) z
  rw [hL, key]
  apply Finset.sum_congr rfl
  intro b hb
  have h1 : Work.Spaces.Zop^[b] (fun z : ℝ => ψ z) z = Work.Spaces.Zop^[b] ψ z := rfl
  have h2 : Work.Spaces.Zop^[j - b] (fun z : ℝ => Work.Spaces.DthIter i x z θ) z
      = Work.Spaces.mixed (j - b) i x z θ := by
    rw [Work.Spaces.mixed]
    exact (congrFun (Work.FTS.LocData.Zop_iterate_slice (j - b)
      (Work.Spaces.DthIter i x) θ) z).symm
  rw [h1, h2]

/-! ## The pointwise bound -/

/-- **Pointwise bound for the mixed derivative of a radial multiple.**  For `z > 0` and
`0 < θ < π/2`, the square of any mixed derivative `D_z^bD_θ^a(ψ·x)`, weighted by an arbitrary
nonnegative factor `ρ`, is bounded by `(b+1)` times the corresponding combination of the mixed
derivatives of `x` (weighted by `ρ`), with coefficients `(C(b,c)·K)²`. -/
theorem mixed_psi_mul_sq_le_open {k : ℕ} {ψ : ℝ → ℝ} {K ρ : ℝ} (hK : 0 ≤ K) (hρ : 0 ≤ ρ)
    (hKb : ∀ c ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[c] ψ z| ≤ K)
    (hψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioi 0))
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {a b : ℕ} (hab : a + b ≤ k) {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ))
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ * (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2 ≤
      ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
        ((b.choose c : ℝ) * K) ^ 2 * (ρ * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) := by
  have hcore : (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2 ≤
      ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
        ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2 := by
    rw [mixed_zmul_zOnly b a ψ g hψ hg hz hθ]
    calc (∑ c ∈ Finset.range (b + 1),
            (b.choose c : ℝ) * (Work.Spaces.Zop^[c] ψ z * Work.Spaces.mixed (b - c) a g z θ)) ^ 2
        ≤ ((Finset.range (b + 1)).card : ℝ) * ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * (Work.Spaces.Zop^[c] ψ z
              * Work.Spaces.mixed (b - c) a g z θ)) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * (Work.Spaces.Zop^[c] ψ z
              * Work.Spaces.mixed (b - c) a g z θ)) ^ 2 := by
          simp
      _ ≤ ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Finset.sum_le_sum fun c hc => ?_
          have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
          have hsq : (Work.Spaces.Zop^[c] ψ z) ^ 2 ≤ K ^ 2 := by
            have h := pow_le_pow_left₀ (abs_nonneg (Work.Spaces.Zop^[c] ψ z))
              (hKb c (by omega) z hz) 2
            rwa [sq_abs] at h
          have e1 : ((b.choose c : ℝ) * (Work.Spaces.Zop^[c] ψ z
                * Work.Spaces.mixed (b - c) a g z θ)) ^ 2
              = ((b.choose c : ℝ) ^ 2 * (Work.Spaces.Zop^[c] ψ z) ^ 2)
                * (Work.Spaces.mixed (b - c) a g z θ) ^ 2 := by ring
          have e2 : ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2
              = ((b.choose c : ℝ) ^ 2 * K ^ 2)
                * (Work.Spaces.mixed (b - c) a g z θ) ^ 2 := by ring
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) (sq_nonneg _)
  calc ρ * (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2
      ≤ ρ * (((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcore hρ
    _ = ((b : ℝ) + 1) * (ρ * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) := by ring
    _ = ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 * (ρ * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) := by
        rw [Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun c _ => by ring

/-! ## The four traces -/

/-- **`BdryTraces` is preserved by multiplication with a bounded radial multiplier**
(open-quadrant version of `Work.FTS.CoercivityFix.PsiMul.BdryTraces_psi_mul`, which asks for
`SmoothQuad` of the factor and of the datum, i.e. `C^∞` on the *strip* `z > -1`).

For `ψ : ℝ → ℝ` of class `C^∞` on `(0,∞)` whose `Zop`-iterates `Zop^c ψ = (z∂_z)^c ψ`
(`Work.Spaces.Zop`) are bounded by `K` up to order `k`, and `x` of class `SmoothOpen`
(`C^∞` on the *open quadrant* `(0,∞) × (0,π/2)`) with `BdryTraces α k x`, the product
`(z,θ) ↦ ψ(z)·x(z,θ)` again has `BdryTraces α k`.

Route: `OpenPkg.ProdOpen.leibniz_open_mixed` expands the mixed derivative of the product of
two `SmoothOpen` factors on the quadrant; since `(z,θ) ↦ ψ z` is `SmoothOpen` (from `hψ`),
the terms with `a > 0` vanish and the expansion collapses to
`D_z^bD_θ^a(ψ·x) = Σ_{c≤b} C(b,c)·(Zop^c ψ)(z)·(D_z^{b-c}D_θ^a x)(z,θ)`,
in which every slot `(a, b-c)` has `a + (b-c) ≤ a + b ≤ k`, so the four traces of the product
are squeezed between `0` and a finite combination of the traces of `x`. -/
theorem BdryTraces_psi_mul_open {α : ℝ} (k : ℕ) {ψ : ℝ → ℝ} {K : ℝ}
    {x : Work.FTS.Galerkin.Fn}
    (hK : 0 ≤ K)
    (hZ : ∀ c : ℕ, c ≤ k → ∀ z : ℝ, 0 < z → |Work.Spaces.Zop^[c] ψ z| ≤ K)
    (hψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioi 0))
    (hxsm : Work.FTS.EllipticEst.SmoothOpen x)
    (hx : Work.FTS.Nonlin.BdryTraces α k x) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => ψ z * x z θ) := by
  have hKb : ∀ c ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[c] ψ z| ≤ K :=
    fun c hc z hz => hZ c hc z hz
  -- the two angular intervals are eventually true along the two one-sided filters
  have hIoo0 : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioo (-1) (π / 2), isOpen_Ioo,
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      fun x hx => ⟨hx.2, hx.1.2⟩⟩
  have hIooπ : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[<] (π / 2) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioo (π / 4) (π / 2 + 1), isOpen_Ioo,
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      fun x hx => ⟨by linarith [hx.1.1, Real.pi_pos], hx.2⟩⟩
  intro a b hab
  refine ⟨?_, ?_⟩
  · intro θ hθ
    refine ⟨?_, ?_⟩
    · -- radial trace at `z → 0⁺`
      refine squeeze_zero'
        (g := fun z => ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 *
            (z * (Work.Spaces.mixed (b - c) a x z θ * Work.Spaces.w z) ^ 2)) ?_ ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact mul_nonneg (le_of_lt hz) (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin] with z hz
        have hbnd : (z * (Work.Spaces.w z) ^ 2) *
              (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ) ^ 2 ≤
              ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  ((z * (Work.Spaces.w z) ^ 2) * (Work.Spaces.mixed (b - c) a x z θ) ^ 2) :=
          mixed_psi_mul_sq_le_open hK
            (mul_nonneg (le_of_lt hz) (sq_nonneg (Work.Spaces.w z))) hKb hψ hxsm hab hz hθ
        calc z * (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ * Work.Spaces.w z) ^ 2
            = (z * (Work.Spaces.w z) ^ 2) *
                (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ) ^ 2 := by ring
          _ ≤ ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 * ((z * (Work.Spaces.w z) ^ 2) *
                  (Work.Spaces.mixed (b - c) a x z θ) ^ 2) := hbnd
          _ = ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  (z * (Work.Spaces.mixed (b - c) a x z θ * Work.Spaces.w z) ^ 2) := by
              congr 1
              exact Finset.sum_congr rfl fun c _ => by ring
      · have hsum : Tendsto (fun z => ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 *
              (z * (Work.Spaces.mixed (b - c) a x z θ * Work.Spaces.w z) ^ 2))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have h := tendsto_finsetSum (Finset.range (b + 1)) (fun c hc => by
            have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            exact (((hx a (b - c) (by omega)).1 θ hθ).1).const_mul
              (((b.choose c : ℝ) * K) ^ 2))
          simpa using h
        simpa using hsum.const_mul ((b : ℝ) + 1)
    · -- radial trace at `z → ∞`
      refine squeeze_zero'
        (g := fun z => ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 *
            (z * (Work.Spaces.mixed (b - c) a x z θ * Work.Spaces.w z) ^ 2)) ?_ ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        exact mul_nonneg (le_of_lt hz) (sq_nonneg _)
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        have hbnd : (z * (Work.Spaces.w z) ^ 2) *
              (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ) ^ 2 ≤
              ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  ((z * (Work.Spaces.w z) ^ 2) * (Work.Spaces.mixed (b - c) a x z θ) ^ 2) :=
          mixed_psi_mul_sq_le_open hK
            (mul_nonneg (le_of_lt hz) (sq_nonneg (Work.Spaces.w z))) hKb hψ hxsm hab hz hθ
        calc z * (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ * Work.Spaces.w z) ^ 2
            = (z * (Work.Spaces.w z) ^ 2) *
                (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ) ^ 2 := by ring
          _ ≤ ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 * ((z * (Work.Spaces.w z) ^ 2) *
                  (Work.Spaces.mixed (b - c) a x z θ) ^ 2) := hbnd
          _ = ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  (z * (Work.Spaces.mixed (b - c) a x z θ * Work.Spaces.w z) ^ 2) := by
              congr 1
              exact Finset.sum_congr rfl fun c _ => by ring
      · have hsum : Tendsto (fun z => ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 *
              (z * (Work.Spaces.mixed (b - c) a x z θ * Work.Spaces.w z) ^ 2))
            atTop (𝓝 0) := by
          have h := tendsto_finsetSum (Finset.range (b + 1)) (fun c hc => by
            have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            exact (((hx a (b - c) (by omega)).1 θ hθ).2).const_mul
              (((b.choose c : ℝ) * K) ^ 2))
          simpa using h
        simpa using hsum.const_mul ((b : ℝ) + 1)
  · intro z hz
    refine ⟨?_, ?_⟩
    · -- angular trace at `θ → 0⁺`
      refine squeeze_zero'
        (g := fun θ => ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 *
            (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b - c) a x z θ) ^ 2)) ?_ ?_ ?_
      · filter_upwards [hIoo0] with θ hθ
        have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))) _
        exact mul_nonneg hsin (sq_nonneg _)
      · filter_upwards [hIoo0] with θ hθ
        have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))) _
        have hbnd : Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
              (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ) ^ 2 ≤
              ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                    * (Work.Spaces.mixed (b - c) a x z θ) ^ 2) :=
          mixed_psi_mul_sq_le_open hK hsin hKb hψ hxsm hab hz hθ
        exact hbnd
      · have hsum : Tendsto (fun θ => ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 *
              (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                * (Work.Spaces.mixed (b - c) a x z θ) ^ 2))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have h := tendsto_finsetSum (Finset.range (b + 1)) (fun c hc => by
            have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            exact (((hx a (b - c) (by omega)).2 z hz).1).const_mul
              (((b.choose c : ℝ) * K) ^ 2))
          simpa using h
        simpa using hsum.const_mul ((b : ℝ) + 1)
    · -- angular trace at `θ → (π/2)⁻`
      refine squeeze_zero'
        (g := fun θ => ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 *
            (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b - c) a x z θ) ^ 2)) ?_ ?_ ?_
      · filter_upwards [hIooπ] with θ hθ
        have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))) _
        exact mul_nonneg hsin (sq_nonneg _)
      · filter_upwards [hIooπ] with θ hθ
        have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))) _
        have hbnd : Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
              (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ) ^ 2 ≤
              ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                    * (Work.Spaces.mixed (b - c) a x z θ) ^ 2) :=
          mixed_psi_mul_sq_le_open hK hsin hKb hψ hxsm hab hz hθ
        exact hbnd
      · have hsum : Tendsto (fun θ => ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 *
              (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                * (Work.Spaces.mixed (b - c) a x z θ) ^ 2))
            (𝓝[<] (π / 2)) (𝓝 0) := by
          have h := tendsto_finsetSum (Finset.range (b + 1)) (fun c hc => by
            have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            exact (((hx a (b - c) (by omega)).2 z hz).2).const_mul
              (((b.choose c : ℝ) * K) ^ 2))
          simpa using h
        simpa using hsum.const_mul ((b : ℝ) + 1)

end Work.FTS.StrongEps.EpsE4Thr.TracesAux
