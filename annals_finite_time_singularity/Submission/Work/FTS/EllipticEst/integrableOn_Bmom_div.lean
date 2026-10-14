import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false

/-! ## Elementary closure properties of `SmoothOpen`

These are stated for the (uncurried) `SmoothOpen` of `OpenQDefs`, i.e. `C^∞` on the open
quadrant `Q0 = (0,∞) × (0,π/2)`.  They are the open-quadrant analogues of
`smoothQuad_mul`, `SmoothQuad.DzIter`, ... of `Work.FTS.LocData.SmoothChain`, and of
`Work.FTS.EllipticEst.smoothOpen_add` / `SmoothOpen.const_mul'` / `smoothOpen_sub`
(delivered in `EllHyp_certificates`).  They are proved here directly, so that this module
depends only on `sorry`-free modules. -/

/-- `SmoothOpen` is closed under pointwise addition. -/
theorem smoothOpen_add_bsl {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ + g z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2 + g p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact hf.add hg

/-- `SmoothOpen` is closed under pointwise subtraction. -/
theorem smoothOpen_sub_bsl {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ - g z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2 - g p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact hf.sub hg

/-- `SmoothOpen` is closed under pointwise negation. -/
theorem smoothOpen_neg_bsl {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => -f z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => -f p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact hf.neg

/-- `SmoothOpen` is closed under multiplication by a constant. -/
theorem smoothOpen_const_mul_bsl (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => c * f z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => c * f p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hf

/-- `SmoothOpen` is closed under pointwise multiplication. -/
theorem smoothOpen_mul_bsl {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ * g z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2 * g p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact hf.mul hg

/-- The iterated plain derivative `∂_θ^i` preserves `SmoothOpen`.  (`OpenQDefs` provides the
analogues for `∂_z`, `D_z`, `D_θ` — `SmoothOpen.pzIter`, `SmoothOpen.DzIter`,
`SmoothOpen.DthIter` — but not for `∂_θ`; `Lzero` needs `∂_θ²`.) -/
theorem smoothOpen_pthIter_bsl {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i f) := by
  induction i with
  | zero => simpa using hf
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact Work.FTS.EllipticEst.SmoothOpen.pth ih

/-- Congruence for `SmoothOpen`: a function agreeing with a `SmoothOpen` function on the
open quadrant is `SmoothOpen`. -/
theorem smoothOpen_congr_bsl {f g : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen f)
    (h' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.FTS.EllipticEst.SmoothOpen g := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Work.FTS.EllipticEst.Q0
  refine ContDiffOn.congr h ?_
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact (h' p.1 p.2 hz hθ0 hθ1).symm

/-! ## The concrete factors `z`, `z²` and `tan θ` -/

/-- The coordinate `z` is `C^∞` on the open quadrant. -/
theorem smoothOpen_z_bsl : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun z _ : ℝ => z))
    Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0
  exact contDiffOn_fst

/-- The factor `z²` of the second-order term of `bslOp` is `C^∞` on the open quadrant. -/
theorem smoothOpen_zsq_bsl : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z ^ 2) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun z _ : ℝ => z ^ 2))
    Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2)
    Work.FTS.EllipticEst.Q0
  exact (contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).pow 2

/-- **`tan θ` is `C^∞` on the open quadrant**, i.e. as a function of `(z,θ)` on `Q0`.  It is
`sin/cos` with `cos θ ≠ 0` for `0 < θ < π/2`. -/
theorem smoothOpen_tan_bsl : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun _ : ℝ => Real.tan))
    Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2)
    Work.FTS.EllipticEst.Q0
  have hfun : (fun p : ℝ × ℝ => Real.tan p.2)
      = fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2 := by
    funext p; exact Real.tan_eq_sin_div_cos p.2
  rw [hfun]
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin p.2)
      Work.FTS.EllipticEst.Q0 := by
    change ContDiffOn ℝ Work.Stability.smoothOrder (Real.sin ∘ Prod.snd)
      Work.FTS.EllipticEst.Q0
    exact (Real.contDiff_sin (n := Work.Stability.smoothOrder)).comp_contDiffOn contDiffOn_snd
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.cos p.2)
      Work.FTS.EllipticEst.Q0 := by
    change ContDiffOn ℝ Work.Stability.smoothOrder (Real.cos ∘ Prod.snd)
      Work.FTS.EllipticEst.Q0
    exact (Real.contDiff_cos (n := Work.Stability.smoothOrder)).comp_contDiffOn contDiffOn_snd
  refine ContDiffOn.div hsin hcos ?_
  intro p hp
  obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)

/-! ## `SmoothNbhd` implies `SmoothOpen` -/



/-! ## The certificate -/



end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HkIntegrand_add_le_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The algebraic core: sums of squares of sums -/

private lemma sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    (∑ i ∈ s, (x i + y i) ^ 2) ≤ 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
  calc (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ ∑ i ∈ s, (2 * x i ^ 2 + 2 * y i ^ 2) :=
        Finset.sum_le_sum fun i _ => by
          have h := add_sq_le (a := x i) (b := y i); linarith
    _ = 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The pointwise inequality for the integrand, given the additivity of the iterated operators
at `(z, θ)`. -/
private lemma HkIntegrand_add_le_pt (α : ℝ) (k : ℕ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hz : ∀ i, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ)
    (hm : ∀ i j, Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  have hZ : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have h1 : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range (k + 1),
          ((Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
            + (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz i]; ring
    rw [h1]
    exact sum_sq_add_le _ _ _
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    set S : Finset (ℕ × ℕ) := ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
      (fun p => 1 ≤ p.1 ∧ p.1 + p.2 ≤ k) with hS
    have e : ∀ u : ℝ → ℝ → ℝ,
        (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i u z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = ∑ p ∈ S, (Work.Spaces.mixed p.2 p.1 u z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      intro u
      rw [hS, Finset.sum_filter, Finset.sum_product]
    rw [e f, e g, e (fun z θ => f z θ + g z θ)]
    have hconv : (∑ p ∈ S,
          (Work.Spaces.mixed p.2 p.1 (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2)
        = ∑ p ∈ S, ((Work.Spaces.mixed p.2 p.1 f z θ * Work.Spaces.Wt α z θ)
            + (Work.Spaces.mixed p.2 p.1 g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hm p.1 p.2]; ring
    rw [hconv]
    exact sum_sq_add_le _ _ _
  simp only [Work.Spaces.HkIntegrand]
  linarith [hZ, hM]

/-! ## The theorem -/

/-- **Subadditivity of the `ℋ^k`-integrand for `SmoothOpen` data.**  For `f`, `g` of class
`C^∞` on the open quadrant `(0,∞) × (0,π/2)` and every `(z,θ) ∈ Iz ×ˢ Iθ`,

`HkIntegrand α k (f+g) z θ ≤ 2 · HkIntegrand α k f z θ + 2 · HkIntegrand α k g z θ`. -/
theorem HkIntegrand_add_le_open (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g) {z : ℝ} (hz : z ∈ Work.Spaces.Iz)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  by_cases hz0 : z = 0
  · -- `z = 0`: the integrand vanishes identically
    rw [hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f 0 θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g 0 θ
    linarith
  by_cases hs : Real.sin (2 * θ) = 0
  · -- `sin (2θ) = 0`: the integrand vanishes identically
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
      (fun z θ => f z θ + g z θ) z θ hs]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g z θ
    linarith
  · -- interior point of the quadrant: additivity of the `D`-operators plus the algebra
    have hzge : 0 ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
    have hzpos : 0 < z := lt_of_le_of_ne hzge (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ π / 2 := by
      simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
    have hθ1 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h | h
      · exact absurd (by rw [← h]; simp) hs
      · exact h
    have hθ2 : θ < π / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h | h
      · exact h
      · exact absurd (by rw [h, show (2 : ℝ) * (π / 2) = π from by ring, Real.sin_pi]) hs
    exact HkIntegrand_add_le_pt α k f g z θ
      (fun i => SmoothOpen.DzIter_add hf hg i z θ hzpos hθ1 hθ2)
      (fun i j => SmoothOpen.mixed_add hf hg j i z θ hzpos hθ1 hθ2)

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set Filter
open scoped Real Topology

/-- The angular `L²`-slice `A s = ∫_θ (D_z^j F s θ · w(s)/sin(2θ)^{η/2})²` is the dominating
quantity: by Cauchy–Schwarz (`PsiInt_sq_mul_w_le_open`) it controls the radial moment
`Bmom F j s = PsiInt F j s`, and `integrableOn_slice_l2` shows that it is integrable on every
compact subinterval of `(0,∞)`. -/
theorem integrableOn_Bmom_div (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s / s) (Set.Icc a b) := by
  intro a b ha hab
  -- The dominating quantity: the angular `L²`-slice of the `j`-th weighted `D_z`-summand.
  set A : ℝ → ℝ := fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.DzIter j F s θ * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    with hAdef
  -- (1) `A` is integrable on `[a,b]` (indeed on all of `Iz`).
  have hAint : MeasureTheory.IntegrableOn A (Set.Icc a b) :=
    integrableOn_slice_l2 α k hF hmem j hj a b ha hab
  have hA0 : ∀ s : ℝ, 0 ≤ A s := fun s => integral_nonneg fun θ => sq_nonneg _
  -- (2) Pointwise bound: for `s > 0`, `|Bmom F j s / s| ≤ √(π/2)·(A s + 1)`.
  have hpt : ∀ s : ℝ, 0 < s → ‖Work.FTS.EllipticEst.Bmom F j s / s‖
      ≤ Real.sqrt (Real.pi / 2) * (A s + 1) := by
    intro s hs
    have hcs := PsiInt_sq_mul_w_le_open F hF j hs
      (integrableOn_zSummand α k hF hmem j hj (Set.mem_Ici.mpr (le_of_lt hs)))
    -- `s·w(s) ≥ 1`, hence `w(s)²·s² ≥ 1`
    have hws : 1 ≤ s * Work.Spaces.w s := by
      have heq : s * Work.Spaces.w s = (1 + s) ^ 2 / s := by
        rw [Work.Spaces.w]
        field_simp
      rw [heq, le_div_iff₀ hs]
      nlinarith [sq_nonneg s]
    have hws2 : 1 ≤ (Work.Spaces.w s) ^ 2 * s ^ 2 := by
      have h := mul_le_mul hws hws (by norm_num) (le_trans zero_le_one hws)
      have he : (s * Work.Spaces.w s) * (s * Work.Spaces.w s)
          = (Work.Spaces.w s) ^ 2 * s ^ 2 := by ring
      linarith [h, he]
    have hinv : 1 / s ^ 2 ≤ (Work.Spaces.w s) ^ 2 := by
      rw [div_le_iff₀ (pow_pos hs 2)]
      exact hws2
    -- Cauchy–Schwarz, with the factor `1/s` absorbed by `s·w(s) ≥ 1`
    have hstep : (PsiInt F j s / s) ^ 2 ≤ (PsiInt F j s) ^ 2 * (Work.Spaces.w s) ^ 2 := by
      rw [div_pow, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [one_div] at hinv
      exact hinv
    have hsq : (PsiInt F j s / s) ^ 2 ≤ (Real.pi / 2) * A s := le_trans hstep hcs
    have hsqrt1 : |PsiInt F j s / s| ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (A s) := by
      rw [← Real.sqrt_sq_eq_abs]
      calc Real.sqrt ((PsiInt F j s / s) ^ 2)
          ≤ Real.sqrt ((Real.pi / 2) * A s) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (Real.pi / 2) * Real.sqrt (A s) := Real.sqrt_mul (by positivity) _
    have hsqrt2 : Real.sqrt (A s) ≤ A s + 1 := by
      have h := Real.sq_sqrt (hA0 s)
      nlinarith [h, Real.sqrt_nonneg (A s), sq_nonneg (Real.sqrt (A s) - 1 / 2)]
    rw [Work.FTS.EllipticEst.Bmom, Real.norm_eq_abs]
    calc |PsiInt F j s / s| ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (A s) := hsqrt1
      _ ≤ Real.sqrt (Real.pi / 2) * (A s + 1) :=
          mul_le_mul_of_nonneg_left hsqrt2 (Real.sqrt_nonneg _)
  -- (3) The dominating function `s ↦ √(π/2)·(A s + 1)` is integrable on `[a,b]`.
  have hdom : MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt (Real.pi / 2) * (A s + 1))
      (Set.Icc a b) := by
    have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => A s + 1) (Set.Icc a b) :=
      hAint.add (MeasureTheory.integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    exact h1.const_mul _
  -- (4) Measurability of the target function, by Fubini from the joint measurability of the
  -- uncurried angular integrand on the open quadrant.
  have hmeas : AEStronglyMeasurable (fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s / s)
      (volume.restrict (Set.Icc a b)) := by
    have hsin : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ := by
      unfold Work.Elliptic.sinCos2
      fun_prop
    have hjoint : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.DzIter j F p.1 p.2 * Work.Elliptic.sinCos2 p.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j F p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hF.DzIter j).continuousOn
      have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hsin.comp continuous_snd).continuousOn
      exact Work.Spaces.aesm_of_continuousOn_Qd _ (h1.mul h2)
    have hB : AEStronglyMeasurable (fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s)
        (volume.restrict Work.Spaces.Iz) := by
      have h := hjoint.integral_prod_right' (μ := volume.restrict Work.Spaces.Iz)
        (ν := volume.restrict Work.Spaces.Iθ)
      simpa only [Work.FTS.EllipticEst.Bmom, Work.FTS.EllipticEst.PsiInt] using h
    have hle : (volume.restrict (Set.Icc a b)) ≤ (volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Measure.restrict_mono
        (fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)) le_rfl
    have hB2 : AEStronglyMeasurable (fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s)
        (volume.restrict (Set.Icc a b)) := hB.mono_measure hle
    have h2 : AEStronglyMeasurable (fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s * s⁻¹)
        (volume.restrict (Set.Icc a b)) :=
      hB2.mul (measurable_inv.aestronglyMeasurable :
        AEStronglyMeasurable (fun s : ℝ => s⁻¹) (volume.restrict (Set.Icc a b)))
    have he : (fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s / s)
        = fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s * s⁻¹ := by
      funext s
      exact div_eq_mul_inv _ _
    rw [he]
    exact h2
  -- (5) Domination gives integrability.
  refine hdom.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun s hs => hpt s (lt_of_lt_of_le ha hs.1)

end Work.FTS.EllipticEst
end
