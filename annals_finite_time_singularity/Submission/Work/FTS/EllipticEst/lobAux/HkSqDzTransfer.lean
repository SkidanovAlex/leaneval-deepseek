/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `ℋ^k`-transfer of the elliptic equation solved for `D_z Ψ` (`heqB` of `lowerOrderPieces`)

The elliptic operator of Elgindi's §'Elliptic Regularity Estimates' (PolarBSL) is

  `bslOp α Ψ = -α²z²∂_z²Ψ - α(5+α)z∂_zΨ + Lzero Ψ`,

so on the open quadrant the elliptic law `bslOp α Ψ = F` can be *solved for the radial
derivative* `D_z Ψ = z∂_zΨ`:

  `α(5+α)·D_z Ψ = Lzero Ψ - F - α²·(z²∂_z²Ψ)`  on `Q0`.

Since `HkSq α k` is the iterated integral of a sum of squares of *linear* functionals
(`Work.Spaces.HkIntegrand`), and since all the input functions agree on the open quadrant
`Q0` (a set whose complement in the quadrant `[0,∞) × [0,π/2]` is null), squaring the
identity gives the `ℋ^k`-level transfer proved here:

  `α² |D_z Ψ|_{ℋ^k}² ≤ 3 (|Lzero Ψ|_{ℋ^k}² + |F|_{ℋ^k}² + α⁴ |z²∂_z²Ψ|_{ℋ^k}²)`.

The constant `3` is `1/(5+α)² · 3 ≤ 3`, the `3` being the three-term Cauchy–Schwarz bound
`(a-b-c)² ≤ 3(a²+b²+c²)`.

## How the pointwise statement is turned into an integral statement

`Work.Spaces.HkSq α k f = ∫_z∈Iz ∫_θ∈Iθ HkIntegrand α k f z θ`, and the value of the
integral is the junk value `0` for a non-integrable integrand.  The transfer is therefore
proved *at the level of the integrand*, pointwise on the whole closed quadrant:

* on the interior `(z,θ) ∈ Q0` the two functions `(α(5+α))·D_z Ψ` and
  `Lzero Ψ - F - α²z²∂_z²Ψ` agree on an open neighbourhood, so by the locality of the
  iterated `D`-operators all their `ℋ^k`-summands agree, and the pointwise
  three-term Cauchy–Schwarz bound `HkIntegrand_sub3_le` applies;
* on the two boundary lines the integrand vanishes identically
  (`HkIntegrand_eq_zero_of_z_eq_zero`, `HkIntegrand_eq_zero_of_sin`).

The integrand is then integrated against the dominating combination of
`HkMem`-certificates (`HkSq_le_of_integrand_le`), which is integrable exactly because the
three functions on the right are honest elements of `ℋ^k` (that is the role of the three
`HkMem` hypotheses of the statement).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.lobAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

open Work.FTS.EllipticEst

/-! ## Homogeneity of `HkSq` in the amplitude (with no `HkMem` hypothesis) -/

/-- `HkSq` is homogeneous of degree two in the amplitude.  The `HkIntegrand`-level identity is
`Work.FTS.LocData.HkIntegrand_const_mul`; the passage to the iterated integral uses only the
(unconditional) linearity of the Lebesgue integral in a constant factor, so no `HkMem`
hypothesis is needed — unlike `Work.FTS.LocData.HkSq_const_mul`, which carries one because its
callers have it. -/
theorem HkSq_const_mul_unc (α : ℝ) (k : ℕ) (β : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => β * f z θ) = β ^ 2 * Work.Spaces.HkSq α k f := by
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ)
        = β ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z
    rw [funext fun θ => Work.FTS.LocData.HkIntegrand_const_mul α k β f z θ]
    exact integral_const_mul (β ^ 2) _
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  simp only [hinner]
  exact integral_const_mul (β ^ 2) _

/-! ## Smoothness of the pieces on the open quadrant -/

/-- `Lzero Ψ = -∂_θ²Ψ + ∂_θ(tan θ·Ψ) - 6Ψ` is `C^∞` on the open quadrant whenever `Ψ` is
(`tan` is smooth there because `cos θ ≠ 0` for `0 < θ < π/2`). -/
theorem smoothOpen_lzero (Ψ : ℝ → ℝ → ℝ) (hΨ : SmoothOpen Ψ) :
    SmoothOpen (Work.Elliptic.Lzero Ψ) := by
  have htan : SmoothOpen (fun _ : ℝ => Real.tan) := Cert.smoothOpen_tan_bsl
  have htΨ : SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Cert.smoothOpen_mul_bsl htan hΨ
  have hcomp : SmoothOpen
      (fun z θ => -(Work.Spaces.pthIter 2 Ψ z θ)
        + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ) :=
    Cert.smoothOpen_sub_bsl
      (Cert.smoothOpen_add_bsl
        (Cert.smoothOpen_neg_bsl (Cert.smoothOpen_pthIter_bsl hΨ 2))
        (Cert.smoothOpen_pthIter_bsl htΨ 1))
      (Cert.smoothOpen_const_mul_bsl 6 hΨ)
  exact Cert.smoothOpen_congr_bsl hcomp
    (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ,
      Work.Spaces.pthIter_zero, Work.Spaces.pth])

/-! ## The elliptic law solved for `D_z Ψ` -/

/-- The elliptic operator in the `D_z`-form: on the open quadrant

  `bslOp α Ψ = Lzero Ψ - α(5+α)·D_z Ψ - α²·(z²∂_z²Ψ)`,

the identity obtained from `bslOp α Ψ = -α²z²∂_z²Ψ - α(5+α)z∂_zΨ + Lzero Ψ` by writing
`z∂_zΨ = D_z Ψ`.  Purely definitional — no differentiability of `Ψ` is needed. -/
theorem bslOp_eq_split (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.bslOp α Ψ z θ
      = Work.Elliptic.Lzero Ψ z θ - (α * (5 + α)) * Work.Spaces.Dz Ψ z θ
        - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
  rw [Work.Elliptic.bslOp_apply]
  simp only [Work.Spaces.Dz]
  ring

/-! ## Locality and linearity of the iterated operators on the open quadrant

The `SmoothOpen`-closed iterated `D`-operators are linear on `Q0`; `SmoothOpenAdd` provides
the additive form, the subtractive form is redone here in the same style. -/

/-- Two functions agreeing on the open quadrant have the same iterated `D_θ`-derivatives
there.  (Locality of `D_θ`; no smoothness is needed.) -/
theorem DthIter_congr_open {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i F z θ = Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun θ' => Work.Spaces.DthIter n F z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n G z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨h1, h2⟩)]
          with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq]

/-- Two functions agreeing on the open quadrant have the same mixed derivatives there. -/
theorem mixed_congr_open {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (j i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i F z θ = Work.Spaces.mixed j i G z θ :=
  SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i F) (G := Work.Spaces.DthIter i G)
    (DthIter_congr_open h i) j

/-- The iterated `D_z`-operator is additive for `-` on the open quadrant for `SmoothOpen`
data.  (The subtraction counterpart of `SmoothOpen.DzIter_add`.) -/
theorem DzIter_sub_open {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) (j : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter j (fun z θ => f z θ - g z θ) z θ
        = Work.Spaces.DzIter j f z θ - Work.Spaces.DzIter j g z θ := by
  induction j with
  | zero => intro z θ hz h1 h2; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ - g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n f z' θ - Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        ((hf.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n g z' θ) z :=
        ((hg.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd : deriv (fun z' => Work.Spaces.DzIter n f z' θ - Work.Spaces.DzIter n g z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
            - deriv (fun z' => Work.Spaces.DzIter n g z' θ) z := deriv_sub hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- The iterated `D_θ`-operator is additive for `-` on the open quadrant for `SmoothOpen`
data. -/
theorem DthIter_sub_open {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i (fun z θ => f z θ - g z θ) z θ
        = Work.Spaces.DthIter i f z θ - Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨h1, h2⟩
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => f z θ - g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n f z θ' - Work.Spaces.DthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n f z θ') θ :=
        (((hf.DthIter n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n g z θ') θ :=
        (((hg.DthIter n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd : deriv (fun θ' => Work.Spaces.DthIter n f z θ' - Work.Spaces.DthIter n g z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ
            - deriv (fun θ' => Work.Spaces.DthIter n g z θ') θ := deriv_sub hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

/-- The mixed operators `D_z^j D_θ^i` are additive for `-` on the open quadrant for
`SmoothOpen` data. -/
theorem mixed_sub_open {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) (j i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i (fun z θ => f z θ - g z θ) z θ
        = Work.Spaces.mixed j i f z θ - Work.Spaces.mixed j i g z θ := by
  intro z θ hz h1 h2
  have hcongr := SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i (fun z θ => f z θ - g z θ))
    (G := fun z θ => Work.Spaces.DthIter i f z θ - Work.Spaces.DthIter i g z θ)
    (fun z θ hz h1 h2 => DthIter_sub_open hf hg i z θ hz h1 h2) j z θ hz h1 h2
  have hadd := DzIter_sub_open (hf.DthIter i) (hg.DthIter i) j z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-! ## Congruence of the `ℋ^k`-integrand on the open quadrant -/

/-- Two functions which agree on the open quadrant have the same `ℋ^k`-integrand
there. -/
theorem HkIntegrand_congr_open (α : ℝ) (k : ℕ) {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.HkIntegrand α k F z θ = Work.Spaces.HkIntegrand α k G z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      rw [SmoothOpen.DzIter_congr h i z θ hz hθ0 hθ1]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mixed_congr_open h j i z θ hz hθ0 hθ1]

/-! ## Vanishing of the `ℋ^k`-integrand on the boundary of the quadrant -/

theorem DthIter_succ_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    (m : ℕ) (z : ℝ) : Work.Spaces.DthIter (m + 1) f z θ = 0 := by
  simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth, hs, zero_mul]

theorem DzIter_eq_zero_of_slice (f : ℝ → ℝ → ℝ) {θ : ℝ} (h : ∀ z, f z θ = 0) :
    ∀ (j : ℕ) (z : ℝ), Work.Spaces.DzIter j f z θ = 0 := by
  intro j
  induction j with
  | zero => intro z; exact h z
  | succ n ih =>
      intro z
      have hslice : (fun z' => Work.Spaces.DzIter n f z' θ) = fun _ => (0 : ℝ) := funext ih
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [hslice]
      simp

theorem mixed_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    {j i : ℕ} (hi : 1 ≤ i) (z : ℝ) : Work.Spaces.mixed j i f z θ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simp only [Work.Spaces.mixed]
  exact DzIter_eq_zero_of_slice (Work.Spaces.DthIter (m + 1) f) (θ := θ)
    (fun z' => DthIter_succ_eq_zero_of_sin f hs m z') j z

/-- The `ℋ^k`-integrand vanishes on the angular boundary `sin(2θ) = 0`: the first sum is
killed by the `1/sin(2θ)^{η/2}` factor and the second by the `D_θ`-factors of all its
summands (all of them carry `i ≥ 1`). -/
theorem HkIntegrand_eq_zero_of_sin (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [mixed_eq_zero_of_sin f hs hc.1 z, zero_mul, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-- The `ℋ^k`-integrand vanishes on the radial boundary `z = 0` (where `w 0 = 0`). -/
theorem HkIntegrand_eq_zero_of_z_eq_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [Work.Spaces.w, Work.Spaces.Wt, Work.Spaces.wTheta]

/-! ## The pointwise three-term Cauchy–Schwarz bound for the `ℋ^k`-integrand -/

theorem sub3_sq_le (a b c : ℝ) : (a - b - c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b - c)]

theorem sum_sq_sub3_le {ι : Type*} (s : Finset ι) (x y w : ι → ℝ) :
    (∑ i ∈ s, (x i - y i - w i) ^ 2)
      ≤ 3 * ((∑ i ∈ s, x i ^ 2) + (∑ i ∈ s, y i ^ 2) + (∑ i ∈ s, w i ^ 2)) := by
  calc (∑ i ∈ s, (x i - y i - w i) ^ 2)
      ≤ ∑ i ∈ s, 3 * (x i ^ 2 + y i ^ 2 + w i ^ 2) :=
        Finset.sum_le_sum fun i _ => sub3_sq_le _ _ _
    _ = 3 * ((∑ i ∈ s, x i ^ 2) + (∑ i ∈ s, y i ^ 2) + (∑ i ∈ s, w i ^ 2)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- The `ℋ^k`-integrand of a difference, given the pointwise linearity of the iterated
operators at `(z,θ)`. -/
private theorem HkIntegrand_sub3_le_pt (α : ℝ) (k : ℕ) (A B C : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hDz : ∀ i, Work.Spaces.DzIter i (fun z θ => A z θ - B z θ - C z θ) z θ
      = Work.Spaces.DzIter i A z θ - Work.Spaces.DzIter i B z θ
        - Work.Spaces.DzIter i C z θ)
    (hMx : ∀ j i, Work.Spaces.mixed j i (fun z θ => A z θ - B z θ - C z θ) z θ
      = Work.Spaces.mixed j i A z θ - Work.Spaces.mixed j i B z θ
        - Work.Spaces.mixed j i C z θ) :
    Work.Spaces.HkIntegrand α k (fun z θ => A z θ - B z θ - C z θ) z θ
      ≤ 3 * (Work.Spaces.HkIntegrand α k A z θ + Work.Spaces.HkIntegrand α k B z θ
          + Work.Spaces.HkIntegrand α k C z θ) := by
  have hZ : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => A z θ - B z θ - C z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 3 * ((∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i A z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i B z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i C z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)) := by
    have hconv : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => A z θ - B z θ - C z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range (k + 1),
          (((Work.Spaces.DzIter i A z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
              - (Work.Spaces.DzIter i B z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            - (Work.Spaces.DzIter i C z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hDz i]; ring
    rw [hconv]
    exact sum_sq_sub3_le _ _ _ _
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => A z θ - B z θ - C z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 3 * ((∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i C z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))) := by
    set S : Finset (ℕ × ℕ) := ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
      (fun p => 1 ≤ p.1 ∧ p.1 + p.2 ≤ k) with hS
    have e : ∀ u : ℝ → ℝ → ℝ,
        (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i u z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = ∑ p ∈ S, (Work.Spaces.mixed p.2 p.1 u z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      intro u
      rw [hS, Finset.sum_filter, Finset.sum_product]
    rw [e (fun z θ => A z θ - B z θ - C z θ), e A, e B, e C]
    have hconv : (∑ p ∈ S,
          (Work.Spaces.mixed p.2 p.1 (fun z θ => A z θ - B z θ - C z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2)
        = ∑ p ∈ S, ((Work.Spaces.mixed p.2 p.1 A z θ * Work.Spaces.Wt α z θ)
            - (Work.Spaces.mixed p.2 p.1 B z θ * Work.Spaces.Wt α z θ)
            - (Work.Spaces.mixed p.2 p.1 C z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hMx p.2 p.1]; ring
    rw [hconv]
    exact sum_sq_sub3_le _ _ _ _
  simp only [Work.Spaces.HkIntegrand]
  linarith [hZ, hM]

/-- **The three-term pointwise bound for the `ℋ^k`-integrand** on the open quadrant: the
integrand is a sum of squares of linear functionals, so `(a-b-c)² ≤ 3(a²+b²+c²)` applies
termwise.  The constant `3` is sharp. -/
theorem HkIntegrand_sub3_le (α : ℝ) (k : ℕ) {A B C : ℝ → ℝ → ℝ}
    (hA : SmoothOpen A) (hB : SmoothOpen B) (hC : SmoothOpen C)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.HkIntegrand α k (fun z θ => A z θ - B z θ - C z θ) z θ
      ≤ 3 * (Work.Spaces.HkIntegrand α k A z θ + Work.Spaces.HkIntegrand α k B z θ
          + Work.Spaces.HkIntegrand α k C z θ) := by
  refine HkIntegrand_sub3_le_pt α k A B C z θ (fun i => ?_) (fun j i => ?_)
  · have h1 : Work.Spaces.DzIter i (fun z θ => A z θ - B z θ - C z θ) z θ
        = Work.Spaces.DzIter i (fun z θ => A z θ - B z θ) z θ
          - Work.Spaces.DzIter i C z θ :=
      DzIter_sub_open (f := fun z θ => A z θ - B z θ) (g := C)
        (Cert.smoothOpen_sub_bsl hA hB) hC i z θ hz hθ0 hθ1
    have h2 : Work.Spaces.DzIter i (fun z θ => A z θ - B z θ) z θ
        = Work.Spaces.DzIter i A z θ - Work.Spaces.DzIter i B z θ :=
      DzIter_sub_open hA hB i z θ hz hθ0 hθ1
    rw [h1, h2]
  · have h1 : Work.Spaces.mixed j i (fun z θ => A z θ - B z θ - C z θ) z θ
        = Work.Spaces.mixed j i (fun z θ => A z θ - B z θ) z θ
          - Work.Spaces.mixed j i C z θ :=
      mixed_sub_open (f := fun z θ => A z θ - B z θ) (g := C)
        (Cert.smoothOpen_sub_bsl hA hB) hC j i z θ hz hθ0 hθ1
    have h2 : Work.Spaces.mixed j i (fun z θ => A z θ - B z θ) z θ
        = Work.Spaces.mixed j i A z θ - Work.Spaces.mixed j i B z θ :=
      mixed_sub_open hA hB j i z θ hz hθ0 hθ1
    rw [h1, h2]

/-! ## The pointwise transfer on the open quadrant -/

/-- **The pointwise transfer of the elliptic law solved for `D_z Ψ`.**  On `Q0` the law
`bslOp α Ψ = F` gives `(α(5+α))·D_z Ψ = Lzero Ψ - F - α²z²∂_z²Ψ`; hence, using the congruence
of the `ℋ^k`-integrand on the open quadrant and the three-term pointwise bound of
`HkIntegrand_sub3_le`, the `ℋ^k`-integrand of `(α(5+α))·D_z Ψ` is dominated by the three
source integrands. -/
theorem HkIntegrand_transfer_pt {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hbsl : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hΨ : SmoothOpen Ψ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.HkIntegrand α k (fun z θ => (α * (5 + α)) * Work.Spaces.Dz Ψ z θ) z θ
      ≤ 3 * (Work.Spaces.HkIntegrand α k (Work.Elliptic.Lzero Ψ) z θ
          + Work.Spaces.HkIntegrand α k F z θ
          + α ^ 4 * Work.Spaces.HkIntegrand α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) := by
  have hAsm : SmoothOpen (Work.Elliptic.Lzero Ψ) := smoothOpen_lzero Ψ hΨ
  have hBsm : SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ
  have hGsm : SmoothOpen (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Cert.smoothOpen_mul_bsl Cert.smoothOpen_zsq_bsl (hΨ.pzIter 2)
  have hCsm : SmoothOpen (fun z θ : ℝ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    Cert.smoothOpen_const_mul_bsl (α ^ 2) hGsm
  have hcongr : Work.Spaces.HkIntegrand α k
        (fun z θ => (α * (5 + α)) * Work.Spaces.Dz Ψ z θ) z θ
      = Work.Spaces.HkIntegrand α k
        (fun z θ => Work.Elliptic.Lzero Ψ z θ - Work.Elliptic.bslOp α Ψ z θ
          - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ :=
    HkIntegrand_congr_open α k (fun z θ hz' h1 h2 => by rw [bslOp_eq_split]; ring) hz hθ0 hθ1
  have h3 := HkIntegrand_sub3_le α k hAsm hBsm hCsm hz hθ0 hθ1
  have hBF : Work.Spaces.HkIntegrand α k (Work.Elliptic.bslOp α Ψ) z θ
      = Work.Spaces.HkIntegrand α k F z θ :=
    HkIntegrand_congr_open α k (fun z θ hz' h1 h2 => hbsl z hz' θ h1 h2) hz hθ0 hθ1
  have hCeq : Work.Spaces.HkIntegrand α k
        (fun z θ : ℝ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
      = α ^ 4 * Work.Spaces.HkIntegrand α k
          (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
    rw [Work.FTS.LocData.HkIntegrand_const_mul α k (α ^ 2)
      (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ]
    ring
  calc Work.Spaces.HkIntegrand α k (fun z θ => (α * (5 + α)) * Work.Spaces.Dz Ψ z θ) z θ
      = Work.Spaces.HkIntegrand α k (fun z θ => Work.Elliptic.Lzero Ψ z θ
          - Work.Elliptic.bslOp α Ψ z θ
          - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ := hcongr
    _ ≤ 3 * (Work.Spaces.HkIntegrand α k (Work.Elliptic.Lzero Ψ) z θ
          + Work.Spaces.HkIntegrand α k (Work.Elliptic.bslOp α Ψ) z θ
          + Work.Spaces.HkIntegrand α k
              (fun z θ : ℝ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) := h3
    _ = 3 * (Work.Spaces.HkIntegrand α k (Work.Elliptic.Lzero Ψ) z θ
          + Work.Spaces.HkIntegrand α k F z θ
          + α ^ 4 * Work.Spaces.HkIntegrand α k
              (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) := by
        rw [hBF, hCeq]

/-- The pointwise transfer on the whole closed quadrant `Iz × Iθ`: on the two boundary
lines (where the weight `w` or the factor `sin(2θ)` vanishes) the `ℋ^k`-integrand is
identically `0`, so the bound follows from the nonnegativity of the integrand. -/
theorem HkIntegrand_transfer_all {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hbsl : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hΨ : SmoothOpen Ψ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => (α * (5 + α)) * Work.Spaces.Dz Ψ z θ) z θ
        ≤ 3 * (Work.Spaces.HkIntegrand α k (Work.Elliptic.Lzero Ψ) z θ
            + Work.Spaces.HkIntegrand α k F z θ
            + α ^ 4 * Work.Spaces.HkIntegrand α k
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) := by
  intro z hz θ hθ
  by_cases hz0 : z = 0
  · rw [hz0, HkIntegrand_eq_zero_of_z_eq_zero]
    have ha := Work.Spaces.HkIntegrand_nonneg α k (Work.Elliptic.Lzero Ψ) 0 θ
    have hb := Work.Spaces.HkIntegrand_nonneg α k F 0 θ
    have hc := Work.Spaces.HkIntegrand_nonneg α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 0 θ
    have h4 : 0 ≤ α ^ 4 * Work.Spaces.HkIntegrand α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 0 θ :=
      mul_nonneg (by positivity) hc
    linarith
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_eq_zero_of_sin α k
      (fun z θ => (α * (5 + α)) * Work.Spaces.Dz Ψ z θ) hs]
    have ha := Work.Spaces.HkIntegrand_nonneg α k (Work.Elliptic.Lzero Ψ) z θ
    have hb := Work.Spaces.HkIntegrand_nonneg α k F z θ
    have hc := Work.Spaces.HkIntegrand_nonneg α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
    have h4 : 0 ≤ α ^ 4 * Work.Spaces.HkIntegrand α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
      mul_nonneg (by positivity) hc
    linarith
  · have hzpos : 0 < z := lt_of_le_of_ne (Set.mem_Ici.mp hz) (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := hθ
    have hθ0 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h | h
      · exact absurd (by rw [← h]; simp) hs
      · exact h
    have hθ1 : θ < Real.pi / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h | h
      · exact h
      · exact absurd (by rw [h, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring,
          Real.sin_pi]) hs
    exact HkIntegrand_transfer_pt hbsl hΨ hzpos hθ0 hθ1

/-! ## From a pointwise integrand bound to the `HkSq` bound -/

/-- Additivity of the Lebesgue integral over three summands, in the shape in which it is used
below.  (The two `rfl`-steps align `f + g` with `fun x => f x + g x`, which is what makes the
`integral_add` patterns match syntactically.) -/
theorem integral_add3 (f g h : ℝ → ℝ) (μ : Measure ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (hh : Integrable h μ) :
    ∫ x, (f x + g x + h x) ∂μ = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) + ∫ x, h x ∂μ := by
  have e1 : (∫ x, (f x + g x + h x) ∂μ) = ∫ x, ((f + g) x + h x) ∂μ := rfl
  have e2 : (∫ x, (f + g) x ∂μ) = ∫ x, (f x + g x) ∂μ := rfl
  rw [e1, integral_add (hf.add hg) hh, e2, integral_add hf hg]

/-- The constant multiple of the three-term integral. -/
theorem integral_mul_add3 (c : ℝ) (f g h : ℝ → ℝ) (μ : Measure ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (hh : Integrable h μ) :
    ∫ x, c * (f x + g x + h x) ∂μ = c * ((∫ x, f x ∂μ) + (∫ x, g x ∂μ) + ∫ x, h x ∂μ) := by
  have e1 : (∫ x, c * (f x + g x + h x) ∂μ) = ∫ x, c * ((f x + g x) + h x) ∂μ := rfl
  have e2 : (∫ x, c * ((f x + g x) + h x) ∂μ) = ∫ x, c * ((f + g) x + h x) ∂μ := rfl
  have e3 : (∫ x, (f + g) x ∂μ) = ∫ x, (f x + g x) ∂μ := rfl
  rw [e1, e2, integral_const_mul, integral_add (hf.add hg) hh, e3, integral_add hf hg]

/-- **Integration of a pointwise bound of `ℋ^k`-integrands.**  If the integrand of `U` is
pointwise dominated by `3(R₁ + R₂ + α⁴R₃)` on the closed quadrant and the three dominating
integrands are honest (`HkMem`), then the same bound holds for the iterated integrals.  This
is the two-step monotonicity argument of `Work.FTS.LocData.HkSq_add_le`; the integrability of
the dominating function — the role of the three `HkMem` hypotheses — is what makes it work in
the presence of the junk value `0` attached to a non-integrable integrand. -/
theorem HkSq_le_of_integrand_le (α : ℝ) (k : ℕ) {U R1 R2 R3 : ℝ → ℝ → ℝ}
    (h1 : Work.Spaces.HkMem α k R1) (h2 : Work.Spaces.HkMem α k R2)
    (h3 : Work.Spaces.HkMem α k R3)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k U z θ
        ≤ 3 * (Work.Spaces.HkIntegrand α k R1 z θ + Work.Spaces.HkIntegrand α k R2 z θ
            + α ^ 4 * Work.Spaces.HkIntegrand α k R3 z θ)) :
    Work.Spaces.HkSq α k U
      ≤ 3 * (Work.Spaces.HkSq α k R1 + Work.Spaces.HkSq α k R2
          + α ^ 4 * Work.Spaces.HkSq α k R3) := by
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k U z θ)
        ≤ 3 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R1 z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R2 z θ)
            + α ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R3 z θ)) := by
    intro z hz
    have hf : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α k R1 z θ)
        (volume.restrict Work.Spaces.Iθ) := h1.1 z hz
    have hg : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α k R2 z θ)
        (volume.restrict Work.Spaces.Iθ) := h2.1 z hz
    have hh : Integrable (fun θ : ℝ => α ^ 4 * Work.Spaces.HkIntegrand α k R3 z θ)
        (volume.restrict Work.Spaces.Iθ) := (h3.1 z hz).const_mul (α ^ 4)
    have hint : Integrable (fun θ : ℝ => 3 * (Work.Spaces.HkIntegrand α k R1 z θ
        + Work.Spaces.HkIntegrand α k R2 z θ
        + α ^ 4 * Work.Spaces.HkIntegrand α k R3 z θ))
        (volume.restrict Work.Spaces.Iθ) := ((hf.add hg).add hh).const_mul 3
    have hle := integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k U z θ) hint
      (ae_restrict_of_forall_mem hmesθ fun θ hθ => hpt z hz θ hθ)
    refine hle.trans_eq ?_
    rw [integral_mul_add3 (μ := volume.restrict Work.Spaces.Iθ) 3
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k R1 z θ)
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k R2 z θ)
      (fun θ : ℝ => α ^ 4 * Work.Spaces.HkIntegrand α k R3 z θ) hf hg hh,
      integral_const_mul]
  have hX1 : Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R1 z θ)
      (volume.restrict Work.Spaces.Iz) := h1.2
  have hX2 : Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R2 z θ)
      (volume.restrict Work.Spaces.Iz) := h2.2
  have hX3 : Integrable
      (fun z : ℝ => α ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R3 z θ))
      (volume.restrict Work.Spaces.Iz) := h3.2.const_mul (α ^ 4)
  have houter : (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k U z θ)
      ≤ ∫ z in Work.Spaces.Iz, 3 *
          ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R1 z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R2 z θ)
            + α ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R3 z θ)) := by
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k U z θ)
      (((hX1.add hX2).add hX3).const_mul 3) ?_
    exact ae_restrict_of_forall_mem hmesz fun z hz => hinner z hz
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine houter.trans_eq ?_
  rw [integral_mul_add3 (μ := volume.restrict Work.Spaces.Iz) 3
    (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R1 z θ)
    (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R2 z θ)
    (fun z : ℝ => α ^ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k R3 z θ))
    hX1 hX2 hX3,
    integral_const_mul]

/-! ## The transfer theorem -/

theorem HkSqDzTransfer (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkMem α k F →
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) →
      Work.Spaces.HkMem α k (Work.Elliptic.Lzero Ψ) →
      α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz Ψ)
        ≤ C * (Work.Spaces.HkSq α k (Work.Elliptic.Lzero Ψ) + Work.Spaces.HkSq α k F
            + α ^ 4 * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
  refine ⟨3, by norm_num, ?_⟩
  intro α F Ψ hα _hα4 hbsl hsm hmF hmG hmA
  have hΨ : SmoothOpen Ψ := smoothOpen_of_forall hsm
  have hpt := HkIntegrand_transfer_all (α := α) (k := k) (F := F) (Ψ := Ψ) hbsl hΨ
  have hint := HkSq_le_of_integrand_le α k hmA hmF hmG hpt
  have hscale : Work.Spaces.HkSq α k (fun z θ => (α * (5 + α)) * Work.Spaces.Dz Ψ z θ)
      = (α * (5 + α)) ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz Ψ) :=
    HkSq_const_mul_unc α k (α * (5 + α)) (Work.Spaces.Dz Ψ)
  have h5 : (1 : ℝ) ≤ (5 + α) ^ 2 := by
    have h10 : (0 : ℝ) ≤ α * (α + 10) := mul_nonneg (le_of_lt hα) (by linarith)
    nlinarith [h10]
  have hX : 0 ≤ α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz Ψ) :=
    mul_nonneg (sq_nonneg α) (Work.Spaces.HkSq_nonneg α k _)
  calc α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz Ψ)
      = (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz Ψ)) * 1 := by ring
    _ ≤ (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz Ψ)) * (5 + α) ^ 2 :=
        mul_le_mul_of_nonneg_left h5 hX
    _ = (α * (5 + α)) ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz Ψ) := by ring
    _ = Work.Spaces.HkSq α k (fun z θ => (α * (5 + α)) * Work.Spaces.Dz Ψ z θ) :=
        hscale.symm
    _ ≤ 3 * (Work.Spaces.HkSq α k (Work.Elliptic.Lzero Ψ) + Work.Spaces.HkSq α k F
          + α ^ 4 * Work.Spaces.HkSq α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := hint

end Work.FTS.EllipticEst.lobAux
