/-
# Subadditivity of the `ℋ^k`-integrand over `SmoothQuad` data (the localisation chapter)

`Work.Spaces.HkIntegrand α k f z θ` is the sum of the squares of the weighted derivatives of `f`
at `(z,θ)`:

```
∑_{i≤k} (D_z^i f · w/sin(2θ)^{η/2})²  +  ∑_{i≤k} ∑_{j≤k} (if 1 ≤ i ∧ i+j ≤ k then D_z^j D_θ^i f · W else 0)².
```

The `D`-operators are linear on the quadrant on which the data are `C^∞`, so pointwise
additivity of `D_z^i` and of `D_z^j D_θ^i` holds there, and `(x + y)² ≤ 2x² + 2y²` termwise gives

`HkIntegrand α k (a+b) z θ ≤ 2 · HkIntegrand α k a z θ + 2 · HkIntegrand α k b z θ`

for `(z,θ) ∈ Iz × Iθ`.  This is the `2 + 2` (rather than `2 · (· + ·)`) form of subadditivity,
which is what the downstream estimates of the localisation chapter consume.

The two boundary lines of the domain `Iz × Iθ = [0,∞) × [0,π/2]` need separate treatment:

* at `z = 0` the weight `w 0 = (1+0)²/0² = 0` (Lean's totalised division) kills every term;
* at `sin(2θ) = 0` the first sum is killed by `1/0 = 0` and, in the second sum, the surviving
  indices all have `i ≥ 1`, so the term is `(D_z^j D_θ^i f)²` with an *odd* number of `D_θ`-factors,
  each carrying the factor `sin(2θ) = 0` evaluated at the same boundary point; hence it vanishes.

So the left-hand side is `0` on the boundary and the bound follows from nonnegativity of the
integrand; the interior is handled by the additivity/algebra argument above.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Additivity of the iterated operators on the open quadrant

The data are `SmoothQuad`, i.e. `C^∞` on `quadU = (-1,∞) × (0,π/2)`; on that open set the
derivatives are honest, so `deriv_add` gives the additivity of `D_z`, and induction gives it
for `D_z^i` and `D_θ^i`. -/

/-- Two functions agreeing on `quadU` have the same `D_z`-iterates there. -/
private lemma DzIter_congr_quad {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, -1 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j F z θ = Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n F z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq]

/-- `D_θ`-iterates are additive on the open quadrant for `SmoothQuad` data. -/
private lemma DthIter_add_quad {a b : ℝ → ℝ → ℝ} (ha : SmoothQuad a)
    (hb : SmoothQuad b) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.DthIter i a z θ + Work.Spaces.DthIter i b z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => a z θ + b z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => Work.Spaces.DthIter n a z θ' + Work.Spaces.DthIter n b z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n a z θ') θ :=
        ha.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n b z θ') θ :=
        hb.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
      have hd : deriv (fun θ' => Work.Spaces.DthIter n a z θ' + Work.Spaces.DthIter n b z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n a z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter n b z θ') θ :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

/-- `D_z`-iterates are additive on the open quadrant for `SmoothQuad` data. -/
private lemma DzIter_add_quad {a b : ℝ → ℝ → ℝ} (ha : SmoothQuad a)
    (hb : SmoothQuad b) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.DzIter i a z θ + Work.Spaces.DzIter i b z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => a z θ + b z θ) z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n a z' θ + Work.Spaces.DzIter n b z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n a z' θ) z :=
        ha.differentiableAt_slice_DzIter n hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n b z' θ) z :=
        hb.differentiableAt_slice_DzIter n hz ⟨h1, h2⟩
      have hd : deriv (fun z' => Work.Spaces.DzIter n a z' θ + Work.Spaces.DzIter n b z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n a z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter n b z' θ) z :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- The mixed operators `D_z^j D_θ^i` are additive on the open quadrant for `SmoothQuad` data. -/
private lemma mixed_add_quad {a b : ℝ → ℝ → ℝ} (ha : SmoothQuad a)
    (hb : SmoothQuad b) (j i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.mixed j i a z θ + Work.Spaces.mixed j i b z θ := by
  intro z θ hz h1 h2
  have hcongr := DzIter_congr_quad (j := j)
    (F := Work.Spaces.DthIter i (fun z θ => a z θ + b z θ))
    (G := fun z θ => Work.Spaces.DthIter i a z θ + Work.Spaces.DthIter i b z θ)
    (fun z θ hz h1 h2 => DthIter_add_quad ha hb i z θ hz h1 h2) z θ hz h1 h2
  have hadd := DzIter_add_quad (ha.DthIter i) (hb.DthIter i) j z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-! ## Vanishing of the integrand on the two boundary lines -/

/-- At `sin(2θ) = 0` the `D_θ`-iterates of order `≥ 1` vanish at that same `θ`. -/
private lemma DthIter_succ_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    (m : ℕ) (z : ℝ) : Work.Spaces.DthIter (m + 1) f z θ = 0 := by
  simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth, hs, zero_mul]

/-- A function whose `θ`-slice vanishes identically has vanishing `D_z`-iterates there. -/
private lemma DzIter_eq_zero_of_slice (f : ℝ → ℝ → ℝ) {θ : ℝ} (h : ∀ z, f z θ = 0) :
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

/-- At `sin(2θ) = 0` every mixed derivative `D_z^j D_θ^i` with `i ≥ 1` vanishes at `(z,θ)`. -/
private lemma mixed_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    {j i : ℕ} (hi : 1 ≤ i) (z : ℝ) : Work.Spaces.mixed j i f z θ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simp only [Work.Spaces.mixed]
  exact DzIter_eq_zero_of_slice (Work.Spaces.DthIter (m + 1) f) (θ := θ)
    (fun z' => DthIter_succ_eq_zero_of_sin f hs m z') j z

/-- The `ℋ^k`-integrand vanishes on the angular boundary `sin(2θ) = 0`: the first sum is killed
by the `1/sin(2θ)^{η/2}` factor and the second by the `D_θ`-factors of all its summands. -/
private lemma HkIntegrand_eq_zero_of_sin (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
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
private lemma HkIntegrand_eq_zero_of_z_eq_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [Work.Spaces.w, Work.Spaces.Wt, Work.Spaces.wTheta]

/-! ## The algebraic core: sums of squares of sums -/

private lemma sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    (∑ i ∈ s, (x i + y i) ^ 2) ≤ 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
  calc (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ ∑ i ∈ s, (2 * x i ^ 2 + 2 * y i ^ 2) :=
        Finset.sum_le_sum fun i _ => by
          have h := add_sq_le (a := x i) (b := y i); linarith
    _ = 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The pointwise inequality, given the additivity of the iterated operators at `(z,θ)`. -/
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

theorem HkIntegrand_add_le (α : ℝ) (k : ℕ) {a b : ℝ → ℝ → ℝ} (hsa : SmoothQuad a)
    (hsb : SmoothQuad b) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => a z θ + b z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k a z θ + 2 * Work.Spaces.HkIntegrand α k b z θ := by
  by_cases hz0 : z = 0
  · rw [hz0, HkIntegrand_eq_zero_of_z_eq_zero]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k a 0 θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k b 0 θ
    linarith
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_eq_zero_of_sin α k (fun z θ => a z θ + b z θ) hs]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k a z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k b z θ
    linarith
  · have hzge : 0 ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
    have hzpos : 0 < z := lt_of_le_of_ne hzge (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ π / 2 := by simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
    have hθ1 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h | h
      · exact absurd (by rw [← h]; simp) hs
      · exact h
    have hθ2 : θ < π / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h | h
      · exact h
      · exact absurd (by rw [h, show (2 : ℝ) * (π / 2) = π from by ring, Real.sin_pi]) hs
    exact HkIntegrand_add_le_pt α k a b z θ
      (fun i => DzIter_add_quad hsa hsb i z θ (by linarith) hθ1 hθ2)
      (fun i j => mixed_add_quad hsa hsb j i z θ (by linarith) hθ1 hθ2)

end Work.FTS.LocData
