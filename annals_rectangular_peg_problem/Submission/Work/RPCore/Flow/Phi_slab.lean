import Mathlib
import Submission.Work.RPCore.Flow.HamFlow

/-!
# C0: the Hamiltonian flow fixes the support slab pointwise

The compactly supported, `2π`-periodic Hamiltonian `Hh.H` vanishes on the closed slab
`{|q₁| + |p₁| + |p₂| ≥ Hh.R}` (`CptPerHam.supp`).  Consequently its clamped Hamiltonian
`clampHam Hh t` vanishes on that slab as well, its Hamiltonian vector field `hamVF` vanishes
*at every point of the slab*, and the clamped autonomous field `clampedField Hh` equals `(1, 0)`
there.  The flow curve `s ↦ (s, x)` is therefore an integral curve of the clamped field for every
`x` in the slab, and uniqueness of integral curves identifies it with the flow through `(a, x)`.
Hence `Phi Hh a b x = x` for all times.

The only point requiring care is that `x` may lie on the *boundary* of the slab, where `Hh.H t`
does not vanish on a neighbourhood.  There one uses that `{y | fderiv ℝ (Hh.H t) y = 0}` is closed
(the derivative of a `C⁴` function is continuous) and contains the open superlevel set
`{|q₁| + |p₁| + |p₂| > R}`, which is dense in the closure `slab Hh.R` when `R > 0` (a point of the
open set can be pushed radially outward).  For `R ≤ 0` the slab is all of `PS` and `Hh.H t ≡ 0`.

Main contents:

* `slabPhi_smul` : positive homogeneity of the slab function `y ↦ |q₁| + |p₁| + |p₂|`;
* `hamVF_eq_zero_of_fderiv_eq_zero` : a vanishing derivative gives a vanishing Hamiltonian field;
* `fderiv_HH_eq_zero_of_mem_slab` : `fderiv ℝ (Hh.H t) x = 0` for `x` in the slab;
* `Phi_slab` : the flow fixes the slab pointwise.
-/

set_option autoImplicit false

open RectangularPegProblem Manifold Complex Real
open scoped ContDiff Topology

noncomputable section

namespace Work.RPCore.Flow

open Work.RPV Filter

/-- The slab function `y ↦ |q₁| + |p₁| + |p₂|` is positively homogeneous. -/
lemma slabPhi_smul (c : ℝ) (hc : 0 ≤ c) (y : PS) :
    |(c • y).1.1| + |(c • y).2.1| + |(c • y).2.2| = c * (|y.1.1| + |y.2.1| + |y.2.2|) := by
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_nonneg hc]
  ring

/-- A vanishing Fréchet derivative gives a vanishing Hamiltonian vector field. -/
theorem hamVF_eq_zero_of_fderiv_eq_zero {W : PS → ℝ} {x : PS} (h : fderiv ℝ W x = 0) :
    hamVF W x = 0 := by
  simp [hamVF, h]

/-- On the support slab `{|q₁| + |p₁| + |p₂| ≥ R}` of `Hh`, the derivative of `Hh.H t` vanishes:
off the (open) interior this is clear, and on the boundary it follows by continuity of `fderiv`. -/
theorem fderiv_HH_eq_zero_of_mem_slab (Hh : CptPerHam) (t : ℝ) {x : PS}
    (hx : x ∈ slab Hh.R) : fderiv ℝ (Hh.H t) x = 0 := by
  by_cases hR : Hh.R ≤ 0
  · -- the slab is everything: `Hh.H t` is the zero function
    have hH : Hh.H t = fun _ => 0 := by
      funext y
      exact Hh.supp t y (le_trans hR (by positivity))
    rw [hH]; simp
  · push Not at hR
    -- off the open slab the derivative vanishes
    have hφcont : Continuous (fun y : PS => |y.1.1| + |y.2.1| + |y.2.2|) := by fun_prop
    have hA : ∀ y : PS, Hh.R < |y.1.1| + |y.2.1| + |y.2.2| →
        fderiv ℝ (Hh.H t) y = 0 := by
      intro y hy
      have hopen : {z : PS | Hh.R < |z.1.1| + |z.2.1| + |z.2.2|} ∈ 𝓝 y :=
        (isOpen_lt continuous_const hφcont).mem_nhds hy
      have hev : (fun z => Hh.H t z) =ᶠ[𝓝 y] 0 := by
        filter_upwards [hopen] with z hz using Hh.supp t z hz.le
      rw [hev.fderiv_eq]; simp
    -- the set where the derivative vanishes is closed
    have hcl : IsClosed {y : PS | fderiv ℝ (Hh.H t) y = 0} := by
      have h4 : ContDiff ℝ 4 (fun y : PS => Hh.H t y) := by
        have h : ContDiff ℝ 4 (fun y : PS => (t, y)) := by fun_prop
        exact Hh.smooth.comp h
      have hcont : Continuous (fderiv ℝ (fun y : PS => Hh.H t y)) :=
        h4.continuous_fderiv (by norm_num)
      have : {y : PS | fderiv ℝ (Hh.H t) y = 0}
          = (fderiv ℝ (fun y : PS => Hh.H t y)) ⁻¹' {0} := rfl
      rw [this]; exact isClosed_singleton.preimage hcont
    have hφx : 0 < |x.1.1| + |x.2.1| + |x.2.2| := lt_of_lt_of_le hR hx
    -- push `x` radially outward to reach the open slab
    let u : ℕ → PS := fun n => (1 + 1 / ((n : ℝ) + 1)) • x
    have htend : Tendsto u atTop (𝓝 x) := by
      have h : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 1) := by
        have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
          tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
        have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
          have := tendsto_inv_atTop_zero.comp h1
          simpa [one_div, Function.comp_def] using this
        have h3 : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add h2
        simpa using h3
      simpa [u] using h.smul_const x
    have hev : ∀ᶠ n in (atTop : Filter ℕ), u n ∈ {y : PS | fderiv ℝ (Hh.H t) y = 0} := by
      refine Filter.Eventually.of_forall (fun n => hA _ ?_)
      have hc : (0 : ℝ) ≤ 1 + 1 / ((n : ℝ) + 1) := by positivity
      have hs := slabPhi_smul (1 + 1 / ((n : ℝ) + 1)) hc x
      show Hh.R < |(u n).1.1| + |(u n).2.1| + |(u n).2.2|
      rw [show (u n).1.1 = ((1 + 1 / ((n : ℝ) + 1)) • x).1.1 from rfl, hs]
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hk : (1 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by linarith
      calc Hh.R ≤ |x.1.1| + |x.2.1| + |x.2.2| := hx
        _ < (1 + 1 / ((n : ℝ) + 1)) * (|x.1.1| + |x.2.1| + |x.2.2|) := by
              simpa using mul_lt_mul_of_pos_right hk hφx
    exact hcl.mem_of_tendsto htend hev

theorem Phi_slab (Hh : Work.RPV.CptPerHam) {a b : ℝ} {x : Work.RPV.PS}
    (hx : x ∈ Work.RPCore.slab Hh.R) : Work.RPCore.Phi Hh a b x = x := by
  -- the clamped field equals `(1, 0)` along `{x}` in the second factor
  have hfderiv : ∀ s : ℝ, fderiv ℝ (clampHam Hh s) x = 0 := fun s =>
    fderiv_HH_eq_zero_of_mem_slab Hh (clampPsi s) hx
  have hVF : ∀ s : ℝ, hamVF (clampHam Hh s) x = 0 := fun s =>
    hamVF_eq_zero_of_fderiv_eq_zero (hfderiv s)
  have hfield : ∀ s : ℝ, clampedField Hh (s, x) = (1, 0) := by
    intro s
    simp only [clampedField, autoVF]
    rw [hVF s]
  -- `s ↦ (s, x)` is an integral curve of the clamped field ...
  have hγ2 : IsIntegralCurve (fun r : ℝ => (r, x)) (fun _ y => clampedField Hh y) := by
    intro r
    have hd : HasDerivAt (fun r : ℝ => (r, x)) (clampedField Hh (r, x)) r := by
      rw [hfield r]
      exact (hasDerivAt_id r).prodMk (hasDerivAt_const (x := r) (c := x))
    exact hd
  -- ... as is the flow curve through `(a, x)`
  have hγ1 : IsIntegralCurve (fun r : ℝ => clampFlow Hh (r - a) (a, x))
      (fun _ y => clampedField Hh y) := by
    have h := (clampFlow_curve Hh (a, x)).comp_add (-a)
    simpa [Function.comp_def, sub_eq_add_neg] using h
  have hinit : (fun r : ℝ => clampFlow Hh (r - a) (a, x)) a = (fun r : ℝ => (r, x)) a := by
    simp [clampFlow_zero]
  have hfun := Port.ODE.eq_of_isIntegralCurve (clampedField_lipschitz Hh) hγ1 hγ2 hinit
  have hb := congrFun hfun b
  simp only [Phi]
  rw [hb]

end Work.RPCore.Flow
