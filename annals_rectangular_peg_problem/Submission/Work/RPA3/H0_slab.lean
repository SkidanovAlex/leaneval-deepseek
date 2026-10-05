import Mathlib
import Submission.Work.RPA3.TubularHDefs
import Submission.Work.RPA3.theta_slab_bounded

/-!
# RPA3: `H0` is supported in the slab `|q₁| + |p₁| + |p₂| ≥ R`

The tubular Hamiltonian `H0 L F T τ` vanishes outside a slab `{|q₁| + |p₁| + |p₂| ≥ R}`,
uniformly for `τ ∈ [-1,2]`.

At a point `y` with a witness `w = ((x,t),ξ)` (`‖ξ‖ < T.ε`) the value is
`H0 τ y = cutXi T.ε ‖ξ‖ · F.h τ (x,t)` (`H0_of`), so it vanishes in each of the following cases:

* `T.ε/2 ≤ ‖ξ‖`: the transverse cut-off vanishes (`cutXi_eq_zero`);
* `L.X0 ≤ |x|`: the flux primitive vanishes (`FluxPrimitive.van`);
* `|x| < max L.X0 0` and `‖ξ‖ < T.ε/2`: here `(τ,x,t,ξ)` lies in the compact strip on which
  `theta_slab_bounded` bounds `|q₁| + |p₁| + |p₂|` of the image.  Reducing the angle `t` modulo
  `2π` (`exists_shift_two_pi_Ico`, `theta_per_int`) and using that `Tk` only changes `q₂`, this
  bound also bounds `|q₁| + |p₁| + |p₂|` at `y`; the slab hypothesis on `y` then gives a
  contradiction.

Hence with `R := R₀ + 1`, where `R₀` bounds the strip image, no point of the slab has a witness in
the support region, so `H0` vanishes there.
-/

open scoped ContDiff
open Real

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-- The slab function `|q₁| + |p₁| + |p₂|` of `H0_slab`. -/
private def slabQ (y : PS) : ℝ := |y.1.1| + |y.2.1| + |y.2.2|

/-- The slab function is invariant under the angle shift `Tk k`, which only moves `q₂`. -/
private lemma slabQ_Tk (k : ℤ) (y : PS) : slabQ (Tk k y) = slabQ y := by
  simp [slabQ, Tk]

theorem H0_slab (L : Work.RPA3.LagFamilyAll) (F : Work.RPA3.FluxPrimitive L)
    (T : Work.RPA3.TubularData L) :
    ∃ R, ∀ τ ∈ Set.Icc (-1 : ℝ) 2, ∀ y : Work.RPA3.PS,
      R ≤ |y.1.1| + |y.2.1| + |y.2.2| → Work.RPA3.H0 L F T τ y = 0 := by
  obtain ⟨R, hR⟩ := theta_slab_bounded L T
  refine ⟨R + 1, ?_⟩
  intro τ hτ y hy
  by_cases hwit : HasWitness L T τ y
  · -- `y` has a witness: compute `H0` at (the chosen) witness `w`
    rw [H0_of L F T τ y hwit]
    set w : PS := wit L T τ y hwit with hwdef
    have hwθ : theta L τ w.1.1 w.1.2 w.2 = y := by
      rw [hwdef]
      exact theta_wit L T τ y hwit
    by_cases hξ : T.ε / 2 ≤ ‖w.2‖
    · -- the transverse cut-off vanishes
      rw [cutXi_eq_zero T.εpos hξ, zero_mul]
    · rw [not_le] at hξ
      by_cases hx : L.X0 ≤ |w.1.1|
      · -- the flux primitive vanishes
        have hvan : F.h τ w.1 = 0 := F.van τ w.1.1 w.1.2 hx
        rw [hvan, mul_zero]
      · -- the witness lies in the compact strip: reduce the angle and use the strip bound
        rw [not_le] at hx
        exfalso
        obtain ⟨t', ht', k, hk⟩ := exists_shift_two_pi_Ico w.1.2
        have hs : slabQ ((thetaP L (τ, ((w.1.1, t'), w.2))).2) ≤ R :=
          hR τ hτ w.1.1 t' (le_of_lt (lt_of_lt_of_le hx (le_max_left L.X0 0)))
            (Set.Ico_subset_Icc_self ht') w.2 (le_of_lt hξ)
        have hQy : slabQ y = slabQ ((thetaP L (τ, ((w.1.1, t'), w.2))).2) := by
          have hyTk : y = Tk k (theta L τ w.1.1 t' w.2) := by
            rw [← hwθ, hk]
            exact theta_per_int L τ w.1.1 t' w.2 k
          calc slabQ y = slabQ (Tk k (theta L τ w.1.1 t' w.2)) := congrArg slabQ hyTk
            _ = slabQ (theta L τ w.1.1 t' w.2) := slabQ_Tk k _
            _ = slabQ ((thetaP L (τ, ((w.1.1, t'), w.2))).2) := rfl
        have hy1 : R + 1 ≤ slabQ y := by simpa only [slabQ] using hy
        linarith [hQy, hs, hy1]
  · -- no witness: `H0` is `0` by definition
    rw [H0_of_not L F T τ y hwit]

end Work.RPA3
