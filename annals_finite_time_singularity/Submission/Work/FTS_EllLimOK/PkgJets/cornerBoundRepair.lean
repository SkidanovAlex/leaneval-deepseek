/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PkgJets/cornerBoundRepair` — the machine-checked companions of the `BoxDataD` verdict

The task `FTS_EllLimOK/PkgJets/boxDataD_of_hasPkgE` asked for `BoxDataD α Ce` from
`HasPkgE α Ce`.  The verdict (see `PkgJets/NOTES_boxDataD.md`, and the two reviewers of
`FTS_EllLimOK/PkgJets/cornerBoundUniform_of_hasPkgE`) is that the requested implication is **not
derivable from the interface as formalized**, because the field `PkgRepair.PkgCorner` binds its
bound constant *after* the source:

```
PkgCorner α Ce E = ∀ g, ClassC α g → ∃ K, 0 < K ∧ ∀ a b, 0 < a → a ≤ b → ∀ k ≤ 3 →
                     ∀ p ∈ cbox a b, ‖iteratedFDeriv ℝ k (uncurry (E g)) p‖ ≤ K * Xn6 α g
```

while its consumer `BoxReg_of_uniform` needs *one* constant for the whole sequence
`n ↦ E (fn n)`, and nothing in `HasPkgE` bounds `sup_n K (fn n)`; `PkgCorner`'s own docstring
says "uniform (in `g`)" and its siblings `PkgDecay`/`PkgSlice` do put the constant outside
`∀ g`.

This module records, with proofs, (a) the repaired field `PkgCornerU`, (b) the crux uniform box
bound that follows from it, (c) the intended consumption of that bound via
`BoxReg_of_uniform` (applied to a *reindexed* sequence — the observation that this is legitimate
is what makes the repair sufficient), and (d) the degeneracy that makes every other field of
`HasPkgE` blind at the angular endpoints: the operator `D_θ = sin(2θ)·∂_θ` vanishes identically
there, so *all* mixed jets vanish at `θ = 0, π/2` — the normalisation in which `PkgDecay`,
`LocalBound4D` and the packages' slot bounds are stated.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.BoxReg_of_uniform
import Submission.Work.Spaces.SmoothStripDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## §1  The repaired corner field -/

/-- **The repaired corner field**: exactly `PkgRepair.PkgCorner` with the bound constant moved
*outside* the source quantifier — which is what its docstring announces ("uniform (in `g`)
bounds") and what `PkgDecay`/`PkgSlice` already do. -/
def PkgCornerU (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ g, Work.FTS.ClassC.ClassC α g →
    ∀ a b : ℝ, 0 < a → a ≤ b → ∀ k : ℕ, k ≤ 3 →
      ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
        ‖iteratedFDeriv ℝ k (Function.uncurry (E g)) p‖ ≤ K * Work.FTS.StrongGlobal.Xn6 α g

/-! ## §2  The crux: a uniform box bound along a `LimSeq4` -/

/-- **The crux piece.**  From the repaired corner field and a `LimSeq4` sequence, *one*
constant `C` bounds the values and every order-`≤ 3` plain iterated derivative of every
`E (fn n)` on a fixed closed box.  This is exactly the `hbdd` hypothesis of
`BoxReg_of_uniform`; with the per-source `PkgCorner` only `K (fn n) · Xn6 α (fn n) ≤
K (fn n) · B` is available, and nothing bounds `sup_n K (fn n)`. -/
theorem cornerBoundUniform_of_pkgCornerU {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn}
    (h : PkgCornerU α Ce E) {fn : ℕ → Fn} {f : Fn}
    (hL : Work.FTS_EllLimOK.LimSeq4 α fn f) :
    ∀ a b : ℝ, 0 < a → a ≤ b → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ k : ℕ, k ≤ 3 →
      ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
        ‖iteratedFDeriv ℝ k (Function.uncurry (E (fn n))) p‖ ≤ C := by
  obtain ⟨K, hKpos, hK⟩ := h
  obtain ⟨B, hB⟩ := hL.bound
  refine fun a b ha hab => ⟨K * max B 0 + 1, by nlinarith [hKpos, le_max_right B 0], ?_⟩
  intro n k hk p hp
  have hXn : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 :=
    le_trans (hB n) (le_max_left _ _)
  have h1 := hK (fn n) (hL.classC n) a b ha hab k hk p hp
  have h2 : K * Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ K * max B 0 :=
    mul_le_mul_of_nonneg_left hXn hKpos.le
  linarith

/-! ## §3  The consumption: closed-box `C²`-regularity of a cluster limit -/

/-- **How the corner clause of `BoxDataD` was meant to be discharged.**  `BoxReg_of_uniform`
takes the box convergence of the *sequence it is applied to*; applying it to the *reindexed*
sequence `n ↦ E (fn (σ n))` (with its own internal Arzelà–Ascoli extraction) is legitimate, so
the uniform box bound of §2 plus the convergence along the cluster subsequence `σ` gives
`BoxReg Ψ` for the cluster limit.  The per-source `PkgCorner` does not supply §2, which is why
the assigned statement is not derivable as formalized. -/
theorem boxReg_of_subseq_of_uniformCorner {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} {fn : ℕ → Fn} {f : Fn}
    (hstrip : ∀ g, Work.FTS.ClassC.ClassC α g → Work.Spaces.SmoothStrip (E g))
    (hcorner : PkgCornerU α Ce E) (hL : Work.FTS_EllLimOK.LimSeq4 α fn f)
    (σ : ℕ → ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hconv : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      Filter.Tendsto (fun n => E (fn (σ n)) p.1 p.2) Filter.atTop (𝓝 (Ψ p.1 p.2))) :
    Work.FTS_EllLimOK.BoxReg Ψ := by
  refine Work.FTS_EllLimOK.BoxReg_of_uniform (Ψn := fun n => E (fn (σ n))) (Ψ := Ψ)
    (fun n => hstrip (fn (σ n)) (hL.classC (σ n))) ?_ ?_
  · intro a b ha hab
    obtain ⟨C, hCpos, hC⟩ := cornerBoundUniform_of_pkgCornerU hcorner hL a b ha hab
    refine ⟨C, hCpos, fun n p hp => ⟨?_, ?_, ?_, ?_⟩⟩
    · have h0 := hC (σ n) 0 (by norm_num) p hp
      rw [norm_iteratedFDeriv_zero] at h0
      simpa only [Real.norm_eq_abs] using h0
    · exact hC (σ n) 1 (by norm_num) p hp
    · exact hC (σ n) 2 (by norm_num) p hp
    · exact hC (σ n) 3 (by norm_num) p hp
  · intro a b ha hab p hp
    exact hconv a b ha hab p hp

/-! ## §4  Why the other fields of `HasPkgE` see nothing at the angular endpoints -/

/-- `D_θ^i` vanishes at `θ = 0` for every `i ≥ 1` and every `f`: `D_θ = sin(2θ)·∂_θ`. -/
theorem DthIter_eq_zero_at_zero (i : ℕ) (hi : 1 ≤ i) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.DthIter i f z 0 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have h : Work.Spaces.DthIter (k + 1) f = Work.Spaces.Dth (Work.Spaces.DthIter k f) := rfl
  rw [h, Work.Spaces.Dth]
  have hs : Real.sin (2 * 0) = 0 := by norm_num
  rw [hs, zero_mul]

/-- `D_θ^i` vanishes at `θ = π/2` for every `i ≥ 1` and every `f`. -/
theorem DthIter_eq_zero_at_pi_div_two (i : ℕ) (hi : 1 ≤ i) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.DthIter i f z (π / 2) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have h : Work.Spaces.DthIter (k + 1) f = Work.Spaces.Dth (Work.Spaces.DthIter k f) := rfl
  rw [h, Work.Spaces.Dth]
  have hs : Real.sin (2 * (π / 2)) = 0 := by
    rw [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
  rw [hs, zero_mul]

/-- `D_z^j` of a function whose slice at `θ = 0` vanishes identically vanishes too. -/
theorem DzIter_eq_zero_at_zero (j : ℕ) {h : ℝ → ℝ → ℝ} (hh : ∀ z, h z 0 = 0) :
    ∀ z, Work.Spaces.DzIter j h z 0 = 0 := by
  induction j with
  | zero => exact hh
  | succ j ih =>
      intro z
      have hz : (fun z' => Work.Spaces.DzIter j h z' 0) = fun _ => (0 : ℝ) := funext ih
      show z * deriv (fun z' => Work.Spaces.DzIter j h z' 0) z = 0
      have h2 : deriv (fun z' => Work.Spaces.DzIter j h z' 0) z = 0 := by
        rw [hz, deriv_const]
      rw [h2, mul_zero]

/-- `D_z^j` of a function whose slice at `θ = π/2` vanishes identically vanishes too. -/
theorem DzIter_eq_zero_at_pi_div_two (j : ℕ) {h : ℝ → ℝ → ℝ}
    (hh : ∀ z, h z (π / 2) = 0) : ∀ z, Work.Spaces.DzIter j h z (π / 2) = 0 := by
  induction j with
  | zero => exact hh
  | succ j ih =>
      intro z
      have hz : (fun z' => Work.Spaces.DzIter j h z' (π / 2)) = fun _ => (0 : ℝ) := funext ih
      show z * deriv (fun z' => Work.Spaces.DzIter j h z' (π / 2)) z = 0
      have h2 : deriv (fun z' => Work.Spaces.DzIter j h z' (π / 2)) z = 0 := by
        rw [hz, deriv_const]
      rw [h2, mul_zero]

/-- **The mixed normalisation is blind at `θ = 0`.**  For every `f`, every `j` and every `i ≥ 1`,
`mixed j i f z 0 = 0`.  In particular the (uniform, `PkgDecay`-style) bounds on the mixed jets
carry no information about the plain derivatives `∂_θ^i f` at the angular endpoint. -/
theorem mixed_eq_zero_at_zero {f : ℝ → ℝ → ℝ} {i : ℕ} (hi : 1 ≤ i) (j : ℕ) (z : ℝ) :
    Work.Spaces.mixed j i f z 0 = 0 :=
  DzIter_eq_zero_at_zero j (fun z' => DthIter_eq_zero_at_zero i hi f z') z

/-- **The mixed normalisation is blind at `θ = π/2`** (the same statement there). -/
theorem mixed_eq_zero_at_pi_div_two {f : ℝ → ℝ → ℝ} {i : ℕ} (hi : 1 ≤ i) (j : ℕ) (z : ℝ) :
    Work.Spaces.mixed j i f z (π / 2) = 0 :=
  DzIter_eq_zero_at_pi_div_two j (fun z' => DthIter_eq_zero_at_pi_div_two i hi f z') z

end Work.FTS_EllLimOK.PkgJets
