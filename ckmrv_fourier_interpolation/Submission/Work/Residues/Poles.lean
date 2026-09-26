/-
# Simple poles and residues of functions on `ℍ`

This file develops the elementary API for "`f` has at most a simple pole at `z` with residue
`c`" that the residue theorem of CKMRV Theorem 4.9(3) needs.

The notion used throughout this chapter is

  `Work.Residues.HasResidue f z c`  ⟺  `(τ - z)·f τ → c`  as `τ → z` (`τ ≠ z`),

the *limit* form of "simple pole with residue `c`".  It is deliberately weaker than the
`MDifferentiableAt`-based `Work.Kernels.HasSimplePoleWithResidue` (which additionally pins
down the value of the holomorphic part at `z`); the implication
`Work.Kernels.HasSimplePoleWithResidue f z c → HasResidue f z c` is
`Work.Residues.hasResidue_of_hasSimplePoleWithResidue`.

## Main results

* `Work.Residues.HasResidue` : the definition.
* `Work.Residues.HasResidue.add`, `.const_mul`, `HasResidue.unique`, `.of_eventuallyEq` :
  the elementary API.
* `Work.Residues.hasResidue_of_cleared` : if `(j(τ) - j(z))·f τ = A τ` for `τ` near `z₀`,
  `A` is holomorphic at `z₀`, `j(z₀) = j(z)` and `(j(τ)-j(z₀))/(τ-z₀) → c ≠ 0`, then `f` has
  residue `A(z₀)/c` at `z₀`.  This is the computational core of the residue theorem: the
  residue of the *uncleared* kernel is the value of the *cleared* kernel divided by `j'`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

open Filter
open scoped Topology

namespace Work.Residues

open Work.Kernels

/-! ## The definition -/

/-- `HasResidue f z c` : the function `f` has at `z` at most a simple pole, with residue `c`:
the limit of `(τ - z) f τ` along `τ → z`, `τ ≠ z`, is `c`. -/
def HasResidue (f : ℍ → ℂ) (z : ℍ) (c : ℂ) : Prop :=
  Tendsto (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * f τ) (𝓝[≠] z) (𝓝 c)

lemma hasResidue_iff {f : ℍ → ℂ} {z : ℍ} {c : ℂ} :
    HasResidue f z c ↔
      Tendsto (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * f τ) (𝓝[≠] z) (𝓝 c) := Iff.rfl

/-- Two residues of the same function at the same point coincide. -/
theorem HasResidue.unique {f : ℍ → ℂ} {z : ℍ} {c c' : ℂ}
    (h : HasResidue f z c) (h' : HasResidue f z c') : c = c' :=
  tendsto_nhds_unique (hasResidue_iff.mp h) (hasResidue_iff.mp h')

/-- The zero function has residue `0`. -/
lemma hasResidue_zero (z : ℍ) : HasResidue (fun _ : ℍ => (0 : ℂ)) z 0 := by
  rw [HasResidue]
  simpa using tendsto_const_nhds

lemma HasResidue.add {f g : ℍ → ℂ} {z : ℍ} {c d : ℂ}
    (hf : HasResidue f z c) (hg : HasResidue g z d) : HasResidue (f + g) z (c + d) := by
  have h1 : Tendsto (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * f τ) (𝓝[≠] z) (𝓝 c) := hf
  have h2 : Tendsto (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * g τ) (𝓝[≠] z) (𝓝 d) := hg
  have h : (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * (f + g) τ)
      = fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * f τ + ((τ : ℂ) - (z : ℂ)) * g τ := by
    funext τ; simp only [Pi.add_apply]; ring
  rw [HasResidue, h]
  exact h1.add h2

lemma HasResidue.const_mul {f : ℍ → ℂ} {z : ℍ} {c : ℂ} (a : ℂ)
    (hf : HasResidue f z c) : HasResidue (fun τ => a * f τ) z (a * c) := by
  have h1 : Tendsto (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * f τ) (𝓝[≠] z) (𝓝 c) := hf
  have h : (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * (fun τ => a * f τ) τ)
      = fun τ : ℍ => a * (((τ : ℂ) - (z : ℂ)) * f τ) := by
    funext τ; simp only; ring
  rw [HasResidue, h]
  exact h1.const_mul a

lemma HasResidue.neg {f : ℍ → ℂ} {z : ℍ} {c : ℂ} (hf : HasResidue f z c) :
    HasResidue (fun τ => - f τ) z (-c) := by
  have h := HasResidue.const_mul (-1 : ℂ) hf
  simpa using h

lemma HasResidue.sub {f g : ℍ → ℂ} {z : ℍ} {c d : ℂ}
    (hf : HasResidue f z c) (hg : HasResidue g z d) :
    HasResidue (fun τ => f τ - g τ) z (c - d) := by
  have h : (fun τ : ℍ => f τ - g τ) = (fun τ : ℍ => f τ + (- g τ)) := rfl
  rw [h, sub_eq_add_neg]
  exact hf.add hg.neg

lemma HasResidue.of_eventuallyEq {f g : ℍ → ℂ} {z : ℍ} {c : ℂ}
    (h : f =ᶠ[𝓝[≠] z] g) (hg : HasResidue g z c) : HasResidue f z c := by
  have hg' : Tendsto (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * g τ) (𝓝[≠] z) (𝓝 c) := hg
  have h' : (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * f τ)
      =ᶠ[𝓝[≠] z] (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * g τ) :=
    h.mono fun τ hτ => by simp only [hτ]
  exact Tendsto.congr' h'.symm hg'

/-! ## Holomorphic functions have residue zero -/

lemma tendsto_sub_self_nhdsNE (z : ℍ) :
    Tendsto (fun τ : ℍ => ((τ : ℂ) - (z : ℂ))) (𝓝[≠] z) (𝓝 0) := by
  have hcont : Continuous (fun τ : ℍ => ((τ : ℂ) - (z : ℂ))) :=
    UpperHalfPlane.continuous_coe.sub continuous_const
  have h := hcont.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z)
  simpa using h

lemma hasResidue_of_continuousAt {f : ℍ → ℂ} {z : ℍ} (hf : ContinuousAt f z) :
    HasResidue f z 0 := by
  rw [HasResidue]
  have h2 : Tendsto f (𝓝[≠] z) (𝓝 (f z)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have h := (tendsto_sub_self_nhdsNE z).mul h2
  simpa using h

/-- A function holomorphic at `z` has residue `0` there. -/
lemma hasResidue_of_mdifferentiableAt {f : ℍ → ℂ} {z : ℍ}
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f z) : HasResidue f z 0 :=
  hasResidue_of_continuousAt hf.continuousAt

/-- The `MDifferentiableAt`-based notion `Work.Kernels.HasSimplePoleWithResidue` implies the
limit-based `HasResidue`. -/
lemma hasResidue_of_hasSimplePoleWithResidue {f : ℍ → ℂ} {z : ℍ} {c : ℂ}
    (h : Work.Kernels.HasSimplePoleWithResidue f z c) : HasResidue f z c := by
  have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => f τ - c * (((τ : ℂ) - (z : ℂ)))⁻¹) z := h
  have hcont := hmd.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds :
    𝓝[≠] z ≤ 𝓝 z)
  rw [HasResidue]
  have key : (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * f τ)
      =ᶠ[𝓝[≠] z]
        fun τ : ℍ => c + ((τ : ℂ) - (z : ℂ)) *
          (f τ - c * (((τ : ℂ) - (z : ℂ)))⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτne : τ ≠ z := by simpa using hτ
    have hτ' : ((τ : ℂ) - (z : ℂ)) ≠ 0 := sub_ne_zero.mpr (fun hh => hτne (UpperHalfPlane.ext hh))
    have hc : ((τ : ℂ) - (z : ℂ)) * (c * (((τ : ℂ) - (z : ℂ)))⁻¹) = c := by
      rw [← mul_assoc, mul_comm ((τ : ℂ) - (z : ℂ)) c, mul_assoc, mul_inv_cancel₀ hτ', mul_one]
    rw [mul_sub, hc]
    ring
  refine Tendsto.congr' key.symm ?_
  have h := (tendsto_sub_self_nhdsNE z).mul hcont
  simpa using h.const_add c

/-! ## The residue from the cleared kernel -/

/-- **The residue of a function whose cleared form is holomorphic.**  Suppose that near `z₀`
(off `z₀`) the function `f` satisfies `(j(τ) - j(z))·f τ = A τ` where `A` is holomorphic at
`z₀`, that `j(z₀) = j(z)`, and that the difference quotient
`(j(τ) - j(z₀))/(τ - z₀)` tends to a nonzero limit `c` (namely `j'(z₀)`).  Then `f` has
residue `A(z₀)/c` at `z₀`.

This is the computational core of CKMRV Theorem 4.9(3): the residue of the kernel at a pole is
the value of the *cleared* kernel at the pole, divided by `j'(z₀) = -2πiE₄²E₆/Δ`. -/
theorem hasResidue_of_cleared {f A : ℍ → ℂ} {z z₀ : ℍ} {c : ℂ}
    (hA : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) A z₀) (hj : jInvariantFun z₀ = jInvariantFun z)
    (hc : Tendsto (fun τ : ℍ => (jInvariantFun τ - jInvariantFun z₀) / ((τ : ℂ) - (z₀ : ℂ)))
      (𝓝[≠] z₀) (𝓝 c))
    (hc0 : c ≠ 0)
    (hf : ∀ᶠ τ in 𝓝[≠] z₀, f τ * (jInvariantFun τ - jInvariantFun z) = A τ) :
    HasResidue f z₀ (A z₀ / c) := by
  have hne : ∀ᶠ τ in 𝓝[≠] z₀,
      (jInvariantFun τ - jInvariantFun z₀) / ((τ : ℂ) - (z₀ : ℂ)) ≠ 0 :=
    hc.eventually (eventually_ne_nhds hc0)
  have key : (fun τ : ℍ => ((τ : ℂ) - (z₀ : ℂ)) * f τ)
      =ᶠ[𝓝[≠] z₀]
        fun τ : ℍ => A τ / ((jInvariantFun τ - jInvariantFun z₀) / ((τ : ℂ) - (z₀ : ℂ))) := by
    filter_upwards [hne, hf, self_mem_nhdsWithin] with τ hu hfτ hτ
    have hτne : τ ≠ z₀ := by simpa using hτ
    have hτ' : ((τ : ℂ) - (z₀ : ℂ)) ≠ 0 := sub_ne_zero.mpr (fun hh => hτne (UpperHalfPlane.ext hh))
    have hu' : jInvariantFun τ - jInvariantFun z₀ ≠ 0 := by
      intro h0; exact hu (by rw [h0, zero_div])
    have hz : jInvariantFun τ - jInvariantFun z ≠ 0 := by rw [← hj]; exact hu'
    have hfτ' : f τ = A τ / (jInvariantFun τ - jInvariantFun z) := by
      rw [eq_div_iff hz]
      exact hfτ
    rw [hfτ', ← hj]
    field_simp
  rw [HasResidue]
  refine Tendsto.congr' key.symm ?_
  have hA' : Tendsto A (𝓝[≠] z₀) (𝓝 (A z₀)) :=
    hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact hA'.div hc hc0

end Work.Residues
