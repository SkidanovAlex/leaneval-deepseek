/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/` — design (B): the log-coordinate Friedrichs `ε`-scheme

This is the vocabulary module of the **FTS/StrongEps** area, the replacement of the vacuous
strong-solution route (`FTS_HARD_DESIGN.md`, section *(B)*, and the lead's statement file
`FTS_HARD_STMTS.lean.txt`, namespace `Work.FTS.ScratchC46H`).

## Why the log coordinates

The scheme mollifies the profile `g` in the two coordinates

  `s = log z`,   `ζ = log tan θ`

(the paper's `D_z = z∂_z` is `∂_s`, and `D_θ = sin(2θ)∂_θ` is `2∂_ζ`).  The two boundaries of the
quadrant `z = 0` and `θ = 0, π/2` move to `s = -∞`, `ζ = ±∞`, so the quadrant becomes the whole
plane and the substitution

  `z ↦ z · e^{-p₁}`,   `θ ↦ arctan (tan θ · e^{-p₂})`

is exactly the *translation* `(s,ζ) ↦ (s - p₁, ζ - p₂)`.  Consequently the mollifier `J_ε` of
`Jeps` below is a genuine two-dimensional convolution *in the log coordinates*, and

* `J_ε` commutes with `D_z` (hence with every `D_z^j`) and with `D_θ` (hence with every
  `D_θ^i`), so also with the mixed operators `D_z^j D_θ^i` of `Spaces.mixed`;
* the paper's weights change by a factor `e^{C|p|}` under the shift, so all the weighted norms
  are preserved up to `e^{Cε}`.

Both facts are the content of **E1** of the design; the commutativity is proved in
`Submission/Work/FTS/StrongEps/Commute.lean` and the weight bounds in the `E1`-modules.

## What lives here

* the two shifts `zShift`, `thShift` and the log-coordinate maps `sOf`, `zOfS`, `zetaOf`,
  `thOfZeta`, with the identity `zetaOf (thShift θ p) = zetaOf θ - p`;
* the two-dimensional kernel `Jker ρ ε`, and the class `IsMollKernel ρ` of admissible `ρ`
  (continuous, supported in the unit ball, nonnegative, total mass `1`);
* **`Jeps`**, **`Jfam`**, **`IsEpsSol`**, **`EpsUniform`** — verbatim from the lead's statement
  file (`FTS_HARD_STMTS.lean.txt`), with the same names and the same conventions;
* **`global_strong2`**, the target of the area (in `Submission/Work/FTS/StrongEps/Assembly.lean`).

Nothing here is a reduction of the target to a new axiom: `IsMollKernel` and the shifts are the
*definitions* the area is built on.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.StrongGlobal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS)

set_option autoImplicit false

/-! ## The log coordinates and the two shifts -/

/-- The open quadrant of the paper's variables. -/
def Quad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem mem_Quad {z θ : ℝ} : (z, θ) ∈ Quad ↔ 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2) := Iff.rfl

/-- The `z`-shift of the mollifier: `s ↦ s - p`, i.e. `z ↦ z e^{-p}` in the variable `z`. -/
def zShift (z p : ℝ) : ℝ := z * Real.exp (-p)

/-- The `θ`-shift of the mollifier: `ζ ↦ ζ - p`, i.e. `θ ↦ arctan (tan θ · e^{-p})`. -/
def thShift (θ p : ℝ) : ℝ := Real.arctan (Real.tan θ * Real.exp (-p))

/-- The log-coordinate `s = log z`. -/
def sOf (z : ℝ) : ℝ := Real.log z

/-- The inverse log-coordinate `z = e^s`. -/
def zOfS (s : ℝ) : ℝ := Real.exp s

/-- The log-coordinate `ζ = log tan θ`. -/
def zetaOf (θ : ℝ) : ℝ := Real.log (Real.tan θ)

/-- The inverse log-coordinate `θ = arctan e^ζ`. -/
def thOfZeta (ζ : ℝ) : ℝ := Real.arctan (Real.exp ζ)

/-- The pull-back of a profile to the log-coordinates `(s,ζ) = (log z, log tan θ)`:
`Jeps` is, in these coordinates, the convolution of `logPull f` with `Jker ρ ε`. -/
def logPull (f : Fn) : ℝ × ℝ → ℝ := fun x => f (Real.exp x.1) (Real.arctan (Real.exp x.2))

/-! ## The mollifier kernel

`IsMollKernel ρ` is the class of admissible kernels: `ρ` is continuous, supported in the closed
unit ball of `ℝ²`, nonnegative, with total mass `1`.  Every statement of the `E1` chapter carries
it, and it is the only hypothesis on `ρ` anywhere in the area. -/

/-- **The admissible mollifier kernels.**  `ρ` is continuous, supported in the closed unit ball,
nonnegative and has total mass `1`.  (The support condition makes every `p`-integral below an
integral over the compact ball of radius `ε`; the mass condition makes `J_ε` approximate the
identity.) -/
structure IsMollKernel (ρ : ℝ × ℝ → ℝ) : Prop where
  /-- continuity of the kernel. -/
  cont : Continuous ρ
  /-- the support is contained in the closed unit ball. -/
  support : ∀ p : ℝ × ℝ, ρ p ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1
  /-- nonnegativity. -/
  nonneg : ∀ p : ℝ × ℝ, 0 ≤ ρ p
  /-- total mass one. -/
  mass : ∫ p : ℝ × ℝ, ρ p = 1

/-- **The smooth mollifier kernels**: the class needed by the *smoothing* property of `J_ε`
(`E1` of the design, `Jeps_contDiffOn`).  A merely continuous admissible kernel does *not*
suffice: in the log coordinates `J_ε` is the convolution with `Jker ρ ε`, and the derivatives can
only be pushed onto the kernel (the profile being mollified is merely locally integrable), so the
kernel itself must be `C^∞`. -/
structure IsSmoothKernel (ρ : ℝ × ℝ → ℝ) : Prop where
  /-- smoothness at every finite order (the order `⊤` of this Mathlib is *analyticity*). -/
  smooth : ∀ n : ℕ, ContDiff ℝ n ρ
  /-- the mass, support and nonnegativity conditions. -/
  moll : IsMollKernel ρ

/-- The rescaled kernel `k_ε(p) = ε^{-2} ρ(p/ε)` of `Jeps`, i.e. the density of `ρ` at scale
`ε` in the two log-coordinates. -/
def Jker (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ := ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)

/-! ## The mollifier `Jeps`, the family `Jfam`, the `ε`-scheme `IsEpsSol` and its uniform bound
`EpsUniform` (verbatim from `FTS_HARD_STMTS.lean.txt`) -/

/-- **(B) the log-coordinate mollifier** `J_ε`, verbatim from the lead's statement file.

In the log coordinates `s = log z`, `ζ = log tan θ` this is the convolution of `logPull f` with
the kernel `Jker ρ ε`; on the boundary of the quadrant (where the log coordinates degenerate) it
is defined to be `0`. -/
def Jeps (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) : Fn := fun z θ =>
  if 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2) then
    ∫ p : ℝ × ℝ, ε⁻¹ ^ 2 * ρ (ε⁻¹ • p) *
      f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))
  else 0

/-- The same, applied slicewise to a family (verbatim). -/
def Jfam (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fam) : Fam := fun z θ τ => Jeps ρ ε (slice g τ) z θ

/-- **the `ε`-scheme on `[0,T]`**: `∂_τ g = J_ε[𝓛-part + RHS](J_ε g)`, with
`Ψ = Φs + EllSol(J_ε g)` (verbatim). -/
def IsEpsSol (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn) (g : Fam) :
    Prop :=
  (∀ z θ, g z θ 0 = g₀ z θ) ∧
  ∀ z θ τ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → τ ∈ Set.Icc 0 T →
    HasDerivWithinAt (fun s => g z θ s)
      (Jeps ρ ε (fun z' θ' => dynLin α (Jfam ρ ε g) τ z' θ'
          + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Jfam ρ ε g)) (Jfam ρ ε g) τ z' θ') z θ)
      (Set.Icc 0 T) τ

/-- **(B) uniform `ε`-bounds on every `[0,T]`** (verbatim): for every `T > 0` there is `ε₁ > 0`
such that for every `ε ∈ (0, ε₁]` the `ε`-scheme has a solution on `[0,T]` whose mollified
slices are of size `≤ C₀α²` and whose own slices are of size `≤ K e^{KT}`. -/
def EpsUniform (α : ℝ) (ρ : ℝ × ℝ → ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn) (C₀ K : ℝ) : Prop :=
  ∀ T > 0, ∃ ε₁ > 0, ∀ ε ∈ Set.Ioc 0 ε₁, ∃ g : Fam, IsEpsSol α ρ ε T Φs E g₀ g ∧
    ∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (Jfam ρ ε g) τ) ≤ C₀ * α ^ 2 ∧
      Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ K * Real.exp (K * T)

/-! ## Elementary consequences -/

@[simp] theorem Jfam_apply (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fam) (z θ τ : ℝ) :
    Jfam ρ ε g z θ τ = Jeps ρ ε (slice g τ) z θ := rfl

@[simp] theorem slice_Jfam (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fam) (τ : ℝ) :
    slice (Jfam ρ ε g) τ = Jeps ρ ε (slice g τ) := rfl

/-- The value of `Jeps` on the open quadrant: the log-coordinate convolution. -/
theorem Jeps_eq_integral (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Jeps ρ ε f z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z p.1) (thShift θ p.2) := by
  simp only [Jeps, Jker, zShift, thShift, if_pos (show 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2) from ⟨hz, hθ⟩)]

/-- The value of `Jeps` at the boundary of the quadrant is `0`. -/
theorem Jeps_eq_zero (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) {z θ : ℝ}
    (h : ¬(0 < z ∧ θ ∈ Set.Ioo 0 (π / 2))) : Jeps ρ ε f z θ = 0 := by
  simp only [Jeps, if_neg h]

theorem Jeps_eq_zero_of_le (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) {z θ : ℝ} (hz : z ≤ 0) :
    Jeps ρ ε f z θ = 0 :=
  Jeps_eq_zero ρ ε f (fun h => absurd h.1 (not_lt.2 hz))

theorem Jeps_eq_zero_of_theta (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) {z θ : ℝ}
    (hθ : θ ∉ Set.Ioo 0 (π / 2)) : Jeps ρ ε f z θ = 0 :=
  Jeps_eq_zero ρ ε f (fun h => hθ h.2)

/-- `Jeps` depends only on the profile. -/
theorem Jeps_congr (ρ : ℝ × ℝ → ℝ) (ε : ℝ) {f f' : Fn} (h : ∀ z θ, f z θ = f' z θ) :
    ∀ z θ, Jeps ρ ε f z θ = Jeps ρ ε f' z θ := by
  intro z θ
  by_cases hc : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · rw [Jeps_eq_integral ρ ε f hc.1 hc.2, Jeps_eq_integral ρ ε f' hc.1 hc.2]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [h]
  · rw [Jeps_eq_zero ρ ε f hc, Jeps_eq_zero ρ ε f' hc]

/-- `Jeps` of the zero profile. -/
@[simp] theorem Jeps_zero (ρ : ℝ × ℝ → ℝ) (ε : ℝ) :
    Jeps ρ ε (fun _ _ => 0) = fun _ _ => 0 := by
  funext z θ
  by_cases hc : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · rw [Jeps_eq_integral ρ ε _ hc.1 hc.2]
    simp
  · rw [Jeps_eq_zero ρ ε _ hc]

/-! ## The log coordinates -/

theorem zShift_pos {z p : ℝ} (hz : 0 < z) : 0 < zShift z p := by
  simpa only [zShift] using mul_pos hz (Real.exp_pos (-p))

theorem sOf_zShift {z p : ℝ} (hz : 0 < z) : sOf (zShift z p) = sOf z - p := by
  simp only [sOf, zShift, Real.log_mul hz.ne' (Real.exp_ne_zero _), Real.log_exp, sub_eq_add_neg]

theorem zOfS_sOf {z : ℝ} (hz : 0 < z) : zOfS (sOf z) = z := by
  simp only [zOfS, sOf, Real.exp_log hz]

theorem tan_thShift (θ p : ℝ) : Real.tan (thShift θ p) = Real.tan θ * Real.exp (-p) := by
  simp only [thShift, Real.tan_arctan]

theorem zetaOf_thShift {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    zetaOf (thShift θ p) = zetaOf θ - p := by
  have ht : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
  simp only [zetaOf, thShift, Real.tan_arctan]
  rw [Real.log_mul ht.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem thShift_mem {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    thShift θ p ∈ Set.Ioo 0 (π / 2) := by
  have ht : 0 < Real.tan θ * Real.exp (-p) :=
    mul_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2) (Real.exp_pos _)
  exact ⟨(Real.arctan_pos (x := Real.tan θ * Real.exp (-p))).2 ht,
    Real.arctan_lt_pi_div_two _⟩

theorem thOfZeta_zetaOf {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : thOfZeta (zetaOf θ) = θ := by
  have ht : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
  have hlt : -(π / 2) < θ := by linarith [hθ.1, Real.pi_pos]
  simp only [thOfZeta, zetaOf, Real.exp_log ht, Real.arctan_tan hlt hθ.2]

/-- **The shift is the translation `(s,ζ) ↦ (s - p₁, ζ - p₂)` in the log coordinates**: this is
the identity that makes `Jeps` a convolution. -/
theorem logPull_shift (f : Fn) {z θ : ℝ} {p : ℝ × ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    logPull f (sOf z - p.1, zetaOf θ - p.2) = f (zShift z p.1) (thShift θ p.2) := by
  have h1 : Real.exp (sOf z - p.1) = zShift z p.1 := by
    rw [sOf, Real.exp_sub, Real.exp_log hz, zShift, div_eq_mul_inv, ← Real.exp_neg]
  have h2 : Real.exp (zetaOf θ - p.2) = Real.tan θ * Real.exp (-p.2) := by
    rw [zetaOf, Real.exp_sub, Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2),
      div_eq_mul_inv, ← Real.exp_neg]
  simp only [logPull, thShift, h1, h2]

/-- The log coordinates are a bijection of the quadrant onto the whole plane
`(s,ζ) ∈ ℝ²`, with inverse `(z,θ) = (e^s, arctan e^ζ)`. -/
theorem quadrant_logCoord {z θ : ℝ} (h : (z, θ) ∈ Quad) :
    (zOfS (sOf z), thOfZeta (zetaOf θ)) = (z, θ) := by
  rw [mem_Quad] at h
  rw [zOfS_sOf h.1, thOfZeta_zetaOf h.2]

end Work.FTS.StrongEps
