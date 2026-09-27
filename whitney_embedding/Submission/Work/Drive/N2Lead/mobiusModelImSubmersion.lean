import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperStarRowKit
import Submission.Work.Drive.N2Lead.mobiusPacketDefs
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The Möbius model is an `(f, Im (Z ·)²)`-submersion in the kernel of `df`

This file proves `Work.Drive.N2Lead.mobiusModelImSubmersion`: on the scaled Morse chart of the
saddle (`Z` the scaled complex Morse coordinate, `f = f p + lam0² · Re (Z ·)²` on the model ball)
a *non-zero* tangent vector `v` killed by `df` can never be killed by the differential of
`Im (Z ·)²`.  Equivalently: `Im (Z ·)²` is a submersion from each level of `f` (inside the model
ball) to `ℝ`.

The reason is the Cauchy–Riemann structure of `ζ ↦ ζ²`: for `z ≠ 0` the two real functionals
`d(Re ζ²)_z` and `d(Im ζ²)_z` have trivial common kernel.  Indeed both are the real and imaginary
part of `w ↦ 2 z w`, and a complex number whose real and imaginary part both vanish is zero, so
`2 z w = 0`, i.e. `w = 0` as soon as `z ≠ 0`.  Here `z = Z y ≠ 0` because the level value is
strictly above the critical one: `lam0² · Re (Z y)² = 3η/2 > 0`.  Injectivity of `dZ` at `y`
(the packet's `hZimm`, the immersion row of the chart) then converts `w = 0` into `v = 0`.

This is the model-side input of the Möbius saddle window: it says that on the upper level
`f = f p + 3η/2` the function `Im (Z ·)²` is a *coordinate* transverse to the level of `f`, which
is exactly what the two-piece assembly of the window uses to separate the model piece from the
transported picture.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

/-- The derivative of `ζ ↦ Im (ζ²)` on `ℂ`, in the `mfderiv` normalisation: the model with
corners on `ℂ` (resp. `ℝ`) is the identity, so the `mfderiv` is the ordinary derivative. -/
lemma mfderiv_sq_im_apply_self (z v : ℂ) :
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun ζ : ℂ => (ζ ^ 2).im) z) v = (2 * z * v).im := by
  rw [mfderiv_eq_fderiv]
  exact Work.Drive.N2.fderiv_sq_im_apply z v

/-- **The two real components of `w ↦ 2 z w` have trivial common kernel for `z ≠ 0`.**  If both
the real and the imaginary part of `2 z w` vanish, then `2 z w = 0`, hence `w = 0`. -/
lemma eq_zero_of_sq_components_eq_zero {z w : ℂ} (hz : z ≠ 0)
    (hre : (2 * z * w).re = 0) (him : (2 * z * w).im = 0) : w = 0 := by
  have h : 2 * z * w = 0 := Complex.ext hre him
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' (mul_ne_zero (by norm_num) hz)
  · exact h'

theorem mobiusModelImSubmersion {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (S : Work.Drive.N2Lead.MobiusPacket D η)
    {y : M} (hy : f y = f p + 3 * η / 2)
    (hreg : y ∈ Work.Drive.N2.saddleRegion
      (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z (39 / 20))
    {v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y}
    (hv : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) f y v = 0) (hvne : v ≠ 0) :
    mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) (fun z : M => ((S.Z z) ^ 2).im) y v ≠ 0 := by
  -- `y` lies in the model ball, which is open
  have hyU : y ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) := hreg.1
  have hUopen : IsOpen (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) :=
    isOpen_modelBall_mobius (D.φ D.j) (D.ρ D.j)
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- differentiability of the chart coordinate at `y`
  have hZmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℂ) S.Z y :=
    (S.hZsm.contMDiffAt (hUopen.mem_nhds hyU)).mdifferentiableAt hn
  -- the normal form of `f` holds on a neighbourhood of `y`
  have hfeq : f =ᶠ[𝓝 y] (fun x : M => f p + S.lam0 ^ 2 * ((S.Z x) ^ 2).re) := by
    filter_upwards [hUopen.mem_nhds hyU] with x hx
    exact S.hlev x hx
  -- the image of `v` under `dZ`
  let w : ℂ := (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) S.Z y) v
  -- ### The real part of `2 · Z y · w` vanishes
  have hqc : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ)
      (fun ζ : ℂ => f p + S.lam0 ^ 2 * (ζ ^ 2).re) (S.Z y) :=
    (mdifferentiableAt_iff_differentiableAt (𝕜 := ℝ)).mpr (by fun_prop)
  have h1p : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun x : M => f p + S.lam0 ^ 2 * ((S.Z x) ^ 2).re) y v = 0 := by
    rw [← hfeq.mfderiv_eq_v433]
    exact hv
  have h1'' : (fderiv ℝ (fun ζ : ℂ => S.lam0 ^ 2 * (ζ ^ 2).re) (S.Z y)) w = 0 := by
    have h1' : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        ((fun ζ : ℂ => f p + S.lam0 ^ 2 * (ζ ^ 2).re) ∘ S.Z) y v = 0 := h1p
    rw [mfderiv_comp_apply (f := S.Z)
      (g := fun ζ : ℂ => f p + S.lam0 ^ 2 * (ζ ^ 2).re) y hqc hZmd v] at h1'
    rw [mfderiv_eq_fderiv, fderiv_const_add] at h1'
    exact h1'
  have hre : (2 * S.Z y * w).re = 0 := by
    have h := h1''
    rw [Work.Drive.N2.fderiv_smul_sq_re_apply] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (pow_ne_zero 2 (ne_of_gt S.hlam0pos))
    · exact h'
  -- ### `Z y ≠ 0`
  have hZne : S.Z y ≠ 0 := by
    have h := S.hlev y hyU
    have hsq : S.lam0 ^ 2 * ((S.Z y) ^ 2).re = 3 * η / 2 := by linarith
    have hpos : 0 < ((S.Z y) ^ 2).re := by
      have hl : (0 : ℝ) < S.lam0 ^ 2 := pow_pos S.hlam0pos 2
      have h32 : (0 : ℝ) < 3 * η / 2 := by linarith
      nlinarith [hsq]
    intro h0
    rw [h0] at hpos
    simp at hpos
  -- ### The imaginary part of the differential of `Im (Z ·)²`
  have hqi : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun ζ : ℂ => (ζ ^ 2).im) (S.Z y) :=
    (mdifferentiableAt_iff_differentiableAt (𝕜 := ℝ)).mpr (by fun_prop)
  have hgoal_eq : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => ((S.Z z) ^ 2).im) y v
      = (2 * S.Z y * w).im := by
    have h2' : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) ((fun ζ : ℂ => (ζ ^ 2).im) ∘ S.Z) y v
        = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun ζ : ℂ => (ζ ^ 2).im) (S.Z y))
            ((mfderiv (𝓡 2) 𝓘(ℝ, ℂ) S.Z y) v) :=
      mfderiv_comp_apply (f := S.Z) (g := fun ζ : ℂ => (ζ ^ 2).im) y hqi hZmd v
    have h3 : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun ζ : ℂ => (ζ ^ 2).im) (S.Z y)) w
        = (2 * S.Z y * w).im := mfderiv_sq_im_apply_self (S.Z y) w
    show mfderiv (𝓡 2) 𝓘(ℝ, ℝ) ((fun ζ : ℂ => (ζ ^ 2).im) ∘ S.Z) y v
      = (2 * S.Z y * w).im
    exact h2'.trans h3
  intro h0
  have him : (2 * S.Z y * w).im = 0 := by
    rw [← hgoal_eq]
    exact h0
  have hzero : w = 0 := eq_zero_of_sq_components_eq_zero hZne hre him
  have hzero' : (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) S.Z y) v = 0 := hzero
  exact hvne (S.hZimm y hyU (by rw [hzero', map_zero]))

end Work.Drive.N2Lead
