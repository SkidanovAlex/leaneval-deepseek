import Submission.PaperBand.McStraight
import Submission.PaperBand.KernelSegments
import Submission.PaperBand.SecondDeriv
import Submission.Commons.Analysis.InnerProductSpace.orthonormal_triple_expansion

open OptimalMoebius Topology ContDiff
open scoped BigOperators
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Brick C, piece (i) — a unit kernel-direction field near the bend arc

Setup: on a maximal kernel segment `z(s) = x₀ + s•w₀` (`0 < s < β`) with
`w₀ 0 ≠ 0` (a crossing direction), the shape-operator matrix
`S = dNentry` has the kernel spanned by `w₀`.  The *mirror kernel field*
`V2f f x = c(x)•e₀ − b(x)•e₁` (`McStraight`) is a section of the kernel
(`V2f_mem_ker`) and is nonzero exactly where `S ≠ 0` cannot be killed along
`w₀` — more precisely:

* `V2f f x ≠ 0` at every interior point `x` with `dN f x ≠ 0` whose kernel
  contains a vector with nonzero `0`-coordinate (a *crossing* kernel
  direction); hence on `U`-points of the arc (`dN(z(s)) ≠ 0`),
  `V2f f (z(s)) ≠ 0`;
* by continuity and compactness, `‖V2f f x‖ ≥ c > 0` in a whole tube around
  a compact arc portion, so `x ↦ V2f f x / ‖V2f f x‖` is a smooth **unit**
  kernel-direction field there (this is the field whose integral lines are
  the nearby bends — the connectors of Brick C).

The main new fact is the converse direction `dNentry = 0 → dN = 0` (the
entries determine the shape operator because it is tangent-valued and the
tangent frame is orthonormal).
-/

noncomputable section
namespace Submission.PaperBand

/-- **The entries determine the shape operator**: if all `dNentry f x i j`
vanish at an interior point `x`, then `dN f x = 0`.  (The shape operator is
tangent-valued — `dN_tangent_valued` — and the tangent frame `(tangent₀,
tangent₁, unitNormal)` is an orthonormal basis of `ℝ³`.) -/
lemma dN_eq_zero_of_dNentry_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior)
    (hent : ∀ i j : Fin 2, dNentry f x i j = 0) : dN f x = 0 := by
  ext v
  rw [clm_apply_vec_decomp (dN f x) v]
  -- it suffices to show dN f x applied to each basis vector is zero
  have hde0 : (dN f x) !₂[1, 0] = 0 := by
    have hxn : x ∈ unitStrip := stripInterior_subset_unitStrip hx
    have hexp := Commons.Analysis.InnerProductSpace.orthonormal_triple_expansion
      (t₀ := tangent₀ f x) (t₁ := tangent₁ f x) (Nx := unitNormal f x)
      (v := (dN f x) !₂[1, 0])
      (tangent₀_norm hf x hxn) (tangent₁_norm hf x hxn) (unitNormal_norm hf x hxn)
      (tangent₀₁_orthogonal hf x hxn) (tangent₀_normal_orthogonal hf x hxn)
      (tangent₁_normal_orthogonal hf x hxn)
    have h0 : inner ℝ ((dN f x) !₂[1, 0]) (tangent₀ f x) = 0 := by
      have hd := hent 0 0
      simpa [dNentry] using hd
    have h1 : inner ℝ ((dN f x) !₂[1, 0]) (tangent₁ f x) = 0 := by
      have hd := hent 0 1
      simpa [dNentry] using hd
    have hN : inner ℝ ((dN f x) !₂[1, 0]) (unitNormal f x) = 0 :=
      dN_tangent_valued hf x hx !₂[1, 0]
    rw [hexp]
    simp [h0, h1, hN]
  have hde1 : (dN f x) !₂[0, 1] = 0 := by
    have hxn : x ∈ unitStrip := stripInterior_subset_unitStrip hx
    have hexp := Commons.Analysis.InnerProductSpace.orthonormal_triple_expansion
      (t₀ := tangent₀ f x) (t₁ := tangent₁ f x) (Nx := unitNormal f x)
      (v := (dN f x) !₂[0, 1])
      (tangent₀_norm hf x hxn) (tangent₁_norm hf x hxn) (unitNormal_norm hf x hxn)
      (tangent₀₁_orthogonal hf x hxn) (tangent₀_normal_orthogonal hf x hxn)
      (tangent₁_normal_orthogonal hf x hxn)
    have h0 : inner ℝ ((dN f x) !₂[0, 1]) (tangent₀ f x) = 0 := by
      have hd := hent 1 0
      simpa [dNentry] using hd
    have h1 : inner ℝ ((dN f x) !₂[0, 1]) (tangent₁ f x) = 0 := by
      have hd := hent 1 1
      simpa [dNentry] using hd
    have hN : inner ℝ ((dN f x) !₂[0, 1]) (unitNormal f x) = 0 :=
      dN_tangent_valued hf x hx !₂[0, 1]
    rw [hexp]
    simp [h0, h1, hN]
  simp [hde0, hde1]

/-- **The mirror kernel field does not vanish at `U`-points whose kernel
contains a crossing direction**: if `dN f x ≠ 0` and `dN f x w₀ = 0` with
`w₀ 0 ≠ 0`, then `V2f f x ≠ 0`.  (If `V2f f x = 0`, its entries `b = c`
vanish; the kernel equation along `w₀` then forces `a = 0`, so all entries
vanish and `dN f x = 0`.) -/
lemma V2f_ne_zero_of_kernel_crossing {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x w₀ : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    (hw0 : w₀ 0 ≠ 0) (hker : dN f x w₀ = 0) : V2f f x ≠ 0 := by
  intro hv2
  -- coordinates of V2f x = (c)•e₀ + (-b)•e₁ vanish:
  have hc : dNentry f x 1 1 = 0 := by
    have hc0 : (V2f f x) 0 = 0 := congrArg (fun z : ℝ² => z 0) hv2
    have hb0 : (V2f f x) 0 = dNentry f x 1 1 := by
      simp [V2f]
    rwa [hb0] at hc0
  have hb : dNentry f x 1 0 = 0 := by
    have hc1 : (V2f f x) 1 = 0 := congrArg (fun z : ℝ² => z 1) hv2
    have hb1 : (V2f f x) 1 = -(dNentry f x 1 0) := by
      simp [V2f]
    have : -(dNentry f x 1 0) = 0 := by simpa [hb1] using hc1
    linarith
  -- the kernel equation along w₀ gives (w₀ 0) * a + (w₀ 1) * b = 0
  have hw0t : inner ℝ ((dN f x) w₀) (tangent₀ f x) = 0 := by
    simp [hker]
  have hdecomp := clm_apply_vec_decomp (dN f x) w₀
  have hmain0 : (w₀ 0) * dNentry f x 0 0 + (w₀ 1) * dNentry f x 1 0 = 0 := by
    have hcalc : inner ℝ ((dN f x) w₀) (tangent₀ f x) =
        (w₀ 0) * dNentry f x 0 0 + (w₀ 1) * dNentry f x 1 0 := by
      rw [hdecomp]
      rw [inner_add_left, inner_smul_left, inner_smul_left]
      simp [dNentry]
    rwa [hcalc] at hw0t
  have ha : dNentry f x 0 0 = 0 := by
    rw [hb] at hmain0
    have h0 : (w₀ 0) * dNentry f x 0 0 = 0 := by
      simpa using hmain0
    exact mul_eq_zero.mp h0 |>.resolve_left hw0
  -- all four entries vanish (symmetry gives 0 1 = 1 0)
  have h01 : dNentry f x 0 1 = 0 := by
    have hs := shapeOperator_symm hf x hx (0 : Fin 2) (1 : Fin 2)
    rwa [hb] at hs
  have hent : ∀ i j : Fin 2, dNentry f x i j = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, h01]
  exact hdN (dN_eq_zero_of_dNentry_zero hf hx hent)


/-- **`V2f` does not vanish on the `U`-points of a kernel segment in a
crossing direction**: if `w₀ 0 ≠ 0`, the kernel condition and `dN ≠ 0` hold
at `x₀ + s•w₀ ∈ stripInterior`, then `V2f f (x₀ + s•w₀) ≠ 0`. -/
lemma V2f_ne_zero_on_kernel_segment {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ w₀ : ℝ²} {β s : ℝ} (hseg : ∀ s ∈ Set.Ioo (0 : ℝ) β, x₀ + s • w₀ ∈ stripInterior)
    (hker : ∀ s ∈ Set.Ioo (0 : ℝ) β, dN f (x₀ + s • w₀) w₀ = 0)
    (hU : ∀ s ∈ Set.Ioo (0 : ℝ) β, dN f (x₀ + s • w₀) ≠ 0)
    (hs : s ∈ Set.Ioo (0 : ℝ) β) (hw0 : w₀ 0 ≠ 0) :
    V2f f (x₀ + s • w₀) ≠ 0 :=
  V2f_ne_zero_of_kernel_crossing hf (hseg s hs) (hU s hs) hw0 (hker s hs)

/-- **`V2f` is parallel to the segment direction on the arc**: at each
`U`-point of the kernel segment (rank-one shape operator), the mirror kernel
vector `V2f` is a scalar multiple of `w₀`. -/
lemma V2f_parallel_w₀_on_kernel_segment {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ w₀ : ℝ²} {β s : ℝ} (hseg : ∀ s ∈ Set.Ioo (0 : ℝ) β, x₀ + s • w₀ ∈ stripInterior)
    (hker : ∀ s ∈ Set.Ioo (0 : ℝ) β, dN f (x₀ + s • w₀) w₀ = 0)
    (hU : ∀ s ∈ Set.Ioo (0 : ℝ) β, dN f (x₀ + s • w₀) ≠ 0)
    (hs : s ∈ Set.Ioo (0 : ℝ) β) (hw₀ : w₀ ≠ 0) :
    ∃ c : ℝ, V2f f (x₀ + s • w₀) = c • w₀ :=
  kernel_direction_parallel hf (hseg s hs) (hU s hs) (hker s hs)
    (V2f_mem_ker hf (x₀ + s • w₀) (hseg s hs)) hw₀


/-- **The unit kernel-direction field**: the normalization of the mirror
kernel field `V2f`, wherever it is nonzero:

    unitKernelDir f x := (‖V2f f x‖⁻¹) • V2f f x

It is a unit vector in the kernel of the shape operator at `x` (when
`V2f f x ≠ 0`), i.e. a unit tangent to the bend through `x`. -/
def unitKernelDir (f : ℝ² → ℝ³) (x : ℝ²) : ℝ² :=
  (‖V2f f x‖⁻¹) • V2f f x

/-- The unit kernel direction has norm `1` wherever `V2f` is nonzero. -/
lemma norm_unitKernelDir {f : ℝ² → ℝ³} {x : ℝ²} (h : V2f f x ≠ 0) :
    ‖unitKernelDir f x‖ = 1 := by
  dsimp [unitKernelDir]
  have hnorm : ‖V2f f x‖ ≠ 0 := norm_ne_zero_iff.mpr h
  calc
    ‖(‖V2f f x‖⁻¹) • V2f f x‖ = ‖(‖V2f f x‖⁻¹ : ℝ)‖ * ‖V2f f x‖ := by rw [norm_smul]
    _ = (‖V2f f x‖⁻¹) * ‖V2f f x‖ := by
      rw [show ‖(‖V2f f x‖⁻¹ : ℝ)‖ = ‖V2f f x‖⁻¹ by
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg]
        exact inv_nonneg.mpr (norm_nonneg _)]
    _ = 1 := by field_simp [hnorm]

/-- The unit kernel direction is a nonzero vector wherever it is defined. -/
lemma unitKernelDir_ne_zero {f : ℝ² → ℝ³} {x : ℝ²} (h : V2f f x ≠ 0) :
    unitKernelDir f x ≠ 0 := by
  have hn := norm_unitKernelDir h
  intro hz
  have : ‖unitKernelDir f x‖ = 0 := by rw [hz]; norm_num
  linarith

/-- The unit kernel direction lies in the kernel of the shape operator:
`dN f x (unitKernelDir f x) = 0` at every interior point (wherever it is
defined). -/
lemma unitKernelDir_mem_ker {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    dN f x (unitKernelDir f x) = 0 := by
  dsimp [unitKernelDir]
  rw [map_smul]
  simp [V2f_mem_ker hf x hx]

/-- The unit kernel direction varies continuously with the base point at any
interior point where `V2f` is nonzero. -/
lemma continuousAt_unitKernelDir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) (h : V2f f x ≠ 0) :
    ContinuousAt (fun q : ℝ² => unitKernelDir f q) x := by
  have hnorm_ne : ‖V2f f x‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hcont_norm : ContinuousAt (fun q : ℝ² => ‖V2f f q‖) x :=
    (continuousAt_V2f hf x hx).norm
  have hcont_inv : ContinuousAt (fun q : ℝ² => (‖V2f f q‖⁻¹ : ℝ)) x := by
    exact hcont_norm.inv₀ hnorm_ne
  have hsmul : ContinuousAt (fun q : ℝ² => (‖V2f f q‖⁻¹) • V2f f q) x :=
    hcont_inv.smul (continuousAt_V2f hf x hx)
  simpa [unitKernelDir] using hsmul

end Submission.PaperBand


