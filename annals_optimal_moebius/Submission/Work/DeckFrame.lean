import ChallengeDeps
import Submission.PaperBand.Developable
import Submission.PaperBand.PeriodicFacts
import Submission.PaperBand.McStraight
import Submission.Work.LeafContinuity

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open Filter
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The deck map and the developable frame (GREEN)

The band is the quotient of the strip by the deck map
`period a (x0,x1) = (1−x0, x1+a)` with `f (period a x) = f x` on the strip.
This file transfers the developable frame across the deck.  Differentiating
`f (period a x) = f x` on the strip interior gives, for the coordinate
directions `e0 = (1,0)`, `e1 = (0,1)`,

    fderiv f x e0 = − fderiv f (period a x) e0     (period flips e0)
    fderiv f x e1 =   fderiv f (period a x) e1     (period keeps e1)

so the tangent frame flips its `e0`-column and keeps its `e1`-column:

    tangent₀ f (period a x) = − tangent₀ f x
    tangent₁ f (period a x) =   tangent₁ f x

and the unit normal `N = tangent₀ × tangent₁` is ODD under the deck:

    unitNormal f (period a x) = − unitNormal f x

(the deck map is orientation-reversing on the band).  These are the
foundational identities for the deck flip of the shape operator `dN`, its
kernel (the bend direction) and the canonical leaves
(`uHeightBend (y+a) = period-flip (uHeightBend y)`, the missing
`BandFoliation` field), which the next session builds on top of this file.
The proofs differentiate along the straight lines `t ↦ x + t • eᵢ` and use
`HasDerivAt` uniqueness on eventually-equal curves.
-/

noncomputable section
namespace Submission.PaperBand

/-- `period` preserves the strip interior. -/
lemma period_mem_stripInterior (a : ℝ) {x : ℝ²} (hx : x ∈ stripInterior) :
    period a x ∈ stripInterior := by
  have hx0 : x 0 ∈ Set.Ioo (0 : ℝ) 1 := by simpa [stripInterior] using hx
  rw [stripInterior]
  change (period a x) 0 ∈ Set.Ioo (0 : ℝ) 1
  rw [show (period a x) 0 = 1 - x 0 by simp [period]]
  rw [Set.mem_Ioo]
  constructor
  · linarith [(Set.mem_Ioo.mp hx0).2]
  · linarith [(Set.mem_Ioo.mp hx0).1]

/-- The straight line `t ↦ x + t•v` has derivative `v` at `0`. -/
lemma hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x v : E) : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
  have hid : HasDerivAt (fun t : ℝ => t) (1 : ℝ) 0 := hasDerivAt_id 0
  have hsmul : HasDerivAt (fun t : ℝ => t • v) ((1 : ℝ) • v) 0 := hid.smul_const v
  exact HasDerivAt.const_add x (by simpa using hsmul)

/-- Differentiating `f` along the straight line `x + t•v` at `t = 0` gives
`fderiv f x v`. -/
lemma hasDerivAt_fderiv_apply_add_smul {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {x v : E} (hd : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
  have hf : HasFDerivAt f (fderiv ℝ f x) x := hd.hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ => x + t • v) v 0 := hasDerivAt_line x v
  have hx0 : x + (0 : ℝ) • v = x := by simp
  have hf0 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by simpa [hx0] using hf
  exact HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (f := fun t : ℝ => x + t • v)
    (f' := v) (l := f) (l' := fderiv ℝ f x) hf0 hγ

/-- `f` is (fully) differentiable at every point of the strip interior
(from `C∞`-smoothness on the whole closed strip). -/
lemma differentiableAt_of_stripInterior {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) {x : ℝ²} (hx : x ∈ stripInterior) :
    DifferentiableAt ℝ f x := by
  have hd : DifferentiableOn ℝ f unitStrip :=
    (hf.smooth.differentiableOn (by norm_num : (∞ : WithTop ℕ∞) ≠ 0))
  exact hd.differentiableAt (unitStrip_mem_nhds_of_mem_stripInterior hx)

/-- **`f ∘ period` and `f` agree on the strip interior** (this is exactly
the deck periodicity `f (period a x) = f x`). -/
lemma f_period_agree_stripInterior {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    f (period a x) = f x :=
  hf.periodic x (stripInterior_subset_unitStrip hx)

/-! ## The derivative of `f` under the deck, along the two coordinate lines -/

/-- **Derivative flip along `e0`**: for `x` in the strip interior,
`fderiv f x e0 = − fderiv f (period a x) e0` — the deck reverses the
`x0`-direction (differentiating `f(period a (x+t e0)) = f(x+t e0)` at
`t = 0`). -/
lemma fderiv_e0_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    fderiv ℝ f x !₂[1, 0] = -(fderiv ℝ f (period a x) !₂[1, 0]) := by
  let e0 : ℝ² := !₂[1, 0]
  have hdx : DifferentiableAt ℝ f x := differentiableAt_of_stripInterior hf hx
  have hxp : period a x ∈ stripInterior := period_mem_stripInterior a hx
  have hdp : DifferentiableAt ℝ f (period a x) := differentiableAt_of_stripInterior hf hxp
  -- derivative of t ↦ f (x + t e0) at 0
  have hγx : HasDerivAt (fun t : ℝ => f (x + t • e0)) (fderiv ℝ f x e0) 0 :=
    hasDerivAt_fderiv_apply_add_smul hdx
  -- period(x + t e0) = period x + t • (−e0)
  have hpe : ∀ t : ℝ, period a (x + t • e0) = period a x + t • (-e0) := by
    intro t
    ext i <;> fin_cases i <;> simp [period, e0] <;> ring
  -- derivative of t ↦ f (period a (x + t e0)) at 0 = fderiv f (period x) (−e0)
  have hline : HasDerivAt (fun t : ℝ => f (period a x + t • (-e0)))
      (fderiv ℝ f (period a x) (-e0)) 0 :=
    hasDerivAt_fderiv_apply_add_smul hdp
  have hcurve : (fun t : ℝ => f (period a (x + t • e0))) =
      fun t : ℝ => f (period a x + t • (-e0)) := by
    funext t
    rw [hpe t]
  have hγp : HasDerivAt (fun t : ℝ => f (period a (x + t • e0)))
      (fderiv ℝ f (period a x) (-e0)) 0 := by
    simpa [hcurve] using hline
  -- the two curves agree eventually at 0 (deck periodicity, points stay in strip)
  have hev : (fun t : ℝ => f (period a (x + t • e0))) =ᶠ[𝓝 0]
      (fun t : ℝ => f (x + t • e0)) := by
    have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • e0 ∈ unitStrip := by
      have hcont : ContinuousAt (fun t : ℝ => x + t • e0) 0 := (hasDerivAt_line x e0).continuousAt
      have hV : unitStrip ∈ 𝓝 (x + (0 : ℝ) • e0) := by
        simpa using (unitStrip_mem_nhds_of_mem_stripInterior hx)
      exact hcont hV
    filter_upwards [hmem] with t ht
    exact hf.periodic (x + t • e0) ht
  -- so the derivative of t ↦ f (x + t e0) is also fderiv f (period x)(−e0)
  have hγp' : HasDerivAt (fun t : ℝ => f (x + t • e0))
      (fderiv ℝ f (period a x) (-e0)) 0 :=
    hγp.congr_of_eventuallyEq hev.symm
  have heq := HasDerivAt.unique hγx hγp'
  -- fderiv f (period x)(−e0) = −(fderiv f (period x) e0) by linearity
  calc
    fderiv ℝ f x e0 = fderiv ℝ f (period a x) (-e0) := heq
    _ = -(fderiv ℝ f (period a x) e0) := by
      simpa using (map_neg (fderiv ℝ f (period a x)) e0)

/-- **Derivative preservation along `e1`**: `fderiv f x e1 = fderiv f
(period a x) e1` — the deck keeps the `x1`-direction. -/
lemma fderiv_e1_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    fderiv ℝ f x !₂[0, 1] = fderiv ℝ f (period a x) !₂[0, 1] := by
  let e1 : ℝ² := !₂[0, 1]
  have hdx : DifferentiableAt ℝ f x := differentiableAt_of_stripInterior hf hx
  have hxp : period a x ∈ stripInterior := period_mem_stripInterior a hx
  have hdp : DifferentiableAt ℝ f (period a x) := differentiableAt_of_stripInterior hf hxp
  have hγx : HasDerivAt (fun t : ℝ => f (x + t • e1)) (fderiv ℝ f x e1) 0 :=
    hasDerivAt_fderiv_apply_add_smul hdx
  have hpe : ∀ t : ℝ, period a (x + t • e1) = period a x + t • e1 := by
    intro t
    ext i <;> fin_cases i <;> simp [period, e1] <;> ring
  have hline : HasDerivAt (fun t : ℝ => f (period a x + t • e1))
      (fderiv ℝ f (period a x) e1) 0 :=
    hasDerivAt_fderiv_apply_add_smul hdp
  have hcurve : (fun t : ℝ => f (period a (x + t • e1))) =
      fun t : ℝ => f (period a x + t • e1) := by
    funext t
    rw [hpe t]
  have hγp : HasDerivAt (fun t : ℝ => f (period a (x + t • e1)))
      (fderiv ℝ f (period a x) e1) 0 := by
    simpa [hcurve] using hline
  have hev : (fun t : ℝ => f (period a (x + t • e1))) =ᶠ[𝓝 0]
      (fun t : ℝ => f (x + t • e1)) := by
    have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • e1 ∈ unitStrip := by
      have hcont : ContinuousAt (fun t : ℝ => x + t • e1) 0 := (hasDerivAt_line x e1).continuousAt
      have hV : unitStrip ∈ 𝓝 (x + (0 : ℝ) • e1) := by
        simpa using (unitStrip_mem_nhds_of_mem_stripInterior hx)
      exact hcont hV
    filter_upwards [hmem] with t ht
    exact hf.periodic (x + t • e1) ht
  have hγp' : HasDerivAt (fun t : ℝ => f (x + t • e1))
      (fderiv ℝ f (period a x) e1) 0 :=
    hγp.congr_of_eventuallyEq hev.symm
  exact HasDerivAt.unique hγx hγp'

/-! ## The tangent frame and the unit normal under the deck -/

/-- The `0`-column of the frame flips under the deck:
`tangent₀ f (period a x) = − tangent₀ f x` on the strip interior. -/
lemma tangent₀_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    tangent₀ f (period a x) = -tangent₀ f x := by
  have hxp : period a x ∈ stripInterior := period_mem_stripInterior a hx
  have hmain := fderiv_e0_deck hf hx
  unfold tangent₀
  rw [fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_mem_stripInterior hx),
      fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_mem_stripInterior hxp)]
  -- hmain : fderiv f x e0 = −(fderiv f (period x) e0); need the negated form
  have hneg := congrArg Neg.neg hmain
  -- goal: fderiv f (period x) e0 = −(fderiv f x e0)
  simpa using hneg.symm

/-- The `1`-column of the frame is preserved by the deck:
`tangent₁ f (period a x) = tangent₁ f x` on the strip interior. -/
lemma tangent₁_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    tangent₁ f (period a x) = tangent₁ f x := by
  have hxp : period a x ∈ stripInterior := period_mem_stripInterior a hx
  have hmain := fderiv_e1_deck hf hx
  unfold tangent₁
  rw [fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_mem_stripInterior hx),
      fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_mem_stripInterior hxp)]
  exact hmain.symm

/-- The cross product is odd in its first argument:
`(−a) ⨯₃ b = −(a ⨯₃ b)` (coordinatewise from the cross formula). -/
lemma neg_cross_left (a b : Fin 3 → ℝ) : (-a) ⨯₃ b = -(a ⨯₃ b) := by
  ext i
  fin_cases i <;> simp [cross_apply] <;> ring

/-- The cross product is odd in its second argument:
`a ⨯₃ (−b) = −(a ⨯₃ b)`. -/
lemma neg_cross_right (a b : Fin 3 → ℝ) : a ⨯₃ (-b) = -(a ⨯₃ b) := by
  ext i
  fin_cases i <;> simp [cross_apply] <;> ring

/-- The unit normal is ODD under the deck:
`unitNormal f (period a x) = − unitNormal f x` on the strip interior —
going once around the Möbius band reverses the normal (the deck map is
orientation reversing). -/
lemma unitNormal_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    unitNormal f (period a x) = -unitNormal f x := by
  have ht0 := tangent₀_deck hf hx
  have ht1 := tangent₁_deck hf hx
  have hcross : WithLp.ofLp (tangent₀ f (period a x)) ⨯₃
        WithLp.ofLp (tangent₁ f (period a x)) =
      -(WithLp.ofLp (tangent₀ f x) ⨯₃ WithLp.ofLp (tangent₁ f x)) := by
    rw [ht0, ht1]
    have hneg : WithLp.ofLp (-tangent₀ f x) = -WithLp.ofLp (tangent₀ f x) := by simp
    rw [hneg]
    exact neg_cross_left (WithLp.ofLp (tangent₀ f x)) (WithLp.ofLp (tangent₁ f x))
  unfold unitNormal
  exact congrArg (WithLp.toLp 2) hcross


/-! ## The shape operator (dN) under the deck -/

/-- For a function `G` that is anti-invariant under the deck
(`G (period a y) = −G y` on the strip interior), differentiating along the
`e0`-line gives `fderiv G (period a x) e0 = fderiv G x e0`. -/
lemma fderiv_anti_deck_e0 {a : ℝ} {G : ℝ² → ℝ³}
    (hG : ∀ y ∈ stripInterior, G (period a y) = -G y)
    {x : ℝ²} (hx : x ∈ stripInterior)
    (hdG : DifferentiableAt ℝ G x) (hdGp : DifferentiableAt ℝ G (period a x)) :
    fderiv ℝ G (period a x) !₂[1, 0] = fderiv ℝ G x !₂[1, 0] := by
  let e0 : ℝ² := !₂[1, 0]
  have hxp : period a x ∈ stripInterior := period_mem_stripInterior a hx
  have hpe : ∀ s : ℝ, period a (x + s • e0) = period a x + s • (-e0) := by
    intro s
    ext i <;> fin_cases i <;> simp [period, e0] <;> ring
  have hcurve : (fun s : ℝ => G (period a (x + s • e0))) =
      fun s : ℝ => G (period a x + s • (-e0)) := by
    funext s
    rw [hpe s]
  have hlineP : HasDerivAt (fun s : ℝ => G (period a x + s • (-e0)))
      (fderiv ℝ G (period a x) (-e0)) 0 :=
    hasDerivAt_fderiv_apply_add_smul hdGp
  have hγp : HasDerivAt (fun s : ℝ => G (period a (x + s • e0)))
      (fderiv ℝ G (period a x) (-e0)) 0 := by
    simpa [hcurve] using hlineP
  have hlineX : HasDerivAt (fun s : ℝ => G (x + s • e0)) (fderiv ℝ G x e0) 0 :=
    hasDerivAt_fderiv_apply_add_smul hdG
  have hnegX : HasDerivAt (fun s : ℝ => -G (x + s • e0)) (-(fderiv ℝ G x e0)) 0 :=
    hlineX.neg
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • e0 ∈ stripInterior := by
    have hcont : ContinuousAt (fun s : ℝ => x + s • e0) 0 := (hasDerivAt_line x e0).continuousAt
    have hV : stripInterior ∈ 𝓝 (x + (0 : ℝ) • e0) := by
      simpa using (IsOpen.mem_nhds stripInterior_isOpen hx)
    exact hcont hV
  have hev : (fun s : ℝ => G (period a (x + s • e0))) =ᶠ[𝓝 0]
      (fun s : ℝ => -G (x + s • e0)) := by
    filter_upwards [hmem] with s hs
    exact hG (x + s • e0) hs
  have hγx : HasDerivAt (fun s : ℝ => G (period a (x + s • e0)))
      (-(fderiv ℝ G x e0)) 0 :=
    hnegX.congr_of_eventuallyEq hev
  have heq := HasDerivAt.unique hγp hγx
  -- heq : fderiv G (period x)(−e0) = −(fderiv G x e0); use linearity map_neg
  have hm : fderiv ℝ G (period a x) (-e0) = -(fderiv ℝ G (period a x) e0) :=
    map_neg (fderiv ℝ G (period a x)) e0
  rw [hm] at heq
  exact neg_inj.mp heq

/-- For a function `G` anti-invariant under the deck, differentiating along
the `e1`-line gives `fderiv G (period a x) e1 = −(fderiv G x e1)`. -/
lemma fderiv_anti_deck_e1 {a : ℝ} {G : ℝ² → ℝ³}
    (hG : ∀ y ∈ stripInterior, G (period a y) = -G y)
    {x : ℝ²} (hx : x ∈ stripInterior)
    (hdG : DifferentiableAt ℝ G x) (hdGp : DifferentiableAt ℝ G (period a x)) :
    fderiv ℝ G (period a x) !₂[0, 1] = -(fderiv ℝ G x !₂[0, 1]) := by
  let e1 : ℝ² := !₂[0, 1]
  have hxp : period a x ∈ stripInterior := period_mem_stripInterior a hx
  have hpe : ∀ s : ℝ, period a (x + s • e1) = period a x + s • e1 := by
    intro s
    ext i <;> fin_cases i <;> simp [period, e1] <;> ring
  have hcurve : (fun s : ℝ => G (period a (x + s • e1))) =
      fun s : ℝ => G (period a x + s • e1) := by
    funext s
    rw [hpe s]
  have hlineP : HasDerivAt (fun s : ℝ => G (period a x + s • e1))
      (fderiv ℝ G (period a x) e1) 0 :=
    hasDerivAt_fderiv_apply_add_smul hdGp
  have hγp : HasDerivAt (fun s : ℝ => G (period a (x + s • e1)))
      (fderiv ℝ G (period a x) e1) 0 := by
    simpa [hcurve] using hlineP
  have hlineX : HasDerivAt (fun s : ℝ => G (x + s • e1)) (fderiv ℝ G x e1) 0 :=
    hasDerivAt_fderiv_apply_add_smul hdG
  have hnegX : HasDerivAt (fun s : ℝ => -G (x + s • e1)) (-(fderiv ℝ G x e1)) 0 :=
    hlineX.neg
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • e1 ∈ stripInterior := by
    have hcont : ContinuousAt (fun s : ℝ => x + s • e1) 0 := (hasDerivAt_line x e1).continuousAt
    have hV : stripInterior ∈ 𝓝 (x + (0 : ℝ) • e1) := by
      simpa using (IsOpen.mem_nhds stripInterior_isOpen hx)
    exact hcont hV
  have hev : (fun s : ℝ => G (period a (x + s • e1))) =ᶠ[𝓝 0]
      (fun s : ℝ => -G (x + s • e1)) := by
    filter_upwards [hmem] with s hs
    exact hG (x + s • e1) hs
  have hγx : HasDerivAt (fun s : ℝ => G (period a (x + s • e1)))
      (-(fderiv ℝ G x e1)) 0 :=
    hnegX.congr_of_eventuallyEq hev
  exact HasDerivAt.unique hγp hγx

/-- The unit-normal field is anti-invariant under the deck (restated for
the `dN` transfer). -/
lemma unitNormal_anti_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ y ∈ stripInterior, unitNormal f (period a y) = -unitNormal f y := by
  intro y hy
  exact unitNormal_deck hf hy

/-- **Shape operator under the deck, `e0`-column**: `dN f (period a x) e0 =
dN f x e0` — differentiating `unitNormal (period y) = −unitNormal y` along
the `e0`-line (the deck reverses the domain direction but the normal also
flips, so the `e0`-column is preserved). -/
lemma dN_deck_e0 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    dN f (period a x) !₂[1, 0] = dN f x !₂[1, 0] := by
  have hxp : period a x ∈ stripInterior := period_mem_stripInterior a hx
  have hG : ∀ y ∈ stripInterior,
      (fun y : ℝ² => unitNormal f y) (period a y) = -(fun y : ℝ² => unitNormal f y) y :=
    unitNormal_anti_deck hf
  rw [dN_eq_fderiv hxp, dN_eq_fderiv hx]
  exact fderiv_anti_deck_e0 hG hx (differentiableAt_unitNormal hf x hx)
    (differentiableAt_unitNormal hf (period a x) hxp)

/-- **Shape operator under the deck, `e1`-column**: `dN f (period a x) e1 =
−(dN f x e1)` — the `e1`-column changes sign (the normal flip dominates the
preserved domain direction). -/
lemma dN_deck_e1 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    dN f (period a x) !₂[0, 1] = -(dN f x !₂[0, 1]) := by
  have hxp : period a x ∈ stripInterior := period_mem_stripInterior a hx
  have hG : ∀ y ∈ stripInterior,
      (fun y : ℝ² => unitNormal f y) (period a y) = -(fun y : ℝ² => unitNormal f y) y :=
    unitNormal_anti_deck hf
  rw [dN_eq_fderiv hxp, dN_eq_fderiv hx]
  exact fderiv_anti_deck_e1 hG hx (differentiableAt_unitNormal hf x hx)
    (differentiableAt_unitNormal hf (period a x) hxp)


/-! ## The full-map transfer and the kernel-line flip -/

/-- The deck derivative `D`: flips the `0`-coordinate, keeps the
`1`-coordinate (`D v = !₂[−v0, v1]`, the linear part of `period a`). -/
def deckFlip (v : ℝ²) : ℝ² := !₂[-(v 0), v 1]

/-- `deckFlip` is an involution: `D (D v) = v`. -/
lemma deckFlip_involutive (v : ℝ²) : deckFlip (deckFlip v) = v := by
  ext i <;> fin_cases i <;> simp [deckFlip]

/-- Any vector decomposes into the coordinate basis. -/
lemma vec_eq_coord_smul_basis (w : ℝ²) :
    w = (w 0) • (!₂[1, 0] : ℝ²) + (w 1) • (!₂[0, 1] : ℝ²) := by
  ext i <;> fin_cases i <;> simp

/-- The deck flip of a decomposed vector:
`D (w0•e0 + w1•e1) = (−w0)•e0 + w1•e1`. -/
lemma deckFlip_coord_smul_basis (w : ℝ²) :
    deckFlip w = (-(w 0)) • (!₂[1, 0] : ℝ²) + (w 1) • (!₂[0, 1] : ℝ²) := by
  ext i <;> fin_cases i <;> simp [deckFlip]

/-- **Full shape-operator transfer under the deck**:
`dN f (period a x) (D w) = −(dN f x w)` for every `w`, where
`D v = !₂[−v0, v1]` — the deck conjugates the shape operator to its
negation. -/
lemma dN_deck_flip {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) (w : ℝ²) :
    dN f (period a x) (deckFlip w) = -(dN f x w) := by
  have hdw : deckFlip w = (-(w 0)) • (!₂[1, 0] : ℝ²) + (w 1) • (!₂[0, 1] : ℝ²) :=
    deckFlip_coord_smul_basis w
  have hw : w = (w 0) • (!₂[1, 0] : ℝ²) + (w 1) • (!₂[0, 1] : ℝ²) :=
    vec_eq_coord_smul_basis w
  calc
    dN f (period a x) (deckFlip w)
        = dN f (period a x) ((-(w 0)) • (!₂[1, 0] : ℝ²) + (w 1) • (!₂[0, 1] : ℝ²)) := by
      rw [hdw]
    _ = (-(w 0)) • dN f (period a x) (!₂[1, 0] : ℝ²) +
        (w 1) • dN f (period a x) (!₂[0, 1] : ℝ²) := by
      simp [map_add, map_smul]
    _ = (-(w 0)) • dN f x (!₂[1, 0] : ℝ²) + (w 1) • (-(dN f x (!₂[0, 1] : ℝ²))) := by
      rw [dN_deck_e0 hf hx, dN_deck_e1 hf hx]
    _ = -((w 0) • dN f x (!₂[1, 0] : ℝ²) + (w 1) • dN f x (!₂[0, 1] : ℝ²)) := by
      rw [neg_smul, smul_neg, ← neg_add]
    _ = -(dN f x w) := by
      rw [hw]
      simp [map_add, map_smul]

/-- **Kernel flip**: the bend-direction kernel transfers across the deck:
`w` is in the kernel of `dN` at `period a x` iff `D w` is in the kernel of
`dN` at `x`. -/
lemma dN_ker_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) (w : ℝ²) :
    dN f (period a x) w = 0 ↔ dN f x (deckFlip w) = 0 := by
  have h := dN_deck_flip hf hx (deckFlip w)
  -- h : dN f (period a x) (deckFlip (deckFlip w)) = -(dN f x (deckFlip w))
  rw [deckFlip_involutive] at h
  -- h : dN f (period a x) w = -(dN f x (deckFlip w))
  constructor
  · intro hw0
    have h' : -(dN f x (deckFlip w)) = 0 := by simpa [hw0] using h
    exact neg_eq_zero.mp (by simpa using h')
  · intro hdf
    rw [hdf] at h
    simpa using h

/-! ## The shape-operator entries and the mirror kernel field under the deck -/

/-- **Entry (0,0) flips under the deck**:
`dNentry f (period a x) 0 0 = −(dNentry f x 0 0)` — the shape-operator
matrix entry `a` changes sign. -/
lemma dNentry_deck_00 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    dNentry f (period a x) 0 0 = -(dNentry f x 0 0) := by
  unfold dNentry
  simp
  rw [dN_deck_e0 hf hx, tangent₀_deck hf hx]
  exact inner_neg_right (dN f x (!₂[1, 0] : ℝ²)) (tangent₀ f x)

/-- **Entry (0,1) is preserved under the deck**:
`dNentry f (period a x) 0 1 = dNentry f x 0 1`. -/
lemma dNentry_deck_01 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    dNentry f (period a x) 0 1 = dNentry f x 0 1 := by
  unfold dNentry
  simp
  rw [dN_deck_e0 hf hx, tangent₁_deck hf hx]

/-- **Entry (1,0) is preserved under the deck**:
`dNentry f (period a x) 1 0 = dNentry f x 1 0` (two sign flips cancel). -/
lemma dNentry_deck_10 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    dNentry f (period a x) 1 0 = dNentry f x 1 0 := by
  unfold dNentry
  simp
  rw [dN_deck_e1 hf hx, tangent₀_deck hf hx]
  -- ⟪−A, −B⟫ = −⟪A, −B⟫ = ⟪A, B⟫
  rw [inner_neg_left, inner_neg_right]
  simp

/-- **Entry (1,1) flips under the deck**:
`dNentry f (period a x) 1 1 = −(dNentry f x 1 1)` — the entry `c` changes
sign. -/
lemma dNentry_deck_11 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    dNentry f (period a x) 1 1 = -(dNentry f x 1 1) := by
  unfold dNentry
  simp
  rw [dN_deck_e1 hf hx, tangent₁_deck hf hx]
  exact inner_neg_left (dN f x (!₂[0, 1] : ℝ²)) (tangent₁ f x)

/-- **Mirror kernel field under the deck**:
`V2f f (period a x) = deckFlip (V2f f x)` — the kernel direction transfers
with the deck flip of coordinates. -/
lemma V2f_deck_flip {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    V2f f (period a x) = deckFlip (V2f f x) := by
  change (dNentry f (period a x) 1 1) • e0 + (-(dNentry f (period a x) 1 0)) • e1 =
      deckFlip ((dNentry f x 1 1) • e0 + (-(dNentry f x 1 0)) • e1)
  have h11 := dNentry_deck_11 hf hx
  have h10 := dNentry_deck_10 hf hx
  rw [h11, h10]
  unfold deckFlip
  ext i <;> fin_cases i <;> simp <;> ring

/-! ## The leaf-endpoint period relations -/

/-- **Endpoint period relation (left)**: the left-boundary intersection of
the `deckFlip`-image of a line through `period a x` is the period image of
the right-boundary intersection of the line through `x`:
`leftPointOfDir (period a x) (deckFlip d) = period a (rightPointOfDir x d)`
(for `d 0 ≠ 0`). -/
lemma leftPointOfDir_period_deckFlip (a : ℝ) {x d : ℝ²} (hd0 : d 0 ≠ 0) :
    leftPointOfDir (period a x) (deckFlip d) = period a (rightPointOfDir x d) := by
  unfold leftPointOfDir rightPointOfDir leftParam rightParam deckFlip period
  ext i <;> fin_cases i
  · simp
    field_simp [hd0]
    ring
  · simp
    field_simp [hd0]
    ring

/-- **Endpoint period relation (right)**: the right-boundary intersection of
the `deckFlip`-image of a line through `period a x` is the period image of
the left-boundary intersection of the line through `x`:
`rightPointOfDir (period a x) (deckFlip d) = period a (leftPointOfDir x d)`
(for `d 0 ≠ 0`). -/
lemma rightPointOfDir_period_deckFlip (a : ℝ) {x d : ℝ²} (hd0 : d 0 ≠ 0) :
    rightPointOfDir (period a x) (deckFlip d) = period a (leftPointOfDir x d) := by
  unfold leftPointOfDir rightPointOfDir leftParam rightParam deckFlip period
  ext i <;> fin_cases i
  · simp
    field_simp [hd0]
    ring
  · simp
    field_simp [hd0]
    ring

/-- **The shape operator vanishes under the deck iff it vanishes at
`x`**: `dN f (period a x) = 0 ↔ dN f x = 0` on the strip interior. -/
lemma dN_zero_period_iff {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    dN f (period a x) = 0 ↔ dN f x = 0 := by
  constructor
  · intro hz
    apply ContinuousLinearMap.ext
    intro w
    have h := dN_deck_flip hf hx w
    -- h : dN f (period a x) (deckFlip w) = -(dN f x w)
    rw [hz] at h
    have hneg : -(dN f x w) = 0 := by simpa using h.symm
    exact neg_eq_zero.mp hneg
  · intro hz
    apply ContinuousLinearMap.ext
    intro w
    have h := dN_deck_flip hf hx (deckFlip w)
    rw [deckFlip_involutive] at h
    rw [hz] at h
    simpa using h

/-- **Nonzero shape operator transfers across the deck**:
`dN f (period a x) ≠ 0 ↔ dN f x ≠ 0` on the strip interior (the deck flip
`dN_deck_flip` is a bijection between the kernels, so one shape operator is
trivial iff the other is). -/
lemma dN_ne_zero_period_iff {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) :
    dN f (period a x) ≠ 0 ↔ dN f x ≠ 0 := by
  exact not_congr (dN_zero_period_iff hf hx)
