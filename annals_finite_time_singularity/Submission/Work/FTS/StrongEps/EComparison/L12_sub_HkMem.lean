import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory

set_option autoImplicit false

/-- **Subtraction companion of `Work.FTS.LocData.L12_add_mul`.**  Under the *same* four
integrability hypotheses as the additivity half of `L12_add_mul` (the `θ`-slices of `a` and of
`b` integrable on `Iθ` for every `s > z`, and the two densities integrable on `(z,∞)`), the
`L₁₂`-integral of the difference splits:

`L₁₂(a - b)(z) = L₁₂ a(z) - L₁₂ b(z)`.

The point is that `L12_add_mul` already provides both linearity identities it is stated with —
additivity of `a + ·` and homogeneity in a constant `c` *of its first argument* — so
`a - b = a + (-1)·b` splits as `L₁₂ a + L₁₂ ((-1)·b)`, and the second summand is
`(-1)·L₁₂ b`.  No hypothesis beyond the four integrability inputs is needed: the two auxiliary
integrability statements for the rescaled datum `(-1)·b` are obtained from those of `b` by
`Integrable.const_mul` together with the pointwise homogeneity of the density
(`Work.FTS.LocData.L12dens_const_mul`). -/
theorem L12_sub_of_integrable {a b : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : ∀ s ∈ Set.Ioi z,
      IntegrableOn (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ s ∈ Set.Ioi z,
      IntegrableOn (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z))
    (h4 : IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    Work.Construction.L12 (fun z θ => a z θ - b z θ) z
      = Work.Construction.L12 a z - Work.Construction.L12 b z := by
  -- the `θ`-slice of the rescaled datum `(-1)·b` is integrable (the slices of `b` are)
  have hslice_nb : ∀ s ∈ Set.Ioi z,
      IntegrableOn (fun θ => Work.Spaces.K θ * ((-1) * b s θ) / s) Work.Spaces.Iθ := by
    intro s hs
    refine IntegrableOn.congr_fun
      (Integrable.const_mul (h2 s hs) (-1)) (fun θ _ => ?_) measurableSet_Icc
    ring
  -- and so is its density, by pointwise homogeneity of the density
  have hdens_nb : IntegrableOn
      (Work.Construction.L12dens (fun z θ => (-1) * b z θ)) (Set.Ioi z) := by
    refine IntegrableOn.congr_fun
      (Integrable.const_mul h4 (-1)) (fun s _ => ?_) measurableSet_Ioi
    exact (Work.FTS.LocData.L12dens_const_mul Work.Spaces.K (-1) b s).symm
  -- additivity of `L₁₂` applied to the pair `(a, (-1)·b)`
  obtain ⟨hadd, -⟩ :=
    Work.FTS.LocData.L12_add_mul (c := -1) h1 hslice_nb h3 hdens_nb
  -- homogeneity of `L₁₂` at `c = -1`, applied to `b`
  have hhom : Work.Construction.L12 (fun z θ => (-1) * b z θ) z
      = (-1) * Work.Construction.L12 b z :=
    (Work.FTS.LocData.L12_add_mul (c := -1) (a := b) (b := b) h2 h2 h4 h4).2
  have heq : (fun z θ => a z θ - b z θ) = fun z θ => a z θ + (-1) * b z θ := by
    funext z θ
    ring
  rw [heq, hadd, hhom]
  ring

/-- **Additivity of `L₁₂` on the honest `ℋ⁴`-class, on the half-line `z ∈ Iz`.**  With `a`, `b`
of class `SmoothOpen` and honest weighted `ℋ⁴`-size, `z ↦ L₁₂(a - b)(z)` splits as
`L₁₂ a - L₁₂ b` for every `z ∈ Iz`.

The restriction `z ∈ Iz = [0,∞)` is essential and is the correction of a review: for `z < 0` the
density is integrated over `(z,∞) ⊃ (z,0)`, where `SmoothOpen`/`HkMem` give no control at all and
the Bochner integral is the junk value `0` (`integral_undef`), so additivity genuinely fails there.
For `z ≥ 0` every `s > z` satisfies `s > 0`, so the slice integrability required by the proved
`Work.FTS.LocData.L12_add_mul` (`Submission/Work/FTS/LocData/L12_add_mul.lean`) follows from
`HkMem α 4 a`/`HkMem α 4 b` (the proved `integrableOn_slice_of_SmoothOpen_HkMem` /
`integrableOn_L12dens_of_SmoothOpen_HkMem`), and `IntegrableOn.mono_set` transfers the density
integrability from `Ioi 0` to `Ioi z`.  The `z = 0` case is the proved
`Work.FTS.GalBasis.cc.L12_add_of_HkMem` (`Submission/Work/FTS/GalBasis/cc/L12_add_of_HkMem.lean`);
subtraction is the homogeneity case `c = -1`.

*Proof.*  The uniform argument `L12_sub_of_integrable` (above) covers every `z ∈ Iz` at once: for
`s > z ≥ 0` the slice integrability is `integrableOn_slice_of_SmoothOpen_HkMem`, and
`IntegrableOn.mono_set` along `Ioi z ⊆ Ioi 0` (from `0 ≤ z`) gives the two density
integrability statements; `a - b = a + (-1)·b` then splits by `L12_add_mul`. -/
theorem L12_sub_HkMem {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen a) (hb : Work.FTS.EllipticEst.SmoothOpen b)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b) :
    ∀ z ∈ Work.Spaces.Iz, Work.Construction.L12 (fun z θ => a z θ - b z θ) z
      = Work.Construction.L12 a z - Work.Construction.L12 b z := by
  intro z hz
  have hz0 : 0 ≤ z := hz
  -- for `s > z ≥ 0` the `θ`-slice of `K · f s · / s` is integrable, from `HkMem α 4 f`
  have hslt : ∀ s ∈ Set.Ioi z, 0 < s := fun s hs => lt_of_le_of_lt hz0 (Set.mem_Ioi.mp hs)
  refine L12_sub_of_integrable (z := z) ?_ ?_ ?_ ?_
  · intro s hs
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem ha hma (hslt s hs)
  · intro s hs
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hb hmb (hslt s hs)
  · exact (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem ha hma).mono_set
      (Set.Ioi_subset_Ioi hz0)
  · exact (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hb hmb).mono_set
      (Set.Ioi_subset_Ioi hz0)

end Work.FTS.StrongEps.EComparison
