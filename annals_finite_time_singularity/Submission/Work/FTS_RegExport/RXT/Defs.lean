import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS_RegExport.RXT.omega_facts
import Submission.Work.FTS_RegExport.RXT.logcoord_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Defs` — the logarithmic coordinates of RX-T

`cz s = eˢ` and `cth ψ = arctan(e^ψ)` put the self-similar quadrant `(0,∞) × (0,π/2)` in
bijection with `ℝ²`; in these coordinates the transport coefficients of `(E)` are bounded and
the weight ratio `φ = u/ω` satisfies a first-order transport equation with bounded
coefficients (see `RXT.Pullback`).  This file collects the definitions together with the
elementary facts about the weight `ω α z θ = z²(sinθcos²θ)^α/(1+z)²` that they need.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-! ## §1 The logarithmic coordinates and the pulled-back unknown -/

/-! ### The angular coordinate `ψ ↦ arctan (e^ψ)` -/

theorem arctan_exp_mem (ψ : ℝ) : 0 < Real.arctan (Real.exp ψ) ∧ Real.arctan (Real.exp ψ) < Real.pi / 2 :=
  logcoord_facts.1 ψ

theorem sin_two_arctan_exp_pos (ψ : ℝ) : 0 < Real.sin (2 * Real.arctan (Real.exp ψ)) :=
  logcoord_facts.2.1 ψ

theorem hasDerivAt_arctan_exp (ψ : ℝ) :
    HasDerivAt (fun ψ' => Real.arctan (Real.exp ψ'))
      (Real.sin (2 * Real.arctan (Real.exp ψ)) / 2) ψ :=
  logcoord_facts.2.2.1 ψ

theorem exists_exp (z : ℝ) (hz : 0 < z) : ∃ s : ℝ, Real.exp s = z :=
  logcoord_facts.2.2.2.1 z hz

theorem exists_arctan_exp (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    ∃ ψ : ℝ, Real.arctan (Real.exp ψ) = θ :=
  logcoord_facts.2.2.2.2.1 θ hθ hθπ

theorem sin_two_pos_of_mem {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    0 < Real.sin (2 * θ) :=
  logcoord_facts.2.2.2.2.2.1 θ hθ hθπ

theorem c2m_abs_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 :=
  logcoord_facts.2.2.2.2.2.2 θ

/-- The radial logarithmic coordinate `s = log z`. -/
def cz (s : ℝ) : ℝ := Real.exp s

/-- The angular logarithmic coordinate `ψ = log (tan θ)`. -/
def cth (ψ : ℝ) : ℝ := Real.arctan (Real.exp ψ)

theorem cz_pos (s : ℝ) : 0 < cz s := Real.exp_pos s

theorem cth_pos (ψ : ℝ) : 0 < cth ψ := (arctan_exp_mem ψ).1

theorem cth_lt (ψ : ℝ) : cth ψ < Real.pi / 2 := (arctan_exp_mem ψ).2

theorem cth_sin_two_pos (ψ : ℝ) : 0 < Real.sin (2 * cth ψ) := sin_two_arctan_exp_pos ψ

/-- The weight of the pulled-back unknown. -/
def om (α s ψ : ℝ) : ℝ := Work.FTS.RegExportIface.ω α (cz s) (cth ψ)

theorem om_pos {α s ψ : ℝ} (hα : 0 < α) : 0 < om α s ψ :=
  (omega_facts α hα).1 (cz s) (cth ψ) (cz_pos s) (cth_pos ψ) (cth_lt ψ)

/-- The pulled-back unknown `φ = u(z,θ,τ)/ω(z,θ)` in the logarithmic coordinates. -/
def phi (α : ℝ) (u : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => u (cz s) (cth ψ) τ / om α s ψ

/-- The `s`-derivative of `φ`, i.e. `D_zφ = D_zu/ω − 2φ/(1+z)`. -/
def dphi_s (α : ℝ) (u : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ =>
    cz s * Work.Spaces.pz (fun z θ => u z θ τ) (cz s) (cth ψ) / om α s ψ
      - 2 * phi α u s ψ τ / (1 + cz s)

/-- The `ψ`-derivative of `φ`; since `dθ/dψ = sin 2θ/2` and `∂_θω/ω = 2α·c2m θ/sin 2θ`,
this is `(sin 2θ/2)·∂_θu/ω − α·c2m θ·φ`. -/
def dphi_ψ (α : ℝ) (u : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ =>
    (Real.sin (2 * cth ψ) / 2) * (Work.Spaces.pth (fun z θ => u z θ τ) (cz s) (cth ψ) / om α s ψ)
      - phi α u s ψ τ * (α * Work.Construction.c2m (cth ψ))

/-- The `s`-coefficient of the pulled-back equation: `a = Vz`. -/
def trA (Vz : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => Vz (cz s) (cth ψ) τ

/-- The `ψ`-coefficient of the pulled-back equation: `b = 2Vθ/sin 2θ`. -/
def trB (Vθ : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => 2 * Vθ (cz s) (cth ψ) τ / Real.sin (2 * cth ψ)

/-- The zero-order coefficient of the pulled-back equation:
`c = cs + 2Vz/(1+z) + α·c2m(θ)·b`. -/
def trC (α : ℝ) (Vz Vθ cs : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ =>
    cs (cz s) (cth ψ) τ + 2 * Vz (cz s) (cth ψ) τ / (1 + cz s)
      + α * Work.Construction.c2m (cth ψ) * (2 * Vθ (cz s) (cth ψ) τ / Real.sin (2 * cth ψ))

/-- The source of the pulled-back equation: `f = σ/ω`. -/
def trF (α : ℝ) (σ : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => σ (cz s) (cth ψ) τ / om α s ψ

/-! ## §2 The pull-back of the equation to the logarithmic coordinates -/

/-- The domain `(0,∞) × (0,π/2) × [0,S]` on which `u` is `C¹`. -/
def dom (S : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)

theorem hasDerivAt_cz (s : ℝ) : HasDerivAt cz (cz s) s := Real.hasDerivAt_exp s

theorem hasDerivAt_cth (ψ : ℝ) : HasDerivAt cth (Real.sin (2 * cth ψ) / 2) ψ :=
  hasDerivAt_arctan_exp ψ

end Work.FTS_RegExport.RXT
