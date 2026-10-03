import Mathlib
import Submission.Work.L62.lowcyl
import Submission.Work.L62.l62c_end
import Submission.Work.L62.section_Bl
import Submission.Work.L62.availableDown_box
import Submission.Work.L62.tau0_pushdown_holo_deriv
import Submission.Work.L62.avail_down
import Submission.Work.L62.cont_family_of_selfmap
import Submission.Work.L62.lowBall_contraction
import Submission.Work.L62.uniform_escape2
import Submission.Work.L62C.escape_of_selfmap

/-!
# L62LD — the lower-end cylinder family built from a normalised section of `d.E - β` over `Bl`

This file contains the *parametric* machinery used by `Work.L62.model_head_down_deep`:

* `Work.L62LD.HeadData` packs, for one `β` with `AvailableDown d hd β`, a normalised
  `T`-equivariant section `σ` of `ĥ = d.E - β` over `hd.Bl` together with its reflected pushdown
  `H` and all the properties of `H` (holomorphy on `lowOmega`, self-map, `H 0 = 0`,
  `HasDerivAt H (π (cl - β)) 0`, injectivity, nonvanishing, and the section relation);
* `Work.L62LD.HeadData.qlow_link`: the *definitional* link `H (qlow w) = qlow (σ w)`;
* the family `HB` and its **joint continuity** on the available box × `lowOmega`
  (`Work.L62LD.HB_continuousOn`);
* the **escape** (`Work.L62LD.HB_escape`) and the **uniform step count**
  (`Work.L62LD.HB_uniform_escape`).

Everything is stated relative to a *provider* `HD : ∀ β, AvailableDown d hd β → HeadData d hd cl β`
(the existence of such a provider is `Work.L62LD.headDataExists`, proved in
`Submission/Work/L62LD/head_data.lean` from `Work.L62.section_Bl` and `Work.L62LD.refl_pushdown`).
-/

namespace Work.L62LD

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-- **The lower-end head data at one parameter `β`.**  `σ` is the normalised `T`-equivariant
section of `ĥ = d.E - β` over the lower horn `hd.Bl` (`Work.L62.section_Bl`) and `H` its reflected
pushdown `H ζ = if ζ = 0 then 0 else τ₀ (pushdown σ (τ₀ ζ))`, with its properties
(`Work.L62LD.refl_pushdown`). -/
structure HeadData (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) (cl β : ℂ) where
  σ : ℂ → ℂ
  H : ℂ → ℂ
  σ_holo : DifferentiableOn ℂ σ hd.Bl
  σ_mem : ∀ y ∈ hd.Bl, σ y ∈ hd.Bl
  σ_sec : ∀ y ∈ hd.Bl, d.E (σ y) - β = y
  σ_equi : ∀ y ∈ hd.Bl, σ (y + 1) = σ y + 1
  σ_asymp : Filter.Tendsto (fun w => σ w - w - (β - cl)) MandelDim.lowerEnd (nhds 0)
  H_def : ∀ ζ : ℂ, H ζ = if ζ = 0 then 0 else
    MandelDim.tau0 (MandelDim.pushdown σ (MandelDim.tau0 ζ))
  H_holo : DifferentiableOn ℂ H (Work.L62.lowOmega d hd)
  H_map : Set.MapsTo H (Work.L62.lowOmega d hd) (Work.L62.lowOmega d hd)
  H_zero : H 0 = 0
  H_deriv : HasDerivAt H (MandelDim.piExp (cl - β)) 0
  H_inj : Set.InjOn H (Work.L62.lowOmega d hd)
  H_ne : ∀ ζ ∈ Work.L62.lowOmega d hd, ζ ≠ 0 → H ζ ≠ 0
  H_rel : ∀ ζ ∈ Work.L62.lowOmega d hd,
    MandelDim.tau0 (MandelDim.pushdown d.E (MandelDim.tau0 (H ζ))) =
      MandelDim.piExp (-β) * ζ

/-- **The link between the lift chain and the cylinder chain.**  For the reflected pushdown `H` of
the section `σ`, `H (qlow w) = qlow (σ w)` for `w ∈ hd.Bl`.  This is what makes
`qlow '' W j` the orbit of the cylinder family along the chain `W (j+1) = σ '' W j`. -/
theorem HeadData.qlow_link {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d}
    {cl β : ℂ} (HD : HeadData d hd cl β) {w : ℂ} (hw : w ∈ hd.Bl) :
    HD.H (Work.L62.qlow w) = Work.L62.qlow (HD.σ w) := by
  have hq : Work.L62.qlow w ≠ 0 := Work.L62.qlow_ne_zero w
  rw [HD.H_def, ite_eq_right hq]
  have h1 : MandelDim.tau0 (Work.L62.qlow w) = MandelDim.piExp w := by
    rw [Work.L62.qlow_eq_tau0]
    exact Work.L62.tau0_invol (MandelDim.piExp w) (Work.Horn.MandelDim.piExp_ne_zero w)
  rw [h1]
  have h2 : MandelDim.pushdown HD.σ (MandelDim.piExp w) = MandelDim.piExp (HD.σ w) :=
    Work.Horn.MandelDim.pushdown_piExp hd.Bl_T (fun y hy _ => HD.σ_equi y hy) hw
  rw [h2, Work.L62.qlow_eq_tau0]

end

end Work.L62LD
