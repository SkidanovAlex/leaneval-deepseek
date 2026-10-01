/-
# ZeroFreeTables/OffAxis — `RectCertC_proof`

**AREA 3 at rectangle height `L`, complex case, first level** (`Work.ZeroFreeTables.RectCertC`,
`OFFAXIS_ROUTE_LEAD.md` §3.1).

`RectCertC` asks, uniformly in `L ≥ 1` and `q ≥ q₀(L)`, for the four first-level conclusions
about a pair `(χ₁, ρ₁)` carrying the rectangle-height numbering `IsRectMin L χ₁ ρ₁` (i.e.
`|Im ρ₁| ≤ L` and `λ₁` minimal over *all* non-principal zeros of height `≤ 10L`) with
`1 < |Im ρ₁|`:

* `348/1000 ≤ λ₁` — HB Lemma 9.5 at rectangle height `L` (`RectC_HB95`);
* `Z2` (`0.56 ≤ λ₁` when `χ₁` is real and `ρ₁` is not) — the off-axis `(9.16)` computation
  (`RectC_Z2`);
* `Z3` — the three universal bounds `λ₀ ≥ 0.695`, `λ₂ ≥ 0.701`, `λ₃ ≥ 0.856`
  (`RectC_Lam0`, `RectC_Lam2`, `RectC_Lam3`);
* `Z4` — the §15 rows (`RectC_Z4`).

The only work carried out here is the finite combination of the six height-`L` inputs at a
common threshold `q₀`; each input is proved separately in its own module.  Note that `Z2`'s
guard `ρ₁.im ≠ 0` is supplied by `1 < |ρ₁.im|`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.RectC_HB95
import Submission.Work.ZeroFreeTables.OffAxis.RectC_Z2
import Submission.Work.ZeroFreeTables.OffAxis.RectC_Lam0
import Submission.Work.ZeroFreeTables.OffAxis.RectC_Lam2
import Submission.Work.ZeroFreeTables.OffAxis.RectC_Lam3
import Submission.Work.ZeroFreeTables.OffAxis.RectC_Z4

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

/-- **`RectCertC`** from the six height-`L` inputs. -/
theorem RectCertC_proof : Work.ZeroFreeTables.RectCertC := by
  intro L hL
  obtain ⟨q1, h1⟩ := RectC_HB95 L hL
  obtain ⟨q2, h2⟩ := RectC_Z2 L hL
  obtain ⟨q3, h3⟩ := RectC_Lam0 L hL
  obtain ⟨q4, h4⟩ := RectC_Lam2 L hL
  obtain ⟨q5, h5⟩ := RectC_Lam3 L hL
  obtain ⟨q6, h6⟩ := RectC_Z4 L hL
  refine ⟨max (max (max q1 q2) (max q3 q4)) (max q5 q6), ?_⟩
  intro q hq _inst χ₁ ρ₁ hm him
  have hq1 : q1 ≤ q := by omega
  have hq2 : q2 ≤ q := by omega
  have hq3 : q3 ≤ q := by omega
  have hq4 : q4 ≤ q := by omega
  have hq5 : q5 ≤ q := by omega
  have hq6 : q6 ≤ q := by omega
  have him0 : ρ₁.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at him
    linarith
  exact ⟨h1 q hq1 χ₁ ρ₁ hm him,
    (fun hsq _ => h2 q hq2 χ₁ ρ₁ hm him hsq),
    ⟨h3 q hq3 χ₁ ρ₁ hm him, h4 q hq4 χ₁ ρ₁ hm him, h5 q hq5 χ₁ ρ₁ hm him⟩,
    h6 q hq6 χ₁ ρ₁ hm him⟩

end Work.ZeroFreeTables.OffAxis
