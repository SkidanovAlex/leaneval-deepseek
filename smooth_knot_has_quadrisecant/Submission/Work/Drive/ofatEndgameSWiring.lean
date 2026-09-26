import Mathlib
import Submission.Work.Drive.oFatDefsS
import Submission.Work.Drive.oFatDefs
import Submission.Work.Drive.ofatEndgame
import Submission.Work.Drive.spreadBookkeepingK_spreadCrux
import Submission.Work.Drive.isUnknotted_of_close

/-!
# The `S` (`E3′` + uniform-`ρ₀`) wiring of the `OFat` lane

The project lead's `NOTES_LEAD_endgameUniform.md` replaces the old `OFatCrosscutEndgame` by a design
in which (i) the crosscut avoids the enlarged obstruction set
`Work.Drive.OFatObstructionS r ρ δs` (`E3′`) and (ii) the chamfer *depth* is scheduled
(`Work.Drive.chamferLoopGen` + `Work.Drive.schedAlpha/schedBeta`), so that the fatness threshold `ρ`
enters only through *uniform* constants instead of through the crosscut-dependent `ρ ≤ lam · W`.

This module names the two new pieces and proves the wiring between them:

* `Work.Drive.OFatE3S r₀` — the `E3′` dichotomy in the speed-bound-free `C²`-ball form;
* `Work.Drive.OFatE3SV r₀` — the same dichotomy in the *lead's verbatim* form (with the reference
  speed bound `V` as a parameter), which is the shape in which it is actually proved; `OFatE3S`
  follows (`Work.Drive.ofatE3S_of_V`) since `V` is derivable from `IsSmoothKnot r₀`;
* `Work.Drive.OFatCrosscutEndgameS r` — the **new pin** (the uniform-`ρ₀` endgame contract);
* `Work.Drive.spreadCrux_of_endgameS` — `E3′` + the new endgame give the crux
  `Work.Drive.SpreadCrux`, hence `Work.Drive.SpreadQuadrisecantFullCloseK_v2`.

**Note (workspace churn).**  An earlier module `Drive/ofatEndgameS.lean` of this lane held these
definitions and was emptied by a workspace housekeeping pass (`WIP_ofatEndgameS.lean.txt`); this file
is the faithful copy, kept under a distinct module name so that the sibling `E3′` lane can re-create
its own files without a clash.  The only difference is the added `OFatE3SV` (the lead's verbatim
quantifier order, which the sibling's `crosscut_or_spreadQuad_of_closeS` produces).
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant Set

/-- **`E3′` of the lead's uniform-`ρ₀` design** (`NOTES_LEAD_endgameUniform.md` §1), in the
`C²`-ball form *without* the reference speed bound.  For every smooth knot `r₀` there are a ball
radius `ε₁ > 0` and a cap `δsmax > 0` on the short-chord scale such that, for every `ρ > 0` and every
`δs ∈ (0, δsmax]`, every `r'` in the `C²`-`ε₁`-ball around `r₀` that is in tangent-chord general
position and inflection-free either has a *uniform* `δ`-spread quadrisecant (`δ` independent of `r'`),
or carries a bottom–top crosscut of the period strip avoiding
`Work.Drive.OFatObstructionS r' ρ δs`. -/
def OFatE3S (r₀ : ℝ → Space) : Prop :=
  IsSmoothKnot r₀ → ∃ ε₁ δsmax : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ 0 < δsmax ∧
    ∀ {ρ δs : ℝ}, 0 < ρ → 0 < δs → δs ≤ δsmax →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ r' : ℝ → Space, IsSmoothKnot r' → TangentChordGP r' →
          (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) →
          (∀ t : ℝ, ‖r' t - r₀ t‖ < ε₁ ∧ ‖velocity r' t - velocity r₀ t‖ < ε₁ ∧
            ‖deriv (deriv r') t - deriv (deriv r₀) t‖ < ε₁) →
          ((∃ a b z w : ℝ, SpreadQuad δ a b z w ∧
              IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
              IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (w : KnotParam)) ∨
            StripCrosscutAvoidingOFatS r' ρ δs)

/-- **The same `E3′` dichotomy in the lead's verbatim form**: the reference speed bound `V` is a
parameter (this is the shape in which the dichotomy is proved, since its proof needs the Lipschitz
constant of `r₀`). -/
def OFatE3SV (r₀ : ℝ → Space) : Prop :=
  IsSmoothKnot r₀ → ∀ V : ℝ, 0 < V → (∀ t : ℝ, ‖velocity r₀ t‖ ≤ V) →
    ∃ ε₁ δsmax : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ 0 < δsmax ∧
      ∀ {ρ δs : ℝ}, 0 < ρ → 0 < δs → δs ≤ δsmax →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ r' : ℝ → Space, IsSmoothKnot r' → TangentChordGP r' →
            (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) →
            (∀ t : ℝ, ‖r' t - r₀ t‖ < ε₁ ∧ ‖velocity r' t - velocity r₀ t‖ < ε₁ ∧
              ‖deriv (deriv r') t - deriv (deriv r₀) t‖ < ε₁) →
            ((∃ a b z w : ℝ, SpreadQuad δ a b z w ∧
                IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
                IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (w : KnotParam)) ∨
              StripCrosscutAvoidingOFatS r' ρ δs)

/-- **The speed-bound-free `E3′` from the lead's form.**  The bound `V` is produced from
`IsSmoothKnot r₀` (`Work.Drive.exists_knot_velocity_bound`). -/
theorem ofatE3S_of_V (h : ∀ r : ℝ → Space, OFatE3SV r) : ∀ r : ℝ → Space, OFatE3S r := by
  intro r₀ hr₀
  obtain ⟨V, hVpos, hvel⟩ := exists_knot_velocity_bound hr₀
  obtain ⟨ε₁, δsmax, hε₁pos, hε₁le, hδsmaxpos, hE3⟩ := h r₀ hr₀ V hVpos hvel
  exact ⟨ε₁, δsmax, hε₁pos, hε₁le, hδsmaxpos, hE3⟩

/-- **The endgame contract of the uniform-`ρ₀` design** (`NOTES_LEAD_endgameUniform.md` §2).  For a
smooth knot `r` there are `ε₂ > 0` and `δs₀ > 0` such that, for every short-chord scale
`δs ∈ (0, δs₀]`, there is `ρ₀ > 0` such that every `r'` which is `C²`-`ε₂`-close to `r`, in
tangent-chord general position and inflection-free, and every `ρ ∈ (0, ρ₀]`, satisfies: a bottom–top
crosscut of the period strip avoiding `OFatObstructionS r' ρ δs` forces `r'` to be unknotted. -/
def OFatCrosscutEndgameS (r : ℝ → Space) : Prop :=
  IsSmoothKnot r → ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∃ δs₀ : ℝ, 0 < δs₀ ∧
    ∀ δs : ℝ, 0 < δs → δs ≤ δs₀ → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' → TangentChordGP r' →
        (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) →
        (∀ t : ℝ, ‖r' t - r t‖ < ε₂ ∧ ‖velocity r' t - velocity r t‖ < ε₂ ∧
          ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε₂) →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → StripCrosscutAvoidingOFatS r' ρ δs → IsUnknotted r'

/-- **`E3′` + the uniform-`ρ₀` endgame give the crux.**  The exact analogue of
`Work.Drive.spreadCrux_of_endgame` for the `S` pair: the dichotomy produces, for every approximant in
the ball, either a uniform spread or the `S`-crosscut; the endgame rules the crosscut out. -/
theorem spreadCrux_of_endgameS
    (hE3 : ∀ r : ℝ → Space, OFatE3S r)
    (hend : ∀ r : ℝ → Space, OFatCrosscutEndgameS r) :
    ∀ r : ℝ → Space, SpreadCrux r := by
  intro r hr hnu
  obtain ⟨εu, hεupos, hu⟩ := isUnknotted_of_close hr
  obtain ⟨ε₁, δsmax, hε₁pos, hε₁le, hδsmaxpos, hE3'⟩ := hE3 r hr
  obtain ⟨ε₂, hε₂pos, δs₀, hδs₀pos, hend'⟩ := hend r hr
  -- the short-chord scale: below both caps
  set δs : ℝ := min δs₀ δsmax with hδsdef
  have hδspos : 0 < δs := lt_min hδs₀pos hδsmaxpos
  have hδsδs₀ : δs ≤ δs₀ := min_le_left _ _
  have hδsδsmax : δs ≤ δsmax := min_le_right _ _
  -- the endgame at that scale
  obtain ⟨ρ₀, hρ₀pos, hend''⟩ := hend' δs hδspos hδsδs₀
  -- the fatness threshold handed to `E3′` (small, for the endgame)
  set ρf : ℝ := min ρ₀ 1 with hρfdef
  have hρfpos : 0 < ρf := lt_min hρ₀pos one_pos
  have hρfρ₀ : ρf ≤ ρ₀ := min_le_left _ _
  -- the uniform spread of `E3′` at that threshold and scale
  obtain ⟨δ, hδpos, hE3δ⟩ := hE3' hρfpos hδspos hδsδsmax
  -- the crux's ball
  set εc : ℝ := min ε₁ (min ε₂ εu) with hεcdef
  have hεcε₁ : εc ≤ ε₁ := min_le_left _ _
  have hεcε₂ : εc ≤ ε₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεcu : εc ≤ εu := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δ, hδpos, εc, by positivity, ?_⟩
  intro r' hr' _hgp hinfl _hn5 htc _hfib _hqi hclose
  have hcl₁ : ∀ t : ℝ, ‖r' t - r t‖ < ε₁ ∧ ‖velocity r' t - velocity r t‖ < ε₁ ∧
      ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε₁ :=
    fun t => ⟨lt_of_lt_of_le (hclose t).1 hεcε₁, lt_of_lt_of_le (hclose t).2.1 hεcε₁,
      lt_of_lt_of_le (hclose t).2.2 hεcε₁⟩
  have hcl₂ : ∀ t : ℝ, ‖r' t - r t‖ < ε₂ ∧ ‖velocity r' t - velocity r t‖ < ε₂ ∧
      ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε₂ :=
    fun t => ⟨lt_of_lt_of_le (hclose t).1 hεcε₂, lt_of_lt_of_le (hclose t).2.1 hεcε₂,
      lt_of_lt_of_le (hclose t).2.2 hεcε₂⟩
  have hcl_u : ∀ t : ℝ, ‖r' t - r t‖ < εu ∧ ‖velocity r' t - velocity r t‖ < εu :=
    fun t => ⟨lt_of_lt_of_le (hclose t).1 hεcu, lt_of_lt_of_le (hclose t).2.1 hεcu⟩
  rcases hE3δ r' hr' htc hinfl hcl₁ with hspread | hcc
  · exact hspread
  · exact absurd (hu r' hr' hcl_u (hend'' r' hr' htc hinfl hcl₂ ρf hρfpos hρfρ₀ hcc)) hnu

/-- The spread statement of this lane, from the `E3′` + `S`-endgame pair. -/
theorem spreadQuadrisecantFullCloseK_of_endgameS
    (hE3 : ∀ r : ℝ → Space, OFatE3S r)
    (hend : ∀ r : ℝ → Space, OFatCrosscutEndgameS r) : SpreadQuadrisecantFullCloseK_v2 :=
  spreadQuadrisecantFullCloseK_of_spreadCrux_all (spreadCrux_of_endgameS hE3 hend)

end Work.Drive
