import Mathlib
import Submission.Helpers
import Submission.KnotMap
import Submission.QuadrisecantLimit
import Submission.QuadrisecantChord
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.genericFullDefs
import Submission.Work.Drive.genericFullDense
import Submission.Work.Drive.finiteMeridianFibreK
import Submission.Work.Drive.spreadBookkeepingFull
import Submission.Work.Drive.isUnknotted_of_close
import Submission.Work.Drive.quadrisecantChord_of_tendsto_quadrisecants
import Submission.Work.Drive.circSepAPI

/-!
# The generic reduction, wired to the lead's consolidated genericity package

Two ingredients of the assembly of `Work.Drive.quadrisecant_of_genericCase_noInfl` are strengthened
so that the *corrected* crux (brick (d′) + the Layer-B sweep pin `Work.Drive.OPrimeSweepFamily`, see
`Work.Drive.exists_nontrivial_quadrisecant_of_generalPosition_of_pins`) can be plugged in:

* `Work.Drive.GenericFullFiniteDense` — the density of approximants that are simultaneously in
  transverse general position, inflection-free, five-collinear-free, in tangent-chord general
  position and have a finite meridian trace.  Proved from the *proved* `GenericFullDense` together
  with `finiteMeridianFibre_of_tangentChordGP`.
* `Work.Drive.SpreadQuadrisecantFullClose` (in `spreadBookkeepingFull.lean`) — the spread statement
  for such approximants, proved from the strengthened crux and the *proved* collapse resistance.

The assembly `Work.Drive.quadrisecant_of_genericCase_full` below is the same bookkeeping as the
original assembly with the two extra clauses threaded through.
-/

set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Topology

noncomputable section

/-- **Step 1'' (the lead's `GenericFullDense` plus the finite meridian trace).**  Every smooth knot
has arbitrarily `C¹`-close approximants that are in transverse general position, inflection-free,
five-collinear-free, in tangent-chord general position, and have a finite vertical trace of the
lifted trisecant locus. -/
def GenericFullFiniteDense : Prop :=
  ∀ r : ℝ → Space, IsSmoothKnot r → ∀ ε : ℝ, 0 < ε → ∃ r' : ℝ → Space,
    IsSmoothKnot r' ∧ TorusGeneralPositionTransverse r' ∧
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) ∧
      NoFiveCollinear r' ∧ TangentChordGP r' ∧ FiniteMeridianFibre r' ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε

/-- `GenericFullFiniteDense` from the *proved* `GenericFullDense` plus the finite-meridian-trace
continuation `Work.Drive.finiteMeridianFibre_of_tangentChordK`. -/
theorem genericFullFiniteDense_of_fullDense : GenericFullFiniteDense := by
  intro r hr ε hε
  obtain ⟨r', h1, h2, h3, h4, h5, h6⟩ := genericFullDense r hr ε hε
  exact ⟨r', h1, h2, h3, h4, h5,
    finiteMeridianFibre_of_tangentChordK h1 h2 h3 h5, h6⟩

theorem quadrisecant_of_genericCase_full_noHgen
    (hA : GenericFullFiniteDense) (hB : SpreadQuadrisecantFullClose) :
    ∀ r : ℝ → Space, IsSmoothKnot r → ¬ IsUnknotted r → HasQuadrisecant r := by
  intro r hr hnu
  obtain ⟨δ, hδpos, ε, hεpos, hS⟩ := hB r hr hnu
  -- a sequence of approximants, C¹-closer and closer to `r`
  have hmain : ∀ n : ℕ, ∃ r' : ℝ → Space, IsSmoothKnot r' ∧ TorusGeneralPositionTransverse r' ∧
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) ∧ NoFiveCollinear r' ∧
      TangentChordGP r' ∧ FiniteMeridianFibre r' ∧
      (∀ t : ℝ, ‖r' t - r t‖ < min ε (1 / ((n : ℝ) + 1)) ∧
        ‖velocity r' t - velocity r t‖ < min ε (1 / ((n : ℝ) + 1))) := by
    intro n
    exact hA r hr _ (lt_min hεpos (by positivity))
  choose r' hr's hr'gp hr'infl hr'n5 hr'tc hr'fib hr'close using hmain
  -- each approximant has a spread quadrisecant
  have hsp : ∀ n : ℕ, ∃ a b z w : ℝ, SpreadQuad δ a b z w ∧
      IsMiddleOnChord (r' n) (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
      IsMiddleOnChord (r' n) (a : KnotParam) (b : KnotParam) (w : KnotParam) :=
    fun n => hS (r' n) (hr's n) (hr'gp n) (hr'infl n) (hr'n5 n) (hr'tc n) (hr'fib n)
      (fun t => ⟨lt_of_lt_of_le (hr'close n t).1 (min_le_left _ _),
        lt_of_lt_of_le (hr'close n t).2 (min_le_left _ _)⟩)
  choose aa bb zz ww hh using hsp
  -- all quadruples lie in the compact box `[0, period]⁴`
  have hbox : ∀ n : ℕ, (aa n, (bb n, (zz n, ww n))) ∈
      (Set.Icc (0 : ℝ) period) ×ˢ ((Set.Icc (0 : ℝ) period) ×ˢ
        ((Set.Icc (0 : ℝ) period) ×ˢ (Set.Icc (0 : ℝ) period))) := by
    intro n
    obtain ⟨h1, h2, h3, h4, -⟩ := (hh n).1
    exact ⟨⟨h1.1, le_of_lt h1.2⟩, ⟨h2.1, le_of_lt h2.2⟩,
      ⟨h3.1, le_of_lt h3.2⟩, ⟨h4.1, le_of_lt h4.2⟩⟩
  have hcomp : IsCompact ((Set.Icc (0 : ℝ) period) ×ˢ ((Set.Icc (0 : ℝ) period) ×ˢ
      ((Set.Icc (0 : ℝ) period) ×ˢ (Set.Icc (0 : ℝ) period)))) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  obtain ⟨⟨A, B, Z, W⟩, -, φ, hφmono, hφtend⟩ := hcomp.tendsto_subseq hbox
  have htA : Tendsto (fun n => aa (φ n)) atTop (𝓝 A) := by
    have h := hφtend; rw [nhds_prod_eq] at h; exact h.fst
  have htB : Tendsto (fun n => bb (φ n)) atTop (𝓝 B) := by
    have h := hφtend; rw [nhds_prod_eq] at h
    have h2 := h.snd; rw [nhds_prod_eq] at h2; exact h2.fst
  have htZ : Tendsto (fun n => zz (φ n)) atTop (𝓝 Z) := by
    have h := hφtend; rw [nhds_prod_eq] at h
    have h2 := h.snd; rw [nhds_prod_eq] at h2
    have h3 := h2.snd; rw [nhds_prod_eq] at h3; exact h3.fst
  have htW : Tendsto (fun n => ww (φ n)) atTop (𝓝 W) := by
    have h := hφtend; rw [nhds_prod_eq] at h
    have h2 := h.snd; rw [nhds_prod_eq] at h2
    have h3 := h2.snd; rw [nhds_prod_eq] at h3; exact h3.snd
  -- the linear separation bounds survive the limit
  have hsep : ∀ (u v : ℕ → ℝ) (U V : ℝ), Tendsto u atTop (𝓝 U) → Tendsto v atTop (𝓝 V) →
      (∀ n, δ ≤ circSep (u n) (v n)) → δ ≤ circSep U V := by
    intro u v U V hu hv huv
    have htv : Tendsto (fun n => circSep (u n) (v n)) atTop (𝓝 (circSep U V)) := by
      have h := (continuous_circSep.tendsto (U, V)).comp (hu.prodMk_nhds hv)
      simpa [Function.comp_def] using h
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htv (Eventually.of_forall huv)
  have hsepAB := hsep _ _ _ _ htA htB (fun n => (hh (φ n)).1.2.2.2.2.1)
  have hsepAZ := hsep _ _ _ _ htA htZ (fun n => (hh (φ n)).1.2.2.2.2.2.1)
  have hsepAW := hsep _ _ _ _ htA htW (fun n => (hh (φ n)).1.2.2.2.2.2.2.1)
  have hsepBZ := hsep _ _ _ _ htB htZ (fun n => (hh (φ n)).1.2.2.2.2.2.2.2.1)
  have hsepBW := hsep _ _ _ _ htB htW (fun n => (hh (φ n)).1.2.2.2.2.2.2.2.2.1)
  have hsepZW := hsep _ _ _ _ htZ htW (fun n => (hh (φ n)).1.2.2.2.2.2.2.2.2.2)
  have hQD : QuadDistinct (A : KnotParam) (B : KnotParam) (Z : KnotParam) (W : KnotParam) :=
    quadDistinct_of_circSep (lt_of_lt_of_le hδpos hsepAB) (lt_of_lt_of_le hδpos hsepAZ)
      (lt_of_lt_of_le hδpos hsepAW) (lt_of_lt_of_le hδpos hsepBZ)
      (lt_of_lt_of_le hδpos hsepBW) (lt_of_lt_of_le hδpos hsepZW)
  -- the quadrisecant data along the subsequence
  have hmem' : ∀ n : ℕ, QuadDistinct ((aa (φ n) : ℝ) : KnotParam) ((bb (φ n) : ℝ) : KnotParam)
        ((zz (φ n) : ℝ) : KnotParam) ((ww (φ n) : ℝ) : KnotParam) ∧
      IsMiddleOnChord (r' (φ n)) ((aa (φ n) : ℝ) : KnotParam) ((bb (φ n) : ℝ) : KnotParam)
        ((zz (φ n) : ℝ) : KnotParam) ∧
      IsMiddleOnChord (r' (φ n)) ((aa (φ n) : ℝ) : KnotParam) ((bb (φ n) : ℝ) : KnotParam)
        ((ww (φ n) : ℝ) : KnotParam) := by
    intro n
    exact ⟨SpreadQuad.quadDistinct hδpos (hh (φ n)).1, (hh (φ n)).2.1, (hh (φ n)).2.2⟩
  -- uniform convergence of the approximants
  have hconv : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, dist (r' (φ n) t) (r t) < ρ := by
    intro ρ hρ
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ρ)
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    intro t
    have hφn : n ≤ φ n := hφmono.id_le n
    have h1 : ‖r' (φ n) t - r t‖ < 1 / ((φ n : ℝ) + 1) :=
      lt_of_lt_of_le (hr'close (φ n) t).1 (min_le_right _ _)
    have h2 : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : N + 1 ≤ φ n + 1 := Nat.succ_le_succ (le_trans hn hφn)
      exact_mod_cast this
    have h3 : 1 / ((N : ℝ) + 1) < ρ := by
      rw [div_lt_iff₀ (by positivity)]
      have h4 : (1 : ℝ) < (N : ℝ) * ρ := (div_lt_iff₀ hρ).mp hN
      nlinarith [hρ, hN, h4]
    rw [dist_eq_norm]
    exact lt_trans (lt_of_lt_of_le h1 h2) h3
  -- the limit is a quadrisecant chord of `r`
  have hchord : QuadrisecantChord r :=
    quadrisecantChord_of_tendsto_quadrisecants (r := r) (r' := fun n => r' (φ n)) hr
      (fun n => hr's (φ n)) hconv hQD hmem'
      (tendsto_coe_addCircle htA) (tendsto_coe_addCircle htB)
      (tendsto_coe_addCircle htZ) (tendsto_coe_addCircle htW)
  exact (hasQuadrisecant_iff_quadrisecantChord hr).mpr hchord

/-- **The generic reduction with the (unused) `hgen` parameter.**  The original statement of the
assembly, kept for the consumers that supply a `hgen` argument (e.g.
`Work.Drive.quadrisecant_of_genericCase_noInfl`); its proof never uses it.  The parameter-free form
`Work.Drive.quadrisecant_of_genericCase_full_noHgen` is the one the project's top-level assembly
needs, because an *unconditional* proof of `hgen` (`(QuadrisecantFree ∧ TGT) → IsUnknotted`) is not
available in the workspace — the route formalised here is the `O'`-crux route, which does not
consume `hgen` at all. -/
theorem quadrisecant_of_genericCase_full
    (hA : GenericFullFiniteDense) (hB : SpreadQuadrisecantFullClose)
    (_hgen : ∀ r : ℝ → Space, IsSmoothKnot r → QuadrisecantFree r →
      TorusGeneralPositionTransverse r →
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) → IsUnknotted r) :
    ∀ r : ℝ → Space, IsSmoothKnot r → ¬ IsUnknotted r → HasQuadrisecant r :=
  quadrisecant_of_genericCase_full_noHgen hA hB


end

end Work.Drive
