import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_gen
import Submission.Work.Smooth.JordanSeparation.lwalk_peel_main
import Submission.Work.Smooth.JordanSeparation.loopNat_homotopy_unpack

/-!
# The walk loop is null-homotopic in `↥U`

`lwalk_nullhomotopic_of_n_le` (`lwalk_peel_main.lean`) proves that the *lifted* loop `W.loopNat`
of a closed lattice walk whose trace lies in `U` is null-homotopic in `↥U` (given that `U` is open
with preconnected complement in the sphere).  Here we transfer that to the realization
`W.loopIn hbase hval`, and deduce that loops in `U` are null-homotopic from the approximation
(`lwalk_approximation`).
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- A homotopy in `X` whose image lies in a subset `S` and whose sides have ranges in `S` lifts to a
homotopy in `↥S`. -/
theorem Path.Homotopic.subtype_of_range' {X : Type*} [TopologicalSpace X] {S : Set X} {a b : X}
    (ha : a ∈ S) (hb : b ∈ S) {p q : Path a b} (hp : Set.range p ⊆ S) (hq : Set.range q ⊆ S)
    (F : Path.Homotopy p q) (hF : Set.range F ⊆ S) :
    (Path.toSubtype ha hb p hp).Homotopic (Path.toSubtype ha hb q hq) := by
  refine ⟨?_⟩
  refine ContinuousMap.HomotopyWith.mk ?_ ?_
  · refine ContinuousMap.Homotopy.mk ?_ ?_ ?_
    · exact ⟨fun ts => ⟨F ts, hF ⟨ts, rfl⟩⟩, Continuous.subtype_mk F.continuous _⟩
    · intro z; exact Subtype.ext (F.map_zero_left z)
    · intro z; exact Subtype.ext (F.map_one_left z)
  · rintro t z (hz | hz)
    · subst hz; exact Subtype.ext (by show F (t, 0) = p 0; rw [F.source t, p.source])
    · subst hz; exact Subtype.ext (by show F (t, 1) = p 1; rw [F.target t, p.target])

/-- **The realization of a closed lattice walk with trace in `U` is null-homotopic in `↥U`.** -/
theorem loopIn_homotopic_refl {U : Set ℂ} (hUo : IsOpen U)
    (hpre : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty}))
    (W : LWalk) (hbase : W.pt 0 ∈ U) (hval : ∀ t, W.path t ∈ U) :
    Path.Homotopic (W.loopIn hbase hval) (Path.refl (⟨W.pt 0, hbase⟩ : ↥U)) := by
  have hpt : W.pt 0 ∈ U := W.pt_mem hval (Nat.zero_le _)
  obtain ⟨H, hH⟩ := loopNat_homotopy_unpack W hval
    (lwalk_nullhomotopic_of_n_le W.n hUo hpre W le_rfl hval)
  have hp : Set.range W.loop ⊆ (U : Set ℂ) := fun y hy => by
    rcases hy with ⟨s, rfl⟩
    have h0 : H (0, s) = W.loop s := H.map_zero_left s
    rw [← h0]
    exact hH (0, s)
  have hq : Set.range (Path.refl (W.pt 0)) ⊆ (U : Set ℂ) := fun y hy => by
    rcases hy with ⟨s, rfl⟩
    exact hpt
  have hF : Set.range H ⊆ (U : Set ℂ) := fun y hy => by
    rcases hy with ⟨s, rfl⟩
    exact hH s
  have hlift := Path.Homotopic.subtype_of_range' hpt hpt hp hq H hF
  have e1 : Path.toSubtype hpt hpt W.loop hp = W.loopIn hbase hval := by
    apply Path.ext
    funext t
    apply Subtype.ext
    rw [LWalk.loopIn, path_cast_apply]
    rfl
  have e2 : Path.toSubtype hpt hpt (Path.refl (W.pt 0)) hq
      = Path.refl (⟨W.pt 0, hbase⟩ : ↥U) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    rfl
  rw [e1, e2] at hlift
  exact hlift

/-- An open preconnected non-empty subset of `ℂ` is path connected. -/
theorem isPathConnected_of_isOpen_of_isPreconnected {U : Set ℂ} (hUo : IsOpen U)
    (hUp : IsPreconnected U) (hUne : U.Nonempty) : IsPathConnected U :=
  (hUo.isConnected_iff_isPathConnected).mp ⟨hUne, hUp⟩

/-- The approximation statement of `lwalk_approximation`, as a hypothesis (so that the rest of the
argument can be developed independently of it). -/
def LWalkApprox : Prop := ∀ {U : Set ℂ}, IsOpen U → ∀ {x : ℂ} (hx : x ∈ U),
      (γ : Path (⟨x, hx⟩ : ↥U) (⟨x, hx⟩ : ↥U)) →
      ∃ (W : LWalk) (hbase : W.pt 0 ∈ U) (hval : ∀ t, W.path t ∈ U)
        (a : Path (⟨x, hx⟩ : ↥U) (⟨W.pt 0, hbase⟩ : ↥U)),
        Path.Homotopic γ (a.trans ((W.loopIn hbase hval).trans a.symm))

/-- **Loops in an open set with preconnected complement in the sphere are null-homotopic**, given
the approximation of `lwalk_approximation`. -/
theorem plane_loops_of_approx (approx : LWalkApprox)
    {U : Set ℂ} (hUo : IsOpen U)
    (hpre : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty}))
    {x : ℂ} (hx : x ∈ U) (γ : Path (⟨x, hx⟩ : ↥U) (⟨x, hx⟩ : ↥U)) :
    Path.Homotopic γ (Path.refl (⟨x, hx⟩ : ↥U)) := by
  obtain ⟨W, hbase, hval, a, ha⟩ := approx hUo hx γ
  exact homotopic_refl_of_conj γ (W.loopIn hbase hval) a ha
    (loopIn_homotopic_refl hUo hpre W hbase hval)

end

end Work.Smooth.JordanSeparation
