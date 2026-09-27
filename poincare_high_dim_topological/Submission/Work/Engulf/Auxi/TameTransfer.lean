import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Auxi.Carrier

/-!
# A9 aux: `Tame`/`SmoothChart` are stable under subdivision and under changing `f` off `L`

`SmoothChart` only inspects `f` on faces contained in the frozen set `L`, so it is unchanged if `f`
is replaced by a map agreeing with it on `L` (`Tame.congr`); and by the carrier lemma every face of
a subdivision which is contained in `L` is contained in a *single* coarse face inside `L`, so the
local linearity clause transfers to subdivisions (`tame_subdivision`).
-/

open Set Metric PL Finset

namespace Work.Engulf

variable {n : ℕ} {M : Type*} [MetricSpace M] {N : ℕ}

theorem LinIn.mono {ψ : CubeChart n M} {f : E N → M} {S S' : Set (E N)} (h : S' ⊆ S)
    (hl : LinIn ψ f S) : LinIn ψ f S' := by
  obtain ⟨A, hA⟩ := hl
  exact ⟨A, fun y hy => hA y (h hy)⟩

/-- `SmoothChart` depends on `f` only through its restriction to `L`. -/
theorem SmoothChart.congr {p : ℕ} {X : Set M} {Γ : Cx N} {L : Set (E N)} {f g : E N → M}
    {ψ : CubeChart n M} (h : EqOn g f L) (hs : SmoothChart p X Γ L f ψ) :
    SmoothChart p X Γ L g ψ := by
  refine ⟨hs.1, ?_⟩
  intro s hsf hsL y hy hcube
  rw [h (hsL hy)] at hcube
  obtain ⟨δ, hδ, hlin⟩ := hs.2 s hsf hsL y hy hcube
  refine ⟨δ, hδ, ?_⟩
  obtain ⟨A, hA⟩ := hlin
  exact ⟨A, fun z hz => ⟨(hA z hz).1, by rw [h (hsL hz.1), (hA z hz).2]⟩⟩

/-- `Tame` depends on `f` only through its restriction to `L`. -/
theorem Tame.congr {p : ℕ} {X : Set M} {Γ : Cx N} {L : Set (E N)} {f g : E N → M}
    (h : EqOn g f L) (ht : Tame n p X Γ L f) : Tame n p X Γ L g := by
  intro x
  obtain ⟨ψ, hx, hs⟩ := ht x
  exact ⟨ψ, hx, hs.congr h⟩

/-- `Tame` transfers to a subdivision of the complex. -/
theorem tame_subdivision {p : ℕ} {X : Set M} {K : Cx N} {L : Set (E N)} {f : E N → M}
    (S : SubdivTools N) {r : ℕ} {hK : K.faces.Finite} (hLK : IsSubSp K L)
    (ht : Tame n p X K L f) : Tame n p X (S.sdIter r K hK) L f := by
  intro x
  obtain ⟨ψ, hx, hs⟩ := ht x
  refine ⟨ψ, hx, hs.1, ?_⟩
  intro s hsF hsL y hy hcube
  obtain ⟨τ, hτK, hτL, hτs⟩ := exists_coarse_face_of_simp_subset S hLK hsF hsL
  obtain ⟨δ, hδ, hlin⟩ := hs.2 τ hτK hτL y (hτs hy) hcube
  exact ⟨δ, hδ, LinIn.mono (S := simp τ ∩ ball y δ) (S' := simp s ∩ ball y δ)
    (fun z hz => ⟨hτs hz.1, hz.2⟩) hlin⟩

end Work.Engulf
