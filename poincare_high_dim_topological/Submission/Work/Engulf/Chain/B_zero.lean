import Mathlib
import Submission.Work.Engulf.Defs

namespace Work.Engulf.Chain

open Set Metric PL

/-- Under `BadCard Γ H f V 0`, every face of `Γ` contained in `H` has its image in `V`:
the only way a face can fail is `s.card ≤ 0`, i.e. `s = ∅`, and `f '' simp ∅ = ∅ ⊆ V`. -/
theorem image_subset_of_badCard_zero {N : ℕ} {M : Type*} [MetricSpace M]
    {Γ : Cx N} {H : Set (E N)} {f : E N → M} {V : Set M}
    (hBad : BadCard Γ H f V 0) {s : Finset (E N)} (hs : s ∈ Γ.faces) (hsH : simp s ⊆ H) :
    f '' simp s ⊆ V := by
  by_contra hbad
  have hcard : s.card ≤ 0 := hBad s hs hsH hbad
  have hs0 : s = ∅ := Finset.card_eq_zero.mp (by omega)
  rw [hs0] at hbad
  simp [simp] at hbad

/-- **`B_zero`** (base of the `B`-induction; `Submission/Work/NOTES_LEAD_poincare_engulf.md` §8): `B n p 0` says that if every face of `H` not mapped into `V` has at most `0` vertices, then `X ∪ f '' H ⊆ V` already holds and no engulfing is needed.  Proof: take `g := f` and the identity homeomorphism, `CSupp (Homeomorph.refl M) univ` with `C = ∅`; from `BadCard` (applied to the faces given by `IsSubSp Γ H`) get `f '' H ⊆ V`, and `X ⊆ V` is a hypothesis. -/
theorem B_zero (n p : ℕ) : Work.Engulf.B n p 0 := by
  intro M _ V X N Γ H L f _hAmb hCfg hXV hBad ε hε
  have hfH : f '' H ⊆ V := by
    rintro _ ⟨x, hxH, rfl⟩
    obtain ⟨s, hs, hxs, hsH⟩ := hCfg.subH.2 x hxH
    exact image_subset_of_badCard_zero hBad hs hsH ⟨x, hxs, rfl⟩
  refine ⟨f, hCfg.cont, fun x _ => rfl, fun x _ => by simpa using hε,
    Homeomorph.refl M, ?_, ?_⟩
  · refine ⟨∅, isCompact_empty, Set.empty_subset _, ?_⟩
    intro x _
    rfl
  · rw [Homeomorph.refl_apply, Set.image_id]
    exact Set.union_subset hXV hfH

end Work.Engulf.Chain
