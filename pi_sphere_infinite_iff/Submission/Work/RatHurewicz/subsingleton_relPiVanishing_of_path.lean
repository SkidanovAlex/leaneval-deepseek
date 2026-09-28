import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.RelPiPathDefs
import Submission.Work.RatHurewicz.RelPiPathBasepoint
import Submission.Work.RatHurewicz.RelPiPathHomotopy
import Submission.Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint

namespace Work.RatHurewicz

open scoped Topology Topology.Homotopy unitInterval

/-- **Basepoint change for the relative groups along a path in the subspace.**

Let `A ⊆ Y`, let `η` be a path in `↥A` from `a₀` to `a` (so both endpoints lie in `A`), and let
`k : ℕ`.  If the `k`-th homotopy group of the homotopy fibre of `setIncl A : ↥A → Y` at `a₀` is
trivial, then so is the `k`-th homotopy group of the homotopy fibre at `a`:
`Subsingleton (RelHomotopyGroup (setIncl A) a₀ k) → Subsingleton (RelHomotopyGroup (setIncl A) a k)`.

Proof route.  The homotopy fibres are
`fibre(a) = {(a', γ) : γ a path in Y from a to a' ∈ A}` (the pullback of the path–loop fibration
`evalOne` along `setIncl A`), and concatenation with `η` gives continuous maps
`φ : fibre(a) → fibre(a₀), (a', γ) ↦ (a', η * γ)` and
`ψ : fibre(a₀) → fibre(a), (a', γ') ↦ (a', η⁻¹ * γ')`,
mutually inverse up to homotopy by the concatenation homotopies `η * η⁻¹ ~ const` and
`η⁻¹ * η ~ const`.  They are therefore homotopy equivalences, and one transports the vanishing
with `Work.Stems.mulEquiv_of_homotopyEquiv` together with the basepoint-change result
`Work.Stems.subsingleton_homotopyGroup_change_basepoint`.  Note (pointedness): `φ` is not pointed
for the canonical basepoints — `φ (a, Path.refl a) = (a, η)` and the canonical basepoint of
`fibre(a₀)` is `(a₀, Path.refl a₀)`; the two are joined by the path
`t ↦ (η (1 - t), s ↦ η (s * (1 - t)))` inside `fibre(a₀)`, so the transport needs one basepoint
change inside each of the two homotopy fibres in addition to the homotopy equivalence.
The imports `Submission.Work.Stems.mulEquiv_of_homotopyEquiv` and
`Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint` are declared in `depends_on`
and do not import `Work.RatHurewicz`, so there is no cycle. -/
theorem subsingleton_relPiVanishing_of_path {Y : Type} [TopologicalSpace Y] {A : Set Y}
    (a₀ a : ↥A) (η : Path a₀ a) (k : ℕ)
    (h : Subsingleton (RelHomotopyGroup (setIncl A) a₀ k)) :
    Subsingleton (RelHomotopyGroup (setIncl A) a k) := by
  let e : ContinuousMap.HomotopyEquiv (homotopyFibre (setIncl A) a)
      (homotopyFibre (setIncl A) a₀) :=
    { toFun := relPathPhi a₀ a η
      invFun := relPathPsi a₀ a η
      left_inv := relPathPsi_comp_relPathPhi_homotopic a₀ a η
      right_inv := relPathPhi_comp_relPathPsi_homotopic a₀ a η }
  by_cases hk : k = 0
  · subst hk
    have hZ : Subsingleton (ZerothHomotopy (homotopyFibre (setIncl A) a₀)) := by
      haveI := h
      let ex := homotopyGroupEquivZerothHomotopyOfIsEmpty (N := Fin 0)
        (X := homotopyFibre (setIncl A) a₀) (homotopyFibreBasepoint (setIncl A) a₀)
      exact ⟨fun u v => ex.symm.injective (Subsingleton.elim (ex.symm u) (ex.symm v))⟩
    have hZ' : Subsingleton (ZerothHomotopy (homotopyFibre (setIncl A) a)) :=
      subsingleton_zerothHomotopy_of_homotopyEquiv e hZ
    haveI := hZ'
    let ex := homotopyGroupEquivZerothHomotopyOfIsEmpty (N := Fin 0)
      (X := homotopyFibre (setIncl A) a) (homotopyFibreBasepoint (setIncl A) a)
    exact ⟨fun u v => ex.injective (Subsingleton.elim (ex u) (ex v))⟩
  · haveI : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
    obtain ⟨me⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin k) e
      (homotopyFibreBasepoint (setIncl A) a)
    have hb : Subsingleton (HomotopyGroup (Fin k) (homotopyFibre (setIncl A) a₀)
        (e (homotopyFibreBasepoint (setIncl A) a))) :=
      Work.Stems.subsingleton_homotopyGroup_change_basepoint (N := Fin k)
        (show Path (homotopyFibreBasepoint (setIncl A) a₀)
          (e (homotopyFibreBasepoint (setIncl A) a))
          from (joined_relPathPhi_basepoint a₀ a η).somePath) h
    haveI := hb
    exact ⟨fun u v => me.injective (Subsingleton.elim (me u) (me v))⟩

end Work.RatHurewicz
