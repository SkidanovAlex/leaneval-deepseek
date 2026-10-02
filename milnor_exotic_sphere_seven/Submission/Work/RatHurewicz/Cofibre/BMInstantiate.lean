import Mathlib
import Submission.Work.RatHurewicz.Cofibre.BMHyp
import Submission.Work.RatHurewicz.Cofibre.URetractEqv
import Submission.Work.RatHurewicz.homotopyExcision
import Submission.Work.RatHurewicz.Cofibre.collarHomotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Instantiating the Blakers–Massey hypotheses and applying the excision theorem

This file feeds the two hypotheses proved in `Cofibre/BMHyp.lean` — hypothesis (A) for
`(cofibreU ι, cofibreU ι ∩ cofibreV ι)` and hypothesis (B) for `(cofibreV ι, …)` — into
`Work.RatHurewicz.homotopyExcision` with `p = k-2`, `q = k`, and transfers the conclusion to the
relative groups of the subspace inclusion `cofibreV ι ↪ cofibre ι`.

The inputs of (A) and (B) are the connectivities of the three pieces of the cover:
`↥(cofibreU ι) ≃ E` (`cofibreUHomotopyEquiv`), `↥(cofibreV ι)` contractible
(`exists_contraction_cofibreV`) and the collar `↥(cofibreU ι ∩ cofibreV ι) ≃ F`
(`collarHomotopyEquiv`).  They enter here in the form of `∀ y, Subsingleton (π_J _ y)` hypotheses.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- **`π_J ↥(cofibreU ι)` is trivial** when `π_J E` is, for every base point (the half-open cone
retracts onto `E` by `cofibreUHomotopyEquiv`). -/
theorem subsingleton_pi_cofibreU (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) (J : ℕ)
    (hJ : 1 ≤ J) (hE : ∀ y : E, Subsingleton (HomotopyGroup (Fin J) E y))
    (z : ↥(cofibreU ι)) : Subsingleton (HomotopyGroup (Fin J) ↥(cofibreU ι) z) := by
  haveI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  exact (subsingleton_homotopyGroup_of_homotopyEquiv (N := Fin J)
    (cofibreUHomotopyEquiv ι e₀) z).mpr (hE (cofibreURetract ι e₀ z))

/-- **`π_J` of the collar is trivial** when `π_J F` is, for every base point (the collar is homotopy
equivalent to `F` by `Cofibre.collarHomotopyEquiv`). -/
theorem subsingleton_pi_collar (ι : C(F, E)) [Nonempty F] (J : ℕ) (hJ : 1 ≤ J)
    (hF : ∀ y : F, Subsingleton (HomotopyGroup (Fin J) F y))
    (x : ↥(cofibreU ι ∩ cofibreV ι)) :
    Subsingleton (HomotopyGroup (Fin J) ↥(cofibreU ι ∩ cofibreV ι) x) := by
  obtain ⟨e⟩ := Cofibre.collarHomotopyEquiv ι
  haveI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  exact (subsingleton_homotopyGroup_of_homotopyEquiv (N := Fin J) e x).mpr (hF (e.toFun x))

/-- **Hypothesis (A), instantiated**: the relative groups of `(cofibreU ι, cofibreU ι ∩ cofibreV ι)`
are trivial once `π_{J+1} E` and `π_J` of the collar are. -/
theorem subsingleton_relPi_interInclLeft_of_conn (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E)
    (J : ℕ) (x₀ : ↥(cofibreU ι ∩ cofibreV ι))
    (hE : ∀ y : E, Subsingleton (HomotopyGroup (Fin (J + 1)) E y))
    (hcol : Subsingleton (HomotopyGroup (Fin J) ↥(cofibreU ι ∩ cofibreV ι) x₀)) :
    Subsingleton (RelHomotopyGroup (interInclLeft (cofibreU ι) (cofibreV ι)) x₀ J) :=
  subsingleton_relPi_interInclLeft ι J x₀ hcol
    (subsingleton_pi_cofibreU ι e₀ (J + 1) (by omega) hE ⟨x₀.1, x₀.2.1⟩)

/-- **Hypothesis (B), instantiated**: the relative groups of `(cofibreV ι, cofibreU ι ∩ cofibreV ι)`
are trivial once `π_{J+1} ↥(cofibreV ι)` and `π_J` of the collar are. -/
theorem subsingleton_relPi_interInclRight_of_conn (ι : C(F, E)) (J : ℕ)
    (x₀ : ↥(cofibreU ι ∩ cofibreV ι))
    (hV : Subsingleton (HomotopyGroup (Fin (J + 1)) ↥(cofibreV ι) ⟨x₀.1, x₀.2.2⟩))
    (hcol : Subsingleton (HomotopyGroup (Fin J) ↥(cofibreU ι ∩ cofibreV ι) x₀)) :
    Subsingleton (RelHomotopyGroup (interInclRight (cofibreU ι) (cofibreV ι)) x₀ J) :=
  subsingleton_relPi_interInclRight ι J x₀ hcol hV

/-- **Blakers–Massey for the cover of the cofibre.**  Under the two hypotheses of the excision
theorem (`p = k-2` for `(cofibreU ι, cofibreU ι ∩ cofibreV ι)` and `q = k` for the other pair) and
the vanishing of the relative groups of `(cofibreU ι, cofibreU ι ∩ cofibreV ι)` in the wider range
`J ≤ 2k-2`, `J ≠ k-1` — which provides the *source* of the comparison map — the relative groups of
the subspace inclusion `cofibreV ι ↪ cofibre ι` are trivial in the range `1 ≤ J ≤ 2k-2`,
`J ≠ k-1`. -/
theorem subsingleton_relPi_cofibreV_of_blakersMassey (ι : C(F, E)) (k : ℕ)
    (x₀ : ↥(cofibreU ι ∩ cofibreV ι))
    (hA : ∀ J : ℕ, J ≤ k - 2 →
      Subsingleton (RelHomotopyGroup (interInclLeft (cofibreU ι) (cofibreV ι)) x₀ J))
    (hB : ∀ J : ℕ, J ≤ k →
      Subsingleton (RelHomotopyGroup (interInclRight (cofibreU ι) (cofibreV ι)) x₀ J))
    (hvan : ∀ J : ℕ, J ≤ 2 * k - 2 → J ≠ k - 1 →
      Subsingleton (RelHomotopyGroup (interInclLeft (cofibreU ι) (cofibreV ι)) x₀ J))
    (J : ℕ) (hJ1 : 1 ≤ J) (hJ : J ≤ 2 * k - 2) (hJk : J ≠ k - 1) :
    Subsingleton (RelHomotopyGroup (setIncl (cofibreV ι)) ⟨x₀.1, x₀.2.2⟩ J) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, J = n + 1 := ⟨J - 1, by omega⟩
  have hbij := Work.RatHurewicz.homotopyExcision (X := cofibre ι) (B := cofibreU ι)
    (C := cofibreV ι) (cofibreU_union_cofibreV ι) (isOpen_cofibreU ι) (isOpen_cofibreV ι)
    x₀ (k - 2) k hA hB n (by omega)
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hbij.surjective a
  obtain ⟨b', rfl⟩ := hbij.surjective b
  rw [(hvan (n + 1) (by omega) hJk).elim a' b']

end

end Work.RatHurewicz
