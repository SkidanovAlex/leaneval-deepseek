import Mathlib
import Submission.Work.Pi6.EMM2.Defs
import Submission.Work.Serre.serreAttachKillPi
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.EMFG.killChain_pi_subsingleton
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The `K(ℤ,2)` model built from `S²` by killing `π₃, …, π_M` (area EMM2)

`kZB Y k` is `Y` with `(k)` rounds of "attach an `(m+2)`-cell along *every* map `S^{m+1} → −`"
applied for `m = 2, …, k+1`: concretely `kZ Y 0 = Y` and `kZ Y (k+1) = KillCells (k+2) (kZ Y k)`.
By `Work.Serre.killCells_step` the `j`-th round kills `π_{j+2}` and preserves `π_i` for `i ≤ j+1`,
so `kZ Y k` preserves `π_0, π_1, π_2` and kills `π_3, …, π_{k+2}`.

Applying this with `Y = S²` gives a range model of `K(ℤ,2)`, and — the point of the construction —
a map `φ : S² → X` into a space with `π_i(X) = 0` for `3 ≤ i ≤ M` extends over `kZ S² (M-2)`.

This file contains the definitions and the two `π`-bookkeeping lemmas; the range-model statement,
the extension statement and the (Les-)computations on the fibre are separate lemmas.
-/

open scoped Topology

namespace Work.Pi6.EMM2

noncomputable section

/-- A type bundled with its topology. -/
abbrev Bundled : Type 1 := Σ T : Type, TopologicalSpace T

/-- The iterated "kill `π₃, …, π_{k+2}`" tower, as bundled spaces. -/
noncomputable def kZB : Bundled → ℕ → Bundled
  | Y, 0 => Y
  | Y, (k + 1) => ⟨@Work.Serre.KillCells (k + 2) (kZB Y k).1 (kZB Y k).2, by
      letI : TopologicalSpace (kZB Y k).1 := (kZB Y k).2
      exact inferInstance⟩

/-- The iterated "kill `π₃, …, π_{k+2}`" tower over `Y`. -/
abbrev kZ (Y : Type) [tY : TopologicalSpace Y] (k : ℕ) : Type :=
  (kZB ⟨Y, tY⟩ k).1

instance kZTop (Y : Type) [tY : TopologicalSpace Y] (k : ℕ) : TopologicalSpace (kZ Y k) :=
  (kZB ⟨Y, tY⟩ k).2

attribute [instance] kZTop

/-- The one-step inclusion `kZ Y k → kZ Y (k+1)` (which kills `π_{k+3}`). -/
noncomputable def kZIncl (Y : Type) [tY : TopologicalSpace Y] (k : ℕ) :
    C(kZ Y k, kZ Y (k + 1)) :=
  Work.Serre.killIncl (k + 2) (kZ Y k)

/-- The inclusion `Y → kZ Y k`. -/
noncomputable def kZUp (Y : Type) [tY : TopologicalSpace Y] : ∀ k, C(Y, kZ Y k)
  | 0 => ContinuousMap.id Y
  | (k + 1) => (kZIncl Y k).comp (kZUp Y k)

@[simp]
theorem kZUp_zero (Y : Type) [tY : TopologicalSpace Y] :
    kZUp Y 0 = ContinuousMap.id Y := rfl

theorem kZUp_succ_apply (Y : Type) [tY : TopologicalSpace Y] (k : ℕ) (y : Y) :
    kZUp Y (k + 1) y = kZIncl Y k (kZUp Y k y) := rfl

/-- **`kZ Y k` has no homotopy in degrees `3, …, k+2`.**  The `j`-th round of the tower kills
`π_{j+2}` (`Work.Serre.killCells_step`) while preserving the lower degrees; the higher rounds
preserve the degrees already killed. -/
theorem kZ_pi_subsingleton {Y : Type} [TopologicalSpace Y] (k : ℕ) :
    ∀ (p : kZ Y k) (i : ℕ), 3 ≤ i → i ≤ k + 2 →
      Subsingleton (HomotopyGroup (Fin i) (kZ Y k) p) := by
  induction k with
  | zero =>
      intro p i hi hik
      omega
  | succ k ih =>
      intro p i hi hik
      have hstep := Work.Serre.killCells_step (k + 2) (kZ Y k)
      by_cases hle : i ≤ k + 2
      · obtain ⟨y, hy⟩ := hstep.2.2 p
        have hbij := hstep.1 i hle y
        have hsubY : Subsingleton (HomotopyGroup (Fin i) (kZ Y k) y) := ih y i hi hle
        have hsub : Subsingleton (HomotopyGroup (Fin i)
            (Work.Serre.KillCells (k + 2) (kZ Y k))
            (Work.Serre.killIncl (k + 2) (kZ Y k) y)) :=
          ⟨fun a b => by
            obtain ⟨a', rfl⟩ := hbij.surjective a
            obtain ⟨b', rfl⟩ := hbij.surjective b
            exact congrArg (Work.Serre.piMapN (Work.Serre.killIncl (k + 2) (kZ Y k)) i y)
              (hsubY.allEq a' b')⟩
        exact Work.EMFG.subsingleton_homotopyGroup_of_joined' hy.symm i (by omega) hsub
      · have hik' : i = k + 3 := by omega
        subst hik'
        exact hstep.2.1 p

/-- **The inclusion `Y → kZ Y k` is a bijection on `π_i` for `i ≤ 2`**: each round of the tower
preserves the degrees below the one it kills. -/
theorem kZUp_pi_bijective {Y : Type} [TopologicalSpace Y] (k : ℕ) :
    ∀ (i : ℕ), i ≤ 2 → ∀ y : Y,
      Function.Bijective (Work.Serre.piMapN (kZUp Y k) i y) := by
  induction k with
  | zero =>
      intro i _hi y
      have h : Work.Serre.piMapN (kZUp Y 0) i y = id := by
        funext a
        exact Work.Serre.piMapN_id i y a
      rw [h]
      exact Function.bijective_id
  | succ k ih =>
      intro i hi y
      have hcomp : Work.Serre.piMapN (kZUp Y (k + 1)) i y
          = (Work.Serre.piMapN (kZIncl Y k) i (kZUp Y k y))
              ∘ (Work.Serre.piMapN (kZUp Y k) i y) := by
        funext a
        exact Work.Serre.piMapN_comp (kZUp Y k) (kZIncl Y k) i y a
      rw [hcomp]
      have hstep : Function.Bijective
          (Work.Serre.piMapN (kZIncl Y k) i (kZUp Y k y)) :=
        (Work.Serre.killCells_step (k + 2) (kZ Y k)).1 i (by omega) (kZUp Y k y)
      exact hstep.comp (ih i hi y)

/-- The `πmap` (shifted index) form of `kZUp_pi_bijective`: the inclusion is a bijection on `π_1`
and `π_2`. -/
theorem kZUp_πmap_bijective {Y : Type} [TopologicalSpace Y] (k : ℕ) :
    ∀ (n : ℕ), n ≤ 1 → ∀ y : Y,
      Function.Bijective (Work.StemsB.πmap (kZUp Y k) n y) := by
  intro n hn y
  have h := kZUp_pi_bijective (Y := Y) k (n + 1) (by omega) y
  exact h

end

end Work.Pi6.EMM2
