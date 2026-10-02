import Mathlib
import Submission.Work.Serre.serreAttachCompress
import Submission.Work.Serre.serreAttachKillPi
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress
import Submission.Work.Serre.attachIncl_pi0_bijective
import Submission.Work.Serre.exists_joined_attachIncl
import Submission.Work.Serre.Models
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.attachCells_piMap_bijective
import Submission.Work.RatHurewicz.excisionTransfer
import Submission.Work.RatHurewicz.CompressRelToRelPi
import Submission.Work.RatHurewicz.LESConsequences
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.killFamily_subsingleton
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.pi_homeo_invariance
import Submission.Work.StemsB.basepoint_transport
import Submission.Work.Serre.fibrationPiOne

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

open scoped Topology unitInterval

open Work.StemsB

noncomputable section

/-- **Triviality of a homotopy group transports along a path.** -/
theorem subsingleton_homotopyGroup_of_joined {X : Type} [TopologicalSpace X] {x y : X}
    (h : Joined x y) (k : ℕ) :
    Subsingleton (HomotopyGroup (Fin (k + 1)) X x) →
      Subsingleton (HomotopyGroup (Fin (k + 1)) X y) := by
  intro hx
  obtain ⟨γ⟩ := h
  obtain ⟨e⟩ := Work.StemsB.basepoint_transport k γ
  haveI := hx
  exact ⟨fun a b => e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b))⟩

/-- **The "killing" step, at the base point `killIncl n Y y`.** -/
theorem killIncl_pi_subsingleton (n : ℕ) (Y : Type) [TopologicalSpace Y] (y : Y) :
    Subsingleton (HomotopyGroup (Fin (n + 1)) (KillCells n Y) (killIncl n Y y)) := by
  refine ⟨fun a b => ?_⟩
  have h1 : ∀ a : HomotopyGroup (Fin (n + 1)) (KillCells n Y) (killIncl n Y y), a = 1 := by
    intro a
    obtain ⟨c, rfl⟩ :=
      Work.RatHurewicz.surjective_πmap_attachIncl n Y (KillIdx n Y) (fun g => g) y a
    exact serreAttachKillPi n Y y c
  rw [h1 a, h1 b]

/-- **The one-step analysis of the Postnikov tower.** -/
theorem killCells_step (m : ℕ) (Y : Type) [TopologicalSpace Y] :
    (∀ i : ℕ, i ≤ m → ∀ y : Y, Function.Bijective (piMapN (killIncl m Y) i y)) ∧
    (∀ p : KillCells m Y,
      Subsingleton (HomotopyGroup (Fin (m + 1)) (KillCells m Y) p)) ∧
    (∀ p : KillCells m Y, ∃ y : Y, Joined p (killIncl m Y y)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi y
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have hfun : piMapN (killIncl m Y) 0 y
          = HomotopyGroup.map (N := Fin 0)
              (Work.RatHurewicz.attachIncl m Y (KillIdx m Y) (fun g => g)) (x := y) := by
        funext a
        rfl
      rw [hfun]
      exact attachIncl_pi0_bijective m Y (KillIdx m Y) (fun g => g) y
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      have hfun : Work.StemsB.πmap
            (Work.RatHurewicz.attachIncl m Y (KillIdx m Y) (fun g => g)) j y
          = piMapN (killIncl m Y) (j + 1) y := by
        funext a
        rfl
      rw [← hfun]
      exact attachIncl_piMap_bijective_of_compress m Y (KillIdx m Y) (fun g => g) y
        (j + 1) (by omega) (by omega)
  · intro p
    obtain ⟨y, hy⟩ := exists_joined_attachIncl m Y (KillIdx m Y) (fun g => g) p
    exact subsingleton_homotopyGroup_of_joined hy.symm m (killIncl_pi_subsingleton m Y y)
  · intro p
    exact exists_joined_attachIncl m Y (KillIdx m Y) (fun g => g) p

/-- **The finite Postnikov truncation of a space, in a form strong enough for the induction.** -/
theorem serrePostnikovTower_strong (k : ℕ) :
    ∀ (m N : ℕ) (Y : Type) [TopologicalSpace Y], N - m = k → m ≤ N →
      ∃ (P : Type) (_ : TopologicalSpace P) (g : C(Y, P)),
        (∀ i : ℕ, i ≤ m → ∀ y : Y, Function.Bijective (piMapN g i y)) ∧
        (∀ i : ℕ, m < i → i ≤ N → ∀ p : P, Subsingleton (HomotopyGroup (Fin i) P p)) ∧
        (∀ p : P, ∃ y : Y, Joined p (g y)) := by
  induction k with
  | zero =>
    intro m N Y _ hNm hmN
    have hmN' : m = N := by omega
    subst hmN'
    refine ⟨Y, inferInstance, ContinuousMap.id Y, ?_, ?_, ?_⟩
    · intro i hi y
      have h : piMapN (ContinuousMap.id Y) i y = id := funext fun a => piMapN_id i y a
      rw [h]
      exact Function.bijective_id
    · intro i hi h2
      omega
    · intro p
      exact ⟨p, Joined.refl p⟩
  | succ k ih =>
    intro m N Y _ hNm hmN
    have hmlt : m < N := by omega
    obtain ⟨P, topP, g', hg'1, hg'2, hg'3⟩ :=
      ih (m + 1) N (KillCells m Y) (by omega) (by omega)
    refine ⟨P, topP, g'.comp (killIncl m Y), ?_, ?_, ?_⟩
    · intro i hi y
      have hg'i : Function.Bijective (piMapN g' i (killIncl m Y y)) :=
        hg'1 i (by omega) (killIncl m Y y)
      have hφi : Function.Bijective (piMapN (killIncl m Y) i y) :=
        (killCells_step m Y).1 i hi y
      have heq : piMapN (g'.comp (killIncl m Y)) i y
          = (piMapN g' i (killIncl m Y y)) ∘ (piMapN (killIncl m Y) i y) := by
        funext a
        exact piMapN_comp (killIncl m Y) g' i y a
      rw [heq]
      exact hg'i.comp hφi
    · intro i hi hiN p
      rcases eq_or_lt_of_le (show m + 1 ≤ i from hi) with h | h
      · obtain ⟨y', hy'⟩ := hg'3 p
        obtain ⟨y, hy⟩ := exists_joined_attachIncl m Y (KillIdx m Y) (fun g => g) y'
        have hkillY' : Subsingleton (HomotopyGroup (Fin (m + 1)) (KillCells m Y) y') :=
          subsingleton_homotopyGroup_of_joined hy.symm m (killIncl_pi_subsingleton m Y y)
        have hP : Subsingleton (HomotopyGroup (Fin (m + 1)) P (g' y')) := by
          haveI := hkillY'
          exact (hg'1 (m + 1) le_rfl y').surjective.subsingleton
        subst h
        exact subsingleton_homotopyGroup_of_joined hy'.symm m hP
      · exact hg'2 i h hiN p
    · intro p
      obtain ⟨y', hy'⟩ := hg'3 p
      obtain ⟨y, hy⟩ := exists_joined_attachIncl m Y (KillIdx m Y) (fun g => g) y'
      exact ⟨y, hy'.trans (Joined.map hy g'.continuous)⟩

theorem serrePostnikovTower :
    ∀ (m N : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y), m ≤ N →
      ∃ (P : Type) (_ : TopologicalSpace P) (g : C(Y, P)),
        (∀ i : ℕ, i ≤ m → Function.Bijective (Work.Serre.piMapN g i y₀)) ∧
        (∀ i : ℕ, m < i → i ≤ N → ∀ p : P, Subsingleton (HomotopyGroup (Fin i) P p)) := by
  intro m N Y _ y₀ hmN
  obtain ⟨P, topP, g, h1, h2, _⟩ :=
    serrePostnikovTower_strong (N - m) m N Y rfl hmN
  exact ⟨P, topP, g, fun i hi => h1 i hi y₀, h2⟩

end

end Work.Serre
