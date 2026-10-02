import Mathlib
import Submission.Work.Stems.HomAdd.PrismFaces
import Submission.Work.Stems.Pinch.readingPerm
import Submission.Work.Stems.HomAdd.cl_rhoPos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The class effect of the coordinate movement `rhoNeg`

`Work.Stems.HomAdd.rhoNeg i` is the self-map of the `n`-cube that occurs as the *top face* of the
`killMapNeg i`-prism (`Work.Stems.HomAdd.PrismFaces`): it moves the coordinate `i` into the last
slot, cyclically shifting the coordinates `i, …, n-1` down by one (no reflection).

It is exactly the coordinate permutation `Fin.cycleIcc i (Fin.last n)` read in the `permMap` sense,
so `readingPerm` and the sign of the tail cycle (`Work.Stems.HomAdd.cl_rhoPos_sign_cycleIcc_last`)
give `cl (p ∘ rhoNeg i) = (cl p)^{(-1)^{n-1-i}}`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.Stems.HomAdd

noncomputable section

variable {k : ℕ}

theorem rhoNeg_apply_lt {i : Fin (k+1)} {v : IC (k+1)} {j : Fin (k+1)}
    (hj : j < i) : rhoNeg i v j = v j := by
  have hφ : (Fin.castSucc i).succAbove j = Fin.castSucc j := Fin.succAbove_castSucc_of_lt i j hj
  have h1 : Fin.castSucc j ≠ Fin.castSucc i := fun h =>
    absurd (Fin.castSucc_inj.mp h) (ne_of_lt hj)
  have h2 : Fin.castSucc j ≠ Fin.last (k+1) := castSucc_ne_last j
  rw [rhoNeg, hφ, killMapNeg_apply_of_ne i h1 h2,
    show Fin.castSucc j = (Fin.last (k+1)).succAbove j from (congrFun Fin.succAbove_last j).symm,
    faceCM_apply, Work.RatHurewicz.faceFun_apply_succAbove]

theorem rhoNeg_apply_le {i : Fin (k+1)} {v : IC (k+1)} {j : Fin (k+1)}
    (hj : i ≤ j) (hjl : j ≠ Fin.last k) : rhoNeg i v j = v (j + 1) := by
  have hφ : (Fin.castSucc i).succAbove j = j.succ := Fin.succAbove_castSucc_of_le i j hj
  have hjlt : (j : ℕ) + 1 < k + 1 := by
    have h := Fin.val_lt_last hjl
    omega
  have hcast : j.succ = Fin.castSucc (j + 1 : Fin (k+1)) := by
    refine Fin.ext ?_
    rw [Fin.val_succ, Fin.val_castSucc, Fin.val_add_one_of_lt' hjlt]
  have hne1 : Fin.castSucc (j + 1 : Fin (k+1)) ≠ Fin.castSucc i := by
    intro h
    have hv := congrArg Fin.val (Fin.castSucc_inj.mp h)
    rw [Fin.val_add_one_of_lt' hjlt] at hv
    have hle := Fin.le_def.mp hj
    omega
  have hne2 : Fin.castSucc (j + 1 : Fin (k+1)) ≠ Fin.last (k+1) := castSucc_ne_last _
  rw [rhoNeg, hφ, hcast, killMapNeg_apply_of_ne i hne1 hne2,
    show Fin.castSucc (j + 1) = (Fin.last (k+1)).succAbove (j + 1) from
      (congrFun Fin.succAbove_last (j + 1)).symm,
    faceCM_apply, Work.RatHurewicz.faceFun_apply_succAbove]

theorem rhoNeg_apply_last (i : Fin (k+1)) (v : IC (k+1)) :
    rhoNeg i v (Fin.last k) = v i := by
  have hle : i ≤ Fin.last k := Fin.le_def.mpr (by simp only [Fin.val_last]; omega)
  have hφ : (Fin.castSucc i).succAbove (Fin.last k) = Fin.last (k+1) := by
    rw [Fin.succAbove_castSucc_of_le i (Fin.last k) hle, Fin.succ_last]
  rw [rhoNeg, hφ, killMapNeg_apply_last, faceCM_apply, Work.RatHurewicz.faceFun_apply_same,
    one_mul]
  rw [show Fin.castSucc i = (Fin.last (k+1)).succAbove i from (congrFun Fin.succAbove_last i).symm]
  rw [Work.RatHurewicz.faceFun_apply_succAbove]

/-- **`rhoNeg i` is the cycle `(i i+1 … n-1)` read as a coordinate permutation.** -/
theorem rhoNeg_eq_permMap_cycleIcc (i : Fin (k+1)) (v : IC (k+1)) :
    rhoNeg i v = Work.Stems.permMap (Fin.cycleIcc i (Fin.last k)) v := by
  funext j
  rw [Work.Stems.permMap_apply]
  rcases lt_or_ge j i with hj | hj
  · rw [rhoNeg_apply_lt hj, Fin.cycleIcc_of_lt hj]
  · by_cases hjl : j = Fin.last k
    · subst hjl
      rw [rhoNeg_apply_last i v,
        Fin.cycleIcc_of_last (Fin.le_def.mpr (by simp only [Fin.val_last]; omega))]
    · rw [rhoNeg_apply_le hj hjl,
        Fin.cycleIcc_of_ge_of_lt hj (Fin.lt_last_iff_ne_last.mpr hjl)]

theorem cl_rhoNeg_succ {X : Type} [TopologicalSpace X] {x₀ : X}
    (i : Fin (k+1)) (p q : GenLoop (Fin (k+1)) X x₀)
    (hq : ∀ v : IC (k+1), q.1 v = p.1 (rhoNeg i v)) :
    Work.RatHurewicz.cl (k+1) X x₀ q
      = (Work.RatHurewicz.cl (k+1) X x₀ p) ^ ((-1 : ℤ) ^ (k - (i : ℕ))) := by
  set cyc : Equiv.Perm (Fin (k+1)) := Fin.cycleIcc i (Fin.last k) with hcyc
  have hsign : ((Equiv.Perm.sign cyc : ℤˣ) : ℤ) = (-1 : ℤ) ^ (k - (i : ℕ)) := by
    rw [hcyc]
    exact cl_rhoPos_sign_cycleIcc_last i
  have hqc : ∀ u : IC (k+1), q.1 u = p.1 (fun j => u (cyc.symm.symm j)) := by
    intro u
    rw [Equiv.symm_symm]
    rw [hq u, rhoNeg_eq_permMap_cycleIcc, ← hcyc]
    rfl
  have hmain : Work.RatHurewicz.cl (k+1) X x₀ q
      = (Work.RatHurewicz.cl (k+1) X x₀ p) ^ (((Equiv.Perm.sign cyc : ℤˣ) : ℤ)) := by
    have h := Work.Stems.readingPerm cyc.symm p q hqc
    rwa [Equiv.Perm.sign_symm] at h
  rw [hmain, hsign]

end

theorem cl_rhoNeg {n : ℕ} (i : Fin n) [NeZero n] {X : Type} [TopologicalSpace X] {x₀ : X}
    (p q : GenLoop (Fin n) X x₀)
    (hq : ∀ v : Work.Stems.Cubical.IC n, q.1 v = p.1 (Work.Stems.HomAdd.rhoNeg i v)) :
    Work.RatHurewicz.cl n X x₀ q
      = (Work.RatHurewicz.cl n X x₀ p) ^ ((-1 : ℤ) ^ (n - 1 - (i : ℕ))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [show (k + 1) - 1 - (i : ℕ) = k - (i : ℕ) from by omega]
  exact cl_rhoNeg_succ (k := k) i p q hq

end Work.Stems.HomAdd
