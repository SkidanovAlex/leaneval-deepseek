import Mathlib
import Submission.Work.Stems.HomAdd.PrismFaces
import Submission.Work.Stems.Pinch.readingPerm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The class effect of the coordinate movement `rhoPos`

`Work.Stems.HomAdd.rhoPos i` is the self-map of the `n`-cube that occurs as the *top face* of the
`killMapPos i`-prism (`Work.Stems.HomAdd.PrismFaces`): it moves the coordinate `i` into the last
slot, cyclically shifting the coordinates `i, …, n-1` down by one and replacing the last coordinate
by `1 - v i`.

The lemma proved here is the only sign input of the elementary proof of Hutchings' `(2.2b)`
(`Work.RatHurewicz.PinchAll`, see `Submission/Work/Stems/HomAdd/DESIGN.md`): reading a based cube
through `rhoPos i` multiplies its class by `(-1)^{n-i}`.

The proof decomposes `rhoPos i` as the last-coordinate flip composed with the coordinate permutation
`Fin.cycleIcc i (Fin.last (n-1))` (the cycle `(i i+1 … n-1)`), and then uses

* `Work.Stems.flipMap_class` (a coordinate reversal inverts the class), and
* `Work.Stems.readingPerm` (a coordinate permutation acts by its sign)
* `Fin.sign_cycleIcc_of_le` (a cycle of length `n-i` has sign `(-1)^{n-i-1}`).

The only genuinely computational part is the pointwise formula for `rhoPos` (`rhoPos_eq_flipMap_permMap`
below), which is a finite case analysis on `Fin n` using `Fin.succAbove`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.Stems.HomAdd

noncomputable section

variable {k : ℕ}

/-! ## The pointwise description of `rhoPos`

For `i : Fin (k+1)` and `v : IC (k+1)` (so that the last index of `IC (k+1)` is `Fin.last k`):

* `rhoPos i v j = v j` for `j < i`;
* `rhoPos i v j = v (j+1)` for `i ≤ j ≠ Fin.last k`;
* `rhoPos i v (Fin.last k) = 1 - v i`.

These are exactly the components of `flipMap (Fin.last k) ∘ permMap (Fin.cycleIcc i (Fin.last k))`. -/

theorem cl_rhoPos_apply_lt {i : Fin (k+1)} {v : IC (k+1)} {j : Fin (k+1)}
    (hj : j < i) : rhoPos i v j = v j := by
  have hφ : (Fin.castSucc i).succAbove j = Fin.castSucc j := Fin.succAbove_castSucc_of_lt i j hj
  have h1 : Fin.castSucc j ≠ Fin.castSucc i := fun h =>
    absurd (Fin.castSucc_inj.mp h) (ne_of_lt hj)
  have h2 : Fin.castSucc j ≠ Fin.last (k+1) := castSucc_ne_last j
  rw [rhoPos, hφ, killMapPos_apply_of_ne i h1 h2,
    show Fin.castSucc j = (Fin.last (k+1)).succAbove j from (congrFun Fin.succAbove_last j).symm,
    faceCM_apply, Work.RatHurewicz.faceFun_apply_succAbove]

theorem cl_rhoPos_apply_le {i : Fin (k+1)} {v : IC (k+1)} {j : Fin (k+1)}
    (hj : i ≤ j) (hjl : j ≠ Fin.last k) : rhoPos i v j = v (j + 1) := by
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
  rw [rhoPos, hφ, hcast, killMapPos_apply_of_ne i hne1 hne2,
    show Fin.castSucc (j + 1) = (Fin.last (k+1)).succAbove (j + 1) from
      (congrFun Fin.succAbove_last (j + 1)).symm,
    faceCM_apply, Work.RatHurewicz.faceFun_apply_succAbove]

theorem cl_rhoPos_apply_last (i : Fin (k+1)) (v : IC (k+1)) :
    rhoPos i v (Fin.last k) = unitInterval.symm (v i) := by
  have hle : i ≤ Fin.last k := Fin.le_def.mpr (by simp only [Fin.val_last]; omega)
  have hφ : (Fin.castSucc i).succAbove (Fin.last k) = Fin.last (k+1) := by
    rw [Fin.succAbove_castSucc_of_le i (Fin.last k) hle, Fin.succ_last]
  rw [rhoPos, hφ, killMapPos_apply_last, faceCM_apply, Work.RatHurewicz.faceFun_apply_same,
    one_mul]
  congr 1
  rw [show Fin.castSucc i = (Fin.last (k+1)).succAbove i from (congrFun Fin.succAbove_last i).symm]
  rw [Work.RatHurewicz.faceFun_apply_succAbove]

/-- **The coordinate movement `rhoPos` is a flip of the last coordinate composed with the cycle
`(i i+1 … n-1)`.** -/
theorem cl_rhoPos_eq_flipMap_permMap (i : Fin (k+1)) (v : IC (k+1)) :
    rhoPos i v
      = Work.Stems.flipMap (Fin.last k) (Work.Stems.permMap (Fin.cycleIcc i (Fin.last k)) v) := by
  funext j
  rw [Work.Stems.flipMap_apply]
  by_cases hjl : j = Fin.last k
  · subst hjl
    rw [if_pos rfl, cl_rhoPos_apply_last i v, Work.Stems.permMap_apply,
      Fin.cycleIcc_of_last (Fin.le_def.mpr (by simp only [Fin.val_last]; omega))]
  · rw [if_neg hjl, Work.Stems.permMap_apply]
    rcases lt_or_ge j i with hj | hj
    · rw [cl_rhoPos_apply_lt hj, Fin.cycleIcc_of_lt hj]
    · rw [cl_rhoPos_apply_le hj hjl,
        Fin.cycleIcc_of_ge_of_lt hj (Fin.lt_last_iff_ne_last.mpr hjl)]

/-! ## The sign of the tail cycle -/

/-- The cycle `(i i+1 … n-1)` of `Fin (k+1)` has sign `(-1)^{k-i}`. -/
theorem cl_rhoPos_sign_cycleIcc_last (i : Fin (k+1)) :
    ((Equiv.Perm.sign (Fin.cycleIcc i (Fin.last k)) : ℤˣ) : ℤ) = (-1 : ℤ) ^ (k - (i : ℕ)) := by
  rw [Fin.sign_cycleIcc_of_le (Fin.le_def.mpr (by simp only [Fin.val_last]; omega))]
  rw [Units.val_pow_eq_pow_val]
  norm_num

/-- `(a⁻¹)^{(-1)^m} = a^{(-1)^{m+1}}`. -/
theorem cl_rhoPos_inv_zpow_neg_one_pow {G : Type} [Group G] (a : G) (m : ℕ) :
    (a⁻¹) ^ ((-1 : ℤ) ^ m) = a ^ ((-1 : ℤ) ^ (m + 1)) := by
  rw [inv_zpow']
  congr 1
  rw [pow_succ]
  ring

/-! ## The class computation -/

theorem cl_rhoPos_succ {X : Type} [TopologicalSpace X] {x₀ : X}
    (i : Fin (k+1)) (p q : GenLoop (Fin (k+1)) X x₀)
    (hq : ∀ v : IC (k+1), q.1 v = p.1 (rhoPos i v)) :
    Work.RatHurewicz.cl (k+1) X x₀ q
      = (Work.RatHurewicz.cl (k+1) X x₀ p) ^ ((-1 : ℤ) ^ ((k+1) - (i : ℕ))) := by
  set cyc : Equiv.Perm (Fin (k+1)) := Fin.cycleIcc i (Fin.last k) with hcyc
  set p' : GenLoop (Fin (k+1)) X x₀ :=
    ⟨p.1.comp (Work.Stems.flipMap (Fin.last k)),
      fun u hu => p.2 _ (Work.Stems.flipMap_boundary (Fin.last k) hu)⟩ with hp'def
  have hcl_p' : Work.RatHurewicz.cl (k+1) X x₀ p'
      = (Work.RatHurewicz.cl (k+1) X x₀ p)⁻¹ := by
    rw [hp'def]
    exact Work.Stems.flipMap_class (Fin.last k) p
  have hsign : ((Equiv.Perm.sign cyc : ℤˣ) : ℤ) = (-1 : ℤ) ^ (k - (i : ℕ)) := by
    rw [hcyc]
    exact cl_rhoPos_sign_cycleIcc_last i
  have hqc : ∀ u : IC (k+1), q.1 u = p'.1 (fun j => u (cyc.symm.symm j)) := by
    intro u
    rw [Equiv.symm_symm, hp'def]
    rw [hq u, cl_rhoPos_eq_flipMap_permMap, ← hcyc]
    rfl
  have hmain : Work.RatHurewicz.cl (k+1) X x₀ q
      = (Work.RatHurewicz.cl (k+1) X x₀ p') ^ (((Equiv.Perm.sign cyc : ℤˣ) : ℤ)) := by
    have h := Work.Stems.readingPerm cyc.symm p' q hqc
    rwa [Equiv.Perm.sign_symm] at h
  rw [hmain, hcl_p', hsign, cl_rhoPos_inv_zpow_neg_one_pow]
  have hk : (k + 1) - (i : ℕ) = (k - (i : ℕ)) + 1 := by
    have := i.isLt
    omega
  rw [hk]

end

theorem cl_rhoPos {n : ℕ} (i : Fin n) [NeZero n] {X : Type} [TopologicalSpace X] {x₀ : X}
    (p q : GenLoop (Fin n) X x₀)
    (hq : ∀ v : Work.Stems.Cubical.IC n, q.1 v = p.1 (Work.Stems.HomAdd.rhoPos i v)) :
    Work.RatHurewicz.cl n X x₀ q
      = (Work.RatHurewicz.cl n X x₀ p) ^ ((-1 : ℤ) ^ (n - (i : ℕ))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact cl_rhoPos_succ (k := k) i p q hq

end Work.Stems.HomAdd
