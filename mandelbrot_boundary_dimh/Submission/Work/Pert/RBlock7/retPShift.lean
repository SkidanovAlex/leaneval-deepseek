import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.Gates
import Submission.Work.Pert.coordP_level_eq

/-!
# PERT · `Work.Pert.RBlock7.retPShift`: `T`-equivariance of the level-preserving return map

`Work.Pert.RBlock7.retP_phi_eq` shows that the level-preserving return map
`R̃ = Work.Pert.retP f Df τ Φ Wa α` (with the waist `Wa = Qm Ξ α ∩ Qp Ξ α` as level structure)
satisfies `φ_f ∘ R̃ = φ_f` for free.  Here we prove its other defining property,

  `R̃ (w+1) = R̃ w + 1`   (`T`-equivariance),

from the gate orbit relation and the single extra hypothesis that the forward walk from the two
level-`0` representatives stays inside the **upper** gate `Qp Ξ α` (so that the deck translate
`Tt α` of every walk point is a *gate* point, and the iterated Abel equation applies to it).

The combinatorics: with `m = mIdxP … w`, `n = mIdxP … (w+1)`, chosen representatives `ς`, `ς'` and
`Φ ς = w - m`, `Φ ς' = w + 1 - n`,

* if `n ≤ m` then `ς' = F^{m+1-n} ς` and `Φ (Tt α ς') = Φ (Tt α ς) + (m+1-n)`, giving
  `R̃ (w+1) = n + Φ(Tt α ς) + (m+1-n) = R̃ w + 1`;
* if `n ≥ m+1` then `ς = F^{n-m-1} ς'`, so `Φ (Tt α ς) = Φ (Tt α ς') + (n-m-1)` and
  `R̃ w = m + Φ(Tt α ς') + (n-m-1) = n - 1 + Φ(Tt α ς') = R̃ (w+1) - 1`.

No case distinction on `mIdxP` is needed beyond `n ≤ m` vs `m+1 ≤ n`.
-/

namespace Work.Pert.RBlock7

open _root_.MandelDim Complex Set

noncomputable section

/-- Iterating the commutation `F ∘ Tt α = Tt α ∘ F`. -/
private lemma iterate_Tt {F : ℂ → ℂ} {α : ℂ}
    (hcomm : ∀ w : ℂ, F (Work.Pert.Tt α w) = Work.Pert.Tt α (F w)) (j : ℕ) (x : ℂ) :
    F^[j] (Work.Pert.Tt α x) = Work.Pert.Tt α (F^[j] x) := by
  have hc : Function.Commute (Work.Pert.Tt α) F := fun w => (hcomm w).symm
  exact ((hc.iterate_right j) x).symm

/-- The iterated Abel equation for `Φ` along the `Tt α`-transport of an `F`-walk, given that the
walk points lie in the upper gate (so their deck translates lie in the lower gate). -/
private lemma abel_iter_transport {F Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {x : ℂ} {k : ℕ}
    (hab : ∀ z ∈ Work.Pert.Qm Ξ α, F z ∈ Work.Pert.Qm Ξ α → Φ (F z) = Φ z + 1)
    (hcomm : ∀ w : ℂ, F (Work.Pert.Tt α w) = Work.Pert.Tt α (F w))
    (hwalk : ∀ j : ℕ, j ≤ k → F^[j] x ∈ Work.Pert.Qp Ξ α) :
    Φ (F^[k] (Work.Pert.Tt α x)) = Φ (Work.Pert.Tt α x) + (k : ℂ) := by
  have hwalk' : ∀ j : ℕ, j ≤ k → F^[j] (Work.Pert.Tt α x) ∈ Work.Pert.Qm Ξ α := by
    intro j hj
    rw [iterate_Tt hcomm j x]
    exact Work.Pert.Tt_mem_Qm_iff.mpr (hwalk j hj)
  exact abel_iter hwalk' hab

theorem retP_add_one {f F τ Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {Df : Set ℂ} {w : ℂ}
    (hinj : Set.InjOn Φ (Work.Pert.Qm Ξ α))
    (hab : ∀ z ∈ Work.Pert.Qm Ξ α, F z ∈ Work.Pert.Qm Ξ α → Φ (F z) = Φ z + 1)
    (hOrb : ∀ z ∈ Work.Pert.Qm Ξ α, ∀ z' ∈ Work.Pert.Qm Ξ α, ∀ k : ℕ,
      Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Work.Pert.Qm Ξ α) ∧ F^[k] z = z')
    (hcomm : ∀ x : ℂ, F (Work.Pert.Tt α x) = Work.Pert.Tt α (F x))
    (hG : Work.Pert.GoodP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w)
    (hG1 : Work.Pert.GoodP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) (w + 1))
    (hw : ∀ j : ℕ, j ≤ Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w + 1 →
      F^[j] (Work.Pert.invOn Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)
        (w - (Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w : ℂ)))
      ∈ Work.Pert.Qp Ξ α)
    (hw1 : ∀ j : ℕ, j ≤ Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) (w + 1) →
      F^[j] (Work.Pert.invOn Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)
        (w + 1 - (Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) (w + 1) : ℂ)))
      ∈ Work.Pert.Qp Ξ α) :
    Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α (w + 1)
      = Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α w + 1 := by
  classical
  -- the two level representatives
  obtain ⟨hz, hzwalk⟩ := Work.Pert.mIdxP_spec hG
  obtain ⟨hz1, hz1walk⟩ := Work.Pert.mIdxP_spec hG1
  obtain ⟨ς, hςWa, hςΦ⟩ := hz
  obtain ⟨ς', hς'Wa, hς'Φ⟩ := hz1
  have hςQm : ς ∈ Work.Pert.Qm Ξ α := hςWa.1
  have hςQp : ς ∈ Work.Pert.Qp Ξ α := hςWa.2
  have hς'Qm : ς' ∈ Work.Pert.Qm Ξ α := hς'Wa.1
  have hς'Qp : ς' ∈ Work.Pert.Qp Ξ α := hς'Wa.2
  -- the inverses are the chosen representatives
  have hinvς : Work.Pert.invOn Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)
      (w - (Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w : ℂ)) = ς :=
    Work.Pert.invOn_eq (hinj.mono inter_subset_left) ⟨ς, hςWa, hςΦ⟩ hςWa hςΦ
  have hinvς' : Work.Pert.invOn Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)
      (w + 1 - (Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) (w + 1) : ℂ))
      = ς' :=
    Work.Pert.invOn_eq (hinj.mono inter_subset_left) ⟨ς', hς'Wa, hς'Φ⟩ hς'Wa hς'Φ
  rw [hinvς] at hw
  rw [hinvς'] at hw1
  -- the two `retP` values
  have hRw : Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α w
      = (Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w : ℂ)
        + Φ (Work.Pert.Tt α ς) := by
    simp only [Work.Pert.retP]
    rw [Work.Pert.invOn_eq (hinj.mono inter_subset_left) ⟨ς, hςWa, hςΦ⟩ hςWa hςΦ]
  have hRw1 : Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α (w + 1)
      = (Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) (w + 1) : ℂ)
        + Φ (Work.Pert.Tt α ς') := by
    simp only [Work.Pert.retP]
    rw [Work.Pert.invOn_eq (hinj.mono inter_subset_left) ⟨ς', hς'Wa, hς'Φ⟩ hς'Wa hς'Φ]
  rw [hRw, hRw1]
  set m : ℕ := Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w with hmdef
  set n : ℕ := Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) (w + 1) with hndef
  rcases lt_or_ge n (m + 1) with hlt | hge
  · -- `n ≤ m`:  `ς' = F^{m+1-n} ς`
    have hle : n ≤ m := by omega
    have hcast : ((m + 1 - n : ℕ) : ℂ) = (m : ℂ) + 1 - (n : ℂ) := by
      rw [Nat.cast_sub (by omega : n ≤ m + 1), Nat.cast_add, Nat.cast_one]
    obtain ⟨-, hfin⟩ := hOrb ς hςQm ς' hς'Qm (m + 1 - n)
      (by rw [hcast, hς'Φ, hςΦ]; ring)
    have htr := abel_iter_transport hab hcomm (x := ς) (k := m + 1 - n)
      (fun j hj => hw j (by omega))
    rw [iterate_Tt hcomm (m + 1 - n) ς, hfin] at htr
    rw [htr, hcast]
    ring
  · -- `m + 1 ≤ n`:  `ς = F^{n-m-1} ς'`
    have hm1 : m + 1 ≤ n := hge
    have hcast : ((n - (m + 1) : ℕ) : ℂ) = (n : ℂ) - ((m : ℂ) + 1) := by
      rw [Nat.cast_sub hm1, Nat.cast_add, Nat.cast_one]
    obtain ⟨-, hfin⟩ := hOrb ς' hς'Qm ς hςQm (n - (m + 1))
      (by rw [hcast, hςΦ, hς'Φ]; ring)
    have htr := abel_iter_transport hab hcomm (x := ς') (k := n - (m + 1))
      (fun j hj => hw1 j (by omega))
    rw [iterate_Tt hcomm (n - (m + 1)) ς', hfin] at htr
    rw [htr, hcast]
    ring

end

end Work.Pert.RBlock7
