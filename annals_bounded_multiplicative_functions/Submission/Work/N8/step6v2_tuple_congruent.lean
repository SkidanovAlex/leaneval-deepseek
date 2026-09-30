import Mathlib
import Submission.Work.N8.step6v2_defs
import Submission.Work.N8.step6_defs
import Submission.Work.N8.cycle_congruence
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

theorem step6v2_tuple_congruent {V : Type} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) [DecidableRel Adj]
    (T : Finset V) (pr : V → V → ℕ × ℕ) (γ : V → Polynomial ℝ) (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ)
    (P : ℝ)
    (u : V) (hu : u ∈ T) (mw qw : ℕ)
    (hedge : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      Work.BMF.IsPrimeIn P (2 * P) (pr v v').1 ∧ Work.BMF.IsPrimeIn P (2 * P) (pr v v').2 ∧
      Work.BMF.IntegralOn 1 (Work.BMF.dil (((pr v v').2 : ℕ) : ℝ) (γ v) -
        Work.BMF.dil (((pr v v').1 : ℕ) : ℝ) (γ v')))
    (hdvd : ∀ A B : ℕ, Work.BMF.IntegralOn 1
      (Work.BMF.dil (A : ℝ) (γ u) - Work.BMF.dil (B : ℝ) (γ u)) →
      (qw : ℤ) ∣ ((A : ℤ) ^ mw - (B : ℤ) ^ mw))
    (w : Fin ℓ → V) (hw : w ∈ Work.N8.step6Walks Adj T ℓ)
    (hw0 : w ⟨0, by omega⟩ = u) :
    (∏ i, Work.N8.step6Tuple2 ℓ pr w i) ^ mw ≡
      (∏ i, Work.N8.step6Tuple1 ℓ pr w i) ^ mw [MOD qw] := by
  classical
  -- `ℓ ≥ 1`, so `cycle_congruence` applies with `m = ℓ`.
  have hℓ1 : 1 ≤ ℓ := by omega
  obtain ⟨hwT, hwAdj⟩ := mem_step6Walks.mp hw
  -- The two tuples of edge labels read along the walk, as functions `Fin ℓ → ℕ`.
  set p₁ : Fin ℓ → ℕ := fun j => (pr (w j) (w (step6next ℓ j))).1 with hp₁
  set p₂ : Fin ℓ → ℕ := fun j => (pr (w j) (w (step6next ℓ j))).2 with hp₂
  -- The base point of the walk, for an arbitrary proof that `0 < ℓ`.
  have hw0u : ∀ h : 0 < ℓ, w ⟨0, h⟩ = u := by
    intro h
    have : (⟨0, h⟩ : Fin ℓ) = ⟨0, by omega⟩ := Fin.ext rfl
    rw [this]; exact hw0
  -- The edge relation at every step of the walk: exactly the lattice congruence
  -- `γ_{j}(p₂ j ·) - γ_{j+1}(p₁ j ·)` integral on `ℤ`.
  have hrel : ∀ j : Fin ℓ, Work.BMF.IntegralOn 1
      (Work.BMF.dil ((p₂ j : ℕ) : ℝ) (γ (w j)) -
        Work.BMF.dil ((p₁ j : ℕ) : ℝ)
          (γ (w ⟨((j : ℕ) + 1) % ℓ, Nat.mod_lt _ (by omega)⟩))) := by
    intro j
    have h := (hedge (w j) (hwT j) (w (step6next ℓ j)) (hwT (step6next ℓ j)) (hwAdj j)).2.2
    have hidx : w (step6next ℓ j) = w ⟨((j : ℕ) + 1) % ℓ, Nat.mod_lt _ (by omega)⟩ := by
      have hstep6 : step6next ℓ j = (⟨((j : ℕ) + 1) % ℓ, Nat.mod_lt _ (by omega)⟩ : Fin ℓ) :=
        Fin.ext rfl
      rw [hstep6]
    rw [hp₁, hp₂, ← hidx]
    exact h
  -- Telescoping the congruences around the closed walk.
  have hcyc := cycle_congruence ℓ hℓ1 (fun j => γ (w j)) p₁ p₂ hrel
  -- At the base point `w 0 = u`, the telescoped relation reads
  -- `γ_u((∏ p₂) ·) - γ_u((∏ p₁) ·) ∈ ℤ`.
  have hcyc' : Work.BMF.IntegralOn 1
      (Work.BMF.dil (((Finset.univ.prod p₂ : ℕ)) : ℝ) (γ u) -
        Work.BMF.dil (((Finset.univ.prod p₁ : ℕ)) : ℝ) (γ u)) := by
    simpa only [hw0u] using hcyc
  -- The arithmetic hypothesis turns this into a congruence of `mw`-th powers.
  have hd : (qw : ℤ) ∣
      (((Finset.univ.prod p₂ : ℕ) : ℤ) ^ mw - ((Finset.univ.prod p₁ : ℕ) : ℤ) ^ mw) :=
    hdvd (Finset.univ.prod p₂) (Finset.univ.prod p₁) hcyc'
  -- Identify the two products with the tuples read along the walk.
  have e1 : (∏ i, Work.N8.step6Tuple1 ℓ pr w i) = Finset.univ.prod p₁ := by
    apply Finset.prod_congr rfl; intro i _
    rw [hp₁]; rfl
  have e2 : (∏ i, Work.N8.step6Tuple2 ℓ pr w i) = Finset.univ.prod p₂ := by
    apply Finset.prod_congr rfl; intro i _
    rw [hp₂]; rfl
  rw [Nat.modEq_iff_dvd, e2, e1, Nat.cast_pow, Nat.cast_pow]
  simpa [neg_sub] using dvd_neg.mpr hd

end Work.N8
