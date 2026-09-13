import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.rank_poset_trans
import Submission.Commons.LinearAlgebra.Matrix.rank_le_of_sub
import Submission.Commons.LinearAlgebra.Matrix.range_inf_range_sub_eq_bot
import Submission.Commons.LinearAlgebra.Matrix.range_sup_range_sub_eq
import Submission.Commons.LinearAlgebra.Matrix.rank_eq_zero_iff
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_le_finrank_le_pow

set_option linter.style.haveILetI false

namespace Commons.LinearAlgebra.Matrix

open Module

/-- **Fiber bound for the rank poset over `𝔽₂`.**

Fix a matrix `Y` over `ZMod 2` with `Y.rank ≤ d`.  Then the number of matrices `X` of rank
`k` that are "below" `Y` in the rank poset, i.e. satisfy
`Y.rank = X.rank + (Y - X).rank`, is at most `2 ^ (3 * k * d)`.

The condition `Y.rank = X.rank + (Y - X).rank` means that `X` and `Y - X` have independent
images summing to the image of `Y`.  Writing `V = range Y.mulVecLin` (`finrank V = Y.rank ≤ d`),
every such `X` is the projection of `Y` onto its own image along the image of `Y - X`, so `X`
is determined by the pair `(range X.mulVecLin, range (Y - X).mulVecLin)` of submodules of `V`.
This gives an injection into the product of the `k`-dimensional and the `(Y.rank - k)`-dimensional
submodules of `V`, whose cardinalities are bounded by
`card_submodule_le_finrank_le_pow`. -/
theorem card_rank_poset_fiber_le_pow (n m d k : ℕ) (Y : Matrix (Fin n) (Fin m) (ZMod 2))
    (hY : Y.rank ≤ d) :
    Nat.card {X : Matrix (Fin n) (Fin m) (ZMod 2) //
      Y.rank = X.rank + (Y - X).rank ∧ X.rank = k} ≤ 2 ^ (3 * k * d) := by
  classical
  set V : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.range Y.mulVecLin with hV
  have hfr : Module.finrank (ZMod 2) V = Y.rank := by rw [hV]; rfl
  by_cases hk0 : k = 0
  · -- The rank-zero matrices form a subsingleton, so the fiber has at most one element.
    subst hk0
    have hsub : Subsingleton {X : Matrix (Fin n) (Fin m) (ZMod 2) //
        Y.rank = X.rank + (Y - X).rank ∧ X.rank = 0} := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : a.1 = 0 := (rank_eq_zero_iff a.1).mp a.2.2
      have hb : b.1 = 0 := (rank_eq_zero_iff b.1).mp b.2.2
      rw [ha, hb]
    have hle1 : Nat.card {X : Matrix (Fin n) (Fin m) (ZMod 2) //
        Y.rank = X.rank + (Y - X).rank ∧ X.rank = 0} ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr hsub
    calc Nat.card {X : Matrix (Fin n) (Fin m) (ZMod 2) //
            Y.rank = X.rank + (Y - X).rank ∧ X.rank = 0} ≤ 1 := hle1
      _ = 2 ^ (3 * 0 * d) := by norm_num
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    by_cases hkr : k ≤ Y.rank
    · -- Main case: inject the fiber into the product of the `k`- and `(Y.rank - k)`-dimensional
      -- submodules of `V`.
      let A := {U : Submodule (ZMod 2) (Fin n → ZMod 2) // U ≤ V ∧ Module.finrank (ZMod 2) U = k}
      let B := {W : Submodule (ZMod 2) (Fin n → ZMod 2) //
        W ≤ V ∧ Module.finrank (ZMod 2) W = Y.rank - k}
      let Ψ : {X : Matrix (Fin n) (Fin m) (ZMod 2) //
            Y.rank = X.rank + (Y - X).rank ∧ X.rank = k} → A × B :=
        fun X =>
          (⟨LinearMap.range X.1.mulVecLin, by
              rw [hV, range_sup_range_sub_eq X.1 Y X.2.1]; exact le_sup_left,
            X.2.2⟩,
           ⟨LinearMap.range (Y - X.1).mulVecLin, by
              rw [hV, range_sup_range_sub_eq X.1 Y X.2.1]; exact le_sup_right, by
                have h1 : Y.rank = k + (Y - X.1).rank := by
                  calc Y.rank = X.1.rank + (Y - X.1).rank := X.2.1
                    _ = k + (Y - X.1).rank := by rw [X.2.2]
                have h2 : (Y - X.1).rank = Y.rank - k := by omega
                show Module.finrank (ZMod 2) (LinearMap.range (Y - X.1).mulVecLin) = Y.rank - k
                rw [show Module.finrank (ZMod 2) (LinearMap.range (Y - X.1).mulVecLin)
                      = (Y - X.1).rank from rfl]
                exact h2⟩)
      have hΨ : Function.Injective Ψ := by
        intro X₁ X₂ h
        have hU : LinearMap.range X₁.1.mulVecLin = LinearMap.range X₂.1.mulVecLin :=
          congrArg (fun z : A × B => (z.1).1) h
        have hW : LinearMap.range (Y - X₁.1).mulVecLin = LinearMap.range (Y - X₂.1).mulVecLin :=
          congrArg (fun z : A × B => (z.2).1) h
        apply Subtype.ext
        have hlin : X₁.1.mulVecLin = X₂.1.mulVecLin := by
          apply LinearMap.ext
          intro v
          have hbot := range_inf_range_sub_eq_bot X₁.1 Y X₁.2.1
          have hmemU : X₁.1.mulVec v - X₂.1.mulVec v ∈ LinearMap.range X₁.1.mulVecLin := by
            apply Submodule.sub_mem
            · exact LinearMap.mem_range_self _ v
            · rw [hU]; exact LinearMap.mem_range_self _ v
          have hmemW : X₁.1.mulVec v - X₂.1.mulVec v ∈ LinearMap.range (Y - X₁.1).mulVecLin := by
            have hz : X₁.1.mulVec v - X₂.1.mulVec v =
                (Y - X₂.1).mulVec v - (Y - X₁.1).mulVec v := by
              rw [Matrix.sub_mulVec, Matrix.sub_mulVec]; abel
            rw [hz]
            apply Submodule.sub_mem
            · rw [hW]; exact LinearMap.mem_range_self _ v
            · exact LinearMap.mem_range_self _ v
          have hmem : X₁.1.mulVec v - X₂.1.mulVec v ∈
              (⊥ : Submodule (ZMod 2) (Fin n → ZMod 2)) := by
            rw [← hbot]; exact Submodule.mem_inf.mpr ⟨hmemU, hmemW⟩
          have hz : X₁.1.mulVec v - X₂.1.mulVec v = 0 := by simpa using hmem
          rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
          exact sub_eq_zero.mp hz
        ext i j
        have hc := congrArg (fun f : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) =>
          f (Pi.single j 1) i) hlin
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
          Matrix.mulVec_single_one, Matrix.col_apply, Matrix.col_apply] at hc
        exact hc
      have hcard1 : Nat.card {X : Matrix (Fin n) (Fin m) (ZMod 2) //
            Y.rank = X.rank + (Y - X).rank ∧ X.rank = k} ≤ Nat.card (A × B) :=
        Nat.card_le_card_of_injective Ψ hΨ
      have hAB : Nat.card (A × B) ≤ Nat.card A * Nat.card B := by
        rw [Nat.card_prod]
      have hA : Nat.card A ≤ 2 ^ (k * (Y.rank - k) + k) := by
        have h := Commons.LinearAlgebra.Submodule.card_submodule_le_finrank_le_pow
          (K := ZMod 2) (V := Fin n → ZMod 2) V k
        rw [Nat.card_zmod, hfr] at h
        exact h
      have hB : Nat.card B ≤ 2 ^ ((Y.rank - k) * k + (Y.rank - k)) := by
        have h := Commons.LinearAlgebra.Submodule.card_submodule_le_finrank_le_pow
          (K := ZMod 2) (V := Fin n → ZMod 2) V (Y.rank - k)
        rw [Nat.card_zmod, hfr, Nat.sub_sub_self hkr] at h
        exact h
      have hexp : k * (Y.rank - k) + k + ((Y.rank - k) * k + (Y.rank - k)) ≤ 3 * k * d := by
        have h1 : k * (Y.rank - k) ≤ k * d :=
          Nat.mul_le_mul_left k (le_trans (Nat.sub_le _ _) hY)
        have h2 : (Y.rank - k) * k ≤ k * d := by
          rw [Nat.mul_comm]; exact Nat.mul_le_mul_left k (le_trans (Nat.sub_le _ _) hY)
        have h3 : k + (Y.rank - k) ≤ k * d := by
          rw [Nat.add_sub_cancel' hkr]
          exact le_trans hY (by simpa using Nat.mul_le_mul_right d hk1)
        have hrearr : k * (Y.rank - k) + k + ((Y.rank - k) * k + (Y.rank - k))
            = (k * (Y.rank - k) + (Y.rank - k) * k) + (k + (Y.rank - k)) := by omega
        rw [hrearr]
        calc (k * (Y.rank - k) + (Y.rank - k) * k) + (k + (Y.rank - k))
            ≤ (k * d + k * d) + k * d := Nat.add_le_add (Nat.add_le_add h1 h2) h3
          _ = 3 * k * d := by ring
      calc Nat.card {X : Matrix (Fin n) (Fin m) (ZMod 2) //
              Y.rank = X.rank + (Y - X).rank ∧ X.rank = k}
            ≤ 2 ^ (k * (Y.rank - k) + k) * 2 ^ ((Y.rank - k) * k + (Y.rank - k)) :=
            le_trans (le_trans hcard1 hAB) (Nat.mul_le_mul hA hB)
        _ = 2 ^ (k * (Y.rank - k) + k + ((Y.rank - k) * k + (Y.rank - k))) := by rw [← pow_add]
        _ ≤ 2 ^ (3 * k * d) := Nat.pow_le_pow_right (by norm_num) hexp
    · -- Case `Y.rank < k`: the fiber is empty since `rank X ≤ rank Y`.
      have hkr' : Y.rank < k := not_le.mp hkr
      haveI : IsEmpty {X : Matrix (Fin n) (Fin m) (ZMod 2) //
          Y.rank = X.rank + (Y - X).rank ∧ X.rank = k} :=
        ⟨fun a => by
          have h1 : a.1.rank ≤ Y.rank := rank_le_of_sub a.1 Y a.2.1
          have h2 : a.1.rank = k := a.2.2
          omega⟩
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _

end Commons.LinearAlgebra.Matrix
