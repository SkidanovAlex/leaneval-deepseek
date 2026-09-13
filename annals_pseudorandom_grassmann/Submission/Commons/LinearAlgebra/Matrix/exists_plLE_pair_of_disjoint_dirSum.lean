import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.exists_plLE_pair_of_disjoint

namespace Commons.LinearAlgebra.Matrix

open Module

local notation "𝔽₂" => ZMod 2

/-- If `C = A + B` and `Im A ∩ Im B ∩ Im C = {0}` then `A '' ker B` and `B '' ker A`
are disjoint.  (Cross version of `map_ker_inf_map_ker_eq_bot_of`.)

This is the key new fact making the "direct sum" condition available: it says that the
two pieces `Y'`, `Z'` of the construction below have ranges meeting trivially. -/
theorem map_ker_inf_map_ker_eq_bot_symm {m n : ℕ} (A B C : (Fin m → 𝔽₂) →ₗ[𝔽₂] (Fin n → 𝔽₂))
    (hC : C = A + B) (h1 : LinearMap.range A ⊓ LinearMap.range B ⊓ LinearMap.range C = ⊥) :
    Submodule.map A (LinearMap.ker B) ⊓ Submodule.map B (LinearMap.ker A) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro w ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
  have hAu : A u ∈ LinearMap.range A := ⟨u, rfl⟩
  have hBu : A u ∈ LinearMap.range B := ⟨v, hvu⟩
  have hCu : A u ∈ LinearMap.range C :=
    ⟨u, by rw [hC, LinearMap.add_apply, LinearMap.mem_ker.mp hu, add_zero]⟩
  have hmem : A u ∈ LinearMap.range A ⊓ LinearMap.range B ⊓ LinearMap.range C :=
    Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hAu, hBu⟩, hCu⟩
  rw [h1] at hmem
  simpa using hmem

theorem exists_plLE_pair_of_disjoint_dirSum {n m : ℕ} (X Y Z : Matrix (Fin n) (Fin m) (ZMod 2))
    (h : Y + Z = X)
    (h1 : LinearMap.range Y.mulVecLin ⊓ LinearMap.range Z.mulVecLin ⊓ LinearMap.range X.mulVecLin = ⊥)
    (h2 : LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin = ⊤) :
    ∃ Y' Z' : Matrix (Fin n) (Fin m) (ZMod 2),
      Y.rank = Y'.rank + (Y - Y').rank ∧ Z.rank = Z'.rank + (Z - Z').rank ∧
      (Y' + Z').rank = Y'.rank + Z'.rank ∧ Y' + Z' = X := by
  classical
  have hC : X.mulVecLin = Y.mulVecLin + Z.mulVecLin := by rw [← h, Matrix.mulVecLin_add]
  have hC' : X.mulVecLin = Z.mulVecLin + Y.mulVecLin := by rw [hC, add_comm]
  have h1' : LinearMap.range Z.mulVecLin ⊓ LinearMap.range Y.mulVecLin ⊓
      LinearMap.range X.mulVecLin = ⊥ := by
    rw [show LinearMap.range Z.mulVecLin ⊓ LinearMap.range Y.mulVecLin =
      LinearMap.range Y.mulVecLin ⊓ LinearMap.range Z.mulVecLin from inf_comm _ _]
    exact h1
  -- kernels spanning, as required by the extension lemma
  have hST_Y : LinearMap.ker Z.mulVecLin ⊔
      (LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker X.mulVecLin) = ⊤ := by
    rw [← h2]; ac_rfl
  have hST_Z : LinearMap.ker Y.mulVecLin ⊔
      (LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin) = ⊤ := by
    rw [← h2]; ac_rfl
  -- the two extensions
  obtain ⟨Y'Lin, hYs, hY'T, hYker, hYrange, hYdiffer, hYdker⟩ :=
    exists_linearMap_eqOn_of_sup_eq_top (LinearMap.ker Z.mulVecLin)
      (LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker X.mulVecLin) hST_Y Y.mulVecLin
      (inf_sup_ker_le_of Y.mulVecLin Z.mulVecLin X.mulVecLin hC h1)
  obtain ⟨Z'Lin, hZs, hZ'T, hZker, hZrange, hZdiffer, hZdker⟩ :=
    exists_linearMap_eqOn_of_sup_eq_top (LinearMap.ker Y.mulVecLin)
      (LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin) hST_Z Z.mulVecLin
      (inf_sup_ker_le_of Z.mulVecLin Y.mulVecLin X.mulVecLin hC' h1')
  have hY'T0 : ∀ t, t ∈ LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker X.mulVecLin → Y'Lin t = 0 :=
    fun t ht => LinearMap.mem_ker.mp (hY'T ht)
  have hZ'T0 : ∀ t, t ∈ LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin → Z'Lin t = 0 :=
    fun t ht => LinearMap.mem_ker.mp (hZ'T ht)
  -- matrices attached to the extensions
  let Y' : Matrix (Fin n) (Fin m) 𝔽₂ := Matrix.toLin'.symm Y'Lin
  let Z' : Matrix (Fin n) (Fin m) 𝔽₂ := Matrix.toLin'.symm Z'Lin
  have hY'lin : Y'.mulVecLin = Y'Lin := by
    rw [← Matrix.toLin'_apply']
    exact LinearEquiv.apply_symm_apply Matrix.toLin' Y'Lin
  have hZ'lin : Z'.mulVecLin = Z'Lin := by
    rw [← Matrix.toLin'_apply']
    exact LinearEquiv.apply_symm_apply Matrix.toLin' Z'Lin
  have hdiffY : (Y - Y').mulVecLin = Y.mulVecLin - Y'Lin := by rw [mulVecLin_sub, hY'lin]
  have hdiffZ : (Z - Z').mulVecLin = Z.mulVecLin - Z'Lin := by rw [mulVecLin_sub, hZ'lin]
  -- descriptions of the kernels of the four pieces
  have hk1 : LinearMap.ker Y'Lin =
      LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker X.mulVecLin := by
    rw [hYker, sup_eq_left.mpr (le_trans inf_le_right le_sup_left)]
  have hk2 : LinearMap.ker (Y.mulVecLin - Y'Lin) =
      LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker Y.mulVecLin := by
    rw [hYdker, inf_eq_right.mpr le_sup_left]
  have hl1 : LinearMap.ker Z'Lin =
      LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin := by
    rw [hZker, sup_eq_left.mpr (le_trans inf_le_right le_sup_left)]
  have hl2 : LinearMap.ker (Z.mulVecLin - Z'Lin) =
      LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker Z.mulVecLin := by
    rw [hZdker, inf_eq_right.mpr le_sup_left]
  refine ⟨Y', Z', ?_, ?_, ?_, ?_⟩
  · -- rank decomposition for Y
    have hkerY : LinearMap.ker Y'.mulVecLin ⊔ LinearMap.ker (Y - Y').mulVecLin = ⊤ := by
      rw [hY'lin, hdiffY, hk1, hk2, eq_top_iff, ← h2, sup_le_iff, sup_le_iff]
      exact ⟨⟨le_trans le_sup_left le_sup_left, le_trans le_sup_left le_sup_right⟩,
        le_trans le_sup_right le_sup_left⟩
    have hinfY : LinearMap.range Y'.mulVecLin ⊓ LinearMap.range (Y - Y').mulVecLin = ⊥ := by
      rw [hY'lin, hdiffY]
      have hr2 : LinearMap.range (Y.mulVecLin - Y'Lin) =
          Submodule.map Y.mulVecLin (LinearMap.ker X.mulVecLin) := by
        rw [hYdiffer, Submodule.map_sup, map_ker_eq_bot', bot_sup_eq]
      rw [hYrange, hr2]
      exact map_ker_inf_map_ker_eq_bot_of Y.mulVecLin Z.mulVecLin X.mulVecLin hC h1
    have key := rank_add_eq_rank_add_rank Y' (Y - Y') hkerY hinfY
    rwa [show Y' + (Y - Y') = Y from by abel] at key
  · -- rank decomposition for Z
    have hkerZ : LinearMap.ker Z'.mulVecLin ⊔ LinearMap.ker (Z - Z').mulVecLin = ⊤ := by
      rw [hZ'lin, hdiffZ, hl1, hl2, eq_top_iff, ← h2, sup_le_iff, sup_le_iff]
      exact ⟨⟨le_trans le_sup_left le_sup_right, le_trans le_sup_left le_sup_left⟩,
        le_trans le_sup_right le_sup_left⟩
    have hinfZ : LinearMap.range Z'.mulVecLin ⊓ LinearMap.range (Z - Z').mulVecLin = ⊥ := by
      rw [hZ'lin, hdiffZ]
      have hr2 : LinearMap.range (Z.mulVecLin - Z'Lin) =
          Submodule.map Z.mulVecLin (LinearMap.ker X.mulVecLin) := by
        rw [hZdiffer, Submodule.map_sup, map_ker_eq_bot', bot_sup_eq]
      rw [hZrange, hr2]
      exact map_ker_inf_map_ker_eq_bot_of Z.mulVecLin Y.mulVecLin X.mulVecLin hC' h1'
    have key := rank_add_eq_rank_add_rank Z' (Z - Z') hkerZ hinfZ
    rwa [show Z' + (Z - Z') = Z from by abel] at key
  · -- the sum Y' + Z' = X has rank the sum of the ranks (direct sum condition)
    have hsup : LinearMap.ker Y'.mulVecLin ⊔ LinearMap.ker Z'.mulVecLin = ⊤ := by
      rw [hY'lin, hZ'lin, hk1, hl1]
      refine le_antisymm le_top ?_
      rw [← h2]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact le_trans le_sup_left le_sup_left
      · exact le_trans le_sup_left le_sup_right
      · exact le_trans le_sup_right le_sup_left
    have hinf : LinearMap.range Y'.mulVecLin ⊓ LinearMap.range Z'.mulVecLin = ⊥ := by
      rw [hY'lin, hZ'lin, hYrange, hZrange]
      exact map_ker_inf_map_ker_eq_bot_symm Y.mulVecLin Z.mulVecLin X.mulVecLin hC h1
    exact rank_add_eq_rank_add_rank Y' Z' hsup hinf
  · -- the pair sums to X
    have hsumLin : Y'Lin + Z'Lin = X.mulVecLin := by
      apply LinearMap.ext
      intro w
      obtain ⟨u, hu, c, hc, huc⟩ :=
        Submodule.mem_sup.mp (show w ∈ LinearMap.ker Y.mulVecLin ⊔
          LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin by rw [h2]; trivial)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu
      have hw_eq : w = b + (a + c) := by rw [← huc, ← hab]; abel
      have hw_eq' : w = a + (b + c) := by rw [← huc, ← hab]; abel
      have hac : (a + c) ∈ LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker X.mulVecLin :=
        Submodule.add_mem_sup ha hc
      have hbc : (b + c) ∈ LinearMap.ker Z.mulVecLin ⊔ LinearMap.ker X.mulVecLin :=
        Submodule.add_mem_sup hb hc
      have hYw : Y'Lin w = Y.mulVecLin b := by
        rw [hw_eq, map_add, hYs b hb, hY'T0 (a + c) hac, add_zero]
      have hZw : Z'Lin w = Z.mulVecLin a := by
        rw [hw_eq', map_add, hZs a ha, hZ'T0 (b + c) hbc, add_zero]
      rw [LinearMap.add_apply, hYw, hZw]
      have key : X.mulVecLin w = Y.mulVecLin b + Z.mulVecLin a := by
        have ha0 : Y.mulVecLin a = 0 := LinearMap.mem_ker.mp ha
        have hb0 : Z.mulVecLin b = 0 := LinearMap.mem_ker.mp hb
        have hc0 : Y.mulVecLin c + Z.mulVecLin c = 0 := by
          have hcx := LinearMap.mem_ker.mp hc
          rwa [hC, LinearMap.add_apply] at hcx
        rw [hw_eq, hC, LinearMap.add_apply]
        simp only [map_add, ha0, hb0, zero_add]
        rw [show (Y.mulVecLin b + Y.mulVecLin c) + (Z.mulVecLin a + Z.mulVecLin c) =
            (Y.mulVecLin b + Z.mulVecLin a) + (Y.mulVecLin c + Z.mulVecLin c) from by abel,
          hc0, add_zero]
      rw [key]
    have hsum : Y' + Z' = X := by
      show Matrix.toLin'.symm Y'Lin + Matrix.toLin'.symm Z'Lin = X
      rw [← map_add, hsumLin, ← Matrix.toLin'_apply']
      exact LinearEquiv.symm_apply_apply Matrix.toLin' X
    exact hsum

end Commons.LinearAlgebra.Matrix
