import Mathlib
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.bike_adi_side
import Submission.Work.BMF.GAdjQ_iff_stepS_or

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset Real

theorem polyrel_walk_maxmin {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : Work.BMF.QuadData k f c C X L P₁ P₂) (hC : 0 < C) (hP : 0 < P₁) (hL : 0 < L)
    (hbig : 8000 * P₁ ^ 2 < X / L) (hL1 : 1 ≤ L / (2 * P₁))
    (hLbig : 2 * Work.BMF.symmConst k (max C (Work.BMF.symmConst k C)) * ((k : ℝ) + 1) *
        (k : ℝ) ^ k * (k.factorial : ℝ) < L / (2 * P₁))
    {ℓ : ℕ} {x : ℝ} {q : ℕ} {W : Fin (ℓ + 1) → Work.BMF.GVert D}
    (hW : W ∈ Work.BMF.closedWalkVal D q ℓ x)
    {S : Finset ℕ} (hSne : S.Nonempty) (hSprime : ∀ p ∈ S, p.Prime)
    (hstep : ∀ p ∈ S, ∀ j : Fin ℓ,
      p ∈ Work.BMF.stepS D (W j.castSucc) (W j.succ) ∨
      p ∈ Work.BMF.stepS D (W j.succ) (W j.castSucc)) :
    Work.BMF.PolyRel k
      (max (Work.BMF.cycConst k (Work.BMF.symmConst k (max C (Work.BMF.symmConst k C))) ℓ)
        (Work.BMF.symmConst k
          (Work.BMF.cycConst k (Work.BMF.symmConst k (max C (Work.BMF.symmConst k C))) ℓ)))
      (1 / ((S.prod (fun p => p) : ℕ) : ℝ))
      (x / (((max (Work.BMF.walkProdV D ℓ W) (Work.BMF.walkProdU D ℓ W) : ℕ)) : ℝ))
      (L / (((max (Work.BMF.walkProdV D ℓ W) (Work.BMF.walkProdU D ℓ W) : ℕ)) : ℝ))
      (Work.BMF.dil (((max (Work.BMF.walkProdV D ℓ W) (Work.BMF.walkProdU D ℓ W) : ℕ)) : ℝ)
        (D.pol x))
      (x / (((min (Work.BMF.walkProdV D ℓ W) (Work.BMF.walkProdU D ℓ W) : ℕ)) : ℝ))
      (L / (((min (Work.BMF.walkProdV D ℓ W) (Work.BMF.walkProdU D ℓ W) : ℕ)) : ℝ))
      (Work.BMF.dil (((min (Work.BMF.walkProdV D ℓ W) (Work.BMF.walkProdU D ℓ W) : ℕ)) : ℝ)
        (D.pol x)) := by
  classical
  obtain ⟨hWwalk, hWlast, hW0⟩ := Finset.mem_filter.mp hW
  obtain ⟨-, hadj⟩ := Finset.mem_filter.mp hWwalk
  -- pass to the full graph
  have hWall : W ∈ closedWalkAll D ℓ x := by
    rw [closedWalkAll, Finset.mem_filter, walkSetAll, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ W, fun j => GAdjQ_le_GAdjAll D (hadj j)⟩, hWlast.symm, hW0⟩
  have hmain := bike_adi_side D hC hP hL hbig hL1 hLbig hWall hSne hSprime hstep
  -- positivity of the two products of primes
  have hVpos : 0 < walkProdV D ℓ W :=
    Finset.prod_pos (fun j _ => (stepV_prime D (hadj j)).1.pos)
  have hUpos : 0 < walkProdU D ℓ W :=
    Finset.prod_pos (fun j _ => (stepU_prime D (hadj j)).1.pos)
  have hVpos' : (0 : ℝ) < ((walkProdV D ℓ W : ℕ) : ℝ) := by exact_mod_cast hVpos
  have hUpos' : (0 : ℝ) < ((walkProdU D ℓ W : ℕ) : ℝ) := by exact_mod_cast hUpos
  have hCcyc : 0 < cycConst k (symmConst k (max C (symmConst k C))) ℓ :=
    cycConst_pos k (symmConst_pos (lt_of_lt_of_le hC (le_max_left _ _))) ℓ
  by_cases hle : walkProdU D ℓ W ≤ walkProdV D ℓ W
  · -- `max = walkProdV`, `min = walkProdU`
    have hmax : max (walkProdV D ℓ W) (walkProdU D ℓ W) = walkProdV D ℓ W :=
      le_antisymm (max_le le_rfl hle) (le_max_left _ _)
    have hmin : min (walkProdV D ℓ W) (walkProdU D ℓ W) = walkProdU D ℓ W :=
      le_antisymm (min_le_right _ _) (le_min hle le_rfl)
    rw [hmax, hmin]
    exact PolyRel.mono hmain (le_max_left _ _)
      (div_nonneg hL.le hVpos'.le) (div_nonneg hL.le hUpos'.le)
  · -- `walkProdV < walkProdU`, so `max = walkProdU`, `min = walkProdV`
    have hlt : walkProdV D ℓ W < walkProdU D ℓ W := not_le.mp hle
    have hmax : max (walkProdV D ℓ W) (walkProdU D ℓ W) = walkProdU D ℓ W :=
      le_antisymm (max_le hlt.le le_rfl) (le_max_right _ _)
    have hmin : min (walkProdV D ℓ W) (walkProdU D ℓ W) = walkProdV D ℓ W :=
      le_antisymm (min_le_left _ _) (le_min le_rfl hlt.le)
    rw [hmax, hmin]
    exact PolyRel.mono (hmain.symm hCcyc (div_pos hL hVpos') (div_pos hL hUpos'))
      (le_max_right _ _) (div_nonneg hL.le hUpos'.le) (div_nonneg hL.le hVpos'.le)

end Work.BMF
