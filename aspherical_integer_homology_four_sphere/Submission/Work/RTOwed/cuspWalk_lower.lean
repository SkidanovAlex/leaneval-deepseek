import Mathlib
import Submission.Work.RTOwed.cuspWall_step
import Submission.Work.RTOwed.cuspWallTableCerts
import Submission.Work.RTOwed.cuspCert.CuspSupport
import Submission.Work.RTOwed.cuspDev
import Submission.Work.RTOwed.cuspCertWalls
import Submission.Work.RTOwed.CuspPiece

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-- The generator of a lower wall of the far cube agrees with the generator of the corresponding
lower wall of the near cube, for the directions *along* the wall (certificate conjunct 5 of
`cuspWallTableCerts` at `side = 0`, `sj = 0`). -/
theorem wGen_wallNb_lower (a : Fin 48) (i : Fin 3) {j : Fin 3} (hj : j ≠ i) :
    cuspCert.wGen (wallNb a i 0) j = cuspCert.wGen a j := by
  obtain ⟨_, _, _, _, h5, _⟩ := cuspWallTableCerts
  have h := h5 a i 0 j 0
  simp only [hj, ite_false, ite_true] at h
  exact h

/-- The group element of the *lower* wall `(a,i)` is the generator `wGen a i`
(certificate conjunct 1 of `cuspWallTableCerts` at `side = 0`). -/
theorem wGen_eq_wallGamK (a : Fin 48) (i : Fin 3) :
    cuspCert.wGen a i = (wallGamK a i 0, wallGamFlip a i 0) := by
  obtain ⟨h1, _, _, _, _, _⟩ := cuspWallTableCerts
  have h := h1 a i 0
  simp only [ite_true] at h
  exact h.symm

/-- The copy bit of the far cube of a *lower* wall (certificate conjunct 2 of
`cuspWallTableCerts` at `side = 0`). -/
theorem cubeBit_wallNb_lower (a : Fin 48) (i : Fin 3) :
    cubeBit (wallNb a i 0) = cubeBit a + wallGamFlip a i 0 := by
  obtain ⟨_, h2, _, _, _, _⟩ := cuspWallTableCerts
  exact h2 a i 0

-- in namespace Work.RTOwed (file Submission/Work/RTOwed/cuspWalk_lower.lean)
/-- **The lower-wall walk of the cusp chart.**  From a cell `(a,k)` of the cusp development of `v`
whose unfolded cube coordinate `u = uhsXj q - lamV v k` lies in the closed unit cube of `a`, and a
set `S` of *pinned* directions (`u i = cubeCorner a i` for `i ∈ S`), a sequence of crossings of the
*lower* walls of the successive cubes reaches a cell `(a',k')` of the same cusp `v` with the chart
value of `(a,k)` carried to the chart value of `(a',k')` by the group element `S.sum (wGen a)`:

  `cellPt v a' k' q = act ((S.sum (wGen a)).1) (cellPt v a k q)`,  and the copy bits match.

The single step is `Work.RTOwed.cuspWall_step` (`side = 0`) together with the certificate
`(wallGamK a i 0, wallGamFlip a i 0) = cuspCert.wGen a i` and the copy-bit identity
`cubeBit (wallNb a i 0) = cubeBit a + wallGamFlip a i 0` of `Work.RTOwed.cuspWallTableCerts`
(conjuncts 1 and 2); the induction needs `cuspWall_lo_iff` (the tangential pinned directions are
inherited) and the fact that the wall types of the far cube agree with those of the near cube,
`wGen (wallNb a i 0) j = wGen a j` for `j ≠ i` (conjunct 5 of the same certificate, and the finite
check it is proved by), together with `cuspWall_cubeCusp_wallNb`, `cuspWall_mem_box`,
`cuspWall_lamV_add` and `FoldInst.act_add`. -/
theorem cuspWalk_lower (v : Fin 5) (q : CuspE4) (hs : 11 / 10 ≤ q 3) :
    ∀ (S : Finset (Fin 3)) (a : Fin 48) (k : Fin 3 → ℤ),
      Cusp.cubeCusp a = v →
      (uhsXj q - cuspCert.lamV v k) ∈ cubeBox a →
      (∀ i ∈ S, (uhsXj q - cuspCert.lamV v k) i = (Cusp.cubeCorner a i : ℝ)) →
      ∃ (a' : Fin 48) (k' : Fin 3 → ℤ),
        Cusp.cubeCusp a' = v ∧
        (uhsXj q - cuspCert.lamV v k') ∈ cubeBox a' ∧
        cellPt v a' k' q = FoldInst.act ((S.sum (cuspCert.wGen a)).1) (cellPt v a k q) ∧
        cubeBit a' = cubeBit a + (S.sum (cuspCert.wGen a)).2 := by
  intro S
  induction S using Finset.induction with
  | empty =>
      intro a k hca hu hp
      exact ⟨a, k, hca, hu, by simp [FoldInst.act_zero], by simp⟩
  | insert i s hi ih =>
      intro a k hca hu hp
      have hwall : (uhsXj q - cuspCert.lamV v k) i
          = (Cusp.cubeCorner a i : ℝ) + (if (0 : Fin 2) = 0 then 0 else 1) := by
        have h0 := hp i (Finset.mem_insert_self i s)
        rw [h0]; norm_num
      obtain ⟨k', hlam, hcell, hmem, hcusp, hnorm, hhi, hlo, hbd⟩ :=
        cuspWall_step (v := v) (a := a) hca i 0 hs hu hwall
      have hp' : ∀ j ∈ s, (uhsXj q - cuspCert.lamV v k') j
          = (Cusp.cubeCorner (wallNb a i 0) j : ℝ) := by
        intro j hj
        have hji : j ≠ i := fun h => hi (h ▸ hj)
        exact (hlo j hji).mpr (hp j (Finset.mem_insert_of_mem hj))
      obtain ⟨a', k'', hca', hmem', hcell', hbit'⟩ := ih (wallNb a i 0) k' hcusp hmem hp'
      have hgenw : s.sum (cuspCert.wGen (wallNb a i 0)) = s.sum (cuspCert.wGen a) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact wGen_wallNb_lower a i (fun h => hi (h ▸ hj))
      refine ⟨a', k'', hca', hmem', ?_, ?_⟩
      · have key : ((s.sum (cuspCert.wGen (wallNb a i 0))).1 + wallGamK a i 0)
            = (((insert i s).sum (cuspCert.wGen a)).1) := by
          rw [hgenw, Finset.sum_insert hi, wGen_eq_wallGamK]
          simp [add_comm]
        rw [hcell', hcell, FoldInst.act_add, key]
      · rw [hbit', cubeBit_wallNb_lower, hgenw, Finset.sum_insert hi, wGen_eq_wallGamK]
        simp [add_assoc]

end Work.RTOwed
