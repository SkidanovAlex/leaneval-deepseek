import Submission.Work.ThomBordism._gtd.P4

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped Topology

namespace Work.ThomBordism.Grassmann

open Work.PTGeometric
open Work.ThomBordism.PontryaginThom Work.ThomBordism.Gauss Work.ThomBordism.OrthFrame

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The `ambEquiv`-reindexing (`ℝ^{8+k} ≅ ℝ^{k+8}`) is the same as `reIdxEuc`, so it has the same
coordinate formula. -/
theorem ambEquiv_ofLp (k : ℕ) (y : EuclideanSpace ℝ (Fin (8 + k))) (j : Fin (k + 8)) :
    ((ambEquiv k) y).ofLp j = y.ofLp ((finCongr (Nat.add_comm 8 k)).symm j) :=
  reIdxEuc_apply_ofLp k y j

/-- **`padEuc` has zero coordinates outside the first `8 + k`.**  Both `padEuc v` and the two-fold
`snoc0`-extension of `v` have norm `‖v‖` and agree on the first `8 + k` coordinates, so the
remaining two coordinates of `padEuc v` are zero. -/
theorem padEuc_ofLp_last_eq_zero (k : ℕ) (v : EuclideanSpace ℝ (Fin (8 + k))) :
    (padEuc k 10 (by norm_num) v).ofLp (Fin.last (k + 9)) = 0 ∧
    (padEuc k 10 (by norm_num) v).ofLp ((Fin.last (k + 8)).castSucc) = 0 := by
  set w := padEuc k 10 (by norm_num) v with hw
  have hnorm : ‖w‖ = ‖v‖ := norm_padEuc k 10 (by norm_num) v
  have hcoord : ∀ j : Fin (8 + k), w.ofLp (Fin.castLE (by omega : 8 + k ≤ k + 10) j) = v.ofLp j :=
    fun j => padEuc_apply_ofLp k 10 (by norm_num) v j
  have hw2 : ‖w‖ ^ 2 = ∑ i : Fin (k + 10), (w.ofLp i) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  have hv2 : ‖v‖ ^ 2 = ∑ i : Fin (8 + k), (v.ofLp i) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  have hsplit : ∑ i : Fin (k + 10), (w.ofLp i) ^ 2
      = (∑ i : Fin (k + 8), (w.ofLp i.castSucc.castSucc) ^ 2)
        + (w.ofLp (Fin.last (k + 8)).castSucc) ^ 2 + (w.ofLp (Fin.last (k + 9))) ^ 2 := by
    rw [Fin.sum_univ_castSucc (fun i : Fin (k + 10) => (w.ofLp i) ^ 2)]
    rw [Fin.sum_univ_castSucc (fun i : Fin (k + 9) => (w.ofLp i.castSucc) ^ 2)]
  have hidx0 : ∀ j : Fin (8 + k), (((finCongr (Nat.add_comm 8 k)) j).castSucc.castSucc : Fin (k + 10))
      = Fin.castLE (by omega : 8 + k ≤ k + 10) j := by
    intro j; ext <;> rfl
  have hre : (∑ i : Fin (k + 8), (w.ofLp i.castSucc.castSucc) ^ 2)
      = ∑ i : Fin (8 + k), (v.ofLp i) ^ 2 := by
    rw [← Equiv.sum_comp (finCongr (Nat.add_comm 8 k))
      (fun i : Fin (k + 8) => (w.ofLp i.castSucc.castSucc) ^ 2)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hidx0 j, hcoord j]
  have hzero : (w.ofLp (Fin.last (k + 8)).castSucc) ^ 2 + (w.ofLp (Fin.last (k + 9))) ^ 2 = 0 := by
    have h := hsplit
    rw [hre, ← hv2, ← hw2, ← hnorm] at h
    linarith
  exact ⟨by nlinarith [hzero, sq_nonneg (w.ofLp (Fin.last (k + 9))),
      sq_nonneg (w.ofLp (Fin.last (k + 8)).castSucc)],
    by nlinarith [hzero, sq_nonneg (w.ofLp (Fin.last (k + 9))),
      sq_nonneg (w.ofLp (Fin.last (k + 8)).castSucc)]⟩

/-- **The padded Gauss frame is the twice-appended ambient frame.**  Both are the `gframe`-vector
placed in the first `8 + k` coordinates of `Amb (k + 10)`: `padGFrame` uses `padEuc`, the
iteration `inclFrame k 9 (inclFrame k 8 ·)` uses `snoc0` twice. -/
theorem padGFrame_inclFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) (a : Fin k) :
    (inclFrame k 9 (inclFrame k 8 (⟨ambGframe E ND i x, orthonormal_ambGframe E ND i hx⟩ :
      Stiefel k 8))).1 a = padGFrame E ND i x a := by
  have hz := padEuc_ofLp_last_eq_zero k (gframe E ND i x a)
  simp only [inclFrame_val, snoc0LI_apply, padGFrame, padIsom_apply]
  apply PiLp.ext
  intro m
  induction m using Fin.lastCases with
  | last =>
      rw [snoc0_ofLp_last]
      exact hz.1.symm
  | cast m =>
      induction m using Fin.lastCases with
      | last =>
          rw [snoc0_ofLp_castSucc, snoc0_ofLp_last]
          exact hz.2.symm
      | cast m' =>
          have hidx : (m'.castSucc.castSucc : Fin (k + 10)) =
              Fin.castLE (by omega : 8 + k ≤ k + 10)
                ((finCongr (Nat.add_comm 8 k)).symm m') := by ext <;> rfl
          rw [snoc0_ofLp_castSucc, snoc0_ofLp_castSucc, hidx, padEuc_apply_ofLp]
          show ((ambEquiv k) (gframe E ND i x a)).ofLp m'
            = (gframe E ND i x a).ofLp ((finCongr (Nat.add_comm 8 k)).symm m')
          exact ambEquiv_ofLp k (gframe E ND i x a) m'

/-- **The padded Gauss map is the iterated inclusion of the plain Gauss map.** -/
theorem padGaussFun_eq_ogIncl (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    padGaussFun E ND
      = fun x => ((ogInclCM k 9).comp ((ogInclCM k 8).comp (Gauss.gauss E ND))) x := by
  funext x
  set i := ND.D.indexAt x with hi
  have hmem : x ∈ ND.D.baseSet i := ND.D.mem_baseSet_at x
  rw [padGaussFun_eq E ND i hmem]
  show ogMk k 10 (⟨padGFrame E ND i x, padGFrame_orthonormal E ND i hmem⟩ : Stiefel k 10) = _
  have hg8 : Gauss.gauss E ND x = ogMk k 8 (gaussStiefel E ND i x) := rfl
  rw [show ((ogInclCM k 9).comp ((ogInclCM k 8).comp (Gauss.gauss E ND))) x
      = ogIncl k 9 (ogIncl k 8 (Gauss.gauss E ND x)) from rfl, hg8]
  rw [gaussStiefel_of_mem E ND i hmem]
  rw [show ogIncl k 8 (ogMk k 8 (⟨ambGframe E ND i x, orthonormal_ambGframe E ND i hmem⟩ :
      Stiefel k 8)) = ogMk k 9 (inclFrame k 8 (⟨ambGframe E ND i x,
        orthonormal_ambGframe E ND i hmem⟩ : Stiefel k 8)) from rfl]
  rw [show ogIncl k 9 (ogMk k 9 (inclFrame k 8 (⟨ambGframe E ND i x,
      orthonormal_ambGframe E ND i hmem⟩ : Stiefel k 8)))
      = ogMk k 10 (inclFrame k 9 (inclFrame k 8 (⟨ambGframe E ND i x,
        orthonormal_ambGframe E ND i hmem⟩ : Stiefel k 8))) from rfl]
  refine Quotient.sound ⟨⟨1, IsSO.one⟩, ?_⟩
  apply Subtype.ext
  funext a
  simp only [SOk.act, soActFun_one]
  exact padGFrame_inclFrame E ND i hmem a

end

end Work.ThomBordism.Grassmann
