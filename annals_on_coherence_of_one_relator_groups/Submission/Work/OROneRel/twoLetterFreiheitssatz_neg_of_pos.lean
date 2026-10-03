import Mathlib
import Submission.Work.OROneRel.twoLetterReflect
import Submission.Work.OROneRel.decor_neg
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.twoLetterWindow_neg
import Submission.Work.OROneRel.reflectData
import Submission.Work.OROneRel.winE_transfer
import Submission.Work.OROneRel.hone_transfer
import Submission.Work.OROneRel.winTree_transfer
import Submission.Work.OROneRel.winRootList_neg

namespace Work.OROneRel

/-- **The candidate root reflects.**  The deleted walk word `winRoot` of the weight `-c` is the
reflection (`winUnreflectHom`, i.e. the isomorphism of free groups induced by
`(x, i) ↦ (x, -i)`) of the deleted walk word of the weight `c` with the reflected gauge
`j ↦ Wt (-j)` and the reflected window `[-hi, -lo]`. -/
theorem winRoot_neg {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (u : FreeGroup α) :
    winRoot Wt (fun a => -c a) lo hi u
      = winUnreflectHom Wt c lo hi (winRoot (fun j => Wt (-j)) c (-hi) (-lo) u) := by
  rw [winRoot, winRoot, winUnreflectHom_mk, winRootList_neg]

/-- **The reflection reduction of the two-letter Freiheitssatz.**  If the two-letter Freiheitssatz holds for the weight `tlW p q` for every gauge and every window satisfying the hypotheses, then it holds for the weight `-tlW p q` for every gauge and window satisfying the corresponding hypotheses.  The reduction is via the level graph isomorphism `(x, i) ↦ (x, -i)`: it carries the walk of `u` to the walk of `u` (`decor_neg`), loop classes to loop classes (`coverClassAt_reflect`), the window `[lo,hi]` to `[-hi,-lo]` (`mem_winE_reflect`), and hence `winBeta`, `winTree`, `winRho` and `winRoot` of the data with weight `-tlW p q` to those of the reflected data with weight `tlW p q`. -/
theorem twoLetterFreiheitssatz_neg_of_pos (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l)
    (hpos : ∀ {Wt : ℤ → FreeGroup (Fin 2)} {lo hi : ℤ},
      Wt 0 = 1 →
      (∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i) →
      Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Work.OROneRel.tlU p q) = 1 →
      (∃ τ : FreeGroup (Fin 2),
        Work.OROneRel.cohom (Work.OROneRel.tlW p q) τ = Multiplicative.ofAdd 1) →
      (∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) lo hi) →
      (∀ k : ℤ, k ≠ 0 → ¬ (∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
          (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
          lo ≤ e.1.2 + k ∧ lo ≤ e.1.2 + Work.OROneRel.tlW p q e.1.1 + k ∧ e.1.2 + k ≤ hi ∧
            e.1.2 + Work.OROneRel.tlW p q e.1.1 + k ≤ hi)) →
      (∀ i : ℤ, lo ≤ i → i ≤ hi → ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
          (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) lo hi) →
      ∀ x : FreeGroup (Work.OROneRel.winBeta Wt (Work.OROneRel.tlW p q) lo hi),
        Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) lo hi x ∈
            Subgroup.normalClosure ({Work.OROneRel.tlU p q ^ l} : Set (FreeGroup (Fin 2))) →
          x ∈ Subgroup.normalClosure
            ({Work.OROneRel.winRoot Wt (Work.OROneRel.tlW p q) lo hi (Work.OROneRel.tlU p q) ^ l} :
              Set (FreeGroup (Work.OROneRel.winBeta Wt (Work.OROneRel.tlW p q) lo hi))))
    {Wt : ℤ → FreeGroup (Fin 2)} {lo hi : ℤ}
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ,
      Work.OROneRel.cohom (fun a => -Work.OROneRel.tlW p q a) (Wt i) = Multiplicative.ofAdd i)
    (hcu : Work.OROneRel.cohom (fun a => -Work.OROneRel.tlW p q a) (Work.OROneRel.tlU p q) = 1)
    (hτ : ∃ τ : FreeGroup (Fin 2),
      Work.OROneRel.cohom (fun a => -Work.OROneRel.tlW p q a) τ = Multiplicative.ofAdd 1)
    (hwin : ∀ e ∈ Work.OROneRel.decor (fun a => -Work.OROneRel.tlW p q a) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈
        Work.OROneRel.winE (fun a => -Work.OROneRel.tlW p q a) lo hi)
    (hone : ∀ k : ℤ, k ≠ 0 → ¬ (∀ e ∈ Work.OROneRel.decor
          (fun a => -Work.OROneRel.tlW p q a) 0 (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
        lo ≤ e.1.2 + k ∧ lo ≤ e.1.2 + (fun a => -Work.OROneRel.tlW p q a) e.1.1 + k ∧
          e.1.2 + k ≤ hi ∧ e.1.2 + (fun a => -Work.OROneRel.tlW p q a) e.1.1 + k ≤ hi))
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi → ∀ e ∈ Work.OROneRel.decor
        (fun a => -Work.OROneRel.tlW p q a) 0 (Work.OROneRel.wordOf (Wt i)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt (fun a => -Work.OROneRel.tlW p q a) lo hi) :
    ∀ x : FreeGroup (Work.OROneRel.winBeta Wt (fun a => -Work.OROneRel.tlW p q a) lo hi),
      Work.OROneRel.winRho Wt (fun a => -Work.OROneRel.tlW p q a) lo hi x ∈
          Subgroup.normalClosure ({Work.OROneRel.tlU p q ^ l} : Set (FreeGroup (Fin 2))) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt (fun a => -Work.OROneRel.tlW p q a) lo hi
              (Work.OROneRel.tlU p q) ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt (fun a => -Work.OROneRel.tlW p q a) lo hi))) := by
  intro x hx
  -- ### The reflected gauge and the reflected window
  -- Every hypothesis is transferred to the gauge `j ↦ Wt (-j)` and the window `[-hi, -lo]`.
  have hW0' : (fun j : ℤ => Wt (-j)) 0 = 1 := by simpa using hW0
  -- The gauge condition: `cohom (-c) (Wt i) = ofAdd i` says `cohom c (Wt i) = ofAdd (-i)`, i.e.
  -- `cohom c (Wt (-j)) = ofAdd j`.
  have hcoh' : ∀ i : ℤ, cohom (tlW p q) ((fun j : ℤ => Wt (-j)) i) = Multiplicative.ofAdd i := by
    intro i
    have h := hcoh (-i)
    rw [cohom_neg] at h
    have h2 := congrArg (fun z : Multiplicative ℤ => z⁻¹) h
    simp only [inv_inv] at h2
    rw [h2, ← ofAdd_neg, neg_neg]
  have hcu' : cohom (tlW p q) (tlU p q) = 1 := by
    have h := hcu
    rw [cohom_neg] at h
    have h2 := congrArg (fun z : Multiplicative ℤ => z⁻¹) h
    simpa using h2
  have hτ' : ∃ τ : FreeGroup (Fin 2), cohom (tlW p q) τ = Multiplicative.ofAdd 1 := by
    obtain ⟨τ, hττ⟩ := hτ
    refine ⟨τ⁻¹, ?_⟩
    have h := hττ
    rw [cohom_neg] at h
    rw [map_inv, h]
  have hwin' : ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlW p q) (-hi) (-lo) :=
    winE_transfer (tlW p q) lo hi (tlU p q) hwin
  have hone' : ∀ k : ℤ, k ≠ 0 → ¬ (∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      (-hi) ≤ e.1.2 + k ∧ (-hi) ≤ e.1.2 + tlW p q e.1.1 + k ∧ e.1.2 + k ≤ (-lo) ∧
        e.1.2 + tlW p q e.1.1 + k ≤ (-lo)) :=
    hone_transfer (tlW p q) lo hi (tlU p q) hone
  have htree' : ∀ i : ℤ, (-hi) ≤ i → i ≤ (-lo) →
      ∀ e ∈ decor (tlW p q) 0 (wordOf ((fun j : ℤ => Wt (-j)) i)),
        coverEdge e ∈ winTree (fun j : ℤ => Wt (-j)) (tlW p q) (-hi) (-lo) :=
    fun i hi1 hi2 => winTree_transfer Wt (tlW p q) lo hi htree i hi1 hi2
  -- ### The Freiheitssatz for the reflected data
  have key := hpos (Wt := fun j : ℤ => Wt (-j)) (lo := -hi) (hi := -lo)
    hW0' hcoh' hcu' hτ' hwin' hone' htree'
  -- The class map of the reflected data is the class map of the target data along `winReflectHom`.
  have hx' : winRho (fun j : ℤ => Wt (-j)) (tlW p q) (-hi) (-lo)
      (winReflectHom Wt (tlW p q) lo hi x) ∈
      Subgroup.normalClosure ({tlU p q ^ l} : Set (FreeGroup (Fin 2))) := by
    rw [winRho_winReflectHom]
    exact hx
  have hy := key (winReflectHom Wt (tlW p q) lo hi x) hx'
  -- The candidate root of the reflected data is the image of the candidate root of the target data.
  have hroot : winReflectHom Wt (tlW p q) lo hi
        (winRoot Wt (fun a => -tlW p q a) lo hi (tlU p q)) =
      winRoot (fun j : ℤ => Wt (-j)) (tlW p q) (-hi) (-lo) (tlU p q) := by
    rw [winRoot_neg (Wt := Wt) (c := tlW p q) (lo := lo) (hi := hi) (u := tlU p q)]
    exact winReflect_winUnreflect Wt (tlW p q) lo hi _
  have hy' : winReflectHom Wt (tlW p q) lo hi x ∈
      Subgroup.normalClosure
        ((singleton (winReflectHom Wt (tlW p q) lo hi
          (winRoot Wt (fun a => -tlW p q a) lo hi (tlU p q)) ^ l)) :
          Set (FreeGroup (winBeta (fun j : ℤ => Wt (-j)) (tlW p q) (-hi) (-lo)))) := by
    rw [hroot]
    exact hy
  -- ### Transporting the conclusion back along the reflection
  -- `winReflectHom` is surjective, so the normal closure of the reflected root is the image of the
  -- normal closure of the root.
  have hsurj : Function.Surjective (winReflectHom Wt (tlW p q) lo hi) := fun y =>
    ⟨winUnreflectHom Wt (tlW p q) lo hi y, winReflect_winUnreflect Wt (tlW p q) lo hi y⟩
  have hmem : winReflectHom Wt (tlW p q) lo hi x ∈
      (Subgroup.normalClosure
        ({winRoot Wt (fun a => -tlW p q a) lo hi (tlU p q) ^ l} :
          Set (FreeGroup (winBeta Wt (fun a => -tlW p q a) lo hi)))).map
          (winReflectHom Wt (tlW p q) lo hi) := by
    rw [Subgroup.map_normalClosure _ _ hsurj, Set.image_singleton, map_pow]
    exact hy'
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hmem
  have hzx' : z = x := by
    have h := congrArg (winUnreflectHom Wt (tlW p q) lo hi) hzx
    simpa only [winUnreflect_winReflect] using h
  rw [hzx'] at hz
  exact hz

end Work.OROneRel
