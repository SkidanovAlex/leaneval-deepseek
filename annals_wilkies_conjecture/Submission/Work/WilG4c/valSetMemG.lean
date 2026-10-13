/-
  `valSetMemG` — a self-contained re-proof of `Work.WilG4c.ValSetMem`.

  The point of this module is that it must NOT import `Submission.Work.WilG4c.ValSetDefs`,
  `...ValSetMem` or `...ValSetEq` (nor anything importing them): those modules declare
  `Work.WilG4c.wIdx` / `Work.WilG4c.vIdx`, and `Submission.Work.WilG4c.EpsSetDefs` declares
  *different* declarations with the same names, so any module whose closure contains both
  fails to build.  Here the index bookkeeping (the `w`-block `wIdxG`, the value coordinate
  `vIdxG`, the `Fin.append` coordinate lemmas) and the set identity (`valSetEqG`) are
  localised, and the `Ω`-bookkeeping of `ValSetMem` is redone on top of them.

  Layout: a point of `ℝ^{p+M+1}` is `Fin.append (Fin.append l w) t` — parameters `l`, then the
  `M` variables `w`, then the value `t`.  The bad locus is
  `famGraph f ∩ coordPre (wIdxG p M) (openCube M) ∩ (coordPre (vIdxG p M) (openCube 1))ᶜ`,
  from which `projN 1` drops the value and `projN M` drops the `w`-block; complementing gives
  the parameter set on which the family is cube-valued in `(0,1)^M`.
-/
import Mathlib
import Submission.Work.WilG5.Basic
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG5.Reindex3

set_option autoImplicit false
noncomputable section

namespace Work.WilG4c

open WilkiesDesign

/-! ## 1. The index maps -/

/-- The `w`-block of a point of `Fin (p+M+1)`: the coordinates `p, …, p+M-1`. -/
def wIdxG (p M : ℕ) : Fin M → Fin (p + M + 1) := fun j => Fin.castAdd 1 (Fin.natAdd p j)

/-- The value coordinate of a point of `Fin (p+M+1)`. -/
def vIdxG (p M : ℕ) : Fin 1 → Fin (p + M + 1) := fun _ => Fin.last (p + M)

/-! ## 2. Coordinates of `Fin.append z t` -/

/-- The first `n` coordinates of `Fin.append z t` form `z`. -/
theorem init_append_oneG {n : ℕ} (z : Fin n → ℝ) (t : Fin 1 → ℝ) :
    Fin.init (Fin.append z t) = z := by
  funext i
  show Fin.append z t (Fin.castSucc i) = z i
  rw [show Fin.castSucc i = Fin.castAdd 1 i from Fin.ext rfl, Fin.append_left]

/-- The last coordinate of `Fin.append z t` is `t 0`. -/
theorem last_append_oneG {n : ℕ} (z : Fin n → ℝ) (t : Fin 1 → ℝ) :
    Fin.append z t (Fin.last n) = t 0 := by
  rw [show Fin.last n = Fin.natAdd n (0 : Fin 1) from Fin.ext rfl, Fin.append_right]

/-- The `w`-block of `Fin.append z t` is the `w`-block of `z`. -/
theorem append_wIdxG {p M : ℕ} (z : Fin (p + M) → ℝ) (t : Fin 1 → ℝ) :
    (fun j : Fin M => Fin.append z t (wIdxG p M j)) = fun j : Fin M => z (Fin.natAdd p j) := by
  funext j
  show Fin.append z t (Fin.castAdd 1 (Fin.natAdd p j)) = z (Fin.natAdd p j)
  rw [Fin.append_left]

/-- The value coordinate of `Fin.append z t` is `t 0`. -/
theorem append_vIdxG {p M : ℕ} (z : Fin (p + M) → ℝ) (t : Fin 1 → ℝ) :
    (fun i : Fin 1 => Fin.append z t (vIdxG p M i)) = fun _ : Fin 1 => t 0 := by
  funext i
  show Fin.append z t (Fin.last (p + M)) = t 0
  rw [last_append_oneG]

/-- The graph equation for a point of the form `Fin.append z t`. -/
theorem mem_famGraph_appendG {p M : ℕ} (f : (Fin p → ℝ) → (Fin M → ℝ) → ℝ)
    (z : Fin (p + M) → ℝ) (t : Fin 1 → ℝ) :
    Fin.append z t ∈ WilkiesDesign.CG.famGraph f ↔
      t 0 = f (fun i : Fin p => z (Fin.castAdd M i)) (fun j : Fin M => z (Fin.natAdd p j)) := by
  simp only [WilkiesDesign.CG.famGraph, WilkiesDesign.graphOf, Set.mem_ofPred_eq,
    init_append_oneG, last_append_oneG]

/-- Membership in the `w`-cube condition, for a point of the form `Fin.append z t`. -/
theorem mem_W_appendG {p M : ℕ} (z : Fin (p + M) → ℝ) (t : Fin 1 → ℝ) :
    Fin.append z t ∈ Work.WilG5.coordPre (wIdxG p M) (WilkiesDesign.openCube M) ↔
      (fun j : Fin M => z (Fin.natAdd p j)) ∈ WilkiesDesign.openCube M := by
  show (fun j : Fin M => Fin.append z t (wIdxG p M j)) ∈ WilkiesDesign.openCube M ↔ _
  rw [append_wIdxG]

/-- Membership in the value condition, for a point of the form `Fin.append z t`. -/
theorem mem_V_appendG {p M : ℕ} (z : Fin (p + M) → ℝ) (t : Fin 1 → ℝ) :
    Fin.append z t ∈ Work.WilG5.coordPre (vIdxG p M) (WilkiesDesign.openCube 1) ↔
      t 0 ∈ Set.Ioo (0 : ℝ) 1 := by
  show (fun i : Fin 1 => Fin.append z t (vIdxG p M i)) ∈ WilkiesDesign.openCube 1 ↔ _
  rw [append_vIdxG]
  simp only [WilkiesDesign.openCube, Set.mem_ofPred_eq]
  constructor
  · intro h; exact h 0
  · intro h i; fin_cases i; exact h

/-! ## 3. The set identity -/

/-- The two descriptions of the parameter set: the complement of the doubly projected bad
locus is exactly the set of `l` for which `f l ·` maps the cube `(0,1)^M` into `(0,1)`. -/
theorem valSetEqG (p M : ℕ) (f : (Fin p → ℝ) → (Fin M → ℝ) → ℝ) :
    (Work.WilG5.projN M (Work.WilG5.projN 1 (WilkiesDesign.CG.famGraph f ∩
        Work.WilG5.coordPre (wIdxG p M) (WilkiesDesign.openCube M) ∩
        (Work.WilG5.coordPre (vIdxG p M) (WilkiesDesign.openCube 1))ᶜ)))ᶜ =
      {l : Fin p → ℝ | ∀ w ∈ WilkiesDesign.openCube M, f l w ∈ Set.Ioo (0 : ℝ) 1} := by
  have hA : ∀ (z : Fin (p + M) → ℝ) (t : Fin 1 → ℝ),
      Fin.append z t ∈ (WilkiesDesign.CG.famGraph f ∩
        Work.WilG5.coordPre (wIdxG p M) (WilkiesDesign.openCube M) ∩
        (Work.WilG5.coordPre (vIdxG p M) (WilkiesDesign.openCube 1))ᶜ) ↔
      (t 0 = f (fun i : Fin p => z (Fin.castAdd M i)) (fun j : Fin M => z (Fin.natAdd p j)) ∧
        (fun j : Fin M => z (Fin.natAdd p j)) ∈ WilkiesDesign.openCube M ∧
        t 0 ∉ Set.Ioo (0 : ℝ) 1) := by
    intro z t
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, mem_famGraph_appendG,
      mem_W_appendG, mem_V_appendG]
    tauto
  ext l
  constructor
  · -- `l` avoids the projected set: every `w` in the cube gives a value in `(0,1)`
    intro hl w hw
    by_contra hc
    exact hl ⟨w, fun _ : Fin 1 => f l w, by
      rw [hA (Fin.append l w) (fun _ : Fin 1 => f l w)]
      simp only [Fin.append_left, Fin.append_right]
      exact ⟨trivial, hw, hc⟩⟩
  · -- conversely, a parameter with values in `(0,1)` on the cube avoids the projected set
    intro h hl
    simp only [Set.mem_ofPred_eq] at h
    rcases hl with ⟨y, t, ht⟩
    rw [hA (Fin.append l y) t] at ht
    simp only [Fin.append_left, Fin.append_right] at ht
    exact (ht.1 ▸ ht.2.2) (h y ht.2.1)

/-! ## 4. The `Ω`-bookkeeping -/

/-- Intersection of two `Ω`-sets at a common format: the format grows by one, the degrees
add. -/
theorem inter2_memG {S : WilkiesDesign.SOMin} {N F Da Db : ℕ} {A B : Set (Fin N → ℝ)}
    (hA : A ∈ S.Ω F Da N) (hB : B ∈ S.Ω F Db N) : A ∩ B ∈ S.Ω (F + 1) (Da + Db) N := by
  have h := S.inter (F := F) (fun i : Fin 2 => if i = 0 then Da else Db)
    (fun i : Fin 2 => if i = 0 then A else B) (by intro i; fin_cases i <;> simp [hA, hB])
  rw [show (∑ i : Fin 2, (if i = 0 then Da else Db)) = Da + Db from by
    simp [Fin.sum_univ_two]] at h
  rw [show (⋂ i : Fin 2, (if i = 0 then A else B)) = A ∩ B from by
    ext z; simp [Fin.forall_fin_two]] at h
  exact h

/-- The set of parameters at which a family is cube-valued in `(0,1)^M` is `Ω`-definable, with
*additive* format and degree depending only on `p, M`. -/
theorem valSetMemG (S : WilkiesDesign.SOMin) (p M : ℕ) :
    ∃ (a c : ℕ), ∀ (F0 D : ℕ) (f : (Fin p → ℝ) → (Fin M → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + M + 1) →
      {l : Fin p → ℝ | ∀ w ∈ WilkiesDesign.openCube M, f l w ∈ Set.Ioo (0 : ℝ) 1} ∈
        S.Ω (F0 + a) (D + c) p := by
  refine ⟨65536 * (p + M + 4) + M + 4,
    ((16 * M + 16) + 32 * ((p + M + 1) + M) + 32) +
      (32 + 32 * ((p + M + 1) + 1) + 32), ?_⟩
  intro F0 D f hf
  -- the bad locus in `ℝ^{p+M+1}`: graph, `w`-cube condition, and the value outside `(0,1)`
  let A : Set (Fin (p + M + 1) → ℝ) := WilkiesDesign.CG.famGraph f ∩
      Work.WilG5.coordPre (wIdxG p M) (WilkiesDesign.openCube M) ∩
      (Work.WilG5.coordPre (vIdxG p M) (WilkiesDesign.openCube 1))ᶜ
  -- the family graph, in the working format
  have hG : WilkiesDesign.CG.famGraph f ∈ S.Ω (F0 + 65536 * (p + M + 4)) D (p + M + 1) :=
    Work.WilG5.mem_mono hf _ _ (by omega) (le_refl D)
  -- the `w`-cube condition
  have hW : Work.WilG5.coordPre (wIdxG p M) (WilkiesDesign.openCube M) ∈
      S.Ω (F0 + 65536 * (p + M + 4)) ((16 * M + 16) + 32 * ((p + M + 1) + M) + 32)
        (p + M + 1) := by
    have h := Work.WilG5.coordPre_mem (S := S) (ι := wIdxG p M) (A := WilkiesDesign.openCube M)
      (Work.WilG5.openCube_mem (S := S) (n := M))
    exact Work.WilG5.mem_mono h _ _ (by omega) (by omega)
  -- the value condition
  have hVc : (Work.WilG5.coordPre (vIdxG p M) (WilkiesDesign.openCube 1))ᶜ ∈
      S.Ω (F0 + 65536 * (p + M + 4)) (32 + 32 * ((p + M + 1) + 1) + 32) (p + M + 1) := by
    have h := Work.WilG5.coordPre_mem (S := S) (ι := vIdxG p M) (A := WilkiesDesign.openCube 1)
      (Work.WilG5.openCube_mem (S := S) (n := 1))
    exact Work.WilG5.mem_mono (S.compl h) _ _ (by omega) (by omega)
  -- assemble the bad locus: two intersections, degrees adding
  have h1 : (WilkiesDesign.CG.famGraph f ∩
      Work.WilG5.coordPre (wIdxG p M) (WilkiesDesign.openCube M)) ∈
      S.Ω (F0 + 65536 * (p + M + 4) + 1)
        (D + ((16 * M + 16) + 32 * ((p + M + 1) + M) + 32)) (p + M + 1) :=
    inter2_memG hG hW
  have hVc' : (Work.WilG5.coordPre (vIdxG p M) (WilkiesDesign.openCube 1))ᶜ ∈
      S.Ω (F0 + 65536 * (p + M + 4) + 1) (32 + 32 * ((p + M + 1) + 1) + 32)
        (p + M + 1) :=
    Work.WilG5.mem_mono hVc _ _ (by omega) (le_refl _)
  have hA : A ∈ S.Ω ((F0 + 65536 * (p + M + 4) + 1) + 1)
      ((D + ((16 * M + 16) + 32 * ((p + M + 1) + M) + 32)) +
        (32 + 32 * ((p + M + 1) + 1) + 32)) (p + M + 1) :=
    inter2_memG (N := p + M + 1) (F := F0 + 65536 * (p + M + 4) + 1)
      (Da := D + ((16 * M + 16) + 32 * ((p + M + 1) + M) + 32))
      (Db := 32 + 32 * ((p + M + 1) + 1) + 32)
      (A := WilkiesDesign.CG.famGraph f ∩
        Work.WilG5.coordPre (wIdxG p M) (WilkiesDesign.openCube M))
      (B := (Work.WilG5.coordPre (vIdxG p M) (WilkiesDesign.openCube 1))ᶜ) h1 hVc'
  -- forget the value coordinate, then the `w`-block, and complement
  have hB := Work.WilG5.projN_mem (S := S) (n := p + M) 1 _ _ hA
  have hC := Work.WilG5.projN_mem (S := S) (n := p) M _ _ hB
  have hD : (Work.WilG5.projN M (Work.WilG5.projN 1 A))ᶜ ∈
      S.Ω (F0 + (65536 * (p + M + 4) + M + 4))
        (D + (((16 * M + 16) + 32 * ((p + M + 1) + M) + 32) +
          (32 + 32 * ((p + M + 1) + 1) + 32))) p :=
    Work.WilG5.mem_mono (S.compl hC) _ _ (by omega) (by omega)
  have hEq : (Work.WilG5.projN M (Work.WilG5.projN 1 A))ᶜ =
      {l : Fin p → ℝ | ∀ w ∈ WilkiesDesign.openCube M, f l w ∈ Set.Ioo (0 : ℝ) 1} :=
    valSetEqG p M f
  rw [hEq] at hD
  exact hD

end Work.WilG4c
