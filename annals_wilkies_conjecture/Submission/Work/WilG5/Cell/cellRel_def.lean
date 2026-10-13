/-
  WilG5 — the explicit relation parametrising a cell from its free coordinates.

  `cellRel e κ p ⊆ ℝ^{d+n}`: the free coordinates of a point `x ∈ κ` are `x ∘ e`, and the
  relation contains `(x ∘ e, x)` for each `x ∈ κ`; the points `u` of the open cube that are not
  free coordinates of any point of `κ` are filled in with the fixed point `p ∈ κ`.  This is
  exactly the relation appearing in `Work.WilG5.Cell.cell_par`: it is built directly from `κ`
  and `e` (no convex combinations) and its `Ω`-degree is `2D + const`.
-/
import Mathlib
import Submission.Work.WilG5.Defs

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG5.Cell

open WilkiesDesign WilkiesConjecture

variable {S : SOMin}

/-! ## 1. The relation -/

/-- The parametrising relation: free points are `x ∘ e`; the complement of `coordImage e κ`
inside the open cube is filled with the constant point `p`. -/
def cellRel {n d : ℕ} (e : Fin d → Fin n) (κ : Set (Fin n → ℝ)) (p : Fin n → ℝ) :
    Set (Fin (d + n) → ℝ) :=
  (Work.WilG5.coordPre (Fin.natAdd d) κ ∩
      Work.WilG5.funeqSet (fun i : Fin d => Fin.natAdd d (e i)) (Fin.castAdd n))
    ∪ (Work.WilG5.coordPre (Fin.castAdd n) (openCube d) ∩
        Work.WilG5.coordPre (Fin.castAdd n) ((Work.WilG5.coordImage e κ)ᶜ) ∩
        Work.WilG5.coordPre (Fin.natAdd d) ({p} : Set (Fin n → ℝ)))

/-! ## 2. Membership of a point of `ℝ^{d+n}` written as `Fin.append u x` -/

theorem append_coordPre_natAdd {n d : ℕ} (u : Fin d → ℝ) (x : Fin n → ℝ)
    {A : Set (Fin n → ℝ)} :
    Fin.append u x ∈ Work.WilG5.coordPre (Fin.natAdd d) A ↔ x ∈ A := by
  show (Fin.append u x) ∘ (Fin.natAdd d) ∈ A ↔ x ∈ A
  rw [show (Fin.append u x) ∘ (Fin.natAdd d) = x from by
    funext j; rw [Function.comp_apply, Fin.append_right]]

theorem append_coordPre_castAdd {n d : ℕ} (u : Fin d → ℝ) (x : Fin n → ℝ)
    {B : Set (Fin d → ℝ)} :
    Fin.append u x ∈ Work.WilG5.coordPre (Fin.castAdd n) B ↔ u ∈ B := by
  show (Fin.append u x) ∘ (Fin.castAdd n) ∈ B ↔ u ∈ B
  rw [show (Fin.append u x) ∘ (Fin.castAdd n) = u from by
    funext j; rw [Function.comp_apply, Fin.append_left]]

theorem append_funeqSet {n d : ℕ} (e : Fin d → Fin n) (u : Fin d → ℝ) (x : Fin n → ℝ) :
    Fin.append u x ∈ Work.WilG5.funeqSet (fun i : Fin d => Fin.natAdd d (e i)) (Fin.castAdd n) ↔
      x ∘ e = u := by
  simp only [Work.WilG5.funeqSet, Set.mem_ofPred_eq]
  constructor
  · intro h
    funext i
    have := h i
    rwa [Fin.append_right, Fin.append_left] at this
  · intro h i
    rw [Fin.append_right, Fin.append_left]
    exact congrFun h i

/-- Membership in `cellRel` in the coordinates `(u, x) = (first d, last n)`. -/
theorem cellRel_mem_iff {n d : ℕ} (e : Fin d → Fin n) (κ : Set (Fin n → ℝ)) (p : Fin n → ℝ)
    (u : Fin d → ℝ) (x : Fin n → ℝ) :
    (Fin.append u x ∈ cellRel e κ p) ↔
      ((x ∈ κ ∧ x ∘ e = u) ∨
        (u ∈ openCube d ∧ u ∉ Work.WilG5.coordImage e κ ∧ x = p)) := by
  simp only [cellRel, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
    append_coordPre_natAdd, append_coordPre_castAdd, append_funeqSet]
  tauto

/-! ## 3. Combining `Ω`-sets at a common format -/

theorem inter2_mem' {N F Da Db : ℕ} {A B : Set (Fin N → ℝ)}
    (hA : A ∈ S.Ω F Da N) (hB : B ∈ S.Ω F Db N) : A ∩ B ∈ S.Ω (F + 1) (Da + Db) N := by
  have h := S.inter (F := F) (fun i : Fin 2 => if i = 0 then Da else Db)
      (fun i : Fin 2 => if i = 0 then A else B)
      (by intro i; fin_cases i <;> simp [hA, hB])
  rw [show (∑ i : Fin 2, (if i = 0 then Da else Db)) = Da + Db from by
    simp [Fin.sum_univ_two]] at h
  rw [show (⋂ i : Fin 2, (if i = 0 then A else B)) = A ∩ B from by
    ext z; simp [Fin.forall_fin_two]] at h
  exact h

theorem union2_mem' {N F Da Db : ℕ} {A B : Set (Fin N → ℝ)}
    (hA : A ∈ S.Ω F Da N) (hB : B ∈ S.Ω F Db N) : A ∪ B ∈ S.Ω F (Da + Db) N := by
  have h := S.union (F := F) (fun i : Fin 2 => if i = 0 then Da else Db)
      (fun i : Fin 2 => if i = 0 then A else B)
      (by intro i; fin_cases i <;> simp [hA, hB])
  rw [show (∑ i : Fin 2, (if i = 0 then Da else Db)) = Da + Db from by
    simp [Fin.sum_univ_two]] at h
  rw [show (⋃ i : Fin 2, (if i = 0 then A else B)) = A ∪ B from by
    ext z; simp [Fin.exists_fin_two]] at h
  exact h

theorem mem_monoF' {F D N : ℕ} {X : Set (Fin N → ℝ)} (h : X ∈ S.Ω F D N) {F' : ℕ}
    (hF : F ≤ F') : X ∈ S.Ω F' D N := Work.WilG5.mem_mono h F' D hF (le_refl _)

/-! ## 4. `Ω`-membership of `cellRel` -/

/-- `cellRel` is `Ω`-definable; its degree is linear in `D` (with coefficient `2`) and its format
grows linearly in the ambient data. -/
theorem cellRel_mem {n d : ℕ} (F D : ℕ) {κ : Set (Fin n → ℝ)}
    (hΩ : κ ∈ S.Ω F D n) (e : Fin d → Fin n) (p : Fin n → ℝ) :
    cellRel e κ p ∈ S.Ω (F + (1000 * (d + n) + 1100)) (2 * D + (1000 * (d + n) + 1100))
      (d + n) := by
  have h1 : Work.WilG5.coordPre (Fin.natAdd d) κ ∈
      S.Ω (F + 64 * ((d + n) + n) + 64) (D + 32 * ((d + n) + n) + 32) (d + n) :=
    Work.WilG5.coordPre_mem (S := S) hΩ
  have h2 : Work.WilG5.funeqSet (fun i : Fin d => Fin.natAdd d (e i)) (Fin.castAdd n) ∈
      S.Ω (4 * ((d + n) + (d + n)) + 8) (2 * d + 4) (d + n) :=
    Work.WilG5.funeqSet_mem (S := S) (fun i : Fin d => Fin.natAdd d (e i)) (Fin.castAdd n)
  have hp1 : Work.WilG5.coordPre (Fin.castAdd n) (openCube d) ∈
      S.Ω ((4 * d + 24) + 64 * ((d + n) + d) + 64) ((16 * d + 16) + 32 * ((d + n) + d) + 32)
        (d + n) :=
    Work.WilG5.coordPre_mem (S := S) (N := d + n) (openCube_mem (S := S))
  have hci : Work.WilG5.coordImage e κ ∈
      S.Ω (F + 64 * (n + d) + 64) (D + 32 * (n + d) + 32) d :=
    Work.WilG5.coordImage_mem (S := S) hΩ
  have hp2 : Work.WilG5.coordPre (Fin.castAdd n) ((Work.WilG5.coordImage e κ)ᶜ) ∈
      S.Ω ((F + 64 * (n + d) + 65) + 64 * ((d + n) + d) + 64)
        ((D + 32 * (n + d) + 32) + 32 * ((d + n) + d) + 32) (d + n) :=
    Work.WilG5.coordPre_mem (S := S) (N := d + n) (S.compl hci)
  have hp3 : Work.WilG5.coordPre (Fin.natAdd d) ({p} : Set (Fin n → ℝ)) ∈
      S.Ω ((4 * n + 20) + 64 * ((d + n) + n) + 64) ((4 * n + 4) + 32 * ((d + n) + n) + 32)
        (d + n) :=
    Work.WilG5.coordPre_mem (S := S) (N := d + n) (singleton_mem (S := S) p)
  have h1' := mem_monoF' h1 (F' := F + 500 * (d + n) + 500) (by omega)
  have h2' := mem_monoF' h2 (F' := F + 500 * (d + n) + 500) (by omega)
  have hp1' := mem_monoF' hp1 (F' := F + 500 * (d + n) + 500) (by omega)
  have hp2' := mem_monoF' hp2 (F' := F + 500 * (d + n) + 500) (by omega)
  have hp3' := mem_monoF' hp3 (F' := F + 500 * (d + n) + 500) (by omega)
  have hP1 := inter2_mem' h1' h2'
  have hP2a := inter2_mem' hp1' hp2'
  have hP2a' := mem_monoF' hP2a (F' := F + 500 * (d + n) + 501) (by omega)
  have hp3'' := mem_monoF' hp3' (F' := F + 500 * (d + n) + 501) (by omega)
  have hP2 := inter2_mem' hP2a' hp3''
  have hP1'' := mem_monoF' hP1 (F' := F + 500 * (d + n) + 502) (by omega)
  have hP2' := mem_monoF' hP2 (F' := F + 500 * (d + n) + 502) (by omega)
  have hR := union2_mem' hP1'' hP2'
  rw [cellRel]
  exact Work.WilG5.mem_mono hR _ _ (by omega) (by omega)

end Work.WilG5.Cell
