/-
  WilG5.Interior — the "single-valuedisation" of a cell parametrisation, and the explicit
  padding bound.

  The cell parametrisation produced by `Work.WilG5.Cell.cell_par` is a relation
  `R ⊆ ℝ^{d+n}` which is single valued and total only over the *open* cube `openCube d`; this is
  all that `CellPar` records.  The F-lemma (`WilkiesDesign.CG.FLem`), on the other hand, needs a
  *function* whose graph is `Ω`-definable, and `Work.WilG5.RelSel` is definable only when its
  relation is single valued over the *whole* parameter space.

  `svRel R` repairs this: it keeps `R` over the open cube and replaces the (unconstrained)
  outside of the open cube by the constant `0`.  Thus

  * `svRel R` is single valued everywhere (given `R` is single valued on the open cube), and
  * `RelSel (svRel R) u = RelSel R u` for `u` in the open cube,

  while `svRel R` remains `Ω`-definable with controlled format and degree
  (`svRel_mem`).  Together with `padRel_mem_explicit` (the padding lemma with explicit
  constants, needed because the cell dimension `d` varies with the cell and the final counting
  polynomial must not) this is the technical input of `Work.WilG5.Interior.cell_charts`.
-/
import Mathlib
import Submission.Work.WilG5.Defs
import Submission.Work.WilG5.Rel.padRel_mem

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG5.Interior

/-! ## 1. A globally single valued version of a relation -/

/-- `svRel R` agrees with `R` over the open cube of the parameter and is constantly `0` outside
of it.  Hence it is single valued as soon as `R` is single valued on the open cube. -/
def svRel {d n : ℕ} (R : Set (Fin (d + n) → ℝ)) : Set (Fin (d + n) → ℝ) :=
  (Work.WilG5.coordPre (Fin.castAdd n) (WilkiesDesign.openCube d) ∩ R) ∪
    ((Work.WilG5.coordPre (Fin.castAdd n) (WilkiesDesign.openCube d))ᶜ ∩
      {z : Fin (d + n) → ℝ | (fun j : Fin n => z (Fin.natAdd d j)) = 0})

theorem mem_zeroTail {d n : ℕ} (u : Fin d → ℝ) (x : Fin n → ℝ) :
    Fin.append u x ∈ {z : Fin (d + n) → ℝ | (fun j : Fin n => z (Fin.natAdd d j)) = 0} ↔
      x = 0 := by
  rw [Set.mem_ofPred_eq]
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    simpa [Fin.append_right] using hj
  · intro h
    funext j
    rw [h, Fin.append_right]

theorem mem_castAdd {d n : ℕ} (u : Fin d → ℝ) (x : Fin n → ℝ) {B : Set (Fin d → ℝ)} :
    Fin.append u x ∈ Work.WilG5.coordPre (Fin.castAdd n) B ↔ u ∈ B := by
  show (Fin.append u x) ∘ (Fin.castAdd n) ∈ B ↔ u ∈ B
  rw [show (Fin.append u x) ∘ (Fin.castAdd n) = u from by
    funext i; rw [Function.comp_apply, Fin.append_left]]

/-- Membership of an appended point in `svRel R`. -/
theorem svRel_iff {d n : ℕ} (R : Set (Fin (d + n) → ℝ)) (u : Fin d → ℝ) (x : Fin n → ℝ) :
    Fin.append u x ∈ svRel R ↔
      (u ∈ WilkiesDesign.openCube d ∧ Fin.append u x ∈ R) ∨
        (u ∉ WilkiesDesign.openCube d ∧ x = 0) := by
  unfold svRel
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
  rw [mem_castAdd, mem_zeroTail]

/-- `svRel R` is single valued wherever `R` is single valued on the open cube. -/
theorem svRel_single {d n : ℕ} {R : Set (Fin (d + n) → ℝ)}
    (huniq : ∀ u ∈ WilkiesDesign.openCube d, ∀ x y : Fin n → ℝ,
      Fin.append u x ∈ R → Fin.append u y ∈ R → x = y) :
    ∀ u : Fin d → ℝ, (∃ x : Fin n → ℝ, Fin.append u x ∈ svRel R) →
      ∀ x y : Fin n → ℝ, Fin.append u x ∈ svRel R → Fin.append u y ∈ svRel R → x = y := by
  intro u _ x y hx hy
  rw [svRel_iff] at hx hy
  rcases hx with ⟨hxu, hxR⟩ | ⟨hxu, hx0⟩
  · rcases hy with ⟨hyu, hyR⟩ | ⟨hyu, _⟩
    · exact huniq u hxu x y hxR hyR
    · exact absurd hxu hyu
  · rcases hy with ⟨hyu, hyR⟩ | ⟨hyu, hy0⟩
    · exact absurd hyu hxu
    · rw [hx0, hy0]

/-- On the open cube, the function selected by `svRel R` is the one selected by `R`. -/
theorem svRel_RelSel {d n : ℕ} {R : Set (Fin (d + n) → ℝ)}
    (hne : ∀ u ∈ WilkiesDesign.openCube d, ∃ x : Fin n → ℝ, Fin.append u x ∈ R)
    (huniq : ∀ u ∈ WilkiesDesign.openCube d, ∀ x y : Fin n → ℝ,
      Fin.append u x ∈ R → Fin.append u y ∈ R → x = y)
    {u : Fin d → ℝ} (hu : u ∈ WilkiesDesign.openCube d) :
    Work.WilG5.RelSel (svRel R) u = Work.WilG5.RelSel R u := by
  refine Work.WilG5.RelSel_eq ?_ ?_
  · rw [svRel_iff]; exact Or.inl ⟨hu, Work.WilG5.RelSel_spec (hne u hu)⟩
  · intro y hy
    rw [svRel_iff] at hy
    rcases hy with ⟨hyu, hyR⟩ | ⟨hyu, _⟩
    · exact huniq u hu y (Work.WilG5.RelSel R u) hyR (Work.WilG5.RelSel_spec (hne u hu))
    · exact absurd hu hyu

/-! ## 2. Two-set unions and intersections at a common format -/

theorem inter2_mem {S : WilkiesDesign.SOMin} {N F Da Db : ℕ} {A B : Set (Fin N → ℝ)}
    (hA : A ∈ S.Ω F Da N) (hB : B ∈ S.Ω F Db N) : A ∩ B ∈ S.Ω (F + 1) (Da + Db) N := by
  have h := S.inter (F := F) (fun i : Fin 2 => if i = 0 then Da else Db)
      (fun i : Fin 2 => if i = 0 then A else B) (by intro i; fin_cases i <;> simp [hA, hB])
  rw [show (∑ i : Fin 2, (if i = 0 then Da else Db)) = Da + Db from by
    simp [Fin.sum_univ_two]] at h
  rw [show (⋂ i : Fin 2, (if i = 0 then A else B)) = A ∩ B from by
    ext z; simp [Fin.forall_fin_two]] at h
  exact h

theorem union2_mem {S : WilkiesDesign.SOMin} {N F Da Db : ℕ} {A B : Set (Fin N → ℝ)}
    (hA : A ∈ S.Ω F Da N) (hB : B ∈ S.Ω F Db N) : A ∪ B ∈ S.Ω F (Da + Db) N := by
  have h := S.union (F := F) (fun i : Fin 2 => if i = 0 then Da else Db)
      (fun i : Fin 2 => if i = 0 then A else B) (by intro i; fin_cases i <;> simp [hA, hB])
  rw [show (∑ i : Fin 2, (if i = 0 then Da else Db)) = Da + Db from by
    simp [Fin.sum_univ_two]] at h
  rw [show (⋃ i : Fin 2, (if i = 0 then A else B)) = A ∪ B from by
    ext z; simp [Fin.exists_fin_two]] at h
  exact h

/-! ## 3. `Ω`-membership of `svRel` -/

theorem svRel_mem {S : WilkiesDesign.SOMin} {d n : ℕ} :
    ∃ A L : ℕ, ∀ (A₀ B : ℕ) (R : Set (Fin (d + n) → ℝ)), R ∈ S.Ω A₀ B (d + n) →
      svRel R ∈ S.Ω (A + A₀) (B + L) (d + n) := by
  refine ⟨((4 * d + 24) + 64 * ((d + n) + d) + 64) + d + n + 5,
          2 * ((16 * d + 16) + 32 * ((d + n) + d) + 32) + (2 * n + 4), ?_⟩
  intro A₀ B R hR
  have hO : Work.WilG5.coordPre (Fin.castAdd n) (WilkiesDesign.openCube d) ∈
      S.Ω ((4 * d + 24) + 64 * ((d + n) + d) + 64)
        ((16 * d + 16) + 32 * ((d + n) + d) + 32) (d + n) :=
    Work.WilG5.coordPre_mem (S := S) (Work.WilG5.openCube_mem (S := S))
  have hOc : (Work.WilG5.coordPre (Fin.castAdd n) (WilkiesDesign.openCube d))ᶜ ∈
      S.Ω (((4 * d + 24) + 64 * ((d + n) + d) + 64) + 1)
        ((16 * d + 16) + 32 * ((d + n) + d) + 32) (d + n) := S.compl hO
  have hZ : {z : Fin (d + n) → ℝ | (fun j : Fin n => z (Fin.natAdd d j)) = 0} ∈
      S.Ω (d + n + 1) (2 * n + 4) (d + n) := Work.WilG5.zeroTail_mem
  have hO1 := Work.WilG5.mem_mono hO
    (((4 * d + 24) + 64 * ((d + n) + d) + 64) + A₀ + d + n + 3)
    ((16 * d + 16) + 32 * ((d + n) + d) + 32) (by omega) (le_refl _)
  have hR1 := Work.WilG5.mem_mono hR
    (((4 * d + 24) + 64 * ((d + n) + d) + 64) + A₀ + d + n + 3) B (by omega) (le_refl _)
  have hP1 := inter2_mem hO1 hR1
  have hOc1 := Work.WilG5.mem_mono hOc
    (((4 * d + 24) + 64 * ((d + n) + d) + 64) + A₀ + d + n + 3 + 1)
    ((16 * d + 16) + 32 * ((d + n) + d) + 32) (by omega) (le_refl _)
  have hZ1 := Work.WilG5.mem_mono hZ
    (((4 * d + 24) + 64 * ((d + n) + d) + 64) + A₀ + d + n + 3 + 1)
    (2 * n + 4) (by omega) (le_refl _)
  have hP2 := inter2_mem hOc1 hZ1
  have hP1' := Work.WilG5.mem_mono hP1
    (((4 * d + 24) + 64 * ((d + n) + d) + 64) + A₀ + d + n + 3 + 2)
    ((16 * d + 16) + 32 * ((d + n) + d) + 32 + B) (by omega) (le_refl _)
  have hP2' := Work.WilG5.mem_mono hP2
    (((4 * d + 24) + 64 * ((d + n) + d) + 64) + A₀ + d + n + 3 + 2)
    ((16 * d + 16) + 32 * ((d + n) + d) + 32 + (2 * n + 4)) (by omega) (le_refl _)
  have hU := union2_mem hP1' hP2'
  unfold svRel
  exact Work.WilG5.mem_mono hU _ _ (by omega) (by omega)

/-! ## 4. Padding with explicit constants -/

theorem padRel_mem_explicit {S : WilkiesDesign.SOMin} {d n μ : ℕ} (h : d ≤ μ) (A₀ B : ℕ)
    (R : Set (Fin (d + n) → ℝ)) (hR : R ∈ S.Ω A₀ B (d + n)) :
    Work.WilG5.padRel h R ∈ S.Ω (64 * ((μ + n) + (d + n)) + 64 + A₀)
      (B + (32 * ((μ + n) + (d + n)) + 32)) (μ + n) := by
  have hcoord := Work.WilG5.coordPre_mem (S := S) (ι := Work.WilG5.Rel.padRelIdx h) (A := R) hR
  rw [Work.WilG5.Rel.padRel_eq_coordPre h R]
  exact Work.WilG5.mem_mono hcoord _ _ (by omega) (by omega)

end Work.WilG5.Interior
