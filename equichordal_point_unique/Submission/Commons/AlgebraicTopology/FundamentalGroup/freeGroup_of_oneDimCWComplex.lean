import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Homotopy.Lifting
import Submission.Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv

set_option autoImplicit true

set_option maxHeartbeats 1000000

open Set Function
open scoped Topology

namespace Commons.AlgebraicTopology.FundamentalGroup

namespace CWGraph

noncomputable section

variable {Y : Type*} [TopologicalSpace Y] {C : Set Y} [Topology.CWComplex C]

def vpt (v : Topology.CWComplex.cell C 0) : Y := Topology.RelCWComplex.map (C := C) 0 v ![]

lemma vpt_injective : Function.Injective (vpt (C := C)) :=
  Topology.RelCWComplex.injective_map_zero C

@[simp] lemma vpt_inj {v w : Topology.CWComplex.cell C 0} : vpt (C := C) v = vpt w ↔ v = w :=
  ⟨fun h => vpt_injective h, fun h => h ▸ rfl⟩

lemma exists_map_one_one_eq (e : Topology.CWComplex.cell C 1) :
    ∃ x : Topology.CWComplex.cell C 0,
      Topology.RelCWComplex.map (C := C) 1 e (1 : Fin 1 → ℝ) = vpt x := by
  obtain ⟨x, y, hxy⟩ := Topology.CWComplex.exists_cellFrontier_one_eq e
  have h1 : (Topology.RelCWComplex.map (C := C) 1 e) (1 : Fin 1 → ℝ) ∈
      Topology.RelCWComplex.closedCell 0 x ∪ Topology.RelCWComplex.closedCell 0 y := by
    rw [← hxy]
    exact mem_image_of_mem _ (by simp)
  rw [Topology.RelCWComplex.closedCell_zero_eq_singleton,
      Topology.RelCWComplex.closedCell_zero_eq_singleton] at h1
  simp only [mem_union, mem_singleton_iff] at h1
  rcases h1 with h | h
  · exact ⟨x, h⟩
  · exact ⟨y, h⟩

lemma exists_map_one_neg_one_eq (e : Topology.CWComplex.cell C 1) :
    ∃ x : Topology.CWComplex.cell C 0,
      Topology.RelCWComplex.map (C := C) 1 e (-1 : Fin 1 → ℝ) = vpt x := by
  obtain ⟨x, y, hxy⟩ := Topology.CWComplex.exists_cellFrontier_one_eq e
  have h1 : (Topology.RelCWComplex.map (C := C) 1 e) (-1 : Fin 1 → ℝ) ∈
      Topology.RelCWComplex.closedCell 0 x ∪ Topology.RelCWComplex.closedCell 0 y := by
    rw [← hxy]
    exact mem_image_of_mem _ (by simp)
  rw [Topology.RelCWComplex.closedCell_zero_eq_singleton,
      Topology.RelCWComplex.closedCell_zero_eq_singleton] at h1
  simp only [mem_union, mem_singleton_iff] at h1
  rcases h1 with h | h
  · exact ⟨x, h⟩
  · exact ⟨y, h⟩

noncomputable def srcIdx (e : Topology.CWComplex.cell C 1) : Topology.CWComplex.cell C 0 :=
  Classical.choose (exists_map_one_neg_one_eq (C := C) e)

lemma map_one_neg_one_eq_srcIdx (e : Topology.CWComplex.cell C 1) :
    Topology.RelCWComplex.map (C := C) 1 e (-1 : Fin 1 → ℝ) = vpt (srcIdx (C := C) e) :=
  Classical.choose_spec (exists_map_one_neg_one_eq (C := C) e)

noncomputable def tgtIdx (e : Topology.CWComplex.cell C 1) : Topology.CWComplex.cell C 0 :=
  Classical.choose (exists_map_one_one_eq (C := C) e)

lemma map_one_one_eq_tgtIdx (e : Topology.CWComplex.cell C 1) :
    Topology.RelCWComplex.map (C := C) 1 e (1 : Fin 1 → ℝ) = vpt (tgtIdx (C := C) e) :=
  Classical.choose_spec (exists_map_one_one_eq (C := C) e)

/-- The linear parametrisation of the closed unit ball of `Fin 1 → ℝ`. -/
def segF (t : unitInterval) : Fin 1 → ℝ := fun _ => 2 * (t : ℝ) - 1

lemma continuous_segF : Continuous segF := by unfold segF; fun_prop

lemma segF_mem (t : unitInterval) : segF t ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  simp only [Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sup_singleton, segF]
  rw [coe_nnnorm, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [unitInterval.nonneg t], by linarith [unitInterval.le_one t]⟩

lemma segF_zero : segF (0 : unitInterval) = (-1 : Fin 1 → ℝ) := by
  funext i; fin_cases i
  show 2 * ((0 : unitInterval) : ℝ) - 1 = -1
  norm_num

lemma segF_one : segF (1 : unitInterval) = (1 : Fin 1 → ℝ) := by
  funext i; fin_cases i
  show 2 * ((1 : unitInterval) : ℝ) - 1 = 1
  norm_num

/-- The characteristic map of a cell is injective on the open ball of its domain (this is the
bijectivity of the characteristic map onto the open cell, as recorded in Mathlib's CW-complex API). -/
lemma RelCWComplex.injOn_map_ball (n : ℕ) (i : Topology.RelCWComplex.cell C n) :
    Set.InjOn (Topology.RelCWComplex.map (C := C) n i) (Metric.ball 0 1) := by
  have h := (Topology.RelCWComplex.map (C := C) n i).injOn
  rwa [Topology.RelCWComplex.source_eq] at h

/-- **The open star of a vertex of a one-dimensional CW complex is open.**  The union of the open
cells of all cells whose closed cell contains the given `0`-cell is open. -/
theorem isOpen_openStar {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n))
    (v : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    IsOpen (⋃ (n : ℕ) (j : Topology.RelCWComplex.cell (Set.univ : Set X) n),
      ⋃ (_ : Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 v ![] ∈
        Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) n j),
        Topology.RelCWComplex.openCell (C := (Set.univ : Set X)) n j) := by
  set star : Set X := ⋃ (n : ℕ) (j : Topology.RelCWComplex.cell (Set.univ : Set X) n),
      ⋃ (_ : Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 v ![] ∈
        Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) n j),
        Topology.RelCWComplex.openCell (C := (Set.univ : Set X)) n j with hstar
  rw [← isClosed_compl_iff]
  have hmem : ∀ {n' : ℕ} {j' : Topology.RelCWComplex.cell (Set.univ : Set X) n'}
      (_ : Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 v ![] ∈
        Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) n' j'),
      Topology.RelCWComplex.openCell (C := (Set.univ : Set X)) n' j' ⊆ star := by
    intro n' j' hv' x hx
    rw [hstar]
    exact Set.mem_iUnion.mpr ⟨n', Set.mem_iUnion.mpr ⟨j', Set.mem_iUnion.mpr ⟨hv', hx⟩⟩⟩
  have hnot : ∀ {n' : ℕ} {j' : Topology.RelCWComplex.cell (Set.univ : Set X) n'},
      Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 v ![] ∉
        Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) n' j' →
      Disjoint star (Topology.RelCWComplex.openCell (C := (Set.univ : Set X)) n' j') := by
    intro n' j' hv'
    rw [Set.disjoint_left]
    intro x hxs hxO
    rw [hstar] at hxs
    simp only [Set.mem_iUnion] at hxs
    obtain ⟨n'', j'', hv'', hxO''⟩ := hxs
    have heq : (⟨n', j'⟩ : Σ n, Topology.RelCWComplex.cell (Set.univ : Set X) n) = ⟨n'', j''⟩ := by
      by_contra hne
      exact Set.disjoint_left.mp
        (Topology.RelCWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set X)) hne)
        hxO hxO''
    cases heq
    exact hv' hv''
  apply Topology.CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    (C := (Set.univ : Set X))
  · intro x _
    trivial
  · intro n hn j
    by_cases hv : Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 v ![] ∈
        Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) n j
    · left
      rw [Set.disjoint_left]
      intro x hxA hxO
      exact hxA (hmem hv hxO)
    · right
      have hn1 : n = 1 := by
        rcases n with _ | _ | m
        · omega
        · rfl
        · exact ((h2 (m + 2) (by omega)).false j).elim
      subst hn1
      have hfront : Topology.RelCWComplex.cellFrontier (C := (Set.univ : Set X)) 1 j ⊆
          {vpt (C := (Set.univ : Set X)) (srcIdx (C := (Set.univ : Set X)) j),
           vpt (C := (Set.univ : Set X)) (tgtIdx (C := (Set.univ : Set X)) j)} := by
        intro y hy
        rw [Topology.RelCWComplex.cellFrontier_one_eq] at hy
        obtain ⟨p, hp, rfl⟩ := hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl
        · exact Or.inl (map_one_neg_one_eq_srcIdx (C := (Set.univ : Set X)) j)
        · exact Or.inr (map_one_one_eq_tgtIdx (C := (Set.univ : Set X)) j)
      have hsub : Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) 1 j ⊆ starᶜ := by
        intro x hx
        rw [Set.mem_compl_iff]
        rw [← Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell] at hx
        rcases hx with hx | hx
        · have hx' := hfront hx
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
          rcases hx' with rfl | rfl
          · intro hxs
            by_cases h0 : Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 v ![] ∈
                Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) 0
                  (srcIdx (C := (Set.univ : Set X)) j)
            · refine hv ?_
              have hv_eq : Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 v ![] =
                  Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0
                    (srcIdx (C := (Set.univ : Set X)) j) ![] := by
                simpa only [Topology.RelCWComplex.closedCell_zero_eq_singleton,
                  Set.mem_singleton_iff] using h0
              rw [hv_eq]
              exact Topology.RelCWComplex.cellFrontier_subset_closedCell (C := (Set.univ : Set X)) 1 j hx
            · exact Set.disjoint_left.mp (hnot h0) hxs
                (Topology.RelCWComplex.openCell_zero_eq_singleton (C := (Set.univ : Set X))
                  (j := srcIdx (C := (Set.univ : Set X)) j) ▸ Set.mem_singleton _)
          · intro hxs
            by_cases h0 : Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 v ![] ∈
                Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) 0
                  (tgtIdx (C := (Set.univ : Set X)) j)
            · refine hv ?_
              have hv_eq : Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 v ![] =
                  Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0
                    (tgtIdx (C := (Set.univ : Set X)) j) ![] := by
                simpa only [Topology.RelCWComplex.closedCell_zero_eq_singleton,
                  Set.mem_singleton_iff] using h0
              rw [hv_eq]
              exact Topology.RelCWComplex.cellFrontier_subset_closedCell (C := (Set.univ : Set X)) 1 j hx
            · exact Set.disjoint_left.mp (hnot h0) hxs
                (Topology.RelCWComplex.openCell_zero_eq_singleton (C := (Set.univ : Set X))
                  (j := tgtIdx (C := (Set.univ : Set X)) j) ▸ Set.mem_singleton _)
        · exact fun hxs => Set.disjoint_left.mp (hnot hv) hxs hx
      rw [Set.inter_eq_right.mpr hsub]
      exact Topology.RelCWComplex.isClosed_closedCell

/-- The characteristic path of a 1-cell, from its source vertex to its target vertex. -/
def fwdPath (e : Topology.CWComplex.cell C 1) :
    Path (vpt (srcIdx (C := C) e)) (vpt (tgtIdx (C := C) e)) where
  toFun t := Topology.RelCWComplex.map (C := C) 1 e (segF t)
  continuous_toFun :=
    (Topology.RelCWComplex.continuousOn (C := C) 1 e).comp_continuous continuous_segF segF_mem
  source' := by
    show Topology.RelCWComplex.map (C := C) 1 e (segF 0) = vpt (srcIdx (C := C) e)
    rw [segF_zero]; exact map_one_neg_one_eq_srcIdx (C := C) e
  target' := by
    show Topology.RelCWComplex.map (C := C) 1 e (segF 1) = vpt (tgtIdx (C := C) e)
    rw [segF_one]; exact map_one_one_eq_tgtIdx (C := C) e

/-- An oriented 1-cell of the complex. -/
structure OEdge where
  cell : Topology.CWComplex.cell C 1
  dir : Bool

namespace OEdge

noncomputable def src (o : OEdge (C := C)) : Topology.CWComplex.cell C 0 :=
  if o.dir then srcIdx (C := C) o.cell else tgtIdx (C := C) o.cell

noncomputable def tgt (o : OEdge (C := C)) : Topology.CWComplex.cell C 0 :=
  if o.dir then tgtIdx (C := C) o.cell else srcIdx (C := C) o.cell

def neg (o : OEdge (C := C)) : OEdge (C := C) := ⟨o.cell, !o.dir⟩

@[simp] lemma src_mk_true (e : Topology.CWComplex.cell C 1) :
    (OEdge.mk e true).src = srcIdx (C := C) e := rfl

@[simp] lemma src_mk_false (e : Topology.CWComplex.cell C 1) :
    (OEdge.mk e false).src = tgtIdx (C := C) e := rfl

@[simp] lemma tgt_mk_true (e : Topology.CWComplex.cell C 1) :
    (OEdge.mk e true).tgt = tgtIdx (C := C) e := rfl

@[simp] lemma tgt_mk_false (e : Topology.CWComplex.cell C 1) :
    (OEdge.mk e false).tgt = srcIdx (C := C) e := rfl

@[simp] lemma neg_cell (o : OEdge (C := C)) : o.neg.cell = o.cell := rfl

@[simp] lemma neg_neg (o : OEdge (C := C)) : o.neg.neg = o := by
  cases o; simp [neg]

@[simp] lemma src_neg (o : OEdge (C := C)) : o.neg.src = o.tgt := by
  cases o with
  | mk c d => cases d <;> simp [neg, src, tgt]

@[simp] lemma tgt_neg (o : OEdge (C := C)) : o.neg.tgt = o.src := by
  cases o with
  | mk c d => cases d <;> simp [neg, src, tgt]

/-- The path traversing the oriented edge from its source to its target. -/
def path (o : OEdge (C := C)) : Path (vpt o.src) (vpt o.tgt) :=
  match o with
  | ⟨e, true⟩ => fwdPath (C := C) e
  | ⟨e, false⟩ => (fwdPath (C := C) e).symm

end OEdge

def IsWalk (u : Topology.CWComplex.cell C 0) : List (OEdge (C := C)) → Prop
  | [] => True
  | o :: l => o.src = u ∧ IsWalk o.tgt l

def endOfList (u : Topology.CWComplex.cell C 0) :
    (l : List (OEdge (C := C))) → IsWalk (C := C) u l → Topology.CWComplex.cell C 0
  | [], _ => u
  | o :: l, h => endOfList o.tgt l h.2

lemma isWalk_take {u : Topology.CWComplex.cell C 0} {l : List (OEdge (C := C))}
    (h : IsWalk (C := C) u l) (n : ℕ) : IsWalk (C := C) u (l.take n) := by
  induction l generalizing u n with
  | nil => cases n <;> trivial
  | cons o l ih =>
    cases n with
    | zero => trivial
    | succ n => exact ⟨h.1, ih h.2 n⟩

@[simp] lemma endOfList_nil {u : Topology.CWComplex.cell C 0}
    (h : IsWalk (C := C) u []) : endOfList u [] h = u := rfl

def Walk (u : Topology.CWComplex.cell C 0) :=
  { l : List (OEdge (C := C)) // IsWalk (C := C) u l }

namespace Walk

variable {u : Topology.CWComplex.cell C 0}

def endOf (w : Walk (C := C) u) : Topology.CWComplex.cell C 0 := endOfList u w.1 w.2

def nil (u : Topology.CWComplex.cell C 0) : Walk (C := C) u := ⟨[], trivial⟩

instance : Inhabited (Walk (C := C) u) := ⟨Walk.nil u⟩

@[simp] lemma endOf_nil : endOf (C := C) (nil u) = u := rfl

lemma obj_eq_of_isWalk {o : OEdge (C := C)} {l : List (OEdge (C := C))}
    (h : IsWalk (C := C) u (o :: l)) : o.src = u := h.1

lemma isWalk_append {l l' : List (OEdge (C := C))}
    (h : IsWalk (C := C) u l) (h' : IsWalk (C := C) (endOfList u l h) l') :
    IsWalk (C := C) u (l ++ l') := by
  induction l generalizing u with
  | nil => exact h'
  | cons o l ih => exact ⟨h.1, ih h.2 h'⟩

lemma endOfList_append {l l' : List (OEdge (C := C))}
    (h : IsWalk (C := C) u l) (h' : IsWalk (C := C) (endOfList u l h) l') :
    endOfList u (l ++ l') (isWalk_append h h') = endOfList (endOfList u l h) l' h' := by
  induction l generalizing u with
  | nil => rfl
  | cons o l ih => exact ih h.2 h'

/-- Concatenation of walks. -/
def concat (w : Walk (C := C) u) (w' : Walk (C := C) w.endOf) : Walk (C := C) u :=
  ⟨w.1 ++ w'.1, isWalk_append w.2 w'.2⟩

@[simp] lemma concat_endOf (w : Walk (C := C) u) (w' : Walk (C := C) w.endOf) :
    (w.concat w').endOf = w'.endOf := endOfList_append w.2 w'.2

/-- The path in `Y` obtained by traversing a list of oriented edges. -/
def pathOfList (u : Topology.CWComplex.cell C 0) :
    (l : List (OEdge (C := C))) → (h : IsWalk (C := C) u l) →
      Path (vpt u) (vpt (endOfList u l h))
  | [], _ => Path.refl _
  | o :: l, h =>
    (((OEdge.path (C := C) o).trans (pathOfList o.tgt l h.2)).cast (by rw [h.1]) rfl)

/-- The path in `Y` obtained by traversing the walk. -/
def pathOf (w : Walk (C := C) u) : Path (vpt u) (vpt w.endOf) :=
  pathOfList u w.1 w.2

end Walk

end

noncomputable section

variable {Y : Type*} [TopologicalSpace Y] {C : Set Y} [Topology.CWComplex C]

/-- A list of oriented edges is *reduced* if no two consecutive letters are inverse to one another
(as oriented edges). -/
def Reduced (l : List (OEdge (C := C))) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < l.length), l[i+1] ≠ (l[i]).neg

lemma reduced_take {l : List (OEdge (C := C))} (h : Reduced (C := C) l) (n : ℕ) :
    Reduced (C := C) (l.take n) := by
  intro i hi
  rw [List.getElem_take, List.getElem_take]
  exact h i (by rw [List.length_take] at hi; omega)

lemma reduced_dropLast {l : List (OEdge (C := C))} (h : Reduced (C := C) l) :
    Reduced (C := C) l.dropLast := by
  intro i hi
  rw [List.getElem_dropLast, List.getElem_dropLast]
  exact h i (by rw [List.length_dropLast] at hi; omega)

lemma reduced_cons_iff {a : OEdge (C := C)} {l : List (OEdge (C := C))} :
    Reduced (C := C) (a :: l) ↔
      (∀ b, l.head? = some b → b ≠ a.neg) ∧ Reduced (C := C) l := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · cases l with
      | nil => intro b hb; simp at hb
      | cons b l =>
        intro b' hb'
        have hbb : b = b' := by simpa using hb'
        subst hbb
        have h0 := h 0 (by simp)
        simpa using h0
    · intro i hi
      have h' := h (i + 1) (by simpa using hi)
      simpa only [List.getElem_cons_succ] using h'
  · rintro ⟨h₁, h₂⟩ i hi
    cases i with
    | zero =>
      cases l with
      | nil => simp at hi
      | cons b l =>
        have hb := h₁ b rfl
        simpa using hb
    | succ i =>
      have h' := h₂ i (by simpa using hi)
      simpa only [List.getElem_cons_succ] using h'

/-- A reduced list does not end with a letter followed by its inverse. -/
lemma reduced_snoc_ne_neg {l : List (OEdge (C := C))} {o : OEdge (C := C)}
    (h : Reduced (C := C) (l ++ [o])) (hl : l ≠ []) : o ≠ (l.getLast hl).neg := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a t ih =>
    rw [List.cons_append] at h
    obtain ⟨h₁, h₂⟩ := (reduced_cons_iff (C := C)).mp h
    cases t with
    | nil =>
      have ho := h₁ o (by simp)
      simpa using ho
    | cons b t =>
      have ht : (b :: t) ≠ [] := by simp
      have hgt : (a :: b :: t).getLast (by simp : (a :: b :: t) ≠ []) =
          (b :: t).getLast ht := by
        simp
      rw [hgt]
      exact ih h₂ ht

lemma isWalk_dropLast {u : Topology.CWComplex.cell C 0} {l : List (OEdge (C := C))}
    (h : IsWalk (C := C) u l) : IsWalk (C := C) u l.dropLast := by
  cases l with
  | nil => trivial
  | cons a l =>
    cases l with
    | nil => trivial
    | cons b l => exact ⟨h.1, isWalk_dropLast h.2⟩

/-- A walk whose last letter is `o` ends at the target of `o`. -/
lemma endOfList_append_singleton {u : Topology.CWComplex.cell C 0}
    {l : List (OEdge (C := C))} {o : OEdge (C := C)}
    (h : IsWalk (C := C) u (l ++ [o])) : endOfList u (l ++ [o]) h = o.tgt := by
  induction l generalizing u with
  | nil => rfl
  | cons a l ih => exact ih h.2

/-- The endpoint of a nonempty walk is the target of its last letter. -/
lemma endOfList_eq_getLast_tgt {u : Topology.CWComplex.cell C 0} :
    ∀ (l : List (OEdge (C := C))) (h : IsWalk (C := C) u l) (hne : l ≠ []),
      endOfList u l h = (l.getLast hne).tgt
  | [], _, hne => absurd rfl hne
  | [_], _, _ => rfl
  | _ :: b :: l, h, _ => endOfList_eq_getLast_tgt (b :: l) h.2 (by simp)

/-- The endpoint of a nonempty walk with its last letter dropped is the source of the last letter. -/
lemma endOfList_eq_getLast_src {u : Topology.CWComplex.cell C 0} :
    ∀ (l : List (OEdge (C := C))) (h : IsWalk (C := C) u l) (hne : l ≠ []),
      endOfList u l.dropLast (isWalk_dropLast h) = (l.getLast hne).src
  | [], _, hne => absurd rfl hne
  | [_], h, _ => by simpa [List.dropLast_singleton] using h.1.symm
  | _ :: b :: l, h, _ => endOfList_eq_getLast_src (b :: l) h.2 (by simp)

/-- Reduced walks starting at `u`. -/
abbrev RWalk (u : Topology.CWComplex.cell C 0) :=
  { l : List (OEdge (C := C)) // IsWalk (C := C) u l ∧ Reduced (C := C) l }

namespace RWalk

variable {u : Topology.CWComplex.cell C 0}

/-- The endpoint of a reduced walk. -/
def endOf (W : RWalk (C := C) u) : Topology.CWComplex.cell C 0 :=
  endOfList u W.1 W.2.1

/-- Dropping the last letter of a reduced walk. -/
def dropLast (W : RWalk (C := C) u) : RWalk (C := C) u :=
  ⟨W.1.dropLast, isWalk_dropLast W.2.1, reduced_dropLast W.2.2⟩

@[simp] lemma dropLast_val (W : RWalk (C := C) u) : W.dropLast.1 = W.1.dropLast := rfl

/-- The prefix of a reduced walk of a given length. -/
def take (W : RWalk (C := C) u) (n : ℕ) : RWalk (C := C) u :=
  ⟨W.1.take n, isWalk_take W.2.1 n, reduced_take W.2.2 n⟩

@[simp] lemma take_val (W : RWalk (C := C) u) (n : ℕ) : (W.take n).1 = W.1.take n := rfl

/-- The empty reduced walk, i.e. the base vertex of the universal cover. -/
def nil (u : Topology.CWComplex.cell C 0) : RWalk (C := C) u :=
  ⟨[], trivial, by intro i hi; simp at hi⟩

@[simp] lemma nil_val (u : Topology.CWComplex.cell C 0) : (nil (C := C) u).1 = [] := rfl

@[simp] lemma take_zero (W : RWalk (C := C) u) : W.take 0 = nil u := by
  apply Subtype.ext
  simp [take]

lemma take_ne_nil {W : RWalk (C := C) u} {n : ℕ} (hn : n ≠ 0) (hW : W.1 ≠ []) :
    (W.take n).1 ≠ [] := by
  intro hc
  have hc' : W.1.take n = [] := by simpa using hc
  have h1 : (W.1.take n).length = 0 := by rw [hc', List.length_nil]
  have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hW' : 1 ≤ W.1.length := by
    have := List.length_eq_zero_iff.not.mpr hW
    omega
  have h1m : 1 ≤ (W.1.take n).length := by
    rw [List.length_take]; exact le_min hn' hW'
  rw [h1] at h1m
  omega

/-- The last letter of a nonempty reduced walk. -/
def lastLetter (W : RWalk (C := C) u) (h : W.1 ≠ []) : OEdge (C := C) := W.1.getLast h

/-- The endpoint of a nonempty reduced walk is the target of its last letter. -/
lemma endOf_eq_lastLetter_tgt (W : RWalk (C := C) u) (h : W.1 ≠ []) :
    W.endOf = (W.lastLetter h).tgt :=
  endOfList_eq_getLast_tgt W.1 W.2.1 h

/-- The endpoint of the walk with its last letter dropped is the source of the last letter. -/
lemma endOf_dropLast_eq_lastLetter_src (W : RWalk (C := C) u) (h : W.1 ≠ []) :
    W.dropLast.endOf = (W.lastLetter h).src :=
  endOfList_eq_getLast_src W.1 W.2.1 h

/-- **A reduced walk does not extend by the inverse of its last letter.**  If `W'` is a reduced
walk with `W'.dropLast = W` then the last letter of `W'` is not the inverse of the last letter
of `W` (otherwise `W'` would not be reduced). -/
lemma lastLetter_ne_neg {W W' : RWalk (C := C) u} {hW : W.1 ≠ []} {hW' : W'.1 ≠ []}
    (hd : W'.dropLast = W) : W'.lastLetter hW' ≠ (W.lastLetter hW).neg := by
  have hdrop : W'.1.dropLast = W.1 := by
    have h := congrArg (fun x : RWalk (C := C) u => x.1) hd
    simpa only [RWalk.dropLast_val] using h
  have hl : W'.1.dropLast ≠ [] := by rw [hdrop]; exact hW
  have hkey : Reduced (C := C) (W'.1.dropLast ++ [W'.1.getLast hW']) := by
    rw [List.dropLast_append_getLast hW']
    exact W'.2.2
  have h := reduced_snoc_ne_neg (C := C) hkey hl
  have hgl : (W'.1.dropLast).getLast hl = W.1.getLast hW :=
    List.getLast_congr hl hW hdrop
  rw [hgl] at h
  simpa only [RWalk.lastLetter] using h

end RWalk

/-- The vertices of the universal cover carry the discrete topology (vertices are isolated). -/
instance instTopologicalSpaceRWalk : TopologicalSpace (RWalk (C := C) u) := ⊥

instance instDiscreteTopologyRWalk : DiscreteTopology (RWalk (C := C) u) := ⟨rfl⟩

/-- The naive points of the universal cover: either a reduced walk (a vertex) or a reduced walk of
positive length together with a parameter in the unit interval (a point of the corresponding edge).
The edge is the one "above" the walk, i.e. the last letter of the walk. -/
abbrev TreePt (u : Topology.CWComplex.cell C 0) :=
  RWalk (C := C) u ⊕ ({W : RWalk (C := C) u // W.1 ≠ []} × unitInterval)

/-- The naive points of the universal cover carry the sum topology: the discrete topology on the
vertices and, for each edge, a copy of the unit interval. -/
instance instTopologicalSpaceTreePt : TopologicalSpace (TreePt (C := C) u) :=
  inferInstanceAs (TopologicalSpace (RWalk (C := C) u ⊕
    ({W : RWalk (C := C) u // W.1 ≠ []} × unitInterval)))

/-- The gluing relation for the universal cover: the two ends of the edge above `W` are glued to
the vertices `W` (at parameter `0`) and `W.dropLast` (at parameter `1`). -/
def treeRel (u : Topology.CWComplex.cell C 0) : TreePt (C := C) u → TreePt (C := C) u → Prop
  | Sum.inr (⟨W, _⟩, t), Sum.inl W' => (t = 0 ∧ W' = W) ∨ (t = 1 ∧ W' = W.dropLast)
  | _, _ => False

lemma treeRel_inr_inl (W : RWalk (C := C) u) (hW : W.1 ≠ []) (t : unitInterval)
    (W' : RWalk (C := C) u) :
    treeRel (C := C) u (Sum.inr (⟨W, hW⟩, t)) (Sum.inl W') ↔
      (t = 0 ∧ W' = W) ∨ (t = 1 ∧ W' = W.dropLast) := Iff.rfl

/-- The universal cover of the one-skeleton. -/
def Tree (u : Topology.CWComplex.cell C 0) : Type _ :=
  Quotient (Relation.EqvGen.setoid (treeRel (C := C) u))

namespace Tree

variable {u : Topology.CWComplex.cell C 0}

/-- The universal cover carries the quotient topology. -/
instance instTopologicalSpaceTree : TopologicalSpace (Tree (C := C) u) :=
  inferInstanceAs (TopologicalSpace (Quotient (Relation.EqvGen.setoid (treeRel (C := C) u))))

/-- The quotient map from the naive points to the tree. -/
def mk (x : TreePt (C := C) u) : Tree (C := C) u := Quotient.mk _ x

/-- The vertex of the tree corresponding to a reduced walk. -/
def vertex (W : RWalk (C := C) u) : Tree (C := C) u := mk (Sum.inl W)

/-- A point of the tree in the interior of the edge above the reduced walk `W`. -/
def ept (W : RWalk (C := C) u) (hW : W.1 ≠ []) (t : unitInterval) : Tree (C := C) u :=
  mk (Sum.inr (⟨W, hW⟩, t))

lemma ept_zero_eq_vertex (W : RWalk (C := C) u) (hW : W.1 ≠ []) :
    ept W hW 0 = vertex W :=
  Quotient.sound (Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, rfl⟩))

lemma ept_one_eq_vertex_dropLast (W : RWalk (C := C) u) (hW : W.1 ≠ []) :
    ept W hW 1 = vertex W.dropLast :=
  Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩))

/-- The height of a point of the universal cover, i.e. the length of the walk to which it belongs. -/
def heightPt : TreePt (C := C) u → ℝ
  | Sum.inl W => (W.1.length : ℝ)
  | Sum.inr (⟨W, _⟩, t) => (W.1.length : ℝ) - (t : ℝ)

/-- The projection of the universal cover to the one-skeleton. -/
def projPt : TreePt (C := C) u → Y
  | Sum.inl W => vpt (endOfList u W.1 W.2.1)
  | Sum.inr (⟨W, hW⟩, t) => (OEdge.path (C := C) (W.lastLetter hW)).symm t

/-- The height of the `0`-end of the edge above `W` is the length of `W`. -/
lemma heightPt_ept_zero (W : RWalk (C := C) u) (hW : W.1 ≠ []) :
    heightPt (C := C) (Sum.inr (⟨W, hW⟩, (0 : unitInterval))) = (W.1.length : ℝ) := by
  show (W.1.length : ℝ) - ((0 : unitInterval) : ℝ) = (W.1.length : ℝ)
  norm_num

/-- The height of the `1`-end of the edge above `W` is the length of `W.dropLast`. -/
lemma heightPt_ept_one (W : RWalk (C := C) u) (hW : W.1 ≠ []) :
    heightPt (C := C) (Sum.inr (⟨W, hW⟩, (1 : unitInterval))) =
      (W.dropLast.1.length : ℝ) := by
  have hlen : 1 ≤ W.1.length := by
    have := List.length_eq_zero_iff.not.mpr hW
    omega
  show (W.1.length : ℝ) - ((1 : unitInterval) : ℝ) = (W.dropLast.1.length : ℝ)
  rw [RWalk.dropLast_val, List.length_dropLast, Nat.cast_sub hlen]
  norm_num

@[simp] lemma heightPt_vertex (W : RWalk (C := C) u) :
    heightPt (C := C) (Sum.inl W) = (W.1.length : ℝ) := rfl

@[simp] lemma projPt_vertex (W : RWalk (C := C) u) :
    projPt (C := C) (Sum.inl W) = vpt W.endOf := rfl

/-- The `0`-end of the edge above `W` projects to the endpoint of `W`. -/
lemma projPt_ept_zero (W : RWalk (C := C) u) (hW : W.1 ≠ []) :
    projPt (C := C) (Sum.inr (⟨W, hW⟩, (0 : unitInterval))) = vpt (W.lastLetter hW).tgt :=
  Path.source _

/-- The `1`-end of the edge above `W` projects to the endpoint of `W.dropLast`. -/
lemma projPt_ept_one (W : RWalk (C := C) u) (hW : W.1 ≠ []) :
    projPt (C := C) (Sum.inr (⟨W, hW⟩, (1 : unitInterval))) = vpt (W.lastLetter hW).src :=
  Path.target _

/-- On the generating relation, heights match. -/
lemma heightPt_eq_of_rel {x y : TreePt (C := C) u} (h : treeRel (C := C) u x y) :
    heightPt (C := C) x = heightPt (C := C) y := by
  rcases x with W | ⟨⟨W, hW⟩, t⟩ <;> rcases y with W' | ⟨⟨W', hW'⟩, t'⟩
  · exact absurd h (by simp [treeRel])
  · exact absurd h (by simp [treeRel])
  · rw [treeRel_inr_inl] at h
    rcases h with ⟨ht, hW'⟩ | ⟨ht, hW'⟩
    · rw [ht, hW', heightPt_ept_zero W hW, heightPt_vertex W]
    · rw [ht, hW', heightPt_ept_one W hW, heightPt_vertex W.dropLast]
  · exact absurd h (by simp [treeRel])

/-- On the generating relation, projections match.  This is exactly where
`endOfList_eq_getLast_tgt` and `endOfList_eq_getLast_src` are used. -/
lemma projPt_eq_of_rel {x y : TreePt (C := C) u} (h : treeRel (C := C) u x y) :
    projPt (C := C) x = projPt (C := C) y := by
  rcases x with W | ⟨⟨W, hW⟩, t⟩ <;> rcases y with W' | ⟨⟨W', hW'⟩, t'⟩
  · exact absurd h (by simp [treeRel])
  · exact absurd h (by simp [treeRel])
  · rw [treeRel_inr_inl] at h
    rcases h with ⟨ht, hW'⟩ | ⟨ht, hW'⟩
    · rw [ht, hW', projPt_ept_zero W hW, projPt_vertex W, RWalk.endOf_eq_lastLetter_tgt W hW]
    · rw [ht, hW', projPt_ept_one W hW, projPt_vertex W.dropLast,
        RWalk.endOf_dropLast_eq_lastLetter_src W hW]
  · exact absurd h (by simp [treeRel])

/-- Heights are invariant under the equivalence relation generated by `treeRel`. -/
lemma heightPt_eqvGen {x y : TreePt (C := C) u}
    (h : Relation.EqvGen (treeRel (C := C) u) x y) :
    heightPt (C := C) x = heightPt (C := C) y := by
  induction h with
  | rel x y h => exact heightPt_eq_of_rel h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Projections are invariant under the equivalence relation generated by `treeRel`. -/
lemma projPt_eqvGen {x y : TreePt (C := C) u}
    (h : Relation.EqvGen (treeRel (C := C) u) x y) :
    projPt (C := C) x = projPt (C := C) y := by
  induction h with
  | rel x y h => exact projPt_eq_of_rel h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The height function on the universal cover. -/
def height : Tree (C := C) u → ℝ :=
  Quotient.lift (heightPt (C := C)) fun _ _ h => heightPt_eqvGen h

/-- The projection of the universal cover onto the one-skeleton. -/
def proj : Tree (C := C) u → Y :=
  Quotient.lift (projPt (C := C)) fun _ _ h => projPt_eqvGen h

@[simp] lemma height_vertex (W : RWalk (C := C) u) :
    height (C := C) (vertex W) = (W.1.length : ℝ) := rfl

@[simp] lemma height_ept (W : RWalk (C := C) u) (hW : W.1 ≠ []) (t : unitInterval) :
    height (C := C) (ept W hW t) = (W.1.length : ℝ) - (t : ℝ) := rfl

@[simp] lemma proj_vertex (W : RWalk (C := C) u) :
    proj (C := C) (vertex W) = vpt W.endOf := rfl

@[simp] lemma proj_ept (W : RWalk (C := C) u) (hW : W.1 ≠ []) (t : unitInterval) :
    proj (C := C) (ept W hW t) = (OEdge.path (C := C) (W.lastLetter hW)).symm t := rfl

/-- Clamping a real number to the unit interval. -/
def unitClamp (x : ℝ) : unitInterval where
  val := max 0 (min 1 x)
  property := by
    refine ⟨le_max_left _ _, ?_⟩
    rw [max_le_iff]
    exact ⟨zero_le_one, min_le_left _ _⟩

@[simp] lemma unitClamp_val (x : ℝ) : ((unitClamp x : unitInterval) : ℝ) = max 0 (min 1 x) := rfl

lemma unitClamp_eq_one {x : ℝ} (h : 1 ≤ x) : unitClamp x = 1 := by
  apply Subtype.ext
  show max 0 (min 1 x) = 1
  rw [min_eq_left h, max_eq_right zero_le_one]

lemma unitClamp_eq_zero {x : ℝ} (h : x ≤ 0) : unitClamp x = 0 := by
  apply Subtype.ext
  show max 0 (min 1 x) = 0
  rw [min_eq_right (le_trans h zero_le_one), max_eq_left h]

/-- The walk underlying a naive point of the universal cover. -/
def walkOf : TreePt (C := C) u → RWalk (C := C) u
  | Sum.inl W => W
  | Sum.inr (⟨W, _⟩, _) => W

@[simp] lemma walkOf_inl (W : RWalk (C := C) u) :
    walkOf (Sum.inl W : TreePt (C := C) u) = W := rfl

@[simp] lemma walkOf_inr (W : RWalk (C := C) u) (hW : W.1 ≠ []) (t : unitInterval) :
    walkOf (Sum.inr (⟨W, hW⟩, t) : TreePt (C := C) u) = W := rfl

/-- Truncating a walk at height `r`: the point whose walk is the prefix of length `⌈r⌉` and whose
parameter is `⌈r⌉ - r`.  (Only used for `0 ≤ r ≤ height`; the guard makes the definition total.) -/
def truncW (r : ℝ) (W : RWalk (C := C) u) : TreePt (C := C) u :=
  if h : ⌈r⌉₊ = 0 ∨ W.1 = [] then Sum.inl (W.take ⌈r⌉₊)
  else Sum.inr (⟨W.take ⌈r⌉₊, RWalk.take_ne_nil (fun hc => h (Or.inl hc))
      (fun hc => h (Or.inr hc))⟩, unitClamp (⌈r⌉₊ - r))

/-- **The point at height `r` on the geodesic from the base vertex to `x`**, in the coordinates of
the tree: take the prefix of the walk of length `⌈r⌉` and the parameter `⌈r⌉ - r` on the edge above
it.  (Only used for `0 ≤ r ≤ height x`; the guard makes the definition total.) -/
def truncPt (r : ℝ) : TreePt (C := C) u → TreePt (C := C) u
  | Sum.inl W => truncW r W
  | Sum.inr (⟨W, _⟩, _) => truncW r W

@[simp] lemma truncPt_inl (r : ℝ) (W : RWalk (C := C) u) :
    truncPt r (Sum.inl W : TreePt (C := C) u) = truncW r W := rfl

@[simp] lemma truncPt_inr (r : ℝ) (W : RWalk (C := C) u) (hW : W.1 ≠ []) (t : unitInterval) :
    truncPt r (Sum.inr (⟨W, hW⟩, t) : TreePt (C := C) u) = truncW r W := rfl

lemma truncW_of_ne_zero {r : ℝ} {W : RWalk (C := C) u} (hr : ⌈r⌉₊ ≠ 0) (hW : W.1 ≠ []) :
    truncW (C := C) r W =
      Sum.inr (⟨W.take ⌈r⌉₊, RWalk.take_ne_nil hr hW⟩, unitClamp (⌈r⌉₊ - r)) := by
  rw [truncW, dif_neg (by rintro (h | h); exacts [hr h, hW h])]

@[simp] lemma truncW_zero (W : RWalk (C := C) u) :
    truncW (C := C) (0 : ℝ) W = Sum.inl (RWalk.nil u) := by
  have h0 : ⌈(0 : ℝ)⌉₊ = 0 := Nat.ceil_eq_zero.mpr (le_refl (0 : ℝ))
  rw [truncW, dif_pos (Or.inl h0), h0, RWalk.take_zero]

lemma take_dropLast_eq_take {l : List (OEdge (C := C))} {n : ℕ} (h : n ≤ l.length - 1) :
    l.dropLast.take n = l.take n := by
  rw [List.dropLast_eq_take, List.take_take, min_eq_left h]

/-- **The truncation respects the gluing relation.**  Both points have height at least `r`, so the
walk components agree: at parameter `0` the two coordinates coincide definitionally, and at
parameter `1` the walk `W` and `W.dropLast` have the same prefix of length `⌈r⌉`. -/
lemma truncPt_eq_of_rel {r : ℝ} {x y : TreePt (C := C) u}
    (h : treeRel (C := C) u x y) (hx : r ≤ heightPt (C := C) x) :
    truncPt (C := C) r x = truncPt (C := C) r y := by
  rcases x with W | ⟨⟨W, hW⟩, t⟩ <;> rcases y with W' | ⟨⟨W', hW'⟩, t'⟩
  · exact absurd h (by simp [treeRel])
  · exact absurd h (by simp [treeRel])
  · rw [treeRel_inr_inl] at h
    rcases h with ⟨ht, hW'⟩ | ⟨ht, hW'⟩
    · subst hW'
      subst ht
      simp only [truncPt]
    · subst hW'
      subst ht
      have hlen : 1 ≤ W.1.length := by
        have := List.length_eq_zero_iff.not.mpr hW
        omega
      have hx' : r ≤ (W.1.length : ℝ) - 1 := by
        simpa [heightPt] using hx
      have hceil : ⌈r⌉₊ ≤ W.1.length - 1 := by
        rw [Nat.ceil_le, Nat.cast_sub hlen]
        simpa using hx'
      simp only [truncPt, truncW]
      by_cases hc : ⌈r⌉₊ = 0
      · rw [dif_pos (Or.inl hc), dif_pos (Or.inl hc), hc, RWalk.take_zero, RWalk.take_zero]
      · have hWne : ¬(⌈r⌉₊ = 0 ∨ (W.dropLast).1 = []) := by
          rintro (h | h)
          · exact hc h
          · have hlen : 1 ≤ ⌈r⌉₊ := Nat.one_le_iff_ne_zero.mpr hc
            have h0 : (W.1.dropLast).length = 0 := List.length_eq_zero_iff.mpr h
            rw [List.length_dropLast] at h0
            omega
        rw [dif_neg (fun h => h.elim hc hW), dif_neg hWne]
        refine congrArg Sum.inr (Prod.ext ?_ rfl)
        exact Subtype.ext (Subtype.ext (take_dropLast_eq_take hceil).symm)
  · exact absurd h (by simp [treeRel])

@[simp] lemma truncPt_zero (x : TreePt (C := C) u) :
    truncPt (C := C) 0 x = Sum.inl (RWalk.nil u) := by
  rcases x with W | ⟨⟨W, hW⟩, t⟩ <;> exact truncW_zero W

/-- Two `Sum.inr` points with the same walk and parameter are the same point of the tree. -/
lemma mk_inr_congr {W W' : RWalk (C := C) u} {hW : W.1 ≠ []} {hW' : W'.1 ≠ []} {t t' : unitInterval}
    (h : W = W') (ht : t = t') :
    (Tree.mk (Sum.inr (⟨W, hW⟩, t)) : Tree (C := C) u) =
      Tree.mk (Sum.inr (⟨W', hW'⟩, t')) := by
  subst h; subst ht; rfl

/-- The prefix of length `k` of a reduced walk, with its last letter dropped, is the prefix of
length `k - 1`. -/
lemma RWalk.dropLast_take_eq_take {W : RWalk (C := C) u} {k : ℕ} (hk : 1 ≤ k)
    (hkL : k ≤ W.1.length) : (W.take k).dropLast = W.take (k - 1) := by
  apply Subtype.ext
  rw [RWalk.dropLast_val, RWalk.take_val, RWalk.take_val,
    List.dropLast_take_eq_take_dropLast, take_dropLast_eq_take]
  omega

/-- The truncation at an integer height is the corresponding vertex. -/
lemma mk_truncW_natCast {W : RWalk (C := C) u} (hW : W.1 ≠ []) {j : ℕ}
    (hj : j ≤ W.1.length) :
    (Tree.mk (truncW (C := C) (j : ℝ) W) : Tree (C := C) u) = Tree.vertex (W.take j) := by
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · subst hj0
    simp only [Nat.cast_zero]
    rw [truncW_zero W, RWalk.take_zero]
    rfl
  · have hceil : ⌈(j : ℝ)⌉₊ = j := Nat.ceil_natCast j
    have hu : unitClamp ((⌈(j : ℝ)⌉₊ : ℝ) - (j : ℝ)) = (0 : unitInterval) := by
      rw [hceil, show (j : ℝ) - (j : ℝ) = 0 by ring, unitClamp_eq_zero le_rfl]
    have hw : W.take ⌈(j : ℝ)⌉₊ = W.take j := by
      apply Subtype.ext
      simp only [RWalk.take_val, hceil]
    rw [truncW_of_ne_zero (by omega) hW]
    rw [hu, ← hw]
    exact Tree.ept_zero_eq_vertex (W.take ⌈(j : ℝ)⌉₊) (RWalk.take_ne_nil (by omega) hW)

/-- The truncations at heights corresponding to `k` and to `k + 1` agree at the vertex in
between. -/
lemma ept_zero_eq_ept_one_take {W : RWalk (C := C) u} (hW : W.1 ≠ []) {k : ℕ} (hk : 1 ≤ k)
    (hkL : k + 1 ≤ W.1.length) :
    Tree.ept (W.take k) (RWalk.take_ne_nil (by omega) hW) (0 : unitInterval) =
      Tree.ept (W.take (k + 1)) (RWalk.take_ne_nil (by omega) hW) (1 : unitInterval) := by
  rw [Tree.ept_zero_eq_vertex, Tree.ept_one_eq_vertex_dropLast]
  exact (congrArg Tree.vertex (RWalk.dropLast_take_eq_take (k := k + 1) (by omega) hkL)).symm

/-- **The geodesic description of the truncation.**  For `r ∈ [k-1, k]`, truncating a nonempty
reduced walk at height `r` gives the point at height `r` on the edge above the prefix of length
`k`. -/
lemma mk_truncW_eq_ept {W : RWalk (C := C) u} (hW : W.1 ≠ []) {k : ℕ} (hk : 1 ≤ k)
    (hkL : k ≤ W.1.length) {r : ℝ} (hr1 : (k : ℝ) - 1 ≤ r) (hr2 : r ≤ k) :
    (Tree.mk (truncW (C := C) r W) : Tree (C := C) u) =
      Tree.ept (W.take k) (RWalk.take_ne_nil (by omega) hW) (unitClamp ((k : ℝ) - r)) := by
  by_cases hlt : (k : ℝ) - 1 < r
  · have hceil : ⌈r⌉₊ = k := by
      rw [Nat.ceil_eq_iff (by omega)]
      refine ⟨?_, hr2⟩
      rw [Nat.cast_sub hk]; push_cast; exact hlt
    have hu : unitClamp ((⌈r⌉₊ : ℝ) - r) = unitClamp ((k : ℝ) - r) := by rw [hceil]
    have hw : W.take ⌈r⌉₊ = W.take k := by
      apply Subtype.ext
      simp only [RWalk.take_val, hceil]
    rw [truncW_of_ne_zero (by omega) hW]
    rw [hu]
    refine congrArg (fun P : {W : RWalk (C := C) u // W.1 ≠ []} =>
      (Tree.mk (Sum.inr (P, unitClamp ((k : ℝ) - r))) : Tree (C := C) u)) ?_
    apply Subtype.ext
    apply Subtype.ext
    simp only [RWalk.take_val, hceil]
  · have heq : r = (k : ℝ) - 1 := le_antisymm (le_of_not_gt hlt) hr1
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk, Nat.cast_one]
    rw [heq, show ((k : ℝ) - ((k : ℝ) - 1)) = 1 by ring, unitClamp_eq_one le_rfl,
      Tree.ept_one_eq_vertex_dropLast, RWalk.dropLast_take_eq_take hk hkL, ← hcast]
    exact mk_truncW_natCast hW (by omega)


lemma truncPt_eqvGen_aux {x y : TreePt (C := C) u}
    (h : Relation.EqvGen (treeRel (C := C) u) x y) :
    heightPt (C := C) x = heightPt (C := C) y ∧
      ∀ (r : ℝ), r ≤ heightPt (C := C) x →
        truncPt (C := C) r x = truncPt (C := C) r y := by
  induction h with
  | rel x y h => exact ⟨heightPt_eq_of_rel h, fun r hr => truncPt_eq_of_rel h hr⟩
  | refl x => exact ⟨rfl, fun _ _ => rfl⟩
  | symm x y _ ih =>
      exact ⟨ih.1.symm, fun r hr => (ih.2 r (ih.1 ▸ hr)).symm⟩
  | trans x y z _ _ ih₁ ih₂ =>
      exact ⟨ih₁.1.trans ih₂.1, fun r hr => (ih₁.2 r hr).trans (ih₂.2 r (ih₁.1 ▸ hr))⟩

/-- **The truncation respects the gluing relation.**  Version through the generated
equivalence relation, i.e. well defined on the universal cover. -/
lemma truncPt_eqvGen {r : ℝ} {x y : TreePt (C := C) u}
    (h : Relation.EqvGen (treeRel (C := C) u) x y) (hx : r ≤ heightPt (C := C) x) :
    truncPt (C := C) r x = truncPt (C := C) r y :=
  (truncPt_eqvGen_aux h).2 r hx

/-! ## The topology on the universal cover -/

/-- In a product whose first factor is discrete, openness is detected on the slices. -/
lemma isOpen_prod_discrete_iff {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [DiscreteTopology α] {A : Set (α × β)} :
    IsOpen A ↔ ∀ a : α, IsOpen {b | (a, b) ∈ A} := by
  constructor
  · intro hA a
    exact hA.preimage (continuous_const.prodMk continuous_id)
  · intro h
    have hA : A = Set.iUnion fun a : α => ({a} : Set α) ×ˢ {b | (a, b) ∈ A} := by
      ext p
      constructor
      · intro hp
        exact Set.mem_iUnion.mpr ⟨p.1, by rw [Set.mem_prod]; exact ⟨rfl, hp⟩⟩
      · intro hp
        rw [Set.mem_iUnion] at hp
        obtain ⟨a, ha⟩ := hp
        rw [Set.mem_prod] at ha
        show (p.1, p.2) ∈ A
        rw [ha.1]
        exact ha.2
    rw [hA]
    exact isOpen_iUnion fun a => (isOpen_discrete _).prod (h a)

/-- The quotient map from the naive points to the universal cover is continuous. -/
lemma continuous_mkPt : Continuous fun x : TreePt (C := C) u => (mk x : Tree (C := C) u) :=
  continuous_quotient_mk'

/-- For fixed `W`, the map `t ↦ ept W hW t` is continuous. -/
lemma continuous_ept (W : RWalk (C := C) u) (hW : W.1 ≠ []) :
    Continuous fun t : unitInterval => ept (C := C) W hW t :=
  continuous_mkPt.comp (continuous_inr.comp (continuous_const.prodMk continuous_id))

/-- **A subset of the universal cover is open iff all of its slices along edges are open.** -/
lemma isOpen_iff (s : Set (Tree (C := C) u)) :
    IsOpen s ↔ ∀ (W : RWalk (C := C) u) (hW : W.1 ≠ []),
      IsOpen {t : unitInterval | ept (C := C) W hW t ∈ s} := by
  have key : IsOpen s ↔
      IsOpen ((fun x : TreePt (C := C) u => (mk x : Tree (C := C) u)) ⁻¹' s) :=
    isOpen_coinduced
  rw [key]
  constructor
  · intro hA W hW
    have h2 : Continuous fun t : unitInterval => (Sum.inr (⟨W, hW⟩, t) : TreePt (C := C) u) :=
      continuous_inr.comp (continuous_const.prodMk continuous_id)
    have h3 := hA.preimage h2
    convert h3 using 1
    ext t
    rfl
  · intro h
    have h' : IsOpen ((fun x : RWalk (C := C) u ⊕
        ({W : RWalk (C := C) u // W.1 ≠ []} × unitInterval) =>
          (mk x : Tree (C := C) u)) ⁻¹' s) := by
      rw [isOpen_sum_iff]
      constructor
      · exact isOpen_discrete _
      · rw [isOpen_prod_discrete_iff]
        intro e
        exact h e.1 e.2
    exact isOpen_coinduced.mpr h'

/-- **Continuity of a map out of the universal cover is detected on the edges.** -/
lemma continuous_iff {Z : Type*} [TopologicalSpace Z] (f : Tree (C := C) u → Z) :
    Continuous f ↔ ∀ (W : RWalk (C := C) u) (hW : W.1 ≠ []),
      Continuous fun t : unitInterval => f (ept (C := C) W hW t) := by
  constructor
  · intro hf W hW
    exact hf.comp (continuous_ept W hW)
  · intro h
    rw [continuous_def]
    intro U hU
    rw [isOpen_iff]
    intro W hW
    convert hU.preimage (h W hW) using 1
    ext t
    rfl

/-- The projection of the universal cover to the one-skeleton is continuous. -/
lemma continuous_proj : Continuous (proj (C := C) (u := u)) := by
  rw [continuous_iff]
  intro W hW
  exact (OEdge.path (C := C) (W.lastLetter hW)).symm.continuous

/-- The height function on the universal cover is continuous. -/
lemma continuous_height : Continuous (height (C := C) (u := u)) := by
  rw [continuous_iff]
  intro W hW
  show Continuous fun t : unitInterval => (W.1.length : ℝ) - (t : ℝ)
  exact continuous_const.sub continuous_subtype_val

/-! ## The geodesic contraction of the universal cover -/

lemma truncPt_eq_truncW (r : ℝ) (x : TreePt (C := C) u) :
    truncPt (C := C) r x = truncW (C := C) r (walkOf x) := by
  rcases x with W | ⟨⟨W, hW⟩, t⟩ <;> rfl

/-- In a product whose first factor is discrete, a map is continuous iff all its slices are. -/
lemma continuous_prod_of_discrete {α β γ : Type*} [TopologicalSpace α] [DiscreteTopology α]
    [TopologicalSpace β] [TopologicalSpace γ] {f : α × β → γ} :
    Continuous f ↔ ∀ a : α, Continuous fun b => f (a, b) := by
  constructor
  · intro hf a
    exact hf.comp (continuous_const.prodMk continuous_id)
  · intro h
    refine continuous_of_continuousOn_iUnion_of_isOpen (fun a => ?_)
      (fun a => (isOpen_discrete ({a} : Set α)).prod isOpen_univ) ?_
    · have h2 : ContinuousOn (fun p : α × β => f (a, p.2)) ({a} ×ˢ (Set.univ : Set β)) :=
        (h a).comp_continuousOn continuous_snd.continuousOn
      refine ContinuousOn.congr (s := {a} ×ˢ (Set.univ : Set β)) h2 (fun p hp => ?_)
      have hx : (a, p.2) = p := by rw [← hp.1]
      exact (congrArg f hx).symm
    · rw [eq_univ_iff_forall]
      intro p
      exact Set.mem_iUnion.mpr ⟨p.1, by simp⟩

/-- In a product `(α × β) × γ` whose first factor is discrete, a map is continuous iff all its
slices are. -/
lemma continuous_prod_prod_of_discrete {α β γ δ : Type*} [TopologicalSpace α]
    [DiscreteTopology α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
    {f : (α × β) × γ → δ} :
    Continuous f ↔ ∀ a : α, Continuous fun p : β × γ => f ((a, p.1), p.2) := by
  have hsymm : Continuous (⇑(Homeomorph.prodAssoc α β γ).symm) :=
    (Homeomorph.prodAssoc α β γ).symm.continuous
  constructor
  · intro hf a
    exact hf.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  · intro h
    have h2 : Continuous (fun p : α × (β × γ) => f ((p.1, p.2.1), p.2.2)) := by
      rw [continuous_prod_of_discrete]
      intro a
      exact h a
    have h3 : Continuous (f ∘ ⇑(Homeomorph.prodAssoc α β γ).symm) := h2
    exact (Homeomorph.comp_continuous_iff' (f := f) (Homeomorph.prodAssoc α β γ).symm).mp h3

/-- The unit clamp is continuous. -/
lemma continuous_unitClamp : Continuous (unitClamp : ℝ → unitInterval) := by
  have h : Continuous fun x : ℝ => max 0 (min 1 x) :=
    continuous_const.max (continuous_const.min continuous_id)
  exact h.subtype_mk (fun x => (unitClamp x).2)

@[simp] lemma unitClamp_of_mem (t : unitInterval) : unitClamp (t : ℝ) = t := by
  apply Subtype.ext
  show max 0 (min 1 (t : ℝ)) = (t : ℝ)
  rw [min_eq_right t.2.2, max_eq_right t.2.1]

/-- **The geodesic from the base vertex to a point of the tree is continuous.** -/
lemma continuous_geo {W : RWalk (C := C) u} (hW : W.1 ≠ []) :
    Continuous fun p : unitInterval × unitInterval =>
      (Tree.mk (truncW (C := C) ((1 - (p.2 : ℝ)) * ((W.1.length : ℝ) - (p.1 : ℝ))) W) :
        Tree (C := C) u) := by
  have hL1 : 1 ≤ W.1.length := by
    have := List.length_eq_zero_iff.not.mpr hW
    omega
  have hL1' : (1 : ℝ) ≤ (W.1.length : ℝ) := by exact_mod_cast hL1
  set r : unitInterval × unitInterval → ℝ :=
    fun p => (1 - (p.2 : ℝ)) * ((W.1.length : ℝ) - (p.1 : ℝ)) with hr
  have hrcont : Continuous r := by
    rw [hr]; fun_prop
  have hr_nonneg (p : unitInterval × unitInterval) : 0 ≤ r p := by
    rw [hr]
    have h1 : 0 ≤ 1 - (p.2 : ℝ) := by linarith [p.2.2.2]
    have h2 : 0 ≤ (W.1.length : ℝ) - (p.1 : ℝ) := by linarith [p.1.2.2, hL1']
    exact mul_nonneg h1 h2
  have hr_bound (p : unitInterval × unitInterval) : r p ≤ (W.1.length : ℝ) := by
    rw [hr]
    show (1 - (p.2 : ℝ)) * ((W.1.length : ℝ) - (p.1 : ℝ)) ≤ (W.1.length : ℝ)
    have h1 : (1 - (p.2 : ℝ)) ≤ (1 : ℝ) := by linarith [p.2.2.1]
    have h3 : 0 ≤ ((W.1.length : ℝ) - (p.1 : ℝ)) := by linarith [p.1.2.2, hL1']
    calc (1 - (p.2 : ℝ)) * ((W.1.length : ℝ) - (p.1 : ℝ))
          ≤ (1 : ℝ) * ((W.1.length : ℝ) - (p.1 : ℝ)) := mul_le_mul_of_nonneg_right h1 h3
      _ ≤ (W.1.length : ℝ) := by linarith [p.1.2.1]
  set P : ℕ → Set (unitInterval × unitInterval) :=
    fun k => {p | (k : ℝ) ≤ r p ∧ r p ≤ (k : ℝ) + 1 ∧ k + 1 ≤ W.1.length} with hP
  have hPclosed (k : ℕ) : IsClosed (P k) := by
    have h1 : IsClosed {p : unitInterval × unitInterval | (k : ℝ) ≤ r p} :=
      isClosed_le continuous_const hrcont
    have h2 : IsClosed {p : unitInterval × unitInterval | r p ≤ (k : ℝ) + 1} :=
      isClosed_le hrcont continuous_const
    have h3 : IsClosed {p : unitInterval × unitInterval | k + 1 ≤ W.1.length} := by
      by_cases h : k + 1 ≤ W.1.length
      · rw [show {p : unitInterval × unitInterval | k + 1 ≤ W.1.length} = univ from
          Set.eq_univ_of_forall fun p => h]
        exact isClosed_univ
      · rw [show {p : unitInterval × unitInterval | k + 1 ≤ W.1.length} = ∅ from
          Set.eq_empty_of_forall_notMem fun p hp => h hp]
        exact isClosed_empty
    rw [hP]
    convert h1.inter (h2.inter h3) using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  have hlf : LocallyFinite P := by
    intro p₀
    refine ⟨{p | r p < r p₀ + 1}, ?_, ?_⟩
    · refine (isOpen_lt hrcont continuous_const).mem_nhds ?_
      show r p₀ < r p₀ + 1
      exact lt_add_one _
    · refine Set.Finite.subset (Set.finite_Iic ⌈r p₀⌉₊) ?_
      rintro k ⟨p, hkP, hpU⟩
      rw [hP] at hkP
      simp only [Set.mem_setOf_eq, Set.mem_Iic]
      by_contra hlt
      push_neg at hlt
      have h1 : (⌈r p₀⌉₊ : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlt
      have h2 : r p₀ ≤ (⌈r p₀⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : (k : ℝ) ≤ r p := hkP.1
      have h4 : r p < r p₀ + 1 := hpU
      linarith
  have hcov : ⋃ k, P k = univ := by
    rw [eq_univ_iff_forall]
    intro p
    rcases lt_or_eq_of_le (hr_bound p) with hlt | heq
    · refine Set.mem_iUnion.mpr ⟨⌊r p⌋₊, ?_⟩
      rw [hP]
      simp only [Set.mem_setOf_eq]
      have hfl : (⌊r p⌋₊ : ℝ) ≤ r p := Nat.floor_le (hr_nonneg p)
      have hfr : r p < (⌊r p⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have hltL : ⌊r p⌋₊ + 1 ≤ W.1.length := by
        have hh : ⌊r p⌋₊ < W.1.length := (Nat.floor_lt (hr_nonneg p)).mpr hlt
        omega
      exact ⟨hfl, le_of_lt hfr, hltL⟩
    · refine Set.mem_iUnion.mpr ⟨W.1.length - 1, ?_⟩
      rw [hP]
      simp only [Set.mem_setOf_eq]
      have hcast : ((W.1.length - 1 : ℕ) : ℝ) = (W.1.length : ℝ) - 1 := by
        rw [Nat.cast_sub hL1, Nat.cast_one]
      refine ⟨?_, ?_, by omega⟩
      · rw [hcast]; linarith [heq]
      · rw [hcast]; linarith [heq]
  refine LocallyFinite.continuous hlf hcov hPclosed (fun k => ?_)
  have hk' : (W.take (k + 1)).1 ≠ [] := RWalk.take_ne_nil (by omega) hW
  have htheta : Continuous fun p : unitInterval × unitInterval =>
      (Tree.ept (W.take (k + 1)) hk' (unitClamp (((k + 1 : ℕ) : ℝ) - r p)) :
        Tree (C := C) u) :=
    (Tree.continuous_ept (W.take (k + 1)) hk').comp
      (continuous_unitClamp.comp (continuous_const.sub hrcont))
  refine htheta.continuousOn.congr (fun p hp => ?_)
  rw [hP] at hp
  have hkk : (((k + 1 : ℕ) : ℝ)) - 1 ≤ r p := by push_cast; linarith [hp.1]
  have hk2 : r p ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith [hp.2.1]
  exact mk_truncW_eq_ept hW (by omega) hp.2.2 hkk hk2


/-! ## The contraction of the universal cover -/

lemma RWalk.take_length (W : RWalk (C := C) u) : W.take W.1.length = W := by
  apply Subtype.ext
  rw [RWalk.take_val, List.take_length]

lemma RWalk.length_pos {W : RWalk (C := C) u} (hW : W.1 ≠ []) : 0 < W.1.length :=
  Nat.pos_of_ne_zero fun h => hW (List.length_eq_zero_iff.mp h)

/-- The truncation at the height of a vertex is that vertex. -/
lemma mk_truncW_self_vertex (W : RWalk (C := C) u) :
    (Tree.mk (truncW (C := C) (W.1.length : ℝ) W) : Tree (C := C) u) =
      Tree.mk (Sum.inl W) := by
  rcases Nat.eq_zero_or_pos W.1.length with hL0 | hLpos
  · have hWnil : W = RWalk.nil (C := C) u := by
      apply Subtype.ext
      rw [RWalk.nil_val]
      exact List.length_eq_zero_iff.mp hL0
    subst hWnil
    rw [RWalk.nil_val, List.length_nil, Nat.cast_zero, truncW_zero]
  · have hW : W.1 ≠ [] := fun h => by simp [h] at hLpos
    have hceil : ⌈(W.1.length : ℝ)⌉₊ = W.1.length := Nat.ceil_natCast _
    have hw : W.take ⌈(W.1.length : ℝ)⌉₊ = W := by
      rw [hceil, RWalk.take_length]
    have ht : unitClamp (⌈(W.1.length : ℝ)⌉₊ - (W.1.length : ℝ)) = (0 : unitInterval) := by
      rw [hceil, sub_self, unitClamp_eq_zero le_rfl]
    rw [truncW_of_ne_zero (by rw [hceil]; omega) hW, ht]
    have hrel : treeRel (C := C) u
        (Sum.inr (⟨W.take ⌈(W.1.length : ℝ)⌉₊, RWalk.take_ne_nil (by rw [hceil]; omega) hW⟩,
          (0 : unitInterval)))
        (Sum.inl (W.take ⌈(W.1.length : ℝ)⌉₊)) := Or.inl ⟨rfl, rfl⟩
    refine (Quotient.sound (Relation.EqvGen.rel _ _ hrel)).trans ?_
    rw [hw]
    rfl

/-- The truncation at the height of a point in an edge is that point. -/
lemma mk_truncW_self_inr {W : RWalk (C := C) u} (hW : W.1 ≠ []) (t : unitInterval) :
    (Tree.mk (truncW (C := C) ((W.1.length : ℝ) - (t : ℝ)) W) : Tree (C := C) u) =
      Tree.mk (Sum.inr (⟨W, hW⟩, t)) := by
  have hLpos := RWalk.length_pos hW
  rcases lt_or_eq_of_le t.2.2 with ht | ht
  · -- t < 1 : the truncation has height `length` and parameter `t`
    have hceil : ⌈(W.1.length : ℝ) - (t : ℝ)⌉₊ = W.1.length := by
      rw [Nat.ceil_eq_iff (by omega)]
      constructor
      · rw [Nat.cast_sub (by omega : 1 ≤ W.1.length), Nat.cast_one]; linarith [t.2.2]
      · linarith [t.2.1]
    rw [truncW_of_ne_zero (by rw [hceil]; omega) hW]
    have hw : W.take ⌈(W.1.length : ℝ) - (t : ℝ)⌉₊ = W := by
      rw [hceil, RWalk.take_length]
    have ht' : unitClamp (⌈(W.1.length : ℝ) - (t : ℝ)⌉₊ -
        ((W.1.length : ℝ) - (t : ℝ))) = t := by
      rw [hceil, show (W.1.length : ℝ) - ((W.1.length : ℝ) - (t : ℝ)) = (t : ℝ) by ring,
        unitClamp_of_mem]
    exact mk_inr_congr hw ht'
  · -- t = 1 : the truncation is the vertex `W.dropLast`
    have ht1 : t = (1 : unitInterval) := Subtype.ext ht
    subst ht1
    have hcast : ((1 : unitInterval) : ℝ) = 1 := rfl
    rw [hcast, show (W.1.length : ℝ) - 1 = ((W.1.length - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega : 1 ≤ W.1.length), Nat.cast_one]]
    -- the target vertex
    have h2 : (Tree.mk (Sum.inr (⟨W, hW⟩, (1 : unitInterval))) : Tree (C := C) u) =
        Tree.mk (Sum.inl W.dropLast) := by
      have hrel : treeRel (C := C) u (Sum.inr (⟨W, hW⟩, (1 : unitInterval)))
          (Sum.inl W.dropLast) := Or.inr ⟨rfl, rfl⟩
      exact Quotient.sound (Relation.EqvGen.rel _ _ hrel)
    have hd : W.take (W.1.length - 1) = W.dropLast := by
      have h3 := RWalk.dropLast_take_eq_take (k := W.1.length) hLpos le_rfl
      rw [RWalk.take_length] at h3
      exact h3.symm
    rcases Nat.eq_zero_or_pos (W.1.length - 1) with hk0 | hkpos
    · -- length = 1 : the truncation is the base vertex
      have hnil : W.dropLast = RWalk.nil (C := C) u := by
        have hl1 : W.1.length = 1 := by omega
        apply Subtype.ext
        apply List.length_eq_zero_iff.mp
        rw [RWalk.dropLast_val, List.length_dropLast, hl1]
      rw [show W.1.length - 1 = 0 by omega]
      simp only [Nat.cast_zero, truncW_zero]
      have hrel : treeRel (C := C) u (Sum.inr (⟨W, hW⟩, (1 : unitInterval)))
          (Sum.inl (RWalk.nil (C := C) u)) := Or.inr ⟨rfl, hnil.symm⟩
      exact (Quotient.sound (Relation.EqvGen.rel _ _ hrel)).symm
    · have hk : ⌈((W.1.length - 1 : ℕ) : ℝ)⌉₊ = W.1.length - 1 := Nat.ceil_natCast _
      rw [truncW_of_ne_zero (by rw [hk]; omega) hW]
      have h0 : unitClamp (⌈((W.1.length - 1 : ℕ) : ℝ)⌉₊ - ((W.1.length - 1 : ℕ) : ℝ)) =
          (0 : unitInterval) := by
        rw [hk, sub_self, unitClamp_eq_zero le_rfl]
      rw [h0]
      have hrel : treeRel (C := C) u
          (Sum.inr (⟨W.take ⌈((W.1.length - 1 : ℕ) : ℝ)⌉₊,
            RWalk.take_ne_nil (by rw [hk]; omega) hW⟩, (0 : unitInterval)))
          (Sum.inl (W.take ⌈((W.1.length - 1 : ℕ) : ℝ)⌉₊)) := Or.inl ⟨rfl, rfl⟩
      refine (Quotient.sound (Relation.EqvGen.rel _ _ hrel)).trans ?_
      rw [hk, hd]
      exact h2.symm

/-- The truncation at the height of a naive point is that point, in the tree. -/
lemma mk_truncPt_heightPt (x : TreePt (C := C) u) :
    (Tree.mk (truncPt (C := C) (heightPt x) x) : Tree (C := C) u) = Tree.mk x := by
  rw [truncPt_eq_truncW]
  rcases x with W | ⟨⟨W, hW⟩, t⟩
  · exact mk_truncW_self_vertex W
  · exact mk_truncW_self_inr hW t

/-- The naive contraction of the universal cover onto its base vertex. -/
def contractPt : TreePt (C := C) u × unitInterval → Tree (C := C) u :=
  fun p => Tree.mk (truncPt (C := C) ((1 - (p.2 : ℝ)) * heightPt p.1) p.1)

/-- **The naive contraction is continuous.** -/
lemma continuous_contractPt : Continuous (contractPt (C := C) (u := u)) := by
  have key : Continuous (fun q : (RWalk (C := C) u × unitInterval) ⊕
      (({W : RWalk (C := C) u // W.1 ≠ []} × unitInterval) × unitInterval) =>
      contractPt (C := C) (u := u)
        ((Homeomorph.sumProdDistrib (X := RWalk (C := C) u)
          (Y := ({W : RWalk (C := C) u // W.1 ≠ []} × unitInterval))
          (Z := unitInterval)).symm q)) := by
    rw [continuous_sum_dom]
    constructor
    · change Continuous fun q : RWalk (C := C) u × unitInterval =>
        contractPt (C := C) (u := u) (Sum.inl q.1, q.2)
      rw [continuous_prod_of_discrete]
      intro W
      rcases eq_or_ne W (RWalk.nil (C := C) u) with rfl | hW
      · have hconst : (fun σ : unitInterval => contractPt (C := C) (u := u)
            (Sum.inl (RWalk.nil (C := C) u), σ)) =
            fun _ => Tree.vertex (RWalk.nil (C := C) u) := by
          funext σ
          show (Tree.mk (truncW (C := C) ((1 - (σ : ℝ)) * ((RWalk.nil (C := C) u).1.length : ℝ))
            (RWalk.nil (C := C) u)) : Tree (C := C) u) = Tree.vertex (RWalk.nil (C := C) u)
          rw [RWalk.nil_val, List.length_nil, Nat.cast_zero, mul_zero, truncW_zero]
          rfl
        rw [hconst]
        exact continuous_const
      · have hW' : W.1 ≠ [] := fun h => hW (Subtype.ext (by rw [h, RWalk.nil_val]))
        have hg : Continuous fun σ : unitInterval => (Tree.mk (truncW (C := C)
            ((1 - (σ : ℝ)) * ((W.1.length : ℝ) - ((0 : unitInterval) : ℝ))) W) :
              Tree (C := C) u) :=
          (continuous_geo (C := C) (u := u) hW').comp
            (continuous_const.prodMk continuous_id)
        convert hg using 1
        ext σ
        simp only [contractPt, truncPt_inl, heightPt_vertex]
        norm_num
    · change Continuous fun q : ({W : RWalk (C := C) u // W.1 ≠ []} × unitInterval) ×
          unitInterval => contractPt (C := C) (u := u) (Sum.inr q.1, q.2)
      rw [continuous_prod_prod_of_discrete]
      rintro ⟨W, hW⟩
      have hg := continuous_geo (C := C) (u := u) hW
      convert hg using 1
      ext p
      simp only [contractPt, truncPt_inr, heightPt]
  exact (Homeomorph.comp_continuous_iff' _).mp key


/-- Heights are nonnegative. -/
lemma heightPt_nonneg (x : TreePt (C := C) u) : 0 ≤ heightPt (C := C) x := by
  rcases x with W | ⟨⟨W, hW⟩, t⟩
  · exact Nat.cast_nonneg _
  · show 0 ≤ (W.1.length : ℝ) - (t : ℝ)
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have hL1 : (1 : ℝ) ≤ (W.1.length : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (RWalk.length_pos hW)
    linarith

/-- The contraction of the universal cover onto its base vertex. -/
def contract : Tree (C := C) u × unitInterval → Tree (C := C) u :=
  fun p => Quotient.lift
    (fun x : TreePt (C := C) u =>
      Tree.mk (truncPt (C := C) ((1 - (p.2 : ℝ)) * heightPt x) x))
    (fun x y h => by
      have hh : heightPt (C := C) y = heightPt (C := C) x := (heightPt_eqvGen h).symm
      have hσ : (1 - (p.2 : ℝ)) ≤ 1 := by linarith [p.2.2.1]
      have hle : (1 - (p.2 : ℝ)) * heightPt (C := C) x ≤ heightPt (C := C) x := by
        calc (1 - (p.2 : ℝ)) * heightPt (C := C) x ≤ 1 * heightPt (C := C) x :=
              mul_le_mul_of_nonneg_right hσ (heightPt_nonneg x)
          _ = heightPt (C := C) x := one_mul _
      rw [hh]
      exact congrArg Tree.mk (truncPt_eqvGen (C := C) h hle)) p.1

/-- The computation rule for the contraction. -/
lemma contract_mk (x : TreePt (C := C) u) (σ : unitInterval) :
    contract (C := C) (Quotient.mk (Relation.EqvGen.setoid (treeRel (C := C) u)) x, σ) =
      Tree.mk (truncPt (C := C) ((1 - (σ : ℝ)) * heightPt x) x) := rfl

/-- **The contraction is continuous.** -/
lemma continuous_contract : Continuous (contract (C := C) (u := u)) := by
  refine Topology.IsQuotientMap.continuous_lift_prod_left
    (f := fun x : TreePt (C := C) u => (Tree.mk x : Tree (C := C) u))
    isQuotientMap_quotient_mk' ?_
  have hfun : (fun p : TreePt (C := C) u × unitInterval =>
      contract (C := C) (Tree.mk p.1, p.2)) = contractPt (C := C) (u := u) := by
    funext p
    exact contract_mk p.1 p.2
  rw [hfun]
  exact continuous_contractPt

@[simp] lemma contract_zero (z : Tree (C := C) u) : contract (C := C) (z, 0) = z := by
  induction z using Quotient.inductionOn with
  | h x =>
      rw [contract_mk, show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, one_mul]
      exact mk_truncPt_heightPt x

@[simp] lemma contract_one (z : Tree (C := C) u) :
    contract (C := C) (z, 1) = Tree.vertex (RWalk.nil (C := C) u) := by
  induction z using Quotient.inductionOn with
  | h x =>
      rw [contract_mk, show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, zero_mul,
        truncPt_zero]
      rfl

/-- **The universal cover is contractible.** -/
instance contractibleSpace : ContractibleSpace (Tree (C := C) u) := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨Tree.vertex (RWalk.nil (C := C) u), ⟨?_⟩⟩
  refine
    { toFun := fun p : unitInterval × Tree (C := C) u => contract (C := C) (p.2, p.1)
      continuous_toFun := continuous_contract.comp continuous_swap
      map_zero_left := fun z => contract_zero z
      map_one_left := fun z => contract_one z }


/-! ## The lift of a walk to the universal cover -/

/-- The edge of the universal cover above the nonempty reduced walk `W`, as a path from `vertex W`
down to `vertex W.dropLast`. -/
def edgePath (W : RWalk (C := C) u) (hW : W.1 ≠ []) :
    Path (vertex W) (vertex W.dropLast) where
  toFun := fun t => ept W hW t
  continuous_toFun := continuous_ept W hW
  source' := ept_zero_eq_vertex W hW
  target' := ept_one_eq_vertex_dropLast W hW

/-- **The lift of a walk to the universal cover**, by recursion on the length: walk up the tree from
the base vertex, and for every nonempty prefix `W'` of `W` traverse the edge above `W'` from below.
The result is a path from the base vertex of the tree to `vertex W`. -/
def walkPathAux : (n : ℕ) → (W : RWalk (C := C) u) → W.1.length = n →
    Path (vertex (RWalk.nil (C := C) u)) (vertex W)
  | 0, W, h => (Path.refl (vertex (RWalk.nil (C := C) u))).cast rfl
      (congrArg (vertex (C := C) (u := u))
        (Subtype.ext (by rw [RWalk.nil_val]; exact List.length_eq_zero_iff.mp h)))
  | n + 1, W, h => by
      have hne : W.1 ≠ [] := by
        intro hc
        rw [hc, List.length_nil] at h
        omega
      have hlen : W.dropLast.1.length = n := by
        rw [RWalk.dropLast_val, List.length_dropLast, h]
        omega
      exact (walkPathAux n W.dropLast hlen).trans (edgePath W hne).symm

/-- The lift of a reduced walk to the universal cover. -/
def walkPath (W : RWalk (C := C) u) :
    Path (vertex (RWalk.nil (C := C) u)) (vertex W) :=
  walkPathAux W.1.length W rfl

@[simp] lemma walkPath_one (W : RWalk (C := C) u) : walkPath W 1 = vertex W :=
  Path.target _

@[simp] lemma walkPath_zero (W : RWalk (C := C) u) :
    walkPath W 0 = vertex (RWalk.nil (C := C) u) :=
  Path.source _


/-- The interior of the unit interval maps into the open ball under `segF`. -/
lemma segF_mem_ball {t : unitInterval} (h0 : 0 < (t : ℝ)) (h1 : (t : ℝ) < 1) :
    segF t ∈ Metric.ball (0 : Fin 1 → ℝ) 1 := by
  rw [Metric.mem_ball, dist_zero_right]
  simp only [Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sup_singleton, segF]
  rw [coe_nnnorm, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith

/-- A point in the interior of an edge of the one-skeleton lies in the corresponding open cell. -/
lemma OEdge.path_mem_openCell {o : OEdge (C := C)} {s : unitInterval}
    (h0 : 0 < (s : ℝ)) (h1 : (s : ℝ) < 1) :
    OEdge.path (C := C) o s ∈ Topology.RelCWComplex.openCell (C := C) 1 o.cell := by
  rcases o with ⟨e, d⟩
  cases d
  · show (fwdPath (C := C) e).symm s ∈ Topology.RelCWComplex.openCell (C := C) 1 e
    rw [Path.symm_apply]
    refine Set.mem_image_of_mem _ (segF_mem_ball ?_ ?_)
    · show (0 : ℝ) < ((unitInterval.symm s : unitInterval) : ℝ)
      show (0 : ℝ) < 1 - (s : ℝ)
      linarith
    · show (((unitInterval.symm s : unitInterval)) : ℝ) < 1
      show (1 : ℝ) - (s : ℝ) < 1
      linarith
  · show fwdPath (C := C) e s ∈ Topology.RelCWComplex.openCell (C := C) 1 e
    exact Set.mem_image_of_mem _ (segF_mem_ball h0 h1)



/-- **The first half of an edge.**  The image of the unit interval cut at `1/2` under the
characteristic path of `⟨e,true⟩` is the half of the closed ball cut out by `x 0 < 0`. -/
lemma fwdPath_image_left (e : Topology.CWComplex.cell C 1) :
    (fwdPath (C := C) e) '' {t : unitInterval | (t : ℝ) < 1 / 2} =
      Topology.RelCWComplex.map (C := C) 1 e ''
        (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩ {x : Fin 1 → ℝ | x 0 < 0}) := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [Set.mem_setOf_eq] at ht
    refine ⟨segF t, ⟨segF_mem t, ?_⟩, rfl⟩
    show 2 * (t : ℝ) - 1 < 0
    linarith
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    have hb : |x 0| ≤ 1 := by
      have h1 : ‖x‖ ≤ 1 := by simpa only [dist_zero_right] using Metric.mem_closedBall.mp hx.1
      simpa only [Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        Finset.sup_singleton, coe_nnnorm, Real.norm_eq_abs] using h1
    have h1 : -1 ≤ x 0 := (abs_le.mp hb).1
    have h2 : x 0 ≤ 1 := (abs_le.mp hb).2
    refine ⟨⟨(x 0 + 1) / 2, ⟨by linarith, by linarith⟩⟩, ?_, ?_⟩
    · show ((x 0 + 1) / 2 : ℝ) < 1 / 2
      linarith [hx.2]
    · show Topology.RelCWComplex.map (C := C) 1 e (segF _) =
        Topology.RelCWComplex.map (C := C) 1 e x
      congr 1
      funext i
      fin_cases i
      show 2 * ((x 0 + 1) / 2) - 1 = x 0
      ring


/-- The image of a general initial segment of the unit interval under the characteristic path. -/
lemma fwdPath_image_lt (e : Topology.CWComplex.cell C 1) (c : ℝ) :
    (fwdPath (C := C) e) '' {t : unitInterval | (t : ℝ) < c} =
      Topology.RelCWComplex.map (C := C) 1 e ''
        (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩ {x : Fin 1 → ℝ | x 0 < 2 * c - 1}) := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [Set.mem_setOf_eq] at ht
    refine ⟨segF t, ⟨segF_mem t, ?_⟩, rfl⟩
    show 2 * (t : ℝ) - 1 < 2 * c - 1
    linarith
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    have hb : |x 0| ≤ 1 := by
      have h1 : ‖x‖ ≤ 1 := by simpa only [dist_zero_right] using Metric.mem_closedBall.mp hx.1
      simpa only [Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        Finset.sup_singleton, coe_nnnorm, Real.norm_eq_abs] using h1
    have h1 : -1 ≤ x 0 := (abs_le.mp hb).1
    have h2 : x 0 ≤ 1 := (abs_le.mp hb).2
    refine ⟨⟨(x 0 + 1) / 2, ⟨by linarith, by linarith⟩⟩, ?_, ?_⟩
    · show ((x 0 + 1) / 2 : ℝ) < c
      linarith [hx.2]
    · show Topology.RelCWComplex.map (C := C) 1 e (segF _) =
        Topology.RelCWComplex.map (C := C) 1 e x
      congr 1
      funext i
      fin_cases i
      show 2 * ((x 0 + 1) / 2) - 1 = x 0
      ring


/-- The image of a general terminal segment of the unit interval under the characteristic path. -/
lemma fwdPath_image_gt (e : Topology.CWComplex.cell C 1) (c : ℝ) :
    (fwdPath (C := C) e) '' {t : unitInterval | c < (t : ℝ)} =
      Topology.RelCWComplex.map (C := C) 1 e ''
        (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩ {x : Fin 1 → ℝ | 2 * c - 1 < x 0}) := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [Set.mem_setOf_eq] at ht
    refine ⟨segF t, ⟨segF_mem t, ?_⟩, rfl⟩
    show 2 * c - 1 < 2 * (t : ℝ) - 1
    linarith
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    have hb : |x 0| ≤ 1 := by
      have h1 : ‖x‖ ≤ 1 := by simpa only [dist_zero_right] using Metric.mem_closedBall.mp hx.1
      simpa only [Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        Finset.sup_singleton, coe_nnnorm, Real.norm_eq_abs] using h1
    have h1 : -1 ≤ x 0 := (abs_le.mp hb).1
    have h2 : x 0 ≤ 1 := (abs_le.mp hb).2
    refine ⟨⟨(x 0 + 1) / 2, ⟨by linarith, by linarith⟩⟩, ?_, ?_⟩
    · show c < ((x 0 + 1) / 2 : ℝ)
      linarith [hx.2]
    · show Topology.RelCWComplex.map (C := C) 1 e (segF _) =
        Topology.RelCWComplex.map (C := C) 1 e x
      congr 1
      funext i
      fin_cases i
      show 2 * ((x 0 + 1) / 2) - 1 = x 0
      ring

/-- The symmetry of the unit interval sends initial segments to terminal segments. -/
lemma symm_image_lt (c : ℝ) :
    unitInterval.symm '' {t : unitInterval | (t : ℝ) < c} =
      {t : unitInterval | 1 - c < (t : ℝ)} := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    simp only [Set.mem_setOf_eq] at hs ⊢
    rw [unitInterval.coe_symm_eq]
    linarith
  · intro ht
    refine ⟨unitInterval.symm t, ?_, unitInterval.symm_symm t⟩
    simp only [Set.mem_setOf_eq] at ht ⊢
    rw [unitInterval.coe_symm_eq]
    linarith

/-- The image of a general initial segment of the unit interval under the reversed characteristic
path. -/
lemma fwdPath_symm_image_lt (e : Topology.CWComplex.cell C 1) (c : ℝ) :
    ((fwdPath (C := C) e).symm) '' {t : unitInterval | (t : ℝ) < c} =
      Topology.RelCWComplex.map (C := C) 1 e ''
        (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩ {x : Fin 1 → ℝ | 2 * (1 - c) - 1 < x 0}) := by
  rw [show (fwdPath (C := C) e).symm = (fwdPath (C := C) e) ∘ unitInterval.symm from rfl,
    Set.image_comp, symm_image_lt, fwdPath_image_gt]

/-- The same description of the reversed initial segment, with the cut in the form that matches the
condition on the *negated* coordinate. -/
lemma fwdPath_symm_image_lt' (e : Topology.CWComplex.cell C 1) (c : ℝ) :
    ((fwdPath (C := C) e).symm) '' {t : unitInterval | (t : ℝ) < c} =
      Topology.RelCWComplex.map (C := C) 1 e ''
        (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩ {y : Fin 1 → ℝ | -(y 0) < 2 * c - 1}) := by
  rw [fwdPath_symm_image_lt]
  congr 1
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith [h2]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith [h2]⟩

/-- **The second half of an edge.**  The image of the unit interval cut at `1/2` under the
characteristic path of `⟨e,true⟩` is the half of the closed ball cut out by `0 < x 0`. -/
lemma fwdPath_image_right (e : Topology.CWComplex.cell C 1) :
    (fwdPath (C := C) e) '' {t : unitInterval | (1 : ℝ) / 2 < (t : ℝ)} =
      Topology.RelCWComplex.map (C := C) 1 e ''
        (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩ {x : Fin 1 → ℝ | 0 < x 0}) := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [Set.mem_setOf_eq] at ht
    refine ⟨segF t, ⟨segF_mem t, ?_⟩, rfl⟩
    show 0 < 2 * (t : ℝ) - 1
    linarith
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    have hb : |x 0| ≤ 1 := by
      have h1 : ‖x‖ ≤ 1 := by simpa only [dist_zero_right] using Metric.mem_closedBall.mp hx.1
      simpa only [Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        Finset.sup_singleton, coe_nnnorm, Real.norm_eq_abs] using h1
    have h1 : -1 ≤ x 0 := (abs_le.mp hb).1
    have h2 : x 0 ≤ 1 := (abs_le.mp hb).2
    refine ⟨⟨(x 0 + 1) / 2, ⟨by linarith, by linarith⟩⟩, ?_, ?_⟩
    · show (1 : ℝ) / 2 < (x 0 + 1) / 2
      linarith [hx.2]
    · show Topology.RelCWComplex.map (C := C) 1 e (segF _) =
        Topology.RelCWComplex.map (C := C) 1 e x
      congr 1
      funext i
      fin_cases i
      show 2 * ((x 0 + 1) / 2) - 1 = x 0
      ring

/-- **The half-star of a vertex of a one-dimensional CW complex**: the vertex together with half
of every edge incident to it, the half being the one on the side of the vertex.  It is described
through the characteristic paths of the oriented edges. -/
def halfStar (v : Topology.CWComplex.cell C 0) : Set Y :=
  {vpt (C := C) v} ∪ ⋃ (o : OEdge (C := C)) (_ : o.src = v),
    (OEdge.path (C := C) o) '' {t : unitInterval | (t : ℝ) < 1 / 2}



/-- A `0`-cell of a one-dimensional CW complex is never in the open cell of a `1`-cell. -/
lemma vpt_not_mem_openCell_one (w : Topology.CWComplex.cell C 0)
    (e : Topology.CWComplex.cell C 1) :
    vpt (C := C) w ∉ Topology.RelCWComplex.openCell (C := C) 1 e := by
  intro h
  have h0 : vpt (C := C) w ∈ Topology.RelCWComplex.openCell (C := C) 0 w := by
    rw [Topology.RelCWComplex.openCell_zero_eq_singleton]; exact Set.mem_singleton _
  have hd := Topology.RelCWComplex.disjoint_openCell_of_ne (C := C) (n := 0) (m := 1)
    (i := w) (j := e) (by intro hh; exact absurd (Sigma.mk.inj hh).1 (by omega))
  exact Set.disjoint_left.mp hd h0 h

/-- The norm of the parametrisation of the closed unit ball. -/
lemma segF_norm (t : unitInterval) : ‖segF t‖ = |2 * (t : ℝ) - 1| := by
  simp only [Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sup_singleton, segF, coe_nnnorm, Real.norm_eq_abs]

/-- If the parametrisation of the closed ball lands on the sphere, the parameter is an endpoint. -/
lemma segF_eq_endpoints_of_mem_sphere {t : unitInterval}
    (h : segF t ∈ Metric.sphere (0 : Fin 1 → ℝ) 1) : (t : ℝ) = 0 ∨ (t : ℝ) = 1 := by
  rw [Metric.mem_sphere, dist_zero_right, segF_norm, abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at h
  rcases h with h | h
  · right; linarith
  · left; linarith

/-- If the parametrisation of the closed ball is not in the open ball, it is on the sphere. -/
lemma segF_mem_sphere_of_notMem_ball {t : unitInterval}
    (h : segF t ∉ Metric.ball (0 : Fin 1 → ℝ) 1) : segF t ∈ Metric.sphere (0 : Fin 1 → ℝ) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  have h1 := Metric.mem_closedBall.mp (segF_mem t)
  rw [dist_zero_right] at h1
  have h2 : ¬ ‖segF t‖ < 1 := fun hc =>
    h (by simpa only [Metric.mem_ball, dist_zero_right] using hc)
  linarith

/-- The path of an oriented edge in the positive direction is the characteristic path. -/
@[simp] lemma path_mk_true (e : Topology.CWComplex.cell C 1) :
    OEdge.path (C := C) ⟨e, true⟩ = fwdPath (C := C) e := by
  simp only [OEdge.path]
  rfl

/-- The path of an oriented edge in the negative direction is the reverse characteristic path. -/
@[simp] lemma path_mk_false (e : Topology.CWComplex.cell C 1) :
    OEdge.path (C := C) ⟨e, false⟩ = (fwdPath (C := C) e).symm := by
  simp only [OEdge.path]
  rfl

/-- The first half of an edge meets the vertex set only in the image of the source. -/
lemma fwdPath_image_left_vertex {e : Topology.CWComplex.cell C 1}
    {w : Topology.CWComplex.cell C 0} {t : unitInterval} (ht : (t : ℝ) < 1 / 2)
    (h : fwdPath (C := C) e t = vpt (C := C) w) :
    vpt (C := C) w = vpt (C := C) (srcIdx (C := C) e) := by
  by_cases hb : segF t ∈ Metric.ball (0 : Fin 1 → ℝ) 1
  · exact absurd (h ▸ Set.mem_image_of_mem _ hb) (vpt_not_mem_openCell_one w e)
  · have hs := segF_mem_sphere_of_notMem_ball hb
    have h0 := segF_eq_endpoints_of_mem_sphere hs
    have hz : (t : ℝ) = 0 := by rcases h0 with h0 | h0; exact h0; linarith
    have ht0 : t = 0 := Subtype.ext hz
    have h' : Topology.RelCWComplex.map (C := C) 1 e (segF (0 : unitInterval)) =
        vpt (C := C) w := by rw [ht0] at h; exact h
    rw [segF_zero] at h'
    rw [← h', map_one_neg_one_eq_srcIdx]

/-- The first half of the reversed edge meets the vertex set only in the image of the target. -/
lemma fwdPath_symm_image_left_vertex {e : Topology.CWComplex.cell C 1}
    {w : Topology.CWComplex.cell C 0} {t : unitInterval} (ht : (t : ℝ) < 1 / 2)
    (h : (fwdPath (C := C) e).symm t = vpt (C := C) w) :
    vpt (C := C) w = vpt (C := C) (tgtIdx (C := C) e) := by
  have h2 : fwdPath (C := C) e (unitInterval.symm t) = vpt (C := C) w := h
  by_cases hb : segF (unitInterval.symm t) ∈ Metric.ball (0 : Fin 1 → ℝ) 1
  · exact absurd (h2 ▸ Set.mem_image_of_mem _ hb) (vpt_not_mem_openCell_one w e)
  · have hs := segF_mem_sphere_of_notMem_ball hb
    have h0 := segF_eq_endpoints_of_mem_sphere hs
    rw [unitInterval.coe_symm_eq] at h0
    have hz : (t : ℝ) = 0 := by rcases h0 with h0 | h0; linarith; linarith
    have ht0 : t = 0 := Subtype.ext hz
    have hσ : unitInterval.symm (0 : unitInterval) = 1 := by
      apply Subtype.ext; rw [unitInterval.coe_symm_eq]; norm_num
    have h' : Topology.RelCWComplex.map (C := C) 1 e (segF (1 : unitInterval)) =
        vpt (C := C) w := by rw [ht0, hσ] at h2; exact h2
    rw [segF_one] at h'
    rw [← h', map_one_one_eq_tgtIdx]

/-- The image of the first half of an edge meets the vertex set only in the source vertex. -/
lemma path_image_left_subset (o : OEdge (C := C)) {w : Topology.CWComplex.cell C 0}
    (h : vpt (C := C) w ∈ (OEdge.path (C := C) o) '' {t : unitInterval | (t : ℝ) < 1 / 2}) :
    vpt (C := C) w = vpt (C := C) o.src := by
  obtain ⟨t, ht, ht'⟩ := h
  simp only [Set.mem_setOf_eq] at ht
  rcases o with ⟨e, b⟩
  cases b
  · rw [path_mk_false] at ht'
    exact fwdPath_symm_image_left_vertex (C := C) ht ht'
  · rw [path_mk_true] at ht'
    exact fwdPath_image_left_vertex (C := C) ht ht'

/-- **The only vertex in the half-star of `v` is `v` itself.** -/
lemma eq_of_vpt_mem_halfStar {v w : Topology.CWComplex.cell C 0}
    (h : vpt (C := C) w ∈ halfStar (C := C) v) : w = v := by
  rw [halfStar] at h
  rcases h with h | h
  · rw [Set.mem_singleton_iff] at h
    exact vpt_injective h
  · rw [Set.mem_iUnion] at h
    obtain ⟨o, h⟩ := h
    rw [Set.mem_iUnion] at h
    obtain ⟨ho, h⟩ := h
    have hp := path_image_left_subset o h
    rw [ho] at hp
    exact vpt_injective hp


/-- The boundary of a `1`-cell consists of the two end vertices. -/
lemma cellFrontier_one_subset (j : Topology.CWComplex.cell C 1) :
    Topology.RelCWComplex.cellFrontier (C := C) 1 j ⊆
      {vpt (C := C) (srcIdx (C := C) j), vpt (C := C) (tgtIdx (C := C) j)} := by
  intro y hy
  rw [Topology.RelCWComplex.cellFrontier_one_eq] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact Or.inl (map_one_neg_one_eq_srcIdx (C := C) j)
  · exact Or.inr (map_one_one_eq_tgtIdx (C := C) j)

/-- Reversing the unit interval turns the first half into the second half. -/
lemma symm_image_Ico :
    unitInterval.symm '' {t : unitInterval | (t : ℝ) < 1 / 2} =
      {t : unitInterval | (1 : ℝ) / 2 < (t : ℝ)} := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    simp only [Set.mem_setOf_eq] at hs ⊢
    rw [unitInterval.coe_symm_eq]
    linarith
  · intro ht
    refine ⟨unitInterval.symm t, ?_, unitInterval.symm_symm t⟩
    simp only [Set.mem_setOf_eq] at ht ⊢
    rw [unitInterval.coe_symm_eq]
    linarith

/-- The first half of a reversed edge is the second half of the edge. -/
lemma fwdPath_symm_image_left (e : Topology.CWComplex.cell C 1) :
    ((fwdPath (C := C) e).symm) '' {t : unitInterval | (t : ℝ) < 1 / 2} =
      Topology.RelCWComplex.map (C := C) 1 e ''
        (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩ {x : Fin 1 → ℝ | 0 < x 0}) := by
  rw [show (fwdPath (C := C) e).symm = (fwdPath (C := C) e) ∘ unitInterval.symm from rfl,
    Set.image_comp, symm_image_Ico, fwdPath_image_right]

/-- The two halves of an edge, described with the characteristic map. -/
lemma OEdge_path_image_left (o : OEdge (C := C)) :
    (OEdge.path (C := C) o) '' {t : unitInterval | (t : ℝ) < 1 / 2} =
      (if o.dir then
        Topology.RelCWComplex.map (C := C) 1 o.cell ''
          (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩ {x : Fin 1 → ℝ | x 0 < 0})
      else
        Topology.RelCWComplex.map (C := C) 1 o.cell ''
          (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩ {x : Fin 1 → ℝ | 0 < x 0})) := by
  rcases o with ⟨e, b⟩
  cases b
  · show (OEdge.path (C := C) ⟨e, false⟩) '' {t : unitInterval | (t : ℝ) < 1 / 2} =
      Topology.RelCWComplex.map (C := C) 1 e ''
        (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩ {x : Fin 1 → ℝ | 0 < x 0})
    rw [path_mk_false]
    exact fwdPath_symm_image_left e
  · show (OEdge.path (C := C) ⟨e, true⟩) '' {t : unitInterval | (t : ℝ) < 1 / 2} =
      Topology.RelCWComplex.map (C := C) 1 e ''
        (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩ {x : Fin 1 → ℝ | x 0 < 0})
    rw [path_mk_true]
    exact fwdPath_image_left e

/-- The first half of an edge lies in the closed cell of that edge. -/
lemma path_image_left_subset_closedCell (o : OEdge (C := C)) :
    (OEdge.path (C := C) o) '' {t : unitInterval | (t : ℝ) < 1 / 2} ⊆
      Topology.RelCWComplex.closedCell (C := C) 1 o.cell := by
  rw [OEdge_path_image_left]
  split_ifs
  · exact Set.image_mono Set.inter_subset_left
  · exact Set.image_mono Set.inter_subset_left

/-- The first half of an edge does not meet the open cell of a different edge. -/
lemma path_image_left_disjoint_openCell (o : OEdge (C := C)) (j : Topology.CWComplex.cell C 1)
    (h : o.cell ≠ j) :
    Disjoint ((OEdge.path (C := C) o) '' {t : unitInterval | (t : ℝ) < 1 / 2})
      (Topology.RelCWComplex.openCell (C := C) 1 j) := by
  rw [Set.disjoint_left]
  intro y hy hoj
  have h1 := path_image_left_subset_closedCell o hy
  rw [← Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell] at h1
  rcases h1 with h1 | h1
  · have h2 := cellFrontier_one_subset o.cell h1
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
    rcases h2 with h2 | h2
    · rw [h2] at hoj; exact vpt_not_mem_openCell_one _ j hoj
    · rw [h2] at hoj; exact vpt_not_mem_openCell_one _ j hoj
  · exact Set.disjoint_left.mp (Topology.RelCWComplex.disjoint_openCell_of_ne (C := C)
      (by intro hh; exact h (eq_of_heq (Sigma.mk.inj hh).2))) h1 hoj


/-- Points of the unit sphere of `Fin 1 → ℝ` are the two endpoints. -/
lemma eq_neg_one_or_one_of_mem_sphere {x : Fin 1 → ℝ}
    (h : x ∈ Metric.sphere (0 : Fin 1 → ℝ) 1) : x = -1 ∨ x = 1 := by
  rw [Metric.mem_sphere, dist_zero_right] at h
  have h1 : |x 0| = 1 := by
    simpa only [Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sup_singleton, coe_nnnorm, Real.norm_eq_abs] using h
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h1 with h2 | h2
  · right; funext i; fin_cases i; exact h2
  · left; funext i; fin_cases i; exact h2

/-- A point of the closed unit ball is either in the open ball or one of the two endpoints. -/
lemma ball_or_eq_neg_one_or_one {x : Fin 1 → ℝ}
    (hx : x ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1) :
    x ∈ Metric.ball (0 : Fin 1 → ℝ) 1 ∨ x = -1 ∨ x = 1 := by
  by_cases hb : x ∈ Metric.ball (0 : Fin 1 → ℝ) 1
  · exact Or.inl hb
  · have h1 := Metric.mem_closedBall.mp hx
    rw [dist_zero_right] at h1
    have h2 : ¬ ‖x‖ < 1 := fun hc =>
      hb (by simpa only [Metric.mem_ball, dist_zero_right] using hc)
    have hs : x ∈ Metric.sphere (0 : Fin 1 → ℝ) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]; linarith
    rcases eq_neg_one_or_one_of_mem_sphere hs with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)


/-- **A point of the half of an edge on the side of `v` projects into the half-star of `v`.** -/
lemma mem_halfStar_of_half {j : Topology.CWComplex.cell C 1} {v : Topology.CWComplex.cell C 0}
    {x : Fin 1 → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1)
    (h : (srcIdx (C := C) j = v ∧ x 0 < 0) ∨ (tgtIdx (C := C) j = v ∧ 0 < x 0)) :
    Topology.RelCWComplex.map (C := C) 1 j x ∈ halfStar (C := C) v := by
  rcases h with ⟨hv, hx0⟩ | ⟨hv, hx0⟩
  · have hmem : Topology.RelCWComplex.map (C := C) 1 j x ∈
        (fwdPath (C := C) j) '' {t : unitInterval | (t : ℝ) < 1 / 2} := by
      rw [fwdPath_image_left]
      exact ⟨x, ⟨hx, hx0⟩, rfl⟩
    rw [halfStar]
    refine Or.inr (Set.mem_iUnion.mpr ⟨⟨j, true⟩, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩)
    · exact hv
    · rw [path_mk_true]
      exact hmem
  · have hmem : Topology.RelCWComplex.map (C := C) 1 j x ∈
        ((fwdPath (C := C) j).symm) '' {t : unitInterval | (t : ℝ) < 1 / 2} := by
      rw [fwdPath_symm_image_left]
      exact ⟨x, ⟨hx, hx0⟩, rfl⟩
    rw [halfStar]
    refine Or.inr (Set.mem_iUnion.mpr ⟨⟨j, false⟩, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩)
    · exact hv
    · rw [path_mk_false]
      exact hmem

/-- **Inside the open cell of `j`, the half-star of `v` meets the half of `j` on the side of
`v`.** -/
lemma mem_half_of_mem_map_half {j : Topology.CWComplex.cell C 1} {v : Topology.CWComplex.cell C 0}
    {x : Fin 1 → ℝ} (hx : x ∈ Metric.ball (0 : Fin 1 → ℝ) 1)
    (hmem : Topology.RelCWComplex.map (C := C) 1 j x ∈ halfStar (C := C) v) :
    (srcIdx (C := C) j = v ∧ x 0 < 0) ∨ (tgtIdx (C := C) j = v ∧ 0 < x 0) := by
  have hoj : Topology.RelCWComplex.map (C := C) 1 j x ∈
      Topology.RelCWComplex.openCell (C := C) 1 j := Set.mem_image_of_mem _ hx
  rw [halfStar] at hmem
  rcases hmem with hmem | hmem
  · rw [Set.mem_singleton_iff] at hmem
    exact absurd (hmem ▸ hoj) (vpt_not_mem_openCell_one v j)
  · rw [Set.mem_iUnion] at hmem
    obtain ⟨o, hmem⟩ := hmem
    rw [Set.mem_iUnion] at hmem
    obtain ⟨ho, hmem⟩ := hmem
    obtain ⟨c, b⟩ := o
    have hcell : c = j := by
      by_contra hc
      exact Set.disjoint_left.mp (path_image_left_disjoint_openCell ⟨c, b⟩ j hc) hmem hoj
    rw [hcell] at hmem ho
    rw [OEdge_path_image_left] at hmem
    cases b
    · rw [if_neg (by simp : ¬ (OEdge.dir ⟨j, false⟩ = true))] at hmem
      obtain ⟨x', hx', hx''⟩ := hmem
      rw [Set.mem_inter_iff, Set.mem_setOf_eq] at hx'
      have hxball : x' ∈ Metric.ball (0 : Fin 1 → ℝ) 1 := by
        rcases ball_or_eq_neg_one_or_one hx'.1 with hb' | hb' | hb'
        · exact hb'
        · rw [hb', map_one_neg_one_eq_srcIdx] at hx''
          exact absurd (hx'' ▸ hoj) (vpt_not_mem_openCell_one (srcIdx (C := C) j) j)
        · rw [hb', map_one_one_eq_tgtIdx] at hx''
          exact absurd (hx'' ▸ hoj) (vpt_not_mem_openCell_one (tgtIdx (C := C) j) j)
      have hxx : x' = x := RelCWComplex.injOn_map_ball 1 j hxball hx hx''
      rw [hxx] at hx'
      exact Or.inr ⟨ho, hx'.2⟩
    · rw [if_pos (by simp : OEdge.dir ⟨j, true⟩ = true)] at hmem
      obtain ⟨x', hx', hx''⟩ := hmem
      rw [Set.mem_inter_iff, Set.mem_setOf_eq] at hx'
      have hxball : x' ∈ Metric.ball (0 : Fin 1 → ℝ) 1 := by
        rcases ball_or_eq_neg_one_or_one hx'.1 with hb' | hb' | hb'
        · exact hb'
        · rw [hb', map_one_neg_one_eq_srcIdx] at hx''
          exact absurd (hx'' ▸ hoj) (vpt_not_mem_openCell_one (srcIdx (C := C) j) j)
        · rw [hb', map_one_one_eq_tgtIdx] at hx''
          exact absurd (hx'' ▸ hoj) (vpt_not_mem_openCell_one (tgtIdx (C := C) j) j)
      have hxx : x' = x := RelCWComplex.injOn_map_ball 1 j hxball hx hx''
      rw [hxx] at hx'
      exact Or.inl ⟨ho, hx'.2⟩

/-- **The "far" part of an edge is disjoint from the half-star of the near endpoint.** -/
lemma not_mem_halfStar {j : Topology.CWComplex.cell C 1} {v : Topology.CWComplex.cell C 0}
    {x : Fin 1 → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1)
    (h1 : srcIdx (C := C) j = v → 0 ≤ x 0) (h2 : tgtIdx (C := C) j = v → x 0 ≤ 0) :
    Topology.RelCWComplex.map (C := C) 1 j x ∉ halfStar (C := C) v := by
  intro hmem
  rcases ball_or_eq_neg_one_or_one hx with hb | hb | hb
  · rcases mem_half_of_mem_map_half hb hmem with ⟨hv, hx0⟩ | ⟨hv, hx0⟩
    · linarith [h1 hv, hx0]
    · linarith [h2 hv, hx0]
  · have hv : srcIdx (C := C) j = v := by
      rw [hb] at hmem
      rw [map_one_neg_one_eq_srcIdx] at hmem
      exact eq_of_vpt_mem_halfStar hmem
    have h0 := h1 hv
    rw [hb] at h0
    norm_num at h0
  · have hv : tgtIdx (C := C) j = v := by
      rw [hb] at hmem
      rw [map_one_one_eq_tgtIdx] at hmem
      exact eq_of_vpt_mem_halfStar hmem
    have h0 := h2 hv
    rw [hb] at h0
    norm_num at h0



lemma vpt_mem_halfStar (v : Topology.CWComplex.cell C 0) :
    vpt (C := C) v ∈ halfStar (C := C) v := Or.inl rfl


/-- **The half-star of a vertex of a one-dimensional CW complex is open.** -/
theorem isOpen_halfStar {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n))
    (v : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    IsOpen (halfStar (C := (Set.univ : Set X)) v) := by
  rw [← isClosed_compl_iff]
  refine Topology.CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    (C := (Set.univ : Set X)) (by intro y hy; trivial) ?_
  intro n hn j
  right
  rcases n with _ | _ | m
  · rw [Topology.RelCWComplex.closedCell_zero_eq_singleton]
    by_cases hj : j = v
    · have hemp : (halfStar (C := (Set.univ : Set X)) v)ᶜ ∩
          {Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 j ![]} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro y hy
        refine hy.1 ?_
        rw [hy.2, hj]
        exact vpt_mem_halfStar (C := (Set.univ : Set X)) v
      rw [hemp]
      exact isClosed_empty
    · have hnot : Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 j ![] ∉
          halfStar (C := (Set.univ : Set X)) v := fun h =>
        hj (eq_of_vpt_mem_halfStar (C := (Set.univ : Set X)) (v := v) h)
      have hsingle : (halfStar (C := (Set.univ : Set X)) v)ᶜ ∩
          {Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 j ![]} =
          {Topology.RelCWComplex.map (C := (Set.univ : Set X)) 0 j ![]} := by
        rw [Set.inter_eq_right, Set.singleton_subset_iff]
        exact hnot
      rw [hsingle]
      exact isClosed_singleton
  · classical
    set K : Set (Fin 1 → ℝ) :=
      Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩
        (if srcIdx (C := (Set.univ : Set X)) j = v then
          {y : Fin 1 → ℝ | 0 ≤ y 0} else Set.univ) ∩
        (if tgtIdx (C := (Set.univ : Set X)) j = v then
          {y : Fin 1 → ℝ | y 0 ≤ 0} else Set.univ) with hK
    have hKclosed : IsClosed K := by
      rw [hK]
      refine IsClosed.inter (IsClosed.inter Metric.isClosed_closedBall ?_) ?_
      · split_ifs
        · exact isClosed_le continuous_const (continuous_apply 0)
        · exact isClosed_univ
      · split_ifs
        · exact isClosed_le (continuous_apply 0) continuous_const
        · exact isClosed_univ
    have hKsub : K ⊆ Metric.closedBall (0 : Fin 1 → ℝ) 1 := by
      rw [hK]; exact fun y hy => hy.1.1
    have hKcompact : IsCompact K :=
      IsCompact.of_isClosed_subset (ProperSpace.isCompact_closedBall (0 : Fin 1 → ℝ) 1)
        hKclosed hKsub
    have hset : (halfStar (C := (Set.univ : Set X)) v)ᶜ ∩
        Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) 1 j =
        Topology.RelCWComplex.map (C := (Set.univ : Set X)) 1 j '' K := by
      ext y
      constructor
      · rintro ⟨hy1, hy2⟩
        obtain ⟨x, hx, rfl⟩ := hy2
        refine ⟨x, ?_, rfl⟩
        rw [hK]
        refine ⟨⟨hx, ?_⟩, ?_⟩
        · by_cases hc : srcIdx (C := (Set.univ : Set X)) j = v
          · rw [if_pos hc]
            by_contra hlt
            rw [Set.mem_setOf_eq, not_le] at hlt
            exact hy1 (mem_halfStar_of_half (C := (Set.univ : Set X)) hx (Or.inl ⟨hc, hlt⟩))
          · rw [if_neg hc]
            exact trivial
        · by_cases hc : tgtIdx (C := (Set.univ : Set X)) j = v
          · rw [if_pos hc]
            by_contra hlt
            rw [Set.mem_setOf_eq, not_le] at hlt
            exact hy1 (mem_halfStar_of_half (C := (Set.univ : Set X)) hx (Or.inr ⟨hc, hlt⟩))
          · rw [if_neg hc]
            exact trivial
      · rintro ⟨x, hxK, rfl⟩
        refine ⟨?_, Set.mem_image_of_mem _ (hKsub hxK)⟩
        rw [hK] at hxK
        obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hxK
        refine not_mem_halfStar (C := (Set.univ : Set X)) hx1 ?_ ?_
        · intro hc
          rw [if_pos hc] at hx2
          exact hx2
        · intro hc
          rw [if_pos hc] at hx3
          exact hx3
    rw [hset]
    exact (hKcompact.image_of_continuousOn
      ((Topology.RelCWComplex.continuousOn (C := (Set.univ : Set X)) 1 j).mono hKsub)).isClosed
  · exact ((h2 (m + 2) (by omega)).false j).elim

/-! ## The star with prescribed radii -/

/-- The star of a vertex with prescribed radii, one for each orientation of each incident cell. -/
def epsStar (v : Topology.CWComplex.cell C 0)
    (δt δf : Topology.CWComplex.cell C 1 → unitInterval) : Set Y :=
  {vpt (C := C) v} ∪
    ((⋃ (e : Topology.CWComplex.cell C 1) (_ : srcIdx (C := C) e = v),
        (fwdPath (C := C) e) '' {t : unitInterval | (t : ℝ) < (δt e : ℝ)}) ∪
      (⋃ (e : Topology.CWComplex.cell C 1) (_ : tgtIdx (C := C) e = v),
        ((fwdPath (C := C) e).symm) '' {t : unitInterval | (t : ℝ) < (δf e : ℝ)}))

lemma mem_epsStar_of_lt {v : Topology.CWComplex.cell C 0}
    {δt δf : Topology.CWComplex.cell C 1 → unitInterval} {j : Topology.CWComplex.cell C 1}
    {x : Fin 1 → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1)
    (h : (srcIdx (C := C) j = v ∧ x 0 < 2 * (δt j : ℝ) - 1) ∨
         (tgtIdx (C := C) j = v ∧ -(x 0) < 2 * (δf j : ℝ) - 1)) :
    Topology.RelCWComplex.map (C := C) 1 j x ∈ epsStar (C := C) v δt δf := by
  rcases h with ⟨hv, hx0⟩ | ⟨hv, hx0⟩
  · refine Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hv, ?_⟩⟩))
    have hmem : Topology.RelCWComplex.map (C := C) 1 j x ∈
        Topology.RelCWComplex.map (C := C) 1 j ''
          (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩
            {y : Fin 1 → ℝ | y 0 < 2 * (δt j : ℝ) - 1}) :=
      ⟨x, ⟨hx, hx0⟩, rfl⟩
    rw [fwdPath_image_lt]
    exact hmem
  · refine Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hv, ?_⟩⟩))
    have hmem : Topology.RelCWComplex.map (C := C) 1 j x ∈
        Topology.RelCWComplex.map (C := C) 1 j ''
          (Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩
            {y : Fin 1 → ℝ | -(y 0) < 2 * (δf j : ℝ) - 1}) :=
      ⟨x, ⟨hx, hx0⟩, rfl⟩
    rw [fwdPath_symm_image_lt']
    exact hmem

lemma eq_of_vpt_mem_epsStar {v w : Topology.CWComplex.cell C 0}
    {δt δf : Topology.CWComplex.cell C 1 → unitInterval}
    (hδt : ∀ e, (δt e : ℝ) < 1 / 2) (hδf : ∀ e, (δf e : ℝ) < 1 / 2)
    (h : vpt (C := C) w ∈ epsStar (C := C) v δt δf) : w = v := by
  rw [epsStar] at h
  rcases h with h | h | h
  · rw [Set.mem_singleton_iff] at h
    exact vpt_injective h
  · rw [Set.mem_iUnion] at h
    obtain ⟨e, h⟩ := h
    rw [Set.mem_iUnion] at h
    obtain ⟨he, h⟩ := h
    obtain ⟨t, ht, htx⟩ := h
    have hsub : vpt (C := C) w ∈ (fwdPath (C := C) e) '' {t : unitInterval | (t : ℝ) < 1 / 2} :=
      ⟨t, lt_trans ht (hδt e), htx⟩
    obtain ⟨r, hr, hrx⟩ := hsub
    have hw : w = srcIdx (C := C) e := vpt_injective (fwdPath_image_left_vertex (C := C) hr hrx)
    rw [hw, he]
  · rw [Set.mem_iUnion] at h
    obtain ⟨e, h⟩ := h
    rw [Set.mem_iUnion] at h
    obtain ⟨he, h⟩ := h
    obtain ⟨t, ht, htx⟩ := h
    have hsub : vpt (C := C) w ∈
        ((fwdPath (C := C) e).symm) '' {t : unitInterval | (t : ℝ) < 1 / 2} :=
      ⟨t, lt_trans ht (hδf e), htx⟩
    obtain ⟨r, hr, hrx⟩ := hsub
    have hw : w = tgtIdx (C := C) e :=
      vpt_injective (fwdPath_symm_image_left_vertex (C := C) hr hrx)
    rw [hw, he]

lemma not_mem_epsStar {v : Topology.CWComplex.cell C 0}
    {δt δf : Topology.CWComplex.cell C 1 → unitInterval}
    (hδt : ∀ e, (δt e : ℝ) < 1 / 2) (hδf : ∀ e, (δf e : ℝ) < 1 / 2)
    (hδtp : ∀ e, srcIdx (C := C) e = v → 0 < (δt e : ℝ))
    (hδfp : ∀ e, tgtIdx (C := C) e = v → 0 < (δf e : ℝ))
    {j : Topology.CWComplex.cell C 1} {x : Fin 1 → ℝ}
    (hx : x ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1)
    (h1 : srcIdx (C := C) j = v → 2 * (δt j : ℝ) - 1 ≤ x 0)
    (h2 : tgtIdx (C := C) j = v → 2 * (δf j : ℝ) - 1 ≤ -(x 0)) :
    Topology.RelCWComplex.map (C := C) 1 j x ∉ epsStar (C := C) v δt δf := by
  intro hmem
  rcases ball_or_eq_neg_one_or_one hx with hb | hb | hb
  · have hoj : Topology.RelCWComplex.map (C := C) 1 j x ∈
        Topology.RelCWComplex.openCell (C := C) 1 j := Set.mem_image_of_mem _ hb
    rw [epsStar] at hmem
    rcases hmem with hmem | hmem | hmem
    · rw [Set.mem_singleton_iff] at hmem
      exact vpt_not_mem_openCell_one (C := C) v j (hmem ▸ hoj)
    · rw [Set.mem_iUnion] at hmem
      obtain ⟨e, hmem⟩ := hmem
      rw [Set.mem_iUnion] at hmem
      obtain ⟨he, hmem⟩ := hmem
      obtain ⟨s, hs, hsx⟩ := hmem
      have hsub : Topology.RelCWComplex.map (C := C) 1 j x ∈
          (OEdge.path (C := C) ⟨e, true⟩) '' {t : unitInterval | (t : ℝ) < 1 / 2} := by
        rw [path_mk_true]
        exact ⟨s, lt_trans hs (hδt e), hsx⟩
      have hej : e = j := by
        by_contra hc
        exact Set.disjoint_left.mp
          (path_image_left_disjoint_openCell (C := C) ⟨e, true⟩ j (by simpa using hc)) hsub hoj
      have hmem2 : Topology.RelCWComplex.map (C := C) 1 j x ∈
          (fwdPath (C := C) j) '' {t : unitInterval | (t : ℝ) < (δt j : ℝ)} := by
        rw [hej] at hs hsx
        exact ⟨s, hs, hsx⟩
      rw [fwdPath_image_lt] at hmem2
      obtain ⟨y, hy, hyx⟩ := hmem2
      rcases ball_or_eq_neg_one_or_one hy.1 with hyb | hyb | hyb
      · have hyx' : y = x := RelCWComplex.injOn_map_ball (C := C) 1 j hyb hb hyx
        rw [hyx'] at hy
        exact absurd (h1 (by rw [← hej]; exact he)) (not_le.mpr hy.2)
      · rw [hyb, map_one_neg_one_eq_srcIdx] at hyx
        exact absurd (hyx ▸ hoj) (vpt_not_mem_openCell_one (C := C) (srcIdx (C := C) j) j)
      · rw [hyb, map_one_one_eq_tgtIdx] at hyx
        exact absurd (hyx ▸ hoj) (vpt_not_mem_openCell_one (C := C) (tgtIdx (C := C) j) j)
    · rw [Set.mem_iUnion] at hmem
      obtain ⟨e, hmem⟩ := hmem
      rw [Set.mem_iUnion] at hmem
      obtain ⟨he, hmem⟩ := hmem
      obtain ⟨s, hs, hsx⟩ := hmem
      have hsub : Topology.RelCWComplex.map (C := C) 1 j x ∈
          (OEdge.path (C := C) ⟨e, false⟩) '' {t : unitInterval | (t : ℝ) < 1 / 2} := by
        rw [path_mk_false]
        exact ⟨s, lt_trans hs (hδf e), hsx⟩
      have hej : e = j := by
        by_contra hc
        exact Set.disjoint_left.mp
          (path_image_left_disjoint_openCell (C := C) ⟨e, false⟩ j (by simpa using hc)) hsub hoj
      have hmem2 : Topology.RelCWComplex.map (C := C) 1 j x ∈
          ((fwdPath (C := C) j).symm) '' {t : unitInterval | (t : ℝ) < (δf j : ℝ)} := by
        rw [hej] at hs hsx
        exact ⟨s, hs, hsx⟩
      rw [fwdPath_symm_image_lt'] at hmem2
      obtain ⟨y, hy, hyx⟩ := hmem2
      rcases ball_or_eq_neg_one_or_one hy.1 with hyb | hyb | hyb
      · have hyx' : y = x := RelCWComplex.injOn_map_ball (C := C) 1 j hyb hb hyx
        rw [hyx'] at hy
        exact absurd (h2 (by rw [← hej]; exact he)) (not_le.mpr hy.2)
      · rw [hyb, map_one_neg_one_eq_srcIdx] at hyx
        exact absurd (hyx ▸ hoj) (vpt_not_mem_openCell_one (C := C) (srcIdx (C := C) j) j)
      · rw [hyb, map_one_one_eq_tgtIdx] at hyx
        exact absurd (hyx ▸ hoj) (vpt_not_mem_openCell_one (C := C) (tgtIdx (C := C) j) j)
  · have hxe : x 0 = -1 := by rw [hb]; simp
    have hxj : Topology.RelCWComplex.map (C := C) 1 j x = vpt (C := C) (srcIdx (C := C) j) := by
      rw [hb]
      exact map_one_neg_one_eq_srcIdx (C := C) j
    have hv : srcIdx (C := C) j = v := by
      refine eq_of_vpt_mem_epsStar (C := C) hδt hδf ?_
      rw [← hxj]
      exact hmem
    linarith [h1 hv, hxe, hδtp j hv]
  · have hxe : x 0 = 1 := by rw [hb]; simp
    have hxj : Topology.RelCWComplex.map (C := C) 1 j x = vpt (C := C) (tgtIdx (C := C) j) := by
      rw [hb]
      exact map_one_one_eq_tgtIdx (C := C) j
    have hv : tgtIdx (C := C) j = v := by
      refine eq_of_vpt_mem_epsStar (C := C) hδt hδf ?_
      rw [← hxj]
      exact hmem
    linarith [h2 hv, hxe, hδfp j hv]

/-- **The star of a vertex with prescribed radii is open.** -/
theorem isOpen_epsStar {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n))
    (v : Topology.CWComplex.cell (Set.univ : Set X) 0)
    (δt δf : Topology.CWComplex.cell (Set.univ : Set X) 1 → unitInterval)
    (hδt : ∀ e, (δt e : ℝ) < 1 / 2) (hδf : ∀ e, (δf e : ℝ) < 1 / 2)
    (hδtp : ∀ e, srcIdx (C := (Set.univ : Set X)) e = v → 0 < (δt e : ℝ))
    (hδfp : ∀ e, tgtIdx (C := (Set.univ : Set X)) e = v → 0 < (δf e : ℝ)) :
    IsOpen (epsStar (C := (Set.univ : Set X)) v δt δf) := by
  rw [← isClosed_compl_iff]
  refine Topology.CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    (C := (Set.univ : Set X)) (by intro y hy; trivial) ?_
  intro n hn j
  right
  rcases n with _ | _ | m
  · exact absurd hn (Nat.lt_irrefl 0)
  · classical
    set K : Set (Fin 1 → ℝ) :=
      Metric.closedBall (0 : Fin 1 → ℝ) 1 ∩
        (if srcIdx (C := (Set.univ : Set X)) j = v then
          {y : Fin 1 → ℝ | 2 * (δt j : ℝ) - 1 ≤ y 0} else Set.univ) ∩
        (if tgtIdx (C := (Set.univ : Set X)) j = v then
          {y : Fin 1 → ℝ | 2 * (δf j : ℝ) - 1 ≤ -(y 0)} else Set.univ) with hK
    have hKclosed : IsClosed K := by
      rw [hK]
      refine IsClosed.inter (IsClosed.inter Metric.isClosed_closedBall ?_) ?_
      · split_ifs
        · exact isClosed_le continuous_const (continuous_apply 0)
        · exact isClosed_univ
      · split_ifs
        · exact isClosed_le continuous_const (continuous_apply 0).neg
        · exact isClosed_univ
    have hKsub : K ⊆ Metric.closedBall (0 : Fin 1 → ℝ) 1 := by
      rw [hK]
      exact fun y hy => hy.1.1
    have hKcompact : IsCompact K :=
      IsCompact.of_isClosed_subset (ProperSpace.isCompact_closedBall (0 : Fin 1 → ℝ) 1)
        hKclosed hKsub
    have hset : (epsStar (C := (Set.univ : Set X)) v δt δf)ᶜ ∩
        Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) 1 j =
        Topology.RelCWComplex.map (C := (Set.univ : Set X)) 1 j '' K := by
      ext y
      constructor
      · rintro ⟨hy1, hy2⟩
        obtain ⟨x, hx, rfl⟩ := hy2
        refine ⟨x, ?_, rfl⟩
        rw [hK]
        refine ⟨⟨hx, ?_⟩, ?_⟩
        · by_cases hc : srcIdx (C := (Set.univ : Set X)) j = v
          · rw [if_pos hc]
            by_contra hlt
            rw [Set.mem_setOf_eq, not_le] at hlt
            exact hy1 (mem_epsStar_of_lt (C := (Set.univ : Set X)) hx (Or.inl ⟨hc, hlt⟩))
          · rw [if_neg hc]
            exact trivial
        · by_cases hc : tgtIdx (C := (Set.univ : Set X)) j = v
          · rw [if_pos hc]
            by_contra hlt
            rw [Set.mem_setOf_eq, not_le] at hlt
            exact hy1 (mem_epsStar_of_lt (C := (Set.univ : Set X)) hx (Or.inr ⟨hc, hlt⟩))
          · rw [if_neg hc]
            exact trivial
      · rintro ⟨x, hxK, rfl⟩
        refine ⟨?_, Set.mem_image_of_mem _ (hKsub hxK)⟩
        rw [hK] at hxK
        obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hxK
        refine not_mem_epsStar (C := (Set.univ : Set X)) hδt hδf hδtp hδfp hx1 ?_ ?_
        · intro hc
          rw [if_pos hc] at hx2
          exact hx2
        · intro hc
          rw [if_pos hc] at hx3
          exact hx3
    rw [hset]
    exact (hKcompact.image_of_continuousOn
      ((Topology.RelCWComplex.continuousOn (C := (Set.univ : Set X)) 1 j).mono hKsub)).isClosed
  · exact ((h2 (m + 2) (by omega)).false j).elim

/-- **The fibre of the projection of the universal cover over a vertex consists of vertices.** -/
lemma exists_vertex_of_proj_eq {x : Tree (C := C) u} {v : Topology.CWComplex.cell C 0}
    (hx : proj (C := C) x = vpt (C := C) v) :
    ∃ W : RWalk (C := C) u, W.endOf = v ∧ x = vertex W := by
  induction x using Quotient.inductionOn with
  | h y =>
    rcases y with W | ⟨⟨W, hW⟩, t⟩
    · refine ⟨W, ?_, rfl⟩
      exact vpt_injective (show vpt (C := C) W.endOf = vpt (C := C) v from hx)
    · by_cases ht0 : t = 0
      · subst ht0
        refine ⟨W, ?_, ept_zero_eq_vertex W hW⟩
        have hpx : proj (C := C) (vertex W) = vpt (C := C) v := by
          rw [← ept_zero_eq_vertex W hW]; exact hx
        exact vpt_injective hpx
      · by_cases ht1 : t = 1
        · subst ht1
          refine ⟨W.dropLast, ?_, ept_one_eq_vertex_dropLast W hW⟩
          have hpx : proj (C := C) (vertex W.dropLast) = vpt (C := C) v := by
            rw [← ept_one_eq_vertex_dropLast W hW]; exact hx
          exact vpt_injective hpx
        · exfalso
          have h0 : (0 : ℝ) < (t : ℝ) := by
            rcases lt_or_gt_of_ne (fun h => ht0 (Subtype.ext h)) with h | h
            · exact absurd h (not_lt.mpr t.2.1)
            · exact h
          have h1 : (t : ℝ) < 1 := by
            rcases lt_or_gt_of_ne (fun h => ht1 (Subtype.ext h)) with h | h
            · exact h
            · exact absurd h (not_lt.mpr t.2.2)
          have heq : (OEdge.path (C := C) (W.lastLetter hW)) (unitInterval.symm t) =
              vpt (C := C) v := by
            have h := hx
            rw [show proj (C := C) (Quotient.mk _
                (Sum.inr (⟨W, hW⟩, t)) : Tree (C := C) u) =
                (OEdge.path (C := C) (W.lastLetter hW)).symm t from rfl, Path.symm_apply] at h
            exact h
          have hmem : (OEdge.path (C := C) (W.lastLetter hW)) (unitInterval.symm t) ∈
              Topology.RelCWComplex.openCell (C := C) 1 (W.lastLetter hW).cell := by
            refine OEdge.path_mem_openCell ?_ ?_
            · show (0 : ℝ) < ((unitInterval.symm t : unitInterval) : ℝ)
              show (0 : ℝ) < 1 - (t : ℝ)
              linarith
            · show (((unitInterval.symm t : unitInterval)) : ℝ) < 1
              show (1 : ℝ) - (t : ℝ) < 1
              linarith
          have hmem0 : vpt (C := C) v ∈ Topology.RelCWComplex.openCell (C := C) 0 v := by
            rw [Topology.RelCWComplex.openCell_zero_eq_singleton]
            exact Set.mem_singleton _
          exact Set.disjoint_left.mp
            (Topology.RelCWComplex.disjoint_openCell_of_ne (C := C)
              (by intro h; exact absurd (Sigma.mk.inj h).1 (by omega)))
            (heq ▸ hmem) hmem0

/-- **Interior points of an edge of the universal cover are glued only to themselves.**  If `t` is
not an endpoint parameter, the class of `Sum.inr (⟨W, hW⟩, t)` under the relation generated by
`treeRel` is a singleton.  (Needed for `Tree.ept`-uniqueness.) -/
lemma eqvGen_eq_of_interior {W : RWalk (C := C) u} {hW : W.1 ≠ []} {t : unitInterval}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ∀ {a b : TreePt (C := C) u}, Relation.EqvGen (treeRel (C := C) u) a b →
      (a = Sum.inr (⟨W, hW⟩, t) → b = Sum.inr (⟨W, hW⟩, t)) ∧
      (b = Sum.inr (⟨W, hW⟩, t) → a = Sum.inr (⟨W, hW⟩, t)) := by
  intro a b h
  induction h with
  | rel a b hab =>
      refine ⟨fun ha => ?_, fun hb => ?_⟩
      · subst ha
        exfalso
        rcases b with W' | ⟨⟨W', hW'⟩, t'⟩
        · rw [treeRel_inr_inl] at hab
          rcases hab with ⟨ht, -⟩ | ⟨ht, -⟩
          · exact ht0 ht
          · exact ht1 ht
        · exact hab
      · subst hb
        rcases a with W' | ⟨⟨W', hW'⟩, t'⟩ <;> exact hab.elim
  | refl a => exact ⟨id, id⟩
  | symm a b _ ih => exact ⟨ih.2, ih.1⟩
  | trans a b c _ _ ih₁ ih₂ =>
      exact ⟨fun ha => ih₂.1 (ih₁.1 ha), fun hc => ih₁.2 (ih₂.2 hc)⟩

/-- **Uniqueness of interior points of the universal cover**: two interior points of edges that are
equal in the tree come from the same walk and the same parameter. -/
lemma ept_eq_of_ne_endpoints {W W' : RWalk (C := C) u} {hW : W.1 ≠ []} {hW' : W'.1 ≠ []}
    {t s : unitInterval} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : ept (C := C) W hW t = ept (C := C) W' hW' s) :
    W = W' ∧ t = s := by
  have hq : Relation.EqvGen (treeRel (C := C) u)
      (Sum.inr (⟨W, hW⟩, t) : TreePt (C := C) u) (Sum.inr (⟨W', hW'⟩, s)) :=
    Quotient.exact h
  have hY : (Sum.inr (⟨W', hW'⟩, s) : TreePt (C := C) u) = Sum.inr (⟨W, hW⟩, t) :=
    (eqvGen_eq_of_interior (C := C) ht0 ht1 hq).1 rfl
  obtain ⟨hW'', ht'⟩ : (⟨W', hW'⟩ : {W : RWalk (C := C) u // W.1 ≠ []}) = ⟨W, hW⟩ ∧ s = t := by
    have h2 := Sum.inr.inj hY
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
  exact ⟨(congrArg Subtype.val hW'').symm, ht'.symm⟩


/-! ## Auxiliary structural lemmas about the universal cover -/

/-- Auxiliary: the vertex of the tree nearest to a naive point, in the parameter direction: a point
of the edge above `W` at parameter `0` is assigned `W`, every other point is assigned `W.dropLast`. -/
def uOfPt : TreePt (C := C) u → RWalk (C := C) u :=
  Sum.elim id fun p => if h : p.2 = 0 then p.1.1 else p.1.1.dropLast

lemma uOfPt_eq_of_rel {x y : TreePt (C := C) u} (h : treeRel (C := C) u x y) :
    uOfPt (C := C) x = uOfPt (C := C) y := by
  rcases x with W | ⟨⟨W, hW⟩, t⟩ <;> rcases y with W' | ⟨⟨W', hW'⟩, t'⟩
  · exact absurd h (by simp [treeRel])
  · exact absurd h (by simp [treeRel])
  · rw [treeRel_inr_inl] at h
    rcases h with ⟨ht, hW'⟩ | ⟨ht, hW'⟩
    · rw [ht, hW']
      show (if h : (0 : unitInterval) = 0 then W else W.dropLast) = W
      rw [dif_pos rfl]
    · rw [ht, hW']
      show (if h : (1 : unitInterval) = 0 then W else W.dropLast) = W.dropLast
      rw [dif_neg]
      intro hc
      have h1 : ((1 : unitInterval) : ℝ) = 0 := congrArg Subtype.val hc
      norm_num at h1
  · exact absurd h (by simp [treeRel])

lemma uOfPt_eqvGen {x y : TreePt (C := C) u}
    (h : Relation.EqvGen (treeRel (C := C) u) x y) : uOfPt (C := C) x = uOfPt (C := C) y := by
  induction h with
  | rel x y h => exact uOfPt_eq_of_rel h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The vertex of the tree nearest to a point of the tree. -/
def uOf (x : Tree (C := C) u) : RWalk (C := C) u :=
  Quotient.lift (uOfPt (C := C)) (fun _ _ h => uOfPt_eqvGen h) x

@[simp] lemma uOf_vertex (W : RWalk (C := C) u) : uOf (C := C) (vertex W) = W := rfl

/-- **The vertices of the universal cover are distinct**: two reduced walks with equal vertices are
equal. -/
lemma vertex_injective : Function.Injective (vertex (C := C) (u := u)) := by
  intro W W' h
  have hq : Relation.EqvGen (treeRel (C := C) u) (Sum.inl W : TreePt (C := C) u) (Sum.inl W') :=
    Quotient.exact h
  exact uOfPt_eqvGen hq

/-- An interior point of an edge is never a vertex. -/
lemma ept_ne_vertex {W W' : RWalk (C := C) u} {hW : W.1 ≠ []} {t : unitInterval}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) : ept (C := C) W hW t ≠ vertex W' := by
  intro h
  have hq : Relation.EqvGen (treeRel (C := C) u)
      (Sum.inr (⟨W, hW⟩, t) : TreePt (C := C) u) (Sum.inl W') := Quotient.exact h
  exact Sum.inl_ne_inr ((eqvGen_eq_of_interior (C := C) ht0 ht1 hq).1 rfl)

/-- Characterisation of when a point of an edge equals a vertex. -/
lemma ept_eq_vertex_iff {W W' : RWalk (C := C) u} {hW : W.1 ≠ []} {t : unitInterval} :
    ept (C := C) W hW t = vertex W' ↔ (t = 0 ∧ W' = W) ∨ (t = 1 ∧ W' = W.dropLast) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases ht0 : t = 0
    · refine Or.inl ⟨ht0, ?_⟩
      have : ept (C := C) W hW t = vertex W := by rw [ht0, ept_zero_eq_vertex]
      rw [this] at h
      exact (vertex_injective h).symm
    · by_cases ht1 : t = 1
      · refine Or.inr ⟨ht1, ?_⟩
        have : ept (C := C) W hW t = vertex W.dropLast := by rw [ht1, ept_one_eq_vertex_dropLast]
        rw [this] at h
        exact (vertex_injective h).symm
      · exact absurd h (ept_ne_vertex ht0 ht1)
  · rcases h with ⟨ht, hW'⟩ | ⟨ht, hW'⟩
    · rw [ht, hW', ept_zero_eq_vertex]
    · rw [ht, hW', ept_one_eq_vertex_dropLast]



/-- The second half of an edge meets the vertex set only in the image of the target. -/
lemma fwdPath_image_right_vertex {e : Topology.CWComplex.cell C 1}
    {w : Topology.CWComplex.cell C 0} {t : unitInterval} (ht : (1 : ℝ) / 2 < (t : ℝ))
    (h : fwdPath (C := C) e t = vpt (C := C) w) :
    vpt (C := C) w = vpt (C := C) (tgtIdx (C := C) e) := by
  by_cases hb : segF t ∈ Metric.ball (0 : Fin 1 → ℝ) 1
  · exact absurd (h ▸ Set.mem_image_of_mem _ hb) (vpt_not_mem_openCell_one w e)
  · have hs := segF_mem_sphere_of_notMem_ball hb
    have h0 := segF_eq_endpoints_of_mem_sphere hs
    have hz : (t : ℝ) = 1 := by
      rcases h0 with h0 | h0
      · exact absurd h0 (by linarith [ht])
      · exact h0
    have ht1 : t = 1 := Subtype.ext hz
    have h' : Topology.RelCWComplex.map (C := C) 1 e (segF (1 : unitInterval)) =
        vpt (C := C) w := by rw [ht1] at h; exact h
    rw [segF_one, map_one_one_eq_tgtIdx] at h'
    exact h'.symm

/-- The star of a vertex of the universal cover: the vertex itself together with the halves of the
incident edges pointing towards it.  Concretely, it consists of `vertex W` together with the points
of the edge above `W` of parameter `< 1/2` and the points of the edges above `W'` with
`W'.dropLast = W` of parameter `> 1/2`. -/
def starSet (W : RWalk (C := C) u) : Set (Tree (C := C) u) :=
  {x | x = vertex W} ∪
  {x | ∃ (hW : W.1 ≠ []) (t : unitInterval), (t : ℝ) < 1 / 2 ∧ x = ept W hW t} ∪
  {x | ∃ (W' : RWalk (C := C) u) (hW' : W'.1 ≠ []) (t : unitInterval),
      W'.dropLast = W ∧ (1 : ℝ) / 2 < (t : ℝ) ∧ x = ept W' hW' t}

lemma mem_starSet_vertex (W : RWalk (C := C) u) : vertex W ∈ starSet (C := C) W := by
  simp [starSet]

lemma ept_congr {W W' : RWalk (C := C) u} (h : W = W') (hW : W.1 ≠ []) (hW' : W'.1 ≠ [])
    (t : unitInterval) : ept (C := C) W hW t = ept (C := C) W' hW' t := by
  subst h; rfl

/-- The naive description of the star at the level of points of edges. -/
lemma ept_mem_starSet_iff {W W' : RWalk (C := C) u} {hW' : W'.1 ≠ []} {t : unitInterval} :
    ept (C := C) W' hW' t ∈ starSet (C := C) W ↔
      (W' = W ∧ (t : ℝ) < 1 / 2) ∨ (W'.dropLast = W ∧ (1 : ℝ) / 2 < (t : ℝ)) := by
  simp only [starSet, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases h with (h | ⟨hW, s, hs, he⟩) | ⟨W'', hW'', s, hd, hs, he⟩
    · rw [ept_eq_vertex_iff] at h
      rcases h with ⟨ht, hW'W⟩ | ⟨ht, hW'W⟩
      · exact Or.inl ⟨hW'W.symm, by rw [ht]; norm_num⟩
      · exact Or.inr ⟨hW'W.symm, by rw [ht]; norm_num⟩
    · rcases eq_or_ne t 0 with ht | ht
      · have he' : ept (C := C) W hW s = vertex W' := by rw [← he, ht, ept_zero_eq_vertex]
        rw [ept_eq_vertex_iff] at he'
        rcases he' with ⟨hs0, hW'W⟩ | ⟨hs1, -⟩
        · exact Or.inl ⟨hW'W, by rw [ht]; norm_num⟩
        · exact absurd (by rw [hs1] at hs; exact hs) (by norm_num)
      · rcases eq_or_ne t 1 with ht1 | ht1
        · have he' : ept (C := C) W hW s = vertex W'.dropLast := by
            rw [← he, ht1, ept_one_eq_vertex_dropLast]
          rw [ept_eq_vertex_iff] at he'
          rcases he' with ⟨hs0, hW'⟩ | ⟨hs1, -⟩
          · exact Or.inr ⟨hW', by rw [ht1]; norm_num⟩
          · exact absurd (by rw [hs1] at hs; exact hs) (by norm_num)
        · obtain ⟨hW'W, hts⟩ := ept_eq_of_ne_endpoints (C := C) ht ht1 he
          exact Or.inl ⟨hW'W, by rw [hts]; exact hs⟩
    · rcases eq_or_ne t 0 with ht | ht
      · have he' : ept (C := C) W'' hW'' s = vertex W' := by rw [← he, ht, ept_zero_eq_vertex]
        rw [ept_eq_vertex_iff] at he'
        rcases he' with ⟨hs0, -⟩ | ⟨hs1, hW'W⟩
        · exact absurd (by rw [hs0] at hs; exact hs) (by norm_num)
        · exact Or.inl ⟨by rw [hW'W, hd], by rw [ht]; norm_num⟩
      · rcases eq_or_ne t 1 with ht1 | ht1
        · have he' : ept (C := C) W'' hW'' s = vertex W'.dropLast := by
            rw [← he, ht1, ept_one_eq_vertex_dropLast]
          rw [ept_eq_vertex_iff] at he'
          rcases he' with ⟨hs0, -⟩ | ⟨hs1, hW'W⟩
          · exact absurd (by rw [hs0] at hs; exact hs) (by norm_num)
          · exact Or.inr ⟨by rw [hW'W, hd], by rw [ht1]; norm_num⟩
        · obtain ⟨hW''W', hts⟩ := ept_eq_of_ne_endpoints (C := C) ht ht1 he
          exact Or.inr ⟨by rw [hW''W', hd], by rw [hts]; exact hs⟩
  · rintro (⟨hWW, ht⟩ | ⟨hd, ht⟩)
    · exact Or.inl (Or.inr ⟨by rw [← hWW]; exact hW', t, ht, (ept_congr hWW.symm _ hW' t).symm⟩)
    · exact Or.inr ⟨W', hW', t, hd, ht, rfl⟩

/-- **The star of a vertex of the universal cover is open.** -/
lemma isOpen_starSet (W : RWalk (C := C) u) : IsOpen (starSet (C := C) W) := by
  rw [isOpen_iff]
  intro W' hW'
  have hslice : {t : unitInterval | ept (C := C) W' hW' t ∈ starSet (C := C) W} =
      {t : unitInterval | (t : ℝ) < 1 / 2 ∧ W' = W} ∪
      {t : unitInterval | (1 : ℝ) / 2 < (t : ℝ) ∧ W'.dropLast = W} := by
    ext t
    rw [Set.mem_setOf_eq, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq, ept_mem_starSet_iff]
    tauto
  rw [hslice]
  refine IsOpen.union ?_ ?_
  · by_cases h : W' = W
    · simpa [h] using isOpen_lt continuous_subtype_val continuous_const
    · simp [h]
  · by_cases h : W'.dropLast = W
    · simpa [h] using isOpen_lt continuous_const continuous_subtype_val
    · simp [h]




/-- Reversing a path twice is the identity (pointwise, since the coercion through `Path.symm`
does not simplify definitionally). -/
lemma path_symm_symm_apply {x y : Y} {γ : Path x y} (t : unitInterval) :
    γ.symm.symm t = γ t := by
  show γ (unitInterval.symm (unitInterval.symm t)) = γ t
  rw [unitInterval.symm_symm]

/-- The reverse of an oriented edge. -/
@[simp] lemma neg_mk_true (e : Topology.CWComplex.cell C 1) :
    (OEdge.mk e true).neg = OEdge.mk e false := rfl

@[simp] lemma neg_mk_false (e : Topology.CWComplex.cell C 1) :
    (OEdge.mk e false).neg = OEdge.mk e true := rfl

/-- **The path of the reversed edge is the reverse of the path.** -/
lemma path_neg_apply (o : OEdge (C := C)) (t : unitInterval) :
    OEdge.path (C := C) o.neg t = (OEdge.path (C := C) o).symm t := by
  rcases o with ⟨e, b⟩
  cases b
  · rw [neg_mk_false, path_mk_true, path_mk_false]
    exact (path_symm_symm_apply (γ := fwdPath (C := C) e) t).symm
  · rw [neg_mk_true, path_mk_false, path_mk_true]
    rfl

/-- **The star of a vertex of the tree projects into the half-star of the corresponding vertex of
the one-skeleton.** -/
lemma proj_mem_halfStar_of_mem_starSet {W : RWalk (C := C) u} {x : Tree (C := C) u}
    (hx : x ∈ starSet (C := C) W) : proj (C := C) x ∈ halfStar (C := C) W.endOf := by
  simp only [starSet, Set.mem_union, Set.mem_setOf_eq] at hx
  rcases hx with (hx | ⟨hW, t, ht, hx⟩) | ⟨W', hW', t, hd, ht, hx⟩
  · rw [hx, proj_vertex]
    exact vpt_mem_halfStar W.endOf
  · rw [hx, proj_ept, ← path_neg_apply (W.lastLetter hW) t]
    rw [halfStar]
    refine Or.inr (Set.mem_iUnion.mpr ⟨(W.lastLetter hW).neg, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩)
    · rw [OEdge.src_neg]
      exact (RWalk.endOf_eq_lastLetter_tgt W hW).symm
    · exact ⟨t, ht, rfl⟩
  · rw [hx, proj_ept]
    rw [halfStar]
    refine Or.inr (Set.mem_iUnion.mpr ⟨W'.lastLetter hW', Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩)
    · rw [← RWalk.endOf_dropLast_eq_lastLetter_src W' hW', hd]
    · refine ⟨unitInterval.symm t, ?_, ?_⟩
      · show ((unitInterval.symm t : unitInterval) : ℝ) < 1 / 2
        rw [unitInterval.coe_symm_eq]
        linarith
      · rfl


/-- Appending one letter preserves reducedness, provided the new letter is not the inverse of the
last one. -/
lemma reduced_append_singleton {l : List (OEdge (C := C))} (h : Reduced (C := C) l)
    {o : OEdge (C := C)} (hne : ∀ (h' : l ≠ []), o ≠ (l.getLast h').neg) :
    Reduced (C := C) (l ++ [o]) := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons a l ih =>
    cases l with
    | nil =>
      rw [List.singleton_append, reduced_cons_iff]
      refine ⟨?_, ?_⟩
      · intro b hb
        simp only [List.head?_cons, Option.some.injEq] at hb
        rw [← hb]
        simpa using hne (by simp)
      · intro i hi; simp at hi
    | cons b l =>
      rw [List.cons_append, reduced_cons_iff]
      refine ⟨?_, ?_⟩
      · intro c hc
        simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hc
        rw [← hc]
        rw [reduced_cons_iff] at h
        exact h.1 b rfl
      · rw [reduced_cons_iff] at h
        exact ih h.2 fun h' => hne (by simp)


/-- The walk obtained by appending one oriented edge is a walk. -/
lemma isWalk_snoc (W : RWalk (C := C) u) {o : OEdge (C := C)} (ho : o.src = W.endOf) :
    IsWalk (C := C) u (W.1 ++ [o]) := by
  refine Walk.isWalk_append W.2.1 ?_
  exact ⟨ho, trivial⟩

/-- The walk obtained by appending one oriented edge is reduced, provided the new edge is not the
inverse of the last letter. -/
lemma reduced_snoc (W : RWalk (C := C) u) {o : OEdge (C := C)}
    (hne : ∀ (h' : W.1 ≠ []), o ≠ (W.1.getLast h').neg) :
    Reduced (C := C) (W.1 ++ [o]) :=
  reduced_append_singleton W.2.2 hne

/-- Dropping the last letter of a walk with one letter appended returns the original walk. -/
lemma dropLast_snoc (W : RWalk (C := C) u) {o : OEdge (C := C)}
    (hwalk : IsWalk (C := C) u (W.1 ++ [o])) (hred : Reduced (C := C) (W.1 ++ [o])) :
    RWalk.dropLast (⟨W.1 ++ [o], hwalk, hred⟩ : RWalk (C := C) u) = W := by
  refine Subtype.ext ?_
  simp only [RWalk.dropLast_val, List.dropLast_concat]

/-- The last letter of a walk with one letter appended is that letter. -/
lemma lastLetter_snoc (W : RWalk (C := C) u) {o : OEdge (C := C)}
    (hwalk : IsWalk (C := C) u (W.1 ++ [o])) (hred : Reduced (C := C) (W.1 ++ [o]))
    (hne : (⟨W.1 ++ [o], hwalk, hred⟩ : RWalk (C := C) u).1 ≠ []) :
    RWalk.lastLetter (⟨W.1 ++ [o], hwalk, hred⟩ : RWalk (C := C) u) hne = o := by
  rw [RWalk.lastLetter]
  simp

/-- **Every point of the half-star of a vertex comes from the star of the corresponding vertex of
the tree.** -/
lemma exists_mem_starSet_of_mem_halfStar {W : RWalk (C := C) u} {y : Y}
    (hy : y ∈ halfStar (C := C) W.endOf) : ∃ x ∈ starSet (C := C) W, proj (C := C) x = y := by
  rw [halfStar] at hy
  rcases hy with hy | hy
  · rw [Set.mem_singleton_iff] at hy
    exact ⟨vertex W, mem_starSet_vertex W, by rw [hy, proj_vertex]⟩
  · rw [Set.mem_iUnion] at hy
    obtain ⟨o, hy⟩ := hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨ho, hy⟩ := hy
    obtain ⟨t, ht, rfl⟩ := hy
    simp only [Set.mem_setOf_eq] at ht
    have hchild : ∀ (hred : Reduced (C := C) (W.1 ++ [o])),
        ∃ x ∈ starSet (C := C) W, proj (C := C) x = OEdge.path (C := C) o t := by
      intro hred
      have hwalk := isWalk_snoc W ho
      set W' : RWalk (C := C) u := ⟨W.1 ++ [o], hwalk, hred⟩ with hW'def
      have hne' : W'.1 ≠ [] := by rw [hW'def]; simp
      have hdrop : W'.dropLast = W := dropLast_snoc W hwalk hred
      have hlast : W'.lastLetter hne' = o := lastLetter_snoc W hwalk hred hne'
      refine ⟨ept W' hne' (unitInterval.symm t), ?_, ?_⟩
      · rw [starSet]
        simp only [Set.mem_union, Set.mem_setOf_eq]
        refine Or.inr ⟨W', hne', unitInterval.symm t, hdrop, ?_, rfl⟩
        show (1 : ℝ) / 2 < ((unitInterval.symm t : unitInterval) : ℝ)
        rw [unitInterval.coe_symm_eq]
        linarith
      · rw [proj_ept, hlast]
        show OEdge.path (C := C) o (unitInterval.symm (unitInterval.symm t)) =
          OEdge.path (C := C) o t
        rw [unitInterval.symm_symm]
    by_cases hW : W.1 = []
    · exact hchild (reduced_snoc W fun h' => absurd hW h')
    · by_cases hcase : o = (W.lastLetter hW).neg
      · refine ⟨ept W hW t, ?_, ?_⟩
        · rw [starSet]
          simp only [Set.mem_union, Set.mem_setOf_eq]
          exact Or.inl (Or.inr ⟨hW, t, ht, rfl⟩)
        · rw [proj_ept, ← path_neg_apply, hcase]
      · refine hchild (reduced_snoc W fun h' hc => hcase (hc.trans ?_))
        rw [RWalk.lastLetter]

/-- **The star of a vertex of the tree projects onto the half-star of the corresponding vertex of
the one-skeleton.** -/
lemma proj_image_starSet (W : RWalk (C := C) u) :
    proj (C := C) '' starSet (C := C) W = halfStar (C := C) W.endOf := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact proj_mem_halfStar_of_mem_starSet hx
  · intro hy
    obtain ⟨x, hx, hxy⟩ := exists_mem_starSet_of_mem_halfStar hy
    exact ⟨x, hx, hxy⟩


/-- The parametrisation of the unit interval is injective. -/
lemma segF_injective : Function.Injective segF := by
  intro u v huv
  have h : (segF u) 0 = (segF v) 0 := congrFun huv 0
  simp only [segF] at h
  apply Subtype.ext
  linarith

/-- The characteristic path of an edge is injective on the open unit interval. -/
lemma fwdPath_injOn (e : Topology.CWComplex.cell C 1) :
    Set.InjOn (fwdPath (C := C) e) {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by
  intro u hu v hv huv
  refine segF_injective (RelCWComplex.injOn_map_ball 1 e ?_ ?_ ?_)
  · exact segF_mem_ball hu.1 hu.2
  · exact segF_mem_ball hv.1 hv.2
  · exact huv

/-- The reverse of the characteristic path is injective on the open unit interval. -/
lemma fwdPath_symm_injOn (e : Topology.CWComplex.cell C 1) :
    Set.InjOn ((fwdPath (C := C) e).symm) {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by
  intro u hu v hv huv
  have huv' : (fwdPath (C := C) e) (unitInterval.symm u) =
      (fwdPath (C := C) e) (unitInterval.symm v) := huv
  refine Function.Involutive.injective unitInterval.symm_involutive ?_
  refine fwdPath_injOn e ?_ ?_ huv'
  · exact ⟨by rw [unitInterval.coe_symm_eq]; linarith [hu.2],
      by rw [unitInterval.coe_symm_eq]; linarith [hu.1]⟩
  · exact ⟨by rw [unitInterval.coe_symm_eq]; linarith [hv.2],
      by rw [unitInterval.coe_symm_eq]; linarith [hv.1]⟩

/-- The characteristic path of an oriented edge is injective on the open unit interval. -/
lemma path_injOn (o : OEdge (C := C)) :
    Set.InjOn (OEdge.path (C := C) o) {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by
  rcases o with ⟨e, b⟩
  cases b
  · rw [path_mk_false]; exact fwdPath_symm_injOn e
  · rw [path_mk_true]; exact fwdPath_injOn e

/-- The projection of an interior point of an edge of the tree lies in the open cell of that edge. -/
lemma proj_ept_mem_openCell {W : RWalk (C := C) u} {hW : W.1 ≠ []} {t : unitInterval}
    (h0 : 0 < (t : ℝ)) (h1 : (t : ℝ) < 1) :
    proj (C := C) (ept (C := C) W hW t) ∈
      Topology.RelCWComplex.openCell (C := C) 1 (W.lastLetter hW).cell := by
  rw [proj_ept]
  exact OEdge.path_mem_openCell (C := C) (by rw [unitInterval.coe_symm_eq]; linarith)
    (by rw [unitInterval.coe_symm_eq]; linarith)

/-- Two oriented edges with the same underlying cell are equal or inverse to each other. -/
lemma eq_or_eq_neg_of_cell_eq {o o' : OEdge (C := C)} (h : o.cell = o'.cell) :
    o = o' ∨ o = o'.neg := by
  rcases o with ⟨e, b⟩
  rcases o' with ⟨e', b'⟩
  simp only [OEdge.mk.injEq] at h
  subst h
  cases b <;> cases b' <;> simp [OEdge.neg]


/-- **Comparing the characteristic paths of two oriented edges.**  If the values at parameters in
the open unit interval agree, then the edges have the same underlying cell and either they are
equal (with equal parameters) or they are inverse to each other (with parameters exchanged). -/
lemma path_apply_eq {o o' : OEdge (C := C)} {u v : unitInterval}
    (hu : 0 < (u : ℝ) ∧ (u : ℝ) < 1) (hv : 0 < (v : ℝ) ∧ (v : ℝ) < 1)
    (h : OEdge.path (C := C) o u = OEdge.path (C := C) o' v) :
    (o' = o ∧ u = v) ∨ (o' = o.neg ∧ u = unitInterval.symm v) := by
  have hcell : o.cell = o'.cell := by
    by_contra hc
    exact Set.disjoint_left.mp
      (Topology.RelCWComplex.disjoint_openCell_of_ne (C := C) (n := 1) (m := 1)
        (i := o.cell) (j := o'.cell)
        (by intro hh; exact hc (eq_of_heq (Sigma.mk.inj hh).2)))
      (OEdge.path_mem_openCell (C := C) hu.1 hu.2)
      (h ▸ OEdge.path_mem_openCell (C := C) hv.1 hv.2)
  rcases eq_or_eq_neg_of_cell_eq hcell with hcase | hcase
  · left
    refine ⟨hcase.symm, path_injOn o hu hv ?_⟩
    rw [← hcase] at h
    exact h
  · have hcase' : o' = o.neg :=
      ((congrArg OEdge.neg hcase).trans (OEdge.neg_neg o')).symm
    right
    refine ⟨hcase', ?_⟩
    have h3 : OEdge.path (C := C) o u = (OEdge.path (C := C) o).symm v := by
      rw [hcase'] at h
      rw [path_neg_apply] at h
      exact h
    exact path_injOn o hu ⟨by rw [unitInterval.coe_symm_eq]; linarith [hv.2],
      by rw [unitInterval.coe_symm_eq]; linarith [hv.1]⟩ h3


lemma RWalk.lastLetter_congr {W W' : RWalk (C := C) u} (h : W = W')
    (hW : W.1 ≠ []) (hW' : W'.1 ≠ []) : W.lastLetter hW = W'.lastLetter hW' :=
  List.getLast_congr hW hW' (congrArg Subtype.val h)

/-- The only vertex of the tree lying in the star of `W` is `vertex W`. -/
lemma eq_of_vertex_mem_starSet {W W'' : RWalk (C := C) u}
    (h : vertex W'' ∈ starSet (C := C) W) : W'' = W := by
  simp only [starSet, Set.mem_union, Set.mem_setOf_eq] at h
  rcases h with (h | ⟨hW, t, ht, he⟩) | ⟨W', hW', t, hd, ht, he⟩
  · exact vertex_injective h
  · rw [eq_comm, ept_eq_vertex_iff] at he
    rcases he with ⟨ht0, hWW⟩ | ⟨ht1, -⟩
    · exact hWW
    · exact absurd (by rw [ht1] at ht; exact ht) (by norm_num)
  · rw [eq_comm, ept_eq_vertex_iff] at he
    rcases he with ⟨ht0, -⟩ | ⟨ht1, hWW⟩
    · exact absurd (by rw [ht0] at ht; exact ht) (by norm_num)
    · exact hWW.trans hd

/-- A point of the star of `W` whose projection is the projection of `vertex W` is `vertex W`. -/
lemma eq_vertex_of_proj_eq {W : RWalk (C := C) u} {x : Tree (C := C) u}
    (hx : x ∈ starSet (C := C) W)
    (h : proj (C := C) x = proj (C := C) (vertex W)) : x = vertex W := by
  obtain ⟨W'', -, hxW''⟩ := exists_vertex_of_proj_eq (C := C) (x := x)
    (v := W.endOf) (by rw [h, proj_vertex])
  rw [hxW''] at hx ⊢
  exact congrArg vertex (eq_of_vertex_mem_starSet hx)

/-- A point of the star of `W` which is not the vertex `vertex W` is an interior point of an edge
above some nonempty reduced walk. -/
lemma exists_ept_of_mem_starSet_ne_vertex {W : RWalk (C := C) u} {x : Tree (C := C) u}
    (hx : x ∈ starSet (C := C) W) (hv : x ≠ vertex W) :
    ∃ (W' : RWalk (C := C) u) (hW' : W'.1 ≠ []) (t : unitInterval),
      x = ept (C := C) W' hW' t ∧ t ≠ 0 ∧ t ≠ 1 := by
  simp only [starSet, Set.mem_union, Set.mem_setOf_eq] at hx
  rcases hx with (h | ⟨hW, t, ht, hxt⟩) | ⟨W', hW', t, hd, ht, hxt⟩
  · exact absurd h hv
  · refine ⟨W, hW, t, hxt, ?_, ?_⟩
    · intro h0; exact hv (by rw [hxt, h0, ept_zero_eq_vertex])
    · intro h1; exact absurd (h1 ▸ ht) (by norm_num)
  · refine ⟨W', hW', t, hxt, ?_, ?_⟩
    · intro h0; exact absurd (h0 ▸ ht) (by norm_num)
    · intro h1; exact hv (by rw [hxt, h1, ept_one_eq_vertex_dropLast, hd])

/-- **Interior points of the star of `W` are separated by the projection.** -/
lemma ept_injOn_starSet {W W' W'' : RWalk (C := C) u} {hW' : W'.1 ≠ []} {hW'' : W''.1 ≠ []}
    {t s : unitInterval} (hx : ept (C := C) W' hW' t ∈ starSet (C := C) W)
    (hy : ept (C := C) W'' hW'' s ∈ starSet (C := C) W)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (h : proj (C := C) (ept (C := C) W' hW' t) = proj (C := C) (ept (C := C) W'' hW'' s)) :
    ept (C := C) W' hW' t = ept (C := C) W'' hW'' s := by
  have htR : (0 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 1 :=
    ⟨lt_of_le_of_ne t.2.1 (fun hh => ht0 (Subtype.ext hh.symm)),
     lt_of_le_of_ne t.2.2 (fun hh => ht1 (Subtype.ext hh))⟩
  have hsR : (0 : ℝ) < (s : ℝ) ∧ (s : ℝ) < 1 :=
    ⟨lt_of_le_of_ne s.2.1 (fun hh => hs0 (Subtype.ext hh.symm)),
     lt_of_le_of_ne s.2.2 (fun hh => hs1 (Subtype.ext hh))⟩
  have hσt : 0 < ((unitInterval.symm t : unitInterval) : ℝ) ∧
      ((unitInterval.symm t : unitInterval) : ℝ) < 1 := by
    rw [unitInterval.coe_symm_eq]
    exact ⟨by linarith [htR.2], by linarith [htR.1]⟩
  have hσs : 0 < ((unitInterval.symm s : unitInterval) : ℝ) ∧
      ((unitInterval.symm s : unitInterval) : ℝ) < 1 := by
    rw [unitInterval.coe_symm_eq]
    exact ⟨by linarith [hsR.2], by linarith [hsR.1]⟩
  have hpath : OEdge.path (C := C) (W'.lastLetter hW') (unitInterval.symm t)
      = OEdge.path (C := C) (W''.lastLetter hW'') (unitInterval.symm s) := by
    rw [proj_ept, proj_ept, Path.symm_apply, Path.symm_apply] at h
    exact h
  have hpae := path_apply_eq (C := C) (o := W'.lastLetter hW') (o' := W''.lastLetter hW'')
    (u := unitInterval.symm t) (v := unitInterval.symm s) hσt hσs hpath
  have hsymm_inj : Function.Injective (unitInterval.symm : unitInterval → unitInterval) :=
    Function.Involutive.injective unitInterval.symm_involutive
  have hnum : ∀ {a b : unitInterval},
      unitInterval.symm a = unitInterval.symm (unitInterval.symm b) → (1 : ℝ) - (a : ℝ) = (b : ℝ) := by
    intro a b hab
    have : ((unitInterval.symm a : unitInterval) : ℝ) = (b : ℝ) := by
      rw [hab, unitInterval.symm_symm]
    simpa [unitInterval.coe_symm_eq] using this
  have hshape' := (ept_mem_starSet_iff (C := C) (W := W) (W' := W')
    (hW' := hW') (t := t)).mp hx
  have hshape'' := (ept_mem_starSet_iff (C := C) (W := W) (W' := W'')
    (hW' := hW'') (t := s)).mp hy
  rcases hshape' with ⟨hW'W, ht2⟩ | ⟨hW'W, ht2⟩ <;>
    rcases hshape'' with ⟨hW''W, hs2⟩ | ⟨hW''W, hs2⟩ <;>
    rcases hpae with ⟨ho, hσ⟩ | ⟨hone, hσ⟩
  · -- both in the parent position
    have hts : t = s := hsymm_inj hσ
    rw [hts]
    exact ept_congr (by rw [hW'W, hW''W]) hW' hW'' s
  · -- both parent, second alternative: impossible by the size of the parameters
    exfalso
    have := hnum hσ
    linarith [ht2, hs2, this]
  · -- parent / child, first alternative
    exfalso
    have hts : (t : ℝ) = (s : ℝ) := congrArg Subtype.val (hsymm_inj hσ)
    linarith [ht2, hs2, hts]
  · -- parent / child, second alternative: contradicts reducedness
    exfalso
    have hW : W.1 ≠ [] := by rw [← hW'W]; exact hW'
    have hne := RWalk.lastLetter_ne_neg (C := C) (W := W) (W' := W'')
      (hW := hW) (hW' := hW'') hW''W
    exact hne (by rw [hone, RWalk.lastLetter_congr (C := C) hW'W hW' hW])
  · -- child / parent, first alternative
    exfalso
    have hts : (t : ℝ) = (s : ℝ) := congrArg Subtype.val (hsymm_inj hσ)
    linarith [ht2, hs2, hts]
  · -- child / parent, second alternative: contradicts reducedness
    exfalso
    have hW : W.1 ≠ [] := by rw [← hW''W]; exact hW''
    have hne := RWalk.lastLetter_ne_neg (C := C) (W := W) (W' := W')
      (hW := hW) (hW' := hW') hW'W
    refine hne ?_
    have h1 : W'.lastLetter hW' = ((W'.lastLetter hW').neg).neg := (OEdge.neg_neg _).symm
    rw [h1, ← hone, RWalk.lastLetter_congr (C := C) hW''W hW'' hW]
  · -- both in the child position
    have hts : t = s := hsymm_inj hσ
    have hd' : W'.1.dropLast = W.1 := by
      simpa only [RWalk.dropLast_val] using congrArg Subtype.val hW'W
    have hd'' : W''.1.dropLast = W.1 := by
      simpa only [RWalk.dropLast_val] using congrArg Subtype.val hW''W
    have hgl : W'.1.getLast hW' = W''.1.getLast hW'' := ho.symm
    have hWW : W' = W'' := by
      apply Subtype.ext
      rw [← List.dropLast_append_getLast hW', ← List.dropLast_append_getLast hW'',
        hd', hd'', hgl]
    rw [hts]
    exact ept_congr hWW hW' hW'' s
  · -- both child, second alternative: impossible by the size of the parameters
    exfalso
    have := hnum hσ
    linarith [ht2, hs2, this]

/-- **The projection is injective on a sheet.** -/
lemma injOn_proj_starSet (W : RWalk (C := C) u) :
    Set.InjOn (proj (C := C) (u := u)) (starSet (C := C) W) := by
  intro x hx y hy hxy
  rcases eq_or_ne x (vertex W) with hxv | hxv
  · rw [hxv] at hxy ⊢
    exact (eq_vertex_of_proj_eq hy hxy.symm).symm
  rcases eq_or_ne y (vertex W) with hyv | hyv
  · rw [hyv] at hxy ⊢
    exact eq_vertex_of_proj_eq hx hxy
  obtain ⟨W', hW', t, hxt, ht0, ht1⟩ := exists_ept_of_mem_starSet_ne_vertex hx hxv
  obtain ⟨W'', hW'', s, hys, hs0, hs1⟩ := exists_ept_of_mem_starSet_ne_vertex hy hyv
  rw [hxt] at hx
  rw [hys] at hy
  rw [hxt, hys] at hxy ⊢
  exact ept_injOn_starSet hx hy ht0 ht1 hs0 hs1 hxy

/-- **Every point of the tree over the half-star of a vertex lies in the star of a walk ending at
that vertex.** -/
lemma exists_starSet_of_proj_mem_halfStar {x : Tree (C := C) u}
    {v : Topology.CWComplex.cell C 0} (hx : proj (C := C) x ∈ halfStar (C := C) v) :
    ∃ W : RWalk (C := C) u, W.endOf = v ∧ x ∈ starSet (C := C) W := by
  induction x using Quotient.inductionOn with
  | h y =>
    rcases y with W | ⟨⟨W, hW⟩, t⟩
    · have hxv : (Quotient.mk _ (Sum.inl W) : Tree (C := C) u) = vertex W := rfl
      rw [hxv] at hx ⊢
      exact ⟨W, eq_of_vpt_mem_halfStar (C := C) (by simpa using hx),
        mem_starSet_vertex (C := C) W⟩
    · have hxe : (Quotient.mk _ (Sum.inr (⟨W, hW⟩, t)) : Tree (C := C) u) = ept W hW t := rfl
      rw [hxe] at hx ⊢
      rcases eq_or_ne t 0 with ht0 | ht0
      · refine ⟨W, ?_, ?_⟩
        · refine eq_of_vpt_mem_halfStar (C := C) ?_
          simpa [ht0, ept_zero_eq_vertex] using hx
        · rw [ht0, ept_zero_eq_vertex]
          exact mem_starSet_vertex (C := C) W
      · rcases eq_or_ne t 1 with ht1 | ht1
        · refine ⟨W.dropLast, ?_, ?_⟩
          · have hx' : vpt (C := C) W.dropLast.endOf ∈ halfStar (C := C) v := by
              simpa [ht1, ept_one_eq_vertex_dropLast] using hx
            exact eq_of_vpt_mem_halfStar (C := C) hx'
          · rw [ht1, ept_one_eq_vertex_dropLast]
            exact mem_starSet_vertex (C := C) W.dropLast
        · have htpos : (0 : ℝ) < (t : ℝ) :=
            lt_of_le_of_ne t.2.1 (fun hh => ht0 (Subtype.ext hh.symm))
          have htlt : (t : ℝ) < 1 :=
            lt_of_le_of_ne t.2.2 (fun hh => ht1 (Subtype.ext hh))
          have hproj : proj (C := C) (ept W hW t)
              = OEdge.path (C := C) ((W.lastLetter hW).neg) t := by
            rw [proj_ept, path_neg_apply]
          rw [hproj] at hx
          rw [halfStar] at hx
          rcases hx with hx | hx
          · exact absurd (hx ▸ OEdge.path_mem_openCell (C := C) htpos htlt)
              (vpt_not_mem_openCell_one (C := C) v _)
          · rw [Set.mem_iUnion] at hx
            obtain ⟨o', hx⟩ := hx
            rw [Set.mem_iUnion] at hx
            obtain ⟨ho', s, hs, hsx⟩ := hx
            simp only [Set.mem_setOf_eq] at hs
            have hs0 : s ≠ 0 := by
              intro hs0
              have hmem : proj (C := C) (ept W hW t) ∈
                  Topology.RelCWComplex.openCell (C := C) 1 (W.lastLetter hW).neg.cell := by
                rw [hproj]
                exact OEdge.path_mem_openCell (C := C) htpos htlt
              have hv : proj (C := C) (ept W hW t) = vpt (C := C) v :=
                calc proj (C := C) (ept W hW t)
                      = OEdge.path (C := C) ((W.lastLetter hW).neg) t := hproj
                  _ = OEdge.path (C := C) o' s := hsx.symm
                  _ = OEdge.path (C := C) o' 0 := by rw [hs0]
                  _ = vpt (C := C) o'.src := (OEdge.path (C := C) o').source
                  _ = vpt (C := C) v := congrArg (vpt (C := C)) ho'
              exact vpt_not_mem_openCell_one (C := C) v _ (hv ▸ hmem)
            have hsR : (0 : ℝ) < (s : ℝ) ∧ (s : ℝ) < 1 :=
              ⟨lt_of_le_of_ne s.2.1 (fun hh => hs0 (Subtype.ext hh.symm)),
               lt_of_lt_of_le hs (by norm_num)⟩
            have hsx' : OEdge.path (C := C) ((W.lastLetter hW).neg) t
                = OEdge.path (C := C) o' s := hsx.symm
            rcases path_apply_eq (C := C) (o := (W.lastLetter hW).neg) (o' := o')
              (u := t) (v := s) ⟨htpos, htlt⟩ hsR hsx' with ⟨ho, hts⟩ | ⟨ho, hts⟩
            · refine ⟨W, ?_, ?_⟩
              · rw [ho, OEdge.src_neg, ← RWalk.endOf_eq_lastLetter_tgt] at ho'
                exact ho'
              · simp only [starSet, Set.mem_union, Set.mem_setOf_eq]
                exact Or.inl (Or.inr ⟨hW, t, by rw [hts]; exact hs, rfl⟩)
            · have ho'' : o' = W.lastLetter hW := by rw [ho, OEdge.neg_neg]
              refine ⟨W.dropLast, ?_, ?_⟩
              · rw [ho'', ← RWalk.endOf_dropLast_eq_lastLetter_src] at ho'
                exact ho'
              · simp only [starSet, Set.mem_union, Set.mem_setOf_eq]
                exact Or.inr ⟨W, hW, t, rfl, by rw [hts, unitInterval.coe_symm_eq]; linarith, rfl⟩
/-- Distinct stars of vertices of the universal cover are disjoint. -/
lemma starSet_disjoint {W W' : RWalk (C := C) u} (h : W ≠ W') :
    Disjoint (starSet (C := C) W) (starSet (C := C) W') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  induction x using Quotient.inductionOn with
  | h y =>
    rcases y with W'' | ⟨⟨W'', hW''⟩, t⟩
    · have hv : (Quotient.mk _ (Sum.inl W'') : Tree (C := C) u) = vertex W'' := rfl
      rw [hv] at hx hx'
      exact h ((eq_of_vertex_mem_starSet hx).symm.trans (eq_of_vertex_mem_starSet hx'))
    · have hxe : (Quotient.mk _ (Sum.inr (⟨W'', hW''⟩, t)) : Tree (C := C) u) =
          ept W'' hW'' t := rfl
      rw [hxe] at hx hx'
      have h1 := (ept_mem_starSet_iff (C := C) (W := W) (W' := W'')
        (hW' := hW'') (t := t)).mp hx
      have h2 := (ept_mem_starSet_iff (C := C) (W := W') (W' := W'')
        (hW' := hW'') (t := t)).mp hx'
      rcases h1 with ⟨hWW'', ht⟩ | ⟨hd, ht⟩ <;> rcases h2 with ⟨hW'W'', ht'⟩ | ⟨hd', ht'⟩
      · exact h (hWW''.symm.trans hW'W'')
      · exact absurd ht' (by linarith [ht])
      · exact absurd ht (by linarith [ht'])
      · exact h (hd.symm.trans hd')

/-- **The fibre of the projection over a vertex is discrete.** -/
lemma discreteTopology_fiber_vertex (u : Topology.CWComplex.cell C 0)
    (v : Topology.CWComplex.cell C 0) :
    DiscreteTopology (proj (C := C) (u := u) ⁻¹' {vpt (C := C) v}) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro a
  have ha : proj (C := C) (u := u) a.1 ∈ halfStar (C := C) v := by
    rw [a.2]; exact vpt_mem_halfStar (C := C) v
  obtain ⟨W, hWe, hWa⟩ := exists_starSet_of_proj_mem_halfStar (C := C) ha
  have haW : a.1 = vertex W := by
    obtain ⟨W'', hW''e, haW''⟩ := exists_vertex_of_proj_eq (C := C) (x := a.1) a.2
    have hW''W : W'' = W := eq_of_vertex_mem_starSet (by rw [← haW'']; exact hWa)
    rw [haW'', hW''W]
  have hsing : ({(a : proj (C := C) (u := u) ⁻¹' {vpt (C := C) v})} : Set _) =
      Subtype.val ⁻¹' starSet (C := C) W := by
    ext b
    constructor
    · intro hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact hWa
    · intro hb
      rw [Set.mem_singleton_iff]
      refine Subtype.ext ?_
      obtain ⟨W', hW'e, hbW'⟩ := exists_vertex_of_proj_eq (C := C) (x := b.1) b.2
      have hW'W : W' = W := eq_of_vertex_mem_starSet (by rw [← hbW']; exact hb)
      rw [hbW', hW'W, haW]
  rw [hsing]
  exact (isOpen_starSet (C := C) W).preimage continuous_subtype_val

/-! ## The star of a vertex of the tree with prescribed radii -/

/-- The radius attached to an oriented edge, in the orientation of the edge. -/
def epsRad (δt δf : Topology.CWComplex.cell C 1 → unitInterval)
    (o : OEdge (C := C)) : ℝ :=
  if o.dir then (δt o.cell : ℝ) else (δf o.cell : ℝ)

@[simp] lemma epsRad_mk_true (δt δf : Topology.CWComplex.cell C 1 → unitInterval)
    (e : Topology.CWComplex.cell C 1) :
    epsRad δt δf (OEdge.mk e true) = (δt e : ℝ) := rfl

@[simp] lemma epsRad_mk_false (δt δf : Topology.CWComplex.cell C 1 → unitInterval)
    (e : Topology.CWComplex.cell C 1) :
    epsRad δt δf (OEdge.mk e false) = (δf e : ℝ) := rfl

/-- **The star of a vertex of the universal cover with prescribed radii**: the vertex itself, the
part of the edge above `W` up to parameter `δ` (the "parent" leg) and the parts of the edges above
`W ++ [o]` from parameter `1 - δ` (the "child" legs). -/
def starPt (W : RWalk (C := C) u) (δt δf : Topology.CWComplex.cell C 1 → unitInterval) :
    Set (Tree (C := C) u) :=
  {x | x = vertex W} ∪
    {x | ∃ (hW : W.1 ≠ []) (t : unitInterval),
        (t : ℝ) < epsRad δt δf (W.lastLetter hW).neg ∧ x = ept W hW t} ∪
    {x | ∃ (W' : RWalk (C := C) u) (hW' : W'.1 ≠ []), W'.dropLast = W ∧
        ∃ (t : unitInterval),
          (1 : ℝ) - epsRad δt δf (W'.lastLetter hW') < (t : ℝ) ∧ x = ept W' hW' t}

lemma mem_starPt_vertex (W : RWalk (C := C) u)
    (δt δf : Topology.CWComplex.cell C 1 → unitInterval) :
    vertex W ∈ starPt (C := C) W δt δf := by
  rw [starPt]; exact Or.inl (Or.inl rfl)

lemma mem_starPt_parent {W : RWalk (C := C) u} {δt δf : Topology.CWComplex.cell C 1 → unitInterval}
    {hW : W.1 ≠ []} {t : unitInterval}
    (ht : (t : ℝ) < epsRad δt δf (W.lastLetter hW).neg) :
    ept (C := C) W hW t ∈ starPt (C := C) W δt δf := by
  rw [starPt]; simp only [Set.mem_union, Set.mem_setOf_eq]
  exact Or.inl (Or.inr ⟨hW, t, ht, rfl⟩)

lemma mem_starPt_child {W W' : RWalk (C := C) u}
    {δt δf : Topology.CWComplex.cell C 1 → unitInterval} {hW' : W'.1 ≠ []} {t : unitInterval}
    (hd : W'.dropLast = W)
    (ht : (1 : ℝ) - epsRad δt δf (W'.lastLetter hW') < (t : ℝ)) :
    ept (C := C) W' hW' t ∈ starPt (C := C) W δt δf := by
  rw [starPt]; simp only [Set.mem_union, Set.mem_setOf_eq]
  exact Or.inr ⟨W', hW', hd, t, ht, rfl⟩

/-- **The path of an oriented edge, started at the source, lies in the eps-star of its source.** -/
lemma mem_epsStar_of_path {δt δf : Topology.CWComplex.cell C 1 → unitInterval}
    {o : OEdge (C := C)} {t : unitInterval}
    (ht : (t : ℝ) < epsRad δt δf o) :
    OEdge.path (C := C) o t ∈ epsStar (C := C) o.src δt δf := by
  rcases o with ⟨f, b⟩
  cases b
  · rw [path_mk_false]
    refine Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨rfl, t, ?_, rfl⟩⟩))
    simpa using ht
  · rw [path_mk_true]
    refine Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨rfl, t, ?_, rfl⟩⟩))
    simpa using ht

/-- **The star of a vertex of the tree projects into the eps-star of the corresponding vertex.** -/
lemma proj_mem_epsStar_of_mem_starPt {W : RWalk (C := C) u}
    {δt δf : Topology.CWComplex.cell C 1 → unitInterval} {x : Tree (C := C) u}
    (hx : x ∈ starPt (C := C) W δt δf) :
    proj (C := C) x ∈ epsStar (C := C) W.endOf δt δf := by
  simp only [starPt, Set.mem_union, Set.mem_setOf_eq] at hx
  rcases hx with (hx | ⟨hW, t, ht, rfl⟩) | ⟨W', hW', hd, t, ht, rfl⟩
  · rw [hx, proj_vertex]
    exact Or.inl rfl
  · rw [proj_ept, ← path_neg_apply (W.lastLetter hW) t]
    have h1 : ((W.lastLetter hW).neg).src = W.endOf := by
      rw [OEdge.src_neg, RWalk.endOf_eq_lastLetter_tgt]
    have hset : epsStar (C := C) ((W.lastLetter hW).neg).src δt δf =
        epsStar (C := C) W.endOf δt δf :=
      congrArg (fun v => epsStar (C := C) v δt δf) h1
    rw [← hset]
    exact mem_epsStar_of_path (C := C) (δt := δt) (δf := δf)
      (o := (W.lastLetter hW).neg) ht
  · rw [proj_ept]
    have hs : ((unitInterval.symm t : unitInterval) : ℝ) <
        epsRad δt δf (W'.lastLetter hW') := by
      rw [unitInterval.coe_symm_eq]; linarith [ht]
    have hsrc : (W'.lastLetter hW').src = W.endOf := by
      rw [← RWalk.endOf_dropLast_eq_lastLetter_src W' hW', hd]
    have hset : epsStar (C := C) (W'.lastLetter hW').src δt δf =
        epsStar (C := C) W.endOf δt δf :=
      congrArg (fun v => epsStar (C := C) v δt δf) hsrc
    rw [← hset]
    exact mem_epsStar_of_path (C := C) (δt := δt) (δf := δf)
      (o := W'.lastLetter hW') hs

/-- **Every point of the eps-star of a vertex of the one-skeleton is the projection of a point of
the corresponding star of the tree.** -/
lemma exists_mem_starPt_of_mem_epsStar {W : RWalk (C := C) u}
    {δt δf : Topology.CWComplex.cell C 1 → unitInterval} {y : Y}
    (hy : y ∈ epsStar (C := C) W.endOf δt δf) :
    ∃ x ∈ starPt (C := C) W δt δf, proj (C := C) x = y := by
  rw [epsStar] at hy
  rcases hy with hy | hy | hy
  · rw [Set.mem_singleton_iff] at hy
    exact ⟨vertex W, mem_starPt_vertex _ _ _, by rw [hy, proj_vertex]⟩
  · rw [Set.mem_iUnion] at hy
    obtain ⟨e, hy⟩ := hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨he, hy⟩ := hy
    obtain ⟨t, ht, rfl⟩ := hy
    simp only [Set.mem_setOf_eq] at ht
    have ho : (OEdge.mk e true).src = W.endOf := by simpa using he
    have hchild : ∀ (hred : Reduced (C := C) (W.1 ++ [OEdge.mk e true])),
        ∃ x ∈ starPt (C := C) W δt δf, proj (C := C) x = fwdPath (C := C) e t := by
      intro hred
      have hwalk := isWalk_snoc W ho
      set W' : RWalk (C := C) u := ⟨W.1 ++ [OEdge.mk e true], hwalk, hred⟩ with hW'def
      have hne' : W'.1 ≠ [] := by rw [hW'def]; simp
      have hdrop : W'.dropLast = W := dropLast_snoc W hwalk hred
      have hlast : W'.lastLetter hne' = OEdge.mk e true := lastLetter_snoc W hwalk hred hne'
      refine ⟨ept W' hne' (unitInterval.symm t), mem_starPt_child hdrop ?_, ?_⟩
      · rw [hlast, epsRad_mk_true, unitInterval.coe_symm_eq]
        linarith
      · rw [proj_ept, hlast, path_mk_true]
        show fwdPath (C := C) e (unitInterval.symm (unitInterval.symm t)) = fwdPath (C := C) e t
        rw [unitInterval.symm_symm]
    by_cases hW : W.1 = []
    · exact hchild (reduced_snoc W fun h' => absurd hW h')
    · by_cases hcase : OEdge.mk e true = (W.lastLetter hW).neg
      · refine ⟨ept W hW t, mem_starPt_parent ?_, ?_⟩
        · rw [← hcase, epsRad_mk_true]; exact ht
        · rw [proj_ept, ← path_neg_apply, ← hcase, path_mk_true]
          rfl
      · exact hchild (reduced_snoc W fun h' hc =>
          hcase (hc.trans (congrArg OEdge.neg (List.getLast_congr h' hW rfl))))
  · rw [Set.mem_iUnion] at hy
    obtain ⟨e, hy⟩ := hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨he, hy⟩ := hy
    obtain ⟨t, ht, rfl⟩ := hy
    simp only [Set.mem_setOf_eq] at ht
    have ho : (OEdge.mk e false).src = W.endOf := by simpa using he
    have hchild : ∀ (hred : Reduced (C := C) (W.1 ++ [OEdge.mk e false])),
        ∃ x ∈ starPt (C := C) W δt δf,
          proj (C := C) x = (fwdPath (C := C) e).symm t := by
      intro hred
      have hwalk := isWalk_snoc W ho
      set W' : RWalk (C := C) u := ⟨W.1 ++ [OEdge.mk e false], hwalk, hred⟩ with hW'def
      have hne' : W'.1 ≠ [] := by rw [hW'def]; simp
      have hdrop : W'.dropLast = W := dropLast_snoc W hwalk hred
      have hlast : W'.lastLetter hne' = OEdge.mk e false := lastLetter_snoc W hwalk hred hne'
      refine ⟨ept W' hne' (unitInterval.symm t), mem_starPt_child hdrop ?_, ?_⟩
      · rw [hlast, epsRad_mk_false, unitInterval.coe_symm_eq]
        linarith
      · rw [proj_ept, hlast, path_mk_false]
        show ((fwdPath (C := C) e).symm) (unitInterval.symm (unitInterval.symm t)) =
          ((fwdPath (C := C) e).symm) t
        rw [unitInterval.symm_symm]
    by_cases hW : W.1 = []
    · exact hchild (reduced_snoc W fun h' => absurd hW h')
    · by_cases hcase : OEdge.mk e false = (W.lastLetter hW).neg
      · refine ⟨ept W hW t, mem_starPt_parent ?_, ?_⟩
        · rw [← hcase, epsRad_mk_false]; exact ht
        · rw [proj_ept, ← path_neg_apply, ← hcase, path_mk_false]
          rfl
      · exact hchild (reduced_snoc W fun h' hc =>
          hcase (hc.trans (congrArg OEdge.neg (List.getLast_congr h' hW rfl))))


/-! ## Radii for the star of a tree vertex -/

/-- From an open subset of the unit interval containing `0`, extract a positive radius. -/
lemma exists_radius_zero {S : Set unitInterval} (hS : IsOpen S) (h0 : (0 : unitInterval) ∈ S) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : unitInterval, (t : ℝ) < ε → t ∈ S := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hS 0 h0
  refine ⟨ε, hε, fun t ht => hsub ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
  have h0' : ((0 : unitInterval) : ℝ) = 0 := rfl
  rw [h0', sub_zero, abs_of_nonneg (unitInterval.nonneg t)]
  exact ht

/-- From an open subset of the unit interval containing `1`, extract a positive radius. -/
lemma exists_radius_one {S : Set unitInterval} (hS : IsOpen S) (h1 : (1 : unitInterval) ∈ S) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : unitInterval, 1 - ε < (t : ℝ) → t ∈ S := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hS 1 h1
  refine ⟨ε, hε, fun t ht => hsub ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
  have h1' : ((1 : unitInterval) : ℝ) = 1 := rfl
  rw [h1', abs_of_nonpos (by linarith [unitInterval.le_one t])]
  linarith

/-- **Radii for the star of a vertex of the tree inside an open set.**  If `U` is an open
neighbourhood of `vertex W`, there are radii `δt`, `δf` (all smaller than `1/2`, positive in the
incident orientations) such that the star `starPt W δt δf` is contained in `U`. -/
lemma exists_radii_starPt {W : RWalk (C := C) u} {U : Set (Tree (C := C) u)}
    (hU : IsOpen U) (hWU : vertex W ∈ U) :
    ∃ (δt δf : Topology.CWComplex.cell C 1 → unitInterval),
      starPt (C := C) W δt δf ⊆ U ∧
      (∀ e, (δt e : ℝ) < 1 / 2) ∧ (∀ e, (δf e : ℝ) < 1 / 2) ∧
      (∀ e, srcIdx (C := C) e = W.endOf → 0 < (δt e : ℝ)) ∧
      (∀ e, tgtIdx (C := C) e = W.endOf → 0 < (δf e : ℝ)) := by
  classical
  have hpar : ∀ (hW : W.1 ≠ []), ∃ ε : ℝ, 0 < ε ∧ ∀ t : unitInterval, (t : ℝ) < ε →
      ept (C := C) W hW t ∈ U := by
    intro hW
    have h0 : (0 : unitInterval) ∈ {t : unitInterval | ept (C := C) W hW t ∈ U} := by
      show ept (C := C) W hW 0 ∈ U
      rw [ept_zero_eq_vertex W hW]
      exact hWU
    exact exists_radius_zero (hU.preimage (continuous_ept W hW)) h0
  have hchi : ∀ (W' : RWalk (C := C) u) (hW' : W'.1 ≠ []), W'.dropLast = W →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : unitInterval, 1 - ε < (t : ℝ) → ept (C := C) W' hW' t ∈ U := by
    intro W' hW' hd
    have h1 : (1 : unitInterval) ∈ {t : unitInterval | ept (C := C) W' hW' t ∈ U} := by
      show ept (C := C) W' hW' 1 ∈ U
      rw [ept_one_eq_vertex_dropLast W' hW', hd]
      exact hWU
    exact exists_radius_one (hU.preimage (continuous_ept W' hW')) h1
  let pb : ℝ := if hW : W.1 = [] then 1 else Classical.choose (hpar hW)
  have pb_pos : 0 < pb := by
    by_cases hW : W.1 = []
    · simp only [pb, dif_pos hW]; norm_num
    · simp only [pb, dif_neg hW]; exact (Classical.choose_spec (hpar hW)).1
  have pb_spec : ∀ (hW : W.1 ≠ []), ∀ t : unitInterval, (t : ℝ) < pb →
      ept (C := C) W hW t ∈ U := by
    intro hW t ht
    have h : pb = Classical.choose (hpar hW) := by simp only [pb, dif_neg hW]
    rw [h] at ht
    exact (Classical.choose_spec (hpar hW)).2 t ht
  let cb : (o : OEdge (C := C)) → o.src = W.endOf → ℝ := fun o ho =>
    if hred : Reduced (C := C) (W.1 ++ [o]) then
      Classical.choose (hchi ⟨W.1 ++ [o], isWalk_snoc W ho, hred⟩ (by simp)
        (dropLast_snoc W (isWalk_snoc W ho) hred))
    else 1
  have cb_spec : ∀ (o : OEdge (C := C)) (ho : o.src = W.endOf)
      (hred : Reduced (C := C) (W.1 ++ [o])) (t : unitInterval),
      1 - cb o ho < (t : ℝ) →
        ept (C := C) (⟨W.1 ++ [o], isWalk_snoc W ho, hred⟩ : RWalk (C := C) u) (by simp) t ∈ U := by
    intro o ho hred t ht
    have h : cb o ho = Classical.choose (hchi ⟨W.1 ++ [o], isWalk_snoc W ho, hred⟩ (by simp)
        (dropLast_snoc W (isWalk_snoc W ho) hred)) := by simp only [cb, dif_pos hred]
    rw [h] at ht
    exact (Classical.choose_spec (hchi ⟨W.1 ++ [o], isWalk_snoc W ho, hred⟩ (by simp)
      (dropLast_snoc W (isWalk_snoc W ho) hred))).2 t ht
  have cb_pos : ∀ (o : OEdge (C := C)) (ho : o.src = W.endOf), 0 < cb o ho := by
    intro o ho
    by_cases hred : Reduced (C := C) (W.1 ++ [o])
    · simp only [cb, dif_pos hred]
      exact (Classical.choose_spec (hchi ⟨W.1 ++ [o], isWalk_snoc W ho, hred⟩ (by simp)
        (dropLast_snoc W (isWalk_snoc W ho) hred))).1
    · simp only [cb, dif_neg hred]; norm_num
  let radO : OEdge (C := C) → ℝ := fun o =>
    min (if h : o.src = W.endOf then cb o h else 1)
      (if _ : ∃ hW : W.1 ≠ [], (W.lastLetter hW).cell = o.cell then pb else 1)
  have radO_pos : ∀ o : OEdge (C := C), 0 < radO o := by
    intro o
    have h1 : 0 < (if h : o.src = W.endOf then cb o h else 1) := by
      by_cases h : o.src = W.endOf
      · rw [dif_pos h]; exact cb_pos o h
      · rw [dif_neg h]; norm_num
    have h2 : 0 < (if _ : ∃ hW : W.1 ≠ [], (W.lastLetter hW).cell = o.cell then pb else 1) := by
      by_cases h : ∃ hW : W.1 ≠ [], (W.lastLetter hW).cell = o.cell
      · rw [dif_pos h]; exact pb_pos
      · rw [dif_neg h]; norm_num
    exact lt_min h1 h2
  let dt : Topology.CWComplex.cell C 1 → unitInterval := fun e =>
    ⟨min (1/4) (radO ⟨e, true⟩), le_min (by norm_num) (le_of_lt (radO_pos _)),
      (min_le_left _ _).trans (by norm_num)⟩
  let df : Topology.CWComplex.cell C 1 → unitInterval := fun e =>
    ⟨min (1/4) (radO ⟨e, false⟩), le_min (by norm_num) (le_of_lt (radO_pos _)),
      (min_le_left _ _).trans (by norm_num)⟩
  have hdt_val : ∀ e, (dt e : ℝ) = min (1/4) (radO ⟨e, true⟩) := fun e => rfl
  have hdf_val : ∀ e, (df e : ℝ) = min (1/4) (radO ⟨e, false⟩) := fun e => rfl
  have hrad : ∀ o : OEdge (C := C), epsRad dt df o = min (1/4) (radO o) := by
    intro o
    cases o with
    | mk c d => cases d <;> rfl
  have heps_le_cb : ∀ (o : OEdge (C := C)) (ho : o.src = W.endOf), epsRad dt df o ≤ cb o ho := by
    intro o ho
    rw [hrad o]
    have h1 : (if h : o.src = W.endOf then cb o h else 1) ≤ cb o ho := by
      by_cases h : o.src = W.endOf
      · rw [dif_pos h]
      · exact absurd ho h
    exact (min_le_right _ _).trans ((min_le_left _ _).trans h1)
  have heps_le_pb : ∀ (hW : W.1 ≠ []), epsRad dt df (W.lastLetter hW).neg ≤ pb := by
    intro hW
    rw [hrad]
    have h2 : (if _ : ∃ hW' : W.1 ≠ [], (W.lastLetter hW').cell = ((W.lastLetter hW).neg).cell
        then pb else 1) ≤ pb := by
      have hP : ∃ hW' : W.1 ≠ [], (W.lastLetter hW').cell = ((W.lastLetter hW).neg).cell :=
        ⟨hW, rfl⟩
      rw [dif_pos hP]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans h2)
  refine ⟨dt, df, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [starPt, Set.mem_union, Set.mem_setOf_eq] at hx
    rcases hx with (hx | ⟨hW, t, ht, rfl⟩) | ⟨W', hW', hd, t, ht, rfl⟩
    · rw [hx]; exact hWU
    · exact pb_spec hW t (lt_of_lt_of_le ht (heps_le_pb hW))
    · have ho : (W'.lastLetter hW').src = W.endOf := by
        rw [← RWalk.endOf_dropLast_eq_lastLetter_src W' hW', hd]
      have hdval : W'.1.dropLast = W.1 := by
        have := congrArg (fun x : RWalk (C := C) u => x.1) hd
        simpa only [RWalk.dropLast_val] using this
      have hlist : W'.1 = W.1 ++ [W'.lastLetter hW'] := by
        rw [← List.dropLast_append_getLast hW', hdval]
        rfl
      have hred : Reduced (C := C) (W.1 ++ [W'.lastLetter hW']) := by
        rw [← hlist]; exact W'.2.2
      have hW'eq : W' = (⟨W.1 ++ [W'.lastLetter hW'], isWalk_snoc W ho, hred⟩ :
          RWalk (C := C) u) := Subtype.ext hlist
      have hb : 1 - cb (W'.lastLetter hW') ho < (t : ℝ) := by
        have hle := heps_le_cb (W'.lastLetter hW') ho
        linarith
      have heq : ept (C := C) W' hW' t = ept (C := C) (⟨W.1 ++ [W'.lastLetter hW'],
          isWalk_snoc W ho, hred⟩ : RWalk (C := C) u) (by simp) t :=
        ept_congr hW'eq hW' (by simp) t
      rw [heq]
      exact cb_spec (W'.lastLetter hW') ho hred t hb
  · intro e
    rw [hdt_val]
    exact (min_le_left _ _).trans_lt (by norm_num)
  · intro e
    rw [hdf_val]
    exact (min_le_left _ _).trans_lt (by norm_num)
  · intro e _
    rw [hdt_val]
    exact lt_min (by norm_num) (radO_pos _)
  · intro e _
    rw [hdf_val]
    exact lt_min (by norm_num) (radO_pos _)


/-! ## Openness of the cells and of the characteristic maps -/

/-- **In a one-dimensional CW complex, the open cells are open.** -/
theorem isOpen_openCell_one {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n))
    (e : Topology.RelCWComplex.cell (Set.univ : Set X) 1) :
    IsOpen (Topology.RelCWComplex.openCell (C := (Set.univ : Set X)) 1 e) := by
  classical
  rw [← isClosed_compl_iff]
  refine Topology.CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    (C := (Set.univ : Set X)) (by intro x _; trivial) ?_
  intro n hn j
  rcases Nat.lt_or_ge 1 n with h1n | h1n
  · right
    exact ((h2 n (by omega)).false j).elim
  · obtain rfl : n = 1 := by omega
    have hfr : Disjoint (Topology.RelCWComplex.cellFrontier (C := Set.univ) 1 j)
        (Topology.RelCWComplex.openCell (C := Set.univ) 1 e) := by
      obtain ⟨x, y, hxy⟩ := Topology.CWComplex.exists_cellFrontier_one_eq (C := Set.univ) j
      rw [hxy]
      refine disjoint_union_left.mpr ⟨?_, ?_⟩
      · rw [Topology.RelCWComplex.closedCell_zero_eq_singleton]
        have hd := Topology.RelCWComplex.disjoint_openCell_of_ne (C := Set.univ)
          (n := 0) (m := 1) (i := x) (j := e)
          (by intro h; exact absurd (Sigma.mk.inj h).1 (by omega))
        rwa [Topology.RelCWComplex.openCell_zero_eq_singleton] at hd
      · rw [Topology.RelCWComplex.closedCell_zero_eq_singleton]
        have hd := Topology.RelCWComplex.disjoint_openCell_of_ne (C := Set.univ)
          (n := 0) (m := 1) (i := y) (j := e)
          (by intro h; exact absurd (Sigma.mk.inj h).1 (by omega))
        rwa [Topology.RelCWComplex.openCell_zero_eq_singleton] at hd
    by_cases hj : j = e
    · rw [hj] at hfr ⊢
      right
      have hfe : (Topology.RelCWComplex.openCell (C := Set.univ) 1 e)ᶜ ∩
          Topology.RelCWComplex.closedCell (C := Set.univ) 1 e =
          Topology.RelCWComplex.cellFrontier (C := Set.univ) 1 e := by
        rw [← Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq]
        constructor
        · rintro ⟨ha, hb | hb⟩
          · exact hb
          · exact absurd hb ha
        · intro hb; exact ⟨fun hc => disjoint_left.1 hfr hb hc, Or.inl hb⟩
      rw [hfe]
      exact Topology.RelCWComplex.isClosed_cellFrontier
    · right
      have hcc : Disjoint (Topology.RelCWComplex.closedCell (C := Set.univ) 1 j)
          (Topology.RelCWComplex.openCell (C := Set.univ) 1 e) := by
        rw [← Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell]
        refine disjoint_union_left.mpr ⟨hfr, ?_⟩
        exact Topology.RelCWComplex.disjoint_openCell_of_ne (C := Set.univ)
          (by intro h; exact absurd (eq_of_heq (Sigma.mk.inj h).2) hj)
      have heq : (Topology.RelCWComplex.openCell (C := Set.univ) 1 e)ᶜ ∩
          Topology.RelCWComplex.closedCell (C := Set.univ) 1 j =
          Topology.RelCWComplex.closedCell (C := Set.univ) 1 j := by
        ext x
        exact ⟨fun h => h.2, fun h => ⟨fun hc => disjoint_left.1 hcc h hc, h⟩⟩
      rw [heq]
      exact Topology.RelCWComplex.isClosed_closedCell

/-- **The image of an open subset of the ball under the characteristic map of a `1`-cell is
open.** -/
theorem isOpen_image_map_of_isOpen {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n))
    (e : Topology.RelCWComplex.cell (Set.univ : Set X) 1) {B : Set (Fin 1 → ℝ)}
    (hB : IsOpen B) (hBsub : B ⊆ Metric.ball (0 : Fin 1 → ℝ) 1) :
    IsOpen (Topology.RelCWComplex.map (C := (Set.univ : Set X)) 1 e '' B) := by
  have hsrc : B ⊆ (Topology.RelCWComplex.map (C := Set.univ) 1 e).source := by
    rw [Topology.RelCWComplex.source_eq]; exact hBsub
  rw [(Topology.RelCWComplex.map (C := Set.univ) 1 e).image_eq_target_inter_inv_preimage hsrc]
  have htgt : (Topology.RelCWComplex.map (C := Set.univ) 1 e).target =
      Topology.RelCWComplex.openCell (C := Set.univ) 1 e := by
    rw [← PartialEquiv.image_source_eq_target]
    simp only [Topology.RelCWComplex.source_eq, Topology.RelCWComplex.openCell]
  have hcont := Topology.RelCWComplex.continuousOn_symm (C := Set.univ) 1 e
  have hopenT : IsOpen (Topology.RelCWComplex.map (C := Set.univ) 1 e).target := by
    rw [htgt]; exact isOpen_openCell_one h2 e
  exact (continuousOn_open_iff hopenT).mp hcont B hB


/-! ## The projection of the universal cover is an open map -/

/-- From an open subset of the unit interval containing an interior point, extract a symmetric
positive radius staying inside the set. -/
lemma exists_eps_of_isOpen_mem {S : Set unitInterval} (hS : IsOpen S) {t : unitInterval}
    (ht : t ∈ S) (h0 : 0 < (t : ℝ)) (h1 : (t : ℝ) < 1) :
    ∃ ε : ℝ, 0 < ε ∧ 0 < (t : ℝ) - ε ∧ (t : ℝ) + ε < 1 ∧
      ∀ s : unitInterval, (t : ℝ) - ε < (s : ℝ) → (s : ℝ) < (t : ℝ) + ε → s ∈ S := by
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp hS t ht
  refine ⟨min (ρ / 2) (min ((t : ℝ) / 2) ((1 - (t : ℝ)) / 2)), ?_, ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  · have h2 := min_le_right (ρ / 2) (min ((t : ℝ) / 2) ((1 - (t : ℝ)) / 2))
    have h3 := min_le_left ((t : ℝ) / 2) ((1 - (t : ℝ)) / 2)
    linarith
  · have h2 := min_le_right (ρ / 2) (min ((t : ℝ) / 2) ((1 - (t : ℝ)) / 2))
    have h3 := min_le_right ((t : ℝ) / 2) ((1 - (t : ℝ)) / 2)
    linarith
  · intro s hs0 hs1
    apply hsub
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
    have h2 := min_le_left (ρ / 2) (min ((t : ℝ) / 2) ((1 - (t : ℝ)) / 2))
    constructor <;> linarith

lemma norm_fin_one (z : Fin 1 → ℝ) : ‖z‖ = |z 0| := by
  simp only [Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sup_singleton, coe_nnnorm, Real.norm_eq_abs]

/-- The parametrisation of an edge by the ball, in either orientation. -/
lemma OEdge.path_symm_apply_mk (e : Topology.CWComplex.cell C 1) (b : Bool) (s : unitInterval) :
    (OEdge.path (C := C) (OEdge.mk e b)).symm s =
      Topology.RelCWComplex.map (C := C) 1 e
        (segF (if b then unitInterval.symm s else s)) := by
  cases b
  · show (OEdge.path (C := C) (OEdge.mk e false)).symm s = _
    rw [if_neg (by simp : ¬((false : Bool) = true))]
    exact path_symm_symm_apply (γ := fwdPath (C := C) e) s
  · show (OEdge.path (C := C) (OEdge.mk e true)).symm s = _
    rw [if_pos rfl]
    rfl

/-- **The projection of the universal cover is an open map.** -/
theorem isOpenMap_proj {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n))
    (u : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    IsOpenMap (proj (C := (Set.univ : Set X)) (u := u)) := by
  classical
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hxU, rfl⟩
  have hvertex : ∀ (W₀ : RWalk (C := Set.univ) u), vertex W₀ ∈ U →
      proj (C := Set.univ) '' U ∈ 𝓝 (proj (C := Set.univ) (vertex W₀)) := by
    intro W₀ hW₀U
    obtain ⟨δt, δf, hsub, hlt1, hlt2, hpos1, hpos2⟩ :=
      exists_radii_starPt (C := Set.univ) hU hW₀U
    have hopen := isOpen_epsStar h2 W₀.endOf δt δf hlt1 hlt2 hpos1 hpos2
    have hbase : vpt (C := Set.univ) W₀.endOf ∈ epsStar (C := Set.univ) W₀.endOf δt δf :=
      Or.inl rfl
    refine Filter.mem_of_superset (hopen.mem_nhds hbase) ?_
    intro y' hy'
    obtain ⟨x', hx', hx'y'⟩ := exists_mem_starPt_of_mem_epsStar (C := Set.univ) hy'
    exact ⟨x', hsub hx', hx'y'⟩
  obtain ⟨x₀, rfl⟩ := Quotient.exists_rep x
  rcases x₀ with W | ⟨⟨W, hW⟩, t⟩
  · exact hvertex W hxU
  · show proj (C := Set.univ) '' U ∈ 𝓝 (proj (C := Set.univ) (ept W hW t))
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht0 | ht0
    · obtain rfl : t = 0 := Subtype.ext ht0.symm
      have hxU' : vertex W ∈ U := by
        rw [← ept_zero_eq_vertex W hW]
        exact hxU
      rw [ept_zero_eq_vertex W hW]
      exact hvertex W hxU'
    rcases eq_or_lt_of_le (unitInterval.le_one t) with ht1 | ht1
    · obtain rfl : t = 1 := Subtype.ext ht1
      have hxU' : vertex W.dropLast ∈ U := by
        rw [← ept_one_eq_vertex_dropLast W hW]
        exact hxU
      rw [ept_one_eq_vertex_dropLast W hW]
      exact hvertex W.dropLast hxU'
    · have hSopen : IsOpen {s : unitInterval | ept (C := Set.univ) W hW s ∈ U} :=
        hU.preimage (continuous_ept W hW)
      have htS : t ∈ {s : unitInterval | ept (C := Set.univ) W hW s ∈ U} := hxU
      obtain ⟨ε, hε, hε0, hε1, hεS⟩ := exists_eps_of_isOpen_mem hSopen htS ht0 ht1
      obtain ⟨e, b, hL⟩ : ∃ (e : Topology.CWComplex.cell (Set.univ : Set X) 1) (b : Bool),
          W.lastLetter hW = OEdge.mk e b :=
        ⟨(W.lastLetter hW).cell, (W.lastLetter hW).dir, rfl⟩
      have key : ∀ s : unitInterval, proj (C := Set.univ) (ept W hW s) =
          Topology.RelCWComplex.map (C := Set.univ) 1 e
            (segF (if b then unitInterval.symm s else s)) := by
        intro s
        rw [proj_ept, hL]
        exact OEdge.path_symm_apply_mk e b s
      cases b
      · -- the last letter is `⟨e,false⟩`
        set B : Set (Fin 1 → ℝ) :=
          {z | 2 * ((t : ℝ) - ε) - 1 < z 0 ∧ z 0 < 2 * ((t : ℝ) + ε) - 1} with hB
        have hBopen : IsOpen B := by
          rw [hB]
          exact (isOpen_lt continuous_const (continuous_apply 0)).inter
            (isOpen_lt (continuous_apply 0) continuous_const)
        have hBball : B ⊆ Metric.ball (0 : Fin 1 → ℝ) 1 := by
          intro z hz
          rw [hB] at hz
          simp only [Set.mem_setOf_eq] at hz
          rw [Metric.mem_ball, dist_zero_right, norm_fin_one, abs_lt]
          constructor <;> linarith [hz.1, hz.2, hε0, hε1]
        have hBmem : segF t ∈ B := by
          rw [hB]; simp only [Set.mem_setOf_eq]
          show 2 * ((t : ℝ) - ε) - 1 < 2 * (t : ℝ) - 1 ∧
            2 * (t : ℝ) - 1 < 2 * ((t : ℝ) + ε) - 1
          constructor <;> linarith
        have hsub2 : Topology.RelCWComplex.map (C := Set.univ) 1 e '' B ⊆
            proj (C := Set.univ) '' U := by
          rintro y' ⟨z, hzB, rfl⟩
          rw [hB] at hzB
          simp only [Set.mem_setOf_eq] at hzB
          set s : unitInterval := ⟨(z 0 + 1) / 2, by
            refine ⟨?_, ?_⟩ <;> linarith [hzB.1, hzB.2, hε0, hε1]⟩ with hs
          have hsval : (s : ℝ) = (z 0 + 1) / 2 := rfl
          have hseg : segF s = z := by
            funext i
            fin_cases i
            show 2 * (s : ℝ) - 1 = z 0
            rw [hsval]; ring
          have hst : (t : ℝ) - ε < (s : ℝ) ∧ (s : ℝ) < (t : ℝ) + ε := by
            rw [hsval]; constructor <;> linarith [hzB.1, hzB.2]
          refine ⟨ept (C := Set.univ) W hW s, hεS s hst.1 hst.2, ?_⟩
          rw [key s, if_neg (by simp : ¬((false : Bool) = true)), hseg]
        refine Filter.mem_of_superset
          (IsOpen.mem_nhds (isOpen_image_map_of_isOpen h2 e hBopen hBball) ?_) hsub2
        exact ⟨segF t, hBmem, by rw [key t, if_neg (by simp : ¬((false : Bool) = true))]⟩
      · -- the last letter is `⟨e,true⟩`
        set B : Set (Fin 1 → ℝ) :=
          {z | 2 * ((1 - (t : ℝ)) - ε) - 1 < z 0 ∧ z 0 < 2 * ((1 - (t : ℝ)) + ε) - 1} with hB
        have hBopen : IsOpen B := by
          rw [hB]
          exact (isOpen_lt continuous_const (continuous_apply 0)).inter
            (isOpen_lt (continuous_apply 0) continuous_const)
        have hBball : B ⊆ Metric.ball (0 : Fin 1 → ℝ) 1 := by
          intro z hz
          rw [hB] at hz
          simp only [Set.mem_setOf_eq] at hz
          rw [Metric.mem_ball, dist_zero_right, norm_fin_one, abs_lt]
          constructor <;> linarith [hz.1, hz.2, hε0, hε1]
        have hBmem : segF (unitInterval.symm t) ∈ B := by
          rw [hB]; simp only [Set.mem_setOf_eq]
          show 2 * ((1 - (t : ℝ)) - ε) - 1 < 2 * ((unitInterval.symm t : unitInterval) : ℝ) - 1 ∧
            2 * ((unitInterval.symm t : unitInterval) : ℝ) - 1 < 2 * ((1 - (t : ℝ)) + ε) - 1
          rw [unitInterval.coe_symm_eq]
          constructor <;> linarith
        have hsub2 : Topology.RelCWComplex.map (C := Set.univ) 1 e '' B ⊆
            proj (C := Set.univ) '' U := by
          rintro y' ⟨z, hzB, rfl⟩
          rw [hB] at hzB
          simp only [Set.mem_setOf_eq] at hzB
          set s : unitInterval := ⟨(z 0 + 1) / 2, by
            refine ⟨?_, ?_⟩ <;> linarith [hzB.1, hzB.2, hε0, hε1]⟩ with hs
          have hsval : (s : ℝ) = (z 0 + 1) / 2 := rfl
          have hseg : segF s = z := by
            funext i
            fin_cases i
            show 2 * (s : ℝ) - 1 = z 0
            rw [hsval]; ring
          have hst : (t : ℝ) - ε < ((unitInterval.symm s : unitInterval) : ℝ) ∧
              ((unitInterval.symm s : unitInterval) : ℝ) < (t : ℝ) + ε := by
            rw [unitInterval.coe_symm_eq, hsval]
            constructor <;> linarith [hzB.1, hzB.2]
          refine ⟨ept (C := Set.univ) W hW (unitInterval.symm s), hεS _ hst.1 hst.2, ?_⟩
          rw [key (unitInterval.symm s), if_pos rfl, unitInterval.symm_symm, hseg]
        refine Filter.mem_of_superset
          (IsOpen.mem_nhds (isOpen_image_map_of_isOpen h2 e hBopen hBball) ?_) hsub2
        exact ⟨segF (unitInterval.symm t), hBmem, by rw [key t, if_pos rfl]⟩


/-! ## The projection of the universal cover is a covering map -/

/-- The open edge above a nonempty reduced walk. -/
def edgeInt (W : RWalk (C := C) u) (hW : W.1 ≠ []) : Set (Tree (C := C) u) :=
  {x | ∃ s : unitInterval, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧ x = ept W hW s}

lemma unitInterval_ne_zero {t : unitInterval} (h : 0 < (t : ℝ)) : t ≠ 0 := by
  intro h0; rw [h0] at h; exact lt_irrefl 0 h

lemma unitInterval_ne_one {t : unitInterval} (h : (t : ℝ) < 1) : t ≠ 1 := by
  intro h1; rw [h1] at h; exact lt_irrefl 1 h

lemma unitInterval_pos_of_ne_zero {t : unitInterval} (h : t ≠ 0) : 0 < (t : ℝ) :=
  lt_of_le_of_ne (unitInterval.nonneg t) fun h0 => h (Subtype.ext h0.symm)

lemma unitInterval_lt_one_of_ne_one {t : unitInterval} (h : t ≠ 1) : (t : ℝ) < 1 :=
  lt_of_le_of_ne (unitInterval.le_one t) fun h1 => h (Subtype.ext h1)

lemma mem_edgeInt {W : RWalk (C := C) u} {hW : W.1 ≠ []} {s : unitInterval}
    (h0 : 0 < (s : ℝ)) (h1 : (s : ℝ) < 1) : ept (C := C) W hW s ∈ edgeInt W hW :=
  ⟨s, h0, h1, rfl⟩

lemma isOpen_edgeInt {W : RWalk (C := C) u} {hW : W.1 ≠ []} : IsOpen (edgeInt W hW) := by
  rw [isOpen_iff]
  intro W' hW'
  by_cases h : W' = W
  · have hslice : {t : unitInterval | ept (C := C) W' hW' t ∈ edgeInt W hW} =
        {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by
      ext t
      constructor
      · rintro ⟨s, hs0, hs1, hts⟩
        rcases eq_or_ne t 0 with ht0 | ht0
        · rw [ht0, ept_zero_eq_vertex] at hts
          exact absurd hts.symm (ept_ne_vertex (unitInterval_ne_zero hs0) (unitInterval_ne_one hs1))
        · rcases eq_or_ne t 1 with ht1 | ht1
          · rw [ht1, ept_one_eq_vertex_dropLast] at hts
            exact absurd hts.symm (ept_ne_vertex (unitInterval_ne_zero hs0) (unitInterval_ne_one hs1))
          · have hts' := (ept_eq_of_ne_endpoints ht0 ht1 hts).2
            exact ⟨by rw [hts']; exact hs0, by rw [hts']; exact hs1⟩
      · rintro ⟨ht0, ht1⟩
        exact ⟨t, ht0, ht1, ept_congr h hW' hW t⟩
    rw [hslice]
    exact (isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const)
  · have hslice : {t : unitInterval | ept (C := C) W' hW' t ∈ edgeInt W hW} = ∅ := by
      ext t
      constructor
      · rintro ⟨s, hs0, hs1, hts⟩
        rcases eq_or_ne t 0 with ht0 | ht0
        · rw [ht0, ept_zero_eq_vertex] at hts
          exact absurd hts.symm (ept_ne_vertex (unitInterval_ne_zero hs0) (unitInterval_ne_one hs1))
        · rcases eq_or_ne t 1 with ht1 | ht1
          · rw [ht1, ept_one_eq_vertex_dropLast] at hts
            exact absurd hts.symm (ept_ne_vertex (unitInterval_ne_zero hs0) (unitInterval_ne_one hs1))
          · exact absurd (ept_eq_of_ne_endpoints ht0 ht1 hts).1 h
      · intro ht; exact absurd ht (Set.notMem_empty t)
    rw [hslice]
    exact isOpen_empty

lemma proj_image_edgeInt {W : RWalk (C := C) u} {hW : W.1 ≠ []} :
    proj (C := C) '' edgeInt W hW =
      Topology.RelCWComplex.openCell (C := C) 1 (W.lastLetter hW).cell := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨x, ⟨s, hs0, hs1, rfl⟩, rfl⟩
    exact proj_ept_mem_openCell (C := C) hs0 hs1
  · intro y hy
    have hy' : y ∈ Topology.RelCWComplex.map (C := C) 1 (W.lastLetter hW).cell ''
        Metric.ball (0 : Fin 1 → ℝ) 1 := hy
    obtain ⟨z, hz, hzy⟩ := hy'
    obtain ⟨e, b, hL⟩ : ∃ (e : Topology.CWComplex.cell C 1) (b : Bool),
        W.lastLetter hW = OEdge.mk e b := ⟨_, _, rfl⟩
    have hcell : (W.lastLetter hW).cell = e := by rw [hL]
    have hzy' : Topology.RelCWComplex.map (C := C) 1 e z = y := by rw [← hcell]; exact hzy
    have key : ∀ s : unitInterval, proj (C := C) (ept W hW s) =
        Topology.RelCWComplex.map (C := C) 1 e
          (segF (if b then unitInterval.symm s else s)) := by
      intro s
      rw [proj_ept, hL]
      exact OEdge.path_symm_apply_mk e b s
    have hz0 : |z 0| < 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_fin_one] at hz
      exact hz
    have hzlo : -1 < z 0 := (abs_lt.mp hz0).1
    have hzhi : z 0 < 1 := (abs_lt.mp hz0).2
    set s : unitInterval := ⟨(z 0 + 1) / 2, by
      refine ⟨?_, ?_⟩ <;> linarith⟩ with hs
    have hsval : (s : ℝ) = (z 0 + 1) / 2 := rfl
    have hseg : segF s = z := by
      funext i
      fin_cases i
      show 2 * (s : ℝ) - 1 = z 0
      rw [hsval]; ring
    have hs0 : 0 < (s : ℝ) := by rw [hsval]; linarith
    have hs1 : (s : ℝ) < 1 := by rw [hsval]; linarith
    cases b
    · refine ⟨ept (C := C) W hW s, mem_edgeInt hs0 hs1, ?_⟩
      rw [key s, if_neg (by simp : ¬((false : Bool) = true)), hseg]
      exact hzy'
    · refine ⟨ept (C := C) W hW (unitInterval.symm s),
        mem_edgeInt (by rw [unitInterval.coe_symm_eq]; linarith)
          (by rw [unitInterval.coe_symm_eq]; linarith), ?_⟩
      rw [key (unitInterval.symm s), if_pos rfl, unitInterval.symm_symm, hseg]
      exact hzy'

lemma injOn_proj_edgeInt {W : RWalk (C := C) u} {hW : W.1 ≠ []} :
    Set.InjOn (proj (C := C)) (edgeInt W hW) := by
  rintro x ⟨s, hs0, hs1, rfl⟩ y ⟨s', hs0', hs1', rfl⟩ hxy
  have h : (OEdge.path (C := C) (W.lastLetter hW)) (unitInterval.symm s) =
      (OEdge.path (C := C) (W.lastLetter hW)) (unitInterval.symm s') := hxy
  have hss : s = s' := by
    have h2 := path_injOn (W.lastLetter hW)
      ⟨by rw [unitInterval.coe_symm_eq]; linarith, by rw [unitInterval.coe_symm_eq]; linarith⟩
      ⟨by rw [unitInterval.coe_symm_eq]; linarith, by rw [unitInterval.coe_symm_eq]; linarith⟩ h
    exact Function.Involutive.injective unitInterval.symm_involutive h2
  rw [hss]

lemma edgeInt_disjoint {W W' : RWalk (C := C) u} {hW : W.1 ≠ []} {hW' : W'.1 ≠ []}
    (h : W ≠ W') : Disjoint (edgeInt W hW) (edgeInt W' hW') := by
  rw [Set.disjoint_left]
  rintro x ⟨s, hs0, hs1, rfl⟩ ⟨s', hs0', hs1', hEq⟩
  exact h (ept_eq_of_ne_endpoints (unitInterval_ne_zero hs0) (unitInterval_ne_one hs1) hEq).1

lemma discreteTopology_subtype {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    (p : α → Prop) : DiscreteTopology (Subtype p) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro i
  have h : ({i} : Set (Subtype p)) = Subtype.val ⁻¹' ({i.1} : Set α) := by
    ext j; rw [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
  rw [h]
  exact isOpen_discrete _

/-- **The vertex case of the covering property.** -/
theorem isEvenlyCovered_vertex {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n))
    (u : Topology.CWComplex.cell (Set.univ : Set X) 0)
    (v : Topology.CWComplex.cell (Set.univ : Set X) 0)
    (hne : (proj (C := (Set.univ : Set X)) (u := u) ⁻¹' {vpt (C := (Set.univ : Set X)) v}).Nonempty) :
    IsEvenlyCovered (proj (C := (Set.univ : Set X)) (u := u))
      (vpt (C := (Set.univ : Set X)) v)
      (proj (C := (Set.univ : Set X)) (u := u) ⁻¹' {vpt (C := (Set.univ : Set X)) v}) := by
  classical
  obtain ⟨z, hz⟩ := hne
  have hz' : proj (C := Set.univ) z = vpt (C := Set.univ) v := hz
  obtain ⟨W₀, hW₀, -⟩ := exists_vertex_of_proj_eq (C := Set.univ) hz'
  let ι := {W : RWalk (C := Set.univ) u // W.endOf = v}
  haveI : Nonempty ι := ⟨⟨W₀, hW₀⟩⟩
  haveI : Nonempty (X → Tree (C := Set.univ) u) :=
    ⟨fun _ => vertex (RWalk.nil (C := Set.univ) u)⟩
  haveI : DiscreteTopology ι := discreteTopology_subtype _
  refine (IsEvenlyCovered.of_trivialization (I := ι)
    (t := IsOpen.trivializationDiscrete (f := proj (C := Set.univ) (u := u))
      (fun i : ι => starSet (C := Set.univ) i.1) (halfStar (C := Set.univ) v)
      (isOpen_halfStar h2 v) ?_ ?_ ?_ ?_ ?_)
    (by rw [IsOpen.trivializationDiscrete_baseSet]
        exact vpt_mem_halfStar (C := Set.univ) v)).to_isEvenlyCovered_preimage
  · intro i W hWV
    constructor
    · intro hW
      exact (hW.preimage continuous_proj).inter (isOpen_starSet i.1)
    · intro hW
      have himg : proj (C := Set.univ) '' (proj (C := Set.univ) ⁻¹' W ∩
          starSet (C := Set.univ) i.1) = W := by
        refine Set.Subset.antisymm ?_ ?_
        · rintro y ⟨x, ⟨hx1, -⟩, rfl⟩; exact hx1
        · intro y hy
          have hy' : y ∈ proj (C := Set.univ) '' starSet (C := Set.univ) i.1 := by
            rw [proj_image_starSet, i.2]; exact hWV hy
          obtain ⟨x, hx, hxy⟩ := hy'
          exact ⟨x, ⟨by show proj (C := Set.univ) x ∈ W; rw [hxy]; exact hy, hx⟩, hxy⟩
      rw [← himg]
      exact isOpenMap_proj h2 u _ hW
  · intro i
    exact injOn_proj_starSet i.1
  · intro i
    intro y hy
    have hy' : y ∈ proj (C := Set.univ) '' starSet (C := Set.univ) i.1 := by
      rw [proj_image_starSet, i.2]; exact hy
    obtain ⟨x, hx, hxy⟩ := hy'
    exact ⟨x, hx, hxy⟩
  · intro i j hij
    exact starSet_disjoint (fun h => hij (Subtype.ext h))
  · intro x hx
    obtain ⟨W, hWe, hxW⟩ := exists_starSet_of_proj_mem_halfStar (C := Set.univ) hx
    exact Set.mem_iUnion.mpr ⟨⟨W, hWe⟩, hxW⟩

/-- **The edge case of the covering property.** -/
theorem isEvenlyCovered_of_mem_openCell {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n))
    (u : Topology.CWComplex.cell (Set.univ : Set X) 0)
    {x : X} (e : Topology.RelCWComplex.cell (Set.univ : Set X) 1)
    (hx : x ∈ Topology.RelCWComplex.openCell (C := (Set.univ : Set X)) 1 e)
    (hne : (proj (C := (Set.univ : Set X)) (u := u) ⁻¹' {x}).Nonempty) :
    IsEvenlyCovered (proj (C := (Set.univ : Set X)) (u := u)) x
      (proj (C := (Set.univ : Set X)) (u := u) ⁻¹' {x}) := by
  classical
  obtain ⟨z, hz⟩ := hne
  have hzx : proj (C := Set.univ) z = x := hz
  obtain ⟨z₀, hz₀⟩ := Quotient.exists_rep z
  obtain ⟨W₀, hW₀, t₀, hlt0, hlt1, hzW⟩ : ∃ (W : RWalk (C := Set.univ) u) (hW : W.1 ≠ [])
      (t : unitInterval), 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ z = ept (C := Set.univ) W hW t := by
    rcases z₀ with W₁ | ⟨⟨W₁, hW₁⟩, t₁⟩
    · have hEq : proj (C := Set.univ) (vertex W₁) = proj (C := Set.univ) z := by
        rw [proj_vertex, ← hz₀]; rfl
      have hmem : vpt (C := Set.univ) W₁.endOf ∈
          Topology.RelCWComplex.openCell (C := Set.univ) 1 e := by
        rw [← proj_vertex (C := Set.univ) W₁, hEq, hzx]
        exact hx
      exact absurd hmem (vpt_not_mem_openCell_one (C := Set.univ) W₁.endOf e)
    · rcases eq_or_ne t₁ 0 with ht0 | ht0
      · have hEq : proj (C := Set.univ) (vertex W₁) = proj (C := Set.univ) z := by
          rw [proj_vertex, ← hz₀]
          show vpt (C := Set.univ) W₁.endOf = proj (C := Set.univ) (ept W₁ hW₁ t₁)
          rw [ht0, ept_zero_eq_vertex]; rfl
        have hmem : vpt (C := Set.univ) W₁.endOf ∈
            Topology.RelCWComplex.openCell (C := Set.univ) 1 e := by
          rw [← proj_vertex (C := Set.univ) W₁, hEq, hzx]
          exact hx
        exact absurd hmem (vpt_not_mem_openCell_one (C := Set.univ) W₁.endOf e)
      · rcases eq_or_ne t₁ 1 with ht1 | ht1
        · have hEq : proj (C := Set.univ) (vertex W₁.dropLast) = proj (C := Set.univ) z := by
            rw [proj_vertex, ← hz₀]
            show vpt (C := Set.univ) W₁.dropLast.endOf = proj (C := Set.univ) (ept W₁ hW₁ t₁)
            rw [ht1, ept_one_eq_vertex_dropLast]; rfl
          have hmem : vpt (C := Set.univ) W₁.dropLast.endOf ∈
              Topology.RelCWComplex.openCell (C := Set.univ) 1 e := by
            rw [← proj_vertex (C := Set.univ) W₁.dropLast, hEq, hzx]
            exact hx
          exact absurd hmem (vpt_not_mem_openCell_one (C := Set.univ) W₁.dropLast.endOf e)
        · exact ⟨W₁, hW₁, t₁, unitInterval_pos_of_ne_zero ht0,
            unitInterval_lt_one_of_ne_one ht1, hz₀.symm⟩
  have hz' : proj (C := Set.univ) (ept W₀ hW₀ t₀) = x := by rw [← hzW, hz]
  have hcell : (W₀.lastLetter hW₀).cell = e := by
    by_contra hc
    have hm : x ∈ Topology.RelCWComplex.openCell (C := Set.univ) 1 (W₀.lastLetter hW₀).cell := by
      rw [← hz']; exact proj_ept_mem_openCell (C := Set.univ) hlt0 hlt1
    have hne : (⟨(1 : ℕ), (W₀.lastLetter hW₀).cell⟩ :
        Σ n, Topology.RelCWComplex.cell (Set.univ : Set X) n) ≠ ⟨(1 : ℕ), e⟩ := by
      intro hh
      exact hc (eq_of_heq (Sigma.mk.inj hh).2)
    exact Set.disjoint_left.mp
      (Topology.RelCWComplex.disjoint_openCell_of_ne (C := Set.univ) hne) hm hx
  let ι := {p : {W : RWalk (C := Set.univ) u // W.1 ≠ []} //
    (RWalk.lastLetter p.1 p.2).cell = e}
  haveI : Nonempty ι := ⟨⟨⟨W₀, hW₀⟩, hcell⟩⟩
  haveI : Nonempty (X → Tree (C := Set.univ) u) :=
    ⟨fun _ => vertex (RWalk.nil (C := Set.univ) u)⟩
  haveI : DiscreteTopology ι := discreteTopology_subtype _
  refine (IsEvenlyCovered.of_trivialization (I := ι)
    (t := IsOpen.trivializationDiscrete (f := proj (C := Set.univ) (u := u))
      (fun i : ι => edgeInt (C := Set.univ) i.1.1 i.1.2)
      (Topology.RelCWComplex.openCell (C := (Set.univ : Set X)) 1 e) (isOpen_openCell_one h2 e)
      ?_ ?_ ?_ ?_ ?_)
    (by rw [IsOpen.trivializationDiscrete_baseSet]; exact hx)).to_isEvenlyCovered_preimage
  · intro i W hWV
    constructor
    · intro hW
      exact (hW.preimage continuous_proj).inter (isOpen_edgeInt)
    · intro hW
      have himg : proj (C := Set.univ) '' (proj (C := Set.univ) ⁻¹' W ∩
          edgeInt (C := Set.univ) i.1.1 i.1.2) = W := by
        refine Set.Subset.antisymm ?_ ?_
        · rintro y ⟨x, ⟨hx1, -⟩, rfl⟩; exact hx1
        · intro y hy
          have hy' : y ∈ proj (C := Set.univ) '' edgeInt (C := Set.univ) i.1.1 i.1.2 := by
            rw [proj_image_edgeInt, i.2]; exact hWV hy
          obtain ⟨x, hx, hxy⟩ := hy'
          exact ⟨x, ⟨by show proj (C := Set.univ) x ∈ W; rw [hxy]; exact hy, hx⟩, hxy⟩
      rw [← himg]
      exact isOpenMap_proj h2 u _ hW
  · intro i
    exact injOn_proj_edgeInt
  · intro i
    intro y hy
    have hy' : y ∈ proj (C := Set.univ) '' edgeInt (C := Set.univ) i.1.1 i.1.2 := by
      rw [proj_image_edgeInt, i.2]; exact hy
    obtain ⟨x, hx, hxy⟩ := hy'
    exact ⟨x, hx, hxy⟩
  · intro i j hij
    refine edgeInt_disjoint ?_
    intro h
    exact hij (Subtype.ext (Subtype.ext h))
  · intro y hy
    obtain ⟨y₁, hy₁⟩ := Quotient.exists_rep y
    rcases y₁ with W₁ | ⟨⟨W₁, hW₁⟩, t₁⟩
    · have hEq : proj (C := Set.univ) (vertex W₁) = proj (C := Set.univ) y := by
        rw [proj_vertex, ← hy₁]; rfl
      have hmem : vpt (C := Set.univ) W₁.endOf ∈
          Topology.RelCWComplex.openCell (C := Set.univ) 1 e := by
        rw [← proj_vertex (C := Set.univ) W₁, hEq]
        exact hy
      exact absurd hmem (vpt_not_mem_openCell_one (C := Set.univ) W₁.endOf e)
    · rcases eq_or_ne t₁ 0 with ht0 | ht0
      · have hEq : proj (C := Set.univ) (vertex W₁) = proj (C := Set.univ) y := by
          rw [proj_vertex, ← hy₁]
          show vpt (C := Set.univ) W₁.endOf = proj (C := Set.univ) (ept W₁ hW₁ t₁)
          rw [ht0, ept_zero_eq_vertex]; rfl
        have hmem : vpt (C := Set.univ) W₁.endOf ∈
            Topology.RelCWComplex.openCell (C := Set.univ) 1 e := by
          rw [← proj_vertex (C := Set.univ) W₁, hEq]
          exact hy
        exact absurd hmem (vpt_not_mem_openCell_one (C := Set.univ) W₁.endOf e)
      · rcases eq_or_ne t₁ 1 with ht1 | ht1
        · have hEq : proj (C := Set.univ) (vertex W₁.dropLast) = proj (C := Set.univ) y := by
            rw [proj_vertex, ← hy₁]
            show vpt (C := Set.univ) W₁.dropLast.endOf = proj (C := Set.univ) (ept W₁ hW₁ t₁)
            rw [ht1, ept_one_eq_vertex_dropLast]; rfl
          have hmem : vpt (C := Set.univ) W₁.dropLast.endOf ∈
              Topology.RelCWComplex.openCell (C := Set.univ) 1 e := by
            rw [← proj_vertex (C := Set.univ) W₁.dropLast, hEq]
            exact hy
          exact absurd hmem (vpt_not_mem_openCell_one (C := Set.univ) W₁.dropLast.endOf e)
        · have hcell₁ : (W₁.lastLetter hW₁).cell = e := by
            by_contra hc
            have hm : proj (C := Set.univ) (ept W₁ hW₁ t₁) ∈
                Topology.RelCWComplex.openCell (C := Set.univ) 1 (W₁.lastLetter hW₁).cell :=
              proj_ept_mem_openCell (C := Set.univ)
                (unitInterval_pos_of_ne_zero ht0) (unitInterval_lt_one_of_ne_one ht1)
            have hEq2 : proj (C := Set.univ) (ept W₁ hW₁ t₁) = proj (C := Set.univ) y := by
              rw [← hy₁]; rfl
            have hm' : proj (C := Set.univ) y ∈
                Topology.RelCWComplex.openCell (C := Set.univ) 1 (W₁.lastLetter hW₁).cell := by
              rw [← hEq2]; exact hm
            have hne : (⟨(1 : ℕ), (W₁.lastLetter hW₁).cell⟩ :
                Σ n, Topology.RelCWComplex.cell (Set.univ : Set X) n) ≠ ⟨(1 : ℕ), e⟩ := by
              intro hh
              exact hc (eq_of_heq (Sigma.mk.inj hh).2)
            exact Set.disjoint_left.mp
              (Topology.RelCWComplex.disjoint_openCell_of_ne (C := Set.univ) hne) hm' hy
          have hyEq : y = ept (C := Set.univ) W₁ hW₁ t₁ := hy₁.symm
          refine Set.mem_iUnion.mpr ⟨⟨⟨W₁, hW₁⟩, hcell₁⟩, ?_⟩
          rw [hyEq]
          exact mem_edgeInt (unitInterval_pos_of_ne_zero ht0)
            (unitInterval_lt_one_of_ne_one ht1)

/-- **The projection of the universal cover is a covering map.** -/
theorem isCoveringMap_proj {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n))
    (u : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    IsCoveringMap (proj (C := (Set.univ : Set X)) (u := u)) := by
  classical
  haveI : Nonempty (Tree (C := Set.univ) u) := ⟨vertex (RWalk.nil (C := Set.univ) u)⟩
  intro x
  by_cases hx : x ∈ Set.range (proj (C := (Set.univ : Set X)) (u := u))
  · obtain ⟨z, hxz⟩ := hx
    obtain ⟨z₀, hz₀⟩ := Quotient.exists_rep z
    rcases z₀ with W | ⟨⟨W, hW⟩, t⟩
    · have hEq : x = proj (C := Set.univ) (vertex W) := by
        rw [← hxz, ← hz₀]; rfl
      rw [hEq]
      show IsEvenlyCovered (proj (C := Set.univ) (u := u)) (vpt (C := Set.univ) W.endOf)
        (proj (C := Set.univ) (u := u) ⁻¹' {vpt (C := Set.univ) W.endOf})
      exact isEvenlyCovered_vertex h2 u W.endOf ⟨vertex W, proj_vertex W⟩
    · rcases eq_or_ne t 0 with ht0 | ht0
      · have hEq : x = proj (C := Set.univ) (vertex W) := by
          rw [← hxz, ← hz₀]
          show proj (C := Set.univ) (ept W hW t) = proj (C := Set.univ) (vertex W)
          rw [ht0, ept_zero_eq_vertex]
        rw [hEq]
        show IsEvenlyCovered (proj (C := Set.univ) (u := u)) (vpt (C := Set.univ) W.endOf)
          (proj (C := Set.univ) (u := u) ⁻¹' {vpt (C := Set.univ) W.endOf})
        exact isEvenlyCovered_vertex h2 u W.endOf ⟨vertex W, proj_vertex W⟩
      · rcases eq_or_ne t 1 with ht1 | ht1
        · have hEq : x = proj (C := Set.univ) (vertex W.dropLast) := by
            rw [← hxz, ← hz₀]
            show proj (C := Set.univ) (ept W hW t) = proj (C := Set.univ) (vertex W.dropLast)
            rw [ht1, ept_one_eq_vertex_dropLast]
          rw [hEq]
          show IsEvenlyCovered (proj (C := Set.univ) (u := u)) (vpt (C := Set.univ) W.dropLast.endOf)
            (proj (C := Set.univ) (u := u) ⁻¹' {vpt (C := Set.univ) W.dropLast.endOf})
          exact isEvenlyCovered_vertex h2 u W.dropLast.endOf
            ⟨vertex W.dropLast, proj_vertex W.dropLast⟩
        · have hx' : proj (C := Set.univ) (ept W hW t) ∈
              Topology.RelCWComplex.openCell (C := Set.univ) 1 (W.lastLetter hW).cell :=
            proj_ept_mem_openCell (C := Set.univ) (unitInterval_pos_of_ne_zero ht0)
              (unitInterval_lt_one_of_ne_one ht1)
          have hEq : x = proj (C := Set.univ) (ept W hW t) := by rw [← hxz, ← hz₀]; rfl
          rw [hEq]
          exact isEvenlyCovered_of_mem_openCell h2 u (W.lastLetter hW).cell hx'
            ⟨ept W hW t, rfl⟩
  · haveI : IsEmpty (proj (C := (Set.univ : Set X)) (u := u) ⁻¹' {x}) :=
      ⟨fun z => hx ⟨z.1, z.2⟩⟩
    have hxc : x ∈ ⋃ (n : ℕ) (j : Topology.RelCWComplex.cell (Set.univ : Set X) n),
        Topology.RelCWComplex.openCell (C := (Set.univ : Set X)) n j := by
      rw [Topology.CWComplex.iUnion_openCell_eq_complex]; trivial
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxc
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxn
    rcases n with _ | n
    · -- a vertex
      have hxv : x = vpt (C := Set.univ) j := by
        rw [Topology.RelCWComplex.openCell_zero_eq_singleton] at hxj
        exact hxj
      have hdisj : ∀ y ∈ halfStar (C := Set.univ) j,
          y ∉ Set.range (proj (C := Set.univ) (u := u)) := by
        intro y hy hyr
        obtain ⟨z, rfl⟩ := hyr
        obtain ⟨W, hWe, -⟩ := exists_starSet_of_proj_mem_halfStar (C := Set.univ) hy
        exact hx (hxv ▸ ⟨vertex W, by rw [proj_vertex, hWe]⟩)
      refine IsEvenlyCovered.of_preimage_eq_empty (proj (C := Set.univ) (u := u) ⁻¹' {x})
        (U := halfStar (C := Set.univ) j)
        ((isOpen_halfStar h2 j).mem_nhds ?_) ?_
      · rw [hxv]; exact vpt_mem_halfStar (C := Set.univ) j
      · ext y
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        exact fun hy => hdisj (proj (C := Set.univ) y) hy ⟨y, rfl⟩
    · rcases n with _ | n
      · -- an edge interior
        have hdisj : Topology.RelCWComplex.openCell (C := Set.univ) 1 j ∩
            Set.range (proj (C := Set.univ) (u := u)) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro y ⟨hy1, z, rfl⟩
          obtain ⟨z₀, hz₀⟩ := Quotient.exists_rep z
          rcases z₀ with W₁ | ⟨⟨W₁, hW₁⟩, t₁⟩
          · have hmem : proj (C := Set.univ) (vertex W₁) ∈
                Topology.RelCWComplex.openCell (C := Set.univ) 1 j := by
              rw [show (vertex W₁ : Tree (C := Set.univ) u) = Quotient.mk _ (Sum.inl W₁) from rfl,
                hz₀]
              exact hy1
            rw [proj_vertex] at hmem
            exact vpt_not_mem_openCell_one (C := Set.univ) W₁.endOf j hmem
          · have hmem : proj (C := Set.univ) (ept W₁ hW₁ t₁) ∈
                Topology.RelCWComplex.openCell (C := Set.univ) 1 j := by
              rw [show (ept W₁ hW₁ t₁ : Tree (C := Set.univ) u) =
                Quotient.mk _ (Sum.inr (⟨W₁, hW₁⟩, t₁)) from rfl, hz₀]
              exact hy1
            rcases eq_or_ne t₁ 0 with ht0' | ht0'
            · rw [ht0', ept_zero_eq_vertex, proj_vertex] at hmem
              exact vpt_not_mem_openCell_one (C := Set.univ) W₁.endOf j hmem
            · rcases eq_or_ne t₁ 1 with ht1' | ht1'
              · rw [ht1', ept_one_eq_vertex_dropLast, proj_vertex] at hmem
                exact vpt_not_mem_openCell_one (C := Set.univ) W₁.dropLast.endOf j hmem
              · have hm := proj_ept_mem_openCell (C := Set.univ) (W := W₁) (hW := hW₁) (t := t₁)
                  (unitInterval_pos_of_ne_zero ht0') (unitInterval_lt_one_of_ne_one ht1')
                have hcell₁ : (W₁.lastLetter hW₁).cell = j := by
                  by_contra hc
                  have hne : (⟨(1 : ℕ), (W₁.lastLetter hW₁).cell⟩ :
                      Σ n, Topology.RelCWComplex.cell (Set.univ : Set X) n) ≠ ⟨(1 : ℕ), j⟩ := by
                    intro hh
                    exact hc (eq_of_heq (Sigma.mk.inj hh).2)
                  exact Set.disjoint_left.mp
                    (Topology.RelCWComplex.disjoint_openCell_of_ne (C := Set.univ) hne) hm hmem
                rw [← hcell₁] at hxj
                rw [← proj_image_edgeInt (W := W₁) (hW := hW₁)] at hxj
                obtain ⟨w, -, hwj⟩ := hxj
                exact hx ⟨w, hwj⟩
        have hempty : proj (C := Set.univ) (u := u) ⁻¹'
            (Topology.RelCWComplex.openCell (C := Set.univ) 1 j) = ∅ := by
          ext y
          simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
          intro hy
          have hmem : proj (C := Set.univ) y ∈
              Topology.RelCWComplex.openCell (C := Set.univ) 1 j ∩
              Set.range (proj (C := Set.univ) (u := u)) := ⟨hy, ⟨y, rfl⟩⟩
          rw [hdisj] at hmem
          exact hmem
        exact IsEvenlyCovered.of_preimage_eq_empty (proj (C := Set.univ) (u := u) ⁻¹' {x})
          (U := Topology.RelCWComplex.openCell (C := Set.univ) 1 j)
          ((isOpen_openCell_one h2 j).mem_nhds hxj) hempty
      · exact ((h2 (n + 2) (by omega)).false j).elim



/-! ## The free group of closed reduced walks -/

/-- The encoding of an oriented edge as a generator and an exponent. -/
def enc (o : OEdge (C := C)) : Topology.CWComplex.cell C 1 × Bool := (o.cell, o.dir)

/-- The decoding of a generator and an exponent as an oriented edge. -/
def dec (p : Topology.CWComplex.cell C 1 × Bool) : OEdge (C := C) := OEdge.mk p.1 p.2

@[simp] lemma enc_dec (p : Topology.CWComplex.cell C 1 × Bool) : enc (dec p) = p := rfl

@[simp] lemma dec_enc (o : OEdge (C := C)) : dec (enc o) = o := by rcases o with ⟨e, b⟩; rfl

/-- **The maximal reduction of a list of oriented edges**: cancels adjacent inverse edges. -/
noncomputable def redL (l : List (OEdge (C := C))) : List (OEdge (C := C)) :=
  letI := Classical.decEq (Topology.CWComplex.cell C 1)
  l.foldr (fun x acc =>
    match acc with
    | [] => [x]
    | y :: r => if x.cell = y.cell ∧ x.dir = !y.dir then r else x :: y :: r) []

lemma redL_cons (x : OEdge (C := C)) (l : List (OEdge (C := C))) :
    redL (x :: l) = (letI := Classical.decEq (Topology.CWComplex.cell C 1)
      match redL l with
      | [] => [x]
      | y :: r => if x.cell = y.cell ∧ x.dir = !y.dir then r else x :: y :: r) := rfl

/-- The free group element represented by a list of oriented edges. -/
def wordList (l : List (OEdge (C := C))) : FreeGroup (Topology.CWComplex.cell C 1) :=
  FreeGroup.mk (l.map enc)

lemma wordList_append (l₁ l₂ : List (OEdge (C := C))) :
    wordList (l₁ ++ l₂) = wordList l₁ * wordList l₂ := by
  rw [wordList, List.map_append, ← FreeGroup.mul_mk]; rfl

lemma wordList_nil : wordList (C := C) ([] : List (OEdge (C := C))) = 1 :=
  (FreeGroup.one_eq_mk).symm

lemma wordList_cons (x : OEdge (C := C)) (l : List (OEdge (C := C))) :
    wordList (x :: l) = wordList [x] * wordList l := by
  rw [show x :: l = [x] ++ l from rfl, wordList_append]

lemma wordList_pair_singleton (x : OEdge (C := C)) :
    wordList [x, x.neg] = wordList [x] * wordList [x.neg] := by
  rw [show ([x, x.neg] : List (OEdge (C := C))) = [x] ++ [x.neg] from rfl, wordList_append]

lemma wordList_neg_apply (x : OEdge (C := C)) : wordList [x.neg] = (wordList [x])⁻¹ := by
  rcases x with ⟨e, b⟩
  cases b
  · rfl
  · rfl

lemma wordList_neg_pair (x : OEdge (C := C)) : wordList [x, x.neg] = 1 := by
  rw [wordList_pair_singleton, wordList_neg_apply, mul_inv_cancel]

lemma wordList_redL (l : List (OEdge (C := C))) : wordList (redL l) = wordList l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [redL_cons]
    cases h : redL l with
    | nil =>
      have hl : wordList l = 1 := by rw [← ih, h, wordList_nil]
      have hr : wordList (x :: l) = wordList [x] := by
        rw [show x :: l = [x] ++ l from rfl, wordList_append, hl, mul_one]
      show wordList ([x] : List (OEdge (C := C))) = wordList (x :: l)
      rw [hr]
    | cons y r =>
      classical
      have hlr : wordList (y :: r) = wordList l := by rw [← h]; exact ih
      show wordList (if x.cell = y.cell ∧ x.dir = !y.dir then r else x :: y :: r) =
        wordList (x :: l)
      by_cases hc : x.cell = y.cell ∧ x.dir = !y.dir
      · rw [if_pos hc]
        have hy : y = x.neg := by
          rcases x with ⟨ex, bx⟩
          rcases y with ⟨ey, by'⟩
          obtain ⟨h1, h2⟩ := hc
          cases h1
          cases bx <;> cases by' <;> simp_all
        have hr : wordList (x :: l) = wordList r := by
          rw [show x :: l = [x] ++ l from rfl, wordList_append, ← hlr]
          rw [show (y :: r : List (OEdge (C := C))) = [y] ++ r from rfl, wordList_append]
          rw [hy, wordList_neg_apply, ← mul_assoc, mul_inv_cancel, one_mul]
        rw [hr]
      · rw [if_neg hc]
        have hr : wordList (x :: (y :: r)) = wordList (x :: l) := by
          rw [show (x :: y :: r) = [x] ++ (y :: r) from rfl,
            show (x :: l) = [x] ++ l from rfl, wordList_append, wordList_append, hlr]
        rw [hr]


/-! ## `redL` and the free group -/

lemma enc_injective : Function.Injective (enc (C := C)) := by
  intro a b h
  rcases a with ⟨ea, ba⟩
  rcases b with ⟨eb, bb⟩
  have h1 : ea = eb := congrArg Prod.fst h
  have h2 : ba = bb := congrArg Prod.snd h
  subst h1
  subst h2
  rfl

lemma enc_imp_iff {a b : OEdge (C := C)} :
    ((enc a).1 = (enc b).1 → (enc a).2 = (enc b).2) ↔ b ≠ a.neg := by
  rcases a with ⟨ea, ba⟩
  rcases b with ⟨eb, bb⟩
  simp only [enc]
  cases ba <;> cases bb <;> simp [OEdge.neg, eq_comm]

lemma isReduced_map_enc_iff (l : List (OEdge (C := C))) :
    FreeGroup.IsReduced (l.map enc) ↔ Reduced l := by
  induction l with
  | nil => exact ⟨fun _ => by intro i hi; simp at hi, fun _ => FreeGroup.IsReduced.nil⟩
  | cons a l ih =>
    cases l with
    | nil =>
      exact ⟨fun _ => by intro i hi; simp at hi, fun _ => FreeGroup.IsReduced.singleton⟩
    | cons b l' =>
      simp only [List.map_cons] at ih ⊢
      rw [FreeGroup.isReduced_cons_cons, ih]
      conv_rhs => rw [reduced_cons_iff]
      rw [enc_imp_iff]
      refine ⟨fun ⟨h1, h2⟩ => ⟨fun c hc => ?_, h2⟩, fun ⟨h1, h2⟩ => ⟨h1 b rfl, h2⟩⟩
      rw [show (b :: l').head? = some b from rfl] at hc
      exact fun hca => h1 ((Option.some.inj hc).trans hca)

lemma reduce_map_enc_of_reduced {l : List (OEdge (C := C))} (h : Reduced l) :
    (letI := Classical.decEq (Topology.CWComplex.cell C 1);
      FreeGroup.reduce (l.map enc)) = l.map enc := by
  letI := Classical.decEq (Topology.CWComplex.cell C 1)
  exact (FreeGroup.IsReduced.red_iff_eq ((isReduced_map_enc_iff l).mpr h)).mp FreeGroup.reduce.red

lemma wordList_injOn {l₁ l₂ : List (OEdge (C := C))}
    (h₁ : Reduced l₁) (h₂ : Reduced l₂) (h : wordList l₁ = wordList l₂) : l₁ = l₂ := by
  letI := Classical.decEq (Topology.CWComplex.cell C 1)
  have h' : FreeGroup.mk (l₁.map enc) = FreeGroup.mk (l₂.map enc) := h
  have hred := FreeGroup.reduce.sound h'
  rw [reduce_map_enc_of_reduced h₁, reduce_map_enc_of_reduced h₂] at hred
  exact List.map_injective_iff.mpr enc_injective hred


/-! ## The endpoint and the reduction -/

/-- The endpoint of a list of oriented edges, ignoring the walk condition. -/
def lastTgt (u : Topology.CWComplex.cell C 0) : List (OEdge (C := C)) → Topology.CWComplex.cell C 0
  | [] => u
  | o :: l => lastTgt o.tgt l

lemma endOfList_eq_lastTgt : ∀ (l : List (OEdge (C := C))) (u : Topology.CWComplex.cell C 0)
    (h : IsWalk (C := C) u l), endOfList u l h = lastTgt u l
  | [], _, _ => rfl
  | o :: l, u, h => endOfList_eq_lastTgt l o.tgt h.2

lemma lastTgt_append (u : Topology.CWComplex.cell C 0) :
    ∀ (l₁ l₂ : List (OEdge (C := C))),
      lastTgt u (l₁ ++ l₂) = lastTgt (lastTgt u l₁) l₂
  | [], _ => rfl
  | o :: l₁, l₂ => lastTgt_append o.tgt l₁ l₂

lemma eq_neg_iff (a b : OEdge (C := C)) :
    b = a.neg ↔ (a.cell = b.cell ∧ a.dir = !b.dir) := by
  rcases a with ⟨ea, ba⟩
  rcases b with ⟨eb, bb⟩
  cases ba <;> cases bb <;> simp [OEdge.neg, eq_comm]

lemma reduced_redL (l : List (OEdge (C := C))) : Reduced (redL l) := by
  classical
  induction l with
  | nil =>
    show Reduced (redL ([] : List (OEdge (C := C))))
    rw [show redL ([] : List (OEdge (C := C))) = [] from rfl]
    intro i hi
    simp only [List.length_nil] at hi
    omega
  | cons x l ih =>
    rw [redL_cons]
    cases h : redL l with
    | nil =>
      show Reduced ([x] : List (OEdge (C := C)))
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      omega
    | cons y r =>
      show Reduced (if x.cell = y.cell ∧ x.dir = !y.dir then r else x :: y :: r)
      have hred : Reduced (y :: r) := by rw [← h]; exact ih
      by_cases hc : x.cell = y.cell ∧ x.dir = !y.dir
      · rw [if_pos hc]
        exact (reduced_cons_iff.mp hred).2
      · rw [if_neg hc]
        refine reduced_cons_iff.mpr ⟨?_, hred⟩
        intro b hb hbn
        rw [show (y :: r).head? = some y from rfl] at hb
        exact hc ((eq_neg_iff x y).mp ((Option.some.inj hb).trans hbn))

lemma isWalk_redL : ∀ (l : List (OEdge (C := C))) (u : Topology.CWComplex.cell C 0),
    IsWalk (C := C) u l → IsWalk (C := C) u (redL l)
  | [], _, _ => trivial
  | x :: l, u, h => by
    classical
    rw [redL_cons]
    have ih := isWalk_redL l x.tgt h.2
    cases hh : redL l with
    | nil =>
      show IsWalk (C := C) u ([x] : List (OEdge (C := C)))
      exact ⟨h.1, trivial⟩
    | cons y r =>
      show IsWalk (C := C) u
        (if x.cell = y.cell ∧ x.dir = !y.dir then r else x :: y :: r)
      have hyr : IsWalk (C := C) x.tgt (y :: r) := by rw [← hh]; exact ih
      by_cases hc : x.cell = y.cell ∧ x.dir = !y.dir
      · rw [if_pos hc]
        rw [show u = y.tgt from by
          rw [← h.1, show y = x.neg from (eq_neg_iff x y).mpr hc, OEdge.tgt_neg]]
        exact hyr.2
      · rw [if_neg hc]
        exact ⟨h.1, hyr⟩

lemma lastTgt_redL : ∀ (l : List (OEdge (C := C))) (u : Topology.CWComplex.cell C 0)
    (h : IsWalk (C := C) u l), lastTgt u (redL l) = lastTgt u l
  | [], u, _ => rfl
  | x :: l, u, h => by
    classical
    rw [redL_cons]
    have ih := lastTgt_redL l x.tgt h.2
    cases hh : redL l with
    | nil =>
      show lastTgt u ([x] : List (OEdge (C := C))) = lastTgt u (x :: l)
      rw [show lastTgt u (x :: l) = lastTgt x.tgt (redL l) from by
        show lastTgt x.tgt l = lastTgt x.tgt (redL l)
        exact ih.symm]
      rw [hh]
      rfl
    | cons y r =>
      show lastTgt u (if x.cell = y.cell ∧ x.dir = !y.dir then r else x :: y :: r) =
        lastTgt u (x :: l)
      have hR : lastTgt u (x :: l) = lastTgt y.tgt r := by
        rw [show lastTgt u (x :: l) = lastTgt x.tgt l from rfl, ← ih, hh]
        rfl
      by_cases hc : x.cell = y.cell ∧ x.dir = !y.dir
      · rw [if_pos hc, hR]
        rw [show u = y.tgt from by
          rw [← h.1, show y = x.neg from (eq_neg_iff x y).mpr hc, OEdge.tgt_neg]]
      · rw [if_neg hc, hR]
        rfl


/-! ## The type of closed reduced walks -/

/-- **The type of closed reduced walks at `u`** (the fibre of the universal cover over `vpt u`). -/
abbrev Lcw (u : Topology.CWComplex.cell C 0) := {W : RWalk (C := C) u // W.endOf = u}

lemma isWalk_append' {l l' : List (OEdge (C := C))} {u : Topology.CWComplex.cell C 0}
    (h : IsWalk (C := C) u l) (h' : IsWalk (C := C) (lastTgt u l) l') :
    IsWalk (C := C) u (l ++ l') := by
  rw [← endOfList_eq_lastTgt l u h] at h'
  exact Walk.isWalk_append h h'

lemma Lcw.lastTgt_eq (W : Lcw (C := C) u) : lastTgt u W.1.1 = u :=
  (endOfList_eq_lastTgt W.1.1 u W.1.2.1).symm.trans W.2

/-- The multiplication of closed reduced walks: concatenate and reduce. -/
noncomputable def Lcw.mul (W W' : Lcw (C := C) u) : Lcw (C := C) u :=
  let h := isWalk_append' W.1.2.1 (by rw [Lcw.lastTgt_eq W]; exact W'.1.2.1)
  ⟨⟨redL (W.1.1 ++ W'.1.1), isWalk_redL _ u h, reduced_redL _⟩, by
    show endOfList u (redL (W.1.1 ++ W'.1.1)) (isWalk_redL _ u h) = u
    rw [endOfList_eq_lastTgt, lastTgt_redL _ u h, lastTgt_append, Lcw.lastTgt_eq W,
      Lcw.lastTgt_eq W']⟩

/-- The free group element represented by a closed reduced walk. -/
def Lcw.word (W : Lcw (C := C) u) : FreeGroup (Topology.CWComplex.cell C 1) :=
  wordList W.1.1

lemma Lcw.word_mul (W W' : Lcw (C := C) u) :
    Lcw.word (Lcw.mul W W') = Lcw.word W * Lcw.word W' := by
  show wordList (redL (W.1.1 ++ W'.1.1)) = wordList W.1.1 * wordList W'.1.1
  rw [wordList_redL, wordList_append]

lemma Lcw.word_injective : Function.Injective (Lcw.word (C := C) (u := u)) := by
  intro W W' h
  have h' : W.1.1 = W'.1.1 := wordList_injOn W.1.2.2 W'.1.2.2 h
  exact Subtype.ext (Subtype.ext h')


lemma reduced_iff_isChain (l : List (OEdge (C := C))) :
    Reduced l ↔ List.IsChain (fun a b : OEdge (C := C) => b ≠ a.neg) l := by
  rw [List.isChain_iff_getElem]
  rfl

lemma reduced_reverse_map_neg (l : List (OEdge (C := C))) (h : Reduced l) :
    Reduced (l.reverse.map OEdge.neg) := by
  rw [reduced_iff_isChain] at h ⊢
  rw [List.isChain_map, List.isChain_reverse] at ⊢
  exact List.IsChain.imp (fun a b hab hc => hab (by rw [← OEdge.neg_neg b, hc])) h

lemma lastTgt_reverse_map_neg : ∀ (l : List (OEdge (C := C))) (u : Topology.CWComplex.cell C 0),
    IsWalk (C := C) u l → lastTgt (lastTgt u l) (l.reverse.map OEdge.neg) = u
  | [], u, _ => rfl
  | o :: l, u, h => by
    rw [List.reverse_cons, List.map_append]
    rw [show lastTgt u (o :: l) = lastTgt o.tgt l from rfl]
    rw [lastTgt_append, lastTgt_reverse_map_neg l o.tgt h.2]
    exact (show lastTgt o.tgt ([OEdge.neg o] : List (OEdge (C := C))) = u from by
      rw [show lastTgt o.tgt ([OEdge.neg o] : List (OEdge (C := C))) = (OEdge.neg o).tgt
          from rfl, OEdge.tgt_neg, h.1])

lemma isWalk_reverse_map_neg : ∀ (l : List (OEdge (C := C))) (u : Topology.CWComplex.cell C 0),
    IsWalk (C := C) u l → IsWalk (C := C) (lastTgt u l) (l.reverse.map OEdge.neg)
  | [], u, _ => trivial
  | o :: l, u, h => by
    rw [List.reverse_cons, List.map_append]
    rw [show lastTgt u (o :: l) = lastTgt o.tgt l from rfl]
    refine isWalk_append' (isWalk_reverse_map_neg l o.tgt h.2) ?_
    show IsWalk (C := C) (lastTgt (lastTgt o.tgt l) (l.reverse.map OEdge.neg)) [OEdge.neg o]
    rw [lastTgt_reverse_map_neg l o.tgt h.2]
    exact ⟨OEdge.src_neg o, trivial⟩


/-- The inverse of a closed reduced walk: reverse the list and negate every letter. -/
noncomputable def Lcw.inv (W : Lcw (C := C) u) : Lcw (C := C) u :=
  let h := isWalk_reverse_map_neg W.1.1 u W.1.2.1
  have h' : IsWalk (C := C) u (W.1.1.reverse.map OEdge.neg) :=
    (congrArg (fun v => IsWalk (C := C) v (W.1.1.reverse.map OEdge.neg)) (Lcw.lastTgt_eq W)).mp h
  ⟨⟨W.1.1.reverse.map OEdge.neg, h', reduced_reverse_map_neg W.1.1 W.1.2.2⟩, by
    show endOfList u (W.1.1.reverse.map OEdge.neg) h' = u
    rw [endOfList_eq_lastTgt]
    have h'' := lastTgt_reverse_map_neg W.1.1 u W.1.2.1
    rw [Lcw.lastTgt_eq W] at h''
    exact h''⟩

lemma wordList_reverse_map_neg (l : List (OEdge (C := C))) :
    wordList (l.reverse.map OEdge.neg) = (wordList l)⁻¹ := by
  induction l with
  | nil => rw [List.reverse_nil, List.map_nil, wordList_nil, inv_one]
  | cons o l ih =>
    rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, wordList_append,
      ih, wordList_neg_apply o]
    rw [show wordList (o :: l) = wordList [o] * wordList l from wordList_cons o l, mul_inv_rev]

noncomputable instance Lcw.instMul : Mul (Lcw (C := C) u) := ⟨Lcw.mul⟩

instance Lcw.instOne : One (Lcw (C := C) u) := ⟨⟨RWalk.nil (C := C) u, rfl⟩⟩

noncomputable instance Lcw.instInv : Inv (Lcw (C := C) u) := ⟨Lcw.inv⟩

lemma Lcw.word_one : Lcw.word (1 : Lcw (C := C) u) = 1 := wordList_nil

lemma Lcw.word_inv (W : Lcw (C := C) u) : Lcw.word (W⁻¹) = (Lcw.word W)⁻¹ :=
  wordList_reverse_map_neg W.1.1

/-- **The group of closed reduced walks at `u`.** -/
noncomputable instance Lcw.instGroup : Group (Lcw (C := C) u) :=
  Group.ofLeftAxioms
    (fun a b c => Lcw.word_injective (by
      show Lcw.word (Lcw.mul (Lcw.mul a b) c) = Lcw.word (Lcw.mul a (Lcw.mul b c))
      rw [Lcw.word_mul, Lcw.word_mul, Lcw.word_mul, Lcw.word_mul, mul_assoc]))
    (fun a => Lcw.word_injective (by
      show Lcw.word (Lcw.mul 1 a) = Lcw.word a
      rw [Lcw.word_mul, Lcw.word_one, one_mul]))
    (fun a => Lcw.word_injective (by
      show Lcw.word (Lcw.mul a⁻¹ a) = Lcw.word 1
      rw [Lcw.word_mul, Lcw.word_inv, inv_mul_cancel, Lcw.word_one]))

/-- The multiplicative map from closed reduced walks to the free group. -/
noncomputable def Lcw.wordHom : Lcw (C := C) u →* FreeGroup (Topology.CWComplex.cell C 1) where
  toFun := Lcw.word
  map_one' := Lcw.word_one
  map_mul' := Lcw.word_mul

lemma Lcw.wordHom_injective : Function.Injective (Lcw.wordHom (C := C) (u := u)) :=
  Lcw.word_injective

/-- **The group of closed reduced walks at a vertex is free.** -/
theorem isFreeGroup_Lcw (u : Topology.CWComplex.cell C 0) : IsFreeGroup (Lcw (C := C) u) :=
  IsFreeGroup.ofMulEquiv (MonoidHom.ofInjective (Lcw.wordHom_injective (C := C) (u := u))).symm

/-! ## The translation of the universal cover by a closed walk

The universal cover `Tree u` carries an action of the group `Lcw u` of closed reduced walks at `u`:
a closed walk `W` acts on a vertex `vertex Z` by `vertex (concat W Z)`, where `concat W Z` is the
reduction of the concatenation of `W` and `Z`.  On an interior point of the edge above `Z` the
action may shift the parameter (when the reduction of `W.1 ++ Z.1` eats into the edge above `Z`),
which is why it is implemented below *on paths* rather than on points: `transWalkAux W Z` is a path
in the tree from `vertex W` to `vertex (concat W Z)` whose projection is independent of `W`. -/

/-- The reduction of a reduced list is the list itself. -/
lemma redL_eq_self_of_reduced {l : List (OEdge (C := C))} (h : Reduced (C := C) l) :
    redL l = l :=
  wordList_injOn (reduced_redL l) h (wordList_redL l)

/-- Reduction of a concatenation with a single appended letter only depends on the reduced form of
the prefix. -/
lemma redL_append_singleton_eq (l : List (OEdge (C := C))) (x : OEdge (C := C)) :
    redL (l ++ [x]) = redL (redL l ++ [x]) :=
  wordList_injOn (reduced_redL _) (reduced_redL _) (by
    rw [wordList_redL (l ++ [x]), wordList_redL (redL l ++ [x]),
      wordList_append, wordList_append, wordList_redL l])

/-- A backtracking pair at the end of a list cancels under reduction. -/
lemma redL_append_neg_pair (l : List (OEdge (C := C))) (y : OEdge (C := C)) :
    redL (l ++ [y, y.neg]) = redL l := by
  classical
  refine wordList_injOn (reduced_redL _) (reduced_redL _) ?_
  rw [wordList_redL (l ++ [y, y.neg]), wordList_redL l]
  rw [show l ++ [y, y.neg] = (l ++ [y]) ++ [y.neg] from by simp]
  rw [wordList_append, wordList_append, wordList_neg_apply, mul_assoc, mul_inv_cancel, mul_one]

/-- If `x` is the inverse of the last letter of a reduced nonempty list `l`, then appending `x` and
reducing drops the last letter. -/
lemma redL_append_singleton_eq_dropLast {l : List (OEdge (C := C))} {x : OEdge (C := C)}
    (hl : Reduced (C := C) l) (hnil : l ≠ []) (h : x = (l.getLast hnil).neg) :
    redL (l ++ [x]) = l.dropLast := by
  conv_lhs => rw [← List.dropLast_append_getLast hnil, h]
  rw [List.append_assoc]
  simp only [List.singleton_append]
  rw [redL_append_neg_pair, redL_eq_self_of_reduced (reduced_dropLast hl)]

/-- A non-reduced list with an appended letter has a genuine last letter. -/
lemma notReduced_snoc_ne_nil {l : List (OEdge (C := C))} {x : OEdge (C := C)}
    (h : ¬ Reduced (C := C) (l ++ [x])) : l ≠ [] := by
  intro hl
  refine h ?_
  rw [hl]
  intro i hi
  simp only [List.nil_append, List.length_cons, List.length_nil] at hi
  omega

/-- If appending `x` to a reduced list destroys reducedness, then `x` is the inverse of the last
letter. -/
lemma notReduced_snoc_eq_neg {l : List (OEdge (C := C))} {x : OEdge (C := C)}
    (hl' : Reduced (C := C) l) (hl : l ≠ [])
    (h : ¬ Reduced (C := C) (l ++ [x])) : x = (l.getLast hl).neg := by
  by_contra hne
  refine h (reduced_append_singleton (C := C) hl' (fun h' hc => hne ?_))
  rw [hc, List.getLast_congr h' hl rfl]

/-- Prepend a closed reduced walk at `u` to a reduced walk at `u` and reduce. -/
noncomputable def concat (W : Lcw (C := C) u) (Z : RWalk (C := C) u) : RWalk (C := C) u :=
  ⟨redL (W.1.1 ++ Z.1),
    isWalk_redL (W.1.1 ++ Z.1) u
      (isWalk_append' W.1.2.1 (by rw [Lcw.lastTgt_eq W]; exact Z.2.1)),
    reduced_redL (W.1.1 ++ Z.1)⟩

/-- The endpoint of a reduced concatenation is the endpoint of the second factor. -/
lemma concat_endOf (W : Lcw (C := C) u) (Z : RWalk (C := C) u) :
    (concat W Z).endOf = Z.endOf := by
  have h : IsWalk (C := C) u (W.1.1 ++ Z.1) :=
    isWalk_append' W.1.2.1 (by rw [Lcw.lastTgt_eq W]; exact Z.2.1)
  show endOfList u (redL (W.1.1 ++ Z.1)) (isWalk_redL _ u h) = endOfList u Z.1 Z.2.1
  rw [endOfList_eq_lastTgt, endOfList_eq_lastTgt,
    lastTgt_redL (W.1.1 ++ Z.1) u h, lastTgt_append, Lcw.lastTgt_eq W]

@[simp] lemma concat_nil_walk (W : Lcw (C := C) u) :
    concat W (RWalk.nil (C := C) u) = W.1 := by
  refine Subtype.ext ?_
  show redL (W.1.1 ++ []) = W.1.1
  rw [List.append_nil, redL_eq_self_of_reduced W.1.2.2]

/-- Concatenating the empty walk on the left does nothing. -/
lemma concat_one (Z : RWalk (C := C) u) :
    concat (1 : Lcw (C := C) u) Z = Z := by
  refine Subtype.ext ?_
  show redL ((1 : Lcw (C := C) u).1.1 ++ Z.1) = Z.1
  rw [show ((1 : Lcw (C := C) u).1.1) = ([] : List (OEdge (C := C))) from rfl, List.nil_append,
    redL_eq_self_of_reduced Z.2.2]

/-- `concat` does nothing when the second walk is empty. -/
lemma concat_eq_self_of_length_zero (W : Lcw (C := C) u) (Z : RWalk (C := C) u)
    (h : Z.1.length = 0) : concat W Z = W.1 := by
  refine Subtype.ext ?_
  show redL (W.1.1 ++ Z.1) = W.1.1
  rw [List.length_eq_zero_iff.mp h, List.append_nil, redL_eq_self_of_reduced W.1.2.2]

/-- The key relation between `concat` and its one-letter version. -/
lemma concat_val_snoc (W : Lcw (C := C) u) (Z : RWalk (C := C) u) (hZ : Z.1 ≠ []) :
    redL (W.1.1 ++ Z.1) =
      redL (redL (W.1.1 ++ Z.dropLast.1) ++ [Z.lastLetter hZ]) := by
  conv_lhs => rw [← List.dropLast_append_getLast hZ, ← List.append_assoc]
  rw [redL_append_singleton_eq]
  rfl

/-- The one-letter version of `concat`. -/
noncomputable def concatPt (X : RWalk (C := C) u) (o : OEdge (C := C))
    (hsrc : o.src = X.endOf) : RWalk (C := C) u :=
  ⟨redL (X.1 ++ [o]), isWalk_redL (X.1 ++ [o]) u (isWalk_snoc X hsrc),
    reduced_redL (X.1 ++ [o])⟩

/-- `concat` at a walk with a last letter. -/
lemma concat_eq_concatPt {X : RWalk (C := C) u} {o : OEdge (C := C)} {hsrc : o.src = X.endOf}
    (W : Lcw (C := C) u) (Z : RWalk (C := C) u) (hZ : Z.1 ≠ [])
    (hX : X = concat W Z.dropLast) (ho : o = Z.lastLetter hZ) :
    concat W Z = concatPt X o hsrc := by
  subst hX
  subst ho
  refine Subtype.ext ?_
  show redL (W.1.1 ++ Z.1) =
    redL ((concat W Z.dropLast).1 ++ [Z.lastLetter hZ])
  exact concat_val_snoc W Z hZ

/-! ### The one-step lift and the translated lift -/

/-- Appending a letter to a reduced walk while keeping it reduced. -/
abbrev snocWalk (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf)
    (hred : Reduced (C := C) (X.1 ++ [o])) : RWalk (C := C) u :=
  ⟨X.1 ++ [o], isWalk_snoc X hsrc, hred⟩

@[simp] lemma snocWalk_val (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf)
    (hred : Reduced (C := C) (X.1 ++ [o])) : (snocWalk X o hsrc hred).1 = X.1 ++ [o] := rfl

lemma snocWalk_ne (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf)
    (hred : Reduced (C := C) (X.1 ++ [o])) : (snocWalk X o hsrc hred).1 ≠ [] := by
  rw [snocWalk_val]; simp

lemma snocWalk_dropLast (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf)
    (hred : Reduced (C := C) (X.1 ++ [o])) : (snocWalk X o hsrc hred).dropLast = X := by
  refine Subtype.ext ?_
  show (X.1 ++ [o]).dropLast = X.1
  exact List.dropLast_concat

lemma snocWalk_lastLetter (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf)
    (hred : Reduced (C := C) (X.1 ++ [o])) (hne : (snocWalk X o hsrc hred).1 ≠ []) :
    (snocWalk X o hsrc hred).lastLetter hne = o := by
  rw [RWalk.lastLetter]
  exact List.getLast_append_singleton X.1

lemma concatPt_eq_snocWalk (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf)
    (hred : Reduced (C := C) (X.1 ++ [o])) :
    concatPt X o hsrc = snocWalk X o hsrc hred := by
  refine Subtype.ext ?_
  show redL (X.1 ++ [o]) = X.1 ++ [o]
  exact redL_eq_self_of_reduced hred

lemma concatPt_eq_dropLast (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf)
    (hXs : X.1 ≠ []) (ho : o = (X.1.getLast hXs).neg) :
    concatPt X o hsrc = X.dropLast := by
  refine Subtype.ext ?_
  show redL (X.1 ++ [o]) = X.1.dropLast
  exact redL_append_singleton_eq_dropLast X.2.2 hXs ho

/-- The lift of a single edge, in the case where no cancellation occurs. -/
noncomputable def stepPathA (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf)
    (hred : Reduced (C := C) (X.1 ++ [o])) :
    Path (vertex X) (vertex (concatPt X o hsrc)) :=
  (edgePath (snocWalk X o hsrc hred) (snocWalk_ne X o hsrc hred)).symm.cast
    (congrArg (vertex (C := C) (u := u)) (snocWalk_dropLast X o hsrc hred).symm)
    (congrArg (vertex (C := C) (u := u)) (concatPt_eq_snocWalk X o hsrc hred))

/-- The lift of a single edge, in the case where the last letter of `X` cancels. -/
noncomputable def stepPathB (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf)
    (hXs : X.1 ≠ []) (ho : o = (X.1.getLast hXs).neg) :
    Path (vertex X) (vertex (concatPt X o hsrc)) :=
  (edgePath X hXs).cast rfl
    (congrArg (vertex (C := C) (u := u)) (concatPt_eq_dropLast X o hsrc hXs ho))

lemma proj_stepPathA (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf)
    (hred : Reduced (C := C) (X.1 ++ [o])) (t : unitInterval) :
    proj (C := C) (stepPathA X o hsrc hred t) = OEdge.path (C := C) o t := by
  show proj (C := C) ((edgePath (snocWalk X o hsrc hred) (snocWalk_ne X o hsrc hred)).symm t)
    = OEdge.path (C := C) o t
  show proj (C := C) (ept (snocWalk X o hsrc hred) (snocWalk_ne X o hsrc hred)
    (unitInterval.symm t)) = OEdge.path (C := C) o t
  rw [proj_ept, snocWalk_lastLetter]
  show (OEdge.path (C := C) o).symm (unitInterval.symm t) = OEdge.path (C := C) o t
  show OEdge.path (C := C) o (unitInterval.symm (unitInterval.symm t)) = OEdge.path (C := C) o t
  rw [unitInterval.symm_symm]

lemma proj_stepPathB (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf)
    (hXs : X.1 ≠ []) (ho : o = (X.1.getLast hXs).neg) (t : unitInterval) :
    proj (C := C) (stepPathB X o hsrc hXs ho t) = OEdge.path (C := C) o t := by
  show proj (C := C) (edgePath X hXs t) = OEdge.path (C := C) o t
  show proj (C := C) (ept X hXs t) = OEdge.path (C := C) o t
  rw [proj_ept]
  have hlast : X.lastLetter hXs = o.neg := by
    rw [RWalk.lastLetter]
    rw [show X.1.getLast hXs = o.neg from by rw [ho, OEdge.neg_neg]]
  rw [hlast]
  show (OEdge.path (C := C) o.neg).symm t = OEdge.path (C := C) o t
  show OEdge.path (C := C) o.neg (unitInterval.symm t) = OEdge.path (C := C) o t
  rw [path_neg_apply]
  show (OEdge.path (C := C) o).symm (unitInterval.symm t) = OEdge.path (C := C) o t
  show OEdge.path (C := C) o (unitInterval.symm (unitInterval.symm t)) = OEdge.path (C := C) o t
  rw [unitInterval.symm_symm]

/-- The lift of a single edge, in general. -/
noncomputable def stepPath (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf) :
    Path (vertex X) (vertex (concatPt X o hsrc)) := by
  classical
  exact if hred : Reduced (C := C) (X.1 ++ [o]) then stepPathA X o hsrc hred
    else stepPathB X o hsrc (notReduced_snoc_ne_nil hred)
      (notReduced_snoc_eq_neg X.2.2 (notReduced_snoc_ne_nil hred) hred)

lemma proj_stepPath (X : RWalk (C := C) u) (o : OEdge (C := C)) (hsrc : o.src = X.endOf)
    (t : unitInterval) :
    proj (C := C) (stepPath X o hsrc t) = OEdge.path (C := C) o t := by
  unfold stepPath
  split_ifs with hred
  · exact proj_stepPathA X o hsrc hred t
  · exact proj_stepPathB X o hsrc _ _ t

/-! ### The lifted walk path -/

/-- The lift of a walk translated by a closed walk at `u`. -/
noncomputable def transWalkAux : (n : ℕ) → (Z : RWalk (C := C) u) → Z.1.length = n →
    (W : Lcw (C := C) u) → Path (vertex (C := C) W.1) (vertex (C := C) (concat W Z))
  | 0, Z, h, W => (Path.refl (vertex (C := C) W.1)).cast rfl
      (congrArg (vertex (C := C) (u := u)) (concat_eq_self_of_length_zero W Z h))
  | n+1, Z, h, W => by
      have hZ : Z.1 ≠ [] := by intro hc; rw [hc, List.length_nil] at h; omega
      have hlen : Z.dropLast.1.length = n := by
        rw [RWalk.dropLast_val, List.length_dropLast, h]; omega
      have hsrc : (Z.lastLetter hZ).src = (concat W Z.dropLast).endOf := by
        rw [concat_endOf]
        exact (RWalk.endOf_dropLast_eq_lastLetter_src Z hZ).symm
      refine (transWalkAux n Z.dropLast hlen W).trans ?_
      refine (stepPath (concat W Z.dropLast) (Z.lastLetter hZ) hsrc).cast rfl ?_
      exact congrArg (vertex (C := C) (u := u))
        (concat_eq_concatPt (C := C) (hsrc := hsrc) W Z hZ rfl rfl)

/-- **The translated lift projects like the untranslated one.** -/
lemma proj_transWalkAux : ∀ (n : ℕ) (Z : RWalk (C := C) u) (h : Z.1.length = n)
    (W : Lcw (C := C) u) (t : unitInterval),
    proj (C := C) (transWalkAux n Z h W t) = proj (C := C) (walkPathAux n Z h t)
  | 0, Z, h, W, t => by
      rw [transWalkAux.eq_1, walkPathAux.eq_1]
      show vpt (C := C) W.1.endOf = vpt (C := C) (RWalk.nil (C := C) u).endOf
      rw [W.2]
      rfl
  | n+1, Z, h, W, t => by
      have hZ : Z.1 ≠ [] := by intro hc; rw [hc, List.length_nil] at h; omega
      have hlen : Z.dropLast.1.length = n := by
        rw [RWalk.dropLast_val, List.length_dropLast, h]; omega
      rw [transWalkAux.eq_2, walkPathAux.eq_2]
      rw [Path.trans_apply, Path.trans_apply]
      split_ifs with ht
      · exact proj_transWalkAux n Z.dropLast hlen W _
      · show proj (C := C) (stepPath (concat W Z.dropLast) (Z.lastLetter hZ) _ _) =
          proj (C := C) ((edgePath Z hZ).symm _)
        rw [proj_stepPath]
        show OEdge.path (C := C) (Z.lastLetter hZ) _ = proj (C := C) ((edgePath Z hZ).symm _)
        show OEdge.path (C := C) (Z.lastLetter hZ) _ =
          proj (C := C) (ept Z hZ (unitInterval.symm _))
        rw [proj_ept]
        show OEdge.path (C := C) (Z.lastLetter hZ) _ =
          (OEdge.path (C := C) (Z.lastLetter hZ)).symm (unitInterval.symm _)
        show OEdge.path (C := C) (Z.lastLetter hZ) _ =
          OEdge.path (C := C) (Z.lastLetter hZ) (unitInterval.symm (unitInterval.symm _))
        rw [unitInterval.symm_symm]

/-! ### Monodromy of the lifted walk -/

lemma proj_vertex_nil : proj (C := C) (u := u) (vertex (RWalk.nil (C := C) u)) =
    vpt (C := C) u := rfl

/-- The class in the fundamental groupoid of the base represented by the lifted walk `Z`. -/
noncomputable def psiR (Z : RWalk (C := C) u) :
    Path.Homotopic.Quotient (proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)))
      (proj (C := C) (vertex (C := C) Z)) :=
  ⟦(walkPathAux (C := C) Z.1.length Z rfl).map continuous_proj⟧

lemma psiR_eq (Z : RWalk (C := C) u) :
    psiR (C := C) Z =
      ⟦(walkPathAux (C := C) Z.1.length Z rfl).map continuous_proj⟧ := rfl

/-- The element of the fundamental group of the base represented by a closed reduced walk. -/
noncomputable def Psi (Z : Lcw (C := C) u) :
    FundamentalGroup Y (proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))) :=
  (psiR (C := C) Z.1).cast rfl
    (((proj_vertex (C := C) Z.1).trans
      ((congrArg (vpt (C := C)) Z.2).trans (proj_vertex_nil (C := C) (u := u)).symm)).symm)

lemma Psi_eq (Z : Lcw (C := C) u) :
    Psi (C := C) Z = (psiR (C := C) Z.1).cast rfl
      (((proj_vertex (C := C) Z.1).trans
        ((congrArg (vpt (C := C)) Z.2).trans (proj_vertex_nil (C := C) (u := u)).symm)).symm) := rfl

/-- **The monodromy of `Psi Z` at the base vertex is `vertex Z`.** -/
theorem monodromy_Psi (cov : IsCoveringMap (proj (C := C) (u := u))) (Z : Lcw (C := C) u) :
    ((IsCoveringMap.monodromy cov (Psi (C := C) Z)
        (⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩ :
          proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))}) :
        proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))}) :
        Tree (C := C) u)
      = vertex (C := C) Z.1 := by
  refine Eq.trans (congrArg (Subtype.val) (IsCoveringMap.monodromy_eq_of_map_eq cov
    (γ := Psi (C := C) Z)
    (x := proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)))
    (y := proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)))
    (ex := ⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩)
    (ey := ⟨vertex (C := C) Z.1, (proj_vertex (C := C) Z.1).trans
      ((congrArg (vpt (C := C)) Z.2).trans (proj_vertex_nil (C := C) (u := u)).symm)⟩)
    (Γ := ⟦walkPathAux (C := C) Z.1.1.length Z.1 rfl⟧) ?_)) rfl
  rw [Psi_eq]
  simp only [Path.Homotopic.Quotient.cast_cast]
  rw [psiR_eq]
  simp only [Path.Homotopic.Quotient.mk''_eq_mk]
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
  congr 1

/-- **The monodromy of `Psi A` at the translate of the base vertex by `B`.** -/
theorem monodromy_Psi_translate (cov : IsCoveringMap (proj (C := C) (u := u)))
    (A : Lcw (C := C) u) (B : Lcw (C := C) u) :
    ((IsCoveringMap.monodromy cov (Psi (C := C) A)
        (⟨vertex (C := C) B.1, (proj_vertex (C := C) B.1).trans
          ((congrArg (vpt (C := C)) B.2).trans (proj_vertex_nil (C := C) (u := u)).symm)⟩ :
          proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))}) :
        proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))}) :
        Tree (C := C) u)
      = vertex (C := C) (concat B A.1) := by
  refine Eq.trans (congrArg (Subtype.val) (IsCoveringMap.monodromy_eq_of_map_eq cov
    (γ := Psi (C := C) A)
    (x := proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)))
    (y := proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)))
    (ex := ⟨vertex (C := C) B.1, (proj_vertex (C := C) B.1).trans
      ((congrArg (vpt (C := C)) B.2).trans (proj_vertex_nil (C := C) (u := u)).symm)⟩)
    (ey := ⟨vertex (C := C) (concat B A.1),
      (proj_vertex (C := C) (concat B A.1)).trans
        ((congrArg (vpt (C := C)) ((concat_endOf B A.1).trans A.2)).trans
          (proj_vertex_nil (C := C) (u := u)).symm)⟩)
    (Γ := ⟦transWalkAux (C := C) A.1.1.length A.1 rfl B⟧) ?_)) rfl
  rw [Psi_eq]
  simp only [Path.Homotopic.Quotient.cast_cast]
  rw [psiR_eq]
  simp only [Path.Homotopic.Quotient.mk''_eq_mk]
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
  congr 1
  refine Path.ext (funext fun t => ?_)
  show proj (C := C) (transWalkAux (C := C) A.1.1.length A.1 rfl B t) =
    proj (C := C) (walkPathAux (C := C) A.1.1.length A.1 rfl t)
  exact proj_transWalkAux (C := C) A.1.1.length A.1 rfl B t


/-! ### The monodromy action is free -/

/-- The monodromy of a path class at the base vertex of the universal cover is computed by the
path lifting property. -/
theorem monodromy_base (cov : IsCoveringMap (proj (C := C) (u := u)))
    (g : Path (proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)))
      (proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)))) :
    (IsCoveringMap.monodromy cov (Path.Homotopic.Quotient.mk g)
      (⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩ :
        proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))})).1
      = IsCoveringMap.liftPath cov g (vertex (C := C) (RWalk.nil (C := C) u))
          (g.source.trans (rfl : proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)) = _).symm) 1 :=
  rfl

/-- **The monodromy action of the fundamental group of the base on the universal cover is free.** -/
theorem monodromy_eq_one_imp (cov : IsCoveringMap (proj (C := C) (u := u)))
    {γ : FundamentalGroup Y (proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)))}
    (h : IsCoveringMap.monodromy cov γ
        (⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩ :
          proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))}) =
      ⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩) : γ = 1 := by
  obtain ⟨g, hg⟩ := Quotient.exists_rep γ
  have hg' : Path.Homotopic.Quotient.mk g = γ := hg
  have h' : IsCoveringMap.monodromy cov (Path.Homotopic.Quotient.mk g)
      (⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩ :
        proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))}) =
      ⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩ := by
    rw [hg']
    exact h
  have hlift : IsCoveringMap.liftPath cov g (vertex (C := C) (RWalk.nil (C := C) u))
      (g.source.trans (rfl : proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)) = _).symm) 1
      = vertex (C := C) (RWalk.nil (C := C) u) := by
    have := congrArg (Subtype.val) h'
    rw [monodromy_base] at this
    exact this
  let L : Path (vertex (C := C) (RWalk.nil (C := C) u))
      (vertex (C := C) (RWalk.nil (C := C) u)) :=
    ⟨IsCoveringMap.liftPath cov g (vertex (C := C) (RWalk.nil (C := C) u))
        (g.source.trans (rfl : proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)) = _).symm),
      IsCoveringMap.liftPath_zero .., hlift⟩
  have hL : Path.Homotopic.Quotient.mk L =
      Path.Homotopic.Quotient.mk (Path.refl (vertex (C := C) (RWalk.nil (C := C) u))) :=
    Quotient.sound (SimplyConnectedSpace.paths_homotopic L (Path.refl _))
  have hmap : (Path.Homotopic.Quotient.mk L).map ⟨proj (C := C) (u := u), continuous_proj⟩
      = Path.Homotopic.Quotient.mk g := by
    rw [← Path.Homotopic.Quotient.mk_map]
    refine congrArg Path.Homotopic.Quotient.mk (Path.ext (funext fun t => ?_))
    show proj (C := C) (IsCoveringMap.liftPath cov g (vertex (C := C) (RWalk.nil (C := C) u))
      (g.source.trans (rfl : proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)) = _).symm) t)
      = g t
    exact congrFun (IsCoveringMap.liftPath_lifts cov g (vertex (C := C) (RWalk.nil (C := C) u))
      (g.source.trans (rfl : proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)) = _).symm)) t
  have hone : (Path.Homotopic.Quotient.mk (Path.refl (vertex (C := C) (RWalk.nil (C := C) u)))).map
      ⟨proj (C := C) (u := u), continuous_proj⟩
      = (1 : FundamentalGroup Y (proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)))) := by
    rw [← Path.Homotopic.Quotient.mk_map, FundamentalGroup.one_def,
      ← Path.Homotopic.Quotient.mk_refl]
    exact congrArg Path.Homotopic.Quotient.mk (Path.ext rfl)
  rw [← hg', ← hmap, hL, hone]

/-- **The monodromy map at the base vertex is injective.** -/
theorem monodromy_injective (cov : IsCoveringMap (proj (C := C) (u := u))) :
    Function.Injective fun γ : FundamentalGroup Y
        (proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))) =>
      IsCoveringMap.monodromy cov γ
        (⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩ :
          proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))}) := by
  intro γ γ' h
  have h' : IsCoveringMap.monodromy cov γ
        (⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩ :
          proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))}) =
      IsCoveringMap.monodromy cov γ'
        (⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩ :
          proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))}) := h
  have hmul : ∀ a b : FundamentalGroup Y
      (proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))),
      IsCoveringMap.monodromy cov (a * b)
          (⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩ :
            proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))}) =
        IsCoveringMap.monodromy cov a (IsCoveringMap.monodromy cov b
          (⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩ :
            proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))})) := by
    intro a b
    rw [FundamentalGroup.mul_def, IsCoveringMap.monodromy_trans_apply]
  have h1 : IsCoveringMap.monodromy cov (γ⁻¹ * γ')
      (⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩ :
        proj (C := C) ⁻¹' {proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))}) =
      ⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩ := by
    rw [hmul γ⁻¹ γ', ← h', ← hmul γ⁻¹ γ, inv_mul_cancel]
    exact congrFun (IsCoveringMap.monodromy_refl cov
      (x := proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)))) _
  have := monodromy_eq_one_imp cov h1
  rwa [inv_mul_eq_one] at this



/-! ### The group structure on the closed walks and the fundamental group -/

/-- The basepoint of the universal cover, over which the monodromy is computed. -/
abbrev basePt :
    proj (C := C) (u := u) ⁻¹'
      {proj (C := C) (u := u) (vertex (C := C) (RWalk.nil (C := C) u))} :=
  ⟨vertex (C := C) (RWalk.nil (C := C) u), rfl⟩

/-- The target of the monodromy of `Psi Z` as an element of the fibre. -/
abbrev targetPt (Z : Lcw (C := C) u) :
    proj (C := C) (u := u) ⁻¹'
      {proj (C := C) (u := u) (vertex (C := C) (RWalk.nil (C := C) u))} :=
  ⟨vertex (C := C) Z.1, (proj_vertex (C := C) Z.1).trans
    ((congrArg (vpt (C := C)) Z.2).trans (proj_vertex_nil (C := C) (u := u)).symm)⟩

theorem monodromy_Psi' (cov : IsCoveringMap (proj (C := C) (u := u))) (Z : Lcw (C := C) u) :
    IsCoveringMap.monodromy cov (Psi (C := C) Z) (basePt (C := C) (u := u)) =
      targetPt (C := C) Z :=
  Subtype.ext (monodromy_Psi cov Z)

theorem monodromy_Psi_translate' (cov : IsCoveringMap (proj (C := C) (u := u)))
    (A : Lcw (C := C) u) (B : Lcw (C := C) u) :
    IsCoveringMap.monodromy cov (Psi (C := C) A) (targetPt (C := C) B) =
      ⟨vertex (C := C) (concat B A.1),
        (proj_vertex (C := C) (concat B A.1)).trans
          ((congrArg (vpt (C := C)) ((concat_endOf B A.1).trans A.2)).trans
            (proj_vertex_nil (C := C) (u := u)).symm)⟩ :=
  Subtype.ext (monodromy_Psi_translate cov A B)

theorem Psi_one (cov : IsCoveringMap (proj (C := C) (u := u))) :
    Psi (C := C) (1 : Lcw (C := C) u) = 1 := by
  refine monodromy_injective cov ?_
  change IsCoveringMap.monodromy cov (Psi (C := C) (1 : Lcw (C := C) u))
      (basePt (C := C) (u := u)) =
    IsCoveringMap.monodromy cov (1 : FundamentalGroup Y
      (proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)))) (basePt (C := C) (u := u))
  rw [monodromy_Psi', show (targetPt (C := C) (1 : Lcw (C := C) u)) =
      (basePt (C := C) (u := u)) from rfl]
  exact (congrFun (IsCoveringMap.monodromy_refl cov
    (x := proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u)))) _).symm

theorem Psi_mul (cov : IsCoveringMap (proj (C := C) (u := u)))
    (A : Lcw (C := C) u) (B : Lcw (C := C) u) :
    Psi (C := C) (Lcw.mul B A) = Psi (C := C) A * Psi (C := C) B := by
  refine monodromy_injective cov ?_
  change IsCoveringMap.monodromy cov (Psi (C := C) (Lcw.mul B A)) (basePt (C := C) (u := u)) =
    IsCoveringMap.monodromy cov (Psi (C := C) A * Psi (C := C) B) (basePt (C := C) (u := u))
  rw [monodromy_Psi',
    show Psi (C := C) A * Psi (C := C) B = (Psi (C := C) B).trans (Psi (C := C) A) from rfl,
    IsCoveringMap.monodromy_trans_apply, monodromy_Psi', monodromy_Psi_translate']
  rfl

/-- The monoid homomorphism from the opposite of the group of closed reduced walks to the
fundamental group of the base. -/
noncomputable def PsiHom (cov : IsCoveringMap (proj (C := C) (u := u))) :
    (Lcw (C := C) u)ᵐᵒᵖ →* FundamentalGroup Y
      (proj (C := C) (vertex (C := C) (RWalk.nil (C := C) u))) where
  toFun Z := Psi (C := C) Z.unop
  map_one' := Psi_one cov
  map_mul' A B := Psi_mul cov A.unop B.unop

theorem Psi_injective (cov : IsCoveringMap (proj (C := C) (u := u))) :
    Function.Injective (Psi (C := C) (u := u)) := by
  intro A B hAB
  have h : IsCoveringMap.monodromy cov (Psi (C := C) A) (basePt (C := C) (u := u)) =
      IsCoveringMap.monodromy cov (Psi (C := C) B) (basePt (C := C) (u := u)) := by
    rw [hAB]
  rw [monodromy_Psi', monodromy_Psi'] at h
  exact Subtype.ext (vertex_injective (Subtype.ext_iff.mp h))

theorem Psi_surjective (cov : IsCoveringMap (proj (C := C) (u := u))) :
    Function.Surjective (Psi (C := C) (u := u)) := by
  intro γ
  obtain ⟨W, hW, hx⟩ := exists_vertex_of_proj_eq (C := C)
    (x := (IsCoveringMap.monodromy cov γ (basePt (C := C) (u := u))).1)
    (IsCoveringMap.monodromy cov γ (basePt (C := C) (u := u))).2
  refine ⟨⟨W, hW⟩, ?_⟩
  refine monodromy_injective cov ?_
  change IsCoveringMap.monodromy cov (Psi (C := C) ⟨W, hW⟩) (basePt (C := C) (u := u)) =
    IsCoveringMap.monodromy cov γ (basePt (C := C) (u := u))
  rw [monodromy_Psi']
  exact Subtype.ext hx.symm

/-- Inversion reverses the product, so the opposite group of the closed walks is itself. -/
noncomputable def Lcw.opSelf (u : Topology.CWComplex.cell C 0) :
    (Lcw (C := C) u)ᵐᵒᵖ ≃* Lcw (C := C) u where
  toFun W := W.unop⁻¹
  invFun W := MulOpposite.op W⁻¹
  left_inv W := by simp
  right_inv W := by simp
  map_mul' A B := by
    show (A * B).unop⁻¹ = (A.unop)⁻¹ * (B.unop)⁻¹
    rw [show (A * B).unop = B.unop * A.unop from rfl, mul_inv_rev]

/-- **The fundamental group of a one-dimensional CW complex at a vertex is free.** -/
theorem isFreeGroup_vertex {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n))
    (u : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    IsFreeGroup (FundamentalGroup X
      (proj (C := Set.univ) (u := u) (vertex (C := Set.univ) (RWalk.nil (C := Set.univ) u)))) := by
  haveI : IsFreeGroup (Lcw (C := Set.univ) u) := isFreeGroup_Lcw (C := Set.univ) u
  haveI : IsFreeGroup ((Lcw (C := Set.univ) u)ᵐᵒᵖ) :=
    IsFreeGroup.ofMulEquiv (Lcw.opSelf (C := Set.univ) u).symm
  refine IsFreeGroup.ofMulEquiv (MulEquiv.ofBijective
    (PsiHom (C := Set.univ) (u := u) (isCoveringMap_proj h2 u)) ⟨?_, ?_⟩)
  · intro A B h
    exact MulOpposite.unop_injective (Psi_injective (isCoveringMap_proj h2 u) h)
  · intro γ
    obtain ⟨Z, hZ⟩ := Psi_surjective (isCoveringMap_proj h2 u) γ
    exact ⟨MulOpposite.op Z, hZ⟩

end Tree

end



/-! ### Every point of a one-dimensional CW complex is joined to a vertex -/

/-- The path from a point of the characteristic path of an edge to its source vertex. -/
noncomputable def OEdge.pathToSrc {X : Type*} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (o : OEdge (C := (Set.univ : Set X))) (t : unitInterval) :
    Path (OEdge.path (C := (Set.univ : Set X)) o t) (vpt (C := (Set.univ : Set X)) o.src) where
  toFun s := OEdge.path (C := (Set.univ : Set X)) o
    ⟨(1 - (s : ℝ)) * (t : ℝ),
      ⟨mul_nonneg (sub_nonneg.mpr s.2.2) t.2.1, by
        have h1 := s.2.1; have h2 := s.2.2; have h3 := t.2.2
        nlinarith⟩⟩
  continuous_toFun := (OEdge.path (C := (Set.univ : Set X)) o).continuous.comp
    (Continuous.subtype_mk (by fun_prop) _)
  source' :=
    congrArg (OEdge.path (C := (Set.univ : Set X)) o) (Subtype.ext (by norm_num))
  target' :=
    Eq.trans (congrArg (OEdge.path (C := (Set.univ : Set X)) o) (Subtype.ext (by norm_num)))
      (OEdge.path (C := (Set.univ : Set X)) o).source

/-- The closed `1`-cell of `j` is contained in the image of the characteristic path of the
oriented edge `⟨j, true⟩`. -/
lemma closedCell_one_subset_range {X : Type*} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (j : Topology.CWComplex.cell (Set.univ : Set X) 1) :
    Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) 1 j ⊆
      Set.range (OEdge.path (C := (Set.univ : Set X)) ⟨j, true⟩) := by
  intro y hy
  rw [Topology.RelCWComplex.closedCell] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hb : |x 0| ≤ 1 := by
    have h := Metric.mem_closedBall.mp hx
    rw [dist_zero_right] at h
    simpa only [Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sup_singleton, coe_nnnorm, Real.norm_eq_abs] using h
  refine ⟨⟨(x 0 + 1) / 2, ⟨by linarith [(abs_le.mp hb).1], by linarith [(abs_le.mp hb).2]⟩⟩, ?_⟩
  show OEdge.path (C := (Set.univ : Set X)) ⟨j, true⟩ _ =
    Topology.RelCWComplex.map (C := (Set.univ : Set X)) 1 j x
  rw [show OEdge.path (C := (Set.univ : Set X)) ⟨j, true⟩ = fwdPath (C := (Set.univ : Set X)) j
    from rfl]
  show Topology.RelCWComplex.map (C := (Set.univ : Set X)) 1 j (segF _) =
    Topology.RelCWComplex.map (C := (Set.univ : Set X)) 1 j x
  congr 1
  funext i
  fin_cases i
  show 2 * ((x 0 + 1) / 2 : ℝ) - 1 = x 0
  ring

/-- **Every point of a one-dimensional CW complex is joined to a vertex.** -/
lemma exists_path_to_vertex {X : Type*} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n)) (y : X) :
    ∃ u : Topology.CWComplex.cell (Set.univ : Set X) 0,
      Nonempty (Path y (vpt (C := (Set.univ : Set X)) u)) := by
  have hy : y ∈ ⋃ (n : ℕ) (j : Topology.RelCWComplex.cell (Set.univ : Set X) n),
      Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) n j := by
    rw [Topology.CWComplex.union]
    trivial
  simp only [Set.mem_iUnion] at hy
  obtain ⟨n, j, hyj⟩ := hy
  rcases n with _ | _ | n
  · have hy' : y = vpt (C := (Set.univ : Set X)) j := by
      simpa only [Topology.RelCWComplex.closedCell_zero_eq_singleton, Set.mem_singleton_iff, vpt]
        using hyj
    exact ⟨j, ⟨(Path.refl y).cast rfl hy'.symm⟩⟩
  · obtain ⟨t, ht⟩ := closedCell_one_subset_range j hyj
    refine ⟨srcIdx (C := (Set.univ : Set X)) j,
      ⟨(OEdge.pathToSrc (X := X) ⟨j, true⟩ t).cast ht.symm
        (congrArg (vpt (C := (Set.univ : Set X)))
          (OEdge.src_mk_true (C := (Set.univ : Set X)) j)).symm⟩⟩
  · exact ((h2 (n + 2) (by omega)).false j).elim

/-- A one-dimensional CW complex with no cells in dimension `≥ 2` and nonempty is nonempty in
dimension `0`. -/
lemma nonempty_cell_zero {X : Type*} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n))
    (hne : Nonempty X) : Nonempty (Topology.CWComplex.cell (Set.univ : Set X) 0) := by
  obtain ⟨y⟩ := hne
  have hy : y ∈ ⋃ (n : ℕ) (j : Topology.RelCWComplex.cell (Set.univ : Set X) n),
      Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) n j := by
    rw [Topology.CWComplex.union]
    trivial
  simp only [Set.mem_iUnion] at hy
  obtain ⟨n, j, _⟩ := hy
  rcases n with _ | _ | n
  · exact ⟨j⟩
  · exact ⟨srcIdx (C := (Set.univ : Set X)) j⟩
  · exact ((h2 (n + 2) (by omega)).false j).elim

end CWGraph

end Commons.AlgebraicTopology.FundamentalGroup
/-
## Roadmap for the completion of this file

The slice universal-cover route to `freeGroup_of_oneDimCWComplex` proceeds as follows.

Data attached to a one-dimensional CW complex `Y` (no cells of dimension `≥ 2`), defined above:
`vpt`, `srcIdx`, `tgtIdx`, `OEdge` (an oriented 1-cell) with `OEdge.path` (the traversal),
`IsWalk`/`Walk`/`Walk.pathOf` (combinatorial walks and their realisations in `Y`),
`Reduced`/`RWalk` (reduced walks, their endpoint and `dropLast`), and

`Tree u` : the universal cover of the one-skeleton, as a quotient of the vertices (= reduced walks
from `u`) and the edges (= reduced walks of positive length, together with a parameter), where the
two ends of the edge above `W` are glued to `vertex W` and `vertex W.dropLast`.  The projection
`Tree.proj` and the height `Tree.heightPt` are the obvious ones.

Remaining steps (each a concrete Lean target in this file):
1. DONE.  `Reduced` API (`reduced_cons_iff`, preservation under `take`/`dropLast`), the endpoint
   computations (`endOfList_eq_getLast_tgt`, `endOfList_eq_getLast_src`, `endOfList_nil`).
2. DONE.  `treeRel`-invariance of `projPt`/`heightPt` (`heightPt_eqvGen`, `projPt_eqvGen`), giving
   `Tree.proj`, `Tree.height` and their computation lemmas; the topology on `TreePt u` (discrete
   vertices, sum topology), the quotient topology on `Tree u`, `isOpen_prod_discrete_iff`, and the
   characterisations `Tree.isOpen_iff` ("open iff all edge slices are open") and `Tree.continuous_iff`
   ("a map OUT of the tree is continuous iff all composites with `t ↦ ept W hW t` are"), from which
   `Tree.continuous_proj`, `Tree.continuous_height` follow.
3. DONE.  Contractibility of `Tree u`.  The truncation `truncW r W` (`⌈r⌉`-prefix, parameter
   `⌈r⌉ - r`), its well definedness on the glueing relation (`truncPt_eq_of_rel`, `truncPt_eqvGen`),
   the geodesic description `mk_truncW_eq_ept`, the continuity `continuous_geo` (closed locally
   finite cover of `I × I` by the pieces `{k ≤ r ≤ k+1 ∧ k+1 ≤ W.length}`, on each of which the
   truncation is the explicit continuous `Tree.ept`-formula), continuity of the naive contraction
   `continuous_contractPt` (via `Homeomorph.sumProdDistrib`, `continuous_sum_dom`,
   `continuous_prod_of_discrete`, `continuous_prod_prod_of_discrete`), the quotient contraction
   `Tree.contract` with `contract_mk` (computation rule), `continuous_contract` (via
   `Topology.IsQuotientMap.continuous_lift_prod_left`), the endpoints `contract_zero` (uses
   `mk_truncPt_heightPt`) and `contract_one`, and finally the instance `contractibleSpace :
   ContractibleSpace (Tree u)` (from `contractible_iff_id_nullhomotopic`).  Consequently
   `SimplyConnectedSpace (Tree u)` is available by `SimplyConnectedSpace.ofContractible`.
4. NEXT.  `IsCoveringMap (Tree.proj)`: on the open 1-cell of `e` the preimage is a disjoint union of
   the interiors of the edges above `e` (each mapped homeomorphically by the characteristic map,
   using `continuousOn_symm`), and at a vertex `v` the evenly covered neighbourhood is the
   "open star" of `v` (its complement is closed by the weak topology of the CW structure,
   `Topology.CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell`), whose preimage
   is the disjoint union of the open stars of the vertices of `Tree u` over `v`.  Mathlib then gives
   path lifting, homotopy lifting and the monodromy (`Topology.IsCoveringMap.exists_path_lifts`,
   `liftPath`, `liftHomotopy`, `monodromy`, `fundamentalGroupEquiv`, ...).
   USEFUL API: `Topology.IsCoveringMap` is `Mathlib.Topology.Covering.Basic`; the lifting lemmas are
   in `Mathlib.Topology.Homotopy.Lifting` (with `SimplyConnectedSpace` hypotheses!).
5. Lift computation: for a reduced walk `W` from `u`, the lift of `Walk.pathOf W` starting at the
   base vertex ends at `vertex W` (induction on `W`, using that `W` is reduced so each new letter
   is not the inverse of the last one, whence the lift goes to `vertex (W ++ [letter])`).
6. The group `G`: the subgroup of `FreeGroup (OEdge)` generated by the words of the closed reduced
   walks at `u`.  It is free by Nielsen–Schreier (`IsFreeGroupoid.subgroupIsFreeOfIsFree`).  The map
   `φ : G →* FundamentalGroup Y (vpt u)`, sending (the word of) a closed walk to the class of its
   realisation, is well defined because cancelling a backtracking pair `o o.neg` is a homotopy
   rel endpoints supported in the closed cell of `o`; it is a homomorphism by construction and
   injective by steps 4-5 (if `φ g = 1`, homotopy lifting shows the lift of the loop both ends at
   `vertex W` and at the base vertex, so `W` is the empty walk); it is surjective by step 3
   (any two paths in the simply connected tree with the same endpoints are homotopic, so the loop
   is homotopic to the realisation of the walk given by its lift).
7. Assembly: `FundamentalGroup Y (vpt u) ≃* G` is free; transfer along a path from any basepoint
   to a vertex (every point lies in a cell, which is convex) and along the given homotopy
   equivalence `X ≃ₕ Y` (`Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv`).

## Implementation notes (hard-won)

* `RWalk` and `TreePt` are `abbrev`s (NOT `def`s): with `def`s many tactics fail with
  "the target expression is not type-correct under the `implicit` transparency level".
  `Tree` is still a `def` (so terms of type `Tree u` are `Quotient.mk _ _`, displayed `⟦x⟧`;
  rewriting with lemmas stated using `Tree.mk` can fail -- state such lemmas with `Quotient.mk`).
* `discrete` = `⊥`, not `⊤` (Mathlib's `DiscreteTopology` field is `eq_bot`).
* Dependent rewrites of the form `⌈r⌉₊ → k` (with `k` a natural number that appears inside a proof
  argument) need `subst`/`cases` on a *variable*, or `Subtype.ext`-based equality of the whole
  subtype element -- plain `rw` fails with "motive is not type correct".
* `Relation.EqvGen.rel` takes `(x y : α) (h : r x y)` with `x y` explicit; the relation is inferred
  from `h`, so the hypothesis must be *stated* with type `treeRel ...` (an `Or.inl`-proof would
  make Lean infer `r := Or`).
* Casts: `↑(0 : ℕ) : ℝ` and `0 : ℝ` are NOT definitionally equal (`Nat.cast_zero` is a theorem);
  same for `↑(1 : unitInterval)` vs `1` (there `rfl` does work).
* The file sets `set_option maxHeartbeats 1000000`.
* For step 4 (the covering map): Mathlib's `Topology.RelCWComplex` structure gives, for a cell
  `map n i : PartialEquiv (Fin n → ℝ) X`, the facts `source_eq : source = ball 0 1`,
  `continuousOn : ContinuousOn (map n i) (closedBall 0 1)`, `continuousOn_symm :
  ContinuousOn (map n i).symm (map n i).target`, while `PartialEquiv.injOn` gives injectivity on the
  source.  `RelCWComplex.openCell n i` is *defined* as `map n i '' ball 0 1`, and
  `RelCWComplex.closed` is the weak-topology criterion (a set is closed iff all its intersections
  with closed cells are closed) -- use it (or
  `CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell`, as in
  `Commons/Topology/CWComplex/dimOne/isClosed_vertices.lean`) to show that the "open star" of a
  vertex is open.  `IsCoveringMap` is `Topology.IsCoveringMap` in `Mathlib.Topology.Covering.Basic`
  (`IsEvenlyCovered`, `isCoveringMap_iff_isCoveringMapOn_univ`), and the lifting/homotopy-lifting
  lemmas are in `Mathlib.Topology.Homotopy.Lifting` (`exists_path_lifts`, `liftPath`,
  `liftHomotopy`, `monodromy`, `fundamentalGroupEquiv`, `monodromy_theorem`).  A *proper* local
  homeomorphism is a covering map (`Commons.Topology.Covering.isCoveringMap_of_isProperMap`) but
  `proj` is NOT proper here (its fibres are infinite and discrete).
* DONE (first bit of the vertex case).  `exists_vertex_of_proj_eq : proj x = vpt v → ∃ W, W.endOf = v ∧
  x = vertex W` -- **the fibre of `proj` over a vertex consists of vertices**, with the helpers
  `segF_mem_ball` (`0 < t < 1 → segF t ∈ ball 0 1`) and
  `OEdge.path_mem_openCell` (`0 < s < 1 → OEdge.path o s ∈ openCell 1 o.cell`).  Method: quotient
  induction; a tree point `ept W hW t` projects to `(OEdge.path (W.lastLetter hW)).symm t`
  (`proj_ept`), which for `0 < t < 1` lies in the open *1*-cell (`Path.symm_apply` sends it to
  `path o (unitInterval.symm t)` with `unitInterval.symm t ∈ (0,1)`), while `vpt v` lies in the open
  *0*-cell `{vpt v}`; these two open cells are disjoint (`RelCWComplex.disjoint_openCell_of_ne` at
  the Sigma level, `⟨1, ·⟩ ≠ ⟨0, ·⟩`).  For `t = 0, 1` the point *is* a vertex
  (`ept_zero_eq_vertex`, `ept_one_eq_vertex_dropLast`) and the conclusion is `vpt_injective`.
  CONCRETE NEXT TARGET: `isOpen_halfStar (W : RWalk u)` for the set
  `O_W := {vertex W} ∪ {ept W hW t | (hW : W.1 ≠ []), (t:ℝ) < 1/2}
        ∪ {ept W' hW' t | (W' : RWalk u) (hW' : W'.1 ≠ []), W'.dropLast = W, (1:ℝ)/2 < t}`.
  Openness: `Tree.isOpen_iff` reduces it to the slices `{t | ept W' hW' t ∈ O_W}`, which are
  (i) `[0,1/2)` when `W' = W`, (ii) `(1/2,1]` when `W'.dropLast = W` and `W' ≠ W`, (iii) `∅`
  otherwise -- all open in `unitInterval` because it is a subspace (`[0,1/2) = I ∩ (-1,1/2)`,
  `(1/2,1] = I ∩ (1/2,2)`).  The case analysis needs two facts about `Tree.ept`:
  (A) *interior uniqueness*: for `t, s ∈ (0,1)`, `ept W hW t = ept W' hW' s → W = W' ∧ t = s`.
      A cheap route for the *different cell* case: project both sides (`proj_ept`), the images lie in
      `openCell 1 ·`, and different open cells are disjoint (`disjoint_openCell_of_ne`); when the
      cells agree, the parametrisation is injective by `injOn_map_ball` (via
      `OEdge.path_mem_openCell` and the fact that `map 1 e` is injective on `ball 0 1`).  The "same
      cell, different walk" case needs `Quotient.exact` plus the observation that the glueing
      relation only joins `inr (⟨W,hW⟩,t)` to `inl W` (`t = 0`) and to `inl W.dropLast` (`t = 1`),
      so any `EqvGen` chain through interior points is trivial.
  (B) *vertex characterisation*: `ept W' hW' t ∈ {vertex W}` iff (`t = 0` and `W' = W`) or
      (`t = 1` and `W'.dropLast = W`) -- i.e. `vertex` is injective (`W = W'` from
      `vertex W = vertex W'`), which is proved by the same chain analysis, or by `proj` + the
      fact that two distinct vertices project to distinct points (`vpt_injective`).
  On (A), one more thing I checked: there is NO cheap invariant.  The pair `(Tree.height, Tree.proj)`
  does *not* separate interior points: with two oriented edges `⟨e,true⟩`, `⟨e,false⟩` of the same
  cell, the points `ept [⟨e,true⟩] · (1/2)` and `ept [⟨e,false⟩] · (1/2)` are distinct points of the
  tree (different summands, not glued since the parameters are interior) yet have the same height
  `1/2` and the same projection (`(path ⟨e,true⟩).symm (1/2) = (path ⟨e,false⟩).symm (1/2)`, as
  `path ⟨e,false⟩ = (fwdPath e).symm`).  So (A) really is the chain analysis; the statement to prove
  is, for `x₀ = Sum.inr (⟨W,hW⟩,t)` with `t ≠ 0, 1` explicit,
    `∀ y, Relation.EqvGen (treeRel u) x₀ y → y = x₀`   and   `∀ y, EqvGen y x₀ → y = x₀`
  (the two are needed simultaneously: the `symm` case of the induction turns one into the other).
  Equivalently prove `∀ a b, EqvGen a b → (a = x₀ → b = x₀) ∧ (b = x₀ → a = x₀)` by induction on the
  derivation: the `rel` case is vacuous (`treeRel (Sum.inr (⟨W,hW⟩,t)) (Sum.inl W')` forces
  `t = 0 ∨ t = 1`), `refl` is trivial, `symm`/`trans` use the two halves of the invariant.
  (Alternatively: `Quotient.exact` and a direct description of the `EqvGen` classes of the
  `Sum.inr` points, which is the same work.)
  With (A) and (B) the three slices above follow, `isOpen_halfStar` closes, and then
  `O_W ∩ (proj ⁻¹' {vpt v}) = {vertex W}` (every other point of the fibre is a vertex, and `W` is the
  only vertex in `O_W`), giving the open singletons of the fibre and hence
  `DiscreteTopology (proj ⁻¹' {vpt v})`.
  Next in the vertex case: `DiscreteTopology (proj ⁻¹' {vpt v})`.  By the lemma above the fibre is
  exactly `{vertex W | W.endOf = v}`; to see that its singletons are open, use the *half-open star*
  of `W` (one-sided intervals such as `[0,1/2)` and `(1/2,1]` ARE open in `unitInterval`, since
  `I = [0,1]` carries the subspace topology, so e.g. `[0,1/2) = I ∩ (-1,1/2)`): for the vertex `W`
  and each incident edge take the points whose parameter lies in the half closest to `W` -- the
  vertex itself plus the interiors of the incident edges on the `W` side.  Its slices along the
  edges are `[0,1/2)` resp. `(1/2,1]` (open in `I`) or empty, so it is open by `Tree.isOpen_iff`,
  and it meets the fibre only in `vertex W` (the other points of the fibre are vertices and the only
  vertex in the set is `W`).  Then `DiscreteTopology` follows from "all singletons are open".

* NEXT: step 4, `IsCoveringMap (Tree.proj)` -- do the VERTEX case first (it uses the open star just
  proved); the edge-interior case is separate (`injOn_map_ball` + `proj_ept`).
  Vertex case, concretely.  Fix a `0`-cell `v` and put `U := star v` (the open star of `v` in `Y`,
  `isOpen_openStar` above).  We must produce `IsEvenlyCovered proj (vpt v) (proj ⁻¹' {vpt v})`, i.e.
  - `DiscreteTopology (proj ⁻¹' {vpt v})`: the fibre over a vertex consists exactly of the *vertices*
    `vertex W` with `W.endOf = v`.  (No interior point of an edge of the tree maps to a vertex: by
    `proj_ept`, `proj (ept W hW t) = (OEdge.path (W.lastLetter hW)).symm t`, and this is a vertex only
    for `t = 0, 1`, where it equals `vertex W` resp. `vertex W.dropLast`; use `injOn_map_ball` and
    the disjointness of the open cells of `Y` -- a point of `openCell 1 e` is never in a `0`-cell.)
    Consequently the fibre is a copy of `{W : RWalk u // W.endOf = v}` inside the *discrete* set
    `RWalk u`; the singletons are open in the subspace because for each `W` the set of tree points
    whose walk *is* `W` (vertices and interior points of the edge above `W`) is open -- this is
    `{x | walkOf x = W}`-style openness, provable with `isOpen_iff`/the summands of `TreePt`.
  - the sheets: for `W : RWalk u` with `W.endOf = v`, let
    `sheet W := {vertex W} ∪ {ept W hW t | t} ∪ ⋃ (o : OEdge) (h : reduced (W ++ [o])),
    {ept (W ++ [o]) (…) t | t}` -- the union of the interior of the edge above `W` and of the edges
    *above* the extensions `W ++ [o]`: precisely the tree points whose projection lands in `U` and
    whose walk "contains `W`".  Show
      (a) `proj ⁻¹' U = ⋃ (W) (_ : W.endOf = v), sheet W` (split a tree point by whether an interior
          point of `Y` near the vertex is hit first; the projections `proj_vertex` / `proj_ept` give
          `proj (sheet W) ⊆ U` and surjectivity onto `U` comes from `hW.1 : IsWalk`),
      (b) the `sheet W` are pairwise disjoint (the walks determine the sheet, and open cells of `Y`
          are disjoint),
      (c) each `sheet W` is open in `Tree u` (use `Tree.isOpen_iff`: each slice along an edge is an
          open interval or empty) and `proj` restricts to a *homeomorphism* `sheet W ≃ₜ U`
          (injective because the only fibres of `proj` inside `U` are those of the single cell of `U`
          that the point lies in -- `injOn_map_ball`, plus the frontier points of `U` come only from
          `vertex W`).
    Then the desired `proj ⁻¹' U ≃ₜ U × (proj ⁻¹' {vpt v})` is assembled from the `sheet W`, and the
    compatibility `(H x).1.1 = proj x` is `proj_vertex`/`proj_ept`.
  If this gets long, it is legitimate to prove the vertex case as a standalone lemma
  (`isEvenlyCovered_vertex`) first and only then `IsCoveringMap` from the vertex + edge-interior
  cases; the edge-interior case is the easier half (`proj ⁻¹' openCell 1 e` is the disjoint union of
  the interiors of the edges of the tree above `e`, each mapped homeomorphically by `OEdge.path e`,
  using `injOn_map_ball` and `continuousOn_symm`).

* DONE.  **The open star of a vertex of a one-dimensional CW complex is open**, proved in this file
  as `isOpen_openStar {X} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  (h2 : ∀ n, 2 ≤ n → IsEmpty (cell (univ) n)) (v : cell (univ) 0) :
  IsOpen (⋃ n j, ⋃ (_ : map 0 v ![] ∈ closedCell n j), openCell n j)` (it is stated for an
  arbitrary space `X` with `C = univ`, so it is ready to be extracted to the commons: the
  `request_lemma` at `Topology/CWComplex/openStar_isOpen` was declined three times -- the fleet is
  busy -- retry it, or leave the lemma in the file, it is needed by step 4 either way).
  Proof shape (kept for reference): `A := starᶜ`, `rw [← isClosed_compl_iff]`, then
  `Topology.CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell`, whose per-cell
  obligation only concerns `n > 0` (0-cells are handled internally -- the whole 0-cell case
  disappears); `h2` then reduces it to `n = 1`.  Auxiliary facts: `hmem` (if the closed cell of a
  cell contains `v` then its open cell is inside the star -- true by definition of the star) and
  `hnot` (if not, the star is disjoint from that open cell -- uses only
  `disjoint_openCell_of_ne` at the Sigma level, no `h2`).  For a cell `(1,j)` the star is disjoint
  from `closedCell 1 j` when `v` is not in it: `closedCell 1 j = cellFrontier 1 j ∪ openCell 1 j`,
  the open part is handled by `hnot` (`v ∉ closedCell 1 j`), and a frontier point is one of the two
  endpoints (`cellFrontier_one_eq`, `map_one_neg_one_eq_srcIdx`, `map_one_one_eq_tgtIdx`), say
  `x = map 0 w ![]` with `w = srcIdx j` or `tgtIdx j`; if `map 0 v ![] ∈ closedCell 0 w` then
  `map 0 v ![] = x ∈ closedCell 1 j` (`cellFrontier_subset_closedCell 1 j hx`), contradicting the
  hypothesis, and otherwise `hnot` applies to the 0-cell `w` (since `x` lies in `openCell 0 w`,
  `openCell_zero_eq_singleton`).  Finally `IsClosed (closedCell 1 j)` is
  `RelCWComplex.isClosed_closedCell`.
  Lean-level snags hit on the way (all resolved, recorded because they cost time):
  (i) write cell indices explicitly, `{j' : RelCWComplex.cell (univ : Set X) n'}` (else Lean reads
  `RelCWComplex.cell univ : ℕ → Type`);
  (ii) to get equality of cells from non-disjointness use `RelCWComplex.disjoint_openCell_of_ne` at
  the Sigma level followed by `cases` (plain `rw` cannot see `n''`, `j''` under `closedCell`);
  (iii) `.false j` instead of `.elim j` for `h2 ... : IsEmpty _`;
  (iv) `RelCWComplex.cellFrontier_subset_closedCell` takes `(n) (i)` explicitly:
  `cellFrontier_subset_closedCell (C := univ) 1 j hx`;
  (v) in the `by_cases` about a frontier point `x = map 0 w ![]`, the tested membership must be
  `map 0 v ![] ∈ closedCell 0 w` (not `map 0 w ![] ∈ closedCell 0 w`, which is trivially true).

* DONE (part of step 5): `Tree.edgePath`, `Tree.walkPathAux`, `Tree.walkPath` (the explicit lift of
  a reduced walk to the tree, built by recursion on the length: for every nonempty prefix `W'` of
  `W` traverse the edge above `W'` from below), with `walkPath_zero` and `walkPath_one`.
  NEXT (part of step 5): identify the projection of `walkPath W` with the realisation of `W`.
  WARNING: the pointwise identity `proj (walkPath W t) = (Walk.pathOf ⟨W.1, W.2.1⟩) t` is FALSE:
  `walkPath` is an *end* recursion (`dropLast`, so the last edge occupies the last half of the
  interval) while `Walk.pathOf` is a *front* recursion (`pathOfList`, first edge = first half); the
  two paths are only *homotopic rel endpoints*.  Do it in two steps:
  (a) define the *matching* end-recursive realisation of the walk in `Y`,
      `RWalk.realizeAux : (n : ℕ) → (W : RWalk C u) → W.1.length = n →
      Path (vpt u) (vpt W.endOf)`, with the same recursion as `walkPathAux` (in the step, fix the
      endpoints of `OEdge.path (W.lastLetter hne)` with `RWalk.endOf_dropLast_eq_lastLetter_src` and
      `RWalk.endOf_eq_lastLetter_tgt` via `Path.cast (γ) (hx : x' = x) (hy : y' = y)`; normalise a
      cast inside a rewrite with `Path.cast_coe : ⇑(γ.cast hx hy) = ⇑γ`, and note
      `(Path.cast γ hx hy) t = γ t` is `rfl` after `cases hx; cases hy`).  Then prove
      `proj (walkPathAux n W h t) = realizeAux n W h t` by induction on `n`: rewrite with
      `Path.trans_apply` on both sides, `split_ifs with ht`; the first branch is the induction
      hypothesis, and in the second use `Path.symm_apply`, `proj_ept` and
      `unitInterval.symm_symm` (indeed `(OEdge.path o).symm (unitInterval.symm s) = OEdge.path o s`).
  (b) prove `(RWalk.realize W).Homotopic (Walk.pathOf ⟨W.1, W.2.1⟩)` (induction on the list, using
      `Path.Homotopic.trans_assoc`, `Path.Homotopic.refl_trans`, `Path.Homotopic.trans_refl`).  Only
      the homotopy class (hence the endpoint of the lift) is needed for the monodromy argument of
      step 6, and homotopic lifts of paths with the same starting point have the same endpoint
      (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`).
-/

/-! ## PROGRESS LOG (session 13) — READ THIS FIRST

DONE, all complete, in this file (all inside `namespace CWGraph`):
* `Tree.uOfPt`, `Tree.uOfPt_eq_of_rel`, `Tree.uOfPt_eqvGen`, `Tree.uOf`, `Tree.uOf_vertex`,
  `Tree.vertex_injective` (via the class function `uOf`), `Tree.ept_ne_vertex`,
  `Tree.ept_eq_vertex_iff`, and: `starSet`, `mem_starSet_vertex`, `ept_congr`,
  `ept_mem_starSet_iff`, `isOpen_starSet`.

PLAN FOR THE REST (the shape that has been designed in detail; follow it):

* **DONE (session 14): `isOpen_halfStar`** -- the half-star of a vertex of a one-dimensional CW
  complex is open.  Available and verified (all in the `CWGraph` namespace):
  `halfStar` (def, `{vpt v} ∪ ⋃ (o : OEdge) (_ : o.src = v), OEdge.path o '' {t | (t:ℝ) < 1/2}`),
  `vpt_mem_halfStar`, `fwdPath_image_left/_right` (`fwdPath e '' {t | t < 1/2} =
  map 1 e '' (closedBall 0 1 ∩ {x | x 0 < 0})`, and the `> 1/2` / `0 < x 0` version),
  `fwdPath_symm_image_left`, `symm_image_Ico`, `OEdge_path_image_left`, `path_mk_true/false`
  (`OEdge.path ⟨e,true⟩ = fwdPath e`, `OEdge.path ⟨e,false⟩ = (fwdPath e).symm`),
  `vpt_not_mem_openCell_one`, `cellFrontier_one_subset`, `segF_norm`,
  `segF_eq_endpoints_of_mem_sphere`, `segF_mem_sphere_of_notMem_ball`,
  `path_image_left_subset_closedCell`, `path_image_left_disjoint_openCell`,
  `fwdPath_image_left_vertex`, `fwdPath_symm_image_left_vertex`, `path_image_left_subset`,
  `eq_of_vpt_mem_halfStar` (the only vertex in `halfStar v` is `v`), `eq_neg_one_or_one_of_mem_sphere`,
  `ball_or_eq_neg_one_or_one`, `mem_halfStar_of_half`, `mem_half_of_mem_map_half`, `not_mem_halfStar`.
* NEXT: the *varying radius* version of the same statement,
  `isOpen_epsStar : (∀ o : {o : OEdge // o.src = v}, 0 < ε o) →
  IsOpen ({vpt v} ∪ ⋃ (o : {o : OEdge // o.src = v}), OEdge.path o.1 '' {t | (t:ℝ) < ε o})`;
  the proof is the one of `isOpen_halfStar` with `K_j` cut at the ball-coordinate `2ε-1`
  (compact images of closed bounded sets stay closed, and the endpoints `±1` are handled by
  `mem_half_of_mem_map_half` / `eq_of_vpt_mem_halfStar`).  It is what makes the inverse of the
  trivialization continuous at a vertex.
* **DONE (session 14, second batch).**  `path_symm_symm_apply` (`γ.symm.symm t = γ t`, proved by
  `show γ (σ (σ t)) = γ t` + `unitInterval.symm_symm`), `neg_mk_true/neg_mk_false`,
  `path_neg_apply` (`OEdge.path o.neg t = (OEdge.path o).symm t`),
  `proj_mem_halfStar_of_mem_starSet` (the star of a tree vertex projects *into* the half-star of
  its endpoint), `reduced_append_singleton`, and the "snoc" API for reduced walks
  (`isWalk_snoc`, `reduced_snoc`, `dropLast_snoc`, `lastLetter_snoc`), then
  `exists_mem_starSet_of_mem_halfStar` and **`proj_image_starSet :
  proj '' starSet W = halfStar W.endOf`** -- the star of a tree vertex projects *onto* the
  half-star of its endpoint.  This is the bridge from the half-star to the local triviality.
  NOTE (Lean pitfalls that cost time): `RWalk u = {l : List OEdge // IsWalk u l ∧ Reduced l}`
  (a subtype of `List`, NOT of `Walk`), so the projections are `W.1` (the list), `W.2.1`
  (`IsWalk`), `W.2.2` (`Reduced`), and one must write `RWalk.dropLast x` / `RWalk.lastLetter x h`
  (dot-notation resolves against `Subtype` and fails).  For `simpa`/`rw` on `starSet`, unfold
  membership with `simp only [starSet, Set.mem_union, Set.mem_setOf_eq]` and mind that the union
  is left-nested (so `rcases hx with (hx | ⟨...⟩) | ⟨...⟩`).
* HISTORICAL NOTE (first attempt at the above, removed while broken):
  `neg_mk_true/neg_mk_false : (⟨e,true⟩ : OEdge).neg = ⟨e,false⟩` (proof `rfl`),
  `path_neg_apply : OEdge.path o.neg t = (OEdge.path o).symm t` (cases on `o.dir`; for
  `o = ⟨e,true⟩` it is `rw [neg_mk_false, path_mk_true, path_mk_false]` and reflexivity; for
  `o = ⟨e,false⟩` the goal becomes `fwdPath e t = ((fwdPath e).symm).symm t`, which needs
  `Path.symm_symm` applied *pointwise* -- `rw [Path.symm_symm]` on the coerced application did not
  fire; prove a helper `γ.symm.symm t = γ t` first, e.g. by `rw [← DFunLike.coe_fn_eq]`/`congrArg`
  on `Path.symm_symm`), and then `proj '' starSet W = halfStar W.endOf`.
  WATCH OUT: `starSet (C := C) W` in a *new* lemma statement produced
  "Invalid argument name `C` for function" even though the same form is used elsewhere in the file;
  using the explicit arguments of `starSet`/`halfStar` (or restating with the section variables)
  should avoid it.
* NEXT: `proj '' starSet W = halfStar W.endOf`.  For `⊆`: `proj (ept W hW t) =
  (OEdge.path (W.lastLetter hW)).symm t = OEdge.path ((W.lastLetter hW).neg) t` for `t < 1/2`
  (witness `(lastLetter W).neg`, whose source is `endOf W`), and `proj (ept W' hW' t) =
  (OEdge.path (W'.lastLetter hW')).symm t = OEdge.path (lastLetter W') (1-t)` for
  `W'.dropLast = W`, `t > 1/2` (witness `lastLetter W'`, whose source is `endOf W = endOf W'.dropLast`).
  For `⊇`: given `o` with `o.src = W.endOf` and `t < 1/2`, use the parent leg `ept W hW t` when
  `o = (lastLetter W).neg`, and otherwise the child leg `ept (W ++ [o]) _ (1-t)` (note `W ++ [o]` is
  reduced exactly when `o ≠ (lastLetter W).neg`).
* **IN PROGRESS (session 14, third batch): `Set.InjOn proj (starSet W)`.**  The geometric
  helpers are DONE and verified: `segF_injective`, `fwdPath_injOn`, `fwdPath_symm_injOn`,
  `path_injOn` (the characteristic path of an oriented edge is injective on the open interval),
  `proj_ept_mem_openCell` (an interior point of a tree edge projects into the open cell of that
  edge), and `eq_or_eq_neg_of_cell_eq` (two oriented edges with the same cell are equal or inverse).
  DONE (after the helpers): `path_apply_eq : (o' = o ∧ u = v) ∨ (o' = o.neg ∧ u = σ v)` for
  `OEdge.path o u = OEdge.path o' v` with `u, v` in the open interval (same cell by disjointness of
  open cells, then `path_injOn`; `path_neg_apply` for the inverse case).  This turns every case
  below into "read off the two alternatives and contradict or conclude by the size of the
  parameters".
  ONE MISSING INGREDIENT for the mixed parent/child sub-cases with the *second* alternative
  (`o'' = o'.neg`): one needs that a reduced walk does not extend by the inverse of its last
  letter, i.e. for `W'.dropLast = W` (both nonempty),
  `W'.lastLetter hW' ≠ (W.lastLetter hW).neg`.  Proof: decompose
  `W'.1 = W'.1.dropLast ++ [W'.1.getLast hW']` (`List.dropLast_append_getLast`), rewrite
  `W'.1.dropLast = W.1` (from `hd` via `congrArg` and `RWalk.dropLast_val`) and read off the
  constraint `Reduced` at index `W.1.length - 1`, using
  `(l ++ [o])[l.length] = o` and `(l ++ [o])[l.length - 1] = l.getLast _`.
  REMAINING CASE ANALYSIS, fully worked out (write it as `ept_injOn_starSet` for the
  interior/interior case, then `injOn_proj_starSet` for the rest):
  - Unfold the memberships with `simp only [starSet, Set.mem_union, Set.mem_setOf_eq]` (mind the
    left-nesting).
  - Vertex cases: the only "vertex-shaped" point of `starSet W` is `vertex W`
    (`ept W hW 0 = vertex W`, `ept W' hW' 1 = vertex W'.dropLast = vertex W` for
    `W'.dropLast = W`).  If `x = vertex W` and `y = ept W hW t` with `t < 1/2`: for `t = 0` the
    two points coincide; for `0 < t` the projection `(path o).symm t = path o (σ t)` lies in
    `openCell 1 o.cell` (`OEdge.path_mem_openCell`, `σ t ∈ (0,1)`) while `vpt (W.endOf)` is a
    vertex, contradicting `vpt_not_mem_openCell_one`.  Symmetrically for
    `y = ept W' hW' t`, `W'.dropLast = W`, `t > 1/2` (the case `t = 1` gives the vertex again).
  - Interior/interior: use `ept_mem_starSet_iff` on both points to get
    `(W' = W ∧ t < 1/2) ∨ (W'.dropLast = W ∧ 1/2 < t)`.  Write `o' = W'.lastLetter hW'`,
    `o'' = W''.lastLetter hW''`, use `proj_ept` and `path_injOn` (on `σ t, σ s ∈ (0,1)`):
    * both in the "parent" position: `W' = W = W''` and `path o' (σ t) = path o' (σ s)` gives
      `t = s`, hence `ept_congr`;
    * both in the "child" position: `o'.cell = o''.cell` (disjointness of open cells), then
      `eq_or_eq_neg_of_cell_eq`: if `o'' = o'` one gets `σ t = σ s` hence `t = s` and then
      `W' = W''` (decompose `W'.1 = W'.1.dropLast ++ [W'.1.getLast _]` using
      `W'.dropLast = W = W''.dropLast` and `lastLetter` agreement); if `o'' = o'.neg` the equality
      becomes `path o' (σ t) = path o' s`, impossible since `σ t < 1/2 < s`;
    * one parent, one child: the same computation gives `σ t = s` with `σ t < 1/2 < s` (or
      `σ s = t`), a contradiction.  (`path_neg_apply` is what converts `path o.neg` into
      `(path o).symm` here.)
The first version of the plan (step 1) was:
* `halfStar (v : cell C 0) : Set Y := {vpt v} ∪ ⋃ (e : cell C 1),
  ((⋃ (_ : map 1 e (fun _ => (-1:ℝ)) = vpt v), map 1 e '' (closedBall 0 1 ∩ {x | x 0 < 0})) ∪
   (⋃ (_ : map 1 e (fun _ => (1:ℝ))  = vpt v), map 1 e '' (closedBall 0 1 ∩ {x | 0 < x 0})))`
  (equivalently `{vpt v} ∪ ⋃ (o : OEdge) (_ : o.src = v), OEdge.path o '' {t | (t:ℝ) < 1/2}`).
  KEY: `map 1 e (-1) = vpt (srcIdx e)` and `map 1 e 1 = vpt (tgtIdx e)` (both already in the file),
  so the two formulations agree; use the `closedBall ∩ {x 0 < 0}` form for openness.
  * `isOpen_halfStar`: prove via `isClosed_compl_iff` +
    `Topology.CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell`, taking the
    `right` branch for every cell.  For a 1-cell `j` the intersection
    `(halfStar v)ᶜ ∩ closedCell 1 j` equals `map 1 j '' K_j` where
    `K_j := closedBall 0 1 ∩ ({x | 0 ≤ x 0} if srcIdx j = v else univ) ∩
           ({x | x 0 ≤ 0} if tgtIdx j = v else univ)`;
    `K_j` is closed and bounded (hence compact), so `map 1 j '' K_j` is compact and closed (T2).
    The set identity uses only `x ∈ S → map 1 j x ∈ map 1 j '' S` for `⊆` and
    `RelCWComplex.injOn_map_ball` + `cellFrontier ∩ openCell = ∅` for `⊇`.
  * `isOpen_epsStar` (same proof with the closedBall cut at arbitrary `c`, needed for the
    continuity of the inverse of `proj` on a sheet).
* `proj '' starSet W = halfStar (W.endOf)` for `W.endOf = v`, and `InjOn proj (starSet W)`:
  both from `proj_vertex` (`proj (vertex W) = vpt W.endOf`), `proj_ept`
  (`proj (ept W hW t) = (OEdge.path (W.lastLetter hW)).symm t`, whose right-hand side is at
  distance `t` from `vpt (tgt (lastLetter W))` and `1 - t` from `vpt (src ...)`) and
  `OEdge.path ⟨e,false⟩ = (OEdge.path ⟨e,true⟩).symm`.
* sheets: `p⁻¹ (halfStar v) = ⋃ (W : RWalk u) (_ : W.endOf = v), starSet W`, pairwise disjoint;
  the "sheet index" of `x` is the unique `W` with `x ∈ starSet W` and it is *locally constant*
  (on the open `starSet W`), hence continuous.
* `IsEvenlyCovered proj (vpt v) (proj ⁻¹' {vpt v})`: the trivialization
  `proj ⁻¹' U ≃ₜ U × (proj ⁻¹' {vpt v})` is `x ↦ (proj x, index x)`; the inverse is continuous
  because on each sheet it is the inverse of `proj`, which is continuous on the interior of every
  edge (use `continuousOn_symm` of the characteristic map + `segF`), and at the vertex use
  `isOpen_epsStar`.  (`Homeomorph.mk`; `continuous_prod_of_discrete` and `Tree.continuous_iff`
  are already available.)
* edge-interior case: for `y ∈ openCell 1 e`, `U := openCell 1 e` is open
  (`openCell` openness: `isClosed_compl_iff` + the same CW criterion; the complement intersects
  `closedCell 1 j` in `closedCell 1 j` (j ≠ e) or `cellFrontier 1 e` (two points) or a singleton),
  the sheets are the open tree edges above `W'` with `(lastLetter W').cell = e`
  (`{ept W' hW' t | (t:ℝ) ∈ (0,1)}`, open by `isOpen_iff`), each mapping homeomorphically onto
  `openCell 1 e` via `proj_ept` and `RelCWComplex.continuousOn_symm`.
* **BETTER ROUTE, DISCOVERED AT THE END OF THE SESSION (prefer this one):** instead of building
  `IsEvenlyCovered` by hand, exhibit the covering map as a *quotient covering map*.  Mathlib has
  `IsQuotientCoveringMap.isCoveringMap` and `IsQuotientCoveringMap.fundamentalGroupEquiv`
  (`Mathlib/Topology/Covering/Quotient.lean`), so it suffices to let `G := End (of u)` in
  `Quiver.FreeGroupoid Q` act on the tree by "prepend and reduce" (`g • x` = the point obtained by
  following `g` before the walk of `x`, reducing at the junction; define it on `TreePt` and check
  it respects `treeRel`), and to prove `IsQuotientCoveringMap proj G`, i.e.
  (a) `IsQuotientMap proj`: continuity of `proj` is `Tree.continuous_proj` and the *slice*
      direction (preimage open ⟹ open) is the hard one (it is the CW-criterion/arc argument below);
      surjectivity of `proj` additionally needs every point of `Y` to be reachable, i.e. the graph
      has to be connected (from `PreconnectedSpace Y`, which follows from `ConnectedSpace X` and
      the homotopy equivalence via dense range + preconnected closure);
  (b) `ContinuousConstSMul G (Tree u)`: on `TreePt` the action is `(W', t) ↦ (reduce (g ++ W'), t)`
      (with the parameter shifted when the reduction eats into the edge), which is continuous
      because `RWalk` is discrete and `Tree.ept` is continuous in the parameter
      (`Tree.continuous_iff`, `Tree.isOpen_iff`);
  (c) `apply_eq_iff_mem_orbit` (fibres = orbits): for `p x = p y` one shows `y = g • x` with
      `g := reduce (W'' ++ reverse W')` (a closed walk at `u`); needs the standard reduction lemmas
      (`reduce (reduce L) = reduce L`, `reduce (A ++ B) = reduce (reduce A ++ reduce B)`,
      `reduce (reverse W ++ W) = nil`, and `reduce (L ++ W) = W → reduce L = nil` for reduced `W`);
  (d) `disjoint e`: take for `U` the star of the nearest vertex (`starSet`), using
      `g • starSet W = starSet (g • vertex W)` and `ept_mem_starSet_iff` (stars of distinct
      vertices are disjoint) plus freeness of the action (the lemma in (c)).
  Then `π₁(Y, vpt u) ≃* Gᵐᵒᵖ` and `G` is free (`IsFreeGroupoid.endIsFreeOfConnectedFree`), and
  `IsFreeGroup` of `Gᵐᵒᵖ` follows by `IsFreeGroup.ofMulEquiv` (`MulOpposite.opEquiv`).
  This route needs NO `IsEvenlyCovered`/trivialization work at all.
* (alternative, longer route) `IsCoveringMap proj := fun y => ...` by the two cases (`h2` shows every point is in a 0- or
  1-dimensional open cell via `iUnion_openCell_eq_complex`).
* THEN: `Tree` contractible ⟹ `SimplyConnectedSpace (Tree u)`, `PathConnectedSpace`.
  Use `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` (+ `SimplyConnectedSpace.paths_homotopic`)
  to prove: for vertices `u v : cell 0`, the map
  `{W : RWalk u // W.endOf = v} → Path.Homotopic.Quotient (vpt u) (vpt v)`, `W ↦ [proj ∘ walkPath W]`
  is a bijection (injective: lift both `walkPath W`, `walkPath W'` from `vertex nil`;
  surjective: lift any path from `vertex nil` and use `exists_vertex_of_proj_eq` — both already in
  the file).  With `Quiver.FreeGroupoid` on the quiver `Q` (`objects = cell 0`,
  `arrows u v := {e : cell 1 // srcIdx e = u ∧ tgtIdx e = v}`) this gives
  `End (of u) ≃* FundamentalGroup Y (vpt u)`.
* `IsFreeGroup (End (of u))`: `Quiver.FreeGroupoid.lift`/`lift_spec`/`lift_unique` upgrade to
  `IsFreeGroupoid` (see the colleague's `Submission/Work/Topology/Surface/planarDomain_...`);
  `IsFreeGroupoid.endIsFreeOfConnectedFree` needs `IsConnected (Quiver.FreeGroupoid Q)`, which
  follows from the connectivity of the graph, which follows from `PreconnectedSpace Y`
  (`HomotopyEquiv` gives a dense range, a preconnected dense subset forces preconnectedness).
  `Nonempty (cell 0)` is needed: if `cell 0` were empty then `cell 1` is empty
  (`CWComplex.exists_cellFrontier_one_eq`) and then `Y = ∅`.
* Finally transfer: `IsFreeGroup (FundamentalGroup Y y')` for arbitrary `y'` by joining `y'` to a
  vertex (every point lies in an open cell) and conjugating by that path; then
  `Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv` + `IsFreeGroup.ofMulEquiv`.
-/

/-! ## SESSION 15 — MASTER PLAN (final architecture) and STATUS

DONE since the last log (all verified, complete):
* `reduced_snoc_ne_neg`, `RWalk.lastLetter_ne_neg` (a reduced walk does not extend by the inverse
  of its last letter) — the missing ingredient flagged in the previous session.
* `RWalk.lastLetter_congr`, `eq_of_vertex_mem_starSet`, `eq_vertex_of_proj_eq`,
  `exists_ept_of_mem_starSet_ne_vertex`, **`ept_injOn_starSet`**, **`injOn_proj_starSet`**
  (`Set.InjOn proj (starSet W)`): the sheet-injectivity is COMPLETE.
  Proof structure of `ept_injOn_starSet` (worth reusing): from `ept_mem_starSet_iff` the point is
  either a "parent" leg (`W' = W`, `t < 1/2`) or a "child" leg (`W'.dropLast = W`, `t > 1/2`);
  projecting (`proj_ept`, `Path.symm_apply`) turns the hypothesis into
  `OEdge.path o' (σ t) = OEdge.path o'' (σ s)` with both parameters in `(0,1)`, to which
  `path_apply_eq` applies: alternative 1 (`o'' = o'`, `σ t = σ s`) gives `t = s` and then the
  walks agree (parent/parent trivially; child/child via `List.dropLast_append_getLast`);
  alternative 2 (`o'' = o'.neg`) is killed by `linarith` on the parameter sizes (same-kind cases)
  or by `RWalk.lastLetter_ne_neg` (mixed parent/child).

* DONE (SESSION 16).  Steps (1) and (2) of the master plan are COMPLETE:
  `epsRad`, `starPt`, `exists_radii_starPt` (radii for the star), `mem_epsStar_of_path`,
  `proj_mem_epsStar_of_mem_starPt`, `exists_mem_starPt_of_mem_epsStar`, `exists_radius_zero/one`,
  `exists_eps_of_isOpen_mem`, `norm_fin_one`, `OEdge.path_symm_apply_mk`,
  `isOpen_openCell_one` (open cells of a 1-dimensional CW complex are open),
  `isOpen_image_map_of_isOpen` (image of an open subset of the ball under the characteristic map),
  **`isOpenMap_proj`** (the crux), `edgeInt` + `isOpen_edgeInt` + `proj_image_edgeInt` +
  `injOn_proj_edgeInt` + `edgeInt_disjoint` + `discreteTopology_subtype`,
  **`isEvenlyCovered_vertex`**, **`isEvenlyCovered_of_mem_openCell`**, **`isCoveringMap_proj`**
  (the empty-fibre case uses `IsOpenMap.isOpen_range` and the fact that the range of `proj` is
  detected by `halfStar`/`openCell`: that argument is inside `isCoveringMap_proj`).
  KEY LEAN PITFALLS (resolved, do not relearn): `Set.isOpen_iff`-style `rw` on `ᶜ` can fail
  ("motive is not type correct") because of dependent coercions -- transport the *set*
  (`congrArg (fun v => epsStar v δt δf) h`) instead of the point; `rw [hL]` under `OEdge.path`
  then `path_mk_false` breaks on the outer `.symm` -- use `OEdge.path_symm_apply_mk` after
  `rw [proj_ept, hL]`; `Sigma.mk.inj` needs its type fully determined (state the `Σ`-inequality
  as a `have` with an explicit type); `List.getLast_congr (h₁) (h₂) rfl` compares two proofs;
  `IsOpen.trivializationDiscrete` is at the ROOT namespace (not `Topology.`), as are `IsCoveringMap`,
  `IsEvenlyCovered`, and its `baseSet` is exposed by `IsOpen.trivializationDiscrete_baseSet`.
  Use `haveI : DiscreteTopology ι := discreteTopology_subtype _` for the sheet indexing type.

REMAINING (steps 3, 4, 5 of the master plan).  Suggested architecture for step 3+4 (session 17):
  * `enc : OEdge C → cell C 1 × Bool`, `dec`, `redL : List (OEdge C) → List (OEdge C)`
    (`l.foldr` cancelling `x` against the head of the accumulator when `x.cell = y.cell ∧
    x.dir = !y.dir`), `wordList l := FreeGroup.mk (l.map enc)` with
    `FreeGroup.mul_mk`/`List.map_append` giving `wordList (l₁++l₂) = wordList l₁ * wordList l₂`.
  * `redL` preserves `IsWalk`/`endOfList` (induction using `redL_cons`) and produces `Reduced`;
    `wordList (redL l) = wordList l` (each cancelled pair is `w * w⁻¹ = 1`).
  * `wordList` is injective on `Reduced` lists (`FreeGroup.reduce.sound` +
    `FreeGroup.IsReduced.red_iff_eq`; `Reduced l ↔ FreeGroup.IsReduced (l.map enc)`).
  * `Lcw u := {W : RWalk C u // W.endOf = u}` with `W ⊙ W' := redL (W.1 ++ W'.1)`;
    ALL group axioms transfer along the injective `wordList : Lcw u →* FreeGroup (cell C 1)`
    (multiplicativity from `wordList_redL` + `wordList_append`), so no associativity proof is
    needed by hand.  Then `IsFreeGroup (Lcw u)` follows from
    `IsFreeGroup.ofMulEquiv (h : Hsub ≃* Lcw u)` where `Hsub := (wordList).range` and
    `subgroupIsFreeOfIsFree Hsub` (`Mathlib/GroupTheory/FreeGroup/NielsenSchreier.lean`).
  * Step 4: `Ψ : Lcw u →* FundamentalGroup Y (vpt u)`, `W ↦ ⟦proj ∘ walkPath W⟧`; bijective via
    `IsCoveringMap.liftPath`/`liftPath_apply_one_eq_of_homotopicRel` + `contractibleSpace` of
    `Tree u` + `exists_vertex_of_proj_eq` + `vertex_injective`.  For multiplicativity, compare the
    endpoints of the lifts from `vertex nil` (both sides are loops at `vpt u` and `Tree u` is
    simply connected); the RHS needs the "translation" of `walkPath W'` by `W`
    (`transWalk W Z := (transWalk W Z.dropLast).trans (edgePath (W ⊙ Z)).symm`), whose projection
    is `proj ∘ walkPath Z` up to homotopy and whose endpoint is `vertex (W ⊙ Z)`.
  * Step 5: transfer `IsFreeGroup` from `π₁(Y, y₀)` to `π₁(X, x)` using
    `Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv`.

* DONE (SESSION 17, step (3), partial).  The reduction/word machinery is COMPLETE and green:
  `enc`/`dec`/`redL` (+ `redL_cons`), `wordList` (+ `wordList_append`/`_nil`/`_cons`/`_neg_apply`/
  `_neg_pair`), **`wordList_redL`** (`wordList (redL l) = wordList l`), `enc_injective`,
  `enc_imp_iff`, `isReduced_map_enc_iff` (`FreeGroup.IsReduced (l.map enc) ↔ Reduced l`),
  `reduce_map_enc_of_reduced`, **`wordList_injOn`** (injective on reduced lists),
  `lastTgt` (proof-free endpoint) + `endOfList_eq_lastTgt` + `lastTgt_append`,
  `eq_neg_iff`, **`reduced_redL`**, **`isWalk_redL`**, **`lastTgt_redL`**,
  `isWalk_append'`, `Lcw u := {W : RWalk u // W.endOf = u}`, `Lcw.mul` (concat + `redL`),
  `Lcw.word := wordList ∘ W.1.1` with **`Lcw.word_mul`** and **`Lcw.word_injective`**.
  PITFALLS (resolved): `FreeGroup.reduce` needs `[DecidableEq α]` -- wrap with
  `letI := Classical.decEq (cell C 1)` (inside statements too when `reduce` appears there) and put
  `classical` at the start of the proofs of anything calling `rw [redL_cons]`; the free-group
  "head-reduced" lemma is `FreeGroup.isReduced_cons_cons` (lowercase `is`); `FreeGroup.IsReduced`
  has no `cons_cons`; `List.map_injective` does not exist, use `(List.map_injective_iff.mpr h)`.

NEXT (finishing step (3)).  In `Lcw.mul`'s target the goal must be `show`n as
`endOfList u (redL l) (isWalk_redL _ u h) = u` (with `h` a `let`) for `endOfList_eq_lastTgt`
to fire.  Remaining: `Lcw.inv` (reverse the list and negate every letter) with
`lastTgt_reverse_map_neg` (`lastTgt (lastTgt u l) (l.reverse.map OEdge.neg) = u`),
`isWalk_reverse_map_neg` and `reduced_reverse_map_neg` (`Reduced (l.reverse.map OEdge.neg)` --
the last letter of `l.reverse.map OEdge.neg` is `(l.head).neg`, so `Reduced (o :: l)` gives the
needed `o.neg ≠ l.head`; the alternative is `FreeGroup.invRev` +
`List.isChain_reverse`); then `Lcw.one := ⟨RWalk.nil u, rfl⟩`, `Lcw.word_one`,
`Lcw.word_inv`, and the `Group (Lcw u)` instance via `Group.ofLeftAxioms` with every axiom proved
by `Lcw.word_injective` + the corresponding free-group axiom (`Mathlib/Algebra/Group/MinimalAxioms.lean`).
Finally `IsFreeGroup (Lcw u)`: `Hsub := (Lcw.word).range` is a `Subgroup (FreeGroup (cell C 1))`,
free by `subgroupIsFreeOfIsFree Hsub`, and `Lcw u ≃* Hsub` via `word`;
`IsFreeGroup.ofMulEquiv (e : Hsub ≃* Lcw u)`.

REMAINING WORK (the whole architecture; nothing here needs a spanning tree or Zorn):

(1) **`IsOpenMap (Tree.proj)`.**  (STATUS: the parametrisation identities are DONE:
    `fwdPath_image_lt`, `fwdPath_image_gt`, `symm_image_lt`, `fwdPath_symm_image_lt` — general cut
    `c` versions of the four half-cut identities.  NEXT: `mem_epsStar_of_lt` / `not_mem_epsStar`
    and the main openness lemma for the set
    `epsStar v δt δf := {vpt v} ∪ ⋃ (e : cell C 1) (_ : srcIdx e = v), fwdPath e '' {t | t < δt e}
      ∪ ⋃ (e : cell C 1) (_ : tgtIdx e = v), (fwdPath e).symm '' {t | t < δf e}`,
    proved by copying `isOpen_halfStar` with `K_j := closedBall ∩ (if srcIdx j = v then
    {y | 2 * δt j - 1 ≤ y 0} else univ) ∩ (if tgtIdx j = v then {y | 2 * δf j - 1 ≤ -(y 0)} else univ)`;
    then transport to the `OEdge`-indexed form used by `halfStar`/`starSet`.)

**DONE (this stretch): the eps-star openness lemma.**  `epsStar` (line 2041), `mem_epsStar_of_lt`
(2049), `eq_of_vpt_mem_epsStar` (2073), `not_mem_epsStar` (2104), **`isOpen_epsStar` (2196)**:
`epsStar v δt δf` is open provided all radii are `< 1/2`, the radii are positive in the incident
orientations (`srcIdx e = v → 0 < δt e`, `tgtIdx e = v → 0 < δf e`) and there are no cells in
dimension `≥ 2`.  Auxiliary: `fwdPath_image_lt`, `fwdPath_image_gt`, `symm_image_lt`,
`fwdPath_symm_image_lt` and `fwdPath_symm_image_lt'` (the `-(y 0)`-form of the cut, which matches
the condition proved by `not_mem_epsStar` syntactically), plus `fwdPath_image_right_vertex`.
Proof shape: the CW criterion with `A := (epsStar)ᶜ` and
`K_j := closedBall ∩ (if srcIdx j = v then {y | 2 * δt j - 1 ≤ y 0} else univ)
  ∩ (if tgtIdx j = v then {y | 2 * δf j - 1 ≤ -(y 0)} else univ)`,
`(epsStar)ᶜ ∩ closedCell 1 j = map 1 j '' K_j`, compact image.
Lean pitfalls (all resolved): use `not_le.mpr h` (not `by linarith`) to prove the negation
`¬ (2 * δ - 1 ≤ x 0)` from `h : x 0 < 2 * δ - 1`; take the `-(y 0)` form of the
`fwdPath_symm_image_lt` identity to avoid a failing `linarith` under the coercion `↑(δf j)`.

**NEXT (the rest of step (1), then step (2)).**
(a) The tree-star gadget: for `W : RWalk u` and radii `δ` on `{o : OEdge // o.src = W.endOf}`,
    `starPt W δ := {vertex W} ∪ ⋃ o, ({x | x = ept W hW t, (t:ℝ) < δ o, o = (lastLetter W).neg}
      ∪ {x | x = ept W' hW' t, W'.dropLast = W, lastLetter W' = o, 1 - δ o < t})`,
    with `proj '' starPt W δ = (the OEdge-indexed form of epsStar at W.endOf)` (both inclusions as in
    `proj_image_starSet` / `exists_mem_starSet_of_mem_halfStar`).  `starPt` is open in the tree: its
    slices along the incident edges are `[0, δ)` resp. `(1-δ, 1]` (open in `I`) and empty otherwise
    (`Tree.isOpen_iff`).
(b) `IsOpenMap (proj)`: for `U ⊆ Tree u` open and `x ∈ U`, exhibit a neighbourhood `N ⊆ U` of `x`
    with `proj N` a neighbourhood of `proj x`:
    * `x = ept W' hW' t` with `0 < t < 1`: take an interval in the edge above `W'`; its image is an
      open subset of `openCell 1 (lastLetter W').cell` (use `OEdge.path_mem_openCell` and the
      homeomorphism `(path o) : I ≅ closedCell 1 o.cell`), hence open in `Y`.
    * `x = vertex W`: by `Tree.isOpen_iff` the slice of `U` along each incident edge is an open set
      containing the endpoint, hence contains `[0, δ)` (parent) / `(1-δ, 1]` (children) for some
      `δ > 0`; then `proj (starPt W δ) = epsStar (W.endOf) ...` is contained in `proj U` and is open
      by `isOpen_epsStar` (positivity of the radii is exactly the openness of the slices).
    Consequences: `IsOpenMap proj`, `IsQuotientMap proj` (with surjectivity) and the "openness
    determined by preimages" hypothesis of `IsOpen.trivializationDiscrete` in step (2).

**Attempt log (session 15, last stretch).**  A first version of the eps-star block was written
and mostly elaborated, but was reverted (it did not compile).  Pitfalls found, to avoid next
time: (i) `segF_eq_endpoints_of_mem_sphere` gives *equations of unit intervals*
(`(t:ℝ) = 0 ∨ (t:ℝ) = 1`), so in `fwdPath_image_right_vertex` the case `= 0` must be closed by
`exfalso; linarith [ht, h0]` (the goal there is `(t:ℝ) = 1`); (ii) `Set.image_mono` needs explicit
`Set` arguments -- better to destruct the membership with `obtain ⟨t, ht, htx⟩ := h` and rebuild
it; (iii) the file's own lemma is `RelCWComplex.injOn_map_ball` (NOT under `Topology.`);
(iv) never `subst` an equation `e = j` inside `not_mem_epsStar` (it eliminated the wrong variable):
use `rw [hej] at hy hyx` and prove `srcIdx j = v` by `rw [← hej]; exact he`;
(v) `rw [fwdPath_image_lt]` inside a goal of the form `map 1 j x ∈ fwdPath j '' {...}` may shadow
the point `x` with the set-builder variable: state the intersections with an explicit variable
name (e.g. `{y : Fin 1 → ℝ | y 0 < ...}`) and use `show` to pin the subgoal before `linarith`.

(1') **`IsOpenMap (Tree.proj)`.**  THE CRUX of everything topological.  Route: the CW criterion
    `Topology.CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell` (per cell, with
    `n > 0` only, so `n = 1` is the only case since `n ≥ 2` is `IsEmpty`), applied to
    `A := (proj '' U)ᶜ`: it suffices to prove, for every `1`-cell `j`,
    `IsClosed (A ∩ closedCell 1 j)`, i.e. that `proj U ∩ closedCell 1 j` is open in the closed
    cell.  `closedCell 1 j = map 1 j '' closedBall` and `map 1 j` is a homeomorphism on the closed
    ball, so it is enough that
      `{s : I | path ⟨j,true⟩ s ∈ proj U}` is open in `I`  (then use `segF : I ≅ closedBall`).
    For a tree point `z ∈ U` write either `z = ept W'' hW'' t` (`0 < t < 1`) or `z = vertex W''`.
    * interior case: `proj z ∈ openCell 1 (lastLetter W'').cell`; if this meets `closedCell 1 j`
      then `(lastLetter W'').cell = j`, and `z`'s parameter lies in the slice
      `S_{W''} = {t | ept W'' hW'' t ∈ U}` (open in `I` by `Tree.isOpen_iff`); the piece
      `(path (lastLetter W''))⁻¹ '' S_{W''}` is therefore open in `closedCell 1 j` (the
      characteristic path is a homeomorphism `I ≅ closedCell`).
    * vertex case `z = vertex W''`: `W''.endOf ∈ {srcIdx j, tgtIdx j}`; take the OEdge `o` with
      `o.cell = j` and `o.src = W''.endOf`; if `W'' ++ [o]` is reduced put `W' := W'' ++ [o]`,
      otherwise (`o = (lastLetter W'').neg`) put `W' := W''` (if `W'' = []` use `W' := [o]`).
      Then the point `proj z` is the parameter `0`/`1` end of the edge above `W'`, whose parameter
      lies in `S_{W'}`, so `proj z` is an interior point of a piece that is open in the closed
      cell; this is the "honest" replacement of the abandoned `isOpen_epsStar` route — the
      per-cell description never needs compactness, only the nesting of the pieces.
    NOTE: the pieces for all the tree edges with the same cell and the same side are "nested at the
    same end" of the cell, so their union is again a piece and the complement inside the closed
    cell is a closed interval.  The statements needed about the cells/OEdges are all available
    (`srcIdx`, `tgtIdx`, `map_one_neg_one_eq_srcIdx`, `map_one_one_eq_tgtIdx`, `path_mk_true/false`,
    `injOn_map_ball`, `continuousOn`).

(2) **The sheets and `IsCoveringMap (Tree.proj)`.**
    * vertex case: `U := halfStar v` (`isOpen_halfStar`), sheets `starSet W` for `W.endOf = v`
      (`isOpen_starSet`, injective by `injOn_proj_starSet`, onto `U` by `proj_image_starSet`).
      Still to prove: (a) `proj ⁻¹' (halfStar v) ⊆ ⋃_{W.endOf = v} starSet W` (a point whose
      projection is in the half-star is `vertex W` or an interior point `ept W'' hW'' t`; in the
      second case `proj` of it equals `(path (lastLetter W'')).symm t = path (lastLetter W''.neg) t`
      so `path_apply_eq` against the OEdge of the half-star gives either a contradiction or
      `(lastLetter W'').cell = ...` with `W''.endOf = v` and `t < 1/2`); (b) the `starSet W` are
      pairwise disjoint (same case analysis with `ept_mem_starSet_iff` and `eq_of_vrt_mem_starSet`);
      (c) `DiscreteTopology (proj ⁻¹' {vpt v})` (the fibre is exactly `{vertex W | W.endOf = v}` by
      `exists_vertex_of_proj_eq`, and `starSet W ∩ proj ⁻¹' {vpt v} = {vertex W}`);
      (d) assembling `IsEvenlyCovered` with `IsOpen.trivializationDiscrete` (all its hypotheses are
      then available: openness of the `starSet` and of `halfStar`, injectivity, surjectivity, and the
      "openness determined by preimages" condition, whose `⇐` direction is `W = proj (proj⁻¹ W ∩ S)`
      plus `IsOpenMap proj` from (1)).
    * edge-interior case: `U := openCell 1 e`; the sheets are the interiors of the tree edges above
      the walks with `(lastLetter W').cell = e`, each mapping homeomorphically onto `U` via
      `(path (lastLetter W'))⁻¹` (`injOn_map_ball`, `continuousOn_symm`).

(3) **`L` is free.**  `L :=` the closed reduced walks at `u`, with `W ⊙ W' := reduce (W.1 ++ W'.1)`.
    Define `reduce : List OEdge → List OEdge` as the *decode* of Mathlib's `FreeGroup.reduce` on
    `l.map (fun o => (o.cell, o.dir))` (so ALL the reduction lemmas are Mathlib's:
    `FreeGroup.reduce.idem`, `FreeGroup.reduce_append_reduce_reduce`, `FreeGroup.toWord_mk`,
    `FreeGroup.IsReduced.reduce_eq`, `FreeGroup.toWord_eq_nil_iff`, ...), and the injective monoid
    hom `word : L → FreeGroup (cell C 1)` sending a walk to the product of the generators
    `FreeGroup.of o.cell` with sign `o.dir`.  Then `word (W ⊙ W') = word W * word W'` follows from
    `FreeGroup.mk` being multiplicative on lists, `word`'s image `G` is a subgroup of a free group,
    and `IsFreeGroup G` is Mathlib's `IsFreeGroupoid.subgroupIsFreeOfIsFree` instance; transport to
    `L` (and then to `π₁`) along the resulting `MulEquiv`.

(4) **`π₁ (Y, vpt u) ≅ L`.**  `Ψ : L →* FundamentalGroup Y (vpt u)` sends `W` to the class of the
    realisation `Walk.pathOf ⟨W.1, W.2.1⟩`; it is multiplicative because cancelling a backtracking
    pair is a groupoid identity (`mk γ ≫ mk γ⁻¹ = 1` in `FundamentalGroupoid Y`) and concatenation
    of walks is composition of paths.  Bijectivity:
    * surjective: lift a loop `γ` from `x₀ = vertex (RWalk.nil u)`; by `exists_vertex_of_proj_eq`
      it ends at `vertex W`; `walkPath W` is another path in the contractible tree between the same
      two points, so `γ` is homotopic to the projection of `walkPath W`;
    * injective: if `Ψ W = 1` the lift of the realisation from `x₀` is closed
      (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`); the lift is `walkPath W` (unique
      lifting, using the projection computation of `walkPath`), whose endpoint is `vertex W`; hence
      `vertex W = vertex (RWalk.nil u)` and `vertex_injective` gives `W = RWalk.nil u`.
    This needs the projection of `walkPath`: define the *end-recursive* realisation
    `RWalk.realizeAux` (same recursion as `walkPathAux`) and prove
    `proj (walkPathAux n W h t) = realizeAux n W h t` by induction (the log below has the details),
    plus `(RWalk.realize W).Homotopic (Walk.pathOf ⟨W.1, W.2.1⟩)`.

(5) **Transfer.**  `IsFreeGroup (FundamentalGroup Y y)` for an arbitrary `y : Y` by joining `y` to a
    vertex (every point lies in an open cell; `Y` is path connected), then
    `Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv` and
    `IsFreeGroup.ofMulEquiv` for `π₁ (X, x)`.
-/

namespace Commons.AlgebraicTopology.FundamentalGroup

noncomputable section

/-- **The fundamental group of a connected space homotopy equivalent to a one-dimensional CW
complex is free.** -/
theorem freeGroup_of_oneDimCWComplex
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] (x : X)
    (h : ∃ (Y : Type*) (tY : TopologicalSpace Y) (_ : @T2Space Y tY)
        (hY : @Topology.CWComplex Y tY Set.univ),
        (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell Y tY Set.univ hY n)) ∧
        Nonempty (@ContinuousMap.HomotopyEquiv X Y _ tY)) :
    IsFreeGroup (FundamentalGroup X x) := by
  classical
  obtain ⟨Y, tY, hT2, hY, h2, he⟩ := h
  obtain ⟨e⟩ := he
  letI : TopologicalSpace Y := tY
  haveI : T2Space Y := hT2
  letI : Topology.CWComplex (Set.univ : Set Y) := hY
  haveI : IsFreeGroup (FundamentalGroup Y (e.toFun x)) := by
    obtain ⟨u, hp⟩ := CWGraph.exists_path_to_vertex (X := Y) h2 (e.toFun x)
    haveI : IsFreeGroup (FundamentalGroup Y (CWGraph.vpt (C := Set.univ) u)) :=
      CWGraph.Tree.isFreeGroup_vertex h2 u
    exact IsFreeGroup.ofMulEquiv
      (FundamentalGroup.fundamentalGroupMulEquivOfPath hp.some).symm
  obtain ⟨ee⟩ := pi1_equiv_of_homotopyEquiv e x
  exact IsFreeGroup.ofMulEquiv ee.symm

end