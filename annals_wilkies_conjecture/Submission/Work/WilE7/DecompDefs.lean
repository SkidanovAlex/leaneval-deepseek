/-
  Area E7, WilE7: vocabulary and elementary lemmas for the "sections cut the
  cylinder into graphs and bands" decomposition (`Work.WilE7.decomp_of_sections`).

  Given a cell `C ⊆ ℝ^n` and `q` continuous functions `s j : C → ℝ` that are, at
  every point of `C`, strictly increasing in `j` and valued in `(-1,1)`, the
  cylinder `{z : ℝ^{n+1} | init z ∈ C, |last z| ≤ 1}` is cut into the `q+2`
  graphs of the levels `-1, s 0, …, s (q-1), 1` and the `q+1` open bands between
  consecutive levels.

  This file contains the basic vocabulary (`lvl`, `gr`, `bd`, `gcs`, `bcs`,
  `cfs`, `cyl`) and the elementary facts about it.
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.cells
import Submission.Work.WilE7.singleton_cylDecomp

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

variable {n q : ℕ}

/-! ## The level function -/

/-- The `q+2` levels `-1, s 0, …, s (q-1), 1`, as a function of the base point. -/
def lvl (s : Fin q → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin (q + 2) → ℝ :=
  Fin.insertNth 0 (-1) (Fin.insertNth (Fin.last q) (1:ℝ) (fun j : Fin q => s j x) : Fin (q+1) → ℝ)

@[simp] theorem lvl_zero (s : Fin q → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : lvl s x 0 = -1 := by
  simp [lvl]

@[simp] theorem lvl_last (s : Fin q → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    lvl s x (Fin.last (q+1)) = 1 := by simp [lvl]

@[simp] theorem lvl_succ (s : Fin q → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (j : Fin q) :
    lvl s x (Fin.succ (Fin.castSucc j)) = s j x := by simp [lvl]

/-- The levels are strictly increasing whenever the `s j` are strictly increasing
and land in `(-1,1)`. -/
theorem strictMono_lvl {s : Fin q → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hmono : StrictMono fun j : Fin q => s j x) (hbnd : ∀ j, |s j x| < 1) :
    StrictMono (lvl s x) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [lvl]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hq)
    have hlt : (fun j : Fin (m+1) => s j x) (Fin.last m) < 1 := by
      have := hbnd (Fin.last m); rw [abs_lt] at this; exact this.2
    set g : Fin (m+2) → ℝ :=
      Fin.insertNth (Fin.last (m+1)) (1:ℝ) (fun j : Fin (m+1) => s j x) with hg
    have h1 : StrictMono g := Fin.strictMono_insertNth_last hmono (1:ℝ) hlt
    have hg0 : g 0 = s 0 x := by
      rw [hg]
      rw [show (0 : Fin (m+2)) = Fin.succAbove (Fin.last (m+1)) (0 : Fin (m+1)) from by simp]
      rw [Fin.insertNth_apply_succAbove]
    have hlt0 : (-1:ℝ) < g 0 := by rw [hg0]; exact (abs_lt.mp (hbnd 0)).1
    have key : StrictMono (Fin.insertNth 0 (-1) g) := Fin.strictMono_insertNth_zero h1 (-1) hlt0
    have hk : lvl s x = Fin.insertNth 0 (-1) g := by rw [hg]; rfl
    rw [hk]; exact key

/-- All levels lie in `[-1,1]`. -/
theorem abs_lvl_le_one {s : Fin q → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hbnd : ∀ j, |s j x| < 1) (i : Fin (q+2)) : |lvl s x i| ≤ 1 := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨i', rfl⟩
  · subst h; simp
  · rcases Fin.eq_castSucc_or_eq_last i' with ⟨j, hj⟩ | hlast
    · subst hj; simpa using le_of_lt (hbnd j)
    · subst hlast; simp

/-- Each level is continuous on `C`. -/
theorem continuous_lvl {C : Set (Fin n → ℝ)} {s : Fin q → (Fin n → ℝ) → ℝ}
    (hs : ∀ j, ContinuousOn (s j) C) (i : Fin (q+2)) :
    ContinuousOn (fun x => lvl s x i) C := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨i', rfl⟩
  · subst h; simpa [lvl] using continuousOn_const (c := (-1:ℝ)) (s := C)
  · rcases Fin.eq_castSucc_or_eq_last i' with ⟨j, hj⟩ | hlast
    · subst hj; simpa [lvl] using hs j
    · subst hlast; simpa [lvl] using continuousOn_const (c := (1:ℝ)) (s := C)

/-! ## The graph and band cells -/

/-- The graph cell over `C` of `f`. -/
def gr (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Set (Fin (n+1) → ℝ) :=
  {z | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)}

/-- The band cell over `C` strictly between `a` and `b`. -/
def bd (C : Set (Fin n → ℝ)) (a b : (Fin n → ℝ) → ℝ) : Set (Fin (n+1) → ℝ) :=
  {z | Fin.init z ∈ C ∧ a (Fin.init z) < z (Fin.last n) ∧ z (Fin.last n) < b (Fin.init z)}

/-- The graph cells of the level family. -/
def gcs (C : Set (Fin n → ℝ)) (s : Fin q → (Fin n → ℝ) → ℝ) : Finset (Set (Fin (n+1) → ℝ)) :=
  Finset.univ.image fun i : Fin (q+2) => gr C (fun x => lvl s x i)

/-- The band cells between consecutive levels. -/
def bcs (C : Set (Fin n → ℝ)) (s : Fin q → (Fin n → ℝ) → ℝ) : Finset (Set (Fin (n+1) → ℝ)) :=
  Finset.univ.image fun i : Fin (q+1) =>
    bd C (fun x => lvl s x (Fin.castSucc i)) (fun x => lvl s x i.succ)

/-- The full cell family. -/
def cfs (C : Set (Fin n → ℝ)) (s : Fin q → (Fin n → ℝ) → ℝ) : Finset (Set (Fin (n+1) → ℝ)) :=
  gcs C s ∪ bcs C s

/-- The cylinder over `C`. -/
def cyl (C : Set (Fin n → ℝ)) : Set (Fin (n+1) → ℝ) :=
  {z | Fin.init z ∈ C ∧ |z (Fin.last n)| ≤ 1}

/-- A graph cell is a cell. -/
theorem isCell_gr {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hC : IsCell n C) (hf : ContinuousOn f C) : IsCell (n+1) (gr C f) :=
  IsCell.graph hC f hf

/-- A band cell with strict boundary functions is a cell. -/
theorem isCell_bd {C : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → ℝ}
    (hC : IsCell n C) (ha : ContinuousOn a C) (hb : ContinuousOn b C)
    (hab : ∀ x ∈ C, a x < b x) : IsCell (n+1) (bd C a b) := by
  rw [show bd C a b = {z : Fin (n+1) → ℝ | Fin.init z ∈ C ∧
      (a (Fin.init z) : EReal) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < (b (Fin.init z) : EReal)} by
    ext z; simp only [bd, Set.mem_ofPred_eq, EReal.coe_lt_coe_iff]]
  exact IsCell.band hC (fun x => (a x : EReal)) (fun x => (b x : EReal))
    (continuous_coe_real_ereal.comp_continuousOn ha)
    (continuous_coe_real_ereal.comp_continuousOn hb)
    (fun x hx => EReal.coe_lt_coe_iff.mpr (hab x hx))

/-! ## Membership in the cell family -/

theorem mem_gcs {C : Set (Fin n → ℝ)} {s : Fin q → (Fin n → ℝ) → ℝ}
    {κ : Set (Fin (n+1) → ℝ)} :
    κ ∈ gcs C s ↔ ∃ i : Fin (q+2), κ = gr C (fun x => lvl s x i) := by
  constructor
  · intro h
    rw [gcs, Finset.mem_image] at h
    obtain ⟨i, -, hi⟩ := h
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    rw [gcs, Finset.mem_image]
    exact ⟨i, Finset.mem_univ i, rfl⟩

theorem mem_bcs {C : Set (Fin n → ℝ)} {s : Fin q → (Fin n → ℝ) → ℝ}
    {κ : Set (Fin (n+1) → ℝ)} :
    κ ∈ bcs C s ↔ ∃ i : Fin (q+1), κ = bd C (fun x => lvl s x (Fin.castSucc i))
      (fun x => lvl s x i.succ) := by
  constructor
  · intro h
    rw [bcs, Finset.mem_image] at h
    obtain ⟨i, -, hi⟩ := h
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    rw [bcs, Finset.mem_image]
    exact ⟨i, Finset.mem_univ i, rfl⟩

theorem mem_cfs {C : Set (Fin n → ℝ)} {s : Fin q → (Fin n → ℝ) → ℝ}
    {κ : Set (Fin (n+1) → ℝ)} :
    κ ∈ cfs C s ↔
      (∃ i : Fin (q+2), κ = gr C (fun x => lvl s x i)) ∨
      (∃ i : Fin (q+1), κ = bd C (fun x => lvl s x (Fin.castSucc i))
        (fun x => lvl s x i.succ)) := by
  rw [cfs, Finset.mem_union, mem_gcs, mem_bcs]

end Work.WilE7
