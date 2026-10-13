import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.Omega_cast
import Submission.Work.WilG0.API
import Submission.Work.WilG0.diagSet_eq
import Submission.Work.WilG0.diagPoly_totalDegree_le

set_option autoImplicit false

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-! ## Helper development for the composition lemma

We prove here the substitution machinery (`Ω` is closed under coordinate pullback) that the
sibling lemma `Work.WilG4c.Subst` states, entirely inside this file, and then assemble the
composition.  The helpers live in the sub-namespace `Work.WilG4c.Comp`. -/

namespace GraphComp

/-! ### 1. Lifting a set to the trailing coordinate block

`liftTail n A j ⊆ ℝ^{n+j}` places `A ⊆ ℝ^n` in the last `n` coordinates, leaving the first
`j` free.  It is the `j`-fold iterate of `SOMin.prod_left`. -/

/-- `A` placed in the trailing `n` coordinates of `ℝ^{n+j}`. -/
def liftTail (n : ℕ) (A : Set (Fin n → ℝ)) : (j : ℕ) → Set (Fin (n + j) → ℝ)
  | 0 => A
  | j + 1 => {z : Fin (n + (j + 1)) → ℝ | Fin.tail z ∈ liftTail n A j}

theorem tail_addNat (n j : ℕ) (z : Fin (n + (j + 1)) → ℝ) :
    (fun i : Fin n => (Fin.tail z) (Fin.addNat i j)) =
      (fun i : Fin n => z (Fin.addNat i (j + 1))) := by
  funext i
  congr 1

theorem liftTail_spec (n j : ℕ) (A : Set (Fin n → ℝ)) :
    liftTail n A j = {z : Fin (n + j) → ℝ | (fun i : Fin n => z (Fin.addNat i j)) ∈ A} := by
  induction j with
  | zero =>
    ext z
    simp [liftTail]
  | succ j ih =>
    ext z
    rw [show liftTail n A (j + 1) =
        {w : Fin (n + (j + 1)) → ℝ | Fin.tail w ∈ liftTail n A j} from rfl]
    rw [ih]
    change (fun i : Fin n => (Fin.tail z) (Fin.addNat i j)) ∈ A ↔
      (fun i : Fin n => z (Fin.addNat i (j + 1))) ∈ A
    rw [tail_addNat]

theorem liftTail_mem (S : SOMin) {n F D : ℕ} {A : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F D n) (j : ℕ) : liftTail n A j ∈ S.Ω (F + j) D (n + j) := by
  induction j with
  | zero => simpa [liftTail] using hA
  | succ j ih => exact S.prod_left ih

theorem mem_liftTail {n j : ℕ} (A : Set (Fin n → ℝ)) (f : Fin (n + j) → ℝ) :
    f ∈ liftTail n A j ↔ (fun i : Fin n => f (Fin.addNat i j)) ∈ A := by
  rw [liftTail_spec]
  exact Iff.rfl

/-- The same lift, but with the ambient dimension written as `N + n`. -/
def liftTailN (N n : ℕ) (A : Set (Fin n → ℝ)) : Set (Fin (N + n) → ℝ) :=
  (Nat.add_comm n N) ▸ liftTail n A N

theorem liftTailN_mem (S : SOMin) {n F D : ℕ} {A : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F D n) (N : ℕ) : liftTailN N n A ∈ S.Ω (F + N) D (N + n) :=
  Omega_cast (Nat.add_comm n N) (liftTail_mem S hA N)

theorem cast_addNat_eq_natAdd {n N : ℕ} (i : Fin n) :
    Fin.cast (Nat.add_comm n N) (Fin.addNat i N) = Fin.natAdd N i := by
  apply Fin.ext
  show i.val + N = N + i.val
  omega

theorem mem_liftTailN {n N : ℕ} (A : Set (Fin n → ℝ)) (z : Fin (N + n) → ℝ) :
    z ∈ liftTailN N n A ↔
      (fun i : Fin n => z (Fin.cast (Nat.add_comm n N) (Fin.addNat i N))) ∈ A := by
  rw [liftTailN, cast_mem_iff]
  exact mem_liftTail A _

theorem snocIt_mem_liftTailN {n N : ℕ} (A : Set (Fin n → ℝ)) (x : Fin N → ℝ)
    (w : Fin n → ℝ) : snocIt N n x w ∈ liftTailN N n A ↔ w ∈ A := by
  have key : (fun i : Fin n => snocIt N n x w
      (Fin.cast (Nat.add_comm n N) (Fin.addNat i N))) = w := by
    funext i
    rw [cast_addNat_eq_natAdd, snocIt_natAdd]
  constructor
  · intro hx
    rw [mem_liftTailN] at hx
    rwa [key] at hx
  · intro hx
    rw [mem_liftTailN, key]
    exact hx

/-! ### 2. The substitution lemma -/

/-- `diagSet` is `Ω`-definable with format `N+n`, the ambient dimension, and degree `2`
(the diagonal polynomial `Σ (w_j - x_{σ j})²`). -/
theorem diagSet_mem (S : SOMin) (N n : ℕ) (σ : Fin n → Fin N) :
    diagSet N n σ ∈ S.Ω (N + n) 2 (N + n) := by
  have h := Omega.hyp_mem (S := S) 0 (diagPoly N n σ)
  rw [← diagSet_eq] at h
  refine Omega.mono h le_rfl ?_
  simpa using diagPoly_totalDegree_le N n σ

/-- Membership of the glued vector in `diagSet`. -/
theorem snocIt_mem_diagSet {n N : ℕ} (σ : Fin n → Fin N) (x : Fin N → ℝ)
    (w : Fin n → ℝ) : snocIt N n x w ∈ diagSet N n σ ↔ x ∘ σ = w := by
  change (∀ j : Fin n, snocIt N n x w (Fin.natAdd N j) =
    snocIt N n x w (Fin.castAdd n (σ j))) ↔ x ∘ σ = w
  constructor
  · intro h
    funext j
    have hj := h j
    rw [snocIt_natAdd, snocIt_castAdd] at hj
    exact hj.symm
  · intro h j
    rw [snocIt_natAdd, snocIt_castAdd]
    have hj := congrFun h j
    simp only [Function.comp_apply] at hj
    exact hj.symm

theorem proj_lift_inter_diag (n N : ℕ) (σ : Fin n → Fin N) (A : Set (Fin n → ℝ)) :
    projLastIter N n (liftTailN N n A ∩ diagSet N n σ) =
      {x : Fin N → ℝ | x ∘ σ ∈ A} := by
  rw [projLastIter_eq]
  ext x
  constructor
  · rintro ⟨w, hw⟩
    rw [Set.mem_inter_iff] at hw
    have h1 : w ∈ A := (snocIt_mem_liftTailN A x w).mp hw.1
    have h2 : x ∘ σ = w := (snocIt_mem_diagSet σ x w).mp hw.2
    rwa [← h2] at h1
  · intro hx
    refine ⟨x ∘ σ, ?_⟩
    rw [Set.mem_inter_iff]
    exact ⟨(snocIt_mem_liftTailN A x (x ∘ σ)).mpr hx,
      (snocIt_mem_diagSet σ x (x ∘ σ)).mpr rfl⟩

/-- **`Ω` is closed under coordinate substitution.**  The pullback of an `Ω F D n`-set along
`σ : Fin n → Fin N` is `Ω (F + 2*(N+n) + 1) (D+2) N`. -/
theorem subst_mem (S : SOMin) {n N F D : ℕ} (σ : Fin n → Fin N) {A : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F D n) :
    {x : Fin N → ℝ | x ∘ σ ∈ A} ∈ S.Ω (F + 2 * (N + n) + 1) (D + 2) N := by
  have hL : liftTailN N n A ∈ S.Ω (F + N) D (N + n) := liftTailN_mem S hA N
  have hDg : diagSet N n σ ∈ S.Ω (N + n) 2 (N + n) := diagSet_mem S N n σ
  have h1 : liftTailN N n A ∈ S.Ω (max (F + N) (N + n)) D (N + n) :=
    Omega.mono hL (le_max_left _ _) le_rfl
  have h2 : diagSet N n σ ∈ S.Ω (max (F + N) (N + n)) 2 (N + n) :=
    Omega.mono hDg (le_max_right _ _) le_rfl
  have h3 : (liftTailN N n A ∩ diagSet N n σ) ∈
      S.Ω (max (F + N) (N + n) + 1) (D + 2) (N + n) := Omega_inter2 h1 h2
  have h4 : projLastIter N n (liftTailN N n A ∩ diagSet N n σ) ∈
      S.Ω (max (F + N) (N + n) + 1 + n + N) (D + 2) N :=
    projLastIter_mem S N n (max (F + N) (N + n) + 1) (D + 2) _ h3
  have h5 : projLastIter N n (liftTailN N n A ∩ diagSet N n σ) ∈
      S.Ω (F + 2 * (N + n) + 1) (D + 2) N := Omega.mono h4 (by omega) le_rfl
  rw [proj_lift_inter_diag] at h5
  exact h5

/-! ### 3. The coordinate substitutions realising the composition -/

/-- In `ℝ^{(m+1)+m}` with layout `(x, t, w)`, the substitution selecting `(w, t)`. -/
def sigG (m : ℕ) : Fin (m + 1) → Fin ((m + 1) + m) :=
  Fin.snoc (fun j : Fin m => Fin.natAdd (m + 1) j) (Fin.castAdd m (Fin.last m))

/-- In `ℝ^{(m+1)+m}` with layout `(x, t, w)`, the substitution selecting `(x, w_j)`. -/
def sigPhi (m : ℕ) (j : Fin m) : Fin (m + 1) → Fin ((m + 1) + m) :=
  Fin.snoc (fun i : Fin m => Fin.castAdd m (Fin.castSucc i)) (Fin.natAdd (m + 1) j)

@[simp] theorem sigG_last (m : ℕ) : sigG m (Fin.last m) = Fin.castAdd m (Fin.last m) := by
  simp [sigG]

@[simp] theorem sigG_castSucc (m : ℕ) (j : Fin m) :
    sigG m (Fin.castSucc j) = Fin.natAdd (m + 1) j := by
  simp [sigG]

@[simp] theorem sigPhi_last (m : ℕ) (j : Fin m) :
    sigPhi m j (Fin.last m) = Fin.natAdd (m + 1) j := by
  simp [sigPhi]

@[simp] theorem sigPhi_castSucc (m : ℕ) (j : Fin m) (i : Fin m) :
    sigPhi m j (Fin.castSucc i) = Fin.castAdd m (Fin.castSucc i) := by
  simp [sigPhi]

/-- The pullback of `graph g`: the last `m+1` coordinates carry `(w, t)` with `t = g w`. -/
def setG (m : ℕ) (g : (Fin m → ℝ) → ℝ) : Set (Fin ((m + 1) + m) → ℝ) :=
  {z | z ∘ sigG m ∈ graphOf g}

/-- The pullback of `graph φ_j`: the coordinate `w_j` and the first `m` coordinates `x`. -/
def setH (m : ℕ) (φ : (Fin m → ℝ) → (Fin m → ℝ)) (j : Fin m) :
    Set (Fin ((m + 1) + m) → ℝ) :=
  {z | z ∘ sigPhi m j ∈ graphOf (fun x : Fin m → ℝ => φ x j)}

theorem snocIt_sigG (m : ℕ) (x : Fin (m + 1) → ℝ) (w : Fin m → ℝ) :
    snocIt (m + 1) m x w ∘ sigG m = Fin.snoc w (x (Fin.last m)) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Function.comp_apply, sigG_last, snocIt_castAdd, Fin.snoc_last]
  · intro j
    rw [Function.comp_apply, sigG_castSucc, snocIt_natAdd, Fin.snoc_castSucc]

theorem snocIt_sigPhi (m : ℕ) (j : Fin m) (x : Fin (m + 1) → ℝ) (w : Fin m → ℝ) :
    snocIt (m + 1) m x w ∘ sigPhi m j = Fin.snoc (Fin.init x) (w j) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Function.comp_apply, sigPhi_last, snocIt_natAdd, Fin.snoc_last]
  · intro i
    rw [Function.comp_apply, sigPhi_castSucc, snocIt_castAdd, Fin.snoc_castSucc]
    simp [Fin.init]

theorem mem_setG {m : ℕ} (g : (Fin m → ℝ) → ℝ) (x : Fin (m + 1) → ℝ) (w : Fin m → ℝ) :
    snocIt (m + 1) m x w ∈ setG m g ↔ x (Fin.last m) = g w := by
  change (snocIt (m + 1) m x w ∘ sigG m) ∈ graphOf g ↔ x (Fin.last m) = g w
  rw [snocIt_sigG]
  simp [graphOf]

theorem mem_setH {m : ℕ} (φ : (Fin m → ℝ) → (Fin m → ℝ)) (j : Fin m)
    (x : Fin (m + 1) → ℝ) (w : Fin m → ℝ) :
    snocIt (m + 1) m x w ∈ setH m φ j ↔ w j = φ (Fin.init x) j := by
  change (snocIt (m + 1) m x w ∘ sigPhi m j) ∈ graphOf (fun x : Fin m → ℝ => φ x j) ↔
    w j = φ (Fin.init x) j
  rw [snocIt_sigPhi]
  simp [graphOf]

end GraphComp

open GraphComp

/-- **Composition of `Ω`-definable maps.**  If `g : ℝ^m → ℝ` and each coordinate of
`φ : ℝ^m → ℝ^m` have `Ω`-definable graphs, then so does `g ∘ φ`, with format and degree
bounded by sums of the given formats/degrees plus constants depending on `m` only (linear
bookkeeping, as needed for the polynomial bounds of `FLem`).

Construction.  Work in `ℝ^{2m+1}`; the pullback of `graph g` under the coordinate substitution
`(w,y) ↦` trailing block and the `m` pullbacks of `graph φ_j` under `(x,w_j) ↦ (x,w_j)` are
`Ω`-sets (a coordinate substitution `σ : Fin (m+1) → Fin (2m+1)` is realised by putting the
`m+1` fresh coordinates as the trailing block, intersecting with the single hypersurface
`Σ (Z_{new,i} − Z_{σ i})² = 0` and projecting the fresh block away — the argument of the
sibling lemma `Work.WilG4c.Subst`; it may be inlined).  Intersecting the `m+1` sets and
projecting the trailing `w`-block away (`SOMin.proj` `m` times) gives exactly
`graphOf (g ∘ φ)`.  `Work.WilG1.Basic` has reusable closure lemmas
(`inter_mem`, `projLast_mem`, `prodLeft_mem`, `hyp_mem`, `mono`). -/
theorem GraphOfComp (S : SOMin) {m F₁ F₂ D₁ D₂ : ℕ} (g : (Fin m → ℝ) → ℝ)
    (φ : (Fin m → ℝ) → (Fin m → ℝ))
    (hg : graphOf g ∈ S.Ω F₁ D₁ (m + 1))
    (hφ : ∀ j : Fin m, graphOf (fun x : Fin m → ℝ => φ x j) ∈ S.Ω F₂ D₂ (m + 1)) :
    ∃ C₁ C₂ : ℕ, graphOf (g ∘ φ) ∈ S.Ω (F₁ + F₂ + C₁) (D₁ + m * D₂ + C₂) (m + 1) := by
  -- the `g`-pullback
  have hG : setG m g ∈ S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1))
      (D₁ + 2) ((m + 1) + m) :=
    Omega.mono (subst_mem S (sigG m) hg) (by omega) le_rfl
  -- the `φ_j`-pullbacks
  have hH : ∀ j : Fin m, setH m φ j ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1)) (D₂ + 2) ((m + 1) + m) :=
    fun j => Omega.mono (subst_mem S (sigPhi m j) (hφ j)) (by omega) le_rfl
  -- intersect the `φ_j`-pullbacks
  have hA2 : (⋂ j : Fin m, setH m φ j) ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1)
        (m * (D₂ + 2)) ((m + 1) + m) := by
    have h := S.inter (F := F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1))
      (n := (m + 1) + m) (D := fun _ : Fin m => D₂ + 2)
      (A := fun j : Fin m => setH m φ j) hH
    have hsum : (∑ _ : Fin m, (D₂ + 2)) = m * (D₂ + 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    rw [hsum] at h
    exact h
  -- raise `g` to the same format and intersect everything
  have hG' : setG m g ∈ S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1)
      (D₁ + 2) ((m + 1) + m) := Omega.mono hG (by omega) le_rfl
  have hInt : (setG m g ∩ ⋂ j : Fin m, setH m φ j) ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1)
        ((D₁ + 2) + m * (D₂ + 2)) ((m + 1) + m) := Omega_inter2 hG' hA2
  -- project the `w`-block away
  have hProj : projLastIter (m + 1) m (setG m g ∩ ⋂ j : Fin m, setH m φ j) ∈
      S.Ω ((F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1) + m + (m + 1))
        ((D₁ + 2) + m * (D₂ + 2)) (m + 1) :=
    projLastIter_mem S (m + 1) m (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1)
      ((D₁ + 2) + m * (D₂ + 2)) _ hInt
  -- the projected set is the graph of the composite
  have hset : projLastIter (m + 1) m (setG m g ∩ ⋂ j : Fin m, setH m φ j) =
      graphOf (g ∘ φ) := by
    rw [projLastIter_eq]
    ext x
    constructor
    · rintro ⟨w, hw⟩
      rw [Set.mem_inter_iff] at hw
      obtain ⟨hGm, hHm⟩ := hw
      rw [Set.mem_iInter] at hHm
      have hlast : x (Fin.last m) = g w := (mem_setG g x w).mp hGm
      have hwx : w = φ (Fin.init x) := by
        funext j
        exact (mem_setH φ j x w).mp (hHm j)
      rw [hwx] at hlast
      simpa [graphOf] using hlast
    · intro hx
      have hx' : x (Fin.last m) = g (φ (Fin.init x)) := by simpa [graphOf] using hx
      refine ⟨φ (Fin.init x), ?_⟩
      rw [Set.mem_inter_iff, Set.mem_iInter]
      exact ⟨(mem_setG g x (φ (Fin.init x))).mpr hx',
        fun j => (mem_setH φ j x (φ (Fin.init x))).mpr rfl⟩
  refine ⟨2 * (((m + 1) + m) + (m + 1)) + 1 + 1 + 1 + m + (m + 1), 2 + 2 * m, ?_⟩
  rw [← hset]
  have hF : ((F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1) + m + (m + 1)) ≤
      F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1 + 1 + 1 + m + (m + 1)) :=
    le_of_eq (by ring)
  have hD : (D₁ + 2) + m * (D₂ + 2) ≤ D₁ + m * D₂ + (2 + 2 * m) := le_of_eq (by ring)
  exact Omega.mono hProj hF hD

end Work.WilG4c
