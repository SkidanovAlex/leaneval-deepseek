import Mathlib
import Submission.Work.WilG4c.GraphOfComp

/-!
## `Work.WilG4c.graphOfCompGen`: the rectangular composition of `Ω`-definable graphs

`Work.WilG4c.GraphOfComp` (and its explicit-constant restatement `Work.WilG4c.compExp` /
`Work.WilG4c.graphOf_comp_exp`) treats the *square* case `φ : ℝ^m → ℝ^m`: the graph of `g` and
the coordinate graphs of `φ` live in the same ambient space `ℝ^{m+1}`.

This file proves the *rectangular* case needed by the lead: `g : ℝ^n → ℝ` and
`φ : ℝ^M → ℝ^n`, so that `graphOf g ⊆ ℝ^{n+1}` while each `graphOf φ_j ⊆ ℝ^{M+1}`.  The
construction is the same one:

* work in `ℝ^{(M+1)+n}` with layout `(x, t, w)`: `x` are the first `M` coordinates, `t` is the
  coordinate `M` (the value of the composite) and `w` are the trailing `n` "intermediate"
  coordinates;
* the pullback of `graphOf g` under the substitution `(w, t)` (`sigGGen`) is `Ω`-definable with
  degree `D₁ + 2`;
* the pullback of `graphOf φ_j` under the substitution `(x, w_j)` (`sigPhiGen`) is `Ω`-definable
  with degree `D₂ + 2`;
* intersecting the `n` latter sets and then the former, and projecting the `w`-block away, gives
  exactly `graphOf (g ∘ φ)`.

The only difference from the square case is bookkeeping: the number of intersected `φ`-graphs is
`n` (so the degree is `D₁ + n * D₂ + const`) and the two substitution constants differ
(the source dimensions are `n + 1` and `M + 1` respectively).
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

namespace GraphCompGen

/-! ### 1. The two substitution maps -/

/-- In `ℝ^{(M+1)+n}` with layout `(x, t, w)`, the substitution selecting `(w, t)`. -/
def sigGGen (M n : ℕ) : Fin (n + 1) → Fin ((M + 1) + n) :=
  Fin.snoc (fun j : Fin n => Fin.natAdd (M + 1) j) (Fin.castAdd n (Fin.last M))

/-- In `ℝ^{(M+1)+n}` with layout `(x, t, w)`, the substitution selecting `(x, w_j)`. -/
def sigPhiGen (M n : ℕ) (j : Fin n) : Fin (M + 1) → Fin ((M + 1) + n) :=
  Fin.snoc (fun i : Fin M => Fin.castAdd n (Fin.castSucc i)) (Fin.natAdd (M + 1) j)

@[simp] theorem sigGGen_last (M n : ℕ) :
    sigGGen M n (Fin.last n) = Fin.castAdd n (Fin.last M) := by
  simp [sigGGen]

@[simp] theorem sigGGen_castSucc (M n : ℕ) (j : Fin n) :
    sigGGen M n (Fin.castSucc j) = Fin.natAdd (M + 1) j := by
  simp [sigGGen]

@[simp] theorem sigPhiGen_last (M n : ℕ) (j : Fin n) :
    sigPhiGen M n j (Fin.last M) = Fin.natAdd (M + 1) j := by
  simp [sigPhiGen]

@[simp] theorem sigPhiGen_castSucc (M n : ℕ) (j : Fin n) (i : Fin M) :
    sigPhiGen M n j (Fin.castSucc i) = Fin.castAdd n (Fin.castSucc i) := by
  simp [sigPhiGen]

/-! ### 2. The membership of the glued vector -/

theorem snocIt_sigGGen (M n : ℕ) (x : Fin (M + 1) → ℝ) (w : Fin n → ℝ) :
    snocIt (M + 1) n x w ∘ sigGGen M n = Fin.snoc w (x (Fin.last M)) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Function.comp_apply, sigGGen_last, snocIt_castAdd, Fin.snoc_last]
  · intro j
    rw [Function.comp_apply, sigGGen_castSucc, snocIt_natAdd, Fin.snoc_castSucc]

theorem snocIt_sigPhiGen (M n : ℕ) (j : Fin n) (x : Fin (M + 1) → ℝ) (w : Fin n → ℝ) :
    snocIt (M + 1) n x w ∘ sigPhiGen M n j = Fin.snoc (Fin.init x) (w j) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Function.comp_apply, sigPhiGen_last, snocIt_natAdd, Fin.snoc_last]
  · intro i
    rw [Function.comp_apply, sigPhiGen_castSucc, snocIt_castAdd, Fin.snoc_castSucc]
    simp [Fin.init]

/-! ### 3. The two pulled-back sets and their description on glued vectors -/

/-- The pullback of `graphOf g` under `sigGGen`. -/
def setGGen (M n : ℕ) (g : (Fin n → ℝ) → ℝ) : Set (Fin ((M + 1) + n) → ℝ) :=
  {z | z ∘ sigGGen M n ∈ graphOf g}

/-- The pullback of `graphOf φ_j` under `sigPhiGen`. -/
def setHGen (M n : ℕ) (φ : (Fin M → ℝ) → (Fin n → ℝ)) (j : Fin n) :
    Set (Fin ((M + 1) + n) → ℝ) :=
  {z | z ∘ sigPhiGen M n j ∈ graphOf (fun x : Fin M → ℝ => φ x j)}

theorem mem_setGGen {M n : ℕ} (g : (Fin n → ℝ) → ℝ) (x : Fin (M + 1) → ℝ)
    (w : Fin n → ℝ) :
    snocIt (M + 1) n x w ∈ setGGen M n g ↔ x (Fin.last M) = g w := by
  change (snocIt (M + 1) n x w ∘ sigGGen M n) ∈ graphOf g ↔ x (Fin.last M) = g w
  rw [snocIt_sigGGen]
  simp [graphOf]

theorem mem_setHGen {M n : ℕ} (φ : (Fin M → ℝ) → (Fin n → ℝ)) (j : Fin n)
    (x : Fin (M + 1) → ℝ) (w : Fin n → ℝ) :
    snocIt (M + 1) n x w ∈ setHGen M n φ j ↔ w j = φ (Fin.init x) j := by
  change (snocIt (M + 1) n x w ∘ sigPhiGen M n j) ∈
    graphOf (fun x : Fin M → ℝ => φ x j) ↔ w j = φ (Fin.init x) j
  rw [snocIt_sigPhiGen]
  simp [graphOf]

/-! ### 4. The projection of the intersection is the graph of the composite -/

theorem projLastIter_setGGen_inter (M n : ℕ) (g : (Fin n → ℝ) → ℝ)
    (φ : (Fin M → ℝ) → (Fin n → ℝ)) :
    projLastIter (M + 1) n (setGGen M n g ∩ ⋂ j : Fin n, setHGen M n φ j) =
      graphOf (g ∘ φ) := by
  rw [projLastIter_eq]
  ext x
  constructor
  · rintro ⟨w, hw⟩
    rw [Set.mem_inter_iff] at hw
    obtain ⟨hGm, hHm⟩ := hw
    rw [Set.mem_iInter] at hHm
    have hlast : x (Fin.last M) = g w := (mem_setGGen g x w).mp hGm
    have hwx : w = φ (Fin.init x) := by
      funext j
      exact (mem_setHGen φ j x w).mp (hHm j)
    rw [hwx] at hlast
    simpa [graphOf, Function.comp_def] using hlast
  · intro hx
    have hx' : x (Fin.last M) = g (φ (Fin.init x)) := by
      simpa [graphOf, Function.comp_def] using hx
    refine ⟨φ (Fin.init x), ?_⟩
    rw [Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨(mem_setGGen g x (φ (Fin.init x))).mpr hx',
      fun j => (mem_setHGen φ j x (φ (Fin.init x))).mpr rfl⟩

end GraphCompGen

open GraphCompGen

/-- **Composition of `Ω`-definable maps, rectangular case.**  If `graphOf g ⊆ ℝ^{n+1}` and the
`n` coordinate graphs of `φ : ℝ^M → ℝ^n` are `Ω`-definable, then `graphOf (g ∘ φ)` is
`Ω`-definable, with format and degree bounded by `F₁ + F₂ + C₁` and `D₁ + n * D₂ + C₂` for
constants `C₁, C₂` depending only on `S`, `n` and `M`. -/
theorem graphOfCompGen (S : WilkiesDesign.SOMin) (n M : ℕ) :
    ∃ (C₁ C₂ : ℕ), ∀ (F₁ F₂ D₁ D₂ : ℕ) (g : (Fin n → ℝ) → ℝ)
      (φ : (Fin M → ℝ) → (Fin n → ℝ)),
      WilkiesDesign.graphOf g ∈ S.Ω F₁ D₁ (n+1) →
      (∀ j : Fin n, WilkiesDesign.graphOf (fun x : Fin M → ℝ => φ x j) ∈ S.Ω F₂ D₂ (M+1)) →
      WilkiesDesign.graphOf (g ∘ φ) ∈ S.Ω (F₁ + F₂ + C₁) (D₁ + n * D₂ + C₂) (M+1) := by
  refine ⟨2 * (((M + 1) + n) + (n + 1)) + 1 +
      (2 * (((M + 1) + n) + (M + 1)) + 1) + 1 + 1 + n + (M + 1), 2 + 2 * n, ?_⟩
  intro F₁ F₂ D₁ D₂ g φ hg hφ
  -- the `g`-pullback
  have hG := GraphComp.subst_mem S (sigGGen M n) hg
  -- the `φ_j`-pullbacks
  have hH : ∀ j : Fin n, setHGen M n φ j ∈
      S.Ω (F₂ + 2 * (((M + 1) + n) + (M + 1)) + 1) (D₂ + 2) ((M + 1) + n) :=
    fun j => GraphComp.subst_mem S (sigPhiGen M n j) (hφ j)
  -- raise both to the common format `(F₁ + K₁) + (F₂ + K₂)`
  have hG' : setGGen M n g ∈
      S.Ω ((F₁ + 2 * (((M + 1) + n) + (n + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + n) + (M + 1)) + 1)) (D₁ + 2) ((M + 1) + n) :=
    Omega.mono hG
      (Nat.le_add_right (F₁ + 2 * (((M + 1) + n) + (n + 1)) + 1)
        (F₂ + 2 * (((M + 1) + n) + (M + 1)) + 1)) le_rfl
  have hH' : ∀ j : Fin n, setHGen M n φ j ∈
      S.Ω ((F₁ + 2 * (((M + 1) + n) + (n + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + n) + (M + 1)) + 1)) (D₂ + 2) ((M + 1) + n) :=
    fun j => Omega.mono (hH j)
      (Nat.le_add_left (F₂ + 2 * (((M + 1) + n) + (M + 1)) + 1)
        (F₁ + 2 * (((M + 1) + n) + (n + 1)) + 1)) le_rfl
  -- intersect the `φ_j`-pullbacks: `n` sets of degree `D₂ + 2`
  have hA2 : (⋂ j : Fin n, setHGen M n φ j) ∈
      S.Ω ((F₁ + 2 * (((M + 1) + n) + (n + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + n) + (M + 1)) + 1) + 1)
        (n * (D₂ + 2)) ((M + 1) + n) := by
    have h := S.inter
      (F := (F₁ + 2 * (((M + 1) + n) + (n + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + n) + (M + 1)) + 1))
      (n := (M + 1) + n) (D := fun _ : Fin n => D₂ + 2)
      (A := fun j : Fin n => setHGen M n φ j) hH'
    have hsum : (∑ _ : Fin n, (D₂ + 2)) = n * (D₂ + 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    rw [hsum] at h
    exact h
  -- raise the `g`-pullback to the same format and intersect everything
  have hG'' : setGGen M n g ∈
      S.Ω ((F₁ + 2 * (((M + 1) + n) + (n + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + n) + (M + 1)) + 1) + 1) (D₁ + 2) ((M + 1) + n) :=
    Omega.mono hG'
      (Nat.le_succ ((F₁ + 2 * (((M + 1) + n) + (n + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + n) + (M + 1)) + 1))) le_rfl
  have hInt : (setGGen M n g ∩ ⋂ j : Fin n, setHGen M n φ j) ∈
      S.Ω (((F₁ + 2 * (((M + 1) + n) + (n + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + n) + (M + 1)) + 1) + 1) + 1)
        ((D₁ + 2) + n * (D₂ + 2)) ((M + 1) + n) :=
    Omega_inter2 hG'' hA2
  -- project the `w`-block away
  have hProj : projLastIter (M + 1) n (setGGen M n g ∩ ⋂ j : Fin n, setHGen M n φ j) ∈
      S.Ω ((((F₁ + 2 * (((M + 1) + n) + (n + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + n) + (M + 1)) + 1) + 1) + 1) + n + (M + 1))
        ((D₁ + 2) + n * (D₂ + 2)) (M + 1) :=
    projLastIter_mem S (M + 1) n
      (((F₁ + 2 * (((M + 1) + n) + (n + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + n) + (M + 1)) + 1) + 1) + 1)
      ((D₁ + 2) + n * (D₂ + 2)) _ hInt
  rw [projLastIter_setGGen_inter M n g φ] at hProj
  refine Omega.mono hProj (le_of_eq (by ring)) (le_of_eq (by ring))

end Work.WilG4c
