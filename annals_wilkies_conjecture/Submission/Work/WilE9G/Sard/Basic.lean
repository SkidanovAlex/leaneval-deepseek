import Mathlib

set_option autoImplicit false

/-!
# Basic vocabulary for the Morse–Sard theorem

This module fixes the notation used by the Morse–Sard development in `Work.WilE9G.Sard`:

* `critSet f` — the critical set of `f : ℝⁿ → ℝᵐ`, i.e. the set of points where the Fréchet
  derivative is not surjective;
* `SardNull n` — the Morse–Sard statement at source dimension `n` (for all target dimensions and
  all open sets);
* the "insert / delete a coordinate" linear algebra used for the change of variables in the
  induction step (`ins`, `del`, `insCLM`, `delCLM`).
-/

namespace Work.WilE9G.Sard

open MeasureTheory

/-- The critical set of `f : ℝⁿ → ℝᵐ`: the set of points where the Fréchet derivative of `f`
fails to be surjective. -/
def critSet {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) : Set (Fin n → ℝ) :=
  {x | ¬ Function.Surjective (fderiv ℝ f x)}

@[simp] theorem mem_critSet {n m : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)} {x : Fin n → ℝ} :
    x ∈ critSet f ↔ ¬ Function.Surjective (fderiv ℝ f x) := Iff.rfl

/-- **The Morse–Sard statement at source dimension `n`.**  For every `m`, every
`f : ℝⁿ → ℝᵐ` analytic on an open set `U`, the critical values lying over `U` are Lebesgue-null. -/
def SardNull (n : ℕ) : Prop :=
  ∀ (m : ℕ) (f : (Fin n → ℝ) → (Fin m → ℝ)) (U : Set (Fin n → ℝ)),
    IsOpen U → AnalyticOn ℝ f U → MeasureTheory.volume (f '' (critSet f ∩ U)) = 0

/-! ### Inserting and deleting a coordinate -/

/-- Insert a real number in position `i`. -/
abbrev ins {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (w : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.insertNth i t w

/-- Delete position `i`. -/
def del {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : Fin n → ℝ := fun k => x (i.succAbove k)

@[simp] theorem ins_self {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (w : Fin n → ℝ) :
    ins i t w i = t :=
  Fin.insertNth_apply_same (α := fun _ => ℝ) i t w

@[simp] theorem ins_succAbove {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (w : Fin n → ℝ) (k : Fin n) :
    ins i t w (i.succAbove k) = w k :=
  Fin.insertNth_apply_succAbove (α := fun _ => ℝ) i t w k

theorem del_ins {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (w : Fin n → ℝ) : del i (ins i t w) = w := by
  funext k; simp [del]

theorem ins_del {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : ins i (x i) (del i x) = x := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
    simp [del]

/-- `(t, w) ↦ ins i t w` as a continuous linear map. -/
noncomputable def insCLM (n : ℕ) (i : Fin (n + 1)) :
    (ℝ × (Fin n → ℝ)) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi fun j => dite (j = i)
    (fun _ => ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))
    (fun hj => (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin n => ℝ) (Classical.choose (Fin.exists_succAbove_eq hj))).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)))

theorem insCLM_apply {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (w : Fin n → ℝ) :
    insCLM n i (t, w) = ins i t w := by
  funext j
  rw [insCLM, ContinuousLinearMap.pi_apply]
  by_cases hj : j = i
  · subst hj; simp [ins]
  · rw [dif_neg hj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    set l := Classical.choose (Fin.exists_succAbove_eq hj) with hl
    have hlj : i.succAbove l = j := by rw [hl]; exact Classical.choose_spec (Fin.exists_succAbove_eq hj)
    show w l = ins i t w j
    rw [← hlj, ins_succAbove]

/-- `x ↦ del i x` as a continuous linear map. -/
noncomputable def delCLM (n : ℕ) (i : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) (i.succAbove k)

theorem delCLM_apply {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    delCLM n i x = del i x := rfl

theorem insCLM_injective {n : ℕ} (i : Fin (n + 1)) : Function.Injective (insCLM n i) := by
  intro p q hpq
  rw [show p = (p.1, p.2) from rfl, show q = (q.1, q.2) from rfl] at hpq
  rw [insCLM_apply, insCLM_apply] at hpq
  have h1 : p.1 = q.1 := by have := congrFun hpq i; simpa using this
  have h2 : p.2 = q.2 := by
    funext k
    have := congrFun hpq (i.succAbove k)
    simpa using this
  exact Prod.ext h1 h2

end Work.WilE9G.Sard
