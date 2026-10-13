/-
  WilE4 / CAD — the size of a family and the degree bookkeeping of one CAD level.

  `famDeg H` is the sum of the atom degrees of the members of `H`.  It bounds the number of members,
  the total degree of every member, and it is the quantity in which every later bound is polynomial.

  The one-level facts collected here are

  * `pad_deg_le`   — padding does not increase the degree;
  * `ofSign_deg_le_famDeg` — the basic set of a sign condition of `H` has degree at most `famDeg H`;
  * `cell_deg_le`  — the degree of a cell of the decomposition at one level up;
  * `cell_basics_length` — the number of basic sets of a cell is inherited from its base cell;
  * `famDeg_projDataT_le` — the size of the projection data, as a polynomial in `famDeg H`.
-/
import Submission.Work.WilE4.CAD.Decomp
import Submission.Work.WilE4.CAD.Bridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec tower)

variable {k m n : ℕ}

/-! ## The size of a family -/

/-- The size of a family: the sum of the atom degrees of its members. -/
def famDeg {m : ℕ} (H : List (MvPolynomial (Fin m) ℝ)) : ℕ := (H.map atomDegD).sum

theorem atomDegD_neg {m : ℕ} (P : MvPolynomial (Fin m) ℝ) : atomDegD (-P) = atomDegD P := by
  simp [atomDegD, MvPolynomial.totalDegree_neg]

theorem one_le_atomDegD {m : ℕ} (P : MvPolynomial (Fin m) ℝ) : 1 ≤ atomDegD P :=
  Nat.succ_le_succ (Nat.zero_le _)

theorem famDeg_append {m : ℕ} (l₁ l₂ : List (MvPolynomial (Fin m) ℝ)) :
    famDeg (l₁ ++ l₂) = famDeg l₁ + famDeg l₂ := by
  simp [famDeg, List.map_append, List.sum_append]

theorem atomDegD_le_famDeg {m : ℕ} {H : List (MvPolynomial (Fin m) ℝ)}
    {P : MvPolynomial (Fin m) ℝ} (h : P ∈ H) : atomDegD P ≤ famDeg H := by
  rw [famDeg]
  exact List.le_sum_of_mem (List.mem_map_of_mem h)

theorem totalDegree_le_famDeg {m : ℕ} {H : List (MvPolynomial (Fin m) ℝ)}
    {P : MvPolynomial (Fin m) ℝ} (h : P ∈ H) : P.totalDegree ≤ famDeg H := by
  have h' := atomDegD_le_famDeg h
  simp only [atomDegD] at h'
  omega

theorem length_le_famDeg {m : ℕ} (H : List (MvPolynomial (Fin m) ℝ)) : H.length ≤ famDeg H := by
  have := List.length_le_sum_of_one_le (H.map atomDegD) fun i hi => by
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hi
    exact one_le_atomDegD P
  simpa [famDeg] using this

theorem famDeg_le_length_mul {m : ℕ} {H : List (MvPolynomial (Fin m) ℝ)} {D : ℕ}
    (hD : ∀ P ∈ H, P.totalDegree ≤ D) : famDeg H ≤ H.length * (D + 1) := by
  rw [famDeg]
  calc (H.map atomDegD).sum ≤ (H.map fun _ => D + 1).sum :=
        List.sum_le_sum fun Q hQ => by
          have hQ' := hD Q hQ
          simp only [atomDegD]
          omega
    _ = H.length * (D + 1) := by
        simp [List.map_const', List.sum_replicate, nsmul_eq_mul]

/-! ## Padding and sign conditions do not increase the degree -/

theorem atomDegD_rename_le {m n : ℕ} (f : Fin m → Fin n) (P : MvPolynomial (Fin m) ℝ) :
    atomDegD (MvPolynomial.rename f P) ≤ atomDegD P := by
  have h := MvPolynomial.totalDegree_rename_le f P
  simp only [atomDegD]
  omega

private theorem basicD_pad_deg_le {m : ℕ} (B : BasicD m) :
    (⟨B.eqs.map (MvPolynomial.rename (Fin.castSucc : Fin m → Fin (m + 1))),
      B.pos.map (MvPolynomial.rename Fin.castSucc)⟩ : BasicD (m + 1)).deg ≤ B.deg := by
  have h : ∀ l : List (MvPolynomial (Fin m) ℝ),
      ((l.map (MvPolynomial.rename (Fin.castSucc : Fin m → Fin (m + 1)))).map atomDegD).sum ≤
        (l.map atomDegD).sum := fun l => by
    rw [List.map_map]
    exact List.sum_le_sum fun P _ => atomDegD_rename_le _ P
  rw [BasicD.deg_cons, BasicD.deg_cons]
  exact add_le_add (h B.eqs) (h B.pos)

theorem pad_deg_le {m : ℕ} (X : SAd m) : (X.pad).deg ≤ X.deg := by
  show ((X.basics.map fun B : BasicD m =>
      (⟨B.eqs.map (MvPolynomial.rename (Fin.castSucc : Fin m → Fin (m + 1))),
        B.pos.map (MvPolynomial.rename Fin.castSucc)⟩ : BasicD (m + 1))).map
      BasicD.deg).sum ≤ (X.basics.map BasicD.deg).sum
  rw [List.map_map]
  exact List.sum_le_sum fun B _ => basicD_pad_deg_le B

theorem pad_basics_length {m : ℕ} (X : SAd m) : (X.pad).basics.length = X.basics.length := by
  simp [SAd.pad]

/-! ## Sums over `filterMap`s and over `finRange` -/

private theorem map_get_finRange {α : Type*} (l : List α) :
    (List.finRange l.length).map l.get = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.length_cons, List.finRange_succ, List.map_cons, List.map_map,
      List.get_cons_zero]
    have h : ((a :: t).get ∘ Fin.succ) = t.get := by
      funext i
      exact List.get_cons_succ
    rw [h, ih]

theorem sum_atomDeg_get_finRange {m : ℕ} (H : List (MvPolynomial (Fin m) ℝ)) :
    ((List.finRange H.length).map fun i => atomDegD (H.get i)).sum = famDeg H := by
  rw [famDeg]
  conv_rhs => rw [← map_get_finRange H]
  rw [List.map_map]
  rfl

private theorem sum_filterMap_le {α β : Type*} (l : List α) (f : α → Option β) (G : α → ℕ)
    (g : β → ℕ) (h : ∀ a b, f a = some b → g b ≤ G a) :
    ((l.filterMap f).map g).sum ≤ (l.map G).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.filterMap_cons]
    rcases hfa : f a with _ | b
    · simp only [hfa, Option.elim_none, List.sum_cons, zero_add]
      exact ih.trans (Nat.le_add_left _ _)
    · simp only [hfa, Option.elim_some, List.map_cons, List.sum_cons]
      exact add_le_add (h a b hfa) ih

/-- The basic set of a sign condition of `H` has degree at most `2 * famDeg H` (each member of `H`
contributes at most one atom, but we do not need the exact partition of the sign condition into
equations and inequalities). -/
theorem ofSign_deg_le_famDeg {m : ℕ} (H : List (MvPolynomial (Fin m) ℝ))
    (v : Fin H.length → SignType) : (BasicD.ofSign H v).deg ≤ 2 * famDeg H := by
  rw [BasicD.deg_cons, ofSign_eqs, ofSign_pos]
  have h1 : (((List.finRange H.length).filterMap
      fun i => if v i = 0 then some (H.get i) else none).map atomDegD).sum ≤ famDeg H := by
    refine (sum_filterMap_le _ _ (fun i => atomDegD (H.get i)) atomDegD ?_).trans (le_of_eq ?_)
    · intro a b hab
      by_cases h : v a = 0
      · rw [if_pos h] at hab
        injection hab with hb
        rw [← hb]
      · rw [if_neg h] at hab
        exact absurd hab (by simp)
    · exact sum_atomDeg_get_finRange H
  have h2 : (((List.finRange H.length).filterMap
      fun i => if v i = 1 then some (H.get i)
        else if v i = -1 then some (-(H.get i)) else none).map atomDegD).sum ≤ famDeg H := by
    refine (sum_filterMap_le _ _ (fun i => atomDegD (H.get i)) atomDegD ?_).trans (le_of_eq ?_)
    · intro a b hab
      by_cases h : v a = 1
      · rw [if_pos h] at hab
        injection hab with hb
        rw [← hb]
      · by_cases h' : v a = -1
        · rw [if_neg h, if_pos h'] at hab
          injection hab with hb
          rw [← hb, atomDegD_neg]
        · rw [if_neg h, if_neg h'] at hab
          exact absurd hab (by simp)
    · exact sum_atomDeg_get_finRange H
  have := add_le_add h1 h2
  linarith

/-! ## The degree of a cell -/

theorem cell_basics_length {m : ℕ} (C : SAd m) (H : List (MvPolynomial (Fin (m + 1)) ℝ))
    (v : Fin H.length → SignType) : (cell C H v).basics.length = C.basics.length := by
  simp [cell, SAd.interBasic, SAd.pad]

/-- The degree of the cell over `C` cut by the sign condition `v`. -/
theorem cell_deg_le {m : ℕ} (C : SAd m) (H : List (MvPolynomial (Fin (m + 1)) ℝ))
    (v : Fin H.length → SignType) :
    (cell C H v).deg ≤ C.deg + C.basics.length * (2 * famDeg H) := by
  have h1 : (C.pad).deg ≤ C.deg := pad_deg_le C
  have h2 : (C.pad).basics.length = C.basics.length := pad_basics_length C
  have h3 : (BasicD.ofSign H v).deg ≤ 2 * famDeg H := ofSign_deg_le_famDeg H v
  rw [cell, SAd.interBasic_deg, h2]
  exact add_le_add h1 (Nat.mul_le_mul_left _ h3)

/-! ## The size of the projection data -/

/-- The projection data of a family has size at most `16 * (famDeg H + 1)^9`. -/
theorem famDeg_projDataT_le {n : ℕ} (H : List (MvPolynomial (Fin (n + 1)) ℝ)) :
    famDeg (projDataT n H) ≤ 16 * (famDeg H + 1) ^ 9 := by
  set E := famDeg H with hE
  have hD : ∀ P ∈ H, P.totalDegree ≤ E := fun P hP => totalDegree_le_famDeg hP
  have hlen : H.length ≤ E := length_le_famDeg H
  have key : famDeg (projDataT n H) ≤
      ((H.length * (E + 1) + (H.length * H.length) * ((E + 1) * (E + 1))
          + (H.length * H.length) * ((E + 1) * (E + 1) * (E + 1)) + 1) *
        ((2 * E * E + 1) + 1)) * ((2 * E * E + 1) + 1) :=
    (famDeg_le_length_mul (projDataT_deg hD)).trans
      (Nat.mul_le_mul_right _ (projDataT_length hD))
  have hsq : (E + 1) ^ 2 = (E + 1) * (E + 1) := by ring
  have h4 : (E + 1) ^ 4 = (E + 1) * (E + 1) * ((E + 1) * (E + 1)) := by ring
  have h5 : (E + 1) ^ 5 = (E + 1) * (E + 1) * ((E + 1) * (E + 1) * (E + 1)) := by ring
  -- the length bound is at most `4 * (E+1)^5`
  have hs : H.length * (E + 1) + (H.length * H.length) * ((E + 1) * (E + 1))
      + (H.length * H.length) * ((E + 1) * (E + 1) * (E + 1)) + 1 ≤ 4 * ((E + 1) ^ 5) := by
    have h1 : H.length * (E + 1) ≤ (E + 1) ^ 2 := by
      refine (Nat.mul_le_mul_right (E + 1) hlen).trans ?_
      rw [hsq]
      exact Nat.mul_le_mul_right (E + 1) (Nat.le_succ E)
    have h2 : (H.length * H.length) * ((E + 1) * (E + 1)) ≤ (E + 1) ^ 4 := by
      have hh : H.length * H.length ≤ (E + 1) * (E + 1) :=
        Nat.mul_le_mul (hlen.trans (Nat.le_succ E)) (hlen.trans (Nat.le_succ E))
      refine (Nat.mul_le_mul hh (le_refl ((E + 1) * (E + 1)))).trans (le_of_eq ?_)
      rw [h4]
    have h3' : (H.length * H.length) * ((E + 1) * (E + 1) * (E + 1)) ≤ (E + 1) ^ 5 := by
      have hh : H.length * H.length ≤ (E + 1) * (E + 1) :=
        Nat.mul_le_mul (hlen.trans (Nat.le_succ E)) (hlen.trans (Nat.le_succ E))
      refine (Nat.mul_le_mul hh (le_refl ((E + 1) * (E + 1) * (E + 1)))).trans (le_of_eq ?_)
      rw [h5]
    have h3 : (E + 1) ^ 2 ≤ (E + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3'' : (E + 1) ^ 4 ≤ (E + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
    have h6 : 1 ≤ (E + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
    linarith
  -- the degree bound is at most `2 * (E+1)^2`
  have hb : (2 * E * E + 1) + 1 ≤ 2 * (E + 1) ^ 2 := by
    have h5a : 2 * E * E ≤ 2 * ((E + 1) * (E + 1)) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.le_succ E) (Nat.le_succ E))
    have h5b : 2 ≤ 2 * ((E + 1) * (E + 1)) := by
      have hpos : (E + 1) * (E + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
      exact Nat.mul_le_mul_left 2 (Nat.one_le_iff_ne_zero.mpr hpos)
    rw [hsq]
    linarith
  calc famDeg (projDataT n H)
      ≤ (4 * (E + 1) ^ 5 * (2 * (E + 1) ^ 2)) * (2 * (E + 1) ^ 2) :=
        key.trans (Nat.mul_le_mul (Nat.mul_le_mul hs hb) hb)
    _ = 16 * (E + 1) ^ 9 := by ring

end Work.WilE4.CAD
