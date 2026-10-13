import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG1.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.API
import Submission.Work.WilG4c.Subst

namespace Work.WilG4c

open WilkiesDesign

noncomputable section

/-! ## Coordinates of the auxiliary space `ℝ^{N+2} = (w,v,t)`

The construction of BNZ §5.4 reads a point of the auxiliary space as `(w,v,t)` where `w` is the
first `N` coordinates, `v` the index `N` and `t` the last index `N+1`.  The substitution
`iota N : Fin (N+1) → Fin (N+2)` sends `(w,v,t)` to `(w,t)` (it forgets `v`), so that the
pullback of `A ⊆ ℝ^{N+1}` along it is `{(w,v,t) | (w,t) ∈ A}`.
-/

/-- The `v`-coordinate index of `ℝ^{N+2}` read as `(w,v,t)`: the index `N`. -/
def vIdx (N : ℕ) : Fin (N + 2) := (Fin.last N).castSucc

/-- The `t`-coordinate index of `ℝ^{N+2}` read as `(w,v,t)`: the last index. -/
def tIdx (N : ℕ) : Fin (N + 2) := Fin.last (N + 1)

/-- The substitution `Fin (N+1) → Fin (N+2)` that keeps the first `N` coordinates and the last:
it inserts the missing index `N`.  Geometrically it reads a point of `ℝ^{N+2} = (w,v,t)` as
`(w,t)`. -/
def iota (N : ℕ) : Fin (N + 1) → Fin (N + 2) :=
  Fin.lastCases (tIdx N) (fun i : Fin N => (Fin.castSucc i).castSucc)

lemma iota_castSucc (N : ℕ) (i : Fin N) :
    iota N (Fin.castSucc i) = (Fin.castSucc i).castSucc :=
  Fin.lastCases_castSucc i

lemma iota_last (N : ℕ) : iota N (Fin.last N) = tIdx N := Fin.lastCases_last

/-- Reading `Fin.snoc z t : Fin (N+2) → ℝ` (a point `(w,v,t)`) along `iota` gives the point
`(w,t)`, i.e. `Fin.snoc (Fin.init z) t`. -/
lemma comp_iota_snoc (N : ℕ) (z : Fin (N + 1) → ℝ) (t : ℝ) :
    (Fin.snoc z t) ∘ iota N = Fin.snoc (Fin.init z) t := by
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | h
  · rw [Function.comp_apply, iota_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl
  · rw [h, Function.comp_apply, iota_last, tIdx, Fin.snoc_last, Fin.snoc_last]

/-! ## The two hyperplanes -/

/-- The hyperplane `v = (t+2)/4` of `ℝ^{N+2}` read as `(w,v,t)`, as the polynomial
`4·X_N - X_{N+1} - 2`; its total degree is `1`. -/
def Hpoly (N : ℕ) : MvPolynomial (Fin (N + 2)) ℝ :=
  MvPolynomial.C 4 * MvPolynomial.X (vIdx N) - MvPolynomial.X (tIdx N) - MvPolynomial.C 2

lemma Hpoly_eval (N : ℕ) (x : Fin (N + 2) → ℝ) :
    MvPolynomial.eval x (Hpoly N) = 4 * x (vIdx N) - x (tIdx N) - 2 := by
  simp [Hpoly]

lemma Hpoly_totalDegree (N : ℕ) : (Hpoly N).totalDegree ≤ 1 := by
  have h1 : (MvPolynomial.C (4 : ℝ) * MvPolynomial.X (vIdx N) :
      MvPolynomial (Fin (N + 2)) ℝ).totalDegree ≤ 1 :=
    le_trans (MvPolynomial.totalDegree_mul _ _) (by
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X])
  have h2 : (MvPolynomial.X (tIdx N) : MvPolynomial (Fin (N + 2)) ℝ).totalDegree ≤ 1 :=
    le_of_eq (MvPolynomial.totalDegree_X _)
  have h3 : (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin (N + 2)) ℝ).totalDegree ≤ 1 := by
    rw [MvPolynomial.totalDegree_C]
    omega
  have h4 : (MvPolynomial.C (4 : ℝ) * MvPolynomial.X (vIdx N) -
      MvPolynomial.X (tIdx N) : MvPolynomial (Fin (N + 2)) ℝ).totalDegree ≤ 1 :=
    le_trans (MvPolynomial.totalDegree_sub _ _) (max_le h1 h2)
  exact le_trans (MvPolynomial.totalDegree_sub _ _) (max_le h4 h3)

/-- The hyperplane `v = 1/2` of `ℝ^{N+1}` (its last coordinate is `v`). -/
def Vpoly (N : ℕ) : MvPolynomial (Fin (N + 1)) ℝ :=
  MvPolynomial.X (Fin.last N) - MvPolynomial.C (1 / 2)

lemma Vpoly_eval (N : ℕ) (z : Fin (N + 1) → ℝ) :
    MvPolynomial.eval z (Vpoly N) = z (Fin.last N) - 1 / 2 := by
  simp [Vpoly]

lemma Vpoly_totalDegree (N : ℕ) : (Vpoly N).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
  · exact le_of_eq (MvPolynomial.totalDegree_X _)
  · rw [MvPolynomial.totalDegree_C]
    omega

/-! ## The two branches of the surrogate, as the two sides of a union -/

/-- Branch 1 of the surrogate: projecting `t` out of
`{(w,v,t) | (w,t) ∈ A ∧ v = (t+2)/4}`. -/
lemma projLast_branch1 (N : ℕ) (A : Set (Fin (N + 1) → ℝ)) :
    projLast {x : Fin (N + 2) → ℝ | x ∘ iota N ∈ A ∧ MvPolynomial.eval x (Hpoly N) = 0}
      = {z : Fin (N + 1) → ℝ |
          ∃ t : ℝ, Fin.snoc (Fin.init z) t ∈ A ∧ z (Fin.last N) = (t + 2) / 4} := by
  ext z
  constructor
  · rintro ⟨t, hA, hH⟩
    rw [comp_iota_snoc N z t] at hA
    rw [Hpoly_eval, vIdx, tIdx, Fin.snoc_castSucc, Fin.snoc_last] at hH
    exact ⟨t, hA, by linarith⟩
  · rintro ⟨t, hA, hv⟩
    refine ⟨t, ?_, ?_⟩
    · rwa [comp_iota_snoc N z t]
    · rw [Hpoly_eval, vIdx, tIdx, Fin.snoc_castSucc, Fin.snoc_last]
      linarith

/-- Branch 2 of the surrogate: `w ∉ projLast A` together with `v = 1/2`. -/
lemma branch2_eq (N : ℕ) (A : Set (Fin (N + 1) → ℝ)) :
    {z : Fin (N + 1) → ℝ | Fin.init z ∈ (projLast A)ᶜ} ∩
        {z : Fin (N + 1) → ℝ | MvPolynomial.eval z (Vpoly N) = 0}
      = {z : Fin (N + 1) → ℝ | Fin.init z ∉ projLast A ∧ z (Fin.last N) = 1 / 2} := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff, Vpoly_eval]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩

/-- The union of the two branches is exactly the surrogate set of the statement. -/
lemma targetSet_eq (N : ℕ) (A : Set (Fin (N + 1) → ℝ)) :
    projLast {x : Fin (N + 2) → ℝ | x ∘ iota N ∈ A ∧ MvPolynomial.eval x (Hpoly N) = 0}
        ∪ ({z : Fin (N + 1) → ℝ | Fin.init z ∈ (projLast A)ᶜ} ∩
          {z : Fin (N + 1) → ℝ | MvPolynomial.eval z (Vpoly N) = 0})
      = {z : Fin (N + 1) → ℝ |
          (∃ t : ℝ, Fin.snoc (Fin.init z) t ∈ A ∧ z (Fin.last N) = (t + 2) / 4) ∨
          (Fin.init z ∉ projLast A ∧ z (Fin.last N) = 1 / 2)} := by
  rw [projLast_branch1, branch2_eq]
  ext z
  simp only [Set.mem_union, Set.mem_ofPred_eq]

/-! ## The surrogate branch is `Ω`-definable -/

/-- The "branch" part of the surrogate construction (BNZ §5.4, the `if`-then-`else` split of
the surrogate): for an `Ω`-set `A ⊆ ℝ^{N+1}`, read as `{(w,t)}` with `w = Fin.init ·` and
`t = · (Fin.last N)`, the set of `(w,v)` with `∃ t, (w,t) ∈ A ∧ v = (t+2)/4`, or with
`w ∉ projLast A ∧ v = 1/2`, is `Ω`-definable at format `F + C₁` and degree `2*D + C₂`.

The coefficient of `D` (exactly `2`) matters: callers combine this with other sets whose
degrees must not be multiplied.

Construction (in `ℝ^{N+2}` laid out as `(w , v, t)`):
* branch 1 is `projLast` (forget `t`) of the intersection of (i) the pullback of `A` along the
  coordinate substitution `(w,v,t) ↦ (w,t)` -- `Work.WilG5.coordPre` with
  `ι : Fin (N+1) → Fin (N+2)` keeping the first `N` coordinates and the last one, cost
  `D + const` -- and (ii) the hyperplane `v = (t+2)/4`, i.e. `4*X_{N+1} - X_N - 2 = 0`, whose
  total degree is `1`;
* branch 2 is the pullback of `(projLast A)ᶜ` to the `w`-coordinates (`Work.WilG5.coordPre`,
  cost `D + const`) intersected with `{v = 1/2}` (`X_N - 1/2 = 0`, degree `1`);
* `SOMin.union`/`SOMin.inter`/`SOMin.proj`/`SOMin.compl`/`SOMin.hyp` give the claim, with the
  union summing the two degrees. -/
theorem surrogateBranch (S : WilkiesDesign.SOMin) (N : ℕ) :
    ∃ (C₁ C₂ : ℕ), ∀ (F D : ℕ) (A : Set (Fin (N + 1) → ℝ)),
      A ∈ S.Ω F D (N + 1) →
      {z : Fin (N + 1) → ℝ |
        (∃ t : ℝ, Fin.snoc (Fin.init z) t ∈ A ∧ z (Fin.last N) = (t + 2) / 4) ∨
        (Fin.init z ∉ WilkiesDesign.projLast A ∧ z (Fin.last N) = 1 / 2)}
      ∈ S.Ω (F + C₁) (2 * D + C₂) (N + 1) := by
  refine ⟨3 * N + 8, 8, ?_⟩
  intro F D A hA
  -- Branch 1: the pullback of `A` to the `(w,t)`-coordinates, of degree `D + 2`.
  have hLift : {x : Fin (N + 2) → ℝ | x ∘ iota N ∈ A} ∈ S.Ω (F + 3 * N + 6) (D + 2) (N + 2) :=
    WilG1.Omega.mono (Subst S (iota N) hA) (by omega) le_rfl
  -- the hyperplane `v = (t+2)/4`, of degree `1`
  have hHY : {x : Fin (N + 2) → ℝ | MvPolynomial.eval x (Hpoly N) = 0} ∈
      S.Ω (F + 3 * N + 6) 1 (N + 2) :=
    WilG1.Omega.mono (S.hyp (N + 2) (Hpoly N)) (by omega) (Hpoly_totalDegree N)
  have hI : ({x : Fin (N + 2) → ℝ | x ∘ iota N ∈ A} ∩
      {x : Fin (N + 2) → ℝ | MvPolynomial.eval x (Hpoly N) = 0}) ∈
      S.Ω (F + 3 * N + 7) (D + 3) (N + 2) :=
    WilG1.Omega.mono (WilG0.Omega_inter2 hLift hHY) (by omega) (by omega)
  -- forget `t`
  have hB1 : projLast ({x : Fin (N + 2) → ℝ | x ∘ iota N ∈ A} ∩
      {x : Fin (N + 2) → ℝ | MvPolynomial.eval x (Hpoly N) = 0}) ∈
      S.Ω (F + 3 * N + 8) (D + 3) (N + 1) :=
    WilG1.Omega.mono (S.proj hI) (by omega) le_rfl
  -- Branch 2: the complement of `projLast A` on the `w`-coordinates, degree `D`
  have hB2a : {z : Fin (N + 1) → ℝ | Fin.init z ∈ (projLast A)ᶜ} ∈
      S.Ω (F + 3 * N + 6) D (N + 1) :=
    WilG1.Omega.mono (S.prod_right (S.compl (S.proj hA))) (by omega) le_rfl
  -- the hyperplane `v = 1/2`, of degree `1`
  have hV : {z : Fin (N + 1) → ℝ | MvPolynomial.eval z (Vpoly N) = 0} ∈
      S.Ω (F + 3 * N + 6) 1 (N + 1) :=
    WilG1.Omega.mono (S.hyp (N + 1) (Vpoly N)) (by omega) (Vpoly_totalDegree N)
  have hB2 : ({z : Fin (N + 1) → ℝ | Fin.init z ∈ (projLast A)ᶜ} ∩
      {z : Fin (N + 1) → ℝ | MvPolynomial.eval z (Vpoly N) = 0}) ∈
      S.Ω (F + 3 * N + 7) (D + 1) (N + 1) :=
    WilG1.Omega.mono (WilG0.Omega_inter2 hB2a hV) (by omega) (by omega)
  have hB2' : ({z : Fin (N + 1) → ℝ | Fin.init z ∈ (projLast A)ᶜ} ∩
      {z : Fin (N + 1) → ℝ | MvPolynomial.eval z (Vpoly N) = 0}) ∈
      S.Ω (F + 3 * N + 8) (D + 1) (N + 1) :=
    WilG1.Omega.mono hB2 (by omega) le_rfl
  -- the union of the two branches
  have hU : (projLast ({x : Fin (N + 2) → ℝ | x ∘ iota N ∈ A} ∩
      {x : Fin (N + 2) → ℝ | MvPolynomial.eval x (Hpoly N) = 0}) ∪
      ({z : Fin (N + 1) → ℝ | Fin.init z ∈ (projLast A)ᶜ} ∩
        {z : Fin (N + 1) → ℝ | MvPolynomial.eval z (Vpoly N) = 0})) ∈
      S.Ω (F + 3 * N + 8) (2 * D + 4) (N + 1) :=
    WilG1.Omega.mono (WilG0.Omega_union2 hB1 hB2') (by omega) (by omega)
  rw [← targetSet_eq N A]
  exact WilG1.Omega.mono hU (by omega) (by omega)

end

end Work.WilG4c
