/-
  WilG4c — patching a family by a constant outside an `Ω`-definable parameter set.

  `IteFamGraphMem` is the `Ω`-membership input of the "cut a family down to a definable
  parameter set `Λ`" step: if the graph of the family member `F i` is `Ω F0 D`-bounded and
  `Λ` is `Ω aΛ dP`, then the member `G i` which agrees with `F i` on `Λ` and is the constant
  `c` outside `Λ` has an `Ω`-bounded graph, with format and degree growing **additively** in
  `F0`, `aΛ`, `D`, `dP`.

  The mathematical content is the set identity

    `famGraph (G i) = (famGraph (F i) ∩ A) ∪ (Aᶜ ∩ H)`,

  where `A = {z | Fin.init z ∈ parSet p (n+1) Λ}` is the parameter condition (the first `p`
  coordinates of `z` lie in `Λ`) and `H = {z | z (last) = c}` is the value hyperplane.  Each
  of `famGraph (F i)` and `A` is used exactly once, so the degrees add; `A` is a coordinate
  substitution (`Work.WilG4c.Subst`), hence linear in `aΛ`, and `H` is a single hypersurface.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG4c.Subst
import Submission.Work.WilG0.API

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The parameter condition as an `Ω`-set -/

/-- The pullback of `Λ ⊆ ℝ^p` to `ℝ^{p+m}`: the points whose first `p` coordinates lie in
`Λ`.  It is the coordinate substitution `Subst` along `i ↦ Fin.castAdd m i`. -/
def parSet (p m : ℕ) (Λ : Set (Fin p → ℝ)) : Set (Fin (p + m) → ℝ) :=
  {w | w ∘ (fun i : Fin p => Fin.castAdd m i) ∈ Λ}

@[simp] theorem mem_parSet {p m : ℕ} {Λ : Set (Fin p → ℝ)} {w : Fin (p + m) → ℝ} :
    w ∈ parSet p m Λ ↔ (fun i : Fin p => w (Fin.castAdd m i)) ∈ Λ :=
  Iff.rfl

/-- `parSet` preserves `Ω`-membership: it is a coordinate substitution, so the format grows
by the (linear) `Subst` bound and the degree by `2`. -/
theorem parSet_mem (S : SOMin) {p m F D : ℕ} {Λ : Set (Fin p → ℝ)}
    (hΛ : Λ ∈ S.Ω F D p) :
    parSet p m Λ ∈ S.Ω (max (F + (p + m)) ((p + m) + p) + 1 + p) (D + 2) (p + m) :=
  Subst S (fun i : Fin p => Fin.castAdd m i) hΛ

/-! ## 2. Reading `famGraph` in coordinates -/

/-- Membership in `famGraph h`, in the coordinates `(l, t, u)` of `ℝ^{p+m+1}`: `l` is the
first `p` coordinates (read through `Fin.init`), `t` the following `m` ones, and `u` the last
coordinate carries the value. -/
theorem mem_famGraph_coords {p m : ℕ} (h : (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
    (z : Fin (p + m + 1) → ℝ) :
    z ∈ famGraph h ↔
      z (Fin.last (p + m)) = h (fun i : Fin p => (Fin.init z) (Fin.castAdd m i))
        (fun j : Fin m => (Fin.init z) (Fin.natAdd p j)) := by
  simp only [famGraph, graphOf, Set.mem_ofPred_eq]

/-! ## 3. The value hyperplane -/

/-- The hyperplane `{z | z (last) = c}` in `ℝ^{N+1}` is `Ω (N+1) 1`-bounded (the zero set of
one polynomial of total degree `1`). -/
theorem lastCoord_eq_mem (S : SOMin) (N : ℕ) (c : ℝ) :
    {z : Fin (N + 1) → ℝ | z (Fin.last N) = c} ∈ S.Ω (N + 1) 1 (N + 1) := by
  have h := S.hyp (N + 1)
    (MvPolynomial.X (Fin.last N) - MvPolynomial.C c : MvPolynomial (Fin (N + 1)) ℝ)
  have hset : {x : Fin (N + 1) → ℝ | MvPolynomial.eval x
        (MvPolynomial.X (Fin.last N) - MvPolynomial.C c : MvPolynomial (Fin (N + 1)) ℝ) = 0}
      = {z : Fin (N + 1) → ℝ | z (Fin.last N) = c} := by
    ext z
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C, sub_eq_zero]
  rw [hset] at h
  refine Work.WilG0.Omega_mono_D (S := S) ?_ h
  exact le_trans (MvPolynomial.totalDegree_sub_C_le (MvPolynomial.X (Fin.last N)) c)
    (le_of_eq (MvPolynomial.totalDegree_X (Fin.last N)))

/-! ## 4. The set identity -/

/-- **The set identity.**  If `g` agrees with `f` on the parameter set `Λ` and equals the
constant `c` outside `Λ`, then the graph of `g` is the graph of `f` restricted to `Λ`,
together with the value hyperplane `u = c` over the complement of `Λ`. -/
theorem famGraph_ite_eq {p m : ℕ} (Λ : Set (Fin p → ℝ)) (c : ℝ)
    (f g : (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
    (hfg : ∀ l t, l ∈ Λ → g l t = f l t)
    (hgc : ∀ l t, l ∉ Λ → g l t = c) :
    famGraph g =
      (famGraph f ∩ {z : Fin (p + m + 1) → ℝ | Fin.init z ∈ parSet p m Λ}) ∪
        (({z : Fin (p + m + 1) → ℝ | Fin.init z ∈ parSet p m Λ})ᶜ ∩
          {z : Fin (p + m + 1) → ℝ | z (Fin.last (p + m)) = c}) := by
  ext z
  rw [mem_famGraph_coords g z]
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq,
    mem_parSet, mem_famGraph_coords f z]
  by_cases hl : (fun i : Fin p => (Fin.init z) (Fin.castAdd m i)) ∈ Λ
  · have key : g (fun i : Fin p => (Fin.init z) (Fin.castAdd m i))
        (fun j : Fin m => (Fin.init z) (Fin.natAdd p j))
        = f (fun i : Fin p => (Fin.init z) (Fin.castAdd m i))
          (fun j : Fin m => (Fin.init z) (Fin.natAdd p j)) := hfg _ _ hl
    rw [key]
    simp [hl]
  · have key : g (fun i : Fin p => (Fin.init z) (Fin.castAdd m i))
        (fun j : Fin m => (Fin.init z) (Fin.natAdd p j)) = c := hgc _ _ hl
    rw [key]
    simp [hl]

/-! ## 5. The `Ω`-membership -/

theorem IteFamGraphMem (S : WilkiesDesign.SOMin) {p n k : ℕ} (Λ : Set (Fin p → ℝ)) (c : ℝ)
    (F G : Work.WilkG4c.Family k p (n + 1)) (i : Fin k) (aΛ dP F0 D : ℕ)
    (hΛ : Λ ∈ S.Ω aΛ dP p)
    (hF : WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1))
    (hG : ∀ l t, l ∈ Λ → G i l t = F i l t)
    (hGc : ∀ l t, l ∉ Λ → G i l t = c) :
    WilkiesDesign.CG.famGraph (G i) ∈
      S.Ω (F0 + aΛ + 3 * (p + (n + 1) + 1) + 3 * p + 6) (D + 2 * dP + 5)
        (p + (n + 1) + 1) := by
  rw [famGraph_ite_eq (m := n + 1) Λ c (F i) (G i) hG hGc]
  -- the parameter set, in the coordinates of `famGraph`
  have hA0 : parSet p (n + 1) Λ ∈
      S.Ω (max (aΛ + (p + (n + 1))) ((p + (n + 1)) + p) + 1 + p) (dP + 2) (p + (n + 1)) :=
    parSet_mem S hΛ
  have hA1 : {z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ parSet p (n + 1) Λ} ∈
      S.Ω (max (aΛ + (p + (n + 1))) ((p + (n + 1)) + p) + 1 + p + 1) (dP + 2)
        (p + (n + 1) + 1) :=
    S.prod_right hA0
  -- a common format for the four pieces
  have hF' : famGraph (F i) ∈
      S.Ω (F0 + aΛ + 3 * (p + (n + 1) + 1) + 3 * p + 4) D (p + (n + 1) + 1) :=
    Work.WilG0.Omega_mono_F (by omega) hF
  have hA' : {z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ parSet p (n + 1) Λ} ∈
      S.Ω (F0 + aΛ + 3 * (p + (n + 1) + 1) + 3 * p + 4) (dP + 2) (p + (n + 1) + 1) := by
    refine Work.WilG0.Omega_mono_F ?_ hA1
    have hm : max (aΛ + (p + (n + 1))) ((p + (n + 1)) + p) ≤
        (aΛ + (p + (n + 1))) + ((p + (n + 1)) + p) :=
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    omega
  have hAc' : ({z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ parSet p (n + 1) Λ})ᶜ ∈
      S.Ω (F0 + aΛ + 3 * (p + (n + 1) + 1) + 3 * p + 4) (dP + 2) (p + (n + 1) + 1) := by
    refine Work.WilG0.Omega_mono_F ?_ (S.compl hA1)
    have hm : max (aΛ + (p + (n + 1))) ((p + (n + 1)) + p) ≤
        (aΛ + (p + (n + 1))) + ((p + (n + 1)) + p) :=
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    omega
  have hH : {z : Fin (p + (n + 1) + 1) → ℝ | z (Fin.last (p + (n + 1))) = c} ∈
      S.Ω (F0 + aΛ + 3 * (p + (n + 1) + 1) + 3 * p + 4) 1 (p + (n + 1) + 1) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega) (lastCoord_eq_mem S (p + (n + 1)) c)
  -- the two intersections and the union
  have hI1 : famGraph (F i) ∩
      {z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ parSet p (n + 1) Λ} ∈
      S.Ω (F0 + aΛ + 3 * (p + (n + 1) + 1) + 3 * p + 5) (D + (dP + 2)) (p + (n + 1) + 1) :=
    Work.WilG0.Omega_inter2 hF' hA'
  have hI2 : ({z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ parSet p (n + 1) Λ})ᶜ ∩
      {z : Fin (p + (n + 1) + 1) → ℝ | z (Fin.last (p + (n + 1))) = c} ∈
      S.Ω (F0 + aΛ + 3 * (p + (n + 1) + 1) + 3 * p + 5) ((dP + 2) + 1)
        (p + (n + 1) + 1) :=
    Work.WilG0.Omega_inter2 hAc' hH
  have hU : (famGraph (F i) ∩
      {z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ parSet p (n + 1) Λ}) ∪
      (({z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ parSet p (n + 1) Λ})ᶜ ∩
        {z : Fin (p + (n + 1) + 1) → ℝ | z (Fin.last (p + (n + 1))) = c}) ∈
      S.Ω (F0 + aΛ + 3 * (p + (n + 1) + 1) + 3 * p + 5)
        ((D + (dP + 2)) + ((dP + 2) + 1)) (p + (n + 1) + 1) :=
    Work.WilG0.Omega_union2 hI1 hI2
  exact Work.WilG0.Omega_mono_FD (by omega) (by omega) hU

end Work.WilG4c
