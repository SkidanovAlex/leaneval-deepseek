/-
  WilG1/Choice/Blocks — index bookkeeping for the block spaces `Fin (p+1+k)` and the affine
  atoms used by the selection-membership proof `Work.WilG1.Choice.selSet_mem`.

  Conventions.  A point of `Fin (p+1+k)` is read as the base point `(l, t) ∈ ℝ^{p+1}` (the
  first `p` coordinates via `basePart`, the value coordinate `t` at `idxT p k`) together with
  `k` extra coordinates `idxE p k i`.  `up u` is the image of a coordinate of `Fin (p+1+k)`
  in the bigger space `Fin (p+1+(k+1))`.

  `AtomPN K u c`, `AtomMN K u c`, `AtomLL K c` are the sets of points of `Fin (p+1+(k+1))`
  whose associated point of `K` (base coordinates, last coordinate `w (up u) + w (last) + c`,
  `w (up u) - w (last) + c`, `w (last) + c`) lies in `K`; they are the specialisations of
  `affLast_mem`.  The `_snoc` lemmas evaluate them at a point `Fin.snoc y t`, and `ctr_mem`
  produces the set of points whose fibre is symmetric about a chosen coordinate.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG1.Choice.Helpers

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Choice

open WilkiesDesign WilkiesConjecture

/-! ## 1. Index bookkeeping -/

/-- The canonical proof that the `p` base coordinates fit into `Fin (p+1+k)`. -/
theorem le_base (p k : ℕ) : p ≤ p + 1 + k :=
  Nat.le_trans (Nat.le_succ p) (Nat.le_add_right (p + 1) k)

/-- Position of the base "value" coordinate in `Fin (p+1+k)`. -/
def idxT (p k : ℕ) : Fin (p + 1 + k) := Fin.castAdd k (Fin.last p)

/-- Position of the `i`-th extra coordinate in `Fin (p+1+k)`. -/
def idxE (p k : ℕ) (i : Fin k) : Fin (p + 1 + k) := Fin.natAdd (p + 1) i

/-- The base `p` coordinates of a point of `Fin (p+1+k)`. -/
def basePart {p k : ℕ} (y : Fin (p + 1 + k) → ℝ) : Fin p → ℝ :=
  fun i => y (Fin.castLE (le_base p k) i)

/-- The image of a coordinate of `Fin (p+1+k)` in the bigger space `Fin (p+1+(k+1))`. -/
def up {p k : ℕ} (u : Fin (p + 1 + k)) : Fin (p + 1 + (k + 1)) := Fin.castSucc u

theorem up_eq {p k : ℕ} (u : Fin (p + 1 + k)) : up u = Fin.castSucc u := rfl

theorem idxT_zero (p : ℕ) : idxT p 0 = Fin.last p := Fin.ext rfl
theorem idxT_one (p : ℕ) : idxT p 1 = Fin.castSucc (Fin.last p) := Fin.ext rfl
theorem idxT_two (p : ℕ) : idxT p 2 = Fin.castSucc (Fin.castSucc (Fin.last p)) := Fin.ext rfl
theorem idxE_one_zero (p : ℕ) : idxE p 1 (0 : Fin 1) = Fin.last (p + 1) := Fin.ext rfl
theorem idxE_two_zero (p : ℕ) : idxE p 2 (0 : Fin 2) = Fin.castSucc (Fin.last (p + 1)) := Fin.ext rfl
theorem idxE_two_one (p : ℕ) : idxE p 2 (1 : Fin 2) = Fin.last (p + 2) := Fin.ext rfl

theorem basePart_self {p : ℕ} (y : Fin (p + 1) → ℝ) : basePart (k := 0) y = Fin.init y := by
  funext i
  show y (Fin.castLE (le_base p 0) i) = Fin.init y i
  rw [show Fin.castLE (le_base p 0) i = Fin.castSucc i from Fin.ext rfl]
  rfl

theorem basePart_snoc {p k : ℕ} (y : Fin (p + 1 + k) → ℝ) (t : ℝ) :
    basePart (k := k + 1) (Fin.snoc y t) = basePart (k := k) y := by
  funext i
  show (Fin.snoc y t : Fin (p + 1 + k + 1) → ℝ) (Fin.castLE (le_base p (k + 1)) i) =
    y (Fin.castLE (le_base p k) i)
  rw [show Fin.castLE (le_base p (k + 1)) i = Fin.castSucc (Fin.castLE (le_base p k) i) from
    Fin.ext rfl]
  rw [Fin.snoc_castSucc]

/-- Evaluation of a `Fin.snoc` point at a `up`-coordinate. -/
theorem snoc_up {p k : ℕ} (y : Fin (p + 1 + k) → ℝ) (t : ℝ) (u : Fin (p + 1 + k)) :
    (Fin.snoc y t : Fin (p + 1 + k + 1) → ℝ) (up u) = y u := by
  rw [up_eq, Fin.snoc_castSucc]

/-- Evaluation of a `Fin.snoc` point at the fresh coordinate. -/
theorem snoc_last {p k : ℕ} (y : Fin (p + 1 + k) → ℝ) (t : ℝ) :
    (Fin.snoc y t : Fin (p + 1 + k + 1) → ℝ) (Fin.last (p + 1 + k)) = t := by
  rw [Fin.snoc_last]

theorem basePart_snoc_zero {p : ℕ} (z : Fin (p + 1) → ℝ) (s : ℝ) :
    basePart (k := 1) (Fin.snoc z s) = Fin.init z := by
  have h := basePart_snoc (p := p) (k := 0) z s
  rw [h, basePart_self]

theorem basePart_snoc_snoc {p : ℕ} (z : Fin (p + 1) → ℝ) (c c' : ℝ) :
    basePart (k := 2) (Fin.snoc (Fin.snoc z c) c') = Fin.init z := by
  have h1 := basePart_snoc (p := p) (k := 1) (Fin.snoc z c) c'
  have h2 := basePart_snoc (p := p) (k := 0) z c
  rw [h1, h2, basePart_self]

theorem snoc_snoc_idxT {p : ℕ} (z : Fin (p + 1) → ℝ) (c c' : ℝ) :
    (Fin.snoc (Fin.snoc z c) c' : Fin (p + 1 + 2) → ℝ) (idxT p 2) = z (Fin.last p) := by
  rw [show idxT p 2 = Fin.castSucc (Fin.castSucc (Fin.last p)) from idxT_two p,
    Fin.snoc_castSucc, Fin.snoc_castSucc]

theorem snoc_snoc_idxE0 {p : ℕ} (z : Fin (p + 1) → ℝ) (c c' : ℝ) :
    (Fin.snoc (Fin.snoc z c) c' : Fin (p + 1 + 2) → ℝ) (idxE p 2 (0 : Fin 2)) = c := by
  rw [show idxE p 2 (0 : Fin 2) = Fin.castSucc (Fin.last (p + 1)) from idxE_two_zero p,
    Fin.snoc_castSucc, Fin.snoc_last]

theorem snoc_snoc_idxE1 {p : ℕ} (z : Fin (p + 1) → ℝ) (c c' : ℝ) :
    (Fin.snoc (Fin.snoc z c) c' : Fin (p + 1 + 2) → ℝ) (idxE p 2 (1 : Fin 2)) = c' := by
  rw [show idxE p 2 (1 : Fin 2) = Fin.last (p + 2) from idxE_two_one p, Fin.snoc_last]

theorem snoc_idxT' {p : ℕ} (z : Fin (p + 1) → ℝ) (s : ℝ) :
    (Fin.snoc z s : Fin (p + 1 + 1) → ℝ) (idxT p 1) = z (Fin.last p) := by
  rw [show idxT p 1 = Fin.castSucc (Fin.last p) from idxT_one p, Fin.snoc_castSucc]

theorem snoc_idxE1_zero {p : ℕ} (z : Fin (p + 1) → ℝ) (s : ℝ) :
    (Fin.snoc z s : Fin (p + 1 + 1) → ℝ) (idxE p 1 (0 : Fin 1)) = s := by
  rw [show idxE p 1 (0 : Fin 1) = Fin.last (p + 1) from idxE_one_zero p, Fin.snoc_last]

/-! ## 2. The canonical atoms over `Fin (p+1+k)` -/

theorem atom_one {S : SOMin} {p k : ℕ} {a D : ℕ} {b : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} (hK : K ∈ S.Ω a (b.eval D) (p + 1))
    (u : Fin (p + 1 + k)) (c : ℝ) :
    {y : Fin (p + 1 + k) → ℝ | Fin.snoc (basePart y) (y u + c) ∈ K} ∈
      S.Ω (max (a + (p + 1 + k)) ((p + 1 + k) + (p + 1)) + 1 + (p + 1))
        ((b + Polynomial.C 2).eval D) (p + 1 + k) := by
  have h := affLast_one (S := S) (le_base p k) hK u c
  have he : {y : Fin (p + 1 + k) → ℝ |
        Fin.snoc (fun i : Fin p => y (Fin.castLE (le_base p k) i)) (y u + c) ∈ K} =
      {y : Fin (p + 1 + k) → ℝ | Fin.snoc (basePart y) (y u + c) ∈ K} := rfl
  rwa [he] at h

theorem atom_add {S : SOMin} {p k : ℕ} {a D : ℕ} {b : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} (hK : K ∈ S.Ω a (b.eval D) (p + 1))
    (u v : Fin (p + 1 + k)) (c : ℝ) :
    {y : Fin (p + 1 + k) → ℝ | Fin.snoc (basePart y) (y u + y v + c) ∈ K} ∈
      S.Ω (max (a + (p + 1 + k)) ((p + 1 + k) + (p + 1)) + 1 + (p + 1))
        ((b + Polynomial.C 2).eval D) (p + 1 + k) := by
  have h := affLast_add (S := S) (le_base p k) hK u v c
  have he : {y : Fin (p + 1 + k) → ℝ |
        Fin.snoc (fun i : Fin p => y (Fin.castLE (le_base p k) i)) (y u + y v + c) ∈ K} =
      {y : Fin (p + 1 + k) → ℝ | Fin.snoc (basePart y) (y u + y v + c) ∈ K} := rfl
  rwa [he] at h

theorem atom_sub {S : SOMin} {p k : ℕ} {a D : ℕ} {b : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} (hK : K ∈ S.Ω a (b.eval D) (p + 1))
    (u v : Fin (p + 1 + k)) (c : ℝ) :
    {y : Fin (p + 1 + k) → ℝ | Fin.snoc (basePart y) (y u - y v + c) ∈ K} ∈
      S.Ω (max (a + (p + 1 + k)) ((p + 1 + k) + (p + 1)) + 1 + (p + 1))
        ((b + Polynomial.C 2).eval D) (p + 1 + k) := by
  have h := affLast_sub (S := S) (le_base p k) hK u v c
  have he : {y : Fin (p + 1 + k) → ℝ |
        Fin.snoc (fun i : Fin p => y (Fin.castLE (le_base p k) i)) (y u - y v + c) ∈ K} =
      {y : Fin (p + 1 + k) → ℝ | Fin.snoc (basePart y) (y u - y v + c) ∈ K} := rfl
  rwa [he] at h

/-! ## 3. The affine atoms over the bigger space -/

/-- The atom `w ↦ (base coordinates of `w`, `w (up u) + w (last) + c`) ∈ K`. -/
def AtomPN {p k : ℕ} (K : Set (Fin (p + 1) → ℝ)) (u : Fin (p + 1 + k)) (c : ℝ) :
    Set (Fin (p + 1 + (k + 1)) → ℝ) :=
  {w | Fin.snoc (basePart w) (w (up u) + w (Fin.last (p + 1 + k)) + c) ∈ K}

/-- The atom `w ↦ (base coordinates of `w`, `w (up u) - w (last) + c`) ∈ K`. -/
def AtomMN {p k : ℕ} (K : Set (Fin (p + 1) → ℝ)) (u : Fin (p + 1 + k)) (c : ℝ) :
    Set (Fin (p + 1 + (k + 1)) → ℝ) :=
  {w | Fin.snoc (basePart w) (w (up u) - w (Fin.last (p + 1 + k)) + c) ∈ K}

/-- The atom `w ↦ (base coordinates of `w`, `w (last) + c`) ∈ K`. -/
def AtomLL {p k : ℕ} (K : Set (Fin (p + 1) → ℝ)) (c : ℝ) :
    Set (Fin (p + 1 + (k + 1)) → ℝ) :=
  {w | Fin.snoc (basePart w) (w (Fin.last (p + 1 + k)) + c) ∈ K}

theorem AtomPN_mem {S : SOMin} {p k : ℕ} {a D : ℕ} {b : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} (hK : K ∈ S.Ω a (b.eval D) (p + 1))
    (u : Fin (p + 1 + k)) (c : ℝ) :
    AtomPN K u c ∈
      S.Ω (max (a + (p + 1 + (k + 1))) ((p + 1 + (k + 1)) + (p + 1)) + 1 + (p + 1))
        ((b + Polynomial.C 2).eval D) (p + 1 + (k + 1)) :=
  atom_add (S := S) (k := k + 1) hK (up u) (Fin.last (p + 1 + k)) c

theorem AtomMN_mem {S : SOMin} {p k : ℕ} {a D : ℕ} {b : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} (hK : K ∈ S.Ω a (b.eval D) (p + 1))
    (u : Fin (p + 1 + k)) (c : ℝ) :
    AtomMN K u c ∈
      S.Ω (max (a + (p + 1 + (k + 1))) ((p + 1 + (k + 1)) + (p + 1)) + 1 + (p + 1))
        ((b + Polynomial.C 2).eval D) (p + 1 + (k + 1)) :=
  atom_sub (S := S) (k := k + 1) hK (up u) (Fin.last (p + 1 + k)) c

theorem AtomLL_mem {S : SOMin} {p k : ℕ} {a D : ℕ} {b : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} (hK : K ∈ S.Ω a (b.eval D) (p + 1)) (c : ℝ) :
    AtomLL (p := p) (k := k) K c ∈
      S.Ω (max (a + (p + 1 + (k + 1))) ((p + 1 + (k + 1)) + (p + 1)) + 1 + (p + 1))
        ((b + Polynomial.C 2).eval D) (p + 1 + (k + 1)) :=
  atom_one (S := S) (k := k + 1) hK (Fin.last (p + 1 + k)) c

theorem AtomPN_snoc {p k : ℕ} {K : Set (Fin (p + 1) → ℝ)} (u : Fin (p + 1 + k)) (c : ℝ)
    (y : Fin (p + 1 + k) → ℝ) (t : ℝ) :
    ((Fin.snoc y t : Fin (p + 1 + (k + 1)) → ℝ) ∈ AtomPN K u c) ↔
      Fin.snoc (basePart y) (y u + t + c) ∈ K := by
  show Fin.snoc (basePart (k := k + 1) (Fin.snoc y t : Fin (p + 1 + k + 1) → ℝ))
      ((Fin.snoc y t : Fin (p + 1 + k + 1) → ℝ) (up u) +
        (Fin.snoc y t : Fin (p + 1 + k + 1) → ℝ) (Fin.last (p + 1 + k)) + c) ∈ K ↔
    Fin.snoc (basePart y) (y u + t + c) ∈ K
  rw [basePart_snoc y t, snoc_up y t u, snoc_last y t]

theorem AtomMN_snoc {p k : ℕ} {K : Set (Fin (p + 1) → ℝ)} (u : Fin (p + 1 + k)) (c : ℝ)
    (y : Fin (p + 1 + k) → ℝ) (t : ℝ) :
    ((Fin.snoc y t : Fin (p + 1 + (k + 1)) → ℝ) ∈ AtomMN K u c) ↔
      Fin.snoc (basePart y) (y u - t + c) ∈ K := by
  show Fin.snoc (basePart (k := k + 1) (Fin.snoc y t : Fin (p + 1 + k + 1) → ℝ))
      ((Fin.snoc y t : Fin (p + 1 + k + 1) → ℝ) (up u) -
        (Fin.snoc y t : Fin (p + 1 + k + 1) → ℝ) (Fin.last (p + 1 + k)) + c) ∈ K ↔
    Fin.snoc (basePart y) (y u - t + c) ∈ K
  rw [basePart_snoc y t, snoc_up y t u, snoc_last y t]

theorem AtomLL_snoc {p k : ℕ} {K : Set (Fin (p + 1) → ℝ)} (c : ℝ)
    (y : Fin (p + 1 + k) → ℝ) (t : ℝ) :
    ((Fin.snoc y t : Fin (p + 1 + (k + 1)) → ℝ) ∈ AtomLL (p := p) (k := k) K c) ↔
      Fin.snoc (basePart y) (t + c) ∈ K := by
  show Fin.snoc (basePart (k := k + 1) (Fin.snoc y t : Fin (p + 1 + k + 1) → ℝ))
      ((Fin.snoc y t : Fin (p + 1 + k + 1) → ℝ) (Fin.last (p + 1 + k)) + c) ∈ K ↔
    Fin.snoc (basePart y) (t + c) ∈ K
  rw [basePart_snoc y t, snoc_last y t]

/-! ## 4. The set of points whose fibre is symmetric about a coordinate -/

theorem ctr_mem {S : SOMin} {p k : ℕ} {a D : ℕ} {b : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} (hK : K ∈ S.Ω a (b.eval D) (p + 1))
    (u : Fin (p + 1 + k)) :
    {y : Fin (p + 1 + k) → ℝ | ∀ t : ℝ,
      (Fin.snoc (basePart y) (y u + t) ∈ K ↔ Fin.snoc (basePart y) (y u - t) ∈ K)} ∈
      S.Ω (max (a + (p + 1 + (k + 1))) ((p + 1 + (k + 1)) + (p + 1)) + 1 + (p + 1) + 5)
        ((Polynomial.C 4 * b + Polynomial.C 8).eval D) (p + 1 + k) := by
  have hP : AtomPN K u 0 ∈
      S.Ω (max (a + (p + 1 + (k + 1))) ((p + 1 + (k + 1)) + (p + 1)) + 1 + (p + 1))
        ((b + Polynomial.C 2).eval D) (p + 1 + (k + 1)) := AtomPN_mem (S := S) hK u 0
  have hM : AtomMN K u 0 ∈
      S.Ω (max (a + (p + 1 + (k + 1))) ((p + 1 + (k + 1)) + (p + 1)) + 1 + (p + 1))
        ((b + Polynomial.C 2).eval D) (p + 1 + (k + 1)) := AtomMN_mem (S := S) hK u 0
  have hΘ : ((AtomPN K u 0)ᶜ ∪ AtomMN K u 0) ∩ ((AtomMN K u 0)ᶜ ∪ AtomPN K u 0) ∈
      S.Ω (max (a + (p + 1 + (k + 1))) ((p + 1 + (k + 1)) + (p + 1)) + 1 + (p + 1) + 2)
        ((Polynomial.C 4 * b + Polynomial.C 8).eval D) (p + 1 + (k + 1)) := by
    have h1 := union2_mem (S := S) (S.compl hP) hM
    have h2 := union2_mem (S := S) (S.compl hM) hP
    have h3 := inter2_mem (S := S) h1 h2
    refine Omega.mono h3 (by simp only [max_self]; omega) ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hW := forall_mem (S := S) hΘ
  have he : {y : Fin (p + 1 + k) → ℝ |
        ∀ t : ℝ, (Fin.snoc y t : Fin (p + 1 + (k + 1)) → ℝ) ∈ ((AtomPN K u 0)ᶜ ∪ AtomMN K u 0) ∩
          ((AtomMN K u 0)ᶜ ∪ AtomPN K u 0)} =
      {y : Fin (p + 1 + k) → ℝ | ∀ t : ℝ,
        (Fin.snoc (basePart y) (y u + t) ∈ K ↔ Fin.snoc (basePart y) (y u - t) ∈ K)} := by
    ext y
    refine forall_congr' (fun t => ?_)
    rw [Set.mem_inter_iff, Set.mem_union, Set.mem_union, Set.mem_compl_iff, Set.mem_compl_iff,
      AtomPN_snoc (K := K) u 0 y t, AtomMN_snoc (K := K) u 0 y t]
    simp only [add_zero, sub_zero]
    tauto
  rw [← he]
  exact hW

end Work.WilG1.Choice
