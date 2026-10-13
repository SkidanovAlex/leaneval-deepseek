import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.Defs
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical

namespace Work.WilG1.Calc

open WilkiesDesign Work.WilG0

/-!
# The interior of an `Ω`-set is an `Ω`-set

`Work.WilG1.Calc.interior_mem`: if `X ∈ S.Ω a (b.eval D) n` then
`interior X ∈ S.Ω (a + 3n + 42) ((12·b + 60).eval D) n`.

The proof is the standard first-order manipulation of the `Ω`-calculus, made explicit.
For a set `X ⊆ ℝⁿ`,

`interior X = {x | ∃ r > 0, ∀ y, ‖y - x‖² < r² → y ∈ X}`,

where `‖y - x‖² = Σᵢ (yᵢ - xᵢ)²` is a *single* polynomial of total degree `2` (this is the point
of the sum-of-squares form: it keeps the degree independent of `n`, unlike an intersection of the
`n` coordinate inequalities). Writing the universal quantifier as a double complement and the two
existential quantifiers as two projections, the construction is

* `Xᶜ ∈ Ω (a+1)`,
* pull it back to `ℝ^{(n+1)+n}` (coordinates `(x,r)` followed by `y`) — format `+ (n+1)`,
* intersect with the positive locus of `r² - Σ(yᵢ-xᵢ)²` (format `2n+3`, degree `4`),
* project out the `n` `y`-coordinates (format `+ n`), complement (format `+ 1`),
* intersect with `{r > 0}` (format `n+3`, degree `3`),
* project out `r` (format `+ 1`).

The total format is `max (a + 2n + 6) (3n + 7) ≤ a + 3n + 42` and the degree `b + 7 ≤ 12b + 60`.
-/

/-! ## Auxiliary closure properties of the `Ω`-calculus -/

/-- Membership in the transport of a set along an equality of dimensions. -/
private theorem cast_mem_iff' {a b : ℕ} (h : a = b) {X : Set (Fin a → ℝ)} (z : Fin b → ℝ) :
    z ∈ (h ▸ X) ↔ (fun i : Fin a => z (Fin.cast h i)) ∈ X := by
  subst h; rfl

/-- Transport of an `Ω`-set along an equality of ambient dimensions. -/
private theorem omega_cast' {S : SOMin} {a b F D : ℕ} (h : a = b) {X : Set (Fin a → ℝ)}
    (hX : X ∈ S.Ω F D a) : (h ▸ X) ∈ S.Ω F D b := by
  subst h; exact hX

/-- The positivity set of a polynomial is `Ω`-definable: for reals
`0 < c ↔ ∃ t, t² · c = 1`, so `{P > 0}` is the projection of the hypersurface cut out by
`X_last² · P - 1`, of total degree `P.totalDegree + 2`. -/
private theorem pos_mem_aux {S : SOMin} {m : ℕ} (D : ℕ) (P : MvPolynomial (Fin m) ℝ) :
    {x : Fin m → ℝ | 0 < MvPolynomial.eval x P} ∈
      S.Ω (m + 2) ((Polynomial.C (P.totalDegree + 2)).eval D) m := by
  set Q : MvPolynomial (Fin (m+1)) ℝ :=
    MvPolynomial.X (Fin.last m) ^ 2 * MvPolynomial.rename Fin.castSucc P - 1 with hQdef
  have htd : Q.totalDegree ≤ P.totalDegree + 2 := by
    rw [hQdef]
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : (MvPolynomial.rename Fin.castSucc P :
          MvPolynomial (Fin (m+1)) ℝ).totalDegree ≤ P.totalDegree :=
        MvPolynomial.totalDegree_rename_le _ _
      have h2 : (MvPolynomial.X (Fin.last m) ^ 2 :
          MvPolynomial (Fin (m+1)) ℝ).totalDegree ≤ 2 := by
        calc (MvPolynomial.X (Fin.last m) ^ 2 : MvPolynomial (Fin (m+1)) ℝ).totalDegree
            ≤ 2 * (MvPolynomial.X (Fin.last m) : MvPolynomial (Fin (m+1)) ℝ).totalDegree :=
              MvPolynomial.totalDegree_pow _ 2
          _ = 2 * 1 := by rw [MvPolynomial.totalDegree_X]
          _ = 2 := by norm_num
      omega
    · rw [MvPolynomial.totalDegree_one]; omega
  have h0 : {z : Fin (m+1) → ℝ | MvPolynomial.eval z Q = 0} ∈
      S.Ω (m+1) ((Polynomial.C Q.totalDegree).eval D) (m+1) :=
    Omega.hyp_mem (S := S) D Q
  have h1 : {z : Fin (m+1) → ℝ | MvPolynomial.eval z Q = 0} ∈
      S.Ω (m+1) ((Polynomial.C (P.totalDegree + 2)).eval D) (m+1) :=
    Omega.mono h0 le_rfl (by simpa [Polynomial.eval_C] using htd)
  have h2 : projLast {z : Fin (m+1) → ℝ | MvPolynomial.eval z Q = 0} ∈
      S.Ω (m+2) ((Polynomial.C (P.totalDegree + 2)).eval D) m :=
    Omega.projLast_mem (S := S) (n := m) (b := Polynomial.C (P.totalDegree + 2)) (D := D) h1
  have hset : projLast {z : Fin (m+1) → ℝ | MvPolynomial.eval z Q = 0}
      = {x : Fin m → ℝ | 0 < MvPolynomial.eval x P} := by
    ext x
    simp only [hQdef, projLast, Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
      MvPolynomial.eval_pow, MvPolynomial.eval_X, MvPolynomial.eval_rename, Fin.snoc_last, map_one]
    have hev : ∀ t : ℝ,
        MvPolynomial.eval (Fin.snoc x t ∘ Fin.castSucc) P = MvPolynomial.eval x P := by
      intro t
      have hfun : (Fin.snoc x t ∘ Fin.castSucc : Fin m → ℝ) = x := by
        funext i
        simp [Function.comp_apply, Fin.snoc_castSucc]
      rw [hfun]
    simp only [hev]
    constructor
    · rintro ⟨t, ht⟩
      nlinarith [sq_nonneg t]
    · intro h
      refine ⟨(Real.sqrt (MvPolynomial.eval x P))⁻¹, ?_⟩
      have hs : (Real.sqrt (MvPolynomial.eval x P)) ^ 2 = MvPolynomial.eval x P :=
        Real.sq_sqrt (le_of_lt h)
      have hne : MvPolynomial.eval x P ≠ 0 := ne_of_gt h
      rw [inv_pow, hs, inv_mul_cancel₀ hne]
      norm_num
  rw [hset] at h2
  exact h2

private theorem cast_addNat_eq_natAdd (n m : ℕ) (j : Fin m) :
    Fin.cast (Nat.add_comm m n) (Fin.addNat j n) = Fin.natAdd n j := by
  ext
  simp only [Fin.val_cast, Fin.val_addNat, Fin.val_natAdd]
  exact Nat.add_comm _ _

/-- Iterating `SOMin.prod_left` `n` times prepends `n` free coordinates to `A`, producing a set
in dimension `m + n` with the `A`-block in the last `m` coordinates. -/
private theorem liftMN_aux {S : SOMin} {m F D : ℕ} {A : Set (Fin m → ℝ)}
    (hA : A ∈ S.Ω F D m) (n : ℕ) : liftMN n m A ∈ S.Ω (F + n) D (m + n) := by
  induction n with
  | zero =>
    have h0 : liftMN 0 m A = A := by ext z; simp [liftMN]
    rw [h0]
    simpa using hA
  | succ n ih =>
    have hz : liftMN (n+1) m A
        = {z : Fin (m+(n+1)) → ℝ | Fin.tail z ∈ liftMN n m A} := by
      apply Set.ext
      intro z
      have hfun : (fun j : Fin m => (Fin.tail z) (Fin.addNat j n))
          = (fun j : Fin m => z (Fin.addNat j (n+1))) := by
        funext j; rfl
      show ((fun j : Fin m => z (Fin.addNat j (n+1))) ∈ A) ↔
           ((fun j : Fin m => (Fin.tail z) (Fin.addNat j n)) ∈ A)
      rw [hfun]
    rw [hz]
    exact S.prod_left ih

private theorem liftNM_eq_liftMN_cast (n m : ℕ) (A : Set (Fin m → ℝ)) :
    liftNM n m A = (Nat.add_comm m n) ▸ liftMN n m A := by
  apply Set.ext
  intro z
  rw [cast_mem_iff']
  simp only [liftNM, liftMN, Set.mem_setOf_eq]
  have hfun : (fun j : Fin m => z (Fin.cast (Nat.add_comm m n) (Fin.addNat j n)))
      = (fun j : Fin m => z (Fin.natAdd n j)) := by
    funext j
    rw [cast_addNat_eq_natAdd]
  rw [hfun]

/-- `Dset` placed in the last `m` coordinates of `ℝ^{k+m}` (first `k` free) is in `Ω`. -/
private theorem liftNM_mem_aux {S : SOMin} {m : ℕ} {F D : ℕ} {Dset : Set (Fin m → ℝ)}
    (hD : Dset ∈ S.Ω F D m) (k : ℕ) :
    {z : Fin (k + m) → ℝ | (fun j : Fin m => z (Fin.natAdd k j)) ∈ Dset} ∈
      S.Ω (F + k) D (k + m) := by
  have h1 : liftMN k m Dset ∈ S.Ω (F + k) D (m + k) := liftMN_aux hD k
  have h2 : (Nat.add_comm m k) ▸ liftMN k m Dset ∈ S.Ω (F + k) D (k + m) :=
    omega_cast' (Nat.add_comm m k) h1
  rwa [← liftNM_eq_liftMN_cast k m Dset] at h2

/-- Iterating `SOMin.proj` `m` times eliminates the last `m` coordinates, costing `+m` format
and preserving the degree. -/
private theorem projLastIter_mem_aux {S : SOMin} (k m : ℕ) {F D : ℕ}
    {X : Set (Fin (k + m) → ℝ)} (hX : X ∈ S.Ω F D (k + m)) :
    projLastIter k m X ∈ S.Ω (F + m) D k := by
  have key : ∀ m (F D : ℕ) (X : Set (Fin (k + m) → ℝ)),
      X ∈ S.Ω F D (k + m) → projLastIter k m X ∈ S.Ω (F + m) D k := by
    intro m
    induction m with
    | zero =>
      intro F D X hX
      simpa [projLastIter] using hX
    | succ m ih =>
      intro F D X hX
      have hX' : projLast X ∈ S.Ω (F + 1) D (k + m) := S.proj hX
      have hres : projLastIter k m (projLast X) ∈ S.Ω ((F + 1) + m) D k :=
        ih (F + 1) D (projLast X) hX'
      have heq : (F + 1) + m = F + (m + 1) := by omega
      change projLastIter k m (projLast X) ∈ S.Ω (F + (m + 1)) D k
      exact heq ▸ hres
  exact key m F D X hX

/-- The interior of `X` is the set of points with some Euclidean ball contained in `X`. -/
private theorem interior_eq_aux {n : ℕ} (X : Set (Fin n → ℝ)) :
    interior X = {x : Fin n → ℝ | ∃ r : ℝ, 0 < r ∧ ∀ y : Fin n → ℝ,
      (∑ i : Fin n, (y i - x i) ^ 2 < r ^ 2) → y ∈ X} := by
  ext x
  rw [mem_interior_iff_mem_nhds]
  constructor
  · intro hx
    rw [Metric.mem_nhds_iff] at hx
    obtain ⟨ε, hε, hsub⟩ := hx
    refine ⟨ε, hε, fun y hy => hsub ?_⟩
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    have hii : (y i - x i) ^ 2 < ε ^ 2 :=
      lt_of_le_of_lt
        (Finset.single_le_sum (fun j _ => sq_nonneg (y j - x j)) (Finset.mem_univ i)) hy
    rw [Real.dist_eq, ← abs_of_pos hε, ← sq_lt_sq]
    exact hii
  · rintro ⟨r, hr, hsub⟩
    apply Filter.mem_of_superset _ hsub
    apply IsOpen.mem_nhds _ _
    · have hcont : Continuous fun y : Fin n → ℝ => ∑ i : Fin n, (y i - x i) ^ 2 := by fun_prop
      exact isOpen_lt hcont continuous_const
    · change (∑ i : Fin n, (x i - x i) ^ 2) < r ^ 2
      have hz : ∑ i : Fin n, (x i - x i) ^ 2 = 0 := by simp
      rw [hz]
      positivity

/-! ## The Euclidean square-norm "ball" relation -/

/-- In `ℝ^{(n+1)+n}`, with the first `n+1` coordinates `(x, r)` (so `x = Fin.castSucc`-part,
`r = Fin.last n`) and the last `n` coordinates `y`, the polynomial `r² - Σᵢ (yᵢ - xᵢ)²`, whose
positive locus is the open Euclidean square-norm ball around `x` of radius `r`. -/
def ballPoly (n : ℕ) : MvPolynomial (Fin ((n+1) + n)) ℝ :=
  MvPolynomial.X (Fin.castAdd n (Fin.last n)) ^ 2 -
    ∑ i : Fin n, (MvPolynomial.X (Fin.natAdd (n+1) i) -
      MvPolynomial.X (Fin.castAdd n (Fin.castSucc i))) ^ 2

/-- Evaluation of `ballPoly` at a glued point `(u, w)`: `r² - Σᵢ (wᵢ - xᵢ)²`. -/
theorem eval_ballPoly (n : ℕ) (u : Fin (n+1) → ℝ) (w : Fin n → ℝ) :
    MvPolynomial.eval (snocIt (n+1) n u w) (ballPoly n)
      = (u (Fin.last n))^2 - ∑ i : Fin n, (w i - u (Fin.castSucc i))^2 := by
  simp only [ballPoly, MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_sum,
    MvPolynomial.eval_X, snocIt_castAdd, snocIt_natAdd]

/-- `ballPoly n` has total degree at most `2`, uniformly in `n`. -/
theorem totalDegree_ballPoly_le (n : ℕ) : (ballPoly n).totalDegree ≤ 2 := by
  have hX2 : (MvPolynomial.X (Fin.castAdd n (Fin.last n)) ^ 2 :
      MvPolynomial (Fin ((n+1)+n)) ℝ).totalDegree ≤ 2 := by
    rw [MvPolynomial.totalDegree_X_pow]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ((MvPolynomial.X (Fin.natAdd (n+1) i) -
        MvPolynomial.X (Fin.castAdd n (Fin.castSucc i))) ^ 2 :
          MvPolynomial (Fin ((n+1)+n)) ℝ).totalDegree ≤ 2 := by
    intro i _
    refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    have hsub : ((MvPolynomial.X (Fin.natAdd (n+1) i) -
        MvPolynomial.X (Fin.castAdd n (Fin.castSucc i)) :
          MvPolynomial (Fin ((n+1)+n)) ℝ)).totalDegree ≤ 1 := by
      refine (MvPolynomial.totalDegree_sub _ _).trans ?_
      rw [max_le_iff]
      exact ⟨by simp, by simp⟩
    calc 2 * ((MvPolynomial.X (Fin.natAdd (n+1) i) -
        MvPolynomial.X (Fin.castAdd n (Fin.castSucc i)) :
          MvPolynomial (Fin ((n+1)+n)) ℝ)).totalDegree ≤ 2 * 1 :=
          Nat.mul_le_mul_left 2 hsub
      _ = 2 := by norm_num
  unfold ballPoly
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [max_le_iff]
  refine ⟨hX2, ?_⟩
  exact MvPolynomial.totalDegree_finsetSum_le (s := Finset.univ) hterm

/-! ## The sets entering the construction -/

/-- The "ball" hypersurface relationship `{r² - Σ(yᵢ-xᵢ)² > 0}` in `ℝ^{(n+1)+n}`. -/
def ballSet (n : ℕ) : Set (Fin ((n+1)+n) → ℝ) :=
  {z | 0 < MvPolynomial.eval z (ballPoly n)}

/-- The complement of `X`, pulled back to the last `n` coordinates of `ℝ^{(n+1)+n}`. -/
def liftSet (n : ℕ) (X : Set (Fin n → ℝ)) : Set (Fin ((n+1)+n) → ℝ) :=
  {z | (fun j : Fin n => z (Fin.natAdd (n+1) j)) ∈ Xᶜ}

/-- `liftSet ∩ ballSet`: the point `y` lies outside `X` but inside the ball around `x`. -/
def S4 (n : ℕ) (X : Set (Fin n → ℝ)) : Set (Fin ((n+1)+n) → ℝ) := liftSet n X ∩ ballSet n

/-- Project the `y`-coordinates away, complement, and record `r > 0`. -/
def S7 (n : ℕ) (X : Set (Fin n → ℝ)) : Set (Fin (n+1) → ℝ) :=
  (projLastIter (n+1) n (S4 n X))ᶜ ∩ {u | 0 < u (Fin.last n)}

/-- Membership in `S7`: `x` survives with radius `t > 0` exactly when every point of the
Euclidean ball of radius `t` around `x` lies in `X`. -/
theorem memS7 (n : ℕ) (X : Set (Fin n → ℝ)) (x : Fin n → ℝ) (t : ℝ) :
    Fin.snoc x t ∈ S7 n X ↔
      0 < t ∧ ∀ w : Fin n → ℝ, (∑ i : Fin n, (w i - x i)^2 < t^2) → w ∈ X := by
  have hIter : projLastIter (n+1) n (S4 n X)
      = {u : Fin (n+1) → ℝ | ∃ w : Fin n → ℝ, snocIt (n+1) n u w ∈ S4 n X} :=
    projLastIter_eq (n+1) n (S4 n X)
  have hmem : ∀ (w : Fin n → ℝ),
      snocIt (n+1) n (Fin.snoc x t) w ∈ S4 n X ↔
        w ∉ X ∧ (∑ i : Fin n, (w i - x i)^2 < t^2) := by
    intro w
    rw [S4, Set.mem_inter_iff, liftSet, Set.mem_setOf_eq, Set.mem_compl_iff, ballSet,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [show (fun j : Fin n => snocIt (n+1) n (Fin.snoc x t) w (Fin.natAdd (n+1) j)) = w from
              funext (fun j => snocIt_natAdd (n+1) n (Fin.snoc x t) w j)] at h1
        exact h1
      · rw [eval_ballPoly] at h2
        simp only [Fin.snoc_castSucc, Fin.snoc_last] at h2
        linarith
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [show (fun j : Fin n => snocIt (n+1) n (Fin.snoc x t) w (Fin.natAdd (n+1) j)) = w from
              funext (fun j => snocIt_natAdd (n+1) n (Fin.snoc x t) w j)]
        exact h1
      · rw [eval_ballPoly]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        linarith
  rw [S7, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, hIter, Set.mem_setOf_eq]
  simp only [Fin.snoc_last, hmem]
  constructor
  · rintro ⟨hnot, hpos⟩
    refine ⟨hpos, ?_⟩
    intro w hw
    by_contra hwx
    exact hnot ⟨w, hwx, hw⟩
  · rintro ⟨hpos, hall⟩
    refine ⟨?_, hpos⟩
    rintro ⟨w, hwx, hw⟩
    exact hwx (hall w hw)

/-- The projection of `S7` along the radius coordinate is the interior of `X`. -/
theorem interior_projLast (n : ℕ) (X : Set (Fin n → ℝ)) :
    interior X = projLast (S7 n X) := by
  rw [interior_eq_aux X]
  ext x
  simp only [projLast, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, (memS7 n X x r).mpr ⟨hr, h⟩⟩
  · rintro ⟨r, hr⟩
    obtain ⟨hrpos, h⟩ := (memS7 n X x r).mp hr
    exact ⟨r, hrpos, h⟩

/-! ## The main theorem -/

theorem interior_mem {S : WilkiesDesign.SOMin} {n : ℕ} {a D : ℕ} {b : Polynomial ℕ}
    {X : Set (Fin n → ℝ)} (hX : X ∈ S.Ω a (b.eval D) n) :
    interior X ∈ S.Ω (a + 3 * n + 42) ((Polynomial.C 12 * b + Polynomial.C 60).eval D) n := by
  have h1 : Xᶜ ∈ S.Ω (a + 1) (b.eval D) n := S.compl hX
  have h2 : liftSet n X ∈ S.Ω ((a+1) + (n+1)) (b.eval D) ((n+1)+n) := liftNM_mem_aux h1 (n+1)
  have h3 : ballSet n ∈ S.Ω (2*n+3) ((Polynomial.C 4).eval D) ((n+1)+n) := by
    have hp := pos_mem_aux (S := S) D (ballPoly n)
    refine Omega.mono hp ?_ ?_
    · omega
    · simp only [Polynomial.eval_C]
      have := totalDegree_ballPoly_le n
      omega
  have h4 : S4 n X ∈ S.Ω (max ((a+1) + (n+1)) (2*n+3) + 1)
      ((b + Polynomial.C 4).eval D) ((n+1)+n) := Omega.inter₂ h2 h3
  have h5 : projLastIter (n+1) n (S4 n X) ∈
      S.Ω (max ((a+1) + (n+1)) (2*n+3) + 1 + n) ((b + Polynomial.C 4).eval D) (n+1) :=
    projLastIter_mem_aux (n+1) n h4
  have h6 : (projLastIter (n+1) n (S4 n X))ᶜ ∈
      S.Ω (max ((a+1) + (n+1)) (2*n+3) + 1 + n + 1) ((b + Polynomial.C 4).eval D) (n+1) :=
    S.compl h5
  have h7 : {u : Fin (n+1) → ℝ | 0 < u (Fin.last n)} ∈
      S.Ω (n+3) ((Polynomial.C 3).eval D) (n+1) := by
    have hp := pos_mem_aux (S := S) D (MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n+1)) ℝ)
    simpa [MvPolynomial.eval_X] using hp
  have h8 : S7 n X ∈
      S.Ω (max (max ((a+1) + (n+1)) (2*n+3) + 1 + n + 1) (n+3) + 1)
        (((b + Polynomial.C 4) + Polynomial.C 3).eval D) (n+1) := Omega.inter₂ h6 h7
  have h9 : projLast (S7 n X) ∈
      S.Ω (max (max ((a+1) + (n+1)) (2*n+3) + 1 + n + 1) (n+3) + 1 + 1)
        (((b + Polynomial.C 4) + Polynomial.C 3).eval D) n := S.proj h8
  rw [interior_projLast n X]
  refine Omega.mono h9 ?_ ?_
  · have hA : max ((a+1) + (n+1)) (2*n+3) ≤ a + 2*n + 38 :=
      max_le (by omega) (by omega)
    have h2' : max ((a+1) + (n+1)) (2*n+3) + 1 + n + 1 ≤ a + 3*n + 40 := by omega
    have h3' : n + 3 ≤ a + 3*n + 40 := by omega
    have h4' : max (max ((a+1) + (n+1)) (2*n+3) + 1 + n + 1) (n+3) ≤ a + 3*n + 40 :=
      max_le h2' h3'
    omega
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    omega

end Work.WilG1.Calc
