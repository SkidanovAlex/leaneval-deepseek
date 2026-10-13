/-
  WilE9 — `Gen` is closed under topological closure (BNZ §3, used by `SharpDeriv`).

  The construction is the one of area G1's `Calc.ClosureDefs`, specialised to the frozen
  inductive `WilkiesDesign.E.Gen`: with `Σ(x,y) = ∑ (yᵢ - xᵢ)²` one has

    `x ∈ closure X ↔ ∀ ε > 0, ∃ y ∈ X, Σ(x,y) < ε²`,

  hence `(closure X)ᶜ = {x | ∃ r ≠ 0, ∀ y ∈ X, r² < Σ(x,y)}`.  The right hand side is
  built from `Gen` in the space `ℝ^{n + (n+1) + 1}` with coordinates `(x | r | y | s)`: the
  set `bigJ X = cylSet X ∩ hypSet n` says `y ∈ X ∧ Σ(x,y) + s² = r²`, and
  `projLast ((projN (n+1) (bigJ X))ᶜ ∩ {r ≠ 0}) = (closure X)ᶜ`.
-/
import Mathlib
import Submission.Work.WilE9.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical Topology
namespace Work.WilE9.Gen
open WilkiesDesign WilkiesDesign.E

/-! ## 0. The squared Euclidean distance and the closure criterion -/

/-- The square of the Euclidean distance on `ℝⁿ`. -/
def esq {n : ℕ} (w x : Fin n → ℝ) : ℝ := ∑ j, (w j - x j) ^ 2

lemma esq_nonneg {n : ℕ} (w x : Fin n → ℝ) : 0 ≤ esq w x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The sup-norm distance is bounded by the Euclidean one. -/
lemma dist_sq_le_esq {n : ℕ} (w x : Fin n → ℝ) : dist w x ^ 2 ≤ esq w x := by
  have h0 : (0 : ℝ) ≤ Real.sqrt (esq w x) := Real.sqrt_nonneg _
  have h1 : dist w x ≤ Real.sqrt (esq w x) := by
    rw [dist_pi_le_iff h0]
    intro j
    rw [Real.dist_eq]
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun i : Fin n => (w i - x i) ^ 2) (s := Finset.univ)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  calc dist w x ^ 2 ≤ (Real.sqrt (esq w x)) ^ 2 := pow_le_pow_left₀ dist_nonneg h1 2
    _ = esq w x := Real.sq_sqrt (esq_nonneg w x)

/-- The Euclidean squared distance is bounded by `n` times the sup-norm one. -/
lemma esq_le_card_mul_dist_sq {n : ℕ} (w x : Fin n → ℝ) : esq w x ≤ n * dist w x ^ 2 := by
  have h : ∀ j : Fin n, (w j - x j) ^ 2 ≤ dist w x ^ 2 := by
    intro j
    have h1 : dist (w j) (x j) ≤ dist w x :=
      (dist_pi_le_iff (r := dist w x) dist_nonneg).mp le_rfl j
    rw [Real.dist_eq] at h1
    nlinarith [abs_nonneg (w j - x j), sq_nonneg (dist w x), sq_abs (w j - x j), h1]
  calc esq w x = ∑ j : Fin n, (w j - x j) ^ 2 := rfl
    _ ≤ ∑ _j : Fin n, dist w x ^ 2 := Finset.sum_le_sum fun j _ => h j
    _ = n * dist w x ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The closure criterion.**  A point is in the closure of `X` iff every Euclidean ball
around it meets `X`. -/
lemma mem_closure_iff_esq {n : ℕ} {X : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ closure X ↔ ∀ ε > 0, ∃ w ∈ X, esq w x < ε ^ 2 := by
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨w, hwX, hw⟩ := h (ε / ((n : ℝ) + 1)) (by positivity)
    refine ⟨w, hwX, ?_⟩
    rw [dist_comm] at hw
    have hd : (0 : ℝ) ≤ dist w x := dist_nonneg
    have h2 : dist w x ^ 2 ≤ (ε / ((n : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ hd hw.le 2
    have h3 : (n : ℝ) * (ε / ((n : ℝ) + 1)) ^ 2 < ε ^ 2 := by
      have hkey : (n : ℝ) * (ε / ((n : ℝ) + 1)) ^ 2 = ((n : ℝ) * ε ^ 2) / ((n : ℝ) + 1) ^ 2 := by
        rw [div_pow, mul_div_assoc]
      rw [hkey, div_lt_iff₀ (by positivity)]
      have hn : (n : ℝ) < ((n : ℝ) + 1) ^ 2 := by
        nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
      nlinarith [mul_lt_mul_of_pos_right hn (pow_pos hε 2)]
    have h4 : esq w x ≤ (n : ℝ) * dist w x ^ 2 := esq_le_card_mul_dist_sq w x
    nlinarith
  · intro h ε hε
    obtain ⟨w, hwX, hw⟩ := h ε hε
    refine ⟨w, hwX, ?_⟩
    have h1 : dist w x ^ 2 ≤ esq w x := dist_sq_le_esq w x
    have h2 : dist w x < ε := by nlinarith [dist_nonneg (x := w) (y := x), hε]
    rwa [dist_comm]

/-- **The complement of the closure**, in the form produced by the construction below. -/
lemma compl_closure_eq {n : ℕ} (X : Set (Fin n → ℝ)) :
    (closure X)ᶜ = {x : Fin n → ℝ | ∃ r : ℝ, r ≠ 0 ∧ ∀ w ∈ X, r ^ 2 < esq w x} := by
  ext x
  rw [Set.mem_compl_iff, mem_closure_iff_esq]
  constructor
  · intro h
    push Not at h
    obtain ⟨ε, hε, hε2⟩ := h
    refine ⟨ε / 2, ne_of_gt (by linarith), fun w hw => ?_⟩
    have := hε2 w hw
    nlinarith [hε]
  · rintro ⟨r, hr0, hr⟩ h
    obtain ⟨w, hw, hw2⟩ := h (|r|) (abs_pos.mpr hr0)
    have h1 := hr w hw
    rw [sq_abs] at hw2
    linarith

/-! ## 1. The `Gen`-calculus: lifts, projections, transports -/

/-- The `i`-th of the last `n` coordinates of `Fin (n + k)`. -/
def lidx {n : ℕ} (k : ℕ) (i : Fin n) : Fin (n + k) := ⟨k + i.val, by omega⟩

/-- `A` placed on the last `n` coordinates of `Fin (n + k) → ℝ`. -/
def liftLast {n : ℕ} (k : ℕ) (A : Set (Fin n → ℝ)) : Set (Fin (n + k) → ℝ) :=
  {z | (fun i : Fin n => z (lidx k i)) ∈ A}

theorem liftLast_mem {n : ℕ} : ∀ (k F D : ℕ) {A : Set (Fin n → ℝ)},
    WilkiesDesign.E.Gen F D n A → WilkiesDesign.E.Gen (F + k) D (n + k) (liftLast k A) := by
  intro k
  induction k with
  | zero =>
    intro F D A h
    have heq : liftLast 0 A = A := by
      ext z
      simp only [liftLast, Set.mem_ofPred_eq]
      have hz : (fun i : Fin n => z (lidx 0 i)) = z := by
        funext i; exact congrArg z (Fin.ext (by simp [lidx]))
      rw [hz]
    rw [heq]
    exact h
  | succ k ih =>
    intro F D A h
    have heq : liftLast (k + 1) A =
        {z : Fin (n + k + 1) → ℝ | Fin.tail z ∈ liftLast k A} := by
      ext z
      change (fun i : Fin n => z (lidx (k + 1) i)) ∈ A ↔
        (fun i : Fin n => Fin.tail z (lidx k i)) ∈ A
      have hfun : (fun i : Fin n => z (lidx (k + 1) i)) =
          (fun i : Fin n => Fin.tail z (lidx k i)) := by
        funext i
        show z (lidx (k + 1) i) = Fin.tail z (lidx k i)
        rw [show Fin.tail z (lidx k i) = z ((lidx k i).succ) from rfl,
          show lidx (k + 1) i = (lidx k i).succ from Fin.ext (by simp [lidx]; omega)]
      rw [hfun]
    rw [heq]
    exact Gen.monoF (by omega) (Gen.prod_left (ih F D h))

/-- Forget the last `k` coordinates. -/
def projN {n : ℕ} (k : ℕ) (A : Set (Fin (n + k) → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∃ y : Fin k → ℝ, Fin.append x y ∈ A}

theorem projN_mem {n : ℕ} : ∀ (k F D : ℕ) {A : Set (Fin (n + k) → ℝ)},
    WilkiesDesign.E.Gen F D (n + k) A → WilkiesDesign.E.Gen (F + k) D n (projN k A) := by
  intro k
  induction k with
  | zero =>
    intro F D A h
    have heq : projN 0 A = A := by
      ext x
      constructor
      · rintro ⟨y, hy⟩
        have h2 : Fin.append x y = x := by
          funext i
          conv_lhs => rw [show i = Fin.castAdd 0 i from Fin.ext rfl]
          rw [Fin.append_left]
        rwa [h2] at hy
      · intro hx
        refine ⟨Fin.elim0, ?_⟩
        have h2 : Fin.append x (Fin.elim0 : Fin 0 → ℝ) = x := by
          funext i
          conv_lhs => rw [show i = Fin.castAdd 0 i from Fin.ext rfl]
          rw [Fin.append_left]
        rwa [h2]
    rw [heq]
    exact h
  | succ k ih =>
    intro F D A h
    have h' := ih (F + 1) D (A := projLast A) (Gen.proj h)
    have heq : projN (k + 1) A = projN k (projLast A) := by
      ext x
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨Fin.init y, ?_⟩
        change ∃ t : ℝ, Fin.snoc (Fin.append x (Fin.init y)) t ∈ A
        refine ⟨y (Fin.last k), ?_⟩
        rw [← Fin.append_snoc]
        rwa [Fin.snoc_init_self y]
      · rintro ⟨y, t, hy⟩
        exact ⟨Fin.snoc y t, by rw [Fin.append_snoc]; exact hy⟩
    rw [heq]
    exact Gen.monoF (by omega) h'

/-- `Gen`-membership transports along arithmetic equalities of the index type. -/
theorem ndrec_mem {N N' F D : ℕ} (h : N = N') {A : Set (Fin N → ℝ)}
    (hA : WilkiesDesign.E.Gen F D N A) : WilkiesDesign.E.Gen F D N' (h ▸ A) := by
  cases h; exact hA

/-- Membership in a set transported along an arithmetic equality of the index type. -/
theorem mem_ndrec {N N' : ℕ} (h : N = N') (T : Set (Fin N → ℝ)) (w : Fin N' → ℝ) :
    w ∈ (h ▸ T) ↔ (fun i : Fin N => w (Fin.cast h i)) ∈ T := by
  cases h; simp

/-! ## 2. The big space `ℝ^{n + (n+1) + 1}` with coordinates `(x | r | y | s)` -/

/-- Index of the `j`-th `x`-coordinate. -/
def bxIdx {n : ℕ} (j : Fin n) : Fin (n + (n + 1) + 1) := ⟨j.val, by omega⟩
/-- Index of the `r`-coordinate. -/
def brIdx (n : ℕ) : Fin (n + (n + 1) + 1) := ⟨n, by omega⟩
/-- Index of the `j`-th `y`-coordinate. -/
def byIdx {n : ℕ} (j : Fin n) : Fin (n + (n + 1) + 1) := ⟨n + 1 + j.val, by omega⟩
/-- Index of the `s`-coordinate.  Written as `(n+1) + n` so that the `Fin.cast` below is
definitional. -/
def bsIdx (n : ℕ) : Fin (n + (n + 1) + 1) := ⟨n + 1 + n, by omega⟩

/-- The polynomial `∑ⱼ (yⱼ - xⱼ)² + s² - r²`. -/
def bigP (n : ℕ) : MvPolynomial (Fin (n + (n + 1) + 1)) ℝ :=
  (∑ j : Fin n, (MvPolynomial.X (byIdx j) - MvPolynomial.X (bxIdx j)) ^ 2)
    + (MvPolynomial.X (bsIdx n)) ^ 2 - (MvPolynomial.X (brIdx n)) ^ 2

/-- The cylinder over `X`: the `y`-block lies in `X`. -/
def cylSet {n : ℕ} (X : Set (Fin n → ℝ)) : Set (Fin (n + (n + 1) + 1) → ℝ) :=
  {z | Fin.init z ∈ liftLast (n + 1) X}

/-- The hypersurface `bigP n = 0`. -/
def hypSet (n : ℕ) : Set (Fin (n + (n + 1) + 1) → ℝ) :=
  {z | MvPolynomial.eval z (bigP n) = 0}

/-- `y ∈ X` and `∑ⱼ (yⱼ - xⱼ)² + s² = r²`. -/
def bigJ {n : ℕ} (X : Set (Fin n → ℝ)) : Set (Fin (n + (n + 1) + 1) → ℝ) :=
  cylSet X ∩ hypSet n

/-- The arithmetic identity putting the big space in the form `Fin ((n+1) + (n+1))`, which is
what the projection `projN (n+1)` needs. -/
theorem bigSpace_eq (n : ℕ) : n + (n + 1) + 1 = (n + 1) + (n + 1) := by omega

/-- The projection of the big set onto the `(x,r)`-coordinates. -/
def bigProj {n : ℕ} (X : Set (Fin n → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  projN (n + 1) (bigSpace_eq n ▸ bigJ X)

/-- `{r ≠ 0} ⊆ ℝ^{n+1}`, on the last coordinate. -/
def rNeZero (n : ℕ) : Set (Fin (n + 1) → ℝ) := {v | v (Fin.last n) ≠ 0}

/-- The final set in `ℝ^{n+1}`: `r ≠ 0` and no `(y,s)` above `(x,r)`. -/
def finalC {n : ℕ} (X : Set (Fin n → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  rNeZero n ∩ (bigProj X)ᶜ

/-! ## 3. Membership lemmas for the big pieces -/

theorem cylSet_mem {n F D : ℕ} {X : Set (Fin n → ℝ)} (hX : WilkiesDesign.E.Gen F D n X) :
    WilkiesDesign.E.Gen (F + (n + 1) + 1) D (n + (n + 1) + 1) (cylSet X) :=
  Gen.prod_right (liftLast_mem (n + 1) F D hX)

theorem hypSet_mem (n : ℕ) :
    WilkiesDesign.E.Gen (n + (n + 1) + 1) (bigP n).totalDegree (n + (n + 1) + 1) (hypSet n) :=
  Gen.hyp (n + (n + 1) + 1) (bigP n)

theorem bigJ_mem {n F D : ℕ} {X : Set (Fin n → ℝ)} (hX : WilkiesDesign.E.Gen F D n X) :
    WilkiesDesign.E.Gen (max (F + (n + 1) + 1) (n + (n + 1) + 1) + 1) (D + (bigP n).totalDegree)
      (n + (n + 1) + 1) (bigJ X) :=
  Gen.inter₂ (cylSet_mem hX) (hypSet_mem n)

theorem bigProj_mem {n F D : ℕ} {X : Set (Fin n → ℝ)} (hX : WilkiesDesign.E.Gen F D n X) :
    WilkiesDesign.E.Gen (max (F + (n + 1) + 1) (n + (n + 1) + 1) + 1 + (n + 1))
      (D + (bigP n).totalDegree) (n + 1) (bigProj X) :=
  projN_mem (n := n + 1) (n + 1) _ _ (ndrec_mem (bigSpace_eq n) (bigJ_mem hX))

theorem rNeZero_mem (n : ℕ) : WilkiesDesign.E.Gen (n + 2) 1 (n + 1) (rNeZero n) := by
  have h : WilkiesDesign.E.Gen (n + 1)
      (MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℝ).totalDegree (n + 1)
      {v : Fin (n + 1) → ℝ | MvPolynomial.eval v (MvPolynomial.X (Fin.last n)) = 0} :=
    Gen.hyp (n + 1) (MvPolynomial.X (Fin.last n))
  rw [MvPolynomial.totalDegree_X] at h
  have h1 : WilkiesDesign.E.Gen (n + 1) 1 (n + 1) {v : Fin (n + 1) → ℝ | v (Fin.last n) = 0} := by
    convert h using 2
    ext v
    simp [MvPolynomial.eval_X]
  have h2 := Gen.compl h1
  have hset : ({v : Fin (n + 1) → ℝ | v (Fin.last n) = 0} : Set (Fin (n + 1) → ℝ))ᶜ = rNeZero n := by
    ext v; simp [rNeZero]
  rwa [hset] at h2

theorem finalC_mem {n F D : ℕ} {X : Set (Fin n → ℝ)} (hX : WilkiesDesign.E.Gen F D n X) :
    WilkiesDesign.E.Gen
      (max (n + 2) (max (F + (n + 1) + 1) (n + (n + 1) + 1) + 1 + (n + 1) + 1) + 1)
      (1 + (D + (bigP n).totalDegree)) (n + 1) (finalC X) :=
  Gen.inter₂ (rNeZero_mem n) (Gen.compl (bigProj_mem hX))

/-! ## 4. Reading the coordinates of the big space -/

theorem mem_cylSet_iff {n : ℕ} {X : Set (Fin n → ℝ)} {z : Fin (n + (n + 1) + 1) → ℝ} :
    z ∈ cylSet X ↔ (fun j : Fin n => z (byIdx j)) ∈ X := by
  rw [cylSet, Set.mem_ofPred_eq, liftLast, Set.mem_ofPred_eq]
  have hfun : (fun i : Fin n => Fin.init z (lidx (n + 1) i)) =
      (fun j : Fin n => z (byIdx j)) := by
    funext j
    show z (Fin.castSucc (lidx (n + 1) j)) = z (byIdx j)
    congr 1
  rw [hfun]

theorem mem_hypSet_iff {n : ℕ} {z : Fin (n + (n + 1) + 1) → ℝ} :
    z ∈ hypSet n ↔
      (∑ j : Fin n, (z (byIdx j) - z (bxIdx j)) ^ 2) + z (bsIdx n) ^ 2 - z (brIdx n) ^ 2 = 0 := by
  rw [hypSet, Set.mem_ofPred_eq, bigP]
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_add, MvPolynomial.eval_sum,
    MvPolynomial.eval_pow, MvPolynomial.eval_X]

theorem cast_bxIdx (n : ℕ) (j : Fin n) :
    Fin.cast (bigSpace_eq n) (bxIdx j) = Fin.castAdd (n + 1) (Fin.castSucc j) := rfl

theorem cast_brIdx (n : ℕ) :
    Fin.cast (bigSpace_eq n) (brIdx n) = Fin.castAdd (n + 1) (Fin.last n) := rfl

theorem cast_byIdx (n : ℕ) (j : Fin n) :
    Fin.cast (bigSpace_eq n) (byIdx j) = Fin.natAdd (n + 1) (Fin.castSucc j) := rfl

theorem cast_bsIdx (n : ℕ) :
    Fin.cast (bigSpace_eq n) (bsIdx n) = Fin.natAdd (n + 1) (Fin.last n) := rfl

/-- Membership in the (transported) big set, in coordinates of `(v, y)`. -/
theorem append_mem_bigJ_iff {n : ℕ} (X : Set (Fin n → ℝ)) (v y : Fin (n + 1) → ℝ) :
    Fin.append v y ∈ (bigSpace_eq n ▸ bigJ X) ↔
      (Fin.init y ∈ X ∧
        esq (Fin.init y) (Fin.init v) + (y (Fin.last n)) ^ 2 = (v (Fin.last n)) ^ 2) := by
  rw [mem_ndrec, bigJ, Set.mem_inter_iff, mem_cylSet_iff, mem_hypSet_iff]
  have hA : ∀ j : Fin n, Fin.append v y (Fin.cast (bigSpace_eq n) (byIdx j)) = Fin.init y j := by
    intro j; rw [cast_byIdx, Fin.append_right]; rfl
  have hB : ∀ j : Fin n, Fin.append v y (Fin.cast (bigSpace_eq n) (bxIdx j)) = Fin.init v j := by
    intro j; rw [cast_bxIdx, Fin.append_left]; rfl
  have hC : Fin.append v y (Fin.cast (bigSpace_eq n) (bsIdx n)) = y (Fin.last n) := by
    rw [cast_bsIdx, Fin.append_right]
  have hD : Fin.append v y (Fin.cast (bigSpace_eq n) (brIdx n)) = v (Fin.last n) := by
    rw [cast_brIdx, Fin.append_left]
  have hcyliff : ((fun j : Fin n => Fin.append v y (Fin.cast (bigSpace_eq n) (byIdx j))) ∈ X)
      ↔ Fin.init y ∈ X := by
    rw [show (fun j : Fin n => Fin.append v y (Fin.cast (bigSpace_eq n) (byIdx j))) = Fin.init y
      from funext hA]
  have hsum : (∑ j : Fin n,
        (Fin.append v y (Fin.cast (bigSpace_eq n) (byIdx j))
          - Fin.append v y (Fin.cast (bigSpace_eq n) (bxIdx j))) ^ 2)
      = ∑ j : Fin n, (Fin.init y j - Fin.init v j) ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hA j, hB j]
  have hH : ((∑ j : Fin n,
        (Fin.append v y (Fin.cast (bigSpace_eq n) (byIdx j))
          - Fin.append v y (Fin.cast (bigSpace_eq n) (bxIdx j))) ^ 2)
        + (Fin.append v y (Fin.cast (bigSpace_eq n) (bsIdx n))) ^ 2
        - (Fin.append v y (Fin.cast (bigSpace_eq n) (brIdx n))) ^ 2 = 0)
      ↔ (esq (Fin.init y) (Fin.init v) + (y (Fin.last n)) ^ 2 = (v (Fin.last n)) ^ 2) := by
    rw [hsum, hC, hD, esq]
    constructor <;> intro h <;> linarith
  rw [hcyliff, hH]

/-! ## 5. The projection of the big set -/

theorem mem_bigProj {n : ℕ} (X : Set (Fin n → ℝ)) (v : Fin (n + 1) → ℝ) :
    v ∈ bigProj X ↔ ∃ w : Fin n → ℝ, w ∈ X ∧ esq w (Fin.init v) ≤ (v (Fin.last n)) ^ 2 := by
  rw [bigProj, projN]
  constructor
  · rintro ⟨y, hy⟩
    rw [append_mem_bigJ_iff] at hy
    obtain ⟨h1, h2⟩ := hy
    exact ⟨Fin.init y, h1, by nlinarith [sq_nonneg (y (Fin.last n)), h2]⟩
  · rintro ⟨w, hw, hle⟩
    refine ⟨Fin.snoc w (Real.sqrt ((v (Fin.last n)) ^ 2 - esq w (Fin.init v))), ?_⟩
    rw [append_mem_bigJ_iff]
    refine ⟨?_, ?_⟩
    · rwa [Fin.init_snoc]
    · rw [Fin.snoc_last, Fin.init_snoc]
      have hsq : (Real.sqrt ((v (Fin.last n)) ^ 2 - esq w (Fin.init v))) ^ 2
          = (v (Fin.last n)) ^ 2 - esq w (Fin.init v) := Real.sq_sqrt (by linarith)
      linarith

/-! ## 6. The final set is `(closure X)ᶜ` -/

theorem projLast_finalC {n : ℕ} (X : Set (Fin n → ℝ)) :
    projLast (finalC X) = {x : Fin n → ℝ | ∃ r : ℝ, r ≠ 0 ∧ ∀ w ∈ X, r ^ 2 < esq w x} := by
  ext x
  rw [projLast, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨r, hr⟩
    rw [finalC, Set.mem_inter_iff, Set.mem_compl_iff, rNeZero, Set.mem_ofPred_eq] at hr
    obtain ⟨hr0, hrnot⟩ := hr
    rw [Fin.snoc_last] at hr0
    refine ⟨r, hr0, fun w hw => ?_⟩
    rw [mem_bigProj] at hrnot
    by_contra hcon
    rw [not_lt] at hcon
    exact hrnot ⟨w, hw, by rw [Fin.init_snoc, Fin.snoc_last]; exact hcon⟩
  · rintro ⟨r, hr0, hr⟩
    refine ⟨r, ?_⟩
    rw [finalC, Set.mem_inter_iff, Set.mem_compl_iff, rNeZero, Set.mem_ofPred_eq, Fin.snoc_last]
    refine ⟨hr0, ?_⟩
    rw [mem_bigProj]
    rintro ⟨w, hw, hle⟩
    rw [Fin.init_snoc, Fin.snoc_last] at hle
    exact absurd hle (not_le.mpr (hr w hw))

/-! ## 7. The theorem -/

/-- **`Gen` is closed under topological closure**, at the cost of a constant format budget and
a polynomial degree budget.  (Proof: `closure X = (interior Xᶜ)ᶜ`, and the interior is a
projection of a complement of a projection of an intersection with the semialgebraic set
`|y i - x i| < ε`, using the sup-metric, whose balls form a neighbourhood basis.) -/
theorem gen_closure (F n : ℕ) : ∃ (a : ℕ) (b : Polynomial ℕ),
    ∀ (D : ℕ) (X : Set (Fin n → ℝ)),
      WilkiesDesign.E.Gen F D n X → WilkiesDesign.E.Gen a (b.eval D) n (closure X) := by
  refine ⟨max (n + 2) (max (F + (n + 1) + 1) (n + (n + 1) + 1) + 1 + (n + 1) + 1) + 1 + 2,
    Polynomial.X + Polynomial.C (1 + (bigP n).totalDegree), ?_⟩
  intro D X hX
  have h1 := Gen.proj (finalC_mem hX)
  rw [projLast_finalC X] at h1
  rw [← compl_closure_eq X] at h1
  have h2 := Gen.compl h1
  rw [compl_compl] at h2
  have hb : (Polynomial.X + Polynomial.C (1 + (bigP n).totalDegree) : Polynomial ℕ).eval D
      = 1 + (D + (bigP n).totalDegree) := by
    simp [Polynomial.eval_add, Polynomial.eval_X]
    omega
  rw [hb]
  exact h2

end Work.WilE9.Gen
