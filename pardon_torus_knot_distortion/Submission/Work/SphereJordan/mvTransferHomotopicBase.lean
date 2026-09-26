import Mathlib
import Submission.Work.SphereJordan.mvTransfer

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Homotopy invariance of the Mayer–Vietoris transfer

The transfer of a labelled subdivision (`SData.transfer`) is the chain-level description of the
Mayer–Vietoris connecting homomorphism `H₁(X) → H₀(U ∩ V)`.  This file proves that it is
well defined on homotopy classes of paths:

`mvTransferHomotopic : γ.Homotopic γ' → d.transfer = d'.transfer`.

The proof follows the standard chain-level argument.  We introduce

* `wTrans U V v w N` — the transfer of a "weighted vertex sequence": the signed sum
  `∑_{i<N} w i • ([v (i+1)] - [v i])` in `H₀(U ∩ V)`;
* `LSub` — a labelled subdivision indexed by `ℕ`, generalising `SData`;
* the *refinement* lemma `wTrans_refine`, identifying a fine weighted sum with a coarse one;
* independence of the subdivision for a single path;
* the two-dimensional (grid) argument proving invariance under a homotopy.
-/

namespace Work.SphereJordan

open Set

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-! ## A path piece lying in a set -/

/-- Two points joined inside a set by a piece of a path have the same `h0cls`. -/
theorem h0cls_eq_of_piece {W : Set X} {a b : X} {γ : Path a b} {p q : unitInterval}
    (hpq : p ≤ q) (hW : ∀ s ∈ Set.Icc p q, γ s ∈ W) :
    h0cls W (γ q) = h0cls W (γ p) := by
  have hp : γ p ∈ W := hW p (left_mem_Icc.mpr hpq)
  have hq : γ q ∈ W := hW q (right_mem_Icc.mpr hpq)
  refine h0cls_eq_of_joinedIn hq hp ?_
  refine ⟨{ toFun := fun u => γ (Set.Icc.convexComb p q (unitInterval.symm u))
            continuous_toFun := ?_
            source' := ?_
            target' := ?_ }, ?_⟩
  · exact γ.continuous.comp ((Set.Icc.continuous_convexComb p q).comp unitInterval.continuous_symm)
  · simp [Set.Icc.convexComb_one]
  · simp [Set.Icc.convexComb_zero]
  · intro x
    exact hW _ ⟨Set.Icc.le_convexComb hpq (unitInterval.symm x),
      Set.Icc.convexComb_le hpq (unitInterval.symm x)⟩

/-! ## The transfer of a weighted vertex sequence -/

/-- The transfer of a weighted vertex sequence: `∑_{i<N} w i • ([v (i+1)] - [v i])`, where `[x]`
denotes the class of `x` in `H₀(U ∩ V)` (and `0` if `x ∉ U ∩ V`). -/
def wTrans (U V : Set X) (v : ℕ → X) (w : ℕ → ℤ) (N : ℕ) : H0 (U ∩ V) :=
  ∑ i ∈ Finset.range N, w i • (h0cls (U ∩ V) (v (i + 1)) - h0cls (U ∩ V) (v i))

/-- A weighted vertex sequence is unchanged if the weights agree wherever the corresponding
"increment" is non-zero. -/
theorem wTrans_congr (U V : Set X) (v : ℕ → X) (w w' : ℕ → ℤ) (N : ℕ)
    (h : ∀ i, i < N → w i ≠ w' i → h0cls (U ∩ V) (v (i + 1)) = h0cls (U ∩ V) (v i)) :
    wTrans U V v w N = wTrans U V v w' N := by
  rw [wTrans, wTrans]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  by_cases hw : w i = w' i
  · rw [hw]
  · rw [h i hi hw]
    simp

/-- A vertex sequence whose consecutive points are all "equal" in `H₀(U ∩ V)` has zero transfer. -/
theorem wTrans_eq_zero_of_const (U V : Set X) {v : ℕ → X} {w : ℕ → ℤ} {N : ℕ}
    (h : ∀ i, i < N → h0cls (U ∩ V) (v (i + 1)) = h0cls (U ∩ V) (v i)) :
    wTrans U V v w N = 0 := by
  rw [wTrans]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [h i hi, sub_self, smul_zero]

/-- **Refinement of a weighted vertex sequence.**  If `v'` is a refinement of `v` along a strictly
increasing `φ` (with `v' (φ i) = v i`) and the weights `w'` are constant on the blocks
`[φ j, φ (j+1))` with value `w j`, then the fine and the coarse transfers agree. -/
theorem wTrans_refine (U V : Set X) (v v' : ℕ → X) (w w' : ℕ → ℤ) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (hφ0 : φ 0 = 0) (hv : ∀ i, v' (φ i) = v i)
    (hw : ∀ j m, φ j ≤ m → m < φ (j + 1) → w' m = w j) :
    ∀ N, wTrans U V v' w' (φ N) = wTrans U V v w N := by
  intro N
  induction N with
  | zero =>
    rw [hφ0, wTrans, wTrans, Finset.range_zero]
    simp
  | succ N ih =>
    have hle : φ N ≤ φ (N + 1) := (hφ (Nat.lt_succ_self N)).le
    have hdisj : Disjoint (Finset.Ico 0 (φ N)) (Finset.Ico (φ N) (φ (N + 1))) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_Ico] at ha hb
      omega
    have hsplit : wTrans U V v' w' (φ (N + 1)) =
        wTrans U V v' w' (φ N) +
          ∑ m ∈ Finset.Ico (φ N) (φ (N + 1)),
            w' m • (h0cls (U ∩ V) (v' (m + 1)) - h0cls (U ∩ V) (v' m)) := by
      rw [wTrans, wTrans, Finset.range_eq_Ico,
        ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le (φ N)) hle, Finset.sum_union hdisj,
        Finset.range_eq_Ico]
    have hblock : (∑ m ∈ Finset.Ico (φ N) (φ (N + 1)),
            w' m • (h0cls (U ∩ V) (v' (m + 1)) - h0cls (U ∩ V) (v' m)))
        = w N • (h0cls (U ∩ V) (v (N + 1)) - h0cls (U ∩ V) (v N)) := by
      have hwN : ∀ m, m ∈ Finset.Ico (φ N) (φ (N + 1)) → w' m = w N := by
        intro m hm
        rw [Finset.mem_Ico] at hm
        exact hw N m hm.1 hm.2
      calc (∑ m ∈ Finset.Ico (φ N) (φ (N + 1)),
              w' m • (h0cls (U ∩ V) (v' (m + 1)) - h0cls (U ∩ V) (v' m)))
          = ∑ m ∈ Finset.Ico (φ N) (φ (N + 1)),
              w N • (h0cls (U ∩ V) (v' (m + 1)) - h0cls (U ∩ V) (v' m)) :=
            Finset.sum_congr rfl fun m hm => by rw [hwN m hm]
        _ = w N • ∑ m ∈ Finset.Ico (φ N) (φ (N + 1)),
              (h0cls (U ∩ V) (v' (m + 1)) - h0cls (U ∩ V) (v' m)) :=
            (Finset.smul_sum).symm
        _ = w N • (h0cls (U ∩ V) (v' (φ (N + 1))) - h0cls (U ∩ V) (v' (φ N))) :=
            congrArg (fun z => w N • z)
              (Finset.sum_Ico_sub (fun m => h0cls (U ∩ V) (v' m)) hle)
        _ = w N • (h0cls (U ∩ V) (v (N + 1)) - h0cls (U ∩ V) (v N)) := by
            rw [hv (N + 1), hv N]
    rw [hsplit, ih, hblock]
    simp only [wTrans]
    rw [Finset.sum_range_succ]

/-- The set of the cover associated with a side. -/
def Side.set (U V : Set X) : Side → Set X
  | Side.U => U
  | Side.V => V

@[simp] theorem Side.set_U (U V : Set X) : Side.set U V Side.U = U := rfl
@[simp] theorem Side.set_V (U V : Set X) : Side.set U V Side.V = V := rfl

theorem side_set_mono {U V : Set X} {b b' : Side} (h : b ≠ b') :
    Side.set U V b ∩ Side.set U V b' = U ∩ V := by
  rcases side_ne_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact (Set.inter_comm U V).symm

/-! ## Labelled subdivisions indexed by `ℕ` -/

/-- A labelled subdivision of a path, written as a strictly increasing sequence of times
`0 = t 0 < t 1 < ... < t N = 1` together with a side for each of the `N` pieces.  The values
`t i` for `i > N` are irrelevant (we set them to `1`). -/
structure LSub {a b : X} (U V : Set X) (γ : Path a b) where
  N : ℕ
  t : ℕ → unitInterval
  t0 : t 0 = 0
  tN : t N = 1
  strict : ∀ i, i < N → t i < t (i + 1)
  side : ℕ → Side
  validU : ∀ i, i < N → side i = Side.U → ∀ s : unitInterval, t i ≤ s → s ≤ t (i + 1) → γ s ∈ U
  validV : ∀ i, i < N → side i = Side.V → ∀ s : unitInterval, t i ≤ s → s ≤ t (i + 1) → γ s ∈ V

namespace LSub

variable {U V : Set X} {a b : X} {γ : Path a b}

/-- The weight of a piece: `1` for a `U`-piece and `0` otherwise. -/
def weight (d : LSub U V γ) (i : ℕ) : ℤ := if d.side i = Side.U then 1 else 0

/-- The transfer of a labelled subdivision. -/
def transfer (d : LSub U V γ) : H0 (U ∩ V) :=
  wTrans U V (fun i => γ (d.t i)) d.weight d.N

theorem transfer_def (d : LSub U V γ) :
    d.transfer = wTrans U V (fun i => γ (d.t i)) d.weight d.N := rfl

theorem weight_eq_one {d : LSub U V γ} {i : ℕ} (h : d.side i = Side.U) : d.weight i = 1 := by
  rw [weight, if_pos h]
theorem weight_eq_zero {d : LSub U V γ} {i : ℕ} (h : d.side i ≠ Side.U) : d.weight i = 0 := by
  rw [weight, if_neg h]

/-- The transfer of a labelled subdivision only depends on the *weights* of the pieces. -/
theorem transfer_eq_weight (d : LSub U V γ) (sd : ℕ → Side)
    (hU : ∀ i, i < d.N → sd i = Side.U → ∀ s : unitInterval, d.t i ≤ s → s ≤ d.t (i + 1) → γ s ∈ U)
    (hV : ∀ i, i < d.N → sd i = Side.V → ∀ s : unitInterval, d.t i ≤ s → s ≤ d.t (i + 1) → γ s ∈ V) :
    d.transfer = wTrans U V (fun i => γ (d.t i)) (fun i => if sd i = Side.U then 1 else 0) d.N := by
  rw [transfer]
  refine wTrans_congr U V _ _ _ d.N fun i hi hne => ?_
  have hsd : sd i ≠ d.side i := by
    intro hEq
    apply hne
    rw [weight, ‹sd i = d.side i›]
  have hpiece : ∀ s ∈ Set.Icc (d.t i) (d.t (i + 1)), γ s ∈ U ∩ V := by
    intro s hs
    rcases side_ne_cases hsd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hU i hi h1 s hs.1 hs.2, d.validV i hi h2 s hs.1 hs.2⟩
    · exact ⟨d.validU i hi h2 s hs.1 hs.2, hV i hi h1 s hs.1 hs.2⟩
  exact h0cls_eq_of_piece (d.strict i hi).le hpiece

end LSub

/-- A `SData` (a `Fin`-indexed labelled subdivision) as an `LSub`. -/
def LSub.ofSData {U V : Set X} {a b : X} {γ : Path a b} (d : SData U V γ) : LSub U V γ where
  N := d.n
  t := fun i => if h : i ≤ d.n then d.t ⟨i, Nat.lt_succ_of_le h⟩ else 1
  t0 := by
    rw [dif_pos (Nat.zero_le d.n)]
    convert d.t0 using 2
    ext; simp
  tN := by
    rw [dif_pos (le_refl d.n)]
    convert d.tn using 2
    ext; simp
  strict := by
    intro i hi
    have h2 : i + 1 ≤ d.n := hi
    rw [dif_pos (le_of_lt hi), dif_pos h2]
    have e1 : (⟨i, Nat.lt_succ_of_le (le_of_lt hi)⟩ : Fin (d.n + 1)) =
        (⟨i, hi⟩ : Fin d.n).castSucc := by ext; simp [Fin.val_castSucc]
    have e2 : (⟨i + 1, Nat.lt_succ_of_le h2⟩ : Fin (d.n + 1)) =
        (⟨i, hi⟩ : Fin d.n).succ := by ext; simp [Fin.val_succ]
    rw [e1, e2]
    exact d.mono Fin.castSucc_lt_succ
  side := fun i => if h : i < d.n then d.side ⟨i, h⟩ else Side.V
  validU := by
    intro i hi hside s hs1 hs2
    have h2 : i + 1 ≤ d.n := hi
    rw [dif_pos (le_of_lt hi)] at hs1
    rw [dif_pos h2] at hs2
    rw [dif_pos hi] at hside
    have e1 : (⟨i, Nat.lt_succ_of_le (le_of_lt hi)⟩ : Fin (d.n + 1)) =
        (⟨i, hi⟩ : Fin d.n).castSucc := by ext; simp [Fin.val_castSucc]
    have e2 : (⟨i + 1, Nat.lt_succ_of_le h2⟩ : Fin (d.n + 1)) =
        (⟨i, hi⟩ : Fin d.n).succ := by ext; simp [Fin.val_succ]
    rw [e1] at hs1
    rw [e2] at hs2
    exact d.validU ⟨i, hi⟩ hside s hs1 hs2
  validV := by
    intro i hi hside s hs1 hs2
    have h2 : i + 1 ≤ d.n := hi
    rw [dif_pos (le_of_lt hi)] at hs1
    rw [dif_pos h2] at hs2
    rw [dif_pos hi] at hside
    have e1 : (⟨i, Nat.lt_succ_of_le (le_of_lt hi)⟩ : Fin (d.n + 1)) =
        (⟨i, hi⟩ : Fin d.n).castSucc := by ext; simp [Fin.val_castSucc]
    have e2 : (⟨i + 1, Nat.lt_succ_of_le h2⟩ : Fin (d.n + 1)) =
        (⟨i, hi⟩ : Fin d.n).succ := by ext; simp [Fin.val_succ]
    rw [e1] at hs1
    rw [e2] at hs2
    exact d.validV ⟨i, hi⟩ hside s hs1 hs2

/-- The transfer of `ofSData d` is the transfer of `d`. -/
theorem LSub.transfer_ofSData {U V : Set X} {a b : X} {γ : Path a b} (d : SData U V γ) :
    (LSub.ofSData d).transfer = d.transfer := by
  have hN : (LSub.ofSData d).N = d.n := rfl
  rw [LSub.transfer_def, hN, SData.transfer, wTrans]
  rw [← Fin.sum_univ_eq_sum_range (fun i => (LSub.ofSData d).weight i •
    (h0cls (U ∩ V) (γ ((LSub.ofSData d).t (i + 1))) -
     h0cls (U ∩ V) (γ ((LSub.ofSData d).t i)))) d.n]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : (LSub.ofSData d).side ↑i = d.side i := by
    show (if h : (i : ℕ) < d.n then d.side ⟨(i : ℕ), h⟩ else Side.V) = d.side i
    rw [dif_pos i.2]
  have ht1 : (LSub.ofSData d).t ↑i = d.t i.castSucc := by
    show (if h : (i : ℕ) ≤ d.n then d.t ⟨(i : ℕ), Nat.lt_succ_of_le h⟩ else 1) = d.t i.castSucc
    rw [dif_pos i.2.le]
    exact congrArg d.t (Fin.ext rfl)
  have ht2 : (LSub.ofSData d).t (↑i + 1) = d.t i.succ := by
    show (if h : (i : ℕ) + 1 ≤ d.n then d.t ⟨(i : ℕ) + 1, Nat.lt_succ_of_le h⟩ else 1) = d.t i.succ
    rw [dif_pos (show (i : ℕ) + 1 ≤ d.n from i.2)]
    exact congrArg d.t (Fin.ext rfl)
  rw [LSub.weight, hs, ht1, ht2]
  by_cases h : d.side i = Side.U <;> simp [h]

/-! ## The two-dimensional cell identity -/

/-- The four-term "cell" combination that appears in the grid argument. -/
def cellTerm {U V : Set X} (A B C D : H0 (U ∩ V)) (a b c d : ℤ) : H0 (U ∩ V) :=
  a • (B - A) + b • (C - B) - c • (C - D) + d • (A - D)

/-- When all four weights agree the cell combination vanishes. -/
theorem cellTerm_self {U V : Set X} (A B C D : H0 (U ∩ V)) (a : ℤ) :
    cellTerm A B C D a a a a = 0 := by
  have h : (B - A) + (C - B) - (C - D) + (A - D) = 0 := by abel
  have h2 : cellTerm A B C D a a a a = a • ((B - A) + (C - B) - (C - D) + (A - D)) := by
    rw [cellTerm]; module
  rw [h2, h, smul_zero]

/-- Cell combination with the four weights of a grid cell; the combination vanishes as soon as
the "top" and "left" weights can be replaced by the cell's own weight. -/
theorem cellTerm_eq {U V : Set X} {A B C D : H0 (U ∩ V)} {a b c d : ℤ}
    (h1 : b = a) (h2 : c = a ∨ C = D) (h3 : d = a ∨ A = D) :
    cellTerm A B C D a b c d = 0 := by
  have e2 : b • (C - B) = a • (C - B) := by rw [h1]
  have e3 : c • (C - D) = a • (C - D) := by
    rcases h2 with h2 | h2
    · rw [h2]
    · rw [h2]; simp
  have e4 : d • (A - D) = a • (A - D) := by
    rcases h3 with h3 | h3
    · rw [h3]
    · rw [h3]; simp
  rw [cellTerm, e2, e3, e4]
  exact cellTerm_self A B C D a

/-! ## The two-dimensional grid argument -/

section Grid

variable {n : ℕ}

/-- The label of the `j`-th piece of the row `i` of a grid, read off from a cell containing it. -/
def rowLab (hn : 0 < n) (lab : Fin n → Fin n → Side) (i : Fin (n + 1)) (j : Fin n) : Side :=
  lab ⟨min i.val (n - 1), by omega⟩ j

/-- The label of the `i`-th piece of the column `j` of a grid. -/
def colLab (hn : 0 < n) (lab : Fin n → Fin n → Side) (i : Fin n) (j : Fin (n + 1)) : Side :=
  lab i ⟨min j.val (n - 1), by omega⟩

/-- The vertices of a grid, as classes in `H₀(U ∩ V)`. -/
def gW (U V : Set X) (u : Fin (n + 1) → unitInterval)
    (H : unitInterval × unitInterval → X) (i j : Fin (n + 1)) : H0 (U ∩ V) :=
  h0cls (U ∩ V) (H (u i, u j))

/-- The weight of the `j`-th piece of the row `i`. -/
def rWeight (hn : 0 < n) (lab : Fin n → Fin n → Side) (i : Fin (n + 1)) (j : Fin n) : ℤ :=
  if rowLab hn lab i j = Side.U then 1 else 0

/-- The weight of the `i`-th piece of the column `j`. -/
def cWeight (hn : 0 < n) (lab : Fin n → Fin n → Side) (i : Fin n) (j : Fin (n + 1)) : ℤ :=
  if colLab hn lab i j = Side.U then 1 else 0

/-- The transfer of the `i`-th row of a grid. -/
def Row (U V : Set X) (hn : 0 < n) (u : Fin (n + 1) → unitInterval)
    (lab : Fin n → Fin n → Side) (H : unitInterval × unitInterval → X) (i : Fin (n + 1)) :
    H0 (U ∩ V) :=
  ∑ j : Fin n, rWeight hn lab i j • (gW U V u H i j.succ - gW U V u H i j.castSucc)

/-- The transfer of the boundary of the `(i, j)`-th grid cell. -/
def Cell (U V : Set X) (hn : 0 < n) (u : Fin (n + 1) → unitInterval)
    (lab : Fin n → Fin n → Side) (H : unitInterval × unitInterval → X) (i j : Fin n) :
    H0 (U ∩ V) :=
  rWeight hn lab i.castSucc j • (gW U V u H i.castSucc j.succ - gW U V u H i.castSucc j.castSucc)
  + cWeight hn lab i j.succ • (gW U V u H i.succ j.succ - gW U V u H i.castSucc j.succ)
  - rWeight hn lab i.succ j • (gW U V u H i.succ j.succ - gW U V u H i.succ j.castSucc)
  - cWeight hn lab i j.castSucc • (gW U V u H i.succ j.castSucc - gW U V u H i.castSucc j.castSucc)

/-- The index of the cell containing the `i`-th grid line (for rows). -/
def rk (hn : 0 < n) (i : Fin (n + 1)) : Fin n := ⟨min i.val (n - 1), by omega⟩

/-- The index of the cell containing the `j`-th grid line (for columns). -/
def ck (hn : 0 < n) (j : Fin (n + 1)) : Fin n := ⟨min j.val (n - 1), by omega⟩

theorem row_mem_cell {u : Fin (n + 1) → unitInterval} (hu : StrictMono u) (hn : 0 < n)
    (i : Fin (n + 1)) : u i ∈ Set.Icc (u (rk hn i).castSucc) (u (rk hn i).succ) := by
  refine ⟨?_, ?_⟩
  · rw [hu.le_iff_le]
    show (rk hn i).castSucc.val ≤ i.val
    rw [Fin.val_castSucc]
    show min i.val (n - 1) ≤ i.val
    omega
  · rw [hu.le_iff_le]
    show i.val ≤ (rk hn i).succ.val
    rw [Fin.val_succ]
    show i.val ≤ min i.val (n - 1) + 1
    omega

theorem col_mem_cell {u : Fin (n + 1) → unitInterval} (hu : StrictMono u) (hn : 0 < n)
    (j : Fin (n + 1)) : u j ∈ Set.Icc (u (ck hn j).castSucc) (u (ck hn j).succ) := by
  refine ⟨?_, ?_⟩
  · rw [hu.le_iff_le]
    show (ck hn j).castSucc.val ≤ j.val
    rw [Fin.val_castSucc]
    show min j.val (n - 1) ≤ j.val
    omega
  · rw [hu.le_iff_le]
    show j.val ≤ (ck hn j).succ.val
    rw [Fin.val_succ]
    show j.val ≤ min j.val (n - 1) + 1
    omega

theorem rowLab_castSucc (hn : 0 < n) (lab : Fin n → Fin n → Side) (i j : Fin n) :
    rowLab hn lab i.castSucc j = lab i j := by
  have h : (⟨min (i.castSucc : Fin (n + 1)).val (n - 1), by omega⟩ : Fin n) = i := by
    apply Fin.ext
    show min (i.castSucc : Fin (n + 1)).val (n - 1) = i.val
    rw [Fin.val_castSucc, min_eq_left (Nat.le_sub_one_of_lt i.2)]
  unfold rowLab
  rw [h]

theorem colLab_castSucc (hn : 0 < n) (lab : Fin n → Fin n → Side) (i : Fin n) (j : Fin n) :
    colLab hn lab i j.castSucc = lab i j := by
  have h : (⟨min (j.castSucc : Fin (n + 1)).val (n - 1), by omega⟩ : Fin n) = j := by
    apply Fin.ext
    show min (j.castSucc : Fin (n + 1)).val (n - 1) = j.val
    rw [Fin.val_castSucc, min_eq_left (Nat.le_sub_one_of_lt j.2)]
  unfold colLab
  rw [h]

theorem rowLab_zero (hn : 0 < n) [NeZero n] (lab : Fin n → Fin n → Side) (j : Fin n) :
    rowLab hn lab 0 j = lab 0 j := by
  have h : (⟨min (0 : Fin (n + 1)).val (n - 1), by omega⟩ : Fin n) = 0 := by
    apply Fin.ext
    show min (0 : Fin (n + 1)).val (n - 1) = (0 : Fin n).val
    simp
  unfold rowLab
  rw [h]

theorem rowLab_last (hn : 0 < n) (lab : Fin n → Fin n → Side) (j : Fin n) :
    rowLab hn lab (Fin.last n) j = lab ⟨n - 1, by omega⟩ j := by
  have h : (⟨min (Fin.last n).val (n - 1), by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    show min (Fin.last n).val (n - 1) = (⟨n - 1, by omega⟩ : Fin n).val
    simp
  unfold rowLab
  rw [h]

/-- Telescoping `Fin`-sums: the sums over `succ` and over `castSucc` differ by the end terms. -/
theorem sum_succ_sub_castSucc {M : Type*} [AddCommGroup M] (n : ℕ) (f : Fin (n + 1) → M) :
    (∑ j : Fin n, f j.succ) - (∑ j : Fin n, f j.castSucc) = f (Fin.last n) - f 0 := by
  have e1 : (∑ j : Fin n, f j.succ) = (∑ i : Fin (n + 1), f i) - f 0 := by
    rw [Fin.sum_univ_succ]; abel
  have e2 : (∑ j : Fin n, f j.castSucc) = (∑ i : Fin (n + 1), f i) - f (Fin.last n) := by
    rw [Fin.sum_univ_castSucc]; abel
  rw [e1, e2]; abel

/-- The horizontal path `t ↦ H (s, t)`. -/
def rowP (H : C(unitInterval × unitInterval, X)) (s : unitInterval) :
    Path (H (s, 0)) (H (s, 1)) where
  toFun := fun t => H (s, t)
  continuous_toFun := H.continuous.comp (continuous_const.prodMk continuous_id)
  source' := rfl
  target' := rfl

/-- The vertical path `s ↦ H (s, t)`. -/
def colP (H : C(unitInterval × unitInterval, X)) (t : unitInterval) :
    Path (H (0, t)) (H (1, t)) where
  toFun := fun s => H (s, t)
  continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
  source' := rfl
  target' := rfl

/-- **The two-dimensional argument.**  For a grid whose cells all map into `U` or into `V` and
whose left and right edges are the constant paths at `a` and `b`, the transfer of the bottom row
equals the transfer of the top row. -/
theorem mvGridRowEq {U V : Set X} {n : ℕ} (hn : 0 < n) (u : Fin (n + 1) → unitInterval)
    (hu : StrictMono u) (hu0 : u 0 = 0) (hun : u (Fin.last n) = 1)
    (lab : Fin n → Fin n → Side) (H : C(unitInterval × unitInterval, X)) {a b : X}
    (hcell : ∀ (i j : Fin n) (s t : unitInterval), s ∈ Set.Icc (u i.castSucc) (u i.succ) →
      t ∈ Set.Icc (u j.castSucc) (u j.succ) → H (s, t) ∈ Side.set U V (lab i j))
    (ha : ∀ s : unitInterval, H (s, 0) = a) (hb : ∀ s : unitInterval, H (s, 1) = b) :
    Row U V hn u lab H 0 = Row U V hn u lab H (Fin.last n) := by
  -- #### the classes at the shared edges agree when the two labels differ
  have top_edge : ∀ (i j : Fin n), rowLab hn lab i.succ j ≠ lab i j →
      gW U V u H i.succ j.succ = gW U V u H i.succ j.castSucc := by
    intro i j hne
    have hpiece : ∀ t ∈ Set.Icc (u j.castSucc) (u j.succ), (rowP H (u i.succ)) t ∈ U ∩ V := by
      intro t ht
      have h1 : H (u i.succ, t) ∈ Side.set U V (lab i j) := by
        refine hcell i j (u i.succ) t ?_ ht
        exact ⟨(hu Fin.castSucc_lt_succ).le, le_rfl⟩
      have h2 : H (u i.succ, t) ∈ Side.set U V (rowLab hn lab i.succ j) := by
        have := hcell (rk hn i.succ) j (u i.succ) t (row_mem_cell hu hn i.succ) ht
        simpa only [rowLab, rk] using this
      have hmem : H (u i.succ, t) ∈
          Side.set U V (rowLab hn lab i.succ j) ∩ Side.set U V (lab i j) := ⟨h2, h1⟩
      rwa [side_set_mono hne] at hmem
    have h := h0cls_eq_of_piece (γ := rowP H (u i.succ)) (p := u j.castSucc) (q := u j.succ)
      (hu Fin.castSucc_lt_succ).le hpiece
    exact h
  have right_edge : ∀ (i j : Fin n), colLab hn lab i j.succ ≠ lab i j →
      gW U V u H i.succ j.succ = gW U V u H i.castSucc j.succ := by
    intro i j hne
    have hpiece : ∀ s ∈ Set.Icc (u i.castSucc) (u i.succ), (colP H (u j.succ)) s ∈ U ∩ V := by
      intro s hs
      have h1 : H (s, u j.succ) ∈ Side.set U V (lab i j) := by
        refine hcell i j s (u j.succ) hs ?_
        exact ⟨(hu Fin.castSucc_lt_succ).le, le_rfl⟩
      have h2 : H (s, u j.succ) ∈ Side.set U V (colLab hn lab i j.succ) := by
        have := hcell i (ck hn j.succ) s (u j.succ) hs (col_mem_cell hu hn j.succ)
        simpa only [colLab, ck] using this
      have hmem : H (s, u j.succ) ∈
          Side.set U V (colLab hn lab i j.succ) ∩ Side.set U V (lab i j) := ⟨h2, h1⟩
      rwa [side_set_mono hne] at hmem
    have h := h0cls_eq_of_piece (γ := colP H (u j.succ)) (p := u i.castSucc) (q := u i.succ)
      (hu Fin.castSucc_lt_succ).le hpiece
    exact h
  -- #### every cell term vanishes
  have cell_zero : ∀ i j : Fin n, Cell U V hn u lab H i j = 0 := by
    intro i j
    have h1 : rWeight hn lab i.castSucc j = (if lab i j = Side.U then (1 : ℤ) else 0) := by
      rw [rWeight, rowLab_castSucc]
    have h4 : cWeight hn lab i j.castSucc = (if lab i j = Side.U then (1 : ℤ) else 0) := by
      rw [cWeight, colLab_castSucc]
    have h2 : cWeight hn lab i j.succ • (gW U V u H i.succ j.succ - gW U V u H i.castSucc j.succ)
        = (if lab i j = Side.U then (1 : ℤ) else 0) •
          (gW U V u H i.succ j.succ - gW U V u H i.castSucc j.succ) := by
      by_cases hcase : colLab hn lab i j.succ = lab i j
      · rw [cWeight, hcase]
      · have hz := right_edge i j hcase
        rw [hz]
        simp
    have h3 : rWeight hn lab i.succ j • (gW U V u H i.succ j.succ - gW U V u H i.succ j.castSucc)
        = (if lab i j = Side.U then (1 : ℤ) else 0) •
          (gW U V u H i.succ j.succ - gW U V u H i.succ j.castSucc) := by
      by_cases hcase : rowLab hn lab i.succ j = lab i j
      · rw [rWeight, hcase]
      · have hz := top_edge i j hcase
        rw [hz]
        simp
    rw [Cell, h1, h2, h3, h4]
    have hA : ((gW U V u H i.castSucc j.succ - gW U V u H i.castSucc j.castSucc)
        + (gW U V u H i.succ j.succ - gW U V u H i.castSucc j.succ)
        - (gW U V u H i.succ j.succ - gW U V u H i.succ j.castSucc)
        - (gW U V u H i.succ j.castSucc - gW U V u H i.castSucc j.castSucc) : H0 (U ∩ V)) = 0 := by abel
    rw [← smul_add, ← smul_sub, ← smul_sub, hA, smul_zero]
  -- #### summing the cells of one horizontal band
  have sum_cell : ∀ i : Fin n, (∑ j : Fin n, Cell U V hn u lab H i j)
      = Row U V hn u lab H i.castSucc - Row U V hn u lab H i.succ := by
    intro i
    have hexp : (∑ j : Fin n, Cell U V hn u lab H i j)
        = (∑ j : Fin n, rWeight hn lab i.castSucc j •
            (gW U V u H i.castSucc j.succ - gW U V u H i.castSucc j.castSucc))
          + (∑ j : Fin n, cWeight hn lab i j.succ •
            (gW U V u H i.succ j.succ - gW U V u H i.castSucc j.succ))
          - (∑ j : Fin n, rWeight hn lab i.succ j •
            (gW U V u H i.succ j.succ - gW U V u H i.succ j.castSucc))
          - (∑ j : Fin n, cWeight hn lab i j.castSucc •
            (gW U V u H i.succ j.castSucc - gW U V u H i.castSucc j.castSucc)) := by
      simp only [Cell]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have htel : (∑ j : Fin n, cWeight hn lab i j.succ •
            (gW U V u H i.succ j.succ - gW U V u H i.castSucc j.succ))
          - (∑ j : Fin n, cWeight hn lab i j.castSucc •
            (gW U V u H i.succ j.castSucc - gW U V u H i.castSucc j.castSucc)) = 0 := by
      have hY : (∑ j : Fin n, cWeight hn lab i j.succ •
            (gW U V u H i.succ j.succ - gW U V u H i.castSucc j.succ))
          = ∑ j : Fin n, (fun k : Fin (n + 1) =>
              cWeight hn lab i k • (gW U V u H i.succ k - gW U V u H i.castSucc k)) j.succ := rfl
      have hW : (∑ j : Fin n, cWeight hn lab i j.castSucc •
            (gW U V u H i.succ j.castSucc - gW U V u H i.castSucc j.castSucc))
          = ∑ j : Fin n, (fun k : Fin (n + 1) =>
              cWeight hn lab i k • (gW U V u H i.succ k - gW U V u H i.castSucc k)) j.castSucc := rfl
      have h0 : cWeight hn lab i 0 • (gW U V u H i.succ 0 - gW U V u H i.castSucc 0) = 0 := by
        have e1 : gW U V u H i.succ 0 = h0cls (U ∩ V) a := by simp only [gW, hu0, ha]
        have e2 : gW U V u H i.castSucc 0 = h0cls (U ∩ V) a := by simp only [gW, hu0, ha]
        rw [e1, e2, sub_self, smul_zero]
      have hlast : cWeight hn lab i (Fin.last n) •
          (gW U V u H i.succ (Fin.last n) - gW U V u H i.castSucc (Fin.last n)) = 0 := by
        have e1 : gW U V u H i.succ (Fin.last n) = h0cls (U ∩ V) b := by simp only [gW, hun, hb]
        have e2 : gW U V u H i.castSucc (Fin.last n) = h0cls (U ∩ V) b := by simp only [gW, hun, hb]
        rw [e1, e2, sub_self, smul_zero]
      rw [hY, hW]
      have := sum_succ_sub_castSucc n (fun k : Fin (n + 1) =>
        cWeight hn lab i k • (gW U V u H i.succ k - gW U V u H i.castSucc k))
      rw [this]
      beta_reduce
      rw [hlast, h0, sub_zero]
    rw [hexp, Row, Row]
    rw [show ∀ (p q r s : H0 (U ∩ V)), p + q - r - s = (p - r) + (q - s) from
      fun p q r s => by abel, htel, add_zero]
  -- #### conclude
  have hstep : ∀ i : Fin n, Row U V hn u lab H i.castSucc = Row U V hn u lab H i.succ := by
    intro i
    have h := sum_cell i
    rw [Finset.sum_eq_zero (fun j _ => cell_zero i j)] at h
    exact sub_eq_zero.mp h.symm
  have hall : ∀ k : Fin (n + 1), Row U V hn u lab H k = Row U V hn u lab H 0 := by
    intro k
    induction k using Fin.induction with
    | zero => rfl
    | succ i ih => rw [← hstep i]; exact ih
  exact (hall (Fin.last n)).symm

end Grid

end

end Work.SphereJordan
