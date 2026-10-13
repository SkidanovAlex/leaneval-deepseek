/-
  WilG5 — definitions shared by the cell-parametrisation modules.

  New notions fixed here (all of them are used by several modules above):

  * `vgraph ρ` — the *graph of a vector valued map* `ρ : ℝ^d → ℝ^n`, as a subset of
    `ℝ^{d+n}` (input coordinates first, output coordinates last).  Cell parametrisations are
    `Ω`-definable *relations* of this shape; the paper's `f ∈ Ω_{F,D}` for a function is
    `graphOf f ∈ Ω_{F,D}` (in `Defs.lean`), and `vgraph` is its vector valued analogue.

  * `funeqSet ι₁ ι₂` — the set where two coordinate selections agree, `x (ι₁ i) = x (ι₂ i)`.

  * `endsInf X`, `endsSup X` — the graphs of the lower/upper ends of the fibres of `X`.  The
    `Ω`-membership of these two sets (`Work.WilG5.Fibre.ends_mem`) is the tool that makes cell
    parametrisations definable: the free coordinate of a cell is swept out by a convex
    combination of the two fibre ends.

  * `RelSel R` — the function selected by a relation.  Cell data are relations (single-valued
    only on the open cube); `RelSel` turns them into functions, and `vgraph_RelSel` records
    that the graph of the selected function is `R` together with the constant `0` outside the
    projection of `R`.  That complement is what makes the *global* graph `Ω`-definable — which
    is what the F-lemma consumes.

  * `embSnoc e : Fin (d+1) → Fin (n+1)` — the free coordinates of a cell after adding the last
    coordinate as a new free one (the band step of the cell recursion); `embCastSucc e` is the
    graph step (no new free coordinate).

  * `CellPar n κ d e R` — the parametrisation predicate: `R` parametrises `κ` from the open
    `d`-cube, with `e` listing the free coordinates in increasing order.

  Conventions are those of `Basic`: `Fin (p+q) → ℝ` with `Fin.castAdd q` for the first `p`
  coordinates and `Fin.natAdd p` for the last `q`.
-/
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG5.Reindex2
import Submission.Work.WilG5.Reindex3

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG5

open WilkiesDesign WilkiesConjecture

variable {S : SOMin}

/-! ## 0. Splitting a point into its first `d` and last `n` coordinates -/

theorem append_self {d n : ℕ} (z : Fin (d + n) → ℝ) :
    Fin.append (fun i : Fin d => z (Fin.castAdd n i))
      (fun j : Fin n => z (Fin.natAdd d j)) = z := by
  funext k
  rcases lt_or_ge k.val d with h | h
  · have hk : k = Fin.castAdd n ⟨k.val, h⟩ := Fin.ext rfl
    rw [hk, Fin.append_left]
  · have hk : k = Fin.natAdd d ⟨k.val - d, by omega⟩ :=
      Fin.ext (show k.val = d + (k.val - d) from by omega)
    rw [hk, Fin.append_right]

/-! ## 1. Graphs of vector valued maps -/

/-- Graph of `ρ : ℝ^d → ℝ^n` inside `ℝ^{d+n}`: first `d` coordinates = input, last `n` =
output. -/
def vgraph {d n : ℕ} (ρ : (Fin d → ℝ) → (Fin n → ℝ)) : Set (Fin (d + n) → ℝ) :=
  {z | ρ (fun i => z (Fin.castAdd n i)) = (fun j => z (Fin.natAdd d j))}

theorem vgraph_iff {d n : ℕ} (ρ : (Fin d → ℝ) → (Fin n → ℝ)) (z : Fin (d + n) → ℝ) :
    z ∈ vgraph ρ ↔ ρ (fun i => z (Fin.castAdd n i)) = (fun j => z (Fin.natAdd d j)) := Iff.rfl

theorem vgraph_apply {d n : ℕ} {ρ : (Fin d → ℝ) → (Fin n → ℝ)} {z : Fin (d + n) → ℝ}
    (h : z ∈ vgraph ρ) (j : Fin n) :
    ρ (fun i => z (Fin.castAdd n i)) j = z (Fin.natAdd d j) :=
  congrFun h j

theorem vgraph_append {d n : ℕ} (ρ : (Fin d → ℝ) → (Fin n → ℝ)) (u : Fin d → ℝ)
    (x : Fin n → ℝ) : Fin.append u x ∈ vgraph ρ ↔ ρ u = x := by
  rw [vgraph_iff]
  rw [show (fun i : Fin d => Fin.append u x (Fin.castAdd n i)) = u from by
        funext i; rw [Fin.append_left],
      show (fun j : Fin n => Fin.append u x (Fin.natAdd d j)) = x from by
        funext j; rw [Fin.append_right]]

theorem vgraph_inj {d n : ℕ} {ρ σ : (Fin d → ℝ) → (Fin n → ℝ)} (h : vgraph ρ = vgraph σ) :
    ρ = σ := by
  funext u
  have h1 : Fin.append u (ρ u) ∈ vgraph ρ := (vgraph_append ρ u (ρ u)).2 rfl
  rw [h] at h1
  exact ((vgraph_append σ u (ρ u)).1 h1).symm

/-! ## 2. Coordinate-identification sets -/

/-- The set of `x` with `x (ι₁ i) = x (ι₂ i)` for all `i`. -/
def funeqSet {N m : ℕ} (ι₁ ι₂ : Fin m → Fin N) : Set (Fin N → ℝ) :=
  {x | ∀ i : Fin m, x (ι₁ i) = x (ι₂ i)}

theorem funeqSet_mem {N m : ℕ} (ι₁ ι₂ : Fin m → Fin N) :
    funeqSet ι₁ ι₂ ∈ S.Ω (4 * (N + N) + 8) (2 * m + 4) N := by
  have hsingle : ∀ i : Fin m,
      {x : Fin N → ℝ | x (ι₁ i) = x (ι₂ i)} ∈ S.Ω N 1 N := by
    intro i
    have hdeg : ((MvPolynomial.X (ι₁ i) - MvPolynomial.X (ι₂ i) :
        MvPolynomial (Fin N) ℝ)).totalDegree ≤ 1 :=
      le_trans (td_sub_le _ _) (max_le (td_X_le _) (td_X_le _))
    have heq : {x : Fin N → ℝ | x (ι₁ i) = x (ι₂ i)} =
        {z : Fin N → ℝ | MvPolynomial.eval z (MvPolynomial.X (ι₁ i) -
          MvPolynomial.X (ι₂ i) : MvPolynomial (Fin N) ℝ) = 0} := by
      ext z
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact mem_mono (S.hyp N (MvPolynomial.X (ι₁ i) - MvPolynomial.X (ι₂ i) :
      MvPolynomial (Fin N) ℝ)) N 1 (le_refl _) hdeg
  have hmem : (⋂ i : Fin m, {x : Fin N → ℝ | x (ι₁ i) = x (ι₂ i)}) ∈
      S.Ω (N + 1) (∑ _ : Fin m, 1) N :=
    S.inter (fun _ : Fin m => 1) (fun i => {x : Fin N → ℝ | x (ι₁ i) = x (ι₂ i)})
      (fun i => hsingle i)
  have hsum : (∑ _ : Fin m, 1) = m := by simp
  rw [hsum] at hmem
  have heq : funeqSet ι₁ ι₂ = ⋂ i : Fin m, {x : Fin N → ℝ | x (ι₁ i) = x (ι₂ i)} := by
    ext z; simp [funeqSet]
  rw [heq]
  exact mem_mono hmem (4 * (N + N) + 8) (2 * m + 4) (by omega) (by omega)

/-- A single vanishing coordinate is an `Ω`-set. -/
theorem zeroCoord_mem {N : ℕ} (i : Fin N) :
    {z : Fin N → ℝ | z i = 0} ∈ S.Ω N 1 N := by
  have heq : {z : Fin N → ℝ | z i = 0} = {z : Fin N → ℝ |
      MvPolynomial.eval z (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) = 0} := by
    ext z; simp
  rw [heq]
  exact mem_mono (S.hyp N (MvPolynomial.X i : MvPolynomial (Fin N) ℝ)) N 1 (le_refl _)
    (td_X_le i)

/-- The last `n` coordinates all vanish, as an `Ω`-set.  This is the extra piece in
`vgraph_RelSel`. -/
theorem zeroTail_mem {d n : ℕ} :
    {z : Fin (d + n) → ℝ | (fun j : Fin n => z (Fin.natAdd d j)) = 0} ∈
      S.Ω (d + n + 1) (2 * n + 4) (d + n) := by
  have h := S.inter (fun _ : Fin n => 1)
    (fun j : Fin n => {z : Fin (d + n) → ℝ | z (Fin.natAdd d j) = 0})
    (fun j => zeroCoord_mem (S := S) (Fin.natAdd d j))
  rw [show (∑ _ : Fin n, 1) = n from by simp] at h
  have heq : (⋂ j : Fin n, {z : Fin (d + n) → ℝ | z (Fin.natAdd d j) = 0}) =
      {z : Fin (d + n) → ℝ | (fun j : Fin n => z (Fin.natAdd d j)) = 0} := by
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, funext_iff, Pi.zero_apply]
  rw [← heq]
  exact mem_mono h _ _ (by omega) (by omega)

/-! ## 3. Selecting a function from a single-valued relation -/

/-- The value selected by the relation `R`: the unique `x` with `(u,x) ∈ R`, and `0` if there
is none. -/
def RelSel {d n : ℕ} (R : Set (Fin (d + n) → ℝ)) (u : Fin d → ℝ) : Fin n → ℝ :=
  if h : ∃ x : Fin n → ℝ, Fin.append u x ∈ R then Classical.choose h else 0

theorem RelSel_spec {d n : ℕ} {R : Set (Fin (d + n) → ℝ)} {u : Fin d → ℝ}
    (h : ∃ x : Fin n → ℝ, Fin.append u x ∈ R) : Fin.append u (RelSel R u) ∈ R := by
  unfold RelSel
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem RelSel_eq {d n : ℕ} {R : Set (Fin (d + n) → ℝ)} {u : Fin d → ℝ} {x : Fin n → ℝ}
    (h : Fin.append u x ∈ R) (hu : ∀ y : Fin n → ℝ, Fin.append u y ∈ R → y = x) :
    RelSel R u = x := by
  have hex : ∃ y : Fin n → ℝ, Fin.append u y ∈ R := ⟨x, h⟩
  exact hu _ (RelSel_spec (R := R) hex)

/-- The graph of the selected function is `R` together with the constant `0` over the points
outside the projection of `R`. -/
theorem vgraph_RelSel {d n : ℕ} (R : Set (Fin (d + n) → ℝ))
    (huniq : ∀ u : Fin d → ℝ, (∃ x : Fin n → ℝ, Fin.append u x ∈ R) →
      ∀ x y : Fin n → ℝ, Fin.append u x ∈ R → Fin.append u y ∈ R → x = y) :
    vgraph (RelSel R) = R ∪ {z : Fin (d + n) → ℝ |
      (¬ ∃ x : Fin n → ℝ, Fin.append (fun i => z (Fin.castAdd n i)) x ∈ R) ∧
      (fun j : Fin n => z (Fin.natAdd d j)) = 0} := by
  have hzz : ∀ z : Fin (d + n) → ℝ,
      Fin.append (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd d j)) = z :=
    fun z => append_self z
  ext z
  rw [vgraph_iff]
  constructor
  · intro hv
    by_cases hex : ∃ x : Fin n → ℝ, Fin.append (fun i => z (Fin.castAdd n i)) x ∈ R
    · left
      have hspec := RelSel_spec (R := R) hex
      rw [hv] at hspec
      rwa [hzz z] at hspec
    · right
      refine ⟨hex, ?_⟩
      have h0 : RelSel R (fun i => z (Fin.castAdd n i)) = 0 := by
        unfold RelSel; rw [dite_eq_right hex]
      rw [← hv, h0]
  · rintro (hzR | ⟨hno, hzero⟩)
    · have hex : ∃ x : Fin n → ℝ, Fin.append (fun i => z (Fin.castAdd n i)) x ∈ R :=
        ⟨fun j => z (Fin.natAdd d j), by rw [hzz z]; exact hzR⟩
      have hRS : RelSel R (fun i => z (Fin.castAdd n i)) = Classical.choose hex := by
        unfold RelSel; rw [dite_eq_left hex]
      have hspec : Fin.append (fun i => z (Fin.castAdd n i)) (Classical.choose hex) ∈ R := by
        rw [← hRS]; exact RelSel_spec (R := R) hex
      have hxy := huniq _ hex (Classical.choose hex) (fun j => z (Fin.natAdd d j)) hspec
        (by rw [hzz z]; exact hzR)
      rw [hRS, hxy]
    · have h0 : RelSel R (fun i => z (Fin.castAdd n i)) = 0 := by
        unfold RelSel; rw [dite_eq_right hno]
      rw [h0, hzero]

/-! ## 4. Fibre ends -/

/-- The graph of the lower end of the fibre of `X ⊆ ℝ^{n+1}`: the last coordinate is the
infimum of `{w ∈ [0,1] : (z', w) ∈ X}`, where `z'` is the first `n` coordinates of `z`. -/
def endsInf {n : ℕ} (X : Set (Fin (n + 1) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {z | 0 ≤ z (Fin.last n) ∧ z (Fin.last n) ≤ 1 ∧
    (∀ w : ℝ, 0 ≤ w → w ≤ 1 → Fin.snoc (Fin.init z) w ∈ X → z (Fin.last n) ≤ w) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ Fin.snoc (Fin.init z) w ∈ X ∧
      w < z (Fin.last n) + ε)}

/-- The graph of the upper end of the fibre of `X ⊆ ℝ^{n+1}`. -/
def endsSup {n : ℕ} (X : Set (Fin (n + 1) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {z | 0 ≤ z (Fin.last n) ∧ z (Fin.last n) ≤ 1 ∧
    (∀ w : ℝ, 0 ≤ w → w ≤ 1 → Fin.snoc (Fin.init z) w ∈ X → w ≤ z (Fin.last n)) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ Fin.snoc (Fin.init z) w ∈ X ∧
      z (Fin.last n) - ε < w)}

/-! ## 5. Free-coordinate embeddings for the cell recursion -/

/-- A `Fin d → Fin n` map, viewed as a `Fin d → Fin (n+1)` map (the graph step). -/
def embCastSucc {d n : ℕ} (e : Fin d → Fin n) : Fin d → Fin (n + 1) :=
  fun i => Fin.castSucc (e i)

/-- Extend a free-coordinate map by the new last coordinate (the band step). -/
def embSnoc {d n : ℕ} (e : Fin d → Fin n) : Fin (d + 1) → Fin (n + 1) :=
  fun i => if h : i.val < d then Fin.castSucc (e ⟨i.val, h⟩) else Fin.last n

theorem embSnoc_castSucc {d n : ℕ} (e : Fin d → Fin n) (i : Fin d) :
    embSnoc e (Fin.castSucc i) = Fin.castSucc (e i) := by
  unfold embSnoc
  rw [dite_eq_left (by simp)]
  exact congrArg Fin.castSucc (congrArg e (Fin.ext rfl))

theorem embSnoc_last {d n : ℕ} (e : Fin d → Fin n) :
    embSnoc e (Fin.last d) = Fin.last n := by
  unfold embSnoc
  rw [dite_eq_right (by simp)]

theorem embSnoc_injective {d n : ℕ} {e : Fin d → Fin n} (he : Function.Injective e) :
    Function.Injective (embSnoc e) := by
  intro i j hij
  by_cases hi : i.val < d
  · by_cases hj : j.val < d
    · rw [show i = Fin.castSucc ⟨i.val, hi⟩ from (Fin.ext rfl).symm,
          show j = Fin.castSucc ⟨j.val, hj⟩ from (Fin.ext rfl).symm] at hij ⊢
      rw [embSnoc_castSucc, embSnoc_castSucc] at hij
      have h1 : ((Fin.castSucc (e ⟨i.val, hi⟩))).val = ((Fin.castSucc (e ⟨j.val, hj⟩))).val :=
        congrArg Fin.val hij
      have h1' : (e ⟨i.val, hi⟩).val = (e ⟨j.val, hj⟩).val := h1
      exact congrArg Fin.castSucc (he (Fin.ext h1'))
    · exfalso
      have hj' : j = Fin.last d := Fin.ext (by show j.val = d; omega)
      rw [show i = Fin.castSucc ⟨i.val, hi⟩ from (Fin.ext rfl).symm, hj'] at hij
      rw [embSnoc_castSucc, embSnoc_last] at hij
      have h1 : ((Fin.castSucc (e ⟨i.val, hi⟩))).val = (Fin.last n).val := congrArg Fin.val hij
      have h1' : (e ⟨i.val, hi⟩).val = n := h1
      have h2 := (e ⟨i.val, hi⟩).isLt
      omega
  · by_cases hj : j.val < d
    · exfalso
      have hi' : i = Fin.last d := Fin.ext (by show i.val = d; omega)
      rw [hi', show j = Fin.castSucc ⟨j.val, hj⟩ from (Fin.ext rfl).symm] at hij
      rw [embSnoc_castSucc, embSnoc_last] at hij
      have h1 : ((Fin.castSucc (e ⟨j.val, hj⟩))).val = (Fin.last n).val :=
        congrArg Fin.val hij.symm
      have h1' : (e ⟨j.val, hj⟩).val = n := h1
      have h2 := (e ⟨j.val, hj⟩).isLt
      omega
    · have hi' : i = Fin.last d := Fin.ext (by show i.val = d; omega)
      have hj' : j = Fin.last d := Fin.ext (by show j.val = d; omega)
      rw [hi', hj']

/-! ## 6. The cell parametrisation predicate -/

/-- `CellPar n κ d e R`: the relation `R ⊆ ℝ^{d+n}` parametrises the set `κ ⊆ ℝ^n` from the
open `d`-cube, with `e : Fin d → Fin n` listing the *free* coordinates.

The relation is single-valued and nonempty-valued on the cube, its values lie in `κ`, and it is
surjective onto `κ`.  Clause 5 says that the free coordinates of every point of `κ` lie in the
open cube, and clause 6 is the "local surjectivity" (or continuity) property of the
parametrisation: arbitrarily close to a point `y ∈ κ` one can realise any prescribed value of
the free coordinates near `y ∘ e`, *within the open cube*.  Clauses 5 and 6 together say that
the projection of `κ` onto its free coordinates is open around every point of `κ`, which is what
makes the parametrisation usable for dimension statements (`cell_dim`): if `d ≥ μ + 1` then any
`μ + 1` free coordinates give a projection of `X ⊇ κ` with non-empty interior, contradicting
`DimLE X μ`. -/
def CellPar (n : ℕ) (κ : Set (Fin n → ℝ)) (d : ℕ) (e : Fin d → Fin n)
    (R : Set (Fin (d + n) → ℝ)) : Prop :=
  (∀ u ∈ openCube d, ∀ x : Fin n → ℝ, Fin.append u x ∈ R → x ∈ κ) ∧
  (∀ u ∈ openCube d, ∀ x y : Fin n → ℝ, Fin.append u x ∈ R → Fin.append u y ∈ R → x = y) ∧
  (∀ u ∈ openCube d, ∃ x : Fin n → ℝ, Fin.append u x ∈ R) ∧
  (∀ x ∈ κ, ∃ u ∈ openCube d, Fin.append u x ∈ R) ∧
  (∀ y ∈ κ, (fun i => y (e i)) ∈ openCube d) ∧
  (∀ y ∈ κ, ∀ η > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ v ∈ openCube d,
      (∀ i, |v i - y (e i)| < ε) →
      ∃ z : Fin n → ℝ, Fin.append v z ∈ R ∧ (∀ j, |z j - y j| < η) ∧ ∀ i, z (e i) = v i)

/-! ## 7. Uniform bounds for the fibre-end sets -/

/-- Uniform `Ω`-bounds for the two fibre-end sets `endsInf`, `endsSup`: the format gain is a
constant independent of the degree, and the degree gain is a constant. -/
def EndsMem (S : SOMin) : Prop :=
  ∀ (m F : ℕ), ∃ (A L : ℕ), ∀ (D : ℕ) (Y : Set (Fin (m + 1) → ℝ)), Y ∈ S.Ω F D (m + 1) →
    endsInf Y ∈ S.Ω (A + F) (D + L) (m + 1) ∧ endsSup Y ∈ S.Ω (A + F) (D + L) (m + 1)

/-! ## 8. The fibre structure of a band cell -/

/-- The fibre of a band cell is the open interval between the two fibre ends, and those ends are
continuous functions of the base point.  `C` is the base cell, `a`, `b` the `EReal` band bounds
of the cell, `κ` the cell.  The hypothesis `κ ⊆ cube01 (m+1)` is what makes the ends real (they
are automatically in `[0,1]`). -/
def BandFib : Prop :=
  ∀ (m : ℕ) (C : Set (Fin m → ℝ)) (a b : (Fin m → ℝ) → EReal),
    (∀ y ∈ C, a y < b y) → ∀ (κ : Set (Fin (m + 1) → ℝ)),
    κ = {z : Fin (m + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
      ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z)} →
    κ ⊆ cube01 (m + 1) →
    ∃ α β : (Fin m → ℝ) → ℝ,
      (∀ y ∈ C, Fin.snoc y (α y) ∈ endsInf κ) ∧
      (∀ y ∈ C, Fin.snoc y (β y) ∈ endsSup κ) ∧
      (∀ y ∈ C, ∀ r : ℝ, Fin.snoc y r ∈ endsInf κ → r = α y) ∧
      (∀ y ∈ C, ∀ r : ℝ, Fin.snoc y r ∈ endsSup κ → r = β y) ∧
      (∀ y ∈ C, ∀ x : Fin (m + 1) → ℝ, Fin.init x = y →
        (x ∈ κ ↔ α y < x (Fin.last m) ∧ x (Fin.last m) < β y)) ∧
      (∀ y ∈ C, ∀ η > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ y' ∈ C, (∀ i, |y' i - y i| < δ) →
        |α y' - α y| < η ∧ |β y' - β y| < η)

/-! ## 9. Padding a parametrisation to a larger source cube -/

/-- Extend a relation `R ⊆ ℝ^{d+n}` to `ℝ^{μ+n}` (`d ≤ μ`) by only reading the first `d`
coordinates of the parameter. -/
def padRel {d n μ : ℕ} (h : d ≤ μ) (R : Set (Fin (d + n) → ℝ)) : Set (Fin (μ + n) → ℝ) :=
  {z | Fin.append (fun i : Fin d => z (Fin.castAdd n (Fin.castLE h i)))
        (fun j : Fin n => z (Fin.natAdd μ j)) ∈ R}

end Work.WilG5
