/-
  WilG4c — BNZ §§5.2–5.5, the induction step `G4_step` of the algebraic lemma.

  This file fixes the vocabulary of the area:

  * the splitting of `ℝ^{n+1}` into `y` (initial coordinates) and `x` (last coordinate);
  * the family/chart conventions of `WilkiesDesign.CG.FLem`;
  * the hypotheses `YBound`, `LipOnCube`, `NormLeOne`, `NormLeOneDef` that the four
    reductions of §§5.2–5.5 add (“without loss of generality we may assume …”);
  * `FLemP`, the F-lemma with a supplementary hypothesis, so that each reduction becomes
    an implication `FLemP P' → FLemP P` between statements of exactly the frozen shape.

  Everything else in `Submission/Work/WilG4c` builds on this file.
-/
import Submission.Work.Wilkies.CG.Spec
import Mathlib.Analysis.Calculus.FDeriv.Comp

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The `(x, y)` splitting of `ℝ^{n+1}`

The first coordinate is the distinguished `x`; the remaining `n` coordinates are the `y`'s.
This matches `WilkiesDesign.CG.G4_bdd_dx`, which splits its variables as `Fin.cons x y`. -/

/-- The point of `ℝ^{n+1}` with first coordinate `x` and remaining coordinates `y`. -/
def pt {n : ℕ} (x : ℝ) (y : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cons x y

@[simp] theorem pt_zero {n : ℕ} (x : ℝ) (y : Fin n → ℝ) : pt x y 0 = x := by simp [pt]

@[simp] theorem pt_succ {n : ℕ} (x : ℝ) (y : Fin n → ℝ) (i : Fin n) : pt x y i.succ = y i := by
  simp [pt]

theorem tail_pt {n : ℕ} (x : ℝ) (y : Fin n → ℝ) : Fin.tail (pt x y) = y := by simp [pt]

theorem pt_eta {n : ℕ} (z : Fin (n + 1) → ℝ) : pt (z 0) (Fin.tail z) = z := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ j => rfl

theorem pt_injective {n : ℕ} {x x' : ℝ} {y y' : Fin n → ℝ} (h : pt x y = pt x' y') :
    x = x' ∧ y = y' :=
  ⟨by rw [← pt_zero x y, h, pt_zero], by rw [← tail_pt x y, h, tail_pt]⟩

/-- The `y`-slice of a function of `n+1` variables at fixed first coordinate `x`. -/
def slice {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ) (x : ℝ) : (Fin n → ℝ) → ℝ := fun y => g (pt x y)

theorem slice_apply {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    slice g x y = g (pt x y) := rfl

/-- The parameter obtained by adjoining the extra parameter `x` at the end. -/
def parSnoc {p : ℕ} (l : Fin p → ℝ) (x : ℝ) : Fin (p + 1) → ℝ := Fin.snoc l x

@[simp] theorem parSnoc_castSucc {p : ℕ} (l : Fin p → ℝ) (x : ℝ) (i : Fin p) :
    parSnoc l x i.castSucc = l i := by simp [parSnoc]

@[simp] theorem parSnoc_last {p : ℕ} (l : Fin p → ℝ) (x : ℝ) : parSnoc l x (Fin.last p) = x := by
  simp [parSnoc]

/-! ## 2. Families, charts and their two encodings -/

/-- A `k`-tuple of functions of `n` variables over the parameter space `ℝ^p`. This is exactly
the type of the family in `WilkiesDesign.CG.FLem`. -/
abbrev Family (k p n : ℕ) : Type := Fin k → (Fin p → ℝ) → (Fin n → ℝ) → ℝ

/-- A tuple of `n` charts of the cube, in the spelling used by the frozen `FLem`. -/
abbrev ChartTuple (p n : ℕ) : Type := Fin n → (Fin p → ℝ) → (Fin n → ℝ) → ℝ

/-- A single self-map of the cube over the parameter space. -/
abbrev PtMap (p n : ℕ) : Type := (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)

/-- The point form of a chart tuple. -/
def toPt {p n : ℕ} (φ : ChartTuple p n) : PtMap p n := fun l t => fun j => φ j l t

/-- The tuple form of a point map. -/
def ofPt {p n : ℕ} (Φ : PtMap p n) : ChartTuple p n := fun j l t => Φ l t j

@[simp] theorem ofPt_toPt {p n : ℕ} (φ : ChartTuple p n) : ofPt (toPt φ) = φ := rfl

@[simp] theorem toPt_ofPt {p n : ℕ} (Φ : PtMap p n) : toPt (ofPt Φ) = Φ := rfl

@[simp] theorem toPt_apply {p n : ℕ} (φ : ChartTuple p n) (l : Fin p → ℝ) (t : Fin n → ℝ)
    (j : Fin n) : toPt φ l t j = φ j l t := rfl

@[simp] theorem ofPt_apply {p n : ℕ} (Φ : PtMap p n) (j : Fin n) (l : Fin p → ℝ)
    (t : Fin n → ℝ) : ofPt Φ j l t = Φ l t j := rfl

/-- The identification of point maps with chart tuples. -/
def chartEquiv (p n : ℕ) : PtMap p n ≃ ChartTuple p n where
  toFun := ofPt
  invFun := toPt
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem chartEquiv_apply {p n : ℕ} (Φ : PtMap p n) : chartEquiv p n Φ = ofPt Φ := rfl

@[simp] theorem chartEquiv_symm_apply {p n : ℕ} (φ : ChartTuple p n) :
    (chartEquiv p n).symm φ = toPt φ := rfl

/-- Turning a finite set of point maps into a finite set of chart tuples, preserving cardinality. -/
def chartFinset {p n : ℕ} (Φ : Finset (PtMap p n)) : Finset (ChartTuple p n) :=
  Φ.map (chartEquiv p n).toEmbedding

@[simp] theorem chartFinset_card {p n : ℕ} (Φ : Finset (PtMap p n)) :
    (chartFinset Φ).card = Φ.card := by
  simp [chartFinset]

theorem mem_chartFinset {p n : ℕ} {Φ : Finset (PtMap p n)} {φ : ChartTuple p n} :
    φ ∈ chartFinset Φ ↔ toPt φ ∈ Φ := by
  rw [chartFinset, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨toPt φ, h, by simp⟩

/-! ## 3. Monotonicity of the filtration `Ω` -/

theorem Omega_mono_F_le (S : SOMin) : ∀ {F F' D n : ℕ} {X : Set (Fin n → ℝ)}, F ≤ F' →
    X ∈ S.Ω F D n → X ∈ S.Ω F' D n := by
  intro F F' D n X h
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction e with
  | zero => intro hX; simpa using hX
  | succ e ih => intro hX; rw [Nat.add_succ]; exact S.mono_F (ih hX)

theorem Omega_mono_D_le (S : SOMin) : ∀ {F D D' n : ℕ} {X : Set (Fin n → ℝ)}, D ≤ D' →
    X ∈ S.Ω F D n → X ∈ S.Ω F D' n := by
  intro F D D' n X h
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction e with
  | zero => intro hX; simpa using hX
  | succ e ih => intro hX; rw [Nat.add_succ]; exact S.mono_D (ih hX)

/-- The `Ω`-filtration is monotone in both the format and the degree. -/
theorem Omega_mono_le (S : SOMin) {F F' D D' n : ℕ} (hF : F ≤ F') (hD : D ≤ D')
    {X : Set (Fin n → ℝ)} (hX : X ∈ S.Ω F D n) : X ∈ S.Ω F' D' n :=
  Omega_mono_D_le S hD (Omega_mono_F_le S hF hX)

/-- `Set.univ` is an `Ω`-set: it is the complement of the empty union. -/
theorem Omega_univ (S : SOMin) (F n : ℕ) : (Set.univ : Set (Fin n → ℝ)) ∈ S.Ω (F + 1) 0 n := by
  have h : (∅ : Set (Fin n → ℝ)) ∈ S.Ω F 0 n := by
    have h0 : (⋃ i : Fin 0, (∅ : Set (Fin n → ℝ))) ∈ S.Ω F (∑ i : Fin 0, 0) n :=
      S.union (D := fun _ : Fin 0 => 0) (A := fun _ : Fin 0 => (∅ : Set (Fin n → ℝ)))
        (fun i => (i.elim0 : (∅ : Set (Fin n → ℝ)) ∈ S.Ω F 0 n))
    simpa using h0
  simpa using S.compl h

/-- The intersection of two `Ω`-sets is `Ω`-bounded. -/
theorem Omega_inter (S : SOMin) {F₁ F₂ D₁ D₂ n : ℕ} {X Y : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω F₁ D₁ n) (hY : Y ∈ S.Ω F₂ D₂ n) :
    X ∩ Y ∈ S.Ω (max F₁ F₂ + 1) (D₁ + D₂) n := by
  have h1 : X ∈ S.Ω (max F₁ F₂) D₁ n := Omega_mono_F_le S (le_max_left _ _) hX
  have h2 : Y ∈ S.Ω (max F₁ F₂) D₂ n := Omega_mono_F_le S (le_max_right _ _) hY
  have hA : ∀ i : Fin 2, (fun i : Fin 2 => if i = 0 then X else Y) i ∈
      S.Ω (max F₁ F₂) ((fun i : Fin 2 => if i = 0 then D₁ else D₂) i) n := by
    intro i
    fin_cases i
    · simpa using h1
    · simpa using h2
  have h3 := S.inter (D := fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (A := fun i : Fin 2 => if i = 0 then X else Y) hA
  have h4 : (⋂ i : Fin 2, (fun i : Fin 2 => if i = 0 then X else Y) i) = X ∩ Y := by
    ext x
    simp only [Set.mem_iInter, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨h 0, h 1⟩
    · rintro ⟨hx, hy⟩ i
      fin_cases i <;> simp_all
  rw [h4] at h3
  have h5 : (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ := by
    simp [Fin.sum_univ_two]
  rw [h5] at h3
  exact h3

/-! ## 4. The hypotheses added by the reductions of §§5.2–5.5 -/

/-- The open unit interval, the range of the distinguished `x`-coordinate. -/
def I : Set ℝ := Set.Ioo 0 1

/-- `YBound F r`: BNZ's cube-local hypothesis `‖F_λ(x,·)‖_r ≤ 1` for `x ∈ I`: all
derivatives of order `≤ r` in the `y`-directions (the coordinates after the first), at fixed
first coordinate `x ∈ I`, are bounded by `1` at every `y` in the cube.  (Both quantifiers are
cube-local, matching BNZ §5.2 and the other predicates of this file.) -/
def YBound {k p n : ℕ} (F : Family k p (n + 1)) (r : ℕ) : Prop :=
  ∀ i l, ∀ x ∈ I, ∀ m, m ≤ r → ∀ y ∈ openCube n,
    ‖iteratedFDeriv ℝ m (slice (F i l) x) y‖ ≤ 1

/-- `LipOnCube F C`: each member of the family is `C`-Lipschitz on the open cube. -/
def LipOnCube {k p n : ℕ} (F : Family k p n) (C : ℝ) : Prop :=
  ∀ i l z z', z ∈ openCube n → z' ∈ openCube n → |F i l z - F i l z'| ≤ C * dist z z'

/-- `NormLeOne F r`: each member is `C^r` on the open cube with all operator norms `≤ 1`. -/
def NormLeOne {k p n : ℕ} (F : Family k p n) (r : ℕ) : Prop :=
  ∀ i l, ContDiffOn ℝ r (F i l) (openCube n) ∧
    ∀ m, m ≤ r → ∀ z ∈ openCube n, ‖iteratedFDeriv ℝ m (F i l) z‖ ≤ 1

/-- `NormLeOneDef F r`: inside the cube, all derivative norms of order `≤ r` are `≤ 1` at
every point where the member is `C^r`. -/
def NormLeOneDef {k p n : ℕ} (F : Family k p n) (r : ℕ) : Prop :=
  ∀ i l, ∀ z ∈ openCube n, ContDiffAt ℝ r (F i l) z → ∀ m, m ≤ r →
    ‖iteratedFDeriv ℝ m (F i l) z‖ ≤ 1

/-- The frozen side condition that a family takes values in `(0,1)` on the cube. -/
def ValuesIn01 {k p n : ℕ} (Λ : Set (Fin p → ℝ)) (F : Family k p n) : Prop :=
  ∀ i, ∀ l ∈ Λ, ∀ x ∈ openCube n, F i l x ∈ Set.Ioo (0 : ℝ) 1

/-! ## 5. The F-lemma with an extra hypothesis, and the four predicates -/

/-- `FLemP S p n P` is the frozen `FLem S p n` with the supplementary hypothesis `P r k F`
on the family. With `P` constantly true it is `FLem`. -/
def FLemP (S : SOMin) (p n : ℕ) (P : ℕ → ∀ k, Family k p n → Prop) : Prop :=
  ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
    ∀ (Λ : Set (Fin p → ℝ)) (F : Family k p n),
      P r k F →
      (∀ i, famGraph (F i) ∈ S.Ω F0 D (p + n + 1)) →
      ValuesIn01 Λ F →
      ∃ Φ : Finset (ChartTuple p n),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        (∀ φ ∈ Φ, (∀ j, famGraph (φ j) ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + n + 1)) ∧
          ∀ l ∈ Λ, (∀ t ∈ openCube n, (fun j => φ j l t) ∈ openCube n) ∧
            ∀ i, ContDiffOn ℝ r (fun t => F i l (fun j => φ j l t)) (openCube n) ∧
              ∀ m ≤ r, ∀ t ∈ openCube n,
                ‖iteratedFDeriv ℝ m (fun t => F i l (fun j => φ j l t)) t‖ ≤ 1) ∧
        ∀ l ∈ Λ, ∀ x ∈ openCube n, ∃ φ ∈ Φ, ∃ t ∈ openCube n,
          ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε

/-- `FLem` is `FLemP` with the vacuous supplementary hypothesis. -/
theorem FLemP_true_iff (S : SOMin) (p n : ℕ) :
    FLemP S p n (fun _ _ _ => True) ↔ FLem S p n := by
  constructor
  · intro h F0
    obtain ⟨a, b, c, h⟩ := h F0
    exact ⟨a, b, c, fun D r k ε hε hε1 Λ F hΩ hval =>
      h D r k ε hε hε1 Λ F trivial hΩ hval⟩
  · intro h F0
    obtain ⟨a, b, c, h⟩ := h F0
    exact ⟨a, b, c, fun D r k ε hε hε1 Λ F _ hΩ hval =>
      h D r k ε hε hε1 Λ F hΩ hval⟩

/-- §5.2: `y`-derivatives bounded by `1`. -/
def PY (p n : ℕ) : ℕ → ∀ k, Family k p (n + 1) → Prop := fun r _ F => YBound F r

/-- §5.3: `y`-derivatives bounded by `1`, and `1`-Lipschitz on the cube. -/
def PYLip (p n : ℕ) : ℕ → ∀ k, Family k p (n + 1) → Prop :=
  fun r _ F => YBound F r ∧ LipOnCube F 1

/-- §5.4: in addition all derivative norms are `≤ 1` wherever they are defined. -/
def PYLipDef (p n : ℕ) : ℕ → ∀ k, Family k p (n + 1) → Prop :=
  fun r _ F => YBound F r ∧ LipOnCube F 1 ∧ NormLeOneDef F r

/-- §5.5 (final normal form): the family is `1`-Lipschitz and `C^r` on the cube with all
derivative norms `≤ 1`. -/
def PSmooth (p n : ℕ) : ℕ → ∀ k, Family k p (n + 1) → Prop :=
  fun r _ F => LipOnCube F 1 ∧ NormLeOne F r

end Work.WilkG4c
