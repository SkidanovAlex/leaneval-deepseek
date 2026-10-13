/-
  WilC4 : `Work.WilC4.paramW_definable` — the parametric locally constant locus `PW Y` is
  `∅`-definable whenever the family `Y ⊆ ℝ^{n+2}` is (`∅`-definable in `LRc`).

  Mathematically this is pure first-order bookkeeping.  Recall

    `PW Y = {p | ∃ y ε, 0 < ε ∧ (p 0, y, tail p) ∈ Y ∧
        ∀ z, p 0 - ε < z → z < p 0 + ε → (z, y, tail p) ∈ Y}`.

  The only point that needs a thought is the quantified real parameter `ε`: `LRc` has no symbol
  for subtraction, and we would rather not introduce auxiliary variables for `p 0 - ε` and
  `p 0 + ε`.  Instead we replace the pair `(ε, ε > 0)` by the two endpoints `a, b` of an interval
  containing `p 0`:

    `p ∈ PW Y  ↔  ∃ y a b, (p 0, y, tail p) ∈ Y ∧ a < p 0 ∧ p 0 < b ∧
        ∀ z, a < z → z < b → (z, y, tail p) ∈ Y`.

  Indeed `⇐` uses `ε = min (p 0 - a) (b - p 0) / 2 > 0`, and `⇒` uses `a = p 0 - ε`, `b = p 0 + ε`.
  The advantage: the right-hand formula only compares *coordinates* with `<`, and `<` between
  coordinates is `∅`-definable in `LRc` because `x ≤ y ↔ ∃ z, x + z * z = y` holds in `ℝ`.

  Formally the body is realised on the index type

    `Sig n = ((((Fin (n+1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1)`,

  holding the row `p`, the three quantified reals `y, a, b` (one `Fin 1` block each, so that the
  unpacking of the existential blocks is a pure beta-reduction) and the bound variable `z`.  The
  four quantifier blocks are then stripped with `Set.Definable.forall_of_finite` (the `z` block)
  and `Set.Definable.exists_of_finite` (the `b`, `a`, `y` blocks).

  Membership of `(p 0, y, tail p)` and of `(z, y, tail p)` in `Y` is obtained by pulling `Y`
  back along the reindexings `t1`, `t2 : Fin (n+2) → Sig n` (`Set.Definable.preimage_comp`);
  this is the role played by `Work.WilC4.PExt` / `PExt_apply` in `ParamMonoDefs`, made explicit.
-/
import Mathlib
import Submission.Work.WilC4.ParamMonoDefs
import Submission.Work.WilC2.finite_definable_singleton

set_option autoImplicit false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

namespace PWDef

variable {n : ℕ}

/-! ## 1. The order is `∅`-definable in `LRc` -/

/-- In `ℝ` every nonnegative real is a square. -/
private lemma sqReal (x : ℝ) (hx : 0 ≤ x) : ∃ z : ℝ, x = z * z :=
  ⟨Real.sqrt x, by nlinarith [Real.sq_sqrt hx]⟩

/-- Strict comparison of two coordinates is `∅`-definable in `LRc`, since `ℝ` is a real closed
field: `x ≤ y ↔ ∃ z, x + z * z = y` and `<` is `≤` minus `≥`. -/
private lemma ltCoord {α : Type} (i j : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v i < v j} := by
  have h1 := Work.WilC2.definable_le (M := ℝ) (A := (∅ : Set ℝ)) sqReal i j
  have h2 := Work.WilC2.definable_le (M := ℝ) (A := (∅ : Set ℝ)) sqReal j i
  convert h1.sdiff h2 using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
  exact lt_iff_le_not_ge

/-! ## 2. The index type, the reindexings of `Y`, and the body -/

/-- The index type of the body: the row `p`, the three quantified reals `y, a, b`, and the bound
variable `z`. -/
abbrev Sig (n : ℕ) : Type := ((((Fin (n + 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1)

/-- The coordinate of `p i`. -/
def xIx (n : ℕ) (i : Fin (n + 1)) : Sig n := Sum.inl (Sum.inl (Sum.inl (Sum.inl i)))

/-- The coordinate of the value `y`. -/
def yIx (n : ℕ) : Sig n := Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))

/-- The coordinate of the left endpoint `a`. -/
def aIx (n : ℕ) : Sig n := Sum.inl (Sum.inl (Sum.inr 0))

/-- The coordinate of the right endpoint `b`. -/
def bIx (n : ℕ) : Sig n := Sum.inl (Sum.inr 0)

/-- The coordinate of the bound variable `z`. -/
def zIx (n : ℕ) : Sig n := Sum.inr 0

/-- The reindexing of `Y ⊆ ℝ^{n+2}` exhibiting `(p 0, y, p₁, …, pₙ)`. -/
def t1 (n : ℕ) : Fin (n + 2) → Sig n :=
  Fin.cons (xIx n 0) (Fin.cons (yIx n) (fun j : Fin n => xIx n j.succ))

/-- The reindexing of `Y ⊆ ℝ^{n+2}` exhibiting `(z, y, p₁, …, pₙ)`. -/
def t2 (n : ℕ) : Fin (n + 2) → Sig n :=
  Fin.cons (zIx n) (Fin.cons (yIx n) (fun j : Fin n => xIx n j.succ))

/-- The body of the formula defining the locally constant locus: `(p 0, y, tail p) ∈ Y`, the
interval `(a, b)` around `p 0`, and the universal condition `a < z < b → (z, y, tail p) ∈ Y`. -/
def body (Y : Set (Fin (n + 2) → ℝ)) : Set (Sig n → ℝ) :=
  {t | (fun i => t (t1 n i)) ∈ Y ∧ t (aIx n) < t (xIx n 0) ∧ t (xIx n 0) < t (bIx n) ∧
    (t (aIx n) < t (zIx n) → t (zIx n) < t (bIx n) → (fun i => t (t2 n i)) ∈ Y)}

/-- The body with the bound variable `z` universally quantified. -/
def univ (Y : Set (Fin (n + 2) → ℝ)) : Set ((((Fin (n + 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) → ℝ) :=
  {t | ∀ uz : Fin 1 → ℝ, Sum.elim t uz ∈ body Y}

/-- The body with `b` existentially quantified. -/
def exB (Y : Set (Fin (n + 2) → ℝ)) : Set (((Fin (n + 1) ⊕ Fin 1) ⊕ Fin 1) → ℝ) :=
  {t | ∃ ub : Fin 1 → ℝ, Sum.elim t ub ∈ univ Y}

/-- The body with `a, b` existentially quantified. -/
def exA (Y : Set (Fin (n + 2) → ℝ)) : Set ((Fin (n + 1) ⊕ Fin 1) → ℝ) :=
  {t | ∃ ua : Fin 1 → ℝ, Sum.elim t ua ∈ exB Y}

/-- The body with `y, a, b` existentially quantified. -/
def fin (Y : Set (Fin (n + 2) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {p | ∃ uy : Fin 1 → ℝ, Sum.elim p uy ∈ exA Y}

/-! ## 3. Unfolding the body -/

/-- Evaluation of the coordinate `p i`. -/
lemma elimX (p : Fin (n + 1) → ℝ) (uy ua ub uz : Fin 1 → ℝ) (i : Fin (n + 1)) :
    (Sum.elim (Sum.elim (Sum.elim (Sum.elim p uy) ua) ub) uz) (xIx n i) = p i := by
  simp [xIx]

/-- Evaluation of the coordinate `y`. -/
lemma elimY (p : Fin (n + 1) → ℝ) (uy ua ub uz : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim (Sum.elim (Sum.elim p uy) ua) ub) uz) (yIx n) = uy 0 := by
  simp [yIx]

/-- Evaluation of the coordinate `a`. -/
lemma elimA (p : Fin (n + 1) → ℝ) (uy ua ub uz : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim (Sum.elim (Sum.elim p uy) ua) ub) uz) (aIx n) = ua 0 := by
  simp [aIx]

/-- Evaluation of the coordinate `b`. -/
lemma elimB (p : Fin (n + 1) → ℝ) (uy ua ub uz : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim (Sum.elim (Sum.elim p uy) ua) ub) uz) (bIx n) = ub 0 := by
  simp [bIx]

/-- Evaluation of the coordinate `z`. -/
lemma elimZ (p : Fin (n + 1) → ℝ) (uy ua ub uz : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim (Sum.elim (Sum.elim p uy) ua) ub) uz) (zIx n) = uz 0 := by
  simp [zIx]

/-- The row underlying the membership `(p 0, y, tail p) ∈ Y`. -/
lemma compT1 (p : Fin (n + 1) → ℝ) (uy ua ub uz : Fin 1 → ℝ) :
    (fun i => (Sum.elim (Sum.elim (Sum.elim (Sum.elim p uy) ua) ub) uz) (t1 n i)) =
      Fin.cons (p 0) (Fin.cons (uy 0) (Fin.tail p)) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ l => rfl

/-- The row underlying the membership `(z, y, tail p) ∈ Y`. -/
lemma compT2 (p : Fin (n + 1) → ℝ) (uy ua ub uz : Fin 1 → ℝ) :
    (fun i => (Sum.elim (Sum.elim (Sum.elim (Sum.elim p uy) ua) ub) uz) (t2 n i)) =
      Fin.cons (uz 0) (Fin.cons (uy 0) (Fin.tail p)) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ l => rfl

/-- Membership in the body, in coordinates. -/
lemma body_apply {Y : Set (Fin (n + 2) → ℝ)} (p : Fin (n + 1) → ℝ) (uy ua ub uz : Fin 1 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim (Sum.elim p uy) ua) ub) uz ∈ body Y ↔
      Fin.cons (p 0) (Fin.cons (uy 0) (Fin.tail p)) ∈ Y ∧ ua 0 < p 0 ∧ p 0 < ub 0 ∧
        (ua 0 < uz 0 → uz 0 < ub 0 → Fin.cons (uz 0) (Fin.cons (uy 0) (Fin.tail p)) ∈ Y) := by
  simp only [body, Set.mem_ofPred_eq, compT1, compT2, elimX, elimA, elimB, elimZ]

/-! ## 4. Definability of the body and of its quantifier blocks -/

/-- The body is `∅`-definable whenever `Y` is. -/
theorem body_definable {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) : (∅ : Set ℝ).Definable LRc (body Y) := by
  have h1 : (∅ : Set ℝ).Definable LRc {t : Sig n → ℝ | (fun i => t (t1 n i)) ∈ Y} := by
    have h := hY.preimage_comp (t1 n)
    convert h using 1
    ext t
    simp [Function.comp_def]
  have h2 : (∅ : Set ℝ).Definable LRc {t : Sig n → ℝ | t (aIx n) < t (xIx n 0)} :=
    ltCoord (aIx n) (xIx n 0)
  have h3 : (∅ : Set ℝ).Definable LRc {t : Sig n → ℝ | t (xIx n 0) < t (bIx n)} :=
    ltCoord (xIx n 0) (bIx n)
  have h4 : (∅ : Set ℝ).Definable LRc {t : Sig n → ℝ | t (aIx n) < t (zIx n)} :=
    ltCoord (aIx n) (zIx n)
  have h5 : (∅ : Set ℝ).Definable LRc {t : Sig n → ℝ | t (zIx n) < t (bIx n)} :=
    ltCoord (zIx n) (bIx n)
  have h6 : (∅ : Set ℝ).Definable LRc {t : Sig n → ℝ | (fun i => t (t2 n i)) ∈ Y} := by
    have h := hY.preimage_comp (t2 n)
    convert h using 1
    ext t
    simp [Function.comp_def]
  have h7 : (∅ : Set ℝ).Definable LRc
      {t : Sig n → ℝ | t (aIx n) < t (zIx n) → t (zIx n) < t (bIx n) →
        (fun i => t (t2 n i)) ∈ Y} := by
    have h := (h4.compl.union h5.compl).union h6
    convert h using 1
    ext t
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
    tauto
  have h := h1.inter (h2.inter (h3.inter h7))
  convert h using 1
  ext t
  simp only [body, Set.mem_inter_iff, Set.mem_ofPred_eq]

/-- The body with `z` universally quantified is `∅`-definable. -/
theorem univ_definable {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) : (∅ : Set ℝ).Definable LRc (univ Y) := by
  have h := (body_definable hY).forall_of_finite
    (α := (((Fin (n + 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1)) (β := Fin 1)
  simpa only [univ] using h

/-- The body with `b` existentially quantified is `∅`-definable. -/
theorem exB_definable {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) : (∅ : Set ℝ).Definable LRc (exB Y) := by
  have h := (univ_definable hY).exists_of_finite
    (α := ((Fin (n + 1) ⊕ Fin 1) ⊕ Fin 1)) (β := Fin 1)
  simpa only [exB] using h

/-- The body with `a, b` existentially quantified is `∅`-definable. -/
theorem exA_definable {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) : (∅ : Set ℝ).Definable LRc (exA Y) := by
  have h := (exB_definable hY).exists_of_finite
    (α := (Fin (n + 1) ⊕ Fin 1)) (β := Fin 1)
  simpa only [exA] using h

/-- The body with `y, a, b` existentially quantified is `∅`-definable. -/
theorem fin_definable {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) : (∅ : Set ℝ).Definable LRc (fin Y) := by
  have h := (exA_definable hY).exists_of_finite (α := (Fin (n + 1))) (β := Fin 1)
  simpa only [fin] using h

/-! ## 5. Unpacking the quantifier blocks of `fin`, over `ℝ` -/

/-- Unfolding of a single `Fin 1` existential block. -/
private lemma exists1 {M : Type} {Q : (Fin 1 → M) → Prop} :
    (∃ f : Fin 1 → M, Q f) ↔ ∃ a : M, Q (fun _ => a) :=
  ⟨fun ⟨f, hf⟩ => ⟨f 0, by
      have h : (fun _ : Fin 1 => f 0) = f := funext fun i => by fin_cases i; rfl
      rwa [h]⟩,
   fun ⟨a, ha⟩ => ⟨fun _ => a, ha⟩⟩

/-- Unfolding of a single `Fin 1` universal block. -/
private lemma forall1 {M : Type} {Q : (Fin 1 → M) → Prop} :
    (∀ f : Fin 1 → M, Q f) ↔ ∀ a : M, Q (fun _ => a) :=
  ⟨fun h a => h (fun _ => a),
   fun h f => by
     have hf : (fun _ : Fin 1 => f 0) = f := funext fun i => by fin_cases i; rfl
     rw [← hf]
     exact h (f 0)⟩

/-- `fin Y`, in coordinates. -/
lemma mem_fin {Y : Set (Fin (n + 2) → ℝ)} (p : Fin (n + 1) → ℝ) :
    p ∈ fin Y ↔ ∃ y a b : ℝ, Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y ∧
      a < p 0 ∧ p 0 < b ∧
      ∀ z : ℝ, a < z → z < b → Fin.cons z (Fin.cons y (Fin.tail p)) ∈ Y := by
  simp only [fin, exA, exB, univ, Set.mem_ofPred_eq, exists1, forall1, body_apply]
  constructor
  · rintro ⟨y, a, b, h⟩
    exact ⟨y, a, b, (h 0).1, (h 0).2.1, (h 0).2.2.1, fun z => (h z).2.2.2⟩
  · rintro ⟨y, a, b, hY, ha, hb, hz⟩
    exact ⟨y, a, b, fun z => ⟨hY, ha, hb, hz z⟩⟩

/-! ## 6. `PW Y` is the set `fin Y` -/

/-- The parametric locally constant locus equals the set `fin Y`: the radius `ε > 0` is traded
for the two endpoints `a < p 0 < b` of an interval (see the file header). -/
lemma PW_eq_fin {Y : Set (Fin (n + 2) → ℝ)} : PW Y = fin Y := by
  ext p
  rw [mem_fin]
  simp only [PW, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, ε, hε, hmem, hgerm⟩
    exact ⟨y, p 0 - ε, p 0 + ε, hmem, by linarith, by linarith,
      fun z h1 h2 => hgerm z h1 h2⟩
  · rintro ⟨y, a, b, hmem, ha, hb, hbox⟩
    refine ⟨y, min (p 0 - a) (b - p 0) / 2, ?_, hmem, ?_⟩
    · have hmin : 0 < min (p 0 - a) (b - p 0) := lt_min (by linarith) (by linarith)
      linarith
    · intro z h1 h2
      refine hbox z ?_ ?_
      · have hm := min_le_left (p 0 - a) (b - p 0)
        linarith
      · have hm := min_le_right (p 0 - a) (b - p 0)
        linarith

end PWDef

/-- Prove in namespace `Work.WilC4` (declaration name `Work.WilC4.paramW_definable`) in the file
`Submission/Work/WilC4/paramW_definable.lean`.  `PW Y ⊆ ℝ^{n+1}` is the parametric locally constant
locus; the inner universal quantifier is over the real variable `z` (encode it as `Fin 1`).  See
`Work.WilC4.PExt_apply` in `Submission/Work/WilC4/ParamMonoDefs.lean`. -/
theorem paramW_definable {n : ℕ} {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.PW Y) := by
  rw [PWDef.PW_eq_fin]
  exact PWDef.fin_definable hY

end Work.WilC4
