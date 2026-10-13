/-
  WilC4 : definability of the four *parametric* one-sided germ loci `PLm`, `PHm`, `PLp`, `PHp`
  of `Submission/Work/WilC4/ParamMonoDefs.lean`.

  This is the parametric version of `Work.WilC4.monoDefinable_germs`
  (`Submission/Work/WilC4/monoDefinable_germs.lean`).  The family is `Y ⊆ ℝ^{n+2}`, the ambient
  variable is the row `p : Fin (n+1) → ℝ` (`p 0` is the point of the fibre and `Fin.tail p` the
  parameters), and membership of `(x, y, Fin.tail p)` in `Y` is written
  `Fin.cons x (Fin.cons y (Fin.tail p)) ∈ Y`.  The construction is the same index bookkeeping as
  in the non-parametric case, with the single point coordinate `Fin 1` replaced by the row
  `Fin (n+1)`: the value/intro-point pairs are packaged through the index maps `kOut`, `kIn`
  realising `Fin.cons _ (Fin.cons _ (Fin.tail p))`.

  The real quantified variables `z` (universal) and `y'` (existential) are encoded as `Fin 1`,
  and the existential pair `(ε, y)` (equivalently `(t, y)` after the change of variable
  `t = p 0 ∓ ε`) as `Fin 2`.
-/
import Mathlib
import Submission.Work.WilC4.ParamMonoDefs
import Submission.Work.WilC2.finite_definable_singleton

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Two elementary definability lemmas -/

/-- Strict order between two coordinates is `∅`-definable (in `ℝ` every nonnegative real is a
square, so `≤` is the `LRc`-formula `∃ z, x + z * z = y`, and `<` is `≤` minus `=`). -/
private lemma definable_lt_coord {α : Type} (i j : α) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {v : α → ℝ | v i < v j} := by
  have h1 := Work.WilC2.definable_le (M := ℝ) (A := (∅ : Set ℝ)) Work.WilC2.real_exists_sq i j
  have h2 := Work.WilC2.definable_le (M := ℝ) (A := (∅ : Set ℝ)) Work.WilC2.real_exists_sq j i
  convert h1.sdiff h2 using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
  exact lt_iff_le_not_ge

/-- Reindexing the membership `Fin.cons x (Fin.cons y (Fin.tail p)) ∈ Y` along an index map into
the ambient type. -/
private lemma definable_memY {n : ℕ} {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    {α : Type} (f : Fin (n + 2) → α) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {v : α → ℝ | v ∘ f ∈ Y} := by
  convert hY.preimage_comp f using 1
  ext v
  rfl

/-! ## 2. The index bookkeeping

The ambient index type of the parametric germ construction is
`GermIdx n := (((Fin (n+1) ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)`, carrying the row `p`, the pair `(t,y)`,
the universally quantified interior point `z`, and the existentially chosen interior value `y'`. -/

/-- The ambient index type of the parametric germ construction. -/
abbrev GermIdx (n : ℕ) := (((Fin (n + 1) ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)

/-- The coordinate of the parameter `p i`. -/
private def gP {n : ℕ} (i : Fin (n + 1)) : GermIdx n := Sum.inl (Sum.inl (Sum.inl i))
/-- The coordinate of the point `p 0`. -/
private def gA {n : ℕ} : GermIdx n := Sum.inl (Sum.inl (Sum.inl (0 : Fin (n + 1))))
/-- The coordinate of the endpoint `t`. -/
private def gT {n : ℕ} : GermIdx n := Sum.inl (Sum.inl (Sum.inr (0 : Fin 2)))
/-- The coordinate of the value `y` at the point. -/
private def gY {n : ℕ} : GermIdx n := Sum.inl (Sum.inl (Sum.inr (1 : Fin 2)))
/-- The coordinate of the interior point `z`. -/
private def gZ {n : ℕ} : GermIdx n := Sum.inl (Sum.inr (0 : Fin 1))
/-- The coordinate of the interior value `y'`. -/
private def gYp {n : ℕ} : GermIdx n := Sum.inr (0 : Fin 1)

/-- The point coordinate at the `Fin (n+1) ⊕ Fin 2` level. -/
private def k2A {n : ℕ} : Fin (n + 1) ⊕ Fin 2 := Sum.inl (0 : Fin (n + 1))
/-- The endpoint coordinate at the `Fin (n+1) ⊕ Fin 2` level. -/
private def k2T {n : ℕ} : Fin (n + 1) ⊕ Fin 2 := Sum.inr (0 : Fin 2)
/-- The value coordinate at the `Fin (n+1) ⊕ Fin 2` level. -/
private def k2Y {n : ℕ} : Fin (n + 1) ⊕ Fin 2 := Sum.inr (1 : Fin 2)

/-- The index map realising `Fin.cons (p 0) (Fin.cons y (Fin.tail p))` at the
`Fin (n+1) ⊕ Fin 2` level. -/
private def kOut {n : ℕ} : Fin (n + 2) → Fin (n + 1) ⊕ Fin 2 :=
  Fin.cons (Sum.inl (0 : Fin (n + 1)))
    (Fin.cons (Sum.inr (1 : Fin 2)) (fun j : Fin n => Sum.inl (Fin.succ j)))

/-- The index map realising `Fin.cons z (Fin.cons y' (Fin.tail p))` at the `GermIdx n` level. -/
private def kIn {n : ℕ} : Fin (n + 2) → GermIdx n :=
  Fin.cons gZ (Fin.cons gYp (fun j : Fin n => gP (Fin.succ j)))

/-- Unfolding of `Fin.tail` at an argument (there is no `simp` lemma for it in Mathlib). -/
private lemma tail_apply {n : ℕ} {β : Type*} (q : Fin (n + 1) → β) (i : Fin n) :
    Fin.tail q i = q i.succ := rfl

private lemma comp_kOut {n : ℕ} (v : (Fin (n + 1) ⊕ Fin 2) → ℝ) :
    v ∘ kOut = Fin.cons (v k2A) (Fin.cons (v k2Y) (Fin.tail (v ∘ Sum.inl))) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [Function.comp_apply, kOut, k2A]
  | succ j =>
    induction j using Fin.cases with
    | zero => simp [Function.comp_apply, kOut, k2Y]
    | succ k => simp [Function.comp_apply, kOut, tail_apply]

private lemma comp_kIn {n : ℕ} (w : GermIdx n → ℝ) :
    w ∘ kIn = Fin.cons (w gZ) (Fin.cons (w gYp) (Fin.tail (w ∘ gP))) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [Function.comp_apply, kIn, gZ]
  | succ j =>
    induction j using Fin.cases with
    | zero => simp [Function.comp_apply, kIn, gYp]
    | succ k => simp [Function.comp_apply, kIn, gP, tail_apply]

/-- The composite of `comp_kOut` with the concrete `Sum.elim` shapes occurring in the goal. -/
private lemma comp_kOut_elim {n : ℕ} (p : Fin (n + 1) → ℝ) (u : Fin 2 → ℝ) :
    (Sum.elim p u) ∘ (kOut (n := n)) = Fin.cons (p 0) (Fin.cons (u 1) (Fin.tail p)) := by
  rw [comp_kOut (n := n) (Sum.elim p u)]
  simp [k2A, k2Y, Sum.elim_comp_inl]

/-- `w ∘ gP = p` for the concrete `Sum.elim` shape occurring in the goal. -/
private lemma elim_comp_gP {n : ℕ} (p : Fin (n + 1) → ℝ) (u : Fin 2 → ℝ)
    (uz uy : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim (Sum.elim p u) uz) uy) ∘ (gP (n := n)) = p := by
  funext i
  simp [Function.comp_apply, gP]

/-- The composite of `comp_kIn` with the concrete `Sum.elim` shapes occurring in the goal. -/
private lemma comp_kIn_elim {n : ℕ} (p : Fin (n + 1) → ℝ) (u : Fin 2 → ℝ)
    (uz uy : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim (Sum.elim p u) uz) uy) ∘ (kIn (n := n)) =
      Fin.cons (uz 0) (Fin.cons (uy 0) (Fin.tail p)) := by
  rw [comp_kIn (n := n), elim_comp_gP]
  simp [gZ, gYp]

/-! ## 3. The shape comparison -/

/-- Compares the shape obtained from the definition (real witnesses `t, y`, an unbounded
universal `z` and an inner existential `y'`) with the shape produced by the `Set.Definable`
combinators (`Fin`-indexed witnesses, the inner existential moved outside the implication by
`Definable.exists_of_finite`).  The two differ only by classical logic. -/
private lemma germ_iff (P Q : ℝ → Prop) (W X V : ℝ → ℝ → Prop) :
    (∃ t y : ℝ, P t ∧ Q y ∧ ∀ z : ℝ, W t z → ∃ y' : ℝ, X z y' ∧ V y' y) ↔
      (∃ u : Fin 2 → ℝ, (P (u 0) ∧ Q (u 1)) ∧
        ∀ u₁ : Fin 1 → ℝ, ∃ u₂ : Fin 1 → ℝ,
          (W (u 0) (u₁ 0) → X (u₁ 0) (u₂ 0) ∧ V (u₂ 0) (u 1))) := by
  constructor
  · rintro ⟨t, y, hP, hQ, hC⟩
    refine ⟨![t, y], ⟨by simpa using hP, by simpa using hQ⟩, ?_⟩
    intro u₁
    by_cases hW : W t (u₁ 0)
    · obtain ⟨y', hX, hV⟩ := hC (u₁ 0) hW
      exact ⟨![y'], by simpa [hW] using ⟨hX, hV⟩⟩
    · exact ⟨![0], by simp [hW]⟩
  · rintro ⟨u, ⟨hP, hQ⟩, hC⟩
    refine ⟨u 0, u 1, hP, hQ, ?_⟩
    intro z hW
    obtain ⟨u₂, h⟩ := hC ![z]
    have h1 : W (u 0) z := by simpa using hW
    exact ⟨u₂ 0, (h h1).1, (h h1).2⟩

/-! ## 4. The change of variable `ε ↔ t` -/

/-- `PLm` with the additive parameter replaced by the left endpoint `t = p 0 - ε`. -/
private lemma mem_PLm_iff {n : ℕ} (Y : Set (Fin (n + 2) → ℝ)) (p : Fin (n + 1) → ℝ) :
    p ∈ PLm Y ↔ ∃ t y : ℝ, t < p 0 ∧
      Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y ∧
      ∀ z : ℝ, (t < z ∧ z < p 0) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail p)) ∈ Y ∧ y' < y := by
  simp only [PLm, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ε, y, hε, hay, hgerm⟩
    exact ⟨p 0 - ε, y, by linarith, hay, fun z hz => hgerm z hz.1 hz.2⟩
  · rintro ⟨t, y, hta, hay, hgerm⟩
    exact ⟨p 0 - t, y, by linarith, hay, fun z hz hza => hgerm z ⟨by linarith, hza⟩⟩

/-- `PHm` with the additive parameter replaced by the left endpoint `t = p 0 - ε`. -/
private lemma mem_PHm_iff {n : ℕ} (Y : Set (Fin (n + 2) → ℝ)) (p : Fin (n + 1) → ℝ) :
    p ∈ PHm Y ↔ ∃ t y : ℝ, t < p 0 ∧
      Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y ∧
      ∀ z : ℝ, (t < z ∧ z < p 0) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail p)) ∈ Y ∧ y < y' := by
  simp only [PHm, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ε, y, hε, hay, hgerm⟩
    exact ⟨p 0 - ε, y, by linarith, hay, fun z hz => hgerm z hz.1 hz.2⟩
  · rintro ⟨t, y, hta, hay, hgerm⟩
    exact ⟨p 0 - t, y, by linarith, hay, fun z hz hza => hgerm z ⟨by linarith, hza⟩⟩

/-- `PLp` with the additive parameter replaced by the right endpoint `t = p 0 + ε`. -/
private lemma mem_PLp_iff {n : ℕ} (Y : Set (Fin (n + 2) → ℝ)) (p : Fin (n + 1) → ℝ) :
    p ∈ PLp Y ↔ ∃ t y : ℝ, p 0 < t ∧
      Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y ∧
      ∀ z : ℝ, (p 0 < z ∧ z < t) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail p)) ∈ Y ∧ y' < y := by
  simp only [PLp, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ε, y, hε, hay, hgerm⟩
    exact ⟨p 0 + ε, y, by linarith, hay, fun z hz => hgerm z hz.1 hz.2⟩
  · rintro ⟨t, y, hat, hay, hgerm⟩
    exact ⟨t - p 0, y, by linarith, hay, fun z hz hzt => hgerm z ⟨hz, by linarith⟩⟩

/-- `PHp` with the additive parameter replaced by the right endpoint `t = p 0 + ε`. -/
private lemma mem_PHp_iff {n : ℕ} (Y : Set (Fin (n + 2) → ℝ)) (p : Fin (n + 1) → ℝ) :
    p ∈ PHp Y ↔ ∃ t y : ℝ, p 0 < t ∧
      Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y ∧
      ∀ z : ℝ, (p 0 < z ∧ z < t) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail p)) ∈ Y ∧ y < y' := by
  simp only [PHp, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ε, y, hε, hay, hgerm⟩
    exact ⟨p 0 + ε, y, by linarith, hay, fun z hz => hgerm z hz.1 hz.2⟩
  · rintro ⟨t, y, hat, hay, hgerm⟩
    exact ⟨t - p 0, y, by linarith, hay, fun z hz hzt => hgerm z ⟨hz, by linarith⟩⟩

/-! ## 5. The four definability statements -/

section Germs

variable {n : ℕ} {Y : Set (Fin (n + 2) → ℝ)}

/-- The germ loci `PLm` and `PHm` share the interval condition `t < z < p 0` but have opposite
inequalities between `y'` and `y`; this is the common body of the two constructions. -/
private lemma definable_germ_left (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    {cmp : ℝ → ℝ → Prop}
    (hcmp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {w : GermIdx n → ℝ | cmp (w gYp) (w gY)}) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : Fin (n + 1) → ℝ | ∃ t y : ℝ, t < v 0 ∧
        Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧
        ∀ z : ℝ, (t < z ∧ z < v 0) →
          ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y ∧ cmp y' y} := by
  have hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {w : GermIdx n → ℝ |
        (w gT < w gZ ∧ w gZ < w gA) → (w ∘ kIn ∈ Y ∧ cmp (w gYp) (w gY))} := by
    convert (((definable_lt_coord (gT (n := n)) (gZ (n := n))).inter
        (definable_lt_coord (gZ (n := n)) (gA (n := n)))).himp
        ((definable_memY hY (kIn (n := n))).inter hcmp)) using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_himp_iff, Set.mem_inter_iff]
  have hB1 := hB.exists_of_finite (α := ((Fin (n + 1) ⊕ Fin 2) ⊕ Fin 1)) (β := Fin 1)
  have hB2 := hB1.forall_of_finite (α := (Fin (n + 1) ⊕ Fin 2)) (β := Fin 1)
  have hout : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : (Fin (n + 1) ⊕ Fin 2) → ℝ | v (k2T (n := n)) < v (k2A (n := n))} :=
    definable_lt_coord (k2T (n := n)) (k2A (n := n))
  have hmemA : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : (Fin (n + 1) ⊕ Fin 2) → ℝ | v ∘ (kOut (n := n)) ∈ Y} :=
    definable_memY hY (kOut (n := n))
  have hE := (hout.inter hmemA).inter hB2
  have hF := hE.exists_of_finite (α := Fin (n + 1)) (β := Fin 2)
  convert hF using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr,
    gA, gT, gY, gZ, gYp, k2A, k2T, comp_kOut_elim, comp_kIn_elim]
  exact germ_iff (fun t => t < v 0) (fun y => Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y)
    (fun t z => t < z ∧ z < v 0)
    (fun z y' => Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y) cmp

/-- The germ loci `PLp` and `PHp` share the interval condition `p 0 < z < t` but have opposite
inequalities between `y'` and `y`. -/
private lemma definable_germ_right (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    {cmp : ℝ → ℝ → Prop}
    (hcmp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {w : GermIdx n → ℝ | cmp (w gYp) (w gY)}) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : Fin (n + 1) → ℝ | ∃ t y : ℝ, v 0 < t ∧
        Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧
        ∀ z : ℝ, (v 0 < z ∧ z < t) →
          ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y ∧ cmp y' y} := by
  have hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {w : GermIdx n → ℝ |
        (w gA < w gZ ∧ w gZ < w gT) → (w ∘ kIn ∈ Y ∧ cmp (w gYp) (w gY))} := by
    convert (((definable_lt_coord (gA (n := n)) (gZ (n := n))).inter
        (definable_lt_coord (gZ (n := n)) (gT (n := n)))).himp
        ((definable_memY hY (kIn (n := n))).inter hcmp)) using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_himp_iff, Set.mem_inter_iff]
  have hB1 := hB.exists_of_finite (α := ((Fin (n + 1) ⊕ Fin 2) ⊕ Fin 1)) (β := Fin 1)
  have hB2 := hB1.forall_of_finite (α := (Fin (n + 1) ⊕ Fin 2)) (β := Fin 1)
  have hout : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : (Fin (n + 1) ⊕ Fin 2) → ℝ | v (k2A (n := n)) < v (k2T (n := n))} :=
    definable_lt_coord (k2A (n := n)) (k2T (n := n))
  have hmemA : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : (Fin (n + 1) ⊕ Fin 2) → ℝ | v ∘ (kOut (n := n)) ∈ Y} :=
    definable_memY hY (kOut (n := n))
  have hE := (hout.inter hmemA).inter hB2
  have hF := hE.exists_of_finite (α := Fin (n + 1)) (β := Fin 2)
  convert hF using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr,
    gA, gT, gY, gZ, gYp, k2A, k2T, comp_kOut_elim, comp_kIn_elim]
  exact germ_iff (fun t => v 0 < t) (fun y => Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y)
    (fun t z => v 0 < z ∧ z < t)
    (fun z y' => Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y) cmp

private lemma definable_PLm (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PLm Y) := by
  have hset : PLm Y = {v : Fin (n + 1) → ℝ | ∃ t y : ℝ, t < v 0 ∧
      Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧
      ∀ z : ℝ, (t < z ∧ z < v 0) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y ∧ y' < y} := by
    ext v
    exact mem_PLm_iff Y v
  rw [hset]
  exact definable_germ_left (Y := Y) hY (cmp := fun y' y => y' < y)
    (definable_lt_coord (gYp (n := n)) (gY (n := n)))

private lemma definable_PHm (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PHm Y) := by
  have hset : PHm Y = {v : Fin (n + 1) → ℝ | ∃ t y : ℝ, t < v 0 ∧
      Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧
      ∀ z : ℝ, (t < z ∧ z < v 0) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y ∧ y < y'} := by
    ext v
    exact mem_PHm_iff Y v
  rw [hset]
  exact definable_germ_left (Y := Y) hY (cmp := fun y' y => y < y')
    (definable_lt_coord (gY (n := n)) (gYp (n := n)))

private lemma definable_PLp (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PLp Y) := by
  have hset : PLp Y = {v : Fin (n + 1) → ℝ | ∃ t y : ℝ, v 0 < t ∧
      Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧
      ∀ z : ℝ, (v 0 < z ∧ z < t) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y ∧ y' < y} := by
    ext v
    exact mem_PLp_iff Y v
  rw [hset]
  exact definable_germ_right (Y := Y) hY (cmp := fun y' y => y' < y)
    (definable_lt_coord (gYp (n := n)) (gY (n := n)))

private lemma definable_PHp (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PHp Y) := by
  have hset : PHp Y = {v : Fin (n + 1) → ℝ | ∃ t y : ℝ, v 0 < t ∧
      Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧
      ∀ z : ℝ, (v 0 < z ∧ z < t) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y ∧ y < y'} := by
    ext v
    exact mem_PHp_iff Y v
  rw [hset]
  exact definable_germ_right (Y := Y) hY (cmp := fun y' y => y < y')
    (definable_lt_coord (gY (n := n)) (gYp (n := n)))

end Germs

/-! ## 6. The theorem -/

theorem paramGerms_definable {n : ℕ} {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.PLm Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.PHm Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.PLp Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.PHp Y) :=
  ⟨definable_PLm hY, definable_PHm hY, definable_PLp hY, definable_PHp hY⟩

end Work.WilC4
