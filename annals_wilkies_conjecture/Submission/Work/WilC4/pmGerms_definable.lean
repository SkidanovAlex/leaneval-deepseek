/-
  WilC4 : definability of the four *parametric* one-sided germ loci `PLm`, `PHm`, `PLp`, `PHp`
  of `Submission/Work/WilC4/ParamMonoDefs.lean`.

  This is the parametric version of `Work.WilC4.monoDefinable_germs`.  The family is
  `Y ⊆ ℝ^{k+2}`, the ambient variable is the row `p : Fin (k+1) → ℝ` (`p 0` is the point of the
  fibre and `Fin.tail p` the parameters), and membership of `(x, y, Fin.tail p)` in `Y` is written
  `Fin.cons x (Fin.cons y (Fin.tail p)) ∈ Y`.  The parametrised row `Fin (k+1)` replaces the single
  point coordinate `Fin 1` of the non-parametric case.

  Mathematically the only content is a change of variable: for the *left* germs, `ε > 0` is
  replaced by the left endpoint `t := p 0 - ε < p 0`, turning the definition into a statement about
  the relation `t < z < p 0` and membership in `Y`; for the *right* germs, `ε > 0` is replaced by
  the right endpoint `t := p 0 + ε > p 0` and the interval becomes `p 0 < z < t`.  All the pieces
  are first-order over `LRc`, and the only order-theoretic input (strict `<` between coordinates)
  is supplied by `Work.WilC4.definable_lt_terms` from `critAux`.

  The formalisation puts the row `p`, the pair `(t, y)` (as `Fin (k+1) ⊕ Fin 2`), the universally
  quantified interior point `z` and the existentially chosen interior value `y'` into the single
  index type
  `GIdx k = ((Fin (k+1) ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1`,
  builds the body of the formula there with the `Set.Definable` combinators, and then quantifies
  the `y'`-block (`exists_of_finite`), the `z`-block (`forall_of_finite`) and the `(t, y)`-block
  (`exists_of_finite`).  The comparison of the two value coordinates is arbitrary, so the two
  left/right inequalities `y' < y` and `y < y'` share a single construction.
-/
import Mathlib
import Submission.Work.WilC4.critAux

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The index types and their coordinates

We use three nested `Sum`-types carrying the row `p` together with the pair `(t, y)`, the interior
point `z` and the interior value `y'`. -/

/-- Parameters `p : Fin (k+1) → ℝ` together with the pair `(t, y)`. -/
private abbrev GPair (k : ℕ) := Fin (k + 1) ⊕ Fin 2
/-- The previous level with the interior point `z` adjoined. -/
private abbrev GZ (k : ℕ) := GPair k ⊕ Fin 1
/-- The ambient index type of the parametric germ construction (with `y'` adjoined). -/
private abbrev GIdx (k : ℕ) := GZ k ⊕ Fin 1

private def qP {k : ℕ} (i : Fin (k+1)) : GPair k := Sum.inl i
private def qT {k : ℕ} : GPair k := Sum.inr 0
private def qY {k : ℕ} : GPair k := Sum.inr 1
private def rP {k : ℕ} (i : Fin (k+1)) : GZ k := Sum.inl (qP i)
private def rT {k : ℕ} : GZ k := Sum.inl qT
private def rY {k : ℕ} : GZ k := Sum.inl qY
private def rZ {k : ℕ} : GZ k := Sum.inr 0
private def sP {k : ℕ} (i : Fin (k+1)) : GIdx k := Sum.inl (rP i)
private def sT {k : ℕ} : GIdx k := Sum.inl rT
private def sY {k : ℕ} : GIdx k := Sum.inl rY
private def sZ {k : ℕ} : GIdx k := Sum.inl rZ
private def sYp {k : ℕ} : GIdx k := Sum.inr 0

/-- The index map realising `(p 0, y, Fin.tail p)` at the `GPair` level. -/
private def kOut {k : ℕ} : Fin (k+2) → GPair k :=
  Fin.cons (qP 0) (Fin.cons qY (fun j : Fin k => qP j.succ))

/-- The index map realising `(z, y', Fin.tail p)` at the `GIdx` level. -/
private def kIn {k : ℕ} : Fin (k+2) → GIdx k :=
  Fin.cons sZ (Fin.cons sYp (fun j : Fin k => sP j.succ))

/-- `(Sum.elim p u) ∘ kOut` is `Fin.cons (p 0) (Fin.cons (u 1) (Fin.tail p))`. -/
private lemma comp_kOut_elim (k : ℕ) (p : Fin (k+1) → ℝ) (u : Fin 2 → ℝ) :
    (Sum.elim p u) ∘ (kOut (k := k)) = Fin.cons (p 0) (Fin.cons (u 1) (Fin.tail p)) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => induction j using Fin.cases with | zero => rfl | succ l => rfl

/-- `(Sum.elim (Sum.elim (Sum.elim p u) z) y') ∘ kIn` is
`Fin.cons (z 0) (Fin.cons (y' 0) (Fin.tail p))`. -/
private lemma comp_kIn_elim (k : ℕ) (p : Fin (k+1) → ℝ) (u : Fin 2 → ℝ)
    (z : Fin 1 → ℝ) (y' : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim (Sum.elim p u) z) y') ∘ (kIn (k := k)) =
      Fin.cons (z 0) (Fin.cons (y' 0) (Fin.tail p)) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => induction j using Fin.cases with | zero => rfl | succ l => rfl

/-! ## 2. Two elementary definability lemmas -/

/-- Strict order between two coordinates is `∅`-definable (`LRc` contains the language of rings,
so `critAux`'s `definable_lt_terms` applies to the two coordinate terms). -/
private lemma definable_lt_coord {α : Type} (i j : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v i < v j} :=
  definable_lt_terms (Term.var i) (Term.var j)

/-- Membership of a reindexed tuple in the `∅`-definable family `Y`. -/
private lemma definable_memY {n : ℕ} {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) {α : Type} (f : Fin (n + 2) → α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v ∘ f ∈ Y} := by
  convert hY.preimage_comp f using 1
  ext v; rfl

/-! ## 3. The shape comparison

Compares the shape obtained from the definition (real witnesses `t, y`, an unbounded universal `z`
and an inner existential `y'`) with the shape produced by the `Set.Definable` combinators
(`Fin`-indexed witnesses, the inner existential moved outside the implication by
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

/-! ## 4. The two constructions -/

/-- The germ loci `PLm` and `PHm` share the interval condition `t < z < p 0` but have opposite
inequalities between `y'` and `y`; this is the common body of the two constructions. -/
private lemma definable_germ_left {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y)
    {cmp : ℝ → ℝ → Prop}
    (hcmp : (∅ : Set ℝ).Definable LRc {w : GIdx k → ℝ | cmp (w sYp) (w sY)}) :
    (∅ : Set ℝ).Definable LRc {v : Fin (k + 1) → ℝ | ∃ t y : ℝ, t < v 0 ∧
      Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧
      ∀ z : ℝ, (t < z ∧ z < v 0) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y ∧ cmp y' y} := by
  have hB : (∅ : Set ℝ).Definable LRc {w : GIdx k → ℝ |
      (w sT < w sZ ∧ w sZ < w (sP 0)) → (w ∘ (kIn (k := k)) ∈ Y ∧ cmp (w sYp) (w sY))} := by
    convert (((definable_lt_coord (sT (k := k)) (sZ (k := k))).inter
        (definable_lt_coord (sZ (k := k)) (sP (k := k) 0))).himp
        ((definable_memY hY (kIn (k := k))).inter hcmp)) using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_himp_iff, Set.mem_inter_iff]
  have hB1 := hB.exists_of_finite (α := GZ k) (β := Fin 1)
  have hB2 := hB1.forall_of_finite (α := GPair k) (β := Fin 1)
  have hout : (∅ : Set ℝ).Definable LRc {v : GPair k → ℝ | v qT < v (qP 0)} :=
    definable_lt_coord (qT (k := k)) (qP (k := k) 0)
  have hmemA : (∅ : Set ℝ).Definable LRc {v : GPair k → ℝ | v ∘ (kOut (k := k)) ∈ Y} :=
    definable_memY hY (kOut (k := k))
  have hE := (hout.inter hmemA).inter hB2
  have hF := hE.exists_of_finite (α := Fin (k + 1)) (β := Fin 2)
  convert hF using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr,
    qP, qT, sP, sT, sY, sZ, sYp, comp_kOut_elim, comp_kIn_elim]
  exact germ_iff (fun t => t < v 0) (fun y => Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y)
    (fun t z => t < z ∧ z < v 0)
    (fun z y' => Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y) cmp

/-- The germ loci `PLp` and `PHp` share the interval condition `p 0 < z < t` but have opposite
inequalities between `y'` and `y`. -/
private lemma definable_germ_right {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y)
    {cmp : ℝ → ℝ → Prop}
    (hcmp : (∅ : Set ℝ).Definable LRc {w : GIdx k → ℝ | cmp (w sYp) (w sY)}) :
    (∅ : Set ℝ).Definable LRc {v : Fin (k + 1) → ℝ | ∃ t y : ℝ, v 0 < t ∧
      Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧
      ∀ z : ℝ, (v 0 < z ∧ z < t) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y ∧ cmp y' y} := by
  have hB : (∅ : Set ℝ).Definable LRc {w : GIdx k → ℝ |
      (w (sP 0) < w sZ ∧ w sZ < w sT) → (w ∘ (kIn (k := k)) ∈ Y ∧ cmp (w sYp) (w sY))} := by
    convert (((definable_lt_coord (sP (k := k) 0) (sZ (k := k))).inter
        (definable_lt_coord (sZ (k := k)) (sT (k := k)))).himp
        ((definable_memY hY (kIn (k := k))).inter hcmp)) using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_himp_iff, Set.mem_inter_iff]
  have hB1 := hB.exists_of_finite (α := GZ k) (β := Fin 1)
  have hB2 := hB1.forall_of_finite (α := GPair k) (β := Fin 1)
  have hout : (∅ : Set ℝ).Definable LRc {v : GPair k → ℝ | v (qP 0) < v qT} :=
    definable_lt_coord (qP (k := k) 0) (qT (k := k))
  have hmemA : (∅ : Set ℝ).Definable LRc {v : GPair k → ℝ | v ∘ (kOut (k := k)) ∈ Y} :=
    definable_memY hY (kOut (k := k))
  have hE := (hout.inter hmemA).inter hB2
  have hF := hE.exists_of_finite (α := Fin (k + 1)) (β := Fin 2)
  convert hF using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr,
    qP, qT, sP, sT, sY, sZ, sYp, comp_kOut_elim, comp_kIn_elim]
  exact germ_iff (fun t => v 0 < t) (fun y => Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y)
    (fun t z => v 0 < z ∧ z < t)
    (fun z y' => Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y) cmp

/-! ## 5. The change of variable `ε ↔ t` -/

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

/-! ## 6. The four definability statements -/

private lemma definable_PLm {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) : (∅ : Set ℝ).Definable LRc (PLm Y) := by
  have hset : PLm Y = {v : Fin (k + 1) → ℝ | ∃ t y : ℝ, t < v 0 ∧
      Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧
      ∀ z : ℝ, (t < z ∧ z < v 0) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y ∧ y' < y} := by
    ext v; exact mem_PLm_iff Y v
  rw [hset]
  exact definable_germ_left (k := k) hY (cmp := fun y' y => y' < y)
    (definable_lt_coord (sYp (k := k)) (sY (k := k)))

private lemma definable_PHm {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) : (∅ : Set ℝ).Definable LRc (PHm Y) := by
  have hset : PHm Y = {v : Fin (k + 1) → ℝ | ∃ t y : ℝ, t < v 0 ∧
      Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧
      ∀ z : ℝ, (t < z ∧ z < v 0) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y ∧ y < y'} := by
    ext v; exact mem_PHm_iff Y v
  rw [hset]
  exact definable_germ_left (k := k) hY (cmp := fun y' y => y < y')
    (definable_lt_coord (sY (k := k)) (sYp (k := k)))

private lemma definable_PLp {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) : (∅ : Set ℝ).Definable LRc (PLp Y) := by
  have hset : PLp Y = {v : Fin (k + 1) → ℝ | ∃ t y : ℝ, v 0 < t ∧
      Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧
      ∀ z : ℝ, (v 0 < z ∧ z < t) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y ∧ y' < y} := by
    ext v; exact mem_PLp_iff Y v
  rw [hset]
  exact definable_germ_right (k := k) hY (cmp := fun y' y => y' < y)
    (definable_lt_coord (sYp (k := k)) (sY (k := k)))

private lemma definable_PHp {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) : (∅ : Set ℝ).Definable LRc (PHp Y) := by
  have hset : PHp Y = {v : Fin (k + 1) → ℝ | ∃ t y : ℝ, v 0 < t ∧
      Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧
      ∀ z : ℝ, (v 0 < z ∧ z < t) →
        ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail v)) ∈ Y ∧ y < y'} := by
    ext v; exact mem_PHp_iff Y v
  rw [hset]
  exact definable_germ_right (k := k) hY (cmp := fun y' y => y < y')
    (definable_lt_coord (sY (k := k)) (sYp (k := k)))

/-- **The four parametric one-sided germ loci are `∅`-definable.** -/
theorem pmGerms_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PLm Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PHm Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PLp Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PHp Y) :=
  ⟨definable_PLm hY, definable_PHm hY, definable_PLp hY, definable_PHp hY⟩

end Work.WilC4
