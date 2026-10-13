/-
  WilC4 : definability of the four one-sided germ sets `MonoLm`, `MonoHm`, `MonoLp`, `MonoHp`
  of `Submission.Work.WilC4.monoDefs`.

  If `Y ⊆ ℝ²` is `∅`-definable in `LRc` then so is each of the four sets of points whose
  one-sided germ lies strictly below/above the value at the point.  Formally, e.g.

    `a ∈ MonoLm Y ↔ ∃ ε y, ε > 0 ∧ (a,y) ∈ Y ∧
        ∀ z, a - ε < z → z < a → ∃ y', (z,y') ∈ Y ∧ y' < y`.

  The mathematical content is only a change of variable: `ε > 0 ↦ t := a - ε < a` (and
  `ε > 0 ↦ t := a + ε > a` for the right-hand germs) turns the definition into a statement
  about the relation `t < z < a` (resp. `a < z < t`) and the relation `(x,y) ∈ Y`, all of
  which are first-order over the language of the model.  Since the model here is `ℝ` itself,
  every nonnegative real is a square, so `≤` is the `LRc`-formula `∃ z, x + z*z = y`
  (`Work.WilC2.definable_le`), and strict `<` is `≤` minus `=`; this is the only
  order-theoretic input.

  The formalisation builds the definable sets with Mathlib's `Set.Definable` combinators
  (intersection, complement, preimages under projections, finite quantification) and the
  formula-level bookkeeping is confined to a small rewriting lemma `germ_iff` plus a change
  of variable `ε ↔ t`.
-/
import Mathlib
import Submission.Work.WilC4.monoDefs
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.finite_definable_singleton

set_option maxHeartbeats 2000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Two elementary definability lemmas -/

section Atoms

/-- Every nonnegative real is a square. -/
private lemma sq_real : ∀ x : ℝ, 0 ≤ x → ∃ z : ℝ, x = z * z :=
  fun x hx => ⟨Real.sqrt x, by rw [← pow_two, Real.sq_sqrt hx]⟩

/-- Strict order between two coordinates is `∅`-definable. -/
private lemma definable_lt_coord {α : Type} (i j : α) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {v : α → ℝ | v i < v j} := by
  have h1 := Work.WilC2.definable_le (M := ℝ) (A := (∅ : Set ℝ)) sq_real i j
  have h2 := Work.WilC2.definable_le (M := ℝ) (A := (∅ : Set ℝ)) sq_real j i
  convert h1.sdiff h2 using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
  exact lt_iff_le_not_ge

/-- Membership of a pair of coordinates in the `∅`-definable set `Y`. -/
private lemma definable_memY_pair {Y : Set (Fin 2 → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) {α : Type} (i j : α) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {v : α → ℝ | ![v i, v j] ∈ Y} := by
  convert hY.preimage_comp (α := Fin 2) (β := α) ![i, j] using 1
  ext v
  have h : v ∘ ![i, j] = ![v i, v j] := by
    funext k; fin_cases k <;> simp [Function.comp_apply]
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  rw [h]

end Atoms

/-! ## 2. The index bookkeeping at each quantifier level

The construction proceeds at three nested variable types:

* `Ω  := (((Fin 1 ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)`, where the coordinates carry
  `a, t, y, z, y'` (the point, the endpoint of the interval, the value at the point, the
  universally quantified interior point and the existentially chosen interior value);
* `Ω₁ := ((Fin 1 ⊕ Fin 2) ⊕ Fin 1)`, after the existential elimination of `y'`;
* `Fin 1 ⊕ Fin 2`, after the universal elimination of `z`, carrying `a, t, y`;
* `Fin 1`, after the existential elimination of `(t,y)`, carrying `a` only. -/

section Indices

/-- The point `a` inside `Ω`. -/
private def gA : ((((Fin 1 ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)) := Sum.inl (Sum.inl (Sum.inl (0 : Fin 1)))
/-- The left endpoint `t` inside `Ω`. -/
private def gT : ((((Fin 1 ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)) := Sum.inl (Sum.inl (Sum.inr (0 : Fin 2)))
/-- The value `y` at the point inside `Ω`. -/
private def gY : ((((Fin 1 ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)) := Sum.inl (Sum.inl (Sum.inr (1 : Fin 2)))
/-- The universally quantified interior point `z` inside `Ω`. -/
private def gZ : ((((Fin 1 ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)) := Sum.inl (Sum.inr (0 : Fin 1))
/-- The existentially quantified interior value `y'` inside `Ω`. -/
private def gYp : ((((Fin 1 ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)) := Sum.inr (0 : Fin 1)

/-- The point `a` inside `Fin 1 ⊕ Fin 2`. -/
private def k2A : Fin 1 ⊕ Fin 2 := Sum.inl (0 : Fin 1)
/-- The left endpoint `t` inside `Fin 1 ⊕ Fin 2`. -/
private def k2T : Fin 1 ⊕ Fin 2 := Sum.inr (0 : Fin 2)
/-- The value `y` at the point inside `Fin 1 ⊕ Fin 2`. -/
private def k2Y : Fin 1 ⊕ Fin 2 := Sum.inr (1 : Fin 2)

end Indices

/-! ## 3. The rewriting lemma

`germ_iff` compares the shape obtained from the definition (real witnesses `t, y`, an
unbounded universal `z` and an inner existential `y'`) with the shape produced by the
`Set.Definable` combinators (`Fin`-indexed witnesses, the inner existential having been
moved outside the implication by `Definable.exists_of_finite`).  The two differ only by
classical logic. -/

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

section ChangeOfVariable

/-- `MonoLm` with the additive parameter replaced by the left endpoint `t = a - ε`. -/
private lemma mem_MonoLm_iff (Y : Set (Fin 2 → ℝ)) (a : ℝ) :
    a ∈ MonoLm Y ↔ ∃ t y : ℝ, t < a ∧ ![a, y] ∈ Y ∧
      ∀ z : ℝ, (t < z ∧ z < a) → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ y' < y := by
  rw [mem_MonoLm]
  constructor
  · rintro ⟨ε, y, hε, hay, hgerm⟩
    exact ⟨a - ε, y, by linarith, hay, fun z hz => hgerm z hz.1 hz.2⟩
  · rintro ⟨t, y, hta, hay, hgerm⟩
    exact ⟨a - t, y, by linarith, hay, fun z hz hza => hgerm z ⟨by linarith, hza⟩⟩

/-- `MonoHm` with the additive parameter replaced by the left endpoint `t = a - ε`. -/
private lemma mem_MonoHm_iff (Y : Set (Fin 2 → ℝ)) (a : ℝ) :
    a ∈ MonoHm Y ↔ ∃ t y : ℝ, t < a ∧ ![a, y] ∈ Y ∧
      ∀ z : ℝ, (t < z ∧ z < a) → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ y < y' := by
  rw [mem_MonoHm]
  constructor
  · rintro ⟨ε, y, hε, hay, hgerm⟩
    exact ⟨a - ε, y, by linarith, hay, fun z hz => hgerm z hz.1 hz.2⟩
  · rintro ⟨t, y, hta, hay, hgerm⟩
    exact ⟨a - t, y, by linarith, hay, fun z hz hza => hgerm z ⟨by linarith, hza⟩⟩

/-- `MonoLp` with the additive parameter replaced by the right endpoint `t = a + ε`. -/
private lemma mem_MonoLp_iff (Y : Set (Fin 2 → ℝ)) (a : ℝ) :
    a ∈ MonoLp Y ↔ ∃ t y : ℝ, a < t ∧ ![a, y] ∈ Y ∧
      ∀ z : ℝ, (a < z ∧ z < t) → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ y' < y := by
  rw [mem_MonoLp]
  constructor
  · rintro ⟨ε, y, hε, hay, hgerm⟩
    exact ⟨a + ε, y, by linarith, hay, fun z hz => hgerm z hz.1 hz.2⟩
  · rintro ⟨t, y, hat, hay, hgerm⟩
    exact ⟨t - a, y, by linarith, hay, fun z hz hza => hgerm z ⟨hz, by linarith⟩⟩

/-- `MonoHp` with the additive parameter replaced by the right endpoint `t = a + ε`. -/
private lemma mem_MonoHp_iff (Y : Set (Fin 2 → ℝ)) (a : ℝ) :
    a ∈ MonoHp Y ↔ ∃ t y : ℝ, a < t ∧ ![a, y] ∈ Y ∧
      ∀ z : ℝ, (a < z ∧ z < t) → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ y < y' := by
  rw [mem_MonoHp]
  constructor
  · rintro ⟨ε, y, hε, hay, hgerm⟩
    exact ⟨a + ε, y, by linarith, hay, fun z hz => hgerm z hz.1 hz.2⟩
  · rintro ⟨t, y, hat, hay, hgerm⟩
    exact ⟨t - a, y, by linarith, hay, fun z hz hza => hgerm z ⟨hz, by linarith⟩⟩

end ChangeOfVariable

/-! ## 5. The four definability statements -/

section Germs

variable {Y : Set (Fin 2 → ℝ)}

/-- The germ sets `MonoLm` and `MonoHm` have the same interval condition (`t < z < a`) but
opposite inequalities between `y'` and `y`; this is the common body of the two constructions. -/
private lemma definable_germ_left (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    {cmp : ℝ → ℝ → Prop}
    (hcmp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {w : ((((Fin 1 ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)) → ℝ | cmp (w gYp) (w gY)}) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : Fin 1 → ℝ | ∃ t y : ℝ, t < v 0 ∧ ![v 0, y] ∈ Y ∧
        ∀ z : ℝ, (t < z ∧ z < v 0) → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ cmp y' y} := by
  have hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {w : ((((Fin 1 ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)) → ℝ |
        (w gT < w gZ ∧ w gZ < w gA) → (![w gZ, w gYp] ∈ Y ∧ cmp (w gYp) (w gY))} := by
    convert (((definable_lt_coord gT gZ).inter (definable_lt_coord gZ gA)).himp
      ((definable_memY_pair hY gZ gYp).inter hcmp)) using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_himp_iff, Set.mem_inter_iff]
  have hB1 := hB.exists_of_finite (α := ((Fin 1 ⊕ Fin 2) ⊕ Fin 1)) (β := Fin 1)
  have hB2 := hB1.forall_of_finite (α := (Fin 1 ⊕ Fin 2)) (β := Fin 1)
  have hout : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : (Fin 1 ⊕ Fin 2) → ℝ | v k2T < v k2A} := definable_lt_coord k2T k2A
  have hmemA : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : (Fin 1 ⊕ Fin 2) → ℝ | ![v k2A, v k2Y] ∈ Y} := definable_memY_pair hY k2A k2Y
  have hE := (hout.inter hmemA).inter hB2
  have hF := hE.exists_of_finite (α := Fin 1) (β := Fin 2)
  convert hF using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr,
    gA, gT, gY, gZ, gYp, k2A, k2T, k2Y]
  exact germ_iff (fun t => t < v 0) (fun y => ![v 0, y] ∈ Y)
    (fun t z => t < z ∧ z < v 0) (fun z y' => ![z, y'] ∈ Y) cmp

/-- The germ sets `MonoLp` and `MonoHp` have the same interval condition (`a < z < t`) but
opposite inequalities between `y'` and `y`. -/
private lemma definable_germ_right (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    {cmp : ℝ → ℝ → Prop}
    (hcmp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {w : ((((Fin 1 ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)) → ℝ | cmp (w gYp) (w gY)}) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : Fin 1 → ℝ | ∃ t y : ℝ, v 0 < t ∧ ![v 0, y] ∈ Y ∧
        ∀ z : ℝ, (v 0 < z ∧ z < t) → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ cmp y' y} := by
  have hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {w : ((((Fin 1 ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)) → ℝ |
        (w gA < w gZ ∧ w gZ < w gT) → (![w gZ, w gYp] ∈ Y ∧ cmp (w gYp) (w gY))} := by
    convert (((definable_lt_coord gA gZ).inter (definable_lt_coord gZ gT)).himp
      ((definable_memY_pair hY gZ gYp).inter hcmp)) using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_himp_iff, Set.mem_inter_iff]
  have hB1 := hB.exists_of_finite (α := ((Fin 1 ⊕ Fin 2) ⊕ Fin 1)) (β := Fin 1)
  have hB2 := hB1.forall_of_finite (α := (Fin 1 ⊕ Fin 2)) (β := Fin 1)
  have hout : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : (Fin 1 ⊕ Fin 2) → ℝ | v k2A < v k2T} := definable_lt_coord k2A k2T
  have hmemA : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : (Fin 1 ⊕ Fin 2) → ℝ | ![v k2A, v k2Y] ∈ Y} := definable_memY_pair hY k2A k2Y
  have hE := (hout.inter hmemA).inter hB2
  have hF := hE.exists_of_finite (α := Fin 1) (β := Fin 2)
  convert hF using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr,
    gA, gT, gY, gZ, gYp, k2A, k2T, k2Y]
  exact germ_iff (fun t => v 0 < t) (fun y => ![v 0, y] ∈ Y)
    (fun t z => v 0 < z ∧ z < t) (fun z y' => ![z, y'] ∈ Y) cmp

private lemma definable_MonoLm (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (MonoLm Y) := by
  have hgp := definable_germ_left (Y := Y) hY
    (cmp := fun y' y => y' < y) (definable_lt_coord gYp gY)
  unfold Set.Definable₁
  convert hgp using 1
  ext v
  exact mem_MonoLm_iff Y (v 0)

private lemma definable_MonoHm (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (MonoHm Y) := by
  have hgp := definable_germ_left (Y := Y) hY
    (cmp := fun y' y => y < y') (definable_lt_coord gY gYp)
  unfold Set.Definable₁
  convert hgp using 1
  ext v
  exact mem_MonoHm_iff Y (v 0)

private lemma definable_MonoLp (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (MonoLp Y) := by
  have hgp := definable_germ_right (Y := Y) hY
    (cmp := fun y' y => y' < y) (definable_lt_coord gYp gY)
  unfold Set.Definable₁
  convert hgp using 1
  ext v
  exact mem_MonoLp_iff Y (v 0)

private lemma definable_MonoHp (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (MonoHp Y) := by
  have hgp := definable_germ_right (Y := Y) hY
    (cmp := fun y' y => y < y') (definable_lt_coord gY gYp)
  unfold Set.Definable₁
  convert hgp using 1
  ext v
  exact mem_MonoHp_iff Y (v 0)

end Germs

/-! ## 6. The theorem -/

theorem monoDefinable_germs {Y : Set (Fin 2 → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (MonoLm Y) ∧
      (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (MonoHm Y) ∧
      (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (MonoLp Y) ∧
      (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (MonoHp Y) :=
  ⟨definable_MonoLm hY, definable_MonoHm hY, definable_MonoLp hY, definable_MonoHp hY⟩

end Work.WilC4
