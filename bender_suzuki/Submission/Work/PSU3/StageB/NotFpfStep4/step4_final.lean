import Mathlib
import Submission.Work.PSU3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.PSU3.StageB.NotFpfStep4

open Work.PSU3

/-!
# Peterfalvi II, Ch. VII §4, relation (10) ⟹ `μ²` fixes the fixed field of `σE`

Source: D. Gorenstein, R. Lyons, R. Solomon, *The classification of the finite simple
groups, Number 2*; Peterfalvi II, Ch. VII §4 (pp. 278–280), the end of the computation
that shows a certain element `η` of the stabiliser acts trivially.

We work in `E n = GF(2^{2n})` with `σE` the `2ⁿ`-power Frobenius (an involution whose
fixed field `F` has `2ⁿ` elements).  For a ring automorphism `μ` of `E n` and `c ∈ E n`
satisfying the relation

  `(c + c⁻¹ + X^μ) · X = (c + c⁻¹ + X^{μ²}) · X^μ`   for every `σE`-fixed `X ≠ b`,

we prove that `μ²` fixes every element of `F`, i.e. `μ (μ x) = x` for `σE x = x`.

The argument has two parts.

* *Algebra (the source's "(10)" step).*  Writing the relation at `X` and at `X + 1`
  (which is again `σE`-fixed, and whose `μ`-image is `X^μ + 1`) and adding the two
  instances in characteristic two, all terms but `X` and `X^{μ²}` cancel; hence
  `μ (μ X) = X` for every `σE`-fixed `X` with `X ≠ b` and `X + 1 ≠ b` (i.e. `X ≠ b + 1`).

* *Exceptions.*  Thus `μ²` fixes `F` outside the two points `b`, `b + 1`.  If `n ≥ 3`
  then `|F| = 2ⁿ ≥ 8`, and for any `y ∈ F` one finds `x ∈ F` with neither `x` nor `y + x`
  in `{b, b+1}` (at most `4` values are forbidden but `|F| > 4`); additivity of `μ²`
  then gives `μ (μ y) = y`.  If `n ≤ 2` then `|F| ≤ 4`, and `μ` permutes `F`, fixes
  `0` and `1`, and hence permutes the at-most-two-element set `F ∖ {0,1}`; so `μ²|_F`
  is the identity outright.
-/

/-- A self-map of a type with at most two elements that is injective is an involution. -/
private lemma sq_self_of_inj_card_le_two {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (hf : Function.Injective f) (hcard : Fintype.card α ≤ 2) :
    ∀ x, f (f x) = x := by
  intro x
  rcases eq_or_ne (f x) x with h | h
  · rw [h, h]
  · have hp : ({x, f x} : Finset α).card = 2 := Finset.card_pair h.symm
    have huniv : ({x, f x} : Finset α) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_univ, hp]; exact hcard
    have hmem : f (f x) ∈ ({x, f x} : Finset α) := by
      rw [huniv]; exact Finset.mem_univ _
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h'
    · exact h'
    · exact absurd h' (fun hh => h (hf hh))

/-- A self-map of a type with at most four elements that is injective and fixes two
distinct points `a`, `b` is an involution.  Indeed it permutes the at-most-two-element
complement of `{a, b}`, where its square is the identity. -/
private lemma sq_self_of_inj_fixes_two_of_card_le_four {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (hf : Function.Injective f) {a b : α} (ha : f a = a) (hb : f b = b)
    (hab : a ≠ b) (hcard : Fintype.card α ≤ 4) : ∀ x, f (f x) = x := by
  have h2 : Fintype.card {x : α // x = a ∨ x = b} = 2 := by
    rw [Fintype.card_subtype]
    rw [show ({x : α | x = a ∨ x = b} : Finset α) = {a, b} from by
      ext x; simp [eq_comm]]
    exact Finset.card_pair hab
  have hC : Fintype.card {x : α // x ≠ a ∧ x ≠ b} ≤ 2 := by
    have hcompl := Fintype.card_subtype_compl (fun x : α => x = a ∨ x = b)
    rw [h2] at hcompl
    have hcc : Fintype.card {x : α // ¬(x = a ∨ x = b)} = Fintype.card {x : α // x ≠ a ∧ x ≠ b} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by
        constructor
        · intro h; exact ⟨fun hh => h (Or.inl hh), fun hh => h (Or.inr hh)⟩
        · intro h; rintro (h' | h') <;> [exact h.1 h'; exact h.2 h']))
    rw [hcc] at hcompl
    omega
  intro x
  rcases eq_or_ne x a with h | h
  · rw [h, ha, ha]
  · rcases eq_or_ne x b with h' | h'
    · rw [h', hb, hb]
    · have hxC : x ≠ a ∧ x ≠ b := ⟨h, h'⟩
      have hfmem : ∀ p : {x : α // x ≠ a ∧ x ≠ b}, f p.1 ≠ a ∧ f p.1 ≠ b := by
        intro p
        refine ⟨fun hh => p.2.1 (hf (hh.trans ha.symm)), fun hh => p.2.2 (hf (hh.trans hb.symm))⟩
      let g : {x : α // x ≠ a ∧ x ≠ b} → {x : α // x ≠ a ∧ x ≠ b} :=
        fun p => ⟨f p.1, hfmem p⟩
      have hginj : Function.Injective g := fun p q hpq => Subtype.ext (hf (Subtype.ext_iff.mp hpq))
      have := sq_self_of_inj_card_le_two g hginj hC ⟨x, hxC⟩
      exact congrArg Subtype.val this

/-- **Small case of §4 (10).**  If `n ≤ 2` the fixed field `F` of `σE` has at most `4`
elements; a ring automorphism `μ` of `E n` that preserves `F` fixes `0` and `1`, so it
permutes the at-most-two-element set `F ∖ {0,1}`, whence `μ²|_F = id`. -/
private theorem step4_le2_aux {n : ℕ} (hn2 : n ≤ 2)
    (hcardF : Nat.card {x : Work.PSU3.E n // Work.PSU3.σE x = x} = 2 ^ n)
    (μ : Work.PSU3.E n ≃+* Work.PSU3.E n)
    (hμF : ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → Work.PSU3.σE (μ x) = μ x) :
    ∀ y : Work.PSU3.E n, Work.PSU3.σE y = y → μ (μ y) = y := by
  classical
  haveI : Fintype {x : Work.PSU3.E n // Work.PSU3.σE x = x} := Fintype.ofFinite _
  have hcard : Fintype.card {x : Work.PSU3.E n // Work.PSU3.σE x = x} ≤ 4 := by
    rw [← Nat.card_eq_fintype_card, hcardF]
    calc (2:ℕ)^n ≤ 2^2 := Nat.pow_le_pow_right (by norm_num) hn2
      _ = 4 := by norm_num
  let a : {x : Work.PSU3.E n // Work.PSU3.σE x = x} := ⟨0, by simp⟩
  let b : {x : Work.PSU3.E n // Work.PSU3.σE x = x} := ⟨1, by simp⟩
  have hab : a ≠ b := by intro h; exact zero_ne_one (congrArg Subtype.val h)
  let g : {x : Work.PSU3.E n // Work.PSU3.σE x = x} → {x : Work.PSU3.E n // Work.PSU3.σE x = x} :=
    fun p => ⟨μ p.1, hμF p.1 p.2⟩
  have hg : Function.Injective g := fun p q hpq => Subtype.ext (μ.injective (Subtype.ext_iff.mp hpq))
  have hga : g a = a := by ext; simp [g, a]
  have hgb : g b = b := by ext; simp [g, b]
  have hsq := sq_self_of_inj_fixes_two_of_card_le_four g hg hga hgb hab hcard
  intro y hy
  exact congrArg Subtype.val (hsq ⟨y, hy⟩)

/-- **Large case of §4 (10).**  If `n ≥ 3` the fixed field `F` of `σE` has `2ⁿ ≥ 8`
elements.  Given that `μ²` fixes every `σE`-fixed `X` with `X ≠ b` and `X ≠ b + 1`, it
fixes all of `F`: for `y ∈ F` choose `x ∈ F` with `x, y + x ∉ {b, b+1}` (at most four
values are excluded, and `|F| > 4`), so that `x` and `y + x` are fixed by `μ²`; then
`μ (μ y) = μ (μ (y + x)) + μ (μ x) = (y + x) + x = y`. -/
private theorem step4_ge3_aux {n : ℕ} (hn : 3 ≤ n)
    (hcardF : Nat.card {x : Work.PSU3.E n // Work.PSU3.σE x = x} = 2 ^ n)
    (μ : Work.PSU3.E n ≃+* Work.PSU3.E n) {b : Work.PSU3.E n}
    (hpair : ∀ X : Work.PSU3.E n, Work.PSU3.σE X = X → X ≠ b → X + 1 ≠ b → μ (μ X) = X) :
    ∀ y : Work.PSU3.E n, Work.PSU3.σE y = y → μ (μ y) = y := by
  classical
  intro y hy
  haveI : Fintype {x : Work.PSU3.E n // Work.PSU3.σE x = x} := Fintype.ofFinite _
  have hcardF' : Fintype.card {x : Work.PSU3.E n // Work.PSU3.σE x = x} = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact hcardF
  have hbig : 4 < Fintype.card {x : Work.PSU3.E n // Work.PSU3.σE x = x} := by
    rw [hcardF']
    calc 4 < 2^3 := by norm_num
      _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
  let T : Finset (Work.PSU3.E n) := {b, b + 1, b + y, b + 1 + y}
  have hT : T.card ≤ 4 := Finset.card_le_four
  have hex : ∃ p : {x : Work.PSU3.E n // Work.PSU3.σE x = x}, p.1 ∉ T := by
    by_contra h
    push_neg at h
    have hinj : Function.Injective (fun p : {x : Work.PSU3.E n // Work.PSU3.σE x = x} =>
        (⟨p.1, h p⟩ : T)) := by
      intro a b hab
      apply Subtype.ext
      simpa using congrArg Subtype.val hab
    have hlt := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_coe] at hlt
    omega
  obtain ⟨p, hp⟩ := hex
  have h1 : p.1 ≠ b := fun hh => hp (by simp [T, hh])
  have h2 : p.1 + 1 ≠ b := by
    intro hh
    apply hp
    have hpb : p.1 = b + 1 := by
      calc p.1 = (p.1 + 1) + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        _ = b + 1 := by rw [hh]
    simp [T, hpb]
  have h3 : y + p.1 ≠ b := by
    intro hh
    apply hp
    have hpb : p.1 = b + y := by
      calc p.1 = y + (y + p.1) := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
        _ = y + b := by rw [hh]
        _ = b + y := by rw [add_comm]
    simp [T, hpb]
  have h4 : y + p.1 + 1 ≠ b := by
    intro hh
    apply hp
    have hyb : y + p.1 = b + 1 := by
      calc y + p.1 = (y + p.1 + 1) + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        _ = b + 1 := by rw [hh]
    have hpb : p.1 = b + 1 + y := by
      calc p.1 = y + (y + p.1) := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
        _ = y + (b + 1) := by rw [hyb]
        _ = b + 1 + y := by rw [add_comm]
    simp [T, hpb]
  have hμ1 := hpair p.1 p.2 h1 h2
  have hμ2 := hpair (y + p.1) (by rw [map_add, hy, p.2]) h3 h4
  have hyeq : (y + p.1) + p.1 = y := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  calc μ (μ y) = μ (μ ((y + p.1) + p.1)) := by rw [hyeq]
    _ = μ (μ (y + p.1)) + μ (μ p.1) := by rw [map_add, map_add]
    _ = (y + p.1) + p.1 := by rw [hμ1, hμ2]
    _ = y := hyeq

/-- **Peterfalvi II, Ch. VII §4, relation (10) ⟹ `μ²` fixes the fixed field of `σE`.**

With `c = ζ + ζ⁻¹` and `μ` the field automorphism of `E n = GF(2^{2n})` induced by `η`,
the source's relation (10) `(c + X^μ) X = (c + X^{μ²}) X^μ` — stated here, uniformly, for
every `σE`-fixed `X ≠ b` — forces `μ (μ x) = x` for every `σE`-fixed `x`.  The relation is
written at `X` and at `X + 1`; since `μ (X + 1) = μ X + 1` and the field has
characteristic two, adding the two instances cancels every term except `X + μ (μ X)`.
The two exceptional values `b`, `b + 1` are then dealt with by the size of the fixed field
(`≥ 8` when `n ≥ 3`, and trivially small when `n ≤ 2`). -/
theorem step4_final {n : ℕ} (hn : 1 ≤ n) (μ : Work.PSU3.E n ≃+* Work.PSU3.E n) {c : Work.PSU3.E n}
    (hc : μ c = c)
    (hμF : ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → Work.PSU3.σE (μ x) = μ x)
    (hcardF : Nat.card {x : Work.PSU3.E n // Work.PSU3.σE x = x} = 2 ^ n)
    {b : Work.PSU3.E n}
    (hS : ∀ X : Work.PSU3.E n, Work.PSU3.σE X = X → X ≠ b →
      (c + c⁻¹ + μ X) * X = (c + c⁻¹ + μ (μ X)) * (μ X)) :
    ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → μ (μ x) = x := by
  -- ## The algebraic step: `μ²` fixes every fixed point off `b` and `b + 1`.
  have hpair : ∀ X : Work.PSU3.E n, Work.PSU3.σE X = X → X ≠ b → X + 1 ≠ b → μ (μ X) = X := by
    intro X hX h1 h2
    have hX1 : Work.PSU3.σE (X + 1) = X + 1 := by rw [map_add, map_one, hX]
    have e1 : (c + c⁻¹ + μ X) * X = (c + c⁻¹ + μ (μ X)) * μ X := hS X hX h1
    have e2 : (c + c⁻¹ + μ (X + 1)) * (X + 1) =
        (c + c⁻¹ + μ (μ (X + 1))) * μ (X + 1) := hS (X + 1) hX1 h2
    rw [map_add, map_one, map_add, map_one] at e2
    have hkey : (c + c⁻¹ + (μ X + 1)) * (X + 1) + (c + c⁻¹ + μ X) * X
        = (c + c⁻¹ + (μ (μ X) + 1)) * (μ X + 1) + (c + c⁻¹ + μ (μ X)) * μ X := by
      rw [e1, e2]
    have h2z : X + μ (μ X) = 0 := by
      linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hkey
    exact (CharTwo.add_eq_zero.mp h2z).symm
  -- ## The two exceptional values.
  intro x hx
  by_cases h3 : 3 ≤ n
  · exact step4_ge3_aux h3 hcardF μ hpair x hx
  · exact step4_le2_aux (by omega) hcardF μ hμF x hx

end Work.PSU3.StageB.NotFpfStep4
