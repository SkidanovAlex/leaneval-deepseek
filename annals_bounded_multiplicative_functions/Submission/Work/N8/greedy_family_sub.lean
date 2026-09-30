import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n8_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.N8.greedy_family`

Greedy extraction of a small sub-family of a family of "quadruples"
`(T, q, qf, γ, Ps)` on which a `Fin K₀ → _` pigeonhole (Ramsey-type) condition holds.

The statement says: given `K₀ > 0`, there is `K` with `0 < K ≤ K₀` such that for *every* family
`G : ℝ → Finset (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)` and every `C₁, N > 0`, if every
`(K₀+1)`-tuple of elements of `G x` contains two elements with the same `q`, congruent `γ`
modulo the constant integer polynomials and with `|ΔT| ≤ C₁ N`, then there is a sub-family
`F x ⊆ ·` with `#(F x) ≤ K` which *dominates* `G x` in the same relation: every `z ∈ G x` is
within `C₁ N` in `T` of some `z' ∈ F x` with the same `q` and `γ ≡ γ' mod ℤ`.

The proof is the greedy argument: take a maximal family of pairwise unrelated elements.  The
hypothesis says that any such family has at most `K₀` elements, and maximality makes it dominate
`G x`.  So `K = K₀` works.  (In the application, `G x` is the *finite* set of quadruples coming
from the finitely many edges, cf. `N8/local_finite`.)
-/

namespace Work.N8

open Work.BMF

/-! ### The relation is symmetric and reflexive -/

private lemma ModZConst_refl (γ : Polynomial ℝ) : ModZConst γ γ := ⟨0, by simp⟩

private lemma ModZConst_symm {γ γ' : Polynomial ℝ} (h : ModZConst γ γ') : ModZConst γ' γ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨-c, by rw [hc]; simp [Polynomial.C_neg]⟩

/-! ### Abstract greedy combinatorics

`gfIndep r I` says that no two distinct elements of `I` are related by `r`. -/

private def gfIndep {α : Type*} (r : α → α → Prop) (I : Finset α) : Prop :=
  ∀ a ∈ I, ∀ b ∈ I, a ≠ b → ¬ r a b

/-- **Greedy construction.**  Every finite set `s` of a symmetric, reflexive relation `r` contains
an `r`-independent subset `I` which dominates `s`: each `z ∈ s` satisfies `r z' z` for some
`z' ∈ I`. -/
private lemma gf_indep_dom {α : Type*} [DecidableEq α] (r : α → α → Prop)
    (hsymm : ∀ a b, r a b → r b a) (href : ∀ a, r a a) (s : Finset α) :
    ∃ I ⊆ s, gfIndep r I ∧ ∀ z ∈ s, ∃ z' ∈ I, r z' z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, Finset.empty_subset _, by intro a ha; simp at ha, by intro z hz; simp at hz⟩
  | insert a t ha ih =>
    obtain ⟨I, hI_sub, hI_ind, hI_dom⟩ := ih
    by_cases hcase : ∃ i ∈ I, r i a
    · -- `a` is already dominated: keep `I`
      refine ⟨I, fun z hz => Finset.mem_insert_of_mem (hI_sub hz), hI_ind, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with hza | hzt
      · rw [hza]; exact hcase
      · exact hI_dom z hzt
    · -- `a` is unrelated to all of `I`: add it
      push Not at hcase
      refine ⟨insert a I, ?_, ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with hza | hzI
        · rw [hza]; exact Finset.mem_insert_self a t
        · exact Finset.mem_insert_of_mem (hI_sub hzI)
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with hxa | hxI
        · rcases Finset.mem_insert.mp hy with hya | hyI
          · rw [hxa, hya] at hxy; exact absurd rfl hxy
          · rw [hxa]; intro h; exact hcase y hyI (hsymm a y h)
        · rcases Finset.mem_insert.mp hy with hya | hyI
          · rw [hya]; exact hcase x hxI
          · exact hI_ind x hxI y hyI hxy
      · intro z hz
        rcases Finset.mem_insert.mp hz with hza | hzt
        · rw [hza]; exact ⟨a, Finset.mem_insert_self a I, href a⟩
        · obtain ⟨z', hz'I, hz'r⟩ := hI_dom z hzt
          exact ⟨z', Finset.mem_insert_of_mem hz'I, hz'r⟩

/-- **Size bound.**  If no `(N₀+1)`-tuple drawn from `s` consists of pairwise unrelated elements,
then every `r`-independent subset of `s` has at most `N₀` elements (reindex a purported larger
independent set of size `N₀+1` along `Fin (N₀+1)` and apply the hypothesis). -/
private lemma gf_card_le {α : Type*} [DecidableEq α] (r : α → α → Prop) (N₀ : ℕ) (s : Finset α)
    (h : ∀ v : Fin (N₀ + 1) → α, (∀ j, v j ∈ s) → ∃ j j', j ≠ j' ∧ r (v j) (v j'))
    (I : Finset α) (hI : I ⊆ s) (hind : gfIndep r I) : I.card ≤ N₀ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht_sub, ht_card⟩ :=
    Finset.exists_subset_card_eq (Nat.succ_le_of_lt hcon : N₀ + 1 ≤ I.card)
  let v : Fin (N₀ + 1) → α := fun k => ((t.equivFin.symm (Fin.cast ht_card.symm k)) : α)
  have hvmem : ∀ k, v k ∈ s := by
    intro k
    exact hI (ht_sub (t.equivFin.symm (Fin.cast ht_card.symm k)).2)
  obtain ⟨j, j', hjj, hr⟩ := h v hvmem
  have hvinj : Function.Injective v := by
    intro a b hab
    have h1 : t.equivFin.symm (Fin.cast ht_card.symm a)
        = t.equivFin.symm (Fin.cast ht_card.symm b) := Subtype.ext hab
    have h2 := EquivLike.injective t.equivFin.symm h1
    exact Fin.cast_injective ht_card.symm h2
  have hne : v j ≠ v j' := fun hh => hjj (hvinj hh)
  have hmemj : v j ∈ I := ht_sub (t.equivFin.symm (Fin.cast ht_card.symm j)).2
  have hmemj' : v j' ∈ I := ht_sub (t.equivFin.symm (Fin.cast ht_card.symm j')).2
  exact hind (v j) hmemj (v j') hmemj' hne hr

/-! ### The lemma -/

theorem greedy_family_sub (K₀ : ℕ) (hK₀ : 0 < K₀) :
    ∃ K : ℕ, 0 < K ∧ K ≤ K₀ ∧
    ∀ (G : ℝ → Finset (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)) (C₁ N : ℝ),
      0 < C₁ → 0 < N →
      (∀ x : ℝ, ∀ v : Fin (K₀ + 1) → (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ),
        (∀ j, v j ∈ G x) →
        ∃ j j' : Fin (K₀ + 1), j ≠ j' ∧ (v j).2.1 = (v j').2.1 ∧
          Work.BMF.ModZConst (v j).2.2.2.1 (v j').2.2.2.1 ∧
          |(v j).1 - (v j').1| ≤ C₁ * N) →
      ∃ F : ℝ → Finset (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ),
        (∀ x, (F x).card ≤ K) ∧ (∀ x, F x ⊆ G x) ∧
        ∀ x, ∀ z ∈ G x, ∃ z' ∈ F x, z'.2.1 = z.2.1 ∧
          Work.BMF.ModZConst z'.2.2.2.1 z.2.2.2.1 ∧ |z'.1 - z.1| ≤ C₁ * N
:= by
  classical
  refine ⟨K₀, hK₀, le_rfl, ?_⟩
  intro G C₁ N hC₁ hN hfam
  -- the relation "same `q`, `γ ≡ γ' mod ℤ`, `|ΔT| ≤ C₁ N`"
  let r : (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ) →
      (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ) → Prop :=
    fun z z' => z.2.1 = z'.2.1 ∧ ModZConst z.2.2.2.1 z'.2.2.2.1 ∧ |z.1 - z'.1| ≤ C₁ * N
  have hsymm : ∀ a b, r a b → r b a := by
    intro a b h
    exact ⟨h.1.symm, ModZConst_symm h.2.1, by rw [abs_sub_comm]; exact h.2.2⟩
  have href : ∀ a, r a a := by
    intro a
    refine ⟨rfl, ModZConst_refl _, ?_⟩
    have h : (0:ℝ) ≤ C₁ * N := mul_nonneg (le_of_lt hC₁) (le_of_lt hN)
    simpa using h
  -- the greedy family, for each `x`
  have hmain : ∀ x : ℝ, ∃ I : Finset (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ),
      I.card ≤ K₀ ∧ I ⊆ G x ∧ ∀ z ∈ G x, ∃ z' ∈ I, r z' z := by
    intro x
    have hbound : ∀ I ⊆ G x, gfIndep r I → I.card ≤ K₀ := by
      intro I hI hind
      exact gf_card_le r K₀ (G x) (fun v hv => hfam x v hv) I hI hind
    obtain ⟨I, hI_sub, hI_ind, hI_dom⟩ := gf_indep_dom r hsymm href (G x)
    exact ⟨I, hbound I hI_sub hI_ind, hI_sub, hI_dom⟩
  choose F hF using hmain
  refine ⟨F, fun x => (hF x).1, fun x => (hF x).2.1, ?_⟩
  intro x z hz
  obtain ⟨z', hz'mem, hz'r⟩ := (hF x).2.2 z hz
  exact ⟨z', hz'mem, hz'r.1, hz'r.2.1, hz'r.2.2⟩

end Work.N8
