import Mathlib
import Submission.Work.ORLocInd.CoprodTree.StarTreePath
import Submission.Work.ORLocInd.CoprodTree.StarTreeTree

namespace Work.ORLocInd.CoprodTree

open Quiver
open Classical

universe u

variable {ι : Type u}

/-! ## Auxiliary structural facts about the letters of a path starting at a coset vertex

For a path starting at the coset vertex `vtx (some i) g`, the letters of the path are the steps
taken *out of* the coset vertices `vtx (some _) _`.  The first letter (when the path is non-empty)
is the step of the first arrow, which starts at `vtx (some i) g`; its index is therefore `i`. -/

/-- The first letter of a non-empty path starting at the coset vertex `vtx (some i) g` has index
`i`. -/
theorem letters_head_some {M : ι → Type u} [∀ i, Group (M i)] {i : ι} {g : Monoid.CoprodI M} :
    ∀ {y : Vertex M} (p : Quiver.Path (vtx (some i) g) y), p.length ≠ 0 →
      ∃ (x : Monoid.CoprodI M) (t : List (ι × Monoid.CoprodI M)),
        letters (some i) g p = (i, x) :: t := by
  intro y p
  induction p with
  | nil => intro h; exact absurd rfl h
  | cons q e ih =>
    intro _
    cases q with
    | nil =>
      have hidx : e.idx = i := (arrow_some_left e).1
      have hcond : isLeafSide (some i)
          (Quiver.Path.nil : Quiver.Path (vtx (some i) g) (vtx (some i) g)).length = true := rfl
      refine ⟨(stt (some i) g Quiver.Path.nil)⁻¹ * e.lbl, [], ?_⟩
      rw [letters_cons, dif_pos hcond, letters_nil, List.nil_append, hidx]
    | cons q' f =>
      obtain ⟨x, t, hq⟩ := ih (by simp only [Quiver.Path.length_cons]; omega)
      exact ⟨x, t ++ _, by rw [letters_cons, hq, List.cons_append]⟩

/-- **The letter bound.**  A list of letters of a path starting at a coset vertex, whose product
lies in the factor of that coset vertex, has at most one letter: if the first letter is trivial
then the remaining letters form a reduced word representing an element of a factor (of length at
most one), and a single remaining letter lying both in the factor of its own index and in the
factor `i` forces it to be trivial. -/
theorem letters_length_le_one_of_some {M : ι → Type u} [∀ i, Group (M i)] {i : ι}
    {l : List (ι × Monoid.CoprodI M)} {y : Monoid.CoprodI M}
    (hhead : ∃ x t, l = (i, x) :: t)
    (hmem : ∀ z ∈ l, z.2 ∈ factor M z.1)
    (hne : ∀ z ∈ l.tail, z.2 ≠ 1)
    (hchain : l.IsChain (fun a b => a.1 ≠ b.1))
    (hprod : (l.map (fun z => z.2)).prod = y)
    (hy : y ∈ factor M i) :
    l.length ≤ 1 := by
  obtain ⟨m, hm⟩ := mem_factor.mp hy
  obtain ⟨x, t, rfl⟩ := hhead
  by_cases hx : x = 1
  · -- The first letter is trivial: apply the bound to the remaining letters.
    have hprod_t : (t.map (fun z => z.2)).prod = y := by
      have h := hprod
      rw [List.map_cons, List.prod_cons, hx, one_mul] at h
      exact h
    have hne_t : ∀ z ∈ t, z.2 ≠ 1 := by
      intro z hz
      exact hne z (by simpa using hz)
    have hchain_t : t.IsChain (fun a b => a.1 ≠ b.1) := by
      simpa using hchain.tail
    have hmem_t : ∀ z ∈ t, z.2 ∈ factor M z.1 := by
      intro z hz
      exact hmem z (List.mem_cons_of_mem _ hz)
    have hle2 : t.length ≤ 1 := by
      have hle : t.length ≤ (Monoid.CoprodI.Word.equiv (M := M) y).toList.length :=
        letters_length_le_word_length' hmem_t hne_t hchain_t hprod_t
      rw [← hm] at hle
      exact le_trans hle (word_length_of_le_one i m)
    cases t with
    | nil => simp
    | cons y₂ t' =>
      -- A single non-trivial letter would lie in two distinct factors.
      exfalso
      have hij : i ≠ y₂.1 := by
        have h := hchain
        rw [List.isChain_cons_cons] at h
        simpa using h.1
      have ht' : t' = [] := by
        have h' : t'.length + 1 ≤ 1 := by simpa using hle2
        exact List.eq_nil_of_length_eq_zero (by omega)
      rw [ht'] at hprod_t hne_t hmem_t
      have hy₂ : y₂.2 = y := by
        simpa using hprod_t
      have hy₂_ne : y₂.2 ≠ 1 := hne_t y₂ (by simp)
      have hy₂_mem_i : y₂.2 ∈ factor M i := by rw [hy₂]; exact hy
      have hy₂_mem : y₂.2 ∈ factor M y₂.1 := hmem_t y₂ (by simp)
      have hbot : y₂.2 ∈ (⊥ : Subgroup (Monoid.CoprodI M)) := by
        have hinf : y₂.2 ∈ factor M i ⊓ factor M y₂.1 := ⟨hy₂_mem_i, hy₂_mem⟩
        rwa [factor_inf_factor_eq_bot hij] at hinf
      exact hy₂_ne (by simpa using hbot)
  · -- Every letter of the list is non-trivial: bound by the length of the reduced word.
    have hne_l : ∀ z ∈ (i, x) :: t, z.2 ≠ 1 := by
      intro z hz
      rcases List.mem_cons.mp hz with h | h
      · rw [h]; exact hx
      · exact hne z (by simpa using h)
    have hle : ((i, x) :: t).length ≤
        (Monoid.CoprodI.Word.equiv (M := M) y).toList.length :=
      letters_length_le_word_length' hmem hne_l hchain hprod
    have hle1 : ((i, x) :: t).length ≤ (Monoid.CoprodI.Word.equiv (M := M)
        (Monoid.CoprodI.of m)).toList.length := by
      rw [← hm] at hle
      exact hle
    have hle2 : ((i, x) :: t).length ≤ 1 := le_trans hle1 (word_length_of_le_one i m)
    simpa using hle2

/-! ## The main theorem -/

theorem eq_nil_of_inv_some {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)] {i : ι} {g : Monoid.CoprodI M} {p : Quiver.Path (Work.ORLocInd.CoprodTree.vtx (some i) g) (Work.ORLocInd.CoprodTree.vtx (some i) g)} (hp : p.IsReduced) (hinv : Work.ORLocInd.CoprodTree.Inv (some i) g p) : p = Quiver.Path.nil := by
  classical
  -- A closed path of even length starting at a coset vertex ends at a coset vertex.
  have hside : isLeafSide (some i) p.length = true := by
    cases hb : isLeafSide (some i) p.length with
    | false => exact absurd (hinv.endpoint_none hb) vtx_some_ne_vtx_none
    | true => rfl
  have hmod : p.length % 2 = 0 := by
    have h := hside
    rw [isLeafSide_some] at h
    exact of_decide_eq_true h
  -- The product of the letters is `g⁻¹` times the state, hence lies in the `i`-th factor.
  have hmem : g⁻¹ * stt (some i) g p ∈ factor M i := by
    obtain ⟨⟨j, hj⟩, _⟩ := hinv.endpoint_some hside
    have hij : j = i := (idx_eq_of_vtx_some_eq hj).symm
    subst hij
    exact (vtx_some_eq_vtx_some).mp hj
  obtain ⟨m, hm⟩ := mem_factor.mp hmem
  have hprod : ((letters (some i) g p).map (fun x => x.2)).prod = Monoid.CoprodI.of m := by
    rw [hinv.prod_letters, hm]
  have hm' : Monoid.CoprodI.of m ∈ factor M i := by rw [hm]; exact hmem
  -- At most one letter, so the path has length at most two.
  have hn : (letters (some i) g p).length ≤ 1 := by
    by_cases hnil : (letters (some i) g p) = []
    · rw [hnil]; simp
    · have hpne : p.length ≠ 0 := by
        intro h0
        refine hnil ?_
        rw [Quiver.Path.eq_nil_of_length_zero p h0]
        rfl
      exact letters_length_le_one_of_some (letters_head_some p hpne)
        hinv.mem hinv.ne_one_tail hinv.chain hprod hm'
  have hLle : p.length ≤ 2 := by
    have h := hn
    rw [letters_length_some i g p] at h
    omega
  rcases (by omega : p.length = 0 ∨ p.length = 2) with h0 | h2
  · exact Quiver.Path.eq_nil_of_length_zero p h0
  · -- A closed path of length two reverses its own arrow, hence is not reduced.
    exfalso
    obtain ⟨c₁, p₁, e₂, rfl⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons (p := p)).mp (by omega)
    have hp1 : p₁.length = 1 := by
      simp only [Quiver.Path.length_cons] at h2
      omega
    obtain ⟨c₂, p₂, e₁, rfl⟩ :=
      (Quiver.Path.length_ne_zero_iff_eq_cons (p := p₁)).mp (by omega)
    have hp2 : p₂.length = 0 := by
      simp only [Quiver.Path.length_cons] at hp1
      omega
    cases p₂ with
    | nil =>
      have hd : e₂.1 = e₁.1 := by
        have hsub : Subsingleton (c₁ ⟶ vtx (some i) g) := subsingleton_arrow c₁ (vtx (some i) g)
        have he : e₂ = Quiver.reverse e₁ := hsub.elim e₂ (Quiver.reverse e₁)
        rw [he, reverse_val]
      exact (not_isReduced_of_data_eq Quiver.Path.nil e₁ e₂ hd) hp
    | cons q f =>
      simp only [Quiver.Path.length_cons] at hp2
      omega

end Work.ORLocInd.CoprodTree
