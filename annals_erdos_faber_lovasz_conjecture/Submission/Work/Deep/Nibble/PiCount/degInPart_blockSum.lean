import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.KahnPartition

namespace Work.Deep.Nibble.PiCount

open Classical

/-- **Sum of indicators as a cardinality.**  For a finite type `α` and a
decidable predicate `p`, the sum of the indicator of `p` (as a real number) is
the cardinality of the set of points satisfying `p`, cast to `ℝ`. -/
lemma sum_ite_one_eq_card {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∑ a : α, (if p a then (1 : ℝ) else 0)) = ((Finset.univ.filter p).card : ℝ) := by
  rw [← Finset.sum_filter]
  simp

/-- The edges of `𝓗` through `v` that lie inside part `i` — the subtype
`{e : partHyp 𝓗 π i // v ∈ e}` — are the same as the edges `e ∈ 𝓗` with
`e ⊆ partSet π i` and `v ∈ e`. -/
noncomputable def subtype_partHyp_equiv {n p : ℕ} {𝓗 : HG n} (v : Fin n)
    (π : Fin n → Fin p) (i : Fin p) :
    {e : partHyp 𝓗 π i // v ∈ (e : Set (Fin n))} ≃
      {e : Set (Fin n) // e ∈ 𝓗 ∧ e ⊆ partSet π i ∧ v ∈ e} where
  toFun x := ⟨x.1.1, x.1.2.1, x.1.2.2, x.2⟩
  invFun y := ⟨⟨y.1, y.2.1, y.2.2.1⟩, y.2.2.2⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

/-- **The block condition characterises the edges inside a part** (given
`π v = i`).  An edge `e` through `v` lies inside part `i` (that is,
`e ⊆ partSet π i`) if and only if every vertex of `e` other than `v` is coloured
`i`.  The hypothesis `π v = i` is used exactly for the vertex `v` itself. -/
noncomputable def subtype_cond_equiv {n p : ℕ} {𝓗 : HG n} (v : Fin n)
    (π : Fin n → Fin p) (i : Fin p) (hv : π v = i) :
    {e : {e : 𝓗 // v ∈ (e : Set (Fin n))} //
      ∀ x ∈ (ErdosFaberLovaszConjecture.verts (e.1 : Set (Fin n))).erase v, π x = i} ≃
      {e : Set (Fin n) // e ∈ 𝓗 ∧ e ⊆ partSet π i ∧ v ∈ e} where
  toFun y := ⟨y.1.1.1, y.1.1.2, (by
    intro x hx
    by_cases hxv : x = v
    · subst hxv; exact hv
    · exact y.2 x (Finset.mem_erase.mpr ⟨hxv, by simpa using hx⟩)), y.1.2⟩
  invFun z := ⟨⟨⟨z.1, z.2.1⟩, z.2.2.2⟩, (by
    intro x hx
    have hxe : x ∈ z.1 := by
      have h1 : x ∈ ErdosFaberLovaszConjecture.verts z.1 := (Finset.mem_erase.mp hx).2
      simpa using h1
    exact z.2.2.1 hxe)⟩
  left_inv y := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

/-- The degree of `v` inside part `i` of the partition `π` counts the edges through `v` whose block `e ∖ {v}` is entirely coloured `i`. -/
theorem degInPart_blockSum {n p : ℕ} {𝓗 : HG n} (v : Fin n)
    (π : Fin n → Fin p) (i : Fin p) (hv : π v = i) :
    (degInPart 𝓗 π v i : ℝ) = ∑ e : {e : 𝓗 // v ∈ (e : Set (Fin n))},
          (if (∀ x ∈ (ErdosFaberLovaszConjecture.verts (e.1 : Set (Fin n))).erase v, π x = i)
            then (1 : ℝ) else 0) := by
  classical
  have hcar : degInPart 𝓗 π v i
      = (Finset.univ.filter (fun e : {e : 𝓗 // v ∈ (e : Set (Fin n))} =>
          ∀ x ∈ (ErdosFaberLovaszConjecture.verts (e.1 : Set (Fin n))).erase v, π x = i)).card := by
    have h2 : Nat.card {e : partHyp 𝓗 π i // v ∈ (e : Set (Fin n))}
        = Nat.card {e : Set (Fin n) // e ∈ 𝓗 ∧ e ⊆ partSet π i ∧ v ∈ e} :=
      Nat.card_congr (subtype_partHyp_equiv v π i)
    have h3 : Nat.card {e : {e : 𝓗 // v ∈ (e : Set (Fin n))} //
          ∀ x ∈ (ErdosFaberLovaszConjecture.verts (e.1 : Set (Fin n))).erase v, π x = i}
        = Nat.card {e : Set (Fin n) // e ∈ 𝓗 ∧ e ⊆ partSet π i ∧ v ∈ e} :=
      Nat.card_congr (subtype_cond_equiv v π i hv)
    have h4 : Nat.card {e : {e : 𝓗 // v ∈ (e : Set (Fin n))} //
          ∀ x ∈ (ErdosFaberLovaszConjecture.verts (e.1 : Set (Fin n))).erase v, π x = i}
        = (Finset.univ.filter (fun e : {e : 𝓗 // v ∈ (e : Set (Fin n))} =>
            ∀ x ∈ (ErdosFaberLovaszConjecture.verts (e.1 : Set (Fin n))).erase v, π x = i)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [show degInPart 𝓗 π v i = Nat.card {e : partHyp 𝓗 π i // v ∈ (e : Set (Fin n))} from rfl,
      h2, ← h3, h4]
  rw [hcar, sum_ite_one_eq_card]

end Work.Deep.Nibble.PiCount
