/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# Kurosh's torsion theorem for a free product of two groups

An element of finite order in a free product `M ∗ N` is conjugate into one of the two factors.

The proof goes through the normal form of free products.  Mathlib has no normal form for the binary
coproduct `Monoid.Coprod M N`, but it does have one for the indexed coproduct `Monoid.CoprodI M`
(`Monoid.CoprodI.Word` is the type of reduced words and `Monoid.CoprodI.Word.equiv` is a bijection
`CoprodI M ≃ Word M` whose inverse is `Word.prod`).  We therefore

* transport `M ∗ N` to `CoprodI (fun b : Bool => cond b N M)` along the isomorphism `bridge` built
  from the two universal properties;
* prove, for reduced words `w`, that `Word.prod w = 1` only for the empty word
  (`coprodWord_prod_eq_one_iff`, an immediate consequence of the bijection);
* show that a reduced word of length `≥ 2` whose first and last letters lie in *different* factors
  has infinite order (`coprodNeWord_prod_pow_ne_one`), the power being represented by
  `NeWord.iterate`;
* show that a reduced word of length `≥ 2` whose first and last letters lie in the *same* factor can
  be conjugated (by its last letter) to a word of strictly smaller length
  (`coprodNeWord_exists_prod_eq_mul_of` + `coprodNeWord_exists_mul_of_prod`).

Strong induction on the length then yields the result.
-/
import Mathlib
import Submission.Work.OROneRel.CoprodNormalForm

open Monoid.CoprodI

namespace Work.OROneRel

universe u

/-- The `Bool`-indexed family `false ↦ M`, `true ↦ N`, so that the indexed free product of
`Fc M N` is the binary free product `M ∗ N`.  It is an `abbrev` so that `Fc M N false` unfolds
to `M` (and `Fc M N true` to `N`) at any transparency. -/
abbrev Fc (M N : Type u) : Bool → Type u
  | false => M
  | true => N

instance instFc (M N : Type u) [Group M] [Group N] : ∀ b, Group (Fc M N b)
  | false => inferInstanceAs (Group M)
  | true => inferInstanceAs (Group N)

/-! ### The reduced-word normal form -/

lemma coprodWord_prod_injective {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] :
    Function.Injective (Word.prod (M := M)) := by
  classical
  intro a b h
  exact (Word.equiv (M := M)).symm.injective h

lemma coprodWord_prod_eq_one_iff {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    (w : Word M) : Word.prod w = 1 ↔ w = Word.empty := by
  constructor
  · intro h
    exact coprodWord_prod_injective (by rw [h, Word.prod_empty])
  · intro h
    rw [h, Word.prod_empty]

/-! ### Reduced words: membership and length API -/

@[simp] lemma NeWord.toList_append {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    {i j k l : ι} (w₁ : NeWord M i j) (h : j ≠ k) (w₂ : NeWord M k l) :
    (NeWord.append w₁ h w₂).toList = w₁.toList ++ w₂.toList := rfl

@[simp] lemma NeWord.toList_singleton {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    {i : ι} (x : M i) (hx : x ≠ 1) :
    (NeWord.singleton x hx).toList = [⟨i, x⟩] := rfl

@[simp] lemma NeWord.length_append {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    {i j k l : ι} (w₁ : NeWord M i j) (h : j ≠ k) (w₂ : NeWord M k l) :
    (NeWord.append w₁ h w₂).toList.length = w₁.toList.length + w₂.toList.length := by
  simp

/-- A non-empty reduced word is a nontrivial element of the free product. -/
lemma coprodNeWord_prod_ne_one {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    {i j : ι} (w : NeWord M i j) : w.prod ≠ 1 := by
  intro h
  have h1 : w.toWord = Word.empty := (coprodWord_prod_eq_one_iff w.toWord).mp h
  have h2 : w.toWord.toList = w.toList := rfl
  rw [h1] at h2
  exact NeWord.toList_ne_nil w (by simpa using h2.symm)

/-! ### Powers of a cyclically reduced word

If the first and last letters of a reduced word lie in different factors, its powers are again
reduced, hence nontrivial. -/

/-- Powers of a reduced word whose first and last letters lie in different factors. -/
def coprodNeWord_iterate {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] {i j : ι} (h : i ≠ j)
    (u : NeWord M i j) : ℕ → NeWord M i j
  | 0 => u
  | n + 1 => NeWord.append (coprodNeWord_iterate h u n) (Ne.symm h) u

lemma coprodNeWord_iterate_prod {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] {i j : ι}
    (h : i ≠ j) (u : NeWord M i j) (n : ℕ) :
    (coprodNeWord_iterate h u n).prod = u.prod ^ (n + 1) := by
  induction n with
  | zero => simp [coprodNeWord_iterate, pow_one]
  | succ n ih =>
      show (NeWord.append (coprodNeWord_iterate h u n) (Ne.symm h) u).prod = u.prod ^ (n + 1 + 1)
      rw [NeWord.append_prod, ih, ← pow_succ]

/-- A reduced word whose first and last letters lie in different factors has infinite order. -/
lemma coprodNeWord_prod_pow_ne_one {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)] {i j : ι}
    (h : i ≠ j) (u : NeWord M i j) (n : ℕ) : u.prod ^ (n + 1) ≠ 1 := by
  rw [← coprodNeWord_iterate_prod h u n]
  exact coprodNeWord_prod_ne_one _

/-! ### Cyclic reduction

Every non-empty reduced word can be conjugated (by its last letter) either to `1`, or to a reduced
word of strictly smaller length.  This is the length-decreasing step of the induction. -/

/-- The last letter of a nontrivial (`length ≥ 2`) reduced word can be split off. -/
lemma coprodNeWord_exists_prod_eq_mul_of {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)]
    {i j : ι} (u : NeWord M i j) (hlen : 2 ≤ u.toList.length) :
    ∃ (k : ι) (u₁ : NeWord M i k) (y : M j),
      u.prod = u₁.prod * Monoid.CoprodI.of y ∧ u₁.toList.length < u.toList.length := by
  induction u with
  | singleton x hx => simp [NeWord.toList] at hlen
  | append u₁ hne u₂ ihu₁ ihu₂ =>
      cases u₂ with
      | singleton y hy =>
          refine ⟨_, u₁, y, ?_, ?_⟩
          · rw [NeWord.append_prod, NeWord.prod_singleton]
          · rw [NeWord.length_append, NeWord.toList_singleton]
            simp
      | append s₁ hne₂ s₂ =>
          have hs : 2 ≤ (NeWord.append s₁ hne₂ s₂).toList.length := by
            rw [NeWord.length_append]
            have h1 : 0 < s₁.toList.length := List.length_pos_iff.mpr (NeWord.toList_ne_nil s₁)
            have h2 : 0 < s₂.toList.length := List.length_pos_iff.mpr (NeWord.toList_ne_nil s₂)
            omega
          obtain ⟨c, s', y, hp, hl⟩ := ihu₂ hs
          refine ⟨c, NeWord.append u₁ hne s', y, ?_, ?_⟩
          · rw [NeWord.append_prod, hp, NeWord.append_prod, mul_assoc]
          · simp only [NeWord.length_append] at hl ⊢
            omega

/-- Multiplying a non-empty reduced word on the left by an element of the first factor either
collapses to `1` or is again the product of a reduced word, of no larger length. -/
lemma coprodNeWord_exists_mul_of_prod {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)]
    {i j : ι} (u : NeWord M i j) : ∀ (y : M i),
    (Monoid.CoprodI.of y * u.prod = 1) ∨
      ∃ (j' : ι) (u' : NeWord M j' j), Monoid.CoprodI.of y * u.prod = u'.prod ∧
        u'.toList.length ≤ u.toList.length := by
  induction u with
  | singleton x hx =>
      intro y
      by_cases h : y * x = 1
      · left
        rw [NeWord.prod_singleton, ← map_mul, h, map_one]
      · right
        refine ⟨_, NeWord.singleton (y * x) h, ?_, ?_⟩
        · simp only [NeWord.prod_singleton]
          exact (map_mul _ y x).symm
        · rw [NeWord.toList_singleton, NeWord.toList_singleton]
          simp
  | append u₁ hne u₂ ihu₁ ihu₂ =>
      intro y
      rcases ihu₁ y with h | ⟨j', u₁', hp, hl⟩
      · right
        refine ⟨_, u₂, ?_, ?_⟩
        · rw [NeWord.append_prod, ← mul_assoc, h, one_mul]
        · rw [NeWord.length_append]
          omega
      · right
        refine ⟨j', NeWord.append u₁' hne u₂, ?_, ?_⟩
        · rw [NeWord.append_prod, ← mul_assoc, hp, NeWord.append_prod]
        · simp only [NeWord.length_append] at hl ⊢
          omega

/-! ### Conjugation bookkeeping -/

lemma conj_trans {G : Type*} [Group G] {p q a c h' : G} (h : q = c * p * c⁻¹)
    (hh : q = h' * a * h'⁻¹) : p = (c⁻¹ * h') * a * (c⁻¹ * h')⁻¹ := by
  have h1 : p = c⁻¹ * (c * p * c⁻¹) * c := by group
  rw [h1, ← h, hh]
  group

lemma isOfFinOrder_conj {G : Type*} [Group G] (c x : G) (h : IsOfFinOrder x) :
    IsOfFinOrder (c * x * c⁻¹) := by
  have h2 := MonoidHom.isOfFinOrder (MulAut.conj c).toMonoidHom h
  simpa [MulAut.conj_apply] using h2

/-! ### The main induction -/

/-- **Kurosh's torsion theorem** in reduced-word form. -/
theorem coprodI_aux (M N : Type u) [Group M] [Group N] (n : ℕ) :
    ∀ (w : Word (Fc M N)), w.toList.length ≤ n → IsOfFinOrder w.prod →
      (∃ (h : Monoid.CoprodI (Fc M N)) (a : M),
          w.prod = h * Monoid.CoprodI.of (i := false) a * h⁻¹) ∨
      (∃ (h : Monoid.CoprodI (Fc M N)) (b : N),
          w.prod = h * Monoid.CoprodI.of (i := true) b * h⁻¹) := by
  induction n with
  | zero =>
      intro w hw _
      have hl : w.toList = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
      have hem : w = Word.empty := Word.ext (by simpa using hl)
      left
      refine ⟨1, 1, ?_⟩
      rw [hem, Word.prod_empty]
      show (1 : Monoid.CoprodI (Fc M N)) = 1 * Monoid.CoprodI.of (i := false) (1 : M) * 1⁻¹
      rw [map_one, mul_one, inv_one, mul_one]
  | succ n ih =>
      intro w hw hfin
      by_cases hsmall : w.toList.length ≤ n
      · exact ih w hsmall hfin
      · simp only [not_le] at hsmall
        have hlen : w.toList.length = n + 1 := by omega
        have hne : w ≠ Word.empty := by
          intro h; rw [h] at hlen; simp at hlen
        by_cases h1 : w.toList.length ≤ 1
        · have hlen1 : w.toList.length = 1 := by omega
          obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen1
          have hprod : w.prod = Monoid.CoprodI.of x.2 := by
            simp [Word.prod, hx]
          rcases x with ⟨b, m⟩
          cases b
          · left
            exact ⟨1, m, by rw [hprod]; simp⟩
          · right
            exact ⟨1, m, by rw [hprod]; simp⟩
        · simp only [not_le] at h1
          have hlen2 : 2 ≤ w.toList.length := by omega
          obtain ⟨i', j', u, hu⟩ := NeWord.of_word w hne
          have huw : u.toList = w.toList := by
            rw [show u.toList = u.toWord.toList from rfl, hu]
          have hup : u.prod = w.prod := by
            rw [show u.prod = u.toWord.prod from rfl, hu]
          have hulen : 2 ≤ u.toList.length := by rw [huw]; exact hlen2
          by_cases hij : i' = j'
          · subst hij
            obtain ⟨k, u₁, y, hprod, hlt⟩ := coprodNeWord_exists_prod_eq_mul_of u hulen
            have hconj : Monoid.CoprodI.of y * w.prod * (Monoid.CoprodI.of y)⁻¹
                = Monoid.CoprodI.of y * u₁.prod := by
              rw [← hup, hprod]
              group
            rcases coprodNeWord_exists_mul_of_prod u₁ y with hc | ⟨j'', u', hprod', hlen'⟩
            · have hconj1 : (Monoid.CoprodI.of y * w.prod * (Monoid.CoprodI.of y)⁻¹) = 1 := by
                rw [hconj, hc]
              have hfin' : IsOfFinOrder (Word.empty.prod : Monoid.CoprodI (Fc M N)) := by
                rw [Word.prod_empty, ← hconj1]
                exact isOfFinOrder_conj _ _ hfin
              rcases ih Word.empty (by simp) hfin' with hcase | hcase
              · left
                obtain ⟨h', a, ha⟩ := hcase
                refine ⟨(Monoid.CoprodI.of y)⁻¹ * h', a, ?_⟩
                exact conj_trans hconj1.symm (by rw [← ha, Word.prod_empty])
              · right
                obtain ⟨h', b, hb⟩ := hcase
                refine ⟨(Monoid.CoprodI.of y)⁻¹ * h', b, ?_⟩
                exact conj_trans hconj1.symm (by rw [← hb, Word.prod_empty])
            · have hkey : u'.toWord.prod
                  = Monoid.CoprodI.of y * w.prod * (Monoid.CoprodI.of y)⁻¹ := by
                rw [show u'.toWord.prod = u'.prod from rfl, ← hprod', ← hconj]
              have hlt' : u'.toWord.toList.length < w.toList.length := by
                rw [show u'.toWord.toList = u'.toList from rfl, ← huw]
                omega
              have hfin' : IsOfFinOrder u'.toWord.prod := by
                rw [hkey]
                exact isOfFinOrder_conj _ _ hfin
              rcases ih u'.toWord (by omega) hfin' with hcase | hcase
              · left
                obtain ⟨h', a, ha⟩ := hcase
                exact ⟨(Monoid.CoprodI.of y)⁻¹ * h', a, conj_trans hkey ha⟩
              · right
                obtain ⟨h', b, hb⟩ := hcase
                exact ⟨(Monoid.CoprodI.of y)⁻¹ * h', b, conj_trans hkey hb⟩
          · exfalso
            obtain ⟨m, hm, hm1⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
            have hm' : u.prod ^ m ≠ 1 := by
              obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
              exact coprodNeWord_prod_pow_ne_one hij u k
            exact hm' (by rw [hup, hm1])

/-! ### The bridge to the binary free product -/

/-- The indexed free product of the two-element family `Fc M N` is the binary free product
`M ∗ N`, both being the coproduct of `M` and `N` in the category of groups. -/
noncomputable def bridge (M N : Type u) [Group M] [Group N] :
    Monoid.CoprodI (Fc M N) ≃* Monoid.Coprod M N :=
  MonoidHom.toMulEquiv
    (Monoid.CoprodI.lift (fun b => match b with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr))
    (Monoid.Coprod.lift (Monoid.CoprodI.of (M := Fc M N) (i := false))
      (Monoid.CoprodI.of (M := Fc M N) (i := true)))
    (by
      apply Monoid.CoprodI.ext_hom
      intro b
      cases b
      · rw [MonoidHom.comp_assoc, Monoid.CoprodI.lift_comp_of, Monoid.Coprod.lift_comp_inl,
          MonoidHom.id_comp]
      · rw [MonoidHom.comp_assoc, Monoid.CoprodI.lift_comp_of, Monoid.Coprod.lift_comp_inr,
          MonoidHom.id_comp])
    (by
      apply Monoid.Coprod.hom_ext
      · rw [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inl, Monoid.CoprodI.lift_comp_of,
          MonoidHom.id_comp]
      · rw [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inr, Monoid.CoprodI.lift_comp_of,
          MonoidHom.id_comp])

@[simp] lemma bridge_of_false (M N : Type u) [Group M] [Group N] (a : M) :
    bridge M N (Monoid.CoprodI.of (i := false) a) = Monoid.Coprod.inl a := by
  simp [bridge, Monoid.CoprodI.lift_of]

@[simp] lemma bridge_of_true (M N : Type u) [Group M] [Group N] (b : N) :
    bridge M N (Monoid.CoprodI.of (i := true) b) = Monoid.Coprod.inr b := by
  simp [bridge, Monoid.CoprodI.lift_of]

/-- **Kurosh's torsion theorem for a free product of two groups**: an element of finite order in
`M ∗ N` is conjugate into one of the two factors. -/
theorem coprod_isOfFinOrder_conj {M N : Type u} [Group M] [Group N] {g : Monoid.Coprod M N}
    (hg : IsOfFinOrder g) :
    (∃ (h : Monoid.Coprod M N) (a : M), g = h * Monoid.Coprod.inl a * h⁻¹) ∨
    (∃ (h : Monoid.Coprod M N) (b : N), g = h * Monoid.Coprod.inr b * h⁻¹) := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : Word (Fc M N), w.prod = (bridge M N).symm g :=
    ⟨Word.equiv ((bridge M N).symm g), (Word.equiv (M := Fc M N)).left_inv _⟩
  have hfin : IsOfFinOrder w.prod := by
    rw [hw]
    exact MonoidHom.isOfFinOrder (bridge M N).symm.toMonoidHom hg
  rcases coprodI_aux M N w.toList.length w le_rfl hfin with hcase | hcase
  · left
    obtain ⟨h, a, ha⟩ := hcase
    refine ⟨bridge M N h, a, ?_⟩
    rw [← MulEquiv.apply_symm_apply (bridge M N) g, ← hw, ha, map_mul, map_mul, map_inv,
      bridge_of_false]
  · right
    obtain ⟨h, b, hb⟩ := hcase
    refine ⟨bridge M N h, b, ?_⟩
    rw [← MulEquiv.apply_symm_apply (bridge M N) g, ← hw, hb, map_mul, map_mul, map_inv,
      bridge_of_true]

end Work.OROneRel
