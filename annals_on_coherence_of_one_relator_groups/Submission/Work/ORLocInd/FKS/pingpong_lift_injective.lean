import Mathlib

namespace Work.ORLocInd.FKS

/-- The Boolean predicate testing equality with `a`. -/
private def eqp {ι : Type*} [DecidableEq ι] (a : ι × Bool) : ι × Bool → Bool :=
  fun x => decide (x = a)

private lemma eqp_self {ι : Type*} [DecidableEq ι] (a : ι × Bool) : eqp a a = true := by
  simp [eqp]

/-- The head of a `dropWhile` never satisfies the predicate. -/
private lemma dropWhile_head_ne {ι : Type*} [DecidableEq ι] (a : ι × Bool) (L : List (ι × Bool)) :
    ∀ (b : ι × Bool) (t : List (ι × Bool)), L.dropWhile (eqp a) = b :: t → b ≠ a := by
  induction L with
  | nil => intro b t h; simp [List.dropWhile] at h
  | cons c l ih =>
    intro b t h
    by_cases hc : eqp a c = true
    · rw [List.dropWhile_cons_of_pos hc] at h
      exact ih b t h
    · rw [List.dropWhile_cons_of_neg hc] at h
      injection h with hcb _
      rw [← hcb]
      intro hca
      exact hc (by rw [hca]; exact eqp_self a)

/-- In a reduced word `l₀^n ++ (l₁ :: t)` with `n ≥ 1` and `l₁ ≠ l₀`, the indices of `l₀` and `l₁`
differ. -/
private lemma isReduced_replicate_cons_ne {ι : Type*} (l₀ l₁ : ι × Bool) (t : List (ι × Bool))
    (n : ℕ) (hred : FreeGroup.IsReduced (List.replicate n l₀ ++ l₁ :: t)) (hn : 1 ≤ n)
    (hl : l₁ ≠ l₀) : l₀.1 ≠ l₁.1 := by
  intro h
  have hrep : List.replicate n l₀ = List.replicate (n - 1) l₀ ++ [l₀] := by
    conv_lhs => rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn).symm]
    rw [List.replicate_add, List.replicate_one]
  have heq : List.replicate n l₀ ++ l₁ :: t = List.replicate (n - 1) l₀ ++ l₀ :: l₁ :: t := by
    rw [hrep, List.append_assoc]; rfl
  have hrel := List.isChain_iff_forall_rel_of_append_cons_cons.mp hred heq
  exact hl (Prod.ext_iff.mpr ⟨h, hrel h⟩).symm

/-- `IsReduced` descends to `dropWhile`. -/
private lemma isReduced_dropWhile {ι : Type*} (p : ι × Bool → Bool) : ∀ (L : List (ι × Bool)),
    FreeGroup.IsReduced L → FreeGroup.IsReduced (L.dropWhile p) := by
  intro L
  induction L with
  | nil => intro _; simp [List.dropWhile]
  | cons c l ih =>
    intro h
    by_cases hc : p c = true
    · rw [List.dropWhile_cons_of_pos hc]
      exact ih (List.IsChain.tail h)
    · rw [List.dropWhile_cons_of_neg hc]
      exact h

/-- The element of `M` attached to a letter. -/
private def ltr {M : Type*} [Group M] {ι : Type*} (g : ι → M) (l : ι × Bool) : M :=
  bif l.2 then g l.1 else (g l.1)⁻¹

private lemma ltr_eq_zpow {M : Type*} [Group M] {ι : Type*} (g : ι → M) (l : ι × Bool) :
    ltr g l = g l.1 ^ (cond l.2 (1 : ℤ) (-1)) := by
  obtain ⟨i, b⟩ := l
  cases b <;> simp [ltr]

/-- Ping-pong for a single reduced word: applying the word to a point outside every `S i` yields a
point of `S i₀`, where `i₀` is the index of the first letter. -/
private lemma pingpong_key {M Ω : Type*} [Group M] [MulAction M Ω] {ι : Type*} [DecidableEq ι]
    (g : ι → M) {S : ι → Set Ω}
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hact : ∀ i (k : ℤ), k ≠ 0 → ∀ x : Ω, x ∉ S i → (g i ^ k) • x ∈ S i) :
    ∀ (n : ℕ) (l₀ : ι × Bool) (t : List (ι × Bool)),
      (l₀ :: t).length ≤ n → FreeGroup.IsReduced (l₀ :: t) →
      ∀ y : Ω, (∀ i, y ∉ S i) → (List.prod ((l₀ :: t).map (ltr g))) • y ∈ S l₀.1 := by
  intro n
  induction n with
  | zero =>
    intro l₀ t hlen _
    simp only [List.length_cons] at hlen
    omega
  | succ n ih =>
    intro l₀ t hlen hred y hy
    set L : List (ι × Bool) := l₀ :: t with hL
    set tw : List (ι × Bool) := L.takeWhile (eqp l₀) with htw
    set nr : ℕ := tw.length with hnr
    have hsplit : tw ++ L.dropWhile (eqp l₀) = L := by
      rw [htw]; exact List.takeWhile_append_dropWhile
    have htk_ne : tw ≠ [] := by
      rw [htw, hL, List.takeWhile_cons_of_pos (eqp_self l₀)]
      simp
    have htake_mem : ∀ x ∈ tw, x = l₀ := fun x hx => by
      rw [htw] at hx
      have := List.mem_takeWhile_imp hx
      simpa [eqp] using this
    have htakeRep : tw = List.replicate nr l₀ := by
      rw [hnr]
      exact List.eq_replicate_length.mpr htake_mem
    have hnr1 : 1 ≤ nr := by
      have h := List.length_pos_iff.mpr htk_ne
      rw [← hnr] at h
      omega
    have hc : cond l₀.2 (1 : ℤ) (-1) ≠ 0 := by
      obtain ⟨i, b⟩ := l₀
      cases b <;> simp
    cases hdrop : L.dropWhile (eqp l₀) with
    | nil =>
      have hLr : L = tw := by
        calc L = tw ++ L.dropWhile (eqp l₀) := hsplit.symm
             _ = tw := by rw [hdrop]; simp
      have hLrep : L = List.replicate nr l₀ := by rw [hLr, htakeRep]
      have hprod : List.prod (L.map (ltr g)) = (ltr g l₀) ^ nr := by
        rw [hLrep, List.map_replicate, List.prod_replicate]
      have hpow : (ltr g l₀) ^ nr
          = g l₀.1 ^ (cond l₀.2 (1 : ℤ) (-1) * (nr : ℤ)) := by
        rw [ltr_eq_zpow, ← zpow_natCast, ← zpow_mul]
      have hK : cond l₀.2 (1 : ℤ) (-1) * (nr : ℤ) ≠ 0 :=
        mul_ne_zero hc (by omega)
      rw [hprod, hpow]
      exact hact l₀.1 _ hK y (hy l₀.1)
    | cons l₁ rest' =>
      have hl₁ne : l₁ ≠ l₀ := dropWhile_head_ne l₀ L l₁ rest' hdrop
      have hLrep : L = List.replicate nr l₀ ++ l₁ :: rest' := by
        calc L = tw ++ L.dropWhile (eqp l₀) := hsplit.symm
             _ = List.replicate nr l₀ ++ l₁ :: rest' := by rw [htakeRep, hdrop]
      have hidx : l₀.1 ≠ l₁.1 := by
        refine isReduced_replicate_cons_ne l₀ l₁ rest' nr ?_ hnr1 hl₁ne
        rw [← hLrep]
        exact hred
      have hredRest : FreeGroup.IsReduced (l₁ :: rest') := by
        have h := isReduced_dropWhile (eqp l₀) L hred
        rwa [hdrop] at h
      have hlenRest : (l₁ :: rest').length ≤ n := by
        have h1 : L.length = nr + (l₁ :: rest').length := by
          calc L.length = (tw ++ L.dropWhile (eqp l₀)).length := by rw [hsplit]
               _ = tw.length + (L.dropWhile (eqp l₀)).length := List.length_append
               _ = nr + (l₁ :: rest').length := by rw [← hnr, hdrop]
        simp only [List.length_cons] at h1 hlen ⊢
        omega
      have hzmem := ih l₁ rest' hlenRest hredRest y hy
      have hz : (List.prod ((l₁ :: rest').map (ltr g))) • y ∉ S l₀.1 :=
        Set.disjoint_left.mp (hdisj l₁.1 l₀.1 (Ne.symm hidx)) hzmem
      have hprod : List.prod (L.map (ltr g))
          = (ltr g l₀) ^ nr * List.prod ((l₁ :: rest').map (ltr g)) := by
        calc List.prod (L.map (ltr g))
            = List.prod ((tw ++ L.dropWhile (eqp l₀)).map (ltr g)) := by rw [hsplit]
          _ = List.prod (tw.map (ltr g) ++ (L.dropWhile (eqp l₀)).map (ltr g)) := by
                rw [List.map_append]
          _ = List.prod (tw.map (ltr g)) * List.prod ((L.dropWhile (eqp l₀)).map (ltr g)) :=
                List.prod_append
          _ = (ltr g l₀) ^ nr * List.prod ((l₁ :: rest').map (ltr g)) := by
                rw [htakeRep, List.map_replicate, List.prod_replicate, hdrop]
      have hpow : (ltr g l₀) ^ nr
          = g l₀.1 ^ (cond l₀.2 (1 : ℤ) (-1) * (nr : ℤ)) := by
        rw [ltr_eq_zpow, ← zpow_natCast, ← zpow_mul]
      have hK : cond l₀.2 (1 : ℤ) (-1) * (nr : ℤ) ≠ 0 := mul_ne_zero hc (by omega)
      rw [hprod, mul_smul, hpow]
      exact hact l₀.1 _ hK _ hz

/-- **Ping-pong lemma.** Let a group `M` act on a type `Ω`. Let `g : ι → M` be a family of elements
and let `S : ι → Set Ω` be pairwise disjoint subsets of `Ω`. Assume that every nonzero power of
`g i` maps the complement of `S i` into `S i`, and that there is a point `x` of `Ω` lying outside
every `S i`. Then the elements `g i` generate a free group: the canonical homomorphism
`FreeGroup ι →* M` sending the generator `i` to `g i` is injective.

(Intended proof: for `u ≠ 1`, consider the reduced word `u.toWord`; group it into maximal runs of
equal letters.  Applying the word to `x` (reading from the right) and using the hypotheses run by
run shows that `(FreeGroup.lift g u) • x` lies in `S i₀`, where `i₀` is the index of the first
letter of the word, while `x ∉ S i₀`; hence `(FreeGroup.lift g u) • x ≠ x`, so `FreeGroup.lift g u
≠ 1`.  The case of an empty index type is trivial since `FreeGroup ι` is then a subsingleton.) -/
theorem pingpong_lift_injective {M Ω : Type*} [Group M] [MulAction M Ω] {ι : Type*} [DecidableEq ι]
    (g : ι → M) {S : ι → Set Ω}
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hact : ∀ i (k : ℤ), k ≠ 0 → ∀ x : Ω, x ∉ S i → (g i ^ k) • x ∈ S i)
    {x : Ω} (hx : ∀ i, x ∉ S i) :
    Function.Injective (FreeGroup.lift g) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  by_contra hne
  have hLne : u.toWord ≠ [] := fun h => hne (FreeGroup.toWord_eq_nil_iff.mp h)
  obtain ⟨l₀, t, hL⟩ : ∃ l₀ t, u.toWord = l₀ :: t := by
    cases hw : u.toWord with
    | nil => exact absurd hw hLne
    | cons a l => exact ⟨a, l, rfl⟩
  have hred : FreeGroup.IsReduced (l₀ :: t) := by
    rw [← hL]; exact FreeGroup.isReduced_toWord
  have hmem := pingpong_key g hdisj hact (l₀ :: t).length l₀ t (le_refl _) hred x hx
  have hlift : FreeGroup.lift g u = List.prod ((l₀ :: t).map (ltr g)) := by
    rw [← FreeGroup.mk_toWord (x := u), FreeGroup.lift_mk, hL]
    rfl
  rw [← hlift] at hmem
  rw [hu, one_smul] at hmem
  exact hx l₀.1 hmem

end Work.ORLocInd.FKS
