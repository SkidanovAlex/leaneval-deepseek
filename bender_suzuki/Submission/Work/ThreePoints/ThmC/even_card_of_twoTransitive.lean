import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.ThreePoints.ThmC

/-- **A `2`-transitive action of degree `≥ 3` has even order.**

If a finite group `X` acts `2`-transitively on a finite set `E` with at least three points, then
`|X|` is even: `|E|·(|E| − 1)` divides `|X|` (orbit–stabiliser for the diagonal action on ordered
pairs of distinct points) and `|E|·(|E| − 1)` is even. -/
theorem even_card_of_twoTransitive {X E : Type} [Group X] [MulAction X E] [Finite X] [Finite E]
    (h2 : MulAction.IsMultiplyPretransitive X E 2) (h3 : 3 ≤ Nat.card E) :
    Even (Nat.card X) := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fintype X := Fintype.ofFinite X
  -- two distinct points of `E`
  obtain ⟨a⟩ : Nonempty E :=
    Fintype.card_pos_iff.mp (by rw [← Nat.card_eq_fintype_card]; omega)
  obtain ⟨b, hba⟩ :=
    Fintype.exists_ne_of_one_lt_card (α := E) (by rw [← Nat.card_eq_fintype_card]; omega) a
  have hab : a ≠ b := fun h => hba h.symm
  -- the orbit of `(a,b)` under the diagonal action is the set of ordered pairs of distinct points
  have horb : MulAction.orbit X (a, b) = {q : E × E | q.1 ≠ q.2} := by
    ext q
    constructor
    · intro hq
      rw [MulAction.mem_orbit_iff] at hq
      obtain ⟨x, hx⟩ := hq
      intro hqeq
      refine hab ?_
      have h1 : x • a = x • b := by
        have h2' : (x • (a, b)).1 = (x • (a, b)).2 := by rw [hx]; exact hqeq
        simpa using h2'
      have h3' := congrArg (fun y => x⁻¹ • y) h1
      simpa using h3'
    · intro hq
      rw [MulAction.mem_orbit_iff]
      obtain ⟨x, hx1, hx2⟩ := (MulAction.is_two_pretransitive_iff.mp h2) hab hq
      refine ⟨x, ?_⟩
      show (x • a, x • b) = q
      rw [hx1, hx2]
  have horb' : (MulAction.orbit X (a, b)).ncard = Nat.card {q : E × E // q.1 ≠ q.2} := by
    rw [horb]
    exact (Nat.card_coe_set_eq _).symm
  -- the number of ordered pairs of distinct points is `n·(n−1)`, hence even
  have heven : Even (Nat.card {q : E × E // q.1 ≠ q.2}) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun q : E × E => q.1 = q.2)]
    have hdiag : Fintype.card {q : E × E // q.1 = q.2} = Fintype.card E := by
      refine Fintype.card_congr ?_
      refine ⟨fun q => q.1.1, fun c => ⟨(c, c), rfl⟩, ?_, ?_⟩
      · rintro ⟨⟨x, y⟩, hxy⟩
        have h : x = y := hxy
        subst h
        exact Subtype.ext rfl
      · intro c
        rfl
    rw [hdiag, Fintype.card_prod]
    set n : ℕ := Fintype.card E with hn
    have hn3 : 3 ≤ n := by
      have h := h3
      rwa [Nat.card_eq_fintype_card] at h
    have hsub : n * n - n = n * (n - 1) := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    rw [hsub]
    rcases Nat.even_or_odd n with hn' | hn'
    · exact Even.mul_right hn' (n - 1)
    · exact Even.mul_left (Nat.Odd.sub_odd hn' ⟨0, by norm_num⟩) n
  -- orbit–stabiliser
  have hindex := MulAction.index_stabilizer X (a, b)
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer X (a, b))
  rw [hindex, horb'] at hcard
  rw [← hcard]
  exact Nat.even_mul.mpr (Or.inr heven)

end Work.ThreePoints.ThmC
