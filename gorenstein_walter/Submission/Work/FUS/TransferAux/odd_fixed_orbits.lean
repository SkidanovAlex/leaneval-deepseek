import Mathlib

set_option linter.style.haveILetI false

namespace Work.FUS.TransferAux

/-- If `g ^ 2 = 1` acts on a `G`-set `α`, then every point has `g`-orbit of length `1` or `2`,
i.e. the minimal period of the map `x ↦ g • x` is `1` or `2`. -/
lemma minimalPeriod_smul_mem_one_two {G : Type*} [Group G] {α : Type*} [MulAction G α]
    (g : G) (hg : g ^ 2 = 1) (x : α) :
    Function.minimalPeriod (fun y => g • y) x = 1 ∨ Function.minimalPeriod (fun y => g • y) x = 2 := by
  have hper : Function.IsPeriodicPt (fun y => g • y) 2 x := by
    simp only [Function.IsPeriodicPt, Function.IsFixedPt]
    change g • (g • x) = x
    rw [← mul_smul, ← pow_two, hg, one_smul]
  rcases Function.minimalPeriod_eq_one_iff_isFixedPt (f := fun y => g • y) (x := x) with ⟨_, h2⟩
  by_cases hfix : Function.IsFixedPt (fun y => g • y) x
  · exact Or.inl (h2 hfix)
  · exact Or.inr <| (Function.minimalPeriod_eq_prime_iff (f := fun y => g • y) (x := x)
      (p := 2) (hp := ⟨Nat.prime_two⟩)).mpr ⟨hper, hfix⟩

/-- Parity lemma: if a finite type `Q` is weighted by `p : Q → ℕ` taking only the values `1` and
`2`, and the total weight `∑ q, p q` is odd, then the number of points of weight `1` is odd. -/
lemma odd_of_sum {Q : Type*} [Fintype Q] (p : Q → ℕ)
    (hp : ∀ q, p q = 1 ∨ p q = 2) (hodd : Odd (∑ q, p q)) :
    Odd (Nat.card {q : Q // p q = 1}) := by
  classical
  have hAval : ∀ q ∈ Finset.univ.filter (fun q => p q = 1), p q = 1 :=
    fun q hq => (Finset.mem_filter.mp hq).2
  have hBval : ∀ q ∈ Finset.univ.filter (fun q => ¬ p q = 1), p q = 2 := by
    intro q hq
    have hne : ¬ p q = 1 := (Finset.mem_filter.mp hq).2
    rcases hp q with h | h
    · exact absurd h hne
    · exact h
  have hsumA : (∑ q ∈ Finset.univ.filter (fun q => p q = 1), p q)
      = (Finset.univ.filter (fun q => p q = 1)).card := by
    have h1 : (∑ q ∈ Finset.univ.filter (fun q => p q = 1), p q)
        = ∑ q ∈ Finset.univ.filter (fun q => p q = 1), (1 : ℕ) :=
      Finset.sum_congr rfl (fun q hq => hAval q hq)
    rw [h1, ← Finset.card_eq_sum_ones]
  have hsumB : (∑ q ∈ Finset.univ.filter (fun q => ¬ p q = 1), p q)
      = (Finset.univ.filter (fun q => ¬ p q = 1)).card * 2 := by
    have h1 : (∑ q ∈ Finset.univ.filter (fun q => ¬ p q = 1), p q)
        = ∑ q ∈ Finset.univ.filter (fun q => ¬ p q = 1), (2 : ℕ) :=
      Finset.sum_congr rfl (fun q hq => hBval q hq)
    rw [h1, Finset.sum_const, nsmul_eq_mul]
    simp
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset Q) (fun q => p q = 1) p
  have hmain : (∑ q, p q)
      = (Finset.univ.filter (fun q => p q = 1)).card
        + (Finset.univ.filter (fun q => ¬ p q = 1)).card * 2 := by
    rw [← hsplit, hsumA, hsumB]
  have hoddA : Odd (Finset.univ.filter (fun q => p q = 1)).card := by
    have h2 : Odd ((Finset.univ.filter (fun q => p q = 1)).card
        + (Finset.univ.filter (fun q => ¬ p q = 1)).card * 2) := by
      rw [← hmain]; exact hodd
    exact (Nat.odd_add.mp h2).mpr ⟨_, by ring⟩
  have hcard : (Finset.univ.filter (fun q => p q = 1)).card = Nat.card {q : Q // p q = 1} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard] at hoddA
  exact hoddA

/-- For a finite group `G`, a subgroup `S` of odd index, and an involution `g`, the number of
orbits of `⟨g⟩` on the coset space `G ⧸ S` that consist of a single point (i.e. the `g`-fixed
orbits) is odd. -/
theorem odd_fixed_orbits {G : Type*} [Group G] [Finite G] (S : Subgroup G) [S.FiniteIndex]
    (g : G) (hg : g ^ 2 = 1) (hodd : Odd S.index) :
    Odd (Nat.card {q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ S)) //
      Function.minimalPeriod (fun x => g • x) q.out = 1}) := by
  classical
  have hfin : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ S))) :=
    Fintype.ofFinite _
  haveI := hfin
  let p : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ S)) → ℕ :=
    fun q => Function.minimalPeriod (fun x => g • x) q.out
  have hp : ∀ q, p q = 1 ∨ p q = 2 := fun q => minimalPeriod_smul_mem_one_two g hg q.out
  have hsum : S.index = ∑ q, p q := Subgroup.index_eq_sum_minimalPeriod S g
  have hodd' : Odd (∑ q, p q) := hsum ▸ hodd
  exact odd_of_sum p hp hodd'

end Work.FUS.TransferAux
