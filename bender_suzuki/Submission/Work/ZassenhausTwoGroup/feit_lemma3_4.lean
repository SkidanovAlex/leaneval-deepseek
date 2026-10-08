import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.involutionMemConj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit 1960, Lemma 3.4 (first sentence): `G` has a single class of involutions

Let `H = Q ⋊ D` be the rank-one data of a Zassenhaus group (`IsSplitRankOne H Q t`) in a finite
group `G`.  Then `G` has exactly one conjugacy class of involutions (Feit, *On a class of doubly
transitive permutation groups*, Illinois J. Math. 4 (1960), Lemma 3.4, p. 181).

The argument is elementary and uses only the strong embedding of `H`:

* `Work.ThmF.Bender.involutionMemConj` (Peterfalvi I, Ch. I §1 (10) (a)): every involution of
  `G` is conjugate into `H`, and the corresponding conjugating element exhibits a conjugate of
  `t` of order `2` inside `H`;
* `Work.ThmF.Bender.DTransitiveInv` (Peterfalvi I, Ch. I §2 Prop. 2 (b)): the two-point
  stabiliser `D = H ∩ H^t` acts transitively on the involutions of `H`.

So an involutution `u ∈ H` (obtained by conjugating `t` into `H`) is conjugate to every
involution of `H`, and conjugating is transitive on conjugacy classes.
-/

namespace Work.ZassenhausTwoGroup

open Classical

/-- An element of `G` lying in a conjugate `H^g` of `H` is of the form `g * y * g⁻¹` with
`y ∈ H`. -/
private lemma exists_mem_of_mem_conj {G : Type} [Group G] {H : Subgroup G} {g x : G}
    (hx : x ∈ Submission.Blueprint.conj g H) : ∃ y ∈ H, g * y * g⁻¹ = x := by
  rw [Submission.Blueprint.conj, Subgroup.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  exact ⟨y, hy, by rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx⟩

theorem feit_lemma3_4 {G : Type} [Group G] [Fintype G] (H Q : Subgroup G) (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    ∃ u : G, orderOf u = 2 ∧ ∀ v : G, orderOf v = 2 → IsConj u v := by
  classical
  have hse := h.stronglyEmbedded
  -- conjugate `t` into `H`; the conjugate is an involution `u ∈ H`
  obtain ⟨g₀, hg₀⟩ := Work.ThmF.Bender.involutionMemConj hse h.invol
  obtain ⟨u, huH, hug₀⟩ := exists_mem_of_mem_conj hg₀
  have hu2 : orderOf u = 2 := by
    have h1 := Work.ThmF.Bender.orderOf_conj_eq g₀ u
    rw [hug₀, h.invol] at h1
    exact h1.symm
  refine ⟨u, hu2, ?_⟩
  intro v hv
  -- every involution of `G` is conjugate into `H`
  obtain ⟨g, hg⟩ := Work.ThmF.Bender.involutionMemConj hse hv
  obtain ⟨y, hyH, hyg⟩ := exists_mem_of_mem_conj hg
  have hy2 : orderOf y = 2 := by
    have h1 := Work.ThmF.Bender.orderOf_conj_eq g y
    rw [hyg, hv] at h1
    exact h1.symm
  -- `D = H ∩ H^t` is transitive on the involutions of `H`
  obtain ⟨d, -, hd⟩ :=
    Work.ThmF.Bender.DTransitiveInv hse h.invol h.not_mem u ⟨huH, hu2⟩ y ⟨hyH, hy2⟩
  refine isConj_iff.mpr ⟨g * d, ?_⟩
  calc (g * d) * u * (g * d)⁻¹ = g * (d * u * d⁻¹) * g⁻¹ := by group
    _ = g * y * g⁻¹ := by rw [hd]
    _ = v := hyg

end Work.ZassenhausTwoGroup
