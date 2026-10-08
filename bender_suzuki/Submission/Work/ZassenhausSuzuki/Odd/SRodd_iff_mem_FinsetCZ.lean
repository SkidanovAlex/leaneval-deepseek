import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

/-- Membership in `FinsetCZ` is exactly `IsCZ`. -/
theorem mem_FinsetCZ_iff {G : Type} [Group G] [Finite G] {A : Subgroup G} :
    A ∈ Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G) ↔ Work.ZassenhausSuzuki.Odd.IsCZ A := by
  simp only [Work.ZassenhausSuzuki.Odd.FinsetCZ, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- **Element form of the disjoint-union decomposition `𝔄 = {1} ⊔ ⊔_{A ∈ ℱ} A#`.**

An element is strongly real of odd order (this includes `1`) if and only if it is the identity
or lies in one of the `ℱ`-subgroups, i.e. in the centraliser `C_G(y)` of some strongly real
element `y` with `y ≠ 1` and `y * y ≠ 1`.

* `→`: if `x` is strongly real of odd order and `x ≠ 1`, then `x² ≠ 1` (otherwise
  `orderOf x ∣ 2` and oddness forces `x = 1`), so `x` is itself an admissible witness and
  `x ∈ C_G(x) ∈ ℱ`.
* `←`: `1` is trivially strongly real of order `1`, while for `A ∈ ℱ` the basic structural
  facts (`isCZ_basic`: `A` is abelian of odd order, and every non-identity element of `A` is
  strongly real) turn `x ∈ A`, `x ≠ 1` into `x` strongly real and `|A|`, hence `orderOf x`,
  odd. -/
theorem SRodd_iff_mem_FinsetCZ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) (x : G) :
    Work.ZassenhausSuzuki.Odd.SRodd x ↔
      x = 1 ∨ ∃ A ∈ Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G), x ∈ A := by
  constructor
  · intro hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · -- `x ≠ 1`: the element `x` itself is an admissible witness for `IsCZ`.
      right
      have hxx : x * x ≠ 1 := by
        intro h2
        have hdvd : orderOf x ∣ 2 :=
          orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
        rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (orderOf x) hdvd with h1 | h1
        · exact hx1 (orderOf_eq_one_iff.mp h1)
        · exact (by norm_num : ¬ Odd 2) (h1 ▸ hx.2)
      refine ⟨Subgroup.centralizer ({x} : Set G), ?_, ?_⟩
      · rw [mem_FinsetCZ_iff]
        exact ⟨x, hx.1, hx1, hxx, rfl⟩
      · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · rintro (rfl | ⟨A, hA, hxA⟩)
    · -- `1` is strongly real of odd order.
      exact ⟨⟨1, 1, by simp, by simp, by simp⟩, by rw [orderOf_one]; norm_num⟩
    · by_cases hx1 : x = 1
      · subst hx1
        exact ⟨⟨1, 1, by simp, by simp, by simp⟩, by rw [orderOf_one]; norm_num⟩
      · -- `x ∈ A ∈ ℱ`: use the structural facts about `ℱ`-subgroups.
        have hCZA : Work.ZassenhausSuzuki.Odd.IsCZ A := mem_FinsetCZ_iff.mp hA
        obtain ⟨-, hoddA, hforall⟩ := Work.ZassenhausSuzuki.Odd.isCZ_basic h hCZA
        obtain ⟨hsr, -⟩ := hforall x hxA hx1
        exact ⟨hsr, hoddA.of_dvd_nat (Subgroup.orderOf_dvd_natCard A hxA)⟩

end Work.ZassenhausSuzuki.Odd
