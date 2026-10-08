import Mathlib
import Submission.Work.FeitSibley.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.Coherence

/-- If the nonidentity elements of a subgroup `A` of a finite group `G` all lie in a single
conjugacy class (realised by elements of `h.D`) and `A` has even order, then `A` is a `2`-group.

The mathematics is elementary: `|A|` even gives, by Cauchy's theorem, an element `t ∈ A` of
order `2`; every other nonidentity `y ∈ A` is conjugate to `t`, hence also of order `2`; so
every element of `A` has order `1` or `2` and `A` is a `2`-group. -/
theorem isPGroup_two_of_conj_transitive {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (A : Subgroup G)
    (htrans : ∀ y z : G, y ∈ A → z ∈ A → y ≠ 1 → z ≠ 1 → ∃ d ∈ h.D, d * y * d⁻¹ = z)
    (heven : Even (Nat.card ↥A)) : IsPGroup 2 ↥A := by
  classical
  -- Cauchy: the even order of `A` produces an element of order `2`.
  have hdvd : 2 ∣ Nat.card ↥A := even_iff_two_dvd.mp heven
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 2 hdvd
  have htne : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have ht2G : (t : G) ^ 2 = 1 := by
    have := congrArg (fun x : ↥A => (x : G)) ht2
    simpa using this
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  by_cases hg : g = 1
  · exact ⟨0, by rw [hg]; simp⟩
  · -- every nonidentity element is conjugate to `t`, hence has order `2`
    have hgG : (g : G) ≠ 1 := fun hh => hg (Subtype.ext hh)
    have htG : (t : G) ≠ 1 := fun hh => htne (Subtype.ext hh)
    obtain ⟨d, -, hd⟩ := htrans (g : G) (t : G) g.2 t.2 hgG htG
    have hgt : (g : G) ^ 2 = 1 := by
      have hg_eq : (g : G) = d⁻¹ * (t : G) * d := by rw [← hd]; group
      rw [hg_eq, pow_two]
      rw [show d⁻¹ * (t : G) * d * (d⁻¹ * (t : G) * d) = d⁻¹ * ((t : G) * (t : G)) * d
            by group,
        ← pow_two, ht2G]
      group
    have hg2 : (g : ↥A) ^ 2 = 1 := by
      rw [Subtype.ext_iff]
      push_cast
      exact hgt
    exact ⟨1, by simpa using hg2⟩

end Work.FeitSibley.Coherence
