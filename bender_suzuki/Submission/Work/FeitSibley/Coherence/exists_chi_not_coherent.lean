import Mathlib
import Submission.Work.FeitSibley.Coherence.coherent_union_singleton
import Submission.Work.FeitSibley.Coherence.Vocab

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.exists_chi_not_coherent`

This is the contrapositive of Feit–Thompson's extension criterion
(`Work.FeitSibley.Coherence.coherent_union_singleton`, Isaacs Theorem 7.14 / Peterfalvi II,
App. XII, Lemme 1(a)): if `S₀ ⊆ S` is `τ`-coherent but `S` is not, then some `χ ∈ S \ S₀`
*obstructs* coherence, in the sense that for every `ψ ∈ S₀` dividing the degree of `χ` (that is,
`χ(1) = d · ψ(1)`) the strict inequality that would allow one to adjoin `χ` to `S₀` fails:

  `∑_{ξ ∈ S₀} ξ(1)² ≤ 2 · ψ(1) · χ(1)`.

The proof runs the extension engine `coherent_union_singleton` as an induction: assuming that
every `χ ∈ S \ S₀` does satisfy the strict inequality against some `ψ ∈ S₀`, one adjoins the
elements of `S \ S₀` to `S₀` one at a time.  The sum `∑_{ξ ∈ T} ξ(1)²` grows as `T` grows, so the
inequality available against `S₀` stays valid against the enlarged set `T`, and
`coherent_union_singleton` applies at each step.  At the end `S` itself is coherent, contradicting
the hypothesis.
-/

namespace Work.FeitSibley.Coherence

open Classical

theorem exists_chi_not_coherent {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S0 S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hsub : S0 ⊆ S)
    (hIrr : ∀ x ∈ S, x ∈ Work.CharCore.Irr H)
    (hτ : Work.Coherence.IsometryOn S τ)
    (hτV : ∀ α ∈ Work.Coherence.ZSpan0 S,
      Work.Coherence.IsVChar (τ α) ∧ τ α 1 = 0)
    (hcoh : Work.Coherence.Coherent S0 τ)
    (hnot : ¬ Work.Coherence.Coherent S τ) :
    ∃ χ ∈ S, χ ∉ S0 ∧ ∀ ψ ∈ S0, ∀ d : ℕ, χ 1 = (d : ℂ) * ψ 1 →
      ∑ ξ ∈ S0, (Work.CharCore.irrDeg ξ) ^ 2 ≤
        2 * Work.CharCore.irrDeg ψ * Work.CharCore.irrDeg χ := by
  classical
  -- Contrapositively: assume every `χ ∈ S \ S₀` has a `ψ ∈ S₀` obstructing coherence in the
  -- *opposite* direction, and derive `Coherent S τ`.
  by_contra hcon0
  -- The negation of the conclusion, in the form needed by `coherent_union_singleton`.
  have hcon : ∀ χ ∈ S, χ ∉ S0 → ∃ ψ ∈ S0, ∃ d : ℕ,
      χ 1 = (d : ℂ) * ψ 1 ∧
      2 * Work.CharCore.irrDeg ψ * Work.CharCore.irrDeg χ <
        ∑ ξ ∈ S0, (Work.CharCore.irrDeg ξ) ^ 2 := by
    intro χ hχS hχnot
    by_contra h
    refine hcon0 ⟨χ, hχS, hχnot, fun ψ hψ d hd => ?_⟩
    by_contra hle
    exact h ⟨ψ, hψ, d, hd, not_le.mp hle⟩
  -- Adjoining the elements of `S \ S₀` one at a time keeps coherence.
  have key : ∀ U : Finset (H → ℂ), U ⊆ S \ S0 →
      Work.Coherence.Coherent (S0 ∪ U) τ := by
    intro U
    refine Finset.induction_on U ?base ?step
    · intro _
      simpa using hcoh
    · intro a U haU ih hsubU
      have ha_mem : a ∈ S \ S0 := hsubU (Finset.mem_insert_self a U)
      have haS : a ∈ S := (Finset.mem_sdiff.mp ha_mem).1
      have haS0 : a ∉ S0 := (Finset.mem_sdiff.mp ha_mem).2
      have hUsub : U ⊆ S \ S0 := fun x hx => hsubU (Finset.mem_insert_of_mem hx)
      have hUS : U ⊆ S := fun x hx => (Finset.mem_sdiff.mp (hUsub hx)).1
      have hcohU : Work.Coherence.Coherent (S0 ∪ U) τ := ih hUsub
      have hsubset' : (S0 ∪ U) ∪ {a} ⊆ S := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · rcases Finset.mem_union.mp hx with hx | hx
          · exact hsub hx
          · exact hUS hx
        · rw [Finset.mem_singleton] at hx
          rw [hx]
          exact haS
      -- The degree obstruction given by `hcon` persists for the enlarged set `S₀ ∪ U`.
      obtain ⟨ψ, hψS0, d, hddeg, hdineq⟩ := hcon a haS haS0
      have hsumle : ∑ ξ ∈ S0, (Work.CharCore.irrDeg ξ) ^ 2 ≤
          ∑ ξ ∈ S0 ∪ U, (Work.CharCore.irrDeg ξ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun x _ _ => Nat.zero_le _)
      have hpsi : ∃ ψ ∈ S0 ∪ U, ∃ d : ℕ, a 1 = (d : ℂ) * ψ 1 ∧
          2 * Work.CharCore.irrDeg ψ * Work.CharCore.irrDeg a <
            ∑ ξ ∈ S0 ∪ U, (Work.CharCore.irrDeg ξ) ^ 2 :=
        ⟨ψ, Finset.mem_union_left _ hψS0, d, hddeg, lt_of_lt_of_le hdineq hsumle⟩
      have hcs := coherent_union_singleton (S0 := S0 ∪ U) (chi := a) (tau := τ)
        (by
          intro h
          rcases Finset.mem_union.mp h with h | h
          · exact haS0 h
          · exact haU h)
        (fun xi hxi => hIrr xi (hsubset' hxi))
        ⟨fun α hα β hβ =>
          hτ.inner_eq α (Work.Coherence.zSpan0_mono hsubset' hα) β
            (Work.Coherence.zSpan0_mono hsubset' hβ)⟩
        (fun α hα => hτV α (Work.Coherence.zSpan0_mono hsubset' hα))
        hcohU hpsi
      have hset : S0 ∪ insert a U = (S0 ∪ U) ∪ {a} := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hset]
      exact hcs
  exact hnot (by
    have h := key (S \ S0) (Finset.Subset.refl _)
    rwa [Finset.union_sdiff_of_subset hsub] at h)

end Work.FeitSibley.Coherence
