import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# An element of a `p`-group outside a cyclic subgroup

If `R` is a `p`-group (in the elementwise sense of `IsPGroup`), `c` is any element of the
ambient group, and `R ⊄ ⟨c⟩`, then there is `r ∈ R` with `r ∉ ⟨c⟩` but `r ^ p ∈ ⟨c⟩`.

The proof is a plain "descend the `p`-power chain" argument.  Fix `b ∈ R \ ⟨c⟩`; since `b` is a
`p`-element, `b ^ (p ^ m) = 1 ∈ ⟨c⟩` for some `m`.  Let `i₀` be the *least* exponent with
`b ^ (p ^ i₀) ∈ ⟨c⟩`; necessarily `i₀ ≥ 1`, and then `r = b ^ (p ^ (i₀ - 1))` satisfies
`r ∉ ⟨c⟩` (minimality of `i₀`) while `r ^ p = b ^ (p ^ i₀) ∈ ⟨c⟩`.  No finiteness (or primality)
of `p` is needed.
-/

set_option linter.unusedVariables false

namespace Work.PGroup.Symplectic

theorem exists_notMem_zpowers_pow_mem {X : Type*} [Group X] {p : ℕ} (hp : p.Prime)
    {R : Subgroup X} (hR : IsPGroup p ↥R) {c : X}
    (hne : ∃ r ∈ R, r ∉ Subgroup.zpowers c) :
    ∃ r ∈ R, r ∉ Subgroup.zpowers c ∧ r ^ p ∈ Subgroup.zpowers c := by
  classical
  obtain ⟨r, hrR, hrc⟩ := hne
  obtain ⟨n, hn⟩ := hR ⟨r, hrR⟩
  -- translate the `IsPGroup` witness to the ambient group
  have hn' : r ^ (p ^ n) = 1 := by
    have := congrArg (fun x : ↥R => (x : X)) hn
    simpa [Subgroup.coe_pow] using this
  -- the exponent `n` shows the set of exponents below is nonempty
  have hmem : ∃ i, r ^ (p ^ i) ∈ Subgroup.zpowers c :=
    ⟨n, by rw [hn']; exact Subgroup.one_mem _⟩
  set i₀ := Nat.find hmem with hi₀def
  have hi₀ : r ^ (p ^ i₀) ∈ Subgroup.zpowers c := Nat.find_spec hmem
  -- `i₀ ≠ 0` since `r ^ (p ^ 0) = r ∉ ⟨c⟩`
  have hi₀pos : 0 < i₀ := by
    rcases Nat.eq_zero_or_pos i₀ with h | h
    · exfalso
      rw [h, pow_zero] at hi₀
      exact hrc (by simpa using hi₀)
    · exact h
  refine ⟨r ^ (p ^ (i₀ - 1)), R.pow_mem hrR _, ?_, ?_⟩
  · -- not in `⟨c⟩`, by minimality of `i₀`
    intro hcon
    have hlt : i₀ - 1 < i₀ := Nat.sub_lt hi₀pos (by norm_num)
    exact (Nat.find_min hmem hlt) hcon
  · -- the `p`-th power lands in `⟨c⟩`
    have hp1 : p ^ (i₀ - 1) * p = p ^ i₀ := by
      rw [← pow_succ]; congr 1; omega
    rw [← pow_mul, hp1]
    exact hi₀

end Work.PGroup.Symplectic
