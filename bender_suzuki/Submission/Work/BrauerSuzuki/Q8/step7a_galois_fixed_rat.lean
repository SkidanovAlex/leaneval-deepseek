import Mathlib
import Submission.Work.Tame.ft10_4

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.BrauerSuzuki.Q8

/-- If `c` lies in the field generated over `ℚ` by the `m`-th roots of unity and is fixed by
every ring automorphism of `ℂ`, then `c` is rational.

Proof sketch: bridge `Algebra.adjoin ℚ {z : ℂ | z ^ m = 1} = Algebra.adjoin ℚ {ζ}` for a
primitive `m`-th root of unity `ζ`, then apply `Work.Tame.ft10_4_galois_fixed` with `a = 1`
(whose conclusion is membership in `Algebra.adjoin ℚ {z : ℂ | z ^ 1 = 1} = ⊥`), yielding
`∃ q : ℚ, c = (q : ℂ)`. -/
theorem step7a_galois_fixed_rat {m : ℕ} (hm : 0 < m) {c : ℂ}
    (hc : c ∈ Algebra.adjoin ℚ ({z : ℂ | z ^ m = 1} : Set ℂ))
    (hfix : ∀ σ : ℂ ≃+* ℂ, σ c = c) : ∃ q : ℚ, c = (q : ℂ) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  -- a primitive `m`-th root of unity generating `ℚ[{z | z ^ m = 1}]`
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ m :=
    ⟨_, Complex.isPrimitiveRoot_exp m hm.ne'⟩
  have hle : Algebra.adjoin ℚ ({z : ℂ | z ^ m = 1} : Set ℂ) ≤ Algebra.adjoin ℚ ({ζ} : Set ℂ) := by
    rw [Algebra.adjoin_le_iff]
    intro z hz
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) i
  have hcζ : c ∈ Algebra.adjoin ℚ ({ζ} : Set ℂ) := hle hc
  -- the cyclotomic fixed-field step with `a = 1`; every ring automorphism of `ℂ` fixes the
  -- `1`-st roots of unity (`z ^ 1 = 1` means `z = 1`), so `hfix` supplies the hypothesis
  have hmem := Work.Tame.ft10_4_galois_fixed (a := 1) (m := m) one_pos hm (one_dvd m) hζ hcζ
    (fun σ _ => hfix σ)
  -- `Algebra.adjoin ℚ {z : ℂ | z ^ 1 = 1} = ⊥`, i.e. `ℚ`
  have hmem2 : c ∈ (⊥ : Subalgebra ℚ ℂ) := by
    have hb : Algebra.adjoin ℚ ({z : ℂ | z ^ 1 = 1} : Set ℂ) ≤ (⊥ : Subalgebra ℚ ℂ) := by
      rw [Algebra.adjoin_le_iff]
      intro z hz
      rw [show z = 1 from by simpa using hz]
      exact Subalgebra.one_mem _
    exact hb hmem
  obtain ⟨q, hq⟩ := Algebra.mem_bot.mp hmem2
  exact ⟨q, hq.symm⟩

end Work.BrauerSuzuki.Q8
