import Mathlib
import Submission.Work.Hering.Config
import Submission.Work.Hering.HardCore.abelian_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The squaring map `C₂ = {x ∈ C | x² ∈ V} → V` is onto

In the abelian configuration of the hard core of Hering's theorem,

* `V ⊴ G` is elementary abelian of order `8`,
* `C = C_G(V)` is an abelian `2`-group with `Ω₁(C) = V` (`hinv`),
* `G/C ≅ Aut(V)` (`hAut`),

the square of an element of the second level `level2 V C = {x ∈ C | x * x ∈ V}` runs through all
of `V`: `sq_level2_surj`.

The mathematical content is a single `2`-adic observation combined with the transitivity of `G`
on `V#`:

* if `c ∈ C` has `c * c ≠ 1` and `c ^ 2 ^ n = 1` with `n` **minimal**, then `n ≥ 2`, and
  `d = c ^ 2 ^ (n - 2)` satisfies `d * d = c ^ 2 ^ (n - 1)`, which is an involution of `C`,
  hence lies in `Ω₁(C) = V` by `hinv` and is `≠ 1` by minimality of `n`
  (`exists_square_mem_V` below);
* every element of `V` is a conjugate of that non-identity element of `V`
  (`trans_of_hAut`, from `G/C ≅ Aut(V)`), and conjugation preserves squares, so every element of
  `V` is the square of an element of `C`; such a square root automatically lies in the second
  level.
-/

set_option autoImplicit false

namespace Work.Hering.HardCore

open LeanEval.GroupTheory.Defs

/-! ## A square of `C` lying in `V \ {1}`

This is the only structural input: `C` is a `2`-group, `Ω₁(C) = V`, and `C` is not elementary
abelian. -/

/-- **A `2`-adic minimality argument.**  If `C` is a `2`-group (`hC2`), every involution of `C`
lies in `V` (`hinv`) and some element of `C` has square `≠ 1` (`hne`), then some element `d` of
`C` has `d * d ∈ V` with `d * d ≠ 1`.

Proof: choose `c ∈ C` with `c * c ≠ 1` and let `n` be minimal with `c ^ 2 ^ n = 1` (exists by
`hC2`).  Then `n ≠ 0` and `n ≠ 1`, so `n ≥ 2`; the element `d = c ^ 2 ^ (n - 2)` squares to
`c ^ 2 ^ (n - 1)`, which is `≠ 1` by minimality of `n` and has square `c ^ 2 ^ n = 1`, hence has
order `2` and lies in `V` by `hinv`. -/
lemma exists_square_mem_V {G : Type*} [Group G] (V C : Subgroup G)
    (hC2 : IsPGroup 2 ↥C)
    (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hne : ∃ c ∈ C, c * c ≠ 1) :
    ∃ d ∈ C, d * d ∈ V ∧ d * d ≠ 1 := by
  classical
  obtain ⟨c, hcC, hcsq⟩ := hne
  have hc1 : c ≠ 1 := fun h => hcsq (by rw [h, mul_one])
  -- `c` has `2`-power order: some power `c ^ 2 ^ n` is `1`
  have hex : ∃ n : ℕ, c ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hC2 ⟨c, hcC⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  -- take the least such `n`
  set n : ℕ := Nat.find hex with hn
  have hpow : c ^ 2 ^ n = 1 := Nat.find_spec hex
  have hmin : ∀ m : ℕ, m < n → c ^ 2 ^ m ≠ 1 := fun m hm => Nat.find_min hex hm
  have hn0 : n ≠ 0 := fun h => hc1 (by simpa [h] using hpow)
  have hn1 : n ≠ 1 := by
    intro h
    refine hcsq ?_
    have h2 : c ^ 2 = 1 := by simpa [h] using hpow
    rwa [pow_two] at h2
  have hn2 : 2 ≤ n := by omega
  -- arithmetic of the `2`-power exponents
  have key₁ : 2 ^ (n - 2) * 2 = 2 ^ (n - 1) := by
    rw [← pow_succ, show n - 2 + 1 = n - 1 by omega]
  have key₂ : 2 ^ (n - 1) * 2 = 2 ^ n := by
    rw [← pow_succ, show n - 1 + 1 = n by omega]
  -- `d = c ^ 2 ^ (n - 2)` squares to `c ^ 2 ^ (n - 1)`
  have hd2 : c ^ 2 ^ (n - 2) * c ^ 2 ^ (n - 2) = c ^ 2 ^ (n - 1) := by
    rw [← pow_two, ← pow_mul, key₁]
  have hy1 : c ^ 2 ^ (n - 1) ≠ 1 := hmin (n - 1) (by omega)
  have hy2 : c ^ 2 ^ (n - 1) * c ^ 2 ^ (n - 1) = 1 := by
    rw [← pow_two, ← pow_mul, key₂, hpow]
  have hyV : c ^ 2 ^ (n - 1) ∈ V :=
    hinv _ (C.pow_mem hcC _) (orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1)
  exact ⟨c ^ 2 ^ (n - 2), C.pow_mem hcC _, by rw [hd2]; exact hyV, by rw [hd2]; exact hy1⟩

/-! ## The surjectivity of squaring on the second level -/

/-- **The squaring map on the second level is onto `V`.**  In the configuration, for every
`v ∈ V` there is `x ∈ level2 V C` with `x * x = v`.

Conjugation by `G` preserves `C` (`C ⊴ G`, since `C = C_G(V)` and `V ⊴ G`) and squares, and acts
transitively on `V#` (`trans_of_hAut`); so the square `d * d ∈ V \ {1}` of `exists_square_mem_V`
can be moved onto any prescribed `v ∈ V`, giving a square root of `v` inside `C`. -/
theorem sq_level2_surj {G : Type*} [Group G] [Finite G] (V C : Subgroup G) [V.Normal]
    (hcard : Nat.card V = 8) (hexp : ∀ x ∈ V, x * x = 1)
    (hC : C = Subgroup.centralizer ((V : Set G))) (hC2 : IsPGroup 2 ↥C)
    (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hAut : ActsAsAut V (inferInstance : V.Normal))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hne : ∃ c ∈ C, c * c ≠ 1) {v : G} (hv : v ∈ V) :
    ∃ x ∈ level2 V C hC hCab hexp, x * x = v := by
  classical
  have hVn : V.Normal := inferInstance
  have hAut' : ActsAsAut V hVn := hAut
  have hCn : C.Normal := C_normal V C hVn hC
  -- a square `d * d ∈ V \ {1}` of an element `d ∈ C`
  obtain ⟨d, hdC, hd2V, hd2ne⟩ := exists_square_mem_V V C hC2 hinv hne
  rcases eq_or_ne v 1 with rfl | hv1
  · -- `v = 1` is the square of `1 ∈ level2`
    exact ⟨1, (mem_level2_iff V C hC hCab hexp).2
        ⟨C.one_mem, by rw [one_mul]; exact V.one_mem⟩, by rw [one_mul]⟩
  · -- conjugate `d` so that its square becomes `v`
    obtain ⟨g, hg⟩ := trans_of_hAut V hVn hcard hexp hAut' (d * d) hd2V v hv hd2ne hv1
    refine ⟨g * d * g⁻¹, (mem_level2_iff V C hC hCab hexp).2 ⟨hCn.conj_mem d hdC g, ?_⟩, ?_⟩
    · rw [show (g * d * g⁻¹) * (g * d * g⁻¹) = g * (d * d) * g⁻¹ by group]
      exact hVn.conj_mem (d * d) hd2V g
    · rw [show (g * d * g⁻¹) * (g * d * g⁻¹) = g * (d * d) * g⁻¹ by group]
      exact hg.symm

end Work.Hering.HardCore
