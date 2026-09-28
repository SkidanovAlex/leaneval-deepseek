import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.Vero

/-- A nonzero submodule of `ℤ` has `ℤ`-rank one.

Lower bound: a nonzero element `x ∈ S` gives an injective linear map `ℤ → S`, `y ↦ y • x`
(injective since `ℤ` is a domain and `x ≠ 0`), so `1 = finrank ℤ ≤ finrank S`.
Upper bound: `S ↪ ℤ` and `finrank ℤ = 1`. -/
lemma finrank_submodule_int_of_ne_bot (S : Submodule ℤ ℤ) (hS : S ≠ ⊥) :
    Module.finrank ℤ ↥S = 1 := by
  have hle : Module.finrank ℤ ↥S ≤ 1 := by
    have h := Submodule.finrank_le (R := ℤ) (M := ℤ) S
    rwa [Module.finrank_self] at h
  have hge : 1 ≤ Module.finrank ℤ ↥S := by
    obtain ⟨x, hxS, hx0⟩ : ∃ x ∈ S, x ≠ 0 := by
      by_contra h
      push Not at h
      exact hS ((Submodule.eq_bot_iff S).mpr h)
    let g : ℤ →ₗ[ℤ] ↥S :=
      { toFun := fun y => y • (⟨x, hxS⟩ : ↥S)
        map_add' := fun a b => by simp [add_smul]
        map_smul' := fun a b => by simp [mul_smul] }
    have hinj : Function.Injective g := by
      intro a b hab
      have h2 : a • (⟨x, hxS⟩ : ↥S) = b • (⟨x, hxS⟩ : ↥S) := hab
      have h3 : a * x = b * x := by
        have := congrArg (fun v : ↥S => (v : ℤ)) h2
        simpa [g, smul_eq_mul] using this
      have h4 : (a - b) * x = 0 := by linarith
      have h5 : a - b = 0 := (mul_eq_zero.mp h4).resolve_right hx0
      linarith
    have h := LinearMap.finrank_le_finrank_of_injective (f := g) hinj
    rwa [Module.finrank_self] at h
  omega

/-- The range of a nonzero linear functional `ℤ^ι → ℤ` is a nonzero submodule of `ℤ`,
hence has rank one. -/
lemma finrank_range_int_functional_of_ne_zero {ι : Type*} [Fintype ι]
    (f : (ι → ℤ) →ₗ[ℤ] ℤ) (hf : f ≠ 0) :
    Module.finrank ℤ ↥f.range = 1 :=
  finrank_submodule_int_of_ne_bot _ (fun h => hf ((LinearMap.range_eq_bot).mp h))

/-- The rank of `latOrth c ⊆ ℤ^ι` is `Fintype.card ι - 1` for `c ≠ 0`.

Suggested route: `latOrth c` is the kernel of the nonzero `ℤ`-linear functional
`Fintype.linearCombination ℤ c`; its image is a nonzero subgroup of `ℤ`, hence isomorphic to `ℤ`, so
the quotient `ℤ^ι / latOrth c` is free of rank one, and rank-nullity
(`Submodule.finrank_quotient_add_finrank` together with `LinearMap.quotKerEquivRange`) gives
`Module.finrank ℤ (latOrth c) = Fintype.card ι - 1`.  (The same argument as in
`Submission/Work/HP/Sig2/gam_rank_det.lean`.) -/
theorem finrank_latOrth {ι : Type*} [Fintype ι] (c : ι → ℤ) (hc : c ≠ 0) :
    Module.finrank ℤ (latOrth c) = Fintype.card ι - 1 := by
  classical
  -- `latOrth c` is by definition the kernel of the functional `f a = ∑ i, a i * c i`.
  have hker : latOrth c = (Fintype.linearCombination ℤ c).ker := rfl
  -- `c ≠ 0` makes `f` nonzero: `f` evaluated at the `i`-th standard basis vector is `c i`.
  have hne : Fintype.linearCombination ℤ c ≠ 0 := by
    intro h
    apply hc
    funext i
    have h1 : (Fintype.linearCombination ℤ c) (Pi.single i 1) = 0 := by rw [h]; rfl
    rw [Fintype.linearCombination_apply_single, one_smul] at h1
    exact h1
  -- Rank–nullity for `f`, combined with `ℤ^ι / ker f ≃ range f`.
  have hrn := Submodule.finrank_quotient_add_finrank (R := ℤ) (M := ι → ℤ)
    (Fintype.linearCombination ℤ c).ker
  rw [LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange (Fintype.linearCombination ℤ c)),
    Module.finrank_fintype_fun_eq_card ℤ,
    finrank_range_int_functional_of_ne_zero (f := Fintype.linearCombination ℤ c) hne] at hrn
  rw [hker]
  omega

end Work.HP.Vero
