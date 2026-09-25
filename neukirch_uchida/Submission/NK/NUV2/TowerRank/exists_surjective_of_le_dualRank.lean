import Mathlib
import Submission.NK.NUV2.TowerRank.towerIso
import Submission.NK.NUV2.TowerRank.exists_submodule_eq_of_isClosed_addSubgroup
import Submission.NK.NUV2.TowerRank.exists_linearEquiv_of_forall_dual_ne_zero
import Submission.NK.NUV2.TowerRank.continuous_of_linearEquiv_fin_fun

/-!
# `ℤ_ℓ`-rank vs. `ℤ_ℓ^r`-quotients for compact abelian groups

The main result of this file, `NK.NUV2.TowerRank.exists_surjective_of_le_dualRank`, is the
"*rank* `⟹` *quotient*" half of Shimizu's Lemma 4f.1 (see `NOTES.md` §1(b)):

for a compact Hausdorff abelian group `G` and a prime `ℓ`, if the continuous dual
`Dual G ℓ = Hom_cts(G, ℤ_ℓ)` has `ℤ_ℓ`-rank at least `r`, then there are `r` continuous characters
`χ_1, …, χ_r : G → ℤ_ℓ` whose joint evaluation

`x ↦ (χ_1 x, …, χ_r x) : G → ℤ_ℓ^r`

is **surjective**.

The proof is a chain of elementary but non-formal facts about `ℤ_ℓ`-modules:

* `Module.le_rank_iff_exists_linearMap` turns `r ≤ rank` into an injective `ℤ_ℓ`-linear map
  `j : ℤ_ℓ^r ↪ Dual G ℓ`; writing `χ i = j (Pi.single i 1)` we get an independent family of
  characters and a continuous homomorphism `Φ : Additive G →+ ℤ_ℓ^r` whose range is
  `H = Φ(Additive G)`.
* `λ ∘ Φ ≠ 0` for every nonzero `λ : ℤ_ℓ^r →ₗ ℤ_ℓ`: indeed `λ ∘ Φ = ∑ i, λ (Pi.single i 1) • χ i`
  as functions (the coordinate expansion `linearMap_fin_fun_apply_eq`), and the family `χ` is
  linearly independent.  Hence `H` is contained in the kernel of no nonzero functional.
* `H`, being a compact (hence closed) additive subgroup of `ℤ_ℓ^r`, is a `ℤ_ℓ`-submodule
  (`exists_submodule_eq_of_isClosed_addSubgroup`); the preceding point then gives a `ℤ_ℓ`-linear
  isomorphism `H ≅ ℤ_ℓ^r` (`exists_linearEquiv_of_forall_dual_ne_zero`), which is automatically
  continuous (`continuous_of_linearEquiv_fin_fun`).
* Composing that isomorphism with `Φ` yields the required `r` continuous characters, and the
  composite `G ↠ H ≅ ℤ_ℓ^r` is surjective because `Φ` is.

-/

set_option linter.unusedSectionVars false

namespace NK.NUV2.TowerRank

/-- **Coordinate expansion of a `ℤ_ℓ`-linear functional on `ℤ_ℓ^r`**: the value on `v` is the
linear combination of the values on the standard basis vectors `Pi.single i 1`. -/
theorem linearMap_fin_fun_apply_eq {ℓ r : ℕ} [Fact ℓ.Prime]
    (f : (Fin r → PadicInt ℓ) →ₗ[PadicInt ℓ] PadicInt ℓ) (v : Fin r → PadicInt ℓ) :
    f v = ∑ i, f (Pi.single i 1) * v i := by
  conv_lhs => rw [show v = ∑ i, v i • Pi.single i 1 from by
    ext j
    simp [Pi.single_apply]]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]

theorem exists_surjective_of_le_dualRank {G : Type*} [CommGroup G] [TopologicalSpace G]
    [CompactSpace G] [T2Space G] {ℓ r : ℕ} [Fact ℓ.Prime]
    (h : (r : Cardinal) ≤ NK.RankTheoryDeep.dualRank G ℓ) :
    ∃ χ : Fin r → NK.Reconstruct.Dual G ℓ,
      Function.Surjective fun x : G => fun i => χ i (Additive.ofMul x) := by
  -- ### Step 1: `r ≤ rank` gives an injection `ℤ_ℓ^r ↪ Dual G ℓ`
  have hrank : (r : Cardinal) ≤ Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual G ℓ) := h
  obtain ⟨j, hj⟩ := Module.le_rank_iff_exists_linearMap.mp hrank
  -- the corresponding independent family of characters
  let χ : Fin r → NK.Reconstruct.Dual G ℓ := fun i => j (Pi.single i 1)
  have hχ : LinearIndependent (PadicInt ℓ) χ := by
    have h1 : LinearIndependent (PadicInt ℓ) ⇑(Pi.basisFun (PadicInt ℓ) (Fin r)) :=
      (Pi.basisFun (PadicInt ℓ) (Fin r)).linearIndependent
    have h2 := h1.map' j (by rw [LinearMap.ker_eq_bot]; exact hj)
    rw [show χ = ⇑j ∘ ⇑(Pi.basisFun (PadicInt ℓ) (Fin r)) from by
      funext i
      simp [χ, Pi.basisFun_apply]]
    exact h2
  -- the joint evaluation map
  let χh : Fin r → (Additive G →+ PadicInt ℓ) := fun i => (χ i : Additive G →+ PadicInt ℓ)
  let Φ : Additive G →+ (Fin r → PadicInt ℓ) :=
    { toFun := fun x => fun i => χh i x
      map_zero' := by funext i; exact map_zero (χh i)
      map_add' := by intro a b; funext i; exact map_add (χh i) a b }
  have hΦcont : Continuous Φ := by
    rw [continuous_pi_iff]
    intro i
    exact (χ i).2
  have hHclosed :
      IsClosed ((Φ.range : AddSubgroup (Fin r → PadicInt ℓ)) : Set (Fin r → PadicInt ℓ)) :=
    (isCompact_range hΦcont).isClosed
  -- ### Step 2: no nonzero functional vanishes on the range
  have hprop : ∀ f : Module.Dual (PadicInt ℓ) (Fin r → PadicInt ℓ), f ≠ 0 →
      ∃ x ∈ Φ.range, f x ≠ 0 := by
    intro f hf
    have hexp : ∀ g : Additive G, f (Φ g) = ∑ i, f (Pi.single i 1) * χh i g := by
      intro g
      rw [linearMap_fin_fun_apply_eq]
      simp [Φ, χh]
    -- some coefficient is nonzero
    have hne : ∃ i, f (Pi.single i 1) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf (LinearMap.ext fun v => by rw [linearMap_fin_fun_apply_eq]; simp [hcon])
    obtain ⟨i0, hi0⟩ := hne
    -- the corresponding combination of characters is nonzero, by independence
    have hcomb : (∑ i, f (Pi.single i 1) • χ i : NK.Reconstruct.Dual G ℓ) ≠ 0 := by
      intro hzero
      have hcoef := (Fintype.linearIndependent_iff.mp hχ) (fun i => f (Pi.single i 1)) hzero
      exact hi0 (hcoef i0)
    -- hence it does not vanish identically
    obtain ⟨g, hg⟩ : ∃ g : Additive G,
        (∑ i, f (Pi.single i 1) • χ i : NK.Reconstruct.Dual G ℓ) g ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hcomb (Subtype.ext (AddMonoidHom.ext fun g => by simpa using hcon g))
    -- evaluation at `g` is `ℤ_ℓ`-linear, which identifies the two expressions
    let ev : NK.Reconstruct.Dual G ℓ →ₗ[PadicInt ℓ] PadicInt ℓ :=
      { toFun := fun ψ => ψ g
        map_add' := fun a b => rfl
        map_smul' := fun a ψ => by rw [NK.RankTheoryDeep.smul_dual_apply]; rfl }
    have hsumapp : (∑ i, f (Pi.single i 1) • χ i : NK.Reconstruct.Dual G ℓ) g
        = ∑ i, f (Pi.single i 1) * χh i g := by
      have h1 := map_sum (s := Finset.univ) ev (fun i => f (Pi.single i 1) • χ i)
      have h2 : ∀ i, ev (f (Pi.single i 1) • χ i) = f (Pi.single i 1) * χh i g :=
        fun i => by rw [map_smul]; rfl
      rw [Finset.sum_congr rfl fun i _ => h2 i] at h1
      exact h1
    refine ⟨Φ g, ⟨g, rfl⟩, ?_⟩
    rw [hexp g, ← hsumapp]
    exact hg
  -- ### Step 3: the range is a `ℤ_ℓ`-submodule, isomorphic to `ℤ_ℓ^r`
  obtain ⟨H', hH'⟩ := exists_submodule_eq_of_isClosed_addSubgroup (Φ.range) hHclosed
  have hprop' : ∀ f : Module.Dual (PadicInt ℓ) (Fin r → PadicInt ℓ), f ≠ 0 →
      ∃ x ∈ H', f x ≠ 0 := by
    intro f hf
    obtain ⟨x, hx, hfx⟩ := hprop f hf
    refine ⟨x, ?_, hfx⟩
    show x ∈ (H' : Set (Fin r → PadicInt ℓ))
    rw [hH']
    exact hx
  obtain ⟨σ⟩ := exists_linearEquiv_of_forall_dual_ne_zero H' hprop'
  have hσcont : Continuous σ := continuous_of_linearEquiv_fin_fun σ
  -- the range, as a map into the submodule
  have hmem : ∀ x : Additive G, Φ x ∈ (H' : Set (Fin r → PadicInt ℓ)) := by
    intro x
    rw [hH']
    exact ⟨x, rfl⟩
  let Φ' : Additive G →+ H' :=
    { toFun := fun x => ⟨Φ x, hmem x⟩
      map_zero' := Subtype.ext Φ.map_zero
      map_add' := fun a b => Subtype.ext (Φ.map_add a b) }
  have hΦ'cont : Continuous Φ' := hΦcont.subtype_mk hmem
  -- ### Step 4: the required characters
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · exact { toFun := fun x => σ (Φ' x) i
            map_zero' := by simp
            map_add' := fun a b => by simp }
  · exact (continuous_apply i).comp (hσcont.comp hΦ'cont)
  · intro v
    have hv : ((σ.symm v : H') : Fin r → PadicInt ℓ) ∈ (H' : Set (Fin r → PadicInt ℓ)) :=
      (σ.symm v).2
    rw [hH'] at hv
    obtain ⟨g, hg⟩ := hv
    refine ⟨Additive.toMul g, ?_⟩
    funext i
    have hgg : Φ' g = σ.symm v := Subtype.ext hg
    show σ (Φ' (Additive.ofMul (Additive.toMul g))) i = v i
    rw [show Additive.ofMul (Additive.toMul g) = g from rfl, hgg]
    exact congrFun (σ.apply_symm_apply v) i

end NK.NUV2.TowerRank
