import Mathlib
import Submission.Work.AbstractDictionary.All

/-!
# `Work.ShafarevichKoch.not_residualTwoFinitenessPresentations_of_card_two`

**Namespace** `Work.ShafarevichKoch`; module
`Submission.Work.ShafarevichKoch.not_residualTwoFinitenessPresentations_of_card_two`.

The residual `2`-finiteness side condition of `Work.AbstractDictionary`,

```
Work.AbstractDictionary.ResidualTwoFinitenessPresentations Γ
```

**fails at a group of order two**: for every topological group `Γ` with `Nat.card Γ = 2` (whatever
the topology), there is a dense generating family and a finite relator set satisfying the *closed*
relation condition for which the abstract group presented by the relators is not residually a
finite `2`-group.

The witness is the pair

* `gen : Fin 2 → Γ`, `gen 0 = g` (the nontrivial element), `gen 1 = 1`, so that the relation kernel
  `K = ker (FreeGroup.lift gen)` is the kernel of the surjection `F₂ ↠ ℤ/2` sending `x₀ ↦ g`,
  `x₁ ↦ 1`;
* `S = {x₀², x₁³}`.  The presented abstract group is

  `⟨x₀, x₁ | x₀² = 1, x₁³ = 1⟩ = ℤ/2 * ℤ/3 = PSL(2,ℤ)`,

which surjects onto `Γ = ℤ/2`, so `S ⊆ K`; and the closed relation condition holds: a finite
`2`-group quotient killing `x₀²` and `x₁³` kills `x₁` (the order of `x₁`'s image divides `3` and is
a power of `2`) and `x₀²`, hence factors through `Γ = F₂/K` — it kills `K`.

On the other hand the class of `x₁` in the presented group is not separated by any finite
`2`-group quotient (the image of `x₁` in a finite `2`-group always has order dividing
`gcd(3, 2ⁿ) = 1`), so the presented group is not residually a finite `2`-group.  This is the same
obstruction as the trivial-group witness of `Work.AbstractDictionary.not_residualTwoFinitenessPresentations_trivial`
(`S = {x³}` there), transported to the two-element group.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical

namespace Work.ShafarevichKoch

/-- **The residual `2`-finiteness side condition `ResidualTwoFinitenessPresentations` fails for a
group of order two.**  The group `ℤ/2` is *itself* a finite `2`-group, but the seam it isolates is
about the presentations of `Γ` that satisfy the *closed* relation condition: the one with relators
`{x₀², x₁³}` on generators `x₀ ↦ g`, `x₁ ↦ 1` presents a group with an element (`x₁`) of order `3`
that every finite `2`-group quotient must kill. -/
theorem not_residualTwoFinitenessPresentations_of_card_two
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (hcard : Nat.card Γ = 2) :
    ¬ Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := Γ) := by
  classical
  intro hRes
  -- the unique nontrivial element `g`
  obtain ⟨g, hg_ne, huniq⟩ := (Nat.card_eq_two_iff' (1 : Γ)).mp hcard
  -- in a group of order two, `g² = 1`
  have hg_sq : g * g = 1 := by
    by_contra h
    have h' : g * g = g := huniq (g * g) h
    exact hg_ne (mul_left_cancel (show g * g = g * 1 from by rw [h', mul_one]))
  -- the dense generating family: `gen 0 = g` (nontrivial), `gen 1 = 1`
  let gen : Fin 2 → Γ := fun i => if i = 0 then g else 1
  have hgen0 : gen 0 = g := by simp [gen]
  have hgen1 : gen 1 = 1 := by simp [gen]
  -- the relator set `{x₀², x₁³}`
  let S : Finset (FreeGroup (Fin 2)) := {FreeGroup.of (0:Fin 2) ^ 2, FreeGroup.of (1:Fin 2) ^ 3}
  -- denseness holds in *any* topology, because the range is all of `Γ`
  have hgen : Work.RelatorRank.DenseGenerating gen := by
    show (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤
    have hrange : Set.range gen = Set.univ := by
      ext x
      simp only [Set.mem_range, Set.mem_univ, iff_true]
      rcases eq_or_ne x 1 with rfl | hx
      · exact ⟨1, hgen1⟩
      · exact ⟨0, by rw [hgen0, huniq x hx]⟩
    rw [hrange, Subgroup.closure_univ]
    exact le_antisymm le_top (Subgroup.le_topologicalClosure ⊤)
  -- both relators die in `Γ`
  have hkill : ∀ s ∈ S, FreeGroup.lift gen s = 1 := by
    intro s hs
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h
    · rw [h, map_pow, FreeGroup.lift_apply_of, hgen0, pow_two, hg_sq]
    · rw [h, map_pow, FreeGroup.lift_apply_of, hgen1, one_pow]
  -- the *closed* relation condition
  have hclosed : Work.AbstractDictionary.ClosedNormalGeneratesTwo
      (MonoidHom.ker (FreeGroup.lift gen)) S := by
    intro Q _ _ hQ φ hφ
    have hφ0 : φ (FreeGroup.of (0:Fin 2)) * φ (FreeGroup.of (0:Fin 2)) = 1 := by
      have hh := hφ (FreeGroup.of (0:Fin 2) ^ 2) (by simp [S])
      rwa [map_pow, pow_two] at hh
    have hφ1 : φ (FreeGroup.of (1:Fin 2)) = 1 :=
      Work.AbstractDictionary.eq_one_of_pow_three_eq_one hQ (by
        have hh := hφ (FreeGroup.of (1:Fin 2) ^ 3) (by simp [S])
        rwa [map_pow] at hh)
    -- a finite `2`-group quotient killing the relators factors through `Γ = F₂/K`
    let β : Γ →* Q :=
      { toFun := fun x => if x = 1 then 1 else φ (FreeGroup.of (0:Fin 2))
        map_one' := by simp
        map_mul' := by
          intro a b
          by_cases ha : a = 1
          · subst ha; simp
          · have ha' : a = g := huniq a ha
            by_cases hb : b = 1
            · subst hb; simp [ha']
            · have hb' : b = g := huniq b hb
              rw [ha', hb', hg_sq]
              simp [hg_ne, hφ0] }
    have hcomp : φ = β.comp (FreeGroup.lift gen) := by
      refine FreeGroup.ext_hom _ _ ?_
      intro i
      fin_cases i <;> simp [β, hgen0, hgen1, hφ1, hg_ne]
    intro w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    rw [hcomp, MonoidHom.comp_apply, hw, map_one]
  -- the presented abstract group is `ℤ/2 * ℤ/3`
  have hres : Work.ClassFieldTower.ResiduallyFiniteTwoGroup
      (FreeGroup (Fin 2) ⧸ Subgroup.normalClosure (S : Set (FreeGroup (Fin 2)))) :=
    hRes 2 gen S hgen hkill hclosed
  -- `x₁` is nontrivial in it: the character onto `ℤ/3` kills the relators but not `x₁`
  have hx1ne : QuotientGroup.mk' (Subgroup.normalClosure (S : Set (FreeGroup (Fin 2))))
      (FreeGroup.of (1 : Fin 2)) ≠ 1 := by
    intro h1
    have hmem : FreeGroup.of (1:Fin 2) ∈ Subgroup.normalClosure (S : Set (FreeGroup (Fin 2))) :=
      (QuotientGroup.eq_one_iff _).mp h1
    let ψ : FreeGroup (Fin 2) →* Multiplicative (ZMod 3) :=
      FreeGroup.lift (fun i : Fin 2 => if i = 0 then 1 else Multiplicative.ofAdd (1 : ZMod 3))
    have hψS : ∀ s ∈ S, s ∈ MonoidHom.ker ψ := by
      intro s hs
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with h | h
      · rw [h, MonoidHom.mem_ker, map_pow, FreeGroup.lift_apply_of]
        decide
      · rw [h, MonoidHom.mem_ker, map_pow, FreeGroup.lift_apply_of]
        decide
    have hle : Subgroup.normalClosure (S : Set (FreeGroup (Fin 2))) ≤ MonoidHom.ker ψ :=
      Subgroup.normalClosure_le_normal hψS
    have hx1ker : FreeGroup.of (1:Fin 2) ∈ MonoidHom.ker ψ := hle hmem
    have hx1val : ψ (FreeGroup.of (1:Fin 2)) ≠ 1 := by
      have hv : ψ (FreeGroup.of (1:Fin 2)) = Multiplicative.ofAdd (1 : ZMod 3) := by
        rw [FreeGroup.lift_apply_of]
        decide
      rw [hv]; decide
    exact hx1val (MonoidHom.mem_ker.mp hx1ker)
  -- ... but no finite `2`-group quotient separates it
  obtain ⟨N, hN, hfin, hpg, hsep⟩ := hres _ hx1ne
  haveI : N.Normal := hN
  haveI : Fintype ((FreeGroup (Fin 2) ⧸
      Subgroup.normalClosure (S : Set (FreeGroup (Fin 2)))) ⧸ N) :=
    Fintype.ofFinite _
  let φ' : FreeGroup (Fin 2) →*
      ((FreeGroup (Fin 2) ⧸ Subgroup.normalClosure (S : Set (FreeGroup (Fin 2)))) ⧸ N) :=
    (QuotientGroup.mk' N).comp
      (QuotientGroup.mk' (Subgroup.normalClosure (S : Set (FreeGroup (Fin 2)))))
  have hφ'S : ∀ s ∈ S, φ' s = 1 := by
    intro s hs
    have hs' : s ∈ Subgroup.normalClosure (S : Set (FreeGroup (Fin 2))) :=
      Subgroup.subset_normalClosure hs
    have hs1 : QuotientGroup.mk' (Subgroup.normalClosure (S : Set (FreeGroup (Fin 2)))) s = 1 :=
      (QuotientGroup.eq_one_iff s).mpr hs'
    simp [φ', MonoidHom.comp_apply, hs1]
  have htop := hclosed _ hpg φ' hφ'S
  -- `x₁` lies in the relation kernel, so the closed condition kills it in the quotient
  have hx1kerK : FreeGroup.of (1:Fin 2) ∈ MonoidHom.ker (FreeGroup.lift gen) := by
    rw [MonoidHom.mem_ker, FreeGroup.lift_apply_of, hgen1]
  have hx1φ' : φ' (FreeGroup.of (1:Fin 2)) = 1 := MonoidHom.mem_ker.mp (htop hx1kerK)
  have hfinal : QuotientGroup.mk' N
      (QuotientGroup.mk' (Subgroup.normalClosure (S : Set (FreeGroup (Fin 2))))
        (FreeGroup.of (1:Fin 2))) = 1 := by
    simpa [φ', MonoidHom.comp_apply] using hx1φ'
  exact hsep hfinal

end Work.ShafarevichKoch
