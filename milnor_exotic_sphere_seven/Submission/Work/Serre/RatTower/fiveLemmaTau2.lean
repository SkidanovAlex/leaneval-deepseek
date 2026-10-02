import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The five lemma for the middle term of a short exact sequence of chain complexes

Let `S₁`, `S₂` be short exact short complexes of chain complexes of `ℚ`-modules and
`φ : S₁ ⟶ S₂` a morphism between them.  Writing `τ₁, τ₂, τ₃` for the three components of `φ`,
we show that if `homologyMap φ.τ₁ n` and `homologyMap φ.τ₃ n` are isomorphisms for all `n < N`,
and are epimorphisms for `n = N`, then the same holds for `homologyMap φ.τ₂`:
isomorphisms below `N` and an epimorphism at `N`.

Each of the short exact sequences gives a long exact homology sequence
(`HomologicalComplex.HomologySequence.composableArrows₅`), and `φ` induces a morphism of these
sequences (`mapComposableArrows₅`).  The conclusions are then the four lemma applied to the
appropriate windows:

* `Mono (homologyMap φ.τ₂ i)` for `i < N` comes from `mono_of_epi_of_mono_of_mono''` with
  `k = 2` on `composableArrows₅ hS (i+1) i`: the window
  `H_{i+1}(S.X₃) → H_i(S.X₁) → H_i(S.X₂) → H_i(S.X₃)` is mapped to the corresponding window of
  `S₂` by `τ₃ (i+1), τ₁ i, τ₂ i, τ₃ i`; the first map is an epimorphism because `i + 1 ≤ N`
  (isomorphism for `i + 1 < N`, and `e₃` for `i + 1 = N`).

* `Epi (homologyMap φ.τ₂ n)` for `n ≥ 1` (and `n ≤ N`) comes from
  `epi_of_epi_of_epi_of_mono''` with `k = 0` on `composableArrows₅ hS n (n-1)`: the window
  `H_n(S.X₁) → H_n(S.X₂) → H_n(S.X₃) → H_{n-1}(S.X₁)` is mapped by
  `τ₁ n, τ₂ n, τ₃ n, τ₁ (n-1)`; here `τ₁ n` and `τ₃ n` are epimorphisms (`n ≤ N`) and
  `τ₁ (n-1)` is a monomorphism (`n-1 < n ≤ N`).

* In degree `0` there is no `j` with `Rel 0 j`, so no five-term sequence is available and the
  above does not apply.  Instead we use the three-term exact sequences
  `H_0(S_i.X₁) → H_0(S_i.X₂) → H_0(S_i.X₃)` (`ShortComplex.ShortExact.homology_exact₂`) together
  with the fact that `H_0` of the third column map is an epimorphism: `S_i.g` is an epimorphism
  (`ShortExact.epi_g`) and `0` has no outgoing differential
  (`HomologicalComplex.epi_homologyMap_of_epi_of_not_rel`).  The lemma
  `epi_of_epi_of_exact_of_epi` below then gives `Epi (homologyMap φ.τ₂ 0)` by a diagram chase in
  the style of the (epi,epi) four lemma.

-/

namespace Work.Serre.RatTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

/-- **A diagram chase.**  Consider a commutative diagram in an abelian category

```
A --f--> B --g--> D
|α       |β       |γ
A'--f'--> B'--g'--> D'
```

in which the second row is exact at `B'`, the vertical maps `α`, `γ` are epimorphisms and `g` is
an epimorphism.  Then `β` is an epimorphism as well.

This is the "three lemma" (epi-epi version) for the middle of a three-term sequence; it is the
`i = 0` case of a five lemma for the long exact homology sequence, where no five-term window is
available.  Note that no exactness of the first row is needed: the target row has to be exact at
`B'` only because its kernel has to be recognised as the image of `f'`. -/
theorem epi_of_epi_of_exact_of_epi {C : Type*} [Category C] [Abelian C]
    {S' : ShortComplex C} {A B D : C} {f : A ⟶ B} {g : B ⟶ D}
    {α : A ⟶ S'.X₁} {β : B ⟶ S'.X₂} {γ : D ⟶ S'.X₃}
    (hS' : S'.Exact) (hα : Epi α) (hγ : Epi γ) (hg : Epi g)
    (hab : f ≫ β = α ≫ S'.f) (hbc : g ≫ γ = β ≫ S'.g) : Epi β := by
  rw [epi_iff_surjective_up_to_refinements]
  intro W y
  -- lift along `γ : D ⟶ D'`
  obtain ⟨W₁, π₁, hπ₁, c, hc⟩ := surjective_up_to_refinements_of_epi γ (y ≫ S'.g)
  -- lift along `g : B ⟶ D`
  obtain ⟨W₂, π₂, hπ₂, b, hb⟩ := surjective_up_to_refinements_of_epi g c
  -- the remaining class lies in the kernel of `g'`
  have hzero : (π₂ ≫ π₁ ≫ y - b ≫ β) ≫ S'.g = 0 := by
    rw [sub_comp]
    simp only [Category.assoc]
    rw [← hbc, ← reassoc_of% hb, ← hc, sub_self]
  obtain ⟨W₃, π₃, hπ₃, a', ha'⟩ := hS'.exact_up_to_refinements (π₂ ≫ π₁ ≫ y - b ≫ β) hzero
  -- lift along `α : A ⟶ A'`
  obtain ⟨W₄, π₄, hπ₄, a, ha⟩ := surjective_up_to_refinements_of_epi α a'
  have hkey : π₄ ≫ π₃ ≫ π₂ ≫ π₁ ≫ y - π₄ ≫ π₃ ≫ b ≫ β = a ≫ f ≫ β := by
    have h1 : π₄ ≫ (π₃ ≫ (π₂ ≫ π₁ ≫ y - b ≫ β)) = π₄ ≫ (a' ≫ S'.f) := by rw [ha']
    rw [comp_sub, comp_sub] at h1
    rw [h1, ← Category.assoc, ha, Category.assoc, ← hab]
  haveI := hπ₄
  refine ⟨W₄, π₄ ≫ π₃ ≫ π₂ ≫ π₁, inferInstance, π₄ ≫ π₃ ≫ b + a ≫ f, ?_⟩
  rw [add_comp]
  simp only [Category.assoc]
  rw [← hkey]
  abel

theorem fiveLemmaTau2 {S₁ S₂ : CategoryTheory.ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)}
    (φ : CategoryTheory.ShortComplex.Hom S₁ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (N : ℕ)
    (hτ₁ : ∀ i : ℕ, i < N → CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₁ i))
    (hτ₃ : ∀ i : ℕ, i < N → CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₃ i))
    (e₁ : CategoryTheory.Epi (HomologicalComplex.homologyMap φ.τ₁ N))
    (e₃ : CategoryTheory.Epi (HomologicalComplex.homologyMap φ.τ₃ N)) :
    (∀ i : ℕ, i < N → CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₂ i)) ∧
      CategoryTheory.Epi (HomologicalComplex.homologyMap φ.τ₂ N) := by
  -- epimorphisms in the first and third column, in all degrees `n ≤ N`
  have hepi₁ : ∀ n : ℕ, n ≤ N → Epi (HomologicalComplex.homologyMap φ.τ₁ n) := by
    intro n hn
    rcases lt_or_eq_of_le hn with h | h
    · haveI := hτ₁ n h; exact IsIso.epi_of_iso _
    · rw [h]; exact e₁
  have hepi₃ : ∀ n : ℕ, n ≤ N → Epi (HomologicalComplex.homologyMap φ.τ₃ n) := by
    intro n hn
    rcases lt_or_eq_of_le hn with h | h
    · haveI := hτ₃ n h; exact IsIso.epi_of_iso _
    · rw [h]; exact e₃
  -- monomorphisms in the first and third column, in all degrees `n < N`
  have hmono₁ : ∀ n : ℕ, n < N → Mono (HomologicalComplex.homologyMap φ.τ₁ n) := by
    intro n hn
    haveI := hτ₁ n hn; exact IsIso.mono_of_iso _
  have hmono₃ : ∀ n : ℕ, n < N → Mono (HomologicalComplex.homologyMap φ.τ₃ n) := by
    intro n hn
    haveI := hτ₃ n hn; exact IsIso.mono_of_iso _
  -- the degree `0` case, where the five-term sequence degenerates to a three-term sequence
  have hepiτ₂0 : Epi (HomologicalComplex.homologyMap φ.τ₂ 0) := by
    have hg : Epi (HomologicalComplex.homologyMap S₁.g 0) := by
      haveI : Epi S₁.g := h₁.epi_g
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S₁.g 0
        (fun j hj => by simp [ComplexShape.down] at hj)
    exact epi_of_epi_of_exact_of_epi (f := HomologicalComplex.homologyMap S₁.f 0)
      (h₂.homology_exact₂ 0)
      (hepi₁ 0 (Nat.zero_le N)) (hepi₃ 0 (Nat.zero_le N)) hg
      (by simp only [← HomologicalComplex.homologyMap_comp, φ.comm₁₂])
      (by simp only [← HomologicalComplex.homologyMap_comp, φ.comm₂₃])
  constructor
  · intro i hi
    -- `homologyMap φ.τ₂ i` is an epimorphism: the second four lemma on degrees `i, i-1`
    haveI : Epi (HomologicalComplex.homologyMap φ.τ₂ i) := by
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · rw [h0]; exact hepiτ₂0
      · have hrel : (ComplexShape.down ℕ).Rel i (i-1) := by
          show (i-1)+1 = i
          omega
        exact CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono'' (n := 5) (k := 0) (by norm_num)
          (HomologicalComplex.HomologySequence.composableArrows₅_exact h₁ i (i-1) hrel)
          (HomologicalComplex.HomologySequence.composableArrows₅_exact h₂ i (i-1) hrel)
          (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ h₁ h₂ i (i-1) hrel)
          0 1 2 3 rfl rfl rfl rfl (hepi₁ i (le_of_lt hi)) (hepi₃ i (le_of_lt hi))
          (hmono₁ (i-1) (by omega))
    -- `homologyMap φ.τ₂ i` is a monomorphism: the first four lemma on degrees `i+1, i`
    haveI : Mono (HomologicalComplex.homologyMap φ.τ₂ i) :=
      CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono'' (n := 5) (k := 2) (by norm_num)
        (HomologicalComplex.HomologySequence.composableArrows₅_exact h₁ (i+1) i rfl)
        (HomologicalComplex.HomologySequence.composableArrows₅_exact h₂ (i+1) i rfl)
        (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ h₁ h₂ (i+1) i rfl)
        2 3 4 5 rfl rfl rfl rfl (hepi₃ (i+1) (Nat.succ_le_of_lt hi))
        (hmono₁ i hi) (hmono₃ i hi)
    exact isIso_of_mono_of_epi _
  · -- the epimorphism in degree `N`
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]; exact hepiτ₂0
    · have hrel : (ComplexShape.down ℕ).Rel N (N-1) := by
        show (N-1)+1 = N
        omega
      exact CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono'' (n := 5) (k := 0) (by norm_num)
        (HomologicalComplex.HomologySequence.composableArrows₅_exact h₁ N (N-1) hrel)
        (HomologicalComplex.HomologySequence.composableArrows₅_exact h₂ N (N-1) hrel)
        (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ h₁ h₂ N (N-1) hrel)
        0 1 2 3 rfl rfl rfl rfl e₁ e₃ (hmono₁ (N-1) (by omega))

end Work.Serre.RatTower
