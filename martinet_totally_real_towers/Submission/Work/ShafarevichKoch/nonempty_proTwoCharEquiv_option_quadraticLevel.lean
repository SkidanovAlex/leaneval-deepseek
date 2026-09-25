import Mathlib
import Submission.Work.ShafarevichKoch.GeneratorRank
import Submission.Work.ShafarevichKoch.isGalois_of_finrank_eq_two

/-!
# `Work.ShafarevichKoch.nonempty_proTwoCharEquiv_option_quadraticLevel`

**The continuous characters `G_∅ → 𝔽₂` are the quadratic levels, plus the trivial character.**

This is the bridge of infinite Galois theory advertised in the docstring of
`Work.ShafarevichKoch.GeneratorRank`, namely

```
#ProTwoChar F M = #(QuadraticLevel F M) + 1,
```

realised as a *bijection*

```
ProTwoChar F M ≃ Option (QuadraticLevel F M)
```

between the continuous homomorphisms `G_∅ = Gal(F_∅/F) → Multiplicative (ZMod 2)` and the
unramified quadratic levels `F_∅/L/F` (`L : IntermediateField F M.K` with `[L : F] = 2`), the
empty option corresponding to the trivial character.

Both directions are elementary once the fundamental theorem of infinite Galois theory is in place:

* a **continuous** character `χ` has a closed (indeed open, since the target is discrete) kernel
  `ker χ`, and if `χ ≠ 1` then `χ` is surjective onto the two-element group `𝔽₂ = Multiplicative (ZMod 2)`,
  so `ker χ` has index `2`.  Its fixed field `L = M.K^{ker χ}` has
  `[L : F] = L.fixingSubgroup.index = (ker χ).index = 2`, by
  `IntermediateField.finrank_eq_fixingSubgroup_index`;

* conversely, a level `L` with `[L : F] = 2` is Galois over `F` in characteristic zero
  (`Work.ShafarevichKoch.isGalois_of_finrank_eq_two`), so `H = Gal(M.K/L)` is an *open normal*
  subgroup of `G_∅` of index `2`; the quotient `G_∅ ⧸ H` is then a discrete two-element group,
  and any isomorphism `G_∅ ⧸ H ≃* Multiplicative (ZMod 2)` (obtained from
  `MulEquiv.mulEquivOfCyclicCardEq`) pulls back to a continuous character with kernel `H`.

A homomorphism into a group of cardinality `2` is determined by its kernel (the target has exactly
one nonidentity element), which makes the two constructions mutually inverse.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open Work.ClassFieldTower

noncomputable section

namespace Work.ShafarevichKoch

/-! ## 1. Group-theoretic preliminaries -/

/-- A group of cardinality `2` is cyclic (its cardinality is a prime). -/
lemma isCyclic_of_card_two (A : Type*) [Group A] (h : Nat.card A = 2) : IsCyclic A :=
  isCyclic_of_prime_card (p := 2) h

/-- A group of cardinality `2` is isomorphic to `Multiplicative (ZMod 2)`. -/
noncomputable def mulEquiv_zmodTwo_of_card_two (A : Type*) [Group A] (h : Nat.card A = 2) :
    A ≃* Multiplicative (ZMod 2) := by
  haveI := isCyclic_of_card_two A h
  exact mulEquivOfCyclicCardEq (by rw [h]; simp)

/-- In a group of cardinality `2`, every element is either `1` or any prescribed nonidentity
element. -/
lemma forall_eq_one_or_eq_of_card_two {A : Type*} [Group A] (hA : Nat.card A = 2) {a : A} (ha : a ≠ 1) :
    ∀ b : A, b = 1 ∨ b = a := by
  obtain ⟨b, hbne, hb⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  intro y
  rcases eq_or_ne y 1 with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [hb y h, hb a ha])

/-- A monoid homomorphism into a group of cardinality `2` is determined by its kernel: the kernel
already decides whether an element is sent to `1`, and the target has only one other element. -/
lemma monoidHom_eq_of_ker_eq_card_two {G : Type*} [Group G] {A : Type*} [Group A] (hA : Nat.card A = 2)
    (f g : G →* A) (h : f.ker = g.ker) : f = g := by
  ext x
  have key : f x = 1 ↔ g x = 1 := by rw [← MonoidHom.mem_ker, h, MonoidHom.mem_ker]
  rcases eq_or_ne (f x) 1 with h1 | h1
  · rw [h1, key.mp h1]
  · have h2 : g x ≠ 1 := fun hh => h1 (key.mpr hh)
    obtain ⟨b, hbne, hb⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
    rw [hb (f x) h1, hb (g x) h2]

variable {F : Type*} [Field F] [NumberField F]

/-! ## 2. Kernels of continuous characters and the Galois correspondence -/

/-- The kernel of a continuous character `G_∅ → 𝔽₂` is closed (the target is T1, so `{1}` is
closed). -/
lemma isClosed_ker_proTwoChar (M : MaximalUnramifiedProP.{0} F 2) (χ : ProTwoChar F M) :
    IsClosed ((χ.1.ker : Subgroup (galoisGroup M)) : Set (galoisGroup M)) := by
  have h1 : IsClosed (χ.1 ⁻¹' ({1} : Set (Multiplicative (ZMod 2)))) :=
    IsClosed.preimage χ.2 isClosed_singleton
  convert h1 using 1
  ext x
  simp [MonoidHom.mem_ker]

/-- The fixed field of the kernel of a continuous character has that kernel as its fixing subgroup
(the fundamental theorem of infinite Galois theory). -/
lemma fixingSubgroup_fixedField_ker (M : MaximalUnramifiedProP.{0} F 2) (χ : ProTwoChar F M) :
    (IntermediateField.fixedField (χ.1.ker)).fixingSubgroup = χ.1.ker := by
  have := InfiniteGalois.fixingSubgroup_fixedField
    (⟨χ.1.ker, isClosed_ker_proTwoChar M χ⟩ : ClosedSubgroup (galoisGroup M))
  simpa using this

/-- **A nontrivial continuous character cuts out a quadratic level.** If `χ ≠ 1` then `χ` is
surjective onto the two-element group `𝔽₂`, so `ker χ` has index `2`, and the fixed field of
`ker χ` has `F`-dimension `2`. -/
lemma finrank_fixedField_ker (M : MaximalUnramifiedProP.{0} F 2) (χ : ProTwoChar F M)
    (h : χ.1 ≠ 1) :
    Module.finrank F (IntermediateField.fixedField (χ.1.ker)) = 2 := by
  have hsurj : Function.Surjective χ.1 := by
    have hex : ∃ x : galoisGroup M, χ.1 x ≠ 1 := by
      by_contra hcon
      exact h (MonoidHom.ext fun x => not_not.mp (not_exists.mp hcon x))
    obtain ⟨x0, hx0⟩ := hex
    have hb : ∀ y : Multiplicative (ZMod 2), y = 1 ∨ y = χ.1 x0 :=
      forall_eq_one_or_eq_of_card_two (A := Multiplicative (ZMod 2)) (by simp) hx0
    intro y
    rcases hb y with h1 | h1
    · exact ⟨1, by rw [h1, map_one]⟩
    · exact ⟨x0, h1.symm⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index M.K (IntermediateField.fixedField (χ.1.ker)),
    fixingSubgroup_fixedField_ker M χ, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
    Subgroup.card_top]
  simp

/-- **Every quadratic level is cut out by a continuous character.** For a level `L` of
`F`-dimension `2`, the subgroup `Gal(M.K/L) = L.fixingSubgroup` is an open normal subgroup of
`G_∅` of index `2`; the quotient `G_∅ ⧸ Gal(M.K/L)` is a discrete two-element group, and pulling
back an isomorphism onto `Multiplicative (ZMod 2)` gives a continuous character with kernel
exactly `Gal(M.K/L)`. -/
lemma exists_proTwoChar_ker_eq (M : MaximalUnramifiedProP.{0} F 2) (L : QuadraticLevel F M) :
    ∃ χ : ProTwoChar F M, χ.1.ker = L.1.fixingSubgroup := by
  set L' : IntermediateField F M.K := L.1 with hL'
  have hL2 : Module.finrank F L' = 2 := L.2
  haveI : FiniteDimensional F ↥L' := Module.finite_of_finrank_pos (by rw [hL2]; norm_num)
  have hgal : IsGalois F ↥L' := isGalois_of_finrank_eq_two F M.K L' hL2
  have hnorm : (L'.fixingSubgroup).Normal := (InfiniteGalois.normal_iff_isGalois L').mpr hgal
  haveI := hnorm
  have hopen : IsOpen ((L'.fixingSubgroup : Subgroup (galoisGroup M)) : Set (galoisGroup M)) :=
    IntermediateField.fixingSubgroup_isOpen L'
  haveI : DiscreteTopology ((galoisGroup M) ⧸ L'.fixingSubgroup) :=
    QuotientGroup.discreteTopology hopen
  have hcard : Nat.card ((galoisGroup M) ⧸ L'.fixingSubgroup) = 2 := by
    rw [← Subgroup.index_eq_card, ← IntermediateField.finrank_eq_fixingSubgroup_index M.K L', hL2]
  let e : ((galoisGroup M) ⧸ L'.fixingSubgroup) ≃* Multiplicative (ZMod 2) :=
    mulEquiv_zmodTwo_of_card_two _ hcard
  let χ₀ : galoisGroup M →* Multiplicative (ZMod 2) :=
    e.toMonoidHom.comp (QuotientGroup.mk' L'.fixingSubgroup)
  have hker : χ₀.ker = L'.fixingSubgroup := by
    ext x
    show e (QuotientGroup.mk' L'.fixingSubgroup x) = 1 ↔ x ∈ L'.fixingSubgroup
    constructor
    · intro hx
      have h1 : QuotientGroup.mk' L'.fixingSubgroup x = 1 := by
        apply e.injective
        rw [hx, map_one]
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' L'.fixingSubgroup] at h1
      exact h1
    · intro hx
      have h1 : QuotientGroup.mk' L'.fixingSubgroup x = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' L'.fixingSubgroup]
        exact hx
      rw [h1, map_one]
  have hcont : Continuous χ₀ := by
    show Continuous fun x : galoisGroup M => e (QuotientGroup.mk' L'.fixingSubgroup x)
    exact continuous_of_discreteTopology.comp QuotientGroup.continuous_mk
  exact ⟨⟨χ₀, hcont⟩, hker⟩

/-! ## 3. The two maps and the equivalence -/

/-- A chosen continuous character with kernel `Gal(M.K/L)`. -/
noncomputable def quadraticLevelChar (M : MaximalUnramifiedProP.{0} F 2) (L : QuadraticLevel F M) :
    ProTwoChar F M :=
  Classical.choose (exists_proTwoChar_ker_eq M L)

/-- The defining property of `quadraticLevelChar`. -/
lemma quadraticLevelChar_ker (M : MaximalUnramifiedProP.{0} F 2) (L : QuadraticLevel F M) :
    (quadraticLevelChar M L).1.ker = L.1.fixingSubgroup :=
  Classical.choose_spec (exists_proTwoChar_ker_eq M L)

/-- The character `χ` is sent to the quadratic level cut out by its kernel, or to `none` if `χ` is
trivial. -/
noncomputable def proTwoCharToOption (M : MaximalUnramifiedProP.{0} F 2) :
    ProTwoChar F M → Option (QuadraticLevel F M) := fun χ =>
  if h : χ.1 = 1 then none
  else some ⟨IntermediateField.fixedField (χ.1.ker), finrank_fixedField_ker M χ h⟩

/-- The level `L` is sent to a continuous character with kernel `Gal(M.K/L)`, and `none` to the
trivial character. -/
noncomputable def optionToProTwoChar (M : MaximalUnramifiedProP.{0} F 2) :
    Option (QuadraticLevel F M) → ProTwoChar F M :=
  fun o => o.elim ⟨1, continuous_const⟩ (quadraticLevelChar M)

/-- `optionToProTwoChar` is a left inverse of `proTwoCharToOption`: a character is recovered from
its kernel. -/
lemma optionToProTwoChar_proTwoCharToOption (M : MaximalUnramifiedProP.{0} F 2)
    (χ : ProTwoChar F M) : optionToProTwoChar M (proTwoCharToOption M χ) = χ := by
  by_cases h : χ.1 = 1
  · have ht : proTwoCharToOption M χ = none := by simp [proTwoCharToOption, h]
    rw [ht]
    apply Subtype.ext
    show (1 : galoisGroup M →* Multiplicative (ZMod 2)) = χ.1
    exact h.symm
  · have ht : proTwoCharToOption M χ =
        some ⟨IntermediateField.fixedField (χ.1.ker), finrank_fixedField_ker M χ h⟩ := by
      simp [proTwoCharToOption, h]
    rw [ht]
    apply Subtype.ext
    show (quadraticLevelChar M
      ⟨IntermediateField.fixedField (χ.1.ker), finrank_fixedField_ker M χ h⟩).1 = χ.1
    apply monoidHom_eq_of_ker_eq_card_two (A := Multiplicative (ZMod 2)) (by simp)
    rw [quadraticLevelChar_ker, fixingSubgroup_fixedField_ker M χ]

/-- `optionToProTwoChar` is a right inverse of `proTwoCharToOption`: the fixed field of the kernel
of the character attached to `L` is `L` itself. -/
lemma proTwoCharToOption_optionToProTwoChar (M : MaximalUnramifiedProP.{0} F 2)
    (o : Option (QuadraticLevel F M)) :
    proTwoCharToOption M (optionToProTwoChar M o) = o := by
  cases o with
  | none => simp [optionToProTwoChar, proTwoCharToOption]
  | some L =>
    have hne : (quadraticLevelChar M L).1 ≠ 1 := by
      intro h1
      have htop : L.1.fixingSubgroup = ⊤ := by
        rw [← quadraticLevelChar_ker M L, h1]
        exact MonoidHom.ker_one
      have hbot : L.1 = ⊥ := by
        rw [← InfiniteGalois.fixedField_fixingSubgroup L.1, htop, InfiniteGalois.fixedField_bot]
      have h1' : Module.finrank F L.1 = 1 := by rw [hbot, IntermediateField.finrank_bot]
      rw [L.2] at h1'
      norm_num at h1'
    show proTwoCharToOption M (quadraticLevelChar M L) = some L
    rw [show proTwoCharToOption M (quadraticLevelChar M L) =
        some ⟨IntermediateField.fixedField ((quadraticLevelChar M L).1.ker),
          finrank_fixedField_ker M _ hne⟩ from by
      simp only [proTwoCharToOption]
      rw [dite_eq_right hne]]
    refine congrArg some (Subtype.ext ?_)
    change IntermediateField.fixedField ((quadraticLevelChar M L).1.ker) = L.1
    rw [quadraticLevelChar_ker, InfiniteGalois.fixedField_fixingSubgroup L.1]

/-! ## 4. The bijection -/

theorem nonempty_proTwoCharEquiv_option_quadraticLevel (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) :
    Nonempty (Work.ShafarevichKoch.ProTwoChar F M ≃
      Option (Work.ShafarevichKoch.QuadraticLevel F M)) := by
  refine ⟨Equiv.ofBijective (proTwoCharToOption M) ⟨?_, ?_⟩⟩
  · intro a b hab
    rw [← optionToProTwoChar_proTwoCharToOption M a, hab,
      optionToProTwoChar_proTwoCharToOption M b]
  · intro b
    exact ⟨optionToProTwoChar M b, proTwoCharToOption_optionToProTwoChar M b⟩

end Work.ShafarevichKoch
