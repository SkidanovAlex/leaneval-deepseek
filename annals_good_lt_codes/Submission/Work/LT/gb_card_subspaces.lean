import Mathlib

/-!
# The number of `j`-dimensional subspaces of a finite `𝔽₂`-vector space

`Work.LT.gb_card_subspaces` computes the Gaussian binomial coefficient at `q = 2` implicitly:
for a finite `𝔽₂`-vector space `V` and `j ≤ finrank V`,

`#{W ≤ V | finrank W = j} * ∏_{i<j} (2^j - 2^i) = ∏_{i<j} (2^{finrank V} - 2^i)`.

The proof is the classical double count of injective linear maps `𝔽₂^j → V`:

* such a map is the same thing as a linearly independent `j`-tuple in `V`
  (`card_li_eq_card_inj`), whose number is `∏_{i<j} (2^{finrank V} - 2^i)` by the
  Mathlib theorem `card_linearIndependent`;
* splitting an injective map according to its image gives a bijection with pairs
  `(W, e)` of a `j`-dimensional subspace `W` and a linear isomorphism `𝔽₂^j ≃ₗ W`
  (`gb_card_inj_eq_sigma`); the fibres are principal homogeneous spaces for the
  automorphism group of `𝔽₂^j`, so this product has cardinality
  `#{W | finrank W = j} * |GL_j(𝔽₂)|` (`gb_card_sigma_subspace`);
* `|GL_j(𝔽₂)| = ∏_{i<j} (2^j - 2^i)` by `Matrix.card_GL_field`
  (`card_selfLinearEquiv`).
-/

open scoped Classical

set_option linter.style.haveILetI false

namespace Work.LT

/-- A linearly independent `j`-tuple in `V` is exactly an injective linear map `𝔽^j → V`
(under the canonical identification `(Fin j → 𝔽) ≃ₗ ((Fin j → 𝔽) →ₗ[𝔽] V)`). -/
theorem card_li_eq_card_inj {𝔽 V : Type*} [Field 𝔽] [AddCommGroup V] [Module 𝔽 V] (j : ℕ) :
    Nat.card {s : Fin j → V // LinearIndependent 𝔽 s} =
      Nat.card {g : (Fin j → 𝔽) →ₗ[𝔽] V // Function.Injective g} := by
  refine Nat.card_congr ((Module.piEquiv (Fin j) 𝔽 V).toEquiv.subtypeEquiv ?_)
  intro s
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  have : ⇑((Module.piEquiv (Fin j) 𝔽 V).toEquiv s) = ⇑(Fintype.linearCombination 𝔽 s) := by
    ext w
    simp [Module.piEquiv_apply_apply, Fintype.linearCombination_apply]
  rw [this]

/-- The number of linearly independent `j`-tuples in a finite `𝔽₂`-vector space `V`. -/
theorem card_li_finrank {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (j : ℕ)
    (hj : j ≤ Module.finrank (ZMod 2) V) :
    Nat.card {s : Fin j → V // LinearIndependent (ZMod 2) s} =
      ∏ i : Fin j, ((2:ℕ)^Module.finrank (ZMod 2) V - 2^(i:ℕ)) := by
  rw [card_linearIndependent (K := ZMod 2) (V := V) hj]
  simp [ZMod.card]

/-- `|GL_j(𝔽₂)|`, presented as the number of linear automorphisms of `𝔽₂^j`, is
`∏_{i<j} (2^j - 2^i)`. -/
theorem card_selfLinearEquiv (j : ℕ) :
    Nat.card ((Fin j → ZMod 2) ≃ₗ[ZMod 2] (Fin j → ZMod 2)) =
      ∏ i : Fin j, ((2:ℕ)^j - 2^(i:ℕ)) := by
  calc Nat.card ((Fin j → ZMod 2) ≃ₗ[ZMod 2] (Fin j → ZMod 2))
      = Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) (Fin j → ZMod 2)) :=
        (Nat.card_congr
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin j → ZMod 2)).toEquiv).symm
    _ = Nat.card (Matrix.GeneralLinearGroup (Fin j) (ZMod 2)) :=
        (Nat.card_congr
          (Matrix.GeneralLinearGroup.toLin (R := ZMod 2) (n := Fin j)).toEquiv).symm
    _ = ∏ i : Fin j, ((2:ℕ)^j - 2^(i:ℕ)) := by
        rw [Matrix.card_GL_field (𝔽 := ZMod 2) j]
        simp [ZMod.card]

/-- An injective linear map `𝔽^j → V`, i.e. an isomorphism onto its image. -/
noncomputable def gbPhi {𝔽 V : Type*} [Field 𝔽] [AddCommGroup V] [Module 𝔽 V] (j : ℕ) :
    {g : (Fin j → 𝔽) →ₗ[𝔽] V // Function.Injective g} →
      Σ (W : {W : Submodule 𝔽 V // Module.finrank 𝔽 W = j}), ((Fin j → 𝔽) ≃ₗ[𝔽] W.1) :=
  fun g => ⟨⟨g.1.range, by
              rw [LinearMap.finrank_range_of_inj g.2, Module.finrank_fintype_fun_eq_card 𝔽,
                Fintype.card_fin]⟩,
            LinearEquiv.ofInjective g.1 g.2⟩

/-- The inverse of `gbPhi`: a pair `(W, e)` is sent to the injective map `W.subtype ∘ e`. -/
noncomputable def gbPsi {𝔽 V : Type*} [Field 𝔽] [AddCommGroup V] [Module 𝔽 V] (j : ℕ) :
    (Σ (W : {W : Submodule 𝔽 V // Module.finrank 𝔽 W = j}), ((Fin j → 𝔽) ≃ₗ[𝔽] W.1)) →
      {g : (Fin j → 𝔽) →ₗ[𝔽] V // Function.Injective g} :=
  fun p => ⟨p.1.1.subtype.comp p.2.toLinearMap,
            fun _ _ hab => p.2.injective (Subtype.coe_injective hab)⟩

theorem gbPsi_gbPhi {𝔽 V : Type*} [Field 𝔽] [AddCommGroup V] [Module 𝔽 V] (j : ℕ)
    (g : {g : (Fin j → 𝔽) →ₗ[𝔽] V // Function.Injective g}) :
    gbPsi j (gbPhi j g) = g := by
  apply Subtype.ext
  rw [LinearMap.ext_iff]
  intro a
  rfl

theorem gbPsi_injective {𝔽 V : Type*} [Field 𝔽] [AddCommGroup V] [Module 𝔽 V] (j : ℕ) :
    Function.Injective (gbPsi (𝔽 := 𝔽) (V := V) j) := by
  intro p q h
  obtain ⟨⟨W1, h1⟩, e1⟩ := p
  obtain ⟨⟨W2, h2⟩, e2⟩ := q
  have hmap : W1.subtype.comp e1.toLinearMap = W2.subtype.comp e2.toLinearMap :=
    congrArg Subtype.val h
  have hW : W1 = W2 := by
    have hr := congrArg LinearMap.range hmap
    rwa [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, LinearEquiv.range,
      Submodule.map_top, Submodule.map_top, Submodule.range_subtype, Submodule.range_subtype] at hr
  subst hW
  refine Sigma.ext (Subtype.ext rfl) (heq_of_eq ?_)
  apply LinearEquiv.ext
  intro a
  apply Subtype.ext
  exact congrArg (fun f : (Fin j → 𝔽) →ₗ[𝔽] V => f a) hmap

/-- Injective linear maps `𝔽^j → V` correspond bijectively to pairs of a `j`-dimensional
subspace `W ≤ V` together with a linear isomorphism `𝔽^j ≃ₗ W`. -/
theorem gb_card_inj_eq_sigma {𝔽 V : Type*} [Field 𝔽] [AddCommGroup V] [Module 𝔽 V] (j : ℕ) :
    Nat.card {g : (Fin j → 𝔽) →ₗ[𝔽] V // Function.Injective g} =
      Nat.card (Σ (W : {W : Submodule 𝔽 V // Module.finrank 𝔽 W = j}),
        ((Fin j → 𝔽) ≃ₗ[𝔽] W.1)) := by
  have hinj := gbPsi_injective (𝔽 := 𝔽) (V := V) j
  exact Nat.card_congr
    { toFun := gbPhi j
      invFun := gbPsi j
      left_inv := gbPsi_gbPhi j
      right_inv := fun p => hinj (gbPsi_gbPhi j (gbPsi j p)) }

/-- The pairs `(W, e)` with `W` a `j`-dimensional subspace and `e : 𝔽^j ≃ₗ W` number
`#{W | finrank W = j} · |GL_j(𝔽)|`. -/
theorem gb_card_sigma_subspace {𝔽 V : Type*} [Field 𝔽] [Fintype 𝔽] [AddCommGroup V] [Module 𝔽 V]
    [Finite V] (j : ℕ) :
    Nat.card (Σ (W : {W : Submodule 𝔽 V // Module.finrank 𝔽 W = j}),
        ((Fin j → 𝔽) ≃ₗ[𝔽] W.1)) =
      Nat.card {W : Submodule 𝔽 V // Module.finrank 𝔽 W = j} *
        Nat.card ((Fin j → 𝔽) ≃ₗ[𝔽] (Fin j → 𝔽)) := by
  haveI : Fintype {W : Submodule 𝔽 V // Module.finrank 𝔽 W = j} := Fintype.ofFinite _
  haveI : ∀ a : {W : Submodule 𝔽 V // Module.finrank 𝔽 W = j},
      Finite ((Fin j → 𝔽) ≃ₗ[𝔽] a.1) :=
    fun a => Finite.of_injective
      (fun (e : (Fin j → 𝔽) ≃ₗ[𝔽] a.1) => (e : (Fin j → 𝔽) → a.1))
      (fun e f h => LinearEquiv.ext (fun x => congrFun h x))
  have hconst : ∀ W : {W : Submodule 𝔽 V // Module.finrank 𝔽 W = j},
      Nat.card ((Fin j → 𝔽) ≃ₗ[𝔽] W.1) =
        Nat.card ((Fin j → 𝔽) ≃ₗ[𝔽] (Fin j → 𝔽)) := by
    intro W
    have hfr : Module.finrank 𝔽 (Fin j → 𝔽) = Module.finrank 𝔽 W.1 := by
      rw [Module.finrank_fintype_fun_eq_card 𝔽, Fintype.card_fin]; exact W.2.symm
    let eW : (Fin j → 𝔽) ≃ₗ[𝔽] W.1 := LinearEquiv.ofFinrankEq (Fin j → 𝔽) W.1 hfr
    refine Nat.card_congr ?_
    exact { toFun := fun e : (Fin j → 𝔽) ≃ₗ[𝔽] W.1 => e.trans eW.symm
            invFun := fun M : (Fin j → 𝔽) ≃ₗ[𝔽] (Fin j → 𝔽) => M.trans eW
            left_inv := by intro e; ext a; simp
            right_inv := by intro M; ext a; simp }
  rw [Nat.card_sigma]
  rw [Finset.sum_congr rfl (fun W _ => hconst W)]
  rw [Finset.sum_const, Finset.card_univ]
  simp [smul_eq_mul]

/-- **The Gaussian binomial coefficient at `q = 2`.** If `V` is a finite `𝔽₂`-vector space and
`j ≤ finrank V`, then the number of `j`-dimensional subspaces of `V`, multiplied by
`∏_{i<j} (2^j - 2^i)`, equals `∏_{i<j} (2^{finrank V} - 2^i)`. -/
theorem gb_card_subspaces {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (j : ℕ)
    (hj : j ≤ Module.finrank (ZMod 2) V) :
    Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = j} *
      (∏ i : Fin j, ((2:ℕ)^j - 2^(i:ℕ))) =
      ∏ i : Fin j, ((2:ℕ)^Module.finrank (ZMod 2) V - 2^(i:ℕ)) := by
  rw [← card_selfLinearEquiv j,
      ← gb_card_sigma_subspace (𝔽 := ZMod 2) (V := V) j,
      ← gb_card_inj_eq_sigma (𝔽 := ZMod 2) (V := V) j,
      ← card_li_eq_card_inj (𝔽 := ZMod 2) (V := V) j]
  exact card_li_finrank j hj

end Work.LT
