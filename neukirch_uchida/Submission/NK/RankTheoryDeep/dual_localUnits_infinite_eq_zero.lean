import Mathlib
import Submission.NK.RankTheoryDeep.IdeleRankDefs

/-!
# Vanishing of the ℓ-adic characters of the local units at an archimedean place

At an *infinite* place `w` of a number field `K` the group of local units is everything
(`NK.GlobalCFT.Place.localUnits_ofInfinite`), so the group whose continuous dual
`NK.Reconstruct.Dual = Hom_cts(-, ℤ_ℓ)` is being computed here is the unit group
`K_wˣ = ℝˣ` (if `w` is real) or `ℂˣ` (if `w` is complex).

**Both `ℝˣ` and `ℂˣ` have no non-trivial `ℤ_ℓ`-valued additive characters at all** (continuity is
irrelevant), because every element of `ℝˣ` (and of `ℂˣ`) has an `ℓ^N`-th root up to a uniquely
2-divisible defect: for every `g` and every `N` there is `y` with `y ^ ℓ^N = g ^ 2`.  Hence
`2 • χ g = ℓ^N • χ y ∈ ⋂_N ℓ^N ℤ_ℓ = 0`, so `2 • χ g = 0` and `χ g = 0` as `ℤ_ℓ` is a domain
of characteristic zero.

This is the archimedean counterpart of
`NK.RankTheoryDeep.dual_localUnits_eq_zero_of_residueChar_ne` (the non-archimedean places with
residual characteristic `≠ ℓ`): both say that such places contribute nothing to the `ℤ_ℓ`-rank of
the character module of the idèle class group (CoNF Ch. X §10.3, (10.3.20)).

## Main results

* `NK.RankTheoryDeep.eq_zero_of_forall_pow_dvd` — an element of `ℤ_ℓ` divisible by `ℓ ^ N` for
  every `N` is zero (the levels `ℤ/ℓ^N` of `ℤ_ℓ` separate its points);
* `NK.RankTheoryDeep.addMonoidHom_eq_zero_of_sq_pow_divisible` — an additive map out of a
  commutative group in which every square is an `ℓ^N`-th power for every `N` is zero;
* `NK.RankTheoryDeep.realUnits_exists_pow_eq_sq`, `…complexUnits_exists_pow_eq_sq` — the root
  existence statements for `ℝˣ` and `ℂˣ`;
* `NK.RankTheoryDeep.dual_localUnits_infinite_eq_zero` — the requested vanishing.
-/

set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace NK.RankTheoryDeep

open NK.GlobalCFT

/-- **An element of `ℤ_ℓ` divisible by every power of `ℓ` is zero.**

The reductions `ℤ_ℓ → ℤ/ℓ^N` separate the points of `ℤ_ℓ`
(`PadicInt.ext_of_toZModPow`), while the `N`-th reduction of `ℓ ^ N` is zero, so the `N`-th
reduction of such an element vanishes for every `N`. -/
theorem eq_zero_of_forall_pow_dvd {ℓ : ℕ} [Fact ℓ.Prime] {y : ℤ_[ℓ]}
    (h : ∀ N : ℕ, ∃ z : ℤ_[ℓ], y = ((ℓ ^ N : ℕ) : ℤ_[ℓ]) * z) : y = 0 := by
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  obtain ⟨z, hz⟩ := h n
  rw [hz, map_mul, map_natCast, map_zero, ZMod.natCast_self, zero_mul]

/-- **The vanishing engine for `ℤ_ℓ`-valued characters of a group in which every square has
`ℓ`-power roots.**

Let `G` be a commutative group such that every square `g ^ 2` is an `ℓ ^ N`-th power, for every
`N ≥ 0`.  Then every additive homomorphism `Additive G →+ ℤ_ℓ` is zero: `2 • f g = f (g ^ 2)` is
divisible by `ℓ ^ N` for every `N`, hence is `0` by `eq_zero_of_forall_pow_dvd`, and `ℤ_ℓ` has no
`2`-torsion. -/
theorem addMonoidHom_eq_zero_of_sq_pow_divisible {ℓ : ℕ} [Fact ℓ.Prime] {G : Type*} [CommGroup G]
    (f : Additive G →+ ℤ_[ℓ])
    (h : ∀ (g : G) (N : ℕ), ∃ y : G, y ^ (ℓ ^ N) = g ^ 2) : f = 0 := by
  refine AddMonoidHom.ext fun a => ?_
  -- For every `a` the value `2 • f a` lies in `⋂_N ℓ^N ℤ_ℓ`.
  have h2 : ∀ N : ℕ, ∃ z : ℤ_[ℓ],
      (2 : ℕ) • f (Additive.ofMul (Additive.toMul a))
        = ((ℓ ^ N : ℕ) : ℤ_[ℓ]) * z := by
    intro N
    obtain ⟨y, hy⟩ := h (Additive.toMul a) N
    refine ⟨f (Additive.ofMul y), ?_⟩
    rw [← map_nsmul, ← ofMul_pow, ← hy, ofMul_pow, map_nsmul, nsmul_eq_mul]
  have hz : (2 : ℕ) • f (Additive.ofMul (Additive.toMul a)) = 0 :=
    eq_zero_of_forall_pow_dvd h2
  rw [nsmul_eq_mul] at hz
  rcases mul_eq_zero.mp hz with h' | h'
  · exact absurd h' (by norm_num)
  · simpa using h'

/-- **Every square in `ℂˣ` is an `ℓ ^ N`-th power.**  Indeed `ℂ` is algebraically closed, so every
element has an `n`-th root for every `n > 0`, and a non-zero element has non-zero roots. -/
theorem complexUnits_exists_pow_eq_sq {ℓ : ℕ} [Fact ℓ.Prime] (g : ℂˣ) (N : ℕ) :
    ∃ y : ℂˣ, y ^ (ℓ ^ N) = g ^ 2 := by
  have hN : 0 < ℓ ^ N := pow_pos (Fact.out : ℓ.Prime).pos N
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℂ) ^ 2) hN
  have hg2 : (g : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Units.ne_zero g)
  have hz0 : z ≠ 0 := fun h => hg2 (by rw [← hz, h, zero_pow hN.ne'])
  refine ⟨Units.mk0 z hz0, ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_pow_eq_pow_val]
  exact hz

/-- **Every square in `ℝˣ` is an `ℓ ^ N`-th power.**  A square is a positive real, and a positive
real `a` has the `ℓ ^ N`-th root `a ^ (1 / ℓ^N)`, which is again positive (hence a unit). -/
theorem realUnits_exists_pow_eq_sq {ℓ : ℕ} [Fact ℓ.Prime] (g : ℝˣ) (N : ℕ) :
    ∃ y : ℝˣ, y ^ (ℓ ^ N) = g ^ 2 := by
  set a : ℝ := (g : ℝ) ^ 2 with ha
  have hapos : 0 < a := by rw [ha]; exact sq_pos_of_ne_zero (Units.ne_zero g)
  have hNpos : ((ℓ ^ N : ℕ) : ℝ) ≠ 0 := by
    have : (ℓ ^ N : ℕ) ≠ 0 := pow_ne_zero N (Fact.out : ℓ.Prime).ne_zero
    exact_mod_cast this
  have hmain : (a ^ ((1:ℝ) / ((ℓ ^ N : ℕ) : ℝ))) ^ (ℓ ^ N) = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hapos), div_mul_cancel₀ _ hNpos,
      Real.rpow_one]
  refine ⟨Units.mk0 (a ^ ((1:ℝ)/((ℓ^N:ℕ):ℝ))) (ne_of_gt (Real.rpow_pos_of_pos hapos _)), ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_pow_eq_pow_val]
  exact hmain.trans ha.symm

/-- **Every additive homomorphism out of the units of an archimedean completion of a number field
is zero.**

The completion `K_w = NK.GlobalCFT.Place.localField K (ofInfinite w)` is `ℝ` at a real place
(`NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal`) and `ℂ` at a complex one
(`…ringEquivComplexOfIsComplex`); in either case the engine
`addMonoidHom_eq_zero_of_sq_pow_divisible` applies, transported along the induced isomorphism of
unit groups. -/
theorem addMonoidHom_units_localField_ofInfinite_eq_zero (K : Type u) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) {ℓ : ℕ} [Fact ℓ.Prime]
    (f : Additive ((NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ)
      →+ ℤ_[ℓ]) : f = 0 := by
  rcases NumberField.InfinitePlace.isReal_or_isComplex w with hw | hw
  · -- real place: `K_w = ℝ`
    let e : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w)) ≃+* ℝ :=
      NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
    let eU : ((NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ) ≃* ℝˣ :=
      Units.mapEquiv e.toMulEquiv
    have hf : f.comp (MulEquiv.toAdditive eU.symm).toAddMonoidHom = 0 :=
      addMonoidHom_eq_zero_of_sq_pow_divisible _ (fun g N => realUnits_exists_pow_eq_sq g N)
    refine AddMonoidHom.ext fun a => ?_
    have h := congrArg
      (fun (φ : Additive ℝˣ →+ ℤ_[ℓ]) => φ (Additive.ofMul (eU (Additive.toMul a)))) hf
    simpa using h
  · -- complex place: `K_w = ℂ`
    let e : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w)) ≃+* ℂ :=
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    let eU : ((NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ) ≃* ℂˣ :=
      Units.mapEquiv e.toMulEquiv
    have hf : f.comp (MulEquiv.toAdditive eU.symm).toAddMonoidHom = 0 :=
      addMonoidHom_eq_zero_of_sq_pow_divisible _ (fun g N => complexUnits_exists_pow_eq_sq g N)
    refine AddMonoidHom.ext fun a => ?_
    have h := congrArg
      (fun (φ : Additive ℂˣ →+ ℤ_[ℓ]) => φ (Additive.ofMul (eU (Additive.toMul a)))) hf
    simpa using h

/-- **Every continuous character of the local units at an archimedean place is trivial.**

The local units at an infinite place are *all* units of the local field
(`NK.GlobalCFT.Place.localUnits_ofInfinite`), so this is the vanishing of
`Hom_cts(K_wˣ, ℤ_ℓ)` for `K_w = ℝ` or `ℂ`; since actually *every* (not merely continuous)
additive homomorphism `K_wˣ → ℤ_ℓ` vanishes
(`addMonoidHom_units_localField_ofInfinite_eq_zero`), the continuity hypothesis is immaterial.

This is the archimedean half of "the places away from `ℓ` contribute nothing to the `ℤ_ℓ`-rank of
`Hom_cts(C_K, ℤ_ℓ)`", the local input of CoNF (10.3.20). -/
theorem dual_localUnits_infinite_eq_zero (K : Type u) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) {ℓ : ℕ} [Fact ℓ.Prime]
    (χ : NK.Reconstruct.Dual
      (↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofInfinite w))) ℓ) :
    χ = 0 := by
  -- Transport along `↥(⊤ : Subgroup K_wˣ) ≃* K_wˣ` (`localUnits` is `⊤` at an infinite place):
  -- the dual of this surjection is injective.
  let G := ((NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ)
  let φ : G →* ↥(⊤ : Subgroup G) := (Subgroup.topEquiv (G := G)).symm
  have hcont : Continuous ⇑φ := continuous_id.subtype_mk _
  have hχ : NK.Reconstruct.dualMap ℓ φ hcont χ = 0 := by
    refine Subtype.ext ?_
    exact addMonoidHom_units_localField_ofInfinite_eq_zero K w _
  have hinj := NK.Reconstruct.dualMap_injective_of_surjective ℓ φ hcont (MulEquiv.surjective _)
  refine hinj ?_
  rw [hχ]
  symm
  refine Subtype.ext ?_
  ext x
  rfl

end NK.RankTheoryDeep
