import Mathlib
import Submission.NK.Reconstruct.GammaDual
import Submission.NK.Reconstruct.galToGamma
import Submission.NK.Reconstruct.galToGamma_continuous
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Γ_K^{tf}`: the Hausdorff torsion-free quotient of the ℓ-adic abelianisation

Shimizu (arXiv:2009.10431, §4) works with

  `Γ_K = Γ_{K,ℓ} = G_K^{ab,(ℓ)}/torsion`,

"the ℓ-part of the abelianisation of `G_K` modulo its torsion", and uses throughout that

* `Γ_K` is a **Hausdorff** compact group (so that kernels of continuous homomorphisms are closed
  and Baire-category arguments apply), and
* `Γ_K` is **torsion-free** (so that a continuous non-zero homomorphism out of `Γ_K` cannot have
  open kernel: an open kernel would make its range finite, hence trivial).

The object `NK.Reconstruct.Gamma K K' ℓ` of `GammaObject.lean` is the ℓ-part of `G_K^{ab}` *with*
its torsion; as recorded in the README (§18.5), the naive torsion quotient
`NK.Reconstruct.GammaTF` is **not** Hausdorff in general (`K = ℚ`, `ℓ = 2` exhibits a dense
torsion submodule), so the quotient topology on it carries no usable information.

This file therefore introduces the correct object: the quotient of `Γ_K` by the *intersection of
the kernels of all continuous homomorphisms `Γ_K → ℤ_ℓ`*, realised as a **subgroup of a product of
copies of `ℤ_ℓ`**:

  `GammaHaus K K' ℓ = range (gammaEvalMul : Γ_K → ∏_{f ∈ Hom_cts(Γ_K,ℤ_ℓ)} ℤ_ℓ)`.

As a subgroup of a product of torsion-free groups it is torsion-free; as the image of a compact
group in a Hausdorff space it is compact Hausdorff.  It is the largest quotient of `Γ_K` on which
the continuous dual of `Γ_K` is faithful — equivalently, it is `Γ_K` modulo the subgroup of
elements invisible to every continuous homomorphism into `ℤ_ℓ` — so it has the same continuous dual
as `Γ_K`.  This is exactly the object needed in Shimizu's Proposition 4f.3, and it is the
topological model of `G_K^{ab,(ℓ),/tor}`.

## Main definitions and results

* `gammaEvalMul`, `GammaHaus`, `gammaHausMk`;
* `gammaHausMk_continuous`, `gammaHausMk_surjective`;
* `gammaHausMk_eq_one_iff` — the kernel of the quotient map is the intersection of the kernels of
  the continuous dual;
* `gammaHaus_pow_eq_one` — `Γ_K^{tf}` is torsion-free;
* `gammaHausLift` — **descent**: a continuous homomorphism `Γ_L → Γ_M` that kills the invisible
  part of `Γ_L` induces a homomorphism `Γ_L^{tf} → Γ_M^{tf}`, computed componentwise
  (`gammaHausLift_apply_coe`), with `gammaHausLift_comp`;
* `not_isOpen_ker_gammaHaus` — a non-zero continuous homomorphism out of `Γ_K^{tf}` with
  torsion-free target has non-open kernel, hence (with `isClosed_ker_of_continuous`) the Baire step
  of Proposition 4f.3 applies.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4;
J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3, Ch. XII.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

open scoped Pointwise

variable {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K']

/-! ## The evaluation map and the object `Γ_K^{tf}` -/

/-- **The evaluation of `Γ_K` into the product of `ℤ_ℓ` over its continuous dual.**  Its kernel is
the subgroup of `Γ_K` which is invisible to every continuous homomorphism into `ℤ_ℓ`. -/
noncomputable def gammaEvalMul (K : Type*) [Field K] (K' : Type*) [Field K'] [Algebra K K']
    [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] :
    Gamma K K' ℓ →* ((f : Dual (Gamma K K' ℓ) ℓ) → Multiplicative (PadicInt ℓ)) where
  toFun x := fun f => Multiplicative.ofAdd (f (Additive.ofMul x))
  map_one' := by
    funext f
    simp
  map_mul' := by
    intro x y
    funext f
    exact map_add f.1 (Additive.ofMul x) (Additive.ofMul y)

section Lemmas

variable {ℓ : ℕ} [Fact ℓ.Prime]

@[simp] theorem gammaEvalMul_apply (x : Gamma K K' ℓ) (f : Dual (Gamma K K' ℓ) ℓ) :
    (gammaEvalMul K K' ℓ x f : PadicInt ℓ) = f (Additive.ofMul x) := rfl

/-- **`Γ_K^{tf}`, the Hausdorff torsion-free quotient of `Γ_K`**: the image of `Γ_K` under the
evaluation into the product of `ℤ_ℓ` over its continuous dual.  This is Shimizu's
`Γ_K = G_K^{ab,(ℓ)}/torsion` as a *topological* group: a compact Hausdorff torsion-free pro-ℓ group
with the same continuous dual as `Γ_K`. -/
noncomputable abbrev GammaHaus (K : Type*) [Field K] (K' : Type*) [Field K'] [Algebra K K']
    [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Type _ :=
  ↥((gammaEvalMul K K' ℓ).range)

/-- The canonical projection `Γ_K ↠ Γ_K^{tf}`. -/
noncomputable def gammaHausMk (K : Type*) [Field K] (K' : Type*) [Field K'] [Algebra K K']
    [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Gamma K K' ℓ →* GammaHaus K K' ℓ :=
  (gammaEvalMul K K' ℓ).codRestrict _ fun x => Set.mem_range_self x

@[simp] theorem gammaHausMk_apply (x : Gamma K K' ℓ) :
    (gammaHausMk K K' ℓ x : (f : Dual (Gamma K K' ℓ) ℓ) → Multiplicative (PadicInt ℓ))
      = gammaEvalMul K K' ℓ x := rfl

theorem gammaHausMk_surjective :
    Function.Surjective (gammaHausMk K K' ℓ) := by
  rintro ⟨y, ⟨x, rfl⟩⟩
  exact ⟨x, rfl⟩

/-- **The kernel of the quotient map is the invisible subgroup of `Γ_K`**: an element of `Γ_K`
becomes trivial in `Γ_K^{tf}` exactly when every continuous homomorphism `Γ_K → ℤ_ℓ` kills it. -/
theorem gammaHausMk_eq_one_iff (x : Gamma K K' ℓ) :
    gammaHausMk K K' ℓ x = 1 ↔ ∀ f : Dual (Gamma K K' ℓ) ℓ, f (Additive.ofMul x) = 0 := by
  constructor
  · intro h f
    have h2 : gammaEvalMul K K' ℓ x f = 1 := by
      have h3 := congrArg (fun z : GammaHaus K K' ℓ => z.1 f) h
      simpa using h3
    rw [gammaEvalMul_apply] at h2
    exact h2
  · intro h
    refine Subtype.ext (funext fun f => ?_)
    rw [gammaHausMk_apply, gammaEvalMul_apply, h f]
    rfl

/-- The kernel form of `gammaHausMk_eq_one_iff`: a member of the invisible subgroup is killed by
the whole continuous dual. -/
theorem gammaHausMk_eq_one_of_forall_dual_eq_zero (x : Gamma K K' ℓ)
    (h : ∀ f : Dual (Gamma K K' ℓ) ℓ, f (Additive.ofMul x) = 0) :
    gammaHausMk K K' ℓ x = 1 :=
  (gammaHausMk_eq_one_iff x).mpr h

/-- **Separation by the dual**: an element of `Γ_K` which is not invisible is detected by some
continuous homomorphism `Γ_K → ℤ_ℓ`.  (This is immediate from the definition of `Γ_K^{tf}`.) -/
theorem exists_dual_ne_zero_of_gammaHausMk_ne_one (x : Gamma K K' ℓ)
    (h : gammaHausMk K K' ℓ x ≠ 1) : ∃ f : Dual (Gamma K K' ℓ) ℓ, f (Additive.ofMul x) ≠ 0 := by
  by_contra hc
  exact h (gammaHausMk_eq_one_of_forall_dual_eq_zero x fun f => by
    by_contra hf
    exact hc ⟨f, hf⟩)

/-! ## Topology -/

theorem continuous_gammaEvalMul :
    Continuous (gammaEvalMul K K' ℓ) := by
  refine continuous_pi fun f => ?_
  exact continuous_ofAdd.comp (f.2.comp continuous_ofMul)

theorem continuous_gammaHausMk : Continuous (gammaHausMk K K' ℓ) :=
  (continuous_gammaEvalMul (K := K) (K' := K') (ℓ := ℓ)).subtype_mk _

/-- `Γ_K^{tf}` is compact (a continuous image of the compact group `Γ_K`). -/
instance gammaHausCompactSpace : CompactSpace (GammaHaus K K' ℓ) :=
  isCompact_iff_compactSpace.mp
    (isCompact_range (continuous_gammaEvalMul (K := K) (K' := K') (ℓ := ℓ)))

/-! ## Torsion-freeness -/

/-- A non-trivial element of `Multiplicative ℤ_ℓ` has infinite order. -/
theorem multiplicative_padicInt_pow_eq_one {y : Multiplicative (PadicInt ℓ)} {n : ℕ}
    (hn : n ≠ 0) (h : y ^ n = 1) : y = 1 := by
  have h1 : n • y.toAdd = 0 := by
    rw [← toAdd_pow, h, toAdd_one]
  rw [nsmul_eq_mul] at h1
  have h2 : y.toAdd = 0 := (mul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr hn)
  simpa using h2

/-- **`Γ_K^{tf}` is torsion-free**: a finite power of an element is trivial only if the element
is. -/
theorem gammaHaus_pow_eq_one {y : GammaHaus K K' ℓ} {n : ℕ} (hn : n ≠ 0) (h : y ^ n = 1) :
    y = 1 := by
  have h1 : y.1 ^ n = 1 := by
    have h2 := congrArg (fun z : GammaHaus K K' ℓ => z.1) h
    simpa using h2
  refine Subtype.ext (funext fun f => ?_)
  exact multiplicative_padicInt_pow_eq_one hn (by simpa using congrFun h1 f)

/-- **A finite subgroup of `Γ_K^{tf}` is trivial.** -/
theorem gammaHaus_finite_eq_bot {H : Subgroup (GammaHaus K K' ℓ)} [Finite H] : H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hcard : Nat.card H ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
  have hdvd : orderOf x ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hx
  exact gammaHaus_pow_eq_one hcard (orderOf_dvd_iff_pow_eq_one.mp hdvd)

/-- **The kernel of a non-zero continuous homomorphism out of `Γ_K^{tf}` is not open**, provided the
target is torsion-free: if the kernel were open, the range would be finite, hence (by
torsion-freeness of the target) trivial. -/
theorem not_isOpen_ker_gammaHaus {N : Type*} [Group N] [TopologicalSpace N]
    (φ : GammaHaus K K' ℓ →* N) (hφ : Continuous φ) (hne : φ ≠ 1)
    (htf : ∀ (y : N) (n : ℕ), n ≠ 0 → y ^ n = 1 → y = 1) :
    ¬ IsOpen ((φ.ker : Subgroup (GammaHaus K K' ℓ)) : Set (GammaHaus K K' ℓ)) := by
  intro hopen
  haveI : DiscreteTopology (GammaHaus K K' ℓ ⧸ φ.ker) := QuotientGroup.discreteTopology hopen
  have hfinQ : Finite (GammaHaus K K' ℓ ⧸ φ.ker) := finite_of_compact_of_discrete
  have hfin : Finite (φ.range) :=
    (QuotientGroup.quotientKerEquivRange φ).finite_iff.mp hfinQ
  haveI := hfin
  have hbot : φ.range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hcard : Nat.card (φ.range) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨⟨y, hy⟩⟩, inferInstance⟩
    exact htf y (Nat.card (φ.range)) hcard
      (orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard φ.range hy))
  apply hne
  refine MonoidHom.ext fun x => ?_
  have hx : φ x ∈ φ.range := Set.mem_range_self x
  rw [hbot] at hx
  simpa using hx

/-! ## The descent to `Γ^{tf}` -/

/-- **Descent of a continuous homomorphism to the torsion-free Hausdorff quotients.**

A continuous homomorphism `Φ : Γ_L → Γ_M` kills the invisible part of `Γ_L`: for
`γ ∈ ker (Γ_L ↠ Γ_L^{tf})` and any continuous `g : Γ_M → ℤ_ℓ` the composite `g ∘ Φ` is a continuous
homomorphism `Γ_L → ℤ_ℓ`, i.e. an element of the dual of `Γ_L`, hence kills `γ`.  The descended
homomorphism `Γ_L^{tf} → Γ_M^{tf}` is constructed *componentwise*: the `g`-component of the image
of `y` is the `(g ∘ Φ)`-component of `y`.  This makes the defining identity `gammaHausLift_comp`
immediate. -/
noncomputable def gammaHausLift {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsGalois K₁ K₁'] [IsGalois K₂ K₂']
    (ℓ : ℕ) [Fact ℓ.Prime] (Φ : Gamma K₁ K₁' ℓ →* Gamma K₂ K₂' ℓ) (hΦ : Continuous ⇑Φ) :
    GammaHaus K₁ K₁' ℓ →* GammaHaus K₂ K₂' ℓ where
  toFun y := ⟨fun g => y.1 (dualMap ℓ Φ hΦ g), by
    obtain ⟨x, hx⟩ := y.2
    refine ⟨Φ x, ?_⟩
    rw [← hx]
    funext g
    rw [gammaEvalMul_apply, gammaEvalMul_apply, dualMap_apply]
    exact congrArg (fun z : Additive (Gamma K₂ K₂' ℓ) => g.1 z)
      (show MonoidHom.toAdditive Φ (Additive.ofMul x) = Additive.ofMul (Φ x) from rfl)⟩
  map_one' := Subtype.ext (funext fun g => rfl)
  map_mul' := fun a b => Subtype.ext (funext fun g => rfl)

@[simp] theorem gammaHausLift_apply_coe {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsGalois K₁ K₁'] [IsGalois K₂ K₂']
    (ℓ : ℕ) [Fact ℓ.Prime] (Φ : Gamma K₁ K₁' ℓ →* Gamma K₂ K₂' ℓ) (hΦ : Continuous ⇑Φ)
    (y : GammaHaus K₁ K₁' ℓ) (g : Dual (Gamma K₂ K₂' ℓ) ℓ) :
    ((gammaHausLift ℓ Φ hΦ y :
      (g : Dual (Gamma K₂ K₂' ℓ) ℓ) → Multiplicative (PadicInt ℓ)) g)
      = y.1 (dualMap ℓ Φ hΦ g) := rfl

/-- **The defining identity of the descent**: the descended map commutes with the projections. -/
theorem gammaHausLift_comp {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsGalois K₁ K₁'] [IsGalois K₂ K₂']
    (ℓ : ℕ) [Fact ℓ.Prime] (Φ : Gamma K₁ K₁' ℓ →* Gamma K₂ K₂' ℓ) (hΦ : Continuous ⇑Φ)
    (x : Gamma K₁ K₁' ℓ) :
    gammaHausLift ℓ Φ hΦ (gammaHausMk K₁ K₁' ℓ x) = gammaHausMk K₂ K₂' ℓ (Φ x) := by
  refine Subtype.ext (funext fun g => ?_)
  rw [gammaHausLift_apply_coe, gammaHausMk_apply, gammaHausMk_apply, gammaEvalMul_apply,
    gammaEvalMul_apply, dualMap_apply]
  exact congrArg (fun z : Additive (Gamma K₂ K₂' ℓ) => g.1 z)
    (show MonoidHom.toAdditive Φ (Additive.ofMul x) = Additive.ofMul (Φ x) from rfl)

theorem continuous_gammaHausLift {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsGalois K₁ K₁'] [IsGalois K₂ K₂']
    (ℓ : ℕ) [Fact ℓ.Prime] (Φ : Gamma K₁ K₁' ℓ →* Gamma K₂ K₂' ℓ) (hΦ : Continuous ⇑Φ) :
    Continuous (gammaHausLift ℓ Φ hΦ) := by
  refine Continuous.subtype_mk (continuous_pi fun g => ?_)
    (fun y => (gammaHausLift ℓ Φ hΦ y).2)
  exact (continuous_apply (dualMap ℓ Φ hΦ g)).comp continuous_subtype_val

end Lemmas

end NK.Reconstruct
