import Mathlib
import Submission.NK.Reconstruct.GammaDual
import Submission.NK.RankTheoryDeep.CharModule

/-!
# The continuous dual only sees quotients killed by the `ℤ/ℓⁿ`-characters

Let `G` be a commutative topological group and `R ≤ G` a subgroup which is killed by **every**
continuous additive character into `ZMod (ℓ ^ n)`, for every `n`:

`∀ n (f : Additive G →+ ZMod (ℓ^n)), Continuous f → ∀ r ∈ R, f r = 0`.

Then the continuous dual `NK.Reconstruct.Dual G ℓ = Hom_cts(G, ℤ_ℓ)` is unchanged by passing to
the quotient `G ⧸ R`.

The mathematical content is the following.  The mod-`ℓⁿ` reductions

`toZModPow n : ℤ_ℓ →+* ZMod (ℓ^n)  (n : ℕ)`

are continuous (`continuous_padicInt_toZModPow`: they are constant on the balls of radius
`‖ℓ‖^{-n}`, which are open because `ℤ_ℓ` is ultrametric) and jointly injective on `ℤ_ℓ`
(`PadicInt.ext_of_toZModPow`).  Hence a continuous character `f : Additive G →+ ℤ_ℓ` vanishes on
`R` as soon as all of its reductions `toZModPow n ∘ f` do, and those are exactly the characters
the hypothesis speaks about.  Once `f` kills `R` it descends to `G ⧸ R` (the quotient map is a
quotient map, so the descent of a continuous map is continuous), and conversely every character of
the quotient pulls back along the quotient map.  The two constructions are inverse to each other
and are `ℤ_ℓ`-linear, giving the advertised linear equivalence.

This is the "a quotient is invisible to the ℓ-adic characters that kill it" step used in the
Artin-duality bridge for the idèle class group.
-/

namespace NK.NUV2.ArtinBridge

open NK.Reconstruct

noncomputable section

open scoped Pointwise

namespace DualKillsAux

/-- **The mod-`ℓⁿ` reduction `ℤ_ℓ → ZMod (ℓ^n)` is continuous** (for the `ℓ`-adic topology on
`ℤ_ℓ` and the discrete topology on `ZMod (ℓ^n)`).  It is locally constant: it is constant on the
closed ball of radius `‖ℓ‖^{-n}`, which is open because `ℤ_ℓ` is ultrametric. -/
theorem continuous_padicInt_toZModPow (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Continuous (PadicInt.toZModPow (p := ℓ) n) := by
  rw [continuous_def]
  have hℓ : ℓ.Prime := Fact.out
  have hrn : ((ℓ : ℝ) ^ (-(n : ℤ))) ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.mpr hℓ.ne_zero)
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨Metric.closedBall x ((ℓ : ℝ) ^ (-(n : ℤ))), ?_,
      IsUltrametricDist.isOpen_closedBall x hrn, ?_⟩
  · intro y hy
    have hy' : ‖y - x‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) := by
      rwa [Metric.mem_closedBall, dist_eq_norm] at hy
    have hmem : y - x ∈ Ideal.span {((ℓ : ℤ_[ℓ]) ^ n)} :=
      (PadicInt.norm_le_pow_iff_mem_span_pow (y - x) n).mp hy'
    have hker : PadicInt.toZModPow (p := ℓ) n (y - x) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact hmem
    rw [map_sub, sub_eq_zero] at hker
    show PadicInt.toZModPow (p := ℓ) n y ∈ U
    rw [hker]
    exact hx
  · rw [Metric.mem_closedBall, dist_self]
    positivity

/-- The hypothesis that the subgroup `R` is killed by every continuous character into
`ZMod (ℓ ^ n)`, `n : ℕ`. -/
def KilledBy (G : Type*) [CommGroup G] [TopologicalSpace G] (ℓ : ℕ) (R : Subgroup G) : Prop :=
  ∀ (n : ℕ) (f : Additive G →+ ZMod (ℓ ^ n)), Continuous ⇑f →
    ∀ r : G, r ∈ R → f (Additive.ofMul r) = 0

section General

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable (R : Subgroup G)

/-- **A continuous character `G → ℤ_ℓ` kills `R`.**  Its mod-`ℓⁿ` reductions are continuous
characters into `ZMod (ℓ^n)`, hence vanish on `R` by hypothesis; and the joint kernel of all the
reductions is trivial. -/
theorem vanish (hR : KilledBy G ℓ R) (f : Dual G ℓ) (r : G) (hr : r ∈ R) :
    f.1 (Additive.ofMul r) = 0 := by
  refine (PadicInt.ext_of_toZModPow (p := ℓ) (x := f.1 (Additive.ofMul r))
    (y := 0)).mp ?_
  intro n
  have hcont : Continuous ⇑((PadicInt.toZModPow (p := ℓ) n).toAddMonoidHom.comp f.1) :=
    (continuous_padicInt_toZModPow ℓ n).comp f.2
  have h := hR n ((PadicInt.toZModPow (p := ℓ) n).toAddMonoidHom.comp f.1) hcont r hr
  simpa using h

/-- The additive form of `vanish`: `R` is contained in the kernel of `f`. -/
theorem vanish_ker (hR : KilledBy G ℓ R) (f : Dual G ℓ) : R.toAddSubgroup ≤ f.1.ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  exact vanish R hR f x.toMul hx

/-- The descent of a continuous character to `G ⧸ R` is continuous: the quotient map is a quotient
map and the composite with it is `f`. -/
theorem continuous_lift (hR : KilledBy G ℓ R) (f : Dual G ℓ) :
    Continuous (QuotientAddGroup.lift R.toAddSubgroup f.1 (vanish_ker R hR f)) := by
  have hvk : R.toAddSubgroup ≤ f.1.ker := vanish_ker R hR f
  rw [(QuotientAddGroup.isQuotientMap_mk R.toAddSubgroup).continuous_iff]
  change Continuous (fun x : Additive G =>
    QuotientAddGroup.lift R.toAddSubgroup f.1 hvk x)
  have heq : (fun x : Additive G =>
      QuotientAddGroup.lift R.toAddSubgroup f.1 hvk x) = ⇑f.1 := by
    funext x
    exact QuotientAddGroup.lift_mk' R.toAddSubgroup hvk x
  rw [heq]
  exact f.2

/-- **The forward map**: a continuous character of `G` killing `R` descends to `G ⧸ R`. -/
noncomputable def fwd (hR : KilledBy G ℓ R) (f : Dual G ℓ) : Dual (G ⧸ R) ℓ :=
  ⟨QuotientAddGroup.lift R.toAddSubgroup f.1 (vanish_ker R hR f), continuous_lift R hR f⟩

/-- The defining property of `fwd`, on representatives. -/
theorem fwd_apply_mk (hR : KilledBy G ℓ R) (f : Dual G ℓ) (x : G) :
    (fwd R hR f).1 (Additive.ofMul (QuotientGroup.mk (s := R) x)) = f.1 (Additive.ofMul x) :=
  QuotientAddGroup.lift_mk' R.toAddSubgroup (vanish_ker R hR f) (Additive.ofMul x)

/-- The quotient map is continuous (in the group form needed by `dualMap`). -/
theorem continuous_quotientGroup_mk' : Continuous ⇑(QuotientGroup.mk' R) := by
  rw [QuotientGroup.coe_mk']
  exact QuotientGroup.continuous_mk

/-- **The backward map**: precomposition with the quotient map `G → G ⧸ R`. -/
noncomputable def bwd (_hR : KilledBy G ℓ R) (g : Dual (G ⧸ R) ℓ) : Dual G ℓ :=
  dualMap ℓ (QuotientGroup.mk' R) (continuous_quotientGroup_mk' R) g

/-- `bwd` is a left inverse of `fwd`. -/
theorem bwd_fwd (hR : KilledBy G ℓ R) (f : Dual G ℓ) : bwd R hR (fwd R hR f) = f := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  rw [← ofMul_toMul x]
  exact fwd_apply_mk R hR f x.toMul

/-- `bwd` is injective, being the dual of the surjection `G → G ⧸ R`. -/
theorem bwd_injective (hR : KilledBy G ℓ R) : Function.Injective (bwd R hR) :=
  dualMap_injective_of_surjective ℓ (QuotientGroup.mk' R) (continuous_quotientGroup_mk' R)
    (QuotientGroup.mk'_surjective R)

/-- `bwd` is a right inverse of `fwd`. -/
theorem fwd_bwd (hR : KilledBy G ℓ R) (g : Dual (G ⧸ R) ℓ) : fwd R hR (bwd R hR g) = g :=
  bwd_injective R hR (bwd_fwd R hR (bwd R hR g))

/-- `fwd` is injective. -/
theorem fwd_injective (hR : KilledBy G ℓ R) : Function.Injective (fwd R hR) := fun f g h => by
  rw [← bwd_fwd R hR f, h, bwd_fwd R hR g]

/-- `fwd` is surjective. -/
theorem fwd_surjective (hR : KilledBy G ℓ R) : Function.Surjective (fwd R hR) :=
  fun g => ⟨bwd R hR g, fwd_bwd R hR g⟩

/-- `fwd` is additive. -/
theorem fwd_add (hR : KilledBy G ℓ R) (f g : Dual G ℓ) :
    fwd R hR (f + g) = fwd R hR f + fwd R hR g := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (s := R) x.toMul
  rw [show x = Additive.ofMul (QuotientGroup.mk (s := R) y) from by rw [hy, ofMul_toMul]]
  simp only [AddSubgroup.coe_add, AddMonoidHom.add_apply, fwd_apply_mk R hR]

/-- `fwd` is `ℤ_ℓ`-linear. -/
theorem fwd_smul (hR : KilledBy G ℓ R) (c : PadicInt ℓ) (f : Dual G ℓ) :
    fwd R hR (c • f) = c • fwd R hR f := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (s := R) x.toMul
  rw [show x = Additive.ofMul (QuotientGroup.mk (s := R) y) from by rw [hy, ofMul_toMul]]
  simp only [NK.RankTheoryDeep.smul_dual_apply, fwd_apply_mk R hR]

/-- `fwd` as a `ℤ_ℓ`-linear map. -/
noncomputable def fwdLin (hR : KilledBy G ℓ R) :
    Dual G ℓ →ₗ[PadicInt ℓ] Dual (G ⧸ R) ℓ where
  toFun := fwd R hR
  map_add' := fwd_add R hR
  map_smul' := fwd_smul R hR

/-- **The general form of the statement**: if every continuous `ZMod (ℓ^n)`-valued character kills
`R`, then `Dual G ℓ ≃ₗ[ℤ_ℓ] Dual (G ⧸ R) ℓ`. -/
noncomputable def dualEquiv (hR : KilledBy G ℓ R) :
    Dual G ℓ ≃ₗ[PadicInt ℓ] Dual (G ⧸ R) ℓ :=
  LinearEquiv.ofBijective (fwdLin R hR) ⟨fwd_injective R hR, fwd_surjective R hR⟩

end General

end DualKillsAux

/-- **The dual only sees the quotients killed by the `ℤ/ℓⁿ`-characters.**  If every continuous
additive character `G → ZMod (ℓ^n)` (`n : ℕ`) kills the subgroup `R`, then passing to `G ⧸ R`
does not change the continuous dual `Hom_cts(-, ℤ_ℓ)`. -/
theorem dualEquivOfKills {G : Type*} [CommGroup G] [TopologicalSpace G] (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Subgroup G)
    (hR : ∀ (n : ℕ) (f : Additive G →+ ZMod (ℓ ^ n)), Continuous ⇑f →
      ∀ r : G, r ∈ R → f (Additive.ofMul r) = 0) :
    Nonempty (NK.Reconstruct.Dual G ℓ ≃ₗ[PadicInt ℓ] NK.Reconstruct.Dual (G ⧸ R) ℓ) :=
  ⟨DualKillsAux.dualEquiv R hR⟩

end

end NK.NUV2.ArtinBridge
