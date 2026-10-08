import Mathlib
import Submission.Work.CharPrelim.weightSpace_decomposition
import Submission.Work.ThmF.ChV12.card_orbit_ge_of_orderOf_prime_pow
import Submission.Work.ThmF.ChV12.zpow_mem_of_iff_smul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `p ≤ finrank K V` for a faithful `W`-module (`|W| = p²`) with an order-`p^k` automorphism

Let `K` be an algebraically closed field with `ringChar K ≠ p` (`p` prime), `W` a finite abelian
group with `|W| = p ^ 2`, `V` a finite-dimensional `K`-vector space, and `ρW : W →* End K V` a
*faithful* representation.  Let `σ : MulAut W` be an automorphism of order `p ^ k` (`k > 0`) that
is realised on `V` by a `K`-linear automorphism `σV` (compatibly).  Then `p ≤ finrank K V`.

The proof is a weight-space (character) count.  Over an algebraically closed field in which `|W|`
is invertible, `V` decomposes into weight spaces `V_χ` indexed by the characters `χ : W →* Kˣ`:

* the *support* `S = {χ | V_χ ≠ 0}` is a finite set, and (linear independence of the weight
  spaces) `|S| ≤ finrank K V`;
* `σV` maps `V_χ` *onto* `V_{σ • χ}`, so `S` is invariant under the action of `σ` on characters;
* faithfulness forces `S` to contain a character moved by `σ`: the image `U` of
  `w ↦ σ w · w⁻¹` is a nontrivial subgroup, and every character fixed by `σ` is trivial on `U`; if
  `S` consisted only of fixed characters, then `ρW u = 1` for `1 ≠ u ∈ U`, contradicting
  faithfulness;
* the orbit of a moved `χ` under `⟨σ⟩` (a group of order `p^k`) then has at least `p` elements,
  all in `S`.
-/

set_option linter.style.haveILetI false

namespace Work.ThmF.ChV12

open Work.CharPrelim

variable {K W : Type*} [Field K] [CommGroup W]

/-- `MulAut W` acts on the character group `W →* Kˣ` by `(φ • χ) w = χ (φ.symm w)`; this is the
action transported from the natural action of `MulAut W` on `W` by taking inverses. -/
instance instMulActionMulAutChar : MulAction (MulAut W) (W →* Kˣ) where
  smul φ χ := χ.comp φ.symm.toMonoidHom
  one_smul χ := by
    show χ.comp (1 : MulAut W).symm.toMonoidHom = χ
    ext w; rfl
  mul_smul φ ψ χ := by
    show (χ.comp ψ.symm.toMonoidHom).comp φ.symm.toMonoidHom =
      χ.comp (φ * ψ).symm.toMonoidHom
    ext w
    rw [show (φ * ψ).symm = ψ.symm * φ.symm from by ext x; rfl]
    rfl

/-- Unwinding of the character action. -/
@[simp] lemma charSmul_apply (φ : MulAut W) (χ : W →* Kˣ) (w : W) :
    (φ • χ) w = χ (φ.symm w) := rfl

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- **Key compatibility lemma.**  If `Φ` intertwines the representation `ρW` with its twist
`ρW ∘ φ` (i.e. `Φ * ρW w = ρW (φ w) * Φ` for all `w`), then `Φ` maps the `χ`-weight space
*onto* the `(φ • χ)`-weight space. -/
theorem map_weightSpace_eq (ρW : W →* Module.End K V) (φ : MulAut W) (Φ : V ≃ₗ[K] V)
    (hcompat : ∀ w : W, (Φ : Module.End K V) * ρW w = ρW (φ w) * (Φ : Module.End K V))
    (χ : W →* Kˣ) :
    Submodule.map (Φ : V →ₗ[K] V) (weightSpace ρW χ) = weightSpace ρW (φ • χ) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨v, hv, rfl⟩
    rw [mem_weightSpace]
    intro w
    have hv' := (mem_weightSpace ρW χ v).mp hv
    have h := congrArg (fun f : Module.End K V => f v) (hcompat (φ.symm w))
    simp only [Module.End.mul_apply] at h
    rw [MulEquiv.apply_symm_apply] at h
    rw [← h, hv' (φ.symm w), LinearMap.map_smul]
    rfl
  · rintro x hx
    rw [Submodule.mem_map]
    refine ⟨Φ.symm x, ?_, by simp⟩
    rw [mem_weightSpace]
    intro w
    have hx' := (mem_weightSpace ρW (φ • χ) x).mp hx
    have h := congrArg (fun f : Module.End K V => f (Φ.symm x)) (hcompat w)
    simp only [Module.End.mul_apply] at h
    simp only [LinearEquiv.coe_coe] at h
    have h2 : Φ (ρW w (Φ.symm x)) = ρW (φ w) x := by
      rw [h, LinearEquiv.apply_symm_apply]
    have key : ρW w (Φ.symm x) = Φ.symm (ρW (φ w) x) := by
      have := congrArg (fun y => Φ.symm y) h2
      rwa [LinearEquiv.symm_apply_apply] at this
    rw [key, hx' (φ w), LinearEquiv.map_smul]
    show (χ (φ.symm (φ w)) : K) • (Φ.symm x) = (χ w : K) • Φ.symm x
    rw [MulEquiv.symm_apply_apply]

/-- The weight space, as an `abbrev` (so that type-class inference can unfold it). -/
abbrev wSp (ρW : W →* Module.End K V) (χ : W →* Kˣ) : Submodule K V :=
  ⨅ z, LinearMap.ker ((ρW z : Module.End K V) - (χ z : K) • 1)

/-- The support: the set of characters occurring as weights of the representation. -/
def charSupp (ρW : W →* Module.End K V) : Set (W →* Kˣ) := {χ | weightSpace ρW χ ≠ ⊥}

@[simp] lemma mem_charSupp {ρW : W →* Module.End K V} {χ : W →* Kˣ} :
    χ ∈ charSupp ρW ↔ weightSpace ρW χ ≠ ⊥ := Iff.rfl

/-- A linear automorphism sends a submodule to `⊥` iff the submodule was `⊥`. -/
lemma map_eq_bot_iff_of_linearEquiv (Φ : V ≃ₗ[K] V) (S : Submodule K V) :
    Submodule.map (Φ : V →ₗ[K] V) S = ⊥ ↔ S = ⊥ := by
  constructor
  · intro h
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hmem : Φ v ∈ Submodule.map (Φ : V →ₗ[K] V) S := ⟨v, hv, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact Φ.injective (by rw [hmem, map_zero])
  · intro h; rw [h, Submodule.map_bot]

/-- **Existence of a moved weight.**  Under faithfulness of `ρW`, if `σ ≠ 1` then the support
contains a character that is moved by `σ`. -/
theorem exists_moved_mem_charSupp {ρW : W →* Module.End K V}
    (hfaith : Function.Injective ρW) (hspan : (⨆ χ : W →* Kˣ, weightSpace ρW χ) = ⊤)
    (σ : MulAut W) (hσne : σ ≠ 1) :
    ∃ χ : W →* Kˣ, χ ∈ charSupp ρW ∧ σ • χ ≠ χ := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  obtain ⟨w₀, hw₀⟩ : ∃ w : W, σ w ≠ w := by
    by_contra h'
    simp only [not_exists, not_not] at h'
    exact hσne (MulEquiv.ext h')
  have hne : σ w₀ * w₀⁻¹ ≠ 1 := by
    intro h1
    apply hw₀
    have h2 : σ w₀ * w₀⁻¹ = w₀ * w₀⁻¹ := by rw [h1, mul_inv_cancel]
    exact mul_right_cancel h2
  have hker : ∀ χ : W →* Kˣ,
      weightSpace ρW χ ≤ LinearMap.ker ((ρW (σ w₀ * w₀⁻¹)) - 1) := by
    intro χ v hv
    rw [LinearMap.mem_ker]
    by_cases hS : weightSpace ρW χ = ⊥
    · rw [hS, Submodule.mem_bot] at hv
      rw [hv]; simp
    · have hfix : σ • χ = χ := h χ hS
      have hχu : χ (σ w₀ * w₀⁻¹) = 1 := by
        have hfixw : χ (σ w₀) = χ w₀ := by
          have hc : (σ • χ) (σ w₀) = χ (σ w₀) :=
            congrArg (fun η : W →* Kˣ => η (σ w₀)) hfix
          rw [charSmul_apply, MulEquiv.symm_apply_apply] at hc
          exact hc.symm
        rw [map_mul, map_inv, hfixw, mul_inv_cancel]
      have hv' := (mem_weightSpace ρW χ v).mp hv
      rw [LinearMap.sub_apply, hv' (σ w₀ * w₀⁻¹), Module.End.one_apply, hχu]
      simp
  have hle : (⨆ χ : W →* Kˣ, weightSpace ρW χ) ≤
      LinearMap.ker ((ρW (σ w₀ * w₀⁻¹)) - 1) := iSup_le hker
  have hkerTop : LinearMap.ker ((ρW (σ w₀ * w₀⁻¹)) - 1) = ⊤ := by
    rw [eq_top_iff, ← hspan]; exact hle
  have hzero : (ρW (σ w₀ * w₀⁻¹)) - 1 = 0 := LinearMap.ker_eq_top.mp hkerTop
  have hone : ρW (σ w₀ * w₀⁻¹) = 1 := sub_eq_zero.mp hzero
  exact hne (hfaith (by rw [hone, map_one]))

theorem Cp2_action_finrank_ge
    {K : Type*} [Field K] [IsAlgClosed K]
    {p : ℕ} (hp : p.Prime) (hchar : ringChar K ≠ p)
    {W : Type*} [CommGroup W] [Finite W] (hW : Nat.card W = p ^ 2)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρW : W →* Module.End K V) (hfaith : Function.Injective ρW)
    (σ : MulAut W) (hσpow : ∃ k : ℕ, 0 < k ∧ orderOf σ = p ^ k)
    (σV : V ≃ₗ[K] V)
    (hcompat : ∀ w : W, (σV : Module.End K V) * ρW w = ρW (σ w) * (σV : Module.End K V)) :
    p ≤ Module.finrank K V := by
  obtain ⟨k, hkpos, hσord⟩ := hσpow
  have hpK : (p : K) ≠ 0 := by
    rw [ne_eq, ringChar.spec]
    intro hdvd
    rcases hp.eq_one_or_self_of_dvd (ringChar K) hdvd with h1 | hp_eq
    · have hdvd1 : ringChar K ∣ 1 := by rw [h1]
      have hzero : (1 : K) = 0 := by simpa using (ringChar.spec K 1).mpr hdvd1
      exact one_ne_zero hzero
    · exact hchar hp_eq
  have hcard : IsUnit ((Nat.card W : ℕ) : K) := by
    rw [hW, Nat.cast_pow]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hpK)
  have hσne : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσord
    have hpk : 1 < p ^ k := one_lt_pow' hp.one_lt hkpos.ne'
    omega
  obtain ⟨hspan, hindep⟩ := weightSpace_decomposition ρW hcard
  letI : Fintype {χ : W →* Kˣ // wSp ρW χ ≠ ⊥} :=
    hindep.fintypeNeBotOfFiniteDimensional
  have hbound : Fintype.card {χ : W →* Kˣ // wSp ρW χ ≠ ⊥} ≤ Module.finrank K V :=
    hindep.subtype_ne_bot_le_finrank
  obtain ⟨χ₀, hχ₀, hmoved⟩ := exists_moved_mem_charSupp hfaith hspan σ hσne
  have hSiff : ∀ χ : W →* Kˣ, χ ∈ charSupp ρW ↔ σ • χ ∈ charSupp ρW := by
    intro χ
    have heq := map_weightSpace_eq ρW σ σV hcompat χ
    have key : Submodule.map (σV : V →ₗ[K] V) (weightSpace ρW χ) = ⊥ ↔
        weightSpace ρW χ = ⊥ := map_eq_bot_iff_of_linearEquiv σV _
    simp only [mem_charSupp]
    rw [← heq]
    exact (Iff.not key).symm
  have horbS : ∀ y ∈ MulAction.orbit (Subgroup.zpowers σ) χ₀, y ∈ charSupp ρW := by
    intro y hy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
    rw [← hg]
    exact zpow_mem_of_iff_smul hSiff g g.2 χ₀ hχ₀
  have hinj : Function.Injective
      (fun y : MulAction.orbit (Subgroup.zpowers σ) χ₀ =>
        (⟨(y : W →* Kˣ), horbS y y.2⟩ : {χ : W →* Kˣ // wSp ρW χ ≠ ⊥})) := by
    intro a b hab
    have h1 : (a : W →* Kˣ) = (b : W →* Kˣ) :=
      congrArg (fun z : {χ : W →* Kˣ // wSp ρW χ ≠ ⊥} => (z : W →* Kˣ)) hab
    exact Subtype.ext h1
  have hOge : p ≤ Nat.card (MulAction.orbit (Subgroup.zpowers σ) χ₀) :=
    card_orbit_ge_of_orderOf_prime_pow hp hσord χ₀ hmoved
  calc p ≤ Nat.card (MulAction.orbit (Subgroup.zpowers σ) χ₀) := hOge
    _ ≤ Nat.card {χ : W →* Kˣ // wSp ρW χ ≠ ⊥} :=
        Nat.card_le_card_of_injective _ hinj
    _ = Fintype.card {χ : W →* Kˣ // wSp ρW χ ≠ ⊥} := Nat.card_eq_fintype_card
    _ ≤ Module.finrank K V := hbound

end Work.ThmF.ChV12
