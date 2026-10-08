import Mathlib
import Submission.Work.BG.CharBridge
import Submission.Work.BG.irrEqTrivialOfInvFixed
import Submission.Work.BG.oddNatCardConjByOrbit
import Submission.Work.BG.restrictionMultiplicityCompHomOfInvolutive
import Submission.Work.BG.existsFixedPointOfInvolutiveOfOddNatCard
import Submission.Work.BG.eq_one_of_trivial_liesOver

set_option linter.style.haveILetI false

/-!
# Area BG: the kernel of a `σ`-invariant irreducible character contains an inverted normal
subgroup

Bender–Glauberman 1981, Lemma 3.6 (the "Piece A" gap of the printed proof, see
`NOTES_c4Degree.md` §1(a) and §3): if an automorphism `σ` of a finite group `U` of **odd**
order inverts every element of a normal subgroup `K ⊴ U` (`σ k = k⁻¹` for `k ∈ K`) and `a` is a
`σ`-invariant irreducible character of `U` (`a (σ u) = a u`), then `K ≤ ker a`, i.e.
`a k = a 1` for every `k ∈ K`.

The printed proof of Lemma 3.6 uses this without proof ("inverting `K`, each element of
`S - S₀` moves `a`"), and as printed it is false for nonlinear `a`: `σ`-invariance only gives
`a k = a (k⁻¹) = conj (a k)` on `K`, which by itself is no contradiction.  The extra input is
that `K` has odd order, via Clifford's theorem:

* `K` is commutative (`σ` inverts it, so inversion is an automorphism of `K`), and `#K` is odd;
* Clifford's single-orbit theorem (`restrictionConstituentsSingleOrbit_of_isIrreducible`)
  says the irreducible constituents of `Res_K a` form a single `U`-conjugation orbit
  `O = conjByOrbit μ₀`;
* the `σ`-invariance of `a` makes this support invariant under the involution
  `μ ↦ μ ∘ σ` of `Irr K` (the multiplicity `⟨Res_K a, μ⟩ = ⟨Res_K a, μ ∘ σ⟩`), because
  `Res_K a` is `σ`-invariant;
* `|O| = [U : I_U(μ₀)]` is odd, so the involution has a fixed point `μ₁ ∈ O`
  (`Work.BG.existsFixedPointOfInvolutiveOfOddNatCard`);
* a fixed point satisfies `μ₁ (k⁻¹) = μ₁ k`; as `K` is commutative and of odd order, `μ₁` must
  be the trivial character (`Work.BG.irrEqTrivialOfInvFixed`);
* the orbit of `1_K` is `{1_K}`, so `O = {1_K}` and `Res_K a` is a multiple of `1_K`: every
  constituent is trivial (`Work.BG.eq_one_of_trivial_liesOver`) and `a` is constant on `K`.

## Main result

* `Work.BG.kerLeOfMulAutInv`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- Restriction of an automorphism of `U` to an invariant subgroup, as a monoid hom. -/
def restrictMulHom {U : Type} [Group U] (K : Subgroup U) (σ : MulAut U)
    (h : ∀ k ∈ K, σ k ∈ K) : K →* K where
  toFun k := ⟨σ k, h k k.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [map_mul]

open OddOrder.RepresentationTheory in
theorem kerLeOfMulAutInv {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (K : Subgroup U) [K.Normal] (hoddU : Odd (Nat.card U))
    (σ : MulAut U) (hσ : ∀ k ∈ K, σ k = k⁻¹) (a : ClassFunction U ℂ)
    (ha : IsIrreducibleCharacter a) (hfix : ∀ u : U, a (σ u) = a u) :
    ∀ k ∈ K, a k = a 1 := by
  classical
  haveI hFinK : Finite K := Finite.of_injective (fun k : K => (k : U))
    (fun x y h => Subtype.ext h)
  haveI hFK : Fintype K := Fintype.ofFinite K
  haveI hIK : Invertible (Nat.card K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `σ` inverts every element of `K`
  have hσinv : ∀ k : K, σ (k : U) = ((k : U))⁻¹ := fun k => hσ k k.2
  have hmemσ : ∀ k ∈ K, σ k ∈ K := fun k hk => by
    rw [hσ k hk]; exact K.inv_mem hk
  -- every element of `K` is inverted by `σ`, so `K` is commutative
  have hcomm : ∀ x y : K, x * y = y * x := by
    intro x y
    apply Subtype.ext
    have hxy : ((x : U) * (y : U))⁻¹ = (x : U)⁻¹ * (y : U)⁻¹ := by
      rw [← hσinv x, ← hσinv y, ← map_mul, hσ ((x : U) * (y : U)) (K.mul_mem x.2 y.2)]
    have h1 : (x : U)⁻¹ * (y : U)⁻¹ = (y : U)⁻¹ * (x : U)⁻¹ := by
      rw [← hxy, mul_inv_rev]
    have h2 : (y : U) * (x : U) = (x : U) * (y : U) := by
      calc (y : U) * (x : U) = ((x : U)⁻¹ * (y : U)⁻¹)⁻¹ := by group
        _ = ((y : U)⁻¹ * (x : U)⁻¹)⁻¹ := by rw [h1]
        _ = (x : U) * (y : U) := by group
    exact h2.symm
  haveI hCommK : IsMulCommutative K := ⟨⟨hcomm⟩⟩
  -- `K` has odd order
  have hKodd : Odd (Nat.card K) := hoddU.of_dvd_nat K.card_subgroup_dvd_card
  -- the restriction of `σ` to `K`
  let σK : K →* K := restrictMulHom K σ hmemσ
  have hσK_coe : ∀ k : K, ((σK k : K) : U) = σ (k : U) := fun k => rfl
  have hσK_eq_inv : ∀ k : K, σK k = k⁻¹ := by
    intro k
    apply Subtype.ext
    rw [hσK_coe k]
    exact hσ k k.2
  have hσK_invol : ∀ k : K, σK (σK k) = k := by
    intro k
    apply Subtype.ext
    rw [hσK_coe (σK k), hσK_coe k]
    rw [hσ (σ (k : U)) (hmemσ (k : U) k.2), hσinv k]
    simp
  have hσK_surj : Function.Surjective σK := fun x => ⟨σK x, hσK_invol x⟩
  -- the irreducible character
  let χ : IrreducibleCharacter U := ⟨a, ha⟩
  haveI hFinIrrK : Finite (IrreducibleCharacter K) := finite_irreducibleCharacter (G := K)
  -- a constituent of `Res_K χ`
  obtain ⟨μ₀, hμ₀⟩ := IrreducibleCharacter.exists_liesOver (H := K) χ
  -- Clifford: the constituents form a single `U`-orbit
  have hsingle : χ.RestrictionConstituentsSingleOrbit :=
    restrictionConstituentsSingleOrbit_of_isIrreducible (H := K) χ
  have hmem_iff : ∀ μ : IrreducibleCharacter K,
      μ ∈ IrreducibleCharacter.conjByOrbit (G := U) (H := K) μ₀ ↔
        IrreducibleCharacter.LiesOver K χ μ := by
    intro μ
    constructor
    · intro h
      rw [IrreducibleCharacter.mem_conjByOrbit] at h
      obtain ⟨g, hg⟩ := h
      rw [← hg]
      exact IrreducibleCharacter.liesOver_conjBy hμ₀ g
    · intro h
      rw [IrreducibleCharacter.mem_conjByOrbit]
      exact hsingle.exists_conj hμ₀ h
  -- the `σ`-twist on irreducible characters of `K`
  let conjσ : IrreducibleCharacter K → IrreducibleCharacter K := fun μ =>
    ⟨ClassFunction.compHom σK (μ : ClassFunction K ℂ),
      IsIrreducibleCharacter.compHom_of_surjective hσK_surj μ.isIrreducible⟩
  have hconjσ_coe : ∀ μ : IrreducibleCharacter K,
      ((conjσ μ : IrreducibleCharacter K) : ClassFunction K ℂ) =
        ClassFunction.compHom σK (μ : ClassFunction K ℂ) := fun μ => rfl
  have hcompHom_id : ∀ φ : ClassFunction K ℂ,
      ClassFunction.compHom (MonoidHom.id K) φ = φ :=
    fun φ => ClassFunction.ext (fun x => rfl)
  have hcomp_self : σK.comp σK = MonoidHom.id K := MonoidHom.ext hσK_invol
  have hconjσ_invol : ∀ μ : IrreducibleCharacter K, conjσ (conjσ μ) = μ := by
    intro μ
    apply IrreducibleCharacter.ext
    rw [hconjσ_coe, hconjσ_coe, ClassFunction.compHom_comp, hcomp_self, hcompHom_id]
  have hfix_K : ∀ k : K, (χ : ClassFunction U ℂ) (σK k) = (χ : ClassFunction U ℂ) k :=
    fun k => hfix (k : U)
  -- the constituent set is `σ`-invariant
  have hmem_conj : ∀ μ : IrreducibleCharacter K,
      μ ∈ IrreducibleCharacter.conjByOrbit (G := U) (H := K) μ₀ →
        conjσ μ ∈ IrreducibleCharacter.conjByOrbit (G := U) (H := K) μ₀ := by
    intro μ hμ
    rw [hmem_iff, IrreducibleCharacter.liesOver_iff] at hμ
    rw [hmem_iff, IrreducibleCharacter.liesOver_iff]
    rw [hconjσ_coe]
    rw [restrictionMultiplicityCompHomOfInvolutive (K := K) (f := σK) (hf := hσK_invol)
      (a := (χ : ClassFunction U ℂ)) (hfix := hfix_K) (μ := (μ : ClassFunction K ℂ))]
    exact hμ
  -- the constituent set has odd cardinality, so the involution `conjσ` has a fixed point
  have hodd_orbit : Odd (Nat.card {η : IrreducibleCharacter K //
      η ∈ IrreducibleCharacter.conjByOrbit (G := U) (H := K) μ₀}) :=
    oddNatCardConjByOrbit K hoddU μ₀
  let S : Set (IrreducibleCharacter K) := IrreducibleCharacter.conjByOrbit (G := U) (H := K) μ₀
  let Φ : ↥S → ↥S := fun μ => ⟨conjσ μ.1, hmem_conj μ.1 μ.2⟩
  have hΦ_invol : Function.Involutive Φ := fun μ => Subtype.ext (hconjσ_invol μ.1)
  haveI hFinS : Finite ↥S := Subtype.finite
  obtain ⟨μ₁, hμ₁⟩ := existsFixedPointOfInvolutiveOfOddNatCard Φ hΦ_invol hodd_orbit
  have hfixpt : conjσ μ₁.1 = μ₁.1 := congrArg Subtype.val hμ₁
  -- the fixed point is the trivial character
  have hinvval : ∀ k : K, (μ₁.1 : ClassFunction K ℂ) k⁻¹ = (μ₁.1 : ClassFunction K ℂ) k := by
    intro k
    have h : (conjσ μ₁.1 : ClassFunction K ℂ) k = (μ₁.1 : ClassFunction K ℂ) k :=
      congrArg (fun x : IrreducibleCharacter K => (x : ClassFunction K ℂ) k) hfixpt
    rw [hconjσ_coe] at h
    have h2 : ClassFunction.compHom σK (μ₁.1 : ClassFunction K ℂ) k =
        (μ₁.1 : ClassFunction K ℂ) (σK k) := rfl
    rw [h2] at h
    rw [← hσK_eq_inv k]
    exact h
  have htriv_class : (μ₁.1 : ClassFunction K ℂ) = trivialClassFunction K :=
    irrEqTrivialOfInvFixed hKodd (μ₁.1 : ClassFunction K ℂ) μ₁.1.isIrreducible hinvval
  have htriv : μ₁.1 = trivialIrreducibleCharacter K :=
    IrreducibleCharacter.ext
      (htriv_class.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter (G := K)).symm)
  have hover : IrreducibleCharacter.LiesOver K χ (trivialIrreducibleCharacter K) := by
    have h := (hmem_iff μ₁.1).mp μ₁.2
    rwa [htriv] at h
  intro k hk
  exact eq_one_of_trivial_liesOver K χ hover ⟨k, hk⟩

end Work.BG
