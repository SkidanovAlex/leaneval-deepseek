import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataTwo.kummerCochar_eq_zero_of_isFrobAtPrime_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Schmidt--Wingberg section four, `p = 2`: the three-term verification step

This module begins the formalisation of the `p = 2` case of section four of Schmidt--Wingberg,
*Šafarevič's theorem on solvable groups as Galois groups* (arXiv:math/9809211, pp. 16--17), on top
of the combinatorial material already on disk (`ZDataTwo/two_partition`, `pigeonhole_three`,
`three_term_cancellation`, `localPowClass_three_term_agree`, `map_decomp_res_eq_zpowers_of_isFrobAtPrime`,
`kummerCochar_eq_zero_of_isFrobAtPrime_eq_zero`).

The class produced by the construction is the **three-term sum** `z = z_i + z_j + z_N` of Schmidt--
Wingberg.  The last step of their verification is: at each prime `P` of the three chosen classes
(and at each of its conjugates) the value of `z` at a Frobenius element vanishes, and then `z`
vanishes on the *whole* local group of that prime.  The second half of that step is the banked
`kummerCochar_eq_zero_of_isFrobAtPrime_eq_zero`; the first half is the computation
`z = z_{b_i} + z_{b_j} + z_{b_N} = z_{b_i b_j b_N}`, which turns the three-term sum into a single
Kummer cochain.

`Work.SSGRoute.ZDataTwo.threeTerm_kills_localGroup` below is that step: if the Kummer cochain of the
*product* `b₁ b₂ b₃` vanishes at a Frobenius element `σ` of the local group of a place `B` (with the
banked hypotheses: `B ∤ 2`, `B` unramified in the auxiliary level `L`, the product unramified at
`B`) and factors through `res k L`, then the sum of the three Kummer cochains vanishes on all of
`decomp k B ⊓ K.fixingSubgroup` — which is Schmidt--Wingberg's "`z_{σP} = 0`" for the three-term
sum, i.e. conjunct (b) of the `z`-data after the conjugacy bookkeeping.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The three-term verification step of Schmidt--Wingberg section four (`p = 2`).**

Let `b₁, b₂, b₃ ∈ (↥K)ˣ` be the Kummer classes of the three members of the constructed sequence and
let `B` be a finite place with `B ∤ 2`, `B` unramified in the finite Galois level `L`, at which the
product `b₁ b₂ b₃` is unramified (some `d` witnesses `v_B(b₁b₂b₃) = v_B(d)²`).  If the Kummer cochain
of the product vanishes at an element `σ` of the local group of `B` which is a Frobenius at the
level `L`, and the cochain of the product factors through `res k L` on the local group, then the
three-term sum of the Kummer cochains vanishes on the whole local group of `B`.

This is the point at which the paper's `z_{σP_i} = 0` becomes `z`'s vanishing on `D_{σP_i} ⊓ G_K`,
i.e. conjunct (b) of the `z`-data. -/
theorem threeTerm_kills_localGroup
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔭 : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭)
    (h2 : ¬ B.valuation (2 : Ω) < 1)
    (hunrL : ¬ SSGRoute.IsRamifiedIn k L B)
    (b₁ b₂ b₃ d : (↥K)ˣ)
    (hur : B.valuation (algebraMap ↥K Ω ((b₁ * b₂ * b₃ : (↥K)ˣ) : ↥K)) =
      B.valuation (algebraMap ↥K Ω (d : ↥K)) ^ 2)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup)
    (hfac : ∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      ∀ τ' ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      SSGRoute.res k L τ = SSGRoute.res k L τ' →
      nodeKummerCochar K ζ hζK hζ (b₁ * b₂ * b₃) τ =
        nodeKummerCochar K ζ hζK hζ (b₁ * b₂ * b₃) τ')
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭 (SSGRoute.res k L σ))
    (hval : nodeKummerCochar K ζ hζK hζ (b₁ * b₂ * b₃) σ = 0) :
    ∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      nodeKummerCochar K ζ hζK hζ b₁ τ + nodeKummerCochar K ζ hζK hζ b₂ τ +
        nodeKummerCochar K ζ hζK hζ b₃ τ = 0 := by
  classical
  have hzero : ∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      nodeKummerCochar K ζ hζK hζ (b₁ * b₂ * b₃) τ = 0 :=
    kummerCochar_eq_zero_of_isFrobAtPrime_eq_zero K ζ hζ hζK L B hB 𝔭 h𝔭 h2 hunrL
      (b₁ * b₂ * b₃) d hur σ hσ hfac hfrob hval
  intro τ hτ
  have hmul : nodeKummerCochar K ζ hζK hζ (b₁ * b₂ * b₃) =
      nodeKummerCochar K ζ hζK hζ b₁ + nodeKummerCochar K ζ hζK hζ b₂ +
        nodeKummerCochar K ζ hζK hζ b₃ := by
    show kummerCochar K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) (b₁ * b₂ * b₃) = _
    rw [kummerCochar_mul, kummerCochar_mul]
    rfl
  have h := hzero τ hτ
  rw [hmul] at h
  simpa only [Pi.add_apply] using h


/-! ## The arithmetic consequence of the three-term verification

The verification step above says that the three-term sum vanishes on the local group of `B`.  Via
the local Kummer dictionary `kummerCochar_eq_zero_iff_localPowClass`, this is exactly the *arithmetic*
condition of `Work.SSGRoute.ZDataTwo.ArithCore` clause (D): the class `b₁ b₂ b₃` is a local `2`-power
at the prime of `K` below `B`. -/

/-- **Clause (D) of the arithmetic core from the three-term verification.**  Under the hypotheses of
`threeTerm_kills_localGroup`, the product `b₁ b₂ b₃` is a local `2`-power at the prime `𝔮` of `K`
below `B` — i.e. Schmidt--Wingberg's sharpened condition (b) for the three-term sum, written in the
arithmetic vocabulary of the core. -/
theorem threeTerm_localPowClass_one
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔭 : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭)
    (h2 : ¬ B.valuation (2 : Ω) < 1)
    (hunrL : ¬ SSGRoute.IsRamifiedIn k L B)
    (b₁ b₂ b₃ d : (↥K)ˣ)
    (hur : B.valuation (algebraMap ↥K Ω ((b₁ * b₂ * b₃ : (↥K)ˣ) : ↥K)) =
      B.valuation (algebraMap ↥K Ω (d : ↥K)) ^ 2)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup)
    (hfac : ∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      ∀ τ' ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      SSGRoute.res k L τ = SSGRoute.res k L τ' →
      nodeKummerCochar K ζ hζK hζ (b₁ * b₂ * b₃) τ =
        nodeKummerCochar K ζ hζK hζ (b₁ * b₂ * b₃) τ')
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭 (SSGRoute.res k L σ))
    (hval : nodeKummerCochar K ζ hζK hζ (b₁ * b₂ * b₃) σ = 0)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔮 : B.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮) :
    NK.UchidaKummer.localPowClass ↥K 2 𝔮 (b₁ * b₂ * b₃) = 1 := by
  classical
  have hmul : nodeKummerCochar K ζ hζK hζ (b₁ * b₂ * b₃) =
      nodeKummerCochar K ζ hζK hζ b₁ + nodeKummerCochar K ζ hζK hζ b₂ +
        nodeKummerCochar K ζ hζK hζ b₃ := by
    show kummerCochar K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) (b₁ * b₂ * b₃) = _
    rw [kummerCochar_mul, kummerCochar_mul]
    rfl
  refine (kummerCochar_eq_zero_iff_localPowClass K ⟨ζ, hζK⟩
    (isPrimitiveRoot_subtype_of_mem hζK hζ) (b₁ * b₂ * b₃) B hB 𝔮 h𝔮).mp ?_
  intro τ hτ
  have hsum := threeTerm_kills_localGroup k Ω K ζ hζ hζK L B hB 𝔭 h𝔭 h2 hunrL b₁ b₂ b₃ d hur
    σ hσ hfac hfrob hval τ hτ
  rw [show kummerCochar K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) (b₁ * b₂ * b₃) τ
      = nodeKummerCochar K ζ hζK hζ (b₁ * b₂ * b₃) τ from rfl, hmul]
  simpa only [Pi.add_apply] using hsum


/-! ## The `G₁` (involution) case of the verification

Schmidt--Wingberg verify `z_s(\mathrm{Frob}_{\sigma P_t}) = 1` for every `\sigma \in G_1` (the
involutions) and every `s, t` by a three-step induction.  Writing
`\varphi\ s\ t = z_s(\mathrm{Frob}_{\sigma P_t}) \in \mathbb{F}_2`, the three steps become:

* **(3)**: `\varphi\ t\ s = 0` for `t > s` (the value of the *later* class at the earlier prime);
* **the Claim**: `\varphi\ s\ s = 0`;
* **the product formula** (the paper's `(z_s, \sigma z_t)_{\sigma P_t} = (\sigma z_s, z_t)_{P_t} =
  (\sigma z_s, z_t)_{\sigma P_s}` chain): `\varphi\ s\ t = \varphi\ t\ s` for `s < t`.

`sw_frob_vanishing_G1` below records the concluding induction, which is pure combinatorics in
`\mathbb{F}_2` — the *content* of the paper's computation is the third bullet. -/

/-- **The `G₁` case of the verification, as combinatorics.**  For a function
`\varphi : \mathbb{N} \to \mathbb{N} \to \mathbb{Z}/2` satisfying the three relations above, `\varphi`
vanishes identically. -/
theorem sw_frob_vanishing_G1 (φ : ℕ → ℕ → ZMod 2)
    (h3 : ∀ s t : ℕ, t > s → φ t s = 0)
    (hclaim : ∀ s : ℕ, φ s s = 0)
    (hrec : ∀ s t : ℕ, s < t → φ s t = φ t s) :
    ∀ s t : ℕ, φ s t = 0 := by
  intro s t
  rcases lt_trichotomy s t with h | h | h
  · rw [hrec s t h]; exact h3 s t h
  · rw [h]; exact hclaim t
  · exact h3 t s h


/-! ## The three-term sum vanishes wherever the product's cochain does

The last step of the assembly rewrites the three-term sum as the single Kummer cochain of the
product `b₁ b₂ b₃` (`kummerCochar_mul`).  This is the form in which the paper's `z = z_i + z_j + z_N`
is fed to the detection lemma at each prime, and it is the form of the node's clause (6)(b). -/

/-- **The three-term sum vanishes wherever the product's cochain does.** -/
theorem threeTerm_eq_of_mul (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω] (K : IntermediateField k Ω) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ 2)
    (hζK : ζ ∈ K) (b₁ b₂ b₃ : (↥K)ˣ) :
    nodeKummerCochar K ζ hζK hζ (b₁ * b₂ * b₃) =
      nodeKummerCochar K ζ hζK hζ b₁ + nodeKummerCochar K ζ hζK hζ b₂ +
        nodeKummerCochar K ζ hζK hζ b₃ := by
  show kummerCochar K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) (b₁ * b₂ * b₃) = _
  rw [kummerCochar_mul, kummerCochar_mul]
  rfl

end Work.SSGRoute.ZDataTwo
