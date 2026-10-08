/-
Area `A7REC`, file `Char/a7Char6_of_table.lean`: the assembly of `A7Char6Prop` from the
character-theoretic leaves of design pass 7.

Given, for every group `G` satisfying `A7RecHyps G S z U V`:

* the C1b indexing of the non-trivial irreducible characters occurring in the three induced
  generalised characters (`A7C1bProp`),
* the p11 bridge `A7BridgeProp` turning the involution counts into the three rational relations,
* the finite table lemma `A7TableLemmaProp`,
* the involution counts `A7InvolutionCounts2Prop`,
* the value lemma `A7Y6ValuesProp`,

we produce the degree-`6` irreducible representation of `A7Char6Prop`.

The route is:

1. fix `π ∈ S` of order `4` with `C(π) = ⟨π⟩` (proved, `Basic.exists_tau_order_four`) and
   `σ ∈ U^#`;
2. C1b + the bridge + the table give the indexing data `n, ι, f, e, a, b` with a unique `i₀`
   such that `f i₀ = 6`, `e i₀ = 0`, `a i₀ = -1`, `b i₀ = 0`; the irreducible character
   `χ = ι i₀` then has `χ(z) = b - 2a = 2` and `χ(zσ) = a + b = -1`.  Since
   `IsIrreducibleCharacter` *is* the existence of a finite-dimensional irreducible
   representation with that character, `χ` yields a genuine representation `ρ`;
3. the completeness lemma `irr_deg_six_mem_range` (Burnside's `Σ χ(1)² = |G|` together with the
   table equality `1 + Σ f² = 2520`) shows that every irreducible character of degree `6` is
   one of the `ι i`, hence `= χ`: this is exactly the uniqueness hypothesis of
   `A7Y6ValuesProp`;
4. `A7Y6ValuesProp` applied to `σ` gives `trace (ρ σ) = 3` and the values at order-`7`
   elements;
5. running the same construction with `σ²` (and transferring along the uniqueness of step 3)
   gives `trace (ρ (z σ²)) = -1`, so `A7Y6ValuesProp` also applies with `σ²`; since `U = ⟨σ⟩`
   has order `3`, the non-identity elements of `U` are exactly `σ` and `σ²`.
-/
import Mathlib
import Submission.Work.A7REC.Char.C1b
import Submission.Work.A7REC.Char.Bridge
import Submission.Work.A7REC.Assembly
import Submission.Work.A7REC.Char.DegSqDeps
import Submission.Work.A7REC.Basic.exists_tau_order_four
import Submission.Work.A7REC.Basic.local
import Submission.Work.A7REC.Basic.exists_involution_inverting
import Submission.Work.A7REC.Char.irr_deg_six_mem_range

namespace Work.A7REC.Char

open Subgroup OddOrder.RepresentationTheory
open scoped Classical

/-- **The degree-`6` data.**  For `σ ∈ U^#`, the C1b indexing, the bridge and the table lemma
produce an irreducible representation `ρ` of dimension `6` with `trace (ρ z) = 2` and
`trace (ρ (zσ)) = -1`, together with the uniqueness of the character in degree `6` (the
hypothesis that `A7Y6ValuesProp` needs). -/
theorem deg6_package {G : Type} [Group G] [Finite G]
    (hTab : A7TableLemmaProp) (hC1b : A7C1bProp) (hBr : A7BridgeProp)
    (hCnt : A7InvolutionCounts2Prop)
    (S : Sylow 2 G) (z : G) (U V : Subgroup G) (hyps : A7RecHyps G S z U V)
    (honeG : OneInvClass G) {σ : G} (hσU : σ ∈ U) (hσ1 : σ ≠ 1) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (ρ : Representation ℂ G W),
      Representation.IsIrreducible ρ ∧ Module.finrank ℂ W = 6 ∧
      LinearMap.trace ℂ W (ρ z) = 2 ∧ LinearMap.trace ℂ W (ρ (z * σ)) = -1 ∧
      (∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']
        (ρ' : Representation ℂ G W'), Representation.IsIrreducible ρ' →
        Module.finrank ℂ W' = 6 →
        ∀ g : G, LinearMap.trace ℂ W' (ρ' g) = LinearMap.trace ℂ W (ρ g)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let ctx : A7RecCtx G := A7RecCtx.ofHyps hyps
  have hcard : Nat.card G = 2520 := ctx.hcard
  have hz2 : orderOf z = 2 := ctx.hz2
  have hC24 : Nat.card (Subgroup.centralizer ({z} : Set G)) = 24 :=
    Basic.card_centralizer_z G ctx
  obtain ⟨π, hπS, hπ4, hπC, _⟩ := Basic.exists_tau_order_four G ctx
  obtain ⟨hcπ, hcz, hczσ⟩ := hCnt G ctx π σ hσU hσ1 hπS hπ4 hπC
  obtain ⟨n, ι, f, e, a, b, hinj, hntriv, hoff, hdeg, hπv, hzv, hzσv, hnz, hf2, hfdiv,
    he2, ha2, hb2, hea, heb, hab, h1e, h1a, h1b, hcong, hle⟩ :=
    hC1b G S z U V π σ hyps honeG hσU hσ1 hπS hπ4 hπC
  have hconj : ∀ x : G, orderOf x = 2 → IsConj x z := fun x hx => honeG x z hx hz2
  -- the bridge states its value hypotheses with the coercions distributed
  have hzv' : ∀ i, (ι i : ClassFunction G ℂ) z = (b i : ℂ) - 2 * (a i : ℂ) := by
    intro i
    rw [hzv i]
    push_cast
    ring
  have hzσv' : ∀ i, (ι i : ClassFunction G ℂ) (z * σ) = (a i : ℂ) + (b i : ℂ) := by
    intro i
    rw [hzσv i]
    push_cast
    ring
  obtain ⟨hr1, hr2, hr3⟩ := hBr G z π σ hcard hz2 hC24 hconj hcπ hcz hczσ n ι f e a b
    hinj hntriv hoff hdeg hπv hzv' hzσv'
  obtain ⟨hsum2520, i0, hf6, _, ha0, hb0, hno6⟩ :=
    hTab n f e a b hnz hf2 (fun i => Int.ofNat_dvd.mp (hfdiv i)) he2 ha2 hb2 hea heb hab
      h1e h1a h1b hcong hr1 hr2 hr3 hle
  set χ : IrreducibleCharacter G := ι i0 with hχdef
  have hχ1 : (χ : ClassFunction G ℂ) 1 = 6 := by
    rw [hχdef, hdeg i0, hf6]
    norm_num
  obtain ⟨W, hAC, hMod, hFD, ρ, hρirr, hχeq⟩ := χ.isIrreducible
  letI : AddCommGroup W := hAC
  letI : Module ℂ W := hMod
  letI : FiniteDimensional ℂ W := hFD
  have hdim : Module.finrank ℂ W = 6 := by
    have h1 : (χ : ClassFunction G ℂ) 1 = (Module.finrank ℂ W : ℂ) := by
      rw [congrFun hχeq 1]
      exact ρ.char_one
    rw [hχ1] at h1
    exact_mod_cast h1.symm
  have hztr : LinearMap.trace ℂ W (ρ z) = 2 := by
    have h2 : (χ : ClassFunction G ℂ) z = LinearMap.trace ℂ W (ρ z) := by
      rw [congrFun hχeq z]
      rfl
    have h1 : (χ : ClassFunction G ℂ) z = ((b i0 - 2 * a i0 : ℤ) : ℂ) := by
      rw [hχdef]
      exact hzv i0
    rw [← h2, h1, ha0, hb0]
    norm_num
  have hzσtr : LinearMap.trace ℂ W (ρ (z * σ)) = -1 := by
    have h2 : (χ : ClassFunction G ℂ) (z * σ) = LinearMap.trace ℂ W (ρ (z * σ)) := by
      rw [congrFun hχeq (z * σ)]
      rfl
    have h1 : (χ : ClassFunction G ℂ) (z * σ) = ((a i0 + b i0 : ℤ) : ℂ) := by
      rw [hχdef]
      exact hzσv i0
    rw [← h2, h1, ha0, hb0]
    norm_num
  have huniq : ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']
      (ρ' : Representation ℂ G W'), Representation.IsIrreducible ρ' → Module.finrank ℂ W' = 6 →
      ∀ g : G, LinearMap.trace ℂ W' (ρ' g) = LinearMap.trace ℂ W (ρ g) := by
    intro W' _ _ _ ρ' hρ'irr h6' g
    let χ' : IrreducibleCharacter G :=
      ⟨repCharacterClassFunction ρ',
        ⟨W', inferInstance, inferInstance, inferInstance, ρ', hρ'irr, rfl⟩⟩
    have hχ'1 : (χ' : ClassFunction G ℂ) 1 = 6 := by
      have h1 : (χ' : ClassFunction G ℂ) 1 = (Module.finrank ℂ W' : ℂ) := by
        show (repCharacterClassFunction ρ' : G → ℂ) 1 = _
        rw [repCharacterClassFunction_apply, ρ'.char_one]
      rw [h1, h6']
      norm_num
    obtain ⟨j, hj⟩ := irr_deg_six_mem_range n ι f hcard hinj hntriv hdeg hsum2520 χ' hχ'1
    have hfj : f j = 6 := by
      have h1 : (f j : ℂ) = (6 : ℂ) := by
        rw [← hdeg j, hj, hχ'1]
      exact_mod_cast h1
    have hji : j = i0 := by
      by_contra h
      exact hno6 j h hfj
    have hχ'eq : χ' = χ := by
      rw [← hj, hji, hχdef]
    have h1 : LinearMap.trace ℂ W' (ρ' g) = (χ' : ClassFunction G ℂ) g := by
      show LinearMap.trace ℂ W' (ρ' g) = (repCharacterClassFunction ρ' : G → ℂ) g
      rw [repCharacterClassFunction_apply]
      rfl
    have h2 : (χ : ClassFunction G ℂ) g = LinearMap.trace ℂ W (ρ g) := by
      rw [congrFun hχeq g]
      rfl
    rw [h1, hχ'eq, h2]
  exact ⟨W, hAC, hMod, hFD, ρ, hρirr, hdim, hztr, hzσtr, huniq⟩

theorem a7Char6_of_table
    (hone : ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
      Work.A7REC.A7RecHyps G S z U V → Work.A7REC.OneInvClass G)
    (hTab : Work.A7REC.A7TableLemmaProp) (hC1b : Work.A7REC.A7C1bProp)
    (hBr : Work.A7REC.A7BridgeProp) (hCnt : Work.A7REC.A7InvolutionCounts2Prop)
    (hY6 : Work.A7REC.A7Y6ValuesProp) : Work.A7REC.A7Char6Prop := by
  intro G instG instF S z U V hyps
  letI : Group G := instG
  letI : Finite G := instF
  haveI : Fintype G := Fintype.ofFinite G
  let ctx : A7RecCtx G := A7RecCtx.ofHyps hyps
  have honeG : OneInvClass G := hone G S z U V hyps
  have hsimple : IsSimpleGroup G := hyps.1
  have hcard : Nat.card G = 2520 := hyps.2.1
  have hz2 : orderOf z = 2 := hyps.2.2.2.2.1
  have hU3 : Nat.card U = 3 := hyps.2.2.2.2.2.2.2.1
  have hCz : Subgroup.centralizer ({z} : Set G) = U ⊔ (S : Subgroup G) :=
    hyps.2.2.2.2.2.2.1
  -- a fixed non-identity element of `U`, used to produce the representation
  obtain ⟨σ, hσU, hσ1⟩ : ∃ σ : G, σ ∈ U ∧ σ ≠ 1 := by
    haveI : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [hU3]; norm_num)
    obtain ⟨a, ha⟩ := exists_ne (1 : U)
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  obtain ⟨W, hAC, hMod, hFD, ρ, hρirr, h6, hztr, hzσtr, huniq⟩ :=
    deg6_package hTab hC1b hBr hCnt S z U V hyps honeG hσU hσ1
  letI : AddCommGroup W := hAC
  letI : Module ℂ W := hMod
  letI : FiniteDimensional ℂ W := hFD
  -- a non-identity element of `U` has order `3` and commutes with `z`
  have horder : ∀ u ∈ U, u ≠ 1 → orderOf u = 3 := by
    intro u hu hu1
    have hdvd : orderOf u ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (α := G) (Subgroup.zpowers_le.mpr hu)
      rwa [Nat.card_zpowers, hU3] at h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hu1
    · exact h3
  have hcommute : ∀ u ∈ U, z * u = u * z := by
    intro u hu
    have hC : u ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [hCz]
      exact Subgroup.mem_sup_left hu
    exact Subgroup.mem_centralizer_iff.mp hC z (Set.mem_singleton z)
  -- the values at the order-`7` elements
  have horder7 : ∀ x : G, orderOf x = 7 → LinearMap.trace ℂ W (ρ x) = -1 := by
    obtain ⟨τ, hτ2, hτσ⟩ := Basic.exists_involution_inverting ctx hσU hσ1
    exact (hY6 G z σ W ρ hsimple hcard hz2 (horder σ hσU hσ1) (hcommute σ hσU) hρirr h6
      hztr hzσtr ⟨τ, hτ2, hτσ⟩ huniq).2
  refine ⟨W, hAC, hMod, hFD, ρ, h6, hztr, ?_, horder7⟩
  -- the values on `U^#`: run the construction for `u` and transfer the value at `z * u`
  intro u hu hu1
  obtain ⟨Wu, hACu, hModu, hFDu, ρu, hρuirr, h6u, _hzu, hzutr, huniqu⟩ :=
    deg6_package hTab hC1b hBr hCnt S z U V hyps honeG hu hu1
  letI : AddCommGroup Wu := hACu
  letI : Module ℂ Wu := hModu
  letI : FiniteDimensional ℂ Wu := hFDu
  have hzu : LinearMap.trace ℂ W (ρ (z * u)) = -1 := by
    rw [← huniq Wu ρu hρuirr h6u (z * u)]
    exact hzutr
  obtain ⟨τu, hτu2, hτuσ⟩ := Basic.exists_involution_inverting ctx hu hu1
  exact (hY6 G z u W ρ hsimple hcard hz2 (horder u hu hu1) (hcommute u hu) hρirr h6 hztr hzu
    ⟨τu, hτu2, hτuσ⟩ huniq).1

end Work.A7REC.Char
