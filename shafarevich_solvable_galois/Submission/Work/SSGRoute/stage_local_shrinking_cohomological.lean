import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Have
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.involution_clause_conj_transfer
import Submission.Work.SSGRoute.involution_clause_of_mem_fixingSubgroup

namespace Work.SSGRoute

open Work.CohomologicalShrinking

open scoped TensorProduct

set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas

The assembly below rests on the following pieces:

* `Work.SSGRoute.level_n_of_cocycle_killed` — the generalisation of
  `Work.SSGRoute.local_level_n_of_class_killed` to an arbitrary subgroup `Δ ≤ Gal(K/ℚ)` equipped
  with a homomorphism `ρ : ↥Δ →* Γ_m(τ)` lifting the inclusion (proved in this file by adapting
  the proof of the place-wise statement).
* `Work.SSGRoute.exists_zpowersHom_of_orderOf_dvd` — the cyclic generator homomorphism (proved in
  this file, via Mathlib's `monoidHomOfForallMemZpowers`).
* `Work.SSGRoute.involution_clause_of_mem_fixingSubgroup` — clause (B) in the degenerate case
  (separate module).
* `Work.SSGRoute.involution_clause_conj_transfer` — transfer of a clause-(B) lift along conjugacy
  (separate module).
* `Work.SSGRoute.kerSuccCocycle_kerIso_mem_Z2` — the transported section cocycle of an arbitrary
  subgroup is a `2`-cocycle (proved in this file).

## The assembly

The family of subgroups of the shrinking is `H' : Option ↥S' → Subgroup Gal(K/ℚ)`, with

* `H' (some A) = (decomp ℚ A).map (restrictNormalHom K)` for a representative `A` of a `T¹`-place
  (carrying the local class `localKappa`),
* `H' none = Subgroup.zpowers (res c₀)` for the image of a chosen involution `c₀ ∉ K.fixingSubgroup`
  (carrying the transported section cocycle, a class in `H²(⟨res c₀⟩, E(m,τ)) ≅ H²(G, E(m,τ) ⊗
  Ind_{⟨res c₀⟩}^G 𝔽_p)`).

`shapiro_packaging_natural` for this single family packages *both* kinds of local classes into
`T = shapiroT p G (Option ↥S') H'`, so that the single application of
`exists_shrinking_H2_tate` (Proposition 6) produces *one* `Φ` that kills the `T¹`-classes and the
involution class simultaneously; `level_n_of_cocycle_killed` then converts the vanishing of the
involution class into a lift of `Ψ = (flowGroupMap Φ).comp φ` over `⟨res c₀⟩`, which is transported
back to `⟨c₀⟩` and, along conjugacy (`involutions_eq_one_or_conjugate`), to every other involution
of `G_ℚ`.  If there is no involution outside `K.fixingSubgroup` at all, clause (B) is trivial and
clause (A) alone (via `clause_A_of_prop5Data_exists`) suffices. -/

/-- **The level-`n` splitting criterion over an arbitrary subgroup.**  This is
`Work.SSGRoute.local_level_n_of_class_killed` with the place `A` (and `localPhi`, `localKappa`)
replaced by an arbitrary subgroup `Δ ≤ Gal(K/ℚ)` and a homomorphism `ρ` lifting the inclusion. -/
theorem level_n_of_cocycle_killed (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (i j m n : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[ℚ] K) T]
    [SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T]
    (Δ : Subgroup (K ≃ₐ[ℚ] K))
    (ρ : ↥Δ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hρ : ∀ σ : ↥Δ, flowQuot p (K ≃ₐ[ℚ] K) m i j (ρ σ) = (σ : K ≃ₐ[ℚ] K))
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (ev : E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T →ₗ[ZMod p] E p (K ≃ₐ[ℚ] K) m i j)
    (C : (K ≃ₐ[ℚ] K) × (K ≃ₐ[ℚ] K) → E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T)
    (hCval : ∀ h h' : ↥Δ,
      ev (C ((h : K ≃ₐ[ℚ] K), (h' : K ≃ₐ[ℚ] K)))
        = kerIso p K i j m (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j ρ
            (flowGroupSection p (K ≃ₐ[ℚ] K) m i j)
            (flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j) h h'))
    (hkill : Work.GroupCohomology.mapCochain2 (K ≃ₐ[ℚ] K)
        ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) C
      ∈ Work.GroupCohomology.B2 (K ≃ₐ[ℚ] K) (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T))
    (hev : ∀ (h : ↥Δ) (z : E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T),
      ev ((h : K ≃ₐ[ℚ] K) • z) = (h : K ≃ₐ[ℚ] K) • ev z)
    (evθ : E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T →ₗ[ZMod p] E p (K ≃ₐ[ℚ] K) n i j)
    (hevθ : ∀ (h : ↥Δ) (z : E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T),
      evθ ((h : K ≃ₐ[ℚ] K) • z) = (h : K ≃ₐ[ℚ] K) • evθ z)
    (hnat : ∀ z : E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T,
      evθ ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T z)
        = gradedMapLin p Φ.toHom Φ.surjective i j (ev z)) :
    ∃ l : ↥Δ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
      (∀ x : ↥Δ, SSGRoute.LiftsFlowAt (l x)
        (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp ρ) x)) ∧
      (∀ x : ↥Δ, (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp ρ) x) = 1 → l x = 1) := by
  classical
  let θ : E p (K ≃ₐ[ℚ] K) m i j →ₗ[ZMod p] E p (K ≃ₐ[ℚ] K) n i j :=
    gradedMapLin p Φ.toHom Φ.surjective i j
  let ρn : ↥Δ →* flowGroup p (K ≃ₐ[ℚ] K) n i j :=
    (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp ρ
  let s : flowGroup p (K ≃ₐ[ℚ] K) m i j →
      flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2 :=
    flowGroupSection p (K ≃ₐ[ℚ] K) m i j
  let s' : flowGroup p (K ≃ₐ[ℚ] K) n i j →
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 :=
    flowGroupSection p (K ≃ₐ[ℚ] K) n i j
  have hs : ∀ x, flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (s x) = x :=
    flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j
  have hs' : ∀ x, flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (s' x) = x :=
    flowGroupSucc_section p (K ≃ₐ[ℚ] K) n i j
  have h1s : s 1 = 1 := flowGroupSection_one p (K ≃ₐ[ℚ] K) m i j
  have h1s' : s' 1 = 1 := flowGroupSection_one p (K ≃ₐ[ℚ] K) n i j
  let κ : ↥Δ × ↥Δ → E p (K ≃ₐ[ℚ] K) m i j :=
    fun q => kerIso p K i j m (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j ρ s hs q.1 q.2)
  have hρn : ∀ σ : ↥Δ, ρn σ = flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (ρ σ) := fun σ => rfl
  -- the flow quotient of `ρn` is the subgroup inclusion
  have hflow : ∀ σ : ↥Δ, flowQuot p (K ≃ₐ[ℚ] K) n i j (ρn σ) = (σ : K ≃ₐ[ℚ] K) := by
    intro σ
    show flowQuot p (K ≃ₐ[ℚ] K) n i j
      (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (ρ σ)) = (σ : K ≃ₐ[ℚ] K)
    rw [flowQuot_flowGroupMap]
    exact hρ σ
  -- the Δ-module structures on the coefficient modules (via the subgroup inclusion)
  letI instT : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  letI instTn : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  letI instEm : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) m i j) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  letI instEn : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  -- (A) `θ ∘ κ` is a `2`-coboundary on `Δ`
  have hAB2 : (fun q : ↥Δ × ↥Δ => θ (κ q))
      ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) := by
    have hres : (fun q : ↥Δ × ↥Δ => θ.rTensor T (C (q.1, q.2)))
        ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T) :=
      mem_B2_restrict (Hc := Δ) (hact := fun σ z => rfl) (c := fun q : (K ≃ₐ[ℚ] K) × (K ≃ₐ[ℚ] K) => θ.rTensor T (C q)) hkill
    let evθa : E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T →+ E p (K ≃ₐ[ℚ] K) n i j := evθ
    have hevθ' : ∀ (σ : ↥Δ) (z : E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T),
        evθa (σ • z) = σ • evθa z := fun σ z => hevθ σ z
    have hpush : (fun q : ↥Δ × ↥Δ => evθ (θ.rTensor T (C (q.1, q.2))))
        ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) :=
      Work.GroupCohomology.mapCochain2_mem_B2 ↥Δ evθa hevθ' hres
    have hfun : (fun q : ↥Δ × ↥Δ => evθ (θ.rTensor T (C (q.1, q.2))))
        = fun q : ↥Δ × ↥Δ => θ (κ q) := by
      funext q
      obtain ⟨σ, τ⟩ := q
      rw [hnat (C ((σ : K ≃ₐ[ℚ] K), (τ : K ≃ₐ[ℚ] K))), hCval σ τ]
    rw [hfun] at hpush
    exact hpush
  -- (B) the naturality of the section cocycle: the level-`n` cocycle over `Δ` is cohomologous to
  -- `θ ∘ κ`
  let δ : ↥Δ → E p (K ≃ₐ[ℚ] K) n i j := fun σ => kerIso p K i j n (Additive.ofMul
    (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ ρ ρn hρn s s' hs hs' σ))
  have hker : (fun q : ↥Δ × ↥Δ => kerIso p K i j n
      (kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' q.1 q.2))
      ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) := by
    have hd1 : Work.GroupCohomology.d1 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) δ
        ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) := ⟨δ, rfl⟩
    have hdiff := sub_mem hAB2 hd1
    have heq : (fun q : ↥Δ × ↥Δ => θ (κ q))
        - Work.GroupCohomology.d1 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) δ
        = fun q : ↥Δ × ↥Δ => kerIso p K i j n
            (kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' q.1 q.2) := by
      funext q
      obtain ⟨σ, τ⟩ := q
      have hnat' := kerSuccCocycle_naturality p (K ≃ₐ[ℚ] K) m n i j Φ ρ ρn hρn s hs s' hs' σ τ
      have h1 := congrArg (kerIso p K i j n) hnat'
      simp only [map_add, map_sub] at h1
      show θ (κ (σ, τ)) - (σ • δ τ - δ (σ * τ) + δ σ)
        = kerIso p K i j n (kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' σ τ)
      rw [h1]
      -- simplify the three `kerIso` images of the correction cochain and the first term
      have hκeq : kerIso p K i j n (Additive.ofMul
            (flowGroupSuccKernelMap p (K ≃ₐ[ℚ] K) i j Φ
              (kerSuccCocycleMul p (K ≃ₐ[ℚ] K) m i j ρ s hs σ τ)))
          = θ (κ (σ, τ)) := by
        rw [kerIso_naturality p K i j m n Φ (kerSuccCocycleMul p (K ≃ₐ[ℚ] K) m i j ρ s hs σ τ)]
        show gradedMapLin p Φ.toHom Φ.surjective i j
            (kerIso p K i j m (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j ρ s hs σ τ))
          = gradedMapLin p Φ.toHom Φ.surjective i j (κ (σ, τ))
        rfl
      have hconj : kerIso p K i j n (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
            (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) (s' (ρn σ))
            (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ ρ ρn hρn s s' hs hs' τ)))
          = σ • δ τ := by
        rw [kerIso_conjKernelMul]
        show (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (s' (ρn σ))).right • δ τ = σ • δ τ
        rw [hs' (ρn σ)]
        show (flowQuot p (K ≃ₐ[ℚ] K) n i j (ρn σ)) • δ τ = σ • δ τ
        rw [hflow σ]
        show (σ : K ≃ₐ[ℚ] K) • δ τ = (σ : K ≃ₐ[ℚ] K) • δ τ
        rfl
      have hlast : kerIso p K i j n (Additive.ofMul
            (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ ρ ρn hρn s s' hs hs' (σ * τ))) = δ (σ * τ) := rfl
      have hlast2 : kerIso p K i j n (Additive.ofMul
            (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ ρ ρn hρn s s' hs hs' σ)) = δ σ := rfl
      rw [hκeq, hconj, hlast, hlast2]
    rw [heq] at hdiff
    exact hdiff
  -- (C) transfer to the kernel coefficients and apply the splitting criterion
  letI : CommGroup ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker :=
    { (inferInstance : Group ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) with
      mul_comm := flowGroupSucc_ker_comm p (K ≃ₐ[ℚ] K) n i j }
  letI : DistribMulAction (flowGroup p (K ≃ₐ[ℚ] K) n i j)
      (Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) :=
    Work.AbsoluteGalois.kernelAction (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) s' hs' h1s'
      (flowGroupSucc_ker_comm p (K ≃ₐ[ℚ] K) n i j)
  letI : DistribMulAction ↥Δ (Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) :=
    DistribMulAction.compHom _ ρn
  have hkerK : (fun q : ↥Δ × ↥Δ => kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' q.1 q.2)
      ∈ Work.GroupCohomology.B2 ↥Δ (Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) := by
    have hφeq : ∀ (h : ↥Δ) (a : Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker),
        kerIso p K i j n (h • a) = h • kerIso p K i j n a := by
      intro h a
      show kerIso p K i j n (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
          (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) (s' (ρn h)) (Additive.toMul a)))
        = (h : K ≃ₐ[ℚ] K) • kerIso p K i j n (Additive.ofMul (Additive.toMul a))
      rw [kerIso_conjKernelMul]
      show (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (s' (ρn h))).right
          • kerIso p K i j n (Additive.ofMul (Additive.toMul a)) = (h : K ≃ₐ[ℚ] K) • _
      rw [hs' (ρn h)]
      show (flowQuot p (K ≃ₐ[ℚ] K) n i j (ρn h)) • kerIso p K i j n
          (Additive.ofMul (Additive.toMul a)) = (h : K ≃ₐ[ℚ] K) • _
      rw [hflow h]
    have hbij : Function.Bijective (kerIso p K i j n).toAddMonoidHom :=
      (kerIso p K i j n).bijective
    exact (mem_B2_mapCochain2_iff (kerIso p K i j n).toAddMonoidHom hφeq hbij
      (fun q : ↥Δ × ↥Δ => kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' q.1 q.2)).mpr hker
  -- the splitting criterion gives the lift over `Δ`
  obtain ⟨ψ, hψ⟩ := (exists_lift_iff_kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' h1s'
      (flowGroupSucc_ker_comm p (K ≃ₐ[ℚ] K) n i j)).mpr hkerK
  refine ⟨ψ, ?_, ?_⟩
  · intro x
    exact (liftsFlowAt_iff_flowGroupSucc p K n i j _ _).mpr (DFunLike.congr_fun hψ x)
  · intro x hx
    have hx1 : x = 1 := by
      apply Subtype.ext
      have h := hflow x
      rw [hx, map_one] at h
      exact h.symm
    show ψ x = 1
    rw [hx1, map_one]

/-- The homomorphism out of the cyclic subgroup generated by `g` sending `g` to `x`, when
`orderOf x` divides `orderOf g`. -/
theorem exists_zpowersHom_of_orderOf_dvd {G H : Type*} [Group G] [Group H] (g : G) (x : H)
    (hx : orderOf x ∣ orderOf g) :
    ∃ ρ : ↥(Subgroup.zpowers g) →* H, ρ ⟨g, Subgroup.mem_zpowers g⟩ = x := by
  have hgen : ∀ y : ↥(Subgroup.zpowers g),
      y ∈ Subgroup.zpowers (⟨g, Subgroup.mem_zpowers g⟩ : ↥(Subgroup.zpowers g)) := by
    intro y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      simpa using hk⟩
  have hdvd : orderOf x ∣ orderOf (⟨g, Subgroup.mem_zpowers g⟩ : ↥(Subgroup.zpowers g)) := by
    rw [Subgroup.orderOf_mk]
    exact hx
  exact ⟨monoidHomOfForallMemZpowers hgen hdvd, monoidHomOfForallMemZpowers_apply_gen hgen hdvd⟩

/-- The transported section cocycle of an arbitrary subgroup `Δ ≤ Gal(K/ℚ)` (equipped with a
homomorphism `ρ : ↥Δ →* Γ_m(τ)` lifting the inclusion) is a `2`-cocycle with values in `E(m,τ)`.
This is `Work.SSGRoute.exists_localCocycle` with the decomposition group of a place replaced by an
arbitrary subgroup. -/
theorem kerSuccCocycle_kerIso_mem_Z2 (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (i j m : ℕ)
    (Δ : Subgroup (K ≃ₐ[ℚ] K))
    (ρ : ↥Δ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hρ : ∀ σ : ↥Δ, flowQuot p (K ≃ₐ[ℚ] K) m i j (ρ σ) = (σ : K ≃ₐ[ℚ] K)) :
    (letI : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) m i j) :=
        DistribMulAction.compHom _ (Subgroup.subtype Δ)
     (fun x : ↥Δ × ↥Δ => kerIso p K i j m (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j ρ
        (flowGroupSection p (K ≃ₐ[ℚ] K) m i j)
        (flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j) x.1 x.2))
       ∈ Work.GroupCohomology.Z2 ↥Δ (E p (K ≃ₐ[ℚ] K) m i j)) := by
  letI : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) m i j) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  have hcomm : ∀ a b : ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker, a * b = b * a :=
    fun a b => (flowGroupSucc_ker_isMulCommutative p (K ≃ₐ[ℚ] K) m i j).is_comm.comm a b
  have hmain := kerSuccCocycle_transport_mem_Z2 (p := p) (G := K ≃ₐ[ℚ] K) m i j
    (H := ↥Δ) ρ (flowGroupSection p (K ≃ₐ[ℚ] K) m i j)
    (flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j)
    (flowGroupSection_one p (K ≃ₐ[ℚ] K) m i j) hcomm
    (kerIso p K i j m) (kerIso_equivariant p K i j m)
  have hψ : (flowQuot p (K ≃ₐ[ℚ] K) m i j).comp ρ = (Subgroup.subtype Δ : ↥Δ →* K ≃ₐ[ℚ] K) :=
    MonoidHom.ext (fun h => hρ h)
  have hact : DistribMulAction.compHom (E p (K ≃ₐ[ℚ] K) m i j)
        ((flowQuot p (K ≃ₐ[ℚ] K) m i j).comp ρ)
      = DistribMulAction.compHom (E p (K ≃ₐ[ℚ] K) m i j) (Subgroup.subtype Δ) :=
    congrArg _ hψ
  rw [hact] at hmain
  exact hmain

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Same statement as `Work.SSGRoute.stage_local_shrinking`, but clause (B) — the involutions — must be obtained by the *same* Shapiro/Proposition-6 shrinking as clause (A), NOT by the two-torsion group-theoretic route.  Reason: the group-theoretic atom used by `stage_local_shrinking` for clause (B) (`gradedStep_diagonal` / the `LiftingAux.GradedStep` / `GradedStep` family) is (most probably) FALSE; see `Submission/Work/SSGRoute/AUDIT_p2_two_torsion_atom.lean.md` and `DIAGONAL_STATUS.md` §§4, 11, 12: at `(j,n) = (8,1)` the graded piece `E(8,8) ≅ L_8` has `dim L_8^σ = 16` while the norm image spans at most `15`.  Do not import `two_torsion_lift_two` / `two_torsion_bridge` / `gradedStep_j_ge_two` / `gradedStep_diagonal`.

Clause (A) is available verbatim: `Work.SSGRoute.clause_A_of_prop5Data_exists` (declared in `Submission/Work/SSGRoute/stage_local_shrinking.lean`, sorry-free and axiom-clean — importing that module is fine as long as this file's proof does not use the module's clause-(B) route).  The paper (Schmidt–Wingberg §5, Step 1a) handles the real places by putting them into the *same* shrinking: "we may replace the module `T` by the direct sum of `Ind_{D_v}^G 𝔽_p`, where `v` runs through `Ram(K|k) ∪ S_p ∪ S_1`".

Three practical points for the prover.  (1) `clause_A_of_prop5Data_exists` hardwires its module (`T := shapiroT p G ↥S' Hsub`) inside its own proof, so the augmented-`T` construction must be redone (or that result generalised) in order that ONE `Φ` serves both clauses: apply `Work.CohomologicalShrinking.exists_shrinking_H2_tate` to `T := shapiroT … ⊕ Ind_{⟨c⟩}^G 𝔽_p`, killing the `T¹`-classes *and* the involution classes at once.  (2) The statement quantifies over *all* involutions `c`; all involutions of `G_ℚ` are conjugate, so the chosen `c₀` plus a conjugacy transfer (as in `local_clause_conj_transfer`, used by clause (A)) covers the general case.  (3) `IsT1Place` concerns *finite* places only, so clause (B) is not covered by clause (A).  For the involution: if the pushed solution `Ψ = flowGroupMap Φ ∘ φ` satisfies `Ψ c = 1` take `l := 1`; otherwise `⟨c⟩ ≅ ℤ/2` and `ker(Ψ|⟨c⟩) = ⊥`, so any lift kills the kernel, and the lift exists because the local class — the restriction of the section cocycle `κ` to `⟨c⟩ ⊆ G_ℚ`, a class in `H²(⟨c⟩, E(m,τ)) ≅ H²(G, E(m,τ) ⊗ Ind_{⟨c⟩}^G 𝔽_p)` — has been killed by the shrinking. -/
theorem stage_local_shrinking_cohomological (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i) (n : ℕ) (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j,
        SSGRoute.IsScholzSolution p K m i j φ →
        ∃ Φ : Work.CohomologicalShrinking.OperatorMap (K ≃ₐ[ℚ] K) m n,
          (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
            ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
                  (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
              (∀ σ : ↥(SSGRoute.decomp ℚ A),
                SSGRoute.LiftsFlowAt (l σ)
                  (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) ∧
              (∀ σ : ↥(SSGRoute.decomp ℚ A),
                ((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ = 1 → l σ = 1)) ∧
          (∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
            ∃ l : ↥(Subgroup.zpowers c) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
                  (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
              (∀ σ : ↥(Subgroup.zpowers c),
                SSGRoute.LiftsFlowAt (l σ)
                  (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) ∧
              (∀ σ : ↥(Subgroup.zpowers c),
                ((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ = 1 → l σ = 1)) := by
  classical
  haveI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ ↥K
  obtain ⟨D⟩ := prop5Data_exists p (K ≃ₐ[ℚ] K) i j hj hji
  by_cases hmain : ∃ c₀ : SSGRoute.GalQ, c₀ ^ 2 = 1 ∧ c₀ ∉ K.fixingSubgroup
  · obtain ⟨c₀, hc₀sq, hc₀fix⟩ := hmain
    have hc₀res : AlgEquiv.restrictNormalHom K c₀ ≠ 1 := by
      intro h1
      exact hc₀fix ((@restrictNormalHom_eq_one_iff_mem_fixingSubgroup ℚ SSGRoute.QBar _ _ _
        K ‹Normal ℚ K› c₀).mp h1)
    have hc₀ne : c₀ ≠ 1 := by
      intro h1
      exact hc₀fix (h1 ▸ K.fixingSubgroup.one_mem)
    have hordσ : orderOf (AlgEquiv.restrictNormalHom K c₀) = 2 := by
      refine orderOf_eq_prime ?_ hc₀res
      rw [← map_pow, hc₀sq, map_one]
    obtain ⟨S, hSfin, hSdisj, hShit⟩ := exists_representatives (p := p) K
    let S' : Finset (ValuationSubring SSGRoute.QBar) :=
      S.filter (fun A => SSGRoute.IsT1Place p K A)
    let Hinv : Subgroup (K ≃ₐ[ℚ] K) := Subgroup.zpowers (AlgEquiv.restrictNormalHom K c₀)
    let ι' : Type _ := Option ↥S'
    let H' : ι' → Subgroup (K ≃ₐ[ℚ] K) := fun a => match a with
      | some A => (SSGRoute.decomp ℚ A.1).map (AlgEquiv.restrictNormalHom K)
      | none => Hinv
    let T : Type _ := shapiroT p (K ≃ₐ[ℚ] K) ι' H'
    obtain ⟨m₀, hm₀n, hm₀⟩ :=
      exists_shrinking_H2_tate p (K ≃ₐ[ℚ] K) hj D T (Fintype.card ι') hn
    refine ⟨m₀, hm₀n, ?_⟩
    intro m hm φ hφ
    -- the homomorphism `ρ : ↥⟨res c₀⟩ →* Γ_m(τ)` sending the generator to `φ c₀`
    have hφc₀dvd : orderOf (φ c₀) ∣ orderOf (AlgEquiv.restrictNormalHom K c₀) := by
      rw [hordσ]
      exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, hc₀sq, map_one])
    obtain ⟨ρ, hρgen⟩ :=
      exists_zpowersHom_of_orderOf_dvd (AlgEquiv.restrictNormalHom K c₀) (φ c₀) hφc₀dvd
    have hρ : ∀ σ : ↥Hinv, flowQuot p (K ≃ₐ[ℚ] K) m i j (ρ σ) = (σ : K ≃ₐ[ℚ] K) := by
      intro σ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
      have hσeq : σ = (⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩ : ↥Hinv) ^ k :=
        Subtype.ext (by simpa using hk.symm)
      have hcoe : ((σ : K ≃ₐ[ℚ] K)) = (AlgEquiv.restrictNormalHom K c₀) ^ k := by
        rw [hσeq]
        exact map_zpow (Subgroup.subtype Hinv) _ k
      rw [hcoe]
      have hρpow : ρ σ = (φ c₀) ^ k := by rw [hσeq, map_zpow, hρgen]
      rw [hρpow, map_zpow]
      rw [show flowQuot p (K ≃ₐ[ℚ] K) m i j (φ c₀) = AlgEquiv.restrictNormalHom K c₀ from
        hφ.1.2.2 c₀]
    -- the packaged family of `2`-cocycles
    let κ : ∀ a : ι', ↥(H' a) × ↥(H' a) → E p (K ≃ₐ[ℚ] K) m i j := fun a => match a with
      | some A => localKappa p K i j m φ hφ A.1 (Finset.mem_filter.mp A.2).2
      | none => fun q => kerIso p K i j m (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j ρ
          (flowGroupSection p (K ≃ₐ[ℚ] K) m i j)
          (flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j) q.1 q.2)
    have hκ : ∀ a : ι',
        (letI : DistribMulAction ↥(H' a) (E p (K ≃ₐ[ℚ] K) m i j) :=
          DistribMulAction.compHom _ (Subgroup.subtype _)
         κ a ∈ Work.GroupCohomology.Z2 (↥(H' a)) (E p (K ≃ₐ[ℚ] K) m i j)) := by
      intro a
      cases a with
      | some A => exact localKappa_mem_Z2 p K i j m φ hφ A.1 (Finset.mem_filter.mp A.2).2
      | none => exact kerSuccCocycle_kerIso_mem_Z2 p K i j m Hinv ρ hρ
    obtain ⟨ev, hev, C, hC, hCval, hnat⟩ :=
      shapiro_packaging_natural p (K ≃ₐ[ℚ] K) ι' H' (E p (K ≃ₐ[ℚ] K) m i j) κ hκ
    let clsA : ι' → Work.GroupCohomology.H2 (K ≃ₐ[ℚ] K)
        (E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T) :=
      fun a => Work.GroupCohomology.H2π (K ≃ₐ[ℚ] K)
        (E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T) ⟨C a, hC a⟩
    let cls : Fin (Fintype.card ι') → Work.GroupCohomology.H2 (K ≃ₐ[ℚ] K)
        (E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T) :=
      fun k => clsA ((Fintype.equivFin ι').symm k)
    obtain ⟨Φ, hΦ⟩ := hm₀ m hm cls
    have hclsA_eval : ∀ a : ι', cls (Fintype.equivFin ι' a) = clsA a := by
      intro a
      simp only [cls, Equiv.symm_apply_apply]
    -- the involution data: the naturality at level `n` and the built-in evaluation maps
    obtain ⟨evθ0, hevθ0, hnat0⟩ := hnat (E p (K ≃ₐ[ℚ] K) n i j)
      (gradedMapLin p Φ.toHom Φ.surjective i j)
      (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x)
    have hkill0 : Work.GroupCohomology.mapCochain2 (K ≃ₐ[ℚ] K)
        ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) (C none)
        ∈ Work.GroupCohomology.B2 (K ≃ₐ[ℚ] K) (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T) :=
      h2Map_eq_zero_iff_B2 (p := p) (G := K ≃ₐ[ℚ] K) (i := i) (j := j) (m := m) (n := n)
        (T := T) Φ ⟨C none, hC none⟩ (by
          have hh := hΦ (Fintype.equivFin ι' none)
          rwa [hclsA_eval none] at hh)
    obtain ⟨lσ, hlσlift, hlσker⟩ := level_n_of_cocycle_killed p K i j m n T Hinv ρ hρ Φ
      (ev none) (C none) (fun h h' => hCval none h h') hkill0 (hev none)
      (evθ0 none) (hevθ0 none) (fun z => hnat0 none z)
    -- the lift over `⟨c₀⟩`
    have hσ₀z : ((⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩ : ↥Hinv) ^ 2) = 1 := by
      apply Subtype.ext
      show (AlgEquiv.restrictNormalHom K c₀) ^ 2 = (1 : K ≃ₐ[ℚ] K)
      rw [← map_pow, hc₀sq, map_one]
    have hx2 : (lσ ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩) ^ 2 = 1 := by
      rw [← map_pow, hσ₀z, map_one]
    have hc₀order : orderOf c₀ = 2 := orderOf_eq_prime hc₀sq hc₀ne
    have hdvd : orderOf (lσ ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩)
        ∣ orderOf c₀ := by
      rw [hc₀order]
      exact orderOf_dvd_iff_pow_eq_one.mpr hx2
    obtain ⟨l₀, hl₀gen⟩ := exists_zpowersHom_of_orderOf_dvd c₀
      (lσ ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩) hdvd
    have hρval : (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ)
          (ρ ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩)
        = (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (φ c₀) :=
      congrArg (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) hρgen
    have hl₀ : ∀ σ : ↥(Subgroup.zpowers c₀),
        SSGRoute.LiftsFlowAt (l₀ σ)
            (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ) ∧
        ((((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ) = 1 → l₀ σ = 1) := by
      intro σ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
      have hσeq : σ = (⟨c₀, Subgroup.mem_zpowers c₀⟩ : ↥(Subgroup.zpowers c₀)) ^ k :=
        Subtype.ext (by simpa using hk.symm)
      have hσcoe : (σ : SSGRoute.GalQ) = c₀ ^ k := by
        rw [hσeq]
        exact map_zpow (Subgroup.subtype (Subgroup.zpowers c₀)) _ k
      have hl₀val : l₀ σ
          = (lσ ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩) ^ k := by
        rw [hσeq, map_zpow, hl₀gen]
      have hΨval : (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)
          = ((((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp ρ)
              ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩)) ^ k := by
        rw [hσcoe, MonoidHom.comp_apply, map_zpow φ c₀ k,
          map_zpow (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (φ c₀) k, ← hρval,
          MonoidHom.comp_apply]
      constructor
      · refine (liftsFlowAt_iff_flowGroupSucc p K n i j _ _).mpr ?_
        rw [hl₀val, hΨval, map_zpow]
        congr 1
        exact (liftsFlowAt_iff_flowGroupSucc p K n i j _ _).mp
          (hlσlift ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩)
      · intro hσ1
        rw [hl₀val, ← map_zpow]
        refine hlσker _ ?_
        rw [map_zpow]
        rw [← hΨval]
        exact hσ1
    refine ⟨Φ, ?_, ?_⟩
    · -- clause (A)
      have hrep : ∀ A ∈ S', ∃ l : ↥(SSGRoute.decomp ℚ A) →*
          flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
          (∀ x : ↥(SSGRoute.decomp ℚ A),
            SSGRoute.LiftsFlowAt (l x) (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) x)) ∧
          (∀ x : ↥(SSGRoute.decomp ℚ A),
            (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) x) = 1 → l x = 1) := by
        intro A hAS'
        have hA : SSGRoute.IsT1Place p K A := (Finset.mem_filter.mp hAS').2
        obtain ⟨evθ, hevθ, hnatval⟩ := hnat (E p (K ≃ₐ[ℚ] K) n i j)
          (gradedMapLin p Φ.toHom Φ.surjective i j)
          (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x)
        have hkillA : Work.GroupCohomology.mapCochain2 (K ≃ₐ[ℚ] K)
            ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) (C (some ⟨A, hAS'⟩))
            ∈ Work.GroupCohomology.B2 (K ≃ₐ[ℚ] K)
                (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T) :=
          h2Map_eq_zero_iff_B2 (p := p) (G := K ≃ₐ[ℚ] K) (i := i) (j := j) (m := m) (n := n)
            (T := T) Φ ⟨C (some ⟨A, hAS'⟩), hC (some ⟨A, hAS'⟩)⟩ (by
              have hh := hΦ (Fintype.equivFin ι' (some ⟨A, hAS'⟩))
              rwa [hclsA_eval (some ⟨A, hAS'⟩)] at hh)
        exact local_level_n_of_class_killed p K i j m n T A hA φ hφ Φ
          (ev (some ⟨A, hAS'⟩)) (C (some ⟨A, hAS'⟩))
          (fun h h' => hCval (some ⟨A, hAS'⟩) h h') hkillA (hev (some ⟨A, hAS'⟩))
          (evθ (some ⟨A, hAS'⟩)) (hevθ (some ⟨A, hAS'⟩)) (fun z => hnatval (some ⟨A, hAS'⟩) z)
      refine local_clause_all_places p K i j n ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) S' ?_ hrep
      intro B hBfin hBram
      obtain ⟨A, hAS, hconj⟩ := hShit B hBfin hBram.symm
      refine ⟨A, Finset.mem_filter.mpr ⟨hAS, ?_⟩, hconj⟩
      exact isT1Place_of_isConjPlace p K (A₀ := B) (A := A)
        (isConjPlace_symm (k := ℚ) hconj) ⟨hBfin, hBram⟩
    · -- clause (B)
      intro c hc
      by_cases hcfix : c ∈ K.fixingSubgroup
      · -- `c` acts trivially: the pushed solution is trivial on `⟨c⟩`
        have hφc : φ c = 1 := hφ.2.2.1 c hc hcfix
        refine ⟨1, ?_, ?_⟩
        · intro σ
          have hσ1 : (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) (σ : SSGRoute.GalQ)) = 1 := by
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
            have h1 : (σ : SSGRoute.GalQ) = c ^ k := hk.symm
            rw [h1, MonoidHom.comp_apply, map_zpow φ c k, hφc, one_zpow, map_one]
          rw [hσ1]
          exact (liftsFlowAt_iff_flowGroupSucc p K n i j 1 1).mpr (map_one _)
        · intro σ _
          exact MonoidHom.one_apply σ
      · -- `c` is a non-trivial involution: transfer along conjugacy from `c₀`
        have hcne : c ≠ 1 := fun h1 => hcfix (h1 ▸ K.fixingSubgroup.one_mem)
        rcases involutions_eq_one_or_conjugate c₀ c hc₀sq hc with h1 | h2 | ⟨g, hg⟩
        · exact absurd h1 hc₀ne
        · exact absurd h2 hcne
        · have hres : AlgEquiv.restrictNormalHom K c ≠ 1 := by
            intro h1
            exact hcfix ((@restrictNormalHom_eq_one_iff_mem_fixingSubgroup ℚ SSGRoute.QBar _ _ _
              K ‹Normal ℚ K› c).mp h1)
          have hΨne : (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) c) ≠ 1 := by
            intro h1
            refine hres ?_
            rw [← hφ.1.2.2 c]
            rw [show flowQuot p (K ≃ₐ[ℚ] K) m i j (φ c)
                = flowQuot p (K ≃ₐ[ℚ] K) n i j
                    (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) c) from by
              rw [MonoidHom.comp_apply, flowQuot_flowGroupMap]]
            rw [h1, map_one]
          exact involution_clause_conj_transfer p K i j m n φ Φ c₀ c g hc₀sq hc hg hΨne l₀
            (fun σ => (hl₀ σ).1)
  · -- no involution of `G_ℚ` lies outside `K.fixingSubgroup`: clause (B) is trivial
    push_neg at hmain
    obtain ⟨m₀, hm₀n, hm₀⟩ := clause_A_of_prop5Data_exists p K i j hj hji hμ n hn D
    refine ⟨m₀, hm₀n, ?_⟩
    intro m hm φ hφ
    obtain ⟨Φ, hA⟩ := hm₀ m hm φ hφ
    exact ⟨Φ, hA, involution_clause_of_mem_fixingSubgroup p K i j m n φ hφ Φ hmain⟩

end Work.SSGRoute
