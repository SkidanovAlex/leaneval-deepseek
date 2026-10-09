import Mathlib
import Submission.Work.SSGRoute.sha2_hasse.Gateway
import Submission.Work.SSGRoute.sha2_hasse.locUnits_mkClass_apply
import Submission.Work.sha2_hasse.exists_involution_extension
import Submission.Work.sha2_hasse.exists_norm_witness_infinitePlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField Pointwise Classical
open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 3200000

noncomputable section

namespace Work.SSGRoute.sha2_hasse

variable {k : Type} [Field k] [NumberField k]

/-! ## A coboundary criterion for a group of order `≤ 2` -/

/-- **A `2`-cocycle on a group of order `≤ 2` is a coboundary as soon as the single equation at the
generator holds.**  If `S` is a finite group with `Nat.card S ≤ 2`, `s ∈ S` is not the identity,
`c` is a `2`-cocycle for the action `ρ` and `z` satisfies `ρ s z + z = c s s + c 1 1`, then `c` is
a coboundary. -/
theorem exists_coboundary_of_card_le_two
    {S R M : Type} [Group S] [Ring R] [AddCommGroup M] [Module R M] [Finite S]
    (ρ : S →* Module.End R M)
    (hcard : Nat.card S ≤ 2) (s : S) (hsne : s ≠ 1)
    (c : S → S → M)
    (hcyc : ∀ g h l : S, ρ g (c h l) - c (g * h) l + c g (h * l) - c g h = 0)
    (z : M) (hz : ρ s z + z = c s s + c 1 1) :
    ∃ f : S → M, ∀ g h : S, ρ g (f h) - f (g * h) + f g = c g h := by
  classical
  haveI : Fintype S := Fintype.ofFinite S
  have hs2 : s * s = 1 := by
    have hdvd : orderOf s ∣ Nat.card S := orderOf_dvd_natCard s
    have hpos : 0 < Nat.card S := Nat.card_pos
    have hle : orderOf s ≤ 2 := le_trans (Nat.le_of_dvd hpos hdvd) hcard
    have hpos' : 0 < orderOf s := orderOf_pos s
    rcases (by omega : orderOf s = 1 ∨ orderOf s = 2) with h1 | h2
    · rw [show s = 1 from orderOf_eq_one_iff.mp h1, mul_one]
    · rw [← sq, ← h2, pow_orderOf_eq_one]
  have hgen : ∀ g : S, g = 1 ∨ g = s := by
    intro g
    by_cases h : g = 1
    · exact Or.inl h
    · refine Or.inr ?_
      by_contra hgs
      have hsng : s ∉ ({g} : Finset S) := by
        simp only [Finset.mem_singleton]
        exact fun hsg => hgs hsg.symm
      have h1ng : (1 : S) ∉ ({s, g} : Finset S) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h' => hsne h'.symm, fun h' => h h'.symm⟩
      have hcard3 : ({1, s, g} : Finset S).card = 3 := by
        rw [Finset.card_insert_of_notMem h1ng, Finset.card_insert_of_notMem hsng,
          Finset.card_singleton]
      have hle := Finset.card_le_univ ({1, s, g} : Finset S)
      rw [hcard3, ← Nat.card_eq_fintype_card] at hle
      omega
  have hρ1 : ∀ x : M, ρ (1 : S) x = x := by
    intro x
    rw [map_one]
    exact Module.End.one_apply x
  have hc1 : ∀ h : S, c 1 h = c 1 1 := by
    intro h
    have h0 := hcyc 1 1 h
    have h1 : c 1 h - c 1 1 = 0 := by
      simpa [hρ1, one_mul] using h0
    exact sub_eq_zero.mp h1
  have hc2 : ∀ g : S, c g 1 = ρ g (c 1 1) := by
    intro g
    have h0 := hcyc g 1 1
    have h1 : ρ g (c 1 1) - c g 1 = 0 := by simpa [mul_one] using h0
    exact (sub_eq_zero.mp h1).symm
  let F : S → M := fun g => if g = 1 then c 1 1 else z
  have hF1 : F 1 = c 1 1 := by
    show (if (1 : S) = 1 then c 1 1 else z) = c 1 1
    rw [if_pos rfl]
  have hFs : F s = z := by
    show (if s = 1 then c 1 1 else z) = z
    rw [if_neg hsne]
  refine ⟨F, ?_⟩
  intro g h
  rcases hgen g with hg | hg <;> rcases hgen h with hh | hh <;> rw [hg, hh]
  · rw [hρ1 (F 1), mul_one, hF1]
    abel
  · rw [hρ1 (F s), one_mul, hFs, hF1, hc1 s]
    abel
  · rw [hF1, mul_one, hFs, hc2 s]
    abel
  · rw [hFs, hs2, hF1]
    have h2 : ρ s z - c 1 1 + z = (ρ s z + z) - c 1 1 := by abel
    rw [h2, hz]
    abel

/-! ## The decomposition group of an infinite place -/

/-- The stabiliser of `Place.ofInfinite v` has the same cardinality as the stabiliser of `v`. -/
theorem natCard_stabilizer_place_ofInfinite
    (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (v : NumberField.InfinitePlace (Lf L)) :
    Nat.card (MulAction.stabilizer (Lf L ≃ₐ[k] Lf L) (NK.GlobalCFT.Place.ofInfinite v))
      = Nat.card (MulAction.stabilizer (Lf L ≃ₐ[k] Lf L) v) :=
  Nat.card_congr (Equiv.subtypeEquivRight (fun δ => by
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj]))

/-! ## The main theorem -/

theorem locUnits_levelClass_eq_zero_infinitePlace
    {k : Type} [Field k] [NumberField k]
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (hfac : ∀ g h u v : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      u ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      v ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      d (g * u) (h * v) = d g h)
    (hvals : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Work.SSGRoute.sha2_hasse.Lf L)ˣ,
        Work.SSGRoute.sha2_hasse.inclUnits L (Additive.ofMul x) = d g h)
    (hinv : ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, σ ^ 2 = 1 →
      ∃ b : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ,
        SSGRoute.IsLocConstOn (Subgroup.zpowers σ) b ∧
        ∀ g ∈ Subgroup.zpowers σ, ∀ h ∈ Subgroup.zpowers σ,
          d g h = g • b h - b (g * h) + b g)
    (hmem : (fun p : (Work.SSGRoute.sha2_hasse.Lf L ≃ₐ[k] Work.SSGRoute.sha2_hasse.Lf L) ×
        (Work.SSGRoute.sha2_hasse.Lf L ≃ₐ[k] Work.SSGRoute.sha2_hasse.Lf L) =>
        Work.SSGRoute.sha2_hasse.levelCocycle L d hvals p.1 p.2)
      ∈ groupCohomology.cocycles₂
          (NK.HassePrinciple.unitsRep k (Work.SSGRoute.sha2_hasse.Lf L)))
    (v : NumberField.InfinitePlace (Work.SSGRoute.sha2_hasse.Lf L)) :
    (NK.HassePrinciple.locUnits k (Work.SSGRoute.sha2_hasse.Lf L)
        (NK.GlobalCFT.Place.ofInfinite v)).hom
      (Work.SSGRoute.sha2_hasse.levelClass L d hvals hmem) = 0 := by
  classical
  let w : NK.GlobalCFT.Place (Lf L) := NK.GlobalCFT.Place.ofInfinite v
  let S := MulAction.stabilizer (Lf L ≃ₐ[k] Lf L) w
  haveI : Fintype S := inferInstance
  haveI hmd : MulDistribMulAction S ((NK.GlobalCFT.Place.localField (Lf L) w)ˣ) :=
    NK.HassePrinciple.instMulDistribMulActionLocalUnits (K := k) (L := Lf L) w
  haveI hda : DistribMulAction S (Additive ((NK.GlobalCFT.Place.localField (Lf L) w)ˣ)) :=
    NK.HassePrinciple.instDistribMulActionAdditiveOfMul (G := S)
      (A := (NK.GlobalCFT.Place.localField (Lf L) w)ˣ)
  let c : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) → Additive (Lf L)ˣ :=
    fun p => levelCocycle L d hvals p.1 p.2
  have hc : c ∈ groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k (Lf L)) := hmem
  let C : S → S → (NK.HassePrinciple.localUnitsRep.{0} k (Lf L) w).V :=
    fun γ δ => (NK.HassePrinciple.unitsToLocalUnits.{0} k (Lf L) w).hom
      (c (S.subtype γ, S.subtype δ))
  have hpush : ⇑(groupCohomology.mapCocycles₂ S.subtype
      (NK.HassePrinciple.unitsToLocalUnits.{0} k (Lf L) w) ⟨c, hc⟩)
      = fun p : S × S => C p.1 p.2 := by
    funext p
    obtain ⟨γ, δ⟩ := p
    rw [groupCohomology.coe_mapCocycles₂, cochainsMap₂_apply]
    rfl
  have hCmem : (fun p : S × S => C p.1 p.2) ∈
      groupCohomology.cocycles₂ (NK.HassePrinciple.localUnitsRep.{0} k (Lf L) w) := by
    rw [← hpush]
    exact (groupCohomology.mapCocycles₂ S.subtype
      (NK.HassePrinciple.unitsToLocalUnits.{0} k (Lf L) w) ⟨c, hc⟩).2
  have hcyc : ∀ g h l : S, (NK.HassePrinciple.localUnitsRep.{0} k (Lf L) w).ρ g (C h l)
      - C (g * h) l + C g (h * l) - C g h = 0 := by
    intro g h l
    exact (mem_cocycles₂_iff (A := NK.HassePrinciple.localUnitsRep.{0} k (Lf L) w)
      (c := fun p : S × S => C p.1 p.2)).mp hCmem g h l
  -- the goal rewritten via the explicit localisation
  have hmain : (NK.HassePrinciple.locUnits k (Lf L) w).hom (levelClass L d hvals hmem)
      = groupCohomology.H2π (NK.HassePrinciple.localUnitsRep.{0} k (Lf L) w)
          (groupCohomology.mapCocycles₂ S.subtype
            (NK.HassePrinciple.unitsToLocalUnits.{0} k (Lf L) w) ⟨c, hc⟩) := by
    unfold levelClass
    exact locUnits_mkClass_apply (k := k) L w c hc
  rw [hmain, groupCohomology.H2π_eq_zero_iff]
  -- the cardinality of the decomposition group
  have hcard : Nat.card S = 1 ∨ Nat.card S = 2 := by
    rw [show Nat.card S = Nat.card (MulAction.stabilizer (Lf L ≃ₐ[k] Lf L) v) from
      natCard_stabilizer_place_ofInfinite L v]
    by_cases h : NumberField.InfinitePlace.IsUnramified k v
    · left
      exact (NumberField.InfinitePlace.isUnramified_iff_card_stabilizer_eq_one
        (k := k) (K := Lf L)).mp h
    · right
      exact (NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two
        (k := k) (K := Lf L)).mp h
  rcases hcard with h1 | h2
  · -- the decomposition group is trivial
    have h1' : Fintype.card S = 1 := by rw [← Nat.card_eq_fintype_card]; exact h1
    haveI : Subsingleton S := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h1')
    have hρ1 : ∀ x : Additive ((NK.GlobalCFT.Place.localField (Lf L) w)ˣ),
        (NK.HassePrinciple.localUnitsRep.{0} k (Lf L) w).ρ (1 : S) x = x := by
      intro x
      rw [map_one]
      exact Module.End.one_apply x
    refine ⟨fun _ => C 1 1, ?_⟩
    funext p
    obtain ⟨γ, δ⟩ := p
    rw [groupCohomology.d₁₂_hom_apply, hpush]
    have hγ : γ = 1 := Subsingleton.elim γ 1
    have hδ : δ = 1 := Subsingleton.elim δ 1
    subst hγ; subst hδ
    simp only [mul_one, hρ1 (C 1 1)]
    abel
  · -- the decomposition group has order two: the local involution
    have hcardle : Nat.card S ≤ 2 := le_of_eq h2
    have hnu : ¬ NumberField.InfinitePlace.IsUnramified k v := by
      intro hunr
      have hc1 : Nat.card (MulAction.stabilizer (Lf L ≃ₐ[k] Lf L) v) = 1 :=
        (NumberField.InfinitePlace.isUnramified_iff_card_stabilizer_eq_one
          (k := k) (K := Lf L)).mp hunr
      have h2' : Nat.card (MulAction.stabilizer (Lf L ≃ₐ[k] Lf L) v) = 2 := by
        rw [← natCard_stabilizer_place_ofInfinite L v]; exact h2
      omega
    have hram := (NumberField.InfinitePlace.not_isUnramified_iff
      (k := k) (K := Lf L) (w := v)).mp hnu
    haveI hLies : v.LiesOver (NumberField.InfinitePlace.comap v (algebraMap k (Lf L))) := ⟨rfl⟩
    obtain ⟨σ₀, hσ₀v, hσ₀conj⟩ := NK.GlobalCFT.Galois.exists_conj_aut (K := k) (L := Lf L)
      (w := v) (v := NumberField.InfinitePlace.comap v (algebraMap k (Lf L))) hram.1 hram.2
    have hσ₀ne : σ₀ ≠ 1 := by
      intro h
      refine (NumberField.InfinitePlace.not_isReal_iff_isComplex).mpr hram.1 ?_
      rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
      ext x
      have hx := hσ₀conj x
      rw [h] at hx
      simpa [NumberField.ComplexEmbedding.conjugate, RingHom.comp_apply] using hx.symm
    -- extend the local conjugation to an involution of `G_k`
    obtain ⟨σ, φ, hσ2, hσres, hφL, hφσ⟩ :=
      Work.sha2_hasse.exists_involution_extension (k := k) L v σ₀ hσ₀conj
    let s : S := ⟨σ₀, by
      rw [MulAction.mem_stabilizer_iff]
      show σ₀ • NK.GlobalCFT.Place.ofInfinite v = NK.GlobalCFT.Place.ofInfinite v
      rw [NK.GlobalCFT.Place.smul_ofInfinite, hσ₀v]⟩
    have hscoe : (s : Lf L ≃ₐ[k] Lf L) = σ₀ := rfl
    have hsne : s ≠ 1 := by
      intro h
      refine hσ₀ne ?_
      have h' : (s : Lf L ≃ₐ[k] Lf L) = 1 := by rw [h]; rfl
      rwa [hscoe] at h'
    have hsσ : levelRes L σ = (s : Lf L ≃ₐ[k] Lf L) := by rw [hscoe]; exact hσres
    have hconjs : ∀ x : Lf L,
        v.embedding ((s : Lf L ≃ₐ[k] Lf L) x) = starRingEnd ℂ (v.embedding x) := by
      intro x; rw [hscoe]; exact hσ₀conj x
    -- the norm witness
    obtain ⟨z, hz⟩ := Work.sha2_hasse.exists_norm_witness_infinitePlace d L hfac hvals hinv v
      σ hσ2 φ hφL hφσ s hsσ hconjs hram.1
    have hρofMul : ∀ (g : S) (u : (NK.GlobalCFT.Place.localField (Lf L) w)ˣ),
        (NK.HassePrinciple.localUnitsRep.{0} k (Lf L) w).ρ g (Additive.ofMul u)
          = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv w g u) := fun g u => rfl
    have hCss : C s s = Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom w
        (Additive.toMul (levelCocycle L d hvals
          (s : Lf L ≃ₐ[k] Lf L) (s : Lf L ≃ₐ[k] Lf L)))) := by
      change (NK.HassePrinciple.unitsToLocalUnits.{0} k (Lf L) w).hom
          (Additive.ofMul (Additive.toMul (levelCocycle L d hvals
            (s : Lf L ≃ₐ[k] Lf L) (s : Lf L ≃ₐ[k] Lf L)))) = _
      rw [NK.HassePrinciple.unitsToLocalUnits_apply]
      rfl
    have hC11 : C 1 1 = Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom w
        (Additive.toMul (levelCocycle L d hvals 1 1))) := by
      change (NK.HassePrinciple.unitsToLocalUnits.{0} k (Lf L) w).hom
          (Additive.ofMul (Additive.toMul (levelCocycle L d hvals 1 1))) = _
      rw [NK.HassePrinciple.unitsToLocalUnits_apply]
      rfl
    let zA : (NK.HassePrinciple.localUnitsRep.{0} k (Lf L) w).V := Additive.ofMul z
    have hzA : zA = Additive.ofMul z := rfl
    have hρz : (NK.HassePrinciple.localUnitsRep.{0} k (Lf L) w).ρ s zA
        = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv w s z) := by
      change (NK.HassePrinciple.localUnitsRep.{0} k (Lf L) w).ρ s (Additive.ofMul z) = _
      rfl
    have hz' : (NK.HassePrinciple.localUnitsRep.{0} k (Lf L) w).ρ s zA + zA = C s s + C 1 1 := by
      rw [hρz, hzA, hCss, hC11]
      exact congrArg Additive.ofMul hz
    obtain ⟨F, hF⟩ := exists_coboundary_of_card_le_two
      (R := NK.HassePrinciple.CoeffInt)
      (ρ := (NK.HassePrinciple.localUnitsRep.{0} k (Lf L) w).ρ)
      hcardle s hsne C hcyc zA hz'
    refine ⟨F, ?_⟩
    funext p
    obtain ⟨γ, δ⟩ := p
    rw [groupCohomology.d₁₂_hom_apply, hpush]
    exact hF γ δ

end Work.SSGRoute.sha2_hasse
