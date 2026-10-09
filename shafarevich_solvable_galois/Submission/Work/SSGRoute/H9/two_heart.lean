import Mathlib
import Submission.Work.SSGRoute.N2v2.heart_chi1_part
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `heart_two_sum`: the `χ₁`-part heart with the three unused hypotheses dropped

This file is a faithful copy of the proof of `Work.SSGRoute.N2v2.heart_chi1_part`
(`Submission/Work/SSGRoute/N2v2/heart_chi1_part.lean`) with the three hypotheses `hθker`, `hθprod`
and `harch` deleted from the signature.  Those three occur nowhere in the body of
`heart_chi1_part` (they are unused), so the deletion is harmless and the resulting statement is
strictly more general.  It is what the `p = 2` trichotomy orthogonality needs: at `p = 2` the
hypothesis `harch` ("all archimedean local Artin factors are trivial", i.e. the level `E` is
unramified at every infinite place of `↥K`) is *not* available — `↥K` need not be totally complex —
but it is also not used.
-/

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.N2v2

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-- **The `χ₁`-part of the escape orthogonality.** -/
theorem heart_two_sum (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (L₁ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁] (hKL₁ : K ≤ L₁)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, _root_.SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hTcov : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : _root_.SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) → ¬ _root_.SSGRoute.IsSplitIn k L₁ B →
      ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ → χ σ = 0))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)]
    (hexpE : ∀ σ : ↥E ≃ₐ[↥K] ↥E, σ ^ p = 1)
    (θ : (v : NK.GlobalCFT.Place ↥K) →
      (NK.GlobalCFT.Place.localField ↥K v)ˣ →* (↥E ≃ₐ[↥K] ↥E))
    (hlift : ∀ (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
      (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
      A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
      ∀ x : (↥K)ˣ, ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ _root_.SSGRoute.decomp (k := ↥K) A ∧
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
          θ (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x))
    (hunith : ∀ (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
      (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
      A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
      ∀ u : (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ,
        u ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔭) →
        ∃ σ : Ω ≃ₐ[↥K] Ω, _root_.SSGRoute.IsInertia k A (σ.restrictScalars k) ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
            θ (NK.GlobalCFT.Place.ofFinite 𝔭) u)
    (hdiagLift : ∀ 𝔭 ∈ T', ∃ σ₀ : Ω ≃ₐ[↥K] Ω,
      ∀ (y : (↥K)ˣ), NK.LocalAnabelian.kummerField (K' := Ω) p y ≤ E →
      ∀ τ : Ω ≃ₐ[↥K] Ω,
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ =
          θ (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) y) →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ y τ =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ y σ₀)
    (hgE : ∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ E.fixingSubgroup → g (σ.restrictScalars k) = 0)
    (hFaE : NK.LocalAnabelian.kummerField (K' := Ω) p a ≤ E)
    (bg : (↥K)ˣ)
    (hbg : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      g σ = Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ bg
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))
    (c₁ : (↥K)ˣ) (hc₁E : NK.LocalAnabelian.kummerField (K' := Ω) p c₁ ≤ E)
    (hc₁L : NK.LocalAnabelian.kummerField (K' := Ω) p c₁ ≤
      Work.SSGRoute.EscapeCoreLib.baseChange K L₁ hKL₁)
    (χE₁ : (↥E ≃ₐ[↥K] ↥E) →* Multiplicative (ZMod p))
    (hχE₁ : ∀ σ : Ω ≃ₐ[↥K] Ω,
      χE₁ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ) =
        Multiplicative.ofAdd
          (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₁ σ))
    (hgsum : ∑ 𝔭 ∈ T', (χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) bg))).toAdd
      = 0) :
    ∑ 𝔭 ∈ T', (χE₁ (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))).toAdd
      = 0 := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hAlgK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hSepK : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  -- rewrite the goal as a sum over the attached subtype of `T'`
  rw [← sum_attach_conv T' (ZMod p)
    (fun 𝔭 => (χE₁ (θ (Place.ofFinite 𝔭) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭) a))).toAdd)]
  -- the local data attached to each place of `T'`
  have hdata : ∀ 𝔭 : {x : NK.Chebotarev.PrimeIdeal ↥K // x ∈ T'},
      ∃ (A : ValuationSubring Ω) (σa τ σb : Ω ≃ₐ[↥K] Ω),
        A ∈ T ∧ A.comap (algebraMap ↥K Ω) =
            IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭.1 ∧
        σa ∈ SSGRoute.decomp (k := ↥K) A ∧
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σa =
          θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) a) ∧
        τ ∈ SSGRoute.decomp (k := ↥K) A ∧
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ =
          θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) c₁) ∧
        σb ∈ SSGRoute.decomp (k := ↥K) A ∧
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σb =
          θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) bg) := by
    intro 𝔭
    obtain ⟨A, hAT, hAcomap⟩ := hT'above 𝔭.1 𝔭.2
    obtain ⟨σa, hσa1, hσa2⟩ := hlift A (hTfin A hAT) 𝔭.1 hAcomap a
    obtain ⟨τ, hτ1, hτ2⟩ := hlift A (hTfin A hAT) 𝔭.1 hAcomap c₁
    obtain ⟨σb, hσb1, hσb2⟩ := hlift A (hTfin A hAT) 𝔭.1 hAcomap bg
    exact ⟨A, σa, τ, σb, hAT, hAcomap, hσa1, hσa2, hτ1, hτ2, hσb1, hσb2⟩
  choose A σa τ σb hAT hAcomap hσadec hσaeq hτdec hτeq hσbdec hσbeq using hdata
  -- the `k`-level avatar of `χ_{c₁}`
  have hψadd : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup,
      klevelKummer (Ω := Ω) p K ζ hζ c₁ (x * y) =
        klevelKummer (Ω := Ω) p K ζ hζ c₁ x + klevelKummer (Ω := Ω) p K ζ hζ c₁ y :=
    klevelKummer_add (Ω := Ω) p K ζ hζ c₁
  have hψkill : ∀ σ ∈ L₁.fixingSubgroup, klevelKummer (Ω := Ω) p K ζ hζ c₁ σ = 0 :=
    klevelKummer_kill (Ω := Ω) p K ζ hζ c₁ L₁ hKL₁ hc₁L
  -- `F_{bg} ≤ E`
  have hbgE : NK.LocalAnabelian.kummerField (K' := Ω) p bg ≤ E := by
    refine kummerField_le_of_vanishes_on_fixingSubgroup p k Ω K ζ hζ bg E ?_
    intro σ hσ
    have hσK : σ.restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    have h1 : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ bg σ =
        g (σ.restrictScalars k) := by
      rw [hbg (σ.restrictScalars k) hσK]
      rw [fixingSubgroupEquiv_restrictScalars_apply K σ hσK]
    rw [h1]
    exact hgE σ hσ
  -- the per-place identity `(★)`
  have hstar : ∀ 𝔭 : {x : NK.Chebotarev.PrimeIdeal ↥K // x ∈ T'},
      (χE₁ (θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) a))).toAdd =
        -(g ((τ 𝔭).restrictScalars k) + h (A 𝔭) ((τ 𝔭).restrictScalars k)) := by
    intro 𝔭
    obtain ⟨σ₀, hσ₀⟩ := hdiagLift 𝔭.1 𝔭.2
    let θE : (↥K)ˣ →* (↥E ≃ₐ[↥K] ↥E) :=
      { toFun := fun x => θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) x)
        map_one' := by simp [NK.CFTLib.IdeleHasse.localImageAt]
        map_mul' := by
          intro x y
          simp [NK.CFTLib.IdeleHasse.localImageAt, map_mul] }
    have hθE : ∀ x : (↥K)ˣ, θE x =
        θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) x) := fun x => rfl
    have hdiag : ∀ c : (↥K)ˣ, NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ E →
        ∀ τ' : Ω ≃ₐ[↥K] Ω,
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ' = θE c →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c τ' =
            Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ₀ := by
      intro c hc τ' hτ'
      exact hσ₀ c hc τ' hτ'
    have hanti := kummerCharZMod_pairing_antisymm (k := k) (Ω := Ω) p K ζ hζ E θE σ₀ hdiag
      a c₁ hFaE hc₁E (le_trans (kummerField_mul_le (Ω := Ω) p K a c₁) (sup_le hFaE hc₁E))
      (σa 𝔭) (τ 𝔭)
      (hσaeq 𝔭) (hτeq 𝔭)
    have hL : (χE₁ (θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) a))).toAdd =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₁ (σa 𝔭) := by
      rw [← hσaeq 𝔭, hχE₁ (σa 𝔭)]
      rfl
    have hR : g ((τ 𝔭).restrictScalars k) + h (A 𝔭) ((τ 𝔭).restrictScalars k) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a (τ 𝔭) := by
      have hτ'K : (τ 𝔭).restrictScalars k ∈ K.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact (τ 𝔭).commutes ⟨x, hx⟩
      have hτ'dec : (τ 𝔭).restrictScalars k ∈ SSGRoute.decomp k (A 𝔭) :=
        restrictScalars_mem_decomp K (hτdec 𝔭)
      have h1 := ha (A 𝔭) (hAT 𝔭)
        ⟨(τ 𝔭).restrictScalars k, ⟨hτ'dec, hτ'K⟩⟩
      have h2 : Work.SSGRoute.gesLocalToGalK K
          ⟨(τ 𝔭).restrictScalars k, ⟨hτ'dec, hτ'K⟩⟩ = τ 𝔭 :=
        fixingSubgroupEquiv_restrictScalars K (τ 𝔭)
      rw [h2] at h1
      exact h1
    rw [hL, hR]
    linear_combination hanti
  -- the `g`-sum vanishes
  have hperg : ∀ 𝔭 : {x : NK.Chebotarev.PrimeIdeal ↥K // x ∈ T'},
      g ((τ 𝔭).restrictScalars k) =
        -(χE₁ (θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) bg))).toAdd := by
    intro 𝔭
    obtain ⟨σ₀, hσ₀⟩ := hdiagLift 𝔭.1 𝔭.2
    let θE : (↥K)ˣ →* (↥E ≃ₐ[↥K] ↥E) :=
      { toFun := fun x => θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) x)
        map_one' := by simp [NK.CFTLib.IdeleHasse.localImageAt]
        map_mul' := by
          intro x y
          simp [NK.CFTLib.IdeleHasse.localImageAt, map_mul] }
    have hdiag : ∀ c : (↥K)ˣ, NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ E →
        ∀ τ' : Ω ≃ₐ[↥K] Ω,
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ' = θE c →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c τ' =
            Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ₀ := by
      intro c hc τ' hτ'
      exact hσ₀ c hc τ' hτ'
    have hanti := kummerCharZMod_pairing_antisymm (k := k) (Ω := Ω) p K ζ hζ E θE σ₀ hdiag
      bg c₁ hbgE hc₁E (le_trans (kummerField_mul_le (Ω := Ω) p K bg c₁) (sup_le hbgE hc₁E))
      (σb 𝔭) (τ 𝔭)
      (hσbeq 𝔭) (hτeq 𝔭)
    have hτK : (τ 𝔭).restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (τ 𝔭).commutes ⟨x, hx⟩
    have h1 : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ bg (τ 𝔭) =
        g ((τ 𝔭).restrictScalars k) := by
      rw [hbg ((τ 𝔭).restrictScalars k) hτK]
      rw [fixingSubgroupEquiv_restrictScalars_apply K (τ 𝔭) hτK]
    have h2 : (χE₁ (θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) bg))).toAdd =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₁ (σb 𝔭) := by
      rw [← hσbeq 𝔭, hχE₁ (σb 𝔭)]
      rfl
    rw [← h1, h2]
    linear_combination hanti
  have hg0 : (∑ 𝔭 : {x : NK.Chebotarev.PrimeIdeal ↥K // x ∈ T'},
      g ((τ 𝔭).restrictScalars k)) = 0 := by
    rw [Finset.sum_congr rfl (fun 𝔭 _ => hperg 𝔭), Finset.sum_neg_distrib,
      (sum_attach_conv T' (ZMod p)
        (fun 𝔭 => (χE₁ (θ (Place.ofFinite 𝔭) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭) bg))).toAdd)).trans
        hgsum, neg_zero]
  -- the `hA`-sum vanishes
  have hperh : ∀ 𝔭 : {x : NK.Chebotarev.PrimeIdeal ↥K // x ∈ T'},
      h (A 𝔭) ((τ 𝔭).restrictScalars k) = 0 := by
    intro 𝔭
    have hτ'K : (τ 𝔭).restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (τ 𝔭).commutes ⟨x, hx⟩
    have hτ'dec : (τ 𝔭).restrictScalars k ∈ SSGRoute.decomp k (A 𝔭) :=
      restrictScalars_mem_decomp K (hτdec 𝔭)
    rcases horth₁ (A 𝔭) (hAT 𝔭) with h0 | h1 | h2
    · exact h0 _ ⟨hτ'dec, hτ'K⟩
    · -- case (ii): every character killing `L₁.fixingSubgroup` kills `D_A`
      have hσa'K : (σa 𝔭).restrictScalars k ∈ K.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact (σa 𝔭).commutes ⟨x, hx⟩
      have hσa'dec : (σa 𝔭).restrictScalars k ∈ SSGRoute.decomp k (A 𝔭) :=
        restrictScalars_mem_decomp K (hσadec 𝔭)
      have hχ0 : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₁
          (σa 𝔭) = 0 := by
        have h := h1 (klevelKummer (Ω := Ω) p K ζ hζ c₁) hψadd hψkill
          ((σa 𝔭).restrictScalars k) ⟨hσa'dec, hσa'K⟩
        rwa [klevelKummer_restrictScalars (Ω := Ω) p K ζ hζ c₁ (σa 𝔭)] at h
      have hχ0' : (χE₁ (θ (Place.ofFinite 𝔭.1)
          (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) a))).toAdd = 0 := by
        rw [← hσaeq 𝔭, hχE₁ (σa 𝔭)]
        rw [hχ0]
        rfl
      have hσb'K : (σb 𝔭).restrictScalars k ∈ K.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact (σb 𝔭).commutes ⟨x, hx⟩
      have hσb'dec : (σb 𝔭).restrictScalars k ∈ SSGRoute.decomp k (A 𝔭) :=
        restrictScalars_mem_decomp K (hσbdec 𝔭)
      have hχb0 : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₁
          (σb 𝔭) = 0 := by
        have h := h1 (klevelKummer (Ω := Ω) p K ζ hζ c₁) hψadd hψkill
          ((σb 𝔭).restrictScalars k) ⟨hσb'dec, hσb'K⟩
        rwa [klevelKummer_restrictScalars (Ω := Ω) p K ζ hζ c₁ (σb 𝔭)] at h
      have hg0' : g ((τ 𝔭).restrictScalars k) = 0 := by
        have hseq : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ bg (τ 𝔭) =
            g ((τ 𝔭).restrictScalars k) := by
          rw [hbg ((τ 𝔭).restrictScalars k) hτ'K]
          rw [fixingSubgroupEquiv_restrictScalars_apply K (τ 𝔭) hτ'K]
        -- antisymmetry for the pair `(c₁, bg)`
        obtain ⟨σ₀, hσ₀⟩ := hdiagLift 𝔭.1 𝔭.2
        let θE : (↥K)ˣ →* (↥E ≃ₐ[↥K] ↥E) :=
          { toFun := fun x => θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) x)
            map_one' := by simp [NK.CFTLib.IdeleHasse.localImageAt]
            map_mul' := by
              intro x y
              simp [NK.CFTLib.IdeleHasse.localImageAt, map_mul] }
        have hdiag : ∀ c : (↥K)ˣ, NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ E →
            ∀ τ' : Ω ≃ₐ[↥K] Ω,
              AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ' = θE c →
              Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c τ' =
                Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ₀ := by
          intro c hc τ' hτ'
          exact hσ₀ c hc τ' hτ'
        have hanti := kummerCharZMod_pairing_antisymm (k := k) (Ω := Ω) p K ζ hζ E θE σ₀ hdiag
          c₁ bg hc₁E hbgE (le_trans (kummerField_mul_le (Ω := Ω) p K c₁ bg) (sup_le hc₁E hbgE))
          (τ 𝔭) (σb 𝔭)
          (hτeq 𝔭) (hσbeq 𝔭)
        -- hanti : χ_{bg}(τ 𝔭) + χ_{c₁}(σb 𝔭) = 0
        have h3 : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ bg (τ 𝔭) = 0 := by
          have hthis := hanti
          rw [hχb0, add_zero] at hthis
          exact hthis
        rw [← hseq, h3]
      -- `h A` from `(★)`
      have hstar' := hstar 𝔭
      rw [hχ0', hg0', zero_add] at hstar'
      exact neg_eq_zero.mp hstar'.symm
    · -- case (iii): the datum kills the inertia
      obtain ⟨hI1, hI2⟩ := h2
      have hψI : ∀ (σ : Ω ≃ₐ[k] Ω) (hσK : σ ∈ K.fixingSubgroup),
          SSGRoute.IsInertia k (A 𝔭) σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c₁
            ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩) = 0 := by
        intro σ hσK hinert
        have h := hI2 (klevelKummer (Ω := Ω) p K ζ hζ c₁) hψadd hψkill σ hσK hinert
        rwa [klevelKummer, dif_pos hσK] at h
      obtain ⟨b, u, hu, hdec⟩ :=
        localImageAt_eq_pow_mul_localUnits_of_inertia p k Ω K ζ hζ (A 𝔭)
          (hTfin (A 𝔭) (hAT 𝔭)) 𝔭.1 (hAcomap 𝔭) c₁ hψI
      obtain ⟨σu, hσu_inertia, hσu_eq⟩ :=
        hunith (A 𝔭) (hTfin (A 𝔭) (hAT 𝔭)) 𝔭.1 (hAcomap 𝔭) u hu
      have hpow : θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) c₁) =
          θ (Place.ofFinite 𝔭.1) u := by
        rw [hdec, map_mul, map_pow, hexpE (θ (Place.ofFinite 𝔭.1) b), one_mul]
      have hδeq : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E (σu⁻¹ * τ 𝔭) = 1 := by
        rw [map_mul, map_inv, hσu_eq, hτeq 𝔭, hpow, inv_mul_cancel]
      have hδE : (IntermediateField.fixingSubgroupEquiv K)
          ⟨(σu⁻¹ * τ 𝔭).restrictScalars k, (by
            rw [IntermediateField.mem_fixingSubgroup_iff]
            intro x hx
            exact (σu⁻¹ * τ 𝔭).commutes ⟨x, hx⟩)⟩ ∈ E.fixingSubgroup := by
        rw [← IntermediateField.restrictNormalHom_ker E, MonoidHom.mem_ker]
        rw [fixingSubgroupEquiv_restrictScalars_apply K (σu⁻¹ * τ 𝔭) _]
        exact hδeq
      have hδdec : (σu⁻¹ * τ 𝔭).restrictScalars k ∈ SSGRoute.decomp k (A 𝔭) :=
        restrictScalars_mem_decomp K (Subgroup.mul_mem _
          (Subgroup.inv_mem _ (hσu_inertia.1)) (hτdec 𝔭))
      have hδK : (σu⁻¹ * τ 𝔭).restrictScalars k ∈ K.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact (σu⁻¹ * τ 𝔭).commutes ⟨x, hx⟩
      have hδ0 : h (A 𝔭) ((σu⁻¹ * τ 𝔭).restrictScalars k) = 0 :=
        hA_eq_zero_of_mem_Efix p K ζ hζ E g h T hTfin a ha hgE hFaE (A 𝔭) (hAT 𝔭)
          _ hδdec hδK hδE
      have hσu0 : h (A 𝔭) (σu.restrictScalars k) = 0 := by
        refine hI1 _ ?_ hσu_inertia
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact σu.commutes ⟨x, hx⟩
      have hprod : h (A 𝔭) ((τ 𝔭).restrictScalars k) =
          h (A 𝔭) (σu.restrictScalars k) + h (A 𝔭) ((σu⁻¹ * τ 𝔭).restrictScalars k) := by
        have hxy : (σu * (σu⁻¹ * τ 𝔭)).restrictScalars k =
            σu.restrictScalars k * (σu⁻¹ * τ 𝔭).restrictScalars k := rfl
        have hceil : σu * (σu⁻¹ * τ 𝔭) = τ 𝔭 := by group
        have hσuK : σu.restrictScalars k ∈ K.fixingSubgroup := by
          rw [IntermediateField.mem_fixingSubgroup_iff]
          intro x hx
          exact σu.commutes ⟨x, hx⟩
        have hlt : σu.restrictScalars k ∈ SSGRoute.decomp k (A 𝔭) ⊓ K.fixingSubgroup :=
          ⟨restrictScalars_mem_decomp K (hσu_inertia.1), hσuK⟩
        have hrt : (σu⁻¹ * τ 𝔭).restrictScalars k ∈
            SSGRoute.decomp k (A 𝔭) ⊓ K.fixingSubgroup := ⟨hδdec, hδK⟩
        have h1 : AlgEquiv.restrictScalars k (τ 𝔭) =
            AlgEquiv.restrictScalars k (σu * (σu⁻¹ * τ 𝔭)) := by rw [hceil]
        rw [h1, hxy]
        exact hh (A 𝔭) (hAT 𝔭) _ hlt _ hrt
      rw [hprod, hσu0, hδ0, add_zero]
  have hh0 : (∑ 𝔭 : {x : NK.Chebotarev.PrimeIdeal ↥K // x ∈ T'},
      h (A 𝔭) ((τ 𝔭).restrictScalars k)) = 0 :=
    Finset.sum_eq_zero (fun 𝔭 _ => hperh 𝔭)
  -- assemble
  have hS0 : (∑ 𝔭 : {x : NK.Chebotarev.PrimeIdeal ↥K // x ∈ T'},
        (χE₁ (θ (Place.ofFinite 𝔭.1) (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite 𝔭.1) a))).toAdd) =
      -((∑ 𝔭 : {x : NK.Chebotarev.PrimeIdeal ↥K // x ∈ T'},
            g ((τ 𝔭).restrictScalars k)) +
         (∑ 𝔭 : {x : NK.Chebotarev.PrimeIdeal ↥K // x ∈ T'},
            h (A 𝔭) ((τ 𝔭).restrictScalars k))) := by
    rw [Finset.sum_congr rfl (fun 𝔭 _ => hstar 𝔭), Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [hS0, hg0, hh0, add_zero, neg_zero]

end Work.SSGRoute.N2v2
