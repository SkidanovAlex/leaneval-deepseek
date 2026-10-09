import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.e9_caseB_descent
import Submission.Work.SSGRoute.Sha2Lib.restrictNormalHom_eq_one_of_isInertiaAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

/-- **The inertia subgroup is trivial in a compositum of unramified-at-`Q` levels.**

Let `k ⊆ K` be number fields (`K/k` finite Galois), `Ω` an algebraically closed extension of both, and
`L : IntermediateField K Ω` a level which is finite over `k` and Galois over `k`.  Let `M₀, L₀` be
levels `k ⊆ M₀, L₀ ⊆ Ω` (each a number field, finite Galois over `k`), and let
`hgenL : L.restrictScalars k ≤ (IsScalarTower.toAlgHom k K Ω).fieldRange ⊔ L₀ ⊔ M₀`
(the caller will have equality: `↥L` is generated over `k` by the image of `K`, `L₀` and `M₀`).  Let
`q'` be a prime of `𝓞 ↥L` with contraction `q` in `𝓞 K`, `wM` in `𝓞 ↥M₀` and `wL` in `𝓞 ↥L₀`.
Assume `M₀/k` is unramified at `wM` (`e(wM | wM ∩ 𝓞 k) = 1`) and `L₀/k` is unramified at `wL`.  Then
the inertia subgroup of the extension `L/K` at `q'` is trivial:
`Ideal.inertia (↥L ≃ₐ[K] ↥L) q'.asIdeal = ⊥`.

Proof: let `σ ∈ Ideal.inertia (↥L ≃ₐ[K] ↥L) q'.asIdeal`.
* The "bridge" `Work.SSGRoute.E9CaseB.isInertiaAt_restrictScalars`
  (`Submission/Work/SSGRoute/e9_caseB_descent.lean`, proved) gives
  `SSGRoute.PTExt.IsInertiaAt q' (AlgEquiv.restrictScalars k σ)`.
* `Work.SSGRoute.Sha2Lib.restrictNormalHom_eq_one_of_isInertiaAt`
  (`Submission/Work/SSGRoute/Sha2Lib/restrictNormalHom_eq_one_of_isInertiaAt.lean`, proved) applied
  with `E := ↥M₀` (resp. `E := ↥L₀`), the primes `qE := wM` (resp. `wL`, with
  `q'.asIdeal.LiesOver qE.asIdeal`) and the unramifiedness hypotheses, shows that
  `AlgEquiv.restrictScalars k σ` fixes `M₀` (resp. `L₀`) pointwise.
* `σ` fixes the image of `K` in `↥L`, i.e. `(IsScalarTower.toAlgHom k K Ω).fieldRange`, because `σ` is
  a `K`-algebra automorphism (`AlgEquiv.commutes`).
* Since `↥L` is generated over `k` by the images of `K`, `L₀`, `M₀` (hypothesis `hgenL`), an
  automorphism fixing them pointwise is the identity: use the fixing-subgroup machinery
  (`IntermediateField.fixingSubgroup_sup`, `IntermediateField.mem_fixingSubgroup_iff`,
  `AlgEquiv.ext`), transporting `M₀`, `L₀` to subfields of `↥L` along `algebraMap ↥L Ω`
  (`IntermediateField.comap`).
* Hence `Ideal.inertia ... = ⊥` by `eq_bot_iff`.

The tower instances `[Algebra ↥M₀ ↥L]`, `[Algebra ↥L₀ ↥L]` and the corresponding `IsScalarTower`s are
hypotheses (manufactured at the call site by `letI := (Subsemiring.inclusion h).toAlgebra` and
`IsScalarTower.of_algebraMap_eq fun _ => rfl`); the intended ones are the canonical inclusion
instances, and the proof may use that the induced embeddings are the inclusions into `Ω`. -/
theorem inertia_eq_bot_of_sup {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (M₀ L₀ : IntermediateField k Ω)
    [NumberField ↥M₀] [FiniteDimensional k ↥M₀] [IsGalois k ↥M₀]
    [NumberField ↥L₀] [FiniteDimensional k ↥L₀] [IsGalois k ↥L₀]
    [Algebra ↥M₀ ↥L] [IsScalarTower k ↥M₀ ↥L] [Algebra ↥L₀ ↥L] [IsScalarTower k ↥L₀ ↥L]
    (hgenL : L.restrictScalars k ≤ (IsScalarTower.toAlgHom k K Ω).fieldRange ⊔ L₀ ⊔ M₀)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : q'.asIdeal.LiesOver q.asIdeal)
    (wM : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M₀))
    (hwM : q'.asIdeal.LiesOver wM.asIdeal)
    (hunrM : wM.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1)
    (wL : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L₀))
    (hwL : q'.asIdeal.LiesOver wL.asIdeal)
    (hunrL : wL.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) :
    Ideal.inertia (↥L ≃ₐ[K] ↥L) q'.asIdeal = ⊥ := by
  classical
  -- The inclusion `↥L →ₐ[k] Ω` and the two `k`-algebra maps `↥M₀ → ↥L`, `↥L₀ → ↥L`.
  let φ : ↥L →ₐ[k] Ω := (L.restrictScalars k).val
  have hφrange : φ.fieldRange = L.restrictScalars k := IntermediateField.fieldRange_val _
  let ψM : ↥M₀ →ₐ[k] ↥L := IsScalarTower.toAlgHom k ↥M₀ ↥L
  let ψL : ↥L₀ →ₐ[k] ↥L := IsScalarTower.toAlgHom k ↥L₀ ↥L
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  -- ## Step 1: `σ` is inertial as a `k`-automorphism of `↥L`.
  have hIn : SSGRoute.PTExt.IsInertiaAt q' (AlgEquiv.restrictScalars k σ) :=
    Work.SSGRoute.E9CaseB.isInertiaAt_restrictScalars q' hσ
  -- ## Step 2: `σ` restricts to the identity on `M₀` and on `L₀`.
  have hτM : AlgEquiv.restrictNormalHom ↥M₀ (AlgEquiv.restrictScalars k σ) = 1 :=
    restrictNormalHom_eq_one_of_isInertiaAt (E := ↥M₀) (L := ↥L) (k := k) q' wM hwM hunrM
      (AlgEquiv.restrictScalars k σ) hIn
  have hτL : AlgEquiv.restrictNormalHom ↥L₀ (AlgEquiv.restrictScalars k σ) = 1 :=
    restrictNormalHom_eq_one_of_isInertiaAt (E := ↥L₀) (L := ↥L) (k := k) q' wL hwL hunrL
      (AlgEquiv.restrictScalars k σ) hIn
  -- ## Step 3: `σ` fixes pointwise the images of `M₀`, `L₀` and of `K` in `↥L`.
  have hfixM : ∀ m : ↥M₀, σ (ψM m) = ψM m := by
    intro m
    have h := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars k σ) ↥M₀ m
    have h4 : ((AlgEquiv.restrictScalars k σ).restrictNormal ↥M₀) m = m := by
      have h5 : (AlgEquiv.restrictScalars k σ).restrictNormal ↥M₀ = 1 := hτM
      rw [h5]
      rfl
    rw [h4, AlgEquiv.restrictScalars_apply] at h
    exact h.symm
  have hfixL : ∀ m : ↥L₀, σ (ψL m) = ψL m := by
    intro m
    have h := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars k σ) ↥L₀ m
    have h4 : ((AlgEquiv.restrictScalars k σ).restrictNormal ↥L₀) m = m := by
      have h5 : (AlgEquiv.restrictScalars k σ).restrictNormal ↥L₀ = 1 := hτL
      rw [h5]
      rfl
    rw [h4, AlgEquiv.restrictScalars_apply] at h
    exact h.symm
  have hfixK : ∀ y : K, σ (algebraMap K ↥L y) = algebraMap K ↥L y := fun y => σ.commutes y
  -- ## Step 4: `M₀`, `L₀` and the image of `K` are contained in `L`, and they generate `L`.
  have hfrM : (φ.comp ψM).fieldRange = M₀ := AlgHom.fieldRange_of_normal (E := M₀) (φ.comp ψM)
  have hfrL : (φ.comp ψL).fieldRange = L₀ := AlgHom.fieldRange_of_normal (E := L₀) (φ.comp ψL)
  have hMle : M₀ ≤ L.restrictScalars k := by
    rw [← hfrM]
    intro x hx
    rw [AlgHom.mem_fieldRange] at hx
    obtain ⟨m, rfl⟩ := hx
    show ((ψM m : ↥L) : Ω) ∈ L
    exact (ψM m).2
  have hLle : L₀ ≤ L.restrictScalars k := by
    rw [← hfrL]
    intro x hx
    rw [AlgHom.mem_fieldRange] at hx
    obtain ⟨m, rfl⟩ := hx
    show ((ψL m : ↥L) : Ω) ∈ L
    exact (ψL m).2
  have hAle : (IsScalarTower.toAlgHom k K Ω).fieldRange ≤ L.restrictScalars k := by
    intro x hx
    rw [AlgHom.mem_fieldRange] at hx
    obtain ⟨y, rfl⟩ := hx
    show algebraMap K Ω y ∈ L
    exact L.algebraMap_mem y
  have hsupEq : (IsScalarTower.toAlgHom k K Ω).fieldRange ⊔ L₀ ⊔ M₀ = L.restrictScalars k :=
    le_antisymm (sup_le (sup_le hAle hLle) hMle) hgenL
  -- ## Step 5: `map φ` of the "comap" fields is the original field.
  have hmapS : ∀ S : IntermediateField k Ω, S ≤ L.restrictScalars k → (S.comap φ).map φ = S := by
    intro S hS
    apply le_antisymm
    · intro y hy
      rw [IntermediateField.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hx
    · intro y hy
      rw [IntermediateField.mem_map]
      have hy' : y ∈ φ.fieldRange := by rw [hφrange]; exact hS hy
      rw [AlgHom.mem_fieldRange] at hy'
      obtain ⟨x, rfl⟩ := hy'
      exact ⟨x, hy, rfl⟩
  have hWmap :
      ((IsScalarTower.toAlgHom k K Ω).fieldRange.comap φ ⊔ L₀.comap φ ⊔ M₀.comap φ).map φ
        = (IsScalarTower.toAlgHom k K Ω).fieldRange ⊔ L₀ ⊔ M₀ := by
    rw [IntermediateField.map_sup, IntermediateField.map_sup, hmapS _ hAle, hmapS _ hLle,
      hmapS _ hMle]
  -- ## Step 6: the comap fields generate `↥L`.
  have htop : (⊤ : IntermediateField k ↥L) ≤
      (IsScalarTower.toAlgHom k K Ω).fieldRange.comap φ ⊔ L₀.comap φ ⊔ M₀.comap φ := by
    intro x _
    have hx1 : (x : Ω) ∈
        ((IsScalarTower.toAlgHom k K Ω).fieldRange.comap φ ⊔ L₀.comap φ ⊔ M₀.comap φ).map φ := by
      rw [hWmap, hsupEq]
      exact x.2
    rw [IntermediateField.mem_map] at hx1
    obtain ⟨w, hw, hwx⟩ := hx1
    have hwx' : w = x := Subtype.ext hwx
    simpa [hwx'] using hw
  -- ## Step 7: `σ` fixes each of the three comap fields pointwise.
  have hfixA' : ∀ x ∈ (IsScalarTower.toAlgHom k K Ω).fieldRange.comap φ, σ x = x := by
    intro x hx
    have hx' : φ x ∈ (IsScalarTower.toAlgHom k K Ω).fieldRange := hx
    rw [AlgHom.mem_fieldRange] at hx'
    obtain ⟨y, hy⟩ := hx'
    change algebraMap K Ω y = (x : Ω) at hy
    have hyx : algebraMap K ↥L y = x := by
      apply Subtype.ext
      change algebraMap K Ω y = (x : Ω)
      exact hy
    rw [← hyx]
    exact hfixK y
  have hfixM' : ∀ x ∈ M₀.comap φ, σ x = x := by
    intro x hx
    have hxM : φ x ∈ M₀ := hx
    have hx' : φ x ∈ (φ.comp ψM).fieldRange := by rw [hfrM]; exact hxM
    rw [AlgHom.mem_fieldRange] at hx'
    obtain ⟨m, hm⟩ := hx'
    have hmx : ψM m = x := Subtype.ext hm
    rw [← hmx]
    exact hfixM m
  have hfixL0' : ∀ x ∈ L₀.comap φ, σ x = x := by
    intro x hx
    have hxL : φ x ∈ L₀ := hx
    have hx' : φ x ∈ (φ.comp ψL).fieldRange := by rw [hfrL]; exact hxL
    rw [AlgHom.mem_fieldRange] at hx'
    obtain ⟨m, hm⟩ := hx'
    have hmx : ψL m = x := Subtype.ext hm
    rw [← hmx]
    exact hfixL m
  -- ## Step 8: conclude.
  have hσfix : AlgEquiv.restrictScalars k σ ∈ ((IsScalarTower.toAlgHom k K Ω).fieldRange.comap φ
      ⊔ L₀.comap φ ⊔ M₀.comap φ).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_sup]
    simp only [SetLike.mem_coe, Subgroup.mem_inf, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨⟨hfixA', hfixL0'⟩, hfixM'⟩
  have hmem : AlgEquiv.restrictScalars k σ ∈ (⊤ : IntermediateField k ↥L).fixingSubgroup :=
    IntermediateField.fixingSubgroup_le htop hσfix
  rw [IntermediateField.fixingSubgroup_top] at hmem
  have hσ'1 : AlgEquiv.restrictScalars k σ = 1 := Subgroup.mem_bot.mp hmem
  refine AlgEquiv.ext fun x => ?_
  have h := congrArg (fun f : ↥L ≃ₐ[k] ↥L => f x) hσ'1
  rw [AlgEquiv.restrictScalars_apply] at h
  simpa using h

end Work.SSGRoute.Sha2Lib
