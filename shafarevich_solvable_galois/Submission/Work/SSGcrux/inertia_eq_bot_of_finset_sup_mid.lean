import Mathlib
import Submission.Work.SSGRoute.E9Nodes.e9_baseS
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGcrux

set_option linter.style.haveILetI false

/-- If `σ` fixes pointwise each member of a finite family of intermediate fields, then `σ` fixes
pointwise their supremum (compositum). -/
private lemma mem_fixingSubgroup_finset_sup {F E : Type*} [Field F] [Field E] [Algebra F E]
    {ι : Type} (s : Finset ι) (f : ι → IntermediateField F E) (σ : E ≃ₐ[F] E)
    (h : ∀ i ∈ s, σ ∈ (f i).fixingSubgroup) : σ ∈ (s.sup f).fixingSubgroup := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sup_insert, IntermediateField.fixingSubgroup_sup]
      exact ⟨h a (Finset.mem_insert_self a s),
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

/-- **Inertia restricts to a subextension.**  Let `k ⊆ E ⊆ L` be a tower of number fields, `q` a
prime of `𝓞 L` lying over `qE` in `𝓞 E`, `σ : L ≃ₐ[k] L` inertial at `q` and `τ : E ≃ₐ[k] E` its
restriction (embedded along the tower, `hcomm`).  Then `τ` is inertial at `qE`.

This is `Work.SSGRoute.E9Nodes.e9_inertia_restrict` without the (unused) hypothesis
`FiniteDimensional E L`; no Galois-ness of `L/k` or of `L/E` is used.  For `x ∈ 𝓞 E` put
`z = τ x - x ∈ 𝓞 E`; the compatibility `hcomm` shows that the image of `z` in `𝓞 L` is
`σ y - y` for `y` the image of `x`, which lies in `q` since `σ` is inertial at `q`; contracting
along `q ⊇ qE` gives `z ∈ qE`. -/
private theorem inertiaAt_restrict {k E L : Type} [Field k] [NumberField k] [Field E]
    [NumberField E] [Algebra k E] [Field L] [NumberField L] [Algebra k L] [Algebra E L]
    [IsScalarTower k E L]
    (qE : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver qE.asIdeal)
    (σ : L ≃ₐ[k] L) (τ : E ≃ₐ[k] E)
    (hcomm : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (τ x))
    (hσ : SSGRoute.PTExt.IsInertiaAt q σ) :
    SSGRoute.PTExt.IsInertiaAt qE τ := by
  intro x
  set z : NumberField.RingOfIntegers E :=
    NumberField.RingOfIntegers.mapRingEquiv (τ : E ≃+* E) x - x with hz
  have hzE : (z : E) = τ (x : E) - (x : E) := by simp [hz]
  rw [← hzE]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  have hunder : qE.asIdeal = Ideal.under (NumberField.RingOfIntegers E) q.asIdeal := hq.over
  rw [hunder, Ideal.under, Ideal.mem_comap]
  set y : NumberField.RingOfIntegers L :=
    algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers L) x with hy
  have hyL : (y : L) = algebraMap E L (x : E) := rfl
  refine (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) q
    (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers L) z)).mp ?_
  show q.valuation L (algebraMap E L (z : E)) < 1
  have harg : algebraMap E L (z : E) = σ (y : L) - (y : L) := by
    rw [hyL, hzE, map_sub, hcomm (x : E)]
  rw [harg]
  exact hσ y

/-- **The inertia subgroup is trivial in a compositum of finitely many `K`-Galois subextensions
each unramified at the prime below `q'`.** -/
theorem inertia_eq_bot_of_finset_sup_mid {k K Ω : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    {ι : Type} [Fintype ι] (Lᵢ : ι → IntermediateField K Ω)
    [∀ i, NumberField ↥(Lᵢ i)] [∀ i, FiniteDimensional K ↥(Lᵢ i)] [∀ i, IsGalois K ↥(Lᵢ i)]
    [∀ i, Algebra ↥(Lᵢ i) ↥L] [∀ i, IsScalarTower K ↥(Lᵢ i) ↥L]
    (hgenL : Finset.univ.sup Lᵢ = L)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : q'.asIdeal.LiesOver q.asIdeal)
    (w : ∀ i, IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Lᵢ i)))
    (hw : ∀ i, q'.asIdeal.LiesOver (w i).asIdeal)
    (hunr : ∀ i, (w i).asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    Ideal.inertia (↥L ≃ₐ[K] ↥L) q'.asIdeal = ⊥ := by
  classical
  -- The inclusion `↥L →ₐ[K] Ω` and, for every `i`, the inclusion `↥(Lᵢ i) →ₐ[K] ↥L`.
  let φ : ↥L →ₐ[K] Ω := L.val
  have hφrange : φ.fieldRange = L := IntermediateField.fieldRange_val L
  let ψ : (i : ι) → ↥(Lᵢ i) →ₐ[K] ↥L := fun i => IsScalarTower.toAlgHom K ↥(Lᵢ i) ↥L
  -- The image of `↥(Lᵢ i)` in `Ω` under the composite is exactly `Lᵢ i`.
  have hfr : ∀ i, (φ.comp (ψ i)).fieldRange = Lᵢ i :=
    fun i => AlgHom.fieldRange_of_normal (E := Lᵢ i) (φ.comp (ψ i))
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  have hIn : SSGRoute.PTExt.IsInertiaAt q' σ :=
    (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := K) (K := ↥L) q' σ).mpr hσ
  -- ## Step 1: `σ` fixes each `↥(Lᵢ i)` pointwise.
  have hfix : ∀ i (m : ↥(Lᵢ i)), σ (ψ i m) = ψ i m := by
    intro i m
    have hcomm : ∀ x : ↥(Lᵢ i),
        σ (algebraMap ↥(Lᵢ i) ↥L x) = algebraMap ↥(Lᵢ i) ↥L
          ((AlgEquiv.restrictNormalHom ↥(Lᵢ i) σ) x) :=
      fun x => (AlgEquiv.restrictNormal_commutes σ (↥(Lᵢ i)) x).symm
    have hτin : SSGRoute.PTExt.IsInertiaAt (w i)
        (AlgEquiv.restrictNormalHom ↥(Lᵢ i) σ) :=
      inertiaAt_restrict (k := K) (E := ↥(Lᵢ i)) (L := ↥L) (w i) q' (hw i) σ
        (AlgEquiv.restrictNormalHom ↥(Lᵢ i) σ) hcomm hIn
    have hPover : q.asIdeal = Ideal.under (NumberField.RingOfIntegers K) (w i).asIdeal := by
      rw [hq'.over, (hw i).over, Ideal.under_under]
    haveI : (w i).asIdeal.LiesOver q.asIdeal := ⟨hPover⟩
    haveI : q.asIdeal.IsPrime := q.isPrime
    haveI : (w i).asIdeal.IsPrime := (w i).isPrime
    have hmem : AlgEquiv.restrictNormalHom ↥(Lᵢ i) σ ∈
        Ideal.inertia (↥(Lᵢ i) ≃ₐ[K] ↥(Lᵢ i)) (w i).asIdeal :=
      (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := K) (K := ↥(Lᵢ i))
        (w i) _).mp hτin
    have hbot : Ideal.inertia (↥(Lᵢ i) ≃ₐ[K] ↥(Lᵢ i)) (w i).asIdeal = ⊥ :=
      (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
        (F := K) (K := ↥(Lᵢ i)) q.asIdeal (w i).asIdeal).mpr (hunr i)
    rw [hbot] at hmem
    have hτ1 : AlgEquiv.restrictNormalHom ↥(Lᵢ i) σ = 1 := Subgroup.mem_bot.mp hmem
    have h := AlgEquiv.restrictNormal_commutes σ (↥(Lᵢ i)) m
    have h5 : (σ.restrictNormal ↥(Lᵢ i)) = 1 := hτ1
    rw [h5] at h
    have hψ : ψ i m = algebraMap ↥(Lᵢ i) ↥L m := rfl
    rw [hψ]
    simpa using h.symm
  -- ## Step 2: `Lᵢ i` is contained in `L`.
  have hGle : ∀ i, Lᵢ i ≤ L := by
    intro i
    rw [← hgenL]
    exact Finset.le_sup (f := Lᵢ) (Finset.mem_univ i)
  -- ## Step 3: the "comap" fields generate `↥L`.
  have hmapS : ∀ S : IntermediateField K Ω, S ≤ L → (S.comap φ).map φ = S :=
    fun S hS => IntermediateField.map_comap_eq_self (f := φ) (by rw [hφrange]; exact hS)
  have hmapF : (Finset.univ.sup fun i => (Lᵢ i).comap φ).map φ = Finset.univ.sup Lᵢ := by
    rw [Finset.sup_univ_eq_iSup (f := fun i => (Lᵢ i).comap φ), IntermediateField.map_iSup,
      Finset.sup_univ_eq_iSup (f := Lᵢ)]
    exact iSup_congr fun i => hmapS (Lᵢ i) (hGle i)
  have htop : (⊤ : IntermediateField K ↥L) ≤ Finset.univ.sup (fun i => (Lᵢ i).comap φ) := by
    intro x _
    have hx1 : (x : Ω) ∈ (Finset.univ.sup (fun i => (Lᵢ i).comap φ)).map φ := by
      rw [hmapF, hgenL]
      exact x.2
    rw [IntermediateField.mem_map] at hx1
    obtain ⟨y, hy, hyx⟩ := hx1
    have hyx' : y = x := Subtype.ext hyx
    simpa [hyx'] using hy
  -- ## Step 4: `σ` fixes each comap field pointwise.
  have hfixFi : ∀ i, ∀ x ∈ (Lᵢ i).comap φ, σ x = x := by
    intro i x hx
    have hxL : φ x ∈ Lᵢ i := hx
    have hx' : φ x ∈ (φ.comp (ψ i)).fieldRange := by rw [hfr i]; exact hxL
    rw [AlgHom.mem_fieldRange] at hx'
    obtain ⟨m, hm⟩ := hx'
    have hmx : ψ i m = x := Subtype.ext hm
    rw [← hmx]
    exact hfix i m
  -- ## Step 5: conclude.
  have hmem : σ ∈ (Finset.univ.sup (fun i => (Lᵢ i).comap φ)).fixingSubgroup :=
    mem_fixingSubgroup_finset_sup Finset.univ _ σ
      (fun i _ => (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr (hfixFi i))
  have hmem' : σ ∈ (⊤ : IntermediateField K ↥L).fixingSubgroup :=
    IntermediateField.fixingSubgroup_le htop hmem
  rw [IntermediateField.fixingSubgroup_top] at hmem'
  exact Subgroup.mem_bot.mp hmem'

end Work.SSGcrux
