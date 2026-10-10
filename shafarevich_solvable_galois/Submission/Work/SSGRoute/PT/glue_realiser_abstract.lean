import Mathlib.FieldTheory.KrullTopology
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
import Submission.Work.SSGRoute.PT.glue_helpers
import Submission.Work.SSGRoute.PT.inertiaVanishing_conj
import Submission.Work.SSGRoute.PT.vf_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct Pointwise

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-! Guidance from the project lead (the requester):

Lead design (Claude) 10-05 02:30: v4 = v3 over an ABSTRACT dictionary interface, so the type is sorry-free and certifiable now (see _lead_design/v4_0215/NOTE.md). Pieces: SSGRoute/PT/glue_realiser_abstract (G), SSGRoute/PT/valueFormula_abstract (V), SSGRoute/PT/finiteS_converse_canonical_v4 (A = G + V + phi1_mono_sylow_in + pt_extSegment_exact + H4244's odd-p helpers isCoboundaryOn_zpowers_of_ne_two, eq_zero_of_inertia_of_coboundaryOn_of_not_ramified in PT/finiteS_converse_canonical_v3.lean). Request siblings by name. NEVER mention finZB / g1FinHalf / localDictionary_natural_family in any statement you dispatch (they are sorry-tainted).
-/

namespace Work.SSGRoute.PT

/-- Transporting a value along a proof of `a = a` is the identity. -/
theorem eq_mp_congrArg_self {P : Type*} {T : P → Type*} {a : P} (h : a = a) (x : T a) :
    Eq.mp (congrArg T h) x = x := by
  cases h
  rfl

/-- **Splitting a linear functional along the coordinates of a finitely supported family.**

Let `Ψ : X →ₗ (∀ v, Q v)` be a linear map whose values are finitely supported and let
`Φ : X →ₗ ZMod p` vanish on the kernel of `Ψ`.  Then `Φ` is a *locally finite* sum of coordinate
functionals: there are `ν v : Q v →ₗ ZMod p` with `Φ x = ∑ᶠ v, ν v (Ψ x v)` for every `x ∈ X`.

For `x` the family `Ψ x` has finite support, so it is the finite sum of the coordinate elements
`Pi.single v (Ψ x v)`; applying `g` (any linear extension of `Φ` from the range of `Ψ` to the
whole product) gives the claim. -/
theorem exists_coordinate_splitting {p : ℕ} [Fact p.Prime] {ı : Type*} {Q : ı → Type*}
    [∀ v, AddCommGroup (Q v)] [∀ v, Module (ZMod p) (Q v)]
    {X : Type*} [AddCommGroup X] [Module (ZMod p) X]
    (Ψ : X →ₗ[ZMod p] (∀ v, Q v))
    (hfin : ∀ x : X, {v | Ψ x v ≠ 0}.Finite)
    (Φ : X →ₗ[ZMod p] ZMod p)
    (hker : ∀ x : X, Ψ x = 0 → Φ x = 0) :
    ∃ ν : ∀ v, Q v →ₗ[ZMod p] ZMod p, ∀ x : X, ∑ᶠ v, ν v (Ψ x v) = Φ x := by
  classical
  -- the coordinate inclusion `Q v ↪ ∀ v, Q v`
  let singleLM : ∀ v : ı, Q v →ₗ[ZMod p] (∀ w, Q w) := fun v =>
    { toFun := fun q => Pi.single v q
      map_add' := fun a b => by
        funext w
        rcases eq_or_ne w v with h | h
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      map_smul' := fun c a => by
        funext w
        rcases eq_or_ne w v with h | h
        · subst h; simp
        · simp [Pi.single_eq_of_ne h] }
  -- the functional induced by `Φ` on the range of `Ψ`
  let Φ' : ↥(LinearMap.range Ψ) →ₗ[ZMod p] ZMod p :=
    { toFun := fun y => Φ (Classical.choose y.2)
      map_add' := fun y y' => by
        have hy : Ψ (Classical.choose y.2) = (y : ∀ v, Q v) := Classical.choose_spec y.2
        have hy' : Ψ (Classical.choose y'.2) = (y' : ∀ v, Q v) := Classical.choose_spec y'.2
        have hyy : Ψ (Classical.choose (y + y').2) = (y + y' : ∀ v, Q v) :=
          Classical.choose_spec (y + y').2
        have h0 := hker (Classical.choose (y + y').2 -
          (Classical.choose y.2 + Classical.choose y'.2)) (by
            rw [map_sub, map_add, hyy, hy, hy']
            simp)
        rw [map_sub, map_add] at h0
        exact sub_eq_zero.mp h0
      map_smul' := fun c y => by
        have hy : Ψ (Classical.choose y.2) = (y : ∀ v, Q v) := Classical.choose_spec y.2
        have hcy : Ψ (Classical.choose (c • y).2) = (c • y : ∀ v, Q v) :=
          Classical.choose_spec (c • y).2
        have h0 := hker (Classical.choose (c • y).2 - c • Classical.choose y.2) (by
          rw [map_sub, map_smul, hcy, hy]
          simp)
        rw [map_sub, map_smul] at h0
        exact sub_eq_zero.mp h0 }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend Φ'
  refine ⟨fun v => g.comp (singleLM v), fun x => ?_⟩
  -- `g` computes `Φ` on the range of `Ψ`
  have hΦ' : ∀ y : ↥(LinearMap.range Ψ), Φ' y = Φ (Classical.choose y.2) := fun y => rfl
  have hgx : g (Ψ x) = Φ x := by
    have h1 := LinearMap.congr_fun hg (Ψ.rangeRestrict x)
    rw [LinearMap.comp_apply] at h1
    have h2 : ((LinearMap.range Ψ).subtype (Ψ.rangeRestrict x)) = Ψ x := rfl
    rw [h2, hΦ'] at h1
    -- `h1 : g (Ψ x) = Φ (Classical.choose (Ψ.rangeRestrict x).2)`
    set x' := Classical.choose (Ψ.rangeRestrict x).2 with hx'def
    have hx' : Ψ x' = Ψ x := by
      have h := Classical.choose_spec (Ψ.rangeRestrict x).2
      simpa [x'] using h
    have h0 := hker (x' - x) (by rw [map_sub, hx', sub_self])
    rw [map_sub] at h0
    rw [h1, sub_eq_zero.mp h0]
  -- `Ψ x` is the finite sum of its coordinate elements
  obtain ⟨T, hT⟩ : ∃ T : Finset ı, ∀ v, v ∈ T ↔ Ψ x v ≠ 0 :=
    ⟨(hfin x).toFinset, fun v => (hfin x).mem_toFinset⟩
  have hsum : (∑ v ∈ T, singleLM v (Ψ x v)) = Ψ x := by
    funext w
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single w]
    · exact Pi.single_eq_same w (Ψ x w)
    · intro b _ hbw
      exact Pi.single_eq_of_ne (Ne.symm hbw) (Ψ x b)
    · intro hw
      have h0 : Ψ x w = 0 := by
        by_contra h
        exact hw ((hT w).mpr h)
      show (Pi.single w (Ψ x w) : ∀ u, Q u) w = 0
      rw [h0]
      exact Pi.single_eq_same w (0 : Q w)
  have hsupp : Function.support (fun v => (g.comp (singleLM v)) (Ψ x v)) ⊆ ↑T := by
    intro v hv
    by_contra hc
    rw [Function.mem_support] at hv
    refine hv ?_
    have h0 : Ψ x v = 0 := by
      by_contra h
      exact hc ((hT v).mpr h)
    rw [h0, map_zero]
  have hgsum : g (∑ v ∈ T, singleLM v (Ψ x v)) = ∑ v ∈ T, (g.comp (singleLM v)) (Ψ x v) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun v _ => rfl
  calc ∑ᶠ v, (g.comp (singleLM v)) (Ψ x v)
      = ∑ v ∈ T, (g.comp (singleLM v)) (Ψ x v) := finsum_eq_sum_of_support_subset _ hsupp
    _ = g (∑ v ∈ T, singleLM v (Ψ x v)) := hgsum.symm
    _ = g (Ψ x) := by rw [hsum]
    _ = Φ x := hgx

/-- **Conjugate places of `K` below non-conjugate places of `Ω`.**

If the places of `K` below two finite places `A`, `B` of `Ω` are conjugate then `A` and `B` are
themselves `Gal(Ω/k)`-conjugate.  This is the converse of `PT.ofFinite_finQW_smul` and is what
makes the assignment `v ↦ ofFinite (finQ K v)` injective up to conjugacy. -/
theorem isConjPlace_of_finQ_conj
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (A B : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hB : SSGRoute.IsFinPlace k B)
    (h : ∃ σ : ↥K ≃ₐ[k] ↥K,
      σ • NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA) =
        NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K B hB)) :
    SSGRoute.IsConjPlace k A B := by
  classical
  haveI hGalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨τ, hτ⟩ := Work.SSGRoute.PT.exists_restrictNormal_eq_of_isAlgClosure K σ
  have hA' : SSGRoute.IsFinPlace k (τ • A) := (Work.SSGRoute.isFinPlace_smul_iff A τ).mpr hA
  -- the prime of `𝓞 K` below `τ • A` is the prime below `B`
  have hq : Work.SSGRoute.PT.finQW K (τ • A) hA' = Work.SSGRoute.PT.finQ K B hB := by
    have h1 : NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW K (τ • A) hA') =
        (τ.restrictNormal ↥K) • NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW K A hA) :=
      Work.SSGRoute.PT.ofFinite_finQW_smul K A hA τ hA'
    rw [hτ] at h1
    rw [show NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW K A hA) =
      NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA) from rfl, hσ] at h1
    exact NK.GlobalCFT.Place.ofFinite_inj.mp h1
  -- the traces on `k` agree
  suffices hc : A.comap (algebraMap k Ω) = B.comap (algebraMap k Ω) by
    haveI hSep : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
    exact (Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq (F := k) (E := Ω) A B hc)
  have htr : ∀ X : ValuationSubring Ω,
      X.comap (algebraMap k Ω) =
        (X.comap (algebraMap ↥K Ω)).comap (algebraMap k ↥K) := by
    intro X
    rw [IsScalarTower.algebraMap_eq k ↥K Ω, ← ValuationSubring.comap_comap]
  have hqB : Work.SSGRoute.PT.finQW K B hB = Work.SSGRoute.PT.finQ K B hB := rfl
  rw [htr A, htr B, Work.SSGRoute.PT.finQW_comap K A hA, Work.SSGRoute.PT.finQW_comap K B hB,
    hqB, ← hq]
  -- the valuation ring of `τ • A` is the translate of that of `A`
  have hVA : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K
        (Work.SSGRoute.PT.finQW K (τ • A) hA') =
      (τ.restrictNormal ↥K) •
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K
          (Work.SSGRoute.PT.finQW K A hA) := by
    rw [Work.SSGRoute.PT.finQW_smulHeightOneSpectrum K A hA τ hA',
      ← Work.SSGRoute.PT.smul_valuationSubringAtPrime K (τ.restrictNormal ↥K)
        (Work.SSGRoute.PT.finQW K A hA)]
  rw [hVA, Work.SSGRoute.comap_algebraMap_smul]

/-- **A transversal of the finite places of `Ω` containing a prescribed finite set.**

`R` consists of one place per `Gal(Ω/k)`-conjugacy class of finite places (`SSGRoute.IsConjPlace`),
contains `S` (which must be pairwise non-conjugate), and every finite place of `Ω` is conjugate to
one of its elements. -/
theorem exists_transversal_finPlaces (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B) :
    ∃ R : Set (ValuationSubring Ω),
      (∀ A ∈ S, A ∈ R) ∧ (∀ v ∈ R, SSGRoute.IsFinPlace k v) ∧
      (∀ v ∈ R, ∀ w ∈ R, SSGRoute.IsConjPlace k v w → v = w) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → ∃ v ∈ R, SSGRoute.IsConjPlace k v B) := by
  classical
  letI : MulAction (Ω ≃ₐ[k] Ω) {v : ValuationSubring Ω // SSGRoute.IsFinPlace k v} :=
    { smul := fun σ v => ⟨σ • v.1, (Work.SSGRoute.isFinPlace_smul_iff v.1 σ).mpr v.2⟩
      one_smul := fun v => Subtype.ext (one_smul _ v.1)
      mul_smul := fun σ τ v => Subtype.ext (mul_smul σ τ v.1) }
  obtain ⟨R', hSR', htrans⟩ := exists_transversal_containing_set
    (G := Ω ≃ₐ[k] Ω) (α := {v : ValuationSubring Ω // SSGRoute.IsFinPlace k v})
    (S := Subtype.val ⁻¹' (↑S : Set (ValuationSubring Ω))) (by
      intro a ha b hb hconj
      obtain ⟨σ, hσ⟩ := hconj
      exact Subtype.ext (hSdisj a.1 (Finset.mem_coe.mp ha) b.1 (Finset.mem_coe.mp hb)
        ⟨σ, congrArg Subtype.val hσ⟩))
  refine ⟨Subtype.val '' R', ?_, ?_, ?_, ?_⟩
  · intro A hA
    have hA' : (⟨A, hSfin A hA⟩ : {v // SSGRoute.IsFinPlace k v}) ∈ R' := hSR' (Finset.mem_coe.mpr hA)
    exact ⟨⟨A, hSfin A hA⟩, hA', rfl⟩
  · rintro v ⟨v', hv', rfl⟩
    exact v'.2
  · rintro v ⟨v', hv', rfl⟩ w ⟨w', hw', rfl⟩ hconj
    obtain ⟨σ, hσ⟩ := hconj
    have hσ' : σ • v' = w' := Subtype.ext hσ
    obtain ⟨u, hu, huniq⟩ := htrans v'
    have h1 : (⟨v', hv'⟩ : ↥R') = u := huniq ⟨v', hv'⟩ ⟨1, one_smul _ v'⟩
    have h2 : (⟨w', hw'⟩ : ↥R') = u := huniq ⟨w', hw'⟩ ⟨σ, hσ'⟩
    exact congrArg (fun x : ↥R' => (x.1).1) (h1.trans h2.symm)
  · intro B hB
    obtain ⟨u₂, ⟨σ₂, hσ₂⟩, -⟩ := htrans ⟨B, hB⟩
    have hσ₂' : σ₂ • B = u₂.1.1 := congrArg Subtype.val hσ₂
    exact ⟨u₂.1.1, ⟨u₂, u₂.2, rfl⟩, ⟨σ₂⁻¹, by rw [← hσ₂', inv_smul_smul]⟩⟩

/-- **Orthogonality from vanishing on the inertia of the representatives.**

If a global locally constant `M'`-cocycle `b` vanishes on the inertia of every place of the
transversal `R` outside `S₁`, then it vanishes on the inertia of *every* finite place not conjugate
to `S₁` (vanishing transfers to conjugate places by `inertiaVanishing_conj`, and the places outside
the conjugates of `S₁` are unramified in `K` by `hS₁ram`), so `horth` applies. -/
theorem horth_offRep
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (R : Set (ValuationSubring Ω)) (hRfin : ∀ v ∈ R, SSGRoute.IsFinPlace k v)
    (hRdisj : ∀ v ∈ R, ∀ w ∈ R, SSGRoute.IsConjPlace k v w → v = w)
    (hRcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → ∃ v ∈ R, SSGRoute.IsConjPlace k v B)
    (S₁ : Finset (ValuationSubring Ω)) (hS₁fin : ∀ A ∈ S₁, SSGRoute.IsFinPlace k A)
    (hS₁disj : ∀ A ∈ S₁, ∀ B ∈ S₁, SSGRoute.IsConjPlace k A B → A = B)
    (hS₁ram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S₁, SSGRoute.IsConjPlace k A B)
    (hS₁R : ∀ A ∈ S₁, A ∈ R)
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M)
    (horth : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → b σ = 0) →
      ∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) b = 0)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hbc : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hlc : SSGRoute.IsLocConstOn ⊤ b)
    (hbunr : ∀ v ∈ R, v ∉ S₁ → ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k v σ → b σ = 0) :
    ∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) b = 0 := by
  classical
  refine horth b hbc hlc ?_
  intro B hBfin hBnc σ hσI
  -- `B` is unramified in `K` and does not lie over `p`, since `hS₁ram` would conjugate it to `S₁`
  have hBram : ¬ SSGRoute.IsRamifiedIn k K B := by
    intro hram
    obtain ⟨A₀, hA₀, hconj⟩ := hS₁ram B hBfin (Or.inl hram)
    exact hBnc A₀ hA₀ hconj
  -- a representative `v ∈ R` of the class of `B`
  obtain ⟨v, hvR, τ, hτ⟩ := hRcov B hBfin
  have hvnotin : v ∉ S₁ := by
    intro hvS
    exact hBnc v hvS ⟨τ, hτ⟩
  have hvram : ¬ SSGRoute.IsRamifiedIn k K v := by
    intro hram
    obtain ⟨A₀, hA₀, hconj₂⟩ := hS₁ram v (hRfin v hvR) (Or.inl hram)
    exact hvnotin (hRdisj A₀ (hS₁R A₀ hA₀) v hvR hconj₂ ▸ hA₀)
  -- vanishing transfers from the inertia of `v` to that of the conjugate place `B`
  have hvanish : ∀ τ' : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v τ' → b τ' = 0 :=
    hbunr v hvR hvnotin
  have hBvanish : ∀ τ' : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ' → b τ' = 0 :=
    (inertiaVanishing_conj p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) b hbc
      hvram hBram (σ := τ) hτ).mp hvanish
  exact hBvanish σ hσI

/-- **Additivity of the abstract pairing in its second variable at a finite place.**

The level formula `hpair` pins `pair (decomp k A) a ·` to
`χ L hKL (ι (levelPair (finZF) (finZI) (βl A hA a) (finZH ·)))`, which is additive in the second
(factorised cocycle) variable by `finZH_add` and `chi_iota_levelPair_add_snd`. -/
theorem pair_add_snd_decomp
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (βl : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ((Ω ≃ₐ[k] Ω) → M) →
        CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1)
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hpair : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
        (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        pair (SSGRoute.decomp k A) a b =
          χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
              (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
              (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hb' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b')
    (hbc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hbc' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b') :
    pair (SSGRoute.decomp k A) a (b + b')
      = pair (SSGRoute.decomp k A) a b + pair (SSGRoute.decomp k A) a b' := by
  classical
  obtain ⟨L, hLfin, hLnorm, hKL, b₀, b₀', hb₀, hb₀'⟩ :=
    exists_level_factors_locConstOnTwo k Ω K (SSGRoute.decomp k A) b b' hb hb'
  letI : FiniteDimensional k L := hLfin
  letI : Normal k L := hLnorm
  letI : IsGalois k L := inferInstance
  letI : NumberField L := inferInstance
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hbcadd : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (b + b') :=
    SSGRoute.IsCocycleOn.add hbc hbc'
  have hlcadd : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (b + b') :=
    SSGRoute.IsLocConstOn.add hb hb'
  have hb₀add : ∀ σ ∈ SSGRoute.decomp k A,
      (b + b') σ = (fun τ => b₀ τ + b₀' τ) (AlgEquiv.restrictNormalHom L σ) := by
    intro σ hσ
    rw [Pi.add_apply, hb₀ σ hσ, hb₀' σ hσ]
  rw [hpair A hA a (b + b') ha hlcadd hbcadd L hKL (fun τ => b₀ τ + b₀' τ) hb₀add,
    hpair A hA a b ha hb hbc L hKL b₀ hb₀,
    hpair A hA a b' ha hb' hbc' L hKL b₀' hb₀']
  rw [G1plusLevel.finZH_add p K T M L hKL A hA b b' hbc hbc' hbcadd b₀ b₀' hb₀ hb₀' hb₀add]
  have hptor : ∀ x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T), p • x = 0 :=
    fun x => nsmul_eq_zero_of_zmod p x
  have ht1 : p • Work.SSGRoute.PT.finZH p K T M L hKL A hA b hbc b₀ hb₀ = 0 :=
    Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hptor _
  have ht2 : p • Work.SSGRoute.PT.finZH p K T M L hKL A hA b' hbc' b₀' hb₀' = 0 :=
    Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hptor _
  exact chi_iota_levelPair_add_snd p (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) (χ L hKL)
    (hχadd L hKL) (finZF hKL A hA) (finZI hKL A hA) (βl A hA a)
    (finZH p K T M L hKL A hA b hbc b₀ hb₀) (finZH p K T M L hKL A hA b' hbc' b₀' hb₀')
    ht1 ht2

/-- **An additive map between `ZMod p`-modules is `ZMod p`-linear.**

`c • x = (c.val) • x` for a `ZMod p`-module, and an additive map is compatible with `ℕ`-multiples;
since `((c.val : ℕ) : ZMod p) = c`, the scalar compatibility follows. -/
theorem zmodLinearMap_of_addHom {p : ℕ} [Fact p.Prime] {X Y : Type*} [AddCommGroup X]
    [Module (ZMod p) X] [AddCommGroup Y] [Module (ZMod p) Y] (f : X →+ Y) :
    ∃ g : X →ₗ[ZMod p] Y, ∀ x, g x = f x := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨{ toFun := f, map_add' := f.map_add, map_smul' := fun c x => ?_ }, fun x => rfl⟩
  have h1 : ∀ n : ℕ, f (n • x) = n • f x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul, f.map_add, ih, succ_nsmul]
  have h2 : c • x = c.val • x := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) c.val x, ZMod.natCast_zmod_val]
  rw [h2, h1 c.val, ← Nat.cast_smul_eq_nsmul (ZMod p) c.val (f x), ZMod.natCast_zmod_val]
  rfl

/-- v4 piece G (glue and realiser), against an abstract dictionary interface.

`βl` and `pair` are variables, constrained only by the spec clauses the route uses: additivity, kernel
and onto for `βl`; unramified classes go to unramified `Ext` classes; the level-value formula
`hpair` (the defining equation of `G1pOwn.finAtLevel`, with `βl` in place of `PT.finZB`); vanishing
of `pair` at involutions (odd `p`); and orthogonality of two unramified classes.  So the type
mentions no `Classical.choose` of a `sorry`, and the instance `βl := PT.finZB`,
`pair := G1pOwn.g1FinHalf χ` (plus the involution branch) comes from `PT.finZB_spec` and the
`finAtValue`/`finAtLevel` unfolding results.

Statement.  Given local data `α` at `S₁` that is orthogonal to the global `M'`-cocycles unramified
outside `S₁`, there are:
* a transversal `R ⊇ S₁` of the finite places (one per prime of `k`);
* unramified local cocycles `α'` at the places of `R \ S₁`, extending `α`, such that the sum of the
  pairings vanishes against **every** global locally constant `M'`-cocycle;
* a glued class `X ∈ Ext¹_Γ(M', 𝕀_K)` with components `βl (α' v)` at `R` and `0` at the infinite
  places.

Route.
(1) Take `R := S₁ ∪ (one place per remaining prime)`.
(2) `λ(b) := Σ_{S₁} pair(α_A, b)` is additive in `b` and kills the cocycles unramified outside `S₁`
(`horth`).  So it factors through `b ↦ (class of b|_{I_u})_{u ∈ R \ S₁}`, which lands in a direct sum
(each global `b` is ramified at finitely many places).  Extend linearly and split into functionals
`λ_u` on local classes at `u` that kill the unramified ones.
(3) `hreal_unr` at each `u ∈ R \ S₁` (good: `S₁` covers `p` and `Ram(K)`) gives unramified `α'_u`
with `pair(α'_u, ·) = -λ_u`.  Then `Σᶠ_R pair(α' v, b) = λ(b) - Σ_u λ_u(b) = 0`, with finite
support by `hpair_unr`.
(4) Glue: `ext_idele_shapiro` (third clause) with the transversal `{finQ K v}` of finite places of
`K`, plus the infinite places.  The components `βl (α'_u)` are unramified for `u ∉ S₁` by `hβl_unr`,
so they are almost all unramified. -/
theorem glue_realiser_abstract (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hp2 : p ≠ 2)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L hKL u = 0 → u = 0)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L'] [FiniteDimensional k L']
      [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (βl : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ((Ω ≃ₐ[k] Ω) → M) →
        CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1)
    (hβl_add : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b b' : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      βl A hA (b + b') = βl A hA b + βl A hA b')
    (hβl_ker : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (βl A hA b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (hβl_onto : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) y,
      ∃ b : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ βl A hA b = y)
    (hβl_unr : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (βl A hA b))
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hpair : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
        (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        pair (SSGRoute.decomp k A) a b =
          χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
              (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
              (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))))
    (hpairC : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      pair (Subgroup.zpowers c) a b = 0)
    (hpair_unr : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0) →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        pair (SSGRoute.decomp k A) a b = 0)
    (hreal_unr : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ lam : ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p,
        (∀ b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
          lam (b + b') = lam b + lam b') →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b → lam b = 0) →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) → lam b = 0) →
        ∃ a : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a ∧
          (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0) ∧
          ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            pair (SSGRoute.decomp k A) a b = lam b)
    (S₁ : Finset (ValuationSubring Ω)) (hS₁fin : ∀ A ∈ S₁, SSGRoute.IsFinPlace k A)
    (hS₁disj : ∀ A ∈ S₁, ∀ B ∈ S₁, SSGRoute.IsConjPlace k A B → A = B)
    (hS₁ram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S₁, SSGRoute.IsConjPlace k A B)
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M)
    (hα : ∀ A ∈ S₁, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (horth : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → b σ = 0) →
      ∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) b = 0) :
    ∃ (R : Set (ValuationSubring Ω)) (hRfin : ∀ v ∈ R, SSGRoute.IsFinPlace k v),
      (∀ A ∈ S₁, A ∈ R) ∧
      (∀ v ∈ R, ∀ w ∈ R, SSGRoute.IsConjPlace k v w → v = w) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → ∃ v ∈ R, SSGRoute.IsConjPlace k v B) ∧
      ∃ α' : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M,
        (∀ A ∈ S₁, α' A = α A) ∧
        (∀ v ∈ R, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v) (α' v) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k v) (α' v)) ∧
        (∀ v ∈ R, v ∉ S₁ → ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k v σ → α' v σ = 0) ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          ∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ R), pair (SSGRoute.decomp k v) (α' v) b = 0) ∧
        ∃ X : CategoryTheory.Abelian.Ext (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) (SSGRoute.PTExt.idelesK k ↥K) 1,
          (∀ (v : ValuationSubring Ω) (hv : v ∈ R),
          SSGRoute.PTExt.extLoc (k := k)
              (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv))) X =
            βl v (hRfin v hv) (α' v)) ∧
        (∀ w : NK.GlobalCFT.Place K,
          (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
            w ≠ NK.GlobalCFT.Place.ofFinite q) → SSGRoute.PTExt.extLoc (k := k) w X = 0) := by
  classical
  -- ## 1. the transversal `R` of the finite places, containing `S₁`
  obtain ⟨R, hS₁R, hRfin, hRdisj, hRcov⟩ := exists_transversal_finPlaces k Ω S₁ hS₁fin hS₁disj
  -- ## 2. the places of `R` outside `S₁` are good (unramified in `K`, not over `p`)
  have hRne : ∀ v ∈ R, v ∉ S₁ → ¬ SSGRoute.IsRamifiedIn k K v ∧ ¬ v.valuation (p : Ω) < 1 := by
    intro v hvR hvS
    constructor
    · intro hram
      obtain ⟨A₀, hA₀, hconj⟩ := hS₁ram v (hRfin v hvR) (Or.inl hram)
      exact hvS (hRdisj A₀ (hS₁R A₀ hA₀) v hvR hconj ▸ hA₀)
    · intro hval
      obtain ⟨A₀, hA₀, hconj⟩ := hS₁ram v (hRfin v hvR) (Or.inr hval)
      exact hvS (hRdisj A₀ (hS₁R A₀ hA₀) v hvR hconj ▸ hA₀)
  -- ## 3. the coefficient module, the global cocycles, and the local quotients
  let M' := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)
  let F := (Ω ≃ₐ[k] Ω) → M'
  let Z := Work.SSGRoute.lcCocycles p k Ω K M' ⊤
  let ı := {v : ValuationSubring Ω // v ∈ R ∧ v ∉ S₁}
  let Kv : ValuationSubring Ω → Submodule (ZMod p) F := fun v =>
    { carrier := {f : F | ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v σ → f σ = 0}
      zero_mem' := fun σ _ => rfl
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_setOf_eq] at hf hg ⊢
        intro σ hσ
        rw [Pi.add_apply, hf σ hσ, hg σ hσ, add_zero]
      smul_mem' := fun c {f} hf => by
        simp only [Set.mem_setOf_eq] at hf ⊢
        intro σ hσ
        rw [Pi.smul_apply, hf σ hσ, smul_zero] }
  let Ψ : ↥Z →ₗ[ZMod p] (∀ v : ı, F ⧸ Kv v.1) :=
    LinearMap.pi (fun v : ı => (Kv v.1).mkQ.comp Z.subtype)
  -- ## 4. monotonicity of the two predicates in the subgroup
  have hmono_loc : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)) (f : F), SSGRoute.IsLocConstOn ⊤ f →
      SSGRoute.IsLocConstOn H f := by
    intro H f hf
    obtain ⟨U, hUo, hU⟩ := hf
    exact ⟨U, hUo, fun g _ u hu _ => hU g trivial u hu trivial⟩
  have hmono_coc : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)) (f : F),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ f →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) H f := by
    intro H f hf
    exact fun g _ h _ => hf g trivial h trivial
  -- ## 5. `Ψ` has finitely supported values
  have hsupp : ∀ x : ↥Z, {v : ı | Ψ x v ≠ 0}.Finite := by
    intro x
    have hxc : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ (x.1 : F) := x.2.1
    have hxl : SSGRoute.IsLocConstOn ⊤ (x.1 : F) := x.2.2
    obtain ⟨Sb, hSbfin, hSbdisj, hSbvanish⟩ :=
      vanishingInertia_finite k Ω K M' (x.1 : F) hxc hxl
    have hmem : ∀ v : ı, Ψ x v ≠ 0 → ∃ A ∈ Sb, SSGRoute.IsConjPlace k A v.1 := by
      intro v hv
      by_contra hno
      push_neg at hno
      have hKv : (x.1 : F) ∈ Kv v.1 := by
        show ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v.1 σ → (x.1 : F) σ = 0
        exact fun σ hσ => hSbvanish v.1 (hRfin v.1 v.2.1) hno σ hσ
      have hzero : Ψ x v = 0 := by
        rw [show Ψ x v = (Kv v.1).mkQ (x.1 : F) from rfl, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact hKv
      exact hv hzero
    let g : ↥{v : ı | Ψ x v ≠ 0} → ↥Sb :=
      fun v => ⟨Classical.choose (hmem v.1 v.2), (Classical.choose_spec (hmem v.1 v.2)).1⟩
    have hginj : Function.Injective g := by
      intro v w hvw
      have hv1 : SSGRoute.IsConjPlace k (Classical.choose (hmem v.1 v.2)) v.1.1 :=
        (Classical.choose_spec (hmem v.1 v.2)).2
      have hw1 : SSGRoute.IsConjPlace k (Classical.choose (hmem w.1 w.2)) w.1.1 :=
        (Classical.choose_spec (hmem w.1 w.2)).2
      have hab : Classical.choose (hmem v.1 v.2) = Classical.choose (hmem w.1 w.2) :=
        congrArg Subtype.val hvw
      have hconj : SSGRoute.IsConjPlace k v.1.1 w.1.1 := by
        obtain ⟨s1, hs1⟩ := hv1
        obtain ⟨s2, hs2⟩ := hw1
        refine ⟨s2 * s1⁻¹, ?_⟩
        calc (s2 * s1⁻¹) • v.1.1 = s2 • (s1⁻¹ • v.1.1) := mul_smul _ _ _
          _ = s2 • (s1⁻¹ • (s1 • Classical.choose (hmem v.1 v.2))) := by rw [hs1]
          _ = s2 • Classical.choose (hmem v.1 v.2) := by rw [inv_smul_smul]
          _ = s2 • Classical.choose (hmem w.1 w.2) := by rw [hab]
          _ = w.1.1 := hs2
      exact Subtype.ext (Subtype.ext (hRdisj v.1.1 v.1.2.1 w.1.1 w.1.2.1 hconj))
    haveI : Finite ↥Sb := Sb.finite_toSet.to_subtype
    exact Finite.of_injective g hginj
  -- ## 6. the functional `Λ = ∑_{A ∈ S₁} pair (decomp k A) (α A) ·`
  have hpair_zero : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M), SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      pair (SSGRoute.decomp k A) a 0 = 0 := by
    intro A hA a ha
    have h0lc : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (0 : F) :=
      ⟨⊤, isOpen_univ, fun _ _ _ _ _ => rfl⟩
    have h0c : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (0 : F) :=
      fun g _ h _ => by show (0 : M') = 0 + (SSGRoute.res k K) g • (0 : M'); rw [smul_zero, add_zero]
    have h := pair_add_snd_decomp p k Ω K ζ hζ hζK T hT χ hχadd M βl pair hpair A hA a 0 0
      ha h0lc h0lc h0c h0c
    rw [add_zero] at h
    have h2 : pair (SSGRoute.decomp k A) a 0 + 0
        = pair (SSGRoute.decomp k A) a 0 + pair (SSGRoute.decomp k A) a 0 := by
      rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  have hΛlin : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A) →
      ∃ LA : ↥Z →ₗ[ZMod p] ZMod p,
        ∀ x : ↥Z, LA x = pair (SSGRoute.decomp k A) (α A) (x.1 : F) := by
    intro A hA hαA
    obtain ⟨LA, hLA⟩ := zmodLinearMap_of_addHom (p := p)
      { toFun := fun x : ↥Z => pair (SSGRoute.decomp k A) (α A) (x.1 : F)
        map_zero' := by
          show pair (SSGRoute.decomp k A) (α A) ((0 : ↥Z).1 : F) = 0
          rw [show ((0 : ↥Z).1 : F) = 0 from rfl]
          exact hpair_zero A hA (α A) hαA
        map_add' := by
          intro x y
          have hb : ∀ z : ↥Z, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (z.1 : F) :=
            fun z => hmono_coc _ _ z.2.1
          have hl : ∀ z : ↥Z, SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (z.1 : F) :=
            fun z => hmono_loc _ _ z.2.2
          have h := pair_add_snd_decomp p k Ω K ζ hζ hζK T hT χ hχadd M βl pair hpair A hA
            (α A) (x.1 : F) (y.1 : F) hαA (hl x) (hl y) (hb x) (hb y)
          rw [show (x.1 : F) + (y.1 : F) = ((x + y : ↥Z).1 : F) from rfl] at h
          exact h }
    exact ⟨LA, fun x => by rw [hLA x]; rfl⟩
  -- the linear functional `Λ`
  let LA : ValuationSubring Ω → ↥Z →ₗ[ZMod p] ZMod p := fun A =>
    if h : A ∈ S₁ then Classical.choose (hΛlin A (hS₁fin A h) (hα A h).2) else 0
  let Λ : ↥Z →ₗ[ZMod p] ZMod p := ∑ A ∈ S₁, LA A
  have hLA : ∀ (A : ValuationSubring Ω) (hA : A ∈ S₁) (x : ↥Z),
      LA A x = pair (SSGRoute.decomp k A) (α A) (x.1 : F) := by
    intro A hA x
    rw [show LA A = Classical.choose (hΛlin A (hS₁fin A hA) (hα A hA).2) from dif_pos hA]
    exact Classical.choose_spec (hΛlin A (hS₁fin A hA) (hα A hA).2) x
  have hΛ : ∀ x : ↥Z, Λ x = ∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) (x.1 : F) := by
    intro x
    have h1 : (∑ A ∈ S₁, LA A) x = ∑ A ∈ S₁, LA A x := LinearMap.sum_apply S₁ LA x
    simp only [Λ]
    rw [h1]
    exact Finset.sum_congr rfl fun A hA => hLA A hA x
  -- ## 7. `Λ` vanishes on the kernel of `Ψ`
  have hΛker : ∀ x : ↥Z, Ψ x = 0 → Λ x = 0 := by
    intro x hx
    rw [hΛ x]
    refine horth_offRep p k Ω K T M pair R hRfin hRdisj hRcov S₁ hS₁fin hS₁disj hS₁ram hS₁R
      α horth (x.1 : F) x.2.1 x.2.2 ?_
    intro v hvR hvS σ hσ
    have hvv : (x.1 : F) ∈ Kv v := by
      have h1 : Ψ x ⟨v, hvR, hvS⟩ = 0 := by rw [hx]; rfl
      rw [show Ψ x ⟨v, hvR, hvS⟩ = (Kv v).mkQ (x.1 : F) from rfl, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at h1
      exact h1
    exact (show ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v τ → (x.1 : F) τ = 0 from hvv) σ hσ
  -- ## 8. split `-Λ` into local functionals
  have hkerΛ : ∀ x : ↥Z, Ψ x = 0 → (-Λ) x = 0 := by
    intro x hx
    rw [LinearMap.neg_apply, hΛker x hx, neg_zero]
  obtain ⟨ν, hν⟩ := exists_coordinate_splitting (p := p) (ı := ı)
    (Q := fun v : ı => F ⧸ Kv v.1) (X := ↥Z) Ψ hsupp (-Λ) hkerΛ
  let lam : ∀ v : ı, F →ₗ[ZMod p] ZMod p := fun v => (ν v).comp (Kv v.1).mkQ
  have hlam : ∀ (v : ı) (f : F), lam v f = ν v (Submodule.Quotient.mk f) := fun v f => rfl
  -- ## 9. realise the local functionals by unramified local cocycles
  have hres_one : ∀ (v : ValuationSubring Ω), ¬ SSGRoute.IsRamifiedIn k K v →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v σ → SSGRoute.res k K σ = 1 := by
    intro v hv σ hσ
    have hker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
      IntermediateField.restrictNormalHom_ker K
    have hmem : σ ∈ K.fixingSubgroup := by
      by_contra h
      exact hv ⟨σ, hσ, h⟩
    exact MonoidHom.mem_ker.mp (hker ▸ hmem)
  have hex : ∀ v : ı, ∃ a : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v.1) a ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k v.1) a ∧
      (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v.1 σ → a σ = 0) ∧
      ∀ b : F, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v.1) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k v.1) b →
        pair (SSGRoute.decomp k v.1) a b = lam v b := by
    intro v
    have hvram := (hRne v.1 v.2.1 v.2.2).1
    have hvval := (hRne v.1 v.2.1 v.2.2).2
    refine hreal_unr v.1 (hRfin v.1 v.2.1) hvval hvram (lam v) ?_ ?_ ?_
    · intro b b' _ _
      exact map_add (lam v) b b'
    · intro b hb
      obtain ⟨m, hm⟩ := hb
      rw [hlam]
      have hKv : b ∈ Kv v.1 := by
        show ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v.1 σ → b σ = 0
        intro σ hσ
        rw [hm σ hσ.1, hres_one v.1 hvram σ hσ, one_smul, sub_self]
      rw [show Submodule.Quotient.mk b = 0 from
        (Submodule.Quotient.mk_eq_zero (Kv v.1)).mpr hKv, map_zero]
    · intro b _ _ hb0
      rw [hlam]
      have hKv : b ∈ Kv v.1 := by
        show ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v.1 σ → b σ = 0
        exact fun σ hσ => hb0 σ hσ
      rw [show Submodule.Quotient.mk b = 0 from
        (Submodule.Quotient.mk_eq_zero (Kv v.1)).mpr hKv, map_zero]
  let αnew : ∀ v : ı, (Ω ≃ₐ[k] Ω) → M := fun v => Classical.choose (hex v)
  have hαnew : ∀ v : ı,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v.1) (αnew v) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k v.1) (αnew v) ∧
      (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v.1 σ → αnew v σ = 0) ∧
      ∀ b : F, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v.1) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k v.1) b →
        pair (SSGRoute.decomp k v.1) (αnew v) b = lam v b :=
    fun v => Classical.choose_spec (hex v)
  -- ## 10. the global local data `α'`
  let α' : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M := fun A =>
    if hS : A ∈ S₁ then α A
    else if hR : A ∈ R then αnew ⟨A, hR, hS⟩ else 0
  have hα'S₁ : ∀ A ∈ S₁, α' A = α A := by
    intro A hA
    rw [show α' A = if hS : A ∈ S₁ then α A else if hR : A ∈ R then αnew ⟨A, hR, hS⟩ else 0
      from rfl, dif_pos hA]
  have hα'cl : ∀ v ∈ R, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v) (α' v) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k v) (α' v) := by
    intro v hvR
    by_cases hvS : v ∈ S₁
    · rw [show α' v = α v from hα'S₁ v hvS]
      exact hα v hvS
    · rw [show α' v = if hS : v ∈ S₁ then α v else if hR : v ∈ R then αnew ⟨v, hR, hS⟩ else 0
        from rfl, dif_neg hvS, dif_pos hvR]
      exact ⟨(hαnew ⟨v, hvR, hvS⟩).1, (hαnew ⟨v, hvR, hvS⟩).2.1⟩
  have hα'unr : ∀ v ∈ R, v ∉ S₁ → ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v σ → α' v σ = 0 := by
    intro v hvR hvS σ hσ
    rw [show α' v = if hS : v ∈ S₁ then α v else if hR : v ∈ R then αnew ⟨v, hR, hS⟩ else 0
      from rfl, dif_neg hvS, dif_pos hvR]
    exact (hαnew ⟨v, hvR, hvS⟩).2.2.1 σ hσ
  -- ## 11. the sum over `R` vanishes
  have hsum : ∀ b : (Ω ≃ₐ[k] Ω) → M',
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      ∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ R), pair (SSGRoute.decomp k v) (α' v) b = 0 := by
    intro b hbc hlc
    let bz : ↥Z := ⟨b, hbc, hlc⟩
    obtain ⟨Sb, hSbfin, hSbdisj, hSbvanish⟩ := vanishingInertia_finite k Ω K M' b hbc hlc
    -- every element of `R` outside `S₁` where the summand does not vanish is conjugate to
    -- an element of the finite set `Sb`; there is at most one place of `R` per class
    have hfin_classes : {v : ValuationSubring Ω | v ∈ R ∧ ∃ A ∈ Sb, SSGRoute.IsConjPlace k A v}.Finite := by
      let g : {v : ValuationSubring Ω // v ∈ R ∧ ∃ A ∈ Sb, SSGRoute.IsConjPlace k A v} → ↥Sb :=
        fun v => ⟨Classical.choose v.2.2, (Classical.choose_spec v.2.2).1⟩
      have hinj : Function.Injective g := by
        intro v w hvw
        have hv : SSGRoute.IsConjPlace k (Classical.choose v.2.2) v.1 :=
          (Classical.choose_spec v.2.2).2
        have hw : SSGRoute.IsConjPlace k (Classical.choose w.2.2) w.1 :=
          (Classical.choose_spec w.2.2).2
        have hab : Classical.choose v.2.2 = Classical.choose w.2.2 := congrArg Subtype.val hvw
        have hconj : SSGRoute.IsConjPlace k v.1 w.1 := by
          obtain ⟨s1, hs1⟩ := hv
          obtain ⟨s2, hs2⟩ := hw
          refine ⟨s2 * s1⁻¹, ?_⟩
          calc (s2 * s1⁻¹) • v.1 = s2 • (s1⁻¹ • v.1) := mul_smul _ _ _
            _ = s2 • (s1⁻¹ • (s1 • Classical.choose v.2.2)) := by rw [hs1]
            _ = s2 • Classical.choose v.2.2 := by rw [inv_smul_smul]
            _ = s2 • Classical.choose w.2.2 := by rw [hab]
            _ = w.1 := hs2
        exact Subtype.ext (hRdisj v.1 v.2.1 w.1 w.2.1 hconj)
      haveI : Finite ↥Sb := Sb.finite_toSet.to_subtype
      exact Finite.of_injective g hinj
    have hfinsupp : (↑R ∩ Function.support
        (fun v : ValuationSubring Ω => pair (SSGRoute.decomp k v) (α' v) b)).Finite := by
      refine Set.Finite.subset ((S₁.finite_toSet).union hfin_classes) ?_
      intro v hv
      obtain ⟨hvR, hvne⟩ := hv
      by_cases hvS : v ∈ S₁
      · exact Or.inl hvS
      · refine Or.inr ⟨hvR, ?_⟩
        by_contra hno
        push_neg at hno
        have hKv : b ∈ Kv v := by
          show ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v σ → b σ = 0
          exact fun σ hσ => hSbvanish v (hRfin v hvR) hno σ hσ
        have hz : (Kv v).mkQ b = 0 := (Submodule.Quotient.mk_eq_zero (Kv v)).mpr hKv
        have hzero : pair (SSGRoute.decomp k v) (α' v) b = 0 := by
          rw [show α' v =
            (if hS : v ∈ S₁ then α v else if hR : v ∈ R then αnew ⟨v, hR, hS⟩ else 0) from rfl,
            dif_neg hvS, dif_pos hvR]
          rw [(hαnew ⟨v, hvR, hvS⟩).2.2.2 b (hmono_coc _ _ hbc) (hmono_loc _ _ hlc)]
          rw [show lam ⟨v, hvR, hvS⟩ b = ν ⟨v, hvR, hvS⟩ ((Kv v).mkQ b) from rfl, hz, map_zero]
        exact hvne hzero
    -- split the sum into the parts over `S₁` and over `R \ S₁`
    have hsets : (↑S₁ : Set (ValuationSubring Ω)) ∪ {v | v ∈ R ∧ v ∉ S₁} = R := by
      ext v
      simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact hS₁R v h
        · exact h
      · intro h
        by_cases hv : v ∈ S₁
        · exact Or.inl hv
        · exact Or.inr ⟨h, hv⟩
    have hdisj : Disjoint (↑S₁ : Set (ValuationSubring Ω)) {v | v ∈ R ∧ v ∉ S₁} := by
      rw [Set.disjoint_left]
      intro v hv hv'
      exact hv'.2 hv
    have hfinS₁ : ((↑S₁ : Set (ValuationSubring Ω)) ∩ Function.support
        (fun v => pair (SSGRoute.decomp k v) (α' v) b)).Finite :=
      S₁.finite_toSet.subset Set.inter_subset_left
    have hfinI : ({v | v ∈ R ∧ v ∉ S₁} ∩ Function.support
        (fun v => pair (SSGRoute.decomp k v) (α' v) b)).Finite :=
      hfinsupp.subset fun v hv => ⟨hv.1.1, hv.2⟩
    have hsplit : (∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ R),
          pair (SSGRoute.decomp k v) (α' v) b)
        = (∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ (↑S₁ : Set (ValuationSubring Ω))),
              pair (SSGRoute.decomp k v) (α' v) b)
          + ∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ {v | v ∈ R ∧ v ∉ S₁}),
              pair (SSGRoute.decomp k v) (α' v) b := by
      rw [← finsum_mem_congr hsets (fun v _ => rfl)]
      exact finsum_mem_union' hdisj hfinS₁ hfinI
    -- the part over `S₁` is `Λ`
    have hS₁part : (∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ (↑S₁ : Set (ValuationSubring Ω))),
          pair (SSGRoute.decomp k v) (α' v) b) = Λ bz := by
      rw [finsum_mem_eq_sum (fun v => pair (SSGRoute.decomp k v) (α' v) b) hfinS₁]
      have hsub : hfinS₁.toFinset ⊆ S₁ := fun v hv =>
        (Set.Finite.mem_toFinset hfinS₁).mp hv |>.1
      have hzero : ∀ x ∈ S₁, x ∉ hfinS₁.toFinset →
          pair (SSGRoute.decomp k x) (α' x) b = 0 := by
        intro x hx hxn
        by_contra hne
        exact hxn ((Set.Finite.mem_toFinset hfinS₁).mpr ⟨hx, Function.mem_support.mpr hne⟩)
      rw [Finset.sum_subset hsub hzero]
      rw [hΛ bz]
      exact Finset.sum_congr rfl fun A hA => by rw [hα'S₁ A hA]
    -- the part over `R \ S₁` is the sum of the local functionals
    have hIpart : (∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ {v | v ∈ R ∧ v ∉ S₁}),
          pair (SSGRoute.decomp k v) (α' v) b) = ∑ᶠ (v : ı), ν v (Ψ bz v) := by
      rw [← finsum_set_coe_eq_finsum_mem (f := fun v : ValuationSubring Ω =>
        pair (SSGRoute.decomp k v) (α' v) b) {v | v ∈ R ∧ v ∉ S₁}]
      refine finsum_congr fun j => ?_
      have hα'j : α' j.1 = αnew j := by
        rw [show α' j.1 =
          (if hS : j.1 ∈ S₁ then α j.1 else if hR : j.1 ∈ R then αnew ⟨j.1, hR, hS⟩ else 0)
          from rfl, dif_neg j.2.2, dif_pos j.2.1]
      rw [hα'j, (hαnew j).2.2.2 b (hmono_coc _ _ hbc) (hmono_loc _ _ hlc)]
      rfl
    rw [hsplit, hS₁part, hIpart, hν bz, LinearMap.neg_apply, add_neg_cancel]
  -- ## 12. the prescribed places of `K` are pairwise non-conjugate
  have hRnc : ∀ (v w : ValuationSubring Ω) (hv : v ∈ R) (hw : w ∈ R),
      (∃ σ : ↥K ≃ₐ[k] ↥K,
        σ • NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)) =
          NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K w (hRfin w hw))) → v = w := by
    intro v w hv hw hconj
    exact hRdisj v hv w hw (isConjPlace_of_finQ_conj k Ω K v w (hRfin v hv) (hRfin w hw) hconj)
  -- ## 13. the glued class `X`
  haveI : Finite T := by
    haveI : Module.Free (ZMod p) T := inferInstance
    haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
    have hfr : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
      rw [hT.1, Module.finrank_self]
    exact Finite.of_injective (LinearEquiv.ofFinrankEq T (ZMod p) hfr : T ≃ₗ[ZMod p] ZMod p)
      (LinearEquiv.injective _)
  haveI : Finite M' := Work.SSGRoute.PT.finite_dualMod_tensor p M T
  let qof : R → NK.GlobalCFT.Place ↥K := fun v =>
    NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v.1 (hRfin v.1 v.2))
  have hqof_nc : ∀ a ∈ Set.range qof, ∀ b ∈ Set.range qof,
      (∃ σ : ↥K ≃ₐ[k] ↥K, σ • a = b) → a = b := by
    rintro a ⟨v, rfl⟩ b ⟨w, rfl⟩ ⟨σ, hσ⟩
    exact congrArg qof (Subtype.ext (hRnc v.1 w.1 v.2 w.2 ⟨σ, hσ⟩))
  obtain ⟨RK, hRKsub, hRKtrans⟩ := exists_transversal_containing_set
    (G := ↥K ≃ₐ[k] ↥K) (α := NK.GlobalCFT.Place ↥K) (Set.range qof) hqof_nc
  -- the family of local `Ext` groups
  let Tpl : NK.GlobalCFT.Place ↥K → Type := fun q =>
    CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) q).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) M'))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) q) 1
  have ha_ex : ∀ w : ↥RK, ∃ y : Tpl w.1,
      ((∃ v : R, qof v = w.1) →
        ∀ (v : R) (hv : qof v = w.1),
          y = Eq.mp (congrArg Tpl hv) (βl v.1 (hRfin v.1 v.2) (α' v.1))) ∧
      ((¬ ∃ v : R, qof v = w.1) → y = 0) := by
    intro w
    by_cases h : ∃ v : R, qof v = w.1
    · obtain ⟨v, hv⟩ := h
      refine ⟨Eq.mp (congrArg Tpl hv) (βl v.1 (hRfin v.1 v.2) (α' v.1)), ?_, ?_⟩
      · intro _ v' hv'
        have hvv : v' = v := Subtype.ext (hRnc v'.1 v.1 v'.2 v.2 ⟨1, by
          rw [one_smul]
          exact hv'.trans hv.symm⟩)
        subst hvv
        rw [show hv' = hv from Subsingleton.elim _ _]
      · intro hc
        exact absurd ⟨v, hv⟩ hc
    · exact ⟨0, fun hc => absurd hc h, fun _ => rfl⟩
  let a : ∀ w : ↥RK, Tpl w.1 := fun w => Classical.choose (ha_ex w)
  have ha_spec : ∀ (w : ↥RK) (v : R) (hv : qof v = w.1),
      a w = Eq.mp (congrArg Tpl hv) (βl v.1 (hRfin v.1 v.2) (α' v.1)) :=
    fun w v hv => (Classical.choose_spec (ha_ex w)).1 ⟨v, hv⟩ v hv
  have ha_zero : ∀ (w : ↥RK), (¬ ∃ v : R, qof v = w.1) → a w = 0 :=
    fun w hw => (Classical.choose_spec (ha_ex w)).2 hw
  -- the value of `a` at the prescribed places
  have ha_q : ∀ (v : R), a ⟨qof v, hRKsub ⟨v, rfl⟩⟩ = βl v.1 (hRfin v.1 v.2) (α' v.1) := by
    intro v
    have hv : qof v = (⟨qof v, hRKsub ⟨v, rfl⟩⟩ : ↥RK).1 := rfl
    have hspec := ha_spec ⟨qof v, hRKsub ⟨v, rfl⟩⟩ v hv
    rw [hspec]
    exact eq_mp_congrArg_self (T := Tpl) hv (βl v.1 (hRfin v.1 v.2) (α' v.1))
  -- the family is unramified at all but finitely many places
  have hbad : {w : ↥RK | ¬ SSGRoute.PTExt.IsUnramifiedExt w.1 (a w)}.Finite := by
    have hzero_unr : ∀ w : ↥RK, (¬ ∃ v : R, qof v = w.1) →
        SSGRoute.PTExt.IsUnramifiedExt w.1 (a w) := by
      intro w hw
      rw [ha_zero w hw]
      exact ⟨0, by rw [CategoryTheory.Abelian.Ext.zero_comp]⟩
    haveI : Finite ↥S₁ := S₁.finite_toSet.to_subtype
    refine Set.Finite.subset (Set.finite_range (fun v : ↥S₁ =>
      (⟨qof ⟨v.1, hS₁R v.1 v.2⟩,
        hRKsub ⟨⟨v.1, hS₁R v.1 v.2⟩, rfl⟩⟩ : ↥RK))) ?_
    intro w hw
    by_cases h : ∃ v : R, qof v = w.1
    · obtain ⟨v, hv⟩ := h
      have hwv : w = ⟨qof v, hRKsub ⟨v, rfl⟩⟩ := Subtype.ext hv.symm
      by_cases hvS : v.1 ∈ S₁
      · rw [hwv]
        refine ⟨⟨v.1, hvS⟩, ?_⟩
        exact Subtype.ext (congrArg qof (Subtype.ext rfl))
      · exfalso
        have hw' : ¬ SSGRoute.PTExt.IsUnramifiedExt w.1 (a w) := hw
        rw [hwv, ha_q v] at hw'
        exact hw' (hβl_unr v.1 (hRfin v.1 v.2) (hRne v.1 v.2 hvS).2 (hRne v.1 v.2 hvS).1
          (α' v.1) (hα'cl v.1 v.2).1 (hα'cl v.1 v.2).2 (hα'unr v.1 v.2 hvS))
    · exfalso
      exact hw (hzero_unr w h)
  haveI : Finite ↥(SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) M') := inferInstanceAs (Finite M')
  obtain ⟨X, hX⟩ := (Work.SSGRoute.ext_idele_shapiro (k := k) (K := ↥K)
    (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) M') 1 RK hRKtrans).2.2 a hbad
  refine ⟨R, hRfin, hS₁R, hRdisj, hRcov, α', hα'S₁, hα'cl, hα'unr, hsum, X, ?_, ?_⟩
  · -- the components at the places of `R`
    intro v hv
    have h1 : SSGRoute.PTExt.extLoc (k := k)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv))) X =
        a ⟨qof ⟨v, hv⟩, hRKsub ⟨⟨v, hv⟩, rfl⟩⟩ := hX ⟨qof ⟨v, hv⟩, hRKsub ⟨⟨v, hv⟩, rfl⟩⟩
    rw [h1, ha_q ⟨v, hv⟩]
  · -- the components at the infinite places
    intro w hw
    obtain ⟨w', hspec, -⟩ := hRKtrans w
    obtain ⟨σ, hσ⟩ := hspec
    have hw'not : ¬ ∃ v : R, qof v = w'.1 := by
      rintro ⟨v, hv⟩
      have hfin : w'.1.IsFinite := by
        rw [← hv]; exact NK.GlobalCFT.Place.isFinite_ofFinite _
      rw [← hσ] at hfin
      obtain ⟨q', hq'⟩ := NK.GlobalCFT.Place.isFinite_iff.mp
        ((Work.SSGRoute.PT.isFinite_smul_iff K σ w).mp hfin)
      exact hw q' hq'
    have hzero : SSGRoute.PTExt.extLoc (k := k) w'.1 X = 0 := by
      rw [hX w', ha_zero w' hw'not]
    have hw_eq : w = σ⁻¹ • w'.1 := by
      rw [← hσ, inv_smul_smul]
    rw [hw_eq]
    exact Work.SSGRoute.e9c_extLoc_conj_zero X σ⁻¹ w'.1 hzero


end Work.SSGRoute.PT
