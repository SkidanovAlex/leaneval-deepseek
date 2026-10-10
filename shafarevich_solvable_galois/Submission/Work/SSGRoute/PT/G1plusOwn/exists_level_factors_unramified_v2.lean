import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PT.finHalfData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finite normal level killing a locally constant cocycle, unramified off a finite place set

Given a finite Galois extension `K/k` (inside an algebraic closure `Ω` of the number field `k`),
a finite place set `S'`, and a locally constant `1`-cocycle `b : G_k → M` (coefficients the Galois
module `M` over `Gal(K/k)`) which vanishes on every inertia group at a finite place of `Ω` *outside*
`S'`, and such that `K/k` is unramified at those places, we produce a finite normal level `L ⊇ K`
with

* `b` inflated from `Gal(L/k)` (i.e. `b` is constant on the fibres of `σ ↦ σ|_L`), and
* every inertia element at a finite place outside `S'` fixes `L` pointwise.

## The construction

Let `G = Gal(Ω/k)`.  Inside `G` consider

* `P₀ = {u ∈ G | ∀ g, b (g * u) = b g}`, the *period subgroup* of `b`.  It is an open subgroup
  (`IsLocConstOn ⊤ b` gives an open subgroup consisting of periods), it contains every inertia
  group `I_B` with `b|I_B = 0`, and `b` factors through any level whose fixing subgroup lies in
  `P₀`;
* `T = ⋃ {I_B | B finite place of `Ω` not conjugate to `S'`}`, the union of the inertia groups
  outside `S'`.  It is conjugation stable, and by hypothesis it lies in `P₀ ⊓ Gal(Ω/K)`;
* `N₀ ≤ P₀ ⊓ Gal(Ω/K)`, an open *normal* subgroup (obtained from the Krull theory: an open
  subgroup contains the fixing subgroup of a finite normal level above `K`).

Then `Q := closure (T ∪ N₀)` is normal (its generating set is conjugation stable), open (it
contains `N₀`), and contained in `P₀ ⊓ Gal(Ω/K)`.  The normal subgroup `P := closure(Q)` is still
contained in `P₀ ⊓ Gal(Ω/K)`, so the fixed field `L := Ω^P` is finite, normal over `k`, contains
`K`, has `L.fixingSubgroup = P`, and by construction contains `⋃ I_B` in its fixing subgroup while
sitting inside `P₀` — whence both conclusions.
-/

open scoped Pointwise

namespace Work.SSGRoute.PT.G1plusOwn

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- **Right periods of a function constant on a neighbourhood of the identity.**

Let `f : G → A` be a function on a topological group such that there is an *open* subgroup `U`
with `f (g * u) = f g` for all `g` and all `u ∈ U` (the `⊤`-case of `SSGRoute.IsLocConstOn`).
Then the set of right periods `{u | ∀ g, f (g * u) = f g}` is an open subgroup of `G`, and it is
the largest such subgroup. -/
theorem exists_open_periodSubgroup_aux {G A : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup A] {f : G → A}
    (hl : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g u : G, u ∈ U → f (g * u) = f g) :
    ∃ Hb : Subgroup G, IsOpen (Hb : Set G) ∧ (∀ u ∈ Hb, ∀ g : G, f (g * u) = f g) ∧
      (∀ u : G, (∀ g : G, f (g * u) = f g) → u ∈ Hb) := by
  obtain ⟨U, hUopen, hU⟩ := hl
  let Hb : Subgroup G :=
    { carrier := {u | ∀ g : G, f (g * u) = f g}
      mul_mem' := by
        intro a b ha hb g
        rw [← mul_assoc, hb (g * a), ha g]
      one_mem' := by intro g; rw [mul_one]
      inv_mem' := by
        intro a ha g
        have h := ha (g * a⁻¹)
        simpa using h.symm }
  refine ⟨Hb, ?_, ?_, ?_⟩
  · exact Subgroup.isOpen_mono (fun u hu g => hU g u hu) hUopen
  · intro u hu g
    exact hu g
  · intro u hu
    exact hu

/-- **Conjugation of inertia outside `S'`.**  If `σ` is an inertia element at a finite place `B`
which is not conjugate to any place of `S'`, then `g * σ * g⁻¹` is an inertia element at another
such place (`g • B`). -/
theorem goodInertiaSet_conj_mem_aux {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (S' : Finset (ValuationSubring Ω)) (g σ : Ω ≃ₐ[k] Ω)
    (h : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) ∧ SSGRoute.IsInertia k B σ) :
    ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) ∧ SSGRoute.IsInertia k B (g * σ * g⁻¹) := by
  obtain ⟨B, hBfin, hBnot, hBin⟩ := h
  refine ⟨g • B, (Work.SSGRoute.isFinPlace_smul_iff B g).mpr hBfin, ?_,
    (Work.SSGRoute.isInertia_conj B g σ).mpr hBin⟩
  intro A hA hconj
  obtain ⟨τ, hτ⟩ := hconj
  exact hBnot A hA ⟨g⁻¹ * τ, by rw [mul_smul, hτ, inv_smul_smul]⟩

/-- **The fixed field of an open normal subgroup.**  For an open normal subgroup `P` of the
absolute Galois group of a number field `k` inside an algebraic closure `Ω`, the fixed field `Ω^P`
is finite over `k`, normal over `k`, and its fixing subgroup is exactly `P`. -/
theorem fixedField_of_openNormal_aux (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (P : Subgroup (Ω ≃ₐ[k] Ω))
    (hPopen : IsOpen (P : Set (Ω ≃ₐ[k] Ω))) (hPnorm : P.Normal) :
    FiniteDimensional k (IntermediateField.fixedField P) ∧
      Normal k (IntermediateField.fixedField P) ∧
      (IntermediateField.fixedField P).fixingSubgroup = P := by
  haveI : IsGalois k Ω := inferInstance
  have hPclosed : IsClosed (P : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isClosed_of_isOpen P hPopen
  have hfix : (IntermediateField.fixedField P).fixingSubgroup = P :=
    InfiniteGalois.fixingSubgroup_fixedField (⟨P, hPclosed⟩ : ClosedSubgroup Gal(Ω/k))
  have hfin : FiniteDimensional k (IntermediateField.fixedField P) := by
    rw [← InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField P), hfix]
    exact hPopen
  have hnorm : Normal k (IntermediateField.fixedField P) := by
    haveI : P.Normal := hPnorm
    haveI : IsGalois k (IntermediateField.fixedField P) :=
      IsGalois.of_fixedField_normal_subgroup P
    exact IsGalois.to_normal
  exact ⟨hfin, hnorm, hfix⟩

theorem exists_level_factors_unramified_v2
    (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (b : (Ω ≃ₐ[k] Ω) → M)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (hl : SSGRoute.IsLocConstOn ⊤ b)
    (S' : Finset (ValuationSubring Ω)) (hS'fin : ∀ A ∈ S', SSGRoute.IsFinPlace k A)
    (hgood : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
      ¬ SSGRoute.IsRamifiedIn k K B ∧
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → b σ = 0)) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : Normal k L),
      K ≤ L ∧
      (∃ b₀ : (↥L ≃ₐ[k] ↥L) → M, ∀ σ : Ω ≃ₐ[k] Ω, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → σ ∈ L.fixingSubgroup) := by
  haveI : IsGalois k Ω := inferInstance
  -- ## Step 1: `b` vanishes at the identity.
  have hb1 : b 1 = 0 := by
    have h := hb (1 : Ω ≃ₐ[k] Ω) trivial (1 : Ω ≃ₐ[k] Ω) trivial
    rw [mul_one, map_one, one_smul] at h
    have h2 : b 1 + 0 = b 1 + b 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  -- ## Step 2: the open period subgroup `P₀` of `b`.
  obtain ⟨U, hUopen, hUconst⟩ := hl
  obtain ⟨P₀, hP₀open, hP₀spec, hP₀max⟩ :=
    exists_open_periodSubgroup_aux (G := Ω ≃ₐ[k] Ω) (A := M) (f := b)
      ⟨U, hUopen, fun g u hu => hUconst g trivial u hu trivial⟩
  -- ## Step 3: the union `T` of the inertia groups at finite places away from `S'`.
  let T : Set (Ω ≃ₐ[k] Ω) := {σ | ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) ∧ SSGRoute.IsInertia k B σ}
  have hT_le : T ⊆ (P₀ ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) := by
    rintro σ ⟨B, hB, hBnot, hI⟩
    refine ⟨hP₀max σ ?_, ?_⟩
    · intro g
      rw [hb g trivial σ trivial, (hgood B hB hBnot).2 σ hI, smul_zero, add_zero]
    · by_contra hσ
      exact (hgood B hB hBnot).1 ⟨σ, hI, hσ⟩
  have hT_conj : ∀ g : Ω ≃ₐ[k] Ω, ∀ σ ∈ T, g * σ * g⁻¹ ∈ T :=
    fun g σ hσ => goodInertiaSet_conj_mem_aux S' g σ hσ
  -- ## Step 4: an open normal subgroup `N₀` of `P₀ ⊓ K.fixingSubgroup`.
  obtain ⟨L₀, hL₀fin, hL₀norm, hK_le_L₀, hN₀_le_P₀⟩ :=
    Work.SSGRoute.PT.exists_finiteNormal_fixingSubgroup_le_of_isOpen k Ω K P₀ hP₀open
  haveI : FiniteDimensional k L₀ := hL₀fin
  haveI : Normal k L₀ := hL₀norm
  have hN₀_le : L₀.fixingSubgroup ≤ P₀ ⊓ K.fixingSubgroup :=
    le_inf hN₀_le_P₀ (IntermediateField.fixingSubgroup_le hK_le_L₀)
  have hN₀_open : IsOpen ((L₀.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) := IntermediateField.fixingSubgroup_isOpen L₀
  have hN₀_normal : L₀.fixingSubgroup.Normal := by
    rw [← IntermediateField.restrictNormalHom_ker (E := L₀)]
    exact MonoidHom.normal_ker _
  -- ## Step 5: the open normal subgroup `P` generated by `T` and `N₀`.
  let Q : Subgroup (Ω ≃ₐ[k] Ω) := Subgroup.closure (T ∪ (L₀.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)))
  have hQ_normal : Q.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
        rcases hx with hxT | hxN
        · exact Subgroup.subset_closure (Or.inl (hT_conj g x hxT))
        · exact Subgroup.subset_closure (Or.inr (hN₀_normal.conj_mem x hxN g))
    | one => simp
    | mul x y hx hy ihx ihy =>
        have hxy : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        rw [hxy]
        exact mul_mem ihx ihy
    | inv x hx ih =>
        have hxy : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        rw [hxy]
        exact inv_mem ih
  let P : Subgroup (Ω ≃ₐ[k] Ω) := Q.topologicalClosure
  have hP_closed : IsClosed (P : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isClosed_topologicalClosure Q
  have hP_normal : P.Normal := by
    haveI : Q.Normal := hQ_normal
    exact Subgroup.is_normal_topologicalClosure Q
  have hN₀_le_Q : L₀.fixingSubgroup ≤ Q := fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hP_open : IsOpen (P : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.isOpen_mono (le_trans hN₀_le_Q (Subgroup.le_topologicalClosure Q)) hN₀_open
  have hQ_le : Q ≤ P₀ ⊓ K.fixingSubgroup := by
    show Subgroup.closure (T ∪ (L₀.fixingSubgroup : Set (Ω ≃ₐ[k] Ω))) ≤
      P₀ ⊓ K.fixingSubgroup
    rw [Subgroup.closure_le]
    rintro x (hxT | hxN)
    · exact hT_le hxT
    · exact hN₀_le hxN
  have hP_le : P ≤ P₀ ⊓ K.fixingSubgroup := by
    refine le_inf ?_ ?_
    · exact Subgroup.topologicalClosure_minimal Q (le_trans hQ_le inf_le_left)
        (Subgroup.isClosed_of_isOpen P₀ hP₀open)
    · exact Subgroup.topologicalClosure_minimal Q (le_trans hQ_le inf_le_right)
        (InfiniteGalois.fixingSubgroup_isClosed K)
  -- ## Step 6: the level `L = Ω^P`.
  obtain ⟨hLfin, hLnorm, hfix_L⟩ := fixedField_of_openNormal_aux k Ω P hP_open hP_normal
  haveI : FiniteDimensional k (IntermediateField.fixedField P) := hLfin
  haveI : Normal k (IntermediateField.fixedField P) := hLnorm
  have hKL : K ≤ IntermediateField.fixedField P :=
    (IntermediateField.le_iff_le P K).mpr (le_trans hP_le inf_le_right)
  have hfix_le : (IntermediateField.fixedField P).fixingSubgroup ≤ P₀ :=
    le_trans (le_of_eq hfix_L) (le_trans hP_le inf_le_left)
  -- ## Step 7: `b` is inflated from the level.
  obtain ⟨b₀, hb₀⟩ :=
    Work.SSGRoute.PT.factors_of_fixingSubgroup_le (k := k) (Ω := Ω) (M := M) ⊤ b
      (IntermediateField.fixedField P) P₀ hfix_le
      (fun g _ u hu _ => hP₀spec u hu g)
  have hb₀' : ∀ σ : Ω ≃ₐ[k] Ω,
      b σ = b₀ (AlgEquiv.restrictNormalHom (IntermediateField.fixedField P) σ) :=
    fun σ => hb₀ σ trivial
  -- ## Step 8: the inertia groups away from `S'` fix the level.
  have hcond2 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ →
        σ ∈ (IntermediateField.fixedField P).fixingSubgroup := by
    intro B hB hBnot σ hI
    have hσT : σ ∈ T := ⟨B, hB, hBnot, hI⟩
    have hσQ : σ ∈ Q := Subgroup.subset_closure (Or.inl hσT)
    have hσP : σ ∈ P := Subgroup.le_topologicalClosure Q hσQ
    rw [hfix_L]
    exact hσP
  exact ⟨IntermediateField.fixedField P, hLfin, hLnorm, hKL, ⟨b₀, hb₀'⟩, hcond2⟩

end Work.SSGRoute.PT.G1plusOwn
