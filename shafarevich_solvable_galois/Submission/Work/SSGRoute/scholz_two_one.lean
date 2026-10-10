import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.N5.theorem13_clean
import Submission.Work.SSGRoute.grunwald_escape_support_E
import Submission.Work.SSGRoute.isLocConstOn_patchFun
import Submission.Work.SSGRoute.scholz_one_one
import Submission.Work.SSGRoute.shafarevich_existence
import Submission.Work.SSGRoute.step4Helpers
import Submission.Work.SSGRoute.step4_tool_S_exists
import Submission.Work.SSGRoute.step4_y_localdata
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

LEAD 09-30: new Step-4 route (design: _NOTE_STEP4_DESIGN.md at the workspace root; read the section for your node). step4_yLarge_exists was FALSE (it asks for an everywhere-unramified y); Step4YPrescribed with the escape at D.Λ is right. Frattini argument for i ≥ 2 (N1), Grünwald with escape (N2, pairing-free; do NOT use kummerChar_eq_zero_iff_local_powClass, which is unfinished), the E-valued version (N3), local data (N4), and the (1,1) → (2,1) step via shafarevich_existence (N5). No Hochschild–Serre transgression and no Poitou–Tate input. Import sibling nodes you depend on (still in flight until they land).
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking

set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime]

/-! ## The split section at stage `(2,1)` and the `(1,1)`-solution -/

section Setup

variable (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n : ℕ)

/-- The split section `σ ↦ (1, res σ)` at stage `(2,1)`. -/
noncomputable def splitSection :
    SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc 1 1).1 (tauSucc 1 1).2 :=
  (SemidirectProduct.inr).comp (restrict K)

/-- The `(1,1)`-solution `σ ↦ (1, res σ)`. -/
noncomputable def oneOne :
    SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n 1 1 :=
  (SemidirectProduct.inr).comp (restrict K)

@[simp] lemma splitSection_apply (σ : SSGRoute.GalQ) :
    splitSection (p := p) K n σ = SemidirectProduct.inr (restrict K σ) := rfl

@[simp] lemma oneOne_apply (σ : SSGRoute.GalQ) :
    oneOne (p := p) K n σ = SemidirectProduct.inr (restrict K σ) := rfl

lemma splitSection_quot (σ : SSGRoute.GalQ) :
    flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc 1 1).1 (tauSucc 1 1).2
      (splitSection (p := p) K n σ) = restrict K σ :=
  SemidirectProduct.rightHom_inr _

lemma oneOne_quot (σ : SSGRoute.GalQ) :
    flowQuot p (K ≃ₐ[ℚ] K) n 1 1 (oneOne (p := p) K n σ) = restrict K σ :=
  SemidirectProduct.rightHom_inr _

/-- An element of `G_ℚ` lies in `K.fixingSubgroup` iff its restriction to `K` is trivial. -/
lemma restrict_eq_one_iff_mem_fixingSubgroup (σ : SSGRoute.GalQ) :
    restrict K σ = 1 ↔ σ ∈ K.fixingSubgroup := by
  exact ⟨mem_fixingSubgroup_of_restrict_eq_one K, restrict_eq_one_of_mem_fixingSubgroup K⟩

lemma oneOne_eq_one_iff (σ : SSGRoute.GalQ) :
    oneOne (p := p) K n σ = 1 ↔ σ ∈ K.fixingSubgroup := by
  rw [oneOne_apply, ← map_one (SemidirectProduct.inr), SemidirectProduct.inr_inj]
  exact restrict_eq_one_iff_mem_fixingSubgroup K σ

lemma splitSection_eq_one_iff (σ : SSGRoute.GalQ) :
    splitSection (p := p) K n σ = 1 ↔ σ ∈ K.fixingSubgroup := by
  rw [splitSection_apply, ← map_one (SemidirectProduct.inr), SemidirectProduct.inr_inj]
  exact restrict_eq_one_iff_mem_fixingSubgroup K σ

lemma oneOne_ker : (oneOne (p := p) K n).ker = K.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker]
  exact oneOne_eq_one_iff K n σ

lemma splitSection_ker : (splitSection (p := p) K n).ker = K.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker]
  exact splitSection_eq_one_iff K n σ

end Setup

/-! ## Surjectivity of the graded-piece inclusion at `(1,1)` -/

/-- At `(1,1)` the graded-piece inclusion `E(n,1,1) → F(n)/F(n)^{(2,1)}` is surjective, because
`F(n)^{(1,1)} = F(n)`: every class of `F(n)/F(n)^{(2,1)}` has a representative in
`F(n)^{(1,1)} = ⊤`. -/
theorem gradeIncl_one_one_surjective (p : ℕ) (G : Type*) [Group G] (n : ℕ) :
    Function.Surjective (gradeIncl p G n 1 1) := by
  intro a
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (flowRel p G n 2 1) a
  have htop : refinedTerm p (Work.Shrinking.freeOperatorGroup G n) 1 1 = ⊤ := by
    rw [refinedTerm_one, pSeries_one]
  have hmem : (x : Work.Shrinking.freeOperatorGroup G n) ∈
      refinedTerm p (Work.Shrinking.freeOperatorGroup G n) 1 1 := by
    rw [htop]; exact Subgroup.mem_top _
  have hkey : gradeIncl p G n 1 1
      (QuotientGroup.mk' _ (⟨(x : Work.Shrinking.freeOperatorGroup G n), hmem⟩ :
        ↥(refinedTerm p (Work.Shrinking.freeOperatorGroup G n) 1 1))) =
      QuotientGroup.mk' (flowRel p G n 2 1) x := by
    rw [gradeIncl_apply_mk']
    have hcoe : (Subgroup.inclusion le_top
        (⟨(x : Work.Shrinking.freeOperatorGroup G n), hmem⟩ :
          ↥(refinedTerm p (Work.Shrinking.freeOperatorGroup G n) 1 1)) :
        ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) = x := Subtype.ext rfl
    rw [hcoe]
    rfl
  exact ⟨_, by rw [hkey]; exact hx⟩

/-! ## The twist of the split section is a Scholz solution

This is the pure-algebra half of the proof: given a class `x` with the local clauses of Theorem 13,
the twist of the split section by `x` is a proper solution at `(2,1)` satisfying (i) and (ii). -/

section Twist

variable (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n : ℕ)

/-- The twist of the split section by an `E(n,1,1)`-valued `1`-cocycle. -/
noncomputable def twistSplit (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ) :
    SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc 1 1).1 (tauSucc 1 1).2 :=
  flowTwistEHom p K n 1 1 x (splitSection (p := p) K n) (splitSection_quot K n) hxmul

lemma twistSplit_apply (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    (σ : SSGRoute.GalQ) :
    twistSplit (p := p) K n x hxmul σ =
      gradeInl p (K ≃ₐ[ℚ] K) n 1 1 (Additive.toMul (x σ)) *
        splitSection (p := p) K n σ := rfl

end Twist

section Main

variable (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n : ℕ)

/-- **The algebraic core of the `(1,1) → (2,1)` step.**

Let `x : G_ℚ → E(n,1,1)` be a `1`-cocycle for the `G(K/ℚ)`-action, locally constant, surjective on
`G_K`, a coboundary on the decomposition groups of the places over `Ram(K/ℚ) ∪ {p, ∞}`, a
coboundary on the subgroups generated by the involutions, cyclic in the sense of clause (7) of
Theorem 13 at every place where its inertia image on `G_K` is non-trivial, and trivial on the
decomposition groups of the places where it is *not* cyclic.  Then the twist `x ⋊ res` of the split
section is a Scholz solution at stage `(2,1)`.

Conditions (i) and (ii) of the Scholz conditions are `ScholzConditions p K`, and the properness is
the surjectivity of the twist, which follows from the surjectivity of `x` on `G_K` because the
graded-piece inclusion is surjective at `(1,1)` (`gradeIncl_one_one_surjective`). -/
theorem isScholzSolution_twistSplit
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    (hxloc : SSGRoute.IsLocConstOn ⊤ x)
    (hxsurj : ∀ v : E p (K ≃ₐ[ℚ] K) n 1 1, ∃ σ ∈ K.fixingSubgroup, x σ = v)
    (hx0T1 : ∀ A : ValuationSubring SSGRoute.QBar, IsT1Place p K A →
      SSGRoute.IsCoboundaryOn (restrict K) (decomp ℚ A) x)
    (hx0inv : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (restrict K) (Subgroup.zpowers c) x)
    (hnew : ∀ A : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ A →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0) →
      ∀ σ ∈ decomp ℚ A, oneOne (p := p) K n σ = 1)
    (hcyc7 : ∀ A : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ A →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0) →
      ∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
        (∀ δ ∈ decomp ℚ A, ∀ u ∈ decomp ℚ A ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
        (∃ g ∈ decomp ℚ A, ∀ δ ∈ decomp ℚ A, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
        SSGRoute.IsCoboundaryOn (restrict K) (decomp ℚ A ⊓ V) x) :
    SSGRoute.IsScholzSolution p K n (tauSucc 1 1).1 (tauSucc 1 1).2
      (twistSplit (p := p) K n x hxmul) := by
  classical
  -- the split section is a lift of the `(1,1)`-solution
  have hLift : ∀ σ, SSGRoute.LiftsFlowAt (splitSection (p := p) K n σ) (oneOne (p := p) K n σ) := by
    intro σ
    refine ⟨by simp, 1, ?_, ?_⟩ <;> simp
  -- the `(1,1)`-solution is surjective
  haveI hsub : Subsingleton (flowQuotient p (K ≃ₐ[ℚ] K) n 1 1) := by
    have h : flowTerm p (K ≃ₐ[ℚ] K) n 1 1 = ⊤ := by
      rw [flowTerm, refinedTerm_one, pSeries_one]
    rw [flowQuotient]
    apply QuotientGroup.subsingleton_iff.mpr
    ext x
    simp [h]
  have hφsurj : Function.Surjective (oneOne (p := p) K n) := by
    intro y
    obtain ⟨σ, hσ⟩ : ∃ σ : SSGRoute.GalQ, restrict K σ = y.right :=
      Work.AbsoluteGalois.restrictHom_surjective K y.right
    refine ⟨σ, ?_⟩
    have hy : y = SemidirectProduct.inr y.right := by
      have h := SemidirectProduct.inl_left_mul_inr_right y
      rw [show y.left = (1 : flowQuotient p (K ≃ₐ[ℚ] K) n 1 1) from Subsingleton.elim _ _] at h
      simpa using h.symm
    rw [oneOne_apply, hσ, ← hy]
  -- the level projection of the twist is `φ`
  have hproj : ∀ σ, flowGroupProj p (K ≃ₐ[ℚ] K) n 1 1
      (twistSplit (p := p) K n x hxmul σ) = oneOne (p := p) K n σ := fun σ =>
    congrFun (congrArg DFunLike.coe
      (flowGroupProj_comp_flowTwistEHom p K n 1 1 x (splitSection (p := p) K n)
        (oneOne (p := p) K n) (splitSection_quot K n) hxmul hLift)) σ
  -- surjectivity of the twist, from the surjectivity of `x` on `G_K`
  have hsurj : Function.Surjective (twistSplit (p := p) K n x hxmul) := by
    intro y
    obtain ⟨a, g, rfl⟩ : ∃ a g, y = SemidirectProduct.mk a g := ⟨y.left, y.right, rfl⟩
    obtain ⟨e', he'⟩ := gradeIncl_one_one_surjective p (K ≃ₐ[ℚ] K) n a
    set e : E p (K ≃ₐ[ℚ] K) n 1 1 := Additive.ofMul e' with he
    have heval : gradeIncl p (K ≃ₐ[ℚ] K) n 1 1 (Additive.toMul e) = a := by
      rw [he]; exact he'
    obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : SSGRoute.GalQ, restrict K σ₁ = g :=
      Work.AbsoluteGalois.restrictHom_surjective K g
    obtain ⟨u, huK, hxu⟩ := hxsurj (g⁻¹ • (e - x σ₁))
    refine ⟨σ₁ * u, ?_⟩
    have hures : restrict K u = 1 := (restrict_eq_one_iff_mem_fixingSubgroup K u).mpr huK
    have hxval : x (σ₁ * u) = e := by
      rw [hxmul σ₁ u, hσ₁, hxu, ← mul_smul, mul_inv_cancel, one_smul]
      abel
    have hres : restrict K (σ₁ * u) = g := by rw [map_mul, hσ₁, hures, mul_one]
    rw [twistSplit_apply, hxval]
    have hψ : splitSection (p := p) K n (σ₁ * u) = SemidirectProduct.inr g := by
      rw [splitSection_apply, hres]
    rw [hψ]
    change SemidirectProduct.inl (gradeIncl p (K ≃ₐ[ℚ] K) n 1 1 (Additive.toMul e)) *
      SemidirectProduct.inr g = SemidirectProduct.mk a g
    rw [heval]
    exact SemidirectProduct.inl_left_mul_inr_right (SemidirectProduct.mk a g)
  refine ⟨?_, ?_⟩
  · -- `IsFlowSolution`
    refine isFlowSolution_flowTwistEHom p K n 1 1 x (splitSection (p := p) K n)
      (splitSection_quot K n) hxmul ?_ hxloc ?_
    · rw [splitSection_ker]
      exact IntermediateField.fixingSubgroup_isOpen K
    · exact hsurj
  · -- `ScholzConditions`
    refine scholzConditions_of_stageData p K n 1 1 (oneOne (p := p) K n)
      (twistSplit (p := p) K n x hxmul) ?_ ?_ ?_ ?_
    · -- (i) at the places over `Ram(K/ℚ) ∪ {p}`
      intro A hA σ hσ hfix
      have hxσ : x σ = 0 := eq_zero_of_isCoboundaryOn p K n 1 1 (hx0T1 A hA) σ hσ hfix
      have hψσ : splitSection (p := p) K n σ = 1 := (splitSection_eq_one_iff K n σ).mpr hfix
      rw [twistSplit_apply, hxσ, hψσ]
      simp
    · -- (i) at the archimedean places (involutions)
      intro c hc1 hcK
      have hxc : x c = 0 :=
        eq_zero_of_isCoboundaryOn p K n 1 1 (hx0inv c hc1) c (Subgroup.mem_zpowers c) hcK
      have hψc : splitSection (p := p) K n c = 1 := (splitSection_eq_one_iff K n c).mpr hcK
      rw [twistSplit_apply, hxc, hψc]
      simp
    · -- the stage-3 clauses at the places where the twist ramifies
      intro A hA hhyp
      obtain ⟨σ₀, hσ₀I, hσ₀K, hσ₀ne⟩ := hhyp
      have hxσ₀ : x σ₀ ≠ 0 := by
        intro hx0
        apply hσ₀ne
        rw [twistSplit_apply, hx0]
        have hψσ₀ : splitSection (p := p) K n σ₀ = 1 :=
          (splitSection_eq_one_iff K n σ₀).mpr hσ₀K
        rw [hψσ₀]; simp
      have htriv : ∀ σ ∈ decomp ℚ A, oneOne (p := p) K n σ = 1 :=
        hnew A hA ⟨σ₀, hσ₀I, hσ₀K, hxσ₀⟩
      refine ⟨fun σ hσ => ?_, Or.inl htriv⟩
      exact (oneOne_eq_one_iff K n σ).mp (htriv σ hσ)
    · -- cyclicity and total ramification at the places of new ramification
      intro A hA hhyp htriv
      obtain ⟨σ₀, hσ₀I, hσ₀K, hσ₀ne⟩ := hhyp
      have hxσ₀ : x σ₀ ≠ 0 := by
        intro hx0
        apply hσ₀ne
        rw [twistSplit_apply, hx0]
        have hψσ₀ : splitSection (p := p) K n σ₀ = 1 :=
          (splitSection_eq_one_iff K n σ₀).mpr hσ₀K
        rw [hψσ₀]; simp
      have htrigger : ∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0 :=
        ⟨σ₀, hσ₀I, hσ₀K, hxσ₀⟩
      obtain ⟨V, hVopen, hVnorm, hVgen, hVcob⟩ := hcyc7 A hA htrigger
      have hxV : ∀ σ ∈ decomp ℚ A ⊓ V, x σ = 0 := fun σ hσ =>
        eq_zero_of_isCoboundaryOn p K n 1 1 hVcob σ hσ
          ((oneOne_eq_one_iff K n σ).mp (htriv σ (Subgroup.mem_inf.mp hσ).1))
      have hψA : ∀ σ ∈ decomp ℚ A, splitSection (p := p) K n σ = 1 := fun σ hσ =>
        (splitSection_eq_one_iff K n σ).mpr ((oneOne_eq_one_iff K n σ).mp (htriv σ hσ))
      obtain ⟨g, hg, hggen⟩ := hVgen
      refine ⟨?_, ?_⟩
      · refine isCyclic_map_flowTwistEHom_of_localCyclic p K n 1 1 x
          (splitSection (p := p) K n) (oneOne (p := p) K n) (splitSection_quot K n)
          (oneOne_quot K n) hxmul A htriv hψA (decomp ℚ A ⊓ V) inf_le_left hxV g hg ?_
        intro δ hδ
        obtain ⟨m, hm⟩ := hggen δ hδ
        exact ⟨m, Subgroup.mem_inf.mpr
          ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hδ) (Subgroup.zpow_mem _ hg m), hm⟩⟩
      · exact inertia_map_eq_flowTwistEHom p K n 1 1 x (splitSection (p := p) K n)
          (oneOne (p := p) K n) (splitSection_quot K n) hxmul hLift A htriv
          (isCyclic_map_flowTwistEHom_of_localCyclic p K n 1 1 x
            (splitSection (p := p) K n) (oneOne (p := p) K n) (splitSection_quot K n)
            (oneOne_quot K n) hxmul A htriv hψA (decomp ℚ A ⊓ V) inf_le_left hxV g hg
            (fun δ hδ => by
              obtain ⟨m, hm⟩ := hggen δ hδ
              exact ⟨m, Subgroup.mem_inf.mpr
                ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hδ) (Subgroup.zpow_mem _ hg m), hm⟩⟩))
          ⟨σ₀, hσ₀I, hσ₀ne⟩

end Main

/-! ## The auxiliary split places indexed by `E(n,1,1)` -/

/-- For a finite Galois extension `K/ℚ` (inside `ℚ̄`), a level `n` and a finite set `S` of finite
places of `ℚ̄`, there is a family `t` of pairwise non-conjugate finite places, indexed by the finite
`𝔽_p`-module `E(n,1,1)`, such that every `t e` splits completely in `K/ℚ` and is not conjugate to
any element of `S`. -/
theorem exists_split_places_of_module (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n : ℕ)
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hS : ∀ A ∈ S, SSGRoute.IsFinPlace ℚ A) :
    ∃ t : E p (K ≃ₐ[ℚ] K) n 1 1 → ValuationSubring SSGRoute.QBar,
      (∀ e, IsFinPlace ℚ (t e) ∧ IsSplitIn ℚ K (t e)) ∧
      (∀ e e', e ≠ e' → ¬ IsConjPlace ℚ (t e) (t e')) ∧
      (∀ e, ∀ A ∈ S, ¬ IsConjPlace ℚ A (t e)) ∧
      ∃ St : Finset (ValuationSubring SSGRoute.QBar),
        (∀ A ∈ St, ∃ e, t e = A) ∧ (∀ e, t e ∈ St) := by
  classical
  haveI hEfin : Finite (E p (K ≃ₐ[ℚ] K) n 1 1) :=
    flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) n 1 1
  haveI : Fintype (E p (K ≃ₐ[ℚ] K) n 1 1) := Fintype.ofFinite _
  obtain ⟨T, hTcard, hTfin, hTsplit, hTavoid, hTdisj⟩ :=
    @Work.SSGRoute.exists_split_places_avoiding ℚ SSGRoute.QBar _ _ _ _ _ K _
      (Work.SSGRoute.isGalois_of_normal K) S hS
      (Fintype.card (E p (K ≃ₐ[ℚ] K) n 1 1))
  have hcard : T.card = Fintype.card (E p (K ≃ₐ[ℚ] K) n 1 1) := hTcard
  let idx : E p (K ≃ₐ[ℚ] K) n 1 1 ≃ T :=
    (Fintype.equivFin (E p (K ≃ₐ[ℚ] K) n 1 1)).trans (hcard ▸ (Finset.equivFin T).symm)
  refine ⟨fun e => (idx e : ValuationSubring SSGRoute.QBar), ?_, ?_, ?_, T, ?_, ?_⟩
  · intro e; exact ⟨hTfin _ (idx e).2, hTsplit _ (idx e).2⟩
  · intro e e' hne hconj
    have hEq : (idx e : ValuationSubring SSGRoute.QBar) = (idx e') :=
      hTdisj _ (idx e).2 _ (idx e').2 hconj
    exact hne (idx.injective (Subtype.ext hEq))
  · intro e A hA hconj
    exact hTavoid _ (idx e).2 A hA (isConjPlace_symm hconj)
  · intro A hA
    exact ⟨idx.symm ⟨A, hA⟩, by simp⟩
  · intro e; exact (idx e).2

/-- **The hypotheses of `SSGRoute.shafarevich_existence` for `k := ℚ`, `Λ := K`**, for a class
`y` on `G_K`: additivity, local constancy, unramifiedness outside `cs(S)` at the places that do not
split in `K`, unramifiedness at `cs(S)`, vanishing on the decomposition groups over `cs(S)` of the
places that are non-split or over `p`, and vanishing on the involutions of `G_K`.

This is the input predicate of the class `x` of Theorem 13 in the N5 construction (`S = S₀ ∪ t(E)`,
`K` playing both the roles of `K` and `Λ`), isolated here so that the Grünwald-to-Theorem-13 step
(child (iv) of N5) can be stated and proved on its own. -/
def ShafHypotheses (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n : ℕ) (S : Finset (ValuationSubring SSGRoute.QBar))
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1) : Prop :=
  (∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup, y (σ * τ) = y σ + y τ) ∧
  SSGRoute.IsLocConstOn K.fixingSubgroup y ∧
  (∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
    (∀ A ∈ S, ¬ IsConjPlace ℚ A B) → ¬ IsSplitIn ℚ K B →
    ∀ σ ∈ K.fixingSubgroup, IsInertia ℚ B σ → y σ = 0) ∧
  (∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
    (∃ A ∈ S, IsConjPlace ℚ A B) →
    ∀ σ ∈ K.fixingSubgroup, IsInertia ℚ B σ → y σ = 0) ∧
  (∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
    (∃ A ∈ S, IsConjPlace ℚ A B) →
    (¬ IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
    ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp ℚ B → y σ = 0) ∧
  (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)

/-! ## Child (iv): the class `y` on `G_K` from N3's escape class `ε` -/

section ShafChild

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ SSGRoute.QBar} [FiniteDimensional ℚ K]
  [Normal ℚ K] {n : ℕ}
variable {T_K : Finset (ValuationSubring SSGRoute.QBar)}
variable {f : ValuationSubring SSGRoute.QBar → (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) →
  E p (K ≃ₐ[ℚ] K) n 1 1}
variable {ε : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → E p (K ≃ₐ[ℚ] K) n 1 1}


/-- **Where the datum at a place of `T_K` kills the inertia, `ε` kills the inertia of the
`↥K`-conjugate places.**  This is the transport by conjugation (`step4_conj_eq_of_additive_K`) of
the inertia clause `hfinertia` along `IsConjPlace ↥K A B`. -/
lemma eps_eq_zero_of_isInertia_conj
    (hεadd : ∀ a b : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, ε (a * b) = ε a + ε b)
    (hεval : ∀ A ∈ T_K, ∀ δ ∈ SSGRoute.decomp ↥K A, ε δ = f A δ)
    {A B : ValuationSubring SSGRoute.QBar} (hA : A ∈ T_K) (hconj : IsConjPlace ↥K A B)
    (hfinertia : ∀ σ ∈ SSGRoute.decomp ↥K A, SSGRoute.IsInertia ↥K A σ → f A σ = 0)
    {σ : SSGRoute.GalQ} (hσK : σ ∈ K.fixingSubgroup) (hI : SSGRoute.IsInertia ℚ B σ) :
    ε ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩) = 0 := by
  classical
  obtain ⟨g, hg⟩ := hconj
  set σt := (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ with hσt
  have hI' : SSGRoute.IsInertia ↥K B σt := (local_transport_isInertia K B σ hσK).mpr hI
  have hkey : g * (g⁻¹ * σt * g) * g⁻¹ = σt := by group
  have hI'' : SSGRoute.IsInertia ↥K A (g⁻¹ * σt * g) :=
    (isInertia_conj A g (g⁻¹ * σt * g)).mp (by rw [hkey, hg]; exact hI')
  calc ε σt = ε (g * (g⁻¹ * σt * g) * g⁻¹) := by rw [hkey]
    _ = ε (g⁻¹ * σt * g) := step4_conj_eq_of_additive_K ε hεadd g _
    _ = f A (g⁻¹ * σt * g) := hεval A hA _ hI''.1
    _ = 0 := hfinertia _ hI''.1 hI''

/-- **Where the datum at a place of `T_K` vanishes, `ε` vanishes on the `↥K`-conjugate places.**
Same conjugation transport, for the decomposition-group clause. -/
lemma eps_eq_zero_of_mem_decomp_conj
    (hεadd : ∀ a b : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, ε (a * b) = ε a + ε b)
    (hεval : ∀ A ∈ T_K, ∀ δ ∈ SSGRoute.decomp ↥K A, ε δ = f A δ)
    {A B : ValuationSubring SSGRoute.QBar} (hA : A ∈ T_K) (hconj : IsConjPlace ↥K A B)
    (hfA : ∀ σ ∈ SSGRoute.decomp ↥K A, f A σ = 0)
    {σ : SSGRoute.GalQ} (hσK : σ ∈ K.fixingSubgroup) (hσD : σ ∈ decomp ℚ B) :
    ε ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩) = 0 := by
  classical
  obtain ⟨g, hg⟩ := hconj
  set σt := (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ with hσt
  have hmemB : σt ∈ SSGRoute.decomp ↥K B :=
    (local_transport_decomp K B σ hσK).mpr hσD
  have hkey : g * (g⁻¹ * σt * g) * g⁻¹ = σt := by group
  have hmemD : g⁻¹ * σt * g ∈ SSGRoute.decomp ↥K A := by
    have h := decomp_conj A g
    rw [hg] at h
    have h2 : σt ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))
        (SSGRoute.decomp ↥K A) := by rw [← h]; exact hmemB
    obtain ⟨x, hx, hxeq⟩ := h2
    have hx' : x = g⁻¹ * σt * g := by
      rw [← hxeq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [hx'] at hx
  calc ε σt = ε (g * (g⁻¹ * σt * g) * g⁻¹) := by rw [hkey]
    _ = ε (g⁻¹ * σt * g) := step4_conj_eq_of_additive_K ε hεadd g _
    _ = f A (g⁻¹ * σt * g) := hεval A hA _ hmemD
    _ = 0 := hfA _ hmemD

/-- **Child (iv) of N5: the class `y` on `G_K` from N3's escape class `ε`.**

Let `S` be the `ℚ`-transversal of the primes over `Ram(K/ℚ) ∪ {p}` together with the auxiliary
completely split places `t e` (`e ∈ E(n,1,1)`), let `T_K` be its `↥K`-transversal (child (ii)), let
`f` be the local datum on the places of `T_K` (killing the inertia, and trivial on the
representatives of the places of `cs(S)` that are non-split in `K` or lie over `p`; this is the
datum of children (i)/(iii)), and let `ε` be a class on `Gal(ℚ̄/↥K)` with the four clauses of
`grunwald_escape_support_E` for this data (with `L := K`).

Then the class `y := patchFun K ε` on `G_ℚ` satisfies the six hypotheses of Theorem 13
(`ShafHypotheses p K n S y`). -/
theorem shafHypotheses_patchFun
    (hKimag : p = 2 → ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → c = 1)
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hSfin : ∀ A ∈ S, IsFinPlace ℚ A)
    (T_K : Finset (ValuationSubring SSGRoute.QBar))
    (hTKfin : ∀ A ∈ T_K, IsFinPlace ↥K A)
    (hTKcover : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ↥K B →
      (∃ A₀ ∈ S, IsConjPlace ℚ A₀ B) → ∃ A ∈ T_K, IsConjPlace ↥K A B)
    (f : ValuationSubring SSGRoute.QBar → (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) →
      E p (K ≃ₐ[ℚ] K) n 1 1)
    (hfinertia : ∀ A ∈ T_K, ∀ σ ∈ SSGRoute.decomp ↥K A, SSGRoute.IsInertia ↥K A σ → f A σ = 0)
    (hfzeroS : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∃ A₀ ∈ S, IsConjPlace ℚ A₀ B) →
      (¬ IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ T_K, IsConjPlace ↥K A B ∧ ∀ σ ∈ SSGRoute.decomp ↥K A, f A σ = 0)
    (ε : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hεadd : ∀ a b : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, ε (a * b) = ε a + ε b)
    (hεloc : SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ε)
    (hεval : ∀ A ∈ T_K, ∀ δ ∈ SSGRoute.decomp ↥K A, ε δ = f A δ)
    (hεesc : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ↥K B →
      (∀ A ∈ T_K, ¬ IsConjPlace ↥K A B) → ¬ IsSplitIn ℚ K B →
      ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, SSGRoute.IsInertia ↥K B δ → ε δ = 0) :
    ShafHypotheses p K n S (patchFun K ε) := by
  classical
  haveI hEfin : Finite (E p (K ≃ₐ[ℚ] K) n 1 1) :=
    flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) n 1 1
  have hε1 : ε 1 = 0 := by
    have h := hεadd 1 1
    rw [mul_one] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- additivity
    intro σ hσ τ hτ
    rw [patchFun_of_mem K ε σ hσ, patchFun_of_mem K ε τ hτ,
      patchFun_of_mem K ε (σ * τ) (K.fixingSubgroup.mul_mem hσ hτ)]
    have hmul : (IntermediateField.fixingSubgroupEquiv K)
          ⟨σ * τ, K.fixingSubgroup.mul_mem hσ hτ⟩ =
        (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ *
        (IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩ := by
      rw [show (⟨σ * τ, K.fixingSubgroup.mul_mem hσ hτ⟩ : ↥(K.fixingSubgroup)) =
        ⟨σ, hσ⟩ * ⟨τ, hτ⟩ from rfl, map_mul]
    rw [hmul, hεadd]
  · -- local constancy
    exact isLocConstOn_patchFun K ε hεloc
  · -- `hyS`: N3's escape clause
    intro B hBfin hBnotS hBnsplit σ hσK hσI
    rw [patchFun_of_mem K ε σ hσK]
    by_cases hconj : ∃ A ∈ T_K, IsConjPlace ↥K A B
    · obtain ⟨A, hA, hconjA⟩ := hconj
      exact eps_eq_zero_of_isInertia_conj hεadd hεval hA hconjA (hfinertia A hA) hσK hσI
    · exact hεesc B ((local_transport_isFinPlace K B).mpr hBfin)
        (fun A hA hc => hconj ⟨A, hA, hc⟩) hBnsplit _
        ((local_transport_isInertia K B σ hσK).mpr hσI)
  · -- `hyT`: the places of `cs(S)`
    intro B hBfin hBS σ hσK hσI
    rw [patchFun_of_mem K ε σ hσK]
    obtain ⟨A, hA, hconjA⟩ := hTKcover B ((local_transport_isFinPlace K B).mpr hBfin) hBS
    exact eps_eq_zero_of_isInertia_conj hεadd hεval hA hconjA (hfinertia A hA) hσK hσI
  · -- `hy0`: the decomposition groups over `cs(S)`
    intro B hBfin hBS hbnp σ hσK hσD
    rw [patchFun_of_mem K ε σ hσK]
    obtain ⟨A, hA, hconjA, hfA⟩ := hfzeroS B hBfin hBS hbnp
    exact eps_eq_zero_of_mem_decomp_conj hεadd hεval hA hconjA hfA hσK hσD
  · -- `hyinf`: the involutions of `G_K`
    intro c hcK hc2
    rw [patchFun_of_mem K ε c hcK]
    by_cases hp2 : p = 2
    · have hc1 : (⟨c, hcK⟩ : ↥(K.fixingSubgroup)) = 1 := by
        ext y
        simpa using congrArg (fun (f : SSGRoute.GalQ) => f y) (hKimag hp2 c hc2 hcK)
      rw [hc1, map_one]
      exact hε1
    · -- `2 • ε c̃ = ε (c̃ * c̃) = ε 1 = 0`, and `2` is invertible in `ZMod p`
      set ct := (IntermediateField.fixingSubgroupEquiv K) ⟨c, hcK⟩ with hct
      have hsq : ct * ct = 1 := by
        have h1 : (⟨c, hcK⟩ : ↥(K.fixingSubgroup)) * ⟨c, hcK⟩ = 1 :=
          Subtype.ext (by simpa [pow_two] using hc2)
        rw [← map_mul, h1, map_one]
      have h2 : (2 : ℕ) • ε ct = 0 := by
        have h := hεadd ct ct
        rw [hsq, hε1] at h
        rw [two_nsmul]
        exact h.symm
      have hne : (2 : ZMod p) ≠ 0 := by
        intro h
        have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
        exact hp2 ((Nat.prime_two.dvd_iff_eq (Fact.out : p.Prime).ne_one).mp hdvd).symm
      have h3 : (2 : ZMod p) • (ε ct) = 0 := by
        have h3' : ((2 : ℕ) : ZMod p) • (ε ct) = 0 :=
          (Nat.cast_smul_eq_nsmul (ZMod p) 2 (ε ct)).trans h2
        simpa using h3'
      have h6 : (2 : ZMod p)⁻¹ • ((2 : ZMod p) • (ε ct)) = 0 := by
        rw [h3, smul_zero]
      rwa [← mul_smul, inv_mul_cancel₀ hne, one_smul] at h6

end ShafChild

/-! ## Child (ii): the `↥K`-transversal of the `ℚ`-classes of `S = S₀ ∪ t(E)` -/

section Transversal

variable (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]

/-- The Frobenius element of a completely split place `A`, transported to `Gal(ℚ̄/↥K)`: the image
of the `ℚ`-Frobenius `localFrobElem A` (which lies in `D_A ≤ G_K`) under
`IntermediateField.fixingSubgroupEquiv K`. -/
noncomputable def frobOfSplit (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsFinPlace ℚ A)
    (hsplit : SSGRoute.decomp ℚ A ≤ K.fixingSubgroup) :
    SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar :=
  (IntermediateField.fixingSubgroupEquiv K)
    ⟨((localFrobElem ⟨A, hA⟩ : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ),
      hsplit (localFrobElem ⟨A, hA⟩).2⟩

lemma frobOfSplit_mem (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsFinPlace ℚ A)
    (hsplit : SSGRoute.decomp ℚ A ≤ K.fixingSubgroup) :
    frobOfSplit K A hA hsplit ∈ SSGRoute.decomp ↥K A :=
  (local_transport_decomp K A
    ((localFrobElem ⟨A, hA⟩ : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)
    (hsplit (localFrobElem ⟨A, hA⟩).2)).mpr (localFrobElem ⟨A, hA⟩).2

end Transversal

/-- **Child (iii) of N5: the local datum of N3 at a completely split place.**

Let `A` be a finite place of `ℚ̄` completely decomposed in `K/ℚ` (`D_A ≤ G_K`) and let `e ∈ E(n,1,1)`.
Then there is an additive locally constant function on `D_A` over `↥K` which kills the inertia and
takes the value `e` at the transported Frobenius element `frobOfSplit`.

This is the input of `grunwald_escape_support_E` (with `L := K`) at the auxiliary places `t e`: the
`↥K`-form of `Work.SSGRoute.exists_cocycle_at_frob_of_split`, obtained by restricting the `ℚ`-datum
along `AlgEquiv.restrictScalars ℚ`. -/
theorem exists_localDatum_of_split (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n : ℕ)
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsFinPlace ℚ A)
    (hsplit : SSGRoute.IsSplitIn ℚ K A) (e : E p (K ≃ₐ[ℚ] K) n 1 1) :
    ∃ f : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → E p (K ≃ₐ[ℚ] K) n 1 1,
      (∀ a ∈ decomp ↥K A, ∀ b ∈ decomp ↥K A, f (a * b) = f a + f b) ∧
      (∃ U : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar),
        IsOpen (U : Set (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ∧
        ∀ x ∈ U, x ∈ decomp ↥K A → f x = 0) ∧
      (∀ σ ∈ decomp ↥K A, IsInertia ↥K A σ → f σ = 0) ∧
      f (frobOfSplit K A hA hsplit) = e := by
  classical
  haveI hGal : IsGalois ℚ K := IsGalois.mk
  haveI hEfin : Finite (E p (K ≃ₐ[ℚ] K) n 1 1) :=
    flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) n 1 1
  obtain ⟨g, hgcoc, hgloc, hginert, hgfrob⟩ :=
    exists_cocycle_at_frob_of_split p K A hA hsplit (E p (K ≃ₐ[ℚ] K) n 1 1) e
  -- the restriction of an element of `Gal(ℚ̄/↥K)` to `ℚ` lies in `K.fixingSubgroup`
  have hmemK : ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar,
      (AlgEquiv.restrictScalars ℚ δ : SSGRoute.GalQ) ∈ K.fixingSubgroup := by
    intro δ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h2 := AlgEquiv.commutes δ (⟨x, hx⟩ : ↥K)
    have h1 : algebraMap ↥K SSGRoute.QBar (⟨x, hx⟩ : ↥K) = x := rfl
    rw [h1] at h2
    exact h2
  -- transport of the decomposition-group condition
  have hmemD : ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar,
      (AlgEquiv.restrictScalars ℚ δ : SSGRoute.GalQ) ∈ decomp ℚ A ↔ δ ∈ decomp ↥K A := by
    intro δ
    have heq : (IntermediateField.fixingSubgroupEquiv K)
        ⟨(AlgEquiv.restrictScalars ℚ δ : SSGRoute.GalQ), hmemK δ⟩ = δ :=
      AlgEquiv.ext (fun _ => rfl)
    have h := local_transport_decomp K A (AlgEquiv.restrictScalars ℚ δ) (hmemK δ)
    rw [heq] at h
    exact h.symm
  -- transport of the inertia condition
  have hmemI : ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar,
      IsInertia ↥K A δ ↔ IsInertia ℚ A (AlgEquiv.restrictScalars ℚ δ : SSGRoute.GalQ) := by
    intro δ
    have heq : (IntermediateField.fixingSubgroupEquiv K)
        ⟨(AlgEquiv.restrictScalars ℚ δ : SSGRoute.GalQ), hmemK δ⟩ = δ :=
      AlgEquiv.ext (fun _ => rfl)
    have h := local_transport_isInertia K A (AlgEquiv.restrictScalars ℚ δ) (hmemK δ)
    rw [heq] at h
    exact h.symm
  refine ⟨fun δ => g (AlgEquiv.restrictScalars ℚ δ), ?_, ?_, ?_, ?_⟩
  · -- additivity
    intro a ha b hb
    show g (AlgEquiv.restrictScalars ℚ (a * b)) =
      g (AlgEquiv.restrictScalars ℚ a) + g (AlgEquiv.restrictScalars ℚ b)
    have hmap : (AlgEquiv.restrictScalars ℚ (a * b) : SSGRoute.GalQ) =
        AlgEquiv.restrictScalars ℚ a * AlgEquiv.restrictScalars ℚ b := rfl
    rw [hmap, hgcoc _ ((hmemD a).mpr ha) _ ((hmemD b).mpr hb),
      restrict_eq_one_of_mem_fixingSubgroup K (hmemK a), one_smul]
  · -- local constancy
    obtain ⟨U₀, hU₀open, hU₀prop⟩ := hgloc
    obtain ⟨M, hMfd, hMnorm, hMU⟩ : ∃ M : IntermediateField ℚ SSGRoute.QBar,
        FiniteDimensional ℚ M ∧ Normal ℚ M ∧ M.fixingSubgroup ≤ U₀ :=
      exists_finiteDimensional_normal_fixingSubgroup_le (U := ℚ) (L := SSGRoute.QBar) U₀ hU₀open
    haveI := hMfd
    haveI := hMnorm
    haveI hfdN : FiniteDimensional ↥K (overK K (M ⊔ K) le_sup_right) :=
      finiteDimensional_overK_of_finite K (M ⊔ K) le_sup_right
    refine ⟨(overK K (M ⊔ K) le_sup_right).fixingSubgroup, ?_, ?_⟩
    · exact IntermediateField.fixingSubgroup_isOpen _
    · intro x hx hxD
      show g (AlgEquiv.restrictScalars ℚ x) = 0
      have hxM : (AlgEquiv.restrictScalars ℚ x : SSGRoute.GalQ) ∈ M.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        have hyN : y ∈ overK K (M ⊔ K) le_sup_right := (le_sup_left : M ≤ M ⊔ K) hy
        have h2 : x ((⟨y, hyN⟩ : ↥(overK K (M ⊔ K) le_sup_right)) :
            SSGRoute.QBar) = ((⟨y, hyN⟩ : ↥(overK K (M ⊔ K) le_sup_right)) : SSGRoute.QBar) :=
          (IntermediateField.mem_fixingSubgroup_iff _ x).mp hx _ hyN
        have h3 : ((⟨y, hyN⟩ : ↥(overK K (M ⊔ K) le_sup_right)) : SSGRoute.QBar) = y := rfl
        simpa [h3] using h2
      have hxU₀ : (AlgEquiv.restrictScalars ℚ x : SSGRoute.GalQ) ∈ U₀ := hMU hxM
      have hxD' : (AlgEquiv.restrictScalars ℚ x : SSGRoute.GalQ) ∈ decomp ℚ A := (hmemD x).mpr hxD
      have hg1 : g 1 = 0 := by
        have h := hgcoc 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
        rw [mul_one, map_one, one_smul] at h
        exact add_left_cancel (h.symm.trans (add_zero _).symm)
      have h1 : g ((AlgEquiv.restrictScalars ℚ x) * 1) = g 1 :=
        hU₀prop 1 (Subgroup.one_mem _) _ hxU₀ (by simpa using hxD')
      rw [mul_one, hg1] at h1
      exact h1
  · -- the inertia group is killed
    intro σ hσ hσI
    show g (AlgEquiv.restrictScalars ℚ σ) = 0
    exact hginert _ ((hmemD σ).mpr hσ) ((hmemI σ).mpr hσI)
  · -- the value at the Frobenius
    show g (AlgEquiv.restrictScalars ℚ (frobOfSplit K A hA hsplit)) = e
    have hfr : AlgEquiv.restrictScalars ℚ (frobOfSplit K A hA hsplit) =
        ((localFrobElem ⟨A, hA⟩ : ↥(decomp ℚ A)) : SSGRoute.GalQ) := by
      simp only [frobOfSplit]
      rfl
    rw [hfr]
    exact hgfrob

/-- **Child (ii) of N5.**  The `↥K`-transversal `T_K` of the `ℚ`-classes of `S₀ ∪ t(E)`:

* its elements are finite places over `↥K` and are pairwise non-`↥K`-conjugate;
* every place over the prime `p` is `↥K`-conjugate to an element of `T_K` (N3's `hTcov`; the
  ramification of `K/K` is vacuous);
* every place that is `ℚ`-conjugate to an element of `S₀ ∪ t(E)` is `↥K`-conjugate to an element
  of `T_K` (this is what makes N3's escape clause give the hypothesis `hyS` of
  `shafarevich_existence`), and in particular `t e` itself is. -/
theorem exists_TK_transversal (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n : ℕ)
    (S₀ : Finset (ValuationSubring SSGRoute.QBar))
    (hS₀fin : ∀ A ∈ S₀, IsFinPlace ℚ A)
    (hS₀disj : ∀ A ∈ S₀, ∀ B ∈ S₀, IsConjPlace ℚ A B → A = B)
    (hS₀ram : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (IsRamifiedIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S₀, IsConjPlace ℚ A B)
    (t : E p (K ≃ₐ[ℚ] K) n 1 1 → ValuationSubring SSGRoute.QBar)
    (htfin : ∀ e, IsFinPlace ℚ (t e)) (htsplit : ∀ e, IsSplitIn ℚ K (t e))
    (htavoid : ∀ e, ∀ A ∈ S₀, ¬ IsConjPlace ℚ A (t e))
    (htdisj : ∀ e e', e ≠ e' → ¬ IsConjPlace ℚ (t e) (t e')) :
    ∃ T_K : Finset (ValuationSubring SSGRoute.QBar),
      (∀ A ∈ T_K, IsFinPlace ↥K A) ∧
      (∀ A ∈ T_K, ∀ B ∈ T_K, IsConjPlace ↥K A B → A = B) ∧
      (∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ↥K B →
        (B.valuation (p : SSGRoute.QBar) < 1 ∨
          IsRamifiedIn ↥K (overK K K le_rfl) B) →
        ∃ A ∈ T_K, IsConjPlace ↥K A B) ∧
      (∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ↥K B →
        (∃ A₀ ∈ S₀, IsConjPlace ℚ A₀ B) ∨ (∃ e, IsConjPlace ℚ (t e) B) →
        ∃ A ∈ T_K, IsConjPlace ↥K A B) ∧
      (∀ e, ∃ A ∈ T_K, IsConjPlace ↥K A (t e)) := by
  classical
  haveI hEfin : Finite (E p (K ≃ₐ[ℚ] K) n 1 1) :=
    flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) n 1 1
  haveI : Fintype (E p (K ≃ₐ[ℚ] K) n 1 1) := Fintype.ofFinite _
  set S : Finset (ValuationSubring SSGRoute.QBar) :=
    S₀ ∪ (Finset.univ.image t) with hS
  have hSfin : ∀ A ∈ S, IsFinPlace ℚ A := by
    intro A hA
    rcases Finset.mem_union.mp hA with h | h
    · exact hS₀fin A h
    · obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp h
      exact htfin e
  have hSdisj : ∀ A ∈ S, ∀ B ∈ S, IsConjPlace ℚ A B → A = B := by
    intro A hA B hB hconj
    rcases Finset.mem_union.mp hA with hA | hA <;> rcases Finset.mem_union.mp hB with hB | hB
    · exact hS₀disj A hA B hB hconj
    · obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hB
      exact absurd hconj (htavoid e A hA)
    · obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hA
      exact absurd (isConjPlace_symm hconj) (htavoid e B hB)
    · obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨e', -, rfl⟩ := Finset.mem_image.mp hB
      by_contra hne
      exact htdisj e e' (fun h => hne (by rw [h])) hconj
  obtain ⟨T_K, hTKfin, hTKdisj, -, hTKcover⟩ :=
    step4_isConjPlace_cover K S hSfin hSdisj
  refine ⟨T_K, hTKfin, hTKdisj, ?_, ?_, ?_⟩
  · -- the places over `p`
    intro B hBfin hBp
    have hBℚ : IsFinPlace ℚ B := (local_transport_isFinPlace K B).mp hBfin
    rcases hBp with hval | hram
    · obtain ⟨A, hA, hconj⟩ := hS₀ram B hBℚ (Or.inr hval)
      exact hTKcover B hBfin ⟨A, Finset.mem_union_left _ hA, hconj⟩
    · -- `IsRamifiedIn ↥K (overK K K) B` is vacuous
      exfalso
      obtain ⟨σ, -, hσN⟩ := hram
      exact hσN (by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have hxK : x ∈ K := hx
        have h1 : algebraMap ↥K SSGRoute.QBar (⟨x, hxK⟩ : ↥K) = x := rfl
        have h2 := AlgEquiv.commutes σ (⟨x, hxK⟩ : ↥K)
        rw [h1] at h2
        exact h2)
  · -- the `ℚ`-classes of `S`
    intro B hBfin hEx
    refine hTKcover B hBfin ?_
    rcases hEx with ⟨A₀, hA₀, hconj⟩ | ⟨e, hconj⟩
    · exact ⟨A₀, Finset.mem_union_left _ hA₀, hconj⟩
    · exact ⟨t e, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩), hconj⟩
  · -- the auxiliary places themselves
    intro e
    refine hTKcover (t e) ((local_transport_isFinPlace K (t e)).mpr (htfin e))
      ⟨t e, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩), isConjPlace_refl (t e)⟩

/-! ## Piece (0a): the datum of N3 over the `↥K`-transversal `T_K` -/

/-- **N5, piece (0a): the datum of N3 over the `↥K`-transversal `T_K` (with its Frobenius values).**

Let `T_K` be a set of pairwise non-`↥K`-conjugate finite places of `ℚ̄` over `↥K`, and let
`t : E(n,1,1) → places` be the auxiliary family of child (i) (each `t e` splits completely in `K`,
the `t e` are pairwise non-`ℚ`-conjugate, and each is `↥K`-conjugate to an element of `T_K`).

Then there is a local datum `f` on the places of `T_K` which is additive on each decomposition
group, locally constant, kills the inertia, vanishes identically on the decomposition groups of the
places of `T_K` that are not `↥K`-conjugate to any auxiliary place, and whose value at the
transported Frobenius is prescribed: if `g • A = t e` then `f A (g⁻¹ * Frob(t e) * g) = e`.

Construction: choose, for each `e`, a representative `Ae e ∈ T_K` with `g e • Ae e = t e`; at
`Ae e` take the datum `hF e` of `exists_localDatum_of_split` at `t e` transported along `g e`
(`δ ↦ hF e (g e * δ * (g e)⁻¹)`), and `0` at all other places of `T_K`.  The prescribed-value
clause uses the conjugation-invariance of `hF e` on `decomp ↥K (t e)` (a consequence of additivity
into an abelian group), and the well-definedness of the choice of `e` uses `htdisj`. -/
theorem exists_datum_of_places (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n : ℕ)
    (T_K : Finset (ValuationSubring SSGRoute.QBar))
    (hTKfin : ∀ A ∈ T_K, IsFinPlace ↥K A)
    (hTKdisj : ∀ A ∈ T_K, ∀ B ∈ T_K, IsConjPlace ↥K A B → A = B)
    (t : E p (K ≃ₐ[ℚ] K) n 1 1 → ValuationSubring SSGRoute.QBar)
    (htfin : ∀ e, IsFinPlace ℚ (t e)) (htsplit : ∀ e, IsSplitIn ℚ K (t e))
    (htdisj : ∀ e e', e ≠ e' → ¬ IsConjPlace ℚ (t e) (t e'))
    (htrepr : ∀ e, ∃ A ∈ T_K, IsConjPlace ↥K A (t e)) :
    ∃ f : ValuationSubring SSGRoute.QBar → (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) →
      E p (K ≃ₐ[ℚ] K) n 1 1,
      (∀ A ∈ T_K, ∀ a ∈ SSGRoute.decomp ↥K A, ∀ b ∈ SSGRoute.decomp ↥K A,
        f A (a * b) = f A a + f A b) ∧
      (∀ A ∈ T_K, ∃ U : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar),
        IsOpen (U : Set (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ∧
        ∀ x ∈ U, x ∈ SSGRoute.decomp ↥K A → f A x = 0) ∧
      (∀ A ∈ T_K, ∀ σ ∈ SSGRoute.decomp ↥K A, SSGRoute.IsInertia ↥K A σ → f A σ = 0) ∧
      (∀ A ∈ T_K, (∀ e, ¬ IsConjPlace ↥K A (t e)) →
        ∀ σ ∈ SSGRoute.decomp ↥K A, f A σ = 0) ∧
      (∀ (e : E p (K ≃ₐ[ℚ] K) n 1 1) (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ T_K)
        (g₀ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar), g₀ • A = t e →
        f A (g₀⁻¹ * frobOfSplit K (t e) (htfin e) (htsplit e) * g₀) = e) := by
  classical
  haveI hEfin : Finite (E p (K ≃ₐ[ℚ] K) n 1 1) :=
    flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) n 1 1
  choose Ae hAeT hAeconj using htrepr
  choose g hg using hAeconj
  choose hF hFadd hFloc hFinert hFfrob using fun e =>
    exists_localDatum_of_split p K n (t e) (htfin e) (htsplit e) e
  -- the datum: at `Ae e` the transport of `hF e` along `g e`, and `0` elsewhere
  let F : ValuationSubring SSGRoute.QBar → (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) →
      E p (K ≃ₐ[ℚ] K) n 1 1 := fun A δ =>
    if h : ∃ e, A = Ae e then hF h.choose (g h.choose * δ * (g h.choose)⁻¹) else 0
  have hFval : ∀ {A : ValuationSubring SSGRoute.QBar} (hex : ∃ e, A = Ae e) (δ : _),
      F A δ = hF hex.choose (g hex.choose * δ * (g hex.choose)⁻¹) := fun hex δ => dif_pos hex
  have hFzero : ∀ {A : ValuationSubring SSGRoute.QBar}, (¬ ∃ e, A = Ae e) → ∀ δ, F A δ = 0 :=
    fun h δ => dif_neg h
  -- `↥K`-conjugacy implies `ℚ`-conjugacy
  have hKQ : ∀ {A B : ValuationSubring SSGRoute.QBar}, IsConjPlace ↥K A B → IsConjPlace ℚ A B := by
    rintro A B ⟨σ, hσ⟩
    refine ⟨AlgEquiv.restrictScalars ℚ σ, ?_⟩
    rw [← hσ]
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists,
      ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, by rw [← hyx, AlgEquiv.smul_def, AlgEquiv.smul_def]; rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, by rw [← hyx, AlgEquiv.smul_def, AlgEquiv.smul_def]; rfl⟩
  -- the membership transport under conjugation
  have hmem_conj : ∀ {A : ValuationSubring SSGRoute.QBar} {e : E p (K ≃ₐ[ℚ] K) n 1 1},
      A = Ae e → ∀ {δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar},
      δ ∈ SSGRoute.decomp ↥K A → g e * δ * (g e)⁻¹ ∈ SSGRoute.decomp ↥K (t e) := by
    intro A e hAe δ hδ
    have hgA' : g e • A = t e := by rw [hAe]; exact hg e
    have h := decomp_conj A (g e)
    have h2 : (MulEquiv.toMonoidHom (MulAut.conj (g e))) δ ∈
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (g e))) (SSGRoute.decomp ↥K A) :=
      Subgroup.mem_map_of_mem _ hδ
    rw [← h, hgA'] at h2
    simpa [MulAut.conj_apply] using h2
  -- conjugation-invariance of `hF e` on its own decomposition group
  have hconj_inv : ∀ e (u v : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar),
      u ∈ SSGRoute.decomp ↥K (t e) → v ∈ SSGRoute.decomp ↥K (t e) →
      hF e (u * v * u⁻¹) = hF e v := by
    intro e u v hu hv
    have h1 : hF e 1 = 0 := by
      have hh := hFadd e 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
      rw [mul_one] at hh
      exact add_left_cancel (hh.symm.trans (add_zero _).symm)
    have h3 : hF e u + hF e u⁻¹ = 0 := by
      have h := hFadd e u hu u⁻¹ (Subgroup.inv_mem _ hu)
      rw [mul_inv_cancel, h1] at h
      exact h.symm
    calc hF e (u * v * u⁻¹) = hF e (u * v) + hF e u⁻¹ :=
          hFadd e _ (Subgroup.mul_mem _ hu hv) _ (Subgroup.inv_mem _ hu)
      _ = (hF e u + hF e v) + hF e u⁻¹ := by rw [hFadd e u hu v hv]
      _ = hF e v := by
          rw [show (hF e u + hF e v) + hF e u⁻¹ = hF e v + (hF e u + hF e u⁻¹) from by abel,
            h3, add_zero]
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · -- additivity
    intro A hA a ha b hb
    by_cases hex : ∃ e, A = Ae e
    · rw [hFval hex (a * b), hFval hex a, hFval hex b]
      have hkey : g hex.choose * (a * b) * (g hex.choose)⁻¹ =
          (g hex.choose * a * (g hex.choose)⁻¹) *
          (g hex.choose * b * (g hex.choose)⁻¹) := by group
      rw [hkey]
      exact hFadd hex.choose _ (hmem_conj hex.choose_spec ha) _
        (hmem_conj hex.choose_spec hb)
    · rw [hFzero hex (a * b), hFzero hex a, hFzero hex b, add_zero]
  · -- local constancy
    intro A hA
    by_cases hex : ∃ e, A = Ae e
    · obtain ⟨U, hUopen, hU0⟩ := hFloc hex.choose
      refine ⟨conjSubgroup (g hex.choose)⁻¹ U, isOpen_conjSubgroup _ _ hUopen, ?_⟩
      intro x hx hxD
      rw [hFval hex x]
      refine hU0 _ ?_ (hmem_conj hex.choose_spec hxD)
      simpa using hx
    · refine ⟨⊤, isOpen_univ, ?_⟩
      intro x hx hxD
      rw [hFzero hex x]
  · -- the datum kills the inertia
    intro A hA σ hσ hσI
    by_cases hex : ∃ e, A = Ae e
    · rw [hFval hex σ]
      have hgg : g hex.choose • A = t hex.choose :=
        (congrArg (fun B => g hex.choose • B) hex.choose_spec).trans (hg hex.choose)
      have hI : SSGRoute.IsInertia ↥K (t hex.choose)
          (g hex.choose * σ * (g hex.choose)⁻¹) :=
        hgg ▸ (isInertia_conj A (g hex.choose) σ).mpr hσI
      exact hFinert hex.choose _ hI.1 hI
    · rw [hFzero hex σ]
  · -- the datum is `0` away from the auxiliary classes
    intro A hA hno σ hσ
    refine hFzero (fun hex => ?_) σ
    obtain ⟨e, he⟩ := hex
    exact hno e ⟨g e, (congrArg (fun B => g e • B) he).trans (hg e)⟩
  · -- the prescribed value at the transported Frobenius
    intro e A hA g₀ hg₀
    have hAe' : A = Ae e := by
      refine hTKdisj A hA (Ae e) (hAeT e) ?_
      exact isConjPlace_trans ⟨g₀, hg₀⟩ (isConjPlace_symm ⟨g e, hg e⟩)
    have hex : ∃ e', A = Ae e' := ⟨e, hAe'⟩
    have heq : hex.choose = e := by
      by_contra hne
      refine htdisj _ _ hne (hKQ ?_)
      have h1 : IsConjPlace ↥K (t hex.choose) (Ae hex.choose) := by
        have hthis := hg hex.choose
        exact ⟨(g hex.choose)⁻¹, by rw [← hthis, ← mul_smul, inv_mul_cancel, one_smul]⟩
      have h2 : IsConjPlace ↥K (Ae hex.choose) A :=
        ⟨1, by rw [← hex.choose_spec, one_smul]⟩
      exact isConjPlace_trans h1 (isConjPlace_trans h2 ⟨g₀, hg₀⟩)
    rw [hFval hex (g₀⁻¹ * frobOfSplit K (t e) (htfin e) (htsplit e) * g₀), heq]
    have hkey : g e * (g₀⁻¹ * frobOfSplit K (t e) (htfin e) (htsplit e) * g₀) * (g e)⁻¹ =
        (g e * g₀⁻¹) * frobOfSplit K (t e) (htfin e) (htsplit e) * (g e * g₀⁻¹)⁻¹ := by
      group
    rw [hkey]
    have hu : g e * g₀⁻¹ ∈ SSGRoute.decomp ↥K (t e) := by
      have h1 : g₀⁻¹ • (t e) = A := by rw [← hg₀, ← mul_smul, inv_mul_cancel, one_smul]
      have h2 : g e • A = t e := (congrArg (fun B => g e • B) hAe').trans (hg e)
      rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff, mul_smul, h1, h2]
    have hv : frobOfSplit K (t e) (htfin e) (htsplit e) ∈ SSGRoute.decomp ↥K (t e) :=
      frobOfSplit_mem K (t e) (htfin e) (htsplit e)
    rw [hconj_inv e _ _ hu hv, hFfrob e]

/-! ## The local clauses of the `(1,1) → (2,1)` step

The lemmas of this section verify the hypotheses of `isScholzSolution_twistSplit` from the clauses of
Theorem 13 (`SSGRoute.shafarevich_existence`) for `k := ℚ`, `Λ := K`. -/

section TwoOneClauses

variable (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]

/-- The valuation of `p` is invariant under translation of the place: conjugate places lie over the
same prime of `ℚ`. -/
lemma valuation_p_lt_one_smul (p : ℕ) (A : ValuationSubring SSGRoute.QBar) (g : SSGRoute.GalQ) :
    (g • A).valuation (p : SSGRoute.QBar) < 1 ↔ A.valuation (p : SSGRoute.QBar) < 1 := by
  have hw : (p : SSGRoute.QBar) ∈ A := by simp
  have hgw : g • (p : SSGRoute.QBar) = (p : SSGRoute.QBar) := by
    rw [show (p : SSGRoute.QBar) = algebraMap ℚ SSGRoute.QBar p from (map_natCast _ p).symm]
    exact g.commutes p
  have h := smul_valuation_lt_one (k := ℚ) g A (p : SSGRoute.QBar) hw
  rwa [hgw] at h

/-- `↥K`-conjugacy of places implies `ℚ`-conjugacy. -/
lemma isConjPlace_K_Q {A B : ValuationSubring SSGRoute.QBar} (h : IsConjPlace ↥K A B) :
    IsConjPlace ℚ A B := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨AlgEquiv.restrictScalars ℚ σ, ?_⟩
  rw [← hσ]
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, by rw [← hyx, AlgEquiv.smul_def, AlgEquiv.smul_def]; rfl⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, by rw [← hyx, AlgEquiv.smul_def, AlgEquiv.smul_def]; rfl⟩

/-- Translating by `τ` conjugates the values of a `1`-cocycle for the `G(K/ℚ)`-action. -/
lemma cocycle_conj_apply (p : ℕ) [Fact p.Prime] (n i j : ℕ)
    {x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j}
    (hx : IsCocycleOn (restrict K) ⊤ x) {σ : SSGRoute.GalQ} (hσ : σ ∈ K.fixingSubgroup)
    (τ : SSGRoute.GalQ) :
    x (τ⁻¹ * σ * τ) = (restrict K τ)⁻¹ • x σ := by
  have h1 : x 1 = 0 := isCocycleOn_apply_one hx
  have hres : restrict K σ = 1 := restrict_eq_one_of_mem_fixingSubgroup K hσ
  have h2 : x (τ⁻¹ * (σ * τ)) = x τ⁻¹ + (restrict K τ)⁻¹ • x (σ * τ) := by
    rw [hx τ⁻¹ (Subgroup.mem_top _) (σ * τ) (Subgroup.mem_top _), map_inv]
  have h3 : x (σ * τ) = x σ + x τ := by
    rw [hx σ (Subgroup.mem_top _) τ (Subgroup.mem_top _), hres, one_smul]
  have h4 : x τ⁻¹ + (restrict K τ)⁻¹ • x τ = 0 := by
    have h := hx τ⁻¹ (Subgroup.mem_top _) τ (Subgroup.mem_top _)
    rw [inv_mul_cancel, h1, map_inv] at h
    exact h.symm
  calc x (τ⁻¹ * σ * τ) = x (τ⁻¹ * (σ * τ)) := by rw [mul_assoc]
    _ = x τ⁻¹ + (restrict K τ)⁻¹ • x (σ * τ) := h2
    _ = x τ⁻¹ + (restrict K τ)⁻¹ • (x σ + x τ) := by rw [h3]
    _ = x τ⁻¹ + ((restrict K τ)⁻¹ • x σ + (restrict K τ)⁻¹ • x τ) := by rw [smul_add]
    _ = (restrict K τ)⁻¹ • x σ := by
        have h5 : x τ⁻¹ + ((restrict K τ)⁻¹ • x σ + (restrict K τ)⁻¹ • x τ)
            = (restrict K τ)⁻¹ • x σ + (x τ⁻¹ + (restrict K τ)⁻¹ • x τ) := by abel
        rw [h5, h4, add_zero]

/-- The same translation, as a vanishing criterion. -/
lemma cocycle_conj_eq_zero_iff (p : ℕ) [Fact p.Prime] (n i j : ℕ)
    {x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j}
    (hx : IsCocycleOn (restrict K) ⊤ x) {σ : SSGRoute.GalQ} (hσ : σ ∈ K.fixingSubgroup)
    (τ : SSGRoute.GalQ) :
    x (τ * σ * τ⁻¹) = 0 ↔ x σ = 0 := by
  have h1 : x (τ * σ * τ⁻¹) = (restrict K τ) • x σ := by
    have h := cocycle_conj_apply K p n i j hx hσ τ⁻¹
    rw [inv_inv, map_inv, inv_inv] at h
    exact h
  rw [h1]
  constructor
  · intro h
    have h2 : (restrict K τ)⁻¹ • ((restrict K τ) • x σ) = 0 := by rw [h, smul_zero]
    rwa [← mul_smul, inv_mul_cancel, one_smul] at h2
  · intro h; rw [h, smul_zero]

/-- **The inertia of a place `ℚ`-conjugate to an element of `S` is killed by `x`.**

At a place of `S` that is not split in `K` this is Theorem 13's clause (4); at a place of `S` that
splits it is clause (3) together with the vanishing of `y` on the inertias of the conjugates
(hypothesis `hyT`); a general place is reduced to one of `S` by the conjugation rule
`cocycle_conj_apply`. -/
theorem x_eq_zero_on_inertia_of_conj_S
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hSfin : ∀ A ∈ S, IsFinPlace ℚ A)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec : ∀ s, restrict K (sec s) = s)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hyT : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∃ A ∈ S, IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia ℚ B σ → y σ = 0)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hx1 : IsCocycleOn (restrict K) ⊤ x)
    (hx3 : ∀ A ∈ S, IsSplitIn ℚ K A → IsCoboundaryOn (restrict K) (decomp ℚ A)
      (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)))
    (hx4 : ∀ A ∈ S, ¬ IsSplitIn ℚ K A → IsCoboundaryOn (restrict K) (decomp ℚ A) x)
    {B : ValuationSubring SSGRoute.QBar} (hB : IsFinPlace ℚ B)
    (hconj : ∃ A ∈ S, IsConjPlace ℚ A B)
    {σ : SSGRoute.GalQ} (hσK : σ ∈ K.fixingSubgroup) (hσI : IsInertia ℚ B σ) :
    x σ = 0 := by
  classical
  haveI hGalQ : IsGalois ℚ SSGRoute.QBar :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  haveI hGal : IsGalois ℚ K := Work.SSGRoute.isGalois_of_normal K
  have hnorm : K.fixingSubgroup.Normal :=
    @IsGalois.fixingSubgroup_normal_of_isGalois ℚ SSGRoute.QBar _ _ _ K hGalQ hGal
  -- the statement at a place of `S`
  have key : ∀ {C : ValuationSubring SSGRoute.QBar}, C ∈ S →
      ∀ {τ : SSGRoute.GalQ}, τ ∈ K.fixingSubgroup → IsInertia ℚ C τ → x τ = 0 := by
    intro C hCS τ hτK hτI
    by_cases hsplit : IsSplitIn ℚ K C
    · obtain ⟨m, hm⟩ := hx3 C hCS hsplit
      have hkey : x τ - (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * τ * sec s)) = 0 := by
        have h := hm τ hτI.1
        rwa [restrict_eq_one_of_mem_fixingSubgroup K hτK, one_smul, sub_self] at h
      rw [sub_eq_zero] at hkey
      have hcor : (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * τ * sec s)) = 0 := by
        refine Finset.sum_eq_zero (fun s _ => ?_)
        have hCfin : IsFinPlace ℚ C := hSfin C hCS
        have hBfin : IsFinPlace ℚ ((sec s)⁻¹ • C) :=
          (isFinPlace_smul_iff C (sec s)⁻¹).mpr hCfin
        have hconj' : ∃ A ∈ S, IsConjPlace ℚ A ((sec s)⁻¹ • C) :=
          ⟨C, hCS, ⟨(sec s)⁻¹, rfl⟩⟩
        have hI' : IsInertia ℚ ((sec s)⁻¹ • C) ((sec s)⁻¹ * τ * sec s) := by
          have h := (isInertia_conj C (sec s)⁻¹ τ).mpr hτI
          rwa [inv_inv] at h
        have hK' : (sec s)⁻¹ * τ * sec s ∈ K.fixingSubgroup := by
          refine mem_fixingSubgroup_of_restrict_eq_one K ?_
          rw [map_mul, map_mul, map_inv, hsec s,
            restrict_eq_one_of_mem_fixingSubgroup K hτK]
          simp
        rw [hyT _ hBfin hconj' _ hK' hI', smul_zero]
      rw [hkey, hcor]
    · exact eq_zero_of_isCoboundaryOn p K n 1 1 (hx4 C hCS hsplit) τ hτI.1 hτK
  obtain ⟨A₀, hA₀S, hconjA⟩ := hconj
  obtain ⟨g, hg⟩ := hconjA
  have hτK : g⁻¹ * σ * g ∈ K.fixingSubgroup := by
    have h := hnorm.conj_mem σ hσK g⁻¹
    rwa [inv_inv] at h
  have hτI : IsInertia ℚ A₀ (g⁻¹ * σ * g) := by
    refine (isInertia_conj A₀ g (g⁻¹ * σ * g)).mp ?_
    rw [show g * (g⁻¹ * σ * g) * g⁻¹ = σ from by group, hg]
    exact hσI
  have h0 : x (g⁻¹ * σ * g) = 0 := key hA₀S hτK hτI
  have h1 : x (g⁻¹ * σ * g) = (restrict K g)⁻¹ • x σ :=
    cocycle_conj_apply K p n 1 1 hx1 hσK g
  rw [h1] at h0
  have h2 : (restrict K g) • ((restrict K g)⁻¹ • x σ) = 0 := by rw [h0, smul_zero]
  rwa [← mul_smul, mul_inv_cancel, one_smul] at h2

/-- **Clause (i) at the places over `Ram(K/ℚ) ∪ {p}`.**  By Theorem 13 the cocycle `x` is a
coboundary on the decomposition group of every place of `S` that is either non-split in `K`
(clause (4)) or split and over `p` (clause (3) plus the vanishing of the formal corestriction,
which follows from `hy0`); a general place over `Ram(K/ℚ) ∪ {p}` is one of their conjugates. -/
theorem isCoboundaryOn_decomp_of_T1
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hSfin : ∀ A ∈ S, IsFinPlace ℚ A)
    (hSram : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (IsRamifiedIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, IsConjPlace ℚ A B)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec : ∀ s, restrict K (sec s) = s)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hy0 : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∃ A ∈ S, IsConjPlace ℚ A B) →
      (¬ IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp ℚ B → y σ = 0)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hx1 : IsCocycleOn (restrict K) ⊤ x)
    (hx3 : ∀ A ∈ S, IsSplitIn ℚ K A → IsCoboundaryOn (restrict K) (decomp ℚ A)
      (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)))
    (hx4 : ∀ A ∈ S, ¬ IsSplitIn ℚ K A → IsCoboundaryOn (restrict K) (decomp ℚ A) x)
    {A : ValuationSubring SSGRoute.QBar} (hA : IsT1Place p K A) :
    IsCoboundaryOn (restrict K) (decomp ℚ A) x := by
  classical
  haveI hGalQ : IsGalois ℚ SSGRoute.QBar :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  haveI hGal : IsGalois ℚ K := IsGalois.mk
  have hnorm : K.fixingSubgroup.Normal :=
    @IsGalois.fixingSubgroup_normal_of_isGalois ℚ SSGRoute.QBar _ _ _ K hGalQ hGal
  obtain ⟨hAfin, hAcond⟩ := hA
  obtain ⟨A₀, hA₀S, hconjA⟩ := hSram A hAfin (hAcond.elim Or.inr Or.inl)
  obtain ⟨g, hg⟩ := hconjA
  have hcob : IsCoboundaryOn (restrict K) (decomp ℚ A₀) x := by
    by_cases hsplit : IsSplitIn ℚ K A₀
    · have hsplitA : IsSplitIn ℚ K A := by
        have h := (isSplitIn_conj K hnorm A₀ g).mpr hsplit
        rwa [hg] at h
      have hnotram : ¬ IsRamifiedIn ℚ K A :=
        fun hram => hram.choose_spec.2 (hsplitA hram.choose_spec.1.1)
      have hvalA : A.valuation (p : SSGRoute.QBar) < 1 := hAcond.resolve_right hnotram
      have hvalA₀ : A₀.valuation (p : SSGRoute.QBar) < 1 :=
        (valuation_p_lt_one_smul p A₀ g).mp (by rw [hg]; exact hvalA)
      have hcor0 : ∀ δ ∈ decomp ℚ A₀,
          (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)) = 0 := by
        intro δ hδ
        refine Finset.sum_eq_zero (fun s _ => ?_)
        have hBfin : IsFinPlace ℚ ((sec s)⁻¹ • A₀) :=
          (isFinPlace_smul_iff A₀ (sec s)⁻¹).mpr (hSfin A₀ hA₀S)
        have hBconj : ∃ A' ∈ S, IsConjPlace ℚ A' ((sec s)⁻¹ • A₀) :=
          ⟨A₀, hA₀S, ⟨(sec s)⁻¹, rfl⟩⟩
        have hBval : ((sec s)⁻¹ • A₀).valuation (p : SSGRoute.QBar) < 1 :=
          (valuation_p_lt_one_smul p A₀ (sec s)⁻¹).mpr hvalA₀
        have hmemD : (sec s)⁻¹ * δ * sec s ∈ decomp ℚ ((sec s)⁻¹ • A₀) := by
          rw [decomp_conj A₀ (sec s)⁻¹]
          exact Subgroup.mem_map.mpr ⟨δ, hδ, by simp⟩
        have hmemK : (sec s)⁻¹ * δ * sec s ∈ K.fixingSubgroup := by
          refine mem_fixingSubgroup_of_restrict_eq_one K ?_
          rw [map_mul, map_mul, map_inv, hsec s,
            restrict_eq_one_of_mem_fixingSubgroup K (hsplit hδ)]
          simp
        rw [hy0 _ hBfin hBconj (Or.inr hBval) _ hmemK hmemD, smul_zero]
      obtain ⟨m, hm⟩ := hx3 A₀ hA₀S hsplit
      refine isCoboundaryOn_of_eq_zero (restrict K) (decomp ℚ A₀) x (fun δ hδ => ?_)
      have hkey : x δ - (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)) = 0 := by
        have h := hm δ hδ
        rwa [restrict_eq_one_of_mem_fixingSubgroup K (hsplit hδ), one_smul, sub_self] at h
      rw [sub_eq_zero] at hkey
      rw [hkey, hcor0 δ hδ]
    · exact hx4 A₀ hA₀S hsplit
  rw [← hg, decomp_smul (k := ℚ) A₀ g]
  exact isCoboundaryOn_map_conj (restrict K) (decomp ℚ A₀) g x hx1 hcob

/-- **The `(2,1)`-solution is trivial on `G_K` at a place of old ramification**: at such a place
`x` is unramified on `G_K` (Theorem 13, clauses (4)/(6) and the transport of the local data), so
`decomp ℚ A ≤ K.fixingSubgroup` and `oneOne` vanishes there. -/
theorem new_ramification_split
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hSfin : ∀ A ∈ S, IsFinPlace ℚ A)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec : ∀ s, restrict K (sec s) = s)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hyT : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∃ A ∈ S, IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia ℚ B σ → y σ = 0)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hx1 : IsCocycleOn (restrict K) ⊤ x)
    (hx3 : ∀ A ∈ S, IsSplitIn ℚ K A → IsCoboundaryOn (restrict K) (decomp ℚ A)
      (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)))
    (hx4 : ∀ A ∈ S, ¬ IsSplitIn ℚ K A → IsCoboundaryOn (restrict K) (decomp ℚ A) x)
    (hx6 : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ IsConjPlace ℚ A B) → ¬ IsSplitIn ℚ K B →
      ∀ σ : SSGRoute.GalQ, IsInertia ℚ B σ → x σ = 0)
    {A : ValuationSubring SSGRoute.QBar} (hA : IsFinPlace ℚ A)
    (hram : ∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0) :
    ∀ σ ∈ decomp ℚ A, oneOne (p := p) K n σ = 1 := by
  by_cases hconj : ∃ A₀ ∈ S, IsConjPlace ℚ A₀ A
  · obtain ⟨σ, hσI, hσK, hσne⟩ := hram
    exact absurd
      (x_eq_zero_on_inertia_of_conj_S K p n S hSfin sec hsec y hyT x hx1 hx3 hx4 hA hconj hσK hσI)
      hσne
  · intro σ hσ
    rw [oneOne_eq_one_iff]
    have hsplit : IsSplitIn ℚ K A := by
      by_contra hns
      obtain ⟨σ', hσ'I, hσ'K, hσ'ne⟩ := hram
      exact hσ'ne (hx6 A hA (fun A' hA' hc => hconj ⟨A', hA', hc⟩) hns σ' hσ'I)
    exact hsplit hσ

/-- **Clause (7) at the places of new ramification.**  At a place `ℚ`-conjugate to an element of `S`
the cocycle `x` is unramified on `G_K`, so the hypothesis of the clause is false; everywhere else it
is Theorem 13's clause (7). -/
theorem cyclic_new_ramification
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hSfin : ∀ A ∈ S, IsFinPlace ℚ A)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec : ∀ s, restrict K (sec s) = s)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hyT : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∃ A ∈ S, IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia ℚ B σ → y σ = 0)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hx1 : IsCocycleOn (restrict K) ⊤ x)
    (hx3 : ∀ A ∈ S, IsSplitIn ℚ K A → IsCoboundaryOn (restrict K) (decomp ℚ A)
      (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)))
    (hx4 : ∀ A ∈ S, ¬ IsSplitIn ℚ K A → IsCoboundaryOn (restrict K) (decomp ℚ A) x)
    (hx7 : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ IsConjPlace ℚ A B) →
      ∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
        (∀ δ ∈ decomp ℚ B, ∀ u ∈ decomp ℚ B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
        (∃ g ∈ decomp ℚ B, ∀ δ ∈ decomp ℚ B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
        IsCoboundaryOn (restrict K) (decomp ℚ B ⊓ V) x)
    {A : ValuationSubring SSGRoute.QBar} (hA : IsFinPlace ℚ A)
    (hram : ∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0) :
    ∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
      (∀ δ ∈ decomp ℚ A, ∀ u ∈ decomp ℚ A ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
      (∃ g ∈ decomp ℚ A, ∀ δ ∈ decomp ℚ A, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
      IsCoboundaryOn (restrict K) (decomp ℚ A ⊓ V) x := by
  by_cases hconj : ∃ A₀ ∈ S, IsConjPlace ℚ A₀ A
  · obtain ⟨σ, hσI, hσK, hσne⟩ := hram
    exact absurd
      (x_eq_zero_on_inertia_of_conj_S K p n S hSfin sec hsec y hyT x hx1 hx3 hx4 hA hconj hσK hσI)
      hσne
  · exact hx7 A hA (fun A' hA' hc => hconj ⟨A', hA', hc⟩)

/-- **Properness of the twist at stage `(2,1)`.**  The cocycle `x` is surjective on `G_K`: at the
auxiliary completely split places `t v` its value at the Frobenius is `v`. -/
theorem x_surjective_on_GK
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (S : Finset (ValuationSubring SSGRoute.QBar))
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec : ∀ s, restrict K (sec s) = s) (hsec1 : sec 1 = 1)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n 1 1)
    (hx3 : ∀ A ∈ S, IsSplitIn ℚ K A → IsCoboundaryOn (restrict K) (decomp ℚ A)
      (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)))
    (t : E p (K ≃ₐ[ℚ] K) n 1 1 → ValuationSubring SSGRoute.QBar)
    (htfin : ∀ e, IsFinPlace ℚ (t e)) (htsplit : ∀ e, IsSplitIn ℚ K (t e))
    (htinS : ∀ e, t e ∈ S)
    (hvalfrob : ∀ v : E p (K ≃ₐ[ℚ] K) n 1 1,
      y (((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) : SSGRoute.GalQ)) = v)
    (hconjzero : ∀ (v : E p (K ≃ₐ[ℚ] K) n 1 1) (s : K ≃ₐ[ℚ] K), s ≠ 1 →
      y ((sec s)⁻¹ * ((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) : SSGRoute.GalQ)
        * sec s) = 0) :
    ∀ v : E p (K ≃ₐ[ℚ] K) n 1 1, ∃ σ ∈ K.fixingSubgroup, x σ = v := by
  intro v
  refine ⟨((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) : SSGRoute.GalQ),
    htsplit v (localFrobElem ⟨t v, htfin v⟩).2, ?_⟩
  obtain ⟨m, hm⟩ := hx3 (t v) (htinS v) (htsplit v)
  have hmem : ((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) : SSGRoute.GalQ)
      ∈ decomp ℚ (t v) := (localFrobElem ⟨t v, htfin v⟩).2
  have hkey : x ((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) : SSGRoute.GalQ)
      - (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹
          * ((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) : SSGRoute.GalQ) * sec s)) = 0 := by
    have h := hm _ hmem
    change x ((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) : SSGRoute.GalQ)
      - (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹
          * ((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) : SSGRoute.GalQ) * sec s))
      = (restrict K) ((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) : SSGRoute.GalQ) • m - m
      at h
    rw [restrict_eq_one_of_mem_fixingSubgroup K (htsplit v hmem), one_smul, sub_self] at h
    exact h
  rw [sub_eq_zero] at hkey
  rw [hkey]
  rw [Finset.sum_eq_single 1 (fun s _ hs => by rw [hconjzero v s hs, smul_zero])
    (fun h => absurd (Finset.mem_univ 1) h)]
  rw [hsec1, inv_one, one_mul, mul_one, one_smul]
  exact hvalfrob v

end TwoOneClauses

/-- The pointwise action of `Gal(ℚ̄/↥K)` on the places of `ℚ̄` agrees with the action of the
underlying `ℚ`-automorphism. -/
lemma restrictScalars_smul_eq (K : IntermediateField ℚ SSGRoute.QBar)
    (σ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) (A : ValuationSubring SSGRoute.QBar) :
    (AlgEquiv.restrictScalars ℚ σ) • A = σ • A := by
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, by rw [← hyx, AlgEquiv.smul_def, AlgEquiv.smul_def]; rfl⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, by rw [← hyx, AlgEquiv.smul_def, AlgEquiv.smul_def]; rfl⟩

/-- The first step `(1,1) → (2,1)` of the tower, done directly.  It replaces the Step-4 route at
`(i,j) = (1,1)`, where the escape at the `(τ+1)`-field is obstructed.

At every level `n` there is a Scholz solution at stage `(2,1)`, i.e. a proper solution
`G_ℚ ↠ F(n)/F(n)_2 ⋊ Gal(K/ℚ)` satisfying (i) and (ii).

Route (every piece already exists except the two shared arithmetic nodes):
* `T¹` places: one place per prime over `Ram(K/ℚ) ∪ {p}`.
* `T'` places: fresh places split completely in `K`, one for each `𝔽_p`-basis vector `e` of
  `E(n,1,1)`, from `exists_split_place_avoiding`.
* Data `y` on `G_K`: `0` on the local groups of `T¹` and on the non-trivial `K`-conjugates of
  `T'`; an unramified datum with Frobenius value `e` at each `T'` place.  Obtain `y` from
  `grunwald_escape_support_E` with `L := K` (where `hsupp` is trivial).
* Put `x := shafarevich_existence` with `Λ := K`.
* Set `φ := flowTwistE p K n 1 1 x ψ₀`, with `ψ₀ σ = (1, res σ)` the split section.
* (i) holds because `x` is a coboundary on `T¹`.
* (ii) holds because `x` is cyclic at every new place, and those places split in `K`.
* Properness holds because `cor y` has Frobenius value `e` at the `T'` place for `e`.
* `K` is totally imaginary by `no_two_torsion_fixingSubgroup`. -/
theorem scholz_two_one (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (hμ : SSGRoute.HasRootsOfUnity p K 1)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n 2 1,
      SSGRoute.IsScholzSolution p K n 2 1 φ := by
  classical
  haveI hGal : IsGalois ℚ K := IsGalois.mk
  haveI hGalQ : IsGalois ℚ SSGRoute.QBar :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  haveI hAlgCl : IsAlgClosure ℚ SSGRoute.QBar := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hEfin : Finite (E p (K ≃ₐ[ℚ] K) n 1 1) := flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) n 1 1
  haveI hsmulc : SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) (E p (K ≃ₐ[ℚ] K) n 1 1) :=
    Work.CohomologicalShrinking.instSMulCommClassRefinedQuotient p 1 1
  have hnorm : K.fixingSubgroup.Normal :=
    @IsGalois.fixingSubgroup_normal_of_isGalois ℚ SSGRoute.QBar _ _ _ K hGalQ hGal
  obtain ⟨ζ, hζK, hζ⟩ : ∃ ζ : SSGRoute.QBar, ζ ∈ K ∧ IsPrimitiveRoot ζ p := by
    obtain ⟨ζ₂, hζ₂K, hζ₂⟩ := hμ
    have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    refine ⟨ζ₂ ^ p, pow_mem hζ₂K p, ?_⟩
    have hdiv : p ∣ p ^ (1 + 1) := ⟨p, by ring⟩
    have h := hζ₂.pow_of_dvd (p := p) hp hdiv
    have hk : p ^ (1 + 1) / p = p := by
      rw [show p ^ (1 + 1) = p * p from by ring]
      exact Nat.mul_div_right p (Nat.pos_of_ne_zero hp)
    rwa [hk] at h
  have hKimag : p = 2 → ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → c = 1 := by
    intro hp2 c hc2 hcK
    subst hp2
    exact no_two_torsion_fixingSubgroup 2 K 1 le_rfl hμ c hc2 hcK
  obtain ⟨S₀, hS₀fin, hS₀disj, hS₀ram⟩ := ramifiedPlaces_finite (p := p) K
  obtain ⟨t, ht1, htdisj, htavoid, St, hStmem, hStuniv⟩ :=
    exists_split_places_of_module p K n S₀ hS₀fin
  have htfin : ∀ e, IsFinPlace ℚ (t e) := fun e => (ht1 e).1
  have htsplit : ∀ e, IsSplitIn ℚ K (t e) := fun e => (ht1 e).2
  set S : Finset (ValuationSubring SSGRoute.QBar) := S₀ ∪ St with hSdef
  have htinS : ∀ e, t e ∈ S := by
    intro e
    rw [hSdef]
    exact Finset.mem_union_right _ (hStuniv e)
  have hSfin : ∀ A ∈ S, IsFinPlace ℚ A := by
    intro A hA
    rw [hSdef] at hA
    rcases Finset.mem_union.mp hA with h | h
    · exact hS₀fin A h
    · obtain ⟨e, rfl⟩ := hStmem A h
      exact htfin e
  have hSdisj : ∀ A ∈ S, ∀ B ∈ S, IsConjPlace ℚ A B → A = B := by
    intro A hA B hB hconj
    rw [hSdef] at hA hB
    rcases Finset.mem_union.mp hA with hA | hA <;> rcases Finset.mem_union.mp hB with hB | hB
    · exact hS₀disj A hA B hB hconj
    · obtain ⟨e, rfl⟩ := hStmem B hB
      exact absurd hconj (htavoid e A hA)
    · obtain ⟨e, rfl⟩ := hStmem A hA
      exact absurd (isConjPlace_symm hconj) (htavoid e B hB)
    · obtain ⟨e, rfl⟩ := hStmem A hA
      obtain ⟨e', rfl⟩ := hStmem B hB
      by_contra hne
      exact htdisj e e' (fun h => hne (by rw [h])) hconj
  have hvalt : ∀ e, ¬ (t e).valuation (p : SSGRoute.QBar) < 1 := by
    intro e hlt
    obtain ⟨A₀, hA₀S, hconjA⟩ := hS₀ram (t e) (htfin e) (Or.inr hlt)
    exact htavoid e A₀ hA₀S hconjA
  have hSram : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (IsRamifiedIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, IsConjPlace ℚ A B := by
    intro B hB hcond
    obtain ⟨A₀, hA₀S, hconj⟩ := hS₀ram B hB hcond
    exact ⟨A₀, by rw [hSdef]; exact Finset.mem_union_left _ hA₀S, hconj⟩
  obtain ⟨T_K, hTKfin, hTKdisj, hTKcov, hTKcover, htrepr⟩ :=
    exists_TK_transversal p K n S₀ hS₀fin hS₀disj hS₀ram t htfin htsplit htavoid htdisj
  obtain ⟨f, hfadd, hfcloc, hfinertia, hfzero, hfrobval⟩ :=
    exists_datum_of_places p K n T_K hTKfin hTKdisj t htfin htsplit htdisj htrepr
  have hTKcover' : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ↥K B →
      (∃ A₀ ∈ S, IsConjPlace ℚ A₀ B) → ∃ A ∈ T_K, IsConjPlace ↥K A B := by
    intro B hB hBS
    obtain ⟨A₀, hA₀S, hconj₀⟩ := hBS
    rw [hSdef] at hA₀S
    rcases Finset.mem_union.mp hA₀S with h | h
    · exact hTKcover B hB (Or.inl ⟨A₀, h, hconj₀⟩)
    · obtain ⟨e, rfl⟩ := hStmem A₀ h
      exact hTKcover B hB (Or.inr ⟨e, hconj₀⟩)
  have hsupp : ∀ A ∈ T_K, (∀ δ ∈ decomp ↥K A, f A δ = 0) ∨
      ∀ χ : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
        (∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, χ (x * y) = χ x + χ y) →
        (∀ δ ∈ (overK K K le_rfl).fixingSubgroup, χ δ = 0) →
        ∀ δ ∈ decomp ↥K A, χ δ = 0 := by
    intro A hA
    refine Or.inr (fun χ _ hχ δ _ => hχ δ ?_)
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hxK : x ∈ K := hx
    have h1 : algebraMap ↥K SSGRoute.QBar (⟨x, hxK⟩ : ↥K) = x := rfl
    have h2 := AlgEquiv.commutes δ (⟨x, hxK⟩ : ↥K)
    rw [h1] at h2
    exact h2
  obtain ⟨ε, hεadd, hεloc, hεval, hεesc⟩ :=
    grunwald_escape_support_E p K ζ hζ hζK hKimag K le_rfl T_K hTKfin hTKdisj hTKcov
      (E p (K ≃ₐ[ℚ] K) n 1 1) f hfadd hfcloc hsupp
  have hfzeroS : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∃ A₀ ∈ S, IsConjPlace ℚ A₀ B) →
      (¬ IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ T_K, IsConjPlace ↥K A B ∧ ∀ σ ∈ decomp ↥K A, f A σ = 0 := by
    intro B hBfin hBS hBcond
    have hBfinK : IsFinPlace ↥K B := (local_transport_isFinPlace K B).mpr hBfin
    have hcase : (∃ A₀ ∈ S₀, IsConjPlace ℚ A₀ B) ∨ (∃ e, IsConjPlace ℚ (t e) B) := by
      obtain ⟨A₀, hA₀S, hconj₀⟩ := hBS
      rw [hSdef] at hA₀S
      rcases Finset.mem_union.mp hA₀S with h | h
      · exact Or.inl ⟨A₀, h, hconj₀⟩
      · obtain ⟨e, rfl⟩ := hStmem A₀ h
        exact Or.inr ⟨e, hconj₀⟩
    obtain ⟨A, hAT, hconjAB⟩ := hTKcover B hBfinK hcase
    refine ⟨A, hAT, hconjAB, ?_⟩
    refine hfzero A hAT (fun e hconjAe => ?_)
    have h1 : IsConjPlace ℚ A (t e) := isConjPlace_K_Q K hconjAe
    have h2 : IsConjPlace ℚ B (t e) :=
      isConjPlace_trans (isConjPlace_symm (isConjPlace_K_Q K hconjAB)) h1
    rcases hBcond with hns | hval
    · obtain ⟨g, hg⟩ := h2
      exact hns ((isSplitIn_conj K hnorm B g).mp (by rw [hg]; exact htsplit e))
    · obtain ⟨g, hg⟩ := h2
      have hval' : (t e).valuation (p : SSGRoute.QBar) < 1 := by
        have h3 := (valuation_p_lt_one_smul p B g).mpr hval
        rwa [hg] at h3
      exact hvalt e hval'
  obtain ⟨hyadd, hyloc, hyS, hyT, hy0, hyinf⟩ :=
    shafHypotheses_patchFun (p := p) (K := K) (n := n) hKimag S hSfin T_K hTKfin
      hTKcover' f hfinertia hfzeroS ε hεadd hεloc hεval hεesc
  obtain ⟨sec, hsec, hsec1⟩ := exists_section_restrict_one K
  obtain ⟨x, hx1, hx2, hx3, hx4, hx5, hx6, hx7u⟩ :=
    @shafarevich_theorem13_of_z_construction p _ ℚ SSGRoute.QBar _ _ _ _ _
      K K _ hGal _ hGal _ le_rfl ζ hζ hζK
      (E p (K ≃ₐ[ℚ] K) n 1 1)
      (show AddCommGroup (E p (K ≃ₐ[ℚ] K) n 1 1) from inferInstance)
      (show Module (ZMod p) (E p (K ≃ₐ[ℚ] K) n 1 1) from inferInstance)
      (show DistribMulAction (K ≃ₐ[ℚ] K) (E p (K ≃ₐ[ℚ] K) n 1 1) from inferInstance)
      (show SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) (E p (K ≃ₐ[ℚ] K) n 1 1) from inferInstance)
      hEfin S hSfin hSdisj hSram (patchFun K ε) hyadd hyloc hyS hyT hy0 hyinf sec hsec
      (@Work.SSGRoute.N5.zConstructionClean p _ ℚ SSGRoute.QBar _ _ _ _ _
        K K _ hGal _ hGal _ le_rfl ζ hζ hζK
        (E p (K ≃ₐ[ℚ] K) n 1 1)
        (show AddCommGroup (E p (K ≃ₐ[ℚ] K) n 1 1) from inferInstance)
        (show Module (ZMod p) (E p (K ≃ₐ[ℚ] K) n 1 1) from inferInstance)
        (show DistribMulAction (K ≃ₐ[ℚ] K) (E p (K ≃ₐ[ℚ] K) n 1 1) from inferInstance)
        (show SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) (E p (K ≃ₐ[ℚ] K) n 1 1) from inferInstance)
        hEfin S hSfin hSdisj hSram (patchFun K ε) hyadd hyloc hyS hyT hy0 hyinf sec hsec)
  -- Theorem 13's clause (7) comes out of the bridge
  -- `Work.SSGRoute.shafarevich_theorem13_of_z_construction` in the "`∃ U = V ⊓ decompp`" form;
  -- `Work.SSGRoute.cyclic_new_ramification` consumes the equivalent "`∃ V`" form, so the two are
  -- converted here (verbatim the conversion used in `Work.SSGRoute.step4_x_exists_of_inputs`).
  have hx7 : ∀ B : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ IsConjPlace ℚ A B) →
      ∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
        (∀ δ ∈ decomp ℚ B, ∀ u ∈ decomp ℚ B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
        (∃ g ∈ decomp ℚ B, ∀ δ ∈ decomp ℚ B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
        IsCoboundaryOn (restrict K) (decomp ℚ B ⊓ V) x := by
    intro B hB hconj
    obtain ⟨U, ⟨V, hV, hUV⟩, hnorm, hcyc, hcob⟩ := hx7u B hB hconj
    refine ⟨V, hV, ?_, ?_, ?_⟩
    · intro δ hδ u hu
      have hu' : u ∈ U := by rw [hUV, inf_comm]; exact hu
      have hm : δ * u * δ⁻¹ ∈ U := hnorm δ hδ u hu'
      rw [hUV] at hm
      exact hm.1
    · obtain ⟨g, hg, hgm⟩ := hcyc
      refine ⟨g, hg, fun δ hδ => ?_⟩
      obtain ⟨m, hm⟩ := hgm δ hδ
      exact ⟨m, (by rw [hUV] at hm; exact hm.1)⟩
    · rw [inf_comm, ← hUV]
      exact hcob
  have hvalfrob : ∀ v : E p (K ≃ₐ[ℚ] K) n 1 1,
      patchFun K ε (((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) : SSGRoute.GalQ)) = v := by
    intro v
    set σ : SSGRoute.GalQ := ((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) :
      SSGRoute.GalQ) with hσdef
    have hσK : σ ∈ K.fixingSubgroup := htsplit v (localFrobElem ⟨t v, htfin v⟩).2
    rw [patchFun_of_mem K ε σ hσK]
    obtain ⟨A, hAT, hconjA⟩ := htrepr v
    obtain ⟨g₀, hg₀⟩ := hconjA
    have hδeq : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ =
        frobOfSplit K (t v) (htfin v) (htsplit v) := by
      have h1 : (⟨σ, hσK⟩ : ↥(K.fixingSubgroup)) =
          ⟨((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) : SSGRoute.GalQ),
            htsplit v (localFrobElem ⟨t v, htfin v⟩).2⟩ := Subtype.ext rfl
      rw [h1]
      rfl
    rw [hδeq]
    have hg₀mem : g₀⁻¹ * frobOfSplit K (t v) (htfin v) (htsplit v) * g₀ ∈ decomp ↥K A := by
      have h := decomp_conj A g₀
      rw [hg₀] at h
      have hmem : frobOfSplit K (t v) (htfin v) (htsplit v) ∈
          (decomp ↥K A).map (MulAut.conj g₀).toMonoidHom := by
        rw [← h]
        exact frobOfSplit_mem K (t v) (htfin v) (htsplit v)
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
      have hy' : y = g₀⁻¹ * frobOfSplit K (t v) (htfin v) (htsplit v) * g₀ := by
        rw [← hyeq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rwa [hy'] at hy
    calc ε (frobOfSplit K (t v) (htfin v) (htsplit v))
        = ε (g₀ * (g₀⁻¹ * frobOfSplit K (t v) (htfin v) (htsplit v) * g₀) * g₀⁻¹) := by
          rw [show g₀ * (g₀⁻¹ * frobOfSplit K (t v) (htfin v) (htsplit v) * g₀) * g₀⁻¹
              = frobOfSplit K (t v) (htfin v) (htsplit v) from by group]
      _ = ε (g₀⁻¹ * frobOfSplit K (t v) (htfin v) (htsplit v) * g₀) :=
          step4_conj_eq_of_additive_K ε hεadd g₀ _
      _ = f A (g₀⁻¹ * frobOfSplit K (t v) (htfin v) (htsplit v) * g₀) :=
          hεval A hAT _ hg₀mem
      _ = v := hfrobval v A hAT g₀ hg₀
  have hconjzero : ∀ (v : E p (K ≃ₐ[ℚ] K) n 1 1) (s : K ≃ₐ[ℚ] K), s ≠ 1 →
      patchFun K ε ((sec s)⁻¹ * ((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) :
        SSGRoute.GalQ) * sec s) = 0 := by
    intro v s hs
    set σ : SSGRoute.GalQ := ((localFrobElem ⟨t v, htfin v⟩ : ↥(decomp ℚ (t v))) :
      SSGRoute.GalQ) with hσdef
    have hσK : σ ∈ K.fixingSubgroup := htsplit v (localFrobElem ⟨t v, htfin v⟩).2
    have hσ'K : (sec s)⁻¹ * σ * sec s ∈ K.fixingSubgroup := by
      refine mem_fixingSubgroup_of_restrict_eq_one K ?_
      rw [map_mul, map_mul, map_inv, hsec s, restrict_eq_one_of_mem_fixingSubgroup K hσK]
      simp
    rw [patchFun_of_mem K ε ((sec s)⁻¹ * σ * sec s) hσ'K]
    set δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar :=
      (IntermediateField.fixingSubgroupEquiv K) ⟨(sec s)⁻¹ * σ * sec s, hσ'K⟩ with hδdef
    have hδmem : δ ∈ decomp ↥K ((sec s)⁻¹ • t v) := by
      rw [local_transport_decomp K ((sec s)⁻¹ • t v) ((sec s)⁻¹ * σ * sec s) hσ'K]
      rw [decomp_conj (t v) (sec s)⁻¹]
      exact Subgroup.mem_map.mpr ⟨σ, (localFrobElem ⟨t v, htfin v⟩).2, by simp⟩
    have hAex : ∃ A ∈ T_K, IsConjPlace ↥K A ((sec s)⁻¹ • t v) :=
      hTKcover ((sec s)⁻¹ • t v)
        ((local_transport_isFinPlace K _).mpr ((isFinPlace_smul_iff (t v) (sec s)⁻¹).mpr (htfin v)))
        (show (∃ A₀ ∈ S₀, IsConjPlace ℚ A₀ ((sec s)⁻¹ • t v)) ∨
            (∃ e, IsConjPlace ℚ (t e) ((sec s)⁻¹ • t v)) from
          Or.inr ⟨v, ⟨(sec s)⁻¹, rfl⟩⟩)
    obtain ⟨A, hAT, hconjS⟩ := hAex
    have hconjA : IsConjPlace ↥K A ((sec s)⁻¹ • t v) := hconjS
    obtain ⟨u, hu⟩ := hconjS
    have hfA0 : ∀ θ ∈ decomp ↥K A, f A θ = 0 :=
      hfzero A hAT (fun e' hconj' => by
        have h1 : IsConjPlace ℚ A (t e') := isConjPlace_K_Q K hconj'
        have h2 : IsConjPlace ℚ ((sec s)⁻¹ • t v) (t e') :=
          isConjPlace_trans (isConjPlace_symm (isConjPlace_K_Q K hconjA)) h1
        have h3 : IsConjPlace ℚ (t v) (t e') :=
          isConjPlace_trans ⟨(sec s)⁻¹, rfl⟩ h2
        have he' : e' = v := by
          by_contra hne
          exact htdisj e' v hne (isConjPlace_symm h3)
        rw [he'] at hconj'
        have h4 : IsConjPlace ↥K ((sec s)⁻¹ • t v) (t v) :=
          isConjPlace_trans (isConjPlace_symm hconjA) hconj'
        obtain ⟨δ', hδ'eq⟩ := h4
        have hstab : (AlgEquiv.restrictScalars ℚ δ') * (sec s)⁻¹ ∈ decomp ℚ (t v) := by
          rw [MulAction.mem_stabilizer_iff, mul_smul,
            restrictScalars_smul_eq K δ' ((sec s)⁻¹ • t v)]
          exact hδ'eq
        have hmemK : (AlgEquiv.restrictScalars ℚ δ') * (sec s)⁻¹ ∈ K.fixingSubgroup :=
          htsplit v hstab
        have hres1 : restrict K ((AlgEquiv.restrictScalars ℚ δ') * (sec s)⁻¹) = 1 :=
          restrict_eq_one_of_mem_fixingSubgroup K hmemK
        have hδ'1 : restrict K (AlgEquiv.restrictScalars ℚ δ') = 1 :=
          (restrict_eq_one_iff_mem_fixingSubgroup K _).mpr (by
            rw [IntermediateField.mem_fixingSubgroup_iff]
            intro x hx
            simpa using AlgEquiv.commutes δ' (⟨x, hx⟩ : ↥K))
        rw [map_mul, hδ'1, one_mul, map_inv, hsec s] at hres1
        exact hs (inv_eq_one.mp hres1))
    have humem : u⁻¹ * δ * u ∈ decomp ↥K A := by
      have h := decomp_conj A u
      rw [hu] at h
      have hmem : δ ∈ (decomp ↥K A).map (MulAut.conj u).toMonoidHom := by
        rw [← h]
        exact hδmem
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
      have hy' : y = u⁻¹ * δ * u := by
        rw [← hyeq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rwa [hy'] at hy
    calc ε δ = ε (u * (u⁻¹ * δ * u) * u⁻¹) := by
          rw [show u * (u⁻¹ * δ * u) * u⁻¹ = δ from by group]
      _ = ε (u⁻¹ * δ * u) := step4_conj_eq_of_additive_K ε hεadd u _
      _ = f A (u⁻¹ * δ * u) := hεval A hAT _ humem
      _ = 0 := hfA0 _ humem
  have hxsurj := x_surjective_on_GK K p n S sec hsec hsec1 (patchFun K ε) x hx3 t htfin htsplit
    htinS hvalfrob hconjzero
  have hx0T1 : ∀ A : ValuationSubring SSGRoute.QBar, IsT1Place p K A →
      IsCoboundaryOn (restrict K) (decomp ℚ A) x :=
    fun A hA => isCoboundaryOn_decomp_of_T1 K p n S hSfin hSram sec hsec (patchFun K ε)
      hy0 x hx1 hx3 hx4 hA
  have hx0inv : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      IsCoboundaryOn (restrict K) (Subgroup.zpowers c) x := hx5
  have hnew : ∀ A : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ A →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0) →
      ∀ σ ∈ decomp ℚ A, oneOne (p := p) K n σ = 1 :=
    fun A hA hram => new_ramification_split K p n S hSfin sec hsec (patchFun K ε) hyT x hx1
      hx3 hx4 hx6 hA hram
  have hcyc7 : ∀ A : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ A →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0) →
      ∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
        (∀ δ ∈ decomp ℚ A, ∀ u ∈ decomp ℚ A ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
        (∃ g ∈ decomp ℚ A, ∀ δ ∈ decomp ℚ A, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
        IsCoboundaryOn (restrict K) (decomp ℚ A ⊓ V) x :=
    fun A hA hram => cyclic_new_ramification K p n S hSfin sec hsec (patchFun K ε) hyT x hx1
      hx3 hx4 hx7 hA hram
  have hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ :=
    fun σ τ => hx1 σ (Subgroup.mem_top σ) τ (Subgroup.mem_top τ)
  have h1 : (Work.CohomologicalShrinking.tauSucc 1 1).1 = 2 := rfl
  have h2 : (Work.CohomologicalShrinking.tauSucc 1 1).2 = 1 := rfl
  change ∃ φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n
      (Work.CohomologicalShrinking.tauSucc 1 1).1
      (Work.CohomologicalShrinking.tauSucc 1 1).2,
    SSGRoute.IsScholzSolution p K n (Work.CohomologicalShrinking.tauSucc 1 1).1
      (Work.CohomologicalShrinking.tauSucc 1 1).2 φ
  exact ⟨twistSplit (p := p) K n x hxmul,
    isScholzSolution_twistSplit K n x hxmul hx2 hxsurj hx0T1 hx0inv hnew hcyc7⟩



/-
# STATE (N5, `Work.SSGRoute.scholz_two_one`): complete

**The node is finished.**  `lake build Submission.Work.SSGRoute.scholz_two_one` is green and the file
contains no unfinished proof; the target `scholz_two_one` is proved in full, from the two arithmetic
inputs of the route and nothing else.  What is proved in this file:

* `splitSection` / `oneOne` (the split section `σ ↦ (1, res σ)` at `(2,1)` and the `(1,1)`-solution)
  with `splitSection_quot`, `oneOne_quot`, `*_eq_one_iff`, `*_ker`, `restrict_eq_one_iff_mem_fixingSubgroup`;
* `gradeIncl_one_one_surjective`: `E(n,1,1) → F(n)/F(n)^{(2,1)}` is surjective (`F(n)^{(1,1)} = F(n)`);
* `twistSplit` and `isScholzSolution_twistSplit` (**the algebraic core of N5**): for a `1`-cocycle
  `x : G_ℚ → E(n,1,1)` for the `G(K/ℚ)`-action which is locally constant, surjective on `G_K`, a
  coboundary on the decomposition groups of the places over `Ram(K/ℚ) ∪ {p}`, a coboundary on the
  `zpowers` of the involutions, trivial on `D_A` where clause (7) applies and cyclic there otherwise,
  the twist of the split section by `x` is a Scholz solution at `(2,1)` (via
  `isFlowSolution_flowTwistEHom`, `scholzConditions_of_stageData`,
  `isCyclic_map_flowTwistEHom_of_localCyclic`, `inertia_map_eq_flowTwistEHom`);
* `frobOfSplit` / `frobOfSplit_mem`; `exists_localDatum_of_split` (**child (iii)**);
* `exists_datum_of_places` (**piece (0a)**): the datum of N3 on the `↥K`-transversal `T_K`, with its
  prescribed Frobenius value `f A (g₀⁻¹ Frob(t e) g₀) = e`;
* `eps_eq_zero_of_isInertia_conj` / `eps_eq_zero_of_mem_decomp_conj`;
* `shafHypotheses_patchFun` (**child (iv)**): `ShafHypotheses p K n S (patchFun K ε)` from N3's class;
* `exists_TK_transversal` (**child (ii)**) and `exists_split_places_of_module` (**child (i)**, which
  also returns the finite set `St` of the auxiliary places);
* `restrictScalars_smul_eq`, `valuation_p_lt_one_smul`, `isConjPlace_K_Q`, `cocycle_conj_apply`,
  `cocycle_conj_eq_zero_iff` (the transport lemmas of the local clauses);
* `x_eq_zero_on_inertia_of_conj_S`, `isCoboundaryOn_decomp_of_T1`, `new_ramification_split`,
  `cyclic_new_ramification`, `x_surjective_on_GK` (**the clauses (i), (ii) and the properness of the
  twist for the class `x` of Theorem 13**: at the places over `Ram(K/ℚ) ∪ {p}` `x` is a coboundary;
  at the places where `x` ramifies on `G_K` either clause (7) of Theorem 13 applies or the place is
  `ℚ`-conjugate to a place of `S` and `x` is unramified there; and `x(Frob(t v)) = v` at every
  auxiliary place, which is the surjectivity of `x` on `G_K`);
* `scholz_two_one`: the assembly.  The data `S₀` (over `Ram(K/ℚ) ∪ {p}`), the auxiliary completely
  split places `t : E(n,1,1) → places` (child (i)), the transversal `T_K` (child (ii)), the datum `f`
  (piece (0a)), the escape class `ε` of N3, the class `y := patchFun K ε` with its Theorem-13
  hypotheses (child (iv)), the class `x` of Theorem 13 (`shafarevich_existence` with `k := ℚ`,
  `Λ := K`), and then the twist `x ⋊ res`: the five local clauses above feed
  `isScholzSolution_twistSplit`.

**The two inputs that are not proved in this file** are the sibling nodes of the route, exactly as
the design anticipates: `Work.SSGRoute.grunwald_escape_support_E` (N3, the `E`-valued Grünwald
statement with the escape) and `Work.SSGRoute.shafarevich_existence` (Theorem 13, i.e. the Z lane
`Work.SSGRoute.z_data_general_of_ramified`).  Both are imported and used here, and both are still
unfinished elsewhere in the workspace; consequently `#print axioms Work.SSGRoute.scholz_two_one`
reports the unfinished-proof axiom through them, and only through them.  Nothing else in the proof of this node
depends on an unfinished declaration.

A note for future work on this file: the instance arguments of `shafarevich_existence` are delicate
(the workspace has two `AddCommGroup` instances on `E(n,1,1)`), and the five coefficient instances
are therefore passed explicitly, as `(show ... from inferInstance)`; the instance arguments for
`IsGalois` are passed as the local `hGal`.  The `Fintype (E(n,1,1))` instance needed for
`Finset.univ` is *not* put into the context as a local instance, because a local `Fintype (E(n,1,1))`
hypothesis perturbs instance search in this context; `exists_split_places_of_module` returns the
finite set `St` of the auxiliary places instead.
-/
end Work.SSGRoute
