import Submission.Work.Kunneth.PointTopValue

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Leray–Hirsch for the trivial bundle over the point

This module assembles `Work.Kunneth.lerayHirschFull_point`: the Leray–Hirsch decomposition of the
projectivisation of the trivial bundle `ε^m` over the point, i.e. of `P(ε^m) = ℂP^{m-1}`, with
coefficients the cohomology of the point.

The two halves of `Work.LerayHirsch.LerayHirschFull` are:

* **even degree `2k`**: the family index `i ≤ k` has only one component in degree `0`
  (`i = k`, `Work.Kunneth.PointSumCollapse`), whose value on `a • 1` is `a • ζ^k`
  (`Work.Kunneth.PointTopValue`); the codomain `H^{2k}(P(ε^{n+1})) = H^{2k}(ℂPⁿ)` is `ℤ·ζ^k`
  (`Work.Kunneth.keyLH`), and `ζ^k` has infinite order because it generates the free module
  `H^{2k}(ℂPⁿ;ℤ) ≅ ℤ` (`Work.Kunneth.PointFunctional`);
* **odd degree `2k+1`**: `H^{2k+1}(ℂPⁿ;ℤ) = 0` (`Work.Projective.cpn_cohomology`), and so is every
  coefficient (positive degree of the point), so both sides are subsingletons;
* **degrees `2k > 2n`**: `H^{2k}(ℂPⁿ;ℤ) = 0` and every coefficient is in positive degree, so again
  both sides are subsingletons;
* **`m = 0`**: `P(ε⁰)` is empty (`Work.Kunneth.isEmpty_projSpace_trivCore_zero`), so its cohomology
  vanishes identically.
-/

open scoped LinearAlgebra.Projectivization

open CategoryTheory

namespace Work.Kunneth

noncomputable section

/-! ## 1. The Leray–Hirsch sum collapses to its top summand -/

/-- **The Leray–Hirsch sum for `P(ε^{n+1})` collapses to its `i = k` summand**: every coefficient
indexed by `i ≠ k` sits in a positive degree of the cohomology of the point, hence vanishes. -/
theorem PointSumCollapse (n k : ℕ) (hk : k ≤ n)
    (xf : (i : {i : Fin (n + 1) // (i : ℕ) ≤ k}) → Work.Thom.Coh ℤ (2 * (k - (i : ℕ))) PUnit) :
    Work.LerayHirsch.lhMap (Work.LerayHirsch.trivCore (n + 1)) k xf
      = Work.LerayHirsch.lhTerm (Work.LerayHirsch.trivCore (n + 1)) k
          (iTop n k hk) (xf (iTop n k hk)) := by
  rw [Work.LerayHirsch.lhMap_apply]
  refine Finset.sum_eq_single (iTop n k hk) ?_ ?_
  · intro i _ hi
    have hlt : (i : ℕ) < k := by
      rcases lt_or_eq_of_le i.2 with h | h
      · exact h
      · exfalso
        apply hi
        refine Subtype.ext (Fin.ext ?_)
        rw [iTop_val]
        exact h
    have hpos : 0 < 2 * (k - (i : ℕ)) := by omega
    haveI : Subsingleton (Work.Thom.Coh ℤ (2 * (k - (i : ℕ))) PUnit) :=
      subsingleton_coh_point_of_pos hpos
    rw [Subsingleton.elim (xf i) 0, Work.LerayHirsch.lhTerm_zero]
  · intro h
    exact absurd (Finset.mem_univ (iTop n k hk)) h

/-- The index of the Leray–Hirsch family is `iTop n k hk` as soon as its value is `k`. -/
theorem eq_iTop_of_val_eq (n k : ℕ) (hk : k ≤ n)
    {i : {i : Fin (n + 1) // (i : ℕ) ≤ k}} (h : (i : ℕ) = k) : i = iTop n k hk := by
  refine Subtype.ext (Fin.ext ?_)
  rw [iTop_val]
  exact h

/-- An index of the Leray–Hirsch family other than the top one has value below `k`. -/
theorem lt_of_ne_iTop {n k : ℕ} (hk : k ≤ n) {i : {i : Fin (n + 1) // (i : ℕ) ≤ k}}
    (hi : i ≠ iTop n k hk) : (i : ℕ) < k := by
  rcases lt_or_eq_of_le i.2 with h | h
  · exact h
  · exact absurd (eq_iTop_of_val_eq n k hk h) hi

/-! ## 2. Trivial bijectivity between subsingletons -/

/-- A map between subsingletons with a chosen source point is bijective. -/
theorem bijective_of_subsingleton {α β : Type*} [Subsingleton α] [Subsingleton β] (f : α → β)
    (a₀ : α) : Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨a₀, Subsingleton.elim (f a₀) b⟩⟩

/-! ## 3. The codomain vanishes in the odd degrees and above `2n` -/

theorem subsingleton_coh_projSpace_trivCore_succ_odd (n k : ℕ) :
    Subsingleton (Work.Thom.Coh ℤ (2 * k + 1)
      (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1)))) :=
  subsingleton_coh_projSpace_trivCore_of_not (by
    rintro ⟨he, -⟩
    obtain ⟨j, hj⟩ := he
    omega)

theorem subsingleton_coh_projSpace_trivCore_succ_high (n k : ℕ) (hk : n < k) :
    Subsingleton (Work.Thom.Coh ℤ (2 * k)
      (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1)))) :=
  subsingleton_coh_projSpace_trivCore_of_not (by
    rintro ⟨-, hle⟩
    omega)

/-! ## 4. The odd part of Leray–Hirsch -/

theorem lerayHirschOdd_trivCore_succ (n k : ℕ) :
    Function.Bijective (Work.LerayHirsch.lhMapOdd (Work.LerayHirsch.trivCore (n + 1)) k) := by
  haveI : ∀ i : {i : Fin (n + 1) // (i : ℕ) ≤ k},
      Subsingleton (Work.Thom.Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) PUnit) :=
    fun i => subsingleton_coh_point_of_pos (by have := i.2; omega)
  haveI hdom : Subsingleton
      ((i : {i : Fin (n + 1) // (i : ℕ) ≤ k}) → Work.Thom.Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) PUnit) :=
    subsingleton_pi
  haveI hcod : Subsingleton (Work.Thom.Coh ℤ (2 * k + 1)
      (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1)))) :=
    subsingleton_coh_projSpace_trivCore_succ_odd n k
  exact bijective_of_subsingleton _ (fun _ => 0)

theorem lerayHirschOdd_trivCore_zero :
    Work.LerayHirsch.LerayHirschOdd (Work.LerayHirsch.trivCore 0) := by
  intro k
  haveI : IsEmpty ({i : Fin 0 // (i : ℕ) ≤ k}) :=
    ⟨fun i => i.1.elim0⟩
  haveI hdom : Subsingleton
      ((i : {i : Fin 0 // (i : ℕ) ≤ k}) → Work.Thom.Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) PUnit) :=
    subsingleton_pi_of_isEmpty
  haveI hcod : Subsingleton (Work.Thom.Coh ℤ (2 * k + 1)
      (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore 0))) :=
    subsingleton_coh_trivCore_zero (2 * k + 1)
  exact bijective_of_subsingleton _ (fun i => isEmptyElim i.1)

/-! ## 5. The even part of Leray–Hirsch in the high degrees and for `m = 0` -/

theorem lerayHirsch_trivCore_succ_high (n k : ℕ) (hk : n < k) :
    Function.Bijective (Work.LerayHirsch.lhMap (Work.LerayHirsch.trivCore (n + 1)) k) := by
  haveI : ∀ i : {i : Fin (n + 1) // (i : ℕ) ≤ k},
      Subsingleton (Work.Thom.Coh ℤ (2 * (k - (i : ℕ))) PUnit) :=
    fun i => subsingleton_coh_point_of_pos (by have := i.1.2; omega)
  haveI hdom : Subsingleton
      ((i : {i : Fin (n + 1) // (i : ℕ) ≤ k}) → Work.Thom.Coh ℤ (2 * (k - (i : ℕ))) PUnit) :=
    subsingleton_pi
  haveI hcod : Subsingleton (Work.Thom.Coh ℤ (2 * k)
      (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1)))) :=
    subsingleton_coh_projSpace_trivCore_succ_high n k hk
  exact bijective_of_subsingleton _ (fun _ => 0)

theorem lerayHirsch_trivCore_zero :
    Work.LerayHirsch.LerayHirsch (Work.LerayHirsch.trivCore 0) := by
  intro k
  haveI : IsEmpty ({i : Fin 0 // (i : ℕ) ≤ k}) :=
    ⟨fun i => i.1.elim0⟩
  haveI hdom : Subsingleton
      ((i : {i : Fin 0 // (i : ℕ) ≤ k}) → Work.Thom.Coh ℤ (2 * (k - (i : ℕ))) PUnit) :=
    subsingleton_pi_of_isEmpty
  haveI hcod : Subsingleton (Work.Thom.Coh ℤ (2 * k)
      (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore 0))) :=
    subsingleton_coh_trivCore_zero (2 * k)
  exact bijective_of_subsingleton _ (fun i => isEmptyElim i.1)

/-! ## 6. A nonvanishing functional on `H^{2k}(ℂPⁿ)` -/

/-- Evaluation at the unique index `0 : Fin 1` of the model module `cpnModel n (2k)` in the even
degrees `2k ≤ 2n`. -/
def cpnEval (n k : ℕ) (h : Even (2 * k) ∧ 2 * k ≤ 2 * n) :
    (↑(Work.Projective.cpnModel n (2 * k)) →ₗ[ℤ] ℤ) :=
  LinearMap.proj (R := ℤ) (ι := Fin (if Even (2 * k) ∧ 2 * k ≤ 2 * n then 1 else 0))
    ⟨0, by rw [if_pos h]; omega⟩

/-- `cpnEval` sends the basis vector at `0` to `1`. -/
theorem cpnEval_single (n k : ℕ) (h : Even (2 * k) ∧ 2 * k ≤ 2 * n) :
    cpnEval n k h (Pi.single (⟨0, by rw [if_pos h]; omega⟩ :
      Fin (if Even (2 * k) ∧ 2 * k ≤ 2 * n then 1 else 0)) (1 : ℤ)) = 1 := by
  rw [cpnEval, LinearMap.proj_apply, Pi.single_eq_same]

/-- **A `ℤ`-linear functional which detects `ζ^k`.**  The cohomology `H^{2k}(ℂPⁿ;ℤ)` of the
projectivisation is identified with `H^{2k}(ℂPⁿ;ℤ) ≅ ℤ` (`Work.Projective.cpn_cohomology`) and a
nonzero functional into `ℤ` cannot vanish on `ζ^k`, because `ζ^k` generates the whole module
(`Work.Kunneth.keyLH`). -/
theorem PointFunctional (n k : ℕ) (hk : k ≤ n) :
    ∃ φ : (↑(Work.Thom.Coh ℤ (2 * k)
        (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1)))) →ₗ[ℤ] ℤ),
      φ (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k) ≠ 0 := by
  have hev : Even (2 * k) ∧ 2 * k ≤ 2 * n := ⟨⟨k, by ring⟩, by omega⟩
  obtain ⟨e⟩ := Work.Projective.cpn_cohomology n (2 * k)
  let e₁ : (↑(Work.Thom.Coh ℤ (2 * k)
        (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1)))) →ₗ[ℤ]
      ↑(Work.Thom.Coh ℤ (2 * k) (Work.Projective.CP n))) :=
    (Work.Thom.CohMap (↑((wkHomeo n).symm) :
        C(Work.Projective.CP n, ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))))) ℤ (2 * k)).hom ∘ₗ
      (Work.Thom.CohMap (↑(Work.LerayHirsch.projUnivHomeo (n + 1)) :
        C(ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))),
          Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1)))) ℤ (2 * k)).hom
  let φ : (↑(Work.Thom.Coh ℤ (2 * k)
        (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1)))) →ₗ[ℤ] ℤ) :=
    (cpnEval n k hev).comp (e.hom.hom.comp e₁)
  refine ⟨φ, ?_⟩
  intro hzero
  have hsurj : Function.Surjective (e.hom.hom.comp e₁) := by
    intro y
    obtain ⟨w, hw⟩ := surjective_of_iso e y
    obtain ⟨v, hv⟩ :=
      (Work.LerayHirsch.bijective_CohMap_of_homeomorph (wkHomeo n).symm (2 * k)).2 w
    obtain ⟨z, hz⟩ :=
      (Work.LerayHirsch.bijective_CohMap_of_homeomorph
        (Work.LerayHirsch.projUnivHomeo (n + 1)) (2 * k)).2 v
    refine ⟨z, ?_⟩
    simp only [LinearMap.comp_apply, e₁, hz, hv, hw]
  have hφ : φ = 0 := by
    have hmap : Submodule.map φ (⊤ : Submodule ℤ ↑(Work.Thom.Coh ℤ (2 * k)
        (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1))))) = ⊥ := by
      rw [← keyLH n k hk, Submodule.map_span, Set.image_singleton, hzero,
        Submodule.span_zero_singleton]
    refine LinearMap.ext fun z => ?_
    have hz : φ z ∈ Submodule.map φ (⊤ : Submodule ℤ ↑(Work.Thom.Coh ℤ (2 * k)
        (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1))))) :=
      ⟨z, trivial, rfl⟩
    rw [hmap] at hz
    simpa using hz
  have hφ₀ : cpnEval n k hev = 0 := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨z, hz⟩ := hsurj y
    have h := congrArg (fun g : (↑(Work.Thom.Coh ℤ (2 * k)
        (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1)))) →ₗ[ℤ] ℤ) => g z) hφ
    simp only [φ, LinearMap.comp_apply] at h
    rw [← hz]
    simpa using h
  have h1 := congrArg (fun g : (↑(Work.Projective.cpnModel n (2 * k)) →ₗ[ℤ] ℤ) =>
      g (Pi.single (⟨0, by rw [if_pos hev]; omega⟩ :
        Fin (if Even (2 * k) ∧ 2 * k ≤ 2 * n then 1 else 0)) (1 : ℤ))) hφ₀
  simp only [cpnEval_single n k hev, LinearMap.zero_apply] at h1
  exact one_ne_zero h1

/-! ## 7. The even part of Leray–Hirsch in the degrees `2k ≤ 2n` -/

/-- **`ζ^k` has infinite order**: if `a • ζ^k = 0` then `a = 0`.  Indeed `ζ^k` generates
`H^{2k}(P(ε^{n+1});ℤ)` (`Work.Kunneth.keyLH`), so any `φ` which does not vanish on `ζ^k`
(`Work.Kunneth.PointFunctional`) has kernel `≠ ⊤`, hence `φ (a • ζ^k) = a * φ (ζ^k) = 0` forces
`a = 0`. -/
theorem smul_zetaPow_eq_zero (n k : ℕ) (hk : k ≤ n) (a : ℤ)
    (h : a • Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k = 0) : a = 0 := by
  obtain ⟨φ, hφ⟩ := PointFunctional n k hk
  have h1 : a • φ (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k) = 0 := by
    rw [← map_zsmul, h, map_zero]
  have h2 : a * φ (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k) = 0 := by
    simpa using h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd h3 hφ

/-- **`a • ζ^k = b • ζ^k` only if `a = b`**: `ζ^k` has infinite order
(`Work.Kunneth.smul_zetaPow_eq_zero`). -/
theorem smul_zetaPow_injective (n k : ℕ) (hk : k ≤ n) (a b : ℤ)
    (h : a • Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k
      = b • Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k) : a = b := by
  obtain ⟨φ, hφ⟩ := PointFunctional n k hk
  have h1 : a • φ (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k)
      = b • φ (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k) := by
    rw [← map_zsmul, ← map_zsmul, h]
  have h2 : a * φ (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k)
      = b * φ (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k) := by
    simpa using h1
  exact mul_right_cancel₀ hφ h2

/-- **The even part of Leray–Hirsch for `P(ε^{n+1})` in the degrees `2k ≤ 2n`**: the Leray–Hirsch
map is the map `a ↦ a • ζ^k` on the single non-vanishing coefficient. -/
theorem lerayHirsch_trivCore_succ_le (n k : ℕ) (hk : k ≤ n) :
    Function.Bijective (Work.LerayHirsch.lhMap (Work.LerayHirsch.trivCore (n + 1)) k) := by
  have hcollapse := PointSumCollapse n k hk
  constructor
  · intro xf xg hfg
    rw [hcollapse xf, hcollapse xg] at hfg
    obtain ⟨a, ha⟩ := exists_smul_oneHtop n k hk (xf (iTop n k hk))
    obtain ⟨b, hb⟩ := exists_smul_oneHtop n k hk (xg (iTop n k hk))
    rw [ha, hb, PointTopValue n k hk a, PointTopValue n k hk b] at hfg
    have hab : a = b := smul_zetaPow_injective n k hk a b hfg
    funext i
    by_cases hi : i = iTop n k hk
    · subst hi
      rw [ha, hb, hab]
    · have hpos : 0 < 2 * (k - (i : ℕ)) := by have := lt_of_ne_iTop hk hi; omega
      haveI : Subsingleton (Work.Thom.Coh ℤ (2 * (k - (i : ℕ))) PUnit) :=
        subsingleton_coh_point_of_pos hpos
      rw [Subsingleton.elim (xf i) 0, Subsingleton.elim (xg i) 0]
  · intro y
    obtain ⟨a, ha⟩ :=
      (Work.Gen.ChernGen.span_singleton_eq_top_iff'
        (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) k)).mp
        (keyLH n k hk) y
    refine ⟨Work.LerayHirsch.lhSoloFamily (iTop n k hk) (a • oneHtop n k hk), ?_⟩
    rw [Work.LerayHirsch.lhMap_eq_single, PointTopValue]
    exact ha.symm

end

end Work.Kunneth
