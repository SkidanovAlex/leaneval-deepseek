import Mathlib
import Submission.Work.StemsB.WangSphereHomology
import Submission.Work.StemsB.WangE4Rat
import Submission.Work.StemsB.SphLoopModel
import Submission.Work.Serre.serreE0Range
import Submission.Work.Stems.Engine.DualVanishing
import Submission.Work.Stems.Engine.C2Range
import Submission.Work.StemsB.fibrewiseTrivial_of_contraction

/-!
# The top Wang computation over the sphere, rationally

For a Hurewicz fibration `p : E → Sⁿ` (`n ≥ 2`) whose fibre `F = p ⁻¹' {∞}` has the rational
homology of `S^{n-1}` up to degree `2n` (`H_t(F;ℚ) = 0` for `0 < t ≤ 2n`, `t ≠ n-1`, and
`H_{n-1}(F;ℚ) ≅ ℚ`), the total space satisfies `H_{2n-1}(E;ℚ) ≅ ℚ`.

The proof is the pair sequence of `(E, p ⁻¹' O)`, where `O = sphLoopOuter n` is the contractible
outer disc of the two-disc decomposition of `Work.StemsB.SphModel n`:

`H_{2n-2}(E|_O;ℚ) → H_{2n-1}(E,E|_O;ℚ) → H_{2n-1}(E;ℚ) → H_{2n-1}(E|_O;ℚ) → H_{2n}(E,E|_O;ℚ)`

Both outer terms vanish (the fibrewise triviality over `O` identifies `H^*(E|_O)` with `H^*(F)` and
`H^{2n-1}(F) = H^{2n-2}(F) = 0`), so the middle map is an isomorphism; and the Wang identification
`τ : H^{2n-1}(E,E|_O) ≅ H^{n-1}(F)` of `Work.StemsB.wangSphereE4Rat` computes the source as `ℚ`.
Finally the field universal coefficient theorem turns the resulting cohomology statement
`H^{2n-1}(E;ℚ) ≅ ℚ` into the required homology statement.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Rat

noncomputable section

/-! ## Elementary algebra: a `ℚ`-vector space whose dual is one-dimensional is one-dimensional -/

/-- The canonical linear equivalence `(ℚ →ₗ[ℚ] ℚ) ≃ₗ[ℚ] ℚ`, `f ↦ f 1`. -/
def dualRatIso : (ℚ →ₗ[ℚ] ℚ) ≃ₗ[ℚ] ℚ where
  toFun f := f 1
  invFun q := q • LinearMap.id
  left_inv f := by
    refine LinearMap.ext (fun x => ?_)
    have h : f x = x * f 1 := by
      have := f.map_smul x (1 : ℚ)
      simpa [smul_eq_mul] using this
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    rw [h, mul_comm]
  right_inv q := by
    show (q • LinearMap.id) 1 = q
    simp
  map_add' f g := by simp
  map_smul' q f := by simp

/-- A module whose double dual is nontrivial is nontrivial. -/
theorem nontrivial_of_dual_dual {V : Type} [AddCommGroup V] [Module ℚ V]
    (h : Nontrivial (Module.Dual ℚ (Module.Dual ℚ V))) : Nontrivial V := by
  rw [← not_subsingleton_iff_nontrivial] at h ⊢
  intro hS
  apply h
  have hD1 : Subsingleton (Module.Dual ℚ V) := by
    haveI := hS
    exact ⟨fun f g => LinearMap.ext fun v => by
      rw [Subsingleton.elim v 0, map_zero, map_zero]⟩
  haveI := hD1
  exact ⟨fun f g => LinearMap.ext fun w => by
    rw [Subsingleton.elim w 0, map_zero, map_zero]⟩

/-- If the double dual of `V` is one-dimensional then so is `V`: the evaluation `V → V^{**}` is
injective, so `V` is a submodule of `ℚ`, and a nonzero submodule of a field is everything. -/
theorem nonempty_linearEquiv_rat_of_dualDual {V : Type} [AddCommGroup V] [Module ℚ V]
    (e : Module.Dual ℚ (Module.Dual ℚ V) ≃ₗ[ℚ] ℚ) : Nonempty (V ≃ₗ[ℚ] ℚ) := by
  classical
  haveI hV : Nontrivial V :=
    nontrivial_of_dual_dual (V := V) e.symm.injective.nontrivial
  let φ : V →ₗ[ℚ] ℚ := e.toLinearMap.comp (Module.Dual.eval ℚ V)
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : Module.Dual.eval ℚ V x = Module.Dual.eval ℚ V y := e.injective hxy
    have h2 : Module.Dual.eval ℚ V (x - y) = 0 := by rw [map_sub, h1, sub_self]
    have h3 : x - y = 0 := (Module.eval_apply_eq_zero_iff ℚ (x - y)).mp h2
    exact sub_eq_zero.mp h3
  obtain ⟨v₀, hv₀⟩ : ∃ v : V, φ v ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨v, fun h => hv (hinj (by rw [h, map_zero]))⟩
  refine ⟨LinearEquiv.ofBijective φ ⟨hinj, fun q => ?_⟩⟩
  refine ⟨(q * (φ v₀)⁻¹) • v₀, ?_⟩
  rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hv₀, mul_one]

/-- **If the dual of `V` is one-dimensional then so is `V`.** -/
theorem nonempty_linearEquiv_rat_of_dual {V : Type} [AddCommGroup V] [Module ℚ V]
    (e : Module.Dual ℚ V ≃ₗ[ℚ] ℚ) : Nonempty (V ≃ₗ[ℚ] ℚ) :=
  nonempty_linearEquiv_rat_of_dualDual (V := V) (dualRatIso.symm.trans e.dualMap).symm

/-- `V^* ≅ ℚ` implies `V ≅ ℚ`. -/
theorem nonempty_iso_of_dual_iso {V : Type} [AddCommGroup V] [Module ℚ V]
    (e : ModuleCat.of ℚ (Module.Dual ℚ V) ≅ ModuleCat.of ℚ ℚ) :
    Nonempty (ModuleCat.of ℚ V ≅ ModuleCat.of ℚ ℚ) := by
  have hinj : Function.Injective e.hom.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hsurj : Function.Surjective e.hom.hom := (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨gel⟩ := nonempty_linearEquiv_rat_of_dual
    (LinearEquiv.ofBijective e.hom.hom ⟨hinj, hsurj⟩)
  exact ⟨LinearEquiv.toModuleIso gel⟩

/-- `V ≅ ℚ` implies `V^* ≅ ℚ`. -/
theorem nonempty_dual_iso_of_iso {V : Type} [AddCommGroup V] [Module ℚ V]
    (h : Nonempty (ModuleCat.of ℚ V ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (ModuleCat.of ℚ (Module.Dual ℚ V) ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨e⟩ := h
  have hinj : Function.Injective e.hom.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hsurj : Function.Surjective e.hom.hom := (ModuleCat.epi_iff_surjective _).mp inferInstance
  let gel : V ≃ₗ[ℚ] ℚ := LinearEquiv.ofBijective e.hom.hom ⟨hinj, hsurj⟩
  exact ⟨LinearEquiv.toModuleIso ((LinearEquiv.dualMap gel).symm.trans dualRatIso)⟩

/-! ## Transfer between rational homology and rational cohomology -/

/-- The field universal coefficient theorem: `H_n(X;ℚ) ≅ ℚ` gives `H^n(X;ℚ) ≅ ℚ`. -/
theorem nonempty_ratCoh_iso_of_ratH_iso {X : TopCat} {j : ℕ}
    (h : Nonempty (Work.Serre.ratH X j ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (Work.Serre.ratCoh X j ≅ ModuleCat.of ℚ ℚ) :=
  ⟨(Classical.choice (Work.StemsB.ratDualUCT (Work.Serre.ratChains X) j)).trans
    (nonempty_dual_iso_of_iso h).some⟩

/-- The converse: `H^n(X;ℚ) ≅ ℚ` gives `H_n(X;ℚ) ≅ ℚ`. -/
theorem nonempty_ratH_iso_of_ratCoh_iso {X : TopCat} {j : ℕ}
    (h : Nonempty (Work.Serre.ratCoh X j ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (Work.Serre.ratH X j ≅ ModuleCat.of ℚ ℚ) := by
  have h' : Nonempty
      (ModuleCat.of ℚ (Module.Dual ℚ ↥(Work.Serre.ratH X j)) ≅ ModuleCat.of ℚ ℚ) :=
    ⟨(Classical.choice (Work.StemsB.ratDualUCT (Work.Serre.ratChains X) j)).symm.trans h.some⟩
  exact nonempty_iso_of_dual_iso h'.some

/-- Vanishing of rational homology implies vanishing of rational cohomology. -/
theorem isZero_ratCoh_of_isZero_ratH' {X : TopCat} {j : ℕ}
    (h : IsZero (Work.Serre.ratH X j)) : IsZero (Work.Serre.ratCoh X j) := by
  have hsub : Subsingleton ↥(Work.Serre.ratH X j) := ModuleCat.isZero_iff_subsingleton.mp h
  have hdual : Subsingleton (↥(Work.Serre.ratH X j) →ₗ[ℚ] ℚ) := by
    haveI := hsub
    exact ⟨fun f g => LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  have hZ : IsZero (ModuleCat.of ℚ (↥(Work.Serre.ratH X j) →ₗ[ℚ] ℚ)) :=
    ModuleCat.isZero_iff_subsingleton.mpr hdual
  exact IsZero.of_iso hZ (Classical.choice (Work.StemsB.ratDualUCT (Work.Serre.ratChains X) j))

/-! ## The top Wang computation -/

theorem wangTopRatH {n : ℕ} (hn : 2 ≤ n) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel n)) (hp : Work.StemsB.IsHurewiczFibration p)
    (hfib : ∀ t : ℕ, 0 < t → t ≠ n - 1 → t ≤ 2 * n →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH
        (TopCat.of ↥(p ⁻¹' ({OnePoint.infty} : Set (Work.StemsB.SphModel n)))) t))
    (hgen : Nonempty (Work.Serre.ratH
      (TopCat.of ↥(p ⁻¹' ({OnePoint.infty} : Set (Work.StemsB.SphModel n))))
      (n - 1) ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (Work.Serre.ratH (TopCat.of E) (2 * n - 1) ≅ ModuleCat.of ℚ ℚ) := by
  classical
  -- ### Fibrewise triviality of `p` over the two discs, from `hp`
  have hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter n)
      (Work.StemsB.dOuter n) :=
    Work.StemsB.fibrewiseTrivial_of_contraction p hp (Work.StemsB.sphLoopOuter n)
      (Work.StemsB.dOuter n) (Work.StemsB.sphLoopOuterContr n)
      (fun w => Work.StemsB.sphLoopOuterContr_zero n w)
      (fun w => by
        rw [show Work.StemsB.dOuter n
            = (⟨OnePoint.infty, Or.inl rfl⟩ : ↥(Work.StemsB.sphLoopOuter n)) from Subtype.ext rfl]
        exact Work.StemsB.sphLoopOuterContr_one n w)
      (fun t => by
        rw [show Work.StemsB.dOuter n
            = (⟨OnePoint.infty, Or.inl rfl⟩ : ↥(Work.StemsB.sphLoopOuter n)) from Subtype.ext rfl]
        exact Work.StemsB.sphLoopOuterContr_fixes n t)
  have hshell : Work.StemsB.sphShellPt n ∈ Work.StemsB.sphLoopBig n :=
    (Work.StemsB.serreSphere_sets n (by omega)).2.2.2.2
  obtain ⟨cc, hcc0, hcc1, hccb⟩ := Work.StemsB.serreSphere_contract_big n (by omega) hshell
  have hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig n)
      ⟨Work.StemsB.sphShellPt n, hshell⟩ :=
    Work.StemsB.fibrewiseTrivial_of_contraction p hp (Work.StemsB.sphLoopBig n)
      ⟨Work.StemsB.sphShellPt n, hshell⟩ cc hcc0 hcc1 hccb
  -- ### The corrected `E4` over the sphere: the two identifications `γ` and `τS`
  obtain ⟨γ, τS, -, -, -⟩ :=
    Work.StemsB.wangSphereE4Rat n hn E p hp hT_O ⟨Work.StemsB.sphShellPt n, hshell⟩ hT_G
  -- ### The rational cohomology of the fibre vanishes in the two degrees used
  have keyFsp : ∀ t : ℕ, 0 < t → t ≠ n - 1 → t ≤ 2 * n →
      IsZero (Work.Serre.ratCoh (Work.StemsB.wangCohFsp n p) t) :=
    fun t h1 h2 h3 => isZero_ratCoh_of_isZero_ratH' (hfib t h1 h2 h3)
  -- ### The same for the outer piece, via `γ`
  have keyA : ∀ t : ℕ, 0 < t → t ≠ n - 1 → t ≤ 2 * n →
      IsZero (Work.Serre.ratCoh
        (TopCat.of ↥(p ⁻¹' Work.StemsB.sphLoopOuter n)) t) :=
    fun t h1 h2 h3 => IsZero.of_iso (keyFsp t h1 h2 h3) (γ t)
  -- ### `H^{n-1}(F;ℚ) ≅ ℚ`, transported to the index `(n-2)+1`
  have hgenCoh : Nonempty (Work.Serre.ratCoh (Work.StemsB.wangCohFsp n p) (n - 1) ≅
      ModuleCat.of ℚ ℚ) := nonempty_ratCoh_iso_of_ratH_iso hgen
  have hgenCoh' : Nonempty (Work.Serre.ratCoh (Work.StemsB.wangCohFsp n p) ((n - 2) + 1) ≅
      ModuleCat.of ℚ ℚ) := by
    obtain ⟨e⟩ := hgenCoh
    exact ⟨(eqToIso (congrArg (fun j => Work.Serre.ratCoh (Work.StemsB.wangCohFsp n p) j)
      (by omega : (n - 2) + 1 = n - 1))).trans e⟩
  -- ### The pair sequence of `(E, p ⁻¹' O)` at the top degree
  have hex2 : Function.Exact
      (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter n))
        ((n - 2) + n + 1))
      (HomologicalComplex.homologyMap
        (Work.Cohomology.restr ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter n))
        ((n - 2) + n + 1)) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (Work.Cohomology.pair_exact₂ ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter n)
        ((n - 2) + n + 1))
  have hex1 : Function.Exact
      (Work.Cohomology.pairδ ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter n) ((n - 2) + n))
      (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter n))
        ((n - 2) + n + 1)) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (Work.Cohomology.pair_exact₁ ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter n)
        ((n - 2) + n))
  -- the middle map `H^{2n-1}(E,E|_O) → H^{2n-1}(E)` is an isomorphism
  have hinj : Function.Injective
      (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter n))
        ((n - 2) + n + 1)) := by
    intro x y hxy
    have h0 : (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter n))
        ((n - 2) + n + 1)) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := (hex1 (x - y)).mp h0
    have hz0 : (Work.Cohomology.pairδ ℚ (TopCat.of E)
        (p ⁻¹' Work.StemsB.sphLoopOuter n) ((n - 2) + n)) z = 0 := by
      haveI : Subsingleton ↥((Work.Cohomology.singularCochainComplex ℚ
          (TopCat.of ↥(p ⁻¹' Work.StemsB.sphLoopOuter n))).homology ((n - 2) + n)) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (keyA ((n - 2) + n) (by omega) (by omega) (by omega))
      rw [Subsingleton.elim z 0, map_zero]
    rw [hz0] at hz
    exact sub_eq_zero.mp hz.symm
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter n))
        ((n - 2) + n + 1)) := by
    intro y
    have hy : (HomologicalComplex.homologyMap
        (Work.Cohomology.restr ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter n))
        ((n - 2) + n + 1)) y = 0 := by
      haveI : Subsingleton ↥((Work.Cohomology.singularCochainComplex ℚ
          (TopCat.of ↥(p ⁻¹' Work.StemsB.sphLoopOuter n))).homology ((n - 2) + n + 1)) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (keyA ((n - 2) + n + 1) (by omega) (by omega) (by omega))
      exact Subsingleton.elim _ _
    exact (hex2 y).mp hy
  let eRel := LinearEquiv.toModuleIso (LinearEquiv.ofBijective
    (HomologicalComplex.homologyMap
      (Work.Cohomology.relIncl ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter n))
      ((n - 2) + n + 1)).hom ⟨hinj, hsurj⟩)
  -- ### Assemble: `H^{2n-1}(E;ℚ) ≅ ℚ`
  have hcohK : Nonempty (Work.Serre.ratCoh (TopCat.of E) ((n - 2) + n + 1) ≅
      ModuleCat.of ℚ ℚ) :=
    ⟨eRel.symm ≪≫ τS (n - 2) ≪≫ hgenCoh'.some⟩
  have hcoh : Nonempty (Work.Serre.ratCoh (TopCat.of E) (2 * n - 1) ≅ ModuleCat.of ℚ ℚ) := by
    obtain ⟨e⟩ := hcohK
    exact ⟨(eqToIso (congrArg (fun j => Work.Serre.ratCoh (TopCat.of E) j)
      (by omega : (n - 2) + n + 1 = 2 * n - 1))).symm ≪≫ e⟩
  exact nonempty_ratH_iso_of_ratCoh_iso hcoh

end

end Work.Rat
