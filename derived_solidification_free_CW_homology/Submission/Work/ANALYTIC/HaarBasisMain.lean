import Mathlib
import Submission.Work.ANALYTIC.HaarBasisDefs
import Submission.Work.ANALYTIC.haar_biorth
import Submission.Work.ANALYTIC.haar_expand

/-!
# The Haar/Schauder basis of `LC T = C(T,ℤ)`: the main theorem

For an infinite light profinite set `T`, the module `LC T = LocallyConstant ↥T ℤ` is free with
basis `{fJ T j | j : JIdx}` (the cylinders `fCyl T j` together with the constant function `1`),
and the dual coordinates are the functionals `phiJ T j`.

The proof combines the two ingredients proved in the sibling files:

* `Work.ANALYTIC.haar_biorth` — the biorthogonality `phiJ T i (fJ T j) = δᵢⱼ`;
* `Work.ANALYTIC.haar_expand` — the level-`N` expansion
  `g = g s₀ • 1 + ∑_{lvl j ≤ N} (phi T j g) • fCyl T j` for `g` invariant under `e_N`.

The first says that the linear map `phiLin` with coordinates `phiJ` inverts the linear map `psi`
sending `single j 1` to `fJ T j` on the free module; the second supplies the other composition:
every `g : LC T` factors through some `e_N` (`exists_factor_level`, from
`Profinite.exists_locallyConstant`), so the finite expansion exhibits `g` as `psi` of an element
of `JIdx →₀ ℤ`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Work.ANALYTIC
namespace Haar

variable (T : LightProfinite.{0}) [Infinite T]

/-! ## Factorisation of a locally constant function through a level -/

theorem exists_factor_level (g : LC T) : ∃ N : ℕ, ∀ x, g x = g (Work.ATOM.e T N x) := by
  obtain ⟨j, g', hg'⟩ := Profinite.exists_locallyConstant.{_, 0}
    (lightToProfinite.mapCone T.asLimitCone) (isLimitOfPreserves lightToProfinite T.asLimit) g
  refine ⟨j.unop, fun x => ?_⟩
  let f := ((lightToProfinite.mapCone T.asLimitCone).π.app j).hom.hom
  have key : ∀ y : ↥T, g y = g' (f y) := by
    intro y
    have h := congrFun (congrArg (fun u : LC T => (⇑u : ↥T → ℤ)) hg') y
    exact h
  have hfproj : ∀ y : ↥T, f y = T.proj j.unop y := fun y => rfl
  have hfx : f (Work.ATOM.e T j.unop x) = f x := by
    rw [hfproj, hfproj, proj_e_self]
  calc g x = g' (f x) := key x
    _ = g' (f (Work.ATOM.e T j.unop x)) := by rw [hfx]
    _ = g (Work.ATOM.e T j.unop x) := (key _).symm

/-! ## The expansion, as an identity of locally constant functions -/

theorem expand_level (N : ℕ) (g : LC T) (hg : ∀ x, g x = g (Work.ATOM.e T N x)) :
    g = (g ((Work.ATOM.levelData T).s₀)) • (1 : LC T)
      + ∑ j ∈ lvlFinset T N, (phi T j g) • fCyl T j := by
  refine LocallyConstant.ext (fun x => ?_)
  have h1 : ((g ((Work.ATOM.levelData T).s₀)) • (1 : LC T)) x = g ((Work.ATOM.levelData T).s₀) := by
    rw [LocallyConstant.smul_apply, LocallyConstant.one_apply, smul_eq_mul, mul_one]
  have h2 : (∑ j ∈ lvlFinset T N, (phi T j g) • fCyl T j) x
      = ∑ j ∈ lvlFinset T N, (phi T j g) * fCyl T j x := by
    rw [← LocallyConstant.evalₐ_apply (R := ℤ) (x := x), map_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [LocallyConstant.evalₐ_apply, LocallyConstant.smul_apply, smul_eq_mul]
  rw [LocallyConstant.add_apply, h1, h2]
  exact haar_expand T N g hg x

/-! ## The coordinates outside a level vanish -/

theorem phi_eq_zero_of_lt_lvl (N : ℕ) (g : LC T) (hg : ∀ x, g x = g (Work.ATOM.e T N x))
    (j : ℕ) (hj : N < Work.ATOM.lvl T j) : phi T j g = 0 := by
  have hpar : par T j = Work.ATOM.e T (Work.ATOM.lvl T j - 1) ((Work.ATOM.levelData T).a j) := by
    rw [par]
    exact dif_neg (by omega)
  have hkey : Work.ATOM.e T N (par T j) = Work.ATOM.e T N ((Work.ATOM.levelData T).a j) := by
    rw [hpar, e_comp_apply, min_eq_right (Nat.le_sub_one_of_lt hj)]
  rw [phi, hg ((Work.ATOM.levelData T).a j), hg (par T j), hkey, sub_self]

/-- The level chosen by `exists_factor_level`. -/
noncomputable def levelOf (g : LC T) : ℕ := Classical.choose (exists_factor_level T g)

theorem levelOf_spec (g : LC T) : ∀ x, g x = g (Work.ATOM.e T (levelOf T g) x) :=
  Classical.choose_spec (exists_factor_level T g)

/-! ## The finite set of relevant indices -/

/-- The index set of the level-`N` expansion, as a finset of `JIdx`: the `j` of level `≤ N`
together with the index `∞` of the constant function. -/
def sIdx (N : ℕ) : Finset JIdx :=
  insert inf ((lvlFinset T N).map ⟨OnePoint.some, OnePoint.coe_injective⟩)

theorem mem_sIdx {N : ℕ} {i : JIdx} :
    i ∈ sIdx T N ↔ i = inf ∨ ∃ j ∈ lvlFinset T N, OnePoint.some j = i := by
  rw [sIdx, Finset.mem_insert, Finset.mem_map]
  exact Iff.rfl

theorem inf_notMem_sIdx (N : ℕ) :
    inf ∉ (lvlFinset T N).map ⟨OnePoint.some, OnePoint.coe_injective⟩ := by
  rw [Finset.mem_map]
  rintro ⟨j, _, hj⟩
  exact OnePoint.coe_ne_infty j hj

theorem support_subset_sIdx (N : ℕ) (g : LC T) (hg : ∀ x, g x = g (Work.ATOM.e T N x)) :
    Function.support (fun i : JIdx => phiJ T i g) ⊆ (sIdx T N : Set JIdx) := by
  intro i hi
  rw [Finset.mem_coe, mem_sIdx]
  induction i using OnePoint.rec with
  | infty => exact Or.inl rfl
  | coe j =>
      refine Or.inr ⟨j, ?_, rfl⟩
      by_contra hcon
      rw [mem_lvlFinset] at hcon
      exact hi (phi_eq_zero_of_lt_lvl T N g hg j (not_le.mp hcon))

/-! ## The two linear maps -/

/-- The linear map `(JIdx →₀ ℤ) ⟶ LC T` sending the basis vector `j` to `fJ T j`. -/
def psi : (JIdx →₀ ℤ) →ₗ[ℤ] LC T :=
  Finsupp.lsum ℤ fun j => LinearMap.toSpanSingleton ℤ (LC T) (fJ T j)

theorem psi_apply (c : JIdx →₀ ℤ) : psi T c = c.sum fun j k => k • fJ T j := by
  rw [psi, Finsupp.lsum_apply]
  exact Finsupp.sum_congr fun j _ => LinearMap.toSpanSingleton_apply ℤ (LC T) (fJ T j) (c j)

theorem psi_single (j : JIdx) (c : ℤ) : psi T (Finsupp.single j c) = c • fJ T j := by
  rw [psi, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- The linear map `LC T ⟶ (JIdx →₀ ℤ)` whose coordinates are the `phiJ`. -/
def phiLin : LC T →ₗ[ℤ] (JIdx →₀ ℤ) where
  toFun g := Finsupp.ofSupportFinite (fun i => phiJ T i g)
    ((Finset.finite_toSet (sIdx T (levelOf T g))).subset
      (support_subset_sIdx T (levelOf T g) g (levelOf_spec T g)))
  map_add' g g' := by
    refine Finsupp.ext (fun i => ?_)
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.add_apply, phiJ_add]
  map_smul' c g := by
    refine Finsupp.ext (fun i => ?_)
    simp only [RingHom.id_apply, Finsupp.ofSupportFinite_coe, Finsupp.smul_apply, phiJ_smul]
    rw [smul_eq_mul]

theorem phiLin_apply (g : LC T) (i : JIdx) : phiLin T g i = phiJ T i g := by
  simp [phiLin, Finsupp.ofSupportFinite_coe]

theorem support_phiLin_subset (g : LC T) : (phiLin T g).support ⊆ sIdx T (levelOf T g) := by
  intro i hi
  rw [Finsupp.mem_support_iff, phiLin_apply] at hi
  exact support_subset_sIdx T (levelOf T g) g (levelOf_spec T g) hi

/-! ## The two compositions -/

theorem phiLin_fJ (j : JIdx) : phiLin T (fJ T j) = Finsupp.single j 1 := by
  refine Finsupp.ext (fun i => ?_)
  rw [phiLin_apply]
  by_cases h : i = j
  · rw [h, Finsupp.single_eq_same, (haar_biorth T j j).1 rfl]
  · rw [Finsupp.single_eq_of_ne h, (haar_biorth T i j).2 h]

theorem phiLin_psi (c : JIdx →₀ ℤ) : phiLin T (psi T c) = c := by
  refine Finsupp.induction c ?_ ?_
  · simp [psi]
  · intro a b f ha hb ih
    rw [map_add, map_add, ih, psi_single, LinearMap.map_smul, phiLin_fJ, Finsupp.smul_single]
    simp

theorem sum_sIdx {M : Type*} [AddCommMonoid M] (N : ℕ) (F : JIdx → M) :
    ∑ i ∈ sIdx T N, F i = F inf + ∑ j ∈ lvlFinset T N, F (j : JIdx) := by
  rw [sIdx, Finset.sum_insert (inf_notMem_sIdx T N),
    Finset.sum_map (lvlFinset T N) ⟨OnePoint.some, OnePoint.coe_injective⟩ F]
  exact congrArg (fun z => F inf + z) (Finset.sum_congr rfl (fun x _ => rfl))

theorem psi_phiLin (g : LC T) : psi T (phiLin T g) = g := by
  rw [psi_apply]
  rw [Finsupp.sum_of_support_subset (phiLin T g) (support_phiLin_subset T g)
    (fun i k => k • fJ T i) (fun i _ => by simp)]
  rw [sum_sIdx]
  simp only [phiLin_apply, fJ_inf, phiJ_inf, phiJ_coe, fJ_coe]
  rw [← expand_level T (levelOf T g) g (levelOf_spec T g)]

/-! ## The linear equivalence and the basis isomorphism -/

/-- **The Haar-Schauder basis**: `LC T` is free of countable rank, with basis `{fJ T j}`. -/
def haarLinearEquiv : LC T ≃ₗ[ℤ] (JIdx →₀ ℤ) :=
  LinearEquiv.ofLinearMap (phiLin T) (psi T)
    (LinearMap.ext fun c => phiLin_psi T c)
    (LinearMap.ext fun g => psi_phiLin T g)

theorem haar_basisIso :
    ∃ e : CategoryTheory.Iso (ModuleCat.of ℤ (LC T)) (ModuleCat.of ℤ (JIdx →₀ ℤ)),
      (∀ (lam : LC T) (j : JIdx), e.hom.hom lam j = phiJ T j lam) ∧
      (∀ j : JIdx, e.inv.hom (Finsupp.single j 1) = fJ T j) := by
  refine ⟨(haarLinearEquiv T).toModuleIso, ?_, ?_⟩
  · intro lam j
    rw [LinearEquiv.toModuleIso_hom]
    exact phiLin_apply T lam j
  · intro j
    rw [LinearEquiv.toModuleIso_inv]
    change psi T (Finsupp.single j 1) = fJ T j
    simpa using psi_single T j 1

end Haar
end Work.ANALYTIC
