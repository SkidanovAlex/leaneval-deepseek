import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.star_char

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.classFun_eq_zero_of_orthogonal`

A class function on a finite group which is orthogonal (for the normalised character inner
product `cfInner`) to every irreducible complex character is zero.

The proof is the classical one.  Let `z = ∑_g f(g⁻¹) g ∈ ℂ[G]`; since `f` is a class
function, `z` is central.  For every simple submodule `N` of the regular module `ℂ[G]`
the operator `T_N = ∑_g f(g⁻¹) ρ_N(g)` on `N` is `ℂ[G]`-linear, hence scalar (its
eigenspace is a non-zero submodule of the simple module `N`); its trace is
`∑_g f(g⁻¹) χ_N(g) = |G| ⟨f, χ_N⟩ = 0`, so the scalar is `0` and `T_N = 0`.  Since the
chosen simple submodules span `ℂ[G]`, the element `z` acts as `0` on the whole regular
module, so `z = 0` and hence `f = 0`.
-/

noncomputable section

open Classical Finset

namespace Work.CharCore

section ClassSumAPI

variable {G : Type*} [Group G] [Fintype G]

/-! ## Conjugates of character values

The fact `star_char` (the complex conjugate of `χ g` is `χ g⁻¹`) is proved in the
companion file `Submission.Work.CharCore.star_char`; we use it below. -/

/-! ## The class sum `∑_g f(g⁻¹) g` in the group algebra -/

/-- The element `∑_g f(g⁻¹) g` of the complex group algebra of `G`.  For a class
function `f` it is central. -/
noncomputable def classSum (f : G → ℂ) : MonoidAlgebra ℂ G :=
  ∑ g : G, f (g⁻¹) • MonoidAlgebra.single g (1 : ℂ)

/-- The coefficient of `g` in `classSum f` is `f (g⁻¹)`. -/
theorem classSum_coeff (f : G → ℂ) (g : G) : (classSum f).coeff g = f (g⁻¹) := by
  simp only [classSum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single g]
  · rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    simp
  · intro b _ hb
    rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne (Ne.symm hb)]
    simp
  · intro h; exact absurd (Finset.mem_univ g) h

/-- Multiplication of `classSum f` on the right by a basis element. -/
theorem classSum_mul_single (f : G → ℂ) (h : G) :
    classSum f * MonoidAlgebra.single h (1 : ℂ)
      = ∑ g : G, f (g⁻¹) • MonoidAlgebra.single (g * h) (1 : ℂ) := by
  rw [classSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [smul_mul_assoc, MonoidAlgebra.single_mul_single]
  simp

/-- Multiplication of a basis element on the left by `classSum f`. -/
theorem single_mul_classSum (f : G → ℂ) (h : G) :
    MonoidAlgebra.single h (1 : ℂ) * classSum f
      = ∑ g : G, f (g⁻¹) • MonoidAlgebra.single (h * g) (1 : ℂ) := by
  rw [classSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_smul_comm, MonoidAlgebra.single_mul_single]
  simp

/-- `f (h * y) = f (y * h)` for a class function. -/
theorem IsClassFun.mul_comm' {f : G → ℂ} (hf : IsClassFun f) (h y : G) :
    f (h * y) = f (y * h) := by
  have := hf (y * h) h
  simpa [mul_assoc] using this

/-- `classSum f` commutes with every basis element when `f` is a class function. -/
theorem classSum_commute_single {f : G → ℂ} (hf : IsClassFun f) (h : G) :
    classSum f * MonoidAlgebra.single h (1 : ℂ)
      = MonoidAlgebra.single h (1 : ℂ) * classSum f := by
  rw [classSum_mul_single, single_mul_classSum]
  have e1 : (∑ g : G, f (g⁻¹) • MonoidAlgebra.single (g * h) (1 : ℂ))
      = ∑ g : G, f (h * g⁻¹) • MonoidAlgebra.single g (1 : ℂ) := by
    rw [← Equiv.sum_comp (Equiv.mulRight h⁻¹)
      (fun g : G => f (g⁻¹) • MonoidAlgebra.single (g * h) (1 : ℂ))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have e2 : (∑ g : G, f (g⁻¹) • MonoidAlgebra.single (h * g) (1 : ℂ))
      = ∑ g : G, f (g⁻¹ * h) • MonoidAlgebra.single g (1 : ℂ) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft h⁻¹)
      (fun g : G => f (g⁻¹) • MonoidAlgebra.single (h * g) (1 : ℂ))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [e1, e2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf.mul_comm' h]

/-- `classSum f` is central when `f` is a class function. -/
theorem classSum_central {f : G → ℂ} (hf : IsClassFun f) (a : MonoidAlgebra ℂ G) :
    classSum f * a = a * classSum f := by
  induction a using MonoidAlgebra.induction_on with
  | of m => simpa using classSum_commute_single hf m
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]
  | smul r x hx =>
      calc classSum f * (r • x)
          = classSum f * (algebraMap ℂ (MonoidAlgebra ℂ G) r * x) := by
            rw [Algebra.smul_def]
        _ = (classSum f * algebraMap ℂ (MonoidAlgebra ℂ G) r) * x := by rw [mul_assoc]
        _ = (algebraMap ℂ (MonoidAlgebra ℂ G) r * classSum f) * x := by
            rw [← Algebra.commutes r (classSum f)]
        _ = algebraMap ℂ (MonoidAlgebra ℂ G) r * (classSum f * x) := by rw [mul_assoc]
        _ = algebraMap ℂ (MonoidAlgebra ℂ G) r * (x * classSum f) := by rw [hx]
        _ = (algebraMap ℂ (MonoidAlgebra ℂ G) r * x) * classSum f := by rw [← mul_assoc]
        _ = (r • x) * classSum f := by rw [Algebra.smul_def]

end ClassSumAPI

/-! ## The main theorem -/

theorem classFun_eq_zero_of_orthogonal {G : Type*} [Group G] [Fintype G] {f : G → ℂ}
    (hf : IsClassFun f) (h : ∀ χ ∈ Irr G, cfInner f χ = 0) : f = 0 := by
  have hcent : ∀ a : MonoidAlgebra ℂ G, classSum f * a = a * classSum f :=
    classSum_central hf
  -- The class sum annihilates every simple submodule of the regular module.
  have hkill : ∀ N ∈ irrSubmodules G, ∀ x : N, classSum f • x = 0 := by
    intro N hN x
    haveI hsimp : IsSimpleModule (groupAlgebra G) N := isSimpleModule_of_mem_irrSubmodules N hN
    haveI hnt : Nontrivial N := IsSimpleModule.nontrivial (groupAlgebra G) N
    set T : N →ₗ[ℂ] N := ∑ g : G, f (g⁻¹) • (submoduleRep N) g with hTdef
    have hTapply : ∀ y : N, T y = classSum f • y := by
      intro y
      rw [hTdef, classSum, Finset.sum_smul, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [LinearMap.smul_apply, smul_assoc]
      congr 1
    have hTsmul : ∀ (a : MonoidAlgebra ℂ G) (y : N), T (a • y) = a • T y := by
      intro a y
      rw [hTapply, hTapply, ← mul_smul, hcent a, mul_smul]
    -- trace of `T`
    have htrace : LinearMap.trace ℂ N T
        = ∑ g : G, f (g⁻¹) * (submoduleRep N).character g := by
      rw [hTdef, map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_smul, smul_eq_mul]
      rfl
    -- the trace is zero, via the hypothesis
    have hsum0 : (∑ g : G, f (g⁻¹) * (submoduleRep N).character g) = 0 := by
      have hchi : (submoduleRep N).character ∈ Irr G := by
        rw [Irr]; exact Finset.mem_image.mpr ⟨N, hN, rfl⟩
      have hcard : (Fintype.card G : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have key : (Fintype.card G : ℂ) * cfInner f ((submoduleRep N).character)
          = ∑ g : G, f (g⁻¹) * (submoduleRep N).character g := by
        rw [cfInner_apply]
        rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
        have hstar : ∀ x : G, starRingEnd ℂ ((submoduleRep N).character x)
            = (submoduleRep N).character x⁻¹ := fun x => star_char (submoduleRep N) x
        calc ∑ x : G, f x * starRingEnd ℂ ((submoduleRep N).character x)
            = ∑ x : G, f x * (submoduleRep N).character x⁻¹ :=
              Finset.sum_congr rfl fun x _ => by rw [hstar x]
          _ = ∑ x : G, f x⁻¹ * (submoduleRep N).character x := by
              simpa using (Equiv.sum_comp (Equiv.inv G)
                (fun x : G => f x⁻¹ * (submoduleRep N).character x))
      rw [← key, h _ hchi, mul_zero]
    have htrace0 : LinearMap.trace ℂ N T = 0 := by rw [htrace, hsum0]
    -- an eigenvalue
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff] at hv
    obtain ⟨hv_mem, hv_ne⟩ := hv
    rw [Module.End.mem_eigenspace_iff] at hv_mem
    -- `T` is scalar
    have hM_ne : Submodule.span (MonoidAlgebra ℂ G) ({v} : Set N) ≠ ⊥ := by
      intro hbot
      have hvbot : v ∈ (⊥ : Submodule (MonoidAlgebra ℂ G) N) := by
        rw [← hbot]; exact Submodule.subset_span (Set.mem_singleton v)
      exact hv_ne (by simpa using hvbot)
    have hM_top : Submodule.span (MonoidAlgebra ℂ G) ({v} : Set N) = ⊤ :=
      (eq_bot_or_eq_top _).resolve_left hM_ne
    have hscalar : ∀ y : N, T y = c • y := by
      intro y
      have hy : y ∈ Submodule.span (MonoidAlgebra ℂ G) ({v} : Set N) := by
        rw [hM_top]; exact Submodule.mem_top
      exact Submodule.span_induction (s := ({v} : Set N))
        (p := fun y _ => T y = c • y)
        (fun z hz => by
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact hv_mem)
        (by rw [map_zero, smul_zero])
        (fun z w _ _ hz hw => by rw [map_add, hz, hw, smul_add])
        (fun a z _ hz => by
          rw [hTsmul, hz]
          exact (smul_comm c a z).symm)
        hy
    have hT_eq : T = c • LinearMap.id := by
      apply LinearMap.ext
      intro y
      rw [LinearMap.smul_apply, LinearMap.id_apply]
      exact hscalar y
    have htrace_scalar : LinearMap.trace ℂ N T = c * (Module.finrank ℂ N : ℂ) := by
      rw [hT_eq, map_smul, LinearMap.trace_id, smul_eq_mul]
    have hfind : (Module.finrank ℂ N : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Module.finrank_pos_iff.mpr hnt).ne'
    have hc0 : c = 0 := by
      have h2 : c * (Module.finrank ℂ N : ℂ) = 0 := by rw [← htrace_scalar, htrace0]
      exact (mul_eq_zero.mp h2).resolve_right hfind
    have hT0 : T = 0 := by rw [hT_eq, hc0]; simp
    rw [← hTapply x, hT0]; simp
  -- Hence `classSum f` acts as `0` on the whole regular module.
  have hzero : classSum f = 0 := by
    let K : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
      { carrier := {y | classSum f * y = 0}
        add_mem' := by
          intro a b ha hb
          show classSum f * (a + b) = 0
          rw [mul_add, ha, hb, add_zero]
        zero_mem' := by
          show classSum f * 0 = 0
          simp
        smul_mem' := by
          intro a b hb
          show classSum f * (a * b) = 0
          rw [← mul_assoc, hcent a, mul_assoc, hb, mul_zero] }
    have hle : sSup ((irrSubmodules G :
        Finset (Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))) : Set _) ≤ K := by
      refine sSup_le fun N hN y hy => ?_
      show classSum f * y = 0
      have hthis := hkill N hN ⟨y, hy⟩
      simpa using congrArg Subtype.val hthis
    have htop : K = ⊤ := top_unique (by rw [← sSup_irrSubmodules G]; exact hle)
    have hone : classSum f * (1 : MonoidAlgebra ℂ G) = 0 := by
      have : (1 : MonoidAlgebra ℂ G) ∈ K := by rw [htop]; exact Submodule.mem_top
      exact this
    simpa using hone
  -- Extract coefficients.
  have hcoeff : ∀ g : G, f (g⁻¹) = 0 := by
    intro g
    have hthis := congrArg (fun w : MonoidAlgebra ℂ G => w.coeff g) hzero
    rw [classSum_coeff] at hthis
    simpa using hthis
  funext g
  simpa using hcoeff g⁻¹

end Work.CharCore
