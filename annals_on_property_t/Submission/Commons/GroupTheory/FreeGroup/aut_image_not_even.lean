import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PicardGroup
import Submission.Commons.GroupTheory.FreeGroup.abHom_mk_toAdd

namespace Commons.GroupTheory.FreeGroup

/-- The vector space `(ℤ/2)^n`, written additively. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- The `u`-th standard basis vector of `(ℤ/2)^n`. -/
def stdBasis (n : ℕ) : Fin n → Vec n := fun u => Pi.single u 1

theorem aut_image_not_even (n : ℕ) (α : MulAut (FreeGroup (Fin n))) (p : Fin n) :
    ∃ u : Fin n, ¬ (2 : ℤ) ∣ (abHom n (α (FreeGroup.of p))).toAdd u := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  let ρa : (Fin n → ℤ) →+ Vec n :=
    { toFun := fun x => fun u => (x u : ZMod 2)
      map_zero' := rfl
      map_add' := fun a b => by funext u; exact Int.cast_add (a u) (b u) }
  let ρ : Multiplicative (Fin n → ℤ) →* Multiplicative (Vec n) := AddMonoidHom.toMultiplicative ρa
  let θ : FreeGroup (Fin n) →* Multiplicative (Vec n) := ρ.comp (abHom n)
  have hθ_of : ∀ u : Fin n, θ (FreeGroup.of u) = Multiplicative.ofAdd (stdBasis n u) := by
    intro u
    have h1 : abHom n (FreeGroup.of u) = Multiplicative.ofAdd (Pi.single u (1 : ℤ)) := by
      rw [abHom, FreeGroup.lift_apply_of]
    rw [show θ (FreeGroup.of u) = ρ (abHom n (FreeGroup.of u)) from rfl, h1]
    show Multiplicative.ofAdd
        (ρa (Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single u (1 : ℤ)))))
        = Multiplicative.ofAdd (stdBasis n u)
    rw [toAdd_ofAdd]
    congr 1
    ext u'
    change (((Pi.single u (1 : ℤ) : Fin n → ℤ) u' : ZMod 2))
      = ((Pi.single u (1 : ZMod 2) : Fin n → ZMod 2) u')
    by_cases h : u' = u
    · subst h; simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]
      simp
  -- the standard basis generates `(ℤ/2)^n` as an additive group
  have hspan : AddSubgroup.closure (Set.range (stdBasis n)) = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro v
    have hv : v = ∑ u : Fin n, v u • stdBasis n u := by
      ext i
      rw [Finset.sum_apply]
      simp only [stdBasis, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      rw [Finset.sum_eq_single i
        (fun b _ hb => by rw [if_neg (by rintro rfl; exact hb rfl), mul_zero])
        (fun hi => absurd (Finset.mem_univ i) hi)]
      rw [if_pos rfl, mul_one]
    rw [hv]
    apply AddSubgroup.sum_mem
    intro u _
    exact zmod_smul_mem (K := AddSubgroup.closure (Set.range (stdBasis n)))
      (AddSubgroup.subset_closure
        (show stdBasis n u ∈ Set.range (stdBasis n) from ⟨u, rfl⟩)) (v u)
  have hpre : Multiplicative.ofAdd ⁻¹'
        (Set.range (fun u => Multiplicative.ofAdd (stdBasis n u)))
      = Set.range (stdBasis n) := by
    ext v
    constructor
    · rintro ⟨u, hu⟩; exact ⟨u, Multiplicative.ofAdd.injective hu⟩
    · rintro ⟨u, rfl⟩; exact ⟨u, rfl⟩
  have hcl : Subgroup.closure (Set.range (fun u => Multiplicative.ofAdd (stdBasis n u))) = ⊤ := by
    have h2 : Subgroup.toAddSubgroup'
          (Subgroup.closure (Set.range (fun u => Multiplicative.ofAdd (stdBasis n u))))
        = Subgroup.toAddSubgroup' (⊤ : Subgroup (Multiplicative (Vec n))) := by
      rw [Subgroup.toAddSubgroup'_closure, hpre, hspan, OrderIso.map_top]
    exact Subgroup.toAddSubgroup'.injective h2
  have hθsurj : Function.Surjective θ := by
    have hθlift : θ = FreeGroup.lift (fun u => Multiplicative.ofAdd (stdBasis n u)) :=
      FreeGroup.ext_hom _ _ (fun u => by rw [hθ_of u, FreeGroup.lift_apply_of])
    rw [hθlift, FreeGroup.lift_surjective_iff_closure_range_eq_top]
    exact hcl
  -- the linear map encoding the induced map on `(ℤ/2)^n`
  let g : Fin n → Vec n := fun u => (θ (α (FreeGroup.of u))).toAdd
  let E : Vec n →ₗ[ZMod 2] Vec n :=
    { toFun := fun x i => ∑ j : Fin n, x j * g j i
      map_add' := by
        intro x y
        ext i
        change (∑ j : Fin n, (x + y) j * g j i)
            = (∑ j : Fin n, x j * g j i) + (∑ j : Fin n, y j * g j i)
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [Pi.add_apply, add_mul]
      map_smul' := by
        intro c x
        ext i
        change (∑ j : Fin n, (c • x) j * g j i) = c * (∑ j : Fin n, x j * g j i)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [Pi.smul_apply, smul_eq_mul]
        ring }
  have hE_basis : ∀ u : Fin n, E (stdBasis n u) = g u := by
    intro u
    ext i
    change (∑ j : Fin n, (stdBasis n u) j * g j i) = g u i
    simp only [stdBasis]
    rw [Finset.sum_eq_single u
      (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_mul])
      (fun hu => absurd (Finset.mem_univ u) hu)]
    rw [Pi.single_eq_same, one_mul]
  have hEcomp : (AddMonoidHom.toMultiplicative E.toAddMonoidHom).comp θ
      = θ.comp α.toMonoidHom := by
    apply FreeGroup.ext_hom
    intro u
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    change (AddMonoidHom.toMultiplicative E.toAddMonoidHom) (θ (FreeGroup.of u))
        = θ (α (FreeGroup.of u))
    rw [hθ_of u]
    show Multiplicative.ofAdd (E (stdBasis n u)) = θ (α (FreeGroup.of u))
    rw [hE_basis u]
    show Multiplicative.ofAdd (g u) = θ (α (FreeGroup.of u))
    rw [show g u = (θ (α (FreeGroup.of u))).toAdd from rfl, ofAdd_toAdd]
  have hEtop : E.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    have hEhom_surj : Function.Surjective (AddMonoidHom.toMultiplicative E.toAddMonoidHom) := by
      rw [← MonoidHom.range_eq_top]
      have hcomp_top : ((AddMonoidHom.toMultiplicative E.toAddMonoidHom).comp θ).range = ⊤ := by
        rw [hEcomp, MonoidHom.range_eq_top]
        intro y
        obtain ⟨x, hx⟩ := hθsurj y
        refine ⟨α.symm x, ?_⟩
        show θ (α (α.symm x)) = y
        rw [MulEquiv.apply_symm_apply]
        exact hx
      rw [eq_top_iff, ← hcomp_top]
      rintro y ⟨x, rfl⟩
      exact ⟨θ x, rfl⟩
    intro v
    obtain ⟨x, hx⟩ := hEhom_surj (Multiplicative.ofAdd v)
    refine ⟨x.toAdd, ?_⟩
    have hxx := congrArg Multiplicative.toAdd hx
    simpa using hxx
  -- `stdBasis n p` lies in the kernel
  have hgp : g p = 0 := by
    have hθα : θ (α (FreeGroup.of p))
        = Multiplicative.ofAdd (fun u => ((abHom n (α (FreeGroup.of p))).toAdd u : ZMod 2)) := by
      show ρ (abHom n (α (FreeGroup.of p))) = _
      rfl
    have hfun : (fun u => ((abHom n (α (FreeGroup.of p))).toAdd u : ZMod 2)) = (0 : Vec n) := by
      funext u
      obtain ⟨k, hk⟩ := hcon u
      have hcast : ((abHom n (α (FreeGroup.of p))).toAdd u : ZMod 2) = 0 := by
        rw [hk]
        push_cast
        rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]
      simpa using hcast
    change (θ (α (FreeGroup.of p))).toAdd = 0
    rw [hθα, toAdd_ofAdd]
    exact hfun
  have hmem : stdBasis n p ∈ LinearMap.ker E := by
    rw [LinearMap.mem_ker, hE_basis p]
    exact hgp
  have hker : 1 ≤ Module.finrank (ZMod 2) (LinearMap.ker E) := by
    have hle : (ZMod 2) ∙ stdBasis n p ≤ LinearMap.ker E := by
      rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hmem
    have h1 : Module.finrank (ZMod 2) ((ZMod 2) ∙ stdBasis n p) = 1 := by
      rw [finrank_span_singleton]
      intro h
      have := congrFun h p
      simp [stdBasis] at this
    calc 1 = Module.finrank (ZMod 2) ((ZMod 2) ∙ stdBasis n p) := h1.symm
      _ ≤ Module.finrank (ZMod 2) (LinearMap.ker E) := Submodule.finrank_mono hle
  have h := LinearMap.finrank_range_add_finrank_ker E
  rw [hEtop, finrank_top,
    Module.finrank_fintype_fun_eq_card (ZMod 2), Fintype.card_fin] at h
  omega

end Commons.GroupTheory.FreeGroup