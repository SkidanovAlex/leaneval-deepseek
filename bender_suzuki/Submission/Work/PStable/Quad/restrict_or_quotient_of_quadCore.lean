import Mathlib
import Submission.Work.PStable.Quad.Defs
import Submission.Work.HallHigman.GLCore.Defs
import Submission.Work.HallHigman.GLCore.restrict_or_quotient_of_coreHyp
import Submission.Work.HallHigman.eq_one_of_pow_eq_one_of_sq_sub_one_eq_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.PStable.Quad

open Work.HallHigman.GLCore

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- `QuadCore` is preserved by a monoid homomorphism out of `stab U` whose image of `X` does not
commute with the image of `Q`.  (The `two` hypothesis is inherited because the image of `Q` is a
quotient of `Q`.) -/
lemma quadCore_map {p : ℕ} {U : Submodule K V} {Q : Subgroup (Module.End K V)ˣ}
    {X : (Module.End K V)ˣ} (h : QuadCore p Q X) (hQ : Q ≤ stab U) (hX : X ∈ stab U)
    {W : Type*} [AddCommGroup W] [Module K W] (f : stab U →* (Module.End K W)ˣ)
    (hnc : ∃ a ∈ (Q.subgroupOf (stab U)).map f, a * f ⟨X, hX⟩ ≠ f ⟨X, hX⟩ * a) :
    QuadCore p ((Q.subgroupOf (stab U)).map f) (f ⟨X, hX⟩) := by
  haveI : Finite ↥Q := h.finite
  let ψ : Q →* (Q.subgroupOf (stab U)).map f :=
    (f.subgroupMap (Q.subgroupOf (stab U))).comp
      { toFun := fun a => ⟨⟨a, hQ a.2⟩, a.2⟩
        map_one' := by ext; rfl
        map_mul' := by intro a b; ext; rfl }
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := f.subgroupMap_surjective (Q.subgroupOf (stab U)) y
    refine ⟨⟨(x : stab U).val, x.2⟩, ?_⟩
    rw [← hx]
    ext
    rfl
  refine { finite := Finite.of_surjective ψ hψ
           cop := fun hd => h.cop (hd.trans (Subgroup.card_dvd_of_surjective (f := ψ) hψ))
           pow := ?_
           norm := ?_
           noncomm := hnc
           two := ?_ }
  · have hXp : (⟨X, hX⟩ : stab U) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      simpa using h.pow
    rw [← map_pow, hXp, map_one]
  · intro a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr ⟨⟨X, hX⟩ * y * ⟨X, hX⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have hy' : (y : (Module.End K V)ˣ) ∈ Q := Subgroup.mem_subgroupOf.mp hy
      have hh := h.norm (y : (Module.End K V)ˣ) hy'
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hh
    · rw [map_mul, map_mul, map_inv]
  · rcases h.two with h5 | h2
    · exact Or.inl h5
    · refine Or.inr ?_
      intro S' hS'
      exact isMulCommutative_of_isPGroup_two_of_surjective hψ h2 hS'

/-- The quadratic failure hypothesis `(X - 1) ^ 2 = 0` is inherited by the restriction to `U`. -/
lemma restrUnit_sq_sub_one_eq_zero {U : Submodule K V} {X : (Module.End K V)ˣ}
    (hX : X ∈ stab U) (hfail : ((X : Module.End K V) - 1) ^ 2 = 0) :
    ((restrUnit U ⟨X, hX⟩ : Module.End K U) - 1) ^ 2 = 0 := by
  refine Module.End.submodule_pow_eq_zero_of_pow_eq_zero (N := U)
    (g := (restrUnit U ⟨X, hX⟩ : Module.End K U) - 1) (G := ((X : Module.End K V) - 1)) ?_ hfail
  ext u
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
    restrUnit, LinearMap.restrict_apply, Submodule.coe_sub, Module.End.one_apply]

/-- The quadratic failure hypothesis `(X - 1) ^ 2 = 0` is inherited by the quotient `V ⧸ U`. -/
lemma quotUnit_sq_sub_one_eq_zero {U : Submodule K V} {X : (Module.End K V)ˣ}
    (hX : X ∈ stab U) (hfail : ((X : Module.End K V) - 1) ^ 2 = 0) :
    ((quotUnit U ⟨X, hX⟩ : Module.End K (V ⧸ U)) - 1) ^ 2 = 0 := by
  have h1 : (1 : Module.End K (V ⧸ U)) = U.mapQ U (1 : Module.End K V)
      (le_of_eq (Submodule.comap_id U)) := (Submodule.mapQ_id U).symm
  have hsub : (quotUnit U ⟨X, hX⟩ : Module.End K (V ⧸ U)) - 1
      = U.mapQ U ((X : Module.End K V) - 1) (fun v hv =>
          show ((X : Module.End K V) - 1) v ∈ U from by
            simpa [LinearMap.sub_apply, Module.End.one_apply] using U.sub_mem (hX.1 hv) hv) := by
    rw [show (quotUnit U ⟨X, hX⟩ : Module.End K (V ⧸ U))
          = U.mapQ U ((X : Module.End K V)) hX.1 from rfl, h1]
    rw [← mapQ_sub]
  rw [hsub, ← Submodule.mapQ_pow]
  ext x
  simp only [LinearMap.comp_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  rw [hfail]
  simp

/-- **The quadratic GL-core is inherited by a restriction or by a quotient.**  If `V` is not
irreducible for `𝒬 ∪ {X}` and `U` is a proper nontrivial invariant subspace, then a counterexample
to the quadratic GL-core (same `p`, with `(X - 1) ^ 2 = 0`) is inherited either by the restriction
to `U` or by the action on `V ⧸ U`. -/
theorem restrict_or_quotient_of_quadCore {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {p : ℕ} [Fact p.Prime] [CharP K p] {Q : Subgroup (Module.End K V)ˣ}
    {X : (Module.End K V)ˣ} (h : Work.PStable.Quad.QuadCore p Q X) {U : Submodule K V}
    (hQU : ∀ a ∈ Q, ∀ v ∈ U, (a : Module.End K V) v ∈ U)
    (hXU : ∀ v ∈ U, (X : Module.End K V) v ∈ U) (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤)
    (hfail : ((X : Module.End K V) - 1) ^ 2 = 0) :
    (∃ (Q' : Subgroup (Module.End K U)ˣ) (X' : (Module.End K U)ˣ),
        Work.PStable.Quad.QuadCore p Q' X' ∧ ((X' : Module.End K U) - 1) ^ 2 = 0) ∨
    (∃ (Q'' : Subgroup (Module.End K (V ⧸ U))ˣ) (X'' : (Module.End K (V ⧸ U))ˣ),
        Work.PStable.Quad.QuadCore p Q'' X'' ∧
          ((X'' : Module.End K (V ⧸ U)) - 1) ^ 2 = 0) := by
  haveI := h.finite
  have hX : X ∈ stab U := mem_stab_of_pow_eq_one (Fact.out : p.Prime).pos h.pow hXU
  have hQ : Q ≤ stab U := le_stab_of_forall_mapsTo hQU
  by_cases hR : ∃ a ∈ (Q.subgroupOf (stab U)).map (restrHom U),
      a * restrHom U ⟨X, hX⟩ ≠ restrHom U ⟨X, hX⟩ * a
  · left
    exact ⟨_, _, quadCore_map h hQ hX (restrHom U) hR, restrUnit_sq_sub_one_eq_zero hX hfail⟩
  · by_cases hQq : ∃ a ∈ (Q.subgroupOf (stab U)).map (quotHom U),
        a * quotHom U ⟨X, hX⟩ ≠ quotHom U ⟨X, hX⟩ * a
    · right
      exact ⟨_, _, quadCore_map h hQ hX (quotHom U) hQq, quotUnit_sq_sub_one_eq_zero hX hfail⟩
    · exfalso
      push_neg at hR hQq
      obtain ⟨a₀, ha₀, hnc⟩ := h.noncomm
      have hcQ : X * a₀ * X⁻¹ * a₀⁻¹ ∈ Q := Q.mul_mem (h.norm a₀ ha₀) (Q.inv_mem ha₀)
      have hcstab : X * a₀ * X⁻¹ * a₀⁻¹ ∈ stab U := hQ hcQ
      have hcomp : (⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩ : stab U)
          = ⟨X, hX⟩ * ⟨a₀, hQ ha₀⟩ * ⟨X, hX⟩⁻¹ * ⟨a₀, hQ ha₀⟩⁻¹ := by
        apply Subtype.ext
        simp [Subgroup.coe_mul, Subgroup.coe_inv]
      have hmemR : restrHom U ⟨a₀, hQ ha₀⟩ ∈ (Q.subgroupOf (stab U)).map (restrHom U) :=
        Subgroup.mem_map.mpr ⟨⟨a₀, hQ ha₀⟩, Subgroup.mem_subgroupOf.mpr ha₀, rfl⟩
      have hmemQ : quotHom U ⟨a₀, hQ ha₀⟩ ∈ (Q.subgroupOf (stab U)).map (quotHom U) :=
        Subgroup.mem_map.mpr ⟨⟨a₀, hQ ha₀⟩, Subgroup.mem_subgroupOf.mpr ha₀, rfl⟩
      have hcommR : restrHom U ⟨a₀, hQ ha₀⟩ * restrHom U ⟨X, hX⟩
          = restrHom U ⟨X, hX⟩ * restrHom U ⟨a₀, hQ ha₀⟩ := hR _ hmemR
      have hcommQ : quotHom U ⟨a₀, hQ ha₀⟩ * quotHom U ⟨X, hX⟩
          = quotHom U ⟨X, hX⟩ * quotHom U ⟨a₀, hQ ha₀⟩ := hQq _ hmemQ
      have hr : restrUnit U ⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩ = 1 := by
        rw [show restrUnit U ⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩
              = restrHom U ⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩ from rfl]
        rw [hcomp, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcommR]
        group
      have hq : quotUnit U ⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩ = 1 := by
        rw [show quotUnit U ⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩
              = quotHom U ⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩ from rfl]
        rw [hcomp, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcommQ]
        group
      have hsq : ((((X * a₀ * X⁻¹ * a₀⁻¹ : (Module.End K V)ˣ)) : Module.End K V) - 1) ^ 2 = 0 :=
        sq_sub_one_eq_zero_of_restr_eq_one_of_quot_eq_one hcstab hr hq
      have hpow : ((X * a₀ * X⁻¹ * a₀⁻¹ : (Module.End K V)ˣ)) ^ Nat.card Q = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard Q hcQ)
      have hpow' : (((X * a₀ * X⁻¹ * a₀⁻¹ : (Module.End K V)ˣ)) : Module.End K V) ^ Nat.card Q
          = 1 := by
        rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
      have hc_eq : (((X * a₀ * X⁻¹ * a₀⁻¹ : (Module.End K V)ˣ)) : Module.End K V) = 1 :=
        Work.HallHigman.eq_one_of_pow_eq_one_of_sq_sub_one_eq_zero h.cop hpow' hsq
      have hcunit : X * a₀ * X⁻¹ * a₀⁻¹ = 1 := Units.ext hc_eq
      have hxa : X * a₀ = a₀ * X := by
        calc X * a₀ = (X * a₀ * X⁻¹ * a₀⁻¹) * (a₀ * X) := by group
          _ = 1 * (a₀ * X) := by rw [hcunit]
          _ = a₀ * X := by group
      exact hnc hxa.symm

end Work.PStable.Quad
