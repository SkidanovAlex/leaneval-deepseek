import Mathlib
import Submission.Work.Cohomology.RatModZ

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

/-!
# Extending a `ℤ`-linear functional on a finite-index submodule up to a natural number

If `B ≤ Z` is a `ℤ`-submodule with `Z ⧸ B` finitely generated and `φ : B →ₗ[ℤ] ℤ` is any linear
functional, then some positive multiple `N • φ` extends to all of `Z`: there are `N : ℕ`, `N > 0`,
and `ψ : Z →ₗ[ℤ] ℤ` with `ψ b = N • φ b` for all `b ∈ B`.

The proof uses the injectivity of `ℚ` (`Work.Cohomology.injective_rat`, i.e. divisibility):

* extend `φ` (viewed as a map into `ℚ`) to a linear map `Ψ : Z →ₗ[ℤ] ℚ`;
* the composite `Z →ₗ[ℤ] ℚ ⧸ ℤ` kills `B`, hence factors through `Z ⧸ B`;
* that quotient is finitely generated and every element of `ℚ ⧸ ℤ` is torsion, so some `N > 0`
  kills the composite; equivalently `N • Ψ z ∈ ℤ` for all `z`;
* this makes `z ↦ N • Ψ z` a linear map into the submodule `ℤ ⊆ ℚ`, which we identify with `ℤ`.

The `ULift` in the first step is only there to put `ℚ` in the same universe as `Z`, which the
statement of `Module.Injective.out` requires.
-/

namespace Work.ThomBordism

open Work.Cohomology

/-- Every element of `ℚ ⧸ ℤ` has finite additive order. -/
lemma qZ_torsion (x : qZ) : ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective ratIntSub x
  refine ⟨q.den, q.pos, ?_⟩
  rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [nsmul_eq_mul, mul_comm, Rat.mul_den_eq_num]
  exact mem_ratIntSub.mpr ⟨q.num, rfl⟩

/-- A finitely generated torsion `ℤ`-module is killed by a positive natural number. -/
lemma exists_nat_nsmul_eq_zero_of_fg_torsion {M : Type*} [AddCommGroup M] [Module ℤ M]
    (hfg : Module.Finite ℤ M) (htor : ∀ x : M, ∃ n : ℕ, 0 < n ∧ n • x = 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : M, N • x = 0 := by
  haveI := hfg
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := ℤ) (M := M))
  set T : Finset M := hSfin.toFinset with hT
  have hTspan : Submodule.span ℤ (T : Set M) = ⊤ := by
    rw [hT, hSfin.coe_toFinset]; exact hSspan
  choose d hdpos hd using htor
  refine ⟨T.prod d, Finset.prod_pos (fun s _ => hdpos s), ?_⟩
  intro x
  have hx : x ∈ Submodule.span ℤ (T : Set M) := by rw [hTspan]; trivial
  refine Submodule.span_induction (p := fun x _ => T.prod d • x = 0) ?_ ?_ ?_ ?_ hx
  · intro s hs
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d hs
    rw [hk, mul_nsmul, hd s, smul_zero]
  · exact smul_zero _
  · intro a b ha hb iha ihb
    rw [smul_add, iha, ihb, add_zero]
  · intro c a ha iha
    rw [smul_comm, iha, smul_zero]

universe u

/-- Every `ℤ`-linear functional on a submodule of a `ℤ`-module extends to the whole module after
viewing `ℤ` as a submodule of the divisible group `ℚ`. -/
lemma rat_extend_of_submodule {Z : Type u} [AddCommGroup Z] [Module ℤ Z]
    (B : Submodule ℤ Z) (f : B →ₗ[ℤ] ℚ) : ∃ F : Z →ₗ[ℤ] ℚ, ∀ b : B, F (b : Z) = f b := by
  haveI : Module.Injective ℤ (ULift.{u,0} ℚ) :=
    Module.ulift_injective_of_injective (R := ℤ) Work.Cohomology.injective_rat
  let f₀ : B →ₗ[ℤ] ULift.{u,0} ℚ :=
    { toFun := fun b => ULift.up (f b)
      map_add' := by intro a b; apply ULift.ext; simp [map_add]
      map_smul' := by intro c b; apply ULift.ext; simp [map_smul] }
  let ι : B →ₗ[ℤ] Z :=
    { toFun := fun b => (b : Z)
      map_add' := by intro a b; rfl
      map_smul' := by
        intro c b
        rw [AddSubgroupClass.coe_zsmul b c]
        simp only [RingHom.id_apply]
        exact (int_smul_eq_zsmul (inferInstanceAs (Module ℤ Z)) c (b : Z)).symm }
  obtain ⟨F', hF'⟩ := Module.Injective.out ι (fun a b h => Subtype.ext h) f₀
  refine ⟨(ULift.moduleEquiv (R := ℤ) (M := ℚ)).toLinearMap.comp F', fun b => ?_⟩
  have hb : F' (b : Z) = f₀ b := hF' b
  change ULift.down (F' (b : Z)) = f b
  rw [hb]
  simp [f₀]

theorem extUpToNat {Z : Type*} [AddCommGroup Z] [Module ℤ Z]
    (B : Submodule ℤ Z) (hfg : Module.Finite ℤ (Z ⧸ B)) (φ : B →ₗ[ℤ] ℤ) :
    ∃ N : ℕ, 0 < N ∧ ∃ ψ : Z →ₗ[ℤ] ℤ, ∀ b : B, ψ (b : Z) = N • φ b := by
  let f₀ : B →ₗ[ℤ] ℚ :=
    { toFun := fun b => (φ b : ℚ)
      map_add' := by intro a b; simp only [map_add, Int.cast_add]
      map_smul' := by
        intro c b
        simp only [map_smul, zsmul_eq_mul, Int.cast_mul, RingHom.id_apply]
        push_cast
        ring }
  obtain ⟨Ψ, hΨ⟩ := rat_extend_of_submodule B f₀
  let Φ : Z →ₗ[ℤ] qZ := (Submodule.mkQ ratIntSub).comp Ψ
  have hker : B ≤ Φ.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    have hx' : Ψ x = (φ ⟨x, hx⟩ : ℚ) := hΨ ⟨x, hx⟩
    have h1 : Φ x = Submodule.Quotient.mk (Ψ x) := rfl
    rw [h1, hx', Submodule.Quotient.mk_eq_zero]
    exact mem_ratIntSub.mpr ⟨φ ⟨x, hx⟩, rfl⟩
  let Φ' : Z ⧸ B →ₗ[ℤ] qZ := Submodule.liftQ B Φ hker
  have hΦ' : ∀ z : Z, Φ' (Submodule.mkQ B z) = Φ z :=
    fun z => Submodule.liftQ_apply B Φ (h := hker) z
  -- the image of `Φ'` is finitely generated and torsion, hence killed by some positive `N`
  haveI := hfg
  obtain ⟨N, hNpos, hkill⟩ := exists_nat_nsmul_eq_zero_of_fg_torsion
      (M := ↥Φ'.range) (inferInstance) (fun y => by
        obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
        obtain ⟨n, hnpos, hn⟩ := qZ_torsion (Φ' x)
        refine ⟨n, hnpos, ?_⟩
        apply Subtype.ext
        change n • (y : qZ) = 0
        rw [← hx]
        exact hn)
  have hmain : ∀ z : Z, N • Φ z = 0 := by
    intro z
    rw [← hΦ' z]
    have h := hkill ⟨Φ' (Submodule.mkQ B z), ⟨Submodule.mkQ B z, rfl⟩⟩
    simpa using congrArg Subtype.val h
  have hmem : ∀ z : Z, N • Ψ z ∈ ratIntSub := by
    intro z
    rw [← Submodule.Quotient.mk_eq_zero]
    have h1 : Submodule.mkQ ratIntSub (N • Ψ z) = 0 := by
      rw [map_nsmul]
      change N • Φ z = 0
      exact hmain z
    rwa [Submodule.mkQ_apply] at h1
  let Θ : Z →ₗ[ℤ] ratIntSub := (N • Ψ).codRestrict ratIntSub hmem
  refine ⟨N, hNpos, intEquiv.symm.comp Θ, fun b => ?_⟩
  have hb : Θ (b : Z) = intEquiv (N • φ b) := by
    apply Subtype.ext
    show N • Ψ (b : Z) = ((N • φ b : ℤ) : ℚ)
    have h1 : Ψ (b : Z) = (φ b : ℚ) := hΨ b
    rw [h1, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [LinearMap.comp_apply, hb]
  simp

end Work.ThomBordism
