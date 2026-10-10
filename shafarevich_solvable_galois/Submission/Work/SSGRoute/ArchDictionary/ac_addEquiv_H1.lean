import Mathlib.FieldTheory.Normal.Defs
import Submission.Work.SSGRoute.ArchDictionary.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ArchDictionary

open Work.SSGRoute

theorem ac_addEquiv_H1 {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (p : ℕ) (E : Type) [AddCommGroup E]
    [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    (c : Ω ≃ₐ[k] Ω) :
    Nonempty (Work.SSGRoute.ArchDictionary.Ac (K := K) (E := E) c ≃+
      @Work.GroupCohomology.H1 ↥(Subgroup.zpowers c) E _ _
        (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
          (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers c))) := by
  classical
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  let H : Subgroup (Ω ≃ₐ[k] Ω) := Subgroup.zpowers c
  -- The restriction of a cocycle on `⟨c⟩` (viewed as a function on the whole Galois group) to
  -- the subgroup `⟨c⟩`.
  let rho : ↥(Zc K E c) →+ ↥(Work.GroupCohomology.Z1 H E) :=
    { toFun := fun b =>
        ⟨fun g => (b : (Ω ≃ₐ[k] Ω) → E) (g : Ω ≃ₐ[k] Ω), by
          intro g h
          have hb := (b.2 : SSGRoute.IsCocycleOn (SSGRoute.res k K) H
            (b : (Ω ≃ₐ[k] Ω) → E)) (g : Ω ≃ₐ[k] Ω) g.2 (h : Ω ≃ₐ[k] Ω) h.2
          show (b : (Ω ≃ₐ[k] Ω) → E) ((g : ↥H) * h : ↥H) =
            g • ((b : (Ω ≃ₐ[k] Ω) → E) (h : Ω ≃ₐ[k] Ω)) +
              (b : (Ω ≃ₐ[k] Ω) → E) (g : Ω ≃ₐ[k] Ω)
          rw [Subgroup.coe_mul, hb, Subgroup.smul_def]
          exact add_comm _ _⟩
      map_zero' := by
        apply Subtype.ext
        funext g
        rfl
      map_add' := by
        intro a b
        apply Subtype.ext
        funext g
        rfl }
  -- The zero-extension of a crossed homomorphism on `⟨c⟩` to the whole Galois group, which is a
  -- cocycle on `⟨c⟩`: this is a section of `rho`.
  let psi : ↥(Work.GroupCohomology.Z1 H E) → ↥(Zc K E c) := fun f =>
    ⟨fun g => if hg : g ∈ H then (f : ↥H → E) ⟨g, hg⟩ else 0, by
      intro g hg h hh
      have hmul : g * h ∈ H := H.mul_mem hg hh
      have hf := (f.2 : Work.GroupCohomology.IsCrossedHom H E (f : ↥H → E))
        ⟨g, hg⟩ ⟨h, hh⟩
      show (if hg : g * h ∈ H then (f : ↥H → E) ⟨g * h, hg⟩ else 0) =
        (if hg : g ∈ H then (f : ↥H → E) ⟨g, hg⟩ else 0) +
          (SSGRoute.res k K) g • (if hg : h ∈ H then (f : ↥H → E) ⟨h, hg⟩ else 0)
      rw [dif_pos hmul, dif_pos hg, dif_pos hh,
        show (⟨g * h, hmul⟩ : ↥H) = ⟨g, hg⟩ * ⟨h, hh⟩ from Subtype.ext rfl,
        hf, Subgroup.smul_def]
      exact add_comm _ _⟩
  have hrho_psi : ∀ f : ↥(Work.GroupCohomology.Z1 H E), rho (psi f) = f := by
    intro f
    apply Subtype.ext
    funext g
    show (if hg : (g : Ω ≃ₐ[k] Ω) ∈ H then (f : ↥H → E) ⟨(g : Ω ≃ₐ[k] Ω), hg⟩ else 0)
      = (f : ↥H → E) g
    rw [dif_pos g.2]
  have hrho_surj : Function.Surjective rho := fun f => ⟨psi f, hrho_psi f⟩
  -- The composite `Z¹(⟨c⟩,E) → H¹(⟨c⟩,E)`.
  let theta : ↥(Zc K E c) →+ Work.GroupCohomology.H1 H E :=
    (Work.GroupCohomology.H1π H E).comp rho
  have htheta_surj : Function.Surjective theta := by
    intro y
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective
      ((Work.GroupCohomology.B1 H E).comap (Work.GroupCohomology.Z1 H E).subtype) y
    obtain ⟨z, hz⟩ := hrho_surj x
    refine ⟨z, ?_⟩
    show Work.GroupCohomology.H1π H E (rho z) = y
    rw [hz]
    exact hx
  have hH1π : ∀ g : ↥(Work.GroupCohomology.Z1 H E),
      Work.GroupCohomology.H1π H E g = 0 ↔
        (g : ↥H → E) ∈ Work.GroupCohomology.B1 H E := by
    intro g
    rw [Work.GroupCohomology.H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_comap]
    exact Iff.rfl
  have hB1_mem : ∀ f : ↥H → E, f ∈ Work.GroupCohomology.B1 H E ↔
      ∃ a : E, ∀ g : ↥H, f g = g • a - a := by
    intro f
    rw [Work.GroupCohomology.mem_B1_iff]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, fun g => by rw [← ha, Work.GroupCohomology.d0_apply]⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, funext fun g => by
        rw [Work.GroupCohomology.d0_apply]; exact (ha g).symm⟩
  have hkey : ∀ b : ↥(Zc K E c),
      ((rho b : ↥(Work.GroupCohomology.Z1 H E)) : ↥H → E) ∈ Work.GroupCohomology.B1 H E ↔
        b ∈ Bc K E c := by
    intro b
    rw [hB1_mem, mem_Bc]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, fun g hg => ?_⟩
      have h1 : (b : (Ω ≃ₐ[k] Ω) → E) g = (rho b : ↥H → E) ⟨g, hg⟩ := rfl
      rw [h1, ha ⟨g, hg⟩, Subgroup.smul_def]
      rfl
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g => ?_⟩
      show (b : (Ω ≃ₐ[k] Ω) → E) (g : Ω ≃ₐ[k] Ω) = g • m - m
      rw [hm (g : Ω ≃ₐ[k] Ω) g.2, Subgroup.smul_def]
      rfl
  have hker : theta.ker = Bc K E c := by
    ext b
    rw [AddMonoidHom.mem_ker]
    show (Work.GroupCohomology.H1π H E (rho b) = 0) ↔ b ∈ Bc K E c
    rw [hH1π (rho b)]
    exact hkey b
  -- Factor through `Z¹/B¹ = Ac`.
  let f : Work.SSGRoute.ArchDictionary.Ac (K := K) (E := E) c →+
      Work.GroupCohomology.H1 H E :=
    QuotientAddGroup.lift (Bc K E c) theta hker.ge
  have hf_mk : ∀ x, f (QuotientAddGroup.mk' (Bc K E c) x) = theta x :=
    fun x => QuotientAddGroup.lift_mk' _ _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨x0, rfl⟩ := QuotientAddGroup.mk'_surjective (Bc K E c) x
    obtain ⟨y0, rfl⟩ := QuotientAddGroup.mk'_surjective (Bc K E c) y
    rw [hf_mk, hf_mk] at hxy
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem]
    have hmem : x0 - y0 ∈ theta.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
    rwa [hker] at hmem
  have hsurjf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := htheta_surj y
    exact ⟨QuotientAddGroup.mk' (Bc K E c) x, by rw [hf_mk, hx]⟩
  exact ⟨AddEquiv.ofBijective f ⟨hinj, hsurjf⟩⟩

end Work.SSGRoute.ArchDictionary
