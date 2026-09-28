import Mathlib
import Submission.Work.Cohomology.CapH
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.kronH_capPair_cup
import Submission.Work.Cohomology.gradedComm
import Submission.Work.Cohomology.uctDual_evaluation
import Submission.Work.Cohomology.free_submodule_of_free_int
import Submission.Work.Cohomology.singularChains_free
import Submission.Work.Cohomology.relChainsProjective

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

-- On a `ℤ`-module the two `ℤ`-actions (the one coming from the module structure and the canonical
-- `zsmul` of the additive group) are the same; preferring the module-structure one makes the
-- instance chosen for `a • x` agree with the one used by Mathlib's torsion API.
attribute [local instance 100] ZSMul.toSMul

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

/-! ## Auxiliary lemmas -/

/-- Evaluation at a fixed element, as a linear map. -/
def evalAtLM {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module ℤ M] [Module ℤ N]
    (c : M) : (M →ₗ[ℤ] N) →ₗ[ℤ] N where
  toFun f := f c
  map_add' f g := rfl
  map_smul' a f := rfl

@[simp] theorem evalAtLM_apply {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module ℤ M]
    [Module ℤ N] (c : M) (f : M →ₗ[ℤ] N) : evalAtLM c f = f c := rfl

/-- Casting along a self-equality is the identity. -/
theorem eqRec_self {α : Sort*} {β : α → Sort*} {a : α} (h : a = a) (x : β a) : h ▸ x = x := by
  rw [Subsingleton.elim h rfl]

/-! ## Every functional on `Hₙ` is a Kronecker pairing -/

/-- **Every functional on `Hₙ` is a Kronecker pairing.**  For a simplicial set `X` whose singular
chains are degreewise free, every `ℤ`-linear functional on `Hₙ(X;ℤ)` is `⟨γ, ·⟩` for some class
`γ ∈ Hⁿ(X;ℤ)`.

This is the surjectivity half of the universal coefficient theorem: the evaluation map
`Hⁿ(X;ℤ) → Hom(Hₙ(X;ℤ), ℤ)` is onto.  Chain-level, a functional on the cycles that vanishes on the
boundaries extends to the chains because the chains split over the cycles (the boundaries are a
subgroup of a free module, hence free). -/
theorem kronH_surjective (X : SSet) (n : ℕ)
    (hfree : ∀ k, Module.Free ℤ ↥((chainC ℤ X).X k)) :
    ∀ χ : ↥((chainC ℤ X).homology n) →ₗ[ℤ] ℤ,
      ∃ γ : ↥((cochainC ℤ X).homology n), kronH ℤ X n γ = χ := by
  intro χ
  haveI : Module.Free ℤ ↥((chainC ℤ X).X (n - 1)) := hfree (n - 1)
  haveI : Module.Free ℤ ↥(uctR (chainC ℤ X) n) := by
    rw [show Submodule.module (uctR (chainC ℤ X) n)
      = AddCommGroup.toIntModule ↥(uctR (chainC ℤ X) n) from Subsingleton.elim _ _]
    exact free_submodule_of_free_int _
  have hproj : Module.Projective ℤ ↥(uctR (chainC ℤ X) n) := inferInstance
  obtain ⟨ρ, hρ⟩ := exists_retraction_cycles (chainC ℤ X) n hproj
  -- the functional on the concrete quotient `Zₙ ⧸ Bₙ`, and its pullback to the cycles
  let χ' : (↥(uctZ (chainC ℤ X) n) ⧸ uctH (chainC ℤ X) n) →ₗ[ℤ] ℤ :=
    χ.comp (homologyZIso (chainC ℤ X) n).inv.hom
  let χt : ↥(uctZ (chainC ℤ X) n) →ₗ[ℤ] ℤ := χ'.comp (uctH (chainC ℤ X) n).mkQ
  let w : ↥((chainC ℤ X).X n) →ₗ[ℤ] ℤ := χt.comp ρ
  have hw : cochainDiff ℤ X w = 0 := by
    ext y
    have hcyc : ((chainC ℤ X).d (n + 1) n).hom y ∈ uctZ (chainC ℤ X) n := by
      rw [uctZ, LinearMap.mem_ker]
      have h := congrArg (fun (g : (chainC ℤ X).X (n + 1) ⟶ (chainC ℤ X).X (n - 1)) =>
        ModuleCat.Hom.hom g y) (HomologicalComplex.d_comp_d (chainC ℤ X) (n + 1) n (n - 1))
      exact h
    have hfix : ρ (((chainC ℤ X).d (n + 1) n).hom y) = ⟨_, hcyc⟩ := by
      have h := LinearMap.congr_fun hρ (⟨_, hcyc⟩ : ↥(uctZ (chainC ℤ X) n))
      simpa using h
    have hker : (⟨_, hcyc⟩ : ↥(uctZ (chainC ℤ X) n)) ∈ uctH (chainC ℤ X) n :=
      (mem_uctH _ n _).mpr ⟨y, rfl⟩
    show w (((chainC ℤ X).d (n + 1) n).hom y) = 0
    simp only [w, LinearMap.comp_apply]
    rw [hfix]
    simp only [χt, χ', LinearMap.comp_apply]
    rw [show (uctH (chainC ℤ X) n).mkQ (⟨_, hcyc⟩ : ↥(uctZ (chainC ℤ X) n)) = 0 from by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]; exact hker]
    simp
  refine ⟨cohomologyClassOf ℤ X w hw, ?_⟩
  apply LinearMap.ext
  intro b
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((chainC ℤ X).homologyπ n)).mp inferInstance b
  rw [kronH_apply ℤ X w hw c]
  have hcyc : ((chainC ℤ X).iCycles n).hom c ∈ uctZ (chainC ℤ X) n := by
    rw [uctZ, LinearMap.mem_ker]
    have h : ModuleCat.Hom.hom ((chainC ℤ X).iCycles n ≫ (chainC ℤ X).d n (n - 1)) c = 0 := by
      rw [HomologicalComplex.iCycles_d, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  have hfix : ρ (((chainC ℤ X).iCycles n).hom c) = ⟨_, hcyc⟩ := by
    have h := LinearMap.congr_fun hρ (⟨_, hcyc⟩ : ↥(uctZ (chainC ℤ X) n))
    simpa using h
  show w (((chainC ℤ X).iCycles n).hom c) = χ (((chainC ℤ X).homologyπ n).hom c)
  simp only [w, LinearMap.comp_apply]
  rw [hfix]
  simp only [χt, χ', LinearMap.comp_apply]
  have hh : (homologyZIso (chainC ℤ X) n).inv.hom
        ((uctH (chainC ℤ X) n).mkQ ((cycIsoZ (chainC ℤ X) n).hom c))
      = (((chainC ℤ X).homologyπ n).hom c) := by
    rw [← homologyZIso_apply _ n c]
    exact CategoryTheory.Iso.hom_inv_id_apply _ _
  have hv : ((cycIsoZ (chainC ℤ X) n).hom c : ↥((chainC ℤ X).X n))
      = ((chainC ℤ X).iCycles n).hom c := cycIsoZ_hom_val _ n c
  rw [show (⟨_, hcyc⟩ : ↥(uctZ (chainC ℤ X) n)) = (cycIsoZ (chainC ℤ X) n).hom c from
    Subtype.ext hv.symm, hh]

/-! ## Torsion: elements killed by all functionals -/

/-- In a finitely generated `ℤ`-module, an element killed by every `ℤ`-linear functional to `ℤ` is
torsion.  (The quotient by the torsion submodule is finitely generated and torsion free, hence
free, and the dual of a free module separates points.) -/
theorem mem_torsion_of_forall_apply_eq_zero {P : Type*} [AddCommGroup P] [Module ℤ P]
    (hfin : Module.Finite ℤ P) (x : P) (h : ∀ ψ : P →ₗ[ℤ] ℤ, ψ x = 0) :
    x ∈ Submodule.torsion ℤ P := by
  by_contra hx
  haveI : Module.Finite ℤ P := hfin
  haveI : Module.Finite ℤ (P ⧸ Submodule.torsion ℤ P) :=
    Module.Finite.of_surjective (Submodule.mkQ (Submodule.torsion ℤ P))
      (Submodule.mkQ_surjective _)
  haveI : Module.Free ℤ (P ⧸ Submodule.torsion ℤ P) := inferInstance
  let b := Module.Free.chooseBasis ℤ (P ⧸ Submodule.torsion ℤ P)
  have hx0 : (Submodule.mkQ (Submodule.torsion ℤ P)) x ≠ 0 := by
    intro h0
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at h0
    exact hx h0
  have hrepr : b.repr ((Submodule.mkQ (Submodule.torsion ℤ P)) x) ≠ 0 := by
    intro h0
    exact hx0 (b.repr.injective (by rw [h0, map_zero]))
  obtain ⟨i, hi⟩ : ∃ i, b.repr ((Submodule.mkQ (Submodule.torsion ℤ P)) x) i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hrepr (Finsupp.ext h')
  let ψ : P →ₗ[ℤ] ℤ := (Finsupp.lapply i).comp
    ((b.repr : _ →ₗ[ℤ] _).comp (Submodule.mkQ (Submodule.torsion ℤ P)))
  have hψ : ψ x = b.repr ((Submodule.mkQ (Submodule.torsion ℤ P)) x) i := rfl
  exact hi (by rw [← hψ]; exact h ψ)

/-- A torsion element of a `ℤ`-module has a positive natural multiple equal to zero. -/
theorem exists_nat_smul_eq_zero_of_mem_torsion {P : Type*} [AddCommGroup P] [Module ℤ P] {x : P}
    (hx : x ∈ Submodule.torsion ℤ P) : ∃ N : ℕ, 0 < N ∧ N • x = 0 := by
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (M := P) x).mp hx
  have hne : (a : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero a
  have ha' : ((a : ℤ) • x) = 0 := Submonoid.smul_def a x ▸ ha
  refine ⟨(a : ℤ).natAbs, Int.natAbs_pos.mpr hne, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℤ ((a : ℤ).natAbs) x]
  rcases lt_trichotomy (a : ℤ) 0 with hneg | hzero | hpos
  · have h1 : (((a : ℤ).natAbs : ℤ)) = -(a : ℤ) := by
      rw [← Int.natAbs_neg (a : ℤ), Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ -(a : ℤ))]
    rw [h1, neg_smul, ha', neg_zero]
  · exact absurd hzero hne
  · have h1 : (((a : ℤ).natAbs : ℤ)) = (a : ℤ) := Int.natAbs_of_nonneg hpos.le
    rw [h1, ha']

/-! ## The main theorem -/

theorem evaluation_kernel_torsion_of_pd {X : TopCat} (n : ℕ)
    (c : (Work.Cohomology.singularChains ℤ X).homology (n + n))
    (hcap : Function.Bijective (fun y : (Work.Cohomology.singularCochainComplex ℤ X).homology n =>
      (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj X) n n) y c))
    (hfg : ∀ k, Module.Finite ℤ ((Work.Cohomology.singularChains ℤ X).homology k)) :
    ∀ α : (Work.Cohomology.singularCochainComplex ℤ X).homology n,
      (∀ b : (Work.Cohomology.singularChains ℤ X).homology n,
        Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) n α b = 0) →
      ∃ N : ℕ, 0 < N ∧ N • α = 0 := by
  intro α hα
  -- the cap-product map with the fundamental class
  let Φ : ↥((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homology n) →ₗ[ℤ]
      ↥((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).homology n) :=
    (evalAtLM c).comp (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj X) n n)
  have hΦ : Function.Bijective Φ := hcap
  have hPfin : Module.Finite ℤ
      ↥((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homology n) := by
    haveI : Module.Finite ℤ
        ↥((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).homology n) := hfg n
    exact Module.Finite.equiv (LinearEquiv.ofBijective Φ hΦ).symm
  -- every functional on `Hⁿ` kills `α`
  have hkill : ∀ ψ : ↥((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homology n) →ₗ[ℤ] ℤ,
      ψ α = 0 := by
    intro ψ
    let e : ↥((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homology n) ≃ₗ[ℤ]
        ↥((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).homology n) :=
      LinearEquiv.ofBijective Φ hΦ
    let χ : ↥((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).homology n) →ₗ[ℤ] ℤ :=
      ψ.comp (e.symm : _ →ₗ[ℤ] _)
    obtain ⟨γ, hγ⟩ := kronH_surjective (TopCat.toSSet.obj X) n
      (fun k => Work.Cohomology.singularChains_free X k) χ
    have h1 : ψ α = χ (Φ α) := by
      show ψ α = ψ (e.symm (Φ α))
      have h2 : e.symm (Φ α) = α := by
        rw [show Φ α = e α from rfl, e.symm_apply_apply]
      rw [h2]
    -- the cap/cup identity, graded commutativity, and the hypothesis
    have hcap1 : Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) n γ (Φ α)
        = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) (n + n)
            ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj X) n n) α γ) c := by
      have hΦα : Φ α = (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj X) n n) α c := rfl
      rw [hΦα]
      exact Work.Cohomology.kronH_capPair_cup ℤ (TopCat.toSSet.obj X) n n α γ c
    have hcap2 : Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) n α (Φ γ)
        = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) (n + n)
            ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj X) n n) γ α) c := by
      have hΦγ : Φ γ = (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj X) n n) γ c := rfl
      rw [hΦγ]
      exact Work.Cohomology.kronH_capPair_cup ℤ (TopCat.toSSet.obj X) n n γ α c
    have hgc' : ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj X) n n) α) γ
        = (-1 : ℤ) ^ (n * n) •
            (((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj X) n n) γ) α) := by
      have hgc := Work.Cohomology.gradedComm ℤ (TopCat.toSSet.obj X) n n α γ
      rw [Subsingleton.elim (Nat.add_comm n n) rfl] at hgc
      exact hgc
    have hkey : χ (Φ α) = 0 := by
      rw [← hγ]
      calc Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) n γ (Φ α)
          = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) (n + n)
              (((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj X) n n) α) γ) c := hcap1
        _ = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) (n + n)
              ((-1 : ℤ) ^ (n * n) •
                (((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj X) n n) γ) α)) c := by
              rw [hgc']
        _ = ((-1 : ℤ) ^ (n * n) • Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) (n + n)
                (((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj X) n n) γ) α)) c := by
              rw [map_smul]
        _ = (-1 : ℤ) ^ (n * n) • (Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) (n + n)
                (((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj X) n n) γ) α) c) :=
              LinearMap.smul_apply _ _ _
        _ = (-1 : ℤ) ^ (n * n) • (Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) n α (Φ γ)) := by
              rw [hcap2]
        _ = 0 := by rw [hα (Φ γ), smul_zero]
    rw [h1, hkey]
  exact exists_nat_smul_eq_zero_of_mem_torsion
    (mem_torsion_of_forall_apply_eq_zero hPfin α hkill)

end

end Work.ThomBordism
