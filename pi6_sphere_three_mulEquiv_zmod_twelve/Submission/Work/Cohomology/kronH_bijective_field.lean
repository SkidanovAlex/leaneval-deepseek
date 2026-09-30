import Mathlib
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.kronH_capPair_cup
import Submission.Work.StemsB.FieldDualUCT
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Kronecker pairing is an isomorphism over a field

`Work.Cohomology.kronH F X n : Hⁿ(X;F) ⟶ (Hₙ(X;F) →ₗ[F] F)` is the Kronecker pairing of a
simplicial set with coefficients in `F`.  Over a *field* `F` no finiteness or freeness hypothesis
is needed: the pairing is bijective in every degree, because

* every functional on the cycles extends to the chains (over a field every subspace is a direct
  summand), which gives surjectivity, and
* a cocycle vanishing on all cycles annihilates the kernel of the differential, hence is pulled back
  from a functional on the chains below, hence is a coboundary; this gives injectivity.

This is the `F`-coefficient (field) counterpart of `Work.Cohomology.kronH_isIso` (integral
coefficients, free homology) and of `Work.Cohomology.kronH_kernel_eq_torsion` (integral
coefficients, the kernel is the torsion subgroup).
-/

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## The computation rule, over an arbitrary field -/

/-- **The Kronecker pairing on classes of cycles**, for coefficients in a field `F`: the pairing of
the class of a cochain cycle `w` with the class of a chain cycle `z` is the evaluation of the
underlying cochain of `w` on the underlying chain of `z`. -/
theorem kronH_cyc_apply_field (F : Type) [Field F] (X : SSet) (n : ℕ)
    (w : (cochainC F X).cycles n) (z : (chainC F X).cycles n) :
    kronH F X n ((cochainC F X).homologyπ n w) ((chainC F X).homologyπ n z) =
      cochainOfCycle F X n w ((chainC F X).iCycles n z) := by
  rw [← cohomologyClassOf_eq_homologyπ F X n w]
  exact kronH_apply F X ((cochainC F X).iCycles n w) (cochainDiff_iCycles F X n w) z

/-! ## The cycles are the kernel of the differential -/

/-- Every cycle (an element killed by the differential) of a homological complex of `F`-modules is
the image of an element of the cycles: the cycles are the kernel of the differential. -/
theorem exists_iCycles_eq_of_d_eq_zero (F : Type) [Field F]
    (C : ChainComplex (ModuleCat.{0,0} F) ℕ) (i j : ℕ)
    (hj : (ComplexShape.down ℕ).next i = j) (x : ↥(C.X i)) (hx : (C.d i j).hom x = 0) :
    ∃ z : ↥(C.cycles i), (C.iCycles i).hom z = x := by
  let k : ModuleCat.of F F ⟶ C.X i :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton F (↥(C.X i)) x)
  have hk : k ≫ C.d i j = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    show (C.d i j).hom (r • x) = 0
    rw [map_smul, hx, smul_zero]
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' (C.cyclesIsKernel i j hj) k hk
  refine ⟨l.hom 1, ?_⟩
  have h2 : (C.iCycles i).hom (l.hom 1) = (ModuleCat.Hom.hom k) 1 := by
    have h := congrArg (fun (g : ModuleCat.of F F ⟶ C.X i) => g.hom (1 : F)) hl
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rwa [Fork.ι_ofι] at h
  refine h2.trans ?_
  show (ModuleCat.Hom.hom k) 1 = x
  simp [k, LinearMap.toSpanSingleton_apply]

/-! ## The inclusion of the cycles splits over a field -/

/-- Over a field, the inclusion of the cycles `Zₙ ⊆ Cₙ` of a chain complex admits a retraction. -/
theorem exists_leftInverse_iCycles (F : Type) [Field F]
    (C : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    ∃ ρ : ↥(C.X n) →ₗ[F] ↥(C.cycles n), ρ ∘ₗ (C.iCycles n).hom = LinearMap.id := by
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective (C.iCycles n).hom
    (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective _).mp inferInstance))
  exact ⟨ρ, hρ⟩

/-! ## Coboundary criteria for the cochain complex

The two lemmas of this section move between the two presentations of the `F`-linear functionals on
the `m`-chains: as an element of the singular cochain complex `cochainC F X` and as a plain linear
map.  They are the only place where the definitional equality of the two presentations is used.
-/

/-- A functional on the `m`-chains, regarded as an element of the singular cochain complex
in degree `m`. -/
def cochainOfLin (F : Type) [Field F] (X : SSet) (m : ℕ)
    (β : ↥((chainC F X).X m) →ₗ[F] F) : ↥((cochainC F X).X m) := β

section FieldLinearAlgebra

set_option backward.isDefEq.respectTransparency false

/-- Over a field, a functional on the `(n+1)`-chains which vanishes on the kernel of the
differential is of the form `β ∘ d`: it is pulled back from a functional on the `n`-chains.
This is the linear-algebra content of the injectivity of the Kronecker pairing. -/
theorem exists_comp_d_eq_of_eq_zero_on_ker (F : Type) [Field F]
    (C : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ)
    (f : ↥(C.X (n+1)) →ₗ[F] F)
    (hfZ : ∀ x : ↥(C.X (n+1)), (C.d (n+1) n).hom x = 0 → f x = 0) :
    ∃ β : ↥(C.X n) →ₗ[F] F, β ∘ₗ (C.d (n+1) n).hom = f := by
  let Z := LinearMap.ker (C.d (n + 1) n).hom
  let fbar : (↥(C.X (n+1)) ⧸ Z) →ₗ[F] F := Z.liftQ f (by intro x hx; exact hfZ x hx)
  let e := (C.d (n + 1) n).hom.quotKerEquivRange
  let g : ↥(LinearMap.range (C.d (n + 1) n).hom) →ₗ[F] F := fbar.comp e.symm.toLinearMap
  obtain ⟨r, hr⟩ := Work.StemsB.exists_retraction_subspace_field F
    (LinearMap.range (C.d (n + 1) n).hom)
  refine ⟨g.comp r, ?_⟩
  ext x
  have h1 : r ((C.d (n + 1) n).hom x) = ⟨(C.d (n + 1) n).hom x, ⟨x, rfl⟩⟩ := by
    have h := LinearMap.congr_fun hr
      (⟨(C.d (n + 1) n).hom x, ⟨x, rfl⟩⟩ : ↥(LinearMap.range (C.d (n + 1) n).hom))
    simpa using h
  show g (r ((C.d (n + 1) n).hom x)) = f x
  rw [h1]
  show fbar (e.symm ⟨(C.d (n + 1) n).hom x, ⟨x, rfl⟩⟩) = f x
  rw [show e.symm ⟨(C.d (n + 1) n).hom x, ⟨x, rfl⟩⟩ = Z.mkQ x from
      LinearMap.quotKerEquivRange_symm_apply_image (C.d (n+1) n).hom x ⟨x, rfl⟩]
  show fbar (Z.mkQ x) = f x
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- The differential of the cochain complex, evaluated on `cochainOfLin β`, is the coboundary
of `β`: the composition of `β` with the differential of the chain complex. -/
theorem d_cochainOfLin (F : Type) [Field F] (X : SSet) (m : ℕ)
    (β : ↥((chainC F X).X m) →ₗ[F] F) :
    ((cochainC F X).d m (m + 1)).hom (cochainOfLin F X m β)
      = cochainOfLin F X (m + 1) (β ∘ₗ ((chainC F X).d (m + 1) m).hom) := by
  rw [SSetCochainComplex_d_apply F X m]
  rfl

/-- **A cycle whose underlying cochain kills the cycles is a coboundary.**  If the underlying
cochain of an `(m+1)`-cycle `w` of the singular cochain complex vanishes on the kernel of the
differential of the chain complex, then `w` has zero cohomology class: it is the coboundary of the
functional `β` on the `m`-chains produced by `exists_comp_d_eq_of_eq_zero_on_ker`. -/
theorem homologyπ_eq_zero_of_vanish_on_cycles (F : Type) [Field F] (X : SSet) (m : ℕ)
    (w : ↥((cochainC F X).cycles (m + 1)))
    (hfZ : ∀ x : ↥((chainC F X).X (m + 1)), ((chainC F X).d (m + 1) m).hom x = 0 →
      cochainOfCycle F X (m + 1) w x = 0) :
    ((cochainC F X).homologyπ (m + 1)).hom w = 0 := by
  obtain ⟨β, hβ⟩ := exists_comp_d_eq_of_eq_zero_on_ker F (chainC F X) m
    (cochainOfCycle F X (m + 1) w) hfZ
  have h : ((cochainC F X).iCycles (m + 1)).hom w
      = ((cochainC F X).d m (m + 1)).hom (cochainOfLin F X m β) := by
    rw [d_cochainOfLin F X m β, hβ]
    rfl
  exact homologyπ_eq_zero_of_d F X (m + 1) m w (cochainOfLin F X m β) h

end FieldLinearAlgebra

/-! ## Injectivity -/

/-- **Injectivity of the Kronecker pairing over a field.**  A cohomology class pairing to zero with
every homology class is zero: its representative cocycle is a coboundary. -/
theorem kronH_eq_zero_imp_eq_zero (F : Type) [Field F] (X : SSet) (n : ℕ)
    (a : ↥((cochainC F X).homology n)) (ha : kronH F X n a = 0) : a = 0 := by
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective ((cochainC F X).homologyπ n)).mp inferInstance a
  rw [← hw] at ha ⊢
  have hf : ∀ z : ↥((chainC F X).cycles n),
      cochainOfCycle F X n w (((chainC F X).iCycles n).hom z) = 0 := by
    intro z
    have h2 : kronH F X n ((cochainC F X).homologyπ n w)
        ((chainC F X).homologyπ n z) = 0 := LinearMap.congr_fun ha _
    rwa [kronH_cyc_apply_field F X n w z] at h2
  rcases n with _ | m
  · -- degree `0`: the cycles are all of `C₀`, so the cocycle itself vanishes
    have hf0 : cochainOfCycle F X 0 w = 0 := by
      ext x
      have hx : ((chainC F X).d 0 (0 - 1)).hom x = 0 := by
        rw [HomologicalComplex.shape (chainC F X) 0 0 (by simp [ComplexShape.down_Rel]),
          ModuleCat.hom_zero]
        rfl
      obtain ⟨z, hz⟩ :=
        exists_iCycles_eq_of_d_eq_zero F (chainC F X) 0 (0 - 1) (down_next 0) x hx
      rw [← hz]
      exact hf z
    have hw0 : w = 0 := by
      apply iCycles_injective F X 0
      rw [map_zero]
      change cochainOfCycle F X 0 w = 0
      exact hf0
    rw [hw0, map_zero]
  · -- positive degree: the coboundary criterion
    have hfZ : ∀ x : ↥((chainC F X).X (m + 1)),
        ((chainC F X).d (m + 1) m).hom x = 0 → cochainOfCycle F X (m + 1) w x = 0 := by
      intro x hx
      obtain ⟨z, hz⟩ := exists_iCycles_eq_of_d_eq_zero F (chainC F X) (m + 1) m
        (by simpa only [Nat.add_sub_cancel] using down_next (m + 1)) x hx
      rw [← hz]
      exact hf z
    exact homologyπ_eq_zero_of_vanish_on_cycles F X m w hfZ

/-- The Kronecker pairing over a field is injective. -/
theorem kronH_injective_field (F : Type) [Field F] (X : SSet) (n : ℕ) :
    Function.Injective (kronH F X n) := by
  intro a b hab
  have h : a - b = 0 :=
    kronH_eq_zero_imp_eq_zero F X n (a - b) (by rw [map_sub, hab, sub_self])
  exact sub_eq_zero.mp h

/-! ## Surjectivity -/

/-- **Surjectivity of the Kronecker pairing over a field.**  Every functional on the homology is
represented by a cocycle: over a field a functional on the cycles extends to the chains, and the
resulting cochain is a cocycle because it vanishes on boundaries. -/
theorem kronH_surjective_field (F : Type) [Field F] (X : SSet) (n : ℕ) :
    Function.Surjective (kronH F X n) := by
  intro φ
  obtain ⟨ρ, hρ⟩ := exists_leftInverse_iCycles F (chainC F X) n
  let ψ : ↥((chainC F X).cycles n) →ₗ[F] F := φ.comp ((chainC F X).homologyπ n).hom
  let α : ↥((chainC F X).X n) →ₗ[F] F := ψ.comp ρ
  have hρα : ∀ z : ↥((chainC F X).cycles n), ρ (((chainC F X).iCycles n).hom z) = z := by
    intro z
    have h := LinearMap.congr_fun hρ z
    simpa using h
  have hα : cochainDiff F X α = 0 := by
    apply LinearMap.ext
    intro y
    show α (((chainC F X).d (n + 1) n).hom y) = 0
    have hd : ((chainC F X).d (n + 1) n).hom y
        = ((chainC F X).iCycles n).hom (((chainC F X).toCycles (n + 1) n) y) := by
      have h := congrArg (fun (g : (chainC F X).X (n+1) ⟶ (chainC F X).X n) => g.hom y)
        (HomologicalComplex.toCycles_i (chainC F X) (n+1) n)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm
    rw [hd]
    show ψ (ρ (((chainC F X).iCycles n).hom (((chainC F X).toCycles (n+1) n) y))) = 0
    rw [hρα]
    show φ (((chainC F X).homologyπ n).hom (((chainC F X).toCycles (n+1) n) y)) = 0
    have hb : ((chainC F X).homologyπ n).hom (((chainC F X).toCycles (n+1) n) y) = 0 := by
      have h := congrArg (fun (g : (chainC F X).X (n+1) ⟶ (chainC F X).homology n) => g.hom y)
        (HomologicalComplex.toCycles_comp_homologyπ (chainC F X) (n+1) n)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h
    rw [hb, map_zero]
  refine ⟨cohomologyClassOf F X α hα, ?_⟩
  apply LinearMap.ext
  intro c
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective ((chainC F X).homologyπ n)).mp inferInstance c
  rw [← hz, kronH_apply F X α hα z]
  show α (((chainC F X).iCycles n).hom z) = φ (((chainC F X).homologyπ n).hom z)
  show ψ (ρ (((chainC F X).iCycles n).hom z)) = φ (((chainC F X).homologyπ n).hom z)
  rw [hρα z]
  rfl

/-! ## The main theorem -/

theorem kronH_bijective_field (F : Type) [Field F] (X : SSet) (n : ℕ) :
    Function.Bijective (Work.Cohomology.kronH F X n) :=
  ⟨kronH_injective_field F X n, kronH_surjective_field F X n⟩

end

end Work.Cohomology
