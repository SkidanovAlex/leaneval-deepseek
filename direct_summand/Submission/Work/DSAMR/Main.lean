import Submission.Work.DSAMR.Defs
import Submission.Work.DSAMR.exists_coaug_lift
import Submission.Work.DSAMR.almostAcycZ_extend
import Submission.Work.DSAMR.rho_f_zero_unit
import Submission.Work.DSAMR.rho_f_zero_d
import Submission.Work.DSAMR.modSplitA_of_forall_pow
import Submission.Work.DSAM3.Api

/-!
# DSAMR: `ModSplit` from almost acyclicity (node **AMR** of the MIX2 subtree)

Area owner: curric-46 DSAMR.  Deliverable: `DSMap.Mix2.modSplit_of_almostAcyc_proved`, whose type is
identical to the frozen `DSMap.Mix2.modSplit_of_almostAcyc`
(`Submission/Work/DSMap/Mix2.lean`, `sources/dsmap/direct_summand_mix2.md`, node AMR), with no unproved
steps and axiom-clean.

## The result

Let `ψ : A →+* W` be a ring map, `I ⊆ W` an ideal, `ϖ : ℕ → W` a compatible tower of `p`-th roots
(`ϖ (k+1) ^ p = ϖ k`), `K` a cochain complex of `W`-modules concentrated in degrees `≥ 0` with a
coaugmentation `e : W → K⁰` which is `I`-almost acyclic w.r.t. `ϖ` (`DSMap.Mix2.AlmostAcyc`), `P` a
bounded-above complex of finite free `A`-modules, `ε : A → P⁰` a cocycle and `ρ : P → K` a chain map
with `ρ⁰ (ε 1) = e 1`.  Then `ModSplit P ε ψ I (ϖ k)` holds for every `k`.

## Proof

`t x := mk I (ϖ j * h⁰ x)`, where `h⁰ : P⁰ → W` is the degree-zero component of an almost
null-homotopy of `ρ` (`Work.DSAMR.exists_coaug_lift`): since `P` is a bounded-above complex of free
modules it is `K`-projective, and a chain map into an `I`-almost acyclic complex is null-homotopic
after multiplying by a loss `ϖ j ^ L` depending only on the number of degrees of `P`
(descending induction on the degrees, one application of the almost acyclicity per degree).  Then

* `t ∘ d⁻¹ = 0`: the relation at `x = d⁻¹ y` gives `e (h⁰ (d⁻¹ y)) ∈ I · K⁰` (using
  `ρ⁰ ∘ d⁻¹ = 0`, `Work.DSAMR.rho_f_zero_d`), and clause (1) of the almost acyclicity gives
  `ϖ j * h⁰ (d⁻¹ y) ∈ I`;
* `t (ε 1) = mk (ϖ j ^ (L+1))`: the relation at `x = ε 1` gives `e (ϖ j ^ L - h⁰ (ε 1)) ∈ I · K⁰`,
  and clause (1) gives `ϖ j * (ϖ j ^ L - h⁰ (ε 1)) ∈ I`.

So `ModSplitA P ε ψ I (ϖ j ^ (L+1))` for **every** `j`.  The tower endgame
(`Work.DSAMR.modSplitA_of_forall_pow`) then removes the loss `L` completely: taking `j = k + L` and
scaling the value by `ϖ j ^ (p^L - L)` (AM1, `Work.DSAM3.modSplitA_mul`) yields the value
`ϖ (k+L) ^ (p^L) = ϖ k`.  Finally `Work.DSAM3.modSplit_iff_ModSplitA` converts back to the frozen
`ModSplit`.

The bridge from the frozen `ℕ`-indexed hypothesis to the `ℤ`-indexed form in which the argument runs
is `Work.DSAMR.almostAcycZ_extend`; the compatibility of `ρ` with the units is
`Work.DSAMR.rho_f_zero_unit`.
-/

open CategoryTheory Limits

namespace Work.DSAMR

universe u

/-- **AMR in the `A`-linear form** (`Work.DSAM3.ModSplitA`) for a `ℤ`-indexed almost acyclic
coaugmented complex: this is the mathematical content of the node, with the frozen statement's
`K.extend`/`unitA` bookkeeping already resolved (`hρ` and `hzero` are its element-level content,
produced by `Work.DSAMR.rho_f_zero_unit` and `Work.DSAMR.rho_f_zero_d`). -/
theorem modSplitA_of_almostAcycZ {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W)
    (p : ℕ) (hp : 1 < p) (ϖ : ℕ → W) (hϖ : ∀ k, ϖ (k + 1) ^ p = ϖ k) (I : Ideal W)
    {K : CochainComplex (ModuleCat.{u} W) ℤ} (e : ModuleCat.of W W ⟶ K.X 0)
    (hK : AlmostAcycZ ϖ I K e)
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (hP : DSMap.Mix.IsBddFinFree P)
    (ε : ModuleCat.of A A ⟶ P.X 0) (hε : (P.d 0 1).hom (ε.hom 1) = 0)
    (ρ : P ⟶ ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (hρ : ((ρ.f 0) (ε.hom (1 : A)) : K.X 0) = e.hom (1 : W))
    (hzero : ∀ y : P.X (-1), ((ρ.f 0) ((P.d (-1) 0).hom y) : K.X 0) = 0) :
    ∀ k : ℕ, DSAM3.ModSplitA P ε ψ I (ϖ k) := by
  letI : Algebra A W := ψ.toAlgebra
  obtain ⟨L, hL⟩ := exists_coaug_lift ψ ϖ I e hK hP ρ
  refine modSplitA_of_forall_pow ψ p hp ϖ hϖ I P ε (L + 1) (fun j => ?_)
  obtain ⟨h, hh⟩ := hL j
  let hW : P.X 0 →ₗ[A] W := h.hom
  have hh' : ∀ x : P.X 0, (P.d 0 1).hom x = 0 →
      ϖ j ^ L • (show K.X 0 from (ρ.f 0) x) -
          e.hom (show W from h x) ∈ I • (⊤ : Submodule W (K.X 0)) :=
    fun x hx => hh x hx
  let m : W →ₗ[A] W :=
    { toFun := fun y => ϖ j * y
      map_add' := fun y z => by ring
      map_smul' := fun a y => by
        show ϖ j * (a • y) = a • (ϖ j * y)
        rw [Algebra.smul_def, Algebra.smul_def]
        ring }
  let t : P.X 0 →ₗ[A] W ⧸ I := (Ideal.Quotient.mkₐ (R₁ := A) I).toLinearMap.comp (m.comp hW)
  have ht : ∀ x : P.X 0, t x = Ideal.Quotient.mk I (ϖ j * hW x) := by
    intro x
    simp [t, m]
  refine ⟨t, ?_, ?_⟩
  · ext y
    rw [LinearMap.comp_apply, LinearMap.zero_apply, ht]
    have hcomp : (P.d 0 1).hom ((P.d (-1) 0).hom y) = 0 := by
      have hdd := HomologicalComplex.d_comp_d P (-1) 0 1
      have h2 := congrArg (fun f : P.X (-1) ⟶ P.X 1 => f.hom y) hdd
      simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h2
    have h0 := hh' ((P.d (-1) 0).hom y) hcomp
    have h0c : ϖ j ^ L • (0 : K.X 0) -
        e.hom (show W from h ((P.d (-1) 0).hom y)) ∈ I • (⊤ : Submodule W (K.X 0)) := by
      have hthis := h0
      rw [show (show K.X 0 from (ρ.f 0) ((P.d (-1) 0).hom y)) = (0 : K.X 0) from hzero y]
        at hthis
      first | dsimp only at hthis | simp only [] at hthis
      simpa using hthis
    have hmem : e.hom (show W from h ((P.d (-1) 0).hom y)) ∈ I • (⊤ : Submodule W (K.X 0)) := by
      have h2 : -(e.hom (show W from h ((P.d (-1) 0).hom y))) ∈
          I • (⊤ : Submodule W (K.X 0)) := by
        simpa using h0c
      simpa using neg_mem h2
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hK.1 _ hmem j)
  · have h0 := hh' (ε.hom 1) hε
    have h0b : ϖ j ^ L • (e.hom (1 : W)) - e.hom (show W from h (ε.hom 1)) ∈
        I • (⊤ : Submodule W (K.X 0)) := by
      have hthis := h0
      rw [show (show K.X 0 from (ρ.f 0) (ε.hom 1)) = e.hom (1 : W) from hρ] at hthis
      first | dsimp only at hthis | simp only [] at hthis
      simpa using hthis
    have h3 : e.hom ((ϖ j ^ L : W) * 1 - (show W from h (ε.hom 1))) ∈
        I • (⊤ : Submodule W (K.X 0)) := by
      have hthis := h0b
      rw [← map_smul, ← map_sub] at hthis
      simpa using hthis
    have hI : ϖ j * ((ϖ j ^ L : W) * 1 - (show W from h (ε.hom 1))) ∈ I := hK.1 _ h3 j
    have hEq : -(ϖ j * ((ϖ j ^ L : W) * 1 - (show W from h (ε.hom 1)))) =
        ϖ j * (show W from h (ε.hom 1)) - ϖ j ^ (L + 1) := by
      rw [pow_succ]
      ring
    have hI' : ϖ j * (show W from h (ε.hom 1)) - ϖ j ^ (L + 1) ∈ I := by
      have := neg_mem hI
      rwa [hEq] at this
    rw [ht]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hI'

end Work.DSAMR

namespace DSMap.Mix2

universe a

open CategoryTheory Limits
open DSMap DSMap.Mix

/-- **AMR**, the frozen interface `DSMap.Mix2.modSplit_of_almostAcyc`, proved. -/
theorem modSplit_of_almostAcyc_proved (p : ℕ) [Fact p.Prime] {A W : Type a} [CommRing A]
    [CommRing W] (ψ : A →+* W) (ϖ : ℕ → W) (hϖ : ∀ k, ϖ (k + 1) ^ p = ϖ k) (I : Ideal W)
    (K : CochainComplex (ModuleCat.{a} W) ℕ) (eK : ModuleCat.of W W ⟶ K.X 0)
    (hK : AlmostAcyc ϖ I K eK) (P : CochainComplex (ModuleCat.{a} A) ℤ) (hP : IsBddFinFree P)
    (ε : ModuleCat.of A A ⟶ P.X 0) (hε : ∀ k, ε ≫ P.d 0 k = 0)
    (ρ : P ⟶ ((ModuleCat.restrictScalars ψ).mapHomologicalComplex _).obj
      (K.extend ComplexShape.embeddingUpNat))
    (hρ : ε ≫ ρ.f 0 ≫ (ModuleCat.restrictScalars ψ).map
      (K.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
        unitA ψ ≫ (ModuleCat.restrictScalars ψ).map eK) :
    ∀ k, ModSplit P ε ψ I (ϖ k) := by
  intro k
  refine (Work.DSAM3.modSplit_iff_ModSplitA P ε ψ I (ϖ k)).mpr ?_
  have hK' := Work.DSAMR.almostAcycZ_extend ϖ I K eK hK
  have hρ' := Work.DSAMR.rho_f_zero_unit ψ K eK P ε ρ hρ
  have hz := Work.DSAMR.rho_f_zero_d ψ K P ρ
  have hε' : (P.d 0 1).hom (ε.hom 1) = 0 := by
    have h2 : (ε ≫ P.d 0 1).hom (1 : A) = 0 := by rw [hε 1]; rfl
    rwa [ModuleCat.comp_apply] at h2
  exact Work.DSAMR.modSplitA_of_almostAcycZ ψ p (Fact.out : p.Prime).one_lt ϖ hϖ I _
    hK' hP ε hε' ρ hρ' hz k

/-- The proved theorem has exactly the type of the frozen (sorried) `modSplit_of_almostAcyc`. -/
example : @DSMap.Mix2.modSplit_of_almostAcyc_proved =
    @DSMap.Mix2.modSplit_of_almostAcyc := rfl

end DSMap.Mix2
