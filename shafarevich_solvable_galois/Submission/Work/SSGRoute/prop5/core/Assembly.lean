import Mathlib
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
import Submission.Work.SSGRoute.prop5.magnusGroupPart
import Submission.Work.SSGRoute.prop5.magnus_unitCongr_isolated
import Submission.Work.SSGRoute.prop5.magLead_mem_nestedImage
import Submission.Work.SSGRoute.prop5.coreGraded
import Submission.Work.SSGRoute.prop5.coreLieBar
import Submission.Work.SSGRoute.prop5.gradedCast
import Submission.Work.SSGRoute.prop5.bracketBar_axioms
import Submission.Work.SSGRoute.prop5.witt.Basic
import Submission.Work.SSGRoute.prop5.witt.Vocab
import Submission.Work.SSGRoute.prop5.witt.Assembly
import Submission.Work.SSGRoute.prop5.witt.Swap
import Submission.Work.SSGRoute.prop5.witt.hall_foliage_lt_right
import Submission.Work.SSGRoute.prop5.witt.hall_spanning
import Submission.Work.SSGRoute.prop5.witt.leading_term_coeff
import Submission.Work.SSGRoute.prop5.core.Defs
import Submission.Work.SSGRoute.prop5.core.gen_span
import Submission.Work.SSGRoute.prop5.core.magLeadLemmas
import Submission.Work.SSGRoute.prop5.core.relations_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Assembly of the Magnus core theorem

This file proves the "instance" form of the hard half of the Magnus embedding theorem:
if `y ∈ γ_{n+1}` and the Magnus image of `y` is congruent to `1` modulo the degree `n+2` part of
the truncated free associative algebra, then `y ∈ γ_{n+2}`.
-/

noncomputable section

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Work.SSGRoute.prop5
namespace core

variable {X : Type*}

/-- `Gam X q` is the same subgroup as `(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries q`. -/
theorem mem_Gam_iff {q : ℕ} {z : FreeGroup X} :
    z ∈ Gam X q ↔ z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries q := by
  rw [Gam, graded.Gam]

theorem monGrp_mem_Gam' (c : Magma X) :
    monGrp X c ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (Magma.size c - 1) :=
  mem_Gam_iff.mp (monGrp_mem_Gam c)

/-! ## Witt's theorem in the form needed here -/

theorem hswap_hall {X : Type} [LinearOrder X] {a b : Magma X} (h : IsHall (Magma.mul a b)) :
    Magma.foliage a ++ Magma.foliage b < Magma.foliage b ++ Magma.foliage a :=
  swap_hall_of_crux (fun _ _ hh => witt.hall_foliage_lt_right hh) h

theorem hspan_hall {X : Type} [LinearOrder X] (v : Magma X) : monLie X v ∈ Sp X :=
  witt.hall_spanning (monLie X) (fun _ _ => rfl) v

theorem hlead_hall {X : Type} [LinearOrder X] (c : Magma X) (hc : IsHall c) :
    coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
      ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0 :=
  witt.leading_term_coeff hc (fun a b hab => hswap_hall hab)

theorem fL_injective_ordered {X : Type} [LinearOrder X] : Function.Injective (fL X) := by
  intro a b hab
  exact fL_injective (X := X) hspan_hall hlead_hall
    (fun a b ha hb h => witt.hall_foliage_injective_aux ha hb h) hab

/-- Witt's theorem: the canonical map from the free Lie ring to the free associative ring is
injective. -/
theorem fL_injective_all (X : Type) : Function.Injective (fL X) := by
  classical
  obtain ⟨instLO, -⟩ := exists_wellFoundedLT X
  letI := instLO
  exact fL_injective_ordered

/-- The canonical `ℤ`-linear map from the free Lie ring on `X` into `FreeAssoc X`. -/
noncomputable def Psi (X : Type) : FreeLieAlgebra ℤ X →ₗ[ℤ] FreeAssoc X :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra ℤ X ≃ₐ[ℤ] FreeAssoc X).toLinearEquiv.toLinearMap.comp
    (fL X).toLinearMap

/-- `fL` sends the bracket evaluation of a tree to the commutator evaluation.  (The version in
`witt/Assembly.lean` is stated under a `LinearOrder X` hypothesis; this one is order free.) -/
theorem fL_monLie' (X : Type) (c : Magma X) : fL X (monLie X c) = monBrkA X c := by
  induction c with
  | gen x => exact FreeLieAlgebra.lift_of_apply _ x
  | mul a b iha ihb =>
      rw [monLie_mul, monBrkA_mul, LieHom.map_lie, iha, ihb, LieRing.of_associative_ring_bracket]

theorem Psi_monLie (X : Type) (c : Magma X) : Psi X (monLie X c) = monBrk X c := by
  show (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra ℤ X ≃ₐ[ℤ] FreeAssoc X)
    ((fL X) (monLie X c)) = monBrk X c
  rw [fL_monLie', equivMonoidAlgebra_monBrkA]

theorem Psi_injective (X : Type) : Function.Injective (Psi X) := by
  intro a b hab
  have h : (fL X) a = (fL X) b := by
    have h2 := congrArg (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm) hab
    change (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm)
        ((FreeAlgebra.equivMonoidAlgebraFreeMonoid) ((fL X) a)) =
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm)
        ((FreeAlgebra.equivMonoidAlgebraFreeMonoid) ((fL X) b)) at h2
    simpa using h2
  exact fL_injective_all X h

/-- Linearity of a linear combination of a family under an additive map. -/
theorem linearCombination_map {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (f : M →+ N)
    (g : ι → M) (μ : ι →₀ ℤ) :
    f (Finsupp.linearCombination ℤ g μ)
      = Finsupp.linearCombination ℤ (fun i => f (g i)) μ := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum,
    map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_zsmul])

theorem linearCombination_map_linear {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (f : M →ₗ[ℤ] N) (g : ι → M) (μ : ι →₀ ℤ) :
    f (Finsupp.linearCombination ℤ g μ)
      = Finsupp.linearCombination ℤ (fun i => f (g i)) μ :=
  linearCombination_map f.toAddMonoidHom g μ

theorem linearCombination_congr_left {ι M : Type*} [AddCommGroup M] {g g' : ι → M}
    (h : g = g') (μ : ι →₀ ℤ) :
    Finsupp.linearCombination ℤ g μ = Finsupp.linearCombination ℤ g' μ := by rw [h]

/-! ## The Magnus leading term as a map on the graded piece -/

/-- The Magnus leading term, as a monoid homomorphism `γ_k/γ_{k+1} →* (1 + filq (k+1) k)`. -/
noncomputable def MbarMul (X : Type*) (k : ℕ) (hk : 1 ≤ k) :
    graded.GLam (G := FreeGroup X) (k - 1) →* Multiplicative (↥(filq X (k + 1) k)) :=
  QuotientGroup.lift ((Gam X (k - 1 + 1)).subgroupOf (Gam X (k - 1)))
    (MonoidHom.mk' (fun u : Gam X (k - 1) =>
      Multiplicative.ofAdd (⟨magLead (k + 1) (u : FreeGroup X),
        magLead_mem_filq (X := X) (k + 1) k hk (by omega) (mem_Gam_iff.mp u.2)⟩ :
          ↥(filq X (k + 1) k)))
      (by
        intro a b
        apply Multiplicative.ext
        apply Subtype.ext
        exact magLead_mul_mem (X := X) k hk a.2 b.2))
    (by
      intro u hu
      apply Multiplicative.ext
      apply Subtype.ext
      have hu1 : (u : FreeGroup X) ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries
          (k - 1 + 1) := mem_Gam_iff.mp ((Subgroup.mem_subgroupOf).1 hu)
      have hu2 : (u : FreeGroup X) ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries k := by
        rwa [Nat.sub_add_cancel hk] at hu1
      exact magLead_eq_zero_of_mem_succ (X := X) k hu2)

/-- The Magnus leading term, as an additive map on the graded piece `Λ_{k-1} = γ_k/γ_{k+1}`. -/
noncomputable def Mbar (X : Type*) (k : ℕ) (hk : 1 ≤ k) :
    Lam X (k - 1) →+ ↥(filq X (k + 1) k) where
  toFun z := Multiplicative.toAdd (MbarMul X k hk (Additive.toMul z))
  map_zero' := by
    show Multiplicative.toAdd (MbarMul X k hk 1) = 0
    rw [map_one]
    rfl
  map_add' a b := by
    show Multiplicative.toAdd (MbarMul X k hk (Additive.toMul (a + b))) =
      Multiplicative.toAdd (MbarMul X k hk (Additive.toMul a)) +
        Multiplicative.toAdd (MbarMul X k hk (Additive.toMul b))
    rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl, map_mul]
    rfl

theorem Mbar_cls (X : Type*) (k : ℕ) (hk : 1 ≤ k) (u : Gam X (k - 1)) :
    Mbar X k hk (cls X (k - 1) u) =
      ⟨magLead (k + 1) (u : FreeGroup X),
        magLead_mem_filq (X := X) (k + 1) k hk (by omega) (mem_Gam_iff.mp u.2)⟩ := rfl

/-- The Magnus leading term, pushed into the truncated free associative algebra. -/
noncomputable def MbarQ (X : Type*) (k : ℕ) (hk : 1 ≤ k) :
    Lam X (k - 1) →+ (FreeAssoc X ⧸ fil X (k + 1)) :=
  ((Submodule.subtype (filq X (k + 1) k)).toAddMonoidHom).comp (Mbar X k hk)

theorem MbarQ_cls (X : Type*) (k : ℕ) (hk : 1 ≤ k) (u : Gam X (k - 1)) :
    MbarQ X k hk (cls X (k - 1) u) = magLead (k + 1) (u : FreeGroup X) := by
  show (Submodule.subtype (filq X (k + 1) k)) (Mbar X k hk (cls X (k - 1) u)) = _
  rw [Mbar_cls X k hk u]
  rfl

/-! ## The degree-`k` part of the truncated algebra -/

/-- `monBrk X c` lies in the degree-`size c` part of `FreeAssoc X`. -/
theorem monBrk_mem_wordSpan (c : Magma X) : monBrk X c ∈ wordSpan (X := X) (Magma.size c) := by
  rw [mem_wordSpan_iff]
  intro w hw
  by_contra hc
  exact hw (monBrk_coeff_length c w hc)

/-- `monBrk X c` lies in the degree-`k` part whenever `size c = k`. -/
theorem monBrk_mem_wordSpan_of_size (c : Magma X) {k : ℕ} (hk : Magma.size c = k) :
    monBrk X c ∈ wordSpan (X := X) k := by
  rw [mem_wordSpan_iff]
  intro w hw
  by_contra hc
  exact hw (hk ▸ monBrk_coeff_length c w hc)

/-- A `ℤ`-linear combination of bracketed monomials of trees of size `k` lies in the degree-`k`
part of `FreeAssoc X`. -/
theorem lincomb_monBrk_mem_wordSpan (k : ℕ) (μ : TreeIdx X k →₀ ℤ) :
    Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monBrk X c.1) μ ∈ wordSpan (X := X) k := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ (monBrk_mem_wordSpan_of_size c.1 c.2))

/-- An element of the degree-`k` part of `FreeAssoc X` which lies in `fil X (k+1)` is zero. -/
theorem eq_zero_of_mem_wordSpan_of_mem_fil {k : ℕ} {a : FreeAssoc X}
    (h1 : a ∈ wordSpan (X := X) k) (h2 : a ∈ fil X (k + 1)) : a = 0 :=
  calc a = degPart (X := X) k a := (degPart_eq_self_of_mem_wordSpan h1).symm
    _ = 0 := degPart_eq_zero_of_mem_fil h2 (by omega)

/-- The bracketed monomial of a tree of size `k` is the Magnus leading term of the corresponding
commutator monomial. -/
theorem magLead_monGrp_eq (k : ℕ) (c : TreeIdx X k) :
    magLead (k + 1) (monGrp X c.1) =
      Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1) := by
  have h1 := magLead_monGrp_sub_mem (X := X) (k + 1) c.1 (by rw [c.2])
  rw [show Magma.size c.1 + 1 = k + 1 from by rw [c.2]] at h1
  have h2 : filq X (k + 1) (k + 1) = ⊥ := filq_self_eq_bot' (X := X) (k + 1)
  rw [h2, Submodule.mem_bot] at h1
  exact sub_eq_zero.mp h1

/-! ## The assembly -/

theorem magnusCore_aux (X : Type) (k : ℕ) (hk : 1 ≤ k) (y : FreeGroup X)
    (hy : y ∈ Gam X (k - 1)) (hzero : magLead (k + 1) y = 0) :
    y ∈ Gam X k := by
  classical
  obtain ⟨μ, hμ⟩ := gen_span X k hk y hy
  -- the values of the two sums
  set gv : TreeIdx X k → ↥(filq X (k + 1) k) := fun c =>
    ⟨magLead (k + 1) (monGrp X c.1),
      magLead_mem_filq (X := X) (k + 1) k hk (by omega)
        (by simpa [c.2] using monGrp_mem_Gam' (X := X) c.1)⟩ with hgv
  set qv : TreeIdx X k → FreeAssoc X ⧸ fil X (k + 1) :=
    fun c => magLead (k + 1) (monGrp X c.1) with hqv
  have hqv' : ∀ c, (gv c : FreeAssoc X ⧸ fil X (k + 1)) = qv c := fun c => rfl
  -- the Magnus leading term of `y` is the image in `FreeAssoc X ⧸ fil X (k+1)` of the Lie element
  have hlead : magLead (k + 1) y
      = Ideal.Quotient.mk (fil X (k + 1))
        (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monBrk X c.1) μ) := by
    have hM : MbarQ X k hk (cls X (k - 1) ⟨y, hy⟩) = MbarQ X k hk (treeToLam X k μ) := by
      rw [hμ]
    rw [MbarQ_cls X k hk ⟨y, hy⟩] at hM
    have hR : MbarQ X k hk (treeToLam X k μ)
        = Finsupp.linearCombination ℤ (fun c : TreeIdx X k => magLead (k + 1) (monGrp X c.1)) μ := by
      rw [show treeToLam X k μ = Finsupp.linearCombination ℤ (treeClOf X k) μ from rfl,
        linearCombination_map (MbarQ X k hk) (treeClOf X k) μ]
      exact linearCombination_congr_left (funext (fun c => by
        rw [treeClOf, MbarQ_cls X k hk])) μ
    rw [hR] at hM
    rw [hM]
    rw [show Ideal.Quotient.mk (fil X (k + 1))
        (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monBrk X c.1) μ)
        = Finsupp.linearCombination ℤ (fun c : TreeIdx X k =>
            Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1)) μ from
      linearCombination_map ((Ideal.Quotient.mk (fil X (k + 1))).toAddMonoidHom)
        (fun c : TreeIdx X k => monBrk X c.1) μ]
    exact linearCombination_congr_left (funext (fun c =>
      magLead_monGrp_eq (X := X) k c)) μ
  have hmk : Ideal.Quotient.mk (fil X (k + 1))
      (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monBrk X c.1) μ) = 0 := by
    rw [← hlead]; exact hzero
  have hsum0 : Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monBrk X c.1) μ = 0 :=
    eq_zero_of_mem_wordSpan_of_mem_fil (lincomb_monBrk_mem_wordSpan k μ)
      (Ideal.Quotient.eq_zero_iff_mem.mp hmk)
  -- hence the Lie element is killed by the (injective) canonical map into `FreeAssoc X`
  have hz : Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monLie X c.1) μ = 0 := by
    apply Psi_injective X
    rw [map_zero]
    change (Psi X).toAddMonoidHom
      (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monLie X c.1) μ) = 0
    rw [linearCombination_map (Psi X).toAddMonoidHom (fun c : TreeIdx X k => monLie X c.1) μ]
    rw [linearCombination_congr_left (funext (fun c => by
      show (Psi X).toAddMonoidHom (monLie X c.1) = monBrk X c.1
      exact Psi_monLie X c.1)) μ, hsum0]
  -- the class of `y` vanishes
  have hcls0 : Finsupp.linearCombination ℤ (fun c : TreeIdx X k => cls X (k - 1)
      ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam (X := X) c.1⟩) μ = 0 := by
    have hz' : rzPsi X (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monLie X c.1) μ)
        = 0 := by rw [hz]; simp
    have hcomp : rzPsi X (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monLie X c.1) μ)
        = graded.lofL (G := FreeGroup X) (k - 1)
          (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => cls X (k - 1)
            ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam (X := X) c.1⟩) μ) := by
      rw [show (rzPsi X) (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monLie X c.1) μ)
          = (rzPsi X).toLinearMap
            (Finsupp.linearCombination ℤ (fun c : TreeIdx X k => monLie X c.1) μ) from rfl]
      rw [linearCombination_map_linear (rzPsi X).toLinearMap
        (fun c : TreeIdx X k => monLie X c.1) μ]
      rw [linearCombination_congr_left (funext (fun c => by
        show (rzPsi X).toLinearMap (monLie X c.1) = graded.lofL (G := FreeGroup X) (k - 1)
          (cls X (k - 1) ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam (X := X) c.1⟩)
        exact rz_psi_monLie_of_size X k (c.1) (c.2))) μ]
      exact (linearCombination_map
        ((DirectSum.lof ℤ ℕ (fun i => graded.LamAdd (G := FreeGroup X) i) (k - 1)).toAddMonoidHom)
        (fun c : TreeIdx X k => cls X (k - 1)
          ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam (X := X) c.1⟩) μ).symm
    rw [hcomp] at hz'
    exact rz_lofL_injective (FreeGroup X) (k - 1) (by simpa using hz')
  -- conclude
  have hfinal : cls X (k - 1) ⟨y, hy⟩ = 0 := by
    have h2 : treeToLam X k μ = Finsupp.linearCombination ℤ (fun c : TreeIdx X k => cls X (k - 1)
        ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam (X := X) c.1⟩) μ := by
      rw [show treeToLam X k μ = Finsupp.linearCombination ℤ (treeClOf X k) μ from rfl]
      exact linearCombination_congr_left (funext (fun c => by rw [treeClOf])) μ
    rw [← hμ, h2, hcls0]
  have hmemk := (cls_eq_zero_iff (X := X) (q := k - 1) (x := ⟨y, hy⟩)).1 hfinal
  simpa [Nat.sub_add_cancel hk] using hmemk

end core
end Work.SSGRoute.prop5
