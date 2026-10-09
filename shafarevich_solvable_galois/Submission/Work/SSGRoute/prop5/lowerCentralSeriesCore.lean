/-
# The core of the Magnus embedding theorem, assembled

The "core" statement used to prove `lowerCentralSeries_torsionFree` is the hard half of the Magnus
embedding theorem:

if `y ∈ γ_k` (Mathlib: `(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k-1)`) and the Magnus
leading term of `y` vanishes modulo the degree `k+1` part of the truncated free associative algebra
`FreeAssoc X ⧸ fil X (k+1)`, then `y ∈ γ_{k+1}`.

## Route

Let `F = FreeGroup X`, `A = FreeAssoc X = ℤ[FreeMonoid X]` and `Λ_q = γ_q/γ_{q+1}` (Mathlib
indexing).  For a binary tree `c` let `monGrp c ∈ F` be the group commutator monomial, `monLie c`
the Lie bracket monomial in `L = FreeLieAlgebra ℤ X` and `monBrk c` the ring commutator monomial
in `A`.

* `core.gen_span` writes the class of `y ∈ γ_k` in `Λ_{k-1}` as a `ℤ`-linear combination
  `Σ_c μ_c [monGrp c]` of the commutator monomials of the trees of size `k`.
* The Magnus leading term is additive on `γ_k` (modulo the degree-`k` piece), so it factors through
  the class map; this gives the homomorphism `Mbar : Λ_{k-1} → (filq X (k+1) k, +)` whose
  compositition with the inclusion of `filq X (k+1) k` is `Theta`.  Hence the *vanishing* of the
  leading term of `y` says that `Σ_c μ_c monBrk c ∈ fil X (k+1)`.
* Each `monBrk c` is a combination of words of length exactly `size c = k`, so `Σ_c μ_c monBrk c`
  lies in the degree-`k` part `wordSpan X k`; intersecting with `fil X (k+1)` gives zero.
* Transporting along `FreeAlgebra.equivMonoidAlgebraFreeMonoid` and applying Witt's theorem
  (`Phi_injective`, the faithfulness of the free Lie ring) yields `Σ_c μ_c monLie c = 0` in `L`.
* The graded Lie map `core.rzPsi` sends `monLie c` to the class of `monGrp c` in `Λ_{k-1}`; since
  the inclusions `Λ_{k-1} → Λbar` are injective (`core.rz_lofL_injective`) this gives
  `Σ_c μ_c [monGrp c] = 0` in `Λ_{k-1}`.
* By `core.gen_span` again, `cls y = 0`, i.e. `y ∈ γ_{k+1}` by `core.cls_eq_zero_iff`.

The file is a self-contained assembly: it only imports materials that are already proved in the
workspace, and avoids both `magnusLieDefs`/`witt.Defs` clashes (the Hall-set inputs used for
Witt's theorem are those of `witt/hall_spanning.lean`, which does not reach `witt/Defs.lean`).
-/
import Mathlib
import Submission.Work.SSGRoute.prop5.magnusFramework
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
import Submission.Work.SSGRoute.prop5.magnus_unitCongr_isolated
import Submission.Work.SSGRoute.prop5.commutator_lowerCentralSeries_le
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
import Submission.Work.SSGRoute.prop5.magnusBase
import Submission.Work.SSGRoute.prop5.core.Defs
import Submission.Work.SSGRoute.prop5.core.gen_span
import Submission.Work.SSGRoute.prop5.core.magLeadLemmas
import Submission.Work.SSGRoute.prop5.core.relations_zero
import Submission.Work.SSGRoute.prop5.magLead_mem_nestedImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

set_option maxHeartbeats 1000000

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Work.SSGRoute.prop5

namespace mcore

variable {X : Type*}

/-! ## The commutator monomial and the lower central series -/

theorem mem_Gam_iff {q : ℕ} {z : FreeGroup X} :
    z ∈ core.Gam X q ↔ z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries q := by
  rw [core.Gam, graded.Gam]

theorem monGrp_mem_Gam' (c : Magma X) :
    core.monGrp X c ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (Magma.size c - 1) :=
  mem_Gam_iff.mp (core.monGrp_mem_Gam c)

/-! ## Finsupp bookkeeping -/

theorem linearCombination_map {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (f : M →+ N)
    (g : ι → M) (μ : ι →₀ ℤ) :
    f (Finsupp.linearCombination ℤ g μ)
      = Finsupp.linearCombination ℤ (fun i => f (g i)) μ := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum,
    map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_zsmul])

theorem linearCombination_congr_left {ι M : Type*} [AddCommGroup M] {g g' : ι → M}
    (h : g = g') (μ : ι →₀ ℤ) :
    Finsupp.linearCombination ℤ g μ = Finsupp.linearCombination ℤ g' μ := by rw [h]

/-! ## The Magnus leading term as a homomorphism on the graded piece `Λ_{k-1}` -/

/-- The Magnus leading term, as a monoid homomorphism `γ_k/γ_{k+1} →* (1 + filq X (k+1) k)`. -/
noncomputable def MbarMul (X : Type*) (k : ℕ) (hk : 1 ≤ k) :
    graded.GLam (G := FreeGroup X) (k - 1) →* Multiplicative (↥(filq X (k + 1) k)) :=
  QuotientGroup.lift ((core.Gam X (k - 1 + 1)).subgroupOf (core.Gam X (k - 1)))
    (MonoidHom.mk' (fun u : core.Gam X (k - 1) =>
      Multiplicative.ofAdd (⟨magLead (k + 1) (u : FreeGroup X),
        magLead_mem_filq (X := X) (k + 1) k hk (by omega) (mem_Gam_iff.mp u.2)⟩ :
          ↥(filq X (k + 1) k)))
      (by
        intro a b
        apply Multiplicative.ext
        apply Subtype.ext
        exact core.magLead_mul_mem (X := X) k hk a.2 b.2))
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
    core.Lam X (k - 1) →+ ↥(filq X (k + 1) k) where
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

/-- The leading term of the class of `u ∈ γ_k` is the leading term of `u`. -/
theorem Mbar_cls (X : Type*) (k : ℕ) (hk : 1 ≤ k) (u : core.Gam X (k - 1)) :
    Mbar X k hk (core.cls X (k - 1) u) =
      ⟨magLead (k + 1) (u : FreeGroup X),
        magLead_mem_filq (X := X) (k + 1) k hk (by omega) (mem_Gam_iff.mp u.2)⟩ := rfl

/-- The Magnus leading term on `Λ_{k-1}`, with values in the quotient `FreeAssoc X ⧸ fil X (k+1)`. -/
noncomputable def Theta (X : Type*) (k : ℕ) (hk : 1 ≤ k) :
    core.Lam X (k - 1) →+ FreeAssoc X ⧸ fil X (k + 1) :=
  (Submodule.subtype (filq X (k + 1) k)).toAddMonoidHom.comp (Mbar X k hk)

theorem Theta_cls (X : Type*) (k : ℕ) (hk : 1 ≤ k) (u : core.Gam X (k - 1)) :
    Theta X k hk (core.cls X (k - 1) u) = magLead (k + 1) (u : FreeGroup X) := by
  rw [Theta, AddMonoidHom.comp_apply, Mbar_cls]
  rfl

/-! ## The degree-`k` part of the truncated algebra -/

theorem monBrk_mem_wordSpan (c : Magma X) : monBrk X c ∈ wordSpan (X := X) (Magma.size c) := by
  rw [mem_wordSpan_iff]
  intro w hw
  by_contra hc
  exact hw (core.monBrk_coeff_length c w hc)

theorem monBrk_mem_wordSpan_of_size (c : Magma X) {k : ℕ} (hk : Magma.size c = k) :
    monBrk X c ∈ wordSpan (X := X) k := by
  rw [mem_wordSpan_iff]
  intro w hw
  by_contra hc
  exact hw (hk ▸ core.monBrk_coeff_length c w hc)

/-- A `ℤ`-linear combination of bracketed monomials of trees of size `k` lies in the degree-`k`
part of `FreeAssoc X`. -/
theorem lincomb_monBrk_mem_wordSpan (k : ℕ) (μ : core.TreeIdx X k →₀ ℤ) :
    Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monBrk X c.1) μ ∈
      wordSpan (X := X) k := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ (fun c _ =>
    Submodule.smul_mem _ _ (monBrk_mem_wordSpan_of_size c.1 c.2))

/-- An element of the degree-`k` part of `FreeAssoc X` which lies in `fil X (k+1)` is zero. -/
theorem eq_zero_of_mem_wordSpan_of_mem_fil {k : ℕ} {a : FreeAssoc X}
    (h1 : a ∈ wordSpan (X := X) k) (h2 : a ∈ fil X (k + 1)) : a = 0 :=
  calc a = degPart (X := X) k a := (degPart_eq_self_of_mem_wordSpan h1).symm
    _ = 0 := degPart_eq_zero_of_mem_fil h2 (by omega)

/-- The bracketed monomial of a tree of size `k` is the Magnus leading term of the corresponding
commutator monomial. -/
theorem magLead_monGrp_eq (k : ℕ) (c : core.TreeIdx X k) :
    magLead (k + 1) (core.monGrp X c.1) =
      Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1) := by
  have h1 := core.magLead_monGrp_sub_mem (X := X) (k + 1) c.1 (by rw [c.2])
  rw [show Magma.size c.1 + 1 = k + 1 from by rw [c.2]] at h1
  have h2 : filq X (k + 1) (k + 1) = ⊥ := filq_self_eq_bot' (X := X) (k + 1)
  rw [h2, Submodule.mem_bot] at h1
  exact sub_eq_zero.mp h1

/-- The leading term of the class of a tree of size `k` is the class of its bracketed monomial. -/
theorem Theta_treeClOf (k : ℕ) (hk : 1 ≤ k) (c : core.TreeIdx X k) :
    Theta X k hk (core.treeClOf X k c) =
      Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1) := by
  rw [core.treeClOf, Theta_cls, magLead_monGrp_eq]

/-- `Theta` computes the degree-`k` part of a linear combination of bracket monomials. -/
theorem Theta_treeToLam (k : ℕ) (hk : 1 ≤ k) (μ : core.TreeIdx X k →₀ ℤ) :
    Theta X k hk (core.treeToLam X k μ) =
      Finsupp.linearCombination ℤ
        (fun c : core.TreeIdx X k => Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1)) μ := by
  rw [show core.treeToLam X k μ = Finsupp.linearCombination ℤ (core.treeClOf X k) μ from rfl]
  rw [linearCombination_map (Theta X k hk) (core.treeClOf X k) μ]
  exact linearCombination_congr_left
    (funext (fun c => Theta_treeClOf (X := X) k hk c)) μ

/-! ## The core statement -/

theorem magnusCore_aux (X : Type) (k : ℕ) (hk : 1 ≤ k) (y : FreeGroup X)
    (hy : y ∈ core.Gam X (k - 1)) (hzero : magLead (k + 1) y = 0) :
    y ∈ core.Gam X k := by
  classical
  obtain ⟨μ, hμ⟩ := core.gen_span X k hk y hy
  -- (1) the Magnus leading term of `y` is the class of `Σ μ_c monBrk c`
  have hlead : magLead (k + 1) y
      = Finsupp.linearCombination ℤ
        (fun c : core.TreeIdx X k => Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1)) μ := by
    have h := congrArg (Theta X k hk) hμ
    rw [Theta_treeToLam, Theta_cls] at h
    exact h.symm
  have hmk : Finsupp.linearCombination ℤ
      (fun c : core.TreeIdx X k => Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1)) μ = 0 := by
    rw [← hlead]; exact hzero
  have hmap_mk : Finsupp.linearCombination ℤ
      (fun c : core.TreeIdx X k => Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1)) μ
      = Ideal.Quotient.mk (fil X (k + 1))
        (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monBrk X c.1) μ) :=
    (linearCombination_map (Ideal.Quotient.mk (fil X (k + 1))).toAddMonoidHom
      (fun c : core.TreeIdx X k => monBrk X c.1) μ).symm
  -- (2) homogeneity forces the combination of bracket monomials to vanish
  have hsum0 : Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monBrk X c.1) μ = 0 :=
    eq_zero_of_mem_wordSpan_of_mem_fil (lincomb_monBrk_mem_wordSpan k μ)
      (Ideal.Quotient.eq_zero_iff_mem.mp (hmap_mk ▸ hmk))
  -- (3) Witt's theorem: the corresponding Lie combination vanishes
  have hz : Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monLie X c.1) μ = 0 := by
    apply Phi_injective X
    rw [map_zero]
    refine (linearCombination_map (Phi X).toLinearMap.toAddMonoidHom
      (fun c : core.TreeIdx X k => monLie X c.1) μ).trans ?_
    exact (linearCombination_congr_left (g' := (fun c : core.TreeIdx X k => monBrk X c.1))
      (funext (fun c => Phi_monLie X c.1)) μ).trans hsum0
  -- (4) the graded Lie map converts the Lie relation into the relation in `Λ_{k-1}`
  have hcls0 : Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => core.cls X (k - 1)
      ⟨core.monGrp X c.1, by simpa [c.2] using core.monGrp_mem_Gam (X := X) c.1⟩) μ = 0 := by
    have hz' : core.rzPsi X
        (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monLie X c.1) μ) = 0 := by
      rw [hz]; simp
    have hcomp : core.rzPsi X
        (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monLie X c.1) μ)
        = graded.lofL (G := FreeGroup X) (k - 1)
          (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => core.cls X (k - 1)
            ⟨core.monGrp X c.1, by simpa [c.2] using core.monGrp_mem_Gam (X := X) c.1⟩) μ) := by
      refine (linearCombination_map (core.rzPsi X).toLinearMap.toAddMonoidHom
        (fun c : core.TreeIdx X k => monLie X c.1) μ).trans ?_
      refine (linearCombination_congr_left (g' := (fun c : core.TreeIdx X k => graded.lofL
          (G := FreeGroup X) (k - 1) (core.cls X (k - 1) ⟨core.monGrp X c.1,
            by simpa [c.2] using core.monGrp_mem_Gam (X := X) c.1⟩)))
        (funext (fun c => core.rz_psi_monLie_of_size X k (c.1) (c.2))) μ).trans ?_
      exact (linearCombination_map
        (DirectSum.lof ℤ ℕ (graded.LamAdd (G := FreeGroup X)) (k - 1)).toAddMonoidHom
        (fun c : core.TreeIdx X k => core.cls X (k - 1)
          ⟨core.monGrp X c.1, by simpa [c.2] using core.monGrp_mem_Gam (X := X) c.1⟩) μ).symm
    rw [hcomp] at hz'
    exact core.rz_lofL_injective (FreeGroup X) (k - 1) (by simpa using hz')
  -- (5) conclude
  have hfinal : core.cls X (k - 1) ⟨y, hy⟩ = 0 := by
    have h2 : core.treeToLam X k μ = Finsupp.linearCombination ℤ
        (fun c : core.TreeIdx X k => core.cls X (k - 1)
          ⟨core.monGrp X c.1, by simpa [c.2] using core.monGrp_mem_Gam (X := X) c.1⟩) μ := by
      rw [show core.treeToLam X k μ = Finsupp.linearCombination ℤ (core.treeClOf X k) μ from rfl]
      exact linearCombination_congr_left (funext (fun c => by rw [core.treeClOf])) μ
    rw [← hμ, h2, hcls0]
  have hmemk := (core.cls_eq_zero_iff (X := X) (q := k - 1) (x := ⟨y, hy⟩)).1 hfinal
  simpa [Nat.sub_add_cancel hk] using hmemk

/-- **The core statement, in the form needed for the torsion argument.** -/
theorem magnusCore (X : Type) (N n : ℕ) (hn : n + 2 ≤ N) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries n)
    (h : magLead N y ∈ filq X N (n + 2)) :
    y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (n + 1) := by
  have h0 : magLead (n + 2) y = 0 := core.magLead_eq_zero_of_mem N n hn y h
  have h1 : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries ((n + 1) - 1) := by
    simpa using hy
  have h2 := magnusCore_aux X (n + 1) (by omega) y (mem_Gam_iff.mpr h1) (by simpa using h0)
  exact mem_Gam_iff.mp h2

end mcore

end Work.SSGRoute.prop5
