/-
# `magnusCore`: the Magnus map detects the lower central series

The statement: if `y ∈ γ_n` (Mathlib indexing, i.e. the paper's `γ_{n+1}`) and the Magnus image of
`y` is congruent to `1` modulo the degree `n+2` part of the truncated free associative algebra then
`y ∈ γ_{n+1}` (the paper's `γ_{n+2}`).

This is the "hard half" of the Magnus embedding theorem (Magnus 1935 / Witt 1937), equivalent
(given the elementary inclusion `magnus_mem_one_add`) to Witt's theorem that the free Lie ring is
faithful.

## Route

Write `F = FreeGroup X`, `L = FreeLieAlgebra ℤ X`, `A = FreeAssoc X = ℤ[FreeMonoid X]`,
`Λ_q = γ_q/γ_{q+1}` (Mathlib indexing) and `magLead N y = ((magnus X N y : A ⧸ fil N) - 1)`.

1. **Reduction of the truncation level.**  The hypothesis says `magLead N y ∈ filq X N (n+2)` with
   `n+2 ≤ N`; passing to the quotient `A ⧸ fil (n+2)` of `A ⧸ fil N` (`core.magLead_eq_zero_of_mem`)
   gives `magLead (n+2) y = 0`.  Put `k = n+1`, so that `y ∈ γ_{k-1}` and the goal is `y ∈ γ_k`.
2. **Generation** (`core.gen_span`).  The class of `y` in `Λ_{k-1}` is a `ℤ`-linear combination
   `Σ_c μ_c [monGrp c]` of the commutator monomials of the trees `c` of size `k`; equivalently
   `treeToLam X k μ = cls X (k-1) ⟨y, _⟩`.
3. **Leading term.**  The Magnus leading term is additive on `γ_{k-1}` modulo the degree-`k` piece,
   so it factors through the class map: `lamLead X k : Λ_{k-1} → (filq X (k+1) k, +)` with
   `lamLead (cls u) = magLead (k+1) u` (`lamLead_cls`) and, on the tree span,
   `lamLead (treeToLam μ) = mk (Σ_c μ_c monBrk c)` (`lamLead_treeToLam`).  Hence `magLead (k+1) y = 0`
   says `Σ_c μ_c monBrk c ∈ fil X (k+1)`.
4. Each `monBrk c` is a combination of words of length exactly `size c = k`
   (`core.monBrk_coeff_length`), so `Σ_c μ_c monBrk c` lies in the degree-`k` part, which meets
   `fil X (k+1)` trivially.  Hence `Σ_c μ_c monBrk c = 0`, and Witt's theorem (`Phi_injective`)
   gives `Σ_c μ_c monLie c = 0` in `L`.
5. The graded Lie map `core.rzPsi` sends `monLie c` to the class of `monGrp c` in `Λ_{k-1}`; its
   injectivity on a graded piece (`core.rz_lofL_injective`) gives `Σ_c μ_c [monGrp c] = 0`, so the
   class of `y` vanishes and `y ∈ γ_k` by `core.cls_eq_zero_iff`.

The Hall-set inputs for Witt's theorem (`witt/hall_spanning.lean`, `witt/leading_term_coeff.lean`,
`witt/hall_foliage_lt_right.lean`, `witt/Assembly.lean`) are those that avoid `witt/Defs.lean`,
whose `IsLyndon` clashes with the `IsLyndon` of `magnusLieDefs`. -/
import Mathlib
import Submission.Work.SSGRoute.prop5.magnusBase
import Submission.Work.SSGRoute.prop5.magnusAux.leadMap
import Submission.Work.SSGRoute.prop5.core.gen_span
import Submission.Work.SSGRoute.prop5.core.magLeadLemmas
import Submission.Work.SSGRoute.prop5.magLead_mem_nestedImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-! ## The degree of the bracketed monomial -/

/-- `monBrk X c` is a combination of words of length exactly `Magma.size c`. -/
theorem monBrk_mem_wordSpan (c : Magma X) : monBrk X c ∈ wordSpan (X := X) (Magma.size c) := by
  rw [mem_wordSpan_iff]
  intro w hw
  by_contra hc
  exact hw (core.monBrk_coeff_length c w hc)

/-- `monBrk X c` for `c` of size `k` lies in the degree-`k` part. -/
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
  refine Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ ?_)
  exact monBrk_mem_wordSpan_of_size c.1 c.2

/-- An element of the degree-`k` part of `FreeAssoc X` which lies in `fil X (k+1)` is zero. -/
theorem eq_zero_of_mem_wordSpan_of_mem_fil {k : ℕ} {a : FreeAssoc X}
    (h1 : a ∈ wordSpan (X := X) k) (h2 : a ∈ fil X (k + 1)) : a = 0 :=
  calc a = degPart (X := X) k a := (degPart_eq_self_of_mem_wordSpan h1).symm
    _ = 0 := degPart_eq_zero_of_mem_fil h2 (by omega)

/-! ## From the vanishing of the bracketed combination to the vanishing of the Lie element -/

/-- The Lie homomorphism `Phi` on a `ℤ`-linear combination of Lie monomials of trees of size `k`
is the corresponding combination of bracketed monomials. -/
theorem Phi_lc_eq (X : Type) (k : ℕ) (μ : core.TreeIdx X k →₀ ℤ) :
    Phi X (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monLie X c.1) μ)
      = Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monBrk X c.1) μ := by
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp only [map_add, ihf, ihg]
  | single c b =>
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      simp only [map_smul]
      exact congrArg (fun z => b • z) (Phi_monLie X c.1)

/-- The graded Lie map `core.rzPsi` on a `ℤ`-linear combination of Lie monomials of trees of
size `k` is the corresponding combination of the classes of the commutator monomials. -/
theorem rzPsi_lc_eq (X : Type) (k : ℕ) (μ : core.TreeIdx X k →₀ ℤ) :
    core.rzPsi X (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monLie X c.1) μ)
      = graded.lofL (G := FreeGroup X) (k - 1)
        (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k =>
          core.cls X (k - 1) ⟨core.monGrp X c.1,
            by simpa [c.2] using core.monGrp_mem_Gam (X := X) c.1⟩) μ) := by
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp only [map_add, ihf, ihg]
  | single c b =>
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      simp only [map_smul]
      exact congrArg (fun z => b • z) (core.rz_psi_monLie_of_size X k c.1 c.2)

/-- If a `ℤ`-linear combination of bracketed monomials of trees of size `k` kills the class of `y`
in `A ⧸ fil (k+1)`, then the corresponding combination of Lie monomials vanishes in `L`
(Witt's theorem). -/
theorem lc_monLie_eq_zero_of_mk (X : Type) (k : ℕ) (μ : core.TreeIdx X k →₀ ℤ)
    (h : Ideal.Quotient.mk (fil X (k + 1))
        (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monBrk X c.1) μ) = 0) :
    Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monLie X c.1) μ = 0 := by
  have hsum0 : Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monBrk X c.1) μ = 0 :=
    eq_zero_of_mem_wordSpan_of_mem_fil (lincomb_monBrk_mem_wordSpan k μ)
      (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have h0 : Phi X (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monLie X c.1) μ) = 0 := by
    rw [Phi_lc_eq, hsum0]
  exact Phi_injective X (by rw [h0, map_zero])

/-- If a `ℤ`-linear combination of Lie monomials of the trees of size `k` vanishes, then the
corresponding combination of classes of the commutator monomials vanishes in `Λ_{k-1}`
(the relation matching step, through the graded Lie map `core.rzPsi`). -/
theorem classZero_of_lieZero (X : Type) (k : ℕ) (hk : 1 ≤ k) (μ : core.TreeIdx X k →₀ ℤ)
    (hz : Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monLie X c.1) μ = 0) :
    Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k =>
        core.cls X (k - 1) ⟨core.monGrp X c.1,
          by simpa [c.2] using core.monGrp_mem_Gam (X := X) c.1⟩) μ = 0 := by
  have h1 : core.rzPsi X
      (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monLie X c.1) μ) = 0 := by
    rw [hz, map_zero]
  rw [rzPsi_lc_eq] at h1
  exact core.rz_lofL_injective (FreeGroup X) (k - 1) (by simpa using h1)

/-! ## The core statement at truncation level `k+1` -/

theorem magnusCoreAux (X : Type) (k : ℕ) (hk : 1 ≤ k) (y : FreeGroup X)
    (hy : y ∈ core.Gam X (k - 1)) (hzero : magLead (k + 1) y = 0) :
    y ∈ core.Gam X k := by
  classical
  obtain ⟨μ, hμ⟩ := core.gen_span X k hk y hy
  -- the leading term of `y` is the image of `Σ μ_c monBrk c`
  have hlead : magLead (k + 1) y = Ideal.Quotient.mk (fil X (k + 1))
      (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monBrk X c.1) μ) := by
    have h1 : Submodule.subtype (filq X (k + 1) k)
          (lamLead X k hk (core.cls X (k - 1) ⟨y, hy⟩))
        = Submodule.subtype (filq X (k + 1) k) (lamLead X k hk (core.treeToLam X k μ)) := by
      rw [hμ]
    rw [lamLead_cls, lamLead_treeToLam] at h1
    simpa using h1
  have hmk : Ideal.Quotient.mk (fil X (k + 1))
      (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monBrk X c.1) μ) = 0 := by
    rw [← hlead]
    exact hzero
  have hz : Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monLie X c.1) μ = 0 :=
    lc_monLie_eq_zero_of_mk X k μ hmk
  have hcls0 : Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k =>
      core.cls X (k - 1) ⟨core.monGrp X c.1,
        by simpa [c.2] using core.monGrp_mem_Gam (X := X) c.1⟩) μ = 0 :=
    classZero_of_lieZero X k hk μ hz
  have hfinal : core.cls X (k - 1) ⟨y, hy⟩ = 0 := by
    rw [← hμ]
    simp only [core.treeToLam, core.treeClOf]
    exact hcls0
  have hmem := (core.cls_eq_zero_iff (X := X) (q := k - 1) (x := ⟨y, hy⟩)).1 hfinal
  simpa [Nat.sub_add_cancel hk] using hmem

/-- **The core statement.**  If `y ∈ γ_n` (Mathlib indexing, i.e. the paper's `γ_{n+1}`) and the
Magnus image of `y` is congruent to `1` modulo the degree `n+2` part of the truncated free
associative algebra, then `y ∈ γ_{n+1}` (the paper's `γ_{n+2}`). -/
theorem magnusCore (X : Type) (N n : ℕ) (hn : n + 2 ≤ N) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries n)
    (h : ((magnus X N y : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1 ∈
      filq X N (n + 2)) :
    y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (n + 1) := by
  have hzero : magLead (n + 2) y = 0 :=
    core.magLead_eq_zero_of_mem (X := X) N n hn y (by simpa [magLead] using h)
  have hy' : y ∈ core.Gam X ((n + 1) - 1) := by
    rw [Nat.add_sub_cancel]
    exact mem_Gam_iff.mpr hy
  have hres := magnusCoreAux X (n + 1) (by omega) y hy' (by simpa using hzero)
  exact mem_Gam_iff.mp hres

end Work.SSGRoute.prop5
