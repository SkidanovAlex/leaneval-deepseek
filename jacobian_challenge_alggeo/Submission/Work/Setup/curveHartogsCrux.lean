/-
# The local Hartogs/`S2` statement for the relative curve `A ⊗[K] R`

This file proves `Work.Setup.curveHartogsCrux`: if `x` is a rational function on the relative
chart `B = A ⊗[K] R` of a smooth curve `A` over a field `K` along a valuation ring `R`, if `x` is
regular at the fibre prime `P = 𝔪_R·B` (`x ∈ B_P`) and if the denominator ideal
`D = denomIdeal x = {b : x·b ∈ B}` is contained in a maximal ideal `N ⊇ P`, then `D` is contained
in a *height one* prime `q ≤ N`.

## The mathematical idea

* **Step 1** (the key algebraic step): if `x·(c·u) = b` with `c ∈ R ∖ 0` and `u ∉ N`, and if `D`
  meets `B ∖ P`, then `D` also meets `B ∖ N`.  Normalise the content of `b`
  (`Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map`: `b = r·b₁` with `b₁ ∉ P`) and use
  the total divisibility of `R`: either `r = c·m'`, whence `u ∈ D` and `u ∉ N`; or `c = r·m'`,
  whence `m'u ∈ D` and either `m' ∉ 𝔪_R` (so `m'u ∉ N`) or else `m' ∈ 𝔪_R`, in which case a
  reduction modulo the prime `P` (using that `B/P` is a domain and that `D` has an element
  outside `P`) gives the contradiction `b₁ ∈ P`.

* **Step 2**: consequently `D` is disjoint from the submonoid `S = (R∖0)·(B∖N) ⊆ B`.  In the
  localisation `T = B[S⁻¹]` the ideal `D·T` is therefore proper, so it is contained in a maximal
  ideal `M`; the contraction `q = M ∩ B` is a prime of `B` with `D ≤ q ≤ N` and `q ∩ R = ⊥`,
  hence `q.height = 1` by `Work.Setup.heightLeOneUnderBot` (the generic fibre
  `A ⊗[K] Frac R` is one-dimensional).
-/
import Mathlib
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Alt.denomIdeal
import Submission.Work.SpecLin.Setup.krullDimLE_tensor
import Submission.Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map
import Submission.Work.SpecLin.Core.module_free_chartTensor
import Submission.Work.Setup.heightLeOneUnderBot

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Setup

universe u

/-! ## Auxiliary: the denominator-ideal characterisation of `InLocalization` -/

section DenomIdealChar

variable {B : Type u} [CommRing B] [IsDomain B]

/-- `x : FractionRing B` lies in the localisation of `B` at the prime `I` if and only if its
denominator ideal is not contained in `I`. -/
theorem inLocalization_iff_not_le_denomIdeal (x : FractionRing B) (I : Ideal B) :
    Work.SpecLin.Alt.InLocalization x I ↔
      ¬ (Work.SpecLin.Alt.denomIdeal x : Ideal B) ≤ I := by
  constructor
  · rintro ⟨b, s, hs, hbs⟩ hle
    exact hs (hle ((Work.SpecLin.Alt.mem_denomIdeal x s).mpr ⟨b, hbs⟩))
  · intro h
    by_contra hcon
    simp only [Work.SpecLin.Alt.InLocalization] at hcon
    push Not at hcon
    refine h (fun d hd => ?_)
    by_contra hdI
    rw [Work.SpecLin.Alt.mem_denomIdeal] at hd
    obtain ⟨b, hb⟩ := hd
    exact (hcon b d hdI) hb

end DenomIdealChar

/-! ## The key algebraic step -/

section Key

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable {B : Type u} [CommRing B] [IsDomain B] [Algebra R B] [Module.Free R B]

/-- The contraction of a maximal ideal containing `𝔪_R·B` is `𝔪_R`. -/
theorem comap_eq_maximalIdeal_of_le (N : Ideal B) [N.IsMaximal]
    (hPN : (IsLocalRing.maximalIdeal R).map (algebraMap R B) ≤ N) :
    N.comap (algebraMap R B) = IsLocalRing.maximalIdeal R := by
  haveI : N.IsPrime := (inferInstance : N.IsMaximal).isPrime
  have hle : IsLocalRing.maximalIdeal R ≤ N.comap (algebraMap R B) :=
    (Ideal.map_le_iff_le_comap).mp hPN
  have hne : N.comap (algebraMap R B) ≠ ⊤ := by
    intro htop
    have h1 : (1 : B) ∈ N := by
      have : (1 : R) ∈ N.comap (algebraMap R B) := by rw [htop]; trivial
      simpa using this
    exact (inferInstance : N.IsMaximal).ne_top (Ideal.eq_top_iff_one N |>.mpr h1)
  exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hne hle).symm

/-- **The key algebraic step.**  Let `B` be a domain, free as an `R`-module, over the valuation
ring `R`, let `N` be a maximal ideal of `B` containing `𝔪_R·B`, suppose that `B ⧸ 𝔪_R·B` is a
domain and that the denominator ideal `D` of `x ∈ Frac B` is contained in `N` but not in
`𝔪_R·B`.  Then `x ≠ b / (c·u)` for all `b ∈ B`, `c ∈ R ∖ 0` and `u ∉ N`. -/
theorem not_eq_of_mul_mem (N : Ideal B) [N.IsMaximal]
    (hPN : (IsLocalRing.maximalIdeal R).map (algebraMap R B) ≤ N)
    (hdom : IsDomain (B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B)))
    (hinj : Function.Injective (algebraMap R B))
    (x : FractionRing B)
    (hD : (Work.SpecLin.Alt.denomIdeal x : Ideal B) ≤ N)
    (hP : ∃ d ∈ (Work.SpecLin.Alt.denomIdeal x : Ideal B),
      d ∉ (IsLocalRing.maximalIdeal R).map (algebraMap R B))
    (b : B) (c : R) (u : B) (hc : c ≠ 0) (hu : u ∉ N) :
    x * algebraMap B (FractionRing B) (algebraMap R B c * u) ≠
      algebraMap B (FractionRing B) b := by
  intro h
  have hσinj : Function.Injective (algebraMap B (FractionRing B)) :=
    IsFractionRing.injective B (FractionRing B)
  -- `x ≠ 0`
  have hx0 : x ≠ 0 := by
    intro h0
    have htop : (Work.SpecLin.Alt.denomIdeal x : Ideal B) = ⊤ :=
      (Work.SpecLin.Alt.denomIdeal_eq_top_iff x).mpr ⟨0, by rw [h0, map_zero]⟩
    exact (inferInstance : N.IsMaximal).ne_top (top_le_iff.mp (htop ▸ hD))
  -- `u ≠ 0`
  have hu0 : u ≠ 0 := fun h0 => hu (h0 ▸ N.zero_mem)
  -- `b ≠ 0`
  have hcne : algebraMap R B c ≠ 0 := fun h0 => hc (hinj (by rw [h0, map_zero]))
  have hb0 : b ≠ 0 := by
    intro hb
    have h1 : x * algebraMap B (FractionRing B) (algebraMap R B c * u) = 0 := by
      rw [h, hb, map_zero]
    have h2 : algebraMap B (FractionRing B) (algebraMap R B c * u) = 0 := by
      rcases mul_eq_zero.mp h1 with h' | h'
      · exact absurd h' hx0
      · exact h'
    have h3 : algebraMap R B c * u = 0 :=
      hσinj (h2.trans (map_zero _).symm)
    rcases mul_eq_zero.mp h3 with h' | h'
    · exact hcne h'
    · exact hu0 h'
  -- content normalisation of `b`
  obtain ⟨r, b₁, hb_eq, hb₁P⟩ :=
    Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map (R := R) (B := B) b
  have hr0 : r ≠ 0 := by
    intro hr
    exact hb0 (by rw [hb_eq, hr, zero_smul])
  have hσr : algebraMap B (FractionRing B) (algebraMap R B r) ≠ 0 := by
    intro h0
    refine hr0 (hinj ((hσinj (h0.trans (map_zero _).symm)).trans (map_zero _).symm))
  have hσc : algebraMap B (FractionRing B) (algebraMap R B c) ≠ 0 := by
    intro h0
    refine hc (hinj ((hσinj (h0.trans (map_zero _).symm)).trans (map_zero _).symm))
  have hσb : algebraMap B (FractionRing B) b =
      algebraMap B (FractionRing B) (algebraMap R B r) * algebraMap B (FractionRing B) b₁ := by
    rw [hb_eq, Algebra.smul_def, map_mul]
  rcases ValuationRing.dvd_total r c with ⟨m', hm'⟩ | ⟨m', hm'⟩
  · -- case `c = r * m'`
    have h2 : x * algebraMap B (FractionRing B) (algebraMap R B m' * u) =
        algebraMap B (FractionRing B) b₁ := by
      have hcancel : algebraMap B (FractionRing B) (algebraMap R B r) *
            (x * algebraMap B (FractionRing B) (algebraMap R B m' * u))
          = algebraMap B (FractionRing B) (algebraMap R B r) *
            algebraMap B (FractionRing B) b₁ := by
        calc algebraMap B (FractionRing B) (algebraMap R B r) *
              (x * algebraMap B (FractionRing B) (algebraMap R B m' * u))
            = x * (algebraMap B (FractionRing B) (algebraMap R B r) *
                (algebraMap B (FractionRing B) (algebraMap R B m') *
                  algebraMap B (FractionRing B) u)) := by
                rw [map_mul]; ring
          _ = x * (algebraMap B (FractionRing B) (algebraMap R B r) *
                algebraMap B (FractionRing B) (algebraMap R B m') *
                  algebraMap B (FractionRing B) u) := by ring
          _ = x * (algebraMap B (FractionRing B) (algebraMap R B c) *
                  algebraMap B (FractionRing B) u) := by
                simp only [map_mul, hm']
          _ = x * algebraMap B (FractionRing B) (algebraMap R B c * u) := by rw [map_mul]
          _ = algebraMap B (FractionRing B) b := h
          _ = algebraMap B (FractionRing B) (algebraMap R B r) *
                algebraMap B (FractionRing B) b₁ := hσb
      exact mul_left_cancel₀ hσr hcancel
    have hmuD : algebraMap R B m' * u ∈ (Work.SpecLin.Alt.denomIdeal x : Ideal B) := by
      rw [Work.SpecLin.Alt.mem_denomIdeal]
      exact ⟨b₁, h2⟩
    by_cases hm'𝔪 : m' ∈ IsLocalRing.maximalIdeal R
    · -- then `m' ∈ N`, and reducing modulo `P` forces `b₁ ∈ P`
      obtain ⟨d₀, hd₀D, hd₀P⟩ := hP
      obtain ⟨β, hβ⟩ := (Work.SpecLin.Alt.mem_denomIdeal x d₀).mp hd₀D
      have h3 : b₁ * d₀ = algebraMap R B m' * (u * β) := by
        apply hσinj
        calc algebraMap B (FractionRing B) (b₁ * d₀)
            = algebraMap B (FractionRing B) b₁ * algebraMap B (FractionRing B) d₀ := by
                rw [map_mul]
          _ = (x * algebraMap B (FractionRing B) (algebraMap R B m' * u)) *
                algebraMap B (FractionRing B) d₀ := by rw [← h2]
          _ = algebraMap B (FractionRing B) (algebraMap R B m' * u) *
                (x * algebraMap B (FractionRing B) d₀) := by ring
          _ = algebraMap B (FractionRing B) (algebraMap R B m' * u) *
                algebraMap B (FractionRing B) β := by rw [hβ]
          _ = algebraMap B (FractionRing B) (algebraMap R B m' * (u * β)) := by
                simp only [map_mul]; ring
      have hmemP : b₁ * d₀ ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R B) := by
        rw [h3]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem (algebraMap R B) hm'𝔪)
      haveI : IsDomain (B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B)) := hdom
      have h5 : (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) b₁) *
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) d₀) = 0 := by
        have h6 : (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B))
            (b₁ * d₀) : B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hmemP
        rw [map_mul] at h6
        exact h6
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact hb₁P (Ideal.Quotient.eq_zero_iff_mem.mp h6)
      · exact hd₀P (Ideal.Quotient.eq_zero_iff_mem.mp h6)
    · -- then `m' ∉ N` and `m' * u ∈ D ∖ N`, contradicting `D ≤ N`
      have hm'N : algebraMap R B m' ∉ N := by
        intro hmem
        exact hm'𝔪 (by
          rw [← comap_eq_maximalIdeal_of_le N hPN]
          exact Ideal.mem_comap.mpr hmem)
      have : algebraMap R B m' * u ∈ N := hD hmuD
      rcases (inferInstance : N.IsMaximal).isPrime.mem_or_mem this with h' | h'
      · exact hm'N h'
      · exact hu h'
  · -- case `r = c * m'`
    have h2 : x * algebraMap B (FractionRing B) u =
        algebraMap B (FractionRing B) (algebraMap R B m' * b₁) := by
      have hcancel : algebraMap B (FractionRing B) (algebraMap R B c) *
            (x * algebraMap B (FractionRing B) u)
          = algebraMap B (FractionRing B) (algebraMap R B c) *
            algebraMap B (FractionRing B) (algebraMap R B m' * b₁) := by
        calc algebraMap B (FractionRing B) (algebraMap R B c) *
              (x * algebraMap B (FractionRing B) u)
            = x * (algebraMap B (FractionRing B) (algebraMap R B c) *
                algebraMap B (FractionRing B) u) := by ring
          _ = x * algebraMap B (FractionRing B) (algebraMap R B c * u) := by rw [map_mul]
          _ = algebraMap B (FractionRing B) b := h
          _ = algebraMap B (FractionRing B) (algebraMap R B r) *
                algebraMap B (FractionRing B) b₁ := hσb
          _ = algebraMap B (FractionRing B) (algebraMap R B c) *
                (algebraMap B (FractionRing B) (algebraMap R B m') *
                  algebraMap B (FractionRing B) b₁) := by
                simp only [map_mul, hm']; ring
          _ = algebraMap B (FractionRing B) (algebraMap R B c) *
                algebraMap B (FractionRing B) (algebraMap R B m' * b₁) := by
                rw [map_mul]
      exact mul_left_cancel₀ hσc hcancel
    have huD : u ∈ (Work.SpecLin.Alt.denomIdeal x : Ideal B) := by
      rw [Work.SpecLin.Alt.mem_denomIdeal]
      exact ⟨algebraMap R B m' * b₁, h2⟩
    exact hu (hD huD)

/-- **`D` misses `(R∖0)·(B∖N)`.**  Under the hypotheses of `not_eq_of_mul_mem`, the denominator
ideal of `x` is disjoint from the submonoid generated by `R ∖ 0` and `B ∖ N`. -/
theorem disjoint_denomIdeal_sup_primeCompl (N : Ideal B) [N.IsMaximal]
    (hPN : (IsLocalRing.maximalIdeal R).map (algebraMap R B) ≤ N)
    (hdom : IsDomain (B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B)))
    (hinj : Function.Injective (algebraMap R B))
    (x : FractionRing B)
    (hD : (Work.SpecLin.Alt.denomIdeal x : Ideal B) ≤ N)
    (hP : ∃ d ∈ (Work.SpecLin.Alt.denomIdeal x : Ideal B),
      d ∉ (IsLocalRing.maximalIdeal R).map (algebraMap R B)) :
    Disjoint (((nonZeroDivisors R).map (algebraMap R B) ⊔ N.primeCompl :
        Submonoid B) : Set B) ((Work.SpecLin.Alt.denomIdeal x : Ideal B) : Set B) := by
  haveI : N.IsPrime := (inferInstance : N.IsMaximal).isPrime
  rw [Set.disjoint_left]
  intro d hdS hdD
  have hdS' : d ∈ ((nonZeroDivisors R).map (algebraMap R B) ⊔ N.primeCompl :
      Submonoid B) := hdS
  rw [Submonoid.mem_sup] at hdS'
  obtain ⟨y, hy, z, hz, hyz⟩ := hdS'
  rw [Submonoid.mem_map] at hy
  obtain ⟨c, hc, hcy⟩ := hy
  have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
  obtain ⟨b, hb⟩ := (Work.SpecLin.Alt.mem_denomIdeal x d).mp hdD
  have hdz : d = algebraMap R B c * z := by rw [← hyz, hcy]
  exact (not_eq_of_mul_mem N hPN hdom hinj x hD hP b c z hc0 hz) (by rw [← hb, hdz])

end Key

/-! ## The local Hartogs statement for the relative curve -/

section Crux

theorem curveHartogsCrux {K : Type u} [Field K] (A : Type u) [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] [Algebra.Smooth K A] [Ring.KrullDimLE 1 A]
    (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    [IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))]
    (N : Ideal (TensorProduct K A R)) [N.IsMaximal]
    (hPN : ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))) <= N)
    (x : FractionRing (TensorProduct K A R))
    (hxP : Work.SpecLin.Alt.InLocalization x ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (hD : (Work.SpecLin.Alt.denomIdeal x : Ideal (TensorProduct K A R)) <= N) :
    exists q : Ideal (TensorProduct K A R), q.IsPrime ∧ q.height = 1 ∧ q <= N ∧
      (Work.SpecLin.Alt.denomIdeal x : Ideal (TensorProduct K A R)) <= q := by
  classical
  -- the `R`-algebra structure on `B = A ⊗[K] R` given by the right factor
  letI : Algebra R (TensorProduct K A R) :=
    Algebra.TensorProduct.rightAlgebra (R := K) (A := A) (B := R)
  haveI hfree : Module.Free R (TensorProduct K A R) :=
    Work.SpecLin.Core.module_free_chartTensor (K := K) (A := A) (R := R)
  -- the identification of `algebraMap R B` with `includeRight`
  have halg : algebraMap R (TensorProduct K A R) =
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) :
        R →+* TensorProduct K A R) :=
    Algebra.TensorProduct.algebraMap_eq_includeRight
  have hinc : ∀ r : R, (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) r =
      algebraMap R (TensorProduct K A R) r := fun r =>
    congrFun (congrArg (fun f : R →+* TensorProduct K A R =>
      (f : R → TensorProduct K A R)) halg.symm) r
  -- `P = 𝔪_R·B`
  set P : Ideal (TensorProduct K A R) := (IsLocalRing.maximalIdeal R).map
    (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) with hPdef
  -- the special fibre is a domain
  have hdom : IsDomain (TensorProduct K A R ⧸ P) := by
    have hRes : IsDomain (TensorProduct K A (R ⧸ IsLocalRing.maximalIdeal R)) :=
      ‹IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))›
    have e : (TensorProduct K A R ⧸ P) ≃+*
        TensorProduct K A (R ⧸ IsLocalRing.maximalIdeal R) :=
      (Algebra.TensorProduct.tensorQuotientEquiv (R := K) (S := K) (T := R) (A := A)
        (I := IsLocalRing.maximalIdeal R)).symm.toRingEquiv
    exact MulEquiv.isDomain _ e.toMulEquiv
  -- injectivity of `algebraMap R B`
  have hinj : Function.Injective (algebraMap R (TensorProduct K A R)) := by
    intro a b hab
    have hι : Function.Injective
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) :=
      Algebra.TensorProduct.includeRight_injective (R := K) (A := A) (B := R)
        (RingHom.injective (algebraMap K A))
    refine hι ?_
    rw [hinc a, hinc b]
    exact hab
  -- the corresponding form of `hPN` for `algebraMap R B`
  have hPNalg : (IsLocalRing.maximalIdeal R).map (algebraMap R (TensorProduct K A R)) ≤ N := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, ← hinc r]
    exact hPN (Ideal.mem_map_of_mem _ hr)
  -- `D` meets `B ∖ P`
  have hP : ∃ d ∈ (Work.SpecLin.Alt.denomIdeal x : Ideal (TensorProduct K A R)), d ∉ P := by
    have hxP' : ¬ (Work.SpecLin.Alt.denomIdeal x : Ideal (TensorProduct K A R)) ≤ P :=
      (inLocalization_iff_not_le_denomIdeal x P).mp hxP
    exact Set.not_subset.mp hxP'
  -- `D` misses `S = (R∖0)·(B∖N)`
  have hdisj : Disjoint (((nonZeroDivisors R).map (algebraMap R (TensorProduct K A R)) ⊔
        N.primeCompl : Submonoid (TensorProduct K A R)) : Set (TensorProduct K A R))
      ((Work.SpecLin.Alt.denomIdeal x : Ideal (TensorProduct K A R)) :
        Set (TensorProduct K A R)) :=
    disjoint_denomIdeal_sup_primeCompl N hPNalg hdom hinj x hD hP
  let S : Submonoid (TensorProduct K A R) :=
    (nonZeroDivisors R).map (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) ⊔
      N.primeCompl
  have hmap_eq : (nonZeroDivisors R).map
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) =
      (nonZeroDivisors R).map (algebraMap R (TensorProduct K A R)) := by
    ext y
    rw [Submonoid.mem_map, Submonoid.mem_map]
    exact ⟨fun ⟨c, hc, hcy⟩ => ⟨c, hc, by rw [← hinc c]; exact hcy⟩,
      fun ⟨c, hc, hcy⟩ => ⟨c, hc, by rw [hinc c]; exact hcy⟩⟩
  have hS_eq : S = ((nonZeroDivisors R).map (algebraMap R (TensorProduct K A R)) ⊔
      N.primeCompl : Submonoid (TensorProduct K A R)) := by
    show ((nonZeroDivisors R).map
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) ⊔
      N.primeCompl : Submonoid (TensorProduct K A R)) = _
    rw [hmap_eq]
  have hSdisj : Disjoint (S : Set (TensorProduct K A R))
      ((Work.SpecLin.Alt.denomIdeal x : Ideal (TensorProduct K A R)) :
        Set (TensorProduct K A R)) := by
    rw [hS_eq]
    exact hdisj
  -- the localisation `T = B[S⁻¹]`
  haveI : IsLocalization S (Localization S) := Localization.isLocalization (M := S)
  have hDmap : Ideal.map (algebraMap (TensorProduct K A R) (Localization S))
      (Work.SpecLin.Alt.denomIdeal x : Ideal (TensorProduct K A R)) ≠ ⊤ := by
    rw [IsLocalization.map_algebraMap_ne_top_iff_disjoint S (Localization S)]
    exact hSdisj
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ hDmap
  haveI : M.IsPrime := hMmax.isPrime
  refine ⟨M.comap (algebraMap (TensorProduct K A R) (Localization S)),
    Ideal.IsPrime.comap _, ?_, ?_, ?_⟩
  · -- height one
    have hqbot : (M.comap (algebraMap (TensorProduct K A R) (Localization S))).comap
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro r hr
      by_contra hr0
      have hmemS : (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) r ∈ S :=
        Submonoid.mem_sup_left ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr0, rfl⟩
      have hunit : IsUnit (algebraMap (TensorProduct K A R) (Localization S)
          ((Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) r)) :=
        IsLocalization.map_units (Localization S) ⟨_, hmemS⟩
      exact hMmax.ne_top (Ideal.eq_top_of_isUnit_mem M (Ideal.mem_comap.mp hr) hunit)
    have hle1 : (M.comap (algebraMap (TensorProduct K A R) (Localization S))).height ≤ 1 :=
      heightLeOneUnderBot (K := K) A hA R _ hqbot
    have hge1 : (1 : ℕ∞) ≤
        (M.comap (algebraMap (TensorProduct K A R) (Localization S))).height := by
      rw [Order.one_le_iff_ne_zero]
      intro h0
      have hbot : M.comap (algebraMap (TensorProduct K A R) (Localization S)) = ⊥ :=
        Ideal.height_eq_zero_iff_eq_bot.mp h0
      have hDq : (Work.SpecLin.Alt.denomIdeal x : Ideal (TensorProduct K A R)) ≤
          M.comap (algebraMap (TensorProduct K A R) (Localization S)) :=
        (Ideal.map_le_iff_le_comap).mp hMle
      exact Work.SpecLin.Alt.denomIdeal_ne_bot x (le_bot_iff.mp (hbot ▸ hDq))
    exact le_antisymm hle1 hge1
  · -- `q ≤ N`
    intro b hb
    by_contra hbN
    have hbS : b ∈ S := Submonoid.mem_sup_right (Ideal.mem_primeCompl_iff.mpr hbN)
    have hunit : IsUnit (algebraMap (TensorProduct K A R) (Localization S) b) :=
      IsLocalization.map_units (Localization S) ⟨b, hbS⟩
    exact hMmax.ne_top (Ideal.eq_top_of_isUnit_mem M (Ideal.mem_comap.mp hb) hunit)
  · -- `D ≤ q`
    exact (Ideal.map_le_iff_le_comap).mp hMle

end Crux

end Work.Setup
