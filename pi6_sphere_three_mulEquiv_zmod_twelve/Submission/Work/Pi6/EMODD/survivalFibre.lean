import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMODD.cohHomology
import Submission.Work.Pi6.EMODD.cpowLaws
import Submission.Work.Pi6.EMODD.kTwoRing
import Submission.Work.Pi6.EMM2.SSKit

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Survival in the fibre column of the Serre spectral sequence (area EMODD)

A class of the fibre of positive even degree whose cup powers are all nonzero is the pullback of a
class of the total space (this is where `H²(fibreIncl)` is nonzero and `H²(fibre)` is a line are
used); the `IsSerreMSS` characterization of the image of `H^q(fibreIncl)` then produces a nonzero
class of `E_{q+2}^{0,q}` for every even `q ≤ N`.

* `Work.Pi6.EMODD.one_ne_zero_of_finrank_one` — the unit of `H⁰(−)` of a space with
  one-dimensional `H⁰` is nonzero;
* `Work.Pi6.EMODD.survivalFibre` — the target lemma.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMODD

noncomputable section

/-- The unit of the cup ring of a space with one-dimensional `H⁰` is nonzero. -/
theorem one_ne_zero_of_finrank_one {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X]
    (h : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X 0) = 1) : Work.Pi6.one 𝕜 X ≠ 0 := by
  have hb : ∃ b : Work.Pi6.Coh 𝕜 X 0, b ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_ne_iff] at hc
    haveI : Subsingleton (Work.Pi6.Coh 𝕜 X 0) := ⟨fun x y => by rw [hc x, hc y]⟩
    rw [Module.finrank_zero_of_subsingleton] at h
    omega
  obtain ⟨b, hb⟩ := hb
  intro hone
  have h1 : (Work.Pi6.cup 𝕜 X 0 0 (Work.Pi6.one 𝕜 X)) b = b :=
    Work.Cohomology.cupH'_one_left 𝕜 (TopCat.toSSet.obj (TopCat.of X)) 0 b
  rw [hone] at h1
  have h0 : (Work.Pi6.cup 𝕜 X 0 0 (0 : Work.Pi6.Coh 𝕜 X 0)) b = 0 :=
    Work.Cohomology.cupH'_zero_left 𝕜 (TopCat.toSSet.obj (TopCat.of X)) 0 0 b
  rw [h0] at h1
  exact hb h1.symm

theorem survivalFibre (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B) (e₀ : E) (N : ℕ) (S : Work.Pi6.CohSS 𝕜)
    (hS : Work.Pi6.IsSerreMSS S p e₀ N)
    (hι : (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) 2).hom ≠ 0)
    (hB0 : Nonempty (Work.Pi6.Coh 𝕜 B 0 ≅ ModuleCat.of 𝕜 𝕜))
    (hF2 : Nonempty (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 2 ≅ ModuleCat.of 𝕜 𝕜))
    (hFp : ∃ w : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 2,
        ∀ k : ℕ, 2 * k ≤ N → Work.Pi6.cpow w k ≠ 0) :
    ∀ q : ℕ, 2 ≤ q → q ≤ N → Even q → ∃ z : S.E (q + 2) (0, (q : ℤ)), z ≠ 0 := by
  intro q _hq2 hqN hqeven
  -- the multiplicative Serre spectral sequence data
  obtain ⟨e2, _hmul, _hvanish, _hdimsum, _hbot, hedge⟩ := hS
  -- write the even `q ≤ N` as `2 * k`
  obtain ⟨k, rfl⟩ : ∃ k, q = 2 * k := by
    obtain ⟨j, hj⟩ := hqeven
    exact ⟨j, by omega⟩
  have hkN : 2 * k ≤ N := hqN
  obtain ⟨w, hw⟩ := hFp
  have hwk : Work.Pi6.cpow w k ≠ 0 := hw k hkN
  -- the unit of `H⁰(B)` is nonzero
  have hone : Work.Pi6.one 𝕜 B ≠ 0 := by
    refine one_ne_zero_of_finrank_one ?_
    obtain ⟨φ⟩ := hB0
    have hφ := LinearEquiv.finrank_eq (CategoryTheory.Iso.toLinearEquiv φ)
    simpa using hφ
  -- the degree-`2` pullback `H²(E) → H²(F)` is nonzero
  obtain ⟨x, hx⟩ : ∃ x : Work.Pi6.Coh 𝕜 E 2,
      (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) 2).hom x ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_ne_iff] at hcon
    exact hι (LinearMap.ext hcon)
  -- ... and `H²(F)` is a line, so it is surjective
  obtain ⟨φ⟩ := hF2
  have hφx : φ.toLinearEquiv ((Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) 2).hom x) ≠ 0 := by
    intro hzero
    exact hx (φ.toLinearEquiv.injective (by rw [hzero, map_zero]))
  obtain ⟨x', hx'⟩ : ∃ x' : Work.Pi6.Coh 𝕜 E 2,
      (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) 2).hom x' = w := by
    refine ⟨(φ.toLinearEquiv w
        / φ.toLinearEquiv ((Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) 2).hom x)) • x, ?_⟩
    have hc : (φ.toLinearEquiv w
          / φ.toLinearEquiv ((Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) 2).hom x))
          • ((Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) 2).hom x) = w := by
      apply φ.toLinearEquiv.injective
      rw [map_smul]
      show (φ.toLinearEquiv w
            / φ.toLinearEquiv ((Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) 2).hom x))
            * φ.toLinearEquiv ((Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) 2).hom x)
          = φ.toLinearEquiv w
      exact div_mul_cancel₀ _ hφx
    rw [map_smul]
    exact hc
  -- the cup powers of `w` lift to `H^{2k}(E)`
  have he : (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) (2 * k)).hom (Work.Pi6.cpow x' k)
      = Work.Pi6.cpow w k := by
    have hcl := (Work.Pi6.EMODD.cpowLaws 𝕜).1 (Work.StemsB.fibreIncl p (p e₀)) x' k
    rw [hx'] at hcl
    exact hcl.symm
  -- the image characterization of `H^{2k}(E) → H^{2k}(F)` produces a nonzero `E_{2k+2}^{0,2k}`
  obtain ⟨z, hz⟩ := (hedge (2 * k) hkN (Work.Pi6.cpow w k)).mp ⟨Work.Pi6.cpow x' k, he⟩
  refine ⟨z, ?_⟩
  intro hz0
  have hmap : (S.colTo ((2 * k : ℕ) : ℤ) (2 * k)).hom z = 0 := by rw [hz0]; simp
  rw [hz] at hmap
  have h2 : Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] Work.Pi6.cpow w k = 0 := by
    have h3 : (e2 0 (2 * k) (by omega) (by omega)).hom
        ((e2 0 (2 * k) (by omega) (by omega)).inv.hom
          (Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] Work.Pi6.cpow w k))
        = Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] Work.Pi6.cpow w k :=
      CategoryTheory.Iso.inv_hom_id_apply _ _
    rw [hmap] at h3
    simpa using h3.symm
  exact Work.Pi6.tmul_ne_zero_of_ne_zero hone hwk h2

end

end Work.Pi6.EMODD
