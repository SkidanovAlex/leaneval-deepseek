import Mathlib
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map
import Submission.Work.SpecLin.Core.module_free_chartTensor

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open scoped TensorProduct

namespace Work.SpecLin.Alt

/-! ## The saturation lemma `B = B_P ∩ B_F`

Throughout, `R` is a valuation ring which is a `K`-algebra, `A` is a `K`-algebra,
`B = A ⊗[K] R` and `P = 𝔪_R · B` is the prime of the generic point of the special fibre.
We prove that the localisations `B_P` (at the special fibre) and `B_F = B ⊗_R Frac R`
(the generic fibre) meet exactly in `B`, which is the "S2-free descent" step of the
strong route to the conservation-of-number statement.

The proof is elementary and uses only
* the content normalisation `Content.exists_smul_notMem_maximalIdeal_map` (which needs
  `B` free over `R`, `Core.module_free_chartTensor`), and
* the total divisibility of a valuation ring. -/

/-- **Divisibility step.**

Let `R` be a valuation ring, `B` a domain `R`-algebra with `algebraMap R B` injective,
`w ∈ B` an element which is *primitive* (not in `𝔪_R · B`), and suppose that for some
`s, d ∈ R` one has `s · b = d · w` in `B`.  Then `s ∣ d`.

Indeed, if `d = 0` this is trivial; otherwise, by total divisibility, either `s ∣ d` or
`d ∣ s`, say `s = d e`; in the second case `s b = d w` gives `d (e b - w) = 0`, so `w = e b` (as
`B` is a domain and `d ≠ 0`), and if `e ∈ 𝔪_R` then `w ∈ 𝔪_R · B`, contradicting primitivity;
so `e` is a unit and `d = s e⁻¹`. -/
theorem dvd_of_mul_eq_of_notMem_maximalIdeal_map
    {R B : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing B] [IsDomain B] [Algebra R B]
    (hinj : Function.Injective (algebraMap R B))
    {s d : R} {w b : B}
    (hw : w ∉ (IsLocalRing.maximalIdeal R).map (algebraMap R B))
    (h : algebraMap R B s * b = algebraMap R B d * w) :
    s ∣ d := by
  by_cases hd : d = 0
  · exact ⟨0, by rw [hd, mul_zero]⟩
  rcases ValuationRing.dvd_total d s with ⟨e, he⟩ | hsd
  · have hds : algebraMap R B d ≠ 0 := fun h0 => hd (hinj (by simpa using h0))
    have h1 := h
    rw [he, map_mul, mul_assoc] at h1
    have hsub : algebraMap R B e * b = w := mul_left_cancel₀ hds h1
    by_cases heM : e ∈ IsLocalRing.maximalIdeal R
    · exfalso
      have : w ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R B) := by
        rw [← hsub]
        exact Ideal.mul_mem_right b _ (Ideal.mem_map_of_mem _ heM)
      exact hw this
    · have heun : IsUnit e := by
        rw [IsLocalRing.mem_maximalIdeal] at heM
        exact not_not.mp heM
      obtain ⟨u, hu⟩ := heun
      rw [← hu] at he
      refine ⟨↑u⁻¹, ?_⟩
      rw [he, mul_assoc, Units.mul_inv, mul_one]
  · exact hsd

theorem B_eq_inter_localizations
    {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    (hdom : IsDomain (TensorProduct K A R ⧸
      (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (u : FractionRing (TensorProduct K A R))
    (hP : Work.SpecLin.Alt.InLocalization u ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (hF : ∃ (b : TensorProduct K A R) (s : R), s ≠ 0 ∧
      u * algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R))
        ((Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) s)
      = algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) b) :
    ∃ b : TensorProduct K A R,
      u = algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) b := by
  classical
  by_cases hu : u = 0
  · exact ⟨0, by rw [hu, map_zero]⟩
  -- the `R`-algebra structure on `B = A ⊗[K] R` coming from the right factor
  letI : Algebra R (TensorProduct K A R) :=
    Algebra.TensorProduct.rightAlgebra (R := K) (A := A) (B := R)
  haveI hfree : Module.Free R (TensorProduct K A R) :=
    Work.SpecLin.Core.module_free_chartTensor (K := K) (A := A) (R := R)
  haveI hntA : Nontrivial A := (algebraMap A (TensorProduct K A R)).domain_nontrivial
  have hιinj : Function.Injective
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) := by
    have : Module.Free K R := Module.Free.of_divisionRing K R
    have : Module.Flat K R := Module.Flat.of_free
    exact Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap K A))
  have halg : algebraMap R (TensorProduct K A R)
      = (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) :
          R →+* TensorProduct K A R) :=
    Algebra.TensorProduct.algebraMap_eq_includeRight
  have hinc : ∀ r : R, (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) r
      = algebraMap R (TensorProduct K A R) r := fun r =>
    congrFun (congrArg (fun f : R →+* TensorProduct K A R => (f : R → TensorProduct K A R))
      halg.symm) r
  have hinj : Function.Injective (algebraMap R (TensorProduct K A R)) := by
    intro x y hxy
    exact hιinj (by rw [hinc x, hinc y]; exact hxy)
  obtain ⟨b, s, hs, hFs⟩ := hF
  obtain ⟨b0, s0, hs0I, hPs⟩ := hP
  rw [hinc] at hFs
  rw [← IsScalarTower.algebraMap_apply R (TensorProduct K A R)
    (FractionRing (TensorProduct K A R)) s] at hFs
  have hσinj : Function.Injective
      (algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R))) :=
    IsFractionRing.injective _ _
  have hσsne : algebraMap R (FractionRing (TensorProduct K A R)) s ≠ 0 := by
    intro h0
    rw [IsScalarTower.algebraMap_apply R (TensorProduct K A R)
      (FractionRing (TensorProduct K A R)) s] at h0
    have h2 : algebraMap R (TensorProduct K A R) s = 0 :=
      hσinj (h0.trans (map_zero (algebraMap (TensorProduct K A R)
        (FractionRing (TensorProduct K A R)))).symm)
    exact hs (hinj (by rw [h2, map_zero]))
  have hu_eq : u = algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) b
      * (algebraMap R (FractionRing (TensorProduct K A R)) s)⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hσsne).mpr hFs
  have hbne : b ≠ 0 := by
    intro hb0
    exact mul_ne_zero hu hσsne (hFs.trans (by rw [hb0, map_zero]))
  -- content normalisation of the numerator
  obtain ⟨c, b₁, hbc, hb₁⟩ :=
    Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map (R := R)
      (B := TensorProduct K A R) b
  have hcne : c ≠ 0 := fun hc0 => hbne (by rw [hbc, hc0, zero_smul])
  have hIpr :
      ((IsLocalRing.maximalIdeal R).map (algebraMap R (TensorProduct K A R))).IsPrime := by
    rw [halg]
    exact (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  have hb₁s0 : b₁ * s0 ∉
      (IsLocalRing.maximalIdeal R).map (algebraMap R (TensorProduct K A R)) := by
    intro hmem
    rcases hIpr.mem_or_mem hmem with h | h
    · exact hb₁ h
    · exact hs0I h
  -- `σ b = (σ_ι c) * σ b₁`
  have hbc' : b = algebraMap R (TensorProduct K A R) c * b₁ := by
    rw [hbc, Algebra.smul_def]
  have hσb : algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) b
      = algebraMap R (FractionRing (TensorProduct K A R)) c
        * algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) b₁ := by
    rw [hbc', map_mul, ← IsScalarTower.algebraMap_apply R (TensorProduct K A R)
      (FractionRing (TensorProduct K A R)) c]
  -- the cross relation in `B`
  have hleft : algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R))
        (algebraMap R (TensorProduct K A R) c * (b₁ * s0))
      = u * algebraMap R (FractionRing (TensorProduct K A R)) s
        * algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) s0 := by
    rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply R (TensorProduct K A R)
      (FractionRing (TensorProduct K A R)) c, ← mul_assoc, ← hσb, ← hFs]
  have hright : algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R))
        (algebraMap R (TensorProduct K A R) s * b0)
      = u * algebraMap R (FractionRing (TensorProduct K A R)) s
        * algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) s0 := by
    rw [map_mul, ← IsScalarTower.algebraMap_apply R (TensorProduct K A R)
      (FractionRing (TensorProduct K A R)) s, ← hPs]
    ring
  have hcross : algebraMap R (TensorProduct K A R) c * (b₁ * s0)
      = algebraMap R (TensorProduct K A R) s * b0 := by
    apply hσinj
    rw [hleft, hright]
  -- divisibility
  have hdvd : s ∣ c :=
    dvd_of_mul_eq_of_notMem_maximalIdeal_map hinj hb₁s0 hcross.symm
  obtain ⟨e, he⟩ := hdvd
  have hcs : algebraMap R (FractionRing (TensorProduct K A R)) c
      = algebraMap R (FractionRing (TensorProduct K A R)) s
        * algebraMap R (FractionRing (TensorProduct K A R)) e := by
    rw [he, map_mul]
  refine ⟨algebraMap R (TensorProduct K A R) e * b₁, ?_⟩
  rw [map_mul, ← IsScalarTower.algebraMap_apply R (TensorProduct K A R)
      (FractionRing (TensorProduct K A R)) e,
    hu_eq, mul_inv_eq_iff_eq_mul₀ hσsne, hσb, hcs]
  ring

end Work.SpecLin.Alt
