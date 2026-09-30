import Mathlib
import Submission.Work.SpecLin.Alt.denomIdeal
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Alt.B_eq_inter_localizations
import Submission.Work.SpecLin.Setup.unitOfAllHeightOneAux
import Submission.Work.CurveBasics.BaseChange.krullDimLE_tensor

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Hartogs/`S2` for the relative curve at a closed point of the special fibre

See the docstring of `Work.SpecLin.Setup.hartogsBridge` for the statement.  The proof is a
*descent along the generic fibre*:

assume that `x ∈ Frac B` is regular at every height-one prime contained in `N` (this is the
negation of the conclusion, via the denominator ideal).  Then `x` lies in the localisation
`O = B[(B∖N)·ι(R∖{0})]⁻¹` of `B = A ⊗[K] R`: the primes of `O` are the primes `q ⊆ N` of `B`
with `q ∩ R = 0`, and those inject into the one-dimensional generic fibre `A ⊗[K] Frac R`, so
they have height at most one, and the hypothesis applies to them; the maximal ideals of `O`
therefore satisfy `denomIdeal x ⊄ 𝔪`.

Writing `x = b/(w·r̄)` with `w ∉ N` and `r ∈ R ∖ {0}` (possible since `x ∈ O`), the element
`x·w = b/r̄` lies in `B_P` (as `x ∈ B_P` and `w ∉ P`) and in the generic fibre `B[ι(R∖{0})⁻¹]`;
the descent lemma `Work.SpecLin.Alt.B_eq_inter_localizations` then gives `x·w ∈ B`, and since
`w ∉ N` is a unit of `B_N` we get `x = (x·w)/w ∈ B_N`, contradicting `denomIdeal x ≤ N`.
-/

namespace Work.SpecLin.Setup

open scoped TensorProduct

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

/-- `Work.SpecLin.Alt.InLocalization x I` in terms of the denominator ideal. -/
theorem inLocalization_iff_denomIdeal_not_le' {B : Type u} [CommRing B] [IsDomain B]
    (x : FractionRing B) (I : Ideal B) :
    Work.SpecLin.Alt.InLocalization x I ↔ ¬ ((Work.SpecLin.Alt.denomIdeal x : Ideal B) ≤ I) := by
  constructor
  · rintro ⟨b, s, hs, hbs⟩ hle
    exact hs (hle ((Work.SpecLin.Alt.mem_denomIdeal x s).2 ⟨b, hbs⟩))
  · intro h
    by_contra hcon
    refine h fun d hd => ?_
    by_contra hdI
    rw [Work.SpecLin.Alt.mem_denomIdeal] at hd
    obtain ⟨b, hb⟩ := hd
    exact hcon ⟨b, d, hdI, hb⟩

noncomputable section

theorem hartogsBridge {K : Type u} [Field K] (A : Type u) [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] [Algebra.Smooth K A] [Ring.KrullDimLE 1 A]
    (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    [IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))]
    (N : Ideal (TensorProduct K A R)) [N.IsMaximal]
    (hPN : ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))) ≤ N)
    (x : FractionRing (TensorProduct K A R))
    (hxP : Work.SpecLin.Alt.InLocalization x ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (hD : (Work.SpecLin.Alt.denomIdeal x : Ideal (TensorProduct K A R)) ≤ N) :
    ∃ q : Ideal (TensorProduct K A R), q.IsPrime ∧ q.height = 1 ∧ q ≤ N ∧
      (Work.SpecLin.Alt.denomIdeal x : Ideal (TensorProduct K A R)) ≤ q := by
  classical
  haveI hNprime : N.IsPrime := (inferInstance : N.IsMaximal).isPrime
  -- abbreviations for the tensor product and the canonical map `R → B`
  set iota : R →+* TensorProduct K A R :=
    (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)).toRingHom with hiotadef
  have hιapp : ∀ r : R, iota r =
      Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) r := by
    intro r; rw [hiotadef]; rfl
  set P : Ideal (TensorProduct K A R) := (IsLocalRing.maximalIdeal R).map
    (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) with hPdef
  have hPN' : P ≤ N := by rw [hPdef]; exact hPN
  have hxP' : Work.SpecLin.Alt.InLocalization x P := by rw [hPdef]; exact hxP
  -- the special fibre `B ⧸ P ≅ A ⊗[K] κ` is a domain
  haveI hdom : IsDomain (TensorProduct K A R ⧸ P) := by
    rw [hPdef]
    exact (MulEquiv.isDomain_iff
      ((Algebra.TensorProduct.tensorQuotientEquiv (R := K) (S := K) (T := R) (A := A)
        (I := IsLocalRing.maximalIdeal R)).toRingEquiv.toMulEquiv)).mp
      (inferInstance : IsDomain (TensorProduct K A (IsLocalRing.ResidueField R)))
  haveI hPprime : P.IsPrime := (Ideal.Quotient.isDomain_iff_prime (I := P)).mp hdom
  -- negation of the goal: regularity at all height-one primes below `N`
  by_contra hcon
  have hInLoc : ∀ q : Ideal (TensorProduct K A R), q.IsPrime → q.height = 1 → q ≤ N →
      Work.SpecLin.Alt.InLocalization x q := by
    intro q hq hht hle
    rw [inLocalization_iff_denomIdeal_not_le']
    intro hDq
    exact hcon ⟨q, hq, hht, hle, hDq⟩
  have hιinj : Function.Injective iota := by
    rw [hiotadef]
    exact Algebra.TensorProduct.includeRight_injective (R := K) (A := A) (B := R)
      (RingHom.injective (algebraMap K A))
  -- the multiplicative set `S' = (B∖N) · ι(R∖{0})`
  set S' : Submonoid (TensorProduct K A R) :=
    { carrier := {z | ∃ w ∈ N.primeCompl, ∃ r ∈ nonZeroDivisors R, z = w * iota r}
      one_mem' := ⟨1, N.primeCompl.one_mem, 1, one_mem _, by rw [map_one, mul_one]⟩
      mul_mem' := by
        rintro z₁ z₂ ⟨w₁, hw₁, r₁, hr₁, rfl⟩ ⟨w₂, hw₂, r₂, hr₂, rfl⟩
        exact ⟨w₁ * w₂, mul_mem hw₁ hw₂, r₁ * r₂, mul_mem hr₁ hr₂,
          by rw [map_mul]; ring⟩ }
    with hS'def
  have hS'le : S' ≤ nonZeroDivisors (TensorProduct K A R) := by
    intro z hz
    rw [hS'def] at hz
    obtain ⟨w, hw, r, hr, rfl⟩ := hz
    have hw0 : w ≠ 0 := fun h0 => hw (by rw [h0]; exact N.zero_mem)
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact mul_ne_zero hw0 (fun h => nonZeroDivisors.ne_zero hr (hιinj (by simpa using h)))
  -- the ring `O = B[S'⁻¹]`, realised inside `Frac B`
  set O : Subalgebra (TensorProduct K A R) (FractionRing (TensorProduct K A R)) :=
    Localization.subalgebra.ofField (FractionRing (TensorProduct K A R)) S' hS'le with hOdef
  haveI hOloc : IsLocalization S' ↥O :=
    Localization.subalgebra.isLocalization_ofField (FractionRing (TensorProduct K A R)) S' hS'le
  have hcoeO : ∀ o : ↥O, (algebraMap ↥O (FractionRing (TensorProduct K A R)) o
      : FractionRing (TensorProduct K A R)) = (o : FractionRing (TensorProduct K A R)) :=
    fun o => rfl
  have hcoeB : ∀ b : TensorProduct K A R,
      ((algebraMap (TensorProduct K A R) ↥O b : ↥O) : FractionRing (TensorProduct K A R))
        = algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) b :=
    fun b => Subalgebra.coe_algebraMap O b
  -- the generic fibre is a localisation of `B` at `ι(R∖{0})`
  haveI hgenloc : IsLocalization (Submonoid.map iota (nonZeroDivisors R))
      (TensorProduct K A (FractionRing R)) := by
    rw [hiotadef]
    exact Work.SpecLin.Setup.isLocalization_tensorProduct_fractionRing
  -- main step: `x ∈ O`
  have hxO : x ∈ O := by
    by_contra hxO
    set J : Ideal ↥O := Work.SpecLin.Alt.denomIdeal x with hJdef
    have hJtop : J ≠ ⊤ := by
      intro hJ
      rw [hJdef] at hJ
      obtain ⟨c, hc⟩ := (Work.SpecLin.Alt.denomIdeal_eq_top_iff (A := ↥O)
        (K := FractionRing (TensorProduct K A R)) x).mp hJ
      exact hxO (by rw [hc]; exact c.2)
    obtain ⟨𝔪, h𝔪max, hJle⟩ := Ideal.exists_le_maximal J hJtop
    haveI h𝔪prime : 𝔪.IsPrime := h𝔪max.isPrime
    set q : Ideal (TensorProduct K A R) :=
      𝔪.comap (algebraMap (TensorProduct K A R) ↥O) with hqdef
    have hqprime : q.IsPrime := by rw [hqdef]; exact Ideal.IsPrime.comap _
    have hqN : q ≤ N := by
      intro b hb
      by_contra hbN
      have hbS' : b ∈ S' := by
        rw [hS'def]
        exact ⟨b, hbN, 1, one_mem _, by rw [map_one, mul_one]⟩
      have hunit : IsUnit (algebraMap (TensorProduct K A R) ↥O b) :=
        IsLocalization.map_units ↥O (⟨b, hbS'⟩ : S')
      have hmem : algebraMap (TensorProduct K A R) ↥O b ∈ 𝔪 := by
        rw [hqdef] at hb
        exact hb
      exact (Ideal.IsMaximal.ne_top h𝔪max)
        (Ideal.eq_top_of_isUnit_mem 𝔪 hmem hunit)
    have hdisj : Disjoint
        (↑(Submonoid.map iota (nonZeroDivisors R)) : Set (TensorProduct K A R))
        (q : Set (TensorProduct K A R)) := by
      rw [Set.disjoint_left]
      intro z hz hzq
      obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.mp hz
      have hrS' : iota r ∈ S' := by
        rw [hS'def]
        exact ⟨1, N.primeCompl.one_mem, r, hr, by rw [one_mul]⟩
      have hunit : IsUnit (algebraMap (TensorProduct K A R) ↥O (iota r)) :=
        IsLocalization.map_units ↥O (⟨iota r, hrS'⟩ : S')
      have hmem : algebraMap (TensorProduct K A R) ↥O (iota r) ∈ 𝔪 := by
        rw [hqdef] at hzq
        exact hzq
      exact (Ideal.IsMaximal.ne_top h𝔪max)
        (Ideal.eq_top_of_isUnit_mem 𝔪 hmem hunit)
    have hhtq' : (q.height : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) := by
      have h1 : (q.map (algebraMap (TensorProduct K A R)
          (TensorProduct K A (FractionRing R)))).height = q.height :=
        IsLocalization.height_map_of_disjoint (Submonoid.map iota (nonZeroDivisors R)) q hdisj
      have h2 : (q.map (algebraMap (TensorProduct K A R)
          (TensorProduct K A (FractionRing R)))).height ≤
            ringKrullDim (TensorProduct K A (FractionRing R)) := by
        refine Ideal.height_le_ringKrullDim_of_ne_top ?_
        exact (IsLocalization.map_algebraMap_ne_top_iff_disjoint
          (Submonoid.map iota (nonZeroDivisors R)) (TensorProduct K A (FractionRing R)) q).mpr hdisj
      have h3 : ringKrullDim (TensorProduct K A (FractionRing R)) ≤ (1 : WithBot ℕ∞) :=
        Ring.krullDimLE_iff.mp (Work.CurveBasics.BaseChange.krullDimLE_tensor (k := K)
          (F := FractionRing R) (R := A) (n := 1) (by assumption))
      calc (q.height : WithBot ℕ∞) = ((q.map (algebraMap (TensorProduct K A R)
              (TensorProduct K A (FractionRing R)))).height : WithBot ℕ∞) := by rw [h1]
        _ ≤ ringKrullDim (TensorProduct K A (FractionRing R)) := h2
        _ ≤ 1 := h3
    have hhtq : q.height ≤ 1 := by exact_mod_cast hhtq'
    -- a witness for `denomIdeal x ⊄ 𝔪`
    have hwit : ∃ s : ↥O, s ∉ 𝔪 ∧
        x * (s : FractionRing (TensorProduct K A R)) ∈ O := by
      by_cases hqbot : q = ⊥
      · -- `q = 0`: use the quotient representation of `x`
        obtain ⟨b, s, hs, hxs⟩ := IsFractionRing.div_surjective (TensorProduct K A R) x
        have hsmem : x * algebraMap (TensorProduct K A R)
            (FractionRing (TensorProduct K A R)) s
            = algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) b := by
          rw [← hxs, div_mul_cancel₀ _
            (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)]
        refine ⟨algebraMap (TensorProduct K A R) ↥O s, ?_, ?_⟩
        · intro hmem
          have hs0 : s ∈ (⊥ : Ideal (TensorProduct K A R)) := by
            rw [← hqbot, hqdef]
            exact hmem
          exact nonZeroDivisors.ne_zero hs (by simpa using hs0)
        · rw [hcoeB s, hsmem]
          simpa only [hcoeB b] using (algebraMap (TensorProduct K A R) ↥O b).2
      · -- otherwise `q` is height one and the hypothesis applies
        have hht1 : q.height = 1 := by
          refine le_antisymm hhtq ?_
          rw [Order.one_le_iff_ne_zero]
          intro h0
          exact hqbot (Ideal.height_eq_zero_iff_eq_bot.mp h0)
        obtain ⟨b, s, hs, hbs⟩ := hInLoc q hqprime hht1 hqN
        refine ⟨algebraMap (TensorProduct K A R) ↥O s, ?_, ?_⟩
        · intro hmem
          exact hs (by rw [hqdef]; exact hmem)
        · rw [hcoeB s, hbs]
          simpa only [hcoeB b] using (algebraMap (TensorProduct K A R) ↥O b).2
    obtain ⟨s, hs𝔪, hxsO⟩ := hwit
    have hsJ : s ∈ J := by
      rw [hJdef, Work.SpecLin.Alt.mem_denomIdeal]
      exact ⟨⟨x * (s : FractionRing (TensorProduct K A R)), hxsO⟩, rfl⟩
    exact hs𝔪 (hJle hsJ)
  -- write `x = b/(w·r̄)` with `w ∉ N` and `r ≠ 0`
  obtain ⟨bz, sz, hszS', hxsz⟩ := (Work.SpecLin.Alt.mem_subalgebra_ofField_iff
    (A := TensorProduct K A R) (K := FractionRing (TensorProduct K A R)) S' hS'le x).mp hxO
  rw [hS'def] at hszS'
  obtain ⟨w, hw, r, hr, rfl⟩ := hszS'
  have hwP : w ∉ P := fun hmem => hw (hPN' hmem)
  have hσne : algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R))
      (w * iota r) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS'le (by
      rw [hS'def]
      exact ⟨w, hw, r, hr, rfl⟩))
  have hfac : x * algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R))
      (w * iota r) = algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) bz := by
    rw [hxsz, mul_assoc, inv_mul_cancel₀ hσne, mul_one]
  have hsplit : (x * algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) w) *
      algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) (iota r)
      = algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) bz := by
    rw [← hfac, map_mul]
    ring
  have hF' : ∃ (b' : TensorProduct K A R) (s' : R), s' ≠ 0 ∧
      (x * algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) w) *
        algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R))
          (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) s')
        = algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) b' := by
    refine ⟨bz, r, nonZeroDivisors.ne_zero hr, ?_⟩
    rw [← hιapp r]
    exact hsplit
  -- `x·w` is still regular at the fibre prime
  have hP'' : Work.SpecLin.Alt.InLocalization
      (x * algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) w) P := by
    obtain ⟨b0, s0, hs0, hx0⟩ := hxP'
    refine ⟨b0 * (w * w), s0 * w, ?_, ?_⟩
    · intro hmem
      rcases hPprime.mem_or_mem hmem with h | h
      · exact hs0 h
      · exact hwP h
    · rw [map_mul, map_mul, map_mul, ← hx0]
      ring
  rw [hPdef] at hP''
  obtain ⟨b1, hb1⟩ := Work.SpecLin.Alt.B_eq_inter_localizations (K := K) (A := A) (R := R) hdom
    (x * algebraMap (TensorProduct K A R) (FractionRing (TensorProduct K A R)) w) hP'' hF'
  exact ((inLocalization_iff_denomIdeal_not_le' x N).mp ⟨b1, w, hw, hb1⟩) hD

/-- **The `InLocalization` form of `hartogsBridge`** — the statement
`Work.SpecLin.Alt.refinedHartogs` (the "crux" of the affine-chart proof of specialisation of
linear equivalence), now proved: a rational function on the relative curve `B = A ⊗[K] R` which
is regular at the fibre prime `P = 𝔪_R·B` and at every height-one prime contained in a maximal
ideal `N ⊇ P` is regular at `N`.

The `denomIdeal` form is `Work.SpecLin.Setup.hartogsBridge`; the passage between the two is
`inLocalization_iff_denomIdeal_not_le'`. -/
theorem hartogsBridge_inLocalization {K : Type u} [Field K] (A : Type u) [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Algebra.Smooth K A]
    [Ring.KrullDimLE 1 A] (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    [IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))]
    (N : Ideal (TensorProduct K A R)) [N.IsMaximal]
    (hPN : ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))) ≤ N)
    (x : FractionRing (TensorProduct K A R))
    (hxP : Work.SpecLin.Alt.InLocalization x ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (hxq : ∀ p : Ideal (TensorProduct K A R), p.IsPrime → p.height = 1 → p ≤ N →
      Work.SpecLin.Alt.InLocalization x p) :
    Work.SpecLin.Alt.InLocalization x N := by
  by_contra hxN
  rw [inLocalization_iff_denomIdeal_not_le'] at hxN
  obtain ⟨q, hq, hq1, hqN, hDq⟩ :=
    hartogsBridge (K := K) A hA R N hPN x hxP (not_not.mp hxN)
  exact (inLocalization_iff_denomIdeal_not_le' x q).mp (hxq q hq hq1 hqN) hDq

/-- **The `IsUnitAt` form of `hartogsBridge`** — the statement
`Work.SpecLin.Setup.cruxPITdomain`, now proved: a rational function which is a unit at the
fibre prime `P = 𝔪_R·B` and at every height-one prime contained in `N ⊇ P` is a unit at `N`. -/
theorem cruxPITdomain_of_hartogsBridge {K : Type u} [Field K] (A : Type u) [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Algebra.Smooth K A]
    [Ring.KrullDimLE 1 A] (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    [IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))]
    (N : Ideal (TensorProduct K A R)) [N.IsMaximal]
    (hPN : ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))) ≤ N)
    (u : FractionRing (TensorProduct K A R))
    (hP : Work.SpecLin.Alt.IsUnitAt u ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (hht : ∀ p : Ideal (TensorProduct K A R), p.IsPrime → p.height = 1 → p ≤ N →
      Work.SpecLin.Alt.IsUnitAt u p) :
    Work.SpecLin.Alt.IsUnitAt u N :=
  ⟨hartogsBridge_inLocalization (K := K) A hA R N hPN u hP.1
      (fun p hp hp1 hpN => (hht p hp hp1 hpN).1),
   hartogsBridge_inLocalization (K := K) A hA R N hPN u⁻¹ hP.2
      (fun p hp hp1 hpN => (hht p hp hp1 hpN).2)⟩

end

end Work.SpecLin.Setup
