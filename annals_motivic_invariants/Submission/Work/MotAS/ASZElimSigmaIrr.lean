import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

namespace Work.MotAS

theorem ASZElimSigmaIrr (K : Type) [Field K] (L : Type) [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (f : MvPolynomial (Fin 2) K) (u : L) (hu : IsUnit u)
    (g : ZMod 5 → MvPolynomial (Fin 2) L)
    (hirr : ∀ i, Irreducible (g i))
    (hconj : ∀ i, MvPolynomial.map (σ : L →+* L) (g i) = g (i + 1))
    (hfac : MvPolynomial.map (algebraMap K L) f = MvPolynomial.C u * ∏ i, g i)
    (hne : ∀ i j, i ≠ j → ¬ Associated (g i) (g j)) :
    Irreducible f := by
  classical
  -- (0) `σ` acts trivially on the image of the coefficient extension
  have hcomp : (σ : L →+* L).comp (algebraMap K L) = algebraMap K L := by
    ext k
    rw [RingHom.comp_apply]
    exact σ.commutes k
  have map_fix : ∀ a : MvPolynomial (Fin 2) K,
      MvPolynomial.map (σ : L →+* L) (MvPolynomial.map (algebraMap K L) a)
        = MvPolynomial.map (algebraMap K L) a := by
    intro a
    rw [MvPolynomial.map_map, hcomp]
  -- (1) unit transfer along the coefficient extension `K[X] → L[X]`
  have isUnit_transfer : ∀ a : MvPolynomial (Fin 2) K,
      IsUnit (MvPolynomial.map (algebraMap K L) a) → IsUnit a := by
    intro a h
    rw [MvPolynomial.isUnit_iff] at h
    rw [MvPolynomial.isUnit_iff]
    refine ⟨?_, ?_⟩
    · have h0 : IsUnit (algebraMap K L (a.coeff 0)) := by
        simpa [MvPolynomial.coeff_map] using h.1
      rw [isUnit_iff_ne_zero] at h0 ⊢
      intro hc
      rw [hc, map_zero] at h0
      exact h0 rfl
    · intro i hi
      have hni : IsNilpotent (algebraMap K L (a.coeff i)) := by
        simpa [MvPolynomial.coeff_map] using h.2 i hi
      rw [isNilpotent_iff_eq_zero] at hni ⊢
      exact FaithfulSMul.algebraMap_injective K L (hni.trans (map_zero (algebraMap K L)).symm)
  -- (2) basic nonvanishing
  have hC_u_unit : IsUnit (MvPolynomial.C u : MvPolynomial (Fin 2) L) :=
    hu.map (MvPolynomial.C : L →+* MvPolynomial (Fin 2) L)
  have hg_ne : ∀ i, g i ≠ 0 := by
    intro i hgi
    rcases (hirr i).isUnit_or_isUnit
        (show g i = (0 : MvPolynomial (Fin 2) L) * 0 by rw [hgi, mul_zero]) with h | h
    · exact not_isUnit_zero h
    · exact not_isUnit_zero h
  have hprod_ne : (∏ i, g i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hg_ne i)
  have hfac_ne : MvPolynomial.map (algebraMap K L) f ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero hC_u_unit.ne_zero hprod_ne
  have hf_ne : f ≠ 0 := by
    intro hf0
    exact hfac_ne (by rw [hf0, map_zero])
  -- `f` is not a unit (a unit would force `∏ g i` to be constant)
  have hf_notunit : ¬ IsUnit f := by
    intro hf
    have hm : IsUnit (MvPolynomial.map (algebraMap K L) f) :=
      hf.map (MvPolynomial.map (algebraMap K L))
    rw [hfac] at hm
    have hP : IsUnit (∏ i, g i) := by
      obtain ⟨y, hy⟩ := isUnit_iff_dvd_one.mp hm
      rw [isUnit_iff_dvd_one]
      exact ⟨MvPolynomial.C u * y, by rw [hy]; ring⟩
    have hg0 : IsUnit (g 0) := by
      rw [isUnit_iff_dvd_one]
      exact dvd_trans (Finset.dvd_prod_of_mem g (Finset.mem_univ 0))
        (isUnit_iff_dvd_one.mp hP)
    exact (hirr 0).not_isUnit hg0
  refine ⟨hf_notunit, ?_⟩
  intro a b hab
  have hAB : MvPolynomial.map (algebraMap K L) a * MvPolynomial.map (algebraMap K L) b
      = MvPolynomial.C u * ∏ i, g i := by
    have hm : MvPolynomial.map (algebraMap K L) (a * b)
        = MvPolynomial.map (algebraMap K L) a * MvPolynomial.map (algebraMap K L) b :=
      map_mul _ a b
    rw [← hm, ← hab, hfac]
  have hAB_ne : MvPolynomial.map (algebraMap K L) a * MvPolynomial.map (algebraMap K L) b ≠ 0 := by
    rw [hAB]; exact mul_ne_zero hC_u_unit.ne_zero hprod_ne
  have hA_ne : MvPolynomial.map (algebraMap K L) a ≠ 0 := fun h => hAB_ne (by rw [h, zero_mul])
  have hB_ne : MvPolynomial.map (algebraMap K L) b ≠ 0 := fun h => hAB_ne (by rw [h, mul_zero])
  -- (3) the divisor set of `a` is invariant under the cyclic shift
  have hshift : ∀ i, g i ∣ MvPolynomial.map (algebraMap K L) a →
      g (i + 1) ∣ MvPolynomial.map (algebraMap K L) a := by
    intro i hi
    have h1 := map_dvd (MvPolynomial.map (σ : L →+* L)) hi
    rw [hconj i, map_fix a] at h1
    exact h1
  have all_of_one : ∀ i0, g i0 ∣ MvPolynomial.map (algebraMap K L) a →
      ∀ j, g j ∣ MvPolynomial.map (algebraMap K L) a := by
    intro i0 hi0 j
    have key : ∀ k : ℕ, g (i0 + (k : ZMod 5)) ∣ MvPolynomial.map (algebraMap K L) a := by
      intro k
      induction k with
      | zero => simpa using hi0
      | succ k ih =>
          have h := hshift (i0 + (k : ZMod 5)) ih
          simpa only [Nat.cast_succ, add_assoc] using h
    have hj : j = i0 + ((j - i0).val : ZMod 5) := by
      rw [ZMod.natCast_zmod_val]; abel
    rw [hj]
    exact key (j - i0).val
  -- (4) any non-unit non-zero divisor of `C u * ∏ g i` is divisible by some `g i`
  have exists_g_dvd : ∀ X : MvPolynomial (Fin 2) L, X ∣ MvPolynomial.C u * ∏ i, g i →
      ¬ IsUnit X → X ≠ 0 → ∃ i, g i ∣ X := by
    intro X hXdiv hXnu hXne
    obtain ⟨h, hhirr, hhdvd⟩ := WfDvdMonoid.exists_irreducible_factor hXnu hXne
    have h1 : h ∣ MvPolynomial.C u * ∏ i, g i := hhdvd.trans hXdiv
    have h2 : h ∣ ∏ i, g i := (IsUnit.dvd_mul_left hC_u_unit).mp h1
    obtain ⟨i, _, hi⟩ := (hhirr.prime.dvd_finsetProd_iff g).mp h2
    rcases (Irreducible.dvd_iff (hirr i)).mp hi with h3 | h3
    · exact absurd h3 hhirr.not_isUnit
    · exact ⟨i, (Associated.dvd_iff_dvd_left h3.symm).mp hhdvd⟩
  -- (5) no `g i` divides both `a` and `b`
  have hdisj : ∀ i, ¬ (g i ∣ MvPolynomial.map (algebraMap K L) a ∧
      g i ∣ MvPolynomial.map (algebraMap K L) b) := by
    intro i ⟨hAi, hBi⟩
    obtain ⟨x, hx⟩ := hAi
    obtain ⟨y, hy⟩ := hBi
    have h1 : g i * (x * MvPolynomial.map (algebraMap K L) b)
        = g i * (MvPolynomial.C u * (∏ j ∈ Finset.univ.erase i, g j)) := by
      have h0 : (g i * x) * MvPolynomial.map (algebraMap K L) b
          = g i * (MvPolynomial.C u * (∏ j ∈ Finset.univ.erase i, g j)) := by
        rw [← hx, hAB, ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i)]
        first | refl_ring1 | ring
      rw [mul_assoc] at h0
      exact h0
    have h2 : x * MvPolynomial.map (algebraMap K L) b
        = MvPolynomial.C u * (∏ j ∈ Finset.univ.erase i, g j) :=
      mul_left_cancel₀ (hg_ne i) h1
    have hdvd : g i ∣ MvPolynomial.C u * (∏ j ∈ Finset.univ.erase i, g j) := by
      refine ⟨x * y, ?_⟩
      rw [← h2, hy]; ring
    rcases (hirr i).prime.dvd_or_dvd hdvd with hcase | hcase
    · exact (hirr i).not_isUnit
        (isUnit_iff_dvd_one.mpr (dvd_trans hcase (isUnit_iff_dvd_one.mp hC_u_unit)))
    · obtain ⟨j, hjmem, hj⟩ := ((hirr i).prime.dvd_finsetProd_iff g).mp hcase
      obtain ⟨hji, -⟩ := Finset.mem_erase.mp hjmem
      have hij : i ≠ j := fun h => hji h.symm
      rcases (Irreducible.dvd_iff (hirr j)).mp hj with h3 | h3
      · exact absurd h3 (hirr i).not_isUnit
      · exact hne i j hij h3.symm
  -- (6) the dichotomy: either every `g i` divides `a`, or `a` is a unit
  by_cases hA_all : ∀ i, g i ∣ MvPolynomial.map (algebraMap K L) a
  · right
    have hB_none : ∀ i, ¬ g i ∣ MvPolynomial.map (algebraMap K L) b :=
      fun i hi => hdisj i ⟨hA_all i, hi⟩
    have hB_unit : IsUnit (MvPolynomial.map (algebraMap K L) b) := by
      by_contra hnu
      obtain ⟨i, hi⟩ := exists_g_dvd (MvPolynomial.map (algebraMap K L) b)
        ⟨MvPolynomial.map (algebraMap K L) a, by rw [← hAB]; ring⟩ hnu hB_ne
      exact hB_none i hi
    exact isUnit_transfer b hB_unit
  · left
    obtain ⟨i0, hi0⟩ := not_forall.mp hA_all
    have hA_none : ∀ i, ¬ g i ∣ MvPolynomial.map (algebraMap K L) a := by
      intro i hi
      exact hi0 (all_of_one i hi i0)
    have hA_unit : IsUnit (MvPolynomial.map (algebraMap K L) a) := by
      by_contra hnu
      obtain ⟨i, hi⟩ := exists_g_dvd (MvPolynomial.map (algebraMap K L) a)
        ⟨MvPolynomial.map (algebraMap K L) b, hAB.symm⟩ hnu hA_ne
      exact hA_none i hi
    exact isUnit_transfer a hA_unit

end Work.MotAS
