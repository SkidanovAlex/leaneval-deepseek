import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.NumberField.House
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# A `ℤ`-basis of the ring of integers with house at most one, in degree one

If `K` is a number field of degree `1` over `ℚ`, then `K ≅ ℚ`, so the ring of integers
`𝓞 K` is `ℤ`, with `ℤ`-basis `{1}`.  The house of `1` is `1`, so this gives a `ℤ`-basis of
`𝓞 K` all of whose elements have house at most one.

The two ingredients are:
* every element of `K` is a rational number, since `ℚ → K` is bijective when `finrank ℚ K = 1`;
* an algebraic integer in `K` is therefore an integer (the rational roots of monic integer
  polynomials are integers, i.e. `ℤ` is integrally closed in `ℚ`).
-/

open scoped NumberField

noncomputable section

namespace Commons.NumberTheory.NumberField

open Function Module.Free

/-- Every integral element of a degree-one number field `K` is an integer: the canonical ring
homomorphism `ℚ → K` is bijective, and `ℤ` is integrally closed in `ℚ`. -/
lemma integral_eq_intCast_of_finrank_eq_one (K : Type*) [Field K] [NumberField K]
    (hf : Module.finrank ℚ K = 1) {x : K} (hx : IsIntegral ℤ x) :
    ∃ n : ℤ, x = (n : K) := by
  classical
  have hbij : Function.Bijective (algebraMap ℚ K) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := ℚ) (E := K)).mp hf
  let e : ℚ ≃+* K := RingEquiv.ofBijective (algebraMap ℚ K) hbij
  let q : ℚ := e.symm x
  have hcompat : (algebraMap ℤ ℚ).comp (RingHom.id ℤ) =
      e.symm.toRingHom.comp (algebraMap ℤ K) := by
    ext z
    simp [e]
  have hqint : IsIntegral ℤ q := by
    dsimp [q]
    exact IsIntegral.map_of_comp_eq (R := ℤ) (S := K) (T := ℤ) (U := ℚ)
      (φ := RingHom.id ℤ) (ψ := e.symm.toRingHom) hcompat hx
  rcases (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hqint with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hxq : x = e q := by
    dsimp [q]
    exact (e.apply_symm_apply x).symm
  calc
    x = e q := hxq
    _ = e (algebraMap ℤ ℚ n) := by rw [← hn]
    _ = (n : K) := by simp [e]

/-- In a degree-one number field, the ring of integers admits a `ℤ`-basis all of whose
elements have house at most `1`. -/
lemma exists_ringOfIntegers_basis_house_le_one_of_finrank_eq_one
    (K : Type*) [Field K] [NumberField K] (hf : Module.finrank ℚ K = 1) :
    ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) ℤ
        (NumberField.RingOfIntegers K),
      ∀ i, NumberField.house ((b i : NumberField.RingOfIntegers K) : K) ≤ 1 := by
  classical
  have hcard :
      Fintype.card (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := NumberField.RingOfIntegers K)]
    rw [NumberField.RingOfIntegers.rank K]
    exact hf
  have hsub : Subsingleton (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) := by
    rcases (Fintype.card_eq_one_iff.mp hcard) with ⟨i0, hi0⟩
    exact subsingleton_of_forall_eq i0 hi0
  let v : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) →
      NumberField.RingOfIntegers K := fun _ => 1
  have hli : LinearIndependent ℤ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' : (∑ j, (g j : NumberField.RingOfIntegers K)) = 0 := by
      simpa [v, zsmul_eq_mul] using hg
    have hsum : (∑ j, (g j : NumberField.RingOfIntegers K)) =
        (g i : NumberField.RingOfIntegers K) := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro b _ hbi
        exact absurd (hsub.allEq b i) hbi
      · intro hnot
        exact absurd (Finset.mem_univ i) hnot
    have hzero : (g i : NumberField.RingOfIntegers K) = 0 := by rw [← hsum]; exact hg'
    exact Int.cast_eq_zero.mp hzero
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro a _
    have h1mem : (1 : NumberField.RingOfIntegers K) ∈ Submodule.span ℤ (Set.range v) :=
      Submodule.subset_span ⟨Classical.choice (inferInstance : Nonempty
        (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K))), by simp [v]⟩
    obtain ⟨n, hn⟩ := integral_eq_intCast_of_finrank_eq_one K hf a.2
    have haeq : a = (n : NumberField.RingOfIntegers K) :=
      Subtype.ext (hn.trans (map_intCast (algebraMap (NumberField.RingOfIntegers K) K) n).symm)
    have hmem : (n : ℤ) • (1 : NumberField.RingOfIntegers K) ∈
        Submodule.span ℤ (Set.range v) :=
      Submodule.smul_mem _ (n : ℤ) h1mem
    have hsmul : (n : ℤ) • (1 : NumberField.RingOfIntegers K) =
        (n : NumberField.RingOfIntegers K) := by simp [zsmul_eq_mul]
    rw [haeq, ← hsmul]
    exact hmem
  refine ⟨Module.Basis.mk hli hsp, ?_⟩
  intro i
  have hbi : (Module.Basis.mk hli hsp i : NumberField.RingOfIntegers K) = 1 := by
    simp [Module.Basis.coe_mk, v]
  rw [show ((Module.Basis.mk hli hsp i : NumberField.RingOfIntegers K) : K) = ((1 : ℤ) : K) by
    rw [hbi]; simp]
  rw [NumberField.house_intCast]
  norm_num

/-- If `K` is a number field of degree `1` over `ℚ`, then the ring of integers `𝓞 K` admits a
`ℤ`-basis all of whose elements have house at most `1` (with respect to the canonical choice of
basis index `Module.Free.ChooseBasisIndex`). -/
theorem basis_house_le_one_of_finrank_eq_one :
    ∀ (K : Type*) [Field K] [NumberField K],
      Module.finrank ℚ K = 1 →
        ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) ℤ
            (NumberField.RingOfIntegers K),
          ∀ i, NumberField.house ((b i : NumberField.RingOfIntegers K) : K) ≤ 1 := by
  intro K _ _ hf
  exact exists_ringOfIntegers_basis_house_le_one_of_finrank_eq_one K hf

end Commons.NumberTheory.NumberField