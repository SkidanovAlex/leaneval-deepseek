import Mathlib.Algebra.Lie.SerreConstruction
import Mathlib.Algebra.Lie.Quotient

namespace Commons.Algebra.Lie.SerreConstruction

open LieSubmodule

/-- The universal property of the Serre construction: given elements `H i`, `E i`, `F i` of a Lie
algebra `K` satisfying the Serre relations of the Cartan matrix `CM`, there is a Lie algebra
homomorphism from the Serre-presented algebra into `K` sending the generators accordingly.

Suggested proof: lift the assignment `Generators.H i ↦ H i`, `Generators.E i ↦ E i`,
`Generators.F i ↦ F i` to a Lie hom `f : FreeLieAlgebra R _ →ₗ⁅R⁆ K` using
`FreeLieAlgebra.lift`; each of the six families of Serre relation elements
(`CartanMatrix.Relations.HH, EF, HE, HF, adE, adF`) lies in `ker f` by the hypotheses, hence the
ideal `CartanMatrix.Relations.toIdeal R CM` is contained in `ker f`
(`LieSubmodule.lieSpan_le` together with `Set.range_subset_iff` and
`LieSubmodule.lie_mem`-closure of the kernel).  Then factor `f` through the quotient using
`Submodule.liftQ` (the induced linear map, well defined since the ideal is in the kernel) and check
the bracket axiom by quotient induction with `LieSubmodule.Quotient.mk_bracket`. -/
theorem liftOfSerrePresentation {R B K : Type*} [CommRing R] [DecidableEq B] [LieRing K]
    [LieAlgebra R K] (CM : Matrix B B ℤ) (H E F : B → K)
    (hHH : ∀ i j, ⁅H i, H j⁆ = 0)
    (hHE : ∀ i j, ⁅H i, E j⁆ = (CM i j : R) • E j)
    (hHF : ∀ i j, ⁅H i, F j⁆ = -(CM i j : R) • F j)
    (hEF : ∀ i j, ⁅E i, F j⁆ = if i = j then H i else 0)
    (hadE : ∀ i j, (LieAlgebra.ad R K (E i) ^ ((-CM i j).toNat)) ⁅E i, E j⁆ = 0)
    (hadF : ∀ i j, (LieAlgebra.ad R K (F i) ^ ((-CM i j).toNat)) ⁅F i, F j⁆ = 0) :
    ∃ φ : (FreeLieAlgebra R (CartanMatrix.Generators B) ⧸ CartanMatrix.Relations.toIdeal R CM) →ₗ⁅R⁆ K,
      (∀ i, φ (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal R CM)
          (FreeLieAlgebra.of R (CartanMatrix.Generators.H i))) = H i) ∧
      (∀ i, φ (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal R CM)
          (FreeLieAlgebra.of R (CartanMatrix.Generators.E i))) = E i) ∧
      (∀ i, φ (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal R CM)
          (FreeLieAlgebra.of R (CartanMatrix.Generators.F i))) = F i) := by
  let L := FreeLieAlgebra R (CartanMatrix.Generators B)
  let g : CartanMatrix.Generators B → K := fun x => match x with
    | .H i => H i
    | .E i => E i
    | .F i => F i
  let f : L →ₗ⁅R⁆ K := FreeLieAlgebra.lift R g
  have hfH : ∀ i, f (FreeLieAlgebra.of R (CartanMatrix.Generators.H i)) = H i :=
    fun i => FreeLieAlgebra.lift_of_apply g (CartanMatrix.Generators.H i)
  have hfE : ∀ i, f (FreeLieAlgebra.of R (CartanMatrix.Generators.E i)) = E i :=
    fun i => FreeLieAlgebra.lift_of_apply g (CartanMatrix.Generators.E i)
  have hfF : ∀ i, f (FreeLieAlgebra.of R (CartanMatrix.Generators.F i)) = F i :=
    fun i => FreeLieAlgebra.lift_of_apply g (CartanMatrix.Generators.F i)
  have hmap_ad : ∀ x y : L, f ((LieAlgebra.ad R L x) y) = (LieAlgebra.ad R K (f x)) (f y) := by
    intro x y
    rw [LieAlgebra.ad_apply, LieHom.map_lie, LieAlgebra.ad_apply]
  have hpow : ∀ (n : ℕ) (x y : L),
      f ((LieAlgebra.ad R L x ^ n) y) = (LieAlgebra.ad R K (f x) ^ n) (f y) := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      rw [pow_succ, Module.End.mul_apply, ih, hmap_ad, pow_succ, Module.End.mul_apply]
  have keyHH : ∀ p : B × B, CartanMatrix.Relations.HH R p ∈ f.ker := by
    rintro ⟨i, j⟩
    rw [LieHom.mem_ker]
    simp only [CartanMatrix.Relations.HH, Function.uncurry_apply_pair, Function.comp_apply]
    rw [LieHom.map_lie, hfH i, hfH j, hHH i j]
  have keyEF : ∀ p : B × B, CartanMatrix.Relations.EF R p ∈ f.ker := by
    rintro ⟨i, j⟩
    rw [LieHom.mem_ker]
    simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, Function.comp_apply]
    by_cases hij : i = j
    · rw [if_pos hij, map_sub, LieHom.map_lie, hfE i, hfF i, hfH i, hEF i i, if_pos rfl, sub_self]
    · rw [if_neg hij, LieHom.map_lie, hfE i, hfF j, hEF i j, if_neg hij]
  have keyHE : ∀ p : B × B, CartanMatrix.Relations.HE R CM p ∈ f.ker := by
    rintro ⟨i, j⟩
    rw [LieHom.mem_ker]
    simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair, Function.comp_apply]
    rw [map_sub, LieHom.map_lie, map_zsmul]
    simp only [hfH, hfE, hHE, Int.cast_smul_eq_zsmul, sub_self]
  have keyHF : ∀ p : B × B, CartanMatrix.Relations.HF R CM p ∈ f.ker := by
    rintro ⟨i, j⟩
    rw [LieHom.mem_ker]
    simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair, Function.comp_apply]
    rw [map_add, LieHom.map_lie, map_zsmul]
    simp only [hfH, hfF, hHF, neg_smul, Int.cast_smul_eq_zsmul, neg_add_cancel]
  have keyAdE : ∀ p : B × B, CartanMatrix.Relations.adE R CM p ∈ f.ker := by
    rintro ⟨i, j⟩
    rw [LieHom.mem_ker]
    simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair, Function.comp_apply]
    rw [hpow]
    simp only [LieHom.map_lie, hfE]
    exact hadE i j
  have keyAdF : ∀ p : B × B, CartanMatrix.Relations.adF R CM p ∈ f.ker := by
    rintro ⟨i, j⟩
    rw [LieHom.mem_ker]
    simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair, Function.comp_apply]
    rw [hpow]
    simp only [LieHom.map_lie, hfF]
    exact hadF i j
  have hset : CartanMatrix.Relations.toSet R CM ⊆ (f.ker : Set L) := by
    refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
      (Set.union_subset ?_ ?_) ?_) ?_) ?_) ?_
    · rintro _ ⟨p, rfl⟩; exact keyHH p
    · rintro _ ⟨p, rfl⟩; exact keyEF p
    · rintro _ ⟨p, rfl⟩; exact keyHE p
    · rintro _ ⟨p, rfl⟩; exact keyHF p
    · rintro _ ⟨p, rfl⟩; exact keyAdE p
    · rintro _ ⟨p, rfl⟩; exact keyAdF p
  have hle : CartanMatrix.Relations.toIdeal R CM ≤ f.ker := by
    rw [CartanMatrix.Relations.toIdeal, LieSubmodule.lieSpan_le]
    exact hset
  have hle' : (CartanMatrix.Relations.toIdeal R CM).toSubmodule ≤ (f : L →ₗ[R] K).ker := by
    intro x hx
    exact hle hx
  let φ₀ : (L ⧸ CartanMatrix.Relations.toIdeal R CM) →ₗ[R] K :=
    Submodule.liftQ (CartanMatrix.Relations.toIdeal R CM).toSubmodule (f : L →ₗ[R] K) hle'
  have hφ₀ : ∀ x : L, φ₀ (LieSubmodule.Quotient.mk
      (N := CartanMatrix.Relations.toIdeal R CM) x) = f x := by
    intro x
    exact Submodule.liftQ_apply (CartanMatrix.Relations.toIdeal R CM).toSubmodule
      (f : L →ₗ[R] K) x
  refine ⟨LieHom.mk φ₀ ?_, ?_, ?_, ?_⟩
  · intro x y
    induction x using Quotient.inductionOn' with | _ a =>
    induction y using Quotient.inductionOn' with | _ b =>
    simp only [LieSubmodule.Quotient.is_quotient_mk]
    rw [← LieSubmodule.Quotient.mk_bracket]
    change φ₀ (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal R CM) ⁅a,b⁆) =
      ⁅φ₀ (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal R CM) a),
        φ₀ (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal R CM) b)⁆
    rw [hφ₀, hφ₀, hφ₀, LieHom.map_lie]
  · intro i
    exact (hφ₀ _).trans (hfH i)
  · intro i
    exact (hφ₀ _).trans (hfE i)
  · intro i
    exact (hφ₀ _).trans (hfF i)

end Commons.Algebra.Lie.SerreConstruction
