import Mathlib
import Submission.Work.BSLit.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.Wielandt

open Classical
open scoped BigOperators

/-- **Range of the "averaging over `H`" operator equals the `H`-invariants.**

Let `F` be a finite group, `p` a prime with `p ∤ |F|`, `V` a finite-dimensional `𝔽_p`-module and
`ρ` a representation of `F` on `V`.  For a subgroup `H ≤ F` let

`e := |H|⁻¹ • Σ_{h ∈ H} h  ∈  𝔽_p[F]`

(the `𝔽_p[F]`-element written in the statement as
`algebraMap _ _ (|H|⁻¹) * MonoidAlgebra.mapRingHom _ (Int.castRingHom _) (groupSum H)`).

Then the `𝔽_p`-linear endomorphism `ρ(e)` of `V` has range exactly the subspace of `H`-invariant
vectors `V^H = Representation.invariants (ρ.comp H.subtype)`.

Route.  Write `S := Σ_{h ∈ H} single h 1`, so `e = |H|⁻¹ • S`.
* *Range ⊆ invariants*: for `g ∈ H` the substitution `y ↦ g * y` on `H` shows
  `single g 1 * e = e`; since `ρ.asAlgebraHom` is an algebra homomorphism sending `single g 1`
  to `ρ g`, we get `ρ g (ρ(e) v) = ρ(e) v`.
* *Invariants ⊆ range*: for `v ∈ V^H`, `ρ(e) v = |H|⁻¹ • Σ_{h ∈ H} ρ h v = |H|⁻¹ • (|H| • v) = v`
  because `|H|` is invertible in `𝔽_p` (it divides `|F|`, which is prime to `p`). -/
theorem RangeAveragingEqInvariants {F V : Type*} [Group F] [Fintype F] {p : ℕ} [Fact p.Prime]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p) F V) (hcop : ¬ p ∣ Nat.card F) (H : Subgroup F) :
    LinearMap.range (ρ.asAlgebraHom
        (algebraMap (ZMod p) (MonoidAlgebra (ZMod p) F) ((Nat.card H : ZMod p))⁻¹ *
          MonoidAlgebra.mapRingHom F (Int.castRingHom (ZMod p)) (Work.BSLit.groupSum H)))
      = Representation.invariants (ρ.comp H.subtype) := by
  classical
  set c : ZMod p := (Nat.card H : ZMod p)⁻¹ with hc
  set S : MonoidAlgebra (ZMod p) F :=
    ∑ y : H, MonoidAlgebra.single (y : F) (1 : ZMod p) with hS
  -- rewriting the group-algebra sum into the standard element-sum over `H`
  have hmap : MonoidAlgebra.mapRingHom F (Int.castRingHom (ZMod p)) (Work.BSLit.groupSum H) = S := by
    rw [hS, Work.BSLit.groupSum, map_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [MonoidAlgebra.mapRingHom_single]
    simp
  -- `|H|` is invertible in `𝔽_p`: it divides `|F|`, which is prime to `p`
  have hne : (Nat.card H : ZMod p) ≠ 0 := by
    intro h
    exact hcop (((ZMod.natCast_eq_zero_iff _ _).mp h).trans (Subgroup.card_subgroup_dvd_card H))
  have heq : algebraMap (ZMod p) (MonoidAlgebra (ZMod p) F) ((Nat.card H : ZMod p))⁻¹ *
        MonoidAlgebra.mapRingHom F (Int.castRingHom (ZMod p)) (Work.BSLit.groupSum H) = c • S := by
    rw [hmap, ← Algebra.smul_def]
  rw [heq]
  -- left multiplication by `single g 1` (`g ∈ H`) fixes `S`, by reindexing `H` along `y ↦ g * y`
  have hsingle_mul_S : ∀ g : F, g ∈ H → MonoidAlgebra.single g (1 : ZMod p) * S = S := by
    intro g hg
    rw [hS, Finset.mul_sum]
    have hstep : (∑ y : H, MonoidAlgebra.single g (1 : ZMod p) *
          MonoidAlgebra.single (y : F) (1 : ZMod p))
        = ∑ y : H, MonoidAlgebra.single (y : F) (1 : ZMod p) := by
      rw [← Equiv.sum_comp (Equiv.mulLeft (⟨g, hg⟩ : H))
        (fun y : H => MonoidAlgebra.single (y : F) (1 : ZMod p))]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [MonoidAlgebra.single_mul_single]
      simp
    exact hstep
  have hmul : ∀ g : F, g ∈ H → MonoidAlgebra.single g (1 : ZMod p) * (c • S) = c • S := by
    intro g hg
    rw [mul_smul_comm, hsingle_mul_S g hg]
  -- `ρ.asAlgebraHom S = Σ_{h ∈ H} ρ h`
  have hSmap : ρ.asAlgebraHom S = ∑ y : H, ρ (y : F) := by
    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Representation.asAlgebraHom_single_one]
  refine le_antisymm ?_ ?_
  · -- every value of `ρ(e)` is fixed by `H`
    intro w hw
    rw [LinearMap.mem_range] at hw
    obtain ⟨v, rfl⟩ := hw
    rw [Representation.mem_invariants]
    intro g
    have hg := hmul (g : F) g.2
    show ρ (g : F) (ρ.asAlgebraHom (c • S) v) = ρ.asAlgebraHom (c • S) v
    rw [← Representation.asAlgebraHom_single_one ρ (g : F), ← Module.End.mul_apply, ← map_mul, hg]
  · -- `ρ(e)` restricts to the identity on the invariants
    intro v hv
    rw [LinearMap.mem_range]
    refine ⟨v, ?_⟩
    have hov : ∀ y : H, ρ (y : F) v = v := fun y => by simpa using hv y
    rw [map_smul, LinearMap.smul_apply, hSmap, LinearMap.sum_apply]
    have h1 : (∑ y : H, ρ (y : F) v) = ∑ y : H, v :=
      Finset.sum_congr rfl fun y _ => hov y
    rw [h1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul (ZMod p), smul_smul, inv_mul_cancel₀ hne, one_smul]

end Work.BSLit.Wielandt
