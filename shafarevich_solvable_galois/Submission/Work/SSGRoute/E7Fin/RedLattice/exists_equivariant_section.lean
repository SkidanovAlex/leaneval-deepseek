import Mathlib
import Submission.Work.SSGRoute.E7Fin.RedLattice.sum_smul_inv_smul_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7Fin.RedLattice

/-- **Maschke/Shafarevich averaging step.**  Let `G` be a finite group acting `ZMod p`-linearly
on the `ZMod p`-modules `A` and `B`, and let `j : A →ₗ B` be a surjective `G`-equivariant linear
map.  Since `p ∤ |G|`, the scalar `|G|` is invertible in `ZMod p`, so an arbitrary linear
section of `j` may be averaged over `G` to obtain a `G`-equivariant linear section.

The existence of the *linear* section is automatic because every module over the field `ZMod p`
is projective; the mathematical content is the averaging, which uses that `ZMod p` is a field in
which `|G|` is a unit. -/
theorem exists_equivariant_section (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (hcop : Nat.Coprime (Fintype.card G) p)
    {A B : Type} [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
      [SMulCommClass G (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
      [SMulCommClass G (ZMod p) B]
    (j : A →ₗ[ZMod p] B) (hjeq : ∀ (g : G) (a : A), j (g • a) = g • j a)
    (hj : Function.Surjective j) :
    ∃ s : B →ₗ[ZMod p] A, (∀ b, j (s b) = b) ∧ (∀ (g : G) (b : B), s (g • b) = g • s b) := by
  classical
  -- Step 1: a (not yet equivariant) linear section exists, since `B` is projective over the field.
  obtain ⟨s₀, hs₀⟩ :=
    LinearMap.exists_rightInverse_of_surjective j (LinearMap.range_eq_top.mpr hj)
  have hs₀' : ∀ b, j (s₀ b) = b := fun b => by
    have := DFunLike.congr_fun hs₀ b
    simpa [LinearMap.comp_apply] using this
  -- `|G|` is invertible in `ZMod p` because `p ∤ |G|`.
  have hC : ((Fintype.card G : ZMod p)) ≠ 0 := by
    intro h
    have hdvd : p ∣ Fintype.card G := (ZMod.natCast_eq_zero_iff (Fintype.card G) p).mp h
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop.symm) hdvd
  -- The bundle of `ZMod p`-linear maps given by the action of `G` on `A` and on `B`.
  let actA : G → A →ₗ[ZMod p] A := fun g => DistribSMul.toLinearMap (ZMod p) A g
  let actB : G → B →ₗ[ZMod p] B := fun g => DistribSMul.toLinearMap (ZMod p) B g
  -- The averaged section `s b = |G|⁻¹ • ∑ g, g • s₀ (g⁻¹ • b)`.
  let s : B →ₗ[ZMod p] A :=
    (Fintype.card G : ZMod p)⁻¹ • ∑ g : G, actA g ∘ₗ (s₀ ∘ₗ actB g⁻¹)
  have hs_apply : ∀ b, s b = (Fintype.card G : ZMod p)⁻¹ • ∑ g : G, g • s₀ (g⁻¹ • b) := by
    intro b
    simp only [s, actA, actB, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      DistribSMul.toLinearMap_apply]
  -- Step 2: `s` is a section of `j`.
  have hsec : ∀ b, j (s b) = b := by
    intro b
    rw [hs_apply b, map_smul, map_sum]
    rw [Finset.sum_congr rfl (fun g _ => by rw [hjeq g, hs₀', smul_inv_smul])]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (ZMod p) (Fintype.card G) b,
      smul_smul, inv_mul_cancel₀ hC, one_smul]
  -- Step 3: `s` is `G`-equivariant, by reindexing the averaging sum.
  have heqv : ∀ (g : G) (b : B), s (g • b) = g • s b := by
    intro g b
    have h1 : s (g • b) = (Fintype.card G : ZMod p)⁻¹ • ∑ k : G, (g * k) • s₀ (k⁻¹ • b) := by
      rw [hs_apply (g • b), sum_smul_inv_smul_mul s₀ g b]
    have h2 : g • s b = (Fintype.card G : ZMod p)⁻¹ • ∑ k : G, (g * k) • s₀ (k⁻¹ • b) := by
      rw [hs_apply b, smul_comm g ((Fintype.card G : ZMod p))⁻¹]
      conv_lhs => rw [Finset.smul_sum]
      simp only [smul_smul]
    rw [h1, h2]
  exact ⟨s, hsec, heqv⟩

end Work.SSGRoute.E7Fin.RedLattice
