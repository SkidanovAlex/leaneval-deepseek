import Mathlib
import Submission.Work.HallHigman.Basic
import Submission.Work.Fitting.Defs
import Submission.Work.NPC.Basic.isNormalPComplement_complement_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.HallHigman.GLCore

/-- A finite group `X` whose quotient by a central `p'`-subgroup `Z` (nontrivial quotient) is a
`p`-group has a nontrivial characteristic `p`-subgroup.

Indeed `|Z|` is coprime to `Z.index = |X ⧸ Z|` (a `p`-power), so by Schur–Zassenhaus there is a
complement `H` of `Z`: `H ⊔ Z = ⊤`, `H ⊓ Z = ⊥`, `|H| = |X ⧸ Z|` (a `p`-power, so `H` is a
`p`-group).  Since `Z` is central, `H` is normal in `X`; `H.index = |Z|` is prime to `p`, so `H`
is Sylow, and a normal Sylow subgroup is characteristic. -/
lemma exists_characteristic_pGroup_of_quotient_isPGroup {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] {Z : Subgroup X} [Z.Normal]
    (hZc : Z ≤ Subgroup.center X) (hZp : Work.HallHigman.IsPiNat (· ≠ p) (Nat.card ↥Z))
    (hq : IsPGroup p (X ⧸ Z)) (hne : Z ≠ ⊤) :
    ∃ P : Subgroup X, P.Characteristic ∧ IsPGroup p ↥P ∧ P ≠ ⊥ := by
  classical
  have hp : p.Prime := Fact.out
  -- `Z` has order prime to `p`.
  have hcop : (Nat.card Z).Coprime p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    exact (hZp p hp hd) rfl
  -- So `Z` is a normal `p`-complement of `X`.
  have hNPC : Work.NPC.IsNormalPComplement p Z :=
    { normal := inferInstance, coprime_card := hcop, isPGroup_quotient := hq }
  -- Take a Sylow `p`-subgroup `P` of `X`; it is a complement of `Z`.
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := X)
  have hcomp : Z.IsComplement' (P : Subgroup X) :=
    Work.NPC.Basic.isNormalPComplement_complement_sylow hNPC P
  -- Every element of `X` is a product `z * q` with `z ∈ Z`, `q ∈ P`, and `Z` is central:
  -- hence `P` is normal in `X`.
  have hPnorm : (P : Subgroup X).Normal := by
    refine Subgroup.Normal.mk (fun n hn g => ?_)
    have hgmem : g ∈ (Z : Set X) * ((P : Subgroup X) : Set X) := by
      rw [hcomp.mul_eq]
      exact Set.mem_univ g
    obtain ⟨z, hz, q, hq, hzq⟩ := Set.mem_mul.mp hgmem
    have hzc : ∀ y : X, y * z = z * y := Subgroup.mem_center_iff.mp (hZc hz)
    rw [← hzq, mul_inv_rev]
    have key : z * q * n * (q⁻¹ * z⁻¹) = q * n * q⁻¹ := by
      have h1 : z * q * n * (q⁻¹ * z⁻¹) = z * (q * n * q⁻¹) * z⁻¹ := by group
      rw [h1, ← hzc (q * n * q⁻¹), mul_assoc, mul_inv_cancel, mul_one]
    rw [key]
    exact (P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem hq hn) ((P : Subgroup X).inv_mem hq)
  -- A normal Sylow subgroup is characteristic; it is nontrivial because `Z ≠ ⊤`.
  exact ⟨(P : Subgroup X), Sylow.characteristic_of_normal P hPnorm, P.isPGroup', by
    intro hbot
    have h := hcomp
    rw [hbot] at h
    exact hne (Subgroup.isComplement'_bot_right.mp h)⟩

end Work.HallHigman.GLCore
