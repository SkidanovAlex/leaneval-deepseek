import Mathlib
import Submission.Work.Hering.Wagner.zmod2_dual_ker_injective
import Submission.Work.Hering.Wagner.exists_dual_ker_eq
import Submission.Work.Hering.Wagner.natCard_subtype_ne
import Submission.Work.Hering.Wagner.finrank_ker_dualMap_sub_one
import Submission.Work.Hering.Wagner.natCard_fixed_pts

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Wagner

-- ==== main assembly ====

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000 in
theorem card_gen {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [Module.Finite (ZMod 2) V] (hV : 0 < Module.finrank (ZMod 2) V) (f : V ≃ₗ[ZMod 2] V) :
    Nat.card {x : V // x ≠ 0 ∧ f x = x} =
      Nat.card {L : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1 ∧
          L.map (f : V →ₗ[ZMod 2] V) = L} := by
  let F : V →ₗ[ZMod 2] V := f
  change Nat.card {x : V // x ≠ 0 ∧ F x = x} =
      Nat.card {L : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1 ∧ L.map F = L}
  haveI : Finite (Module.Dual (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  let kerMap : {φ : Module.Dual (ZMod 2) V // φ ≠ 0 ∧ F.dualMap φ = φ} →
      {L : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1 ∧ L.map F = L} :=
    fun φ => ⟨LinearMap.ker φ.1, by
      refine ⟨?_, ?_⟩
      · have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := φ.1) φ.2.1
        omega
      · have hcomp : φ.1 ∘ₗ F = φ.1 := by
          rw [← LinearMap.dualMap_apply' F φ.1]; exact φ.2.2
        have hle : (LinearMap.ker φ.1).map F ≤ LinearMap.ker φ.1 := by
          rw [Submodule.map_le_iff_le_comap, ← LinearMap.ker_comp, hcomp]
        exact Submodule.eq_of_le_of_finrank_eq hle (by rw [LinearEquiv.finrank_map_eq])⟩
  have hbij : Function.Bijective kerMap := by
    constructor
    · intro φ ψ h
      have hk : LinearMap.ker φ.1 = LinearMap.ker ψ.1 := by
        have := congrArg Subtype.val h; simpa using this
      exact Subtype.ext (zmod2_dual_ker_injective φ.2.1 ψ.2.1 hk)
    · intro L
      obtain ⟨φ, hφne, hker⟩ := exists_dual_ker_eq hV L.1 L.2.1
      have hsurjF : Function.Surjective F := f.surjective
      have hneq : (φ ∘ₗ F) ≠ 0 := by
        intro h0
        refine hφne (LinearMap.dualMap_injective_of_surjective hsurjF ?_)
        rw [LinearMap.dualMap_apply', LinearMap.dualMap_apply', h0]
        simp
      have hle : LinearMap.ker φ ≤ LinearMap.ker (φ ∘ₗ F) := by
        intro x hx
        rw [LinearMap.ker_comp, Submodule.mem_comap]
        have hmap : F x ∈ L.1 := by
          rw [← L.2.2]
          exact Submodule.mem_map_of_mem (hker ▸ hx)
        rwa [hker]
      have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero (f := φ) hφne
      have h2 := Module.Dual.finrank_ker_add_one_of_ne_zero (f := φ ∘ₗ F) hneq
      have hfin : Module.finrank (ZMod 2) (LinearMap.ker φ) =
          Module.finrank (ZMod 2) (LinearMap.ker (φ ∘ₗ F)) := by omega
      have hkeq : LinearMap.ker φ = LinearMap.ker (φ ∘ₗ F) :=
        Submodule.eq_of_le_of_finrank_eq hle hfin
      have hcomp : φ ∘ₗ F = φ :=
        (zmod2_dual_ker_injective hφne hneq hkeq).symm
      have hfix : F.dualMap φ = φ := by
        rw [LinearMap.dualMap_apply', hcomp]
      refine ⟨⟨φ, hφne, hfix⟩, ?_⟩
      apply Subtype.ext
      simpa using hker
  have hA : Nat.card {x : V // x ≠ 0 ∧ F x = x} = Nat.card (LinearMap.ker (F - 1)) - 1 :=
    natCard_fixed_pts F
  have hB : Nat.card {φ : Module.Dual (ZMod 2) V // φ ≠ 0 ∧ F.dualMap φ = φ} =
      Nat.card {L : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1 ∧ L.map F = L} :=
    Nat.card_congr (Equiv.ofBijective kerMap hbij)
  have hC : Nat.card {φ : Module.Dual (ZMod 2) V // φ ≠ 0 ∧ F.dualMap φ = φ} =
      Nat.card (LinearMap.ker (F.dualMap - 1)) - 1 := natCard_fixed_pts F.dualMap
  have hD : Nat.card (LinearMap.ker (F.dualMap - 1)) = Nat.card (LinearMap.ker (F - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.ker (F.dualMap - 1))),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.ker (F - 1))),
      finrank_ker_dualMap_sub_one F]
  rw [hA, ← hB, hC, hD]

theorem card_fixPts_eq_card_fixHyp {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [Module.Finite (ZMod 2) V] (hV : 0 < Module.finrank (ZMod 2) V) (t : V ≃ₗ[ZMod 2] V) :
    Nat.card {x : V // x ≠ 0 ∧ t x = x} =
      Nat.card {L : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1 ∧
          L.map (t : V →ₗ[ZMod 2] V) = L} :=
  card_gen hV t

end Work.Hering.Wagner
