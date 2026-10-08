/-
Area A11 (p-stability) of the Feit--Thompson drive: reduction of the representation-theoretic
p-stability statement to the quadratic GL-core.

Given a nontrivial `p`-element `a` of a `p`-subgroup `A` of a finite `p`-solvable group `G` with
`O_p(G) = 1`, a faithful `F_p`-representation `ρ` and `(ρ a - 1)^2 = 0`, the subgroup
`𝒬 = ρ(O_{p'}(G)) ≤ GL(V)` together with `X = ρ a` satisfies the quadratic core hypothesis
`Work.PStable.Quad.QuadCore`.
-/
import Mathlib
import Submission.Work.PStable.Quad.Defs
import Submission.Work.HallHigman.Basic
import Submission.Work.HallHigman.piCore_isPiNat
import Submission.Work.HallHigman.GLCore.centralizer_opCore_le
import Submission.Work.HallHigman.GLCore.abelian_case

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.PStable.Quad

open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod p) V]

/-- The element of `GL(V)` induced by `ρ g`. -/
noncomputable def repUnits (ρ : Representation (ZMod p) G V) :
    G →* (Module.End (ZMod p) V)ˣ where
  toFun g := Units.mk (ρ g) (ρ g⁻¹) (by rw [← map_mul, mul_inv_cancel, map_one])
    (by rw [← map_mul, inv_mul_cancel, map_one])
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [map_mul]

lemma repUnits_apply (ρ : Representation (ZMod p) G V) (g : G) :
    ((repUnits ρ g : (Module.End (ZMod p) V)ˣ) : Module.End (ZMod p) V) = ρ g := rfl

lemma repUnits_injective (ρ : Representation (ZMod p) G V)
    (hfaith : Function.Injective ρ) : Function.Injective (repUnits ρ) := by
  intro a b hab
  refine hfaith ?_
  simpa [repUnits_apply] using
    congrArg (fun u : (Module.End (ZMod p) V)ˣ => ((u : Module.End (ZMod p) V))) hab

/-- **Reduction to the quadratic GL-core.**  From a nontrivial `p`-element `a` of a `p`-subgroup
`A` acting quadratically, one obtains a `QuadCore` configuration with `𝒬 = ρ(O_{p'}(G))` and
`X = ρ a`. -/
theorem quadCore_of_representation (hp : p.Prime) [Finite G] [Finite V]
    (hps : Work.HallHigman.IsPSolvable p G)
    (h2 : p ≥ 5 ∨ ∀ Q : Sylow 2 G, IsMulCommutative ↥(Q : Subgroup G))
    (ρ : Representation (ZMod p) G V) (hfaith : Function.Injective ρ)
    (hOp : Work.HallHigman.pCore p G = ⊥)
    (A : Subgroup G) (hAp : IsPGroup p A) {a : G} (ha : a ∈ A) (hane : a ≠ 1)
    (hquad : (ρ a - 1) ^ 2 = 0) :
    ∃ (Q : Subgroup (Module.End (ZMod p) V)ˣ) (X : (Module.End (ZMod p) V)ˣ),
      QuadCore p Q X ∧ ((X : Module.End (ZMod p) V) - 1) ^ 2 = 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hV : Nontrivial V
  · haveI := hV
    haveI hchar : CharP (Module.End (ZMod p) V) p := Work.HallHigman.GLCore.charP_moduleEnd
    let u : G →* (Module.End (ZMod p) V)ˣ := repUnits ρ
    have hu_inj : Function.Injective u := repUnits_injective ρ hfaith
    -- `a` is not in `O_{p'}(G)`
    have hp_dvd_ord : p ∣ orderOf a := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
      have hdvd : orderOf a ∣ p ^ k := hk ▸ Subgroup.orderOf_dvd_natCard A ha
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      have hjne : j ≠ 0 := by
        rintro rfl
        simp only [pow_zero] at hj
        exact hane (orderOf_eq_one_iff.mp hj)
      rw [hj]
      exact dvd_pow_self p hjne
    have ha_not_mem : a ∉ Work.HallHigman.opCore p G := by
      intro hmem
      have hdvd : p ∣ Nat.card ↥(Work.HallHigman.opCore p G) :=
        hp_dvd_ord.trans (Subgroup.orderOf_dvd_natCard _ hmem)
      exact (Work.HallHigman.piCore_isPiNat (π := (· ≠ p)) (G := G)) p hp hdvd rfl
    refine ⟨(Work.HallHigman.opCore p G).map u, u a, ?_, ?_⟩
    · haveI : Finite ↥(Work.HallHigman.opCore p G) :=
        Finite.of_injective _ (Subgroup.subtype_injective _)
      have hequiv := Subgroup.equivMapOfInjective (Work.HallHigman.opCore p G) u hu_inj
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Finite.of_equiv _ hequiv.toEquiv
      · rw [Subgroup.card_map_of_injective hu_inj]
        exact fun hdvd =>
          (Work.HallHigman.piCore_isPiNat (π := (· ≠ p)) (G := G)) p hp hdvd rfl
      · refine Units.ext ?_
        have hp2 : 2 ≤ p := hp.two_le
        have hpow' : ∀ n : ℕ, 2 ≤ n → (ρ a - 1) ^ n = 0 := by
          intro n hn
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
          rw [pow_add, hquad, mul_zero]
        have hpow : (ρ a - 1) ^ p = 0 := hpow' p hp2
        have hfd : (ρ a - 1) ^ p = (ρ a) ^ p - 1 := by
          simpa using
            sub_pow_char_of_commute (R := Module.End (ZMod p) V) p (Commute.one_right (ρ a))
        have hunit : (ρ a) ^ p = 1 := sub_eq_zero.mp (hfd ▸ hpow)
        show ((u a ^ p : (Module.End (ZMod p) V)ˣ) : Module.End (ZMod p) V) = 1
        rw [Units.val_pow_eq_pow_val]
        show ((u a : (Module.End (ZMod p) V)ˣ) : Module.End (ZMod p) V) ^ p = 1
        rw [repUnits_apply]
        exact hunit
      · intro q hq
        obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hq
        rw [show u a * u g * (u a)⁻¹ = u (a * g * a⁻¹) from by rw [map_mul, map_mul, map_inv]]
        exact Subgroup.mem_map_of_mem u (Work.HallHigman.opCore_normal.conj_mem g hg a)
      · by_contra hcon
        have hcon' : ∀ g ∈ Work.HallHigman.opCore p G, u g * u a = u a * u g := by
          intro g hg
          by_contra hne
          exact hcon ⟨u g, Subgroup.mem_map_of_mem u hg, hne⟩
        have hcen : a ∈ Subgroup.centralizer
            ((Work.HallHigman.opCore p G : Subgroup G) : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          have h1 : u g * u a = u a * u g := hcon' g hg
          exact hu_inj (by rw [map_mul, map_mul, h1])
        exact ha_not_mem (Work.HallHigman.GLCore.centralizer_opCore_le hps hOp hcen)
      · rcases h2 with h5 | h2
        · exact Or.inl h5
        · refine Or.inr ?_
          have hG2 : ∀ S : Subgroup G, IsPGroup 2 ↥S → IsMulCommutative ↥S :=
            fun S hS => isMulCommutative_of_isPGroup_two_of_sylow h2 hS
          have hQ0 : ∀ S : Subgroup ↥(Work.HallHigman.opCore p G),
              IsPGroup 2 ↥S → IsMulCommutative ↥S :=
            fun S hS => isMulCommutative_of_isPGroup_two_of_le (R := Work.HallHigman.opCore p G)
              hG2 hS
          exact fun S hS =>
            isMulCommutative_of_isPGroup_two_of_equiv
              (Subgroup.equivMapOfInjective (Work.HallHigman.opCore p G) u hu_inj) hQ0 hS
    · show (((u a : (Module.End (ZMod p) V)ˣ) : Module.End (ZMod p) V) - 1) ^ 2 = 0
      rw [repUnits_apply]
      exact hquad
  · exfalso
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    have h1 : ρ a = 1 := LinearMap.ext fun v => Subsingleton.elim _ _
    exact hane (hfaith (by rw [h1, map_one]))

end Work.PStable.Quad
