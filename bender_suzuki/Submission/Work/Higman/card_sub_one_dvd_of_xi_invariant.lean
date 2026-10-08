import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.card_eq_sq_or_cube

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- **Orbit counting for a `ξ`-invariant subgroup.**  If `S ≤ P` is invariant under the Suzuki
automorphism `ξ` (which permutes the involutions of `P` transitively), then `|Ω₁(P)| - 1`
divides `|S| - 1`: every `ξ`-orbit on `S ∖ {1}` has size a positive multiple of `q - 1`, where
`q = |Ω₁(P)|`. -/
theorem card_sub_one_dvd_of_xi_invariant (h : IsSuzuki2Grp P) {S : Subgroup P}
    (hS : S.map (h.xi : MulAut P).toMonoidHom = S) :
    Nat.card ↥(omega1 P) - 1 ∣ Nat.card ↥S - 1 := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  set K : Subgroup (MulAut P) := Subgroup.zpowers h.xi with hK
  have hq : Nat.card ↥(omega1 P) - 1 = (Invol P).ncard := by
    rw [h.card_omega1, Nat.add_sub_cancel]
  rw [hq]
  -- membership in `S` is preserved by `ξ` and all its powers
  have hSiff : ∀ x : P, x ∈ S ↔ h.xi x ∈ S := by
    intro x
    have h1 : h.xi x ∈ S.map (h.xi : MulAut P).toMonoidHom ↔ x ∈ S := by
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := (h.xi : MulAut P).injective hyx
        rwa [this] at hy
      · intro hx; exact ⟨x, hx, rfl⟩
    rw [hS] at h1
    exact h1.symm
  -- `K = ⟨ξ⟩` preserves `S`
  have hKmem : ∀ g ∈ K, ∀ x : P, x ∈ S ↔ (g : MulAut P) x ∈ S := by
    let H : Subgroup (MulAut P) :=
      { carrier := {g : MulAut P | ∀ x : P, x ∈ S ↔ (g : MulAut P) x ∈ S}
        one_mem' := by intro x; simp
        mul_mem' := by
          intro g h' hg hh x
          show x ∈ S ↔ (g : MulAut P) ((h' : MulAut P) x) ∈ S
          rw [← hg ((h' : MulAut P) x), ← hh x]
        inv_mem' := by
          intro g hg x
          have h1 := hg ((g : MulAut P).symm x)
          rw [MulEquiv.apply_symm_apply] at h1
          exact h1.symm }
    have hle : K ≤ H := Subgroup.zpowers_le.mpr hSiff
    intro g hg
    exact hle hg
  -- the ambient `⟨ξ⟩`-orbit of a point of `S` stays in `S`
  have horbS : ∀ x ∈ S, ∀ a ∈ MulAction.orbit K x, a ∈ S := by
    intro x hx a ha
    rw [MulAction.mem_orbit_iff] at ha
    obtain ⟨g, hg⟩ := ha
    rw [← hg]
    exact (hKmem g g.2 x).mp hx
  -- `S ∖ {1}` as a finset of `P`
  set s : Finset P := Finset.univ.filter (fun x : P => x ∈ S ∧ x ≠ 1) with hs
  have hmem_s : ∀ x : P, x ∈ s ↔ x ∈ S ∧ x ≠ 1 := by
    intro x; rw [hs]; simp
  have hcard_s : s.card = Nat.card ↥S - 1 := by
    have hbij : s.card = (Finset.univ.filter (fun x : ↥S => x ≠ 1)).card := by
      refine Finset.card_bij (fun x hx => (⟨x, (hmem_s x).mp hx |>.1⟩ : ↥S)) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun hc => (hmem_s x).mp hx |>.2 (Subtype.ext_iff.mp hc)
      · intro x hx y hy hxy
        simpa using congrArg (fun t : ↥S => (t : P)) hxy
      · intro y hy
        refine ⟨(y : P), (hmem_s _).mpr ⟨y.2, fun hc => ?_⟩, ?_⟩
        · exact (Finset.mem_filter.mp hy).2 (Subtype.ext hc)
        · exact Subtype.ext rfl
    rw [hbij]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ↥S)) (p := fun x : ↥S => x ≠ 1)
    have hone : (Finset.univ.filter (fun x : ↥S => ¬ x ≠ 1)).card = 1 := by
      have hset : (Finset.univ.filter (fun x : ↥S => ¬ x ≠ 1)) = {1} := by
        ext x; simp
      rw [hset]; simp
    rw [hone, Finset.card_univ] at hsplit
    have hScard : Nat.card ↥S = Fintype.card ↥S := Nat.card_eq_fintype_card
    omega
  have hdvd : (Invol P).ncard ∣ s.card := by
    rw [Finset.card_eq_sum_card_image (f := fun x : P => MulAction.orbit K x) s]
    apply Finset.dvd_sum
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hxS, hx1⟩ := (hmem_s x).mp hx
    have hfiber : (s.filter (fun a : P => MulAction.orbit K a = MulAction.orbit K x)).card =
        Nat.card ↥(MulAction.orbit K x) := by
      have hset : (s.filter (fun a : P => MulAction.orbit K a = MulAction.orbit K x)) =
          ((MulAction.orbit K x : Set P)).toFinset := by
        ext a
        simp only [Finset.mem_filter, Set.mem_toFinset, MulAction.orbit_eq_iff, hmem_s,
          Finset.mem_univ, true_and]
        constructor
        · rintro ⟨-, ha⟩; exact ha
        · intro ha
          refine ⟨⟨horbS x hxS a ha, ?_⟩, ha⟩
          intro hcon
          rw [hcon] at ha
          rw [MulAction.mem_orbit_iff] at ha
          obtain ⟨γ, hγ⟩ := ha
          exact hx1 (by
            calc x = γ⁻¹ • (γ • x) := by rw [inv_smul_smul]
              _ = γ⁻¹ • (1 : P) := by rw [← hγ]
              _ = 1 := by simp)
      rw [hset, Set.toFinset_card]
      exact (Nat.card_eq_fintype_card).symm
    rw [hfiber]
    exact invol_ncard_dvd_orbit h hx1
  rw [← hcard_s]
  exact hdvd

end Work.Higman
