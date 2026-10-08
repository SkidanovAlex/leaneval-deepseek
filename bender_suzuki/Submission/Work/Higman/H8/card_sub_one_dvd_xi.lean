import Mathlib
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.invol_ncard_dvd_orderOf_xi

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Higman.H8

variable {P : Type} [Group P] [Finite P]

/-! ## Orbit counting, re-proved with a non-colliding import list

The orbit-counting input `invol_ncard_dvd_orbit` and the orbit description `orbit_invol` live in
`Submission.Work.Higman.card_eq_sq_or_cube`, whose import closure contains two clashing
declarations of `Work.Higman.higman_lemma3_final_step`.  We reproduce them here under fresh names
so that this module builds. -/

/-- The orbit of an involution under `⟨ξ⟩` is the whole set of involutions. -/
theorem orbit_invol_xi (h : IsSuzuki2Grp P) {u : P} (hu : orderOf u = 2) :
    (MulAction.orbit (Subgroup.zpowers h.xi) u : Set P) = Invol P := by
  ext z
  rw [MulAction.mem_orbit_iff, mem_Invol]
  constructor
  · rintro ⟨g, rfl⟩
    show orderOf (g • u) = 2
    rw [show g • u = (g : MulAut P) u from rfl, MulEquiv.orderOf_eq, hu]
  · intro hz
    obtain ⟨k, hk⟩ := h.trans u z hu hz
    refine ⟨⟨h.xi ^ k, ?_⟩, hk⟩
    exact Subgroup.pow_mem (Subgroup.zpowers h.xi) (Subgroup.mem_zpowers h.xi) k

/-- Every orbit of `⟨ξ⟩` on `P \ {1}` has cardinality divisible by `|Ω₁(P)| - 1`. -/
theorem invol_ncard_dvd_orbit_xi (h : IsSuzuki2Grp P) {x : P} (hx : x ≠ 1) :
    (Invol P).ncard ∣ Nat.card ↥(MulAction.orbit (Subgroup.zpowers h.xi) x) := by
  classical
  set K : Subgroup (MulAut P) := Subgroup.zpowers h.xi with hK
  obtain ⟨u, -, hu2, -, -⟩ := h.manyInvol
  -- orbit–stabiliser for the involution `u`
  have horb_u : Nat.card ↥(MulAction.orbit K u) = (Invol P).ncard := by
    rw [Nat.card_coe_set_eq, orbit_invol_xi h hu2]
  have hos_u : (Invol P).ncard * Nat.card ↥(MulAction.stabilizer K u) = orderOf h.xi := by
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K u)
    rw [Nat.card_prod, hK, Nat.card_zpowers] at hh
    rwa [horb_u] at hh
  -- `x` has `2`-power order
  obtain ⟨s, hs⟩ := h.isPGroup.exists_orderOf_eq_pow x
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0
      simp only [pow_zero] at hs
      exact absurd (orderOf_eq_one_iff.mp hs) hx
    · exact hpos
  set w : P := x ^ 2 ^ (s - 1) with hw
  have hw1 : w ≠ 1 := by
    intro hcon
    have hdvd : 2 ^ s ∣ 2 ^ (s - 1) := by
      rw [← hs]
      exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [← hw]; exact hcon)
    have hlt : 2 ^ (s - 1) < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact absurd (Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd) (by omega)
  have hw2 : orderOf w = 2 := by
    have hpow : w ^ 2 = 1 := by
      have hexp : 2 ^ (s - 1) * 2 = 2 ^ s := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hw, ← pow_mul, hexp, ← hs, pow_orderOf_eq_one]
    have hd : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hw1
    · exact h2
  -- the stabiliser of `x` is contained in that of `w`
  have hstab_le : MulAction.stabilizer K x ≤ MulAction.stabilizer K w := by
    intro γ hγ
    rw [MulAction.mem_stabilizer_iff] at hγ ⊢
    have h1 : (γ : MulAut P) x = x := hγ
    show (γ : MulAut P) w = w
    rw [hw, map_pow, h1]
  -- stabilisers of involutions have the same cardinality
  have hcard_stab_w : Nat.card ↥(MulAction.stabilizer K w) =
      Nat.card ↥(MulAction.stabilizer K u) := by
    have h1 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K w)
    rw [Nat.card_prod, hK, Nat.card_zpowers] at h1
    have h2 : Nat.card ↥(MulAction.orbit K w) = (Invol P).ncard := by
      rw [Nat.card_coe_set_eq, orbit_invol_xi h hw2]
    rw [h2] at h1
    have hpos : 0 < (Invol P).ncard :=
      (Set.ncard_pos (Set.toFinite (Invol P))).mpr ⟨u, mem_Invol.mpr hu2⟩
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, hos_u])
  -- orbit–stabiliser for `x`
  have hos_x : Nat.card ↥(MulAction.orbit K x) * Nat.card ↥(MulAction.stabilizer K x) =
      orderOf h.xi := by
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K x)
    rw [Nat.card_prod, hK, Nat.card_zpowers] at hh
    exact hh
  -- `|Stab x|` divides `|Stab u|`
  have hdiv : Nat.card ↥(MulAction.stabilizer K x) ∣
      Nat.card ↥(MulAction.stabilizer K u) := by
    rw [← hcard_stab_w]
    exact Subgroup.card_dvd_of_le hstab_le
  obtain ⟨c, hc⟩ := hdiv
  have key : Nat.card ↥(MulAction.orbit K x) * Nat.card ↥(MulAction.stabilizer K x) =
      (Invol P).ncard * Nat.card ↥(MulAction.stabilizer K u) := by rw [hos_x, hos_u]
  refine ⟨c, ?_⟩
  have hpos : 0 < Nat.card ↥(MulAction.stabilizer K x) := Nat.card_pos
  have h2 : Nat.card ↥(MulAction.orbit K x) * Nat.card ↥(MulAction.stabilizer K x) =
      ((Invol P).ncard * c) * Nat.card ↥(MulAction.stabilizer K x) := by
    rw [key, hc]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h2

/-! ## The divisibility for a `ξ`-invariant subgroup -/

/-- **Orbit counting for a `ξ`-invariant subgroup.**  If `S ≤ P` is invariant under the Suzuki
automorphism `ξ` (which permutes the involutions of `P` transitively), then `|Ω₁(P)| - 1`
divides `|S| - 1`: every `ξ`-orbit on `S ∖ {1}` has size a positive multiple of `q - 1`, where
`q = |Ω₁(P)|`. -/
theorem card_sub_one_dvd_of_xi_invariant_xi (h : IsSuzuki2Grp P) {S : Subgroup P}
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
    exact invol_ncard_dvd_orbit_xi h hx1
  rw [← hcard_s]
  exact hdvd

/-- In a Suzuki 2-group `P`, for any `ξ`-invariant subgroup `S` the orbit decomposition of
`S ∖ {1}` under `⟨ξ⟩` gives `|Ω₁(P)| - 1 ∣ |S| - 1` (the `|S| = 1` case being trivial).

NOTE: the proof already exists, sorry-free, as `Work.Higman.card_sub_one_dvd_of_xi_invariant` (in
`Submission/Work/Higman/card_sub_one_dvd_of_xi_invariant.lean`), together with its orbit-counting
input `Work.Higman.invol_ncard_dvd_orbit`, but that file imports
`Submission.Work.Higman.card_eq_sq_or_cube`, which currently does NOT build (its import closure
contains both `Submission.Work.Higman.lemma9_maximal_abelian` and
`Submission.Work.Higman.higman_lemma3_final_step`, which declare the same name
`Work.Higman.higman_lemma3_final_step`).  So the content of those two lemmas has to be copied /
re-proved here with a non-colliding import list; `Submission.Work.Higman.invol_ncard_dvd_orderOf_xi`
already provides `(Invol P).ncard ∣ orderOf ξ` sorry-free. -/
theorem card_sub_one_dvd_xi {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {S : Subgroup P} (hS : S.map (h.xi : MulAut P).toMonoidHom = S) :
    Nat.card ↥(Work.Higman.omega1 P) - 1 ∣ Nat.card ↥S - 1 :=
  card_sub_one_dvd_of_xi_invariant_xi h hS

end Work.Higman.H8
