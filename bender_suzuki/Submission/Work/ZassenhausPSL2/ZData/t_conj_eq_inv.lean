import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `t` inverts the two-point stabiliser in a split rank-one group

In a split rank-one datum `(H, Q, t)` (Peterfalvi II Ch. V §2) with `H` a Zassenhaus
subgroup, every element `d` of the two-point stabiliser `D = H ∩ H^t = twoPoint H t` is
inverted by the Weyl element `t`:

`t * d * t = d⁻¹`.

The proof uses only the strong embedding of `H` and the Zassenhaus condition; the
hypotheses `Q ≠ ⊥`, `IsPGroup 2 Q` are not needed (the statement is only *asked* for them).

* `centD_eq_bot_aux`: `V = C_D(t) = centD H t` is trivial.  A nontrivial `d ∈ V` would
  commute with `t`, fix the two points corresponding to `H` and `H^t`, and (by Zassenhaus)
  have no other fixed point; while `t` itself has at least one fixed point outside these two
  (Ch. I §2, `Work.ThreePoints.ncard_fixedPts_zpowers`, combined with `|Ω| = |Q|+1`); then
  `ω, d·ω, d²·ω` would be three distinct points fixed by `t`, contradicting Zassenhaus.
* `eq_inv_of_fpf_order_two`: a fixed-point-free automorphism of order two of a finite group
  inverts every element (Burnside's lemma).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausPSL2.ZData

/-- **Burnside's lemma.**  A fixed-point-free automorphism of order two of a finite group
inverts every element.

Indeed `y ↦ y⁻¹ · φ y` is injective (a relation `y⁻¹φ y = z⁻¹φ z` forces `y z⁻¹ = φ (y z⁻¹)`,
hence `y = z`), so it is a bijection of the finite group `K`; and `φ (y⁻¹ φ y) = (y⁻¹ φ y)⁻¹`. -/
theorem eq_inv_of_fpf_order_two {K : Type*} [Group K] [Finite K] (φ : K →* K)
    (h2 : ∀ x, φ (φ x) = x) (hfpf : ∀ x, φ x = x → x = 1) : ∀ x, φ x = x⁻¹ := by
  have hinj : Function.Injective (fun y : K => y⁻¹ * φ y) := by
    intro y z hyz
    change y⁻¹ * φ y = z⁻¹ * φ z at hyz
    have hfin : φ (y * z⁻¹) = y * z⁻¹ := by
      rw [map_mul, map_inv]
      calc φ y * (φ z)⁻¹ = y * (y⁻¹ * φ y) * (φ z)⁻¹ := by group
        _ = y * (z⁻¹ * φ z) * (φ z)⁻¹ := by rw [hyz]
        _ = y * z⁻¹ := by group
    exact mul_inv_eq_one.mp (hfpf _ hfin)
  intro x
  have hsurj : Function.Surjective (fun y : K => y⁻¹ * φ y) :=
    (Finite.injective_iff_surjective).mp hinj
  obtain ⟨y, hy⟩ := hsurj x
  rw [← hy, map_mul, map_inv, h2 y, mul_inv_rev, inv_inv]

/-- `V = C_D(t) = centD H t` is trivial when `H` is strongly embedded, the action is a
Zassenhaus action (three-point stabilisers are trivial) and `t` is an involution outside `H`.
(The hypotheses `Q ≠ ⊥`, `IsPGroup 2 Q` of the target are not needed.) -/
theorem centD_eq_bot_aux {G : Type} [Group G] [Finite G] (H Q : Subgroup G) (t : G)
    (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) : centD H t = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro d hd
  by_contra hdne
  obtain ⟨hdH, hdt_in, hdt⟩ := Work.ThreePoints.mem_centD.mp hd
  have hdD : d ∈ twoPoint H t := Subgroup.mem_inf.mp hd |>.1
  have hdconj : d ∈ conj t H := Work.ThreePoints.mem_conj_iff.mpr hdt_in
  -- `t` has a fixed point `ω` on `Ω = G ⧸ H` (Peterfalvi I Ch. I §2)
  obtain ⟨ω, hω⟩ := Set.ncard_eq_one.mp
    (Work.ThreePoints.ncard_fixedPts_zpowers h.stronglyEmbedded h.invol)
  have hωfix : t • ω = ω := by
    have hm : ω ∈ fixedPts H (Subgroup.zpowers t) := by rw [hω]; exact rfl
    exact (Work.ThreePoints.mem_fixedPts.mp hm) t (Subgroup.mem_zpowers t)
  set a : G ⧸ H := ((1 : G) : G ⧸ H) with ha
  set b : G ⧸ H := ((t : G) : G ⧸ H) with hb
  have hab : a ≠ b := by
    intro h'
    rw [ha, hb] at h'
    exact h.not_mem (by simpa using QuotientGroup.eq.mp h')
  have htb : t • b = a := by
    rw [hb, ha, Work.ThreePoints.smul_mk, Work.ZassenhausPSL2.t_mul_t h]
  have hd_a : d • a = a := by
    have : d ∈ MulAction.stabilizer G a := by
      rw [ha, Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]; exact hdH
    exact MulAction.mem_stabilizer_iff.mp this
  have hd_b : d • b = b := by
    have : d ∈ MulAction.stabilizer G b := by
      rw [hb, Work.ThreePoints.stabilizer_mk]; exact hdconj
    exact MulAction.mem_stabilizer_iff.mp this
  have hωa : ω ≠ a := by
    intro h'
    have hone : t • a = a := by rw [← h']; exact hωfix
    have hmem : t ∈ MulAction.stabilizer G a := MulAction.mem_stabilizer_iff.mpr hone
    rw [ha, Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one] at hmem
    exact h.not_mem hmem
  have hωb : ω ≠ b := by
    intro h'
    have hone : t • b = b := by rw [← h']; exact hωfix
    rw [htb] at hone
    exact hab hone
  have hdx : d • ω ≠ ω := by
    intro hh
    exact hdne (hz a b ω hab hωa.symm hωb.symm d hd_a hd_b hh)
  have hdd : d • (d • ω) ≠ ω := by
    intro hh
    have hh2 : (d * d) • ω = ω := by rw [mul_smul]; exact hh
    have hd2 : d ^ 2 = 1 := by
      have hmul : d * d = 1 := hz a b ω hab hωa.symm hωb.symm (d * d)
        (by rw [mul_smul, hd_a, hd_a]) (by rw [mul_smul, hd_b, hd_b]) hh2
      simpa [pow_two] using hmul
    have hodd : Odd (Nat.card (twoPoint H t)) :=
      Work.ZassenhausPSL2.dStab_odd H t h.stronglyEmbedded h.not_mem
    have hdvd : orderOf d ∣ Nat.card (twoPoint H t) := by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hdD)
    have hd2dvd : orderOf d ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hd2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2dvd with h1 | h1
    · exact hdne (orderOf_eq_one_iff.mp h1)
    · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h1 ▸ hdvd))
  have h23 : d • ω ≠ d • (d • ω) := by
    intro hh
    have hcancel : ∀ y : G ⧸ H, d⁻¹ • (d • y) = y := fun y => by
      rw [← mul_smul, inv_mul_cancel, one_smul]
    have hthis : ω = d • ω := by
      have := congrArg (fun y : G ⧸ H => d⁻¹ • y) hh
      rwa [hcancel ω, hcancel (d • ω)] at this
    exact hdx hthis.symm
  have hfix2 : t • (d • ω) = d • ω := by
    rw [← mul_smul, hdt.symm, mul_smul, hωfix]
  have hfix3 : t • (d • (d • ω)) = d • (d • ω) := by
    rw [← mul_smul, hdt.symm, mul_smul, hfix2]
  have ht1 : t = 1 := hz ω (d • ω) (d • (d • ω)) hdx.symm hdd.symm h23 t hωfix hfix2 hfix3
  have hinv : orderOf t = 2 := h.invol
  rw [ht1, orderOf_one] at hinv
  omega

theorem t_conj_eq_inv {G : Type} [Group G] [Finite G] (H Q : Subgroup G) (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (hQ : Q ≠ ⊥) (h2 : IsPGroup 2 Q) :
    ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t → t * d * t = d⁻¹ := by
  -- `V = C_D(t) = 1`, so conjugation by `t` is a fixed-point-free automorphism of `D`
  -- of order two, hence inversion (Burnside's lemma).
  have hV : centD H t = ⊥ := centD_eq_bot_aux H Q t h hz
  let φhom : ↥(twoPoint H t) →* ↥(twoPoint H t) :=
    { toFun := fun x => ⟨(MulAut.conj t) (x : G), by
        rw [MulAut.conj_apply, Work.ZassenhausPSL2.t_inv h]
        exact Work.ZassenhausPSL2.dStab_conj_mem h x.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show (MulAut.conj t) (↑(x * y) : G) = (MulAut.conj t) ↑x * (MulAut.conj t) ↑y
        rw [Subgroup.coe_mul, map_mul] }
  have hcoe_apply : ∀ x : ↥(twoPoint H t), (φhom x : G) = t * (x : G) * t⁻¹ := by
    intro x
    show (MulAut.conj t) (x : G) = t * (x : G) * t⁻¹
    rw [MulAut.conj_apply]
  have hφ2 : ∀ x : ↥(twoPoint H t), φhom (φhom x) = x := by
    intro x
    apply Subtype.ext
    show (MulAut.conj t) ((MulAut.conj t) (x : G)) = (x : G)
    rw [MulAut.conj_apply, MulAut.conj_apply, Work.ZassenhausPSL2.t_inv h]
    exact Work.ZassenhausPSL2.t_conj_invol h (x : G)
  have hφfpf : ∀ x : ↥(twoPoint H t), φhom x = x → x = 1 := by
    intro x hx
    have h1 : t * (x : G) * t⁻¹ = (x : G) := by
      rw [← hcoe_apply x]
      exact congrArg Subtype.val hx
    rw [Work.ZassenhausPSL2.t_inv h] at h1
    have hcoe : (x : G) * t = t * (x : G) := by
      have h2' : t * (x : G) = (x : G) * t := by
        calc t * (x : G) = t * (x : G) * (t * t) := by
              rw [Work.ZassenhausPSL2.t_mul_t h, mul_one]
          _ = (t * (x : G) * t) * t := by group
          _ = (x : G) * t := by rw [h1]
      exact h2'.symm
    have hmem : (x : G) ∈ centD H t := by
      rw [Work.ThreePoints.mem_centD]
      exact ⟨(Subgroup.mem_inf.mp x.2).1, (Work.ThreePoints.mem_twoPoint.mp x.2).2, hcoe⟩
    have : (x : G) = 1 := Subgroup.mem_bot.mp (hV ▸ hmem)
    exact Subtype.ext this
  have key := eq_inv_of_fpf_order_two φhom hφ2 hφfpf
  intro d hd
  have hx := key ⟨d, hd⟩
  have h1 : (φhom ⟨d, hd⟩ : G) = (⟨d, hd⟩ : ↥(twoPoint H t))⁻¹ := congrArg Subtype.val hx
  rw [hcoe_apply ⟨d, hd⟩, Subgroup.coe_inv, Work.ZassenhausPSL2.t_inv h] at h1
  exact h1

end Work.ZassenhausPSL2.ZData
