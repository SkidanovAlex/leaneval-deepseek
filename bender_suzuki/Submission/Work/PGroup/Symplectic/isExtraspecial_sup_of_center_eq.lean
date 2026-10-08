import Mathlib
import Submission.Work.PGroup.frattini_eq_agemo_sup_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The join of two extraspecial groups with a common centre

Let `p` be a prime and let `E`, `E'` be two non-commutative subgroups of finite exponent `p`
of an ambient finite group `X`, each of which satisfies `Φ(E) = Z(E) = ⁅E, E⁆` with
`|Z(E)| = p` — informally, `E` and `E'` are extraspecial of exponent `p`.  Assume moreover
that `E` and `E'` commute elementwise (`⁅E, E'⁆ = ⊥`) and that their centres coincide as
subgroups of `X` (`Z(E) = Z(E')`).  Then the join `E ⊔ E'` is again extraspecial of exponent
`p` with the same centre; in other words, the central product of two extraspecial groups of
exponent `p` amalgamated over their common centre is extraspecial of exponent `p`.

This is one of the elementary structure facts used in the theory of `p`-groups of symplectic
type (P. Hall's theorem, FT 3.5 / Gorenstein, *Finite Groups*, Theorem 5.4.9): the extraspecial
factor produced by the critical-subgroup argument has to be combined with the subgroups arising
from the cyclic pieces of the centre.

The proof rests on three general facts about two elementwise commuting subgroups `A`, `B` of a
group `G` (proved below):

* `⁅A ⊔ B, A ⊔ B⁆ = ⁅A, A⁆ ⊔ ⁅B, B⁆`;
* `Z(A ⊔ B) = Z(A) · Z(B)` (as subgroups of `G`, under the inclusion maps);
* if `A` and `B` both have exponent dividing `p`, then so does `A ⊔ B`.

Together with `Φ(H) = H^p · [H, H]` for a finite `p`-group `H`
(`Work.PGroup.frattini_eq_powClosure_sup_commutator`) these give, for `H = E ⊔ E'`:
`Z(H) = Z(E) = Z(E')` and `Φ(H) = 1 · Z = Z`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup.Symplectic

section Auxiliary

variable {G : Type*} [Group G]

/-- A subgroup of a commutative group is commutative. -/
theorem isMulCommutative_of_le_of_isMulCommutative {H K : Subgroup G} (hle : H ≤ K)
    (hc : IsMulCommutative ↥K) : IsMulCommutative ↥H := by
  rw [isMulCommutative_iff] at hc ⊢
  intro a b
  exact Subtype.ext (by
    simpa using congrArg Subtype.val (hc ⟨a.1, hle a.2⟩ ⟨b.1, hle b.2⟩))

/-- If two subgroups commute elementwise, then every element of their join is a product of an
element of the first and an element of the second. -/
theorem exists_mem_mul_of_mem_sup_of_commute {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hle : A ≤ Subgroup.normalizer (B : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer (B : Set G) (by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (h a ha b hb).symm)
  have hset : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B hle
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp (hset ▸ hx')
  exact ⟨a, ha, b, hb, hab⟩

/-- **The derived subgroup of the join of two elementwise commuting subgroups.**  For subgroups
`A`, `B` of a group `G` with `⁅A, B⁆ = ⊥` one has `⁅A ⊔ B, A ⊔ B⁆ = ⁅A, A⁆ ⊔ ⁅B, B⁆`. -/
theorem commutator_sup_self_eq_sup {A B : Subgroup G} (hAB : ⁅A, B⁆ = ⊥) :
    ⁅A ⊔ B, A ⊔ B⁆ = ⁅A, A⁆ ⊔ ⁅B, B⁆ := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB ha)
      b hb).symm
  refine le_antisymm ?_ (sup_le (Subgroup.commutator_mono le_sup_left le_sup_left)
    (Subgroup.commutator_mono le_sup_right le_sup_right))
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mem_mul_of_mem_sup_of_commute hcomm hx
  obtain ⟨c, hc, d, hd, rfl⟩ := exists_mem_mul_of_mem_sup_of_commute hcomm hy
  have hbc : ⁅b, c⁆ = 1 := Commute.commutator_eq (hcomm c hc b hb).symm
  have had : ⁅a, d⁆ = 1 := Commute.commutator_eq (hcomm a ha d hd)
  have hac : (a * c) * ⁅b, d⁆ * (a * c)⁻¹ = ⁅b, d⁆ := by
    have h1 : a * ⁅b, d⁆ * a⁻¹ = ⁅b, d⁆ := by
      rw [conjugate_commutatorElement, hcomm a ha b hb, hcomm a ha d hd]
      simp [mul_assoc]
    have h2 : c * ⁅b, d⁆ * c⁻¹ = ⁅b, d⁆ := by
      rw [conjugate_commutatorElement, hcomm c hc b hb, hcomm c hc d hd]
      simp [mul_assoc]
    calc (a * c) * ⁅b, d⁆ * (a * c)⁻¹ = a * (c * ⁅b, d⁆ * c⁻¹) * a⁻¹ := by group
      _ = a * ⁅b, d⁆ * a⁻¹ := by rw [h2]
      _ = ⁅b, d⁆ := h1
  have hexp : ⁅a * b, c * d⁆ = (a * c) * ⁅b, d⁆ * (a * c)⁻¹ * ⁅a, c⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_mul_right_eq_mul_conj, hbc, had]
    group
  rw [hexp, hac]
  exact ((⁅A, A⁆ : Subgroup G) ⊔ ⁅B, B⁆).mul_mem
    (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hb hd))
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha hc))

/-- **The centre of the join of two elementwise commuting subgroups** is the join of their
centres: for `⁅H, K⁆ = ⊥` one has
`Z(H ⊔ K) = Z(H) ⊔ Z(K)`, where `Z(H)` denotes the image of the centre of `H` in the ambient
group and `⊔` is the join of subgroups. -/
theorem center_map_sup_subtype_eq_sup {H K : Subgroup G} (h : ⁅H, K⁆ = ⊥) :
    (Subgroup.center ↥(H ⊔ K)).map (H ⊔ K).subtype
      = (Subgroup.center ↥H).map H.subtype ⊔ (Subgroup.center ↥K).map K.subtype := by
  have hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha)
      b hb).symm
  refine le_antisymm ?_ ?_
  · rintro x ⟨w, hw, rfl⟩
    obtain ⟨a, ha, b, hb, hwab⟩ := exists_mem_mul_of_mem_sup_of_commute hcomm w.2
    have hHz : ∀ y ∈ H, y * (w : G) = (w : G) * y := fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, Subgroup.mem_sup_left hy⟩)
    have hKz : ∀ y ∈ K, y * (w : G) = (w : G) * y := fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, Subgroup.mem_sup_right hy⟩)
    have haZ : a ∈ (Subgroup.center ↥H).map H.subtype := by
      refine Subgroup.mem_map.mpr ⟨⟨a, ha⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      show (y : G) * a = a * (y : G)
      have key : ((y : G) * a) * b = (a * (y : G)) * b := by
        calc ((y : G) * a) * b = (y : G) * (a * b) := by rw [mul_assoc]
          _ = (y : G) * (w : G) := by rw [hwab]
          _ = (w : G) * (y : G) := hHz y y.2
          _ = (a * b) * (y : G) := by rw [hwab]
          _ = a * (b * (y : G)) := by rw [mul_assoc]
          _ = a * ((y : G) * b) := by rw [hcomm (y : G) y.2 b hb]
          _ = (a * (y : G)) * b := by rw [mul_assoc]
      exact mul_right_cancel key
    have hbZ : b ∈ (Subgroup.center ↥K).map K.subtype := by
      refine Subgroup.mem_map.mpr ⟨⟨b, hb⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro z
      apply Subtype.ext
      show (z : G) * b = b * (z : G)
      have key : a * ((z : G) * b) = a * (b * (z : G)) := by
        calc a * ((z : G) * b) = (a * (z : G)) * b := by rw [mul_assoc]
          _ = ((z : G) * a) * b := by rw [(hcomm a ha (z : G) z.2).symm]
          _ = (z : G) * (a * b) := by rw [mul_assoc]
          _ = (z : G) * (w : G) := by rw [hwab]
          _ = (w : G) * (z : G) := hKz z z.2
          _ = (a * b) * (z : G) := by rw [hwab]
          _ = a * (b * (z : G)) := by rw [mul_assoc]
      exact mul_left_cancel key
    change (w : G) ∈ (Subgroup.center ↥H).map H.subtype ⊔ (Subgroup.center ↥K).map K.subtype
    rw [show (w : G) = a * b from hwab.symm]
    exact ((Subgroup.center ↥H).map H.subtype ⊔ (Subgroup.center ↥K).map K.subtype).mul_mem
      (Subgroup.mem_sup_left haZ) (Subgroup.mem_sup_right hbZ)
  · refine sup_le ?_ ?_
    · rintro x ⟨u, hu, rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨u, Subgroup.mem_sup_left u.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      show (y : G) * (u : G) = (u : G) * (y : G)
      obtain ⟨c, hc, d, hd, hycd⟩ := exists_mem_mul_of_mem_sup_of_commute hcomm y.2
      have huc : (u : G) * c = c * (u : G) :=
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hu ⟨c, hc⟩)).symm
      rw [show (y : G) = c * d from hycd.symm]
      calc (c * d) * (u : G) = c * (d * (u : G)) := by rw [mul_assoc]
        _ = c * ((u : G) * d) := by rw [hcomm (u : G) u.2 d hd]
        _ = (c * (u : G)) * d := by rw [mul_assoc]
        _ = ((u : G) * c) * d := by rw [huc]
        _ = (u : G) * (c * d) := by rw [mul_assoc]
    · rintro x ⟨u, hu, rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨u, Subgroup.mem_sup_right u.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      show (y : G) * (u : G) = (u : G) * (y : G)
      obtain ⟨c, hc, d, hd, hycd⟩ := exists_mem_mul_of_mem_sup_of_commute hcomm y.2
      have hud : (u : G) * d = d * (u : G) :=
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hu ⟨d, hd⟩)).symm
      rw [show (y : G) = c * d from hycd.symm]
      calc (c * d) * (u : G) = c * (d * (u : G)) := by rw [mul_assoc]
        _ = c * ((u : G) * d) := by rw [hud]
        _ = (c * (u : G)) * d := by rw [mul_assoc]
        _ = ((u : G) * c) * d := by rw [hcomm c hc (u : G) u.2]
        _ = (u : G) * (c * d) := by rw [mul_assoc]

/-- If two subgroups commute elementwise and both have exponent dividing `p`, then so does their
join. -/
theorem pow_eq_one_sup_of_commutator_eq_bot {H K : Subgroup G} {p : ℕ}
    (h : ⁅H, K⁆ = ⊥) (hH : ∀ x : ↥H, x ^ p = 1) (hK : ∀ x : ↥K, x ^ p = 1) :
    ∀ x : ↥(H ⊔ K), x ^ p = 1 := by
  have hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha)
      b hb).symm
  intro x
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mem_mul_of_mem_sup_of_commute hcomm x.2
  have hap : a ^ p = 1 := by simpa using congrArg Subtype.val (hH ⟨a, ha⟩)
  have hbp : b ^ p = 1 := by simpa using congrArg Subtype.val (hK ⟨b, hb⟩)
  apply Subtype.ext
  show (x : G) ^ p = (1 : G)
  rw [show (x : G) = a * b from hab.symm, Commute.mul_pow (hcomm a ha b hb), hap, hbp, mul_one]

end Auxiliary

set_option linter.unusedVariables false in
/-- **The join of two extraspecial groups of exponent `p` with a common centre.**  If `E` and `E'`
are non-commutative subgroups of a finite group `X` of exponent `p` with `Φ(E) = Z(E) = ⁅E, E⁆`,
`Φ(E') = Z(E') = ⁅E', E'⁆`, `|Z(E)| = p`, which commute elementwise and have the same centre as
subgroups of `X`, then `E ⊔ E'` is non-commutative of exponent `p` with
`Z(E ⊔ E') = Φ(E ⊔ E') = Z(E)` of order `p`. -/
theorem isExtraspecial_sup_of_center_eq {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {E E' : Subgroup X}
    (hEnab : ¬ IsMulCommutative ↥E) (hE'nab : ¬ IsMulCommutative ↥E')
    (hEexp : ∀ x : ↥E, x ^ p = 1) (hE'exp : ∀ x : ↥E', x ^ p = 1)
    (hEfr : (frattini ↥E).map E.subtype = (Subgroup.center ↥E).map E.subtype)
    (hE'fr : (frattini ↥E').map E'.subtype = (Subgroup.center ↥E').map E'.subtype)
    (hEder : (Subgroup.center ↥E).map E.subtype = ⁅E, E⁆)
    (hE'der : (Subgroup.center ↥E').map E'.subtype = ⁅E', E'⁆)
    (hZcard : Nat.card (Subgroup.center ↥E) = p)
    (hcomm : ⁅E, E'⁆ = ⊥)
    (hZeq : (Subgroup.center ↥E).map E.subtype = (Subgroup.center ↥E').map E'.subtype) :
    ¬ IsMulCommutative ↥(E ⊔ E') ∧ (∀ x : ↥(E ⊔ E'), x ^ p = 1) ∧
    (Subgroup.center ↥(E ⊔ E')).map (E ⊔ E').subtype = (Subgroup.center ↥E).map E.subtype ∧
    (frattini ↥(E ⊔ E')).map (E ⊔ E').subtype = (Subgroup.center ↥E).map E.subtype ∧
    Nat.card (Subgroup.center ↥(E ⊔ E')) = p := by
  classical
  set H : Subgroup X := E ⊔ E' with hHdef
  set Z : Subgroup X := (Subgroup.center ↥E).map E.subtype with hZdef
  have hZ'E : (Subgroup.center ↥E').map E'.subtype = Z := hZeq.symm
  have hEderZ : ⁅E, E⁆ = Z := hEder.symm
  have hE'derZ : ⁅E', E'⁆ = Z := hE'der.symm.trans hZ'E
  -- `E ⊔ E'` is non-commutative, since `E` is.
  have hnab : ¬ IsMulCommutative ↥H := fun hc =>
    hEnab (isMulCommutative_of_le_of_isMulCommutative le_sup_left hc)
  -- `E ⊔ E'` has exponent dividing `p`.
  have hexp : ∀ x : ↥H, x ^ p = 1 := pow_eq_one_sup_of_commutator_eq_bot hcomm hEexp hE'exp
  -- the centre of `E ⊔ E'` is `Z`
  have hcenter : (Subgroup.center ↥H).map H.subtype = Z := by
    have key := center_map_sup_subtype_eq_sup hcomm
    rw [hZ'E, sup_idem] at key
    exact key
  -- the derived subgroup of `E ⊔ E'` is `Z`
  have hcommH : ⁅H, H⁆ = Z := by
    have key := commutator_sup_self_eq_sup hcomm
    rw [hEderZ, hE'derZ, sup_idem] at key
    exact key
  -- the Frattini subgroup of `E ⊔ E'` is `Z`, because `Φ(H) = H^p · [H, H]` and `H^p = 1`
  have hfr : (frattini ↥H).map H.subtype = Z := by
    haveI : Finite ↥H := Finite.of_injective H.subtype H.subtype_injective
    have hP : IsPGroup p ↥H :=
      isPGroup_iff_pow_pow_eq_one.mpr fun x => ⟨1, by simpa using hexp x⟩
    have h1 : Subgroup.map H.subtype (Subgroup.closure (Set.range fun x : ↥H => x ^ p)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, Subgroup.closure_le]
      rintro y ⟨x, rfl⟩
      exact MonoidHom.mem_ker.mpr (by simpa using congrArg Subtype.val (hexp x))
    have h2 : Subgroup.map H.subtype ⁅(⊤ : Subgroup ↥H), ⊤⁆ = Z := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      exact hcommH
    rw [frattini_eq_powClosure_sup_commutator hp hP, Subgroup.map_sup, h1, h2, bot_sup_eq]
  -- the order of `Z`
  have hcardZ : Nat.card Z = p := by
    rw [← hZcard]
    exact Subgroup.card_map_of_injective E.subtype_injective
  refine ⟨hnab, hexp, hcenter, hfr, ?_⟩
  rw [← Subgroup.card_map_of_injective H.subtype_injective, hcenter, hcardZ]

end Work.PGroup.Symplectic
