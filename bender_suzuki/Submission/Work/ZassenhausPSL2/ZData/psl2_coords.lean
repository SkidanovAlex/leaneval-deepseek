import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions
import Submission.Work.ZassenhausPSL2.ZData.Q_exponent_two_of_bounds
import Submission.Work.ZassenhausPSL2.ZData.field_coordinates_of_regular
import Submission.Work.ZassenhausPSL2.ZData.canon_f_eq_field_inv
import Submission.Work.ZassenhausPSL2.ZData.three_le_card_twoPoint
import Submission.Work.RankOneUniqueness.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausPSL2.ZData

/-- **Field coordinates of the root group of a split rank-one Zassenhaus datum with an
abelian root group, at the critical size `|Q| = |D| + 1`.**

The hypotheses `|Q| = |D| + 1` (with `Q` an abelian `2`-group) force `Q` to be elementary
abelian and `D` to be regular and fixed-point-free on `Q#`, so `(Q, D)` are the additive and
the multiplicative group of a finite field `GF(2ⁿ)`, the action of `D` being multiplication
(`field_coordinates_of_regular`).  The Zassenhaus condition makes the Weyl element `t` invert
`D` (`t_conj_eq_inv`) and hence the canonical map `f` of the rank-one datum satisfies
`e (f x) · e x = c` for a constant `c` (`prod_f_eq_const`, from the `D`-equivariance of `f`);
rescaling the coordinate by a square root of `c⁻¹` (every element of `GF(2ⁿ)` is a square in
characteristic `2`), `f` becomes the inversion of the field and `n ≥ 2` since `|D| ≥ 3`.

This is step `Z6` of the design of the area: the "coordinatization" of a split rank-one
Zassenhaus datum, in the form needed by the recognition theorem
(`Work.RankOneUniqueness.recognize`) and by `ZassenhausPSL2OfQCore`. -/
theorem psl2_coords {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    [IsSimpleGroup G] (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card (Submission.Blueprint.twoPoint H t) + 1) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ e : Q ≃* Multiplicative (GaloisField 2 n),
      ∀ x y : Q, (x : G) ≠ 1 → Work.RankOneUniqueness.FRel H t (x : G) (y : G) →
        e y = Work.ZassenhausPSL2.psl2F n (e x) := by
  classical
  -- ### `Q ≠ ⊥`
  have hDpos : 1 ≤ Nat.card (twoPoint H t) := by
    have hpos : 0 < Nat.card (twoPoint H t) := Nat.card_pos
    omega
  have hQne : Q ≠ ⊥ := by
    intro hb
    rw [hb] at hcard
    have h1 : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
    omega
  -- ### the canonical structure maps of the rank-one datum
  obtain ⟨C⟩ := canon_exists h
  -- ### `|D| = #Inv(Q)`
  have hInvEq : Nat.card (twoPoint H t) = (involutions (Q : Set G)).ncard :=
    card_dStab_eq_card_involutions H Q t h hz hQne h2
  -- ### `|Q| = |D| + 1` bounds `|Q|` by `2·#Inv(Q) + 1`, so `Q` is elementary abelian
  have hbound : 2 * Nat.card (twoPoint H t) + 1 ≥ Nat.card Q := by omega
  have helemQ : ∀ x : Q, x ^ 2 = 1 :=
    Q_exponent_two_of_bounds Q h2 hab (Nat.card (twoPoint H t)) hInvEq hbound
  have helem : ∀ z : Q, (z : G) * (z : G) = 1 := fun z => by
    have hh : z * z = 1 := by rw [← pow_two]; exact helemQ z
    simpa using congrArg (fun w : Q => (w : G)) hh
  -- ### hence `|D| = |Q| - 1`
  have hreg : Nat.card (twoPoint H t) = Nat.card Q - 1 := by
    rw [← ncard_involutions_exp (Q := Q) helem, hInvEq]
  -- ### field coordinates: `Q` is the additive group and `D` the multiplicative group
  have habD : IsAbelianSubgroup (twoPoint H t) := twoPoint_abelian h hz hQne h2
  have hfpf : ∀ d ∈ twoPoint H t, d ≠ 1 → ∀ x ∈ Q, d * x * d⁻¹ = x → x = 1 :=
    dStab_fpf_on_Q H Q t h hz
  obtain ⟨n, hn, e, φ, hadd, hact⟩ :=
    field_coordinates_of_regular Q (twoPoint H t) h2 hab habD
      (le_trans inf_le_left h.normal) hfpf hreg
  -- ### `e (f x) · e x` is a constant `c ≠ 0`
  obtain ⟨c, hcne, hc⟩ := prod_f_eq_const h hz hQne h2 C e φ hadd hact helem hreg
  -- ### rescale the coordinate so that the constant becomes `1`
  obtain ⟨α, hα⟩ := exists_sq_eq_inv hn c hcne
  have hαne : α ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hα
    exact hcne (inv_eq_zero.mp hα.symm)
  have he1 : e 1 = 0 := (e_eq_zero_iff e hadd 1).mpr rfl
  -- ### the rescaled coordinate as a group isomorphism
  let g : Q →* Multiplicative (GaloisField 2 n) :=
    { toFun := fun q => Multiplicative.ofAdd (α * e q)
      map_one' := by
        show Multiplicative.ofAdd (α * e 1) = 1
        rw [he1, mul_zero]
        rfl
      map_mul' := by
        intro x y
        show Multiplicative.ofAdd (α * e (x * y))
          = Multiplicative.ofAdd (α * e x) * Multiplicative.ofAdd (α * e y)
        rw [hadd, mul_add]
        rfl }
  have hbij : Function.Bijective g := by
    refine ⟨fun x y hxy => ?_, fun u => ?_⟩
    · have hxy' : α * e x = α * e y := congrArg Multiplicative.toAdd hxy
      exact e.injective (mul_left_cancel₀ hαne hxy')
    · refine ⟨e.symm (α⁻¹ * Multiplicative.toAdd u), ?_⟩
      show Multiplicative.ofAdd (α * e (e.symm (α⁻¹ * Multiplicative.toAdd u))) = u
      rw [e.apply_symm_apply, mul_inv_cancel_left₀ hαne]
      rfl
  let e' : Q ≃* Multiplicative (GaloisField 2 n) := MulEquiv.ofBijective g hbij
  have he' : ∀ q : Q, e' q = Multiplicative.ofAdd (α * e q) := fun q => rfl
  -- ### `n ≥ 2`, because `|Q| = |D| + 1 ≥ 4`
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n = 1 := by omega
    have hcardQ : Nat.card Q = 2 ^ n := by
      rw [Nat.card_congr e, GaloisField.card 2 n (by omega)]
    have h4 : 4 ≤ Nat.card Q := by
      have h3 := three_le_card_twoPoint (G := G) (H := H) (Q := Q) (t := t) h hz
      omega
    rw [hn1] at hcardQ
    norm_num at hcardQ
    omega
  refine ⟨n, hn2, e', ?_⟩
  -- ### on `Q#` the relation `FRel` is the canonical map `f`, and `e'` inverts it
  intro x y hx hrel
  obtain ⟨m, hm, hcanon⟩ := hrel
  have hfx : C.f x = y := f_eq_of_canon (h := h) (C := C) hx hm hcanon
  have hxne : x ≠ 1 := fun h1 => hx (by rw [h1]; rfl)
  have hmult : (α * e (C.f x)) * (α * e x) = 1 := by
    rw [show (α * e (C.f x)) * (α * e x) = (α * α) * (e (C.f x) * e x) by ring,
      hα, hc x hxne, inv_mul_cancel₀ hcne]
  have hinv : α * e (C.f x) = (α * e x)⁻¹ := by
    have hcomm : (α * e x) * (α * e (C.f x)) = 1 := by rw [mul_comm]; exact hmult
    exact eq_inv_of_mul_eq_one_right hcomm
  calc e' y = Multiplicative.ofAdd (α * e y) := he' y
    _ = Multiplicative.ofAdd (α * e (C.f x)) := by rw [← hfx]
    _ = Multiplicative.ofAdd ((α * e x)⁻¹) := by rw [hinv]
    _ = Work.ZassenhausPSL2.psl2F n (Multiplicative.ofAdd (α * e x)) := rfl
    _ = Work.ZassenhausPSL2.psl2F n (e' x) := by rw [he' x]

end Work.ZassenhausPSL2.ZData
