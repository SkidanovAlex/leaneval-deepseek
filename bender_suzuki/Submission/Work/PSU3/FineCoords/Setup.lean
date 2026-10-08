import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.FMap
import Submission.Work.PSU3.ModelGL
import Submission.Work.PSU3.GaloisField.card_SZ
import Submission.Work.PSU3.FMap.torusAct_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open scoped commutatorElement

open Work.ThmF

namespace Work.PSU3

/-- The fixed field `F` of the `q`-power Frobenius `σE` of `E n = GF(q²)`, `q = 2ⁿ`, as a
subfield of `E n`. -/
def FixSub (n : ℕ) : Subfield (E n) where
  carrier := {y : E n | σE y = y}
  mul_mem' := by intro a b ha hb; rw [Set.mem_setOf_eq] at ha hb ⊢; rw [map_mul, ha, hb]
  one_mem' := by rw [Set.mem_setOf_eq, map_one]
  add_mem' := by intro a b ha hb; rw [Set.mem_setOf_eq] at ha hb ⊢; rw [map_add, ha, hb]
  zero_mem' := by rw [Set.mem_setOf_eq, map_zero]
  neg_mem' := by intro a ha; rw [Set.mem_setOf_eq] at ha ⊢; rw [map_neg, ha]
  inv_mem' := by intro a ha; rw [Set.mem_setOf_eq] at ha ⊢; rw [map_inv₀, ha]

/-- `F = GF(q)` as a type. -/
abbrev Fx (n : ℕ) : Type := ↥(FixSub n)

namespace CoarseFrame

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Elementary properties of `Q₀ = Z(Q)` -/

/-- Elements of `Q₀` are involutions. -/
lemma Q0_sq_eq_one (fr : CoarseFrame H Q t n) (z : fr.Q0) : (z : G) ^ 2 = 1 :=
  (fr.mem_Q0_iff (z : G) (fr.Q0_le z.2)).mp z.2

/-- `Q₀` is central in `Q`. -/
lemma Q0_comm (fr : CoarseFrame H Q t n) (z : fr.Q0) (x : Q) :
    (z : G) * (x : G) = (x : G) * (z : G) := fr.Q0_central z z.2 x x.2

/-- The element of `Q` underlying an element of `Q₀`. -/
def Q0toQ (fr : CoarseFrame H Q t n) (z : fr.Q0) : Q := ⟨(z : G), fr.Q0_le z.2⟩

@[simp] lemma Q0toQ_coe (fr : CoarseFrame H Q t n) (z : fr.Q0) :
    ((fr.Q0toQ z : Q) : G) = (z : G) := rfl

lemma Q0toQ_mul (fr : CoarseFrame H Q t n) (z z' : fr.Q0) :
    fr.Q0toQ (z * z') = fr.Q0toQ z * fr.Q0toQ z' := rfl

lemma Q0toQ_one (fr : CoarseFrame H Q t n) : fr.Q0toQ 1 = 1 := rfl

lemma Q0toQ_sq (fr : CoarseFrame H Q t n) (z : fr.Q0) :
    fr.Q0toQ z * fr.Q0toQ z = 1 := by
  apply Subtype.ext
  simpa [pow_two] using fr.Q0_sq_eq_one z

/-- The square of `z * a` when `z` is central. -/
lemma sq_mul_of_central {M : Type*} [Group M] {z a : M} (h : z * a = a * z) :
    (z * a) ^ 2 = z ^ 2 * a ^ 2 := by
  rw [pow_two, show (z * a) * (z * a) = z * (a * z) * a from by group, ← h]
  rw [pow_two, pow_two]
  group

/-- The commutator `y x y⁻¹ x⁻¹` of two elements of `Q` lies in `Q₀ = Z(Q)`. -/
lemma comm_mem_Q0 (fr : CoarseFrame H Q t n) (y x : Q) :
    (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ ∈ fr.Q0 := by
  have hcomm : fr.bar y * fr.bar x * (fr.bar y)⁻¹ * (fr.bar x)⁻¹ = 1 := by
    rw [show fr.bar y * fr.bar x * (fr.bar y)⁻¹ * (fr.bar x)⁻¹
        = (fr.bar y * fr.bar x) * (fr.bar x * fr.bar y)⁻¹ from by group]
    rw [mul_inv_eq_one]
    exact mul_comm _ _
  have h : fr.bar (y * x * y⁻¹ * x⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hcomm
  simpa using (fr.bar_eq_one_iff (y * x * y⁻¹ * x⁻¹)).mp h

/-- The class-two squaring identity `(x y)² = (y x y⁻¹ x⁻¹) · x² · y²` in `Q`. -/
lemma mul_sq (fr : CoarseFrame H Q t n) (x y : Q) :
    ((x * y : Q) : G) ^ 2
      = (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ * (x : G) ^ 2 * (y : G) ^ 2 := by
  set c : G := (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ with hc
  have hmem : c ∈ fr.Q0 := by rw [hc]; exact fr.comm_mem_Q0 y x
  have hcx : c * (x : G) = (x : G) * c := fr.Q0_central c hmem x x.2
  have hyx : (y : G) * (x : G) = c * ((x : G) * (y : G)) := by rw [hc]; group
  calc ((x * y : Q) : G) ^ 2
      = (x : G) * ((y : G) * (x : G)) * (y : G) := by
        rw [pow_two, show ((x * y : Q) : G) = (x : G) * (y : G) from rfl]
        group
    _ = (x : G) * (c * ((x : G) * (y : G))) * (y : G) := by rw [hyx]
    _ = c * (x : G) ^ 2 * (y : G) ^ 2 := by
        rw [show (x : G) * (c * ((x : G) * (y : G))) * (y : G)
            = (x : G) * c * ((x : G) * (y : G) * (y : G)) from by group]
        rw [← hcx]
        rw [pow_two, pow_two]
        group

/-- The square of a class-two commutator: `(y x y⁻¹ x⁻¹)² = 1`. -/
lemma comm_sq (fr : CoarseFrame H Q t n) (y x : Q) :
    ((y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹) ^ 2 = 1 :=
  fr.Q0_sq_eq_one ⟨_, fr.comm_mem_Q0 y x⟩

/-! ## The additive form of `bar` and the squaring map `Q → Q₀` -/

/-- The additive form of the frame's `bar : Q → E n`. -/
def barA (fr : CoarseFrame H Q t n) (x : Q) : E n := Multiplicative.toAdd (fr.bar x)

lemma barA_mul (fr : CoarseFrame H Q t n) (x y : Q) :
    fr.barA (x * y) = fr.barA x + fr.barA y := by
  rw [barA, map_mul]
  rfl

lemma barA_one (fr : CoarseFrame H Q t n) : fr.barA 1 = 0 := by
  rw [barA, map_one]
  rfl

lemma barA_inv (fr : CoarseFrame H Q t n) (x : Q) : fr.barA x⁻¹ = -fr.barA x := by
  rw [barA, map_inv]
  rfl

lemma barA_eq_zero_iff (fr : CoarseFrame H Q t n) (x : Q) :
    fr.barA x = 0 ↔ (x : G) ∈ fr.Q0 := by
  have h : fr.barA x = 0 ↔ fr.bar x = 1 := Iff.rfl
  rw [h, fr.bar_eq_one_iff]

/-- A section of `bar`: an element of `Q` above a given class in `Q/Q₀ ≅ E n`. -/
noncomputable def sect (fr : CoarseFrame H Q t n) (a : E n) : Q :=
  Function.surjInv fr.bar_surjective (Multiplicative.ofAdd a)

lemma sect_barA (fr : CoarseFrame H Q t n) (a : E n) : fr.barA (fr.sect a) = a := by
  have h := Function.surjInv_eq fr.bar_surjective (Multiplicative.ofAdd a)
  rw [barA, sect, h]
  rfl

/-- The squaring map `Q → Q₀` only depends on the class of the argument in `Q/Q₀`. -/
lemma sq_eq_of_barA_eq (fr : CoarseFrame H Q t n) {x y : Q} (h : fr.barA x = fr.barA y) :
    (x : G) ^ 2 = (y : G) ^ 2 := by
  have hz : fr.barA (x * y⁻¹) = 0 := by
    rw [fr.barA_mul, fr.barA_inv, h, add_neg_cancel]
  have hmem : ((x * y⁻¹ : Q) : G) ∈ fr.Q0 := (fr.barA_eq_zero_iff _).mp hz
  have hsq : (((x * y⁻¹ : Q) : G)) ^ 2 = 1 := fr.Q0_sq_eq_one ⟨_, hmem⟩
  have hx : (x : G) = ((x * y⁻¹ : Q) : G) * (y : G) := by
    rw [show ((x * y⁻¹ : Q) : G) = (x : G) * (y : G)⁻¹ from rfl]
    group
  rw [hx]
  rw [sq_mul_of_central (fr.Q0_central _ hmem y y.2), hsq, one_mul]

/-! ## The commutator calculus of the class-two group `Q`

`Q₀ = Z(Q)`, so `Q` is of nilpotency class two and every commutator lies in `Q₀`.  The
statements are given for `G`-elements lying in `Q`, which makes rewriting painless. -/

/-- Conjugation by an element of `Q₀` fixes `Q`. -/
lemma conj_Q0_G (fr : CoarseFrame H Q t n) {z u : G} (hz : z ∈ fr.Q0) (hu : u ∈ Q) :
    u * z * u⁻¹ = z := by
  rw [← fr.Q0_central z hz u hu, mul_assoc, mul_inv_cancel, mul_one]

/-- `Q₀` is abelian. -/
lemma Q0_mul_comm_G (fr : CoarseFrame H Q t n) {z z' : G} (hz : z ∈ fr.Q0)
    (hz' : z' ∈ fr.Q0) : z * z' = z' * z :=
  fr.Q0_central z hz z' (fr.Q0_le hz')

/-- The commutator `⁅y, x⁆` of two elements of `Q` lies in `Q₀`. -/
lemma commutator_mem_Q0_G (fr : CoarseFrame H Q t n) {y x : G} (hy : y ∈ Q) (hx : x ∈ Q) :
    ⁅y, x⁆ ∈ fr.Q0 :=
  fr.comm_mem_Q0 ⟨y, hy⟩ ⟨x, hx⟩

/-- The commutator against an element of `Q₀` is trivial. -/
lemma commutator_Q0_eq_one_G (fr : CoarseFrame H Q t n) {z u : G} (hz : z ∈ fr.Q0)
    (hu : u ∈ Q) : ⁅z, u⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (fr.Q0_central z hz u hu)

/-- The commutator against an element of `Q₀`, other order. -/
lemma commutator_eq_one_Q0_G (fr : CoarseFrame H Q t n) {u : G} (hu : u ∈ Q) {z : G}
    (hz : z ∈ fr.Q0) : ⁅u, z⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (fr.Q0_central z hz u hu).symm

/-- Class two in the second argument: `⁅y, x x'⁆ = ⁅y,x⁆ ⁅y,x'⁆`. -/
lemma commutator_mul_right_G (fr : CoarseFrame H Q t n) {y x x' : G} (hy : y ∈ Q)
    (hx : x ∈ Q) (hx' : x' ∈ Q) : ⁅y, x * x'⁆ = ⁅y, x⁆ * ⁅y, x'⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  rw [show ⁅y, x⁆ * x * ⁅y, x'⁆ * x⁻¹ = ⁅y, x⁆ * (x * ⁅y, x'⁆ * x⁻¹) from by group]
  rw [fr.conj_Q0_G (fr.commutator_mem_Q0_G hy hx') hx]

/-- Class two in the first argument: `⁅y y', x⁆ = ⁅y,x⁆ ⁅y',x⁆`. -/
lemma commutator_mul_left_G (fr : CoarseFrame H Q t n) {y y' x : G} (hy : y ∈ Q)
    (hy' : y' ∈ Q) (hx : x ∈ Q) : ⁅y * y', x⁆ = ⁅y, x⁆ * ⁅y', x⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  rw [show y * ⁅y', x⁆ * y⁻¹ * ⁅y, x⁆ = (y * ⁅y', x⁆ * y⁻¹) * ⁅y, x⁆ from by group]
  rw [fr.conj_Q0_G (fr.commutator_mem_Q0_G hy' hx) hy]
  exact fr.Q0_mul_comm_G (fr.commutator_mem_Q0_G hy' hx) (fr.commutator_mem_Q0_G hy hx)

/-- If `x'` and `x` have the same class in `Q/Q₀`, then `x' = z x` with `z ∈ Q₀`. -/
lemma exists_Q0_mul_of_barA_eq (fr : CoarseFrame H Q t n) {x x' : Q}
    (h : fr.barA x = fr.barA x') : ∃ z : fr.Q0, (x' : G) = (z : G) * (x : G) := by
  have hz : ((x' * x⁻¹ : Q) : G) ∈ fr.Q0 := by
    rw [← fr.barA_eq_zero_iff, fr.barA_mul, fr.barA_inv, h, add_neg_cancel]
  refine ⟨⟨_, hz⟩, ?_⟩
  rw [show ((x' * x⁻¹ : Q) : G) = (x' : G) * (x : G)⁻¹ from rfl]
  group

/-- The commutator depends only on the classes in `Q/Q₀`. -/
lemma commutator_eq_of_barA_eq (fr : CoarseFrame H Q t n) {y y' x x' : Q}
    (hy : fr.barA y = fr.barA y') (hx : fr.barA x = fr.barA x') :
    ⁅(y' : G), (x' : G)⁆ = ⁅(y : G), (x : G)⁆ := by
  obtain ⟨z, hz⟩ := fr.exists_Q0_mul_of_barA_eq hy
  obtain ⟨z', hz'⟩ := fr.exists_Q0_mul_of_barA_eq hx
  rw [hz, hz', fr.Q0_central z' z'.2 x x.2]
  rw [fr.commutator_mul_left_G (fr.Q0_le z.2) y.2 (Q.mul_mem x.2 (fr.Q0_le z'.2)),
    fr.commutator_Q0_eq_one_G z.2 (Q.mul_mem x.2 (fr.Q0_le z'.2)), one_mul]
  rw [fr.commutator_mul_right_G y.2 x.2 (fr.Q0_le z'.2),
    fr.commutator_eq_one_Q0_G y.2 z'.2]
  rw [mul_one]

/-! ## The fixed field coordinates of `Q₀` -/

/-- `zc 0 = 1` inside `Q₀`. -/
lemma zc_zero (fr : CoarseFrame H Q t n) : fr.zc 0 = 1 := by
  have h := fr.zc_add 0 0 (map_zero σE) (map_zero σE)
  rw [zero_add] at h
  have h2 := congrArg (fun g : G => (fr.zc 0)⁻¹ * g) h
  simpa using h2.symm

/-- `F = GF(q)` sits inside `Q₀` through `zc`. -/
def zc0 (fr : CoarseFrame H Q t n) (y : Fx n) : fr.Q0 := ⟨fr.zc y, fr.zc_mem y y.2⟩

lemma zc0_add (fr : CoarseFrame H Q t n) (y y' : Fx n) :
    fr.zc0 (y + y') = fr.zc0 y * fr.zc0 y' :=
  Subtype.ext (fr.zc_add y y' y.2 y'.2)

lemma zc0_zero (fr : CoarseFrame H Q t n) : fr.zc0 0 = 1 :=
  Subtype.ext fr.zc_zero

lemma zc0_injective (fr : CoarseFrame H Q t n) : Function.Injective fr.zc0 := by
  intro y y' h
  exact Subtype.ext (fr.zc_inj y y' y.2 y'.2 (Subtype.ext_iff.mp h))

lemma zc0_surjective (fr : CoarseFrame H Q t n) : Function.Surjective fr.zc0 := by
  intro z
  obtain ⟨y, hy, hzy⟩ := fr.zc_surj z z.2
  exact ⟨⟨y, hy⟩, Subtype.ext hzy⟩

/-- `F ≃ Q₀`. -/
noncomputable def zcEquiv (fr : CoarseFrame H Q t n) : Fx n ≃ fr.Q0 :=
  Equiv.ofBijective fr.zc0 ⟨fr.zc0_injective, fr.zc0_surjective⟩

lemma zcEquiv_apply (fr : CoarseFrame H Q t n) (y : Fx n) : fr.zcEquiv y = fr.zc0 y := rfl

/-- Injectivity of `zc` on the fixed field, as an equality of `F`-elements. -/
lemma zc_inj_Fx (fr : CoarseFrame H Q t n) {y y' : Fx n} (h : fr.zc y = fr.zc y') :
    y = y' :=
  Subtype.ext (fr.zc_inj y y' y.2 y'.2 h)

/-- The squaring map `Q → Q₀` on the class level, computed with the section. -/
noncomputable def sqm (fr : CoarseFrame H Q t n) (a : E n) : fr.Q0 :=
  ⟨((fr.sect a : Q) : G) ^ 2, fr.sq_mem_Q0 _ (fr.sect a).2⟩

lemma sqm_barA (fr : CoarseFrame H Q t n) (x : Q) :
    fr.sqm (fr.barA x) = ⟨(x : G) ^ 2, fr.sq_mem_Q0 _ x.2⟩ :=
  Subtype.ext (fr.sq_eq_of_barA_eq (fr.sect_barA (fr.barA x)))

/-- `ψ`: the squaring map `Q/Q₀ → Q₀` in `F = GF(q)` coordinates. -/
noncomputable def psi (fr : CoarseFrame H Q t n) (a : E n) : Fx n :=
  fr.zcEquiv.symm (fr.sqm a)

lemma zc0_psi (fr : CoarseFrame H Q t n) (a : E n) : fr.zc0 (fr.psi a) = fr.sqm a := by
  rw [psi, ← zcEquiv_apply, Equiv.apply_symm_apply]

/-- The commutator pairing of `Q/Q₀`, in `F`-coordinates. -/
noncomputable def bet (fr : CoarseFrame H Q t n) (a b : E n) : Fx n :=
  fr.zcEquiv.symm ⟨⁅((fr.sect b : Q) : G), ((fr.sect a : Q) : G)⁆,
    fr.commutator_mem_Q0_G (fr.sect b).2 (fr.sect a).2⟩

lemma zc0_bet (fr : CoarseFrame H Q t n) (a b : E n) :
    fr.zc0 (fr.bet a b) = ⟨⁅((fr.sect b : Q) : G), ((fr.sect a : Q) : G)⁆,
      fr.commutator_mem_Q0_G (fr.sect b).2 (fr.sect a).2⟩ := by
  rw [bet, ← zcEquiv_apply, Equiv.apply_symm_apply]

/-- The quadratic identity `ψ(a+b) = ψ a + ψ b + bet a b`. -/
lemma psi_add (fr : CoarseFrame H Q t n) (a b : E n) :
    fr.psi (a + b) = fr.bet a b + fr.psi a + fr.psi b := by
  apply fr.zc0_injective
  rw [fr.zc0_add, fr.zc0_add, fr.zc0_psi, fr.zc0_psi, fr.zc0_psi, fr.zc0_bet]
  apply Subtype.ext
  change ((fr.sect (a + b) : Q) : G) ^ 2
      = ⁅((fr.sect b : Q) : G), ((fr.sect a : Q) : G)⁆ * ((fr.sect a : Q) : G) ^ 2
        * ((fr.sect b : Q) : G) ^ 2
  rw [show ((fr.sect (a + b) : Q) : G) ^ 2 = (((fr.sect a * fr.sect b) : Q) : G) ^ 2 from
    fr.sq_eq_of_barA_eq (by rw [fr.barA_mul, fr.sect_barA, fr.sect_barA, fr.sect_barA])]
  rw [fr.mul_sq (fr.sect a) (fr.sect b)]
  rfl

/-- `bet` is additive in its second argument. -/
lemma bet_add_right (fr : CoarseFrame H Q t n) (a b b' : E n) :
    fr.bet a (b + b') = fr.bet a b + fr.bet a b' := by
  apply fr.zc0_injective
  rw [fr.zc0_add, fr.zc0_bet, fr.zc0_bet, fr.zc0_bet]
  apply Subtype.ext
  change ⁅((fr.sect (b + b') : Q) : G), ((fr.sect a : Q) : G)⁆
      = ⁅((fr.sect b : Q) : G), ((fr.sect a : Q) : G)⁆
        * ⁅((fr.sect b' : Q) : G), ((fr.sect a : Q) : G)⁆
  rw [← fr.commutator_eq_of_barA_eq (y := fr.sect (b + b')) (y' := fr.sect b * fr.sect b')
      (x := fr.sect a) (x' := fr.sect a)
      (by rw [fr.barA_mul, fr.sect_barA, fr.sect_barA, fr.sect_barA]) rfl]
  rw [show ((fr.sect b * fr.sect b' : Q) : G) = (fr.sect b : G) * (fr.sect b' : G) from rfl]
  exact fr.commutator_mul_left_G (fr.sect b).2 (fr.sect b').2 (fr.sect a).2

/-- `bet` is additive in its first argument. -/
lemma bet_add_left (fr : CoarseFrame H Q t n) (a a' b : E n) :
    fr.bet (a + a') b = fr.bet a b + fr.bet a' b := by
  apply fr.zc0_injective
  rw [fr.zc0_add, fr.zc0_bet, fr.zc0_bet, fr.zc0_bet]
  apply Subtype.ext
  change ⁅((fr.sect b : Q) : G), ((fr.sect (a + a') : Q) : G)⁆
      = ⁅((fr.sect b : Q) : G), ((fr.sect a : Q) : G)⁆
        * ⁅((fr.sect b : Q) : G), ((fr.sect a' : Q) : G)⁆
  rw [← fr.commutator_eq_of_barA_eq (y := fr.sect b) (y' := fr.sect b)
      (x := fr.sect (a + a')) (x' := fr.sect a * fr.sect a') rfl
      (by rw [fr.barA_mul, fr.sect_barA, fr.sect_barA, fr.sect_barA])]
  rw [show ((fr.sect a * fr.sect a' : Q) : G) = (fr.sect a : G) * (fr.sect a' : G) from rfl]
  exact fr.commutator_mul_right_G (fr.sect b).2 (fr.sect a).2 (fr.sect a').2

/-! ## The action of `KW` on `Q` and the equivariance of `ψ` -/

/-- The conjugation action of `KW` on `Q`. -/
def conjQ (fr : CoarseFrame H Q t n) (d : fr.KW) (x : Q) : Q :=
  ⟨(d : G)⁻¹ * (x : G) * (d : G), fr.KW_normal d x x.2⟩

@[simp] lemma conjQ_coe (fr : CoarseFrame H Q t n) (d : fr.KW) (x : Q) :
    ((fr.conjQ d x : Q) : G) = (d : G)⁻¹ * (x : G) * (d : G) := rfl

lemma barA_conjQ (fr : CoarseFrame H Q t n) (d : fr.KW) (x : Q) :
    fr.barA (fr.conjQ d x) = (fr.κ d : E n) * fr.barA x := by
  have h := fr.act_bar d x (fr.conjQ d x) rfl
  simpa [barA] using h

lemma sq_conjQ (fr : CoarseFrame H Q t n) (d : fr.KW) (x : Q) :
    ((fr.conjQ d x : Q) : G) ^ 2 = (d : G)⁻¹ * (x : G) ^ 2 * (d : G) := by
  rw [conjQ_coe, pow_two, pow_two]
  group

/-- `ψ` in terms of the section. -/
lemma zc_psi_val (fr : CoarseFrame H Q t n) (a : E n) :
    fr.zc (fr.psi a : E n) = ((fr.sect a : Q) : G) ^ 2 :=
  congrArg Subtype.val (fr.zc0_psi a)

/-- `ψ 0 = 0`. -/
lemma psi_zero (fr : CoarseFrame H Q t n) : fr.psi 0 = 0 := by
  have hmem : ((fr.sect 0 : Q) : G) ∈ fr.Q0 :=
    (fr.barA_eq_zero_iff _).mp (by rw [fr.sect_barA])
  have h1 : fr.sqm 0 = fr.zcEquiv (0 : Fx n) := by
    rw [zcEquiv_apply, zc0_zero]
    apply Subtype.ext
    exact fr.Q0_sq_eq_one ⟨_, hmem⟩
  calc fr.psi 0 = fr.zcEquiv.symm (fr.sqm 0) := rfl
    _ = fr.zcEquiv.symm (fr.zcEquiv (0 : Fx n)) := by rw [h1]
    _ = 0 := Equiv.symm_apply_apply _ _

/-- `t ^ 2` as an element of the fixed field. -/
noncomputable def sqFx (t : Fx n) : Fx n :=
  ⟨(t : E n) ^ 2, by show σE ((t : E n) ^ 2) = (t : E n) ^ 2; rw [map_pow, t.2]⟩

lemma sqFx_zero : sqFx (0 : Fx n) = 0 := Subtype.ext (by simp [sqFx])

/-- `ψ` is invariant under conjugation by `ζ`. -/
lemma psi_zeta (fr : CoarseFrame H Q t n) (a : E n) :
    fr.psi ((fr.κ fr.ζ : E n) * a) = fr.psi a := by
  apply fr.zc_inj_Fx
  have hbar : fr.barA (fr.conjQ fr.ζ (fr.sect a)) = (fr.κ fr.ζ : E n) * a := by
    rw [fr.barA_conjQ, fr.sect_barA]
  calc fr.zc (fr.psi ((fr.κ fr.ζ : E n) * a) : E n)
      = ((fr.sect ((fr.κ fr.ζ : E n) * a) : Q) : G) ^ 2 := fr.zc_psi_val _
    _ = ((fr.conjQ fr.ζ (fr.sect a) : Q) : G) ^ 2 :=
        fr.sq_eq_of_barA_eq ((fr.sect_barA _).trans hbar.symm)
    _ = (fr.ζ : G)⁻¹ * ((fr.sect a : Q) : G) ^ 2 * (fr.ζ : G) := fr.sq_conjQ _ _
    _ = (fr.ζ : G)⁻¹ * fr.zc (fr.psi a : E n) * (fr.ζ : G) := by rw [fr.zc_psi_val a]
    _ = fr.zc (fr.psi a : E n) := fr.act_zc_ζ (fr.psi a : E n) (fr.psi a).2

/-- `ψ(t c) = t² ψ(c)` for `t` in the fixed field. -/
lemma psi_F_smul (fr : CoarseFrame H Q t n)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (s : Fx n) (c : E n) : fr.psi ((s : E n) * c) = sqFx s * fr.psi c := by
  rcases eq_or_ne (s : E n) 0 with h0 | h0
  · rw [h0, zero_mul, show sqFx s = 0 from Subtype.ext (by simp [sqFx, h0]), zero_mul]
    exact fr.psi_zero
  · obtain ⟨d, hd⟩ := fr.K_surj (Units.mk0 (s : E n) h0) s.2
    have hdval : (fr.κ d : E n) = (s : E n) := by
      rw [hd, Units.val_mk0]
    have hκd : σE ((fr.κ d : (E n)ˣ) : E n) = ((fr.κ d : (E n)ˣ) : E n) := by
      rw [hdval]; exact s.2
    have hdK : (d : G) ∈ Ksub H t := (fr.mem_K_iff d).mpr hκd
    have hnm : (fr.nm (fr.κ d) : E n) = (s : E n) ^ 2 := by
      rw [hsq (fr.κ d) hκd, hdval]
    apply fr.zc_inj_Fx
    have hbar : fr.barA (fr.conjQ d (fr.sect c)) = (s : E n) * c := by
      rw [fr.barA_conjQ, fr.sect_barA, hdval]
    calc fr.zc (fr.psi ((s : E n) * c) : E n)
        = ((fr.sect ((s : E n) * c) : Q) : G) ^ 2 := fr.zc_psi_val _
      _ = ((fr.conjQ d (fr.sect c) : Q) : G) ^ 2 :=
          fr.sq_eq_of_barA_eq ((fr.sect_barA _).trans hbar.symm)
      _ = (d : G)⁻¹ * ((fr.sect c : Q) : G) ^ 2 * (d : G) := fr.sq_conjQ _ _
      _ = (d : G)⁻¹ * fr.zc (fr.psi c : E n) * (d : G) := by rw [fr.zc_psi_val c]
      _ = fr.zc ((fr.nm (fr.κ d) : E n) * (fr.psi c : E n)) :=
          fr.act_zc_K d hdK (fr.psi c : E n) (fr.psi c).2
      _ = fr.zc ((s : E n) ^ 2 * (fr.psi c : E n)) := by rw [hnm]
      _ = fr.zc ↑(sqFx s * fr.psi c) := rfl


/-! ## The framework for the equivariance of the fine coordinates

The fine coordinates of `Q` are the isomorphisms `Q ≃* SZ (E n)` which are compatible with
`x ↦ μ · bar x` on the quotient and with `zc` on the centre.  The group `KW` acts on this set by
`e ↦ torusAct (κ d)⁻¹ ∘ e ∘ (conj by d)`, and the aim is to show that the action has a fixed
point (the group `KW` has odd order).  The definitions below set up that action. -/

/-- The `F`-coordinate of an element of `ker bar`. -/
noncomputable def kerCoord (fr : CoarseFrame H Q t n) (z : Q) (hz : fr.barA z = 0) : Fx n :=
  fr.zcEquiv.symm ⟨z, (fr.barA_eq_zero_iff z).mp hz⟩

lemma zc_kerCoord (fr : CoarseFrame H Q t n) (z : Q) (hz : fr.barA z = 0) :
    fr.zc (fr.kerCoord z hz : E n) = (z : G) :=
  congrArg Subtype.val (Equiv.apply_symm_apply fr.zcEquiv ⟨z, (fr.barA_eq_zero_iff z).mp hz⟩)

/-- The element of `SZ (E n)` attached to an element of `ker bar`. -/
noncomputable def gEl (fr : CoarseFrame H Q t n) (z : Q) (hz : fr.barA z = 0) : SZ (E n) :=
  ⟨0, (fr.kerCoord z hz : E n), by
    have h := (fr.kerCoord z hz).2
    rw [zero_mul, CharTwo.add_eq_zero]
    exact h.symm⟩

@[simp] lemma gEl_x (fr : CoarseFrame H Q t n) (z : Q) (hz : fr.barA z = 0) :
    (fr.gEl z hz).x = 0 := rfl

@[simp] lemma gEl_y (fr : CoarseFrame H Q t n) (z : Q) (hz : fr.barA z = 0) :
    (fr.gEl z hz).y = (fr.kerCoord z hz : E n) := rfl

/-- The "good" isomorphisms `Q ≃* SZ (E n)`: those matching the quotient coordinate
`x ↦ μ · bar x` and the centre coordinates `zc`. -/
structure Good (fr : CoarseFrame H Q t n) (μ : (E n)ˣ) (e : Q ≃* SZ (E n)) : Prop where
  /-- The quotient coordinate is `μ · bar`. -/
  xcoord : ∀ x : Q, (e x).x = (μ : E n) * fr.barA x
  /-- The centre coordinates agree. -/
  kern : ∀ (z : Q) (hz : fr.barA z = 0), e z = fr.gEl z hz

/-- The shift `p ↦ (p.x, p.y + ε p.x)` of `SZ (E n)`, for `ε : E n → F` additive. -/
noncomputable def shiftFun (ε : E n →+ Fx n) (p : SZ (E n)) : SZ (E n) :=
  ⟨p.x, p.y + (ε p.x : E n), by
    have hε : σE (↑(ε p.x) : E n) = ↑(ε p.x) := (ε p.x).2
    have h2 : (↑(ε p.x) : E n) + ↑(ε p.x) = 0 := CharTwo.add_self_eq_zero _
    rw [map_add, hε]
    linear_combination p.herm + h2⟩

@[simp] lemma shiftFun_x (ε : E n →+ Fx n) (p : SZ (E n)) : (shiftFun ε p).x = p.x := rfl

@[simp] lemma shiftFun_y (ε : E n →+ Fx n) (p : SZ (E n)) :
    (shiftFun ε p).y = p.y + (ε p.x : E n) := rfl

lemma shiftFun_mul (ε : E n →+ Fx n) (p q : SZ (E n)) :
    shiftFun ε (p * q) = shiftFun ε p * shiftFun ε q := by
  ext
  · simp [SZ.mul_x]
  · simp only [shiftFun_x, shiftFun_y, SZ.mul_x, SZ.mul_y]
    rw [show ((ε (p.x + q.x) : Fx n) : E n) = (ε p.x : E n) + (ε q.x : E n) from by
      rw [map_add]; rfl]
    ring

lemma shiftFun_one (ε : E n →+ Fx n) : shiftFun ε 1 = 1 := by
  ext <;> simp [shiftFun]

lemma shiftFun_shiftFun (ε : E n →+ Fx n) (p : SZ (E n)) : shiftFun ε (shiftFun ε p) = p := by
  ext
  · rfl
  · simp only [shiftFun_x, shiftFun_y]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The shift of `SZ (E n)` by an additive `ε : E n → F`. -/
noncomputable def shiftEquiv (ε : E n →+ Fx n) : SZ (E n) ≃* SZ (E n) where
  toFun := shiftFun ε
  invFun := shiftFun ε
  left_inv := shiftFun_shiftFun ε
  right_inv := shiftFun_shiftFun ε
  map_mul' := shiftFun_mul ε

@[simp] lemma shiftEquiv_apply (ε : E n →+ Fx n) (p : SZ (E n)) :
    shiftEquiv ε p = shiftFun ε p := rfl

/-- The conjugation action of `KW` on `Q`. -/
noncomputable def conjQEquiv (fr : CoarseFrame H Q t n) (d : fr.KW) : Q ≃* Q where
  toFun := fr.conjQ d
  invFun := fr.conjQ d⁻¹
  left_inv := fun x => Subtype.ext (by simp [conjQ]; group)
  right_inv := fun x => Subtype.ext (by simp [conjQ]; group)
  map_mul' := fun x y => Subtype.ext (by simp [conjQ]; group)

/-- The torus action of `Eˣ` on `SZ (E n)` as a `MulEquiv`. -/
noncomputable def torusEquiv (c : (E n)ˣ) : SZ (E n) ≃* SZ (E n) where
  toFun := SZ.torusAct c
  invFun := SZ.torusAct c⁻¹
  left_inv := fun p => by
    rw [FMap.torusAct_mul, inv_mul_cancel]
    ext <;> simp [SZ.torusAct]
  right_inv := fun p => by
    rw [FMap.torusAct_mul, mul_inv_cancel]
    ext <;> simp [SZ.torusAct]
  map_mul' := fun p q => by
    ext <;> simp only [SZ.torusAct_x, SZ.torusAct_y, SZ.mul_x, SZ.mul_y, map_mul] <;> ring

/-- The action of `d ∈ KW` on an isomorphism `Q ≃* SZ (E n)`:
`e ↦ (torusAct (κ d))⁻¹ ∘ e ∘ (conj by d)`. -/
noncomputable def actIso (fr : CoarseFrame H Q t n) (d : fr.KW) (e : Q ≃* SZ (E n)) :
    Q ≃* SZ (E n) :=
  ((fr.conjQEquiv d).trans e).trans ((torusEquiv (fr.κ d))⁻¹)

@[simp] lemma actIso_apply (fr : CoarseFrame H Q t n) (d : fr.KW) (e : Q ≃* SZ (E n))
    (x : Q) : fr.actIso d e x = SZ.torusAct (fr.κ d)⁻¹ (e (fr.conjQ d x)) := rfl

end CoarseFrame

end Work.PSU3
