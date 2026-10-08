import Mathlib
import Submission.Work.SmallRank.Defs
import Submission.Work.SmallRank.isExtraspecial_of_isGroupOfOrderP3ExpP
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The kernel of `Aut(H) → Aut(H/Z(H))` is a `p`-group for `H` of order `p³` and exponent `p`

If `H` is the non-abelian group of order `p ^ 3` and exponent `p` then the centre `Z = Z(H)`
coincides with the derived subgroup `[H, H]` and has order `p`
(`Work.SmallRank.isExtraspecial_of_isGroupOfOrderP3ExpP`).  The induced map

`ρ : MulAut H →* MulAut (H ⧸ Z)`

(is well defined because the centre is characteristic) has as kernel the group of automorphisms
which are the identity on `H / Z`.  If `α` is such an automorphism, write `α x = x · c x` with
`c x ∈ Z`.  Then `α` fixes every commutator, whence (because `Z = [H, H]`) it fixes `Z`
pointwise; consequently `α ^ k x = x · (c x) ^ k` and, as `Z` has exponent `p`,
`α ^ p = 1`.  So every element of `ker ρ` has order dividing `p`, i.e. `ker ρ` is a `p`-group.

The whole argument is unconditional and elementary; the only non-trivial input is the
extraspeciality of `H`.
-/

open scoped Classical commutatorElement

noncomputable section

namespace Work.LocalPrelim

open Subgroup

/-- The canonical homomorphism `MulAut G →* MulAut (G ⧸ Z(G))`: an automorphism of `G` restricts
to the (characteristic) centre and hence descends to the quotient by the centre. -/
def centerQuotientMulAutHom (G : Type*) [Group G] :
    MulAut G →* MulAut (G ⧸ Subgroup.center G) where
  toFun α :=
    QuotientGroup.congr (Subgroup.center G) (Subgroup.center G) α (Subgroup.map_center_eq α)
  map_one' := by
    rw [show (1 : MulAut G) = MulEquiv.refl G from rfl]
    exact QuotientGroup.congr_refl _
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on with
    | _ y => simp

/-- The defining property of `centerQuotientMulAutHom`. -/
lemma centerQuotientMulAutHom_apply {G : Type*} [Group G] (α : MulAut G) (x : G) :
    centerQuotientMulAutHom G α (QuotientGroup.mk x) = QuotientGroup.mk (α x) := rfl

/-- Left multiplication of the first argument of a commutator by a central element does not
change the commutator. -/
lemma commutatorElement_mul_left_of_mem_center {H : Type*} [Group H] {z : H}
    (hz : z ∈ Subgroup.center H) (x y : H) : ⁅x * z, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hzy : ⁅z, y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hz y).symm)
  rw [hzy, mul_one]
  group

/-- Right multiplication of the second argument of a commutator by a central element does not
change the commutator. -/
lemma commutatorElement_mul_right_of_mem_center {H : Type*} [Group H] {w : H}
    (hw : w ∈ Subgroup.center H) (x y : H) : ⁅x, y * w⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hyw : ⁅x, w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hw x)
  rw [hyw]
  group

/-- Multiplication by central elements in both variables does not change a commutator. -/
lemma commutatorElement_mul_mul_of_mem_center {H : Type*} [Group H] {z w : H}
    (hz : z ∈ Subgroup.center H) (hw : w ∈ Subgroup.center H) (x y : H) :
    ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_left_of_mem_center hz x (y * w),
    commutatorElement_mul_right_of_mem_center hw x y]

/-- Every element of the centre has `p`-th power `1` as soon as `|Z(H)| = p`. -/
lemma pow_eq_one_of_mem_center_of_card_center_eq {p : ℕ} {H : Type*}
    [Group H] [Finite H] (hcard : Nat.card (Subgroup.center H) = p) {z : H}
    (hz : z ∈ Subgroup.center H) : z ^ p = 1 := by
  have h1 : orderOf (⟨z, hz⟩ : Subgroup.center H) ∣ p := by
    rw [← hcard]
    exact orderOf_dvd_natCard _
  have h2 : (⟨z, hz⟩ : Subgroup.center H) ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
  have h3 := congrArg (Subtype.val) h2
  simpa using h3

/-- If `α : MulAut H` acts trivially on `H ⧸ Z(H)` and `Z(H) = [H, H]`, then `α ^ p = 1`,
provided `|Z(H)| = p` with `p` prime. -/
lemma pow_prime_eq_one_of_mem_ker_centerQuotientMulAutHom {p : ℕ} {H : Type*}
    [Group H] [Finite H] (hZcomm : Subgroup.center H = commutator H)
    (hcard : Nat.card (Subgroup.center H) = p) (α : MulAut H)
    (hα : α ∈ (centerQuotientMulAutHom H).ker) : α ^ p = 1 := by
  -- Every element of `H` is moved by `α` by a central element.
  have hker : ∀ x : H, (α x)⁻¹ * x ∈ Subgroup.center H := by
    intro x
    have h1 : centerQuotientMulAutHom H α = 1 := MonoidHom.mem_ker.mp hα
    have h2 := congrArg
      (fun f : MulAut (H ⧸ Subgroup.center H) => f (QuotientGroup.mk x)) h1
    have hmk : (QuotientGroup.mk (α x) : H ⧸ Subgroup.center H) = QuotientGroup.mk x := by
      simpa [centerQuotientMulAutHom_apply] using h2
    exact QuotientGroup.eq.mp hmk
  -- `α` fixes every commutator.
  have hfixcomm : ∀ x y : H, α ⁅x, y⁆ = ⁅x, y⁆ := by
    intro x y
    have hx : (α x)⁻¹ * x ∈ Subgroup.center H := hker x
    have hy : (α y)⁻¹ * y ∈ Subgroup.center H := hker y
    obtain ⟨c, hcZ, hcx⟩ : ∃ c, c ∈ Subgroup.center H ∧ α x = x * c :=
      ⟨((α x)⁻¹ * x)⁻¹, Subgroup.inv_mem _ hx, by group⟩
    obtain ⟨d, hdZ, hdy⟩ : ∃ d, d ∈ Subgroup.center H ∧ α y = y * d :=
      ⟨((α y)⁻¹ * y)⁻¹, Subgroup.inv_mem _ hy, by group⟩
    rw [map_commutatorElement, hcx, hdy]
    exact commutatorElement_mul_mul_of_mem_center hcZ hdZ x y
  -- hence `α` fixes the centre `Z(H) = [H, H]` pointwise.
  have hZfix : ∀ z ∈ Subgroup.center H, α z = z := by
    let fixSub : Subgroup H :=
      { carrier := {u : H | α u = u}
        mul_mem' := by
          intro a b ha hb
          show α (a * b) = a * b
          rw [map_mul, ha, hb]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          show α a⁻¹ = a⁻¹
          rw [map_inv, ha] }
    have hle : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ fixSub := by
      rw [commutator_le]
      intro a _ b _
      exact hfixcomm a b
    intro z hz
    rw [hZcomm, commutator_def] at hz
    exact hle hz
  -- `α ^ k x = x * c ^ k`, and every central element has `p`-th power `1`.
  have hZpow : ∀ z ∈ Subgroup.center H, z ^ p = 1 :=
    fun z hz => pow_eq_one_of_mem_center_of_card_center_eq hcard hz
  ext x
  rw [MulAut.one_apply]
  obtain ⟨c, hcZ, hcx⟩ : ∃ c, c ∈ Subgroup.center H ∧ α x = x * c :=
    ⟨((α x)⁻¹ * x)⁻¹, Subgroup.inv_mem _ (hker x), by group⟩
  have key : ∀ k : ℕ, (α ^ k) x = x * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hZfix _ hcZ, hcx, pow_succ]
      group
  rw [key p, hZpow c hcZ, mul_one]

/-- Let `H` be the non-abelian group of order `p ^ 3` and exponent `p`
(`Work.SmallRank.IsGroupOfOrderP3ExpP`).  Then the homomorphism
`MulAut H →* MulAut (H ⧸ Z(H))` sending `α` to the automorphism of the quotient induced by `α`
(the centre is characteristic, so `α` induces an automorphism of `H ⧸ Z(H)`, and the conclusion
below pins down the induced map by its effect on cosets) has `p`-power kernel.

Its kernel is the group of *central* automorphisms `α` with `α x * x⁻¹ ∈ Z(H)` for all `x`,
isomorphic to `Hom(H/Z(H), Z(H)) ≅ 𝔽_p ^ 2`.

Proof sketch: write `Z = Z(H)`.  If `α` acts trivially on `H/Z` then `α x = x · z x` for all `x`
with `z x ∈ Z`; hence `α ⁅x,y⁆ = ⁅α x, α y⁆ = ⁅x,y⁆`, so `α` fixes each commutator and therefore
fixes `Z = ⁅H,H⁆` pointwise (extraspecial:
`Work.SmallRank.isExtraspecial_of_isGroupOfOrderP3ExpP`).  Then by induction
`α ^ k x = x · (z x) ^ k`, and `α ^ p x = x` because `Z` has exponent `p`.  So `ker ρ` has
exponent `p` and, being finite, is a `p`-group. -/
theorem mulAut_center_quotient_ker_isPGroup_of_isGroupOfOrderP3ExpP
    {p : ℕ} (hp : p.Prime) {H : Type*} [Group H] [Finite H]
    (hH : Work.SmallRank.IsGroupOfOrderP3ExpP p H) :
    ∃ ρ : MulAut H →* MulAut (H ⧸ Subgroup.center H),
      (∀ (α : MulAut H) (x : H), ρ α (QuotientGroup.mk x) = QuotientGroup.mk (α x)) ∧
      IsPGroup p ↥ρ.ker := by
  obtain ⟨hExt, hZcard⟩ := Work.SmallRank.isExtraspecial_of_isGroupOfOrderP3ExpP hp hH
  -- The centre of `H` is its derived subgroup.
  have hZcomm : Subgroup.center H = commutator H := by
    rcases hExt.2.1 with hEA | hrest
    · exact absurd hEA.1 hExt.1
    · obtain ⟨_, _, hceq, _, _⟩ := hrest
      rw [← Work.SmallRank.centerIn_top_eq_center, hceq, commutator_def]
  refine ⟨centerQuotientMulAutHom H, fun α x => centerQuotientMulAutHom_apply α x, ?_⟩
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have h := pow_prime_eq_one_of_mem_ker_centerQuotientMulAutHom hZcomm hZcard
    (g : MulAut H) g.2
  simpa using h

end Work.LocalPrelim
