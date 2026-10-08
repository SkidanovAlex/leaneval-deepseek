import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.center_eq_commutator_of_isExtraspecial
import Submission.Work.PGroup.card_extraspecial

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The centralizer of a non-central element of an extraspecial group

First structural brick of the character theory needed for Part 2 of Appendix VII
(`REFS/peterfalvi_I_app5_9.md`, pp. 218): for an extraspecial `q`-group `Q` of order
`q ^ (2m+1)`, every `x ∉ Z(Q)` has `|C_Q(x)| = q ^ (2m)`.

The proof is the standard one: in a group of class at most two whose centre has order the
prime `q`, the map `h ↦ ⁅h, x⁆` is a homomorphism `Q →* Z(Q)` with kernel exactly `C_Q(x)`;
it is nontrivial because `x ∉ Z(Q)`, so its image is all of `Z(Q)` (a subgroup of a group of
prime order) and `|C_Q(x)| · q = |Q|`.
-/

open scoped commutatorElement

namespace Work.Hering.AppVII

/-- **Class-two groups with centre of prime order.**  Let `Q` be finite with `⁅Q,Q⁆ ≤ Z(Q)` and
`|Z(Q)| = q` prime.  Then every non-central `x : Q` satisfies `|C_Q(x)| · q = |Q|`. -/
theorem card_centralizer_mul_prime {Q : Type*} [Group Q] [Finite Q] {q : ℕ} (hq : q.Prime)
    (hclass : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q)
    (hZcard : Nat.card (Subgroup.center Q) = q) {x : Q} (hx : x ∉ Subgroup.center Q) :
    Nat.card (Subgroup.centralizer ({x} : Set Q)) * q = Nat.card Q := by
  classical
  have hmem : ∀ a : Q, ⁅a, x⁆ ∈ Subgroup.center Q := fun a =>
    Subgroup.commutator_le.mp hclass a trivial x trivial
  -- the commutator map `h ↦ ⁅h, x⁆ : Q →* Z(Q)`
  let φ : Q →* ↥(Subgroup.center Q) :=
    { toFun := fun a => ⟨⁅a, x⁆, hmem a⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        show ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆
        have hb : ⁅b, x⁆ ∈ Subgroup.center Q := hmem b
        have ha : ⁅a, x⁆ ∈ Subgroup.center Q := hmem a
        rw [commutatorElement_mul_left_eq_conj_mul]
        have h1 : a * ⁅b, x⁆ * a⁻¹ = ⁅b, x⁆ := by
          rw [Subgroup.mem_center_iff.mp hb a]; group
        rw [h1, Subgroup.mem_center_iff.mp ha ⁅b, x⁆] }
  have hker : φ.ker = Subgroup.centralizer ({x} : Set Q) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext_iff.mp h)).symm
    · intro h
      exact Subtype.ext
        (commutatorElement_eq_one_iff_mul_comm.mpr (h x (Set.mem_singleton x)).symm)
  have hφne : φ.range ≠ ⊥ := by
    intro hbot
    apply hx
    rw [Subgroup.mem_center_iff]
    intro a
    have ha : φ a ∈ φ.range := ⟨a, rfl⟩
    rw [hbot, Subgroup.mem_bot] at ha
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext_iff.mp ha)
  have hrange : Nat.card φ.range = q := by
    have hdvd : Nat.card φ.range ∣ q := by
      rw [← hZcard]
      exact Subgroup.card_subgroup_dvd_card φ.range
    rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hφne
    · exact h1
  have hcard_ker : Nat.card φ.ker * Nat.card φ.range = Nat.card Q := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
  rw [hker, hrange] at hcard_ker
  exact hcard_ker

/-- **The centralizer of a non-central element of an extraspecial group.**
If `Q` is extraspecial of order `q ^ (2m+1)` (`q` prime) and `x ∉ Z(Q)`, then
`|C_Q(x)| = q ^ (2m)`. -/
theorem card_centralizer_of_isExtraspecial {Q : Type*} [Group Q] [Finite Q] {q m : ℕ}
    (hq : q.Prime) (hQ : Work.PGroup.IsExtraspecial q (⊤ : Subgroup Q))
    (hcard : Nat.card Q = q ^ (2 * m + 1)) {x : Q} (hx : x ∉ Subgroup.center Q) :
    Nat.card (Subgroup.centralizer ({x} : Set Q)) = q ^ (2 * m) := by
  classical
  have hcenterIn : Work.PGroup.centerIn (⊤ : Subgroup Q) = Subgroup.center Q := by
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      refine Subgroup.mem_center_iff.mpr ?_
      intro a
      rw [← hzy]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨a, trivial⟩)
    · intro hy
      refine ⟨⟨y, trivial⟩, ?_, rfl⟩
      refine Subgroup.mem_center_iff.mpr ?_
      intro w
      exact Subtype.ext (Subgroup.mem_center_iff.mp hy (w : Q))
  have hZcard : Nat.card (Subgroup.center Q) = q := by
    rw [← hcenterIn]; exact hQ.2.2
  have hclass : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q := by
    rw [← hcenterIn]
    exact le_of_eq (Work.PGroup.center_eq_commutator_of_isExtraspecial (⊤ : Subgroup Q) hQ).symm
  have hmain := card_centralizer_mul_prime hq hclass hZcard hx
  have hgoal : Nat.card (Subgroup.centralizer ({x} : Set Q)) * q = q ^ (2 * m) * q := by
    rw [hmain, hcard, pow_succ]
  exact Nat.eq_of_mul_eq_mul_right hq.pos hgoal

end Work.Hering.AppVII
