import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.Symplectic.extraspecial_centralizer
import Submission.Work.PGroup.Symplectic.centralProduct_of_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# An extraspecial group of exponent `p ^ 2` is not of symplectic type (`p` odd)

An extraspecial `p`-group `E` (`p` odd) whose exponent does not divide `p` has exponent exactly
`p ^ 2`.  Its centre `Z(E) = [E,E]` then has order `p`, the `p`-th power map descends to a
non-zero linear functional on the elementary abelian quotient `E / Z(E)`, and duality for the
commutator pairing produces an element `d ∈ E` with `⁅d, c⁆ = c ^ p` for all `c ∈ E`.

Consequently `d ∈ Ω₁(E)`, `d` centralises `Ω₁(E)`, and `d` is *not* central.  Hence
`A := Z(Ω₁(E))` is a characteristic subgroup of `E` that is abelian and strictly larger than
`Z(E)`, so it has exponent `p` but more than `p` elements: it cannot be cyclic.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup.Symplectic

/-! ### Elementary facts about `centerIn` -/

/-- The centre of the top subgroup is contained in the centre of the ambient group. -/
theorem centerIn_top_le_center {G : Type*} [Group G] :
    Work.PGroup.centerIn (⊤ : Subgroup G) ≤ Subgroup.center G := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hz
  have h1 : (⟨g, trivial⟩ : ↥(⊤ : Subgroup G)) * a = a * ⟨g, trivial⟩ :=
    Subgroup.mem_center_iff.mp ha ⟨g, trivial⟩
  have h2 := congrArg (fun t : ↥(⊤ : Subgroup G) => (t : G)) h1
  simp only [Subgroup.coe_mul] at h2
  rw [← haz]
  exact h2

/-- `centerIn H` is characteristic in the ambient group whenever `H` is. -/
theorem centerIn_characteristic {G : Type*} [Group G] {H : Subgroup G} (hH : H.Characteristic) :
    (Work.PGroup.centerIn H).Characteristic := by
  haveI := hH
  show ((Subgroup.center ↥H).map H.subtype).Characteristic
  infer_instance

/-- The centre of a subgroup is abelian. -/
theorem isMulCommutative_centerIn {G : Type*} [Group G] (H : Subgroup G) :
    IsMulCommutative ↥(Work.PGroup.centerIn H) := by
  rw [isMulCommutative_iff]
  intro x y
  apply Subtype.ext
  obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp x.2
  obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.mp y.2
  show (x : G) * (y : G) = (y : G) * (x : G)
  rw [← haz, ← hbz]
  have h1 : a * b = b * a := (Subgroup.mem_center_iff.mp ha b).symm
  have h2 := congrArg (fun t : ↥H => (t : G)) h1
  simp only [Subgroup.coe_mul] at h2
  exact h2

/-- Membership in `Ω₁` of the top subgroup, for an element of order dividing `p`. -/
theorem mem_omega1_top_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} {x : G} (hx : x ^ p = 1) :
    x ∈ Work.PGroup.omega1 G p (⊤ : Subgroup G) := by
  rw [Work.PGroup.omega1]
  exact Subgroup.subset_closure ⟨trivial, by simpa using hx⟩

/-- In a group of nilpotency class at most two whose commutators have order dividing the odd
prime `p`, the set of elements of `p`-th power `1` is a subgroup, namely `Ω₁`. -/
theorem omega1_top_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hclass : (⁅(⊤ : Subgroup G), ⊤⁆ : Subgroup G) ≤ Subgroup.center G)
    (hcomm : ∀ a b : G, ⁅a, b⁆ ^ p = 1) :
    ∀ c ∈ Work.PGroup.omega1 G p (⊤ : Subgroup G), c ^ p = 1 := by
  have hpowmul : ∀ x y : G, (x * y) ^ p = x ^ p * y ^ p :=
    pow_mul_eq_of_class_two hp hodd hclass hcomm
  set S : Subgroup G :=
    { carrier := {x : G | x ^ p = 1}
      mul_mem' := fun {a b} ha hb => by
        show (a * b) ^ p = 1
        rw [hpowmul a b, ha, hb, one_mul]
      one_mem' := by show (1 : G) ^ p = 1; simp
      inv_mem' := fun {a} ha => by show a⁻¹ ^ p = 1; rw [inv_pow, ha, inv_one] } with hSdef
  have homega : Work.PGroup.omega1 G p (⊤ : Subgroup G) = S := by
    refine le_antisymm ?_ ?_
    · rw [Work.PGroup.omega1, Subgroup.closure_le]
      rintro x ⟨-, hx⟩
      show x ^ p = 1
      simpa using hx
    · intro x hx
      exact mem_omega1_top_of_pow_eq_one hx
  intro c hc
  rw [homega] at hc
  exact hc

/-! ### The main theorem -/

theorem extraspecial_of_exponent_p_sq {E : Type*} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (hE : Work.PGroup.IsExtraspecial p (⊤ : Subgroup E))
    (hexp : ¬ Monoid.exponent E ∣ p) :
    ∃ A : Subgroup E, A.Characteristic ∧ IsMulCommutative A ∧ ¬ IsCyclic ↥A := by
  have hder : Nat.card (⁅(⊤ : Subgroup E), ⊤⁆ : Subgroup E) = p := by
    rw [← Work.PGroup.center_eq_commutator_of_isExtraspecial (⊤ : Subgroup E) hE]
    exact hE.2.2
  have hclass : (⁅(⊤ : Subgroup E), ⊤⁆ : Subgroup E) ≤ Subgroup.center E := by
    rw [← Work.PGroup.center_eq_commutator_of_isExtraspecial (⊤ : Subgroup E) hE]
    exact centerIn_top_le_center
  have hZcard : Nat.card (Subgroup.center E) = p := by
    rw [← Nat.card_congr (Subgroup.centerCongr (Subgroup.topEquiv (G := E))).toEquiv]
    exact Work.PGroup.card_center_subtype (⊤ : Subgroup E) hE
  have hcommcomp : ∀ a b : E, ⁅a, b⁆ ^ p = 1 := by
    intro a b
    have hmem : ⁅a, b⁆ ∈ (⁅(⊤ : Subgroup E), ⊤⁆ : Subgroup E) :=
      Subgroup.commutator_mem_commutator trivial trivial
    have h := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hder] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hpowmul : ∀ x y : E, (x * y) ^ p = x ^ p * y ^ p :=
    pow_mul_eq_of_class_two hp hodd hclass hcommcomp
  have hpowcenter : ∀ x : E, x ^ p ∈ Subgroup.center E := by
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    rw [← commutatorElement_eq_one_iff_mul_comm]
    have hcx : Commute x ⁅y, x⁆ :=
      Subgroup.mem_center_iff.mp (hclass (Subgroup.commutator_mem_commutator trivial trivial)) x
    rw [← hcx.commutatorElement_pow_right p]
    exact hcommcomp y x
  let f : E →* Subgroup.center E :=
    { toFun := fun x => ⟨x ^ p, hpowcenter x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (hpowmul x y) }
  have hf : ∀ z : Subgroup.center E, f z = 1 := by
    intro z
    apply Subtype.ext
    show (z : E) ^ p = 1
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center E) z.2
    rw [hZcard] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  obtain ⟨d, hd⟩ := exists_commutator_eq_of_center_prime hp hZcard hclass hpowcenter f hf
  have hdc : ∀ c : E, ⁅d, c⁆ = c ^ p := by
    intro c
    rw [← hd c]
    simp [f]
  have hdp : d ^ p = 1 := by
    have h := hdc d
    rw [commutatorElement_self] at h
    exact h.symm
  have hHchar : (Work.PGroup.omega1 E p (⊤ : Subgroup E)).Characteristic :=
    Work.PGroup.omega1_characteristic (H := E) p Subgroup.topCharacteristic
  have hHpow : ∀ c ∈ Work.PGroup.omega1 E p (⊤ : Subgroup E), c ^ p = 1 :=
    omega1_top_pow_eq_one hp hodd hclass hcommcomp
  have hMA : Subgroup.center E ≤ Work.PGroup.centerIn (Work.PGroup.omega1 E p (⊤ : Subgroup E)) := by
    intro z hz
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center E) hz
    rw [hZcard] at h
    have hz1 : z ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    refine Subgroup.mem_map.mpr ⟨⟨z, mem_omega1_top_of_pow_eq_one hz1⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro e
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz (e : E))
  have hdH : d ∈ Work.PGroup.omega1 E p (⊤ : Subgroup E) := mem_omega1_top_of_pow_eq_one hdp
  have hdA : d ∈ Work.PGroup.centerIn (Work.PGroup.omega1 E p (⊤ : Subgroup E)) := by
    refine Subgroup.mem_map.mpr ⟨⟨d, hdH⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro e
    apply Subtype.ext
    show (e : E) * d = d * (e : E)
    have he1 : (e : E) ^ p = 1 := hHpow e e.2
    exact (commutatorElement_eq_one_iff_mul_comm.mp (by rw [hdc (e : E)]; exact he1)).symm
  have hdM : d ∉ Subgroup.center E := by
    intro hdcenter
    apply hexp
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro c
    have h1 : d * c = c * d := (Subgroup.mem_center_iff.mp hdcenter c).symm
    have hcomm1 : ⁅d, c⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h1
    rw [hdc c] at hcomm1
    exact hcomm1
  refine ⟨Work.PGroup.centerIn (Work.PGroup.omega1 E p (⊤ : Subgroup E)),
    centerIn_characteristic hHchar, isMulCommutative_centerIn _, ?_⟩
  intro hcyc
  have hpowA : ∀ a : ↥(Work.PGroup.centerIn (Work.PGroup.omega1 E p (⊤ : Subgroup E))),
      a ^ p = 1 := by
    intro a
    apply Subtype.ext
    exact hHpow (a : E) (Work.PGroup.centerIn_le _ a.2)
  have hexpA : Monoid.exponent
      ↥(Work.PGroup.centerIn (Work.PGroup.omega1 E p (⊤ : Subgroup E))) ∣ p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpowA
  have hdvd : Nat.card ↥(Work.PGroup.centerIn (Work.PGroup.omega1 E p (⊤ : Subgroup E))) ∣ p := by
    rw [← IsCyclic.exponent_eq_card (α :=
      ↥(Work.PGroup.centerIn (Work.PGroup.omega1 E p (⊤ : Subgroup E))))]
    exact hexpA
  have hlt : Subgroup.center E < Work.PGroup.centerIn (Work.PGroup.omega1 E p (⊤ : Subgroup E)) :=
    lt_of_le_of_ne hMA (by
      intro heq
      exact hdM (by rw [heq]; exact hdA))
  have hcardlt := Subgroup.card_lt_of_lt hlt
  rw [hZcard] at hcardlt
  have hle : Nat.card ↥(Work.PGroup.centerIn (Work.PGroup.omega1 E p (⊤ : Subgroup E))) ≤ p :=
    Nat.le_of_dvd hp.pos hdvd
  omega

end Work.PGroup.Symplectic
