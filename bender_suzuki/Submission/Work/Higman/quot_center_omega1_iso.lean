import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.center_eq_omega1
import Submission.Work.Higman.pow_two_pow_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

open scoped commutatorElement

/-!
# `P / Z(P) ≅ Ω₁(P)` as `ξ`-modules, when `Z(P) ≠ Ω₁(P)`

Higman, *Suzuki 2-groups* (1963).  Let `P` be a Suzuki 2-group with `⁅P, P⁆ ≤ Ω₁(P)` (so that
`P` has nilpotency class two, every square is central and every commutator is an involution) and
suppose `Z(P) ≠ Ω₁(P)`.  Since `Ω₁(P) ≤ Z(P)` always, the centre is *strictly* larger than `Ω₁`.

Write `2 ^ E` for the exponent of the centre `Z = Z(P)` (a homocyclic group, Higman's Lemma 1,
available as `mem_powSub_two_iff`).  The hypothesis `Z ≠ Ω₁` forces `E ≥ 2`: for `E ≤ 1` every
central element would be an involution, i.e. `Z ≤ Ω₁`.

For `E ≥ 2` the `2 ^ E`-th power map

  `f : P → Ω₁(P),  x ↦ x ^ (2 ^ E)`

is a group homomorphism (`pow_two_pow_mul`), it is `ξ`-equivariant (`ξ (x ^ n) = (ξ x) ^ n`), its
kernel is exactly `Z(P)`, and it is surjective: its values are involutions of `Ω₁(P)` by
construction, `f` is not identically `1` as `P` is not abelian, and `ξ` acts transitively on the
involutions.  Hence `f` induces the required `ξ`-equivariant isomorphism `P / Z(P) ≅ Ω₁(P)`.

* `kernel ⊇ Z`: `z ^ (2 ^ E) = 1` for every central `z`, by the definition of `E`.
* `kernel ⊆ Z`: if `x ^ (2 ^ E) = 1` then `(x ^ 2) ^ (2 ^ (E - 1)) = 1` with `x ^ 2` central, so
  `x ^ 2 ∈ powSub Z 2 = Z²`, and Higman's Lemma 2 (`mem_center_of_sq_mem_centerSq`) gives
  `x ∈ Z`.
-/

/-- If the centre of a Suzuki 2-group with `⁅P, P⁆ ≤ Ω₁(P)` is strictly larger than `Ω₁(P)`,
then `P / Z(P)` and `Ω₁(P)` are isomorphic as `ξ`-modules. -/
theorem quot_center_omega1_iso {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P)
    (hne : Subgroup.center P ≠ Work.Higman.omega1 P) :
    ∃ e : (P ⧸ Subgroup.center P) ≃* ↥(Work.Higman.omega1 P),
      ∀ x : P, ((e (QuotientGroup.mk (h.xi x)) : ↥(Work.Higman.omega1 P)) : P)
        = h.xi ((e (QuotientGroup.mk x) : ↥(Work.Higman.omega1 P)) : P) := by
  classical
  -- the centre is a `ξ`-invariant abelian normal subgroup
  have hZxi : IsXiAbelNormal h (Subgroup.center P) :=
    ⟨(Subgroup.center P).normal_of_le_center le_rfl, center_map_xi h,
      fun x hx y hy => (Subgroup.mem_center_iff.mp hx y).symm⟩
  -- exponent data of the centre: `2 ^ E` is the exponent of `Z(P)`
  obtain ⟨E, he1, _he2, hkey⟩ := mem_powSub_two_iff h hZxi
  -- `Z ≠ Ω₁` forces `E ≥ 2`
  have hE : 2 ≤ E := by
    rcases Nat.lt_or_ge E 2 with hlt | hge
    · exfalso
      interval_cases E
      · -- `E = 0`: every central element is `1`, so `Z(P) = ⊥ = Ω₁(P)`
        refine hne (le_antisymm (fun z hz => ?_) h.omega1_le_center)
        have h1 : z = 1 := by simpa using he1 z hz
        rw [h1]
        exact Subgroup.one_mem _
      · -- `E = 1`: every central element is an involution, so `Z(P) ≤ Ω₁(P)`
        refine hne (le_antisymm (fun z hz => ?_) h.omega1_le_center)
        exact h.mem_omega1.mpr (by simpa using he1 z hz)
    · exact hge
  -- `powSub Z 2` is `centerSq P = Z(P)²`
  have hbridge : powSub (Subgroup.center P) 2 = centerSq P := by
    ext y
    rw [mem_powSub_iff (fun a ha b hb => (Subgroup.mem_center_iff.mp ha b).symm), mem_centerSq]
    constructor
    · rintro ⟨z, hz, hz'⟩
      exact ⟨z, hz, by rw [← pow_two, hz']⟩
    · rintro ⟨z, hz, hz'⟩
      exact ⟨z, hz, by rwa [← pow_two] at hz'⟩
  -- the exponents `2 ^ E` and `2 * 2 ^ (E - 1)` agree
  have h2E : 2 ^ E = 2 * 2 ^ (E - 1) := by
    nth_rewrite 1 [show E = (E - 1) + 1 by omega]
    rw [pow_succ']
  -- `x ^ (2 ^ E) = (x ^ 2) ^ (2 ^ (E - 1))`
  have hfold : ∀ t : P, t ^ 2 ^ E = (t ^ 2) ^ 2 ^ (E - 1) := by
    intro t
    rw [← pow_mul, h2E]
  -- every `2 ^ E`-th power lies in `Ω₁(P)`
  have hfmem : ∀ x : P, x ^ 2 ^ E ∈ omega1 P := by
    intro x
    have hx2 : x ^ 2 ∈ Subgroup.center P := sq_mem_center_of_comm h hcomm x
    have h2 : ((x ^ 2) ^ 2 ^ (E - 1)) ^ 2 = 1 := by
      rw [← pow_mul]
      rw [show 2 ^ (E - 1) * 2 = 2 ^ E by rw [← pow_succ]; congr 1; omega]
      exact he1 (x ^ 2) hx2
    rw [h.mem_omega1, hfold x]
    exact h2
  -- the `2 ^ E`-th power map
  let f : P →* ↥(omega1 P) :=
    { toFun := fun x => ⟨x ^ 2 ^ E, hfmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (pow_two_pow_mul h hcomm hE x y) }
  have hfval : ∀ x : P, ((f x : ↥(omega1 P)) : P) = x ^ 2 ^ E := fun _ => rfl
  -- `f` commutes with `ξ`
  have hfxi : ∀ x : P, ((f (h.xi x) : ↥(omega1 P)) : P) = h.xi ((f x : ↥(omega1 P)) : P) := by
    intro x
    rw [hfval (h.xi x), hfval x, map_pow]
  -- the kernel of `f` is exactly the centre
  have hker : f.ker = Subgroup.center P := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : x ^ 2 ^ E = 1 := by
        have hc := congrArg Subtype.val hx
        rwa [hfval x] at hc
      have hx'' : (x ^ 2) ^ 2 ^ (E - 1) = 1 := by rw [← hfold x]; exact hx'
      have hmem : x ^ 2 ∈ powSub (Subgroup.center P) 2 :=
        (hkey (x ^ 2) (sq_mem_center_of_comm h hcomm x)).mpr hx''
      rw [hbridge] at hmem
      exact mem_center_of_sq_mem_centerSq h hmem
    · intro hx
      refine Subtype.ext ?_
      rw [hfval x]
      exact he1 x hx
  -- `f` is not identically `1`, since `P` is not abelian
  have hne0 : ∃ x : P, f x ≠ 1 := by
    by_contra hc
    have hc' : ∀ x : P, f x = 1 := by
      intro x
      by_contra hx
      exact hc ⟨x, hx⟩
    obtain ⟨x, y, hxy⟩ := h.noncomm
    have hxZ : x ∈ Subgroup.center P := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr (hc' x)
    exact hxy (Subgroup.mem_center_iff.mp hxZ y).symm
  -- `f` commutes with every power of `ξ`
  have hfxi_pow : ∀ (k : ℕ) (x : P),
      ((f ((h.xi ^ k) x) : ↥(omega1 P)) : P) = (h.xi ^ k) ((f x : ↥(omega1 P)) : P) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        have hstep : (h.xi ^ (k + 1)) x = h.xi ((h.xi ^ k) x) := by
          rw [pow_succ', MulAut.mul_apply]
        have hstep' : (h.xi ^ (k + 1)) ((f x : ↥(omega1 P)) : P)
            = h.xi ((h.xi ^ k) ((f x : ↥(omega1 P)) : P)) := by
          rw [pow_succ', MulAut.mul_apply]
        rw [hstep, hfxi, ih, hstep']
  -- `f` is onto `Ω₁(P)`
  have hsurj : Function.Surjective f := by
    intro a
    rcases eq_or_ne a 1 with rfl | ha
    · exact ⟨1, map_one f⟩
    · obtain ⟨x₀, hx₀⟩ := hne0
      have hord_a : orderOf (a : P) = 2 := by
        have hd : orderOf (a : P) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp a.2)
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
        · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp h1)) ha
        · exact h2
      have hord_fx : orderOf ((f x₀ : ↥(omega1 P)) : P) = 2 := by
        have hd : orderOf ((f x₀ : ↥(omega1 P)) : P) ∣ 2 :=
          orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp (f x₀).2)
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
        · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp h1)) hx₀
        · exact h2
      obtain ⟨k, hk⟩ := h.trans _ (a : P) hord_fx hord_a
      exact ⟨(h.xi ^ k) x₀, Subtype.ext (by rw [hfxi_pow k x₀, hk])⟩
  -- descend `f` to `P ⧸ Z(P)`
  have hle : Subgroup.center P ≤ f.ker := by rw [hker]
  let F : (P ⧸ Subgroup.center P) →* ↥(omega1 P) :=
    QuotientGroup.lift (Subgroup.center P) f hle
  have hF : ∀ x : P, F (QuotientGroup.mk x) = f x := fun x =>
    QuotientGroup.lift_mk' (Subgroup.center P) hle x
  have hinj : Function.Injective F := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hF x, hF y] at hab
    have h1 : f (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : x⁻¹ * y ∈ Subgroup.center P := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr h1
    rw [QuotientGroup.eq]
    exact h2
  have hsurjF : Function.Surjective F := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨QuotientGroup.mk x, by rw [hF x, hx]⟩
  have hbij : Function.Bijective ⇑F := ⟨hinj, hsurjF⟩
  let eiso : (P ⧸ Subgroup.center P) ≃* ↥(omega1 P) := MulEquiv.ofBijective F hbij
  have heiso : ∀ q : (P ⧸ Subgroup.center P), eiso q = F q := fun q =>
    MulEquiv.ofBijective_apply F hbij q
  refine ⟨eiso, ?_⟩
  intro x
  show ((eiso (QuotientGroup.mk (h.xi x)) : ↥(omega1 P)) : P)
      = h.xi ((eiso (QuotientGroup.mk x) : ↥(omega1 P)) : P)
  rw [heiso, heiso, hF x, hF (h.xi x)]
  exact hfxi x

end Work.Higman
