import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.pure_abelian_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- For a subgroup `A` of a Suzuki 2-group, the elements of `A` with `x ^ 2 = 1` are exactly
`A ⊓ Ω₁(P)`; in particular the two subtypes have the same cardinality. -/
theorem card_twoTorsion_eq_card_inf_omega1 (h : IsSuzuki2Grp P) (A : Subgroup P) :
    Nat.card {x : ↥A | x ^ 2 = 1} = Nat.card ↥(A ⊓ (omega1 P : Subgroup P)) := by
  refine Nat.card_eq_of_bijective
    (fun x : {x : ↥A | x ^ 2 = 1} =>
      (⟨(x.1 : P), Subgroup.mem_inf.mpr ⟨x.1.2, h.mem_omega1.mpr (by
        rw [← Subgroup.coe_pow A x.1 2, x.2]; rfl)⟩⟩ :
        ↥(A ⊓ (omega1 P : Subgroup P)))) ?_
  constructor
  · intro x y hxy
    refine Subtype.ext (Subtype.ext ?_)
    exact congrArg (fun t : ↥(A ⊓ (omega1 P : Subgroup P)) => (t.1 : P)) hxy
  · intro y
    have hyA : (y : P) ∈ A := (Subgroup.mem_inf.mp y.2).1
    have hy2 : (y : P) ^ 2 = 1 := h.mem_omega1.mp (Subgroup.mem_inf.mp y.2).2
    refine ⟨⟨⟨(y : P), hyA⟩, ?_⟩, ?_⟩
    · change (⟨(y : P), hyA⟩ : ↥A) ^ 2 = 1
      rw [Subtype.ext_iff, Subgroup.coe_pow A ⟨(y : P), hyA⟩ 2, Subgroup.coe_one]
      exact hy2
    · exact Subtype.ext rfl

/-- In a Suzuki 2-group `P`, if `A` is `ξ`-invariant and `x ∈ A` is a non-trivial element with
`x ^ 2 = 1` that is a `2 ^ s`-th power in `A`, then every element of `A` with `z ^ 2 = 1` is a
`2 ^ s`-th power in `A`.  (Transitivity of `ξ` on the involutions of `P`.) -/
theorem exists_pow_eq_of_mem_invol (h : IsSuzuki2Grp P)
    {A : Subgroup P} (hinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    {s : ℕ} {x : P} (hxA : x ∈ A) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hpow : ∃ y ∈ A, y ^ 2 ^ s = x) :
    ∀ z ∈ A, z ^ 2 = 1 → ∃ y ∈ A, y ^ 2 ^ s = z := by
  have hpres : ∀ k : ℕ, ∀ y : P, y ∈ A → (h.xi ^ k) y ∈ A := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have hz : (h.xi ^ k) y ∈ A := ih y hy
      have hgoal : (h.xi ^ (k + 1)) y = h.xi.toMonoidHom ((h.xi ^ k) y) := by
        rw [pow_succ', MulAut.mul_apply]; rfl
      rw [hgoal]
      have hmem : h.xi.toMonoidHom ((h.xi ^ k) y) ∈ A.map (h.xi : MulAut P).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hz
      rwa [hinv] at hmem
  have hxord : orderOf x = 2 := by
    have hd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h2
  intro z hzA hz2
  rcases eq_or_ne z 1 with rfl | hz1
  · exact ⟨1, A.one_mem, by rw [one_pow]⟩
  · have hzord : orderOf z = 2 := by
      have hd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hz1
      · exact h2
    obtain ⟨k, hk⟩ := h.trans x z hxord hzord
    obtain ⟨y, hyA, hy⟩ := hpow
    refine ⟨(h.xi ^ k) y, hpres k y hyA, ?_⟩
    calc ((h.xi ^ k) y) ^ 2 ^ s = (h.xi ^ k) (y ^ 2 ^ s) := by rw [map_pow]
      _ = (h.xi ^ k) x := by rw [hy]
      _ = z := hk

/-- A finite abelian 2-group has exponent `2 ^ E` for some `E`, attained by an element. -/
theorem exists_exponent_pow (A : Type*) [CommGroup A] [Finite A] (h2 : IsPGroup 2 A) :
    ∃ E : ℕ, (∀ a : A, a ^ 2 ^ E = 1) ∧ (∃ a : A, orderOf a = 2 ^ E) := by
  obtain ⟨E, hE⟩ := h2.exists_exponent_eq_pow
  refine ⟨E, fun a => ?_, ?_⟩
  · rw [← hE]
    exact Monoid.pow_exponent_eq_one a
  · obtain ⟨a, ha⟩ := Monoid.exists_orderOf_eq_exponent (G := A) Monoid.ExponentExists.of_finite
    exact ⟨a, by rw [ha, hE]⟩

/-- **Higman (1963), Lemma 1** (cyclic case).  An abelian subgroup `A` invariant under `ξ` of a
Suzuki 2-group is homocyclic: with `2 ^ e` its exponent, `|A| = |A ⊓ Ω₁(P)| ^ e`. -/
theorem higman_lemma1 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hinv : A.map (h.xi : MulAut P).toMonoidHom = A) :
    ∃ e : ℕ, (∀ a ∈ A, a ^ 2 ^ e = 1) ∧ (∃ a ∈ A, orderOf a = 2 ^ e) ∧
      Nat.card ↥A = (Nat.card ↥(A ⊓ (Work.Higman.omega1 P : Subgroup P))) ^ e := by
  letI : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun x y => Subtype.ext (hab x x.2 y y.2) }
  have h2 : IsPGroup 2 ↥A := h.isPGroup.to_subgroup A
  have hdich : ∀ (s : ℕ) (x : ↥A), x ^ 2 = 1 → x ≠ 1 → (∃ y : ↥A, y ^ 2 ^ s = x) →
      ∀ z : ↥A, z ^ 2 = 1 → ∃ y : ↥A, y ^ 2 ^ s = z := by
    intro s x hx2 hx1 hpow z hz2
    obtain ⟨y, hy⟩ := hpow
    have hx2' : (x : P) ^ 2 = 1 := by rw [← Subgroup.coe_pow A x 2, hx2]; rfl
    have hx1' : (x : P) ≠ 1 := fun hc => hx1 (Subtype.ext (by rw [hc]; rfl))
    have hpow' : ∃ w ∈ A, w ^ 2 ^ s = (x : P) := by
      refine ⟨(y : P), y.2, ?_⟩
      rw [← Subgroup.coe_pow A y (2 ^ s), hy]
    have hz2' : (z : P) ^ 2 = 1 := by rw [← Subgroup.coe_pow A z 2, hz2]; rfl
    obtain ⟨w, hwA, hw⟩ :=
      exists_pow_eq_of_mem_invol h hinv (s := s) (x := (x : P)) x.2 hx2' hx1' hpow' (z : P) z.2 hz2'
    exact ⟨⟨w, hwA⟩, Subtype.ext (by rw [Subgroup.coe_pow A ⟨w, hwA⟩ (2 ^ s)]; exact hw)⟩
  obtain ⟨e, he1, he2⟩ := exists_exponent_pow ↥A h2
  have he3 := pure_abelian_card ↥A h2 hdich e he1 he2
  refine ⟨e, ?_, ?_, ?_⟩
  · intro a ha
    have hsub := congrArg (Subgroup.subtype A) (he1 ⟨a, ha⟩)
    simpa [Subgroup.coe_pow] using hsub
  · obtain ⟨x, hx⟩ := he2
    exact ⟨(x : P), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  · rw [he3]
    exact congrArg (fun n => n ^ e) (card_twoTorsion_eq_card_inf_omega1 h A)

end Work.Higman
