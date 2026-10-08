/-
# The action of `⟨ξ⟩` on `P/A` is fixed-coset-free

Higman's §4 bookkeeping needs the `𝔽₂⟨ξ⟩`-module `P/A` to be as free as possible.  Here we
prove the elementary structural fact that drives that: if every square of `P` lies in `A`,
`Ω₁(P) ≤ A`, `A² = Ω₁(P)`, and `ξ` permutes the involutions of `P` transitively, then

* any non-trivial fixed point of `ξ^k` inside `Ω₁(P)` forces `ξ^k` to fix all of `Ω₁(P)`
  (`fix_all_omega1_of_fix`), and consequently
* a fixed *coset* of `ξ^k` modulo `A` that is non-trivial (i.e. `x ∉ A` with `ξ^k x ≡ x mod A`)
  forces `ξ^k` to fix all of `Ω₁(P)` (`fixed_coset_imp_fix_all`).

The proof of the second statement is a Hilbert-90-style adjustment: the map `b ↦ ξ^k b · b⁻¹`
on the abelian group `A` has trivial kernel (any fixed point of `ξ^k` in `A` would give, by
`A/A² ≅ A² = Ω₁(P)`, a fixed involution), hence is bijective; using it one can move a fixed
coset to a fixed point `y ∉ A`, and then `y² ∈ A` is fixed, so `y² = 1`, i.e. `y` is one of the
involutions in `Ω₁(P) ≤ A` — contradiction.
-/
import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- `A` is invariant under every power of `ξ` when it is invariant under `ξ`. -/
theorem map_pow_xi_eq (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) (k : ℕ) :
    A.map ((h.xi ^ k : MulAut P)).toMonoidHom = A := by
  induction k with
  | zero => rw [pow_zero]; ext y; simp
  | succ k ih =>
    rw [pow_succ]
    have hcomp : (((h.xi ^ k) * h.xi : MulAut P)).toMonoidHom
        = ((h.xi ^ k : MulAut P)).toMonoidHom.comp (h.xi : MulAut P).toMonoidHom := by
      ext y; simp [MulAut.mul_apply]
    rw [hcomp, ← Subgroup.map_map, hAinv, ih]

/-- If `ξ ^ k` fixes one non-trivial element of `Ω₁(P)`, it fixes all of `Ω₁(P)`
(transitivity of `ξ` on the involutions). -/
theorem fix_all_omega1_of_fix (h : IsSuzuki2Grp P)
    {k : ℕ} {z : P} (hz : z ∈ omega1 P) (hz1 : z ≠ 1) (hzfix : (h.xi ^ k) z = z) :
    ∀ w ∈ omega1 P, (h.xi ^ k) w = w := by
  intro w hw
  rcases eq_or_ne w 1 with hw1 | hw1
  · subst hw1; simp
  · have hz2 : orderOf z = 2 := orderOf_eq_prime (h.mem_omega1.mp hz) hz1
    have hw2 : orderOf w = 2 := orderOf_eq_prime (h.mem_omega1.mp hw) hw1
    obtain ⟨j, hj⟩ := h.trans z w hz2 hw2
    calc (h.xi ^ k) w = (h.xi ^ k) ((h.xi ^ j) z) := by rw [hj]
      _ = (h.xi ^ (k + j)) z := by rw [← MulAut.mul_apply, ← pow_add]
      _ = (h.xi ^ (j + k)) z := by rw [Nat.add_comm]
      _ = (h.xi ^ j * h.xi ^ k) z := by rw [pow_add]
      _ = (h.xi ^ j) ((h.xi ^ k) z) := by rw [MulAut.mul_apply]
      _ = (h.xi ^ j) z := by rw [hzfix]
      _ = w := hj

/-- Rearrangement in an abelian subgroup: `p·q⁻¹ = r·s⁻¹` implies `p·s = r·q`. -/
theorem mul_eq_mul_of_mul_inv_eq_mul_inv {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {p q r s : P} (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A) (hs : s ∈ A)
    (h : p * q⁻¹ = r * s⁻¹) : p * s = r * q := by
  have h2 : p * q⁻¹ * (q * s) = r * s⁻¹ * (q * s) := by rw [h]
  have hq' : q⁻¹ * (q * s) = s := by group
  have hs' : s⁻¹ * (q * s) = q := by
    rw [← mul_assoc, hAab s⁻¹ (A.inv_mem hs) q hq, mul_assoc, inv_mul_cancel, mul_one]
  rw [mul_assoc p q⁻¹ (q * s), hq', mul_assoc r s⁻¹ (q * s), hs'] at h2
  exact h2

/-- Rearrangement in an abelian subgroup: `p·q = r·s` implies `p·r⁻¹ = s·q⁻¹`. -/
theorem mul_inv_eq_of_mul_eq_mul {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {p q r s : P} (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A) (hs : s ∈ A)
    (h : p * q = r * s) : p * r⁻¹ = s * q⁻¹ := by
  have hq' : q * (q⁻¹ * r⁻¹) = r⁻¹ := by group
  have hmul : s * q⁻¹ * r⁻¹ = s * (q⁻¹ * r⁻¹) := by rw [mul_assoc]
  calc p * r⁻¹ = p * q * (q⁻¹ * r⁻¹) := by rw [mul_assoc, hq']
    _ = r * s * (q⁻¹ * r⁻¹) := by rw [h]
    _ = r * (s * q⁻¹ * r⁻¹) := by rw [mul_assoc, mul_assoc]
    _ = r * (s * (q⁻¹ * r⁻¹)) := by rw [hmul]
    _ = (s * (q⁻¹ * r⁻¹)) * r := hAab r hr (s * (q⁻¹ * r⁻¹))
        (A.mul_mem hs (A.mul_mem (A.inv_mem hq) (A.inv_mem hr)))
    _ = s * ((q⁻¹ * r⁻¹) * r) := by rw [mul_assoc]
    _ = s * (q⁻¹ * (r⁻¹ * r)) := by rw [mul_assoc q⁻¹ r⁻¹ r]
    _ = s * q⁻¹ := by rw [inv_mul_cancel, mul_one]

/-- **A non-trivial fixed coset modulo `A` forces `ξ ^ k` to fix all of `Ω₁(P)`.**

Hypotheses: `A ⊴ P` abelian, `ξ`-invariant, `Ω₁(P) ≤ A`, `A² = Ω₁(P)`, every square of `P`
lies in `A`, and `ξ` permutes the involutions of `P` transitively (the `IsSuzuki2Grp`
hypothesis).  If `x ∉ A` and `ξ ^ k x ≡ x (mod A)`, then `ξ ^ k` fixes every element of
`Ω₁(P)`. -/
theorem fixed_coset_imp_fix_all (h : IsSuzuki2Grp P)
    {A : Subgroup P} (hAn : A.Normal)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A) (htop : powSub A 2 = omega1 P)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    {k : ℕ} {x : P} (hxA : x ∉ A) (hfix : ((h.xi ^ k) x) * x⁻¹ ∈ A) :
    ∀ w ∈ omega1 P, (h.xi ^ k) w = w := by
  classical
  have hAk : A.map ((h.xi ^ k : MulAut P)).toMonoidHom = A := map_pow_xi_eq h hAinv k
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw, hwne⟩ := hcon
  -- there is no non-trivial fixed point in Ω₁(P)
  have hno : ∀ z ∈ omega1 P, (h.xi ^ k) z = z → z = 1 := by
    intro z hz hzf
    by_contra hz1
    exact hwne (fix_all_omega1_of_fix h hz hz1 hzf w hw)
  -- any fixed point of ξ^k in A is trivial
  have hCA : ∀ b ∈ A, (h.xi ^ k) b = b → b = 1 := by
    intro b hb hbf
    have hb2w : b ^ 2 ∈ omega1 P := by
      rw [← htop]; exact pow_mem_powSub hb
    have hb2f : (h.xi ^ k) (b ^ 2) = b ^ 2 := by rw [map_pow, hbf]
    exact hno b (h.mem_omega1.mpr (hno _ hb2w hb2f)) hbf
  -- the map `b ↦ ξ^k b · b⁻¹` on `A` is injective, hence surjective
  have hmem : ∀ b ∈ A, (h.xi ^ k) b * b⁻¹ ∈ A := by
    intro b hb
    have h1 : (h.xi ^ k) b ∈ A := by
      have := Subgroup.mem_map_of_mem ((h.xi ^ k : MulAut P)).toMonoidHom hb
      rwa [hAk] at this
    exact A.mul_mem h1 (A.inv_mem hb)
  have hinj : ∀ u ∈ A, ∀ v ∈ A, (h.xi ^ k) u * u⁻¹ = (h.xi ^ k) v * v⁻¹ → u = v := by
    intro u hu v hv huv
    have hu' : (h.xi ^ k) u ∈ A := by
      have := Subgroup.mem_map_of_mem ((h.xi ^ k : MulAut P)).toMonoidHom hu
      rwa [hAk] at this
    have hv' : (h.xi ^ k) v ∈ A := by
      have := Subgroup.mem_map_of_mem ((h.xi ^ k : MulAut P)).toMonoidHom hv
      rwa [hAk] at this
    have key : (h.xi ^ k) u * v = (h.xi ^ k) v * u :=
      mul_eq_mul_of_mul_inv_eq_mul_inv hAab hu' hu hv' hv huv
    have hkey : (h.xi ^ k) u * ((h.xi ^ k) v)⁻¹ = u * v⁻¹ :=
      mul_inv_eq_of_mul_eq_mul hAab hu' hv hv' hu key
    have hfixuv : (h.xi ^ k) (u * v⁻¹) = u * v⁻¹ := by rw [map_mul, map_inv, hkey]
    have hmemuv : u * v⁻¹ ∈ A := A.mul_mem hu (A.inv_mem hv)
    exact mul_inv_eq_one.mp (hCA _ hmemuv hfixuv)
  -- surjectivity of the same map on `A`
  have hsurj : ∀ c ∈ A, ∃ b ∈ A, (h.xi ^ k) b * b⁻¹ = c := by
    intro c hc
    -- the map `b ↦ ⟨ξ^k b · b⁻¹, _⟩` is injective on the finite type `↥A`
    have hf : Function.Injective (fun b : ↥A => (⟨(h.xi ^ k) (b : P) * (b : P)⁻¹, hmem b b.2⟩ : ↥A)) := by
      intro u v huv
      exact Subtype.ext (hinj u u.2 v v.2 (by simpa using congrArg (fun t : ↥A => (t : P)) huv))
    obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.mp hf) ⟨c, hc⟩
    exact ⟨b, b.2, by simpa using congrArg (fun t : ↥A => (t : P)) hb⟩
  -- move the fixed coset of `x` to a fixed point
  set a : P := (h.xi ^ k) x * x⁻¹ with ha
  have haA : a ∈ A := hfix
  have hcA : x⁻¹ * a⁻¹ * x ∈ A := by
    simpa using hAn.conj_mem a⁻¹ (A.inv_mem haA) x⁻¹
  obtain ⟨b, hbA, hbspec⟩ := hsurj (x⁻¹ * a⁻¹ * x) hcA
  have hbval : (h.xi ^ k) b = (x⁻¹ * a⁻¹ * x) * b := by rw [← hbspec]; group
  have haval : (h.xi ^ k) x = a * x := by rw [ha]; group
  have hyfix : (h.xi ^ k) (x * b) = x * b := by
    rw [map_mul, haval, hbval]
    group
  have hyA : x * b ∉ A := by
    intro hyA'
    apply hxA
    have hxeq : x = x * b * b⁻¹ := by group
    rw [hxeq]
    exact A.mul_mem hyA' (A.inv_mem hbA)
  have hy2eq : (x * b) * (x * b) = 1 := by
    have h2A : (x * b) * (x * b) ∈ A := by simpa [pow_two] using hsq (x * b)
    have h2fix : (h.xi ^ k) ((x * b) * (x * b)) = (x * b) * (x * b) := by rw [map_mul, hyfix]
    exact hCA _ h2A h2fix
  have hyom : x * b ∈ omega1 P := h.mem_omega1.mpr (by rw [pow_two]; exact hy2eq)
  exact hyA (hNA hyom)

end Work.Higman

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- **`ξ ^ k` has no non-trivial fixed coset modulo `A` unless it is trivial on `Ω₁(P)`.**

Equivalently: the stabiliser in `⟨ξ⟩` of a nonzero element of `P/A` is contained in the kernel
of the action of `⟨ξ⟩` on `Ω₁(P)`.  Consequently every `⟨ξ⟩`-orbit on `(P/A) \ {0}` has at
least as many elements as the `⟨ξ⟩`-orbit on `Ω₁(P) \ {1}`, namely `q - 1` when `ξ` acts
transitively there: this is the input that pins `finrank (P/A)` down in Higman's §4
bookkeeping. -/
theorem fixed_coset_of_nontrivial_omega1 (h : IsSuzuki2Grp P)
    {A : Subgroup P} (hAn : A.Normal)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A) (htop : powSub A 2 = omega1 P)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    {k : ℕ} {x : P} (hfix : ((h.xi ^ k) x) * x⁻¹ ∈ A)
    (hnt : ∃ z ∈ omega1 P, (h.xi ^ k) z ≠ z) :
    x ∈ A := by
  by_contra hxA
  obtain ⟨z, hz, hzne⟩ := hnt
  exact hzne (fixed_coset_imp_fix_all h hAn hAinv hAab hNA htop hsq hxA hfix z hz)

end Work.Higman

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- **Step (b) of the kernel analysis.**  If an automorphism `k` of `P` fixes a normal subgroup
`A` pointwise, then `k x * x⁻¹` centralises `A` for every `x ∈ P`.

Indeed `k (a * x) = a * k x` (as `a ∈ A` is fixed) and also
`k (a * x) = k x * (x⁻¹ * a * x)` (moving `a` past `x` and using that `x⁻¹ * a * x ∈ A` is
fixed); comparing and cancelling `x` on the right gives `a * (k x * x⁻¹) = (k x * x⁻¹) * a`. -/
theorem commute_mul_inv_of_fixes_pointwise {A : Subgroup P} (hAn : A.Normal) {k : MulAut P}
    (hk : ∀ a ∈ A, k a = a) (x : P) {a : P} (ha : a ∈ A) :
    a * (k x * x⁻¹) = (k x * x⁻¹) * a := by
  have h1 : k (a * x) = a * k x := by rw [map_mul, hk a ha]
  have h2 : k (a * x) = k x * (x⁻¹ * a * x) := by
    have hax : x⁻¹ * a * x ∈ A := by
      have := hAn.conj_mem a ha x⁻¹
      simpa using this
    have heq : a * x = x * (x⁻¹ * a * x) := by group
    rw [heq, map_mul, hk _ hax]
  have h3 : a * k x = k x * (x⁻¹ * a * x) := by rw [← h1, h2]
  have hkx : k x = (k x * x⁻¹) * x := by group
  have h4 : a * ((k x * x⁻¹) * x) = ((k x * x⁻¹) * x) * (x⁻¹ * a * x) := by
    rw [← hkx]; exact h3
  have h5 : a * (k x * x⁻¹) * x = (k x * x⁻¹) * a * x := by
    calc a * (k x * x⁻¹) * x = a * ((k x * x⁻¹) * x) := by group
      _ = ((k x * x⁻¹) * x) * (x⁻¹ * a * x) := h4
      _ = (k x * x⁻¹) * a * x := by group
  exact mul_right_cancel h5

/-- **Step (a), first half.**  If an automorphism `k` of `P` fixes `Ω₁(P)` pointwise, leaves an
abelian subgroup `A` invariant, and `A² = Ω₁(P)`, then `k ^ 2` fixes `A` pointwise: writing
`k a = a * c` with `c = k a * a⁻¹ ∈ A`, squaring gives `a² = (k a)² = a² * c²` (as `a² ∈ A² =
Ω₁(P)` is fixed), so `c ∈ A²` is fixed by `k`, and `k (k a) = k a * c = a * c² = a`. -/
theorem apply_apply_eq_self_of_fixes_omega1 {A : Subgroup P} {k : MulAut P}
    (hAinv : A.map (k : MulAut P).toMonoidHom = A) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (htop : powSub A 2 = omega1 P) (hkΩ : ∀ z ∈ omega1 P, k z = z) :
    ∀ a ∈ A, k (k a) = a := by
  intro a ha
  have hka : k a ∈ A := by
    have := Subgroup.mem_map_of_mem (k : MulAut P).toMonoidHom ha
    rwa [hAinv] at this
  have h4 : a * a ∈ omega1 P := by
    rw [← htop]; simpa [pow_two] using (pow_mem_powSub (n := 2) ha)
  have hzA : k a * a⁻¹ ∈ A := A.mul_mem hka (A.inv_mem ha)
  have hka_eq : k a = a * (k a * a⁻¹) := by
    rw [← mul_assoc a (k a) a⁻¹, hAab a ha (k a) hka]
    group
  have hz2 : (k a * a⁻¹) * (k a * a⁻¹) = 1 := by
    have hh : (k a * a⁻¹) * (k a * a⁻¹) = (k a * k a) * (a⁻¹ * a⁻¹) := by
      calc (k a * a⁻¹) * (k a * a⁻¹) = (k a) * (a⁻¹ * (k a * a⁻¹)) := by rw [mul_assoc]
        _ = (k a) * ((a⁻¹ * (k a)) * a⁻¹) := by rw [mul_assoc a⁻¹ (k a) a⁻¹]
        _ = (k a) * (((k a) * a⁻¹) * a⁻¹) := by rw [hAab a⁻¹ (A.inv_mem ha) (k a) hka]
        _ = (k a) * ((k a) * (a⁻¹ * a⁻¹)) := by rw [mul_assoc (k a) a⁻¹ a⁻¹]
        _ = (k a * k a) * (a⁻¹ * a⁻¹) := by rw [← mul_assoc]
    rw [hh, ← map_mul, hkΩ (a * a) h4]
    group
  have hzOm : k a * a⁻¹ ∈ omega1 P :=
    Subgroup.subset_closure (mem_sqOne.mpr (by rw [pow_two]; exact hz2))
  calc k (k a) = k (a * (k a * a⁻¹)) := congrArg k hka_eq
    _ = (k a) * (k (k a * a⁻¹)) := by rw [map_mul]
    _ = (k a) * (k a * a⁻¹) := by rw [hkΩ (k a * a⁻¹) hzOm]
    _ = (a * (k a * a⁻¹)) * (k a * a⁻¹) := congrArg (fun t => t * (k a * a⁻¹)) hka_eq
    _ = a * ((k a * a⁻¹) * (k a * a⁻¹)) := by rw [mul_assoc]
    _ = a * 1 := by rw [hz2]
    _ = a := by rw [mul_one]


/-- **Exponent shifting (first half of the odd-order extraction).**  If `ξ ^ k` fixes `y` and
`ξ ^ j` sends `x` to `y`, then `ξ ^ (j + t * k)` also sends `x` to `y`, for every `t : ℕ`.
This is the step that lets one move a solution exponent `j` into any prescribed residue class
modulo `k` (used with `k = q - 1` and `ξ^(q-1)` fixing `Ω₁(P)` pointwise). -/
theorem pow_add_mul_pow_eq_of_fixes (h : IsSuzuki2Grp P) {x y : P} {j k : ℕ}
    (hj : (h.xi ^ j) x = y) (hy : (h.xi ^ k) y = y) (t : ℕ) :
    (h.xi ^ (j + t * k)) x = y := by
  have htk : (h.xi ^ (t * k)) y = y := by
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.succ_mul, pow_add, MulAut.mul_apply, hy]; exact ih
  rw [Nat.add_comm j (t * k), pow_add, MulAut.mul_apply, hj, htk]

end Work.Higman
