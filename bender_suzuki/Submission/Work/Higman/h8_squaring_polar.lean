import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.commutator_powSub_A_C

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

namespace Work.Higman

/-! ## The polar form of the squaring map

Higman 1963, §4.  In the situation of Higman's Lemma 8 — `A` a `ξ`-invariant abelian normal
subgroup of a Suzuki 2-group, `C` a subgroup with `C ^ (2) ≤ A` and `⁅C,C⁆ = A` — the `2 ^ e`-th
power of a product of two elements of `C` (`2 ^ e` the exponent of `A`) has the polar form

`(u * v) ^ (2 ^ e) = u ^ (2 ^ e) * v ^ (2 ^ e) * ⁅v, u⁆ ^ (2 ^ (e - 1))`.

The content of the argument is that this is *exactly* the polar form: the Hall–Petrescu
correction terms vanish because they all land in `A ^ (2 ^ e) = 1`.  Writing `θ_m ∈ A ^ (2 ^ (m+1))`
for the total correction after `m + 1` squarings, unipotence (`⁅u, a⁆ ∈ A ^ (2)` for `a ∈ A`,
from `commutator_mem_powSub_two`) gives the base case

`(u * v) ^ 2 = u ^ 2 * v ^ 2 * ⁅v,u⁆ * θ₀`,  `θ₀ = ⁅u, ⁅v,u⁆⁆ ∈ A ^ (2)`,

and the induction step is just `(xy) ^ 2 = x ^ 2 * y ^ 2` for the four pairwise commuting factors
of the inductive formula, with `θ_{m+1} = θ_m ^ 2 ∈ A ^ (2 ^ (m + 2))`.
-/

/-- `(x ^ (2 ^ k)) ^ 2 = x ^ (2 ^ (k + 1))`. -/
private theorem pow_two_pow_sq {G : Type} [Group G] (x : G) (k : ℕ) :
    (x ^ 2 ^ k) ^ 2 = x ^ 2 ^ (k + 1) := by
  rw [← pow_mul, show 2 ^ k * 2 = 2 ^ (k + 1) from (pow_succ 2 k).symm]

/-- `x ^ (2 ^ (k + 1)) = (x ^ 2) ^ (2 ^ k)`. -/
private theorem pow_two_pow_succ {G : Type} [Group G] (x : G) (k : ℕ) :
    x ^ 2 ^ (k + 1) = (x ^ 2) ^ 2 ^ k := by
  rw [← pow_mul]
  congr 1
  exact pow_succ' 2 k

/-- Reversal of a product of four elements of an abelian subgroup. -/
private theorem mul_four_rev {G : Type} [Group G] {A : Subgroup G}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {a b c d : G}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) :
    a * b * c * d = d * c * b * a := by
  have h1 : Commute (a * b) (c * d) :=
    hAab (a * b) (A.mul_mem ha hb) (c * d) (A.mul_mem hc hd)
  have h2 : Commute a b := hAab a ha b hb
  have h3 : Commute c d := hAab c hc d hd
  calc a * b * c * d = (a * b) * (c * d) := by group
    _ = (c * d) * (a * b) := h1.eq
    _ = d * c * (a * b) := by rw [h3.eq]
    _ = d * c * (b * a) := by rw [h2.eq]
    _ = d * c * b * a := by group

/-- Squaring a product of four elements of an abelian subgroup. -/
private theorem mul_four_sq {G : Type} [Group G] {A : Subgroup G}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {a b c d : G}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) :
    (a * b * c * d) ^ 2 = a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 := by
  have h1 : Commute (a * b) (c * d) :=
    hAab (a * b) (A.mul_mem ha hb) (c * d) (A.mul_mem hc hd)
  have h2 : Commute a b := hAab a ha b hb
  have h3 : Commute c d := hAab c hc d hd
  rw [show a * b * c * d = (a * b) * (c * d) from by group, h1.mul_pow 2, h2.mul_pow 2,
    h3.mul_pow 2]
  group

/-- Squaring raises the exponent level of a power subgroup by one. -/
private theorem sq_mem_powSub_succ {G : Type} [Group G] {A : Subgroup G}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {m : ℕ} {θ : G}
    (hθ : θ ∈ powSub A (2 ^ (m + 1))) : θ ^ 2 ∈ powSub A (2 ^ (m + 1 + 1)) := by
  obtain ⟨a, ha, rfl⟩ := (mem_powSub_iff hAab).mp hθ
  rw [pow_two_pow_sq]
  exact pow_mem_powSub ha

/-- **The polar form of iterated squaring.**  Let `A` be an abelian subgroup, `C` a subgroup
with `C ^ (2) ≤ A` and `⁅C,C⁆ ≤ A`, and suppose that `u` acts on `A` trivially modulo `A ^ (2)`
(`⁅u,a⁆ ∈ A ^ (2)` for `a ∈ A`).  Then for `u, v ∈ C` the `2 ^ (m + 1)`-st power of `u * v` is
`u ^ (2 ^ (m+1)) * v ^ (2 ^ (m+1)) * ⁅v,u⁆ ^ (2 ^ m)` up to a correction `θ` lying in
`A ^ (2 ^ (m+1))`. -/
private theorem squaring_chain {G : Type} [Group G] {A C : Subgroup G}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hkey : ∀ u ∈ C, ∀ a ∈ A, ⁅u, a⁆ ∈ powSub A 2)
    (hC2 : powSub C 2 ≤ A) (hCd : ⁅C, C⁆ ≤ A) :
    ∀ m : ℕ, ∀ u ∈ C, ∀ v ∈ C, ∃ θ ∈ powSub A (2 ^ (m + 1)),
      (u * v) ^ 2 ^ (m + 1) = u ^ 2 ^ (m + 1) * v ^ 2 ^ (m + 1) * ⁅v, u⁆ ^ 2 ^ m * θ := by
  intro m
  induction m with
  | zero =>
      intro u hu v hv
      have hu2 : u ^ 2 ∈ A := hC2 (pow_mem_powSub hu)
      have hv2 : v ^ 2 ∈ A := hC2 (pow_mem_powSub hv)
      have hvu : ⁅v, u⁆ ∈ A := hCd (Subgroup.commutator_mem_commutator hv hu)
      have hX : ⁅u, ⁅v, u⁆⁆ ∈ powSub A 2 := hkey u hu ⁅v, u⁆ hvu
      have hXA : ⁅u, ⁅v, u⁆⁆ ∈ A := powSub_le (by norm_num) hX
      refine ⟨⁅u, ⁅v, u⁆⁆, ?_, ?_⟩
      · simpa using hX
      · have hid : (u * v) ^ 2 = ⁅u, ⁅v, u⁆⁆ * ⁅v, u⁆ * u ^ 2 * v ^ 2 := by
          simp only [commutatorElement_def, pow_two]
          group
        have hrev : ⁅u, ⁅v, u⁆⁆ * ⁅v, u⁆ * u ^ 2 * v ^ 2
            = u ^ 2 * v ^ 2 * ⁅v, u⁆ * ⁅u, ⁅v, u⁆⁆ := by
          rw [mul_four_rev hAab hXA hvu hu2 hv2, hAab (v ^ 2) hv2 (u ^ 2) hu2]
        have h2e : (2 : ℕ) ^ (0 + 1) = 2 := by norm_num
        have h0e : (2 : ℕ) ^ 0 = 1 := by norm_num
        rw [h2e, h0e, pow_one]
        rw [hid, hrev]
  | succ m ih =>
      intro u hu v hv
      obtain ⟨θ, hθmem, hθeq⟩ := ih u hu v hv
      have hu2 : u ^ 2 ∈ A := hC2 (pow_mem_powSub hu)
      have hv2 : v ^ 2 ∈ A := hC2 (pow_mem_powSub hv)
      have hvu : ⁅v, u⁆ ∈ A := hCd (Subgroup.commutator_mem_commutator hv hu)
      have hθA : θ ∈ A := powSub_le (by norm_num) hθmem
      have huA : u ^ 2 ^ (m + 1) ∈ A := by
        rw [pow_two_pow_succ]
        exact Subgroup.pow_mem A hu2 (2 ^ m)
      have hvA : v ^ 2 ^ (m + 1) ∈ A := by
        rw [pow_two_pow_succ]
        exact Subgroup.pow_mem A hv2 (2 ^ m)
      have hvuA : ⁅v, u⁆ ^ 2 ^ m ∈ A := Subgroup.pow_mem A hvu (2 ^ m)
      refine ⟨θ ^ 2, sq_mem_powSub_succ hAab hθmem, ?_⟩
      show (u * v) ^ 2 ^ (m + 1 + 1)
        = u ^ 2 ^ (m + 1 + 1) * v ^ 2 ^ (m + 1 + 1) * ⁅v, u⁆ ^ 2 ^ (m + 1) * θ ^ 2
      have hstep : (u * v) ^ 2 ^ (m + 1 + 1) = ((u * v) ^ 2 ^ (m + 1)) ^ 2 := by
        rw [pow_two_pow_sq]
      rw [hstep, hθeq, mul_four_sq hAab huA hvA hvuA hθA, pow_two_pow_sq u (m + 1),
        pow_two_pow_sq v (m + 1), pow_two_pow_sq (⁅v, u⁆) m]

open scoped commutatorElement in
theorem h8_squaring_polar {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hC2 : Work.Higman.powSub C 2 ≤ A) (hCd : ⁅C, C⁆ = A) {e : ℕ}
    (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he : 1 ≤ e) {u v : P} (hu : u ∈ C) (hv : v ∈ C) :
    (u * v) ^ 2 ^ e = u ^ 2 ^ e * v ^ 2 ^ e * ⁅v, u⁆ ^ 2 ^ (e - 1) := by
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hA.abelian x hx y hy
  have hkey : ∀ u ∈ C, ∀ a ∈ A, ⁅u, a⁆ ∈ powSub A 2 :=
    fun u _ a ha => commutator_mem_powSub_two h hA u a ha
  obtain ⟨θ, hθmem, hθeq⟩ :=
    squaring_chain hAab hkey hC2 (le_of_eq hCd) (e - 1) u hu v hv
  have hsub : e - 1 + 1 = e := Nat.sub_add_cancel he
  rw [hsub] at hθmem hθeq
  have hθ1 : θ = 1 := by
    have hbot : powSub A (2 ^ e) = ⊥ := powSub_eq_bot_of_exp hAab le_rfl he1
    have h : θ ∈ (⊥ : Subgroup P) := by rwa [← hbot]
    simpa using h
  rw [hθeq, hθ1, mul_one]

end Work.Higman
