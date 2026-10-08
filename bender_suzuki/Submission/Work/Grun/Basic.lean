/-
# Area `Work.Grun` — P. Hall's transfer theorem (M. Hall, *The Theory of Groups*, §14.4)

Notation used throughout the area:

* `iterComm n u z = ⁅u, z, …, z⁆` (`n` copies of `z`), Hall's `u_{n+1} = e_{n+1}(u,z)`;
  in particular `iterComm (p-1) u z` is Hall's `e_p(u,z)`.
* `cosetKernel H P x`, Hall's `K(x)`: the kernel of the action of `P` by left multiplication on
  the cosets `y * x * H` of `H` (`y ∈ P`), i.e. of the permutation representation of `P` on the
  cosets of `H` inside the double coset `P x H`.

Reference: M. Hall, *The Theory of Groups* (1959), §14.4, pp. 204–213 (Theorem 14.4.1).
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Classical Pointwise commutatorElement

namespace Work.Grun

variable {G : Type*} [Group G]

/-! ### Iterated commutators -/

/-- `iterComm n u z = ⁅u, z, …, z⁆` with `n` copies of `z`; Hall's `u_{n+1}`, so that
`iterComm (p-1) u z = e_p(u,z)`. -/
def iterComm : ℕ → G → G → G
  | 0, u, _ => u
  | n + 1, u, z => ⁅iterComm n u z, z⁆

@[simp] theorem iterComm_zero (u z : G) : iterComm 0 u z = u := rfl

theorem iterComm_succ (n : ℕ) (u z : G) : iterComm (n + 1) u z = ⁅iterComm n u z, z⁆ := rfl

@[simp] theorem iterComm_one (u z : G) : iterComm 1 u z = ⁅u, z⁆ := rfl

theorem iterComm_two (u z : G) : iterComm 2 u z = ⁅⁅u, z⁆, z⁆ := rfl

/-- The iterated commutators are `P`-valued when `u, z ∈ P`. -/
theorem iterComm_mem {P : Subgroup G} {u z : G} (hu : u ∈ P) (hz : z ∈ P) (n : ℕ) :
    iterComm n u z ∈ P := by
  induction n with
  | zero => simpa using hu
  | succ k ih =>
    rw [iterComm_succ, commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem ih hz) (P.inv_mem ih)) (P.inv_mem hz)

/-- If `⁅⁅u,z⁆,z⁆ = 1` then all higher iterated commutators are `1` as well. -/
theorem iterComm_eq_one_of_iterComm_two_eq_one {u z : G} (h : iterComm 2 u z = 1) :
    ∀ n : ℕ, 2 ≤ n → iterComm n u z = 1 := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · omega
      · simpa using h
    · rw [iterComm_succ, ih hk, commutatorElement_def]
      simp

/-! ### Hall's `K(x)` -/

/-- Hall's `K(x)` (M. Hall, §14.4): the kernel of the action of `P` by left multiplication on the
cosets `y * x * H` of `H`, `y ∈ P`; equivalently the kernel of the permutation representation of
`P` on the cosets of `H` in the double coset `P x H`. -/
def cosetKernel (H P : Subgroup G) (x : G) : Subgroup G where
  carrier := {u | u ∈ P ∧ ∀ y ∈ P, (y * x)⁻¹ * u * (y * x) ∈ H}
  one_mem' := ⟨P.one_mem, fun y _ => by simp⟩
  mul_mem' := fun {a b} ha hb => by
    refine ⟨P.mul_mem ha.1 hb.1, fun y hy => ?_⟩
    have ha' := ha.2 y hy
    have hb' := hb.2 y hy
    have : (y * x)⁻¹ * (a * b) * (y * x) =
        ((y * x)⁻¹ * a * (y * x)) * ((y * x)⁻¹ * b * (y * x)) := by group
    rw [this]
    exact H.mul_mem ha' hb'
  inv_mem' := fun {a} ha => by
    refine ⟨P.inv_mem ha.1, fun y hy => ?_⟩
    have ha' := ha.2 y hy
    have : (y * x)⁻¹ * a⁻¹ * (y * x) = ((y * x)⁻¹ * a * (y * x))⁻¹ := by group
    rw [this]
    exact H.inv_mem ha'

theorem mem_cosetKernel {H P : Subgroup G} {x u : G} :
    u ∈ cosetKernel H P x ↔ u ∈ P ∧ ∀ y ∈ P, (y * x)⁻¹ * u * (y * x) ∈ H := Iff.rfl

theorem cosetKernel_le (H P : Subgroup G) (x : G) : cosetKernel H P x ≤ P := fun _ h => h.1

/-- `K(x)` is the kernel of the action of `P` on the cosets of `H` in the double coset `P x H`. -/
theorem mem_cosetKernel_iff_smul {H P : Subgroup G} {x u : G} :
    u ∈ cosetKernel H P x ↔
      u ∈ P ∧ ∀ y ∈ P, u • ((y * x : G) : G ⧸ H) = ((y * x : G) : G ⧸ H) := by
  rw [mem_cosetKernel]
  refine and_congr_right fun _ => forall_congr' fun y => forall_congr' fun _ => ?_
  rw [show u • ((y * x : G) : G ⧸ H) = ((u * (y * x) : G) : G ⧸ H) by simp, QuotientGroup.eq]
  constructor
  · intro h; simpa [mul_assoc] using H.inv_mem h
  · intro h; simpa [mul_assoc] using H.inv_mem h

/-- The elements of `K(x)` fix every coset of the `P`-orbit of `x`. -/
theorem smul_eq_of_mem_cosetKernel {H P : Subgroup G} {x c : G} (hc : c ∈ cosetKernel H P x)
    {y : G} (hy : y ∈ P) : c • ((y * x : G) : G ⧸ H) = ((y * x : G) : G ⧸ H) :=
  (mem_cosetKernel_iff_smul.mp hc).2 y hy

/-- `u` fixes the `z`-translate of a fixed coset, provided `⁅u,z⁆` acts trivially on the orbit. -/
theorem smul_mul_smul_eq_of_mem_cosetKernel {H P : Subgroup G} {x u z : G} (hzP : z ∈ P)
    (hc : ⁅u, z⁆ ∈ cosetKernel H P x) {y : G} (hy : y ∈ P)
    (hu : u • ((y * x : G) : G ⧸ H) = ((y * x : G) : G ⧸ H)) :
    u • (z • ((y * x : G) : G ⧸ H)) = z • ((y * x : G) : G ⧸ H) := by
  have h2 : u * z = ⁅u, z⁆ * z * u := by rw [commutatorElement_def]; group
  have h1 : u • (z • ((y * x : G) : G ⧸ H)) = ⁅u, z⁆ • (z • ((y * x : G) : G ⧸ H)) := by
    rw [← mul_smul, h2, mul_smul, mul_smul, hu]
  rw [h1, show z • ((y * x : G) : G ⧸ H) = (((z * y) * x : G) : G ⧸ H) by
    simp [mul_assoc]]
  exact smul_eq_of_mem_cosetKernel hc (P.mul_mem hzP hy)

end Work.Grun
