import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.isPGroup_pCoreIn_two

/-!
# CORE2B — glue between the `hyp` clause of `L29Hyp` and `O₂(N_G(X))`

Bender 1981, Lemma 2.9, p. 222.  The hypothesis

`hyp : ∀ s ∈ S, ∀ X ≤ U, X ≠ ⊥, [⟨s⟩,X] = X → t ∈ O₂(N_G(X))`

is the only clause of `L29Hyp` that mentions the ambient group through anything other than
`S`; this module extracts its consequences for a subgroup `A ◁ N` of odd order.

* `pCoreIn_inf_eq_bot_of_odd`:  `O₂(M) ⊓ A = ⊥` for `A` of odd order (a 2-group meets an
  odd-order group trivially).
* `conj_mem_pCoreIn`: `M` normalizes `O₂(M) = pCoreIn 2 M`.
* `centralizes_normalizer_of_hyp`: **the key step of Bender's argument.**  For a *valid seed*
  `X` (`X ≤ U`, `X ≠ ⊥`, `X = [⟨s⟩,X]` with `s ∈ S`) and an odd `A ◁ N` (with `A ≤ N`),
  the involution `t` centralizes `N_A(X) = A ⊓ N_G(X)`: `[t, N_A(X)]` lies in `O₂(N_G(X))`
  (as `t` does and `O₂` is normal in `N_G(X)`) and in `A` (as `t ∈ N`, `A ◁ N`), hence in
  `O₂(N_G(X)) ⊓ A = ⊥`.

This is exactly the step Bender's printed proof takes for granted ("Lying in `O₂(N_G(X))`, `t`
centralizes `N_A(X)`"), together with its justification: the odd order of the subgroup involved
is what makes `O₂(N_G(X)) ⊓ A` trivial.
-/

namespace Work.CORE2B

open Subgroup
open scoped commutatorElement

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {G : Type} [Group G] [Finite G]

/-- `O₂(M) ⊓ A = ⊥` for an odd-order `A`: `O₂(M)` is a 2-group, and the order of a common
element divides both a power of two and `|A|` (odd). -/
theorem pCoreIn_inf_eq_bot_of_odd (M A : Subgroup G) (hodd : Odd (Nat.card A)) :
    Work.GW2.pCoreIn 2 M ⊓ A = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxQ, hxA⟩ := hx
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf (p := 2)).mp (isPGroup_pCoreIn_two M) ⟨x, hxQ⟩
  rw [Subgroup.orderOf_mk] at hn
  have hdvd : orderOf x ∣ Nat.card ↥A := by
    rw [← Subgroup.orderOf_mk x hxA]; exact orderOf_dvd_natCard _
  have hoddx : Odd (orderOf x) := Odd.of_dvd_nat hodd hdvd
  have hn0 : n = 0 := by
    by_contra h
    have h2 : 2 ∣ orderOf x := by rw [hn]; exact dvd_pow_self 2 h
    exact (Nat.not_even_iff_odd.mpr hoddx)
      (Nat.even_iff.mpr (Nat.dvd_iff_mod_eq_zero.mp h2))
  rw [hn0, pow_zero] at hn
  exact orderOf_eq_one_iff.mp hn

/-- `M` normalizes `O₂(M) = pCoreIn 2 M`. -/
theorem conj_mem_pCoreIn {M : Subgroup G} {m p : G} (hm : m ∈ M)
    (hp : p ∈ Work.GW2.pCoreIn 2 M) : m * p * m⁻¹ ∈ Work.GW2.pCoreIn 2 M := by
  rw [Work.GW2.pCoreIn, Subgroup.mem_map] at hp ⊢
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨⟨m, hm⟩ * q * ⟨m, hm⟩⁻¹,
    (Work.GW2.pCore_normal 2 ↥M).conj_mem q hq ⟨m, hm⟩, by simp⟩

/-- **The `hyp` clause implies that `t` centralizes `N_A(X)` for every valid seed `X`.**

`h : L29Hyp B V N`, `A ◁ N` of odd order with `A ≤ N`, `X ≤ U` with `X ≠ ⊥` and
`X = [⟨s⟩,X]` for `s ∈ S`.  Then `N_G(X) ⊓ A ≤ C_G(t)`. -/
theorem centralizes_normalizer_of_hyp (B : Work.GW2.BenderSetup G) (V N A X : Subgroup G)
    (h : L29Hyp B V N) (hAN : A ≤ N) (hAnorm : (A.subgroupOf N).Normal)
    (hAodd : Odd (Nat.card A)) (hXU : X ≤ B.U) (hXne : X ≠ ⊥) {s : G}
    (hs : s ∈ (B.S : Subgroup G)) (hXeq : ⁅Subgroup.zpowers s, X⁆ = X) :
    Subgroup.normalizer (X : Set G) ⊓ A ≤ Subgroup.centralizer ({B.t} : Set G) := by
  classical
  set P : Subgroup G := Work.GW2.pCoreIn 2 (Subgroup.normalizer (X : Set G)) with hPdef
  intro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hyNX, hyA⟩ := hy
  have htN : B.t ∈ N := h.V_le_N h.t_mem
  have hyN : y ∈ N := hAN hyA
  -- `t ∈ O₂(N_G(X))`
  have htO2 : B.t ∈ P := h.hyp s X hs hXU hXne hXeq
  have hyO2 : y * B.t * y⁻¹ ∈ P := conj_mem_pCoreIn hyNX htO2
  -- the commutator `t * y * t⁻¹ * y⁻¹` lies in `O₂(N_G(X))`
  have hcommO2 : B.t * y * B.t⁻¹ * y⁻¹ ∈ P := by
    have h2 : y * B.t⁻¹ * y⁻¹ = (y * B.t * y⁻¹)⁻¹ := by group
    have h3 : y * B.t⁻¹ * y⁻¹ ∈ P := by rw [h2]; exact P.inv_mem hyO2
    have h4 : B.t * (y * B.t⁻¹ * y⁻¹) ∈ P := P.mul_mem htO2 h3
    rwa [show B.t * (y * B.t⁻¹ * y⁻¹) = B.t * y * B.t⁻¹ * y⁻¹ from by group] at h4
  -- and in `A`, since `A ◁ N` and `t, y ∈ N`
  have hconjA : B.t * y * B.t⁻¹ ∈ A := by
    have hyAS : (⟨y, hyN⟩ : ↥N) ∈ A.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]; exact hyA
    have hmem : (⟨B.t, htN⟩ * ⟨y, hyN⟩ * (⟨B.t, htN⟩)⁻¹ : ↥N) ∈ A.subgroupOf N :=
      hAnorm.conj_mem ⟨y, hyN⟩ hyAS ⟨B.t, htN⟩
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  have hcommA : B.t * y * B.t⁻¹ * y⁻¹ ∈ A :=
    A.mul_mem hconjA (A.inv_mem hyA)
  have hcomm_bot : B.t * y * B.t⁻¹ * y⁻¹ = 1 := by
    have hmem : B.t * y * B.t⁻¹ * y⁻¹ ∈ (P ⊓ A) := ⟨hcommO2, hcommA⟩
    rw [hPdef, pCoreIn_inf_eq_bot_of_odd _ _ hAodd] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hty : y * B.t = B.t * y := by
    have h : B.t * y * B.t⁻¹ = y := (mul_inv_eq_one).mp hcomm_bot
    calc y * B.t = (B.t * y * B.t⁻¹) * B.t := by rw [h]
      _ = B.t * y := by group
  rwa [Subgroup.mem_centralizer_singleton_iff]

end Work.CORE2B
