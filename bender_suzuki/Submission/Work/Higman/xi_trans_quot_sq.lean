import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.PowSub

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.Higman

/-- A `ξ`-invariant subgroup is invariant under every power of `ξ`. -/
theorem map_xi_pow_eq {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : A.map (h.xi : MulAut P).toMonoidHom = A) (n : ℕ) :
    A.map ((h.xi ^ n : MulAut P)).toMonoidHom = A := by
  induction n with
  | zero =>
    show Subgroup.map ((h.xi ^ 0 : MulAut P)).toMonoidHom A = A
    rw [show ((h.xi ^ 0 : MulAut P)).toMonoidHom = MonoidHom.id P by ext x; simp]
    exact Subgroup.map_id A
  | succ n ih =>
    rw [pow_succ]
    have hcomp : (((h.xi ^ n) * h.xi : MulAut P)).toMonoidHom =
        ((h.xi ^ n : MulAut P)).toMonoidHom.comp (h.xi : MulAut P).toMonoidHom := by
      ext x
      simp [MulAut.mul_apply]
    rw [hcomp, ← Subgroup.map_map, hA, ih]

/-- If `A` is a `ξ`-invariant subgroup then `ξ ^ n` maps `A` into itself. -/
theorem apply_xi_pow_mem {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A : Subgroup P} (hA : A.map (h.xi : MulAut P).toMonoidHom = A) (n : ℕ) {a : P}
    (ha : a ∈ A) : (h.xi ^ n) a ∈ A := by
  have hmap := map_xi_pow_eq h hA n
  have hmem := Subgroup.mem_map_of_mem ((h.xi ^ n : MulAut P)).toMonoidHom ha
  rwa [hmap] at hmem

/-- `ξ` acts transitively on the non-zero vectors of `A / A²`: for `x, y ∈ A` with `x, y ∉ A²`
there is `k` with `(ξ ^ k) x ≡ y` modulo `A²`.

Proof sketch.  Let `e` be given by `mem_powSub_two_iff h hA`, whose `hkey3` says
`u ∈ powSub A 2 ↔ u ^ (2 ^ (e-1)) = 1` for `u ∈ A`.  For `z ∈ A` put `z* = z ^ 2 ^ (e-1)`; then
`z*` is an involution (`z* * z* = z ^ (2^e) = 1`) and `z* = 1 ↔ z ∈ powSub A 2` (by `hkey3`).
Since `ξ` is transitive on the involutions of `P` (`h.trans`), there is `k` with
`(ξ ^ k) (x*) = y*`; then `((ξ ^ k) x * y⁻¹) ^ 2 ^ (e-1) = 1` because `A` is abelian, so
`hkey3` (applied to `(ξ ^ k) x * y⁻¹ ∈ A`) gives `(ξ ^ k) x * y⁻¹ ∈ powSub A 2`. -/
theorem xi_trans_quot_sq {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    {x y : P} (hxA : x ∈ A) (hyA : y ∈ A)
    (hx : x ∉ Work.Higman.powSub A 2) (hy : y ∉ Work.Higman.powSub A 2) :
    ∃ k : ℕ, (h.xi ^ k) x * y⁻¹ ∈ Work.Higman.powSub A 2 := by
  classical
  obtain ⟨hAn, hAinv, hAb⟩ := hA
  obtain ⟨e, he1, -, hkey⟩ := mem_powSub_two_iff h ⟨hAn, hAinv, hAb⟩
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  · -- `A` has exponent `1`, so `A = ⊥` and `x = 1 ∈ A²`, contradicting `hx`.
    have hbot : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      have hh := he1 z hz
      simpa [he0] using hh
    rw [hbot] at hxA
    simp only [Subgroup.mem_bot] at hxA
    exact absurd (hxA ▸ Subgroup.one_mem (powSub A 2)) hx
  · -- `2 ^ (e-1)`-st powers of elements of `A` are exactly the involutions of `A`.
    have hk2 : 2 ^ (e - 1) * 2 = 2 ^ e := by
      rw [← pow_succ]
      congr 1
      omega
    have hxstar_sq : (x ^ 2 ^ (e - 1)) ^ 2 = 1 := by
      rw [← pow_mul, hk2]; exact he1 x hxA
    have hystar_sq : (y ^ 2 ^ (e - 1)) ^ 2 = 1 := by
      rw [← pow_mul, hk2]; exact he1 y hyA
    have hxstar_ne : x ^ 2 ^ (e - 1) ≠ 1 := fun hc => hx ((hkey x hxA).mpr hc)
    have hystar_ne : y ^ 2 ^ (e - 1) ≠ 1 := fun hc => hy ((hkey y hyA).mpr hc)
    have hxstar_ord : orderOf (x ^ 2 ^ (e - 1)) = 2 := by
      have hd : orderOf (x ^ 2 ^ (e - 1)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hxstar_sq
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hxstar_ne
      · exact h2
    have hystar_ord : orderOf (y ^ 2 ^ (e - 1)) = 2 := by
      have hd : orderOf (y ^ 2 ^ (e - 1)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hystar_sq
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hystar_ne
      · exact h2
    -- `ξ` is transitive on the involutions, so some power matches the two images
    obtain ⟨n, hn⟩ := h.trans (x ^ 2 ^ (e - 1)) (y ^ 2 ^ (e - 1)) hxstar_ord hystar_ord
    refine ⟨n, ?_⟩
    have hpow : ((h.xi ^ n) x) ^ 2 ^ (e - 1) = y ^ 2 ^ (e - 1) := by
      rw [← map_pow, hn]
    have hxiA : (h.xi ^ n) x ∈ A := apply_xi_pow_mem h hAinv n hxA
    have hmemA : (h.xi ^ n) x * y⁻¹ ∈ A := A.mul_mem hxiA (A.inv_mem hyA)
    have hcomm : Commute ((h.xi ^ n) x) y⁻¹ := hAb _ hxiA _ (A.inv_mem hyA)
    have hfinal : ((h.xi ^ n) x * y⁻¹) ^ 2 ^ (e - 1) = 1 := by
      rw [hcomm.mul_pow, hpow, inv_pow, mul_inv_cancel]
    exact (hkey ((h.xi ^ n) x * y⁻¹) hmemA).mpr hfinal

end Work.Higman
