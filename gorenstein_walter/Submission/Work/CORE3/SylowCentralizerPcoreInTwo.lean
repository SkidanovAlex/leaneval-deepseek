import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.Case1aFrattiniConj
import Submission.Work.CORE3.eq_one_of_mem_centralizer_sylow_two_of_conj_eq_inv
import Submission.Work.CORE3.map_conj_le_centralizer_of_conj_eq_inv

set_option linter.style.haveILetI false

namespace Work.CORE3

open Work.GW2

/-- **Bender 1981, §3, p. 223, first step in the proof of (5).**

In the setting of case (2,2) (`D : Case1bData B`, so `V := O₂(Ĥ) = pCoreIn 2 B.Hhat` is a
four-group and `|S| = 8`), an element `x ∈ U = O(H)` of odd order inverted by an involution
`y ∉ Ĥ` satisfies `V ∈ Syl₂(C_G(x))`, i.e.

`Odd (V.relIndex C_G(x)) = Odd [C_G(x) : V]`.

This is what Bender's "hence `V ∈ Syl₂(C_G(x))`" means.

*Proof.*  `V ≤ C_G(x)` because `V ≤ C_G(U)` (`Thm26Concl`, `I.h26`) and `x ∈ U`.  Suppose
`2 ∣ [C_G(x) : V]`.  Since `|V| = 4` we get `8 ∣ |C_G(x)|`, so (Sylow) there is `K ≤ C_G(x)`
with `|K| = 8` containing `V`.  As `|B.S| = 8` and `B.S` is a Sylow 2-subgroup of `G`, every
2-subgroup of `G` has order `≤ 8`, so `K ≤ G` is *itself* a Sylow 2-subgroup of `G`.

Now conjugation by `y` inverts `x`, so it normalizes `C_G(x)`; hence `y K y⁻¹ ≤ C_G(x)` and
`|y K y⁻¹| = 8`, so `K` and `y K y⁻¹` are Sylow 2-subgroups of `C_G(x)`: by Sylow conjugacy
inside `C_G(x)` there is `c ∈ C_G(x)` with `c (y K y⁻¹) c⁻¹ = K`.  Then `g := c y` lies in
`N_G(K)` and `g x g⁻¹ = c x⁻¹ c⁻¹ = x⁻¹` (as `c` centralizes `x`), while `x` has odd order and
commutes with `K ≤ C_G(x)`.  In `N_G(K)/K` — of odd order, as `K` is a Sylow 2-subgroup of `G` —
the image of `g` inverts the image of `x`; an element of odd order inverting an element of odd
order forces that element to be trivial, so `x ∈ K`, and an element of odd order in the 2-group
`K` is `1` — contradicting `x ≠ 1`. -/
theorem SylowCentralizerPcoreInTwo (I : Work.CORE3.Case1Inputs) (G : Type) [Group G] [Finite G]
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {x y : G}
    (hxU : x ∈ B.U) (hx1 : x ≠ 1) (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (hxy : y * x * y⁻¹ = x⁻¹) :
    Odd ((Work.GW2.pCoreIn 2 B.Hhat).relIndex (Subgroup.centralizer ({x} : Set G))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat with hV
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have h26 : Thm26Concl B := I.h26 G I.T.ft hBc B
  -- `V ≤ C_G(x)`
  have hVcU : V ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [hV, ← Work.CORE2A.thm26Concl_centralizer_eq h26]
    exact inf_le_right
  have hVC : V ≤ C := by
    rw [hC]
    refine hVcU.trans (Subgroup.centralizer_le ?_)
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    rw [hu]; exact hxU
  have hV4 : Nat.card ↥V = 4 := by rw [hV]; exact D.four.1
  -- `x` has odd order
  have hxodd : Odd (orderOf x) :=
    (Work.CORE2A.bSetup_U_odd B).of_dvd_nat (Subgroup.orderOf_dvd_natCard B.U hxU)
  -- cardinal identity `[C : V] * |V| = |C|`
  have hcard : V.relIndex C * Nat.card ↥V = Nat.card ↥C := by
    have h := Subgroup.relIndex_mul_card V C
    rwa [inf_eq_left.mpr hVC] at h
  rw [← Nat.not_even_iff_odd]
  intro hEven
  have h2dvd : 2 ∣ V.relIndex C := even_iff_two_dvd.mp hEven
  have h8dvd : 8 ∣ Nat.card ↥C := by
    rw [← hcard, hV4]
    have := mul_dvd_mul h2dvd (dvd_refl 4)
    simpa using this
  -- a 2-subgroup of `C_G(x)` of order 8 containing `V`
  obtain ⟨K, hKcard, hVK, hKC⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (p := 2) (n := 3)
    Nat.prime_two (H := V) (L := C) (by rw [hV4]; norm_num) (by simpa using h8dvd) hVC
  have hK8 : Nat.card ↥K = 8 := by rw [hKcard]; norm_num
  have hKp : IsPGroup 2 K := IsPGroup.of_card hKcard
  -- `K` is a Sylow 2-subgroup of `G`
  obtain ⟨P, hKP⟩ := hKp.exists_le_sylow
  have hP8 : Nat.card ↥(P : Subgroup G) = 8 := by
    rw [Sylow.card_eq_multiplicity P, ← Sylow.card_eq_multiplicity B.S]
    exact D.S8
  have hKeq : K = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hKP (by rw [hP8, hK8])
  -- `2 ∤ [C : K]`
  have hnot2 : ¬ 2 ∣ K.relIndex C := by
    intro h2
    have h2idx : 2 ∣ K.index := by
      rw [← Subgroup.relIndex_mul_index hKC]
      exact h2.mul_right C.index
    rw [hKeq] at h2idx
    exact Sylow.not_dvd_index P h2idx
  -- `y K y⁻¹ ≤ C_G(x)`
  have hQle : K.map (MulAut.conj y).toMonoidHom ≤ C := by
    rw [hC]
    exact Work.CORE3.map_conj_le_centralizer_of_conj_eq_inv hxy (by rw [← hC]; exact hKC)
  -- Sylow conjugacy inside `C_G(x)`
  obtain ⟨c, hcC, hconjc⟩ := Work.CORE3.ConjSylowOfSubgroup 2 Nat.prime_two C K
    (K.map (MulAut.conj y).toMonoidHom) hKC hQle hKp
    (hKp.map (MulAut.conj y).toMonoidHom)
    (Subgroup.card_map_of_injective (MulAut.conj y).injective).symm hnot2
  have hcC' : c ∈ Subgroup.centralizer ({x} : Set G) := hC ▸ hcC
  -- `c * y` normalizes `K`
  have hgN : c * y ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · intro z hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨k, hk, hkz⟩ := hz
      rw [← hkz]
      change c * y * k * (c * y)⁻¹ ∈ K
      have h1 : y * k * y⁻¹ ∈ K.map (MulAut.conj y).toMonoidHom := by
        rw [Subgroup.mem_map]
        exact ⟨k, hk, by show (MulAut.conj y) k = y * k * y⁻¹; rw [MulAut.conj_apply]⟩
      have h2 := (hconjc _).mp h1
      have h3 : (c * y) * k * (c * y)⁻¹ = c * (y * k * y⁻¹) * c⁻¹ := by group
      rw [h3]; exact h2
    · rw [Subgroup.card_map_of_injective (MulAut.conj (c * y)).injective]
  -- `c * y` inverts `x`
  have hcx : c * x * c⁻¹ = x := by
    have hcomm : x * c = c * x := (Subgroup.mem_centralizer_iff.mp hcC') x (by simp)
    calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [hcomm]
      _ = x := by group
  have hcxinv : c * x⁻¹ * c⁻¹ = x⁻¹ := by
    have h2 : (c * x * c⁻¹)⁻¹ = c * x⁻¹ * c⁻¹ := by group
    rw [hcx] at h2
    exact h2.symm
  have hgx : (c * y) * x * (c * y)⁻¹ = x⁻¹ := by
    have h3 : (c * y) * x * (c * y)⁻¹ = c * (y * x * y⁻¹) * c⁻¹ := by group
    rw [h3, hxy, hcxinv]
  -- an odd-order element of `N_G(K)` inverting `x` forces `x = 1`
  have hgN' : c * y ∈ Subgroup.normalizer (((P : Subgroup G)) : Set G) := hKeq ▸ hgN
  have hxK' : ∀ t ∈ (P : Subgroup G), t * x = x * t := by
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (hKC (hKeq.symm ▸ ht)) x (by simp)).symm
  have hxone : x = 1 :=
    Work.CORE3.eq_one_of_mem_centralizer_sylow_two_of_conj_eq_inv P hgN' hxK' hxodd hgx
  exact hx1 hxone

end Work.CORE3
