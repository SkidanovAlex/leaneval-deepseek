import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.FourGroupOrderThreeFixed

/-!
# CORE3: an odd-order element normalizing a four-group acts by a 3-cycle,
and any commuting involution centralizes the four-group

`V ≤ G` is a Klein four-group (`Work.GW2.IsFourGroup V`: `|V| = 4` and every element of `V` is
an involution).  Let `x ∈ N_G(V)` have odd order and not centralize `V`.

* `Work.CORE3.fourGroup_oddOrder_conjCycle`: conjugation by `x` induces an automorphism `φ` of
  `V` of odd order dividing `|Aut(V)| = 6` (an automorphism permutes the three nonidentity
  elements), and `φ ≠ 1` because `x ∉ C_G(V)`; hence `φ` has order exactly `3`, i.e. `x` acts
  as a `3`-cycle on `V#`.  Concretely there are `a ∈ V#` and `b = x a x⁻¹` with
  `V = {1, a, b, a b}`, `x b x⁻¹ = a b` and `x (a b) x⁻¹ = a`.

* `Work.CORE3.FourGroupOddOrderCommutingInvolution`: if moreover `c ∈ N_G(V)` is an involution
  (`c² = 1`) commuting with `x`, then `c` centralizes `V`.  Indeed conjugation by `c` is an
  automorphism `ψ` of `V` with `ψ² = 1` and `ψ φ = φ ψ`; since the three nonidentity elements
  form a single `φ`-orbit, `ψ` must fix them all, whence `ψ = 1`.

The main auxiliary input is `Work.CORE3.fourGroup_eq_four` (from `FourGroupOrderThreeFixed`):
two distinct nonidentity elements `a, b` of a Klein four-group satisfy `V = {1, a, b, a b}`.
-/

namespace Work.CORE3

open Subgroup

/-- An odd-order normalizer `x` of a Klein four-group `V` which does not centralize `V` acts
as a `3`-cycle on the three nonidentity elements of `V`. -/
theorem fourGroup_oddOrder_conjCycle {G : Type} [Group G] [Finite G] {V : Subgroup G} {x : G}
    (hV4 : Work.GW2.IsFourGroup V)
    (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hxo : Odd (orderOf x))
    (hxnc : x ∉ Subgroup.centralizer (V : Set G)) :
    ∃ a b : G, a ∈ V ∧ b ∈ V ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
      (V : Set G) = {1, a, b, a * b} ∧
      x * a * x⁻¹ = b ∧ x * b * x⁻¹ = a * b ∧ x * (a * b) * x⁻¹ = a := by
  classical
  -- an element moved by conjugation by `x`
  obtain ⟨a0, ha0V, ha0x⟩ : ∃ w, w ∈ V ∧ w * x ≠ x * w := by
    by_contra hcon
    apply hxnc
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    by_contra hne
    exact hcon ⟨v, hv, hne⟩
  have ha1 : a0 ≠ 1 := by
    intro h
    exact ha0x (by rw [h, one_mul, mul_one])
  have ha2 : a0 * a0 = 1 := by simpa [pow_two] using hV4.2 a0 ha0V
  have ha0_inv : a0⁻¹ = a0 := inv_eq_of_mul_eq_one_right ha2
  have hconj_mem : ∀ v ∈ V, x * v * x⁻¹ ∈ V :=
    fun v hv => (Subgroup.mem_normalizer_iff.mp hxN v).mp hv
  have hbV : x * a0 * x⁻¹ ∈ V := hconj_mem a0 ha0V
  have hb2 : (x * a0 * x⁻¹) * (x * a0 * x⁻¹) = 1 := by
    simpa [pow_two] using hV4.2 (x * a0 * x⁻¹) hbV
  have hb1 : x * a0 * x⁻¹ ≠ 1 := by
    intro h
    apply ha1
    calc a0 = x⁻¹ * (x * a0 * x⁻¹) * x := by group
      _ = x⁻¹ * 1 * x := by rw [h]
      _ = 1 := by group
  have hab : a0 ≠ x * a0 * x⁻¹ := by
    intro h
    apply ha0x
    calc a0 * x = (x * a0 * x⁻¹) * x := congrArg (fun z => z * x) h
      _ = x * a0 := by group
  have hinj : ∀ v w : G, x * v * x⁻¹ = x * w * x⁻¹ → v = w := by
    intro v w h
    calc v = x⁻¹ * (x * v * x⁻¹) * x := by group
      _ = x⁻¹ * (x * w * x⁻¹) * x := by rw [h]
      _ = w := by group
  have hVset : (V : Set G) = {1, a0, x * a0 * x⁻¹, a0 * (x * a0 * x⁻¹)} :=
    fourGroup_eq_four hV4.1 hV4.2 ha0V hbV ha1 hb1 hab
  have hab1 : a0 * (x * a0 * x⁻¹) ≠ 1 := by
    intro h
    exact hab (ha0_inv.symm.trans (inv_eq_of_mul_eq_one_right h))
  have hab2 : a0 * (x * a0 * x⁻¹) ≠ a0 := by
    intro h
    refine hb1 (mul_left_cancel (a := a0) ?_)
    rw [h, mul_one]
  have hab3 : a0 * (x * a0 * x⁻¹) ≠ x * a0 * x⁻¹ := by
    intro h
    refine ha1 (mul_right_cancel (b := x * a0 * x⁻¹) ?_)
    rw [h, one_mul]
  have heV : x * (x * a0 * x⁻¹) * x⁻¹ ∈ V := hconj_mem _ hbV
  have he_ne_one : x * (x * a0 * x⁻¹) * x⁻¹ ≠ 1 := by
    intro h
    refine hb1 (hinj (x * a0 * x⁻¹) 1 ?_)
    exact h.trans (by group)
  have he_ne_b : x * (x * a0 * x⁻¹) * x⁻¹ ≠ x * a0 * x⁻¹ := by
    intro h
    exact hab (hinj (x * a0 * x⁻¹) a0 h).symm
  have he_mem : x * (x * a0 * x⁻¹) * x⁻¹
      ∈ ({1, a0, x * a0 * x⁻¹, a0 * (x * a0 * x⁻¹)} : Set G) := by
    rw [← hVset]; exact heV
  rcases Set.mem_insert_iff.mp he_mem with he1 | he_mem
  · exact absurd he1 he_ne_one
  · rcases Set.mem_insert_iff.mp he_mem with he_a0 | he_mem
    · -- `x` induces an automorphism of `V` squaring to the identity; this forces `x ^ 2` to
      -- centralize `V`, contradicting the oddness of `orderOf x`.
      exfalso
      have hfix_a : (x * x) * a0 * (x * x)⁻¹ = a0 := by
        calc (x * x) * a0 * (x * x)⁻¹ = x * (x * a0 * x⁻¹) * x⁻¹ := by group
          _ = a0 := he_a0
      have hfix_b : (x * x) * (x * a0 * x⁻¹) * (x * x)⁻¹ = x * a0 * x⁻¹ := by
        calc (x * x) * (x * a0 * x⁻¹) * (x * x)⁻¹
            = x * (x * (x * a0 * x⁻¹) * x⁻¹) * x⁻¹ := by group
          _ = x * a0 * x⁻¹ := by rw [he_a0]
      have hfix_ab : (x * x) * (a0 * (x * a0 * x⁻¹)) * (x * x)⁻¹
          = a0 * (x * a0 * x⁻¹) := by
        calc (x * x) * (a0 * (x * a0 * x⁻¹)) * (x * x)⁻¹
            = ((x * x) * a0 * (x * x)⁻¹) * ((x * x) * (x * a0 * x⁻¹) * (x * x)⁻¹) := by
              group
          _ = a0 * (x * a0 * x⁻¹) := by rw [hfix_a, hfix_b]
      have hx2fix : ∀ v ∈ V, (x * x) * v * (x * x)⁻¹ = v := by
        intro v hv
        have hvmem : v ∈ ({1, a0, x * a0 * x⁻¹, a0 * (x * a0 * x⁻¹)} : Set G) := by
          rw [← hVset]; exact hv
        rcases Set.mem_insert_iff.mp hvmem with hv1 | hvmem
        · rw [hv1]; group
        · rcases Set.mem_insert_iff.mp hvmem with hva | hvmem
          · rw [hva]; exact hfix_a
          · rcases Set.mem_insert_iff.mp hvmem with hvb | hvmem
            · rw [hvb]; exact hfix_b
            · rw [Set.mem_singleton_iff.mp hvmem]; exact hfix_ab
      have hx2C : x ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
        rw [pow_two]
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hv' := hx2fix v hv
        calc v * (x * x) = ((x * x) * v * (x * x)⁻¹) * (x * x) := by rw [hv']
          _ = (x * x) * v := by group
      obtain ⟨k, hk⟩ := hxo
      have hx_eq : x = (x ^ 2) ^ (k + 1) := by
        rw [← pow_mul]
        rw [show 2 * (k + 1) = orderOf x + 1 by omega]
        rw [pow_succ, pow_orderOf_eq_one, one_mul]
      have hxC : x ∈ Subgroup.centralizer (V : Set G) := by
        rw [hx_eq]
        exact Subgroup.pow_mem _ hx2C (k + 1)
      exact hxnc hxC
    · rcases Set.mem_insert_iff.mp he_mem with he_b | he_mem
      · exact absurd he_b he_ne_b
      · -- the cycle case
        have hmain_ii : x * (x * a0 * x⁻¹) * x⁻¹ = a0 * (x * a0 * x⁻¹) :=
          Set.mem_singleton_iff.mp he_mem
        have hmain_iii : x * (a0 * (x * a0 * x⁻¹)) * x⁻¹ = a0 := by
          have hfV : x * (a0 * (x * a0 * x⁻¹)) * x⁻¹ ∈ V :=
            hconj_mem _ (V.mul_mem ha0V hbV)
          have hf_ne_one : x * (a0 * (x * a0 * x⁻¹)) * x⁻¹ ≠ 1 := by
            intro h
            refine hab1 (hinj (a0 * (x * a0 * x⁻¹)) 1 ?_)
            exact h.trans (by group)
          have hf_ne_b : x * (a0 * (x * a0 * x⁻¹)) * x⁻¹ ≠ x * a0 * x⁻¹ := by
            intro h
            refine hab2 (hinj (a0 * (x * a0 * x⁻¹)) a0 ?_)
            exact h
          have hf_ne_ab : x * (a0 * (x * a0 * x⁻¹)) * x⁻¹ ≠ a0 * (x * a0 * x⁻¹) := by
            intro h
            refine hab3 (hinj (a0 * (x * a0 * x⁻¹)) (x * a0 * x⁻¹) ?_)
            exact h.trans hmain_ii.symm
          have hf_mem : x * (a0 * (x * a0 * x⁻¹)) * x⁻¹
              ∈ ({1, a0, x * a0 * x⁻¹, a0 * (x * a0 * x⁻¹)} : Set G) := by
            rw [← hVset]; exact hfV
          rcases Set.mem_insert_iff.mp hf_mem with hf1 | hf_mem
          · exact absurd hf1 hf_ne_one
          · rcases Set.mem_insert_iff.mp hf_mem with hfa | hf_mem
            · exact hfa
            · rcases Set.mem_insert_iff.mp hf_mem with hfb | hf_mem
              · exact absurd hfb hf_ne_b
              · exact absurd (Set.mem_singleton_iff.mp hf_mem) hf_ne_ab
        exact ⟨a0, x * a0 * x⁻¹, ha0V, hbV, ha1, hb1, hab, hVset, rfl, hmain_ii, hmain_iii⟩

theorem FourGroupOddOrderCommutingInvolution {G : Type} [Group G] [Finite G] {V : Subgroup G} {x c : G}
    (hV4 : Work.GW2.IsFourGroup V)
    (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hcN : c ∈ Subgroup.normalizer (V : Set G))
    (hxo : Odd (orderOf x))
    (hxnc : x ∉ Subgroup.centralizer (V : Set G))
    (hc2 : c ^ 2 = 1)
    (hxc : c * x = x * c) :
    c ∈ Subgroup.centralizer (V : Set G) := by
  classical
  obtain ⟨a, b, haV, hbV, ha1, hb1, hab, hVset, hxa, hxb, hxab⟩ :=
    fourGroup_oddOrder_conjCycle hV4 hxN hxo hxnc
  have hcc : c * c = 1 := by rw [← pow_two]; exact hc2
  have hc_mem : ∀ v ∈ V, c * v * c⁻¹ ∈ V :=
    fun v hv => (Subgroup.mem_normalizer_iff.mp hcN v).mp hv
  -- conjugation by `c` commutes with conjugation by `x`
  have hstep : ∀ w : G, c * (x * w * x⁻¹) * c⁻¹ = x * (c * w * c⁻¹) * x⁻¹ := by
    intro w
    have h2 : x⁻¹ * c⁻¹ = c⁻¹ * x⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hxc]
    calc c * (x * w * x⁻¹) * c⁻¹ = (c * x) * w * (x⁻¹ * c⁻¹) := by group
      _ = (x * c) * w * (c⁻¹ * x⁻¹) := by rw [hxc, h2]
      _ = x * (c * w * c⁻¹) * x⁻¹ := by group
  have hpsib : c * b * c⁻¹ = x * (c * a * c⁻¹) * x⁻¹ := by
    rw [← hxa]; exact hstep a
  have hpsiab : c * (a * b) * c⁻¹ = x * (c * b * c⁻¹) * x⁻¹ := by
    rw [← hxb]; exact hstep b
  have hphi2 : c * (c * a * c⁻¹) * c⁻¹ = a := by
    calc c * (c * a * c⁻¹) * c⁻¹ = (c * c) * a * (c * c)⁻¹ := by group
      _ = a := by rw [hcc, one_mul, inv_one, mul_one]
  have hab_mul_a : a * b ≠ a := by
    intro h
    exact hb1 (mul_left_cancel (a := a) (by rw [h, mul_one]))
  have hcaV : c * a * c⁻¹ ∈ V := hc_mem a haV
  have hca_ne1 : c * a * c⁻¹ ≠ 1 := by
    intro h
    apply ha1
    calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
      _ = c⁻¹ * 1 * c := by rw [h]
      _ = 1 := by group
  have hca_mem : c * a * c⁻¹ ∈ ({1, a, b, a * b} : Set G) := by
    rw [← hVset]; exact hcaV
  rcases Set.mem_insert_iff.mp hca_mem with hca1 | hca_mem
  · exact absurd hca1 hca_ne1
  · rcases Set.mem_insert_iff.mp hca_mem with hca_a | hca_mem
    · -- conjugation by `c` fixes `a`, hence fixes all of `V`
      have hfix_b : c * b * c⁻¹ = b := by rw [hpsib, hca_a, hxa]
      have hfix_ab : c * (a * b) * c⁻¹ = a * b := by rw [hpsiab, hfix_b, hxb]
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hvmem : v ∈ ({1, a, b, a * b} : Set G) := by rw [← hVset]; exact hv
      have hfix : c * v * c⁻¹ = v := by
        rcases Set.mem_insert_iff.mp hvmem with hv1 | hvmem
        · rw [hv1]; group
        · rcases Set.mem_insert_iff.mp hvmem with hva | hvmem
          · rw [hva]; exact hca_a
          · rcases Set.mem_insert_iff.mp hvmem with hvb | hvmem
            · rw [hvb]; exact hfix_b
            · rw [Set.mem_singleton_iff.mp hvmem]; exact hfix_ab
      calc v * c = (c * v * c⁻¹) * c := by rw [hfix]
        _ = c * v := by group
    · rcases Set.mem_insert_iff.mp hca_mem with hca_b | hca_mem
      · -- conjugation by `c` sends `a` to `b`, forcing `c²` to move `a`: impossible
        exfalso
        have hpsib' : c * b * c⁻¹ = a * b := by rw [hpsib, hca_b, hxb]
        have h2 : c * (c * a * c⁻¹) * c⁻¹ = a * b := by rw [hca_b, hpsib']
        rw [hphi2] at h2
        exact hab_mul_a h2.symm
      · -- conjugation by `c` sends `a` to `a * b`, forcing `c²` to move `a`: impossible
        exfalso
        have hca_ab : c * a * c⁻¹ = a * b := Set.mem_singleton_iff.mp hca_mem
        have hpsib' : c * b * c⁻¹ = a := by rw [hpsib, hca_ab, hxab]
        have h2 : c * (c * a * c⁻¹) * c⁻¹ = b := by
          rw [hca_ab, hpsiab, hpsib', hxa]
        rw [hphi2] at h2
        exact hab h2

end Work.CORE3
