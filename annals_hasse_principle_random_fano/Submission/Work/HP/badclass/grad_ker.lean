import Mathlib
import Submission.Work.HP.badclass.BadDefs

set_option autoImplicit false
noncomputable section

open MvPolynomial Finset

namespace Work.HP.badclass

/-- For `x` in the torus and `p ∤ d` the gradient map `a ↦ ∇f_a(x)` has rank `n+1`, hence its
kernel has `p^{N-(n+1)}` elements. -/
theorem grad_ker (d n p : ℕ) (hp : p.Prime) (hd : 1 ≤ d) (hpd : ¬ p ∣ d)
    (x : Fin (n + 1) → ZMod p) (hx : ∀ i, x i ≠ 0) :
    ({a : Work.HP.Mon d n → ZMod p | ∀ i, Work.HP.gradZ d n p a i x = 0} :
        Set (Work.HP.Mon d n → ZMod p)).ncard = p ^ (Work.HP.NN d n - (n + 1)) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (ZMod p) p := ZMod.charP p
  set G : (Work.HP.Mon d n → ZMod p) →ₗ[ZMod p] (Fin (n + 1) → ZMod p) :=
    LinearMap.pi (fun i : Fin (n + 1) => Fintype.linearCombination (ZMod p)
      (fun m : Work.HP.Mon d n => (m.1 i : ZMod p) *
        ∏ j : Fin (n + 1), x j ^ ((m.1 j : ℕ) - if j = i then 1 else 0))) with hG
  have hGapp : ∀ a i, G a i = Work.HP.gradZ d n p a i x := by
    intro a i
    rw [hG, LinearMap.pi_apply, Fintype.linearCombination_apply]
    simp only [smul_eq_mul, Work.HP.gradZ]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have hmid_ne : ∀ j i : Fin (n + 1), i ≠ j → ((Work.HP.monE d n j).1 i : ZMod p) = 0 := by
    intro j i hij
    rw [Work.HP.monE_ne d n j i hij]
    simp
  have hprod_self : ∀ j : Fin (n + 1),
      (∏ k : Fin (n + 1), x k ^ (((Work.HP.monE d n j).1 k : ℕ) - if k = j then 1 else 0))
        = x j ^ (d - 1) := by
    intro j
    rw [Finset.prod_eq_single j
      (f := fun k : Fin (n + 1) =>
        x k ^ (((Work.HP.monE d n j).1 k : ℕ) - if k = j then 1 else 0))
      (fun k _ hkj => by rw [Work.HP.monE_ne d n j k hkj]; simp)
      (fun hj => absurd (Finset.mem_univ j) hj)]
    rw [Work.HP.monE_self]
    simp
  have hprod_ne : ∀ j i : Fin (n + 1), i ≠ j →
      (∏ k : Fin (n + 1), x k ^ (((Work.HP.monE d n j).1 k : ℕ) - if k = i then 1 else 0))
        = x j ^ d := by
    intro j i hij
    rw [Finset.prod_eq_single j
      (f := fun k : Fin (n + 1) =>
        x k ^ (((Work.HP.monE d n j).1 k : ℕ) - if k = i then 1 else 0))
      (fun k _ hkj => by rw [Work.HP.monE_ne d n j k hkj]; simp)
      (fun hj => absurd (Finset.mem_univ j) hj)]
    rw [Work.HP.monE_self]
    simp [show ¬ (j = i) from fun h => hij h.symm]
  have hside : ∀ j i : Fin (n + 1), ∀ b ∈ (Finset.univ : Finset (Work.HP.Mon d n)),
      b ≠ Work.HP.monE d n j →
      (Pi.single (Work.HP.monE d n j)
          (((d : ZMod p) * x j ^ (d - 1))⁻¹) : Work.HP.Mon d n → ZMod p) b *
        (b.1 i : ZMod p) * ∏ k : Fin (n + 1),
          x k ^ ((b.1 k : ℕ) - if k = i then 1 else 0) = 0 := by
    intro j i b _ hb
    rw [Pi.single_eq_of_ne (show b ≠ Work.HP.monE d n j from hb), zero_mul, zero_mul]
  have hdirac_j : ∀ j : Fin (n + 1),
      G (Pi.single (Work.HP.monE d n j) (((d : ZMod p) * x j ^ (d - 1))⁻¹)) j = 1 := by
    intro j
    rw [hGapp, Work.HP.gradZ,
      Finset.sum_eq_single (Work.HP.monE d n j)
        (f := fun m : Work.HP.Mon d n =>
          (Pi.single (Work.HP.monE d n j)
            (((d : ZMod p) * x j ^ (d - 1))⁻¹) : Work.HP.Mon d n → ZMod p) m *
          (m.1 j : ZMod p) * ∏ k : Fin (n + 1),
            x k ^ ((m.1 k : ℕ) - if k = j then 1 else 0))
        (hside j j) (fun hm => absurd (Finset.mem_univ _) hm)]
    rw [Pi.single_eq_same, hprod_self j, Work.HP.monE_self]
    have hne : (d : ZMod p) * x j ^ (d - 1) ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ (hx j))
      intro h0
      exact hpd ((CharP.cast_eq_zero_iff (ZMod p) p d).mp h0)
    rw [mul_assoc, inv_mul_cancel₀ hne]
  have hdirac_ij : ∀ j i : Fin (n + 1), i ≠ j →
      G (Pi.single (Work.HP.monE d n j) (((d : ZMod p) * x j ^ (d - 1))⁻¹)) i = 0 := by
    intro j i hij
    rw [hGapp, Work.HP.gradZ,
      Finset.sum_eq_single (Work.HP.monE d n j)
        (f := fun m : Work.HP.Mon d n =>
          (Pi.single (Work.HP.monE d n j)
            (((d : ZMod p) * x j ^ (d - 1))⁻¹) : Work.HP.Mon d n → ZMod p) m *
          (m.1 i : ZMod p) * ∏ k : Fin (n + 1),
            x k ^ ((m.1 k : ℕ) - if k = i then 1 else 0))
        (hside j i) (fun hm => absurd (Finset.mem_univ _) hm)]
    rw [Pi.single_eq_same, hmid_ne j i hij, hprod_ne j i hij]
    ring
  have hsurj : Function.Surjective G := by
    intro c
    refine ⟨∑ j : Fin (n + 1), c j • Pi.single (Work.HP.monE d n j)
        (((d : ZMod p) * x j ^ (d - 1))⁻¹), ?_⟩
    ext i
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i
      (f := fun j : Fin (n + 1) => c j *
        (G (Pi.single (Work.HP.monE d n j) (((d : ZMod p) * x j ^ (d - 1))⁻¹)) i))
      (fun b _ hbi => by rw [hdirac_ij b i (fun h => hbi h.symm), mul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [hdirac_j i, mul_one]
  have hkerNat : Nat.card ↥(LinearMap.ker G) = p ^ (Work.HP.NN d n - (n + 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := ↥(LinearMap.ker G)), Nat.card_zmod]
    congr 1
    have h1 := LinearMap.finrank_range_add_finrank_ker G
    have h2 : Module.finrank (ZMod p) ↥(LinearMap.range G) = n + 1 := by
      rw [LinearMap.range_eq_top.mpr hsurj]
      have h3 : Module.finrank (ZMod p)
          ↥(⊤ : Submodule (ZMod p) (Fin (n + 1) → ZMod p))
          = Module.finrank (ZMod p) (Fin (n + 1) → ZMod p) :=
        (Submodule.eq_top_iff_finrank_eq (W := ⊤)).mp rfl
      rw [h3, Module.finrank_fintype_fun_eq_card]
      simp
    have h4 : Module.finrank (ZMod p) (Work.HP.Mon d n → ZMod p) = Work.HP.NN d n :=
      Module.finrank_fintype_fun_eq_card (ZMod p)
    omega
  have hset : ({a : Work.HP.Mon d n → ZMod p | ∀ i, Work.HP.gradZ d n p a i x = 0} :
      Set (Work.HP.Mon d n → ZMod p)) = (G.ker : Set (Work.HP.Mon d n → ZMod p)) := by
    ext a
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_ker]
    constructor
    · intro h
      funext i
      rw [hGapp a i]
      exact h i
    · intro h i
      rw [← hGapp a i]
      simpa using congrFun h i
  rw [hset, Work.HP.ncard_coe_submodule, hkerNat]

end Work.HP.badclass
