import Mathlib
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.Coherence
import Submission.Work.Coherence.norm_one_of_mem_zSpan
import Submission.Work.Coherence.irr_degree_pos

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.CharQ.prodChar_mem_Irr`

The product `prodChar h lam theta` of an irreducible character `lam` of `S` and an irreducible
character `theta` of `Q₁`, viewed as a character of `Q ≅ S × Q₁`, is again irreducible.

The construction is the (external) tensor product of the underlying representations: the
representation `tensorRep h V W` of `Q ≅ S × Q₁` on `V ⊗ W` sends `q` with `prodIso.symm q = (a,b)`
to `V.ρ a ⊗ W.ρ b`.  Its character is `prodChar lam theta` (`tensorRep_character`), so
`prodChar lam theta` is a genuine character (`IsChar`, hence `IsVChar`).  Its norm is computed by
factoring the sum over `Q ≅ S × Q₁`:

`⟪prodChar, prodChar⟫ = [(1/|S|) ∑_a lam a * conj (lam a)] · [(1/|Q₁|) ∑_b theta b * conj (theta b)]
 = ⟪lam,lam⟫ · ⟪theta,theta⟫ = 1`.

A virtual character of norm one is `±` an irreducible one (`Work.Coherence.norm_one_of_mem_zSpan`),
and the minus sign is impossible because `prodChar lam theta 1 = lam 1 * theta 1 > 0` while
`-χ 1 < 0` for `χ ∈ Irr Q` (`Work.Coherence.irr_degree_pos`).
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.FeitSibley.CharQ

variable {G : Type} [Group G] [Fintype G]

/-- The representation of `Q ≅ S × Q₁` on the tensor product `V ⊗ W` of a representation `V` of
`S` and a representation `W` of `Q₁`: the element `q` with `prodIso.symm q = (a, b)` acts as
`V.ρ a ⊗ W.ρ b`. -/
noncomputable def tensorRep (h : Work.FeitSibley.FSData G) (V : FDRep ℂ ↥h.S)
    (W : FDRep ℂ ↥h.Q1) :
    Representation ℂ ↥h.Q (TensorProduct ℂ V W) where
  toFun q := TensorProduct.map (V.ρ (h.prodIso.symm q).1) (W.ρ (h.prodIso.symm q).2)
  map_one' := by
    have h1 : h.prodIso.symm (1 : ↥h.Q) = 1 := map_one _
    simp only [h1, Prod.fst_one, Prod.snd_one, map_one, TensorProduct.map_one]
  map_mul' q q' := by
    have h1 : h.prodIso.symm (q * q') = h.prodIso.symm q * h.prodIso.symm q' := map_mul _ q q'
    rw [h1, Prod.fst_mul, Prod.snd_mul, map_mul, map_mul, TensorProduct.map_mul]

/-- The character of `tensorRep h V W` is `prodChar h V.character W.character`. -/
theorem tensorRep_character (h : Work.FeitSibley.FSData G) (V : FDRep ℂ ↥h.S)
    (W : FDRep ℂ ↥h.Q1) {lam : ↥h.S → ℂ} {theta : ↥h.Q1 → ℂ}
    (hV : V.character = lam) (hW : W.character = theta) :
    (tensorRep h V W).character = h.prodChar lam theta := by
  funext q
  rw [← MulEquiv.apply_symm_apply h.prodIso q]
  have h1 : (tensorRep h V W) (h.prodIso (h.prodIso.symm q)) =
      TensorProduct.map (V.ρ (h.prodIso.symm q).1) (W.ρ (h.prodIso.symm q).2) := by
    show TensorProduct.map (V.ρ (h.prodIso.symm (h.prodIso (h.prodIso.symm q))).1)
      (W.ρ (h.prodIso.symm (h.prodIso (h.prodIso.symm q))).2) = _
    rw [MulEquiv.symm_apply_apply]
  rw [Representation.character, h1, LinearMap.trace_tensorProduct', h.prodChar_apply,
    ← hV, ← hW]
  simp only [FDRep.character]

/-- The self-inner-product of `prodChar h lam theta` is `1` for irreducible `lam`, `theta`. -/
theorem cfInner_prodChar_self (h : Work.FeitSibley.FSData G) {lam : ↥h.S → ℂ}
    {theta : ↥h.Q1 → ℂ} (hl : lam ∈ Work.CharCore.Irr ↥h.S)
    (ht : theta ∈ Work.CharCore.Irr ↥h.Q1) :
    Work.CharCore.cfInner (h.prodChar lam theta) (h.prodChar lam theta) = 1 := by
  have hfacS : (∑ a : ↥h.S, lam a * starRingEnd ℂ (lam a)) = (Fintype.card ↥h.S : ℂ) := by
    have h1 : Work.CharCore.cfInner lam lam = 1 := by
      rw [Work.CharCore.irr_orthonormal lam lam hl hl]; simp
    rw [Work.CharCore.cfInner] at h1
    have hc : (Fintype.card ↥h.S : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
    calc (∑ a : ↥h.S, lam a * starRingEnd ℂ (lam a))
        = 1 * ∑ a : ↥h.S, lam a * starRingEnd ℂ (lam a) := by rw [one_mul]
      _ = ((Fintype.card ↥h.S : ℂ) * (Fintype.card ↥h.S : ℂ)⁻¹) *
            ∑ a : ↥h.S, lam a * starRingEnd ℂ (lam a) := by rw [mul_inv_cancel₀ hc]
      _ = (Fintype.card ↥h.S : ℂ) * ((Fintype.card ↥h.S : ℂ)⁻¹ *
            ∑ a : ↥h.S, lam a * starRingEnd ℂ (lam a)) := by rw [mul_assoc]
      _ = (Fintype.card ↥h.S : ℂ) * 1 := by rw [h1]
      _ = (Fintype.card ↥h.S : ℂ) := by rw [mul_one]
  have hfacT : (∑ b : ↥h.Q1, theta b * starRingEnd ℂ (theta b)) = (Fintype.card ↥h.Q1 : ℂ) := by
    have h1 : Work.CharCore.cfInner theta theta = 1 := by
      rw [Work.CharCore.irr_orthonormal theta theta ht ht]; simp
    rw [Work.CharCore.cfInner] at h1
    have hc : (Fintype.card ↥h.Q1 : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
    calc (∑ b : ↥h.Q1, theta b * starRingEnd ℂ (theta b))
        = 1 * ∑ b : ↥h.Q1, theta b * starRingEnd ℂ (theta b) := by rw [one_mul]
      _ = ((Fintype.card ↥h.Q1 : ℂ) * (Fintype.card ↥h.Q1 : ℂ)⁻¹) *
            ∑ b : ↥h.Q1, theta b * starRingEnd ℂ (theta b) := by rw [mul_inv_cancel₀ hc]
      _ = (Fintype.card ↥h.Q1 : ℂ) * ((Fintype.card ↥h.Q1 : ℂ)⁻¹ *
            ∑ b : ↥h.Q1, theta b * starRingEnd ℂ (theta b)) := by rw [mul_assoc]
      _ = (Fintype.card ↥h.Q1 : ℂ) * 1 := by rw [h1]
      _ = (Fintype.card ↥h.Q1 : ℂ) := by rw [mul_one]
  rw [Work.CharCore.cfInner]
  have hsum : (∑ q : ↥h.Q, (h.prodChar lam theta) q * starRingEnd ℂ ((h.prodChar lam theta) q))
      = (Fintype.card ↥h.S : ℂ) * (Fintype.card ↥h.Q1 : ℂ) := by
    rw [Fintype.sum_equiv h.prodIso.symm.toEquiv
      (fun q : ↥h.Q => (h.prodChar lam theta) q * starRingEnd ℂ ((h.prodChar lam theta) q))
      (fun x : ↥h.S × ↥h.Q1 => (h.prodChar lam theta) (h.prodIso x) *
        starRingEnd ℂ ((h.prodChar lam theta) (h.prodIso x)))
      (fun q => by simp [MulEquiv.apply_symm_apply])]
    rw [Fintype.sum_prod_type]
    have hterm : ∀ a b, (h.prodChar lam theta) (h.prodIso (a, b)) *
        starRingEnd ℂ ((h.prodChar lam theta) (h.prodIso (a, b)))
        = (lam a * starRingEnd ℂ (lam a)) * (theta b * starRingEnd ℂ (theta b)) := by
      intro a b
      rw [h.prodChar_apply, map_mul]
      ring
    simp only [hterm]
    rw [← Finset.sum_mul_sum Finset.univ Finset.univ
      (fun a : ↥h.S => lam a * starRingEnd ℂ (lam a))
      (fun b : ↥h.Q1 => theta b * starRingEnd ℂ (theta b))]
    rw [hfacS, hfacT]
  have hcard : (Fintype.card ↥h.Q : ℂ) = (Fintype.card ↥h.S : ℂ) * (Fintype.card ↥h.Q1 : ℂ) := by
    rw [← Fintype.card_congr h.prodIso.toEquiv, Fintype.card_prod]
    push_cast
    rfl
  rw [hsum, hcard]
  have hne : (Fintype.card ↥h.S : ℂ) * (Fintype.card ↥h.Q1 : ℂ) ≠ 0 := by
    rw [← hcard]; simp [Fintype.card_ne_zero]
  rw [inv_mul_cancel₀ hne]

theorem prodChar_mem_Irr {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {lam : ↥h.S → ℂ} {theta : ↥h.Q1 → ℂ}
    (hl : lam ∈ Work.CharCore.Irr ↥h.S) (ht : theta ∈ Work.CharCore.Irr ↥h.Q1) :
    h.prodChar lam theta ∈ Work.CharCore.Irr ↥h.Q := by
  obtain ⟨V, -, hV⟩ := (Work.CharCore.mem_Irr_iff_fdrep lam).mp hl
  obtain ⟨W, -, hW⟩ := (Work.CharCore.mem_Irr_iff_fdrep theta).mp ht
  -- `prodChar lam theta` is a genuine character
  have hischar : Work.CharCore.IsChar (h.prodChar lam theta) := by
    rw [← tensorRep_character h V W hV hW]
    exact Work.CharCore.isChar_character (tensorRep h V W)
  have hisv : Work.CharCore.IsVChar (h.prodChar lam theta) := hischar.toVChar
  have hz : h.prodChar lam theta ∈ Work.Coherence.ZSpan (Work.CharCore.Irr ↥h.Q) :=
    (Work.CharCore.IsVChar_iff_mem_zSpan_Irr _).mp hisv
  have hnorm : Work.Coherence.cfInner (h.prodChar lam theta) (h.prodChar lam theta) = 1 := by
    simpa only [Work.CharCore.cfInner_coherence] using cfInner_prodChar_self h hl ht
  -- a virtual character of norm one is `±` an irreducible one
  obtain ⟨χ, hχ, hcase⟩ :=
    Work.Coherence.norm_one_of_mem_zSpan Work.CharCore.Orthonormal_Irr hz hnorm
  rcases hcase with hf | hf
  · rw [hf]; exact hχ
  · -- the minus sign is impossible: degrees are positive
    exfalso
    obtain ⟨m, hmpos, hm⟩ := Work.Coherence.irr_degree_pos ((Work.CharCore.mem_Irr_iff_coherence).mp hl)
    obtain ⟨nn, hnpos, hnn⟩ := Work.Coherence.irr_degree_pos ((Work.CharCore.mem_Irr_iff_coherence).mp ht)
    obtain ⟨k, hkpos, hk⟩ := Work.Coherence.irr_degree_pos ((Work.CharCore.mem_Irr_iff_coherence).mp hχ)
    have hfl : (h.prodChar lam theta) 1 = ((m : ℂ) * (nn : ℂ)) := by
      rw [h.prodChar_one, hm, hnn]
    have hcong := congrFun hf 1
    rw [Pi.neg_apply, hfl, hk] at hcong
    have hzero : ((m : ℂ) * (nn : ℂ) + (k : ℂ)) = 0 := by
      rw [eq_neg_iff_add_eq_zero] at hcong; exact hcong
    have hnat : (m * nn + k : ℕ) = 0 := by
      have hcast : ((m * nn + k : ℕ) : ℂ) = 0 := by push_cast; exact hzero
      exact_mod_cast hcast
    omega

end Work.FeitSibley.CharQ
