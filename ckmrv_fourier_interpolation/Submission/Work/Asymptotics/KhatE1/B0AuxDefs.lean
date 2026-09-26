import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.E4cube_cusp_second

/-!
# Auxiliary definitions and `O(q²)` atoms for the funnel bound on `B₀`

The `z⁰`-coefficient `B0 ℓ τ` of the funnel bracket satisfies
`Δ·B0 = NONPSI + (3456π)⁻¹·Ψ` (`Delta_mul_B0`).  Writing the `ψ`-part in terms of the
combination `S = 2ψ₂ + ψ₄ - 6Λ₀ + (192Λ₀ - 72)q` and the individual deviation
`P₂ = ψ₂ - 2Λ₀`, the cleared quantity `3456π·(Δ·B0)` splits as

`3456π·Δ·B0 = cuspC·V₁ + iτ·V₂ + V₃ + (b·S + (a - 2b)·P₂)`

with `a = 1152 E₁₄`, `b = 576 E₄³ - 373248 Δ` and the rational coefficients `V₁, V₂, V₃`
collected here, each of which is expressed through the six polynomial atoms

* `E₆E₄³ - 1 - 216q`,  `E₆Δ - q`,  `E₄Δ - q`,  `E₄⁴ - 1 - 960q`,
  `E₁₄ - 1 + 24q`,  `E₄³ - 1 - 720q`,

all of which are `O(q²)` at the cusp.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `a = 1152 E₁₄`, the coefficient of `ψ₂` in the `ψ`-part `Ψ/3456π`. -/
def B0a (τ : ℍ) : ℂ := 1152 * E14Fun τ

/-- `b = 576 E₄³ - 373248 Δ`, the coefficient of `ψ₄` in the `ψ`-part `Ψ/3456π`. -/
def B0b (τ : ℍ) : ℂ := 576 * E4Fun τ ^ 3 - 373248 * DeltaFun τ

/-- `V₁`, the coefficient of `cuspC` in `3456π·(Δ·B0)`. -/
def B0V1 (τ : ℍ) : ℂ :=
  3400704 * E4Fun τ * DeltaFun τ
    - 3456 * E4Fun τ ^ 4
    + 2 * (B0a τ + B0b τ) - 192 * B0b τ * qParamFun τ

/-- `V₂`, the coefficient of `iτ` in `3456π·(Δ·B0)`. -/
def B0V2 (τ : ℍ) : ℂ :=
  (Real.pi : ℂ) * (-3456 * E6Fun τ * (E4Fun τ ^ 3 - 240 * DeltaFun τ)
    + 2 * (B0a τ + B0b τ) - 192 * B0b τ * qParamFun τ)

/-- `V₃`, the `τ`-free, `cuspC`-free part of `3456π·(Δ·B0)`. -/
def B0V3 (τ : ℍ) : ℂ :=
  -41472 * E4Fun τ * DeltaFun τ + 72 * B0b τ * qParamFun τ

/-! ## The six atoms are `O(q²)` -/

/-- Atom `E₄³ - 1 - 720q`. -/
lemma B0at6_isBigOq : IsBigOq (fun τ : ℍ => E4Fun τ ^ 3 - 1 - 720 * qParamFun τ) 2 := by
  obtain ⟨C, hC, h⟩ := E4cube_cusp_second
  exact ⟨C, hC, fun τ hτ => h τ hτ⟩

/-- Atom `Δ - q`. -/
lemma B0at3_isBigOq : IsBigOq (fun τ : ℍ => DeltaFun τ - qParamFun τ) 2 := DeltaFun_isBigOq

/-- Atom `E₆E₄³ - 1 - 216q`. -/
lemma B0at1_isBigOq :
    IsBigOq (fun τ : ℍ => E6Fun τ * E4Fun τ ^ 3 - 1 - 216 * qParamFun τ) 2 := by
  have h6 := B0at6_isBigOq
  have hv : IsBigOq (fun τ : ℍ => E6Fun τ - 1 + 504 * qParamFun τ) 2 := E6Fun_isBigOq
  have hq2 : IsBigOq (fun τ : ℍ => qParamFun τ ^ 2) 2 := qParamFun_sq_isBigOq
  have hb1 : IsBigOq (fun τ : ℍ => 1 - 504 * qParamFun τ) 0 := by
    have h := isBigOq_one_add_const_mul_q (-504)
    refine h.congr (fun τ => by ring)
  have h1 : IsBigOq (fun τ : ℍ =>
      (1 - 504 * qParamFun τ) * (E4Fun τ ^ 3 - 1 - 720 * qParamFun τ)) 2 := hb1.mul h6
  have hb2 : IsBigOq (fun τ : ℍ =>
      1 + 720 * qParamFun τ + (E4Fun τ ^ 3 - 1 - 720 * qParamFun τ)) 0 := by
    have h1' : IsBigOq (fun τ : ℍ => 1 + 720 * qParamFun τ) 0 := by
      have h := isBigOq_one_add_const_mul_q (720)
      refine h.congr (fun τ => by ring)
    exact h1'.add (h6.mono (by norm_num : 0 ≤ 2))
  have h2 : IsBigOq (fun τ : ℍ => (E6Fun τ - 1 + 504 * qParamFun τ)
      * (1 + 720 * qParamFun τ + (E4Fun τ ^ 3 - 1 - 720 * qParamFun τ))) 2 := hv.mul hb2
  have hc : IsBigOq (fun τ : ℍ => -362880 * qParamFun τ ^ 2) 2 := hq2.const_mul (-362880)
  refine ((hc.add h1).add h2).congr (fun τ => ?_)
  ring

/-- Atom `E₆Δ - q`. -/
lemma B0at2_isBigOq : IsBigOq (fun τ : ℍ => E6Fun τ * DeltaFun τ - qParamFun τ) 2 := by
  have hd := B0at3_isBigOq
  have hv : IsBigOq (fun τ : ℍ => E6Fun τ - 1 + 504 * qParamFun τ) 2 := E6Fun_isBigOq
  have hq : IsBigOq (fun τ : ℍ => qParamFun τ) 1 := qParamFun_isBigOq
  have hq2 : IsBigOq (fun τ : ℍ => qParamFun τ ^ 2) 2 := qParamFun_sq_isBigOq
  have h1 : IsBigOq (fun τ : ℍ => -504 * (qParamFun τ * (DeltaFun τ - qParamFun τ))) 2 :=
    (hq.mul hd).const_mul (-504) |>.mono (by norm_num : 2 ≤ 3)
  have h2 : IsBigOq (fun τ : ℍ =>
      (E6Fun τ - 1 + 504 * qParamFun τ) * qParamFun τ) 2 :=
    (hv.mul hq).mono (by norm_num : 2 ≤ 3)
  have h3 : IsBigOq (fun τ : ℍ =>
      (E6Fun τ - 1 + 504 * qParamFun τ) * (DeltaFun τ - qParamFun τ)) 2 :=
    (hv.mul hd).mono (by norm_num : 2 ≤ 4)
  have h4 : IsBigOq (fun τ : ℍ => -504 * qParamFun τ ^ 2) 2 := hq2.const_mul (-504)
  refine (((h4.add hd).add h1).add (h2.add h3)).congr (fun τ => ?_)
  ring

/-- Atom `E₄Δ - q`. -/
lemma B0at3a_isBigOq : IsBigOq (fun τ : ℍ => E4Fun τ * DeltaFun τ - qParamFun τ) 2 := by
  have hd := B0at3_isBigOq
  have hu : IsBigOq (fun τ : ℍ => E4Fun τ - 1 - 240 * qParamFun τ) 2 := E4Fun_isBigOq
  have hq : IsBigOq (fun τ : ℍ => qParamFun τ) 1 := qParamFun_isBigOq
  have hq2 : IsBigOq (fun τ : ℍ => qParamFun τ ^ 2) 2 := qParamFun_sq_isBigOq
  have h1 : IsBigOq (fun τ : ℍ => 240 * (qParamFun τ * (DeltaFun τ - qParamFun τ))) 2 :=
    (hq.mul hd).const_mul (240) |>.mono (by norm_num : 2 ≤ 3)
  have h2 : IsBigOq (fun τ : ℍ =>
      (E4Fun τ - 1 - 240 * qParamFun τ) * qParamFun τ) 2 :=
    (hu.mul hq).mono (by norm_num : 2 ≤ 3)
  have h3 : IsBigOq (fun τ : ℍ =>
      (E4Fun τ - 1 - 240 * qParamFun τ) * (DeltaFun τ - qParamFun τ)) 2 :=
    (hu.mul hd).mono (by norm_num : 2 ≤ 4)
  have h4 : IsBigOq (fun τ : ℍ => 240 * qParamFun τ ^ 2) 2 := hq2.const_mul (240)
  refine (((h4.add hd).add h1).add (h2.add h3)).congr (fun τ => ?_)
  ring

/-- Atom `E₄⁴ - 1 - 960q`. -/
lemma B0at4_isBigOq : IsBigOq (fun τ : ℍ => E4Fun τ ^ 4 - 1 - 960 * qParamFun τ) 2 := by
  have hu : IsBigOq (fun τ : ℍ => E4Fun τ - 1 - 240 * qParamFun τ) 2 := E4Fun_isBigOq
  have hs : IsBigOq (fun τ : ℍ => E4Fun τ - 1) 1 := E4_minus_one
  have hs2 : IsBigOq (fun τ : ℍ => (E4Fun τ - 1) ^ 2) 2 :=
    (hs.mul hs).congr (fun τ => by ring)
  have hs3 : IsBigOq (fun τ : ℍ => (E4Fun τ - 1) ^ 3) 3 := by
    have h : IsBigOq (fun τ : ℍ => (E4Fun τ - 1) ^ 2 * (E4Fun τ - 1)) 3 := hs2.mul hs
    refine h.congr (fun τ => by ring)
  have hs4 : IsBigOq (fun τ : ℍ => (E4Fun τ - 1) ^ 4) 4 := by
    have h : IsBigOq (fun τ : ℍ => (E4Fun τ - 1) ^ 3 * (E4Fun τ - 1)) 4 := hs3.mul hs
    refine h.congr (fun τ => by ring)
  have h4u : IsBigOq (fun τ : ℍ => 4 * (E4Fun τ - 1 - 240 * qParamFun τ)) 2 := hu.const_mul 4
  have h6s2 : IsBigOq (fun τ : ℍ => 6 * (E4Fun τ - 1) ^ 2) 2 := hs2.const_mul 6
  have h4s3 : IsBigOq (fun τ : ℍ => 4 * (E4Fun τ - 1) ^ 3) 2 := hs3.const_mul 4 |>.mono (by norm_num)
  refine (((h4u.add h6s2).add h4s3).add (hs4.mono (by norm_num : 2 ≤ 4))).congr (fun τ => ?_)
  ring

/-- Atom `E₁₄ - 1 + 24q`. -/
lemma B0at5_isBigOq : IsBigOq (fun τ : ℍ => E14Fun τ - 1 + 24 * qParamFun τ) 2 := by
  have hu : IsBigOq (fun τ : ℍ => E4Fun τ - 1 - 240 * qParamFun τ) 2 := E4Fun_isBigOq
  have hv : IsBigOq (fun τ : ℍ => E6Fun τ - 1 + 504 * qParamFun τ) 2 := E6Fun_isBigOq
  have hs : IsBigOq (fun τ : ℍ => E4Fun τ - 1) 1 := E4_minus_one
  have ht : IsBigOq (fun τ : ℍ => E6Fun τ - 1) 1 := E6_minus_one
  have hs2 : IsBigOq (fun τ : ℍ => (E4Fun τ - 1) ^ 2) 2 :=
    (hs.mul hs).congr (fun τ => by ring)
  have h2st : IsBigOq (fun τ : ℍ => 2 * ((E4Fun τ - 1) * (E6Fun τ - 1))) 2 :=
    (hs.mul ht).const_mul 2
  have hs2t : IsBigOq (fun τ : ℍ => (E4Fun τ - 1) ^ 2 * (E6Fun τ - 1)) 3 := by
    have h : IsBigOq (fun τ : ℍ => (E4Fun τ - 1) ^ 2 * (E6Fun τ - 1)) (2 + 1) := hs2.mul ht
    simpa using h
  have h2u : IsBigOq (fun τ : ℍ => 2 * (E4Fun τ - 1 - 240 * qParamFun τ)) 2 := hu.const_mul 2
  refine (((h2u.add hv).add hs2).add (h2st.add (hs2t.mono (by norm_num : 2 ≤ 3)))).congr
    (fun τ => ?_)
  unfold E14Fun
  ring

/-! ## The coefficients `V₁, V₂, V₃`, `b`, `a - 2b` are `O(q^k)` -/

/-- `b = 576 E₄³ - 373248 Δ` is bounded near the cusp. -/
lemma B0b_isBigOq : IsBigOq B0b 0 := by
  have h6 := B0at6_isBigOq
  have h3 := B0at3_isBigOq
  have hconst : IsBigOq (fun _ : ℍ => (576 : ℂ)) 0 :=
    IsBigOq.bounded 576 (by norm_num) (fun _ _ => by simp)
  have hq : IsBigOq (fun τ : ℍ => (41472 : ℂ) * qParamFun τ) 0 :=
    qParamFun_isBigOq.const_mul (41472 : ℂ) |>.mono (by norm_num : 0 ≤ 1)
  refine ((hconst.add hq).add ((h6.const_mul 576).add (h3.const_mul (-373248)))).congr
    (fun τ => ?_)
  rw [B0b]
  ring

/-- `a - 2b = 1152 (E₁₄ - E₄³ + 648 Δ) = -110592 q + O(q²)`. -/
lemma B0a_sub_2B0b_isBigOq : IsBigOq (fun τ : ℍ => B0a τ - 2 * B0b τ) 1 := by
  have h5 := B0at5_isBigOq
  have h6 := B0at6_isBigOq
  have h3 := B0at3_isBigOq
  have hq : IsBigOq (fun τ : ℍ => qParamFun τ) 1 := qParamFun_isBigOq
  have hinner : IsBigOq (fun τ : ℍ => -96 * qParamFun τ
      + ((E14Fun τ - 1 + 24 * qParamFun τ) + -(E4Fun τ ^ 3 - 1 - 720 * qParamFun τ))
      + 648 * (DeltaFun τ - qParamFun τ)) 1 := by
    refine ((hq.const_mul (-96)).add ((h5.add h6.neg).add (h3.const_mul 648))).congr
      (fun τ => ?_)
    ring
  refine (hinner.const_mul (1152 : ℂ)).congr (fun τ => ?_)
  rw [B0a, B0b]
  ring

/-- `V₁ = O(q²)`. -/
lemma B0V1_isBigOq : IsBigOq B0V1 2 := by
  have h3a := B0at3a_isBigOq
  have h4 := B0at4_isBigOq
  have h5 := B0at5_isBigOq
  have h6 := B0at6_isBigOq
  have h3 := B0at3_isBigOq
  have h6q : IsBigOq (fun τ : ℍ => (E4Fun τ ^ 3 - 1 - 720 * qParamFun τ) * qParamFun τ) 2 :=
    (h6.mul qParamFun_isBigOq).mono (by norm_num : 2 ≤ 3)
  have h3q : IsBigOq (fun τ : ℍ => (DeltaFun τ - qParamFun τ) * qParamFun τ) 2 :=
    (h3.mul qParamFun_isBigOq).mono (by norm_num : 2 ≤ 3)
  have hq2 : IsBigOq (fun τ : ℍ => qParamFun τ ^ 2) 2 := qParamFun_sq_isBigOq
  have h := (((h3a.const_mul (3400704 : ℂ)).add (h4.const_mul (-3456 : ℂ))).add
      ((h5.const_mul (2304 : ℂ)).add (h6.const_mul (1152 : ℂ)))).add
      (((h3.const_mul (-746496 : ℂ)).add (h6q.const_mul (-110592 : ℂ))).add
        ((h3q.const_mul (71663616 : ℂ)).add (hq2.const_mul (-7962624 : ℂ))))
  refine h.congr (fun τ => ?_)
  rw [B0V1, B0a, B0b]
  ring

/-- `V₂ = O(q²)`. -/
lemma B0V2_isBigOq : IsBigOq B0V2 2 := by
  have h1 := B0at1_isBigOq
  have h2 := B0at2_isBigOq
  have h5 := B0at5_isBigOq
  have h6 := B0at6_isBigOq
  have h3 := B0at3_isBigOq
  have h6q : IsBigOq (fun τ : ℍ => (E4Fun τ ^ 3 - 1 - 720 * qParamFun τ) * qParamFun τ) 2 :=
    (h6.mul qParamFun_isBigOq).mono (by norm_num : 2 ≤ 3)
  have h3q : IsBigOq (fun τ : ℍ => (DeltaFun τ - qParamFun τ) * qParamFun τ) 2 :=
    (h3.mul qParamFun_isBigOq).mono (by norm_num : 2 ≤ 3)
  have hq2 : IsBigOq (fun τ : ℍ => qParamFun τ ^ 2) 2 := qParamFun_sq_isBigOq
  have hinner : IsBigOq (fun τ : ℍ =>
      (-3456 : ℂ) * (E6Fun τ * E4Fun τ ^ 3 - 1 - 216 * qParamFun τ)
      + (829440 : ℂ) * (E6Fun τ * DeltaFun τ - qParamFun τ)
      + ((2304 : ℂ) * (E14Fun τ - 1 + 24 * qParamFun τ)
        + (1152 : ℂ) * (E4Fun τ ^ 3 - 1 - 720 * qParamFun τ))
      + ((-746496 : ℂ) * (DeltaFun τ - qParamFun τ)
        + (-110592 : ℂ) * ((E4Fun τ ^ 3 - 1 - 720 * qParamFun τ) * qParamFun τ))
      + ((71663616 : ℂ) * ((DeltaFun τ - qParamFun τ) * qParamFun τ)
        + (-7962624 : ℂ) * qParamFun τ ^ 2)) 2 :=
    (h1.const_mul (-3456)).add (h2.const_mul 829440)
      |>.add ((h5.const_mul 2304).add (h6.const_mul 1152))
      |>.add ((h3.const_mul (-746496)).add (h6q.const_mul (-110592)))
      |>.add ((h3q.const_mul 71663616).add (hq2.const_mul (-7962624)))
  refine (hinner.const_mul (Real.pi : ℂ)).congr (fun τ => ?_)
  rw [B0V2, B0a, B0b]
  ring

/-- `V₃ = O(q²)`. -/
lemma B0V3_isBigOq : IsBigOq B0V3 2 := by
  have h3a := B0at3a_isBigOq
  have h6 := B0at6_isBigOq
  have h3 := B0at3_isBigOq
  have h6q : IsBigOq (fun τ : ℍ => (E4Fun τ ^ 3 - 1 - 720 * qParamFun τ) * qParamFun τ) 2 :=
    (h6.mul qParamFun_isBigOq).mono (by norm_num : 2 ≤ 3)
  have h3q : IsBigOq (fun τ : ℍ => (DeltaFun τ - qParamFun τ) * qParamFun τ) 2 :=
    (h3.mul qParamFun_isBigOq).mono (by norm_num : 2 ≤ 3)
  have hq2 : IsBigOq (fun τ : ℍ => qParamFun τ ^ 2) 2 := qParamFun_sq_isBigOq
  have h := ((h3a.const_mul (-41472 : ℂ)).add (hq2.const_mul (2985984 : ℂ))).add
      ((h6q.const_mul (41472 : ℂ)).add (h3q.const_mul (-26873856 : ℂ)))
  refine h.congr (fun τ => ?_)
  rw [B0V3, B0b]
  ring

end

end Work.Asymptotics.KhatE1
