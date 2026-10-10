import Mathlib
import Submission.Work.MotK.TGen.RadSatDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `(zA, zg) : zC = (zA, zC)`

The chart ideal of the T-census plane model contains

* `zA = b³h·X₁ − a³h·X₂²`  (the elimination coefficient `A₁`, linear in `X₁`),
* `zC = a²b − ab²h·X₁²X₂`  (the numerator `C₁`),
* `zg = ZElim2(x₁,x₂)`  (the plane eliminant),

and the quadratic certificate `zElim_quad_id` reads

`zAl·zC² + zBet·zC·zA + zGam·zA² = C(b⁴h)·zg`   (`zAl = a²b⁴h`),

so that, `b⁴h` being a unit, `(zA, zg) = (zA, zC²)`.  Since `zA` is linear in `X₁` with unit
coefficient, the quotient `K[X₀,X₁,X₂]/(zA) ≅ K[X₀,X₂]` is a domain and the image of `zC` in it is
`a²b − (a⁷h/b⁴)X₂⁵ ≠ 0`; hence `zC` is a non-zero-divisor modulo `(zA)`.

Consequently `B·zC ∈ (zA, zg) = (zA, zC²)` forces `B − zC·r ∈ (zA)`, i.e. `B ∈ (zA, zC)`: this is
`starLem`.

## Main declarations

* `psiT` : the substitution `X₀ ↦ X₀`, `X₁ ↦ c·X₁²`, `X₂ ↦ X₁`; for `c·b³ = a³` it kills `zA` and
  computes in the domain `K[X₀,X₁]`.
* `sigT` : the section `X₀ ↦ X₀`, `X₁ ↦ X₂` of `psiT` modulo `(zA)`.
* `sub_sigT_psiT_mem` : `x − sigT (psiT x) ∈ (zA)` for every `x` (division by `zA`).
* `zC_saturation_aux` : `u·zC ∈ (zA) → u ∈ (zA)`.
* `starLem` : the target.
-/

set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

/-- The substitution `X₀ ↦ X₀`, `X₁ ↦ c·X₁²`, `X₂ ↦ X₁`, from `K[X₀,X₁,X₂]` to `K[X₀,X₁]`.
For `c·b³ = a³` it kills `zA`. -/
noncomputable def psiT (K : Type) [Field K] (c : K) :
    MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.C c * (MvPolynomial.X 1) ^ 2,
    MvPolynomial.X 1]

/-- The inclusion `K[X₀,X₁] → K[X₀,X₁,X₂]`, `X₀ ↦ X₀`, `X₁ ↦ X₂`. -/
noncomputable def sigT (K : Type) [CommSemiring K] :
    MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 3) K :=
  MvPolynomial.rename ![(0 : Fin 3), (2 : Fin 3)]

lemma psiT_C (K : Type) [Field K] (c r : K) :
    psiT K c (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [psiT]

lemma psiT_X0 (K : Type) [Field K] (c : K) :
    psiT K c (MvPolynomial.X (0 : Fin 3)) = MvPolynomial.X (0 : Fin 2) := by
  simp [psiT]

lemma psiT_X1 (K : Type) [Field K] (c : K) :
    psiT K c (MvPolynomial.X (1 : Fin 3))
      = MvPolynomial.C c * (MvPolynomial.X (1 : Fin 2)) ^ 2 := by
  simp [psiT]

lemma psiT_X2 (K : Type) [Field K] (c : K) :
    psiT K c (MvPolynomial.X (2 : Fin 3)) = MvPolynomial.X (1 : Fin 2) := by
  simp [psiT]

lemma sigT_C (K : Type) [CommSemiring K] (r : K) :
    sigT K (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [sigT]

lemma sigT_X0 (K : Type) [CommSemiring K] :
    sigT K (MvPolynomial.X (0 : Fin 2)) = MvPolynomial.X (0 : Fin 3) := by
  simp [sigT, MvPolynomial.rename_X]

lemma sigT_X1 (K : Type) [CommSemiring K] :
    sigT K (MvPolynomial.X (1 : Fin 2)) = MvPolynomial.X (2 : Fin 3) := by
  simp [sigT, MvPolynomial.rename_X]

lemma psiT_mul (K : Type) [Field K] (c : K) (p q : MvPolynomial (Fin 3) K) :
    psiT K c (p * q) = psiT K c p * psiT K c q := map_mul _ _ _

lemma psiT_sub (K : Type) [Field K] (c : K) (p q : MvPolynomial (Fin 3) K) :
    psiT K c (p - q) = psiT K c p - psiT K c q := map_sub _ _ _

lemma psiT_pow (K : Type) [Field K] (c : K) (p : MvPolynomial (Fin 3) K) (n : ℕ) :
    psiT K c (p ^ n) = (psiT K c p) ^ n := map_pow _ _ _

/-- For `c·b³ = a³` the substitution `psiT` kills the elimination coefficient `zA`. -/
lemma psiT_zA (K : Type) [Field K] (a b h c : K) (hc : c * b ^ 3 = a ^ 3) :
    psiT K c (zA K a b h) = 0 := by
  have hcoe : (MvPolynomial.C (b ^ 3 * h) * MvPolynomial.C c : MvPolynomial (Fin 2) K)
      = MvPolynomial.C (a ^ 3 * h) := by
    rw [← MvPolynomial.C_mul]
    congr 1
    rw [show b ^ 3 * h * c = (c * b ^ 3) * h by ring, hc]
  rw [zA, psiT_sub, psiT_mul, psiT_mul, psiT_C, psiT_X1, psiT_C, psiT_pow, psiT_X2]
  rw [show (MvPolynomial.C (b ^ 3 * h)
          * (MvPolynomial.C c * (MvPolynomial.X (1 : Fin 2)) ^ 2)
        : MvPolynomial (Fin 2) K)
      = (MvPolynomial.C (b ^ 3 * h) * MvPolynomial.C c)
          * (MvPolynomial.X (1 : Fin 2)) ^ 2 from by ring,
    hcoe, sub_self]

/-- The image of `zC` under `psiT`. -/
lemma psiT_zC (K : Type) [Field K] (a b h c : K) :
    psiT K c (zC K a b h) = MvPolynomial.C (a ^ 2 * b)
      - MvPolynomial.C (a * b ^ 2 * h) * MvPolynomial.C c ^ 2
        * (MvPolynomial.X (1 : Fin 2)) ^ 5 := by
  rw [zC]
  simp only [map_sub, map_mul, map_pow, psiT_C, psiT_X1, psiT_X2]
  first | refl_ring1 | ring

/-- `zC` is not a zero divisor modulo `zA`: its image under `psiT` has constant coefficient
`a²b ≠ 0`. -/
lemma psiT_zC_ne_zero (K : Type) [Field K] (a b h c : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    psiT K c (zC K a b h) ≠ 0 := by
  have hcc : MvPolynomial.constantCoeff (psiT K c (zC K a b h)) = a ^ 2 * b := by
    rw [psiT_zC K a b h c]
    simp [map_sub, map_mul, map_pow, MvPolynomial.constantCoeff_C, MvPolynomial.constantCoeff_X]
  intro hz
  rw [hz, map_zero] at hcc
  exact mul_ne_zero (pow_ne_zero 2 ha) hb hcc.symm

/-- **The division by `zA`.**  For `c·b³ = a³` the composite `sigT ∘ psiT` is a projection of
`K[X₀,X₁,X₂]` onto a complement of the principal ideal `(zA)`: the defect
`x − sigT (psiT x)` is always divisible by `zA`. -/
lemma sub_sigT_psiT_mem (K : Type) [Field K] (a b h c : K) (hb : b ≠ 0)
    (hh : h ≠ 0) (hc : c * b ^ 3 = a ^ 3) (x : MvPolynomial (Fin 3) K) :
    x - sigT K (psiT K c x)
      ∈ Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K)) := by
  have hb3h : b ^ 3 * h ≠ 0 := mul_ne_zero (pow_ne_zero 3 hb) hh
  have hbase1 : MvPolynomial.X (1 : Fin 3) - sigT K (psiT K c (MvPolynomial.X (1 : Fin 3)))
      ∈ Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K)) := by
    have hsig : sigT K (psiT K c (MvPolynomial.X (1 : Fin 3)))
        = MvPolynomial.C c * (MvPolynomial.X (2 : Fin 3)) ^ 2 := by
      rw [psiT_X1, map_mul, map_pow, sigT_C, sigT_X1]
    have hcoe1 : (MvPolynomial.C (b ^ 3 * h) * MvPolynomial.C ((b ^ 3 * h)⁻¹)
        : MvPolynomial (Fin 3) K) = 1 := by
      rw [← MvPolynomial.C_mul, mul_inv_cancel₀ hb3h, MvPolynomial.C_1]
    have hcoe2 : (b ^ 3 * h)⁻¹ * (a ^ 3 * h) = c := by
      have hc' : c * (b ^ 3 * h) = a ^ 3 * h := by
        rw [show c * (b ^ 3 * h) = (c * b ^ 3) * h by ring, hc]
      rw [← hc']
      calc (b ^ 3 * h)⁻¹ * (c * (b ^ 3 * h)) = c * ((b ^ 3 * h)⁻¹ * (b ^ 3 * h)) := by ring
        _ = c * 1 := by rw [inv_mul_cancel₀ hb3h]
        _ = c := by rw [mul_one]
    have hcoe2' : (MvPolynomial.C (a ^ 3 * h) * MvPolynomial.C ((b ^ 3 * h)⁻¹)
        : MvPolynomial (Fin 3) K) = MvPolynomial.C c := by
      rw [← MvPolynomial.C_mul, mul_comm (a ^ 3 * h) ((b ^ 3 * h)⁻¹), hcoe2]
    refine Ideal.mem_span_singleton.mpr ⟨MvPolynomial.C ((b ^ 3 * h)⁻¹), ?_⟩
    rw [hsig]
    symm
    calc zA K a b h * MvPolynomial.C ((b ^ 3 * h)⁻¹)
        = (MvPolynomial.C (b ^ 3 * h) * MvPolynomial.X 1
            - MvPolynomial.C (a ^ 3 * h) * (MvPolynomial.X 2) ^ 2)
          * MvPolynomial.C ((b ^ 3 * h)⁻¹) := by rw [zA]
      _ = MvPolynomial.C (b ^ 3 * h) * MvPolynomial.C ((b ^ 3 * h)⁻¹) * MvPolynomial.X 1
            - MvPolynomial.C (a ^ 3 * h) * MvPolynomial.C ((b ^ 3 * h)⁻¹)
              * (MvPolynomial.X 2) ^ 2 := by rw [sub_mul]; ring
      _ = MvPolynomial.X 1 - MvPolynomial.C c * (MvPolynomial.X 2) ^ 2 := by
            rw [hcoe1, hcoe2', one_mul]
  have hbase0 : MvPolynomial.X (0 : Fin 3)
      - sigT K (psiT K c (MvPolynomial.X (0 : Fin 3))) = 0 := by
    rw [psiT_X0, sigT_X0, sub_self]
  have hbase2 : MvPolynomial.X (2 : Fin 3)
      - sigT K (psiT K c (MvPolynomial.X (2 : Fin 3))) = 0 := by
    rw [psiT_X2, sigT_X1, sub_self]
  induction x using MvPolynomial.induction_on with
  | C r =>
      rw [psiT_C, sigT_C, sub_self]
      exact Ideal.zero_mem _
  | add p q hp hq =>
      have hsplit : (p + q) - sigT K (psiT K c (p + q))
          = (p - sigT K (psiT K c p)) + (q - sigT K (psiT K c q)) := by
        simp only [map_add]
        first | refl_ring1 | ring
      rw [hsplit]
      exact Ideal.add_mem _ hp hq
  | mul_X p n hp =>
      have hsplit : p * MvPolynomial.X n - sigT K (psiT K c (p * MvPolynomial.X n))
          = MvPolynomial.X n * (p - sigT K (psiT K c p))
            + sigT K (psiT K c p)
              * (MvPolynomial.X n - sigT K (psiT K c (MvPolynomial.X n))) := by
        simp only [map_mul]
        first | refl_ring1 | ring
      rw [hsplit]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ ?_)
      fin_cases n <;> simp only []
      · show MvPolynomial.X (0 : Fin 3) - sigT K (psiT K c (MvPolynomial.X (0 : Fin 3)))
          ∈ Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K))
        rw [hbase0]
        exact Ideal.zero_mem _
      · show MvPolynomial.X (1 : Fin 3) - sigT K (psiT K c (MvPolynomial.X (1 : Fin 3)))
          ∈ Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K))
        exact hbase1
      · show MvPolynomial.X (2 : Fin 3) - sigT K (psiT K c (MvPolynomial.X (2 : Fin 3)))
          ∈ Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K))
        rw [hbase2]
        exact Ideal.zero_mem _

/-- `zC` is a non-zero-divisor modulo `(zA)`: if `u·zC ∈ (zA)` then `u ∈ (zA)`. -/
theorem zC_saturation_aux (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : h ≠ 0) :
    ∀ u : MvPolynomial (Fin 3) K,
      u * (zC K a b h) ∈ Ideal.span {zA K a b h} →
        u ∈ Ideal.span {zA K a b h} := by
  have hc : (a ^ 3 / b ^ 3) * b ^ 3 = a ^ 3 := by
    rw [div_eq_mul_inv]
    calc a ^ 3 * (b ^ 3)⁻¹ * b ^ 3 = a ^ 3 * ((b ^ 3)⁻¹ * b ^ 3) := by ring
      _ = a ^ 3 * 1 := by rw [inv_mul_cancel₀ (pow_ne_zero 3 hb)]
      _ = a ^ 3 := by rw [mul_one]
  intro u hu
  have h0 : psiT K (a ^ 3 / b ^ 3) u = 0 := by
    have hmul : psiT K (a ^ 3 / b ^ 3) u * psiT K (a ^ 3 / b ^ 3) (zC K a b h) = 0 := by
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hu
      rw [← map_mul, hs, map_mul, psiT_zA K a b h (a ^ 3 / b ^ 3) hc, zero_mul]
    rcases mul_eq_zero.mp hmul with h1 | h1
    · exact h1
    · exact absurd h1 (psiT_zC_ne_zero K a b h (a ^ 3 / b ^ 3) ha hb)
  have hker := sub_sigT_psiT_mem K a b h (a ^ 3 / b ^ 3) hb hh hc u
  rwa [h0, map_zero, sub_zero] at hker

theorem starLem (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ∀ B : MvPolynomial (Fin 3) K,
      B * Work.MotK.TGen.zC K a b h
        ∈ Ideal.span {Work.MotK.TGen.zA K a b h, Work.MotK.TGen.zg K a b h} →
      B ∈ Ideal.span {Work.MotK.TGen.zA K a b h, Work.MotK.TGen.zC K a b h} := by
  intro B hB
  -- `(zA, zg) ⊆ (zA, zC²)`, from `zElim_quad_id`.
  have hb4h : b ^ 4 * h ≠ 0 := mul_ne_zero (pow_ne_zero 4 hb) hh
  have hX : zAl K a b h * (zC K a b h) ^ 2
      + zA K a b h * (zBet K a b h * zC K a b h + zGam K a b h * zA K a b h)
      ∈ Ideal.span {zA K a b h, (zC K a b h) ^ 2} := by
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mul_mem_left _ (zAl K a b h) (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_right
        (zBet K a b h * zC K a b h + zGam K a b h * zA K a b h) _
        (Ideal.subset_span (by simp))
  have hzg : zg K a b h ∈ Ideal.span {zA K a b h, (zC K a b h) ^ 2} := by
    have h2 : MvPolynomial.C (b ^ 4 * h) * zg K a b h
        = zAl K a b h * (zC K a b h) ^ 2
          + zA K a b h * (zBet K a b h * zC K a b h + zGam K a b h * zA K a b h) := by
      rw [← zElim_quad_id (K := K) a b h]; ring
    have h3 : zg K a b h = MvPolynomial.C ((b ^ 4 * h)⁻¹)
        * (zAl K a b h * (zC K a b h) ^ 2
          + zA K a b h * (zBet K a b h * zC K a b h + zGam K a b h * zA K a b h)) := by
      rw [← h2, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hb4h, MvPolynomial.C_1,
        one_mul]
    rw [h3]
    exact Ideal.mul_mem_left _ (MvPolynomial.C ((b ^ 4 * h)⁻¹)) hX
  have hsub : Ideal.span {zA K a b h, zg K a b h}
      ≤ Ideal.span {zA K a b h, (zC K a b h) ^ 2} := by
    rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · exact hzg
  have hB' : B * zC K a b h ∈ Ideal.span {zA K a b h, (zC K a b h) ^ 2} := hsub hB
  rw [Ideal.mem_span_pair] at hB'
  obtain ⟨p, r, hpr⟩ := hB'
  -- `zC·(B − zC·r) ∈ (zA)`, hence `B − zC·r ∈ (zA)`.
  have hw : (B - zC K a b h * r) * zC K a b h ∈ Ideal.span {zA K a b h} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨p, ?_⟩
    calc (B - zC K a b h * r) * zC K a b h
        = B * zC K a b h - r * (zC K a b h) ^ 2 := by ring
      _ = (p * zA K a b h + r * (zC K a b h) ^ 2) - r * (zC K a b h) ^ 2 := by rw [← hpr]
      _ = zA K a b h * p := by ring
  have hwm : (B - zC K a b h * r) ∈ Ideal.span {zA K a b h} :=
    zC_saturation_aux K a b h ha hb hh _ hw
  have hfin : B = (B - zC K a b h * r) + r * zC K a b h := by ring
  rw [hfin]
  refine Ideal.add_mem _ ?_ ?_
  · have hsub2 : ({zA K a b h} : Set (MvPolynomial (Fin 3) K)) ⊆ {zA K a b h, zC K a b h} := by
      rintro x rfl
      simp
    exact Ideal.span_mono hsub2 hwm
  · exact Ideal.mul_mem_left _ r (Ideal.subset_span (by simp))

end Work.MotK.TGen
