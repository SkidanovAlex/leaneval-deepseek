import Mathlib
import Submission.Work.MotK.TGen.ZPlaneDefs
import Submission.Work.MotK.TGen.ker_zPsi_eq_saturation
import Submission.Work.MotK.TGen.zIdealMem
import Submission.Work.MotK.TGen.RadSatDefs
import Submission.Work.MotK.TGen.zF1Div
import Submission.Work.MotK.TGen.zJ_inter_rename
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- The chart substitution `x₀ ↦ x₀`, `x₁ ↦ (a³/b³) x₂²`, `x₂ ↦ x₂`, whose kernel is `(zA)`. -/
noncomputable def zChi (a b h : K) : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval
    ![MvPolynomial.X 0, MvPolynomial.C (a^(3:ℕ)/b^(3:ℕ)) * (MvPolynomial.X 1)^(2:ℕ), MvPolynomial.X 1]

/-- The inclusion of the plane variables `x₀, x₂` into the threefold variables. -/
abbrev zEmbA : Fin 2 → Fin 3 := ![(0 : Fin 3), (2 : Fin 3)]

theorem zEmbA_zero : zEmbA (0 : Fin 2) = (0 : Fin 3) := rfl

theorem zEmbA_one : zEmbA (1 : Fin 2) = (2 : Fin 3) := rfl

theorem zChi_C (a b h : K) (r : K) : zChi a b h (C r) = C r := by
  simp only [zChi, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

theorem zChi_X0 (a b h : K) : zChi a b h (X 0) = (X 0 : MvPolynomial (Fin 2) K) := by
  simp only [zChi, MvPolynomial.aeval_X, Matrix.cons_val_zero]

theorem zChi_X1 (a b h : K) :
    zChi a b h (X 1) = C (a^(3:ℕ)/b^(3:ℕ)) * (X 1 : MvPolynomial (Fin 2) K)^(2:ℕ) := by
  simp only [zChi, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem zChi_X2 (a b h : K) : zChi a b h (X 2) = (X 1 : MvPolynomial (Fin 2) K) := by
  simp only [zChi, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  rfl

/-- `C ((b^3*h)⁻¹) * C (b^3*h) = 1` for `b h ≠ 0`. -/
theorem C_inv_mul_coeff (a b h : K) (hb : b ≠ 0) (hh : h ≠ 0) :
    (C ((b^(3:ℕ)*h)⁻¹) : MvPolynomial (Fin 3) K) * C (b^(3:ℕ)*h) = 1 := by
  rw [← C_mul, inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero 3 hb) hh), C_1]

/-- `C ((b^3*h)⁻¹) * C (a^3*h) = C (a³/b³)` for `b h ≠ 0`. -/
theorem C_inv_mul_coeff2 (a b h : K) (hb : b ≠ 0) (hh : h ≠ 0) :
    (C ((b^(3:ℕ)*h)⁻¹) : MvPolynomial (Fin 3) K) * C (a^(3:ℕ)*h) = C (a^(3:ℕ)/b^(3:ℕ)) := by
  rw [← C_mul, show (b^(3:ℕ)*h)⁻¹ * (a^(3:ℕ)*h) = a^(3:ℕ)/b^(3:ℕ) by field_simp]

/-- `χ` kills `zA`. -/
theorem zChi_zA (a b h : K) (hb : b ≠ 0) (hh : h ≠ 0) :
    zChi a b h (zA K a b h) = 0 := by
  have hcoef : (C (b^(3:ℕ)*h) : MvPolynomial (Fin 2) K) * C (a^(3:ℕ)/b^(3:ℕ)) = C (a^(3:ℕ)*h) := by
    rw [← C_mul, show b^(3:ℕ)*h*(a^(3:ℕ)/b^(3:ℕ)) = a^(3:ℕ)*h by field_simp; try ring]
  have hB : (C b : MvPolynomial (Fin 2) K)^(3:ℕ) * C h = C (b^(3:ℕ)*h) := by
    rw [← C_pow, ← C_mul]
  have hA : (C a : MvPolynomial (Fin 2) K)^(3:ℕ) * C h = C (a^(3:ℕ)*h) := by
    rw [← C_pow, ← C_mul]
  simp only [zA, map_sub, map_mul, map_pow, zChi_C, zChi_X1, zChi_X2]
  rw [hB, hA]
  rw [show (C (b^(3:ℕ)*h) : MvPolynomial (Fin 2) K) * (C (a^(3:ℕ)/b^(3:ℕ)) * (X 1)^(2:ℕ))
      = ((C (b^(3:ℕ)*h) : MvPolynomial (Fin 2) K) * C (a^(3:ℕ)/b^(3:ℕ))) * (X 1)^(2:ℕ) from by ring, hcoef]
  first | refl_ring1 | ring

/-- `χ zC ≠ 0`: its constant term is `a²b ≠ 0`. -/
theorem zChi_zC_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    zChi a b h (zC K a b h) ≠ 0 := by
  intro hz
  have hc : MvPolynomial.constantCoeff (zChi a b h (zC K a b h)) = 0 := by rw [hz, map_zero]
  rw [zC] at hc
  simp only [map_sub, map_mul, map_pow, zChi_C, zChi_X1, zChi_X2] at hc
  simp only [map_sub, map_mul, map_pow, pow_two, MvPolynomial.constantCoeff_C,
    MvPolynomial.constantCoeff_X, mul_zero, zero_mul, sub_zero] at hc
  exact (mul_ne_zero (mul_ne_zero ha ha) hb) hc

/-- Every `p` is congruent to its `χ`-image (pulled back along `x₁, x₂`) modulo `(zA)`. -/
theorem zChi_sub_rename (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (p : MvPolynomial (Fin 3) K) :
    p - rename zEmbA (zChi a b h p)
      ∈ Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K)) := by
  have hX1 : (X 1 : MvPolynomial (Fin 3) K) - rename zEmbA (C (a^(3:ℕ)/b^(3:ℕ)) * (X 1)^(2:ℕ))
      ∈ Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K)) := by
    have hcB : (C b : MvPolynomial (Fin 3) K)^(3:ℕ) * C h = C (b^(3:ℕ)*h) := by
      rw [← C_pow, ← C_mul]
    have hcA : (C a : MvPolynomial (Fin 3) K)^(3:ℕ) * C h = C (a^(3:ℕ)*h) := by
      rw [← C_pow, ← C_mul]
    have h : (X 1 : MvPolynomial (Fin 3) K) - rename zEmbA (C (a^(3:ℕ)/b^(3:ℕ)) * (X 1)^(2:ℕ))
        = C ((b^(3:ℕ)*h)⁻¹) * zA K a b h := by
      simp only [zA, map_mul, map_pow, MvPolynomial.rename_C, MvPolynomial.rename_X,
        zEmbA_one]
      rw [hcB, hcA]
      rw [show (C ((b^(3:ℕ)*h)⁻¹) : MvPolynomial (Fin 3) K)
            * (C (b^(3:ℕ)*h) * X 1 - C (a^(3:ℕ)*h) * (X 2)^(2:ℕ))
          = (C ((b^(3:ℕ)*h)⁻¹) * C (b^(3:ℕ)*h)) * X 1
            - (C ((b^(3:ℕ)*h)⁻¹) * C (a^(3:ℕ)*h)) * (X 2)^(2:ℕ) from by ring]
      simp only [C_inv_mul_coeff a b h hb hh, C_inv_mul_coeff2 a b h hb hh, C_1]
      first | refl_ring1 | ring
    rw [h]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [zChi_C, MvPolynomial.rename_C, sub_self]
    exact Ideal.zero_mem _
  | add p q hp hq =>
    rw [map_add, map_add]
    rw [show p + q - (rename zEmbA (zChi a b h p) + rename zEmbA (zChi a b h q))
        = (p - rename zEmbA (zChi a b h p)) + (q - rename zEmbA (zChi a b h q)) from by ring]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    have hXi : (X i : MvPolynomial (Fin 3) K) - rename zEmbA (zChi a b h (X i))
        ∈ Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K)) := by
      fin_cases i
      · change (X (0 : Fin 3) : MvPolynomial (Fin 3) K) - rename zEmbA (zChi a b h (X 0))
          ∈ Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K))
        rw [zChi_X0, MvPolynomial.rename_X, zEmbA_zero, sub_self]
        exact Ideal.zero_mem _
      · change (X (1 : Fin 3) : MvPolynomial (Fin 3) K) - rename zEmbA (zChi a b h (X 1))
          ∈ Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K))
        rw [zChi_X1]
        exact hX1
      · change (X (2 : Fin 3) : MvPolynomial (Fin 3) K) - rename zEmbA (zChi a b h (X 2))
          ∈ Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K))
        rw [zChi_X2, MvPolynomial.rename_X, zEmbA_one, sub_self]
        exact Ideal.zero_mem _
    rw [show p * X i - rename zEmbA (zChi a b h p) * rename zEmbA (zChi a b h (X i))
        = (p - rename zEmbA (zChi a b h p)) * X i
          + rename zEmbA (zChi a b h p) * ((X i : MvPolynomial (Fin 3) K)
              - rename zEmbA (zChi a b h (X i))) from by ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right (X i) (Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K))) hp) (Ideal.mul_mem_left _ _ hXi)

/-- The kernel of `χ` is `(zA)`. -/
theorem zChi_eq_zero_iff (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (p : MvPolynomial (Fin 3) K) :
    zChi a b h p = 0 ↔ p ∈ Ideal.span ({zA K a b h} : Set (MvPolynomial (Fin 3) K)) := by
  constructor
  · intro hp
    have hdiv := zChi_sub_rename (K := K) a b h ha hb hh p
    rw [hp, map_zero, sub_zero] at hdiv
    exact hdiv
  · intro hp0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hp0
    rw [hc, map_mul, zChi_zA a b h hb hh, zero_mul]

/-- **`zA` is a non-zero-divisor modulo `(zB)`**: if `zA * w ∈ (zB)` then `w ∈ (zB)`. -/
theorem zA_cancel_zB (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    [IsDomain (ZD K a b h)] (w : MvPolynomial (Fin 3) K)
    (hw : zA K a b h * w ∈ Ideal.span ({zB K a b h} : Set (MvPolynomial (Fin 3) K))) :
    w ∈ Ideal.span ({zB K a b h} : Set (MvPolynomial (Fin 3) K)) := by
  have hzA : zA K a b h ≠ 0 := by
    intro h0
    exact za1_ne_zero K a b h ha hb hh
      (by rw [← zPsi_zA K a b h, h0, map_zero])
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hw
  have hx : zA K a b h * X 0 = zB K a b h + zC K a b h := by rw [zB]; ring
  -- `zA * (w - c x₀) = - c * zC`
  have hmain : zA K a b h * (w - c * X 0) = -(c * zC K a b h) := by
    rw [mul_sub, hc]
    rw [show zA K a b h * (c * X 0) = c * (zA K a b h * X 0) from by ring, hx]
    first | refl_ring1 | ring
  -- applying `χ`: `χ c * χ zC = 0`, so `χ c = 0`
  have hχ : zChi a b h c * zChi a b h (zC K a b h) = 0 := by
    have hcongr := congrArg (zChi a b h) hmain
    simp only [map_mul, map_sub, map_neg, zChi_zA a b h hb hh, zero_mul] at hcongr
    exact neg_eq_zero.mp hcongr.symm
  have hc0 : zChi a b h c = 0 := by
    rcases mul_eq_zero.mp hχ with hcase | hcase
    · exact hcase
    · exact absurd hcase (zChi_zC_ne_zero (K := K) a b h ha hb)
  -- hence `c ∈ (zA)`, say `c = zA * c'`
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp
    ((zChi_eq_zero_iff (K := K) a b h ha hb hh c).mp hc0)
  rw [Ideal.mem_span_singleton]
  refine ⟨c', ?_⟩
  have h2 : zA K a b h * (w - zB K a b h * c') = 0 := by
    rw [mul_sub, hc, hc']
    first | refl_ring1 | ring
  rcases mul_eq_zero.mp h2 with hcase | hcase
  · exact absurd hcase hzA
  · exact sub_eq_zero.mp hcase



/-- The `zB`-component of the product `zA^2 * zF1` (see `zA_sq_zF1_eq`). -/
noncomputable def zQ (a b h : K) : MvPolynomial (Fin 3) K :=
  2 * zAl K a b h * zC K a b h + zAl K a b h * zB K a b h + zBet K a b h * zA K a b h

/-- **The key identity.**  `zA^2 * zF1` differs from `b^4*h*zg` by a multiple of `zB`:

`zA^2 zF1 = b^4 h zg + zQ zB`.

(Proof: `zA^2 zF1 = zAl (zA x₀)^2 + zBet (zA x₀) zA + zGam zA^2` and `zA x₀ = zC + zB`; the
`zB^0`-coefficient is `zAl zC^2 + zBet zC zA + zGam zA^2 = b^4 h zg` (`zElim_quad_id`).) -/
theorem zA_sq_zF1_eq (a b h : K) :
    zA K a b h ^(2:ℕ) * zF1 K a b h
      = C (b^(4:ℕ)*h) * zg K a b h + zQ (K := K) a b h * zB K a b h := by
  have h1 : zA K a b h ^(2:ℕ) * zF1 K a b h
      = zAl K a b h * (zA K a b h * X 0) ^(2:ℕ) + zBet K a b h * (zA K a b h * X 0) * zA K a b h
        + zGam K a b h * zA K a b h ^(2:ℕ) := by
    rw [zF1]; ring
  have hsub : zA K a b h * X 0 = zB K a b h + zC K a b h := by rw [zB]; ring
  have hexp : zAl K a b h * (zB K a b h + zC K a b h) ^(2:ℕ)
        + zBet K a b h * (zB K a b h + zC K a b h) * zA K a b h + zGam K a b h * zA K a b h ^(2:ℕ)
      = (zAl K a b h * zC K a b h ^(2:ℕ) + zBet K a b h * zC K a b h * zA K a b h
          + zGam K a b h * zA K a b h ^(2:ℕ))
        + (2 * zAl K a b h * zC K a b h + zAl K a b h * zB K a b h
            + zBet K a b h * zA K a b h) * zB K a b h := by ring
  rw [h1, hsub, hexp, zQ, zElim_quad_id (K := K) a b h]

/-- `b^4*h*zg ∈ zJ = (zF1, zB)`. -/
theorem C_b4h_zg_mem_zJ (a b h : K) :
    (C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K) * zg K a b h ∈ zJ K a b h := by
  rw [zJ]
  rw [show (C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K) * zg K a b h
      = zA K a b h ^(2:ℕ) * zF1 K a b h - zQ (K := K) a b h * zB K a b h from by
    rw [zA_sq_zF1_eq]; ring]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/-- `zF1 ∈ zJ`. -/
theorem zF1_mem_zJ (a b h : K) : zF1 K a b h ∈ zJ K a b h :=
  Ideal.subset_span (by simp)

/-- `zB ∈ zJ`. -/
theorem zB_mem_zJ (a b h : K) : zB K a b h ∈ zJ K a b h :=
  Ideal.subset_span (by simp)

/-- `zJ = (zF1, zB)` is contained in `ZI`.

NOTE (2026-10-05): kept `private`, since `Submission/Work/MotK/TGen/ZPlaneModelMain.lean`
(the saturation route `ZRingIsDomainAll`) declares a *public* `zJ_le_ZI` with the same statement:
now that `ZPlaneModel.lean` imports this module, a public copy here would make that file fail with
"`Work.MotK.TGen.zJ_le_ZI` has already been declared". -/
private theorem zJ_le_ZI (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    zJ K a b h ≤ Work.MotK.TwCensus.ZI a b h := by
  rw [zJ, Ideal.span_le]
  intro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact zF1_mem_ZI (K := K) a b h ha hb
  · exact zB_mem_ZI (K := K) a b h hb

/-- The saturations of `(zg, zB)` and of `zJ = (zF1, zB)` at `zA` agree, in the "`∃ N`" form. -/
theorem zA_saturation_iff (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (f : MvPolynomial (Fin 3) K) :
    (∃ N : ℕ, zA K a b h ^ N * f
        ∈ Ideal.span ({zg K a b h, zB K a b h} : Set (MvPolynomial (Fin 3) K)))
      ↔ (∃ N : ℕ, zA K a b h ^ N * f ∈ zJ K a b h) := by
  have hb4 : b^(4:ℕ)*h ≠ 0 := mul_ne_zero (pow_ne_zero 4 hb) hh
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨P, Q, hPQ⟩ := Ideal.mem_span_pair.mp hN
    refine ⟨N, ?_⟩
    have h1 : (C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K) * (zA K a b h ^ N * f)
        = P * ((C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K) * zg K a b h)
          + (C (b^(4:ℕ)*h) * Q) * zB K a b h := by
      rw [← hPQ]; ring
    have h2 : (C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K) * (zA K a b h ^ N * f) ∈ zJ K a b h := by
      rw [h1]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (C_b4h_zg_mem_zJ (K := K) a b h))
        (Ideal.mul_mem_left _ _ (zB_mem_zJ (K := K) a b h))
    have := Ideal.mul_mem_left (zJ K a b h) (C ((b^(4:ℕ)*h)⁻¹) : MvPolynomial (Fin 3) K) h2
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hb4, C_1, one_mul] at this
  · rintro ⟨N, hN⟩
    obtain ⟨P, Q, hPQ⟩ := Ideal.mem_span_pair.mp hN
    refine ⟨N + 2, ?_⟩
    have hstep : zA K a b h ^(2:ℕ) * (P * zF1 K a b h + Q * zB K a b h)
        = P * (zA K a b h ^(2:ℕ) * zF1 K a b h) + (zA K a b h ^(2:ℕ) * Q) * zB K a b h := by
      first | refl_ring1 | ring
    have h2 : zA K a b h ^ (N + 2) * f
        = P * ((C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K) * zg K a b h)
          + (P * zQ (K := K) a b h + zA K a b h ^(2:ℕ) * Q) * zB K a b h := by
      rw [show zA K a b h ^ (N + 2) * f = zA K a b h ^(2:ℕ) * (zA K a b h ^ N * f) from by ring,
        ← hPQ, hstep, zA_sq_zF1_eq]
      first | refl_ring1 | ring
    rw [h2]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/-- **The main step**: `zA` is a non-zero-divisor modulo `zJ = (zF1, zB)`. -/
theorem zJ_zA_cancel (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    [IsDomain (ZD K a b h)] (f : MvPolynomial (Fin 3) K)
    (hf : zA K a b h * f ∈ zJ K a b h) : f ∈ zJ K a b h := by
  obtain ⟨f₀, f₁, q, hfdecomp⟩ := zF1Div K a b h ha hb hh f
  -- the low part `f' = f₀ + f₁ x₀` satisfies `zA * f' ∈ zJ`
  have hf'mem : zA K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0) ∈ zJ K a b h := by
    have h1 : zA K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0)
        = zA K a b h * f - (zA K a b h * q) * zF1 K a b h := by
      rw [hfdecomp]; ring
    rw [h1]
    exact Ideal.sub_mem _ hf (Ideal.mul_mem_left _ _ (zF1_mem_zJ (K := K) a b h))
  -- `zA * f' = rename f₁ * zB + rename θ` with `θ = zpA f₀ + f₁ zpC` in the plane
  have hsplit : zA K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0)
      = rename zEmb f₁ * zB K a b h
        + rename zEmb (zpA K a b h * f₀ + f₁ * zpC K a b h) := by
    rw [zA_eq_rename, zB_eq]
    simp only [map_add, map_mul]
    first | refl_ring1 | ring
  have hθmem : rename zEmb (zpA K a b h * f₀ + f₁ * zpC K a b h) ∈ zJ K a b h := by
    have hsum := hsplit ▸ hf'mem
    have h2 := Ideal.sub_mem _ hsum
      (Ideal.mul_mem_left (zJ K a b h) (rename zEmb f₁) (zB_mem_zJ (K := K) a b h))
    simpa using h2
  -- the plane polynomial `θ` is a multiple of the eliminant
  have hθ : zpA K a b h * f₀ + f₁ * zpC K a b h
      ∈ Ideal.span ({Work.MotK.TwCensus.ZElim2 a b h} : Set (MvPolynomial (Fin 2) K)) :=
    zJ_inter_rename K a b h ha hb hh (zpA K a b h * f₀ + f₁ * zpC K a b h) hθmem
  obtain ⟨ν, hν⟩ := Ideal.mem_span_singleton.mp hθ
  -- so `rename θ = zg * rename ν`
  have hzg : rename zEmb (zpA K a b h * f₀ + f₁ * zpC K a b h)
      = zg K a b h * rename zEmb ν := by
    rw [hν, map_mul]
    rfl
  -- the descent: `zA * (b^4 h f' - zA (rename ν) zF1) ∈ (zB)`
  have hkey : zA K a b h * ((C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K)
        * (rename zEmb f₀ + rename zEmb f₁ * X 0)
        - zA K a b h * rename zEmb ν * zF1 K a b h)
      = ((C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K) * rename zEmb f₁
          - rename zEmb ν * zQ (K := K) a b h) * zB K a b h := by
    have hzf' : zA K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0)
        = rename zEmb f₁ * zB K a b h + zg K a b h * rename zEmb ν := by
      rw [hsplit, hzg]
    calc zA K a b h * ((C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K)
            * (rename zEmb f₀ + rename zEmb f₁ * X 0)
            - zA K a b h * rename zEmb ν * zF1 K a b h)
        = (C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K)
            * (zA K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0))
            - rename zEmb ν * (zA K a b h ^(2:ℕ) * zF1 K a b h) := by ring
      _ = (C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K)
            * (rename zEmb f₁ * zB K a b h + zg K a b h * rename zEmb ν)
            - rename zEmb ν * (C (b^(4:ℕ)*h) * zg K a b h + zQ (K := K) a b h * zB K a b h) := by
          rw [hzf', zA_sq_zF1_eq]
      _ = ((C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K) * rename zEmb f₁
            - rename zEmb ν * zQ (K := K) a b h) * zB K a b h := by ring
  have hmem_zB : (C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K)
        * (rename zEmb f₀ + rename zEmb f₁ * X 0)
        - zA K a b h * rename zEmb ν * zF1 K a b h
      ∈ Ideal.span ({zB K a b h} : Set (MvPolynomial (Fin 3) K)) := by
    refine zA_cancel_zB (K := K) a b h ha hb hh _ ?_
    rw [hkey]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have hlow : rename zEmb f₀ + rename zEmb f₁ * X 0 ∈ zJ K a b h := by
    have hmem' : (C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K)
        * (rename zEmb f₀ + rename zEmb f₁ * X 0)
        - zA K a b h * rename zEmb ν * zF1 K a b h ∈ zJ K a b h :=
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (zB_mem_zJ (K := K) a b h))) hmem_zB
    have h2 : zA K a b h * rename zEmb ν * zF1 K a b h ∈ zJ K a b h :=
      Ideal.mul_mem_left _ _ (zF1_mem_zJ (K := K) a b h)
    have h1 : (C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K)
        * (rename zEmb f₀ + rename zEmb f₁ * X 0) ∈ zJ K a b h := by
      have h3 : (C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K)
          * (rename zEmb f₀ + rename zEmb f₁ * X 0)
          = ((C (b^(4:ℕ)*h) : MvPolynomial (Fin 3) K) * (rename zEmb f₀ + rename zEmb f₁ * X 0)
              - zA K a b h * rename zEmb ν * zF1 K a b h)
            + zA K a b h * rename zEmb ν * zF1 K a b h := by ring
      rw [h3]
      exact Ideal.add_mem _ hmem' h2
    have hb4 : b^(4:ℕ)*h ≠ 0 := mul_ne_zero (pow_ne_zero 4 hb) hh
    have := Ideal.mul_mem_left (zJ K a b h) (C ((b^(4:ℕ)*h)⁻¹) : MvPolynomial (Fin 3) K) h1
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hb4, C_1, one_mul] at this
  rw [hfdecomp]
  exact Ideal.add_mem _ hlow (Ideal.mul_mem_left _ _ (zF1_mem_zJ (K := K) a b h))

/-- The geometric input: `ker zPsi ⊆ √(ZI)`, i.e. no irreducible component of the residual curve
`Z = V(ZI) ⊆ 𝔸³` lies in `{zA = 0}`.

WARNING: `Submission/Work/MotK/TGen/ZPlaneModel.lean` already contains a `sorry`ed declaration
`ker_zPsi_le_radical` with the same content, and `ker_zPsi_le_radical_aux.lean` has the equivalent
`radical_zA_saturation`, also `sorry`ed.  Those must NOT be used: a proof that goes through them
inherits `sorryAx` and is worthless.  The proved pieces of the workspace that may be used freely
are `zA_mul_zG3_sub`, `zg_mem_zB_zG3`, `zB_mem_ZI`, `zg_mem_ZI`, `ker_zPsi_eq_saturation`
(all in `ker_zPsi_le_radical_aux.lean` / `ker_zPsi_eq_saturation.lean`, sorry-free):
they reduce the goal to `radical_zA_saturation` — `zA` is a non-zero-divisor modulo `√(ZI)` —
which is the real content and has to be proved from scratch.

Geometric statement of that content: the finitely many points of `Z = V(ZI)` with `zA = 0`
(equivalently `zA = zC = g = 0`, where `g = ZElim a b h`) are limits of points of the graph
`x₀ = zC/zA` over `V(g)`, so `√(ZI) = ker zPsi` (the ideal of the closure of the graph). -/
theorem kernel_le_radical (K : Type) [Field K] (a b h : K)
    [IsDomain (Work.MotK.TGen.ZD K a b h)] (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    RingHom.ker (Work.MotK.TGen.zPsi K a b h) ≤ Ideal.radical (Work.MotK.TwCensus.ZI a b h) := by
  intro f hf
  obtain ⟨N, hN⟩ := (ker_zPsi_eq_saturation K a b h ha hb hh f).mp hf
  obtain ⟨M, hM⟩ := (zA_saturation_iff (K := K) a b h ha hb hh f).mp ⟨N, hN⟩
  have aux : ∀ M : ℕ, zA K a b h ^ M * f ∈ zJ K a b h → f ∈ zJ K a b h := by
    intro M
    induction M with
    | zero => intro hstep; simpa using hstep
    | succ M ih =>
      intro hstep
      refine ih ?_
      refine zJ_zA_cancel (K := K) a b h ha hb hh (zA K a b h ^ M * f) ?_
      rwa [show zA K a b h * (zA K a b h ^ M * f) = zA K a b h ^ (M + 1) * f from by ring]
  exact Ideal.le_radical (zJ_le_ZI (K := K) a b h ha hb (aux M hM))

end Work.MotK.TGen
