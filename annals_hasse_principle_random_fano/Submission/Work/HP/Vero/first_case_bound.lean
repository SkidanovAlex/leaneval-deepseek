import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.SigmaDefs
import Submission.Work.HP.Vero.LamAux
import Submission.Work.HP.Vero.FirstCaseDefs
import Submission.Work.HP.Vero.gam_witness_gcd
import Submission.Work.HP.Vero.sum_sigma_sq_le
import Submission.Work.HP.Vero.gcdMinors2_posR
import Submission.Work.HP.Vero.span_realify_latOrth_inf
import Submission.Work.HP.Transf.Basic

/-!
# The first case of §3.3 of Browning–Le Boudec–Sawin (the `σ`-test-vector proof)

For `x y : Fin (n+1) → ℤ` and `a` a nonzero element of the dual lattice of
`Γ = Λ_{ν₂x} ∩ Λ_{ν₂y}` that happens to lie in `span_ℝ(ν₂x, ν₂y, ν₂(x+y))`, we prove

`‖a‖ ≥ wedgeNorm x y ^ 2 / (√2 · 𝒢(x,y)^2 · ‖x‖‖y‖)`.

Route.  Writing `a = c₁ν₂x + c₂ν₂y + c₃ν₂(x+y)` and using that `a` is orthogonal to `ν₂x` and
`ν₂y` (this is `span_realify_latOrth_inf`), one gets `c₃ ≠ 0`.  Pairing `a` with the integer
witness `Z ∈ Γ` of `gam_witness_gcd` gives `c₃·𝒢² ∈ ℤ`, whence `|c₃| ≥ 1/𝒢²`.  Pairing `a` with
the test vector `t = σ(u₀,v₀)`, `u₀ = pairU x y = ‖x‖²y - ⟨x,y⟩x`,
`v₀ = pairV x y = ‖y‖²x - ⟨x,y⟩y`, gives `⟨a,t⟩ = c₃·(pairW x y)²` while
`‖t‖² ≤ 2‖u₀‖²‖v₀‖² = 2·pairA x·pairA y·(pairW x y)²`.  Cauchy–Schwarz then yields
`‖a‖ ≥ |c₃|·|pairW|/(√2·‖x‖‖y‖) ≥ (1/𝒢²)·wedgeNorm²/(√2·‖x‖‖y‖)`.
-/

set_option autoImplicit false
noncomputable section
open Finset

namespace Work.HP.Vero

open Work.HP

variable {n : ℕ}

/-! ## Elementary pair data -/

/-- Lagrange's identity: `pairW x y ≥ 0`. -/
lemma pairW_nonneg_aux (x y : Fin (n + 1) → ℤ) : (0 : ℤ) ≤ pairW x y := by
  have hsq : pairC x y ^ 2 ≤ pairA x * pairA y := by
    rw [pairC, pairA]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  rw [pairW]
  linarith

/-- `∑ i, ((x i : ℤ) : ℝ) ^ 2 = pairA x`. -/
lemma sum_cast_sq_pairA (x : Fin (n + 1) → ℤ) :
    (∑ i, ((x i : ℤ) : ℝ) ^ 2) = (pairA x : ℝ) := by
  rw [pairA]
  push_cast
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-- `∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) = pairC x y`. -/
lemma sum_cast_mul_pairC (x y : Fin (n + 1) → ℤ) :
    (∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) = (pairC x y : ℝ) := by
  rw [pairC]
  push_cast
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-- `eNorm x ^ 2 = pairA x` for an integer vector. -/
lemma eNorm_sq_pairA_aux (x : Fin (n + 1) → ℤ) : eNorm x ^ 2 = (pairA x : ℝ) := by
  rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ((x i : ℝ)))]
  exact sum_cast_sq_pairA x

/-- `dotR (toR x) (toR y) = pairC x y`. -/
lemma dotR_toR_pairC_aux (x y : Fin (n + 1) → ℤ) : dotR (toR x) (toR y) = (pairC x y : ℝ) := by
  rw [dotR]
  exact sum_cast_mul_pairC x y

/-- `wedgeNorm x y ^ 2 = pairW x y`. -/
lemma wedgeNorm_sq_pairW_aux (x y : Fin (n + 1) → ℤ) : wedgeNorm x y ^ 2 = (pairW x y : ℝ) := by
  rw [wedgeNorm, eNorm_sq_pairA_aux x, eNorm_sq_pairA_aux y, dotR_toR_pairC_aux x y]
  rw [Real.sq_sqrt (by
    have h := pairW_nonneg_aux x y
    rw [pairW] at h
    exact_mod_cast h)]
  rw [pairW]
  push_cast
  ring

/-- `∑ i, pairU x y i * z i` in terms of the pairings of `x` and `y` with `z`. -/
lemma sum_pairU_mul (x y z : Fin (n + 1) → ℤ) :
    ∑ i, pairU x y i * z i
      = pairA x * (∑ i, y i * z i) - pairC x y * (∑ i, x i * z i) := by
  rw [pairU]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ i, (pairA x * y i - pairC x y * x i) * z i)
      = ∑ i, (pairA x * (y i * z i) - pairC x y * (x i * z i)) from
        Finset.sum_congr rfl (fun i _ => by ring)]
  rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

/-- `∑ i, pairV x y i * z i` in terms of the pairings of `x` and `y` with `z`. -/
lemma sum_pairV_mul (x y z : Fin (n + 1) → ℤ) :
    ∑ i, pairV x y i * z i
      = pairA y * (∑ i, x i * z i) - pairC x y * (∑ i, y i * z i) := by
  rw [pairV]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ i, (pairA y * x i - pairC x y * y i) * z i)
      = ∑ i, (pairA y * (x i * z i) - pairC x y * (y i * z i)) from
        Finset.sum_congr rfl (fun i _ => by ring)]
  rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

/-- `eNorm (pairU x y) ^ 2 = pairA x * pairW x y`. -/
lemma eNorm_sq_pairU (x y : Fin (n + 1) → ℤ) :
    eNorm (pairU x y) ^ 2 = (pairA x : ℝ) * (pairW x y : ℝ) := by
  rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ((pairU x y i : ℝ)))]
  have hexp : ∀ i : Fin (n + 1), ((pairU x y i : ℤ) : ℝ) ^ 2
      = (pairA x : ℝ) ^ 2 * ((y i : ℤ) : ℝ) ^ 2
        - (2 * (pairA x : ℝ) * (pairC x y : ℝ)) * (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ))
        + (pairC x y : ℝ) ^ 2 * ((x i : ℤ) : ℝ) ^ 2 := by
    intro i
    rw [pairU]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [show (∑ i, (pairA x : ℝ) ^ 2 * ((y i : ℤ) : ℝ) ^ 2)
        = (pairA x : ℝ) ^ 2 * (pairA y : ℝ) from by
      rw [← Finset.mul_sum, sum_cast_sq_pairA y]]
  rw [show (∑ i, (2 * (pairA x : ℝ) * (pairC x y : ℝ))
          * (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)))
        = (2 * (pairA x : ℝ) * (pairC x y : ℝ)) * (pairC x y : ℝ) from by
      rw [← Finset.mul_sum, sum_cast_mul_pairC x y]]
  rw [show (∑ i, (pairC x y : ℝ) ^ 2 * ((x i : ℤ) : ℝ) ^ 2)
        = (pairC x y : ℝ) ^ 2 * (pairA x : ℝ) from by
      rw [← Finset.mul_sum, sum_cast_sq_pairA x]]
  rw [pairW]
  push_cast
  ring

/-- `eNorm (pairV x y) ^ 2 = pairA y * pairW x y`. -/
lemma eNorm_sq_pairV (x y : Fin (n + 1) → ℤ) :
    eNorm (pairV x y) ^ 2 = (pairA y : ℝ) * (pairW x y : ℝ) := by
  rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ((pairV x y i : ℝ)))]
  have hexp : ∀ i : Fin (n + 1), ((pairV x y i : ℤ) : ℝ) ^ 2
      = (pairA y : ℝ) ^ 2 * ((x i : ℤ) : ℝ) ^ 2
        - (2 * (pairA y : ℝ) * (pairC x y : ℝ)) * (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ))
        + (pairC x y : ℝ) ^ 2 * ((y i : ℤ) : ℝ) ^ 2 := by
    intro i
    rw [pairV]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [show (∑ i, (pairA y : ℝ) ^ 2 * ((x i : ℤ) : ℝ) ^ 2)
        = (pairA y : ℝ) ^ 2 * (pairA x : ℝ) from by
      rw [← Finset.mul_sum, sum_cast_sq_pairA x]]
  rw [show (∑ i, (2 * (pairA y : ℝ) * (pairC x y : ℝ))
          * (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)))
        = (2 * (pairA y : ℝ) * (pairC x y : ℝ)) * (pairC x y : ℝ) from by
      rw [← Finset.mul_sum, sum_cast_mul_pairC x y]]
  rw [show (∑ i, (pairC x y : ℝ) ^ 2 * ((y i : ℤ) : ℝ) ^ 2)
        = (pairC x y : ℝ) ^ 2 * (pairA y : ℝ) from by
      rw [← Finset.mul_sum, sum_cast_sq_pairA y]]
  rw [pairW]
  push_cast
  ring

/-- Integer pairings and Euclidean norms of the two test vectors `pairU`, `pairV`. -/
lemma pairUV_data_aux (x y : Fin (n + 1) → ℤ) :
    (∑ i, pairU x y i * x i = 0) ∧
    (∑ i, pairU x y i * y i = pairW x y) ∧
    (∑ i, pairV x y i * y i = 0) ∧
    (∑ i, pairV x y i * x i = pairW x y) ∧
    eNorm (pairU x y) ^ 2 = (pairA x : ℝ) * (pairW x y : ℝ) ∧
    eNorm (pairV x y) ^ 2 = (pairA y : ℝ) * (pairW x y : ℝ) := by
  have hyx : (∑ i, y i * x i) = pairC x y := by
    rw [pairC]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hxx : (∑ i, x i * x i) = pairA x := by
    rw [pairA]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hyy : (∑ i, y i * y i) = pairA y := by
    rw [pairA]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hxyC : (∑ i, x i * y i) = pairC x y := by rw [pairC]
  refine ⟨?_, ?_, ?_, ?_, eNorm_sq_pairU x y, eNorm_sq_pairV x y⟩
  · rw [sum_pairU_mul x y x, hyx, hxx]; ring
  · rw [sum_pairU_mul x y y, hyy, hxyC, pairW]; ring
  · rw [sum_pairV_mul x y y, hxyC, hyy]; ring
  · rw [sum_pairV_mul x y x, hxx, hyx, pairW]; ring

/-- `rNorm (toR (σ u v)) ^ 2 ≤ 2 ‖u‖² ‖v‖²`. -/
lemma sigma_rNorm_sq_le_aux (u v : Fin (n + 1) → ℤ) :
    rNorm (toR (sigma n u v)) ^ 2 ≤ 2 * eNorm u ^ 2 * eNorm v ^ 2 := by
  have h := sum_sigma_sq_le (n := n) u v
  have h1 : rNorm (toR (sigma n u v)) ^ 2 = (∑ m, ((sigma n u v m : ℤ) : ℝ) ^ 2) := by
    rw [rNorm, Real.sq_sqrt (Finset.sum_nonneg fun m _ => sq_nonneg (toR (sigma n u v) m))]
    exact Finset.sum_congr rfl (fun m _ => rfl)
  have h2 : (2 : ℝ) * eNorm u ^ 2 * eNorm v ^ 2
      = 2 * (∑ i, ((u i : ℤ) : ℝ) ^ 2) * (∑ j, ((v j : ℤ) : ℝ) ^ 2) := by
    rw [eNorm_sq_pairA_aux u, eNorm_sq_pairA_aux v, ← sum_cast_sq_pairA u,
      ← sum_cast_sq_pairA v]
  rw [h1, h2]
  exact h

/-! ## The main first-case bound -/

/-- **First case.** A nonzero element of the dual lattice of `Γ = Λ_{ν₂x} ∩ Λ_{ν₂y}` that lies in
`span_ℝ(ν₂x, ν₂y, ν₂(x+y))` has norm at least `wedgeNorm x y ^ 2 / (√2 𝒢² ‖x‖‖y‖)`. -/
theorem first_case_bound (n : ℕ) (hn : 2 ≤ n) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y]) (a : Mon 2 n → ℝ)
    (ha : a ∈ dualLat (realify (Gam 2 n x y))) (ha0 : a ≠ 0)
    (hspan : a ∈ Submodule.span ℝ {toR (veronese 2 n x), toR (veronese 2 n y),
      toR (veronese 2 n (x + y))}) :
    wedgeNorm x y ^ 2 / (Real.sqrt 2 * (gcdMinors2 x y : ℝ) ^ 2 * (eNorm x * eNorm y))
      ≤ rNorm a := by
  classical
  obtain ⟨hu0x, hu0y, hv0y, hv0x, hnorU, hnorV⟩ := pairUV_data_aux x y
  have hWnnZ := pairW_nonneg_aux x y
  have hWnn : (0 : ℝ) ≤ (pairW x y : ℝ) := by exact_mod_cast hWnnZ
  have hxne : x ≠ 0 := by
    have := hxy.ne_zero (0 : Fin 2); simpa using this
  have hyne : y ≠ 0 := by
    have := hxy.ne_zero (1 : Fin 2); simpa using this
  -- ## Step 1: expand `a` in the three Veronese vectors
  have hrange : ({toR (veronese 2 n x), toR (veronese 2 n y), toR (veronese 2 n (x + y))} :
      Set (Mon 2 n → ℝ))
      = Set.range ![toR (veronese 2 n x), toR (veronese 2 n y),
          toR (veronese 2 n (x + y))] := by
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (h | h | h)
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
      · exact ⟨2, by simp [h]⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have hspan' : a ∈ Submodule.span ℝ (Set.range ![toR (veronese 2 n x), toR (veronese 2 n y),
      toR (veronese 2 n (x + y))]) := hrange ▸ hspan
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan'
  have hdecomp : a = c 0 • toR (veronese 2 n x) + c 1 • toR (veronese 2 n y)
      + c 2 • toR (veronese 2 n (x + y)) := by
    rw [← hc, Fin.sum_univ_three]
    simp
  -- ## Step 2: `a` is orthogonal to `ν₂x` and `ν₂y`
  have hmem : a ∈ LinearMap.ker (Fintype.linearCombination ℝ (fun m => ((veronese 2 n x) m : ℝ)))
      ⊓ LinearMap.ker (Fintype.linearCombination ℝ (fun m => ((veronese 2 n y) m : ℝ))) := by
    rw [← span_realify_latOrth_inf (veronese 2 n x) (veronese 2 n y)]
    exact ha.1
  have hox : ∑ m, ((veronese 2 n x) m : ℝ) * a m = 0 := by
    have h := hmem.1
    change Fintype.linearCombination ℝ (fun m => ((veronese 2 n x) m : ℝ)) a = 0 at h
    rw [Fintype.linearCombination_apply] at h
    simp only [smul_eq_mul] at h
    rw [Finset.sum_congr rfl (fun m _ => mul_comm (a m) ((veronese 2 n x) m : ℝ))] at h
    exact h
  have hoy : ∑ m, ((veronese 2 n y) m : ℝ) * a m = 0 := by
    have h := hmem.2
    change Fintype.linearCombination ℝ (fun m => ((veronese 2 n y) m : ℝ)) a = 0 at h
    rw [Fintype.linearCombination_apply] at h
    simp only [smul_eq_mul] at h
    rw [Finset.sum_congr rfl (fun m _ => mul_comm (a m) ((veronese 2 n y) m : ℝ))] at h
    exact h
  have hox' : ∑ m, toR (veronese 2 n x) m * a m = 0 := by simpa [toR] using hox
  have hoy' : ∑ m, toR (veronese 2 n y) m * a m = 0 := by simpa [toR] using hoy
  -- ## Step 3: `c 2 ≠ 0`
  have hRne : c 2 ≠ 0 := by
    intro hR0
    have hae : a = c 0 • toR (veronese 2 n x) + c 1 • toR (veronese 2 n y) := by
      rw [hdecomp, hR0]; simp
    have hsum : ∑ m, a m * a m = 0 := by
      have hpoint : ∀ m, a m * a m
          = c 0 * (toR (veronese 2 n x) m * a m)
            + c 1 * (toR (veronese 2 n y) m * a m) := by
        intro m
        have h1 : a m = c 0 * toR (veronese 2 n x) m + c 1 * toR (veronese 2 n y) m := by
          rw [hae]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nth_rewrite 1 [h1]
        ring
      rw [Finset.sum_congr rfl (fun m _ => hpoint m), Finset.sum_add_distrib]
      rw [show (∑ m, c 0 * (toR (veronese 2 n x) m * a m))
            = c 0 * ∑ m, toR (veronese 2 n x) m * a m from by
          rw [Finset.mul_sum],
        show (∑ m, c 1 * (toR (veronese 2 n y) m * a m))
            = c 1 * ∑ m, toR (veronese 2 n y) m * a m from by
          rw [Finset.mul_sum]]
      rw [hox', hoy']
      ring
    have hz : a = 0 := by
      funext m
      have h1 : a m * a m = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => mul_self_nonneg (a m))).mp hsum m
          (Finset.mem_univ m)
      exact mul_self_eq_zero.mp h1
    exact ha0 hz
  -- ## Step 4: the witness `Z ∈ Γ` and `|c 2| ≥ 1 / 𝒢²`
  obtain ⟨Z, hZGam, hZ⟩ := gam_witness_gcd x y hxy
  have hZx : (∑ m, ((veronese 2 n x) m : ℝ) * (Z m : ℝ)) = 0 := by
    have h := mem_latOrth.mp hZGam.1
    rw [pdot, dotZ] at h
    have h2 : ((∑ m, Z m * veronese 2 n x m : ℤ) : ℝ) = 0 := by rw [h]; norm_num
    rw [← h2]
    push_cast
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have hZy : (∑ m, ((veronese 2 n y) m : ℝ) * (Z m : ℝ)) = 0 := by
    have h := mem_latOrth.mp hZGam.2
    rw [pdot, dotZ] at h
    have h2 : ((∑ m, Z m * veronese 2 n y m : ℤ) : ℝ) = 0 := by rw [h]; norm_num
    rw [← h2]
    push_cast
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have hZz : (∑ m, ((veronese 2 n (x + y)) m : ℝ) * (Z m : ℝ))
      = ((gcdMinors2 x y : ℤ) : ℝ) ^ 2 := by
    have h2 : ((∑ m, veronese 2 n (x + y) m * Z m : ℤ) : ℝ)
        = ((gcdMinors2 x y : ℤ) : ℝ) ^ 2 := by
      rw [hZ]; push_cast; ring
    rw [← h2]
    push_cast
    exact Finset.sum_congr rfl (fun m _ => by ring)
  obtain ⟨k, hk⟩ := ha.2 (intCastPi Z) ⟨Z, hZGam, rfl⟩
  have hk' : ∑ m, a m * (Z m : ℝ) = (k : ℝ) := by simpa [intCastPi] using hk
  have hkey : c 2 * ((gcdMinors2 x y : ℤ) : ℝ) ^ 2 = (k : ℝ) := by
    have hexp : ∑ m, a m * (Z m : ℝ) = c 2 * ((gcdMinors2 x y : ℤ) : ℝ) ^ 2 := by
      conv_lhs => rw [hdecomp]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [show (∑ m, c 0 * toR (veronese 2 n x) m * (Z m : ℝ))
            = c 0 * ∑ m, toR (veronese 2 n x) m * (Z m : ℝ) from by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring),
        show (∑ m, c 1 * toR (veronese 2 n y) m * (Z m : ℝ))
            = c 1 * ∑ m, toR (veronese 2 n y) m * (Z m : ℝ) from by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring),
        show (∑ m, c 2 * toR (veronese 2 n (x + y)) m * (Z m : ℝ))
            = c 2 * ∑ m, toR (veronese 2 n (x + y)) m * (Z m : ℝ) from by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)]
      rw [show (∑ m, toR (veronese 2 n x) m * (Z m : ℝ)) = 0 from by simpa [toR] using hZx,
        show (∑ m, toR (veronese 2 n y) m * (Z m : ℝ)) = 0 from by simpa [toR] using hZy,
        show (∑ m, toR (veronese 2 n (x + y)) m * (Z m : ℝ))
            = ((gcdMinors2 x y : ℤ) : ℝ) ^ 2 from by simpa [toR] using hZz]
      ring
    rw [hexp] at hk'
    exact hk'
  have hGpos : (0 : ℝ) < (gcdMinors2 x y : ℝ) := gcdMinors2_posR x y hxy
  have hRabs : 1 / (gcdMinors2 x y : ℝ) ^ 2 ≤ |c 2| := by
    have hk0 : k ≠ 0 := by
      intro h0
      have h2 : c 2 * ((gcdMinors2 x y : ℤ) : ℝ) ^ 2 = 0 := by rw [hkey, h0]; norm_num
      rcases mul_eq_zero.mp h2 with h | h
      · exact hRne h
      · exact absurd h (pow_ne_zero 2 (by exact_mod_cast ne_of_gt hGpos : ((gcdMinors2 x y : ℤ) : ℝ) ≠ 0))
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have h : (1 : ℤ) ≤ |k| := by
        have := abs_pos.mpr hk0
        omega
      exact_mod_cast h
    have habs : |c 2| * ((gcdMinors2 x y : ℤ) : ℝ) ^ 2 = |(k : ℝ)| := by
      have h := congrArg (fun t : ℝ => |t|) hkey
      rwa [abs_mul, abs_of_nonneg (sq_nonneg ((gcdMinors2 x y : ℤ) : ℝ))] at h
    rw [div_le_iff₀ (pow_pos hGpos 2), habs]
    exact hk1
  -- ## Step 5: the test quadric `σ(u₀,v₀)`
  have hsigGam : sigma n (pairU x y) (pairV x y) ∈ Gam 2 n x y :=
    sigma_mem_Gam x y (pairU x y) (pairV x y) hu0x hv0y
  have hsigx : (∑ m, ((veronese 2 n x) m : ℝ) * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ))
      = 0 := by
    have h := mem_latOrth.mp hsigGam.1
    rw [pdot, dotZ] at h
    have h2 : ((∑ m, sigma n (pairU x y) (pairV x y) m * veronese 2 n x m : ℤ) : ℝ) = 0 := by
      rw [h]; norm_num
    rw [← h2]
    push_cast
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have hsigy : (∑ m, ((veronese 2 n y) m : ℝ) * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ))
      = 0 := by
    have h := mem_latOrth.mp hsigGam.2
    rw [pdot, dotZ] at h
    have h2 : ((∑ m, sigma n (pairU x y) (pairV x y) m * veronese 2 n y m : ℤ) : ℝ) = 0 := by
      rw [h]; norm_num
    rw [← h2]
    push_cast
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have hxu : (∑ i, (x + y) i * pairU x y i) = pairW x y := by
    rw [show (∑ i, (x + y) i * pairU x y i)
        = (∑ i, x i * pairU x y i) + ∑ i, y i * pairU x y i from by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply]; ring),
      show (∑ i, x i * pairU x y i) = 0 from by
        rw [← hu0x]; exact Finset.sum_congr rfl (fun i _ => by ring),
      show (∑ i, y i * pairU x y i) = pairW x y from by
        rw [← hu0y]; exact Finset.sum_congr rfl (fun i _ => by ring)]
    rw [zero_add]
  have hxv : (∑ j, (x + y) j * pairV x y j) = pairW x y := by
    rw [show (∑ j, (x + y) j * pairV x y j)
        = (∑ j, x j * pairV x y j) + ∑ j, y j * pairV x y j from by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by rw [Pi.add_apply]; ring),
      show (∑ j, x j * pairV x y j) = pairW x y from by
        rw [← hv0x]; exact Finset.sum_congr rfl (fun j _ => by ring),
      show (∑ j, y j * pairV x y j) = 0 from by
        rw [← hv0y]; exact Finset.sum_congr rfl (fun j _ => by ring)]
    rw [add_zero]
  have hsigz : (∑ m, ((veronese 2 n (x + y)) m : ℝ)
        * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ)) = (pairW x y : ℝ) ^ 2 := by
    have h2 : ((∑ m, veronese 2 n (x + y) m * sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ)
        = (pairW x y : ℝ) ^ 2 := by
      rw [dot_veronese_sigma n (x + y) (pairU x y) (pairV x y), hxu, hxv]
      push_cast
      ring
    rw [← h2]
    push_cast
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have hpair_tsig : ∑ m, a m * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ)
      = c 2 * (pairW x y : ℝ) ^ 2 := by
    conv_lhs => rw [hdecomp]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [show (∑ m, c 0 * toR (veronese 2 n x) m
            * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ))
          = c 0 * ∑ m, toR (veronese 2 n x) m
              * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ) from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring),
      show (∑ m, c 1 * toR (veronese 2 n y) m
            * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ))
          = c 1 * ∑ m, toR (veronese 2 n y) m
              * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ) from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring),
      show (∑ m, c 2 * toR (veronese 2 n (x + y)) m
            * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ))
          = c 2 * ∑ m, toR (veronese 2 n (x + y)) m
              * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ) from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)]
    rw [show (∑ m, toR (veronese 2 n x) m
            * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ)) = 0 from by
          simpa [toR] using hsigx,
      show (∑ m, toR (veronese 2 n y) m
            * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ)) = 0 from by
          simpa [toR] using hsigy,
      show (∑ m, toR (veronese 2 n (x + y)) m
            * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ)) = (pairW x y : ℝ) ^ 2 from by
          simpa [toR] using hsigz]
    ring
  -- ## Step 6: Cauchy–Schwarz and the norm of `σ(u₀,v₀)`
  have hS2 : rNorm (toR (sigma n (pairU x y) (pairV x y))) ^ 2
      ≤ 2 * (pairA x : ℝ) * (pairA y : ℝ) * (pairW x y : ℝ) ^ 2 := by
    have h := sigma_rNorm_sq_le_aux (pairU x y) (pairV x y)
    rw [hnorU, hnorV] at h
    refine h.trans_eq ?_
    ring
  have hdot : dotR a (toR (sigma n (pairU x y) (pairV x y))) = c 2 * (pairW x y : ℝ) ^ 2 := by
    rw [dotR]
    rw [show (∑ m, a m * toR (sigma n (pairU x y) (pairV x y)) m)
        = ∑ m, a m * ((sigma n (pairU x y) (pairV x y) m : ℤ) : ℝ) from
      Finset.sum_congr rfl (fun m _ => rfl)]
    exact hpair_tsig
  have hcs := Transf.dotR_cauchy a (toR (sigma n (pairU x y) (pairV x y)))
  have hrad : (0 : ℝ) < 2 * (pairA x : ℝ) * (pairA y : ℝ) := by
    have h1 : 0 < (pairA x : ℝ) := by
      rw [← eNorm_sq_pairA_aux x]; exact pow_pos (eNorm_pos_of_ne_zero hxne) 2
    have h2 : 0 < (pairA y : ℝ) := by
      rw [← eNorm_sq_pairA_aux y]; exact pow_pos (eNorm_pos_of_ne_zero hyne) 2
    positivity
  have hKpos : (0 : ℝ) < Real.sqrt (2 * (pairA x : ℝ) * (pairA y : ℝ)) :=
    Real.sqrt_pos.mpr hrad
  have hS_le : rNorm (toR (sigma n (pairU x y) (pairV x y)))
      ≤ Real.sqrt (2 * (pairA x : ℝ) * (pairA y : ℝ)) * (pairW x y : ℝ) := by
    have h1 : rNorm (toR (sigma n (pairU x y) (pairV x y))) ^ 2
        ≤ (Real.sqrt (2 * (pairA x : ℝ) * (pairA y : ℝ)) * (pairW x y : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hrad.le]
      exact hS2
    have h2 := sq_le_sq.mp h1
    rwa [abs_of_nonneg (Transf.rNorm_nonneg _),
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hWnn)] at h2
  -- ## Step 7: the final assembly
  have hbig : |c 2| * (pairW x y : ℝ)
      ≤ rNorm a * Real.sqrt (2 * (pairA x : ℝ) * (pairA y : ℝ)) := by
    have h1 : |c 2| * (pairW x y : ℝ) ^ 2
        ≤ rNorm a * (Real.sqrt (2 * (pairA x : ℝ) * (pairA y : ℝ)) * (pairW x y : ℝ)) := by
      have h2 : |c 2 * (pairW x y : ℝ) ^ 2|
          ≤ rNorm a * rNorm (toR (sigma n (pairU x y) (pairV x y))) := by
        rw [← hdot]; exact hcs
      rw [abs_mul, abs_of_nonneg (sq_nonneg ((pairW x y : ℝ)))] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left hS_le (Transf.rNorm_nonneg _))
    rcases eq_or_lt_of_le hWnn with h0 | hpos
    · rw [← h0, mul_zero]
      exact mul_nonneg (Transf.rNorm_nonneg a) (Real.sqrt_nonneg _)
    · refine le_of_mul_le_mul_right ?_ hpos
      nlinarith [h1]
  have hKpos' : (0 : ℝ) < Real.sqrt 2 * eNorm x * eNorm y := by
    have h1 : 0 < eNorm x := eNorm_pos_of_ne_zero hxne
    have h2 : 0 < eNorm y := eNorm_pos_of_ne_zero hyne
    have h3 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact mul_pos (mul_pos h3 h1) h2
  have hK_eq : Real.sqrt (2 * (pairA x : ℝ) * (pairA y : ℝ))
      = Real.sqrt 2 * eNorm x * eNorm y := by
    have hsq : (Real.sqrt 2 * eNorm x * eNorm y) ^ 2
        = 2 * (pairA x : ℝ) * (pairA y : ℝ) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        eNorm_sq_pairA_aux x, eNorm_sq_pairA_aux y]
    rw [← hsq, Real.sqrt_sq hKpos'.le]
  have hstep1 : |c 2| * (pairW x y : ℝ) / (Real.sqrt 2 * eNorm x * eNorm y) ≤ rNorm a := by
    rw [div_le_iff₀ hKpos', ← hK_eq]
    exact hbig
  have hstep2 : (1 / (gcdMinors2 x y : ℝ) ^ 2) * (pairW x y : ℝ)
        / (Real.sqrt 2 * eNorm x * eNorm y) ≤ rNorm a := by
    have haux : 0 ≤ (pairW x y : ℝ) / (Real.sqrt 2 * eNorm x * eNorm y) :=
      div_nonneg hWnn hKpos'.le
    calc (1 / (gcdMinors2 x y : ℝ) ^ 2) * (pairW x y : ℝ)
          / (Real.sqrt 2 * eNorm x * eNorm y)
        = (1 / (gcdMinors2 x y : ℝ) ^ 2)
            * ((pairW x y : ℝ) / (Real.sqrt 2 * eNorm x * eNorm y)) := by ring
      _ ≤ |c 2| * ((pairW x y : ℝ) / (Real.sqrt 2 * eNorm x * eNorm y)) :=
            mul_le_mul_of_nonneg_right hRabs haux
      _ = |c 2| * (pairW x y : ℝ) / (Real.sqrt 2 * eNorm x * eNorm y) := by ring
      _ ≤ rNorm a := hstep1
  rw [wedgeNorm_sq_pairW_aux x y]
  have hg2 : (gcdMinors2 x y : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hGpos)
  have hex0 : eNorm x ≠ 0 := ne_of_gt (eNorm_pos_of_ne_zero hxne)
  have hey0 : eNorm y ≠ 0 := ne_of_gt (eNorm_pos_of_ne_zero hyne)
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  refine le_trans (le_of_eq ?_) hstep2
  field_simp

end Work.HP.Vero
