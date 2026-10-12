import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.Est1.Algebra
import Submission.Work.BoseC3QAll.Prep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.T2bounds` — two bounds of the `T₂` split

Two small facts used by piece **B** (`Est1.estT2sum`) that are not in the
workspace yet:

* `Gop_qw_le` — **`⟨Φ, G Φ⟩ ≤ K₀⟨n₊Φ,Φ⟩`**: the Schur half of
  `Q3KernelFSAll.hatChiSq_form` (with `S = excited Mode`, `c = f_L`, `v s = ã_sΦ`)
  together with `f_L ≤ 1`, `f_L ≥ 0` and `Work.BoseB7A.TildeData.ta_le_N`.  This is what pays
  FS's `Gop`-coefficient excess (`(1+C𝓁²+Cε_T^{-1}(dK_ℓ)²)`) from the `ℓ⁻²n₊`
  half of the energy gap — see `Est1/estT2sum_plan.md` §7 (this formalisation's
  `TildeData` has no field relating `NH` to high momenta, so FS's `ε`-split into
  `n₊^H` is not available).
* `mu_mul_aScat_eq` — **`μa = K_ℓ²ℓ⁻²`**, the identity behind FS's remark
  "notice that `μa = (dK_ℓ)²/(d²ℓ²)`": since `ℓ = K_ℓ(μa)^{-1/2}` (`ell_eq`),
  every comparison in which `μa` and `ℓ` occur together is really a comparison in
  the dimensionless parameter `X = (μa³)^{1/323}` alone.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode}

/-- `0 ≤ K₀` whenever `Q3KernelFSAll K₀ F T E` holds at FS's parameter point: the
lattice count `count_PL` bounds the (nonnegative) cardinality of the low-momentum
support by `K₀(K_ℓK_L)³` with `K_ℓK_L ≥ 1`. -/
theorem K₀_nonneg_of_kernel (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (hv : FSParamsView E) (hK : Q3KernelFSAll K₀ F T E) : 0 ≤ K₀ := by
  by_contra hneg
  have hneg' : K₀ < 0 := not_le.mp hneg
  have hcp := hK.count_PL
  have hcard : (0 : ℝ) ≤ (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hKl : 0 < E.Kl := by linarith [hv.one_le_Kl]
  have hKL : 0 < E.KL := by linarith [hv.one_le_KL]
  have hpos : 0 < (E.Kl * E.KL) ^ 3 := pow_pos (mul_pos hKl hKL) 3
  have hneg2 : K₀ * (E.Kl * E.KL) ^ 3 < 0 := mul_neg_of_neg_of_pos hneg' hpos
  linarith

/-- **`⟨Φ, G Φ⟩ ≤ K₀⟨n₊Φ,Φ⟩`**, where `G = T.Gop E` is FS's
`eq:RepInTermsOfatilde` operator `Σ_{s,s'}f_L(s)f_L(s')χ̂²((s'-s)ℓ)ã_{s'}†ã_s`.
This is the bound that makes the `Gop`-coefficient excess of FS's `T₂,comm`
payable from the `ℓ⁻²n₊` half of the energy gap. -/
theorem Gop_qw_le (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (hv : FSParamsView E) (hK : Q3KernelFSAll K₀ F T E) (Φ : F.H) :
    F.qw Φ (T.Gop E) ≤ K₀ * F.bp (T.N Φ) Φ := by
  have hK0 : 0 ≤ K₀ := K₀_nonneg_of_kernel K₀ F T E hv hK
  -- the Schur half of `Q3KernelFSAll.hatChiSq_form`
  have hform := (hK.hatChiSq_form (excited Mode) E.fL (fun s => T.ta s Φ)
    (fun s hs h => h)).2
  -- the left-hand side, in the shape of `hform`
  have hleft : F.qw Φ (T.Gop E)
      = ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * E.hatChiSq (s' - s) * F.bp (T.ta s' Φ) (T.ta s Φ) := by
    simp only [FockData.qw, Work.BoseB7A.TildeData.Gop, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, bp_taDag_left]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [F.bp_symm (T.ta s Φ) (T.ta s' Φ)]
  -- `Σ_s f_L(s)²⟨ã_sΦ,ã_sΦ⟩ ≤ ⟨n₊Φ,Φ⟩`
  have hright : ∑ s ∈ excited Mode, E.fL s ^ 2 * F.bp (T.ta s Φ) (T.ta s Φ)
      ≤ F.bp (T.N Φ) Φ := by
    have hstep : ∀ s ∈ excited Mode,
        E.fL s ^ 2 * F.bp (T.ta s Φ) (T.ta s Φ) ≤ F.bp (T.ta s Φ) (T.ta s Φ) := by
      intro s _
      have h1 : E.fL s ^ 2 ≤ 1 := by nlinarith [hK.fL_nonneg s, hK.fL_le_one s]
      exact mul_le_of_le_one_left (F.bp_nonneg _) h1
    calc ∑ s ∈ excited Mode, E.fL s ^ 2 * F.bp (T.ta s Φ) (T.ta s Φ)
        ≤ ∑ s ∈ excited Mode, F.bp (T.ta s Φ) (T.ta s Φ) := Finset.sum_le_sum hstep
      _ = F.bp ((∑ s ∈ excited Mode, T.taDag s ∘ₗ T.ta s) Φ) Φ := by
          simp only [map_sum, LinearMap.sum_apply, LinearMap.comp_apply, bp_taDag_left]
      _ ≤ F.bp (T.N Φ) Φ :=
          T.ta_le_N (excited Mode) (fun s hs => (Finset.mem_erase.mp hs).1) Φ
  calc F.qw Φ (T.Gop E)
      = ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * E.hatChiSq (s' - s) * F.bp (T.ta s' Φ) (T.ta s Φ) := hleft
    _ ≤ K₀ * ∑ s ∈ excited Mode, E.fL s ^ 2 * F.bp (T.ta s Φ) (T.ta s Φ) := hform
    _ ≤ K₀ * F.bp (T.N Φ) Φ := mul_le_mul_of_nonneg_left hright hK0

/-- **`μa = K_ℓ²/ℓ²`** (FS: "notice that `μa = (dK_ℓ)²/(d²ℓ²)`"), from
`ℓ = K_ℓ(μa)^{-1/2}` (`FSParamsView.ell_eq`). -/
theorem mu_mul_aScat_eq (E : Q3Env Mode) (hv : FSParamsView E) :
    E.mu * E.aScat = E.Kl ^ 2 / E.ell ^ 2 := by
  have hμ : 0 < E.mu := mu_pos E hv
  have ha : 0 < E.aScat := hv.a_pos
  have hKl : 0 < E.Kl := lt_of_lt_of_le zero_lt_one hv.one_le_Kl
  have hμa : 0 < E.mu * E.aScat := mul_pos hμ ha
  have hell : E.ell = E.Kl * (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) := by
    rw [hv.ell_eq, side]
  have hsq : ((E.mu * E.aScat) ^ (-(1 / 2 : ℝ))) ^ 2 = (E.mu * E.aScat) ^ (-(1 : ℝ)) := by
    rw [sq, ← Real.rpow_add hμa]
    norm_num
  rw [hell, mul_pow, hsq, Real.rpow_neg_one]
  field_simp

end Est1

end Work.BoseC3QAll
