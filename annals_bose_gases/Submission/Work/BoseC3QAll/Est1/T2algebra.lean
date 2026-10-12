import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.Est1.Algebra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.T2algebra` — the commutators of the `T₂` estimate

The algebra of FS's estimate of `T₂(k)` (lines 3058–3230 of
`Papers/fournais_solovej/final_v2.tex`), where the shift

`Y_k = (z/ℓ³) Σ_s γ_{sk} b_{s-k}† Ã_s`,  `Ã_s = ã_s + α_kα_{s-k}ã_{-s}†`

is squared and the factors commuted past each other.  Identities, all valid for
*arbitrary* mode indices (so they cover both the `T₂,comm` and the `T₂,op` parts,
with the substitutions `p = s'-k`, `q = s-k`):

* `taDag_aDag_comm` — `[ã_s†, a_p†] = 0` (a consequence of
  `Work.BoseB7A.TildeData.ta_a_comm`, by adjointness);
* `bOp_comp_bOpDag` — **the squeezed commutator**
  `[b_p, b_q†] = (1-α_pα_q)(χ̂²(p-q) - χ̂_pχ̂_q) • 1`, i.e. FS `eq:bcommutator`
  (it uses `hasKernel` and the parities of `χ̂`, `χ̂²`; unlike
  `Work.BoseB7.bCommutator_eq` it is *not* restricted to the pair `(s-k, -k)`);
* `Atil_comp_bOpDag`, `Atil_comp_bOp`, `AtilDag_comp_bOp`,
  `AtilDag_comp_bOpDag` — the four `Ã`/`b` commutators, each a *scalar* multiple
  of the identity (FS's `𝒞` of `eq:StoerrelseC`): these are what makes the
  Cauchy–Schwarz of FS's estimate of `T₂,op'` (and the `T₂''` term) work.

Only the commutation package of `FockData`/`TildeData` is used
(`F.ccr`, `F.ann_comm`, `F.cre_comm`, `T.ta_comm`, `T.ta_a_comm`, `T.ta_aDag`,
`Est1.taDag_a_comm`, `Est1.a_taDag_comm`); `bOp_comp_bOpDag` additionally uses
`hasKernel` and the parities.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode}

/-- `[ã_s†, a_p†] = 0`: `ã_s†` commutes with every creation operator.  This is
the adjoint (`Est1.bp_ext`) of `Work.BoseB7A.TildeData.ta_a_comm`. -/
theorem taDag_aDag_comm (T : TildeData F) (s p : Mode) :
    T.taDag s ∘ₗ F.aDag p = F.aDag p ∘ₗ T.taDag s := by
  refine bp_ext _ _ fun f g => ?_
  bp_norm
  have h : F.a p (T.ta s g) = T.ta s (F.a p g) := by
    simpa only [LinearMap.comp_apply] using (LinearMap.congr_fun (T.ta_a_comm s p) g).symm
  rw [h]

/-- **The general squeezed commutator** `[b_p, b_q†]`: for every pair of modes,

`b_p b_q† = b_q† b_p + (1-α_pα_q)(χ̂²(p-q) - χ̂_pχ̂_q) • 1`

(`hasKernel` identifies the box commutator `[a_i,a_j†] = ccrK i j`; the parities
of `χ̂`, `χ̂²` make `ccrK (-q) (-p) = χ̂²(p-q) - χ̂_qχ̂_p`).  FS `eq:bcommutator`
is the case `p = s'-k`, `q = s-k`. -/
theorem bOp_comp_bOpDag (E : Q3Env Mode)
    (hker : ∀ i j : Mode, F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j)
    (hχ : ∀ s : Mode, E.hatChi (-s) = E.hatChi s)
    (hχSq : ∀ s : Mode, E.hatChiSq (-s) = E.hatChiSq s) (p q : Mode) :
    F.bOp E.alpha p ∘ₗ F.bOpDag E.alpha q
      = F.bOpDag E.alpha q ∘ₗ F.bOp E.alpha p
        + ((1 - E.alpha p * E.alpha q) *
            (E.hatChiSq (p - q) - E.hatChi p * E.hatChi q)) • (1 : F.H →ₗ[ℝ] F.H) := by
  have h1 : F.a p ∘ₗ F.aDag q
      = F.aDag q ∘ₗ F.a p + (F.ccrK p q) • (1 : F.H →ₗ[ℝ] F.H) := F.ccr p q
  have h2 : F.a p ∘ₗ F.a (-q) = F.a (-q) ∘ₗ F.a p := F.ann_comm p (-q)
  have h3 : F.aDag (-p) ∘ₗ F.aDag q = F.aDag q ∘ₗ F.aDag (-p) := F.cre_comm (-p) q
  have h4 : F.aDag (-p) ∘ₗ F.a (-q)
      = F.a (-q) ∘ₗ F.aDag (-p) - (F.ccrK (-q) (-p)) • (1 : F.H →ₗ[ℝ] F.H) := by
    have h := F.ccr (-q) (-p)
    rw [h]
    abel
  have hcoef : F.ccrK p q - E.alpha p * E.alpha q * F.ccrK (-q) (-p)
      = (1 - E.alpha p * E.alpha q) * (E.hatChiSq (p - q) - E.hatChi p * E.hatChi q) := by
    rw [hker p q, hker (-q) (-p)]
    have e1 : (-q) - (-p) = p - q := by abel
    rw [e1, hχ q, hχ p]
    ring
  rw [FockData.bOp, FockData.bOpDag]
  simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul, LinearMap.smul_comp,
    smul_eq_mul]
  rw [h1, h2, h3, h4, ← hcoef]
  module

/-- `[Ã_s, b_q†] = ccrX s q - α_kα_{s-k}·α_q·ccrX (-s) (-q)` (a scalar). -/
theorem Atil_comp_bOpDag (T : TildeData F) (E : Q3Env Mode) (s k q : Mode) :
    Atil F T E s k ∘ₗ F.bOpDag E.alpha q
      = F.bOpDag E.alpha q ∘ₗ Atil F T E s k
        + (T.ccrX s q - bA E s k * E.alpha q * T.ccrX (-s) (-q)) •
            (1 : F.H →ₗ[ℝ] F.H) := by
  have h1 : T.ta s ∘ₗ F.aDag q = F.aDag q ∘ₗ T.ta s + (T.ccrX s q) • (1 : F.H →ₗ[ℝ] F.H) :=
    T.ta_aDag s q
  have h2 : T.ta s ∘ₗ F.a (-q) = F.a (-q) ∘ₗ T.ta s := T.ta_a_comm s (-q)
  have h3 : T.taDag (-s) ∘ₗ F.aDag q = F.aDag q ∘ₗ T.taDag (-s) :=
    taDag_aDag_comm T (-s) q
  have h4 : T.taDag (-s) ∘ₗ F.a (-q)
      = F.a (-q) ∘ₗ T.taDag (-s) - (T.ccrX (-s) (-q)) • (1 : F.H →ₗ[ℝ] F.H) :=
    taDag_a_comm T (-s) (-q)
  rw [Atil, FockData.bOpDag, bA]
  simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul, LinearMap.smul_comp,
    smul_eq_mul]
  rw [h1, h2, h3, h4]
  module

/-- `[Ã_s, b_q] = α_q·ccrX s (-q) - α_kα_{s-k}·ccrX (-s) q` (a scalar). -/
theorem Atil_comp_bOp (T : TildeData F) (E : Q3Env Mode) (s k q : Mode) :
    Atil F T E s k ∘ₗ F.bOp E.alpha q
      = F.bOp E.alpha q ∘ₗ Atil F T E s k
        + (E.alpha q * T.ccrX s (-q) - bA E s k * T.ccrX (-s) q) •
            (1 : F.H →ₗ[ℝ] F.H) := by
  have h1 : T.ta s ∘ₗ F.a q = F.a q ∘ₗ T.ta s := T.ta_a_comm s q
  have h2 : T.ta s ∘ₗ F.aDag (-q) = F.aDag (-q) ∘ₗ T.ta s + (T.ccrX s (-q)) •
      (1 : F.H →ₗ[ℝ] F.H) := T.ta_aDag s (-q)
  have h3 : T.taDag (-s) ∘ₗ F.a q
      = F.a q ∘ₗ T.taDag (-s) - (T.ccrX (-s) q) • (1 : F.H →ₗ[ℝ] F.H) :=
    taDag_a_comm T (-s) q
  have h4 : T.taDag (-s) ∘ₗ F.aDag (-q) = F.aDag (-q) ∘ₗ T.taDag (-s) :=
    taDag_aDag_comm T (-s) (-q)
  rw [Atil, FockData.bOp, bA]
  simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul, LinearMap.smul_comp,
    smul_eq_mul]
  rw [h1, h2, h3, h4]
  module

/-- `[Ã_s†, b_q†] = -α_q·ccrX s (-q) + α_kα_{s-k}·ccrX (-s) q` (a scalar). -/
theorem AtilDag_comp_bOpDag (T : TildeData F) (E : Q3Env Mode) (s k q : Mode) :
    AtilDag F T E s k ∘ₗ F.bOpDag E.alpha q
      = F.bOpDag E.alpha q ∘ₗ AtilDag F T E s k
        + (-(E.alpha q * T.ccrX s (-q)) + bA E s k * T.ccrX (-s) q) •
            (1 : F.H →ₗ[ℝ] F.H) := by
  have h1 : T.taDag s ∘ₗ F.aDag q = F.aDag q ∘ₗ T.taDag s := taDag_aDag_comm T s q
  have h2 : T.taDag s ∘ₗ F.a (-q)
      = F.a (-q) ∘ₗ T.taDag s - (T.ccrX s (-q)) • (1 : F.H →ₗ[ℝ] F.H) :=
    taDag_a_comm T s (-q)
  have h3 : T.ta (-s) ∘ₗ F.aDag q = F.aDag q ∘ₗ T.ta (-s) + (T.ccrX (-s) q) •
      (1 : F.H →ₗ[ℝ] F.H) := T.ta_aDag (-s) q
  have h4 : T.ta (-s) ∘ₗ F.a (-q) = F.a (-q) ∘ₗ T.ta (-s) := T.ta_a_comm (-s) (-q)
  rw [AtilDag, FockData.bOpDag, bA]
  simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul, LinearMap.smul_comp,
    smul_eq_mul]
  rw [h1, h2, h3, h4]
  module

/-- `[Ã_s†, b_q] = -ccrX s q + α_kα_{s-k}·α_q·ccrX (-s) (-q)` (a scalar). -/
theorem AtilDag_comp_bOp (T : TildeData F) (E : Q3Env Mode) (s k q : Mode) :
    AtilDag F T E s k ∘ₗ F.bOp E.alpha q
      = F.bOp E.alpha q ∘ₗ AtilDag F T E s k
        + (-(T.ccrX s q) + bA E s k * E.alpha q * T.ccrX (-s) (-q)) •
            (1 : F.H →ₗ[ℝ] F.H) := by
  have h1 : T.taDag s ∘ₗ F.a q
      = F.a q ∘ₗ T.taDag s - (T.ccrX s q) • (1 : F.H →ₗ[ℝ] F.H) :=
    taDag_a_comm T s q
  have h2 : T.taDag s ∘ₗ F.aDag (-q) = F.aDag (-q) ∘ₗ T.taDag s :=
    taDag_aDag_comm T s (-q)
  have h3 : T.ta (-s) ∘ₗ F.a q = F.a q ∘ₗ T.ta (-s) := T.ta_a_comm (-s) q
  have h4 : T.ta (-s) ∘ₗ F.aDag (-q) = F.aDag (-q) ∘ₗ T.ta (-s) +
      (T.ccrX (-s) (-q)) • (1 : F.H →ₗ[ℝ] F.H) := T.ta_aDag (-s) (-q)
  rw [AtilDag, FockData.bOp, bA]
  simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul, LinearMap.smul_comp,
    smul_eq_mul]
  rw [h1, h2, h3, h4]
  module

/-! ## 2. The pointwise forms (for rewriting at the level of states) -/

/-- The pointwise form of `taDag_aDag_comm`. -/
theorem taDag_aDag_comm_apply (T : TildeData F) (s p : Mode) (y : F.H) :
    T.taDag s (F.aDag p y) = F.aDag p (T.taDag s y) :=
  LinearMap.congr_fun (taDag_aDag_comm T s p) y

/-- The pointwise form of the squeezed commutator `bOp_comp_bOpDag`
(FS `eq:bcommutator`, in the form in which it is used). -/
theorem bOp_comp_bOpDag_apply (E : Q3Env Mode)
    (hker : ∀ i j : Mode, F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j)
    (hχ : ∀ s : Mode, E.hatChi (-s) = E.hatChi s)
    (hχSq : ∀ s : Mode, E.hatChiSq (-s) = E.hatChiSq s) (p q : Mode) (y : F.H) :
    F.bOp E.alpha p (F.bOpDag E.alpha q y)
      = F.bOpDag E.alpha q (F.bOp E.alpha p y)
        + ((1 - E.alpha p * E.alpha q) *
            (E.hatChiSq (p - q) - E.hatChi p * E.hatChi q)) • y :=
  LinearMap.congr_fun (bOp_comp_bOpDag E hker hχ hχSq p q) y

/-- The pointwise form of `Atil_comp_bOpDag`. -/
theorem Atil_comp_bOpDag_apply (T : TildeData F) (E : Q3Env Mode) (s k q : Mode) (y : F.H) :
    Atil F T E s k (F.bOpDag E.alpha q y)
      = F.bOpDag E.alpha q (Atil F T E s k y)
        + (T.ccrX s q - bA E s k * E.alpha q * T.ccrX (-s) (-q)) • y :=
  LinearMap.congr_fun (Atil_comp_bOpDag T E s k q) y

/-- The pointwise form of `Atil_comp_bOp`. -/
theorem Atil_comp_bOp_apply (T : TildeData F) (E : Q3Env Mode) (s k q : Mode) (y : F.H) :
    Atil F T E s k (F.bOp E.alpha q y)
      = F.bOp E.alpha q (Atil F T E s k y)
        + (E.alpha q * T.ccrX s (-q) - bA E s k * T.ccrX (-s) q) • y :=
  LinearMap.congr_fun (Atil_comp_bOp T E s k q) y

/-- The pointwise form of `AtilDag_comp_bOpDag`. -/
theorem AtilDag_comp_bOpDag_apply (T : TildeData F) (E : Q3Env Mode) (s k q : Mode) (y : F.H) :
    AtilDag F T E s k (F.bOpDag E.alpha q y)
      = F.bOpDag E.alpha q (AtilDag F T E s k y)
        + (-(E.alpha q * T.ccrX s (-q)) + bA E s k * T.ccrX (-s) q) • y :=
  LinearMap.congr_fun (AtilDag_comp_bOpDag T E s k q) y

/-- The pointwise form of `AtilDag_comp_bOp`. -/
theorem AtilDag_comp_bOp_apply (T : TildeData F) (E : Q3Env Mode) (s k q : Mode) (y : F.H) :
    AtilDag F T E s k (F.bOp E.alpha q y)
      = F.bOp E.alpha q (AtilDag F T E s k y)
        + (-(T.ccrX s q) + bA E s k * E.alpha q * T.ccrX (-s) (-q)) • y :=
  LinearMap.congr_fun (AtilDag_comp_bOp T E s k q) y

/-! ## 3. The scalar lattice sum `ℓ⁻³Σ_{P_H}Ŵ₁²/𝒟 ≤ 2Ŵ₁ω(0)`

FS `eq:EstimT2comm`: `(2π)⁻³∫_{P_H}Ŵ₁(k)²/𝒟_k dk ≈ 2Ŵ₁ω(0)`, with the error
`2K₀aK_H⁻¹` of `Q3KernelFSAll.intOne` (the `ρ_z` cancels through
`Ŵ₁(k)α_k = ρ_zŴ₁(k)²/(2𝒟_k)`, `Work.BoseB7.W1_mul_alpha_eq`). -/

/-- **The lattice sum of `Ŵ₁²/𝒟` over `P_H`.**  This is the coefficient with
which FS's `T₂,comm` main term `2ρ_zŴ₁ω(0)⟨G⟩` is produced. -/
theorem sum_W1sq_divD_le (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (hv : FSParamsView E) (hK : Q3KernelFSAll K₀ F T E) :
    E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k ^ 2 / E.D k)
      ≤ 2 * E.W1omega0 + 2 * K₀ * E.aScat * E.KH⁻¹ := by
  have hρ : 0 < E.rho := rho_pos E hv
  -- the pointwise `α ↔ 𝒟` identity of FS `eq:CompIntegrals-Final-2`
  have hpoint : ∀ k ∈ F.PHset E,
      E.W1 k ^ 2 / E.D k = 2 / E.rho * (E.W1 k * E.alpha k) := by
    intro k _
    have h := W1_mul_alpha_eq E (hK.B_eq k)
    rw [h]
    field_simp
  have hsum : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / E.D k
      = (2 / E.rho) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk => hpoint k hk
  -- `intOne`, in the direction giving an upper bound for the sum
  have hle : E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k * E.alpha k)
      ≤ E.rho * E.W1omega0 + K₀ * E.rho * E.aScat * E.KH⁻¹ := by
    have h := (abs_le.mp hK.intOne).1
    linarith
  calc E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k ^ 2 / E.D k)
      = (2 / E.rho) * (E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ F.PHset E, E.W1 k * E.alpha k) := by
        rw [hsum]; ring
    _ ≤ (2 / E.rho) * (E.rho * E.W1omega0 + K₀ * E.rho * E.aScat * E.KH⁻¹) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 2 * E.W1omega0 + 2 * K₀ * E.aScat * E.KH⁻¹ := by
        field_simp

end Est1

end Work.BoseC3QAll
