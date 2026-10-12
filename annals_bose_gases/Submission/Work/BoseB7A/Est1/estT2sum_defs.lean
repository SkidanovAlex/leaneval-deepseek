import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7A.Est1.T2bounds
import Submission.Work.BoseB7A.errA_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Est1.estT2sum_defs` — the split of `Σ_k c_k⁻¹‖Y_kΦ‖²`

Piece **B** of FS `eq:EstimateQ3Tilde1` (`Est1.estT2sum`) bounds the shift sum

  `Σ_{k∈P_H} c_k⁻¹ ‖Y_kΦ‖²`,  `c_k = cD E k = (1-𝓁²)𝒟_k`,
  `Y_k = (z/ℓ³) Σ_{s∈excited} γ_{sk} · (b_{s-k}† ∘ Ã_{sk})`,
  `γ_{sk} = gA E s k = f_L(s)Ŵ₁(k)q3Denom(s,k)`, `Ã_{sk} = ta s + (α_kα_{s-k}) taDag(-s)`.

This module performs the *first step* of FS's `T₂` analysis: the algebraic split of
`‖Y_kΦ‖²` into the **commutator** (`χ̂²`, FS `T₂,comm`) and the **normal-ordered**
(`T₂,op`) parts.

## The algebra

With `Z = z/ℓ³`, `A_s = Atil F T E s k`, `b_p = F.bOp E.alpha p`,
`b_p† = F.bOpDag E.alpha p`, the bilinearity of `F.bp` and the adjointness
`bp (b_p† u) g = bp u (b_p g)` give

  `‖Y_kΦ‖² = Z² Σ_{s,s'} γ_{sk}γ_{s'k} · bp (A_sΦ, b_{s-k} b_{s'-k}† A_{s'}Φ)`

and, commuting `b_{s-k}` past `b_{s'-k}†` by the squeezed commutator
(`b_p b_q† = b_q† b_p + [b_p,b_q†]`, a scalar multiple of the identity),

  `= Z² (T2ComF F T E k Φ + T2OpF F T E k Φ)`

with the two halves defined below.  The scalar commutator is

  `kCom F E s s' k = [b_{s-k}, b_{s'-k}†] = ccrK (s-k) (s'-k) - α_{s-k}α_{s'-k}ccrK (k-s) (k-s')`,

which under `Q3Kernel.hasKernel` and the evenness of `α, χ̂, χ̂²` is FS's
`eq:bComms2` value

  `kCom = (1 - α_{s-k}α_{s'-k})·(χ̂²(s-s') - χ̂(s-k)χ̂(s'-k))`
  (`kCom_eq`).

## The two estimates (FS lines 3058–3230)

**Both pieces are stated for `Z²·Σ_k c_k⁻¹ · (·)`, i.e. for the *physical*
quantities** (this is the form the assembly `Est1.estQ3oneA_of_pieces` consumes;
`Z² = (z/ℓ³)² = ρ_z/ℓ³`, so `Z²·Σ_k c_k⁻¹ W₁(k)²/𝒟_k = 2ρ_zΞ` with `Ξ` the
lattice sum of `eq:CompIntegrals-Final-2` — *this* is what makes the coefficient
come out as `2ρ_zŴ₁ω(0)` and not `2ℓ³Ŵ₁ω(0)`).

* **`estT2sum_com`** — the `χ̂²` part (FS `eq:EstimT2comm`).  The target is

  `Z² Σ_{k∈P_H} c_k⁻¹ T2ComF k Φ ≤ 2ρ_zŴ₁ω(0)·qw Φ (T.Gop E) + C·e1A·‖Φ‖²
      + (b/400)·qw Φ (T.gapOpT E) + (𝓁²/8)·qw Φ (R_{P_H^q})`.

  Route: `kCom = (1-α α)(χ̂² - χ̂χ̂)` (`kCom_eq`), so `T2ComF` splits into the
  `χ̂²` part and the `χ̂χ̂` part.
  * The `χ̂χ̂` part: `|χ̂(s-k)χ̂(s'-k)| ≤ K₀η·1` (`hatChi_small`, `hatChi_le`) since
    `s-k ∈ P_H^q`; then Cauchy–Schwarz in `(s,s')` (`2uv ≤ u²+v²`) and the
    window (`Σ_s f_L(s)‖Ã_{sk}Φ‖² ≤ C(1+β²)(𝓜+1)‖Φ‖²`, via `NWindow_ta_sum`,
    `ta_le_N`, `NWindow_bp_N_le`) give `≤ C ρ_z a³ η (K_ℓK_L)³ 𝓜 ‖Φ‖²`, which is
    far below `C e1A‖Φ‖²` (`e1A ≥ E0·fsXp t 2566`).
  * The `χ̂²` part: its coefficient is
    `Λ_{ss'} = Z² Σ_{k∈P_H} c_k⁻¹ γ_{sk}γ_{s'k}(1-α_{s-k}α_{s'-k})`, and
    `q3Denom·q3Denom·(1-αα) ≤ 1 + C(K₀)𝓁²` on `P_H^q` (`q3Denom_le_four` is too
    lossy here: use `kernel_basic`'s `|α| ≤ 64K₀𝓁`, `1-α² ≥ 1/2`, and
    `1/(1-x²) ≤ 1+2x²` for `|x| ≤ 1/2`).  With `Ξ := Xi F E` and `Xi_bound`
    (`|Ξ - Ŵ₁ω(0)| ≤ K₀aK_H⁻¹`, proved here):

    `Λ_{ss'} ≤ 2ρ_z(Ŵ₁ω(0) + K₀aK_H⁻¹)(1+C𝓁²)·f_L(s)f_L(s')`,

    so the `χ̂²` part is at most `2ρ_z(Ŵ₁ω0 + K₀aK_H⁻¹)(1+C𝓁²)·F_A` with
    `F_A = Σ_{ss'}f_L(s)f_L(s')χ̂²(s-s')bp(Ã_{sk}Φ, Ã_{s'k}Φ)`.
  * Compare `F_A` with `qw Φ (T.Gop E) = Σ_{ss'}f_Lf_L'χ̂²(s-s')bp(ã_sΦ,ã_{s'}Φ)`:
    substituting `Ã = ã + βã†` produces three correction terms (of size
    `|β| ≤ 4096K₀²𝓁²` times `K₀(⟨N⟩ + 𝓜‖Φ‖² + (K_ℓK_L)³‖Φ‖²)`, the `+1` per
    mode from `ã_sã_s† = ã_s†ã_s + 1`), all dominated by
    `2ρ_zK₀a·(small)·(𝓜‖Φ‖²)` and hence payable from the **gap**
    `(b/400)ℓ⁻²⟨n₊⟩` (`b₀ > 0` is the only input needed) or from `e1A`.
  * The deficit `2ρ_zK₀aK_H⁻¹F_A`: use `F_A ≤ K₀(1+β²)(‖n₊Φ‖² + (K_ℓK_L)³‖Φ‖²)`
    (the Schur half of `hatChiSq_form`, `ta_le_N`); the `⟨n₊⟩`-part is paid by the
    gap (or by `e1A`'s `1/b`-term, depending on the size of `E.b`), the constant
    part by `e1A` (it is `≤ Cρ_zK₀²aK_H⁻¹𝓁²(K_ℓK_L)³‖Φ‖² ≤ Ce1A‖Φ‖²`).

* **`estT2sum_op`** — the normal-ordered part (`eq:T2opprime`).  Route: `T2OpF`
  is a symmetric double sum with `γ_sγ_{s'} ≥ 0` (`f_L ≥ 0`, `q3Denom > 0`), so
  `2uv ≤ u²+v²` gives
  `|T2OpF k| ≤ (Σ_s|γ_{sk}|)(Σ_{s'}|γ_{s'k}|·M_{s'})` with
  `M_{s'} = sup_{s}‖b_{s-k}(Ã_{s'k}Φ)‖²`; `‖b_q v‖² ≤ C(⟨v,Nv⟩ + ‖v‖²)`
  (`b_q = a_q + α_qa_{-q}†`, `a_q†a_q ≤ n₊`, `a_{-q}a_{-q}† = a_{-q}†a_{-q} +
  ccrK(-q)(-q)`) makes `M_{s'}` `k`-free, and the window
  (`NWindow_bp_N_le`, `NWindow_ta_sum`) bounds `‖A_{s'}Φ‖²`-sums by
  `C(1+β²)(𝓜+1)‖Φ‖²`.  The `k`-sum is then controlled by
  `Σ_{k∈P_H}W₁(k)²/𝒟_k ≤ 4ℓ³K₀a` (`sum_W1sq` + `𝒟 ≥ ‖·‖²/4`; **never** by
  counting `P_H`, which is not an interface field) — giving
  `Z²Σ_kc_k⁻¹T2OpF ≤ Cρ_za³K₀⁴(K_ℓK_L)³(𝓜+1)²‖Φ‖² ≪ e1A‖Φ‖²`.
  (The reserve `(𝓁²/8)⟨R_{P_H^q}⟩` is offered as extra slack: it is the term FS
  use, via the injectivity of `k ↦ s-k` and `PH_subset_PHq_sub`.)

## Contents

* `kCom`, `kCom_eq` — the squeezed commutator scalar and its `χ̂, χ̂²` form.
* `T2ComF`, `T2OpF` — the two halves of `‖Y_kΦ‖²/Z²`.
* `Xi` and `Xi_bound` — the `P_H` lattice sum `ℓ⁻³Σ W₁(k)²/(2𝒟_k)` and its comparison
  with `Ŵ₁ω(0)` (the only sharp ingredient of the `χ̂²` part).
* `z_div_ell_cube_sq` — `(z/ℓ³)² = ρ_z/ℓ³`.

## Scalar helpers of piece **B** (imported here, so they are in scope)

`Est1.mu_mul_a_eq` (`μa = K_ℓ²/ℓ²`), `Est1.E0_eq`/`Est1.E0_eq_rpow`
(`E0 = X^{-166}K_ℓ²ℓ⁻²`), `Est1.e1A_ge_inv_b` (`e1A ≥ E0·fsXp t (365/2)/E.b`),
`Est1.rpow_neg_two`, `Est1.KH_inv_sq`, `Est1.Kl_sq_KH_inv_sq_bigM_le`
(`K_ℓ²K_H^{-2}𝓜 ≤ X^{33/2}`), and `Work.BoseB7A.Est1.estT2sum_deficit`
(the `E.b`-uniform domination of the `Xi_bound` comparison deficit by the gap share
and the `1/b`-term of `e1A`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The squeezed commutator `[b_{s-k}, b_{s'-k}†]` -/

/-- The scalar `[b_{s-k}, b_{s'-k}†]` of the squeezed modes:
`ccrK (s-k) (s'-k) - α_{s-k}α_{s'-k}·ccrK (k-s) (k-s')`.

The second term is `α_pα_q·ccrK(-q)(-p)` for `p = s-k`, `q = s'-k`, from
`[a_{-p}†, a_{-q}] = -ccrK (-q) (-p)`. -/
def kCom (F : FockData Mode) (E : Q3Env Mode) (s s' k : Mode) : ℝ :=
  F.ccrK (s - k) (s' - k) - E.alpha (s - k) * E.alpha (s' - k) * F.ccrK (k - s) (k - s')

/-- FS `eq:bComms2` in the corpus's `χ̂, χ̂²` normalisation:
`[b_{s-k}, b_{s'-k}†] = (1 - α_{s-k}α_{s'-k})(χ̂²(s-s') - χ̂(s-k)χ̂(s'-k))`. -/
theorem kCom_eq {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (s s' k : Mode) :
    kCom F E s s' k = (1 - E.alpha (s - k) * E.alpha (s' - k)) *
      (E.hatChiSq (s - s') - E.hatChi (s - k) * E.hatChi (s' - k)) := by
  have e1 : (s - k) - (s' - k) = s - s' := by abel
  have e2 : (k - s) - (k - s') = -(s - s') := by abel
  have e3 : k - s = -(s - k) := by abel
  have e4 : k - s' = -(s' - k) := by abel
  rw [kCom, hK.hasKernel (s - k) (s' - k), hK.hasKernel (k - s) (k - s'),
    e1, e2, hK.hatChiSq_even (s - s'), e3, e4,
    hK.hatChi_even (s - k), hK.hatChi_even (s' - k)]
  ring

/-! ## 2. The two halves of `‖Y_kΦ‖²/Z²` -/

/-- The **commutator** (`χ̂²`) half of `‖Y_kΦ‖²/Z²` (FS `T₂,comm`):

  `Σ_{s,s'} γ_{sk}γ_{s'k}·[b_{s-k},b_{s'-k}†]·⟨A_{sk}Φ, A_{s'k}Φ⟩`. -/
def T2ComF (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (k : Mode) (Φ : F.H) : ℝ :=
  ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
    (gA E s k * gA E s' k * kCom F E s s' k) *
      (F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ))

/-- The **normal-ordered** half of `‖Y_kΦ‖²/Z²` (FS `T₂,op`):

  `Σ_{s,s'} γ_{sk}γ_{s'k}·⟨b_{s'-k}(A_{sk}Φ), b_{s-k}(A_{s'k}Φ)⟩`. -/
def T2OpF (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (k : Mode) (Φ : F.H) : ℝ :=
  ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
    (gA E s k * gA E s' k) *
      (F.bp (F.bOp E.alpha (s' - k) (Atil F T E s k Φ))
            (F.bOp E.alpha (s - k) (Atil F T E s' k Φ)))

/-! ## 3. The `P_H` lattice sum of FS `eq:CompIntegrals-Final-2` -/

/-- The `P_H` lattice sum of FS `eq:CompIntegrals-Final-2`,
`Ξ = ℓ⁻³ Σ_{k∈P_H} Ŵ₁(k)²/(2𝒟_k)` (which `lem:EstimateIntegral` compares with
`Ŵ₁ω(0)`). -/
def Xi (F : FockData Mode) (E : Q3Env Mode) : ℝ :=
  E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / (2 * E.D k)

/-- **FS `eq:CompIntegrals-Final-2` from the interface.**  `Q3Kernel.intOne` compares
`ρ_zŴ₁ω(0)` with the `P_H` sum of `Ŵ₁(k)α_k`, and `Ŵ₁(k)α_k = ρ_zŴ₁(k)²/(2𝒟_k)` on
`P_H` (`Work.BoseB7.W1_mul_alpha_eq`, from `Q3Kernel.B_eq`); dividing by `ρ_z > 0`
(`FSParamsView.rho_pos`) gives

  `|Ŵ₁ω(0) - Ξ| ≤ K₀·a·K_H⁻¹`. -/
theorem Xi_bound {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hv : FSParamsView E) (hK : Q3Kernel K₀ F T E) :
    |E.W1omega0 - Xi F E| ≤ K₀ * E.aScat * E.KH⁻¹ := by
  have hrho : 0 < E.rho := Work.BoseB7.rho_pos E hv
  have hpt : ∀ k ∈ F.PHset E, E.W1 k * E.alpha k = E.rho * (E.W1 k ^ 2 / (2 * E.D k)) := by
    intro k _
    simp only [Q3Env.alpha, Q3Env.D, Dcoef, alphaCoef, Submission.BoseGases.bogAlpha,
      Submission.BoseGases.bogD]
    rw [hK.B_eq k]
    ring_nf
  have hsum : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k
      = E.rho * Xi F E := by
    have hpt' : (∑ k ∈ F.PHset E, E.W1 k * E.alpha k)
        = E.rho * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / (2 * E.D k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k hk => hpt k hk
    rw [hpt', Xi]
    ring
  have h1 := hK.intOne
  rw [hsum, ← mul_sub, abs_mul, abs_of_pos hrho] at h1
  have h2 : E.rho * |E.W1omega0 - Xi F E| ≤ E.rho * (K₀ * E.aScat * E.KH⁻¹) := by
    rw [show E.rho * (K₀ * E.aScat * E.KH⁻¹) = K₀ * E.rho * E.aScat * E.KH⁻¹ by ring]
    exact h1
  exact le_of_mul_le_mul_left h2 hrho

/-! ## 4. The normalisation `Z² = ρ_z/ℓ³` -/

/-- `Z² = (z/ℓ³)² = ρ_z/ℓ³`, the identity that turns the `k`-weight
`Z²/𝒟_k` into `ρ_z/ℓ³·(1/𝒟_k)` and hence the coefficient `Z²Σ_k W₁(k)²/𝒟_k`
into `2ρ_zΞ`. -/
theorem z_div_ell_cube_sq {E : Q3Env Mode} (h : E.ell ≠ 0) :
    (E.z / E.ell ^ 3) ^ 2 = E.rho / E.ell ^ 3 := by
  rw [Q3Env.rho, rhoZ]
  field_simp

end Est1

end Work.BoseB7A
