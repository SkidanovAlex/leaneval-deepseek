import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear
import Submission.Work.BourgainPlan.IonescuWainger.norm_opMul_le_of_kernel
import Submission.Work.BourgainPlan.IonescuWainger.tsum_mul_conj_eq_integral_ftLp

namespace Work.BourgainPlan.KPWW

open MeasureTheory
open scoped ENNReal BigOperators lp
open Work.BourgainPlan.IonescuWainger

/-- **Parseval/Plancherel in inner-product form.**  For `h, k ∈ ℓ²(ℤ)` the coefficient pairing
`Σ_n h n · conj (k n)` is the `L²(𝕋)` inner product `⟪ftLp k, ftLp h⟫`.  This is the first step of
`tsum_mul_conj_eq_integral_ftLp`, isolated for reuse. -/
theorem tsum_mul_conj_eq_inner_ftLp {h k : ℤ → ℂ} (hh : Memℓp h 2) (hk : Memℓp k 2) :
    ∑' n : ℤ, h n * star (k n) = inner ℂ (ftLp k hk) (ftLp h hh) := by
  rw [tsum_mul_conj_eq_integral_ftLp hh hk]
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [RCLike.inner_apply, starRingEnd_apply]

/-- **The Fourier transform of a multiplier** is the product of the symbol with the Fourier
transform of the sequence, for an arbitrary `ℓ²`-proof of the image.  This is `ftLp_opMul` with the
`Memℓp`-argument made flexible. -/
theorem ftLp_opMul_apply {Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))} (f : ℤ → ℂ)
    (hf : Memℓp f 2) (h : Memℓp (opMul Φ f hf) 2) :
    ftLp (opMul Φ f hf) h = Φ • ftLp f hf := by
  rw [ftLp_congr_memℓp rfl h (opMul_memℓp Φ f hf)]
  exact ftLp_opMul _ _ _

/-- **Adjointness of the arc multiplier.**  If `ψ = star ∘ φ` pointwise, then the multiplier
`opArcLM ψ hψ E` is the transpose of `opArcLM φ hφ E` for the pairing
`⟨u, v⟩ = Σ_n u n * star (v n)` on finitely supported sequences: for all `f g : ℤ →₀ ℂ`,
`Σ_n (opArcLM φ hφ E f) n * star (g n) = Σ_n f n * star ((opArcLM ψ hψ E g) n)`,
in the equivalent orientation (with `g` on the left) used below; the statement below writes both
sides as convergent series in the orientation `⟨ftLp (Tf), ftLp g⟩ = ⟨ftLp f, ftLp (T*g)⟩`.

Route.  `opArcLM φ hφ E` is the multiplier with symbol `Φ = arcSymbolLp φ hφ E`, so
`ftLp (opArcLM φ hφ E f) = Φ • ftLp f` (`ftLp_opMul`, `OpArcDefs.lean`), and likewise for `ψ`,
whose symbol `Ψ = arcSymbolLp ψ hψ E` satisfies `star Φ = Ψ` a.e. (both sides are a.e. equal to
`arcSymbol ψ E = star ∘ arcSymbol φ E`, the latter by `hψφ` and additivity of `star`; conclude by
`Lp.ext`).  Under the `ℓ²(ℤ) ≅ L²(𝕋)` dictionary,
`⟪ftLp u, ftLp v⟫_{L²} = Σ_n v n * star (u n)` (`tsum_mul_conj_eq_integral_ftLp` together with the
first step of that file), so the identity becomes `⟪Φ • F, G⟫ = ⟪F, star Φ • G⟫`, which is
`(inner_lpSMul_star (star Φ) F G).symm` from
`IonescuWainger/norm_opMul_le_of_kernel.lean` (with `star_star`). -/
theorem opArcLM_pairing {φ ψ : AddCircle (1 : ℝ) → ℂ}
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (hψ : MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (hψφ : ∀ ξ, ψ ξ = star (φ ξ)) (E : Finset (AddCircle (1 : ℝ))) (f g : ℤ →₀ ℂ) :
    (∑' n : ℤ, (g : ℤ → ℂ) n * star (Work.BourgainPlan.IonescuWainger.opArcLM φ hφ E f n))
      = ∑' n : ℤ,
          (Work.BourgainPlan.IonescuWainger.opArcLM ψ hψ E g n) * star ((f : ℤ → ℂ) n) := by
  -- The symbol of `ψ` is the pointwise conjugate of the symbol of `φ`.
  have hstar : arcSymbolLp ψ hψ E = star (arcSymbolLp φ hφ E) := by
    refine Lp.ext ?_
    filter_upwards [arcSymbolLp_coeFn ψ hψ E, arcSymbolLp_coeFn φ hφ E,
      Lp.coeFn_star (arcSymbolLp φ hφ E)] with ξ hψξ hφξ hstξ
    rw [hstξ]
    simp only [Pi.star_apply, hψξ, hφξ, arcSymbol_apply]
    rw [star_sum]
    exact Finset.sum_congr rfl fun β hβ => hψφ (ξ - β)
  -- Replace `opArcLM` by the underlying multiplier `opMul` of its symbol.
  have hptL : (fun n => (g : ℤ → ℂ) n * star (opArcLM φ hφ E f n))
      = fun n => (g : ℤ → ℂ) n * star (opMul (arcSymbolLp φ hφ E) (⇑f)
          (memℓp_finsupp f) n) := by
    funext n; rw [opArcLM_apply]; rfl
  have hptR : (fun n => opArcLM ψ hψ E g n * star ((f : ℤ → ℂ) n))
      = fun n => opMul (arcSymbolLp ψ hψ E) (⇑g) (memℓp_finsupp g) n
          * star ((f : ℤ → ℂ) n) := by
    funext n; rw [opArcLM_apply]; rfl
  rw [hptL, hptR]
  -- Both sides become `L²(𝕋)` inner products (Parseval), then products of `𝓕`s.
  rw [tsum_mul_conj_eq_inner_ftLp (memℓp_finsupp g)
    (opMul_memℓp (arcSymbolLp φ hφ E) (⇑f) (memℓp_finsupp f))]
  rw [ftLp_opMul_apply (⇑f) (memℓp_finsupp f)
    (opMul_memℓp (arcSymbolLp φ hφ E) (⇑f) (memℓp_finsupp f))]
  rw [tsum_mul_conj_eq_inner_ftLp (opMul_memℓp (arcSymbolLp ψ hψ E) (⇑g) (memℓp_finsupp g))
    (memℓp_finsupp f)]
  rw [ftLp_opMul_apply (⇑g) (memℓp_finsupp g)
    (opMul_memℓp (arcSymbolLp ψ hψ E) (⇑g) (memℓp_finsupp g))]
  -- `⟪Φ • F, G⟫ = ⟪F, star Φ • G⟫`, the adjunction for an `L^∞`-symbol.
  rw [hstar]
  exact ((inner_lpSMul_star (star (arcSymbolLp φ hφ E))
    (ftLp (⇑f) (memℓp_finsupp f)) (ftLp (⇑g) (memℓp_finsupp g))).trans
      (by rw [star_star])).symm

end Work.BourgainPlan.KPWW
