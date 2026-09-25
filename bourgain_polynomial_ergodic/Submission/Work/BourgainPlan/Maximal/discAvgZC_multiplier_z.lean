import Mathlib
import Submission.Work.BourgainPlan.Maximal.ftLp_discAvgZC_z
import Submission.Work.BourgainPlan.IonescuWainger.opMul_mul

/-!
# The projected density average as a single `L^∞`-multiplier (arbitrary integer polynomial)

The KMSZ §6.3 model realisation compares the projected average `A_N ∘ Π_{≤l,≤m}` with the
major-arc model `T_ℤ[⟦J_G|𝓂_N η K_{Σ_l}⟧]`.  Both are multipliers on `ℓ²(ℤ) ≅ L²(𝕋)`:

* `discAvgZC P N ∘ opArc φ hφ E` is the multiplier with the **product symbol**
  `khatZMult P N • arcSymbolLp φ hφ E` (`discAvgZC_opArc_eq_opMul_smul` below), by the
  multiplicativity of the symbol action (`opMul_mul`) and the `ℤ`-indexed density-kernel identity
  `ftLp_discAvgZC_z` (which needs no sign hypothesis on `P`, unlike `ftLp_discAvgZC`);
* the model operator is `opArcW θ w S ψ` = the multiplier with the symbol `arcSymbolW θ w S ψ`.

So the *error* `A_N(Π f) − T_model f` is the multiplier with the difference of the two symbols, and
its `ℓ²`-norm is bounded by Plancherel once that difference is pointwise small
(`opMul_l2_bound`).  The pointwise smallness is the content of KMSZ (6.19), formalised as
`Work.BourgainPlan.Maximal.norm_majorArc_error_symbol_le`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **`ftLp` is injective**: the discrete Fourier transform `ℓ²(ℤ) → L²(𝕋)` is the unitary given by
`fourierBasis.repr.symm`, hence an equivalence of the two `ℓ²`-spaces. -/
theorem ftLp_injective {h h' : ℤ → ℂ} (hh : Memℓp h 2) (hh' : Memℓp h' 2)
    (heq : ftLp h hh = ftLp h' hh') : h = h' := by
  have hsub : (⟨h, hh⟩ : lp (fun _ : ℤ => ℂ) 2) = ⟨h', hh'⟩ :=
    (fourierBasis (T := 1)).repr.symm.injective heq
  exact congrArg Subtype.val hsub

/-- **The density average is the multiplier by `khatZMult`**, for every integer polynomial `P`
(no sign hypothesis). -/
theorem opMul_khatZMult_eq_discAvgZC (P : Polynomial ℤ) (N : ℕ) (g : ℤ → ℂ) (hg : Memℓp g 2) :
    opMul (khatZMult P N) g hg = discAvgZC P N g := by
  refine ftLp_injective (opMul_memℓp (khatZMult P N) g hg) (memlp_discAvgZC P N hg) ?_
  rw [ftLp_opMul (khatZMult P N) g hg,
    ftLp_discAvgZC_z P N g hg (memlp_discAvgZC P N hg)]
  rfl

/-- **The projected density average is a single `L^∞`-multiplier**: its symbol is the product of the
density symbol `khatZMult P N` with the arc symbol `arcSymbolLp φ hφ E`. -/
theorem discAvgZC_opArc_eq_opMul_smul (P : Polynomial ℤ) (N : ℕ)
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Work.BourgainPlan.IonescuWainger.Circle)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    discAvgZC P N (opArc φ hφ E f hf)
      = opMul (khatZMult P N • arcSymbolLp φ hφ E) f hf := by
  have h1 := opMul_khatZMult_eq_discAvgZC P N (opMul (arcSymbolLp φ hφ E) f hf)
    (opMul_memℓp (arcSymbolLp φ hφ E) f hf)
  have h2 := opMul_mul (khatZMult P N) (arcSymbolLp φ hφ E) f hf
  rw [opArc, ← h1, ← h2]

end

end Work.BourgainPlan.Maximal
