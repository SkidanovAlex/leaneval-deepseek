import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs

/-!
# The major-arc model of KMSZ §6.3: the weighted multifrequency extension

Kosz–Mirek–Słomian–Zhang, arXiv:2606.12663, §6.3.  The major-arc half of the variational
inequality (6.5) is stated there for the *model operators*

      `T_ℤ ⟦J_G | m_N η_{≤ -dL(N)} K_{Σ_l}⟧`,      `G = G(a/q) = m̃_q(a/q)` the complete sum,

where, with KMSZ's notation (2.2),

      `⟦G | m⟧_Σ (ξ) := Σ_{σ ∈ Σ} G(σ) m(ξ - σ)`

is the **weighted multifrequency extension** of `m` with respect to the finite arc set `Σ ⊆ 𝕋`:
one bump `m(· - σ)` per arc, weighted by `G(σ)`.  This is exactly the symbol of the operator that
KMSZ reduce to after the major-arc approximation (6.19); the companion module
`Maximal/kmsz_major_defs.lean` states the reduction of the *projection* `Π_{≤l,≤m}` to it as the
named input `KMSZMajorArcStatement`.

This file holds only the *vocabulary*: the weighted symbol `arcSymbolW`, its `L^∞`-class
`arcSymbolWLp`, and the two elementary structural facts
`memLp_arcSymbolW` (a.e. boundedness) and `arcSymbolW_apply`.  The operator itself is the generic
`Work.BourgainPlan.IonescuWainger.opMul` applied to `arcSymbolWLp`, so all the generic multiplier
lemmas (`ftLp_opMul`, `opMul_memℓp`) apply verbatim.

The mathematical content that goes on top of this vocabulary — and which §6.3 needs — is

* `norm_arcSymbolW_le`: the **pointwise** bound on the weighted symbol, from the separation of the
  arcs and a bound on the weights (KMSZ: "the pieces corresponding to different fractions do not
  overlap");
* the **`ℓ²` gain** (6.23): Plancherel plus the pointwise bound on the symbol, with the weights
  bounded by the Gauss decay `|G(θ)| ≤ A 2^{-σ l}` (`polyWeight_cap_modulus`);
* the **factorisation** (6.22): `⟦J_G|m η K_{Σ_l}⟧ = ⟦J_1|m η K_{Σ_{≤l}}⟧ · ⟦J_G|η' K_{Σ_l}⟧`
  when `η' ≡ 1` on the support of `m η` and the arcs are separated.
-/

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **KMSZ's weighted multifrequency extension (2.2)**, for a finite indexed family of arcs:
`arcSymbolW θ w s φ ξ = Σ_{i ∈ s} w i * φ (ξ - θ i)`.  With `θ` the (canonical) fractions of a
level, `w` the complete sums `G(θ)` and `φ = m_N η_{≤ -dL(N)}` this is the symbol of the
major-arc model operator. -/
def arcSymbolW {ι : Type*} (θ : ι → Work.BourgainPlan.IonescuWainger.Circle) (w : ι → ℂ)
    (s : Finset ι) (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) :
    Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  fun ξ => ∑ i ∈ s, w i * φ (ξ - θ i)

@[simp] theorem arcSymbolW_apply {ι : Type*}
    (θ : ι → Work.BourgainPlan.IonescuWainger.Circle) (w : ι → ℂ) (s : Finset ι)
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (ξ : Work.BourgainPlan.IonescuWainger.Circle) :
    arcSymbolW θ w s φ ξ = ∑ i ∈ s, w i * φ (ξ - θ i) := rfl

theorem arcSymbolW_empty {ι : Type*}
    (θ : ι → Work.BourgainPlan.IonescuWainger.Circle) (w : ι → ℂ)
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) :
    arcSymbolW θ w ∅ φ = 0 := by
  funext ξ; simp [arcSymbolW]

/-- The weighted symbol is a.e. bounded as soon as `φ` is (a finite sum of scalar multiples of
translates of `φ`). -/
theorem memLp_arcSymbolW {ι : Type*}
    (θ : ι → Work.BourgainPlan.IonescuWainger.Circle) (w : ι → ℂ) (s : Finset ι)
    {φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ}
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) :
    MemLp (arcSymbolW θ w s φ) ⊤ (AddCircle.haarAddCircle (T := 1)) := by
  have h : arcSymbolW θ w s φ
      = fun ξ => ∑ i ∈ s, w i * arcTranslate (θ i) φ ξ := by
    funext ξ; simp [arcSymbolW, arcTranslate]
  rw [h]
  exact memLp_finsetSum s fun i _ => (memLp_arcTranslate hφ (θ i)).const_mul (w i)

/-- The `L^∞(𝕋)`-class of the weighted symbol `Σ_{i ∈ s} w i · φ (· - θ i)`. -/
def arcSymbolWLp {ι : Type*}
    (θ : ι → Work.BourgainPlan.IonescuWainger.Circle) (w : ι → ℂ) (s : Finset ι)
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) :
    Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)) :=
  (memLp_arcSymbolW θ w s hφ).toLp (arcSymbolW θ w s φ)

theorem arcSymbolWLp_coeFn {ι : Type*}
    (θ : ι → Work.BourgainPlan.IonescuWainger.Circle) (w : ι → ℂ) (s : Finset ι)
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) :
    (arcSymbolWLp θ w s φ hφ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] arcSymbolW θ w s φ :=
  MemLp.coeFn_toLp _

/-- **The major-arc model operator** of KMSZ §6.3 at a single scale: the multiplier with the
weighted arc symbol `Σ_{i ∈ s} w i · φ (· - θ i)` acting on `ℓ²(ℤ)`. -/
def opArcW {ι : Type*} (θ : ι → Work.BourgainPlan.IonescuWainger.Circle) (w : ι → ℂ)
    (s : Finset ι) (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ) (hf : Memℓp f 2) : ℤ → ℂ :=
  opMul (arcSymbolWLp θ w s φ hφ) f hf

/-- The Fourier transform of the model operator is the product of its symbol with `𝓕f`. -/
theorem ftLp_opArcW {ι : Type*}
    (θ : ι → Work.BourgainPlan.IonescuWainger.Circle) (w : ι → ℂ) (s : Finset ι)
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ftLp (opArcW θ w s φ hφ f hf) (opMul_memℓp _ f hf)
      = arcSymbolWLp θ w s φ hφ • ftLp f hf :=
  ftLp_opMul (arcSymbolWLp θ w s φ hφ) f hf

end

end Work.BourgainPlan.Maximal
