import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Assembly
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.AngSecond.I_identity
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AngAWeak/Basic` — the interface of Step 2 of Elgindi's `prop:H2` in the a.e. class

This module is the *interface* of the analytic input `Step2` of
`Submission/Work/FTS/EllipticEst/H2W/Ae/Assembly.lean`, i.e. the paper's Step 2 in the weak
class `Work.FTS.EllipticEst.H2W.Ae.AeData`:

  `‖∂_θθu‖_ρ ≤ C (‖G‖_ρ + α ‖z∂_zu‖_ρ)`,  `‖g‖_ρ = √(HkSq α 0 g)`.

## Design

The proof is the paper's: multiply `bslOp α u = G` by `-∂_θθu·w²σ`, integrate over the quadrant
(the *pairing identity*), bound the five pieces

* `I₁ = α²⟨z²∂_zzu, ∂_θθu⟩` (the lower bound: the deep input `AeI1`),
* `I₂ = α(5+α)⟨z∂_zu, ∂_θθu⟩` (Cauchy–Schwarz),
* `I₄ = ⟨∂_θ(tan θ·u), ∂_θθu⟩` (the upper bound: the deep input `AeI4`),
* `I₅ = 6⟨u, ∂_θθu⟩`, `I₆ = ⟨G, ∂_θθu⟩` (Cauchy–Schwarz),

and solve the resulting quadratic inequality.  The Step 1 inputs (`‖u‖_ρ` and the `Ψ̄ = u/cos θ`
analogue in terms of `‖G‖_ρ` and `α‖z∂_zu‖_ρ`, together with the honesty of `u`, `z∂_zu`,
`u/cos θ`) form the input `AeStep1`, and the `IPMem` bookkeeping of the identity is the input
`AeIPMems`.

It contains, sorry-free: (a) the pairing identity in the form needed here — the file
`AngSecond/I_identity.lean` states it for `IsBslSol`, which *includes the pointwise decay at
`z → ∞`* that `AeData` does not have, while its proof only uses the equation on the open
quadrant, so we restate it here; (b) the four `Prop`s `AeStep1`, `AeI1`, `AeI4`, `AeIPMems`
collecting the analytic inputs (each proved elsewhere as a theorem of that `Prop`); (c) the
assembly `step2Ae_of` of the estimate from the four inputs.  The target `step2Ae` itself lives in
`AngAWeak/step2Ae.lean`, which imports this module together with the four proofs.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

open Work.FTS.EllipticEst.AngSecond

/-! ## The pairing identity for data with no decay at `z = ∞` -/

/-- **Linearity of the weighted pairing in its first slot, in finite-sum form.**

With `IP g h = ∫_z ∫_θ g z θ * h z θ * w z² * σ θ` and `IPMem` the honesty of that iterated
integral, a finite linear combination of pairings is the pairing of the linear combination.
(A copy of the private helper of `AngSecond/I_identity.lean`, with the same proof.) -/
private theorem IP_sum_left'' {ι : Type*} [Fintype ι] (c : ι → ℝ) (f : ι → ℝ → ℝ → ℝ)
    (h : ℝ → ℝ → ℝ) (hf : ∀ i, IPMem (f i) h) :
    IP (fun z θ => ∑ i, c i * f i z θ) h = ∑ i, c i * IP (f i) h := by
  simp only [IP]
  have hmid : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (∑ i, c i * f i z θ) * h z θ * w2 z * sig θ)
        = ∑ i, c i * (∫ θ in Work.Spaces.Iθ, f i z θ * h z θ * w2 z * sig θ) := by
    intro z hz
    rw [show (∫ θ in Work.Spaces.Iθ, (∑ i, c i * f i z θ) * h z θ * w2 z * sig θ)
        = ∫ θ in Work.Spaces.Iθ, ∑ i, c i * (f i z θ * h z θ * w2 z * sig θ) from
      setIntegral_congr_fun (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => by
          rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring))]
    rw [MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl (fun i _ => MeasureTheory.integral_const_mul (c i) _)
    · intro i _; exact ((hf i).1 z hz).const_mul (c i)
  rw [MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) hmid]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    exact MeasureTheory.integral_const_mul (c i) _
  · intro i _; exact ((hf i).2).const_mul (c i)

/-- **The weighted pairing vanishes on functions vanishing in the open quadrant.**

If `g` vanishes on `(0,∞) × (0,π/2)` then `IP g h = 0`: the complement of the open quadrant
inside `Iz × Iθ` is the null set of the two boundary lines.  No hypothesis on `h` is needed.
(A copy of the private helper of `AngSecond/I_identity.lean`, with the same proof.) -/
private theorem IP_eq_zero_of_openQuadrant'' (g h : ℝ → ℝ → ℝ)
    (hg : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g z θ = 0) :
    IP g h = 0 := by
  simp only [IP]
  have hslice : ∀ z ∈ Work.Spaces.Iz, z ≠ 0 →
      (∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ) = 0 := by
    intro z hz hz0
    rw [show (∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ)
        = ∫ θ in Work.Spaces.Iθ, (0 : ℝ) from
      setIntegral_congr_ae (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) ?_]
    · simp
    · rw [MeasureTheory.ae_iff]
      refine measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
      · intro θ hθ
        simp only [Set.mem_ofPred_eq] at hθ
        by_contra hbad
        apply hθ
        intro hθI
        have h0 : 0 < θ := lt_of_le_of_ne hθI.1 (fun h => hbad (by rw [h]; simp))
        have h1 : θ < Real.pi / 2 := lt_of_le_of_ne hθI.2 (fun h => hbad (by rw [h]; simp))
        have hzpos : 0 < z := lt_of_le_of_ne hz (fun h => hz0 h.symm)
        rw [hg z hzpos θ ⟨h0, h1⟩]; ring
      · rw [show ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} from by
          ext x; simp only [mem_insert_iff, mem_singleton_iff, mem_union]]
        exact measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2))
  have hae : ∀ᵐ x ∂(volume : MeasureTheory.Measure ℝ), x ∈ Work.Spaces.Iz →
      (∫ θ in Work.Spaces.Iθ, g x θ * h x θ * w2 x * sig θ) = 0 := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (t := ({0} : Set ℝ)) ?_ (measure_singleton 0)
    intro z hz
    by_contra hz0
    exact hz (fun hzI => hslice z hzI hz0)
  rw [MeasureTheory.setIntegral_congr_ae
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) hae]
  simp

/-- **The Step 2 integral identity without any decay hypothesis.**

Multiplying the equation `bslOp α Ψ = F` (on the *open* quadrant only) by
`-∂_θθΨ · w²/sin(2θ)^η` and integrating over the quadrant gives

  `I₁ + I₂ + I₃ + I₄ + I₅ = - IP F (∂_θθΨ)`

with `I₁ = α²·IP (z²∂_zzΨ) (∂_θθΨ)`, `I₂ = α(5+α)·IP (z∂_zΨ) (∂_θθΨ)`,
`I₃ = IP (∂_θθΨ) (∂_θθΨ)`, `I₄ = - IP (∂_θ(tan θ Ψ)) (∂_θθΨ)`, `I₅ = 6·IP Ψ (∂_θθΨ)`.

This is `Work.FTS.EllipticEst.AngSecond.I_identity` with the hypothesis `IsBslSol α F Ψ`
(which contains the pointwise decay `Ψ(·,θ) → 0` at `z → ∞`, unavailable in `AeData`) replaced by
the single equation on the open quadrant — which is all the proof of `I_identity` uses. -/
theorem I_identity_weak (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hF : IPMem F (Work.Spaces.pthIter 2 Ψ))
    (hQ : IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ))
    (hU : IPMem (fun z θ => z * Work.Spaces.pz Ψ z θ) (Work.Spaces.pthIter 2 Ψ))
    (hG : IPMem (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ))
    (hPsi : IPMem Ψ (Work.Spaces.pthIter 2 Ψ))
    (hphi : IPMem (Work.Spaces.pthIter 2 Ψ) (Work.Spaces.pthIter 2 Ψ)) :
    α ^ 2 * IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ)
      + α * (5 + α) * IP (fun z θ => z * Work.Spaces.pz Ψ z θ) (Work.Spaces.pthIter 2 Ψ)
      + IP (Work.Spaces.pthIter 2 Ψ) (Work.Spaces.pthIter 2 Ψ)
      - IP (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          (Work.Spaces.pthIter 2 Ψ)
      + 6 * IP Ψ (Work.Spaces.pthIter 2 Ψ)
      = - IP F (Work.Spaces.pthIter 2 Ψ) := by
  set Ph : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hPhdef
  set Q : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hQdef
  set U : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Ψ z θ with hUdef
  set G₁ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
    with hGdef
  -- the bracket whose vanishing on the open quadrant *is* the elliptic equation
  set B : ℝ → ℝ → ℝ := fun z θ =>
    F z θ + α ^ 2 * Q z θ + α * (5 + α) * U z θ + Ph z θ - G₁ z θ + 6 * Ψ z θ with hBdef
  set c : Fin 6 → ℝ := ![1, α ^ 2, α * (5 + α), 1, -1, 6] with hcdef
  set f : Fin 6 → ℝ → ℝ → ℝ := ![F, Q, U, Ph, G₁, Ψ] with hfdef
  have hBz : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), B z θ = 0 := by
    intro z hz θ hθ
    have hbs := heq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at hbs
    simp only [hBdef, hQdef, hUdef, hGdef, hPhdef]
    rw [← hbs]
    ring
  have hzero : IP B Ph = 0 := IP_eq_zero_of_openQuadrant'' B Ph hBz
  have hBeq : B = fun z θ => ∑ i : Fin 6, c i * f i z θ := by
    funext z θ
    rw [Fin.sum_univ_six, hcdef, hfdef, hBdef]
    simp
    ring
  have hsum : IP B Ph = ∑ i : Fin 6, c i * IP (f i) Ph := by
    rw [hBeq]
    exact IP_sum_left'' c f Ph (fun i => by
      fin_cases i <;> simp [hfdef, hF, hQ, hU, hphi, hG, hPsi])
  have hexp : (∑ i : Fin 6, c i * IP (f i) Ph)
      = 1 * IP F Ph + α ^ 2 * IP Q Ph + α * (5 + α) * IP U Ph + 1 * IP Ph Ph
        + (-1) * IP G₁ Ph + 6 * IP Ψ Ph := by
    rw [Fin.sum_univ_six, hcdef, hfdef]
    simp
  have hsum0 : (∑ i : Fin 6, c i * IP (f i) Ph) = 0 := by
    rw [← hsum]; exact hzero
  have hcomb : α ^ 2 * IP Q Ph + α * (5 + α) * IP U Ph + IP Ph Ph - IP G₁ Ph
      + 6 * IP Ψ Ph + IP F Ph = 0 := by
    rw [show α ^ 2 * IP Q Ph + α * (5 + α) * IP U Ph + IP Ph Ph - IP G₁ Ph
        + 6 * IP Ψ Ph + IP F Ph = ∑ i : Fin 6, c i * IP (f i) Ph from by
      rw [hexp]; ring]
    exact hsum0
  rw [eq_neg_iff_add_eq_zero]
  exact hcomb

/-! ## The four inputs of the assembly

Each is a genuinely independent piece of the paper's Step 2; each is stated with the *full*
`AeData` hypothesis (so that the prover has the equation, the Dirichlet data and the two a.e.
moment conditions available) plus the honesty statements that `AeData` does not supply. -/

/-- **Step 1 in the class `AeData`** (paper: `(radialweightonlyL2)` with the `σ`-upgrade, plus
the `Ψ̄ = u/cos θ` companion): `u`, `z∂_zu` and `u/cos θ` are honest in `ℋ⁰`, and
`‖u‖_ρ ≤ C‖G‖_ρ`, `‖u/cos θ‖_ρ ≤ C‖G‖_ρ`. -/
def AeStep1 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 u ∧
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) ∧
      Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ) ∧
      Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G ∧
      Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => u z θ / Real.cos θ)
        ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G

/-- **The `I₁` lower bound in the class `AeData`**:
`-C α²(IP (z∂_zu) (z∂_zu) + √(IP (z∂_zu)(z∂_zu))·√(IP (∂_θθu)(∂_θθu))) ≤ α² IP (z²∂_zzu) (∂_θθu)`.

The full `AeData` hypothesis class is used (in particular **both** a.e. moment conditions
`F_* u = 0`, `F_* G = 0`): the lower bound is *false* without the moment condition on the
source `G`, since a slice with a jump at `θ = 0` whose angular moment vanishes gives
`IP (z²∂_zzu) (∂_θθu)` of the wrong size (see `AngAWeak/NOTES_aeI1Lower_FALSE.md`); it is the
equation together with `F_* u = F_* G = 0` that forces the slices to have no jump. -/
def AeI1 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) →
      - C * α ^ 2 * (IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => z * Work.Spaces.pz u z θ)
          + Real.sqrt (IP (fun z θ => z * Work.Spaces.pz u z θ)
                (fun z θ => z * Work.Spaces.pz u z θ))
            * Real.sqrt (IP (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
        ≤ α ^ 2 * IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
            (Work.Spaces.pthIter 2 u)

/-- **The `I₄` upper bound in the class `AeData`**:
`IP (∂_θ(tan θ·u)) (∂_θθu) ≤ C(‖u/cos θ‖²_ρ + ‖u/cos θ‖_ρ·‖∂_θθu‖_ρ)`. -/
def AeI4 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u) →
      IP (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ)
          (Work.Spaces.pthIter 2 u)
        ≤ C * (Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
            + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ))
              * Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)))

/-- **The `IPMem` bookkeeping of the identity in the class `AeData`.** -/
def AeIPMems : Prop :=
  ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 u →
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) →
      IPMem G (Work.Spaces.pthIter 2 u) ∧
      IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) ∧
      IPMem (fun z θ => z * Work.Spaces.pz u z θ) (Work.Spaces.pthIter 2 u) ∧
      IPMem (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ)
        (Work.Spaces.pthIter 2 u) ∧
      IPMem u (Work.Spaces.pthIter 2 u) ∧
      IPMem (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)

/-! ## The assembly -/

/-- The quadratic solve used at the end of the assembly. -/
private theorem quad_solve'' {K X N : ℝ} (hK : 0 ≤ K) (hN : 0 ≤ N)
    (h : X ^ 2 ≤ K * (N * X + N ^ 2)) : X ≤ (K + 1) * N := by
  by_cases hX : X ≤ 0
  · nlinarith
  · push_neg at hX
    by_cases hN0 : N = 0
    · subst hN0
      have h2 : X ^ 2 ≤ 0 := by simpa using h
      have h3 : X = 0 := sq_eq_zero_iff.mp (le_antisymm h2 (sq_nonneg X))
      rw [h3]; simp
    · have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hN0)
      by_contra hcon
      push_neg at hcon
      have h1 : 0 < (X - (K + 1) * N) * N := mul_pos (by linarith) hNpos
      nlinarith [hcon, hK, h1, h]

/-- **The assembly of Step 2 in the class `AeData`** from the four inputs. -/
theorem step2Ae_of (h1 : AeStep1) (h2 : AeI1) (h3 : AeI4) (h4 : AeIPMems) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.Spaces.pthIter 2 u)
          ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α
                (fun z θ => z * Work.Spaces.pz u z θ)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := h1
  obtain ⟨C₂, hC₂pos, hC₂⟩ := h2
  obtain ⟨C₃, hC₃pos, hC₃⟩ := h3
  have hK₁0 : (0 : ℝ) ≤ C₂ + C₃ * C₁ ^ 2 + C₃ := by positivity
  refine ⟨max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) + 1, by
    linarith [le_max_left (C₂ + C₃ * C₁ ^ 2 + C₃)
      (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1), hK₁0], ?_⟩
  intro α u G hA
  obtain ⟨hmemu, hmemU, hmemPb, huBd, hPbBd⟩ := hC₁ α u G hA
  have hI1 := hC₂ α u G hA hmemU
  have hI4 := hC₃ α u hA.smooth hmemPb hA.memAng2
  obtain ⟨hFB, hQB, hUB, hG₁B, huB, hBB⟩ := h4 α u G hA hmemu hmemU
  have hα : 0 < α := hA.hα
  have hα4 : α ≤ 1 / 4 := hA.hα4
  have hsol := hA.eq
  have hmemG : Work.Spaces.HkMem α 0 G := hA.memG
  have hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u) := hA.memAng2
  -- abbreviations
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 u with hBdef
  set Q : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ with hQdef
  set U : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz u z θ with hUdef
  set G₁ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ
    with hG₁def
  set PbF : ℝ → ℝ → ℝ := fun z θ => u z θ / Real.cos θ with hPbFdef
  have hPbHon : Work.Spaces.HkMem α 0 PbF := hmemPb
  set f : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α G with hfdef
  set b : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α U with hbdef
  set X : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α B with hXdef
  set N : ℝ := f + α * b with hNdef
  set Pb : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α PbF with hPbdef
  set m : ℝ := Work.FTS.EllipticEst.H2W.Ae.nrm α u with hmdef
  have hf0 : 0 ≤ f := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hPb0 : 0 ≤ Pb := Real.sqrt_nonneg _
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  -- ## `HkSq` versus the honest `IP`-pairing
  have hb2 : b ^ 2 = IP U U := by
    rw [hbdef, hUdef, Work.FTS.EllipticEst.H2W.Ae.nrm,
      Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hX2 : X ^ 2 = IP B B := by
    rw [hXdef, hBdef, Work.FTS.EllipticEst.H2W.Ae.nrm,
      Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hf2 : f ^ 2 = IP G G := by
    rw [hfdef, Work.FTS.EllipticEst.H2W.Ae.nrm,
      Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hPb2 : Pb ^ 2 = IP PbF PbF := by
    rw [hPbdef, hPbFdef, Work.FTS.EllipticEst.H2W.Ae.nrm,
      Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hXeq : Real.sqrt (IP B B) = X := by
    rw [← hX2]; exact Real.sqrt_sq hX0
  have hbeq : Real.sqrt (IP U U) = b := by
    rw [← hb2]; exact Real.sqrt_sq hb0
  have hfeq : Real.sqrt (IP G G) = f := by
    rw [← hf2]; exact Real.sqrt_sq hf0
  have hmeq : Real.sqrt (IP u u) = m := by
    rw [hmdef, Work.FTS.EllipticEst.H2W.Ae.nrm,
      Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
  have hPbeq : Real.sqrt (IP PbF PbF) = Pb := by
    rw [← hPb2]; exact Real.sqrt_sq hPb0
  -- ## the identity, the pieces, and Cauchy–Schwarz
  have hid := I_identity_weak α G u hsol hFB hQB hUB hG₁B huB hBB
  have hcsG := IP_cauchy_schwarz
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemG)
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemB) hFB
  have hcsU := IP_cauchy_schwarz
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemU)
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemB) hUB
  have hcsu := IP_cauchy_schwarz
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemu)
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemB) huB
  -- ## the bounds of the individual pieces
  have e1 : -α ^ 2 * IP Q B ≤ C₂ * (α ^ 2 * b ^ 2) + C₂ * ((α ^ 2 * b) * X) := by
    have h := hI1
    rw [hbeq, hXeq, ← hb2] at h
    linarith [h]
  have e2 : -α * (5 + α) * IP U B ≤ (5 + α) * ((α * b) * X) := by
    have h := (abs_le.mp hcsU).1
    rw [hbeq, hXeq] at h
    have h5 : 0 ≤ α * (5 + α) := by nlinarith [hα]
    nlinarith [h, h5, hb0, hX0]
  have e3 : IP G₁ B ≤ C₃ * (Pb ^ 2 + Pb * X) := by
    have h := hI4
    rw [← Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq α PbF, ← hPb2, Real.sqrt_sq hPb0,
      ← Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq α B, ← hX2, Real.sqrt_sq hX0] at h
    exact h
  have e4 : -6 * IP u B ≤ 6 * (m * X) := by
    have h := (abs_le.mp hcsu).1
    rw [hmeq, hXeq] at h
    linarith [h]
  have e5 : -IP G B ≤ f * X := by
    have h := (abs_le.mp hcsG).1
    rw [hfeq, hXeq] at h
    linarith [h]
  -- ## the identity, solved for the pairing of `∂_θθu` with itself
  have hid' : IP B B
      = -α ^ 2 * IP Q B - α * (5 + α) * IP U B + IP G₁ B - 6 * IP u B - IP G B := by
    linarith [hid]
  -- ## the elementary consequences of the abbreviations
  have hNf : f ≤ N := by rw [hNdef]; nlinarith [hb0, hα.le]
  have hNb : α * b ≤ N := by rw [hNdef]; nlinarith [hf0]
  have hαb2 : α ^ 2 * b ^ 2 ≤ N ^ 2 := by nlinarith [hNb, hα, hb0, hN0]
  have hαbX : (α ^ 2 * b) * X ≤ N * X := by
    have h1 : α ^ 2 * b ≤ N := by
      have h2 : α ^ 2 * b = α * (α * b) := by ring
      rw [h2]
      calc α * (α * b) ≤ α * N := mul_le_mul_of_nonneg_left hNb hα.le
        _ ≤ 1 * N := by
            have h3 : α ≤ 1 := by linarith
            exact mul_le_mul_of_nonneg_right h3 hN0
        _ = N := by ring
    exact mul_le_mul_of_nonneg_right h1 hX0
  have h5bb : (5 + α) * ((α * b) * X) ≤ (21 / 4) * (N * X) := by
    have h1 : 5 + α ≤ 21 / 4 := by linarith
    have h2 : 0 ≤ (α * b) * X := by positivity
    have h3 : (α * b) * X ≤ N * X := mul_le_mul_of_nonneg_right hNb hX0
    calc (5 + α) * ((α * b) * X) ≤ (21 / 4) * ((α * b) * X) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ ≤ (21 / 4) * (N * X) := mul_le_mul_of_nonneg_left h3 (by norm_num)
  have hmb : m ≤ C₁ * N := by
    have h1 : m ≤ C₁ * f := by rw [hmdef, hfdef]; exact huBd
    exact le_trans h1 (mul_le_mul_of_nonneg_left hNf hC₁pos.le)
  have hPbb : Pb ≤ C₁ * N := by
    have h1 : Pb ≤ C₁ * f := by rw [hPbdef, hPbFdef, hfdef]; exact hPbBd
    exact le_trans h1 (mul_le_mul_of_nonneg_left hNf hC₁pos.le)
  have hPb2b : Pb ^ 2 ≤ (C₁ * N) ^ 2 := by nlinarith [hPbb, hPb0, hC₁pos, hN0]
  have hPbX : Pb * X ≤ (C₁ * N) * X := mul_le_mul_of_nonneg_right hPbb hX0
  have hmX : m * X ≤ (C₁ * N) * X := mul_le_mul_of_nonneg_right hmb hX0
  have hfX : f * X ≤ N * X := mul_le_mul_of_nonneg_right hNf hX0
  -- ## the collection
  have hkey : X ^ 2 ≤ (C₂ + C₃ * C₁ ^ 2 + C₃) * N ^ 2
      + (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X) := by
    have hsum : X ^ 2 ≤ C₂ * (α ^ 2 * b ^ 2) + C₂ * ((α ^ 2 * b) * X)
        + (5 + α) * ((α * b) * X) + C₃ * (Pb ^ 2 + Pb * X)
        + 6 * (m * X) + f * X := by
      rw [hX2, hid']
      linarith [e1, e2, e3, e4, e5]
    have t1 : C₂ * (α ^ 2 * b ^ 2) ≤ C₂ * N ^ 2 := mul_le_mul_of_nonneg_left hαb2 hC₂pos.le
    have t2 : C₂ * ((α ^ 2 * b) * X) ≤ C₂ * (N * X) := mul_le_mul_of_nonneg_left hαbX hC₂pos.le
    have t4 : C₃ * (Pb ^ 2 + Pb * X) ≤ C₃ * ((C₁ * N) ^ 2 + (C₁ * N) * X + N ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hC₃pos.le
      nlinarith [hPb2b, hPbX, sq_nonneg N]
    have t5 : 6 * (m * X) ≤ 6 * ((C₁ * N) * X) :=
      mul_le_mul_of_nonneg_left hmX (by norm_num)
    have hcollect : C₂ * (α ^ 2 * b ^ 2) + C₂ * ((α ^ 2 * b) * X)
        + (5 + α) * ((α * b) * X) + C₃ * (Pb ^ 2 + Pb * X)
        + 6 * (m * X) + f * X
        ≤ C₂ * N ^ 2 + C₂ * (N * X) + (21 / 4) * (N * X)
          + C₃ * ((C₁ * N) ^ 2 + (C₁ * N) * X + N ^ 2) + 6 * ((C₁ * N) * X) + N * X := by
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add t1 t2) h5bb) t4) t5) hfX
    calc X ^ 2
        ≤ C₂ * N ^ 2 + C₂ * (N * X) + (21 / 4) * (N * X)
          + C₃ * ((C₁ * N) ^ 2 + (C₁ * N) * X + N ^ 2) + 6 * ((C₁ * N) * X) + N * X :=
          le_trans hsum hcollect
      _ = (C₂ + C₃ * C₁ ^ 2 + C₃) * N ^ 2
          + (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X) := by ring
  have hmain : X ^ 2 ≤ max (C₂ + C₃ * C₁ ^ 2 + C₃)
      (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X + N ^ 2) := by
    have h1 : (C₂ + C₃ * C₁ ^ 2 + C₃) * N ^ 2
        ≤ max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * N ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg N)
    have h2 : (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X)
        ≤ max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hN0 hX0)
    have h3 : max (C₂ + C₃ * C₁ ^ 2 + C₃)
          (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X + N ^ 2)
        = max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * (N * X)
          + max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) * N ^ 2 := by
      ring
    rw [h3]
    linarith [hkey, h1, h2]
  have hKmax : 0 ≤ max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) :=
    le_trans hK₁0 (le_max_left _ _)
  have hfinal := quad_solve'' hKmax hN0 hmain
  calc Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.Spaces.pthIter 2 u) = X := by rw [hXdef, hBdef]
    _ ≤ (max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) + 1) * N := hfinal
    _ = (max (C₂ + C₃ * C₁ ^ 2 + C₃) (C₂ + 21 / 4 + C₃ * C₁ + 6 * C₁ + 1) + 1)
        * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => z * Work.Spaces.pz u z θ)) := by
      rw [hNdef, hfdef, hbdef, hUdef]

end Work.FTS.EllipticEst.AngAWeak
