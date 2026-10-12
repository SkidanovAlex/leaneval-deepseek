import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.Notation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxPairMode
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-277 — D1 item (c2): the τ-pairing identification

`SmallBoxPairMomentum.q4PairWord_eq_fourier_integral` puts the position-space pair word in
momentum form, `q4PairWord = Σ_{q∈pairSet} ∫_u 𝓕W₁(u)𝓕(pairFibreDens_q)(−u)du`.  The
remaining D1 step is the pointwise (in `u`) identification of `Σ_q 𝓕(pairFibreDens_q)(−u)`
with the anti-diagonal τ-pairing quadratic form of FS `lm:appbogolubov`,

    ⟨Φ, b_p†b_{−p}†Φ⟩ = Σ_{q∈pairSet} 𝓕(pairFibreDens_q)(−u) ,      p = 2πu,

where `b_p† = |B|^{−1}a†(g_p)a(1_B)` is the corpus's one-body mode operator with the
`Q_B`-projected χ-momentum mode `g_p = qMode ℓ p` (`SmallBoxPairMode`).

The module proves the identity by reducing BOTH sides to the same explicit expression

    Σ_{q∈pairSet} ∫_{r2} (∫∫ χ(y)χ(z)e^{i⟨p,y−z⟩}(Q_jQ_iΦ)(ins2 y z r2) dydz)
                       · (∫∫ Φ(ins2 u w r2) du dw) ,

the τ-side via the double peel + the two-slot projection identity, the Fourier side via the
shear change of variables in `𝓕`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators Convolution FourierTransform

namespace Submission

open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Vector-valued peel lemmas (generic over the target space) -/

/-- **Generic one-slot peel.**  For an integrable `E`-valued function on the `N`-box, the box
integral is the iterated integral over the `i`-th coordinate and the remaining `N−1`
coordinates. -/
lemma abox_integral_peel_gen {n : ℕ} {ℓ : ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (i : Fin (n + 1)) (F : X (n + 1) → E)
    (hF : IntegrableOn F (abox (n + 1) ℓ) volume) :
    (∫ x in abox (n + 1) ℓ, F x) =
      ∫ r : X n, (∫ y : ℝ³ in acube ℓ, F (kcInsN n i (y, r)))
        ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ)
  let ν : Measure (X n) := (volume : Measure (X n)).restrict (abox n ℓ)
  have hmp2 : MeasurePreserving (⇑(kcInsN n i)) (μ'.prod ν)
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ)) := by
    have h := MeasurePreserving.symm
      (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
      (abox_peel_mp (n := n) ℓ i)
    simpa [kcInsN, μ', ν] using h
  have hpeel : Integrable (fun p : (ℝ³ × X n) => F (kcInsN n i p)) (μ'.prod ν) := by
    change Integrable (fun p : kcE3 × X n => F (kcInsN n i p)) (μ'.prod ν)
    exact (hmp2.integrable_comp (hg := hF.aestronglyMeasurable)).mpr hF
  calc
    (∫ x in abox (n + 1) ℓ, F x)
        = ∫ x : X (n + 1), F x
            ∂((volume : Measure (X (n+1))).restrict (abox (n + 1) ℓ)) := rfl
    _ = ∫ p : ℝ³ × X n, F (kcInsN n i p) ∂(μ'.prod ν) := by
      simpa [μ', ν] using (hmp2.integral_comp' F).symm
    _ = ∫ r : X n, (∫ y : ℝ³, F (kcInsN n i (y, r)) ∂μ') ∂ν := by
      exact MeasureTheory.integral_prod_symm (f := fun p : ℝ³ × X n => F (kcInsN n i p)) hpeel
    _ = ∫ r : X n, (∫ y : ℝ³ in acube ℓ, F (kcInsN n i (y, r))) ∂ν := rfl

/-- The peeled fibre of an integrable `E`-valued function is integrable in the rest. -/
lemma abox_peel_inner_integrable_gen {n : ℕ} {ℓ : ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (i : Fin (n + 1)) (F : X (n + 1) → E)
    (hF : IntegrableOn F (abox (n + 1) ℓ) volume) :
    Integrable (fun r : X n => ∫ y in acube ℓ, F (kcInsN n i (y, r)))
      ((volume : Measure (X n)).restrict (abox n ℓ)) := by
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ)
  let ν : Measure (X n) := (volume : Measure (X n)).restrict (abox n ℓ)
  have hmp : MeasurePreserving (⇑(kcInsN n i)) (μ'.prod ν)
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ)) := by
    have h := MeasurePreserving.symm
      (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
      (abox_peel_mp (n := n) ℓ i)
    simpa [kcInsN, μ', ν] using h
  have hpeel : Integrable (fun p : ℝ³ × X n => F (kcInsN n i p)) (μ'.prod ν) := by
    change Integrable (fun p : kcE3 × X n => F (kcInsN n i p)) (μ'.prod ν)
    exact (hmp.integrable_comp (hg := hF.aestronglyMeasurable)).mpr hF
  have := hpeel.integral_prod_right (μ := μ') (ν := ν)
  simpa only [μ', ν] using this


/-- **Generic two-slot peel.** -/
lemma abox_integral_peel2_gen {p : ℕ} {ℓ : ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (i : Fin (p + 2)) (j' : Fin (p + 1))
    (F : X (p + 2) → E) (hF : IntegrableOn F (abox (p + 2) ℓ) volume) :
    (∫ x in abox (p + 2) ℓ, F x) =
      ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ, F (ins2 i j' y z r2) := by
  have h1 := abox_integral_peel_gen (i := i) (n := p + 1) (F := F) hF
  have hHint : IntegrableOn (fun r : X (p + 1) => ∫ y in acube ℓ, F (kcInsN (p + 1) i (y, r)))
      (abox (p + 1) ℓ) volume :=
    abox_peel_inner_integrable_gen (n := p + 1) (i := i) F hF
  have h2 := abox_integral_peel_gen (i := j') (n := p)
    (F := fun r : X (p + 1) => ∫ y in acube ℓ, F (kcInsN (p + 1) i (y, r))) hHint
  rw [h1]
  simpa only [ins2] using h2

/-! ## 2. The complex `b†` mode operator and its two-mode expansion -/

/-- `|B|^{-1} = (ℓ³)^{-1}` as a complex number. -/
noncomputable def boxInv (ℓ : ℝ) : ℂ := (((ℓ ^ 3 : ℝ))⁻¹ : ℂ)

/-- FS's one-body mode operator `b_g† = |B|^{−1}a†(g)a(1_B)` on `X N`, for a COMPLEX mode `g`
(the corpus's `SmallBoxTauModes.tauDag` is its `|B|^{-1/2}`-multiple with a real mode). -/
noncomputable def bDag (ℓ : ℝ) {N : ℕ} (g : ℝ³ → ℂ) (Ψ : X N → ℂ) (x : X N) : ℂ :=
  boxInv ℓ * ∑ i : Fin N, g (x i) * ∫ z in acube ℓ, Ψ (Function.update x i z)

lemma bDag_apply {N : ℕ} (ℓ : ℝ) (g : ℝ³ → ℂ) (Ψ : X N → ℂ) (x : X N) :
    bDag ℓ g Ψ x = boxInv ℓ * ∑ i : Fin N, g (x i) * ∫ z in acube ℓ,
      Ψ (Function.update x i z) := rfl

/-- The `z`-fibre of `bDag ℓ g' Ψ` at the configuration `x` with slot `i` replaced by `z`:
the `j = i` slot term is annihilated by the mean-vanishing `∫_{acube} g' = 0`, and the remaining
terms carry the two-slot update. -/
lemma integral_bDag_update {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (g' : ℝ³ → ℂ) (Ψ : X N → ℂ)
    (hg'c : Continuous g') (hΨc : Continuous Ψ)
    (hg'int : ∫ z in acube ℓ, g' z = 0) (x : X N) (i : Fin N) :
    (∫ z in acube ℓ, bDag ℓ g' Ψ (Function.update x i z))
      = boxInv ℓ * ∑ j ∈ Finset.univ.erase i, g' (x j) * ∫ z in acube ℓ, ∫ w in acube ℓ,
          Ψ (Function.update (Function.update x j w) i z) := by
  have hpt : ∀ z : ℝ³, bDag ℓ g' Ψ (Function.update x i z)
      = boxInv ℓ * ((∑ j ∈ Finset.univ.erase i, g' (x j) * ∫ w in acube ℓ,
              Ψ (Function.update (Function.update x j w) i z))
          + g' z * (∫ w in acube ℓ, Ψ (Function.update x i w))) := by
    intro z
    rw [bDag_apply]
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin N)))
      (f := fun j => g' ((Function.update x i z) j)
        * ∫ w in acube ℓ, Ψ (Function.update (Function.update x i z) j w)) (Finset.mem_univ i)
    rw [← hsplit]
    have hA : (∑ j ∈ Finset.univ.erase i, g' ((Function.update x i z) j)
        * ∫ w in acube ℓ, Ψ (Function.update (Function.update x i z) j w))
        = (∑ j ∈ Finset.univ.erase i, g' (x j) * ∫ w in acube ℓ,
              Ψ (Function.update (Function.update x j w) i z)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hupd : (fun w : ℝ³ => Ψ (Function.update (Function.update x i z) j w))
          = fun w : ℝ³ => Ψ (Function.update (Function.update x j w) i z) := by
        funext w
        rw [Function.update_comm hji.symm]
      rw [Function.update_of_ne hji, hupd]
    have hB : g' ((Function.update x i z) i) * ∫ w in acube ℓ,
        Ψ (Function.update (Function.update x i z) i w)
        = g' z * (∫ w in acube ℓ, Ψ (Function.update x i w)) := by
      have hupd : (fun w : ℝ³ => Ψ (Function.update (Function.update x i z) i w))
          = fun w : ℝ³ => Ψ (Function.update x i w) := by
        funext w
        rw [Function.update_idem]
      rw [Function.update_self, hupd]
    rw [hA, hB]
  have hfun : (fun z : ℝ³ => bDag ℓ g' Ψ (Function.update x i z))
      = fun z : ℝ³ => boxInv ℓ * ((∑ j ∈ Finset.univ.erase i, g' (x j) * ∫ w in acube ℓ,
              Ψ (Function.update (Function.update x j w) i z))
          + g' z * (∫ w in acube ℓ, Ψ (Function.update x i w))) := funext hpt
  have hcontA : Continuous (fun z : ℝ³ => ∑ j ∈ Finset.univ.erase i, g' (x j) * ∫ w in acube ℓ,
      Ψ (Function.update (Function.update x j w) i z)) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul
      (continuous_parametric_integral_of_continuous
        (f := fun (z : ℝ³) (w : ℝ³) => Ψ (Function.update (Function.update x j w) i z))
        (by fun_prop) (acube_compact hℓ))
  have hcontB : Continuous (fun z : ℝ³ => g' z * (∫ w in acube ℓ, Ψ (Function.update x i w))) :=
    hg'c.mul continuous_const
  rw [hfun, MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_add
    (f := fun z : ℝ³ => ∑ j ∈ Finset.univ.erase i, g' (x j) * ∫ w in acube ℓ,
      Ψ (Function.update (Function.update x j w) i z))
    (g := fun z : ℝ³ => g' z * (∫ w in acube ℓ, Ψ (Function.update x i w)))
    (ContinuousOn.integrableOn_compact (acube_compact hℓ) hcontA.continuousOn)
    (ContinuousOn.integrableOn_compact (acube_compact hℓ) hcontB.continuousOn)]
  rw [MeasureTheory.integral_finsetSum (s := Finset.univ.erase i)
    (f := fun j (z : ℝ³) => g' (x j) * ∫ w in acube ℓ,
      Ψ (Function.update (Function.update x j w) i z))]
  · have hsum2 : (∑ j ∈ Finset.univ.erase i, ∫ z in acube ℓ, g' (x j) * ∫ w in acube ℓ,
        Ψ (Function.update (Function.update x j w) i z))
        = ∑ j ∈ Finset.univ.erase i, g' (x j) * ∫ z in acube ℓ, ∫ w in acube ℓ,
            Ψ (Function.update (Function.update x j w) i z) :=
      Finset.sum_congr rfl fun j _ => MeasureTheory.integral_const_mul _ _
    rw [hsum2, MeasureTheory.integral_mul_const, hg'int, zero_mul, add_zero]
  · intro j _
    exact ContinuousOn.integrableOn_compact (acube_compact hℓ)
      (continuous_const.mul (continuous_parametric_integral_of_continuous
        (f := fun (z : ℝ³) (w : ℝ³) => Ψ (Function.update (Function.update x j w) i z))
        (by fun_prop) (acube_compact hℓ))).continuousOn

/-- **The two-mode expansion of `bDag`.**  For a mean-free mode `g'` the double application
`b_g† b_{g'}†` becomes the sum over ordered pairs of distinct slots with the two-slot update. -/
lemma bDag_double {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (g g' : ℝ³ → ℂ) (Ψ : X N → ℂ)
    (hg'c : Continuous g') (hΨc : Continuous Ψ)
    (hg'int : ∫ z in acube ℓ, g' z = 0) (x : X N) :
    bDag ℓ g (bDag ℓ g' Ψ) x = boxInv ℓ ^ 2 * ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        g (x i) * g' (x j) * ∫ z in acube ℓ, ∫ w in acube ℓ,
          Ψ (Function.update (Function.update x j w) i z) := by
  have hsum : (∑ i : Fin N, g (x i) * ∫ z in acube ℓ, bDag ℓ g' Ψ (Function.update x i z))
      = ∑ i : Fin N, boxInv ℓ * (g (x i) * ∑ j ∈ Finset.univ.erase i, g' (x j) *
          ∫ z in acube ℓ, ∫ w in acube ℓ, Ψ (Function.update (Function.update x j w) i z)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_bDag_update hℓ g' Ψ hg'c hΨc hg'int x i]
    ring
  rw [bDag_apply, hsum, ← Finset.mul_sum, ← mul_assoc, pow_two]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


/-! ## 3. The two-slot update identities and the slot objects -/

/-- The double update at the two slots of `ins2` returns an `ins2`. -/
lemma upd_upd_ins2 {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) (a b z w : ℝ³) (r2 : X p) :
    Function.update (Function.update (ins2 i j' a b r2) (i.succAbove j') w) i z
      = ins2 i j' z w r2 := by
  rw [ins2_update_succ, ins2_update_i]

/-- The `(y,z)`-slot factor of the peeled pair integrand. -/
noncomputable def pairSlot {p : ℕ} (ℓ : ℝ) (G : X (p + 2) → ℝ) (g g' : ℝ³ → ℂ)
    (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) : ℂ :=
  ∫ y in acube ℓ, ∫ z in acube ℓ, g y * g' z * (G (ins2 i j' y z r2) : ℂ)

/-- The `(u,w)`-slot factor of the peeled pair integrand. -/
noncomputable def pairMean {p : ℕ} (ℓ : ℝ) (G : X (p + 2) → ℝ)
    (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) : ℂ :=
  ∫ y in acube ℓ, ∫ z in acube ℓ, (G (ins2 i j' y z r2) : ℂ)

-- (generic Fubini for centred-cube iterated integrals is stated below in the ℂ and ℝ cases)

/-- Fubini for two iterated centred-cube integrals of a continuous ℝ-valued kernel. -/
lemma integral_swap_acube_real {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ³ → ℝ³ → ℝ}
    (hF : Continuous (Function.uncurry F)) :
    (∫ y in acube ℓ, ∫ z in acube ℓ, F y z) = ∫ z in acube ℓ, ∫ y in acube ℓ, F y z := by
  set ν : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ) with hν
  have hprod : (ν.prod ν)
      = (volume : Measure (ℝ³ × ℝ³)).restrict (acube ℓ ×ˢ acube ℓ) := by
    rw [hν, MeasureTheory.Measure.volume_eq_prod ℝ³ ℝ³, Measure.prod_restrict]
  have hintOn : IntegrableOn (Function.uncurry F) (acube ℓ ×ˢ acube ℓ) volume :=
    ContinuousOn.integrableOn_compact ((acube_compact hℓ).prod (acube_compact hℓ)) hF.continuousOn
  have hint : Integrable (Function.uncurry F) (ν.prod ν) := by
    rw [hprod]; exact hintOn
  exact MeasureTheory.integral_integral_swap hint

/-- Fubini for two iterated centred-cube integrals of a continuous ℂ-valued kernel. -/
lemma integral_swap_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ³ → ℝ³ → ℂ}
    (hF : Continuous (Function.uncurry F)) :
    (∫ y in acube ℓ, ∫ z in acube ℓ, F y z) = ∫ z in acube ℓ, ∫ y in acube ℓ, F y z := by
  set ν : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ) with hν
  have hprod : (ν.prod ν)
      = (volume : Measure (ℝ³ × ℝ³)).restrict (acube ℓ ×ˢ acube ℓ) := by
    rw [hν, MeasureTheory.Measure.volume_eq_prod ℝ³ ℝ³, Measure.prod_restrict]
  have hintOn : IntegrableOn (Function.uncurry F) (acube ℓ ×ˢ acube ℓ) volume :=
    ContinuousOn.integrableOn_compact ((acube_compact hℓ).prod (acube_compact hℓ))
      hF.continuousOn
  have hint : Integrable (Function.uncurry F) (ν.prod ν) := by
    rw [hprod]; exact hintOn
  exact MeasureTheory.integral_integral_swap hint

/-- Continuity of `x ↦ Function.update x i v` (as a function of the pair `(x,v)`). -/
lemma continuous_update_prod {n : ℕ} (i : Fin n) :
    Continuous (fun q : X n × ℝ³ => Function.update q.1 i q.2) := by
  rw [continuous_pi_iff]
  intro k
  by_cases hk : k = i
  · subst hk
    simpa only [Function.update_self] using continuous_snd
  · have hc : Continuous (fun a : X n × ℝ³ => a.1 k) :=
      (continuous_apply k).comp continuous_fst
    simpa only [Function.update_of_ne hk] using hc

/-- **The single-pair peel.**  The box integral of the peeled pair integrand (with the two slots
`i` and `i.succAbove j'`) factors into the `(y,z)`-slot integral against the mode product and the
`(u,w)`-slot mean of the state. -/
lemma peel_pair {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ)
    (g g' : ℝ³ → ℂ) (hgc : Continuous g) (hg'c : Continuous g')
    (i : Fin (p + 2)) (j' : Fin (p + 1)) :
    (∫ x in abox (p + 2) ℓ, (Φ x : ℂ) * g (x i) * g' (x (i.succAbove j'))
        * (∫ z in acube ℓ, ∫ w in acube ℓ,
            (Φ (Function.update (Function.update x (i.succAbove j') w) i z) : ℂ)))
      = ∫ r2 in abox p ℓ, pairSlot ℓ Φ g g' i j' r2 * pairMean ℓ Φ i j' r2 := by
  have hΦre : Continuous (fun x : X (p + 2) => (Φ x : ℂ)) := Complex.continuous_ofReal.comp hΦc
  have hupd1 : Continuous (fun q : (X (p + 2) × ℝ³) × ℝ³ =>
      Function.update q.1.1 (i.succAbove j') q.2) :=
    (continuous_update_prod (i.succAbove j')).comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hupd2 : Continuous (fun q : (X (p + 2) × ℝ³) × ℝ³ =>
      Function.update (Function.update q.1.1 (i.succAbove j') q.2) i q.1.2) :=
    (continuous_update_prod i).comp (hupd1.prodMk (continuous_snd.comp continuous_fst))
  have hcontW : Continuous (fun q : X (p + 2) × ℝ³ =>
      ∫ w in acube ℓ, (Φ (Function.update (Function.update q.1 (i.succAbove j') w) i q.2) : ℂ)) := by
    refine continuous_parametric_integral_of_continuous
      (f := fun (q : X (p + 2) × ℝ³) (w : ℝ³) =>
        (Φ (Function.update (Function.update q.1 (i.succAbove j') w) i q.2) : ℂ))
      ?_ (acube_compact hℓ)
    change Continuous (fun p : ((X (p + 2) × ℝ³) × ℝ³) =>
        (Φ (Function.update (Function.update p.1.1 (i.succAbove j') p.2) i p.1.2) : ℂ))
    exact (Complex.continuous_ofReal.comp hΦc).comp hupd2
  have hcontZ : Continuous (fun x : X (p + 2) =>
      ∫ z in acube ℓ, ∫ w in acube ℓ,
        (Φ (Function.update (Function.update x (i.succAbove j') w) i z) : ℂ)) := by
    refine continuous_parametric_integral_of_continuous
      (f := fun (x : X (p + 2)) (z : ℝ³) =>
        ∫ w in acube ℓ, (Φ (Function.update (Function.update x (i.succAbove j') w) i z) : ℂ))
      ?_ (acube_compact hℓ)
    change Continuous (fun q : X (p + 2) × ℝ³ =>
      ∫ w in acube ℓ, (Φ (Function.update (Function.update q.1 (i.succAbove j') w) i q.2) : ℂ))
    exact hcontW
  set F : X (p + 2) → ℂ := fun x => (Φ x : ℂ) * g (x i) * g' (x (i.succAbove j'))
      * (∫ z in acube ℓ, ∫ w in acube ℓ,
          (Φ (Function.update (Function.update x (i.succAbove j') w) i z) : ℂ)) with hFdef
  have hFcont : Continuous F := by
    rw [hFdef]
    exact ((hΦre.mul (hgc.comp (continuous_apply i))).mul
      (hg'c.comp (continuous_apply (i.succAbove j')))).mul hcontZ
  have hgoal : (∫ x in abox (p + 2) ℓ, (Φ x : ℂ) * g (x i) * g' (x (i.succAbove j'))
        * (∫ z in acube ℓ, ∫ w in acube ℓ,
            (Φ (Function.update (Function.update x (i.succAbove j') w) i z) : ℂ))) = ∫ x in abox (p + 2) ℓ, F x :=
    rfl
  rw [hgoal, abox_integral_peel2_gen (i := i) (j' := j') (F := F)
    (ContinuousOn.integrableOn_compact (abox_compact (p + 2) hℓ) hFcont.continuousOn)]
  have hslot : ∀ y z : ℝ³, ∀ r2 : X p, F (ins2 i j' y z r2)
      = ((Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)) * pairMean ℓ Φ i j' r2 := by
    intro y z r2
    rw [hFdef]
    simp only []
    have h1 : (ins2 i j' y z r2) i = y := ins2_apply_i i j' y z r2
    have h2 : (ins2 i j' y z r2) (i.succAbove j') = z := ins2_apply_succ i j' y z r2
    have h3 : (∫ z' in acube ℓ, ∫ w in acube ℓ,
        (Φ (Function.update (Function.update (ins2 i j' y z r2) (i.succAbove j') w) i z') : ℂ))
        = pairMean ℓ Φ i j' r2 := by
      rw [pairMean]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z' => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only []
      rw [upd_upd_ins2]
    rw [h1, h2, h3]
    ring
  simp only [hslot]
  have hswap : ∀ r2 : X p, (∫ z in acube ℓ, ∫ y in acube ℓ,
        (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)) = pairSlot ℓ Φ g g' i j' r2 := by
    intro r2
    have hupd : Continuous (fun q : ℝ³ × ℝ³ => ins2 i j' q.1 q.2 r2) :=
      (contDiff_ins2 i j').continuous.comp
        ((continuous_fst.prodMk continuous_snd).prodMk continuous_const)
    have hcont : Continuous (Function.uncurry
        (fun y z : ℝ³ => (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z))) := by
      change Continuous (fun q : ℝ³ × ℝ³ =>
        (Φ (ins2 i j' q.1 q.2 r2) : ℂ) * (g q.1 * g' q.2))
      exact (hΦre.comp hupd).mul ((hgc.comp continuous_fst).mul (hg'c.comp continuous_snd))
    rw [← integral_swap_acube hℓ hcont, pairSlot]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only []
    ring
  refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
  simp only []
  have hinner : (∫ z in acube ℓ, ∫ y in acube ℓ,
        ((Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)) * pairMean ℓ Φ i j' r2)
      = (∫ z in acube ℓ, (∫ y in acube ℓ,
          (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)) * pairMean ℓ Φ i j' r2) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by
      simp only []
      rw [MeasureTheory.integral_mul_const])
  rw [show (∫ z in acube ℓ, ∫ y in acube ℓ,
          ((Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)) * pairMean ℓ Φ i j' r2)
      = ∫ z in acube ℓ, (∫ y in acube ℓ,
          (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)) * pairMean ℓ Φ i j' r2 from hinner,
    MeasureTheory.integral_mul_const, hswap r2]


/-- Continuity of the double slot update as a function of `(x, w, z)`. -/
lemma continuous_update_update {n : ℕ} (i j : Fin n) :
    Continuous (fun q : (X n × ℝ³) × ℝ³ =>
      Function.update (Function.update q.1.1 j q.2) i q.1.2) := by
  have h1 : Continuous (fun q : (X n × ℝ³) × ℝ³ => Function.update q.1.1 j q.2) :=
    (continuous_update_prod j).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  exact (continuous_update_prod i).comp (h1.prodMk (continuous_snd.comp continuous_fst))

/-- Continuity of the peeled-state mean `x ↦ ∫_z∫_w Φ(x_{j←w, i←z})`. -/
lemma continuous_doubleUpdate_integral {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) (i j : Fin (p + 2)) :
    Continuous (fun x : X (p + 2) => ∫ z in acube ℓ, ∫ w in acube ℓ,
      (Φ (Function.update (Function.update x j w) i z) : ℂ)) := by
  have hΦre : Continuous (fun x : X (p + 2) => (Φ x : ℂ)) := Complex.continuous_ofReal.comp hΦc
  have hone : Continuous (fun q : X (p + 2) × ℝ³ =>
      ∫ w in acube ℓ, (Φ (Function.update (Function.update q.1 j w) i q.2) : ℂ)) := by
    refine continuous_parametric_integral_of_continuous
      (f := fun (q : X (p + 2) × ℝ³) (w : ℝ³) =>
        (Φ (Function.update (Function.update q.1 j w) i q.2) : ℂ))
      ?_ (acube_compact hℓ)
    change Continuous (fun qw : ((X (p + 2) × ℝ³) × ℝ³) =>
      (Φ (Function.update (Function.update qw.1.1 j qw.2) i qw.1.2) : ℂ))
    exact hΦre.comp (continuous_update_update i j)
  refine continuous_parametric_integral_of_continuous
    (f := fun (x : X (p + 2)) (z : ℝ³) =>
      ∫ w in acube ℓ, (Φ (Function.update (Function.update x j w) i z) : ℂ))
    ?_ (acube_compact hℓ)
  change Continuous (fun q : X (p + 2) × ℝ³ =>
    ∫ w in acube ℓ, (Φ (Function.update (Function.update q.1 j w) i q.2) : ℂ))
  exact hone

/-- The reindexing `∑_{j ∈ univ.erase i} = ∑_{j' : Fin N} (i.succAbove j')`. -/
lemma sum_erase_eq_succAbove {N : ℕ} (F : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    (∑ j ∈ Finset.univ.erase i, F j) = ∑ j' : Fin N, F (i.succAbove j') := by
  have h1 := Fin.sum_univ_succAbove F i
  have h2 : (∑ j ∈ Finset.univ.erase i, F j) + F i = ∑ j : Fin (N + 1), F j :=
    Finset.sum_erase_add (Finset.univ : Finset (Fin (N + 1))) F (Finset.mem_univ i)
  have h3 : (∑ j' : Fin N, F (i.succAbove j')) + F i = ∑ j : Fin (N + 1), F j := by
    rw [add_comm]; exact h1.symm
  exact add_right_cancel (h2.trans h3.symm)

/-- **Step B of the `(c2)` identification**: the τ-pairing quadratic form, peeled into the
`(i, i.succAbove j')` pair structure. -/
theorem tau_pair_side {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ)
    (g g' : ℝ³ → ℂ) (hgc : Continuous g) (hg'c : Continuous g')
    (hg'int : ∫ z in acube ℓ, g' z = 0) :
    (∫ x in abox (p + 2) ℓ, (Φ x : ℂ) * bDag ℓ g (bDag ℓ g' (fun y => (Φ y : ℂ))) x)
      = boxInv ℓ ^ 2 * ∑ i : Fin (p + 2), ∑ j' : Fin (p + 1),
          ∫ r2 in abox p ℓ, pairSlot ℓ Φ g g' i j' r2 * pairMean ℓ Φ i j' r2 := by
  have hΦCc : Continuous (fun y : X (p + 2) => (Φ y : ℂ)) := Complex.continuous_ofReal.comp hΦc
  have hpt : ∀ x : X (p + 2), (Φ x : ℂ) * bDag ℓ g (bDag ℓ g' (fun y => (Φ y : ℂ))) x
      = boxInv ℓ ^ 2 * ∑ i : Fin (p + 2), ∑ j ∈ Finset.univ.erase i,
          (Φ x : ℂ) * g (x i) * g' (x j) * (∫ z in acube ℓ, ∫ w in acube ℓ,
            (Φ (Function.update (Function.update x j w) i z) : ℂ)) := by
    intro x
    rw [bDag_double hℓ g g' (fun y => (Φ y : ℂ)) hg'c hΦCc hg'int x]
    rw [show (Φ x : ℂ) * (boxInv ℓ ^ 2 * ∑ i : Fin (p + 2), ∑ j ∈ Finset.univ.erase i,
            g (x i) * g' (x j) * (∫ z in acube ℓ, ∫ w in acube ℓ,
              (Φ (Function.update (Function.update x j w) i z) : ℂ)))
        = boxInv ℓ ^ 2 * ((Φ x : ℂ) * ∑ i : Fin (p + 2), ∑ j ∈ Finset.univ.erase i,
            g (x i) * g' (x j) * (∫ z in acube ℓ, ∫ w in acube ℓ,
              (Φ (Function.update (Function.update x j w) i z) : ℂ))) from by ring]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [show (fun x : X (p + 2) => (Φ x : ℂ) * bDag ℓ g (bDag ℓ g' (fun y => (Φ y : ℂ))) x)
      = fun x : X (p + 2) => boxInv ℓ ^ 2 * ∑ i : Fin (p + 2), ∑ j ∈ Finset.univ.erase i,
          (Φ x : ℂ) * g (x i) * g' (x j) * (∫ z in acube ℓ, ∫ w in acube ℓ,
            (Φ (Function.update (Function.update x j w) i z) : ℂ)) from funext hpt]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  have hInt : ∀ i : Fin (p + 2), (∫ x in abox (p + 2) ℓ, ∑ j ∈ Finset.univ.erase i,
        (Φ x : ℂ) * g (x i) * g' (x j) * (∫ z in acube ℓ, ∫ w in acube ℓ,
          (Φ (Function.update (Function.update x j w) i z) : ℂ)))
      = ∑ j' : Fin (p + 1), ∫ r2 in abox p ℓ, pairSlot ℓ Φ g g' i j' r2 * pairMean ℓ Φ i j' r2 := by
    intro i
    rw [MeasureTheory.integral_finsetSum]
    · rw [sum_erase_eq_succAbove]
      refine Finset.sum_congr rfl fun j' _ => ?_
      exact peel_pair hℓ hΦc g g' hgc hg'c i j'
    · intro j _
      exact ContinuousOn.integrableOn_compact (abox_compact (p + 2) hℓ)
        (((Complex.continuous_ofReal.comp hΦc).mul (hgc.comp (continuous_apply i))).mul
          (hg'c.comp (continuous_apply j)) |>.mul
            (continuous_doubleUpdate_integral hℓ hΦc i j)).continuousOn
  rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
    (f := fun i (x : X (p + 2)) => ∑ j ∈ Finset.univ.erase i,
      (Φ x : ℂ) * g (x i) * g' (x j) * (∫ z in acube ℓ, ∫ w in acube ℓ,
        (Φ (Function.update (Function.update x j w) i z) : ℂ)))]
  · exact Finset.sum_congr rfl fun i _ => hInt i
  · intro i _
    exact ContinuousOn.integrableOn_compact (abox_compact (p + 2) hℓ)
      (continuous_finsetSum _ fun j _ =>
        (((Complex.continuous_ofReal.comp hΦc).mul (hgc.comp (continuous_apply i))).mul
          (hg'c.comp (continuous_apply j))).mul
            (continuous_doubleUpdate_integral hℓ hΦc i j)).continuousOn


/-! ## 4. Slot constancy and mean-vanishing (the `Q_B` structure) -/

/-- `aP ℓ i Φ` at `ins2` is independent of the `i`-slot value. -/
lemma aP_const_slot_i {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    (hΦc : Continuous Φ) (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) (y z : ℝ³) :
    (aP ℓ i Φ) (ins2 i j' y z r2) = (aP ℓ i Φ) (ins2 i j' 0 z r2) := by
  rw [show ins2 i j' y z r2 = Function.update (ins2 i j' 0 z r2) i y from
    (ins2_update_i i j' 0 y z r2).symm]
  exact aP_const_in_coord hℓ i hΦc _ y

/-- `aP ℓ (i.succAbove j') Φ` at `ins2` is independent of the `j`-slot value. -/
lemma aP_const_slot_j {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    (hΦc : Continuous Φ) (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) (y z : ℝ³) :
    (aP ℓ (i.succAbove j') Φ) (ins2 i j' y z r2)
      = (aP ℓ (i.succAbove j') Φ) (ins2 i j' y 0 r2) := by
  rw [show ins2 i j' y z r2 = Function.update (ins2 i j' y 0 r2) (i.succAbove j') z from
    (ins2_update_succ i j' y 0 z r2).symm]
  exact aP_const_in_coord hℓ (i.succAbove j') hΦc _ z

/-- **The `Q_B` mean-vanishing in a single slot**: for any slot `j` and any configuration `x₀`,
the `j`-slot fibre of `aQ ℓ j Φ` has zero mean over the centred cube. -/
lemma integral_aQ_of_update {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    (hΦc : Continuous Φ) (j : Fin (p + 2)) (x₀ : X (p + 2)) :
    (∫ z in acube ℓ, (aQ ℓ j Φ) (Function.update x₀ j z)) = 0 := by
  have h1 : (∫ z in acube ℓ, Φ (Function.update x₀ j z)) = ℓ ^ 3 * aP ℓ j Φ x₀ := by
    simp only [aP]
    field_simp
  have h2 : (∫ z in acube ℓ, (aP ℓ j Φ) (Function.update x₀ j z))
      = ℓ ^ 3 * aP ℓ j Φ x₀ := by
    rw [show (fun z : ℝ³ => (aP ℓ j Φ) (Function.update x₀ j z))
        = fun _ : ℝ³ => aP ℓ j Φ x₀ from
          funext fun z => aP_const_in_coord hℓ j hΦc x₀ z]
    rw [MeasureTheory.integral_const, real_volume_acube ℓ hℓ.le, smul_eq_mul]
  have hc1 : Continuous (fun z : ℝ³ => Φ (Function.update x₀ j z)) :=
    hΦc.comp ((continuous_update_prod j).comp (continuous_const.prodMk continuous_id))
  have hc2 : Continuous (fun z : ℝ³ => (aP ℓ j Φ) (Function.update x₀ j z)) :=
    (aP_continuous hℓ j hΦc).comp
      ((continuous_update_prod j).comp (continuous_const.prodMk continuous_id))
  have hsub : (∫ z in acube ℓ, (aQ ℓ j Φ) (Function.update x₀ j z))
      = (∫ z in acube ℓ, Φ (Function.update x₀ j z))
        - (∫ z in acube ℓ, (aP ℓ j Φ) (Function.update x₀ j z)) := by
    rw [show (fun z : ℝ³ => (aQ ℓ j Φ) (Function.update x₀ j z))
        = fun z : ℝ³ => Φ (Function.update x₀ j z)
            - (aP ℓ j Φ) (Function.update x₀ j z) from funext fun z => rfl]
    exact MeasureTheory.integral_sub
      (ContinuousOn.integrableOn_compact (acube_compact hℓ) hc1.continuousOn)
      (ContinuousOn.integrableOn_compact (acube_compact hℓ) hc2.continuousOn)
  rw [hsub, h1, h2, sub_self]

/-- `aQ ℓ i Φ` is mean-free in the `i`-slot, in the `ins2` parametrisation. -/
lemma slot_aQ_mean_zero {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    (hΦc : Continuous Φ) (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) (z : ℝ³) :
    (∫ y in acube ℓ, (aQ ℓ i Φ) (ins2 i j' y z r2)) = 0 := by
  rw [show (fun y : ℝ³ => (aQ ℓ i Φ) (ins2 i j' y z r2))
      = fun y : ℝ³ => (aQ ℓ i Φ) (Function.update (ins2 i j' 0 z r2) i y) from
        funext fun y => congrArg (aQ ℓ i Φ) (ins2_update_i i j' 0 y z r2).symm]
  exact integral_aQ_of_update hℓ hΦc i _

/-- `aQ ℓ (i.succAbove j') Φ` is mean-free in the `j`-slot, in the `ins2` parametrisation. -/
lemma slot_aQ_mean_zero_j {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    (hΦc : Continuous Φ) (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) (y : ℝ³) :
    (∫ z in acube ℓ, (aQ ℓ (i.succAbove j') Φ) (ins2 i j' y z r2)) = 0 := by
  rw [show (fun z : ℝ³ => (aQ ℓ (i.succAbove j') Φ) (ins2 i j' y z r2))
      = fun z : ℝ³ => (aQ ℓ (i.succAbove j') Φ)
          (Function.update (ins2 i j' y 0 r2) (i.succAbove j') z) from
        funext fun z => congrArg (aQ ℓ (i.succAbove j') Φ) (ins2_update_succ i j' y 0 z r2).symm]
  exact integral_aQ_of_update hℓ hΦc (i.succAbove j') _

/-- Continuity of `y ↦ ins2 i j' y z r2`. -/
lemma continuous_ins2_fst {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) (z : ℝ³) (r2 : X p) :
    Continuous (fun y : ℝ³ => ins2 i j' y z r2) :=
  (contDiff_ins2 i j').continuous.comp
    ((continuous_id.prodMk continuous_const).prodMk continuous_const)

/-- Continuity of `z ↦ ins2 i j' y z r2`. -/
lemma continuous_ins2_snd {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) (y : ℝ³) (r2 : X p) :
    Continuous (fun z : ℝ³ => ins2 i j' y z r2) :=
  (contDiff_ins2 i j').continuous.comp
    ((continuous_const.prodMk continuous_id).prodMk continuous_const)

/-- Continuity of the uncurried two-slot insertion. -/
lemma continuous_ins2_uncurry {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) :
    Continuous (Function.uncurry (fun y z : ℝ³ => ins2 i j' y z r2)) :=
  (contDiff_ins2 i j').continuous.comp
    ((continuous_fst.prodMk continuous_snd).prodMk continuous_const)

/-- **Mean-vanishing of the pair slot kernel in the `j`-slot.** -/
lemma slot_H_mean_zero_j {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    (hΦc : Continuous Φ) (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) (y : ℝ³) :
    (∫ z in acube ℓ, (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2)) = 0 :=
  slot_aQ_mean_zero_j hℓ (aQ_continuous hℓ i hΦc) i j' r2 y

/-- **Mean-vanishing of the pair slot kernel in the `i`-slot.** -/
lemma slot_H_mean_zero_i {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    (hΦc : Continuous Φ) (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) (z : ℝ³) :
    (∫ y in acube ℓ, (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2)) = 0 := by
  have hΨc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hsub : (∫ y in acube ℓ, (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2))
      = (∫ y in acube ℓ, (aQ ℓ i Φ) (ins2 i j' y z r2))
        - (∫ y in acube ℓ, (aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2)) := by
    rw [show (fun y : ℝ³ => (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2))
        = fun y : ℝ³ => (aQ ℓ i Φ) (ins2 i j' y z r2)
            - (aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) from
          funext fun y => rfl]
    refine MeasureTheory.integral_sub
      (ContinuousOn.integrableOn_compact (acube_compact hℓ)
        ((hΨc.comp (continuous_ins2_fst i j' z r2)).continuousOn))
      (ContinuousOn.integrableOn_compact (acube_compact hℓ)
        (((aP_continuous hℓ (i.succAbove j') hΨc).comp
          (continuous_ins2_fst i j' z r2)).continuousOn))
  have hAP : (∫ y in acube ℓ, (aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2))
      = ℓ⁻¹ ^ 3 * (∫ t in acube ℓ, ∫ y in acube ℓ, (aQ ℓ i Φ) (ins2 i j' y t r2)) := by
    have hpt : ∀ y : ℝ³, (aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2)
        = ℓ⁻¹ ^ 3 * (∫ t in acube ℓ, (aQ ℓ i Φ) (ins2 i j' y t r2)) := by
      intro y
      simp only [aP]
      rw [show (∫ t in acube ℓ,
            (aQ ℓ i Φ) (Function.update (ins2 i j' y z r2) (i.succAbove j') t))
          = ∫ t in acube ℓ, (aQ ℓ i Φ) (ins2 i j' y t r2) from
        integral_congr_ae (Filter.Eventually.of_forall fun t => by
          simp only []; rw [ins2_update_succ])]
      ring
    rw [show (fun y : ℝ³ => (aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2))
        = fun y : ℝ³ => ℓ⁻¹ ^ 3 * (∫ t in acube ℓ, (aQ ℓ i Φ) (ins2 i j' y t r2)) from
          funext hpt]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact integral_swap_acube_real hℓ
      (F := fun y t : ℝ³ => (aQ ℓ i Φ) (ins2 i j' y t r2)) (by
        change Continuous (fun q : ℝ³ × ℝ³ => (aQ ℓ i Φ) (ins2 i j' q.1 q.2 r2))
        exact hΨc.comp (continuous_ins2_uncurry i j' r2))
  have hzero : (∫ t in acube ℓ, ∫ y in acube ℓ, (aQ ℓ i Φ) (ins2 i j' y t r2)) = 0 := by
    rw [show (∫ t in acube ℓ, ∫ y in acube ℓ, (aQ ℓ i Φ) (ins2 i j' y t r2))
        = ∫ t in acube ℓ, (0 : ℝ) from
          integral_congr_ae (Filter.Eventually.of_forall fun t =>
            slot_aQ_mean_zero hℓ hΦc i j' r2 t)]
    rw [MeasureTheory.integral_zero]
  rw [hsub, hAP, hzero, mul_zero, slot_aQ_mean_zero hℓ hΦc i j' r2 z, sub_zero]


/-! ## 5. The core two-slot identity -/

/-- Complexified `i`-slot mean-vanishing of the pair fibre. -/
lemma ofReal_slot_H_mean_zero_i {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    (hΦc : Continuous Φ) (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) (z : ℝ³) :
    (∫ y in acube ℓ,
      (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)) = 0 := by
  have hcont : Continuous (fun y : ℝ³ =>
      (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2)) :=
    (aQ_continuous hℓ (i.succAbove j') (aQ_continuous hℓ i hΦc)).comp
      (continuous_ins2_fst i j' z r2)
  have hcast : (∫ y in acube ℓ, (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ))
      = (((∫ y in acube ℓ, (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2)) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm (φ := fun y : ℝ³ =>
      (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2))
      (ContinuousOn.integrableOn_compact (acube_compact hℓ) hcont.continuousOn)
  rw [hcast, slot_H_mean_zero_i hℓ hΦc i j' r2 z, Complex.ofReal_zero]

/-- Complexified `j`-slot mean-vanishing of the pair fibre. -/
lemma ofReal_slot_H_mean_zero_j {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    (hΦc : Continuous Φ) (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) (y : ℝ³) :
    (∫ z in acube ℓ,
      (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)) = 0 := by
  have hcont : Continuous (fun z : ℝ³ =>
      (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2)) :=
    (aQ_continuous hℓ (i.succAbove j') (aQ_continuous hℓ i hΦc)).comp
      (continuous_ins2_snd i j' y r2)
  have hcast : (∫ z in acube ℓ, (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ))
      = (((∫ z in acube ℓ, (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2)) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm (φ := fun z : ℝ³ =>
      (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2))
      (ContinuousOn.integrableOn_compact (acube_compact hℓ) hcont.continuousOn)
  rw [hcast, slot_H_mean_zero_j hℓ hΦc i j' r2 y, Complex.ofReal_zero]


/-- Linearity of the integral of a (right-associated) three-term sum. -/
lemma integral_add_three {α : Type*} [MeasurableSpace α] {μ : Measure α} (f g h : α → ℂ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ a, f a + (g a + h a) ∂μ) = (∫ a, f a ∂μ) + ((∫ a, g a ∂μ) + ∫ a, h a ∂μ) := by
  have hgh : (∫ a, g a + h a ∂μ) = (∫ a, g a ∂μ) + ∫ a, h a ∂μ :=
    MeasureTheory.integral_add hg hh
  have hfgh : (∫ a, f a + (g a + h a) ∂μ) = (∫ a, f a ∂μ) + ∫ a, g a + h a ∂μ :=
    MeasureTheory.integral_add hf (hg.add hh)
  rw [hfgh, hgh]

/-- Additivity of the iterated centred-cube double integral over a two-term sum. -/
lemma double_integral_add {ℓ : ℝ} (hℓ : 0 < ℓ) (A B : ℝ³ → ℝ³ → ℂ)
    (hA : Continuous (Function.uncurry A)) (hB : Continuous (Function.uncurry B)) :
    (∫ y in acube ℓ, ∫ z in acube ℓ, A y z + B y z)
      = (∫ y in acube ℓ, ∫ z in acube ℓ, A y z)
        + ∫ y in acube ℓ, ∫ z in acube ℓ, B y z := by
  have hzA : ∀ y : ℝ³, Integrable (fun z : ℝ³ => A y z)
      ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    fun y => ContinuousOn.integrableOn_compact (acube_compact hℓ)
      ((hA.comp (continuous_const.prodMk continuous_id)).continuousOn)
  have hzB : ∀ y : ℝ³, Integrable (fun z : ℝ³ => B y z)
      ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    fun y => ContinuousOn.integrableOn_compact (acube_compact hℓ)
      ((hB.comp (continuous_const.prodMk continuous_id)).continuousOn)
  have hyA : Integrable (fun y : ℝ³ => ∫ z in acube ℓ, A y z)
      ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ContinuousOn.integrableOn_compact (acube_compact hℓ)
      ((continuous_parametric_integral_of_continuous hA (acube_compact hℓ)).continuousOn)
  have hyB : Integrable (fun y : ℝ³ => ∫ z in acube ℓ, B y z)
      ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ContinuousOn.integrableOn_compact (acube_compact hℓ)
      ((continuous_parametric_integral_of_continuous hB (acube_compact hℓ)).continuousOn)
  rw [show (∫ y in acube ℓ, ∫ z in acube ℓ, A y z + B y z)
      = ∫ y in acube ℓ, ((∫ z in acube ℓ, A y z) + ∫ z in acube ℓ, B y z) from
    integral_congr_ae (Filter.Eventually.of_forall fun y => by
      simp only []
      rw [MeasureTheory.integral_add (hzA y) (hzB y)])]
  rw [MeasureTheory.integral_add hyA hyB]

/-- **The core (c2) identity.**  The `(y,z)`-slot integral of the state against the product of the
two `Q_B`-projected momentum modes `g = qMode ℓ (-P)`, `g' = qMode ℓ P` equals the explicit
`χχe^{i⟨P,y-z⟩}` integral against the pair fibre `aQ_{i.succAbove j'}(aQ_i Φ)`.

This is the reduction of FS `lm:appbogolubov`'s pairing form to the corpus's position-space pair
fibre; it uses only the `Q_B` mean-vanishing structure (`∫g = ∫g' = 0`) and the two-slot
mean-vanishing of the pair fibre. -/
theorem core_identity {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ)
    (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) (P : ℝ³) :
    pairSlot ℓ Φ (qMode ℓ (-P)) (qMode ℓ P) i j' r2
      = ∫ y in acube ℓ, ∫ z in acube ℓ,
          (chiScale ℓ y : ℂ) * (chiScale ℓ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ P (y - z) : ℝ) : ℂ))
            * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ) := by
  have hHc : Continuous (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) :=
    aQ_continuous hℓ (i.succAbove j') (aQ_continuous hℓ i hΦc)
  have hAc : Continuous (aP ℓ i Φ) := aP_continuous hℓ i hΦc
  have hBc : Continuous (aP ℓ (i.succAbove j') (aQ ℓ i Φ)) :=
    aP_continuous hℓ (i.succAbove j') (aQ_continuous hℓ i hΦc)
  have hdec : ∀ x : X (p + 2), Φ x
      = (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) x + (aP ℓ i Φ) x
        + (aP ℓ (i.succAbove j') (aQ ℓ i Φ)) x := by
    intro x
    simp only [aQ]
    ring
  -- the two killed pieces (inner-integral kills)
  have hkillA : (∫ y in acube ℓ, ∫ z in acube ℓ, (qMode ℓ (-P) y) * (qMode ℓ P z)
      * (((aP ℓ i Φ) (ins2 i j' y z r2) : ℝ) : ℂ)) = 0 := by
    have hpt : ∀ y z : ℝ³, (qMode ℓ (-P) y) * (qMode ℓ P z)
        * (((aP ℓ i Φ) (ins2 i j' y z r2) : ℝ) : ℂ)
        = (qMode ℓ (-P) y) * ((qMode ℓ P z)
            * (((aP ℓ i Φ) (ins2 i j' 0 z r2) : ℝ) : ℂ)) := by
      intro y z
      rw [aP_const_slot_i hℓ hΦc i j' r2 y z]
      ring
    simp only [hpt]
    rw [show (∫ y in acube ℓ, ∫ z in acube ℓ, (qMode ℓ (-P) y)
          * ((qMode ℓ P z) * (((aP ℓ i Φ) (ins2 i j' 0 z r2) : ℝ) : ℂ)))
        = ∫ y in acube ℓ, (qMode ℓ (-P) y) * (∫ z in acube ℓ, (qMode ℓ P z)
            * (((aP ℓ i Φ) (ins2 i j' 0 z r2) : ℝ) : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp only []
        rw [MeasureTheory.integral_const_mul])]
    rw [MeasureTheory.integral_mul_const, integral_qMode_eq_zero hℓ (-P), zero_mul]
  have hkillB : (∫ y in acube ℓ, ∫ z in acube ℓ, (qMode ℓ (-P) y) * (qMode ℓ P z)
      * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)) = 0 := by
    have hpt : ∀ y z : ℝ³, (qMode ℓ (-P) y) * (qMode ℓ P z)
        * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)
        = ((qMode ℓ (-P) y)
            * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y 0 r2) : ℝ) : ℂ))
          * (qMode ℓ P z) := by
      intro y z
      rw [aP_const_slot_j hℓ (aQ_continuous hℓ i hΦc) i j' r2 y z]
      ring
    simp only [hpt]
    rw [show (∫ y in acube ℓ, ∫ z in acube ℓ, ((qMode ℓ (-P) y)
          * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y 0 r2) : ℝ) : ℂ))
          * (qMode ℓ P z))
        = ∫ y in acube ℓ, ((qMode ℓ (-P) y)
            * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y 0 r2) : ℝ) : ℂ))
            * (∫ z in acube ℓ, qMode ℓ P z) from
      integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp only []
        rw [MeasureTheory.integral_const_mul])]
    rw [integral_qMode_eq_zero hℓ P,
      show (fun y : ℝ³ => (qMode ℓ (-P) y)
          * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y 0 r2) : ℝ) : ℂ) * (0 : ℂ))
        = fun _ : ℝ³ => (0 : ℂ) from funext fun y => by ring,
      MeasureTheory.integral_zero]
  -- Step A
  have hcontT1 : Continuous (Function.uncurry (fun y z : ℝ³ => (qMode ℓ (-P) y) * (qMode ℓ P z)
      * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ))) := by
    change Continuous (fun q : ℝ³ × ℝ³ => (qMode ℓ (-P) q.1) * (qMode ℓ P q.2)
      * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' q.1 q.2 r2) : ℝ) : ℂ))
    exact (((continuous_qMode (-P)).comp continuous_fst).mul
      ((continuous_qMode P).comp continuous_snd)).mul
      (Complex.continuous_ofReal.comp (hHc.comp (continuous_ins2_uncurry i j' r2)))
  have hcontT23 : Continuous (Function.uncurry (fun y z : ℝ³ =>
      (qMode ℓ (-P) y) * (qMode ℓ P z) * (((aP ℓ i Φ) (ins2 i j' y z r2) : ℝ) : ℂ)
      + (qMode ℓ (-P) y) * (qMode ℓ P z)
        * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ))) := by
    change Continuous (fun q : ℝ³ × ℝ³ =>
      (qMode ℓ (-P) q.1) * (qMode ℓ P q.2) * (((aP ℓ i Φ) (ins2 i j' q.1 q.2 r2) : ℝ) : ℂ)
      + (qMode ℓ (-P) q.1) * (qMode ℓ P q.2)
        * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' q.1 q.2 r2) : ℝ) : ℂ))
    exact ((((continuous_qMode (-P)).comp continuous_fst).mul
        ((continuous_qMode P).comp continuous_snd)).mul
        (Complex.continuous_ofReal.comp (hAc.comp (continuous_ins2_uncurry i j' r2)))).add
      ((((continuous_qMode (-P)).comp continuous_fst).mul
        ((continuous_qMode P).comp continuous_snd)).mul
        (Complex.continuous_ofReal.comp (hBc.comp (continuous_ins2_uncurry i j' r2))))
  have hkillA' : (∫ y in acube ℓ, ∫ z in acube ℓ, (qMode ℓ (-P) y) * (qMode ℓ P z)
      * (((aP ℓ i Φ) (ins2 i j' y z r2) : ℝ) : ℂ)) = 0 := hkillA
  have hkillB' : (∫ y in acube ℓ, ∫ z in acube ℓ, (qMode ℓ (-P) y) * (qMode ℓ P z)
      * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)) = 0 := hkillB
  have hstepA : pairSlot ℓ Φ (qMode ℓ (-P)) (qMode ℓ P) i j' r2
      = ∫ y in acube ℓ, ∫ z in acube ℓ, (qMode ℓ (-P) y) * (qMode ℓ P z)
          * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ) := by
    rw [pairSlot]
    have hpt : ∀ y z : ℝ³, (qMode ℓ (-P) y) * (qMode ℓ P z) * ((Φ (ins2 i j' y z r2) : ℝ) : ℂ)
        = (qMode ℓ (-P) y) * (qMode ℓ P z)
            * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)
          + ((qMode ℓ (-P) y) * (qMode ℓ P z) * (((aP ℓ i Φ) (ins2 i j' y z r2) : ℝ) : ℂ)
            + (qMode ℓ (-P) y) * (qMode ℓ P z)
              * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)) := by
      intro y z
      rw [hdec (ins2 i j' y z r2)]
      push_cast
      ring
    simp only [hpt]
    rw [double_integral_add hℓ (fun y z : ℝ³ => (qMode ℓ (-P) y) * (qMode ℓ P z)
        * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ))
      (fun y z : ℝ³ => (qMode ℓ (-P) y) * (qMode ℓ P z) * (((aP ℓ i Φ) (ins2 i j' y z r2) : ℝ) : ℂ)
        + (qMode ℓ (-P) y) * (qMode ℓ P z)
          * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ))
      hcontT1 hcontT23]
    rw [double_integral_add hℓ
      (fun y z : ℝ³ => (qMode ℓ (-P) y) * (qMode ℓ P z) * (((aP ℓ i Φ) (ins2 i j' y z r2) : ℝ) : ℂ))
      (fun y z : ℝ³ => (qMode ℓ (-P) y) * (qMode ℓ P z)
        * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ))
      (by
        change Continuous (fun q : ℝ³ × ℝ³ => (qMode ℓ (-P) q.1) * (qMode ℓ P q.2)
          * (((aP ℓ i Φ) (ins2 i j' q.1 q.2 r2) : ℝ) : ℂ))
        exact (((continuous_qMode (-P)).comp continuous_fst).mul
          ((continuous_qMode P).comp continuous_snd)).mul
          (Complex.continuous_ofReal.comp (hAc.comp (continuous_ins2_uncurry i j' r2))))
      (by
        change Continuous (fun q : ℝ³ × ℝ³ => (qMode ℓ (-P) q.1) * (qMode ℓ P q.2)
          * (((aP ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' q.1 q.2 r2) : ℝ) : ℂ))
        exact (((continuous_qMode (-P)).comp continuous_fst).mul
          ((continuous_qMode P).comp continuous_snd)).mul
          (Complex.continuous_ofReal.comp (hBc.comp (continuous_ins2_uncurry i j' r2))))]
    rw [hkillA', hkillB', add_zero, add_zero]
  rw [hstepA]
  -- Step B
  set HS : ℝ³ → ℝ³ → ℂ := fun y z =>
    (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ) with hHSdef
  set ChiE : ℝ³ → ℝ³ → ℂ := fun y z => (chiScale ℓ y : ℂ) * (chiScale ℓ z : ℂ)
    * Complex.exp (Complex.I * ((inner ℝ P (y - z) : ℝ) : ℂ)) with hChiEdef
  set K1 : ℝ³ → ℂ := fun z => (-(ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ (-P) * (chiScale ℓ z : ℂ)
    * Complex.exp (Complex.I * ((inner ℝ (-P) z : ℝ) : ℂ)) with hK1def
  set K2 : ℝ³ → ℂ := fun y => (-(ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ P * (chiScale ℓ y : ℂ)
    * Complex.exp (-(Complex.I * ((inner ℝ (-P) y : ℝ) : ℂ))) with hK2def
  set c0 : ℂ := (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * modeChat ℓ (-P) * modeChat ℓ P with hc0def
  have hHScont : Continuous (Function.uncurry HS) := by
    rw [hHSdef]
    change Continuous (fun q : ℝ³ × ℝ³ =>
      (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' q.1 q.2 r2) : ℝ) : ℂ))
    exact Complex.continuous_ofReal.comp (hHc.comp (continuous_ins2_uncurry i j' r2))
  have hH1 : ∀ z : ℝ³, (∫ y in acube ℓ, HS y z) = 0 := by
    intro z
    rw [hHSdef]
    exact ofReal_slot_H_mean_zero_i hℓ hΦc i j' r2 z
  have hH2 : ∀ y : ℝ³, (∫ z in acube ℓ, HS y z) = 0 := by
    intro y
    rw [hHSdef]
    exact ofReal_slot_H_mean_zero_j hℓ hΦc i j' r2 y
  have hChiCont : Continuous (Function.uncurry ChiE) := by
    rw [hChiEdef]
    change Continuous (fun q : ℝ³ × ℝ³ => (chiScale ℓ q.1 : ℂ) * (chiScale ℓ q.2 : ℂ)
      * Complex.exp (Complex.I * ((inner ℝ P (q.1 - q.2) : ℝ) : ℂ)))
    have hphase : Continuous (fun q : ℝ³ × ℝ³ =>
        Complex.exp (Complex.I * ((inner ℝ P (q.1 - q.2) : ℝ) : ℂ))) :=
      Complex.continuous_exp.comp (by
        have h1 : Continuous (fun q : ℝ³ × ℝ³ => ((inner ℝ P (q.1 - q.2) : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp (continuous_inner.comp
            (continuous_const.prodMk (continuous_fst.sub continuous_snd)))
        exact (continuous_const : Continuous (fun _ : ℝ³ × ℝ³ => (Complex.I : ℂ))).mul h1)
    have hchi : Continuous (fun q : ℝ³ × ℝ³ =>
        (chiScale ℓ q.1 : ℂ) * (chiScale ℓ q.2 : ℂ)) :=
      (Complex.continuous_ofReal.comp ((chiScale_continuous ℓ).comp continuous_fst)).mul
        (Complex.continuous_ofReal.comp ((chiScale_continuous ℓ).comp continuous_snd))
    exact hchi.mul hphase
  have hK1Cont : Continuous K1 := by
    rw [hK1def]
    have hphase : Continuous (fun z : ℝ³ =>
        Complex.exp (Complex.I * ((inner ℝ (-P) z : ℝ) : ℂ))) :=
      Complex.continuous_exp.comp (by
        have h1 : Continuous (fun z : ℝ³ => ((inner ℝ (-P) z : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp (continuous_inner.comp
            (continuous_const.prodMk continuous_id))
        exact (continuous_const : Continuous (fun _ : ℝ³ => (Complex.I : ℂ))).mul h1)
    have hc : Continuous (fun _ : ℝ³ => (-(ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ (-P)) :=
      (continuous_const : Continuous (fun _ : ℝ³ => (-(ℓ ^ 3)⁻¹ : ℂ))).mul continuous_const
    exact (hc.mul (Complex.continuous_ofReal.comp (chiScale_continuous ℓ))).mul hphase
  have hK2Cont : Continuous K2 := by
    rw [hK2def]
    have hphase : Continuous (fun z : ℝ³ =>
        Complex.exp (-(Complex.I * ((inner ℝ (-P) z : ℝ) : ℂ)))) :=
      Complex.continuous_exp.comp (by
        have h1 : Continuous (fun z : ℝ³ => ((inner ℝ (-P) z : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp (continuous_inner.comp
            (continuous_const.prodMk continuous_id))
        exact ((continuous_const : Continuous (fun _ : ℝ³ => (Complex.I : ℂ))).mul h1).neg)
    have hc : Continuous (fun _ : ℝ³ => (-(ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ P) :=
      (continuous_const : Continuous (fun _ : ℝ³ => (-(ℓ ^ 3)⁻¹ : ℂ))).mul continuous_const
    exact (hc.mul (Complex.continuous_ofReal.comp (chiScale_continuous ℓ))).mul hphase
  have hmul : ∀ y z : ℝ³, (qMode ℓ (-P) y) * (qMode ℓ P z) = ChiE y z + (K1 z + K2 y + c0) := by
    intro y z
    rw [hChiEdef, hK1def, hK2def, hc0def]
    simp only []
    have hm := qMode_mul (ℓ := ℓ) (-P) y z
    simp only [neg_neg] at hm
    rw [hm]
    rw [show (inner ℝ (-P) (z - y)) = inner ℝ P (y - z) from by
      simp only [inner_neg_left, inner_sub_right]
      ring]
    simp only [Complex.ofReal_inv, Complex.ofReal_pow]
    ring
  have hkill1 : (∫ y in acube ℓ, ∫ z in acube ℓ, K1 z * HS y z) = 0 := by
    rw [integral_swap_acube hℓ (F := fun y z : ℝ³ => K1 z * HS y z) (by
      change Continuous (fun q : ℝ³ × ℝ³ => K1 q.2 * HS q.1 q.2)
      exact (hK1Cont.comp continuous_snd).mul hHScont)]
    rw [show (∫ z in acube ℓ, ∫ y in acube ℓ, K1 z * HS y z)
        = ∫ z in acube ℓ, K1 z * (∫ y in acube ℓ, HS y z) from
      integral_congr_ae (Filter.Eventually.of_forall fun z => by
        simp only []
        rw [MeasureTheory.integral_const_mul])]
    simp_rw [hH1]
    rw [show (∫ z in acube ℓ, K1 z * (0 : ℂ))
        = (∫ z in acube ℓ, K1 z) * 0 from MeasureTheory.integral_mul_const _ _]
    rw [mul_zero]
  have hkill2 : (∫ y in acube ℓ, ∫ z in acube ℓ, (K2 y + c0) * HS y z) = 0 := by
    rw [show (∫ y in acube ℓ, ∫ z in acube ℓ, (K2 y + c0) * HS y z)
        = ∫ y in acube ℓ, (K2 y + c0) * (∫ z in acube ℓ, HS y z) from
      integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp only []
        rw [MeasureTheory.integral_const_mul])]
    simp_rw [hH2]
    rw [show (∫ y in acube ℓ, (K2 y + c0) * (0 : ℂ))
        = (∫ y in acube ℓ, (K2 y + c0)) * 0 from MeasureTheory.integral_mul_const _ _]
    rw [mul_zero]
  have hmain : (∫ y in acube ℓ, ∫ z in acube ℓ, (qMode ℓ (-P) y) * (qMode ℓ P z) * HS y z)
      = (∫ y in acube ℓ, ∫ z in acube ℓ, ChiE y z * HS y z)
        + ((∫ y in acube ℓ, ∫ z in acube ℓ, K1 z * HS y z)
          + (∫ y in acube ℓ, ∫ z in acube ℓ, (K2 y + c0) * HS y z)) := by
    rw [show (fun y : ℝ³ => ∫ z in acube ℓ, (qMode ℓ (-P) y) * (qMode ℓ P z) * HS y z)
        = fun y : ℝ³ => ∫ z in acube ℓ, (ChiE y z * HS y z
            + ((K1 z + K2 y + c0) * HS y z)) from
      funext fun y => integral_congr_ae (Filter.Eventually.of_forall fun z => by
        simp only []
        rw [hmul y z]
        ring)]
    rw [double_integral_add hℓ (fun y z => ChiE y z * HS y z)
      (fun y z => (K1 z + K2 y + c0) * HS y z)
      (hChiCont.mul hHScont)
      (by
        change Continuous (fun q : ℝ³ × ℝ³ => (K1 q.2 + K2 q.1 + c0) * HS q.1 q.2)
        exact (((hK1Cont.comp continuous_snd).add (hK2Cont.comp continuous_fst)).add
          (continuous_const : Continuous (fun _ : ℝ³ × ℝ³ => c0))).mul hHScont)]
    congr 1
    rw [show (fun y : ℝ³ => ∫ z in acube ℓ, (K1 z + K2 y + c0) * HS y z)
        = fun y : ℝ³ => ∫ z in acube ℓ, (K1 z * HS y z + (K2 y + c0) * HS y z) from
      funext fun y => integral_congr_ae (Filter.Eventually.of_forall fun z => by
        simp only []
        ring)]
    rw [double_integral_add hℓ (fun y z => K1 z * HS y z) (fun y z => (K2 y + c0) * HS y z)
      (by
        change Continuous (fun q : ℝ³ × ℝ³ => K1 q.2 * HS q.1 q.2)
        exact (hK1Cont.comp continuous_snd).mul hHScont)
      (by
        change Continuous (fun q : ℝ³ × ℝ³ => (K2 q.1 + c0) * HS q.1 q.2)
        exact ((hK2Cont.comp continuous_fst).add
          (continuous_const : Continuous (fun _ : ℝ³ × ℝ³ => c0))).mul hHScont)]
  rw [hmain, hkill1, hkill2, add_zero, add_zero]

end BoseGases
end Submission
