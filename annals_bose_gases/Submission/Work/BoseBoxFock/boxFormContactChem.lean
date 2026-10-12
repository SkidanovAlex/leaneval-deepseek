import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotContactChemEval
import Submission.Work.BoseBoxFock.uSlot_uSlot_pair_cS2C
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxFormContactChem` — the contact/chemical row of the box form

The contact/chemical group of the row table `PotContactChem` evaluates, at a box state `Θ` and a
word `K • (B (B Θ) − B Θ) − μ' • (B Θ)` with `B = boxSlotSum e (rankOne (evec0 m))` the condensate
slot sum, to the linear combination `K * cS2C ℓ Θ − μ' * cS1C ℓ Θ` of the pair-condensate and
condensate counts.

The proof is the bookkeeping reduction to the two evaluations which are already proved in this
directory:

* `cIPn_boxSlotSum_rankOne_evec0_re` : `(cIPn d Θ (B Θ)).re = cS1C ℓ Θ`;
* `uSlot_uSlot_pair_cS2C` : `(cIPn d Θ (Σ_i Σ_j uSlot (e 0) i (uSlot (e 0) j Θ))).re
  = cS1C ℓ Θ + cS2C ℓ Θ`,

together with the a.e. (on the box) identification `B (B Θ) =ᵐ Σ_i Σ_j uSlot (e 0) i
(uSlot (e 0) j Θ)` and the linearity of `cIPn` in its second argument.

**Performance note (why the word is handled through an abstract `B`).**  The two spellings of the
condensate slot sum — `boxSlotSum e (rankOne (evec0 m))` and `boxSlotSum e (proj0 m)` — are only
*definitionally* equal, and asking a unifier to compare the underlying `LinearMap`s unfolds
`rankOne` into `Finset.sum`/`Multiset`/`Quot` machinery *and then compares the `map_add'` and
`map_smul'` proof fields*.  That is astronomically slow (minutes of heartbeats for one `exact`).
The proof below therefore (i) does the whole argument with an abstract `B` and the single
hypothesis `hB : B = boxSlotSum e (proj0 m)` (so no unification ever sees `rankOne` and `proj0`
together), and (ii) converts the `rankOne`-spelling of the theorem's word to the `proj0`-spelling
in one explicit `rw` of the *function* equation `boxSlotSum_rankOne_evec0_eq_proj0`, before any
application.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators
open Work.BoseDict

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-- `boxSlotSum e (rankOne (evec0 m))` and `boxSlotSum e (proj0 m)` are the same function of the
state, since `|evec0⟩⟨evec0| = proj0 m` as one-particle operators. -/
lemma boxSlotSum_rankOne_evec0_eq_proj0 {m d : ℕ} [NeZero m] (e : Fin m → Sp → ℂ) :
    Work.BoseDict.boxSlotSum (d := d) e (rankOne (evec0 m))
      = Work.BoseDict.boxSlotSum (d := d) e (proj0 m) := by
  funext Ψ
  rw [← proj0_eq_rankOne]

/-- **The box-relative congruence of the slot mean, for an arbitrary number of slots.**
This is the general-`N` form of the proved `aPC_congr_ae_box` (which is stated for `Fin (k+1)`);
the `N = 0` case is vacuous. -/
lemma aPC_congr_ae_abox_B {N : ℕ} {ℓ : ℝ} (i : Fin N) {f g : (Fin N → Sp) → ℂ}
    (h : f =ᵐ[(volume : Measure (Fin N → Sp)).restrict (Submission.BoseGases.abox N ℓ)] g) :
    aPC ℓ i f =ᵐ[(volume : Measure (Fin N → Sp)).restrict (Submission.BoseGases.abox N ℓ)]
      aPC ℓ i g := by
  cases N with
  | zero => exact i.elim0
  | succ k => exact aPC_congr_ae_box i h

/-- **On the box, the sum of the `uSlot`s of a fixed one-particle vector is the sum of the
slot means.** -/
lemma uSlot_sum_ae_eq_aPC_sum {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {u : Sp → ℂ} {c : ℂ}
    (huc : ∀ᵐ z ∂(volume : Measure Sp), u z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹) (Ψ : Xn d → ℂ) :
    (fun x => ∑ j : Fin d, uSlot u j Ψ x)
      =ᵐ[(volume : Measure (Xn d)).restrict (Submission.BoseGases.abox d ℓ)]
      (fun x => ∑ j : Fin d, aPC ℓ j Ψ x) := by
  filter_upwards [Filter.eventually_all.mpr
    (fun j : Fin d => uSlot_ae_eq_aPC_aux hℓ j huc hcc (Θ := Ψ))] with x hx
  exact Finset.sum_congr rfl (fun j _ => hx j)

/-- **On the box, the double `uSlot` sum is the double slot-mean sum.** -/
lemma uSlot_double_ae_eq_aPC_double {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {u : Sp → ℂ} {c : ℂ}
    (huc : ∀ᵐ z ∂(volume : Measure Sp), u z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹) (Ψ : Xn d → ℂ) :
    (fun x => ∑ i : Fin d, ∑ j : Fin d, uSlot u i (uSlot u j Ψ) x)
      =ᵐ[(volume : Measure (Xn d)).restrict (Submission.BoseGases.abox d ℓ)]
      (fun x => ∑ i : Fin d, ∑ j : Fin d, aPC ℓ i (aPC ℓ j Ψ) x) := by
  have hpair : ∀ i j : Fin d,
      (fun x => uSlot u i (uSlot u j Ψ) x)
        =ᵐ[(volume : Measure (Xn d)).restrict (Submission.BoseGases.abox d ℓ)]
        (fun x => aPC ℓ i (aPC ℓ j Ψ) x) := by
    intro i j
    exact (uSlot_ae_eq_aPC_aux hℓ i huc hcc (Θ := uSlot u j Ψ)).trans
      (aPC_congr_ae_abox_B i (uSlot_ae_eq_aPC_aux hℓ j huc hcc (Θ := Ψ)))
  have h2 := Filter.eventually_all.mpr (fun i : Fin d =>
    Filter.eventually_all.mpr (fun j : Fin d => hpair i j))
  filter_upwards [h2] with x hx
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hx i j))

/-- **The contact/chemical row of the box form, with the slot sum kept abstract.** -/
theorem boxFormContactChem_abs_re {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Sp → ℂ}
    (horth : ∀ l l', (∫ z : Sp, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) (⊤ : ENNReal))
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {c : ℂ} (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹)
    (hun : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
      e 0 z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    {C : ℝ} (hC : 0 ≤ C) {Θ : Xn d → ℂ}
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox d ℓ)
    (hΘm : MeasureTheory.AEStronglyMeasurable Θ MeasureTheory.volume)
    (hΘb : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Xn d)), ‖Θ x‖ ≤ C)
    (B : (Xn d → ℂ) → (Xn d → ℂ)) (hB : B = Work.BoseDict.boxSlotSum e (proj0 m))
    (K μ' : ℝ) :
    (cIPn d Θ (K • (B (B Θ) - B Θ) - μ' • (B Θ))).re
      = K * cS2C ℓ Θ - μ' * cS1C ℓ Θ := by
  classical
  set T : Xn d → ℂ := fun x => ∑ i : Fin d, aPC ℓ i Θ x with hTdef
  set S : Xn d → ℂ := fun x => ∑ i : Fin d, ∑ j : Fin d, aPC ℓ i (aPC ℓ j Θ) x with hSdef
  set V2 : Xn d → ℂ := fun x => ∑ i : Fin d, ∑ j : Fin d, uSlot (e 0) i (uSlot (e 0) j Θ) x
    with hV2def
  have hΘM : MemLp Θ (⊤ : ENNReal) (volume : Measure (Xn d)) :=
    memLp_top_of_bound hΘm C hΘb
  -- ## 1. The box reductions of `B`
  have hBfun : ∀ Ψ : Xn d → ℂ, B Ψ = (fun x => ∑ j : Fin d, uSlot (e 0) j Ψ x) := by
    intro Ψ
    rw [hB]
    exact boxSlotSum_proj0 e Ψ
  have hBΘfun : B Θ = (fun x => ∑ j : Fin d, uSlot (e 0) j Θ x) := hBfun Θ
  have hBBfun : B (B Θ) = (fun x => ∑ j : Fin d, uSlot (e 0) j (B Θ) x) := hBfun (B Θ)
  -- ## 2. `cIPn` as a box integral
  have hbox : ∀ Y : Xn d → ℂ,
      cIPn d Θ Y = ∫ x in Submission.BoseGases.abox d ℓ, (starRingEnd ℂ) (Θ x) * Y x := by
    intro Y
    rw [cIPn]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Submission.BoseGases.abox d ℓ)
      (f := fun x => (starRingEnd ℂ) (Θ x) * Y x) (fun x hx => by
        have h0 : Θ x = 0 := by
          by_contra h
          exact hx (hΘsupp (Function.mem_support.mpr h))
        rw [h0, map_zero, zero_mul])).symm
  -- ## 3. A.e. (on the box) identifications
  have hBΘae : B Θ =ᵐ[volume.restrict (Submission.BoseGases.abox d ℓ)] T := by
    rw [hBΘfun, hTdef]
    exact uSlot_sum_ae_eq_aPC_sum hℓ hun hcc Θ
  have hmem : ∀ i : Fin d, MemLp (aPC ℓ i Θ) (⊤ : ENNReal) (volume : Measure (Xn d)) := by
    obtain ⟨C₀, hC₀0, hC₀b⟩ := exists_ae_bound_of_memLp_top_gen hΘM
    intro i
    exact memLp_top_of_bound (aPC_aesm_full ℓ i hΘm) C₀
      (aPC_ae_bound_full ℓ hℓ i hC₀0 hC₀b)
  have hBBae : B (B Θ) =ᵐ[volume.restrict (Submission.BoseGases.abox d ℓ)] S := by
    have h1 : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox d ℓ)),
        (∑ j : Fin d, uSlot (e 0) j (B Θ) x) = (∑ j : Fin d, aPC ℓ j (B Θ) x) := by
      filter_upwards [Filter.eventually_all.mpr
        (fun j => uSlot_ae_eq_aPC_aux hℓ j hun hcc (Θ := B Θ))] with x hx
      exact Finset.sum_congr rfl (fun j _ => hx j)
    have h2 : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox d ℓ)),
        (∑ j : Fin d, aPC ℓ j (B Θ) x) = (∑ j : Fin d, aPC ℓ j T x) := by
      filter_upwards [Filter.eventually_all.mpr
        (fun j => aPC_congr_ae_abox_B (ℓ := ℓ) j hBΘae)] with x hx
      exact Finset.sum_congr rfl (fun j _ => hx j)
    have h3 : ∀ᵐ x ∂(volume : Measure (Xn d)),
        (∑ j : Fin d, aPC ℓ j T x)
          = (∑ j : Fin d, ∑ i : Fin d, aPC ℓ j (aPC ℓ i Θ) x) := by
      filter_upwards [Filter.eventually_all.mpr
        (fun j => aPC_finsetSum_ae ℓ hℓ j Finset.univ (fun k _ => hmem k))] with x hx
      exact Finset.sum_congr rfl (fun j _ => hx j)
    have h3' : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox d ℓ)),
        (∑ j : Fin d, aPC ℓ j T x)
          = (∑ j : Fin d, ∑ i : Fin d, aPC ℓ j (aPC ℓ i Θ) x) :=
      MeasureTheory.ae_mono (Measure.restrict_le_self (s := Submission.BoseGases.abox d ℓ)) h3
    have h4 : ∀ x : Xn d, (∑ j : Fin d, ∑ i : Fin d, aPC ℓ j (aPC ℓ i Θ) x)
        = (∑ i : Fin d, ∑ j : Fin d, aPC ℓ i (aPC ℓ j Θ) x) := fun x => by
      rw [Finset.sum_comm]
    rw [hBBfun, hSdef]
    filter_upwards [h1, h2, h3', Filter.Eventually.of_forall h4] with x h1x h2x h3x h4x
    rw [h1x, h2x, h3x, h4x]
  have hV2ae : V2 =ᵐ[volume.restrict (Submission.BoseGases.abox d ℓ)] S := by
    rw [hV2def, hSdef]
    exact uSlot_double_ae_eq_aPC_double hℓ hun hcc Θ
  have hBBV2 : B (B Θ) =ᵐ[volume.restrict (Submission.BoseGases.abox d ℓ)] V2 :=
    hBBae.trans hV2ae.symm
  -- ## 4. The two evaluations
  have hX1 : (cIPn d Θ (B Θ)).re = cS1C ℓ Θ := by
    rw [hB, proj0_eq_rankOne]
    exact cIPn_boxSlotSum_rankOne_evec0_re hℓ horth hbdd hsupp hcc hun hC hΘsupp hΘm hΘb
  have hX2 : (cIPn d Θ (B (B Θ))).re = cS1C ℓ Θ + cS2C ℓ Θ := by
    have hEq : cIPn d Θ (B (B Θ)) = cIPn d Θ V2 := by
      rw [hbox (B (B Θ)), hbox V2]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hBBV2] with x hx
      rw [hx]
    rw [hEq]
    exact uSlot_uSlot_pair_cS2C hℓ hcc hun hΘM hΘsupp
  -- ## 5. Integrability of the two pieces on the box
  have hIntBB : IntegrableOn (fun x => (starRingEnd ℂ) (Θ x) * (B (B Θ)) x)
      (Submission.BoseGases.abox d ℓ) volume := by
    have hS : IntegrableOn (fun x => (starRingEnd ℂ) (Θ x) * S x)
        (Submission.BoseGases.abox d ℓ) volume := by
      have hsum : (fun x => (starRingEnd ℂ) (Θ x) * S x)
          = fun x => ∑ i : Fin d, ∑ j : Fin d,
              (starRingEnd ℂ) (Θ x) * aPC ℓ i (aPC ℓ j Θ) x := by
        funext x
        rw [hSdef, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])
      rw [hsum]
      exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j _ => (integral_conj_mul_aPC_aPC hℓ hΘM hΘsupp i j).1))
    have hae : (fun x => (starRingEnd ℂ) (Θ x) * (B (B Θ)) x)
        =ᵐ[volume.restrict (Submission.BoseGases.abox d ℓ)]
        (fun x => (starRingEnd ℂ) (Θ x) * S x) := by
      filter_upwards [hBBae] with x hx
      rw [hx]
    exact hS.congr_fun_ae hae.symm
  have hIntB : IntegrableOn (fun x => (starRingEnd ℂ) (Θ x) * (B Θ) x)
      (Submission.BoseGases.abox d ℓ) volume := by
    have hT : IntegrableOn (fun x => (starRingEnd ℂ) (Θ x) * T x)
        (Submission.BoseGases.abox d ℓ) volume := by
      have hsum : (fun x => (starRingEnd ℂ) (Θ x) * T x)
          = fun x => ∑ i : Fin d, (starRingEnd ℂ) (Θ x) * aPC ℓ i Θ x := by
        funext x
        rw [hTdef, Finset.mul_sum]
      rw [hsum]
      refine integrable_finsetSum _ (fun i _ => ?_)
      have h2 : IntegrableOn (fun x => (starRingEnd ℂ) (Θ x) * aPC ℓ i Θ x)
          (Submission.BoseGases.abox d ℓ) volume :=
        (integral_conj_mul_aPC_aPC hℓ hΘM hΘsupp i i).1.congr_fun_ae
          (Filter.Eventually.of_forall (fun x => by rw [aPC_idem hℓ i]))
      exact h2
    have hae : (fun x => (starRingEnd ℂ) (Θ x) * (B Θ) x)
        =ᵐ[volume.restrict (Submission.BoseGases.abox d ℓ)]
        (fun x => (starRingEnd ℂ) (Θ x) * T x) := by
      filter_upwards [hBΘae] with x hx
      rw [hx]
    exact hT.congr_fun_ae hae.symm
  -- ## 6. Linearity of `cIPn` on the box
  have hmain : cIPn d Θ (K • (B (B Θ) - B Θ) - μ' • (B Θ))
      = K • cIPn d Θ (B (B Θ))
        - K • cIPn d Θ (B Θ) - μ' • cIPn d Θ (B Θ) := by
    rw [hbox (K • (B (B Θ) - B Θ) - μ' • (B Θ)), hbox (B (B Θ)), hbox (B Θ)]
    have hI1 : Integrable (fun x => K • ((starRingEnd ℂ) (Θ x) * (B (B Θ)) x))
        (volume.restrict (Submission.BoseGases.abox d ℓ)) := hIntBB.smul K
    have hI2 : Integrable (fun x => K • ((starRingEnd ℂ) (Θ x) * (B Θ) x))
        (volume.restrict (Submission.BoseGases.abox d ℓ)) := hIntB.smul K
    have hI3 : Integrable (fun x => μ' • ((starRingEnd ℂ) (Θ x) * (B Θ) x))
        (volume.restrict (Submission.BoseGases.abox d ℓ)) := hIntB.smul μ'
    have hI12 : Integrable (fun x => K • ((starRingEnd ℂ) (Θ x) * (B (B Θ)) x)
        - K • ((starRingEnd ℂ) (Θ x) * (B Θ) x))
        (volume.restrict (Submission.BoseGases.abox d ℓ)) := hI1.sub hI2
    have hstep : (∫ x in Submission.BoseGases.abox d ℓ,
          (starRingEnd ℂ) (Θ x) * (K • (B (B Θ) - B Θ) - μ' • (B Θ)) x)
        = (∫ x in Submission.BoseGases.abox d ℓ,
            (K • ((starRingEnd ℂ) (Θ x) * (B (B Θ)) x)
              - K • ((starRingEnd ℂ) (Θ x) * (B Θ) x)
              - μ' • ((starRingEnd ℂ) (Θ x) * (B Θ) x))) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul]
        ring))
    rw [hstep]
    rw [MeasureTheory.integral_sub
        (f := fun x => K • ((starRingEnd ℂ) (Θ x) * (B (B Θ)) x)
          - K • ((starRingEnd ℂ) (Θ x) * (B Θ) x))
        (g := fun x => μ' • ((starRingEnd ℂ) (Θ x) * (B Θ) x)) hI12 hI3]
    rw [MeasureTheory.integral_sub
        (f := fun x => K • ((starRingEnd ℂ) (Θ x) * (B (B Θ)) x))
        (g := fun x => K • ((starRingEnd ℂ) (Θ x) * (B Θ) x)) hI1 hI2]
    rw [MeasureTheory.integral_smul, MeasureTheory.integral_smul,
      MeasureTheory.integral_smul]
  -- ## 7. Assembly
  rw [hmain]
  rw [Complex.sub_re, Complex.sub_re, Complex.real_smul, Complex.real_smul, Complex.real_smul,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  rw [hX2, hX1]
  ring

/-- **The contact/chemical row of the box form** (in the `rankOne` spelling of `potContactChem`). -/
theorem boxFormContactChem_re {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Sp → ℂ}
    (horth : ∀ l l', (∫ z : Sp, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) (⊤ : ENNReal))
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {c : ℂ} (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹)
    (hun : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
      e 0 z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    {C : ℝ} (hC : 0 ≤ C) {Θ : Xn d → ℂ}
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox d ℓ)
    (hΘm : MeasureTheory.AEStronglyMeasurable Θ MeasureTheory.volume)
    (hΘb : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Xn d)), ‖Θ x‖ ≤ C)
    (K μ' : ℝ) :
    (cIPn d Θ (K • (Work.BoseDict.boxSlotSum e (rankOne (evec0 m))
          (Work.BoseDict.boxSlotSum e (rankOne (evec0 m)) Θ)
        - Work.BoseDict.boxSlotSum e (rankOne (evec0 m)) Θ)
      - μ' • (Work.BoseDict.boxSlotSum e (rankOne (evec0 m)) Θ))).re
      = K * cS2C ℓ Θ - μ' * cS1C ℓ Θ := by
  have hword :
      (K • (Work.BoseDict.boxSlotSum e (rankOne (evec0 m))
            (Work.BoseDict.boxSlotSum e (rankOne (evec0 m)) Θ)
          - Work.BoseDict.boxSlotSum e (rankOne (evec0 m)) Θ)
        - μ' • (Work.BoseDict.boxSlotSum e (rankOne (evec0 m)) Θ))
      = (K • (Work.BoseDict.boxSlotSum e (proj0 m)
            (Work.BoseDict.boxSlotSum e (proj0 m) Θ)
          - Work.BoseDict.boxSlotSum e (proj0 m) Θ)
        - μ' • (Work.BoseDict.boxSlotSum e (proj0 m) Θ)) := by
    rw [boxSlotSum_rankOne_evec0_eq_proj0 (d := d) e]
  rw [hword]
  exact boxFormContactChem_abs_re hℓ horth hbdd hsupp hcc hun hC hΘsupp hΘm hΘb
    (Work.BoseDict.boxSlotSum e (proj0 m)) rfl K μ'

end Work.BoseBoxFock
