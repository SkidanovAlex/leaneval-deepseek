import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.SliceBadAux
import Submission.Work.BoseBoxFock.aPC_congr_ae_box
import Submission.Work.BoseBoxFock.integral_mode_acube
import Submission.Work.BoseBoxFock.uSlot_ae_eq_aPC
import Submission.Work.BoseBoxFock.uSlot_regular
import Submission.Work.BoseDict.integrable_star_modeProd_Phi
import Submission.Work.BoseDict.modeProd_cIPn
import Submission.Work.BoseDictC.sum_star_modeProd_succAbove
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators ENNReal

/-- The one-particle space. -/
local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. The slot mean commutes with conjugation -/

/-- `aPC` is `ℝ`-linear, hence commutes with complex conjugation. -/
theorem aPC_conj {N : ℕ} (ℓ : ℝ) (i : Fin N) (Ψ : Submission.BoseGases.X N → ℂ) :
    aPC ℓ i (fun x => (starRingEnd ℂ) (Ψ x))
      = fun x => (starRingEnd ℂ) (aPC ℓ i Ψ x) := by
  funext x
  rw [aPC, aPC, integral_conj, map_mul, Complex.conj_ofReal]

/-! ## 1. The slot mean in peeled coordinates -/

/-- In the peeled coordinates `x = kcInsN n i (y, r)`, the slot-`i` mean is the (constant)
cube mean of `Ψ` over the inserted coordinate. -/
theorem aPC_kcInsN {n : ℕ} (ℓ : ℝ) (i : Fin (n + 1)) (Ψ : Submission.BoseGases.X (n + 1) → ℂ)
    (y : Sp) (r : Submission.BoseGases.X n) :
    aPC ℓ i Ψ (Submission.BoseGases.kcInsN n i (y, r))
      = ((1 / ℓ ^ 3 : ℝ) : ℂ)
        * ∫ z in Submission.BoseGases.acube ℓ, Ψ (Submission.BoseGases.kcInsN n i (z, r)) := by
  unfold aPC
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  exact Submission.BoseGases.update_kcInsN (n := n) i y z r

/-! ## 2. The symmetry of the slot mean over the box -/

/-- **The slot mean is symmetric on the box.**  For `ℂ`-valued states whose pairings with the
slot mean are integrable on `abox N ℓ`,

  `∫_{abox} (aPC ℓ i Φ)·Ψ = ∫_{abox} Φ·(aPC ℓ i Ψ)`

Both sides are computed by peeling the slot `i`, where the fibre identity is immediate: in the
peeled coordinates `aPC ℓ i Φ` is the *constant* `ℓ⁻³∫_z Φ(kc (z,r))` on the fibre and
`∫_y aPC ℓ i Ψ (kc (y,r)) dy = ℓ⁻³ (∫_z Ψ(kc (z,r)) dz)·ℓ³`. -/
theorem aPC_sym_box {N : ℕ} {ℓ : ℝ} (i : Fin N) {Φ Ψ : Submission.BoseGases.X N → ℂ}
    (hΦ : IntegrableOn (fun x => aPC ℓ i Φ x * Ψ x) (Submission.BoseGases.abox N ℓ))
    (hΨ : IntegrableOn (fun x => Φ x * aPC ℓ i Ψ x) (Submission.BoseGases.abox N ℓ)) :
    (∫ x in Submission.BoseGases.abox N ℓ, aPC ℓ i Φ x * Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ, Φ x * aPC ℓ i Ψ x := by
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    -- abbreviate the two fibre integrals
    set A : Submission.BoseGases.X n → ℂ := fun r =>
      ∫ z in Submission.BoseGases.acube ℓ, Φ (Submission.BoseGases.kcInsN n i (z, r)) with hA
    set B : Submission.BoseGases.X n → ℂ := fun r =>
      ∫ z in Submission.BoseGases.acube ℓ, Ψ (Submission.BoseGases.kcInsN n i (z, r)) with hB
    have hfib : (fun r => ∫ y in Submission.BoseGases.acube ℓ,
          aPC ℓ i Φ (Submission.BoseGases.kcInsN n i (y, r))
            * Ψ (Submission.BoseGases.kcInsN n i (y, r)))
        = fun r => ∫ y in Submission.BoseGases.acube ℓ,
          Φ (Submission.BoseGases.kcInsN n i (y, r))
            * aPC ℓ i Ψ (Submission.BoseGases.kcInsN n i (y, r)) := by
      funext r
      have h1 : ∀ y : Sp, aPC ℓ i Φ (Submission.BoseGases.kcInsN n i (y, r))
          = ((1 / ℓ ^ 3 : ℝ) : ℂ) * A r := by
        intro y
        rw [aPC_kcInsN]
      have h2 : ∀ y : Sp, aPC ℓ i Ψ (Submission.BoseGases.kcInsN n i (y, r))
          = ((1 / ℓ ^ 3 : ℝ) : ℂ) * B r := by
        intro y
        rw [aPC_kcInsN]
      calc (∫ y in Submission.BoseGases.acube ℓ,
            aPC ℓ i Φ (Submission.BoseGases.kcInsN n i (y, r))
              * Ψ (Submission.BoseGases.kcInsN n i (y, r)))
          = ∫ y in Submission.BoseGases.acube ℓ,
              (((1 / ℓ ^ 3 : ℝ) : ℂ) * A r) * Ψ (Submission.BoseGases.kcInsN n i (y, r)) := by
            apply integral_congr_ae
            filter_upwards with y
            rw [h1 y]
        _ = (((1 / ℓ ^ 3 : ℝ) : ℂ) * A r)
              * ∫ y in Submission.BoseGases.acube ℓ,
                  Ψ (Submission.BoseGases.kcInsN n i (y, r)) :=
            integral_const_mul _ _
        _ = (((1 / ℓ ^ 3 : ℝ) : ℂ) * A r) * B r := by rw [hB]
        _ = A r * (((1 / ℓ ^ 3 : ℝ) : ℂ) * B r) := by ring
        _ = (∫ y in Submission.BoseGases.acube ℓ,
                Φ (Submission.BoseGases.kcInsN n i (y, r)))
              * (((1 / ℓ ^ 3 : ℝ) : ℂ) * B r) := by rw [hA]
        _ = ∫ y in Submission.BoseGases.acube ℓ,
              Φ (Submission.BoseGases.kcInsN n i (y, r))
                * (((1 / ℓ ^ 3 : ℝ) : ℂ) * B r) :=
            (integral_mul_const _ _).symm
        _ = ∫ y in Submission.BoseGases.acube ℓ,
              Φ (Submission.BoseGases.kcInsN n i (y, r))
                * aPC ℓ i Ψ (Submission.BoseGases.kcInsN n i (y, r)) := by
            apply integral_congr_ae
            filter_upwards with y
            rw [h2 y]
    rw [abox_integral_peel_complex (ℓ := ℓ) i _ hΦ, hfib,
      ← abox_integral_peel_complex (ℓ := ℓ) i _ hΨ]

/-! ## 3. The slot mean of an `L¹` state is `L¹` on the box -/

/-- **`aPC` does not increase the `L¹`-mass over the box.**  For a state `G` integrable on the
whole space, the slot mean `aPC ℓ i G` is integrable on `abox d ℓ`; equivalently the cube mean
`ℓ⁻³∫_{acube}` is `L¹`-contractive on the box.

The proof never uses an `L¹`-estimate: in the peeled coordinates `x = kcInsN n i (y', r)` the
fibre integral `∫_{acube} G(x[i↦y]) dy` equals `∫_{acube} G(kcInsN n i (y, r)) dy`, which is the
*average over the forgotten coordinate* of the integrable function `G ∘ kcInsN`; Fubini
(`Integrable.integral_prod_right`) exhibits it as the marginal of an integrable function, and the
measure-preserving peel (`MeasurePreserving.integrable_comp`) transports integrability back to
the box. -/
theorem integrableOn_aPC_of_integrable {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {G : Submission.BoseGases.X d → ℂ} (hG : Integrable G) (i : Fin d) :
    IntegrableOn (fun x => aPC ℓ i G x) (Submission.BoseGases.abox d ℓ) := by
  classical
  cases d with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    set μ₀ : Measure Sp := (volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ) with hμ₀
    set ν : Measure (Submission.BoseGases.X n) :=
      (volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ) with hν
    set κ : Measure (Submission.BoseGases.X (n + 1)) :=
      (volume : Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ) with hκ
    haveI : IsFiniteMeasure μ₀ :=
      ⟨by rw [hμ₀, Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
    have hmp : MeasurePreserving (⇑(Submission.BoseGases.kcInsN n i)) (μ₀.prod ν) κ := by
      have h := MeasurePreserving.symm
        (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Sp) i)
        (Submission.BoseGases.abox_peel_mp n ℓ i)
      simpa [Submission.BoseGases.kcInsN, hμ₀, hν, hκ] using h
    -- a strongly measurable representative of `G`
    set G' : Submission.BoseGases.X (n + 1) → ℂ := hG.aestronglyMeasurable.mk G with hG'def
    have hG'm : StronglyMeasurable G' := hG.aestronglyMeasurable.stronglyMeasurable_mk
    have hG'eq : G =ᵐ[(volume : Measure (Submission.BoseGases.X (n + 1)))] G' :=
      hG.aestronglyMeasurable.ae_eq_mk
    have hG'i : Integrable G' := hG.congr hG'eq
    have hG'aesm : AEStronglyMeasurable G' κ := hG'm.aestronglyMeasurable
    -- the fibre function `x ↦ ∫_y G'(x[i↦y])`
    set Hfun : Submission.BoseGases.X (n + 1) → ℂ :=
      fun x => ∫ y, G' (Function.update x i y) ∂μ₀ with hHfun
    -- ## Step A: `G' ∘ kcInsN` is integrable on the product
    have hf : Integrable (fun z : Sp × Submission.BoseGases.X n =>
        G' (Submission.BoseGases.kcInsN n i z)) (μ₀.prod ν) :=
      (hmp.integrable_comp hG'aesm).mpr (hG'i.mono_measure Measure.restrict_le_self)
    -- ## Step B/C: the marginal in the slot variable, lifted to the product
    have hlift : Integrable (fun p : Sp × Submission.BoseGases.X n =>
        Hfun (Submission.BoseGases.kcInsN n i p)) (μ₀.prod ν) := by
      refine ((integrable_const (1 : ℂ)).mul_prod (hf.integral_prod_right)).congr ?_
      filter_upwards with p
      obtain ⟨y', r⟩ := p
      rw [hHfun]
      simp only [one_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by
        show G' ((Submission.BoseGases.kcInsN n i) (y, r))
          = G' (Function.update ((Submission.BoseGases.kcInsN n i) (y', r)) i y)
        rw [Submission.BoseGases.update_kcInsN])
    -- ## Step D: transport back to the box
    have hAESM : AEStronglyMeasurable Hfun κ := by
      have hpc : AEStronglyMeasurable (fun x => aPC ℓ i G' x) κ :=
        aPC_aesm_aux i hG'm.aestronglyMeasurable
      have h4 : AEStronglyMeasurable
          (fun x => (((ℓ ^ 3 : ℝ)) : ℂ) * aPC ℓ i G' x) κ := hpc.const_mul _
      refine h4.congr ?_
      filter_upwards with x
      rw [hHfun, aPC, hμ₀]
      have hc : (((ℓ ^ 3 : ℝ)) : ℂ) * (((1 / ℓ ^ 3 : ℝ)) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, one_div, mul_inv_cancel₀ (by positivity), Complex.ofReal_one]
      rw [← mul_assoc, hc, one_mul]
    have hH : Integrable Hfun κ := (hmp.integrable_comp hAESM).mp hlift
    have haPC : Integrable (fun x => aPC ℓ i G' x) κ := by
      refine (hH.const_mul (((1 / ℓ ^ 3 : ℝ)) : ℂ)).congr ?_
      filter_upwards with x
      rw [hHfun, aPC, hμ₀]
    -- ## transfer to `G`
    have heq : aPC ℓ i G' =ᵐ[κ] aPC ℓ i G :=
      (aPC_congr_ae_box (ℓ := ℓ) i (ae_mono Measure.restrict_le_self hG'eq)).symm
    exact haPC.congr heq

/-! ## 4. The mode product is a.e. bounded -/

/-- The symmetric mode product of an a.e. bounded mode family is a.e. bounded. -/
theorem ae_bound_modeProd {m : ℕ} {e : Fin m → Sp → ℂ} (hbdd : ∀ l, MemLp (e l) ⊤)
    (d : ℕ) (α : Fin m →₀ ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂(volume : Measure (Submission.BoseGases.X d)),
      ‖Work.BoseDict.modeProd e d α x‖ ≤ C := by
  classical
  choose Cl hCl using fun l => Work.BoseDict.exists_bound_of_memLp_top (hbdd l)
  set D : Fin m → ℝ := fun l => max (Cl l) 0 with hD
  have hDnn : ∀ l, 0 ≤ D l := fun l => le_max_right _ _
  have hDle : ∀ l, Cl l ≤ D l := fun l => le_max_left _ _
  have hae : ∀ l, ∀ᵐ y ∂(volume : Measure Sp), ‖e l y‖ ≤ D l := by
    intro l
    filter_upwards [hCl l] with y hy using le_trans hy (hDle l)
  have hpull : ∀ (l : Fin m) (j : Fin d),
      ∀ᵐ x ∂(volume : Measure (Submission.BoseGases.X d)), ‖e l (x j)‖ ≤ D l := by
    intro l j
    exact (MeasureTheory.Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin d => (volume : Measure Sp)) (i := j)).eventually (hae l)
  have hall : ∀ᵐ x ∂(volume : Measure (Submission.BoseGases.X d)),
      ∀ p : (Fin d → Fin m) × Fin d, ‖e (p.1 p.2) (x p.2)‖ ≤ D (p.1 p.2) :=
    (Filter.eventually_all
      (p := fun (p : (Fin d → Fin m) × Fin d) (x : Submission.BoseGases.X d) =>
        ‖e (p.1 p.2) (x p.2)‖ ≤ D (p.1 p.2))).mpr fun p => hpull (p.1 p.2) p.2
  refine ⟨∑ σ : Fin d → Fin m,
      (if Work.BoseDict.modeMult σ = α then (1 : ℝ) else 0)
        * ∏ j : Fin d, D (σ j), ?_, ?_⟩
  · refine Finset.sum_nonneg fun σ _ => mul_nonneg ?_ ?_
    · split <;> norm_num
    · exact Finset.prod_nonneg fun j _ => hDnn (σ j)
  · filter_upwards [hall] with x hx
    calc ‖Work.BoseDict.modeProd e d α x‖
        = ‖∑ σ : Fin d → Fin m, (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
            * ∏ j : Fin d, e (σ j) (x j)‖ := by rw [Work.BoseDict.modeProd]
      _ ≤ ∑ σ : Fin d → Fin m,
            ‖(if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
              * ∏ j : Fin d, e (σ j) (x j)‖ := norm_sum_le _ _
      _ ≤ ∑ σ : Fin d → Fin m, (if Work.BoseDict.modeMult σ = α then (1 : ℝ) else 0)
            * ∏ j : Fin d, D (σ j) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [norm_mul]
          have h1 : ‖(if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)‖
              = (if Work.BoseDict.modeMult σ = α then (1 : ℝ) else 0) := by
            by_cases h : Work.BoseDict.modeMult σ = α <;> simp [h]
          rw [h1]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [norm_prod]
          exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hx (σ, j))

/-! ## 5. The labelling count: `Σ_i aPC_i M_α = α 0 · M_α` on the box -/

/-- The labelling product, in the updated slot `i`: the factor `e (σ i) y` splits off. -/
private lemma prod_update_slot {d m : ℕ} {e : Fin m → Sp → ℂ} (i : Fin d)
    (σ : Fin d → Fin m) (x : Submission.BoseGases.X d) (y : Sp) :
    (∏ j : Fin d, e (σ j) ((Function.update x i y) j))
      = (∏ j ∈ Finset.univ.erase i, e (σ j) (x j)) * e (σ i) y := by
  rw [← Finset.prod_erase_mul (Finset.univ)
    (fun j => e (σ j) ((Function.update x i y) j)) (Finset.mem_univ i)]
  congr 1
  · exact Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  · rw [Function.update_apply, if_pos rfl]

/-- On the box with `e 0 = c`, the `i`-erased labelling product carries the same factor `c`. -/
private lemma erase_prod_mul_c {d m : ℕ} [NeZero m] {e : Fin m → Sp → ℂ} {c : ℂ} (i : Fin d)
    (σ : Fin d → Fin m) (x : Submission.BoseGases.X d) (hx : ∀ j, e 0 (x j) = c)
    (hσ : σ i = 0) :
    (∏ j ∈ Finset.univ.erase i, e (σ j) (x j)) * c
      = ∏ j : Fin d, e (σ j) (x j) := by
  rw [← Finset.prod_erase_mul (Finset.univ) (fun j => e (σ j) (x j)) (Finset.mem_univ i)]
  rw [hσ, hx i]

/-- The `i`-th slot factor of the labelling count, with `c` folded in. -/
private lemma erase_prod_c_ite {d m : ℕ} [NeZero m] {e : Fin m → Sp → ℂ} {c : ℂ} (i : Fin d)
    (σ : Fin d → Fin m) (x : Submission.BoseGases.X d) (hx : ∀ j, e 0 (x j) = c) :
    (∏ j ∈ Finset.univ.erase i, e (σ j) (x j)) * (c * (if σ i = 0 then (1 : ℂ) else 0))
      = (if σ i = 0 then (1 : ℂ) else 0) * (∏ j : Fin d, e (σ j) (x j)) := by
  by_cases hσ : σ i = 0
  · rw [if_pos hσ]
    simp only [mul_one, one_mul]
    exact erase_prod_mul_c i σ x hx hσ
  · rw [if_neg hσ]
    simp only [mul_zero, zero_mul]

/-- The normalisation `(1/ℓ³)·(ℓ³·X) = X` in the shape in which it appears. -/
private lemma inv_cube_mul {ℓ : ℝ} (K P X : ℂ)
    (hc3 : (((1 / ℓ ^ 3 : ℝ)) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ) = 1) :
    (((1 / ℓ ^ 3 : ℝ)) : ℂ) * (K * (P * ((((ℓ ^ 3 : ℝ)) : ℂ) * X))) = K * (P * X) := by
  rw [show (((1 / ℓ ^ 3 : ℝ)) : ℂ) * (K * (P * ((((ℓ ^ 3 : ℝ)) : ℂ) * X)))
      = ((((1 / ℓ ^ 3 : ℝ)) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ)) * (K * (P * X)) from by ring,
    hc3, one_mul]

/-- **The labelling count.**  On the box, where the pinned mode `e 0` equals the constant `c`
of `θ_Λ`, the slot means of the symmetric mode product add up to the number of `0`-labelled
slots: `Σ_i aPC ℓ i M_α = α 0 · M_α`. -/
theorem sum_aPC_modeProd_aux (ℓ : ℝ) (hℓ : 0 < ℓ) {d : ℕ} {m : ℕ} [NeZero m]
    {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : Measure Sp), e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (α : Fin m →₀ ℕ) :
    ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox d ℓ)),
      (∑ i : Fin d, aPC ℓ i (Work.BoseDict.modeProd e d α) x)
        = ((α 0 : ℕ) : ℂ) * Work.BoseDict.modeProd e d α x := by
  classical
  obtain ⟨c, hcstar, hcae⟩ := hc
  have hc3 : (((ℓ ^ 3 : ℝ)) : ℂ) * (((1 / ℓ ^ 3 : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, one_div, mul_inv_cancel₀ (by positivity), Complex.ofReal_one]
  have hc3' : (((1 / ℓ ^ 3 : ℝ)) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ) = 1 := by
    rw [mul_comm]; exact hc3
  have hcstar' : (starRingEnd ℂ) c * c = (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv]; exact hcstar
  have hbox : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox d ℓ)),
      ∀ j : Fin d, e 0 (x j) = c := by
    rw [Submission.BoseGases.restrict_abox_eq_pi d ℓ]
    refine (Filter.eventually_all (p := fun (j : Fin d) (x : Submission.BoseGases.X d) =>
      e 0 (x j) = c)).mpr fun j =>
      (MeasureTheory.Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin d => (volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ))
        (i := j)).eventually (Work.BoseBoxFock.e0_ae_eq_c hℓ hcae)
  filter_upwards [hbox] with x hx
  -- ## the per-slot computation
  have key : ∀ i : Fin d, aPC ℓ i (Work.BoseDict.modeProd e d α) x
      = ∑ σ : Fin d → Fin m, (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
          * (if σ i = 0 then (1 : ℂ) else 0) * (∏ j : Fin d, e (σ j) (x j)) := by
    intro i
    have hint : ∀ σ : Fin d → Fin m, Integrable (fun y : Sp =>
        (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
          * ∏ j : Fin d, e (σ j) ((Function.update x i y) j))
        ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)) := by
      intro σ
      have h1 : Integrable (fun y : Sp =>
          ((if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
            * (∏ j ∈ Finset.univ.erase i, e (σ j) (x j))) * e (σ i) y) volume :=
        (Work.BoseDict.integrable_single hbdd hsupp (σ i)).const_mul _
      refine (h1.mono_measure Measure.restrict_le_self).congr ?_
      filter_upwards with y
      rw [prod_update_slot i σ x y]
      ring
    have hJ : ∀ σ : Fin d → Fin m,
        (∫ y in Submission.BoseGases.acube ℓ,
            (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
              * ∏ j : Fin d, e (σ j) ((Function.update x i y) j))
          = (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
              * ((∏ j ∈ Finset.univ.erase i, e (σ j) (x j))
                  * ((((ℓ ^ 3 : ℝ)) : ℂ) * (c * (if σ i = 0 then (1 : ℂ) else 0)))) := by
      intro σ
      have hcm := Work.BoseBoxFock.cubeMean_eq hℓ he hcae hcstar' (σ i)
      have hkey : (∫ y in Submission.BoseGases.acube ℓ, e (σ i) y)
          = (((ℓ ^ 3 : ℝ)) : ℂ) * (c * (if σ i = 0 then (1 : ℂ) else 0)) := by
        rw [← hcm]
        rw [show (((ℓ ^ 3 : ℝ)) : ℂ) * ((((1 / ℓ ^ 3 : ℝ)) : ℂ)
              * ∫ y in Submission.BoseGases.acube ℓ, e (σ i) y)
            = ((((ℓ ^ 3 : ℝ)) : ℂ) * (((1 / ℓ ^ 3 : ℝ)) : ℂ))
              * ∫ y in Submission.BoseGases.acube ℓ, e (σ i) y from by ring, hc3, one_mul]
      calc (∫ y in Submission.BoseGases.acube ℓ,
              (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
                * ∏ j : Fin d, e (σ j) ((Function.update x i y) j))
          = ∫ y in Submission.BoseGases.acube ℓ,
              ((if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
                * (∏ j ∈ Finset.univ.erase i, e (σ j) (x j))) * e (σ i) y := by
            apply integral_congr_ae
            filter_upwards with y
            rw [prod_update_slot i σ x y]
            ring
        _ = ((if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
                * (∏ j ∈ Finset.univ.erase i, e (σ j) (x j)))
              * (∫ y in Submission.BoseGases.acube ℓ, e (σ i) y) :=
            MeasureTheory.integral_const_mul _ _
        _ = (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
              * ((∏ j ∈ Finset.univ.erase i, e (σ j) (x j))
                  * ((((ℓ ^ 3 : ℝ)) : ℂ) * (c * (if σ i = 0 then (1 : ℂ) else 0)))) := by
            rw [hkey]; ring
    calc aPC ℓ i (Work.BoseDict.modeProd e d α) x
        = ((1 / ℓ ^ 3 : ℝ) : ℂ) * ∑ σ : Fin d → Fin m,
            (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
              * ((∏ j ∈ Finset.univ.erase i, e (σ j) (x j))
                  * ((((ℓ ^ 3 : ℝ)) : ℂ) * (c * (if σ i = 0 then (1 : ℂ) else 0)))) := by
          unfold aPC Work.BoseDict.modeProd
          rw [MeasureTheory.integral_finsetSum _ (fun σ _ => hint σ)]
          exact congrArg (fun z => ((1 / ℓ ^ 3 : ℝ) : ℂ) * z)
            (Finset.sum_congr rfl fun σ _ => hJ σ)
      _ = ∑ σ : Fin d → Fin m, (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
          * (if σ i = 0 then (1 : ℂ) else 0) * (∏ j : Fin d, e (σ j) (x j)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [inv_cube_mul _ _ _ hc3', erase_prod_c_ite i σ x hx]
          ring
  -- ## summing over the slots
  calc ∑ i : Fin d, aPC ℓ i (Work.BoseDict.modeProd e d α) x
      = ∑ i : Fin d, ∑ σ : Fin d → Fin m,
          (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
            * (if σ i = 0 then (1 : ℂ) else 0) * (∏ j : Fin d, e (σ j) (x j)) :=
        Finset.sum_congr rfl fun i _ => key i
    _ = ∑ σ : Fin d → Fin m, ∑ i : Fin d,
          (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
            * (if σ i = 0 then (1 : ℂ) else 0) * (∏ j : Fin d, e (σ j) (x j)) :=
        Finset.sum_comm
    _ = ∑ σ : Fin d → Fin m, (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
          * (((Work.BoseDict.modeMult σ 0 : ℕ)) : ℂ)
          * (∏ j : Fin d, e (σ j) (x j)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        have hcard : (∑ i : Fin d, (if σ i = 0 then (1 : ℂ) else 0))
            = (((Work.BoseDict.modeMult σ 0 : ℕ)) : ℂ) := by
          rw [Work.BoseDict.modeMult_apply, Finset.sum_boole (R := ℂ)]
        rw [← Finset.sum_mul, ← Finset.mul_sum, hcard]
    _ = ∑ σ : Fin d → Fin m, (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
          * (((α 0 : ℕ)) : ℂ) * (∏ j : Fin d, e (σ j) (x j)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        by_cases h : Work.BoseDict.modeMult σ = α
        · rw [if_pos h, h]
        · rw [if_neg h]; ring
    _ = (((α 0 : ℕ)) : ℂ) * Work.BoseDict.modeProd e d α x := by
        unfold Work.BoseDict.modeProd
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        ring

theorem modeProd_XS_pairing (ℓ : ℝ) (hℓ : 0 < ℓ) {d : ℕ} {m : ℕ} [NeZero m]
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (he : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (α : Fin m →₀ ℕ) (g : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hg : MeasureTheory.IntegrableOn g (Submission.BoseGases.abox d ℓ)) :
    (∫ u in Submission.BoseGases.abox d ℓ,
        (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u)
          * (Work.BoseBoxFock.XS ℓ (Finset.univ : Finset (Fin d)) g u))
      = (((d - α 0 : ℕ)) : ℂ)
        * ∫ u in Submission.BoseGases.abox d ℓ,
            (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u) * g u := by
  classical
  cases d with
  | zero =>
    have hzero : ∀ u : Submission.BoseGases.X 0,
        XS ℓ (Finset.univ : Finset (Fin 0)) g u = 0 := by
      intro u
      simp [XS]
    simp only [hzero, mul_zero, integral_zero, Nat.sub_eq_zero_of_le (Nat.zero_le (α 0)),
      Nat.cast_zero, zero_mul]
  | succ n =>
    set M : Submission.BoseGases.X (n + 1) → ℂ := Work.BoseDict.modeProd e (n + 1) α with hM
    have hMi : Integrable M := by
      rw [hM]; exact Work.BoseDict.integrable_modeProd hbdd hsupp α
    obtain ⟨CM, hCMnn, hCM⟩ := ae_bound_modeProd hbdd (n + 1) α
    have hCM' : ∀ᵐ x ∂(volume : Measure (Submission.BoseGases.X (n + 1))), ‖M x‖ ≤ CM := by
      rw [hM]; exact hCM
    set G : Submission.BoseGases.X (n + 1) → ℂ :=
      (Submission.BoseGases.abox (n + 1) ℓ).indicator g with hGdef
    have hGi : Integrable G :=
      hg.integrable_indicator (Submission.BoseGases.abox_measurable (n + 1) ℓ)
    have hGeq : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)), G x = g x := by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (Submission.BoseGases.abox_measurable (n + 1) ℓ)] with x hx
      rw [hGdef, Set.indicator_of_mem hx]
    have hsum : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)),
        (∑ i : Fin (n + 1), aPC ℓ i M x) = ((α 0 : ℕ) : ℂ) * M x := by
      rw [hM]; exact sum_aPC_modeProd_aux ℓ hℓ he hbdd hsupp hc α
    -- ## integrability of the pieces
    have hMg : Integrable (fun x => (starRingEnd ℂ) (M x) * G x) := by
      refine Integrable.mono' (hGi.norm.const_mul CM) ?_ ?_
      · exact (hMi.aestronglyMeasurable.star).mul hGi.aestronglyMeasurable
      · filter_upwards [hCM'] with x hx
        rw [norm_mul, starRingEnd_apply, norm_star]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    have hAg : IntegrableOn (fun x => (starRingEnd ℂ) (M x) * g x)
        (Submission.BoseGases.abox (n + 1) ℓ) :=
      (hMg.mono_measure Measure.restrict_le_self).congr
        (by filter_upwards [hGeq] with x hx; rw [hx])
    have hpcg : ∀ i : Fin (n + 1), IntegrableOn (fun x => aPC ℓ i g x)
        (Submission.BoseGases.abox (n + 1) ℓ) := fun i =>
      (integrableOn_aPC_of_integrable hℓ hGi i).congr
        (aPC_congr_ae_box (ℓ := ℓ) i hGeq)
    have hMpcg : ∀ i : Fin (n + 1), IntegrableOn
        (fun x => (starRingEnd ℂ) (M x) * aPC ℓ i g x)
        (Submission.BoseGases.abox (n + 1) ℓ) := by
      intro i
      have hbddM : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)),
          ‖M x‖ ≤ CM := ae_mono Measure.restrict_le_self hCM'
      refine Integrable.mono' ((hpcg i).norm.const_mul CM) ?_ ?_
      · exact (hMi.aestronglyMeasurable.restrict.star).mul (hpcg i).aestronglyMeasurable
      · filter_upwards [hbddM] with x hx
        rw [norm_mul, starRingEnd_apply, norm_star]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    have hpcMg : ∀ i : Fin (n + 1), IntegrableOn
        (fun x => (starRingEnd ℂ) (aPC ℓ i M x) * g x)
        (Submission.BoseGases.abox (n + 1) ℓ) := by
      intro i
      have hbddpc : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)),
          ‖aPC ℓ i M x‖ ≤ CM := aPC_ae_bound_aux hℓ i hCM'
      refine Integrable.mono'
        ((hGi.norm.const_mul CM).mono_measure Measure.restrict_le_self) ?_ ?_
      · exact ((aPC_aesm_aux i hMi.aestronglyMeasurable).star).mul hg.aestronglyMeasurable
      · filter_upwards [hbddpc, hGeq] with x h1 h2
        rw [norm_mul, starRingEnd_apply, norm_star, ← h2]
        exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    -- ## the duality `⟨P_i M, g⟩ = ⟨M, P_i g⟩`
    have hsymm : ∀ i : Fin (n + 1),
        (∫ x in Submission.BoseGases.abox (n + 1) ℓ, (starRingEnd ℂ) (aPC ℓ i M x) * g x)
          = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (starRingEnd ℂ) (M x) * aPC ℓ i g x := by
      intro i
      have hconj : aPC ℓ i (fun y => (starRingEnd ℂ) (M y))
          = fun x => (starRingEnd ℂ) (aPC ℓ i M x) := aPC_conj ℓ i M
      have hΦ : IntegrableOn
          (fun x => aPC ℓ i (fun y => (starRingEnd ℂ) (M y)) x * g x)
          (Submission.BoseGases.abox (n + 1) ℓ) := by
        rw [hconj]; exact hpcMg i
      have h := aPC_sym_box (ℓ := ℓ) i hΦ (hMpcg i)
      rw [hconj] at h
      exact h
    -- ## the two sides
    have key1 : (∫ u in Submission.BoseGases.abox (n + 1) ℓ,
          (starRingEnd ℂ) (M u) * XS ℓ (Finset.univ : Finset (Fin (n + 1))) g u)
        = ∑ i : Fin (n + 1),
            ((∫ u in Submission.BoseGases.abox (n + 1) ℓ, (starRingEnd ℂ) (M u) * g u)
              - ∫ u in Submission.BoseGases.abox (n + 1) ℓ,
                  (starRingEnd ℂ) (M u) * aPC ℓ i g u) := by
      rw [show (∫ u in Submission.BoseGases.abox (n + 1) ℓ,
            (starRingEnd ℂ) (M u) * XS ℓ (Finset.univ : Finset (Fin (n + 1))) g u)
          = ∫ u in Submission.BoseGases.abox (n + 1) ℓ, ∑ i : Fin (n + 1),
              ((starRingEnd ℂ) (M u) * g u - (starRingEnd ℂ) (M u) * aPC ℓ i g u) from by
        apply integral_congr_ae
        filter_upwards with u
        rw [show XS ℓ (Finset.univ : Finset (Fin (n + 1))) g u
              = ∑ i : Fin (n + 1), (g u - aPC ℓ i g u) from rfl,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring]
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [MeasureTheory.integral_sub hAg (hMpcg i)]
      · intro i _
        exact Integrable.sub hAg (hMpcg i)
    have hBsum : (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (starRingEnd ℂ) (aPC ℓ i M x) * g x)
        = ((α 0 : ℕ) : ℂ) * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (starRingEnd ℂ) (M x) * g x) := by
      rw [← MeasureTheory.integral_finsetSum Finset.univ
        (f := fun i x => (starRingEnd ℂ) (aPC ℓ i M x) * g x)
        (fun i _ => hpcMg i)]
      rw [MeasureTheory.integral_congr_ae (show (fun x => ∑ i : Fin (n + 1),
            (starRingEnd ℂ) (aPC ℓ i M x) * g x)
          =ᵐ[volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)]
          fun x => ((α 0 : ℕ) : ℂ) * ((starRingEnd ℂ) (M x) * g x) from by
        filter_upwards [hsum] with x hx
        rw [← Finset.sum_mul, ← map_sum, hx, map_mul, map_natCast]
        ring)]
      exact MeasureTheory.integral_const_mul _ _
    by_cases hα0 : α 0 ≤ n + 1
    · rw [key1, Finset.sum_sub_distrib]
      rw [show (∑ i : Fin (n + 1), ∫ u in Submission.BoseGases.abox (n + 1) ℓ,
            (starRingEnd ℂ) (M u) * aPC ℓ i g u)
          = ∑ i : Fin (n + 1), ∫ u in Submission.BoseGases.abox (n + 1) ℓ,
              (starRingEnd ℂ) (aPC ℓ i M u) * g u from
        Finset.sum_congr rfl fun i _ => (hsymm i).symm]
      rw [hBsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub hα0, sub_mul]
    · have hM0 : M = 0 := by
        funext x
        rw [hM]
        unfold Work.BoseDict.modeProd
        refine Finset.sum_eq_zero fun σ _ => ?_
        have hle : (Work.BoseDict.modeMult σ) 0 ≤ n + 1 := by
          rw [Work.BoseDict.modeMult_apply]
          exact le_trans (Finset.card_le_univ _) (le_of_eq (Fintype.card_fin (n + 1)))
        have hne : Work.BoseDict.modeMult σ ≠ α := by
          intro h
          exact hα0 (by rw [← h]; exact hle)
        rw [if_neg hne, zero_mul]
      rw [hM0, Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp hα0)), Nat.cast_zero, zero_mul]
      simp

end Work.BoseBoxFock
