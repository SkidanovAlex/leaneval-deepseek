import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.blockTwo3_II1_Ksub_stateDir
import Submission.Work.BoseBoxFock.chiChiImages_meas_bdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-!
# `Work.BoseBoxFock.blockII1_KsubDir_stripImages`

The block II.1 row shape of the `Q₂` pair row, with the lattice-image kernel `chiChiImages` *split
off* the limit kernel `K1lim` (step (S3) of the reduction of `FINDING_PotPairRows_exists.md`):

    rowShape21 Θ A (K1lim ℓ W') p
      − rowShape21 Θ A (K1lim ℓ W' − chiChiImages ℓ W) p
      = rowShape21 Θ A (chiChiImages ℓ W) p .

The right-hand side is the box-squared pairing of `chiChiImages ℓ W` against the fibre
`pairG21 p Θ A` (`blockII1_fibre_gen`), so the available hypothesis — the *images* pairing bound
`hPair`, stated for every `BoxSmooth` test function — applies directly.  The generic block lemma
`Work.BoseBoxFock.blockII1_KsubDir` (`pairRowS2Dir`) performs exactly this reduction, provided the
eight integrability hypotheses of its Fubini chain are supplied for the two kernels `K1lim ℓ W'`
and `K1lim ℓ W' − chiChiImages ℓ W`.

Everything here is `sorry`-free.
-/

/-- Pointwise-equal function to an integrable function: integrable. -/
private lemma stripImages_integrable_congr_pt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (h : Integrable f μ) (hfg : ∀ a, f a = g a) : Integrable g μ :=
  h.congr (Filter.Eventually.of_forall hfg)

/-- The two-fold update keeps the value inserted first. -/
private lemma stripImages_upd_upd_fst {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {z : Xn n} {y u : E3} : Function.update (Function.update z p.1 y) p.2 u p.1 = y := by
  rw [Function.update_apply, if_neg hp, Function.update_self]

/-- The two-fold update keeps the value inserted second. -/
private lemma stripImages_upd_upd_snd {n : ℕ} {p : Fin n × Fin n} {z : Xn n} {y u : E3} :
    Function.update (Function.update z p.1 y) p.2 u p.2 = u := by
  rw [Function.update_apply, if_pos rfl]

theorem blockII1_KsubDir_stripImages {n : ℕ} {ℓ ε : ℝ}
    (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (hℓ : 0 < ℓ)
    {Θ Θ₀ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ}
    {W W' : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘind : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hCutA : Work.BoseBoxFock.CutSmooth1 ℓ A)
    (hW'm : Measurable W') (hW'b : ∃ C : ℝ, ∀ x, ‖W' x‖ ≤ C) (hW's : HasCompactSupport W')
    (hWm : Measurable W) (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W)
    (hε : 0 ≤ ε)
    (hPair : ∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ,
      Work.BoseBoxFock.BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (Work.BoseBoxFock.massBox ℓ G))) :
    ‖Work.BoseBoxFock.rowShape21 Θ A (Work.BoseBoxFock.K1lim ℓ W') p
      - Work.BoseBoxFock.rowShape21 Θ A (fun w y => Work.BoseBoxFock.K1lim ℓ W' w y
          - Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) p‖
      ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.pairG21 p Θ A))
          + Real.sqrt (Work.BoseBoxFock.massBox ℓ (Work.BoseBoxFock.pairG21 p Θ A))) := by
  classical
  -- ## 0. The two kernels
  let chiF : E3 → E3 → ℂ := fun w y => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y
  -- ## 1. The `ℂ`-valued weight `W` and its image kernel
  have hWmc : Measurable (fun z : E3 => ((W z : ℝ) : ℂ)) := Complex.measurable_ofReal.comp hWm
  have hWbc : ∃ C : ℝ, ∀ x : E3, ‖((W x : ℝ) : ℂ)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hWb
    exact ⟨C, fun x => by simpa using hC x⟩
  have hWsc : HasCompactSupport (fun z : E3 => ((W z : ℝ) : ℂ)) := by
    have h : (fun z : E3 => ((W z : ℝ) : ℂ)) = Complex.ofReal ∘ W := rfl
    rw [h]
    exact hWs.comp_left (by simp)
  obtain ⟨hchim, hchib⟩ := chiChiImages_meas_bdd hℓ hWmc hWbc hWsc
  have hchimF : Measurable (Function.uncurry chiF) := hchim
  have hchibF : ∃ C : ℝ, ∀ w y : E3, ‖chiF w y‖ ≤ C := hchib
  -- ## 2. `W'` is integrable
  have hW'i : Integrable W' := by
    obtain ⟨C, hC⟩ := hW'b
    refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset (μ := (volume : Measure E3))
      (s := tsupport W') (f := W') (subset_tsupport W')).mp ?_
    exact MeasureTheory.IntegrableOn.of_bound (s := tsupport W') hW's.measure_lt_top
      hW'm.aestronglyMeasurable.restrict (max C 0)
      (Filter.Eventually.of_forall fun x => le_trans (hC x) (le_max_left _ _))
  -- ## 3. Data on the fibre `pairG21 p Θ A`
  have hPm : Measurable (Function.uncurry (pairG21 p Θ A)) := pairG21_measurable p hΘm hAm
  have hPb : ∃ C : ℝ, ∀ u y : E3, ‖pairG21 p Θ A u y‖ ≤ C := pairG21_bounded p hΘb hΘs hAb
  have hCsupp : Function.support (Function.uncurry (pairG21 p Θ A)) ⊆
      Set.prod (boxL ℓ) (boxL ℓ) :=
    (pairG_supports p hp (A := A) (B := A) hΘs).2.2
  have hbs : BoxSmooth ℓ (pairG21 p Θ A) :=
    (boxSmooth_fibres hℓ p hp ⟨Θ₀, hΘ₀, hΘind⟩ (A := A) (B := A) hCutA hCutA).2.2
  -- ## 4. Bounds on the two state factors
  obtain ⟨CT, hCT⟩ := hΘb
  obtain ⟨CA, hCA⟩ := hAb
  have hCT0 : (0 : ℝ) ≤ CT := le_trans (norm_nonneg _) (hCT 0)
  have hCA0 : (0 : ℝ) ≤ CA := le_trans (norm_nonneg _) (hCA 0)
  have hbnd : ∀ (x : Xn n) (y u : E3), ‖star (Θ x) * A (x p.1) * A (x p.2)
      * Θ (Function.update (Function.update x p.1 y) p.2 u)‖ ≤ CT * CA * CA * CT := by
    intro x y u
    have h1 : ‖Θ x‖ ≤ CT := hCT x
    have h2 : ‖A (x p.1)‖ ≤ CA := hCA _
    have h3 : ‖A (x p.2)‖ ≤ CA := hCA _
    have h4 : ‖Θ (Function.update (Function.update x p.1 y) p.2 u)‖ ≤ CT := hCT _
    rw [norm_mul, norm_mul, norm_mul, norm_star]
    exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hCT0) h3 (norm_nonneg _)
      (mul_nonneg hCT0 hCA0)) h4 (norm_nonneg _) (mul_nonneg (mul_nonneg hCT0 hCA0) hCA0)
  -- ## 5. The joint state functionals of the Fubini chain, with their support
  have hfacm : Measurable (fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2)) := by
    fun_prop
  have hfacb : ∃ C : ℝ, ∀ w : Xn n × (E3 × E3), ‖star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2)‖ ≤ C :=
    ⟨CT * CA * CA * CT, fun w => hbnd w.1 w.2.1 w.2.2⟩
  have hfacs : Function.support (fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2))
      ⊆ Set.prod (Work.MB.boxPow n ℓ) (Set.prod (boxL ℓ) (boxL ℓ)) := by
    intro w hw
    rw [Function.mem_support] at hw
    refine ⟨?_, ?_, ?_⟩
    · by_contra hx
      refine hw ?_
      have h0 : Θ w.1 = 0 := by
        by_contra h
        exact hx (hΘs (Function.mem_support.mpr h))
      simp [h0]
    · by_contra hy
      refine hw ?_
      have h0 : Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2) = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := p.1) (by rw [stripImages_upd_upd_fst hp]; exact hy)
      simp [h0]
    · by_contra hu
      refine hw ?_
      have h0 : Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2) = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := p.2) (by rw [stripImages_upd_upd_snd]; exact hu)
      simp [h0]
  have hfacm' : Measurable (fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1)) := by
    fun_prop
  have hfacb' : ∃ C : ℝ, ∀ w : Xn n × (E3 × E3), ‖star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1)‖ ≤ C :=
    ⟨CT * CA * CA * CT, fun w => hbnd w.1 w.2.2 w.2.1⟩
  have hfacs' : Function.support (fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1))
      ⊆ Set.prod (Work.MB.boxPow n ℓ) (Set.prod (boxL ℓ) (boxL ℓ)) := by
    intro w hw
    rw [Function.mem_support] at hw
    refine ⟨?_, ?_, ?_⟩
    · by_contra hx
      refine hw ?_
      have h0 : Θ w.1 = 0 := by
        by_contra h
        exact hx (hΘs (Function.mem_support.mpr h))
      simp [h0]
    · by_contra hy
      refine hw ?_
      have h0 : Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1) = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := p.2) (by rw [stripImages_upd_upd_snd]; exact hy)
      simp [h0]
    · by_contra hu
      refine hw ?_
      have h0 : Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1) = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := p.1) (by rw [stripImages_upd_upd_fst hp]; exact hu)
      simp [h0]
  -- ## 6. The four integrability facts for the image kernel `chiF`
  obtain ⟨hchi_int, hchi_x, hchi_swap, hchi_prod⟩ :=
    pairG21_kernel_integrable (K := chiF) (ℓ := ℓ) p hp hPm hPb hΘm ⟨CT, hCT⟩ hΘs hAm
      ⟨CA, hCA⟩ hchimF hchibF
  -- ## 7. The four integrability facts for `K1lim ℓ W'`
  have hK_int : Integrable (Function.uncurry (fun w y : E3 =>
      K1lim ℓ W' w y * pairG21 p Θ A w y)) (volume : Measure (E3 × E3)) :=
    K1lim_mul_integrable (G := pairG21 p Θ A) hℓ hW'i hPm.aestronglyMeasurable hPb hCsupp
  have hK_x : ∀ x : Xn n, Integrable (Function.uncurry (fun y u : E3 =>
      K1lim ℓ W' u y * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u))))
      (volume : Measure (E3 × E3)) := by
    intro x
    refine K1lim_mul_integrable_swap (G := fun y u : E3 => star (Θ x) * A (x p.1) * A (x p.2)
      * Θ (Function.update (Function.update x p.1 y) p.2 u)) hℓ hW'i ?_ ?_ ?_
    · exact (by fun_prop : Measurable (Function.uncurry (fun y u : E3 =>
        star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)))).aestronglyMeasurable
    · exact ⟨CT * CA * CA * CT, fun y u => hbnd x y u⟩
    · intro q hq
      rw [Function.mem_support] at hq
      refine ⟨?_, ?_⟩
      · by_contra hy
        refine hq ?_
        have h0 : Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0 :=
          theta_eq_zero_of_coord_notMem hΘs (j := p.1)
            (by rw [stripImages_upd_upd_fst hp]; exact hy)
        exact (show star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0 by rw [h0, mul_zero])
      · by_contra hu
        refine hq ?_
        have h0 : Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0 :=
          theta_eq_zero_of_coord_notMem hΘs (j := p.2)
            (by rw [stripImages_upd_upd_snd]; exact hu)
        exact (show star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0 by rw [h0, mul_zero])
  have hK_swap : Integrable (Function.uncurry (fun x : Xn n => fun z : E3 × E3 =>
      K1lim ℓ W' z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))))
      (volume : Measure (Xn n × (E3 × E3))) :=
    K1lim_mul_integrable_swapJoint (H := fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2))
      hℓ hW'i hfacm.aestronglyMeasurable hfacb hfacs
  have hK_prod : Integrable (fun z : E3 × E3 => ∫ x : Xn n,
      K1lim ℓ W' z.1 z.2 * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3)) :=
    K1lim_mul_integrable_prod (H := fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1))
      hℓ hW'i hfacm'.aestronglyMeasurable hfacb' hfacs'
  -- ## 8. The same four facts for the difference kernel `K1lim ℓ W' − chiF`
  have hK'_int : Integrable (Function.uncurry (fun w y : E3 =>
      (K1lim ℓ W' w y - chiF w y) * pairG21 p Θ A w y))
      (volume : Measure (E3 × E3)) :=
    stripImages_integrable_congr_pt (hK_int.sub hchi_int) (fun q => by
      show K1lim ℓ W' q.1 q.2 * pairG21 p Θ A q.1 q.2
          - chiF q.1 q.2 * pairG21 p Θ A q.1 q.2
        = (K1lim ℓ W' q.1 q.2 - chiF q.1 q.2) * pairG21 p Θ A q.1 q.2
      ring)
  have hK'_x : ∀ x : Xn n, Integrable (Function.uncurry (fun y u : E3 =>
      (K1lim ℓ W' u y - chiF u y) * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u))))
      (volume : Measure (E3 × E3)) := by
    intro x
    refine stripImages_integrable_congr_pt ((hK_x x).sub (hchi_x x)) (fun q => ?_)
    show K1lim ℓ W' q.2 q.1 * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2))
        - chiF q.2 q.1 * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2))
      = (K1lim ℓ W' q.2 q.1 - chiF q.2 q.1) * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2))
    ring
  have hK'_swap : Integrable (Function.uncurry (fun x : Xn n => fun z : E3 × E3 =>
      (K1lim ℓ W' z.2 z.1 - chiF z.2 z.1) * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))))
      (volume : Measure (Xn n × (E3 × E3))) :=
    stripImages_integrable_congr_pt (hK_swap.sub hchi_swap) (fun q => by
      show K1lim ℓ W' q.2.2 q.2.1 * (star (Θ q.1) * A (q.1 p.1) * A (q.1 p.2)
            * Θ (Function.update (Function.update q.1 p.1 q.2.1) p.2 q.2.2))
          - chiF q.2.2 q.2.1 * (star (Θ q.1) * A (q.1 p.1) * A (q.1 p.2)
            * Θ (Function.update (Function.update q.1 p.1 q.2.1) p.2 q.2.2))
        = (K1lim ℓ W' q.2.2 q.2.1 - chiF q.2.2 q.2.1) * (star (Θ q.1) * A (q.1 p.1)
            * A (q.1 p.2) * Θ (Function.update (Function.update q.1 p.1 q.2.1) p.2 q.2.2))
      ring)
  have hK_prod_mul : Integrable (fun z : E3 × E3 => K1lim ℓ W' z.1 z.2 *
      (∫ x : Xn n, star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3)) :=
    stripImages_integrable_congr_pt hK_prod (fun z => MeasureTheory.integral_const_mul _ _)
  have hchi_prod_mul : Integrable (fun z : E3 × E3 => chiF z.1 z.2 *
      (∫ x : Xn n, star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3)) :=
    stripImages_integrable_congr_pt hchi_prod (fun z => MeasureTheory.integral_const_mul _ _)
  have hK'_prod : Integrable (fun z : E3 × E3 => ∫ x : Xn n,
      (K1lim ℓ W' z.1 z.2 - chiF z.1 z.2) * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3)) := by
    have hmain : Integrable (fun z : E3 × E3 => (K1lim ℓ W' z.1 z.2 - chiF z.1 z.2) *
        (∫ x : Xn n, star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
        (volume : Measure (E3 × E3)) :=
      stripImages_integrable_congr_pt (hK_prod_mul.sub hchi_prod_mul) (fun z => by
        show K1lim ℓ W' z.1 z.2 * (∫ x : Xn n, star (Θ x) * A (x p.1) * A (x p.2)
              * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1))
            - chiF z.1 z.2 * (∫ x : Xn n, star (Θ x) * A (x p.1) * A (x p.2)
              * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1))
          = (K1lim ℓ W' z.1 z.2 - chiF z.1 z.2)
            * (∫ x : Xn n, star (Θ x) * A (x p.1) * A (x p.2)
              * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1))
        ring)
    exact stripImages_integrable_congr_pt hmain (fun z => (MeasureTheory.integral_const_mul _ _).symm)
  -- ## 9. The images pairing bound in the form of the kernel difference `K − K'`
  have hPair' : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in boxL ℓ, ∫ y in boxL ℓ,
          (K1lim ℓ W' w y - (K1lim ℓ W' w y - chiF w y)) * G w y‖
        ≤ ε * (Real.sqrt (L1Tails.pairEnergy ℓ G) + Real.sqrt (massBox ℓ G)) := by
    intro G hG
    have hcongr : (∫ w in boxL ℓ, ∫ y in boxL ℓ,
          (K1lim ℓ W' w y - (K1lim ℓ W' w y - chiF w y)) * G w y)
        = ∫ w in boxL ℓ, ∫ y in boxL ℓ, chiF w y * G w y := by
      refine MeasureTheory.setIntegral_congr_fun
        (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun w hw => ?_)
      refine MeasureTheory.setIntegral_congr_fun
        (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun y hy => ?_)
      ring
    rw [hcongr]
    exact hPair G hG
  -- ## 10. The block II.1 Dirichlet (S2) lemma at the two kernels
  exact blockII1_KsubDir (K := K1lim ℓ W') (K' := fun w y => K1lim ℓ W' w y - chiF w y)
    p hp hℓ hε hCsupp hPair' hbs hK_int hK'_int hK_x hK'_x hK_swap hK'_swap hK_prod hK'_prod

end Work.BoseBoxFock
