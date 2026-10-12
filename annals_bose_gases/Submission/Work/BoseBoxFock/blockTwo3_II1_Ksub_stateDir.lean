import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1lim_mul_integrable_pair
import Submission.Work.BoseBoxFock.K1lim_mul_integrable_prod
import Submission.Work.BoseBoxFock.K1lim_mul_integrable_swapJoint
import Submission.Work.BoseBoxFock.pairG21_bounded
import Submission.Work.BoseBoxFock.pairG21_kernel_integrable
import Submission.Work.BoseBoxFock.pairG21_measurable
import Submission.Work.BoseBoxFock.pairG23_bounded
import Submission.Work.BoseBoxFock.pairRowS2DirState
import Submission.Work.BoseBoxFock.phi23_bound_support
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.blockTwo3_II1_Ksub_stateDir` — the state-level step (S2) for blocks II.2, II.1

Two of the three block-level Dirichlet (S2) substitution lemmas of `pairRowS2Dir`
(`blockTwo3_KsubDir` for block II.2, `blockII1_KsubDir` for block II.1) are stated with the
integrability hypotheses of the block chain as *hypotheses*; at the state level — the level at
which the row `potPairRows` is used — all of them are consequences of the state data:

* measurability, everywhere boundedness and box support of `Θ` and of the weights `A`, `B`;
* `CutSmooth`/`CutSmooth1` shapes of the pin, which make the fibres `BoxSmooth`
  (`boxSmooth_fibres`);
* `K = K1exp` measurable and bounded, `K' = K1lim l W` with `W ∈ L¹` — the integrability inputs for
  the *unbounded* limit kernel in the orientations occurring here are
  `Work.BoseBoxFock.K1lim_mul_integrable` (pair), `…_slot` (one slot),
  `…_pair` (two slots of a configuration, from `lintegral_boxPow_eval_pair`),
  `…_swap` / `…_swapJoint` (transposed arguments) and `…_prod` (parameter integral).

`sorry`-free.
-/

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

open MeasureTheory

/-! ## 1. Elementary vocabulary -/

/-- The two-fold update keeps the value inserted first. -/
private lemma upd_upd_fst {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {z : Fin n → E3} {y u : E3} : Function.update (Function.update z p.1 y) p.2 u p.1 = y := by
  rw [Function.update_apply, if_neg hp, Function.update_self]

/-- The two-fold update keeps the value inserted second. -/
private lemma upd_upd_snd {n : ℕ} {p : Fin n × Fin n} {z : Fin n → E3} {y u : E3} :
    Function.update (Function.update z p.1 y) p.2 u p.2 = u := by
  rw [Function.update_apply, if_pos rfl]

/-- The box squared is invariant under the coordinate swap. -/
private lemma swap_mem_prod_boxL {l : ℝ} {a b : E3} :
    (a, b) ∈ Set.prod (boxL l) (boxL l) ↔ (b, a) ∈ Set.prod (boxL l) (boxL l) :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-! ## 2. The transposed limit-kernel pairing -/

/-- **The `K1lim` pairing against a bounded, box-supported kernel is integrable in the transposed
orientation.**  This is `K1lim_mul_integrable` transported along the measure-preserving coordinate
swap `(w, y) ↦ (y, w)`: the three `χ̂`-rows are bounded uniformly in the position
(`errBdd_pinQ*_bdd`), and the unswapped conclusion with the swapped kernel is exactly the pairing
in the transposed orientation. -/
theorem K1lim_mul_integrable_swap {l : ℝ} (hl : 0 < l) {W : E3 → ℝ}
    (hWi : MeasureTheory.Integrable W) {G : E3 → E3 → ℂ}
    (hGm : MeasureTheory.AEStronglyMeasurable (Function.uncurry G)
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)))
    (hGb : ∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C)
    (hGs : Function.support (Function.uncurry G) ⊆ Set.prod (boxL l) (boxL l)) :
    MeasureTheory.Integrable (fun q : E3 × E3 => K1lim l W q.2 q.1 * G q.1 q.2)
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) := by
  have hmp : MeasurePreserving (Prod.swap : E3 × E3 → E3 × E3)
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3))
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hG'm : MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun a b : E3 => G b a))
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) := by
    have h : (Function.uncurry (fun a b : E3 => G b a))
        = (Function.uncurry G) ∘ (Prod.swap : E3 × E3 → E3 × E3) := rfl
    rw [h]
    exact hGm.comp_measurePreserving hmp
  have hG'b : ∃ C : ℝ, ∀ a b, ‖G b a‖ ≤ C := hGb.imp fun C hC a b => hC b a
  have hG's : Function.support (Function.uncurry (fun a b : E3 => G b a)) ⊆
      Set.prod (boxL l) (boxL l) := by
    intro z hz
    have h2 : Function.uncurry G (Prod.swap z) ≠ 0 := hz
    exact swap_mem_prod_boxL.mpr (hGs h2)
  have h := K1lim_mul_integrable hl hWi hG'm hG'b hG's
  have hg : MeasureTheory.AEStronglyMeasurable
      (fun p : E3 × E3 => K1lim l W p.1 p.2 * G p.2 p.1)
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) := h.aestronglyMeasurable
  exact ((hmp.integrable_comp hg).mpr h).congr (Filter.Eventually.of_forall fun _ => rfl)

/-! ## 3. Bounded kernels: the two elementary integrability facts -/

/-- **The pairing of a bounded measurable kernel with a bounded, box-supported fibre is
integrable.** -/
theorem integrable_bdd_mul_fibre {l : ℝ} {K : E3 → E3 → ℂ} {G : E3 → E3 → ℂ}
    (hKm : Measurable (Function.uncurry K)) (hKb : ∃ C : ℝ, ∀ w y, ‖K w y‖ ≤ C)
    (hGm : Measurable (Function.uncurry G)) (hGb : ∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C)
    (hGs : Function.support (Function.uncurry G) ⊆ Set.prod (boxL l) (boxL l)) :
    MeasureTheory.Integrable (Function.uncurry (fun w y : E3 => K w y * G w y))
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) := by
  obtain ⟨CK, hCK⟩ := hKb
  obtain ⟨CG, hCG⟩ := hGb
  have hCK0 : 0 ≤ CK := le_trans (norm_nonneg _) (hCK 0 0)
  refine Work.MB.integrable_of_bdd_of_support
    (S := Set.prod (boxL l) (boxL l)) (C := CK * CG)
    ((Work.BoseB4.BoxData.boxL_measurableSet _ l).prod
      (Work.BoseB4.BoxData.boxL_measurableSet _ l)) ?_ (hKm.mul hGm).aestronglyMeasurable ?_ ?_
  · rw [show (volume : MeasureTheory.Measure (E3 × E3))
        = (MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume from rfl,
      show Set.prod (boxL l) (boxL l) = boxL l ×ˢ boxL l from rfl,
      MeasureTheory.Measure.prod_prod]
    exact ENNReal.mul_ne_top
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox l).measure_lt_top.ne
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox l).measure_lt_top.ne
  · intro z
    simp only [Function.uncurry]
    rw [norm_mul]
    exact mul_le_mul (hCK z.1 z.2) (hCG z.1 z.2) (norm_nonneg _) hCK0
  · intro z hz
    have h0 : G z.1 z.2 = 0 := Function.notMem_support.mp (fun h => hz (hGs h))
    exact (show K z.1 z.2 * G z.1 z.2 = 0 by rw [h0, mul_zero])

/-- **The `n`-particle pairing of a bounded kernel sitting at two slots of the configuration with
a bounded, box-supported state functional is integrable.** -/
theorem integrable_bdd_slots {n : ℕ} {l : ℝ} {p : Fin n × Fin n}
    {K : E3 → E3 → ℂ} {F : Xn n → ℂ}
    (hKm : Measurable (Function.uncurry K)) (hKb : ∃ C : ℝ, ∀ w y, ‖K w y‖ ≤ C)
    (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFs : Function.support F ⊆ Work.MB.boxPow n l) :
    MeasureTheory.Integrable (fun x : Xn n => K (x p.1) (x p.2) * F x)
      (MeasureTheory.volume : MeasureTheory.Measure (Xn n)) := by
  obtain ⟨CK, hCK⟩ := hKb
  obtain ⟨CF, hCF⟩ := hFb
  have hCK0 : 0 ≤ CK := le_trans (norm_nonneg _) (hCK 0 0)
  have hmK : Measurable (fun x : Xn n => K (x p.1) (x p.2)) :=
    hKm.comp (by fun_prop : Measurable fun x : Xn n => (x p.1, x p.2))
  refine Work.MB.integrable_of_bdd_of_support (S := Work.MB.boxPow n l) (C := CK * CF)
    (Work.MB.measurableSet_boxPow n l) (Work.MB.volume_boxPow_lt_top n l)
    (hmK.mul hFm).aestronglyMeasurable ?_ ?_
  · intro x
    rw [norm_mul]
    exact mul_le_mul (hCK _ _) (hCF x) (norm_nonneg _) hCK0
  · intro x hx
    rw [Function.notMem_support.mp (fun h => hx (hFs h)), mul_zero]

/-! ## 4. The two state-level (S2) wrappers -/

theorem blockTwo3_II1_Ksub_stateDir {n : ℕ} {l : ℝ}
    (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (hl : 0 < l) :
    (∀ {ε : ℝ} {Θ Θ₀ : Work.BoseDict.Xn n → ℂ}
        {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
        {W : EuclideanSpace ℝ (Fin 3) → ℝ},
      Measurable Θ → (∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) →
      Function.support Θ ⊆ Work.MB.boxPow n l →
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A → (∃ C : ℝ, ∀ x, ‖A x‖ ≤ C) →
      Measurable B → (∃ C : ℝ, ∀ x, ‖B x‖ ≤ C) →
      Work.BoseBoxFock.CutSmooth1 l A → Work.BoseBoxFock.CutSmooth1 l B →
      Measurable (Function.uncurry K) → (∃ C : ℝ, ∀ w y, ‖K w y‖ ≤ C) →
      MeasureTheory.Integrable W → 0 ≤ ε →
      (∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ, Work.BoseBoxFock.BoxSmooth l G →
        ‖∫ w in Work.BoseK15.corpusBox.boxL l, ∫ y in Work.BoseK15.corpusBox.boxL l,
            (K w y - Work.BoseBoxFock.K1lim l W w y) * G w y‖
          ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy l G)
              + Real.sqrt (Work.BoseBoxFock.massBox l G))) →
      ‖(∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3),
          star (Θ x) * K (x p.1) (x p.2) * star (A y) * star (B u)
            * Θ (Function.update (Function.update x p.1 y) p.2 u))
        - (∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3),
          star (Θ x) * Work.BoseBoxFock.K1lim l W (x p.1) (x p.2) * star (A y) * star (B u)
            * Θ (Function.update (Function.update x p.1 y) p.2 u))‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG23 p Θ A B))
            + Real.sqrt (Work.BoseBoxFock.massBox l (Work.BoseBoxFock.pairG23 p Θ A B))))
    ∧
    (∀ {ε : ℝ} {Θ Θ₀ : Work.BoseDict.Xn n → ℂ}
        {A : EuclideanSpace ℝ (Fin 3) → ℂ} {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
        {W : EuclideanSpace ℝ (Fin 3) → ℝ},
      Measurable Θ → (∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) →
      Function.support Θ ⊆ Work.MB.boxPow n l →
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A → (∃ C : ℝ, ∀ x, ‖A x‖ ≤ C) →
      Work.BoseBoxFock.CutSmooth1 l A →
      Measurable (Function.uncurry K) → (∃ C : ℝ, ∀ w y, ‖K w y‖ ≤ C) →
      MeasureTheory.Integrable W → 0 ≤ ε →
      (∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ, Work.BoseBoxFock.BoxSmooth l G →
        ‖∫ w in Work.BoseK15.corpusBox.boxL l, ∫ y in Work.BoseK15.corpusBox.boxL l,
            (K w y - Work.BoseBoxFock.K1lim l W w y) * G w y‖
          ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy l G)
              + Real.sqrt (Work.BoseBoxFock.massBox l G))) →
      ‖(∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3),
          star (Θ x) * A (x p.1) * A (x p.2) * K u y
            * Θ (Function.update (Function.update x p.1 y) p.2 u))
        - (∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3),
          star (Θ x) * A (x p.1) * A (x p.2) * Work.BoseBoxFock.K1lim l W u y
            * Θ (Function.update (Function.update x p.1 y) p.2 u))‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG21 p Θ A))
            + Real.sqrt (Work.BoseBoxFock.massBox l (Work.BoseBoxFock.pairG21 p Θ A)))) := by
  constructor
  · -- ### conjunct 1: block II.2 (`pairG23`)
    intro ε Θ Θ₀ A B K W hΘm hΘb hΘs hΘ₀ hΘind hAm hAb hBm hBb hCutA hCutB hKm hKb hWi hε hPair
    have hCsupp : Function.support (Function.uncurry (pairG23 p Θ A B)) ⊆
        Set.prod (Work.BoseK15.corpusBox.boxL l) (Work.BoseK15.corpusBox.boxL l) :=
      (pairG_supports p hp hΘs).2.1
    have hbs : BoxSmooth l (pairG23 p Θ A B) :=
      (boxSmooth_fibres hl p hp ⟨Θ₀, hΘ₀, hΘind⟩ hCutA hCutB).2.1
    have hGm : Measurable (Function.uncurry (pairG23 p Θ A B)) :=
      pairG23_measurable p hΘm hAm hBm
    have hGb : ∃ C : ℝ, ∀ w y, ‖pairG23 p Θ A B w y‖ ≤ C :=
      pairG23_bounded p hp hΘs hΘb hAb hBb
    have hIntK : MeasureTheory.Integrable
        (Function.uncurry (fun w y : E3 => K w y * pairG23 p Θ A B w y))
        (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) :=
      integrable_bdd_mul_fibre hKm hKb hGm hGb hCsupp
    have hIntK' : MeasureTheory.Integrable
        (Function.uncurry (fun w y : E3 => K1lim l W w y * pairG23 p Θ A B w y))
        (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) :=
      K1lim_mul_integrable hl hWi hGm.aestronglyMeasurable hGb hCsupp
    have hphi := phi23_bound_support p hp hΘs hΘb hAb hBb
    have hInt1 : MeasureTheory.Integrable
        (fun x : Xn n => K (x p.1) (x p.2) * phi23 p Θ A B x)
        (MeasureTheory.volume : MeasureTheory.Measure (Xn n)) :=
      integrable_bdd_slots hKm hKb (phi23_measurable p hΘm hAm hBm) hphi.1 hphi.2
    have hInt2 : MeasureTheory.Integrable
        (fun x : Xn n => K1lim l W (x p.1) (x p.2) * phi23 p Θ A B x)
        (MeasureTheory.volume : MeasureTheory.Measure (Xn n)) :=
      K1lim_mul_integrable_pair hl p hp hWi (phi23_measurable p hΘm hAm hBm).aestronglyMeasurable
        hphi.1 hphi.2
    exact blockTwo3_KsubDir p hp hl hε hCsupp hPair hbs hIntK hIntK' hInt1 hInt2
  · -- ### conjunct 2: block II.1 (`pairG21`)
    intro ε Θ Θ₀ A K W hΘm hΘb hΘs hΘ₀ hΘind hAm hAb hCutA hKm hKb hWi hε hPair
    have hPm : Measurable (Function.uncurry (pairG21 p Θ A)) := pairG21_measurable p hΘm hAm
    have hPb : ∃ C : ℝ, ∀ u y, ‖pairG21 p Θ A u y‖ ≤ C := pairG21_bounded p hΘb hΘs hAb
    have hCsupp : Function.support (Function.uncurry (pairG21 p Θ A)) ⊆
        Set.prod (Work.BoseK15.corpusBox.boxL l) (Work.BoseK15.corpusBox.boxL l) :=
      (pairG_supports (A := A) (B := fun _ : E3 => (0 : ℂ)) p hp hΘs).2.2
    have hbs : BoxSmooth l (pairG21 p Θ A) :=
      (boxSmooth_fibres hl p hp ⟨Θ₀, hΘ₀, hΘind⟩ hCutA hCutA).2.2
    obtain ⟨hIntK, hx, hSwap, hProd⟩ :=
      pairG21_kernel_integrable p hp hPm hPb hΘm hΘb hΘs hAm hAb hKm hKb
    have hIntK' : MeasureTheory.Integrable
        (Function.uncurry (fun w y : E3 => K1lim l W w y * pairG21 p Θ A w y))
        (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) :=
      K1lim_mul_integrable hl hWi hPm.aestronglyMeasurable hPb hCsupp
    obtain ⟨CT, hCT⟩ := hΘb
    obtain ⟨CA, hCA⟩ := hAb
    have hCT0 : 0 ≤ CT := le_trans (norm_nonneg _) (hCT 0)
    have hCA0 : 0 ≤ CA := le_trans (norm_nonneg _) (hCA 0)
    -- the state factor of the block II.1 shape, bounded
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
    -- the transposed pair orientation
    have hx' : ∀ x : Xn n, MeasureTheory.Integrable
        (Function.uncurry (fun y u : E3 => K1lim l W u y * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))))
        (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) := by
      intro x
      refine K1lim_mul_integrable_swap hl hWi ?_ ⟨CT * CA * CA * CT, fun y u => hbnd x y u⟩ ?_
      · exact (by fun_prop : Measurable (Function.uncurry (fun y u : E3 =>
          star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 y) p.2 u)))).aestronglyMeasurable
      · intro q hq
        rw [Function.mem_support] at hq
        refine ⟨?_, ?_⟩
        · by_contra hy
          refine hq ?_
          have h0 : Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0 :=
            theta_eq_zero_of_coord_notMem hΘs (j := p.1)
              (by rw [upd_upd_fst hp]; exact hy)
          exact (show star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0 by
            rw [h0, mul_zero])
        · by_contra hu
          refine hq ?_
          have h0 : Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0 :=
            theta_eq_zero_of_coord_notMem hΘs (j := p.2)
              (by rw [upd_upd_snd]; exact hu)
          exact (show star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0 by
            rw [h0, mul_zero])
    -- the two joint state functionals of the block II.1 shape
    have hfacm : Measurable (fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
        * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2)) := by
      fun_prop
    have hfacb : ∃ C : ℝ, ∀ w : Xn n × (E3 × E3), ‖star (Θ w.1) * A (w.1 p.1)
        * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2)‖ ≤ C :=
      ⟨CT * CA * CA * CT, fun w => hbnd w.1 w.2.1 w.2.2⟩
    have hfacs : Function.support (fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
        * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2))
        ⊆ Set.prod (Work.MB.boxPow n l) (Set.prod (boxL l) (boxL l)) := by
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
          theta_eq_zero_of_coord_notMem hΘs (j := p.1)
            (by rw [upd_upd_fst hp]; exact hy)
        simp [h0]
      · by_contra hu
        refine hw ?_
        have h0 : Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2) = 0 :=
          theta_eq_zero_of_coord_notMem hΘs (j := p.2)
            (by rw [upd_upd_snd]; exact hu)
        simp [h0]
    have hfacm' : Measurable (fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
        * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1)) := by
      fun_prop
    have hfacb' : ∃ C : ℝ, ∀ w : Xn n × (E3 × E3), ‖star (Θ w.1) * A (w.1 p.1)
        * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1)‖ ≤ C :=
      ⟨CT * CA * CA * CT, fun w => hbnd w.1 w.2.2 w.2.1⟩
    have hfacs' : Function.support (fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
        * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1))
        ⊆ Set.prod (Work.MB.boxPow n l) (Set.prod (boxL l) (boxL l)) := by
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
          theta_eq_zero_of_coord_notMem hΘs (j := p.2)
            (by rw [upd_upd_snd]; exact hy)
        simp [h0]
      · by_contra hu
        refine hw ?_
        have h0 : Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1) = 0 :=
          theta_eq_zero_of_coord_notMem hΘs (j := p.1)
            (by rw [upd_upd_fst hp]; exact hu)
        simp [h0]
    have hSwap' : MeasureTheory.Integrable
        (Function.uncurry (fun x : Xn n => fun z : E3 × E3 =>
          K1lim l W z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))))
        (MeasureTheory.volume : MeasureTheory.Measure (Xn n × (E3 × E3))) :=
      K1lim_mul_integrable_swapJoint hl hWi hfacm.aestronglyMeasurable hfacb hfacs
    have hProd' : MeasureTheory.Integrable
        (fun z : E3 × E3 => ∫ x : Xn n, K1lim l W z.1 z.2 *
          (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
        (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) :=
      K1lim_mul_integrable_prod hl hWi hfacm'.aestronglyMeasurable hfacb' hfacs'
    exact blockII1_KsubDir p hp hl hε hCsupp hPair hbs hIntK hIntK' hx hx' hSwap hSwap' hProd hProd'

end Work.BoseBoxFock
