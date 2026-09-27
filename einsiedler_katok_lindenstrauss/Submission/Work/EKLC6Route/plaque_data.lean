import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Route.atom_subset_uminus
import Submission.Work.EKLC6Route.uball_smul_mem_atom
import Submission.Work.EKLC6Route.ae_margin
import Submission.Work.EKLC6Route.S_basic
import Submission.Work.EKLC6Route.S_surj
import Submission.Work.EKLC6Route.piece_partition
import Submission.Work.EKLC6Route.piece_mem_of_mem_W
import Submission.Work.EKLC6Route.margin_transfer
import Submission.Work.EKLC6Core.borel_atom_saturated_measurable
import Submission.Work.EKLC6Core.ae_frequently_mem_of_pos_measure
import Submission.Work.EKLC6Core.cutHelpers
import Submission.Work.EKLContract.Lemmas.V_open_one

/-!
# `Work.EKLC6Route.plaque_data` — L6 of `C6GEOM_ROUTE_LEAD.md` §2.8

Let `w` be a window for the diagonal flow `Tm t = aDiag t ·` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` and let `μ`
be a probability measure preserved by `Tm t` whose invariant sets are trivial (`hqerg`).  Then on
a `μ`-conull Borel set `Z` the past σ-algebra `w.A = pastSigSet t w.S` of the coding partition of
the window is a *plaque algebra* for the contracted horospherical subgroup
`Uminus t = G⁻(t)`: its atoms are bounded open `Uminus t`-plaques, and on `Z ∩ w.W` the plaque
shape is contained in `Uball (Uminus t) 2`.

The conull set is `Z = deepVisit w ∩ (avoidN0 w ∩ marginSet w)`, where

* `deepVisit w` — the orbit visits the window at every depth `j`
  (`T^[n] x ∈ w.W ∩ θ ⁻¹' w.C j` frequently).  Conull by `ae_frequently_mem_of_pos_measure`
  applied to the positive measure set `w.W ∩ θ ⁻¹' w.C j` (`Window.hCpos`);
* `avoidN0 w` — the orbit misses the null exceptional set `w.N0`; conull by `μ w.N0 = 0`
  (`S_basic`) and invariance of `μ`;
* `marginSet w` — the *a.e. margin* of the window: `dU` decays at most like `e^{-λn/2}` along the
  orbit, `λ = lamExp t`.  Conull by `ae_margin`.

`Z` is atom-saturated: if `y ∈ atom w.A x` with `x ∈ Z` then `y ∈ avoidN0 w` and `y ∈ deepVisit w`
because the pieces `w.S m` are determined by the itinerary (`S_basic`) and the piece containing a
point of `w.W \ w.N0` is a first-return/depth/grid cell whose `θ`-level is monotone in the depth
(`S_subset_inter_of_mem`); and `y ∈ marginSet w` by `Work.EKLC6Route.margin_transfer`, since
`atom_subset_uminus` exhibits `y = u • x` with `u ∈ Uminus t`.

Hence `Z` is `w.A`-measurable (`borel_atom_saturated_measurable`) and the plaque data at every
point of `Z` follows from `atom_subset_uminus` (upper bound/orbit clause) and
`uball_smul_mem_atom` (lower bound, giving the openness of the shape).
-/

noncomputable section
namespace Work.EKLC6Route

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract
open Work.EKLC6Core

open Classical

variable {μ : MeasureTheory.Measure X3} {t : Fin 3 → ℝ}

/-! ## Iterates of the diagonal action -/

lemma Tm_iterate (t : Fin 3 → ℝ) (n : ℕ) (x : X3) : (Tm t)^[n] x = aDiag t ^ n • x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    change aDiag t • (aDiag t ^ k • x) = aDiag t ^ (k + 1) • x
    rw [← mul_smul, pow_succ']

lemma Tm_iterate_add (t : Fin 3 → ℝ) (j n : ℕ) (x : X3) :
    (Tm t)^[j] ((Tm t)^[n] x) = (Tm t)^[j + n] x := by
  rw [Tm_iterate, Tm_iterate, Tm_iterate, ← mul_smul, pow_add]

/-! ## The conull set -/

/-- Points whose orbit enters the window at every depth `j`. -/
def deepVisit (w : Window μ t) : Set X3 :=
  {x | ∀ j : ℕ, ∃ᶠ n in Filter.atTop, (Tm t)^[n] x ∈ w.W ∩ w.θ ⁻¹' w.C j}

/-- Points whose orbit misses the exceptional set `w.N0`. -/
def avoidN0 (w : Window μ t) : Set X3 := {x | ∀ n : ℕ, (Tm t)^[n] x ∉ w.N0}

/-- Points whose orbit keeps a margin `δ' e^{-λn/2}`, `λ = lamExp t`, from the boundary of the
window. -/
def marginSet (w : Window μ t) : Set X3 :=
  {x | ∃ δ' : ℝ, 0 < δ' ∧ ∀ n : ℕ,
    δ' * Real.exp (-(lamExp t / 2) * n) ≤ w.dU ((Tm t)^[n] x)}

/-- The good set `Z` of §2.8 of the route document. -/
def goodSet (w : Window μ t) : Set X3 := deepVisit w ∩ (avoidN0 w ∩ marginSet w)

lemma mem_goodSet {w : Window μ t} {x : X3} :
    x ∈ goodSet w ↔ x ∈ deepVisit w ∧ x ∈ avoidN0 w ∧ x ∈ marginSet w := Iff.rfl

/-! ## Measurability of the three pieces of the good set -/

lemma measurableSet_deepVisit {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Window μ t)
    (hmp : MeasurePreserving (Tm t) μ μ) : MeasurableSet (deepVisit w) := by
  obtain ⟨-, -, -, -, hWmeas, -, -⟩ := S_basic w hmp
  have hset : deepVisit w = ⋂ j : ℕ, ⋂ N : ℕ, ⋃ n ∈ Set.Ici N,
        (Tm t)^[n] ⁻¹' (w.W ∩ w.θ ⁻¹' w.C j) := by
    ext x
    simp only [deepVisit, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_Ici,
      Set.mem_preimage, Filter.frequently_atTop, ge_iff_le]
    constructor
    · intro h j N
      obtain ⟨n, hn, hp⟩ := h j N
      exact ⟨n, hn, hp⟩
    · intro h j N
      obtain ⟨n, hn, hp⟩ := h j N
      exact ⟨n, hn, hp⟩
  rw [hset]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun N => ?_
  refine MeasurableSet.biUnion (Set.to_countable _) fun n _ => ?_
  exact (((continuous_const_smul (aDiag t)).iterate n).measurable)
    (hWmeas.inter ((w.hCmeas j).preimage w.hθ))

lemma measurableSet_N0 {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Window μ t)
    (hmp : MeasurePreserving (Tm t) μ μ) : MeasurableSet w.N0 := by
  obtain ⟨-, -, -, -, hWmeas, hdUmeas, -⟩ := S_basic w hmp
  rw [show w.N0 = neverReturnSet t w.W ∪ {z : X3 | w.dU z = 0} from rfl]
  refine (firstReturn_partition hWmeas).2.1.union ?_
  exact hdUmeas (measurableSet_singleton (0 : ℝ))

lemma measurableSet_avoidN0 {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Window μ t)
    (hmp : MeasurePreserving (Tm t) μ μ) : MeasurableSet (avoidN0 w) := by
  have hN0m := measurableSet_N0 w hmp
  have hset : avoidN0 w = ⋂ n : ℕ, (Tm t)^[n] ⁻¹' (w.N0)ᶜ := by
    ext x
    simp only [avoidN0, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff]
  rw [hset]
  refine MeasurableSet.iInter fun n => ?_
  exact (((continuous_const_smul (aDiag t)).iterate n).measurable) hN0m.compl

/-- The `q`-th piece of the rational-unions description of the margin set. -/
def marginSetQ (w : Window μ t) (q : ℚ) : Set X3 :=
  if (0 : ℝ) < (q : ℝ) then ⋂ n : ℕ, (Tm t)^[n] ⁻¹'
      {y : X3 | (q : ℝ) * Real.exp (-(lamExp t / 2) * n) ≤ w.dU y}
    else ∅

lemma marginSet_eq_iUnion (w : Window μ t) :
    marginSet w = ⋃ q : ℚ, marginSetQ w q := by
  ext x
  constructor
  · rintro ⟨δ', hδ', hδ'ge⟩
    obtain ⟨q, hq0, hqδ⟩ := exists_rat_btwn hδ'
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    rw [marginSetQ, if_pos hq0]
    refine Set.mem_iInter.mpr fun n => ?_
    have hexp : 0 ≤ Real.exp (-(lamExp t / 2) * (n : ℝ)) := Real.exp_nonneg _
    exact le_trans (mul_le_mul_of_nonneg_right hqδ.le hexp) (hδ'ge n)
  · rintro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨q, hq⟩ := hx
    by_cases hq0 : (0 : ℝ) < (q : ℝ)
    · rw [marginSetQ, if_pos hq0] at hq
      exact ⟨(q : ℝ), hq0, fun n => Set.mem_iInter.mp hq n⟩
    · rw [marginSetQ, if_neg hq0] at hq
      exact absurd hq (by simp)

lemma measurableSet_marginSet {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Window μ t)
    (hmp : MeasurePreserving (Tm t) μ μ) : MeasurableSet (marginSet w) := by
  obtain ⟨-, -, -, -, -, hdUmeas, -⟩ := S_basic w hmp
  rw [marginSet_eq_iUnion]
  refine MeasurableSet.iUnion fun q => ?_
  rw [marginSetQ]
  by_cases hq : (0 : ℝ) < (q : ℝ)
  · rw [if_pos hq]
    refine MeasurableSet.iInter fun n => ?_
    exact (((continuous_const_smul (aDiag t)).iterate n).measurable)
      (hdUmeas measurableSet_Ici)
  · rw [if_neg hq]
    exact MeasurableSet.empty

lemma measurableSet_goodSet {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Window μ t)
    (hmp : MeasurePreserving (Tm t) μ μ) : MeasurableSet (goodSet w) :=
  (measurableSet_deepVisit w hmp).inter
    ((measurableSet_avoidN0 w hmp).inter (measurableSet_marginSet w hmp))

/-! ## Conullness of the three pieces -/

lemma ae_deepVisit {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {t : Fin 3 → ℝ} (w : Window μ t) (hmp : MeasurePreserving (Tm t) μ μ)
    (hqerg : ∀ E : Set X3, MeasurableSet E → (Tm t) ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0) :
    ∀ᵐ x ∂μ, x ∈ deepVisit w := by
  obtain ⟨-, -, -, -, hWmeas, -, -⟩ := S_basic w hmp
  rw [deepVisit]
  simp only [Set.mem_ofPred_eq]
  rw [MeasureTheory.ae_all_iff]
  intro j
  have hAm : MeasurableSet (w.W ∩ w.θ ⁻¹' w.C j) :=
    hWmeas.inter ((w.hCmeas j).preimage w.hθ)
  have hAp : 0 < μ (w.W ∩ w.θ ⁻¹' w.C j) := by
    rw [Window.W]
    exact w.hCpos j
  exact ae_frequently_mem_of_pos_measure hmp hqerg hAm hAp

lemma ae_avoidN0 {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {t : Fin 3 → ℝ} (w : Window μ t) (hmp : MeasurePreserving (Tm t) μ μ) :
    ∀ᵐ x ∂μ, x ∈ avoidN0 w := by
  obtain ⟨-, -, -, hN0, -, -, -⟩ := S_basic w hmp
  rw [avoidN0]
  simp only [Set.mem_ofPred_eq]
  rw [MeasureTheory.ae_all_iff]
  intro n
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1
    ((hmp.iterate n).preimage_null hN0)] with x hx
  exact hx

lemma ae_marginSet {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {t : Fin 3 → ℝ} (w : Window μ t) (hmp : MeasurePreserving (Tm t) μ μ) :
    ∀ᵐ x ∂μ, x ∈ marginSet w := by
  rw [marginSet]
  exact ae_margin w hmp

lemma goodSet_compl {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {t : Fin 3 → ℝ} (w : Window μ t) (hmp : MeasurePreserving (Tm t) μ μ)
    (hqerg : ∀ E : Set X3, MeasurableSet E → (Tm t) ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0) :
    μ (goodSet w)ᶜ = 0 := by
  have h : ∀ᵐ x ∂μ, x ∈ goodSet w := by
    filter_upwards [ae_deepVisit w hmp hqerg, ae_avoidN0 w hmp, ae_marginSet w hmp]
      with x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  rw [show (goodSet w)ᶜ = {a : X3 | a ∉ goodSet w} from rfl]
  exact MeasureTheory.ae_iff.mp h

/-! ## Positive measure of the window -/

lemma measure_W_pos (w : Window μ t) : 0 < μ w.W := by
  rw [Window.W]
  exact lt_of_lt_of_le (w.hCpos 0) (measure_mono Set.inter_subset_left)

/-! ## The margin of a point of the good set -/

noncomputable def mar (w : Window μ t) (z : X3) : ℝ :=
  if h : ∃ δ' : ℝ, 0 < δ' ∧ ∀ n : ℕ,
      δ' * Real.exp (-(lamExp t / 2) * n) ≤ w.dU ((Tm t)^[n] z)
    then Classical.choose h else 1

lemma mar_pos (w : Window μ t) (z : X3) : 0 < mar w z := by
  rw [mar]
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · norm_num

lemma mar_spec (w : Window μ t) {z : X3} (hz : z ∈ marginSet w) :
    ∀ n : ℕ, mar w z * Real.exp (-(lamExp t / 2) * n) ≤ w.dU ((Tm t)^[n] z) := by
  have h : ∃ δ' : ℝ, 0 < δ' ∧ ∀ n : ℕ,
      δ' * Real.exp (-(lamExp t / 2) * n) ≤ w.dU ((Tm t)^[n] z) := hz
  rw [mar, dif_pos h]
  exact (Classical.choose_spec h).2

/-! ## The piece structure -/

lemma mem_Jset_some_iff' (w : Window μ t) {x : X3} {j : ℕ} :
    x ∈ w.Jset (some j) ↔ x ∈ w.W ∧ w.θ x ∈ w.C j ∧ w.θ x ∉ w.C (j + 1) := by
  simp only [Window.Jset, Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff]

lemma mem_Jset_none_iff' (w : Window μ t) {x : X3} :
    x ∈ w.Jset none ↔ x ∈ w.W ∧ ∀ j : ℕ, w.θ x ∈ w.C j := by
  simp only [Window.Jset, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter]

/-- The exceptional set is one of the enumerated pieces. -/
lemma exists_S_eq_N0 (w : Window μ t) : ∃ m : ℕ, w.S m = w.N0 := by
  obtain ⟨m, hm⟩ := S_surj w (some none)
  exact ⟨m, by rw [hm]; rfl⟩

/-- **The piece structure.**  A point `z` of the window which misses `w.N0` and lies at depth `j`
is contained in a piece which lies entirely in `w.W ∩ θ ⁻¹' w.C j`. -/
lemma S_subset_inter_of_mem {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Window μ t)
    (hmp : MeasurePreserving (Tm t) μ μ) {m : ℕ} {z : X3} (hz : z ∈ w.S m)
    (hzW : z ∈ w.W) (hzN : z ∉ w.N0) {j : ℕ} (hzj : z ∈ w.θ ⁻¹' w.C j) :
    w.S m ⊆ w.W ∩ w.θ ⁻¹' w.C j := by
  obtain ⟨-, hSdisj, -, -, -, -, -⟩ := S_basic w hmp
  obtain ⟨i, J, c, -, -, hJ, -, hpz⟩ := piece_mem_of_mem_W w hzW hzN
  obtain ⟨m₀, hm₀⟩ := S_surj w (some (some (i, J, c)))
  have hzm₀ : z ∈ w.S m₀ := by rw [hm₀]; exact hpz
  have hm : m = m₀ := by
    by_contra hne
    exact Set.disjoint_left.1 (hSdisj m m₀ hne) hz hzm₀
  rw [hm, hm₀]
  rcases J with _ | j₀
  · intro x hx
    obtain ⟨-, hxfr, hxJ, -, -⟩ := (Window.mem_D w).1 hx
    exact ⟨hxfr.1.1, (mem_Jset_none_iff' w).1 hxJ |>.2 j⟩
  · have hle : j ≤ j₀ := by
      by_contra hcon
      push_neg at hcon
      have hzJ := (mem_Jset_some_iff' w).1 hJ
      exact hzJ.2.2 (w.hCanti (by omega : j₀ + 1 ≤ j) hzj)
    intro x hx
    obtain ⟨-, hxfr, hxJ, -, -⟩ := (Window.mem_D w).1 hx
    exact ⟨hxfr.1.1, w.hCanti hle ((mem_Jset_some_iff' w).1 hxJ).2.1⟩



/-! ## Atom saturation of the good set -/

lemma mem_goodSet_of_mem_atom {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Window μ t)
    (hmp : MeasurePreserving (Tm t) μ μ)
    (hqerg : ∀ E : Set X3, MeasurableSet E → (Tm t) ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0)
    {x y : X3} (hx : x ∈ goodSet w) (hy : y ∈ atom w.A x) : y ∈ goodSet w := by
  obtain ⟨-, hSdisj, hScover, -, -, -, hatomdesc⟩ := S_basic w hmp
  have hy' : ∀ n m : ℕ, (Tm t)^[n] x ∈ w.S m → (Tm t)^[n] y ∈ w.S m := by
    have h := hy
    rw [hatomdesc x] at h
    exact h
  have hxvisit : ∀ j : ℕ, ∃ᶠ n in Filter.atTop,
      (Tm t)^[n] x ∈ w.W ∩ w.θ ⁻¹' w.C j := hx.1
  have hxN : ∀ n : ℕ, (Tm t)^[n] x ∉ w.N0 := hx.2.1
  -- the point of the enumeration which is the exceptional set
  obtain ⟨mN, hmN⟩ := exists_S_eq_N0 w
  -- 1. `y` misses the exceptional set
  have hyN : ∀ n : ℕ, (Tm t)^[n] y ∉ w.N0 := by
    intro n hcon
    obtain ⟨m₀, hm₀⟩ : ∃ m, (Tm t)^[n] x ∈ w.S m := by
      have h : (Tm t)^[n] x ∈ ⋃ m, w.S m := by rw [hScover]; trivial
      simpa using h
    have hy₀ : (Tm t)^[n] y ∈ w.S m₀ := hy' n m₀ hm₀
    rcases eq_or_ne m₀ mN with h | h
    · have hxN0 : (Tm t)^[n] x ∈ w.N0 := hmN ▸ (h ▸ hm₀)
      exact hxN n hxN0
    · exact Set.disjoint_left.1 (hSdisj m₀ mN h) hy₀ (by rw [hmN]; exact hcon)
  -- 2. `y` visits the window at every depth
  have hyvisit : ∀ j : ℕ, ∃ᶠ n in Filter.atTop,
      (Tm t)^[n] y ∈ w.W ∩ w.θ ⁻¹' w.C j := by
    intro j
    refine (hxvisit j).mono ?_
    intro n hn
    obtain ⟨m, hm⟩ : ∃ m, (Tm t)^[n] x ∈ w.S m := by
      have h : (Tm t)^[n] x ∈ ⋃ m, w.S m := by rw [hScover]; trivial
      simpa using h
    exact S_subset_inter_of_mem w hmp hm hn.1 (hxN n) hn.2 (hy' n m hm)
  -- 3. `y` keeps a margin
  have hymar : y ∈ marginSet w := by
    obtain ⟨δ', hδ', hmar⟩ := hx.2.2
    have hpos : ∀ n : ℕ, w.dU ((Tm t)^[n] y) ≠ 0 := by
      intro n hzero
      exact hyN n (Or.inr hzero)
    obtain ⟨C, -, hU, -⟩ := atom_subset_uminus w hxvisit hxN
    obtain ⟨u, hu, hyu, -⟩ := hU y hy
    exact margin_transfer w hδ' hu hyu hmar hpos
  exact ⟨hyvisit, hyN, hymar⟩

/-! ## The plaque data at a point of the good set -/

lemma atom_subset_orbit {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {t : Fin 3 → ℝ} (w : Window μ t) {x : X3} (hx : x ∈ goodSet w) :
    atom w.A x ⊆ (fun u : SL3 => u • x) '' (Uminus t : Set SL3) := by
  obtain ⟨C, -, hU, -⟩ := atom_subset_uminus w hx.1 hx.2.1
  rintro y hy
  obtain ⟨u, hu, hyu, -⟩ := hU y hy
  exact ⟨u, hu, hyu.symm⟩

lemma shape_bound {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {t : Fin 3 → ℝ} (w : Window μ t) {x : X3} (hx : x ∈ goodSet w) :
    ∃ C : ℝ, ∀ u ∈ shape w.A (Uminus t) x, ∀ i j : Fin 3,
      |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C := by
  obtain ⟨C, -, -, hbd⟩ := atom_subset_uminus w hx.1 hx.2.1
  exact ⟨C, fun u hu i j => hbd u hu.1 hu.2 i j⟩

/-- **Openness of the shape.**  For `x` in the good set the shape of the atom is `O ∩ Uminus t`
for an open `O`: a point `u` of the shape is a plaque point `u • x ∈ atom x`, whose own margin
(the good set is atom-saturated) gives an open ball of `Uminus t` around `u` inside the shape. -/
lemma shape_open {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {t : Fin 3 → ℝ} (w : Window μ t) (hmp : MeasurePreserving (Tm t) μ μ)
    (hqerg : ∀ E : Set X3, MeasurableSet E → (Tm t) ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0)
    {x : X3} (hx : x ∈ goodSet w) :
    ∃ O : Set SL3, IsOpen O ∧ shape w.A (Uminus t) x = O ∩ (Uminus t : Set SL3) := by
  have hsat : ∀ y ∈ atom w.A x, y ∈ goodSet w :=
    fun y hy => mem_goodSet_of_mem_atom w hmp hqerg hx hy
  refine ⟨⋃ u ∈ shape w.A (Uminus t) x, (fun g : SL3 => g * u⁻¹) ⁻¹' V (mar w (u • x) / 8),
    ?_, ?_⟩
  · refine isOpen_iUnion fun u => isOpen_iUnion fun _ => ?_
    exact ((Work.EKLContract.Lemmas.V_open_one _ (by have := mar_pos w (u • x); linarith)).1.preimage
      (continuous_id.mul continuous_const))
  · ext g
    constructor
    · intro hg
      refine ⟨Set.mem_iUnion₂.mpr ⟨g, hg, ?_⟩, hg.1⟩
      show g * g⁻¹ ∈ V (mar w (g • x) / 8)
      rw [mul_inv_cancel]
      exact (Work.EKLContract.Lemmas.V_open_one _ (by have := mar_pos w (g • x); linarith)).2
    · rintro ⟨hgO, hgU⟩
      rw [Set.mem_iUnion₂] at hgO
      obtain ⟨u, hu, hgu⟩ := hgO
      have huU : u ∈ Uminus t := hu.1
      have huy : u • x ∈ atom w.A x := hu.2
      have hyZ : u • x ∈ goodSet w := hsat (u • x) huy
      have hmar := mar_spec w hyZ.2.2
      have hball := uball_smul_mem_atom w (mar_pos w (u • x)) hmar
      have hv : g * u⁻¹ ∈ Work.EKLComp.Uball (Uminus t) (mar w (u • x) / 8) :=
        ⟨Subgroup.mul_mem (Uminus t) hgU (Subgroup.inv_mem (Uminus t) huU), hgu⟩
      have hres := hball (g * u⁻¹) hv
      have hatom_eq : atom w.A (u • x) = atom w.A x := atom_eq_of_mem_atom_c huy
      have hpt : (g * u⁻¹) • (u • x) = g • x := by rw [mul_smul, inv_smul_smul]
      refine ⟨hgU, ?_⟩
      rwa [← hatom_eq, ← hpt]

/-! ## The plaque algebra on the good set -/

theorem plaque_data {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Work.EKLC6Route.Window μ t)
    (hmp : MeasureTheory.MeasurePreserving (Work.EKLC6Route.Tm t) μ μ)
    (hqerg : ∀ E : Set Work.EKLContract.X3, MeasurableSet E →
      (Work.EKLC6Route.Tm t) ⁻¹' E =ᵐ[μ] E → μ E = 0 ∨ μ Eᶜ = 0) :
    ∃ Z : Set Work.EKLContract.X3, MeasurableSet Z ∧ μ Zᶜ = 0 ∧
      Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z w.A ∧
      0 < μ (Z ∩ w.W) ∧
      ∀ x ∈ Z ∩ w.W, ∀ u ∈ Work.EKLC6Core.Uminus t, u • x ∈ Work.EKLContract.atom w.A x →
        ∀ i j : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 2 := by
  have hZbor := measurableSet_goodSet w hmp
  have hZc := goodSet_compl w hmp hqerg
  have hsat : ∀ x ∈ goodSet w, atom w.A x ⊆ goodSet w :=
    fun x hx y hy => mem_goodSet_of_mem_atom w hmp hqerg hx hy
  have hAle : w.A ≤ borel X3 := by
    have hSb : MeasurableSpace.generateFrom (Set.range w.S) ≤ borel X3 :=
      MeasurableSpace.generateFrom_le fun s hs => by
        obtain ⟨n, rfl⟩ := hs
        exact (S_basic w hmp).1 n
    have h1 : w.A =
        Work.EKLC6Core.descSig t (MeasurableSpace.generateFrom (Set.range w.S)) := rfl
    rw [h1]
    exact Work.EKLC6Core.descSig_le_borel _ hSb
  obtain ⟨b', hb'c, hb'⟩ := Work.EKLC6Core.descSig_countably_generated
    (t := t) (M := MeasurableSpace.generateFrom (Set.range w.S)) (b := Set.range w.S)
    (Set.countable_range w.S) rfl
  have hcgen : @MeasurableSpace.CountablyGenerated X3 w.A :=
    MeasurableSpace.CountablyGenerated.mk (m := w.A) ⟨b', hb'c, hb'⟩
  have hZmeas : @MeasurableSet X3 w.A (goodSet w) :=
    Work.EKLC6Core.borel_atom_saturated_measurable hAle hcgen hZbor hsat
  refine ⟨goodSet w, hZbor, hZc, ⟨hAle, ⟨b', hb'c, hb'⟩, hZmeas, ?_⟩, ?_, ?_⟩
  · intro x hx
    exact ⟨hsat x hx, atom_subset_orbit w hx, shape_open w hmp hqerg hx, shape_bound w hx⟩
  · have h1 : μ w.W ≤ μ (goodSet w ∩ w.W) := by
      calc μ w.W ≤ μ ((goodSet w ∩ w.W) ∪ (goodSet w)ᶜ) :=
            measure_mono fun y hy => by
              by_cases hid : y ∈ goodSet w
              · exact Or.inl ⟨hid, hy⟩
              · exact Or.inr hid
        _ ≤ μ (goodSet w ∩ w.W) + μ (goodSet w)ᶜ := measure_union_le _ _
        _ = μ (goodSet w ∩ w.W) := by rw [hZc, add_zero]
    exact lt_of_lt_of_le (measure_W_pos w) h1
  · intro x hx u hu hux i j
    have hx' : x ∈ deepVisit w ∧ x ∈ avoidN0 w ∧ x ∈ marginSet w := hx.1
    obtain ⟨C, hC2, -, hbd⟩ := atom_subset_uminus w hx'.1 hx'.2.1
    rw [hC2 hx.2] at hbd
    exact hbd u hu hux i j

end Work.EKLC6Route
