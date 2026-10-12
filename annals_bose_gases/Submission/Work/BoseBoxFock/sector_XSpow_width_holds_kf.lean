import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.XSpow_aeStronglyMeasurable_ae_bounded
import Submission.Work.BoseBoxFock.aPC_congr_ae_box
import Submission.Work.BoseBoxFock.aPC_finsetSum_ae
import Submission.Work.BoseBoxFock.aPC_slotProj1_absorb
import Submission.Work.BoseBoxFock.aPC_slotProj1_comm_ne
import Submission.Work.BoseBoxFock.sectorXSpowWidth
import Submission.Work.BoseBoxFock.slotExact_finsetSum_ae
import Submission.Work.BoseBoxFock.slotExact_indicator_abox_ae
import Submission.Work.BoseBoxFock.slotProj1_finsetSum_ae
import Submission.Work.BoseBoxFock.xwSlotAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Kf

/-! ## 0. Support and elementary facts -/

/-- `abox n ℓ` is the `n`-fold product of the cube `acube ℓ`. -/
lemma mem_abox_iff' {n : ℕ} {ℓ : ℝ} {x : Fin n → Sp} :
    x ∈ Submission.BoseGases.abox n ℓ ↔ ∀ i : Fin n, x i ∈ Submission.BoseGases.acube ℓ :=
  Iff.rfl

/-- The corpus box `boxL ℓ` is the cube `acube ℓ` (for `ℓ > 0`). -/
lemma boxL_eq_acube'' {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.BoseK15.corpusBox.boxL ℓ = Submission.BoseGases.acube ℓ :=
  boxL_eq_acube_of_pos hℓ

/-- **A state supported in the box has its `i`-slot projection supported in the box.**  Outside
the box at least one slot `k` is outside the cube: if `k = i` the kernel `PV e (x i) ·` vanishes
identically, and if `k ≠ i` the state argument `x[i ↦ w]` keeps the bad coordinate. -/
lemma slotProj1_eq_zero_of_notMem_abox' {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Sp → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {f : (Fin n → Sp) → ℂ}
    (hf0 : ∀ x, x ∉ Submission.BoseGases.abox n ℓ → f x = 0) :
    ∀ x, x ∉ Submission.BoseGases.abox n ℓ → slotProj1 e i f x = 0 := by
  intro x hx
  obtain ⟨k, hk⟩ : ∃ k : Fin n, x k ∉ Submission.BoseGases.acube ℓ := by
    by_contra h
    exact hx (mem_abox_iff'.mpr fun i => by by_contra hi; exact h ⟨i, hi⟩)
  rw [slotProj1]
  have hzero : (fun w : Sp => PV e (x i) w * f (Function.update x i w)) = fun _ => (0 : ℂ) := by
    by_cases hki : k = i
    · funext w
      have hxk : x i ∉ Work.BoseK15.corpusBox.boxL ℓ := by
        rw [boxL_eq_acube'' hℓ]; rwa [← hki]
      rw [PV_apply_eq_zero_of_notMem_boxL hsupp hxk, zero_mul]
    · funext w
      have hk' : k ≠ i := hki
      rw [hf0 _ (fun hmem => hk (by
        have := mem_abox_iff'.mp hmem k
        rwa [Function.update_of_ne hk'] at this)), mul_zero]
  rw [hzero, MeasureTheory.integral_zero]

/-- **A state supported in the box has its `T`-slot projection supported in the box.**  Same
argument as `slotProj1_eq_zero_of_notMem_abox'`: the slot `k` outside the cube is either projected
(the corresponding `PV`-factor of the product kernel vanishes) or kept (the argument of the state
is off the box). -/
lemma slotProj_eq_zero_of_notMem_abox' {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Sp → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : Finset (Fin n)) {f : (Fin n → Sp) → ℂ}
    (hf0 : ∀ x, x ∉ Submission.BoseGases.abox n ℓ → f x = 0) :
    ∀ x, x ∉ Submission.BoseGases.abox n ℓ → slotProj e T f x = 0 := by
  intro x hx
  obtain ⟨k, hk⟩ : ∃ k : Fin n, x k ∉ Submission.BoseGases.acube ℓ := by
    by_contra h
    exact hx (mem_abox_iff'.mpr fun i => by by_contra hi; exact h ⟨i, hi⟩)
  have hxk : x k ∉ Work.BoseK15.corpusBox.boxL ℓ := by rw [boxL_eq_acube'' hℓ]; exact hk
  rw [slotProj]
  have hzero : (fun z : {i : Fin n // i ∈ T} → Sp =>
      (∏ i : {i : Fin n // i ∈ T}, PV e (x i.1) (z i)) *
        f (fun i => if h : i ∈ T then z ⟨i, h⟩ else x i)) = fun _ => (0 : ℂ) := by
    funext z
    by_cases hkT : k ∈ T
    · have hfac : PV e (x k) (z ⟨k, hkT⟩) = 0 :=
        PV_apply_eq_zero_of_notMem_boxL hsupp hxk
      have hprod : (∏ i : {i : Fin n // i ∈ T}, PV e (x i.1) (z i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ (⟨k, hkT⟩ : {i : Fin n // i ∈ T})) hfac
      rw [hprod, zero_mul]
    · have harg : (fun i : Fin n => if h : i ∈ T then z ⟨i, h⟩ else x i) k = x k := by
        simp only [dif_neg hkT]
      rw [hf0 _ (fun hmem => hk (by rw [← harg]; exact mem_abox_iff'.mp hmem k)), mul_zero]
  rw [hzero, MeasureTheory.integral_zero]

/-- `slotProj1 e i` is `ℂ`-homogeneous in its state (pointwise, hence a.e.). -/
lemma slotProj1_smul_eq {m n : ℕ} {e : Fin m → Sp → ℂ} (i : Fin n) (c : ℂ)
    (f : (Fin n → Sp) → ℂ) :
    slotProj1 e i (fun y => c • f y) = fun x => c • slotProj1 e i f x := by
  funext x
  rw [slotProj1, slotProj1]
  rw [show (fun w : Sp => PV e (x i) w * (c • f (Function.update x i w)))
      = fun w : Sp => c * (PV e (x i) w * f (Function.update x i w)) from by
    funext w; simp only [smul_eq_mul]; ring]
  rw [MeasureTheory.integral_const_mul, smul_eq_mul]

/-- `slotProj e T` maps `L^∞` states to `L^∞` states. -/
lemma slotProj_memLp_top' {m n : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : Finset (Fin n)) {f : (Fin n → Sp) → ℂ} (hf : MemLp f ⊤) :
    MemLp (slotProj e T f) ⊤ := by
  obtain ⟨C, hC⟩ := slotProj_ae_bounded (ℓ := ℓ) hbdd hsupp T hf
  exact memLp_top_of_bound (slotProj_aesm (fun l => (hbdd l).aestronglyMeasurable) T
    hf.aestronglyMeasurable) C hC

/-! ## 1. The restricted sectors `sectR` -/

/-- **The `S`-sector restricted to the slot set `R`**: the inclusion–exclusion sum over the
supersets `T` of `S` that are contained in `R`.  For `R = univ` this is exactly `slotExact e S`
(`sectR_univ`). -/
def sectR {m n : ℕ} (e : Fin m → Sp → ℂ) (S R : Finset (Fin n)) (Φ : (Fin n → Sp) → ℂ) :
    (Fin n → Sp) → ℂ :=
  ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ T ⊆ R),
    (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Φ

/-- `sectR e S R` for `R = univ` is `slotExact e S`. -/
lemma sectR_univ {m n : ℕ} (e : Fin m → Sp → ℂ) (S : Finset (Fin n))
    (Φ : (Fin n → Sp) → ℂ) : sectR e S Finset.univ Φ = slotExact e S Φ := by
  classical
  unfold sectR slotExact
  refine Finset.sum_congr ?_ (fun T _ => rfl)
  ext T
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, Finset.subset_univ T⟩⟩

/-- The empty restricted sector of the empty slot set is the identity. -/
lemma sectR_empty_empty {m n : ℕ} (e : Fin m → Sp → ℂ) (f : (Fin n → Sp) → ℂ) :
    sectR e (∅ : Finset (Fin n)) (∅ : Finset (Fin n)) f = f := by
  classical
  funext x
  rw [sectR, Finset.sum_apply]
  rw [show Finset.univ.filter (fun T : Finset (Fin n) =>
      (∅ : Finset (Fin n)) ⊆ T ∧ T ⊆ (∅ : Finset (Fin n))) = {∅} from by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => Finset.subset_empty.mp h.2, fun h => by rw [h]; simp⟩]
  rw [Finset.sum_singleton]
  have hproj : slotProj e (∅ : Finset (Fin n)) f = f := by
    funext y
    rw [slotProj_eq_slotInt_fun]
    exact congrFun (slotInt_empty e f) y
  rw [Pi.smul_apply, hproj]
  norm_num

/-- `sectR e S R` is `L^∞` when the state is. -/
lemma sectR_memLp_top {m n : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S R : Finset (Fin n)) {f : (Fin n → Sp) → ℂ} (hf : MemLp f ⊤) :
    MemLp (sectR e S R f) ⊤ := by
  classical
  have haesm : AEStronglyMeasurable (sectR e S R f) (volume : Measure (Fin n → Sp)) := by
    unfold sectR
    exact Finset.aestronglyMeasurable_sum _
      (fun T _ => (slotProj_memLp_top' (ℓ := ℓ) hbdd hsupp T hf).aestronglyMeasurable.const_smul _)
  choose C hC using fun T : Finset (Fin n) => slotProj_ae_bounded (ℓ := ℓ) hbdd hsupp T hf
  refine memLp_top_of_bound haesm
    (∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ T ⊆ R),
      ‖(-1 : ℂ) ^ (T.card - S.card)‖ * max (C T) 0) ?_
  have hall : ∀ᵐ x ∂(volume : Measure (Fin n → Sp)),
      ∀ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ T ⊆ R),
        ‖slotProj e T f x‖ ≤ max (C T) 0 := by
    rw [Finset.eventually_all]
    intro T _
    filter_upwards [hC T] with x hx
    exact hx.trans (le_max_left _ _)
  filter_upwards [hall] with x hx
  calc ‖sectR e S R f x‖
      = ‖∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ T ⊆ R),
          (-1 : ℂ) ^ (T.card - S.card) • slotProj e T f x‖ := by
        simp only [sectR, Finset.sum_apply, Pi.smul_apply]
    _ ≤ ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ T ⊆ R),
          ‖(-1 : ℂ) ^ (T.card - S.card) • slotProj e T f x‖ := norm_sum_le _ _
    _ ≤ ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ T ⊆ R),
          ‖(-1 : ℂ) ^ (T.card - S.card)‖ * max (C T) 0 := by
        refine Finset.sum_le_sum fun T hT => ?_
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hx T hT) (norm_nonneg _)

/-- If a state vanishes off the box, then so does every restricted sector of it. -/
lemma sectR_eq_zero_of_notMem_abox {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Sp → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S R : Finset (Fin n)) {f : (Fin n → Sp) → ℂ}
    (hf0 : ∀ x, x ∉ Submission.BoseGases.abox n ℓ → f x = 0) :
    ∀ x, x ∉ Submission.BoseGases.abox n ℓ → sectR e S R f x = 0 := by
  classical
  intro x hx
  rw [sectR, Finset.sum_apply]
  exact Finset.sum_eq_zero fun T _ => by
    rw [Pi.smul_apply, slotProj_eq_zero_of_notMem_abox' (ℓ := ℓ) hℓ hsupp T hf0 x hx, smul_zero]

/-! ## 2. The composition law: the single-slot projection slides out of `slotProj` -/

/-- **The composition law.**  If `i ∉ V`, the single-slot projection at `i` can be composed with
`slotProj e V` from the inside:
`slotProj e V (slotProj1 e i Ψ) =ᵐ slotProj e (insert i V) Ψ`.

This is the componentwise form of "`slotProj e V` is the product of the `slotProj1 e i`, `i ∈ V`",
obtained from the iterated peel `slotProj_peel_ae`. -/
lemma slotProj_slotProj1_eq {m n : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hℓ : 0 < ℓ)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (V : Finset (Fin n)) {i : Fin n} (hiV : i ∉ V) {f : (Fin n → Sp) → ℂ} (hf : MemLp f ⊤) :
    (fun x => slotProj e V (slotProj1 e i f) x)
      =ᵐ[(volume : Measure (Fin n → Sp))] (fun x => slotProj e (insert i V) f x) := by
  have hQmem : MemLp (slotProj1 e i f) ⊤ := slotProj1_memLp_top (ℓ := ℓ) hℓ hbdd hsupp i hf
  have hkey : ∀ V : Finset (Fin n), i ∉ V →
      (fun x => slotProj e V (slotProj1 e i f) x)
        =ᵐ[(volume : Measure (Fin n → Sp))] (fun x => slotProj e (insert i V) f x) := by
    intro V
    induction V using Finset.induction_on with
    | empty =>
        intro _
        have h1 : (fun x => slotProj e (∅ : Finset (Fin n)) (slotProj1 e i f) x)
            = slotProj1 e i f := by
          funext y
          rw [slotProj_eq_slotInt_fun]
          exact congrFun (slotInt_empty e (slotProj1 e i f)) y
        have h2 : (fun x => slotProj e (insert i (∅ : Finset (Fin n))) f x)
            =ᵐ[(volume : Measure (Fin n → Sp))] slotProj1 e i f := by
          have hp := slotProj_peel_ae hbdd hsupp (U := (∅ : Finset (Fin n))) (i := i) (by simp) hf
          have h3 : slotProj e (∅ : Finset (Fin n)) f = f := by
            funext y
            rw [slotProj_eq_slotInt_fun]
            exact congrFun (slotInt_empty e f) y
          rw [h3] at hp
          simpa using hp
        rw [h1]
        exact h2.symm
    | insert u V' hu ih =>
        intro hiV
        have hiV' : i ∉ V' := fun h => hiV (Finset.mem_insert_of_mem h)
        have hiu : i ≠ u := fun h => hiV (h ▸ Finset.mem_insert_self u V')
        have hui : u ∉ insert i V' := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun h => hiu h.symm, hu⟩
        have hpeelL := slotProj_peel_ae hbdd hsupp (U := V') (i := u) hu hQmem
        have hpeelR := slotProj_peel_ae hbdd hsupp (U := insert i V') (i := u) hui hf
        have hIH := ih hiV'
        have htrans : (fun x => slotProj1 e u (slotProj e V' (slotProj1 e i f)) x)
            =ᵐ[(volume : Measure (Fin n → Sp))]
            (fun x => slotProj1 e u (slotProj e (insert i V') f) x) :=
          slotProj1_ae_eq_congr_aux e u hIH
        have hset : insert u (insert i V') = insert i (insert u V') :=
          Finset.insert_comm u i V'
        rw [hset] at hpeelR
        exact hpeelL.trans (htrans.trans hpeelR.symm)
  exact hkey V hiV

/-! ## 3. The two recursion identities of the restricted sectors -/

/-- **The `i ∉ S` recursion.**  For `i ∈ R` and `i ∉ S`, the sector `sectR e S R` is obtained from
the sector at `R \ {i}` by `1 − Q_i`.  Both sides are the same inclusion–exclusion sum: the
supersets of `S` in `R` split into those avoiding `i` (which are exactly the supersets of `S` in
`R \ {i}`, giving the `sectR e S (R \ {i})` part) and those containing `i` (which are the
`insert i T`, `T` running over the supersets of `S` in `R \ {i}`, with the opposite sign). -/
lemma sectR_rec_notMem {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {S R : Finset (Fin n)} {i : Fin n} (hiR : i ∈ R) (hiS : i ∉ S)
    {f : (Fin n → Sp) → ℂ} (hf : MemLp f ⊤) :
    sectR e S R f =ᵐ[(volume : Measure (Fin n → Sp)).restrict (Submission.BoseGases.abox n ℓ)]
      fun x => sectR e S (R.erase i) f x - slotProj1 e i (sectR e S (R.erase i) f) x := by
  classical
  set s : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ T ⊆ R.erase i) with hsdef
  have hsmem : ∀ T : Finset (Fin n), T ∈ s ↔ S ⊆ T ∧ T ⊆ R.erase i := by
    intro T; rw [hsdef]; simp
  have hsub_s : ∀ T ∈ s, T ⊆ R.erase i := fun T hT => ((hsmem T).mp hT).2
  have hSU_s : ∀ T ∈ s, S ⊆ T := fun T hT => ((hsmem T).mp hT).1
  have hnotmem_s : ∀ T ∈ s, i ∉ T := fun T hT h => Finset.notMem_erase i R (hsub_s T hT h)
  have hP : Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ T ⊆ R)
      = s ∪ s.image (insert i) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image,
      hsmem]
    constructor
    · rintro ⟨hST, hTR⟩
      by_cases hiT : i ∈ T
      · refine Or.inr ⟨T.erase i, ⟨?_, ?_⟩, Finset.insert_erase hiT⟩
        · exact Finset.subset_erase.mpr ⟨hST, hiS⟩
        · exact Finset.subset_erase.mpr ⟨(Finset.erase_subset i T).trans hTR,
            Finset.notMem_erase i T⟩
      · exact Or.inl ⟨hST, Finset.subset_erase.mpr ⟨hTR, hiT⟩⟩
    · rintro (⟨hST, hTR⟩ | ⟨T', ⟨hST', hT'R⟩, rfl⟩)
      · exact ⟨hST, hTR.trans (Finset.erase_subset i R)⟩
      · refine ⟨hST'.trans (Finset.subset_insert i T'), ?_⟩
        exact Finset.insert_subset hiR (hT'R.trans (Finset.erase_subset i R))
  have hdisj : Disjoint s (s.image (insert i)) := by
    refine Finset.disjoint_left.mpr fun T hTs hTim => ?_
    obtain ⟨T', hT's, hT'eq⟩ := Finset.mem_image.mp hTim
    exact hnotmem_s T hTs (hT'eq ▸ Finset.mem_insert_self i T')
  have hinj : ∀ x ∈ s, ∀ y ∈ s, insert i x = insert i y → x = y := by
    intro x hx y hy hxy
    have hx' : i ∉ x := hnotmem_s x hx
    have hy' : i ∉ y := hnotmem_s y hy
    have := congrArg (fun (U : Finset (Fin n)) => U.erase i) hxy
    rwa [Finset.erase_insert hx', Finset.erase_insert hy'] at this
  have hsign : ∀ T ∈ s, (-1 : ℂ) ^ ((insert i T).card - S.card)
      = -((-1 : ℂ) ^ (T.card - S.card)) := by
    intro T hT
    have hiT : i ∉ T := hnotmem_s T hT
    have hcard : (insert i T).card = T.card + 1 := Finset.card_insert_of_notMem hiT
    have hle : S.card ≤ T.card := Finset.card_le_card (hSU_s T hT)
    have hexp : (insert i T).card - S.card = (T.card - S.card) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  have hsplit : ∀ y, sectR e S R f y
      = ∑ T ∈ s, ((-1 : ℂ) ^ (T.card - S.card) • slotProj e T f y
          + (-1 : ℂ) ^ ((insert i T).card - S.card) • slotProj e (insert i T) f y) := by
    intro y
    have h1 : sectR e S R f y
        = ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) • slotProj e T f y
          + ∑ T ∈ s, (-1 : ℂ) ^ ((insert i T).card - S.card) •
              slotProj e (insert i T) f y := by
      rw [sectR, Finset.sum_apply, hP, Finset.sum_union hdisj, Finset.sum_image hinj]
      simp only [Pi.smul_apply]
    rw [h1, ← Finset.sum_add_distrib]
  have hsectpt : ∀ y, sectR e S (R.erase i) f y
      = ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) • slotProj e T f y := by
    intro y
    rw [sectR, Finset.sum_apply, ← hsdef]
    simp only [Pi.smul_apply]
  have hΘmem : ∀ T ∈ s, MemLp
      (fun y => (-1 : ℂ) ^ (T.card - S.card) • slotProj e T f y) ⊤ := fun T _ =>
    (slotProj_memLp_top' (ℓ := ℓ) hbdd hsupp T hf).const_smul
      ((-1 : ℂ) ^ (T.card - S.card))
  have hsectfun : sectR e S (R.erase i) f
      = fun y => ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) • slotProj e T f y :=
    funext hsectpt
  have hlin := slotProj1_finsetSum_ae (ℓ := ℓ) hℓ hbdd hsupp i s hΘmem
  have hcomp : ∀ᵐ x ∂(volume : Measure (Fin n → Sp)),
      ∀ T ∈ s, slotProj1 e i
          (fun y => (-1 : ℂ) ^ (T.card - S.card) • slotProj e T f y) x
        = (-1 : ℂ) ^ (T.card - S.card) • slotProj e (insert i T) f x := by
    rw [Finset.eventually_all]
    intro T hT
    have hiT : i ∉ T := hnotmem_s T hT
    have hp := slotProj_peel_ae hbdd hsupp (U := T) (i := i) hiT hf
    filter_upwards [hp] with x hx
    rw [slotProj1_smul_eq]
    exact congrArg (fun z => (-1 : ℂ) ^ (T.card - S.card) • z) hx.symm
  have hmain : ∀ᵐ x ∂((volume : Measure (Fin n → Sp)).restrict (Submission.BoseGases.abox n ℓ)),
      slotProj1 e i (sectR e S (R.erase i) f) x
        = ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) • slotProj e (insert i T) f x := by
    rw [hsectfun]
    filter_upwards [hlin, ae_mono Measure.restrict_le_self hcomp] with x hx hxall
    rw [hx]
    exact Finset.sum_congr rfl fun T hT => hxall T hT
  filter_upwards [hmain] with x hx
  rw [hsplit x, hsectpt x, hx, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [hsign T hT, neg_smul, sub_eq_add_neg]

/-- **The `i ∈ S` recursion.**  For `i ∈ S` (and `S ⊆ R`), the sector `sectR e S R` is the
`sectR e (S \ {i}) (R \ {i})`-sector followed by `Q_i`: the supersets of `S` in `R` are exactly
the `insert i V` with `V` a superset of `S \ {i}` in `R \ {i}`, and the coefficients agree. -/
lemma sectR_rec_mem {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {S R : Finset (Fin n)} {i : Fin n} (hiS : i ∈ S) (hSR : S ⊆ R)
    {f : (Fin n → Sp) → ℂ} (hf : MemLp f ⊤) :
    sectR e S R f =ᵐ[(volume : Measure (Fin n → Sp)).restrict (Submission.BoseGases.abox n ℓ)]
      fun x => slotProj1 e i (sectR e (S.erase i) (R.erase i) f) x := by
  classical
  set s : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ T ⊆ R) with hsdef
  set s' : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun V : Finset (Fin n) => S.erase i ⊆ V ∧ V ⊆ R.erase i) with hs'def
  have hsmem : ∀ T : Finset (Fin n), T ∈ s ↔ S ⊆ T ∧ T ⊆ R := by
    intro T; rw [hsdef]; simp
  have hsmem' : ∀ V : Finset (Fin n), V ∈ s' ↔ S.erase i ⊆ V ∧ V ⊆ R.erase i := by
    intro V; rw [hs'def]; simp
  have hnotmem : ∀ V ∈ s', i ∉ V := fun V hV h =>
    Finset.notMem_erase i R (((hsmem' V).mp hV).2 h)
  have hiR : i ∈ R := hSR hiS
  -- the index bijection
  have hP : s = s'.image (insert i) := by
    ext T
    rw [hsmem T, Finset.mem_image]
    constructor
    · rintro ⟨hST, hTR⟩
      refine ⟨T.erase i, (hsmem' (T.erase i)).mpr ⟨?_, ?_⟩, Finset.insert_erase (hST hiS)⟩
      · exact Finset.subset_erase.mpr
          ⟨(Finset.erase_subset i S).trans hST, Finset.notMem_erase i S⟩
      · exact Finset.subset_erase.mpr ⟨(Finset.erase_subset i T).trans hTR,
          Finset.notMem_erase i T⟩
    · rintro ⟨V, hV, rfl⟩
      refine ⟨fun k hk => by
        by_cases hki : k = i
        · rw [hki]; exact Finset.mem_insert_self i V
        · exact Finset.mem_insert_of_mem
            (((hsmem' V).mp hV).1 (Finset.mem_erase.mpr ⟨hki, hk⟩)),
        Finset.insert_subset hiR ((((hsmem' V).mp hV).2).trans (Finset.erase_subset i R))⟩
  have hinj : ∀ x ∈ s', ∀ y ∈ s', insert i x = insert i y → x = y := by
    intro x hx y hy hxy
    have hx' : i ∉ x := hnotmem x hx
    have hy' : i ∉ y := hnotmem y hy
    have := congrArg (fun (U : Finset (Fin n)) => U.erase i) hxy
    rwa [Finset.erase_insert hx', Finset.erase_insert hy'] at this
  -- the coefficients agree
  have hcoeff : ∀ V ∈ s', (-1 : ℂ) ^ ((insert i V).card - S.card)
      = (-1 : ℂ) ^ (V.card - (S.erase i).card) := by
    intro V hV
    have hiV : i ∉ V := hnotmem V hV
    have hcard : (insert i V).card = V.card + 1 := Finset.card_insert_of_notMem hiV
    have hcardS : (S.erase i).card = S.card - 1 := Finset.card_erase_of_mem hiS
    have hcard_le : (S.erase i).card ≤ V.card :=
      Finset.card_le_card (((hsmem' V).mp hV).1)
    have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hiS⟩
    have hexp : (insert i V).card - S.card = V.card - (S.erase i).card := by omega
    rw [hexp]
  -- the sector at `R` as a sum over `s'`
  have hsplit : ∀ y, sectR e S R f y
      = ∑ V ∈ s', (-1 : ℂ) ^ (V.card - (S.erase i).card) •
          slotProj e (insert i V) f y := by
    intro y
    rw [sectR, Finset.sum_apply, ← hsdef, hP, Finset.sum_image hinj]
    simp only [Pi.smul_apply]
    exact Finset.sum_congr rfl fun V hV => by rw [hcoeff V hV]
  -- the sector at `R.erase i` as a sum over `s'`
  have hsectpt : ∀ y, sectR e (S.erase i) (R.erase i) f y
      = ∑ V ∈ s', (-1 : ℂ) ^ (V.card - (S.erase i).card) • slotProj e V f y := by
    intro y
    rw [sectR, Finset.sum_apply, ← hs'def]
    simp only [Pi.smul_apply]
  have hΘmem : ∀ V ∈ s', MemLp
      (fun y => (-1 : ℂ) ^ (V.card - (S.erase i).card) • slotProj e V f y) ⊤ := fun V _ =>
    (slotProj_memLp_top' (ℓ := ℓ) hbdd hsupp V hf).const_smul
      ((-1 : ℂ) ^ (V.card - (S.erase i).card))
  have hlin := slotProj1_finsetSum_ae (ℓ := ℓ) hℓ hbdd hsupp i s' hΘmem
  have hsectfun : sectR e (S.erase i) (R.erase i) f
      = fun y => ∑ V ∈ s', (-1 : ℂ) ^ (V.card - (S.erase i).card) • slotProj e V f y :=
    funext hsectpt
  have hcomp : ∀ᵐ x ∂(volume : Measure (Fin n → Sp)),
      ∀ V ∈ s', slotProj1 e i
          (fun y => (-1 : ℂ) ^ (V.card - (S.erase i).card) • slotProj e V f y) x
        = (-1 : ℂ) ^ (V.card - (S.erase i).card) • slotProj e (insert i V) f x := by
    rw [Finset.eventually_all]
    intro V hV
    have hiV : i ∉ V := hnotmem V hV
    have hp := slotProj_peel_ae hbdd hsupp (U := V) (i := i) hiV hf
    filter_upwards [hp] with x hx
    rw [slotProj1_smul_eq]
    exact congrArg (fun z => (-1 : ℂ) ^ (V.card - (S.erase i).card) • z) hx.symm
  have hmain : ∀ᵐ x ∂((volume : Measure (Fin n → Sp)).restrict (Submission.BoseGases.abox n ℓ)),
      slotProj1 e i (sectR e (S.erase i) (R.erase i) f) x
        = ∑ V ∈ s', (-1 : ℂ) ^ (V.card - (S.erase i).card) • slotProj e (insert i V) f x := by
    rw [hsectfun]
    filter_upwards [hlin, ae_mono Measure.restrict_le_self hcomp] with x hx hxall
    rw [hx]
    exact Finset.sum_congr rfl fun V hV => hxall V hV
  filter_upwards [hmain] with x hx
  rw [hsplit x, hx]

/-! ## 4. The contraction of the restricted sectors -/

/-- **The contraction of the restricted sectors**: `∫_{abox} ‖sectR e S R f‖² ≤ ∫_{abox} ‖f‖²`
for states supported in the box, by induction on `R` on the two single-slot contractions
(`Q_i` and `1 − Q_i`) applied through the recursions `sectR_rec_notMem`/`sectR_rec_mem`. -/
lemma sectR_contract {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    ∀ (S R : Finset (Fin n)), S ⊆ R → ∀ {f : (Fin n → Sp) → ℂ}, MemLp f ⊤ →
      (∀ x, x ∉ Submission.BoseGases.abox n ℓ → f x = 0) →
      (∫ x in Submission.BoseGases.abox n ℓ, ‖sectR e S R f x‖ ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox n ℓ, ‖f x‖ ^ 2 := by
  have key : ∀ R : Finset (Fin n), ∀ S : Finset (Fin n), S ⊆ R →
      ∀ {f : (Fin n → Sp) → ℂ}, MemLp f ⊤ →
      (∀ x, x ∉ Submission.BoseGases.abox n ℓ → f x = 0) →
      (∫ x in Submission.BoseGases.abox n ℓ, ‖sectR e S R f x‖ ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox n ℓ, ‖f x‖ ^ 2 := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
        intro S hS f hf hf0
        have hS0 : S = ∅ := Finset.subset_empty.mp hS
        rw [hS0]
        exact le_of_eq (by rw [sectR_empty_empty])
    | insert a R' ha ih =>
        intro S hSR f hf hf0
        have herase : (insert a R').erase a = R' := Finset.erase_insert ha
        have hmem : MemLp (sectR e S R' f) ⊤ := sectR_memLp_top (ℓ := ℓ) hbdd hsupp S R' hf
        have hzero : ∀ x, x ∉ Submission.BoseGases.abox n ℓ → sectR e S R' f x = 0 :=
          sectR_eq_zero_of_notMem_abox (ℓ := ℓ) hℓ hsupp S R' hf0
        by_cases haS : a ∈ S
        · -- `a ∈ S`: apply `Q_a` to the smaller sector
          have hS' : S.erase a ⊆ R' := fun k hk => by
            rw [Finset.mem_erase] at hk
            have hkS : k ∈ S := hk.2
            have hka : k ≠ a := hk.1
            rcases Finset.mem_insert.mp (hSR hkS) with h | h
            · exact absurd h hka
            · exact h
          have hrec := sectR_rec_mem (ℓ := ℓ) hℓ hbdd hsupp (R := insert a R') (i := a) haS hSR hf
          rw [herase] at hrec
          have hmem' : MemLp (sectR e (S.erase a) R' f) ⊤ :=
            sectR_memLp_top (ℓ := ℓ) hbdd hsupp (S.erase a) R' hf
          have hzero' : ∀ x, x ∉ Submission.BoseGases.abox n ℓ →
              sectR e (S.erase a) R' f x = 0 :=
            sectR_eq_zero_of_notMem_abox (ℓ := ℓ) hℓ hsupp (S.erase a) R' hf0
          have hIH := ih (S.erase a) hS' (f := f) hf hf0
          have h1 : (∫ x in Submission.BoseGases.abox n ℓ, ‖sectR e S (insert a R') f x‖ ^ 2)
              = ∫ x in Submission.BoseGases.abox n ℓ,
                  ‖slotProj1 e a (sectR e (S.erase a) R' f) x‖ ^ 2 := by
            refine integral_congr_ae ?_
            filter_upwards [hrec] with x hx
            rw [hx]
          rw [h1]
          exact (XwSlot.slotProj1_contract_box' (ℓ := ℓ) hℓ he hbdd hsupp a hmem' hzero').trans hIH
        · -- `a ∉ S`: apply `1 − Q_a`
          have hS' : S ⊆ R' := fun k hk => by
            rcases Finset.mem_insert.mp (hSR hk) with h | h
            · exact absurd (h ▸ hk) haS
            · exact h
          have hrec := sectR_rec_notMem (ℓ := ℓ) hℓ hbdd hsupp
            (R := insert a R') (i := a) (Finset.mem_insert_self a R') haS hf
          rw [herase] at hrec
          have hIH := ih S hS' (f := f) hf hf0
          have h1 : (∫ x in Submission.BoseGases.abox n ℓ, ‖sectR e S (insert a R') f x‖ ^ 2)
              = ∫ x in Submission.BoseGases.abox n ℓ,
                  ‖sectR e S R' f x - slotProj1 e a (sectR e S R' f) x‖ ^ 2 := by
            refine integral_congr_ae ?_
            filter_upwards [hrec] with x hx
            rw [hx]
          rw [h1]
          exact (XwSlot.slotProj1_oneSub_contract_box (ℓ := ℓ) hℓ he hbdd hsupp a hmem hzero).trans hIH
  intro S R hSR f hf hf0
  exact key R S hSR hf hf0

/-! ## 5. The contraction of the sector, and the target -/

/-- **The sector projection is an `L²`-contraction over the box**, for an arbitrary `L^∞` state:
multiplying the state by the indicator of the box does not change the sector on the box
(`slotExact_indicator_abox_ae`), and the box-supported case is `sectR_contract` at `R = univ`. -/
lemma slotExact_contract_box {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Ψ : (Fin n → Sp) → ℂ} (hΨ : MemLp Ψ ⊤) :
    (∫ x in Submission.BoseGases.abox n ℓ, ‖slotExact e S Ψ x‖ ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, ‖Ψ x‖ ^ 2 := by
  set Ψb : (Fin n → Sp) → ℂ := (Submission.BoseGases.abox n ℓ).indicator Ψ with hΨbdef
  have hΨbmem : MemLp Ψb ⊤ := hΨ.indicator (Submission.BoseGases.abox_measurable n ℓ)
  have hΨb0 : ∀ x, x ∉ Submission.BoseGases.abox n ℓ → Ψb x = 0 :=
    fun x hx => Set.indicator_of_notMem hx Ψ
  have h1 : (∫ x in Submission.BoseGases.abox n ℓ, ‖slotExact e S Ψ x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, ‖slotExact e S Ψb x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [slotExact_indicator_abox_ae (ℓ := ℓ) hℓ hsupp S hΨ] with x hx
    rw [hx]
  rw [h1, ← sectR_univ e S Ψb]
  refine (sectR_contract (ℓ := ℓ) hℓ he hbdd hsupp S Finset.univ (Finset.subset_univ S)
    hΨbmem hΨb0).trans ?_
  refine le_of_eq ?_
  refine integral_congr_ae ?_
  filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)] with x hx
  rw [hΨbdef, Set.indicator_of_mem hx]

/-! ## 6. The commutation of the slot mean with the sector projection, knot-free

The atoms of `FINDING_sector_XSpow_le_s11.md` §3 are all in this cone:

* **M1** `slotProj1_aPC_absorb_self` : `Qᵢ ∘ Aᵢ =ᵐ[box] Aᵢ`;
* **M2** `aPC_slotProj1_absorb`      : `Aᵢ ∘ Qᵢ =ᵐ[volume] Aᵢ` — *full* volume;
* **E**  `aPC_slotProj1_comm_ne`     : `Aᵢ ∘ Qⱼ =ᵐ[volume] Qⱼ ∘ Aᵢ` for `i ≠ j` — *full* volume;
* **PEEL** `slotProj_peel_ae`        : `slotProj e (insert i U) =ᵐ[volume] Qᵢ ∘ slotProj e U`.

The point that makes the assembly work is that **M2 and E are full-volume statements**: pushing
`Aᵢ` through a slot projection at its own slot *erases* that slot, and the induction on the slot
set can therefore be carried out entirely for the full Lebesgue measure (`aPC_slotProj_erase`).
The erased projection is restored on the box by M1 (`aPC_slotProj_comm_box`), the Möbius sum
(`aPC_finsetSum_ae`, `slotExact_finsetSum_ae`) upgrades it to `slotExact`
(`aPC_slotExact_comm_box`), and the induction on `j` (as in `XSpow_slotExact_comm.lean`) gives
the iterated form (`XSpow_slotExact_comm_box`), which is the input **(comm)** of
`sector_XSpow_width`.

Import note.  The two single-slot contractions are taken from `xwSlotAux` (the *proved*
`XwSlot.slotProj1_contract_box'` and `XwSlot.slotProj1_oneSub_contract_box`) rather than from the
`sorry`-stubs `slotProj1_contract_box.lean` / `slotProj1_oneSub_contract_box.lean`, so that the
axiom footprint of the target theorem stays `[propext, Classical.choice, Quot.sound]`. -/

/-- **Full-volume congruence of the slot mean**, general `N`. -/
theorem ae_aPC_congr_vol_gen {N : ℕ} {ℓ : ℝ} (i : Fin N) {f g : (Fin N → Sp) → ℂ}
    (h : f =ᵐ[(volume : Measure (Fin N → Sp))] g) :
    aPC ℓ i f =ᵐ[(volume : Measure (Fin N → Sp))] aPC ℓ i g := by
  cases N with
  | zero => exact i.elim0
  | succ k => exact ae_aPC_congr_vol (ℓ := ℓ) i h

/-- **Box-relative congruence of the slot mean**, general `N`. -/
theorem aPC_congr_ae_abox {N : ℕ} {ℓ : ℝ} (i : Fin N) {f g : (Fin N → Sp) → ℂ}
    (h : f =ᵐ[(volume : Measure (Fin N → Sp)).restrict (Submission.BoseGases.abox N ℓ)] g) :
    aPC ℓ i f =ᵐ[(volume : Measure (Fin N → Sp)).restrict (Submission.BoseGases.abox N ℓ)]
      aPC ℓ i g := by
  cases N with
  | zero => exact i.elim0
  | succ k => exact aPC_congr_ae_box (ℓ := ℓ) i h

/-- **The box measure is subordinate to the full volume**: an a.e. statement for the full
Lebesgue measure is an a.e. statement on the box. -/
theorem eventuallyEq_restrict_box {N : ℕ} {ℓ : ℝ} {f g : (Fin N → Sp) → ℂ}
    (h : f =ᵐ[(volume : Measure (Fin N → Sp))] g) :
    f =ᵐ[(volume : Measure (Fin N → Sp)).restrict (Submission.BoseGases.abox N ℓ)] g :=
  ae_mono Measure.restrict_le_self h

/-- **`aPC ℓ i` is `ℂ`-homogeneous in its state** (unfolding the slot mean and pulling the
constant out of the Bochner integral). -/
theorem aPC_const_smul (ℓ : ℝ) {N : ℕ} (i : Fin N) (c : ℂ) (Ψ : (Fin N → Sp) → ℂ)
    (x : Fin N → Sp) : aPC ℓ i (fun y => c • Ψ y) x = c • aPC ℓ i Ψ x := by
  have h1 : aPC ℓ i (fun y => c • Ψ y) x
      = ((1 / ℓ ^ 3 : ℝ) : ℂ)
        * (c * ∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update x i y)) := by
    simp only [aPC, smul_eq_mul, MeasureTheory.integral_const_mul]
  have h2 : aPC ℓ i Ψ x
      = ((1 / ℓ ^ 3 : ℝ) : ℂ)
        * ∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update x i y) := rfl
  rw [h1, h2, smul_eq_mul]
  ring

/-- The slot mean of an `L^∞` state is `L^∞`. -/
lemma aPC_memLp_top {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Ψ : (Fin N → Sp) → ℂ}
    (hΨ : MemLp Ψ ⊤) : MemLp (aPC ℓ i Ψ) ⊤ := by
  obtain ⟨C, hC0, hCb⟩ := exists_ae_bound_of_memLp_top_aux hΨ
  exact memLp_top_of_bound (aPC_aesm_full ℓ i hΨ.aestronglyMeasurable) C
    (aPC_ae_bound_full ℓ hℓ i hC0 hCb)

/-- **The slot mean commutes with a slot projection by erasing the projected slot** (full
Lebesgue measure, no box restriction): commuting `aPC ℓ i` past the slot projection at `i` absorbs
that projection (M2), and past a projection at a different slot it commutes (E), so the induction
over the slot set is an induction over the full measure. -/
theorem aPC_slotProj_erase {m N : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : Measure Sp), e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (i : Fin N) (U : Finset (Fin N)) {Ψ : (Fin N → Sp) → ℂ} (hΨ : MemLp Ψ ⊤) :
    (fun x => aPC ℓ i (slotProj e U Ψ) x)
      =ᵐ[(volume : Measure (Fin N → Sp))]
      (fun x => slotProj e (U.erase i) (aPC ℓ i Ψ) x) := by
  classical
  induction U using Finset.induction_on with
  | empty =>
      have h1 : (fun x => aPC ℓ i (slotProj e (∅ : Finset (Fin N)) Ψ) x)
          = fun x => aPC ℓ i Ψ x := by
        rw [slotProj_eq_slotInt_fun, slotInt_empty e Ψ]
      have h2 : (fun x => slotProj e (∅ : Finset (Fin N)) (aPC ℓ i Ψ) x)
          = fun x => aPC ℓ i Ψ x := by
        rw [slotProj_eq_slotInt_fun, slotInt_empty e (aPC ℓ i Ψ)]
      rw [Finset.erase_empty]
      exact (Filter.EventuallyEq.of_eq h1).trans (Filter.EventuallyEq.of_eq h2).symm
  | insert j U' hj ih =>
      have hX : MemLp (slotProj e U' Ψ) ⊤ := slotProj_memLp_top' hbdd hsupp U' hΨ
      have h1 : (fun x => aPC ℓ i (slotProj e (insert j U') Ψ) x)
          =ᵐ[(volume : Measure (Fin N → Sp))]
          (fun x => aPC ℓ i (slotProj1 e j (slotProj e U' Ψ)) x) :=
        ae_aPC_congr_vol_gen i
          (slotProj_peel_ae (ℓ := ℓ) hbdd hsupp (U := U') (i := j) hj hΨ)
      by_cases hji : j = i
      · -- the projected slot is the slot of the mean: it is absorbed
        have h2 : (fun x => aPC ℓ i (slotProj1 e j (slotProj e U' Ψ)) x)
            =ᵐ[(volume : Measure (Fin N → Sp))]
            (fun x => aPC ℓ i (slotProj e U' Ψ) x) := by
          rw [hji]
          exact aPC_slotProj1_absorb ℓ hℓ he hbdd hsupp hc i hX
        have hj' : i ∉ U' := fun h => hj (hji ▸ h)
        have hset : (insert j U').erase i = U'.erase i := by
          rw [hji, Finset.erase_insert hj', Finset.erase_eq_of_notMem hj']
        simpa only [hset] using h1.trans (h2.trans ih)
      · -- the projected slot is a different slot: the two commute
        have hij : j ≠ i := hji
        have h2 : (fun x => aPC ℓ i (slotProj1 e j (slotProj e U' Ψ)) x)
            =ᵐ[(volume : Measure (Fin N → Sp))]
            (fun x => slotProj1 e j (aPC ℓ i (slotProj e U' Ψ)) x) :=
          aPC_slotProj1_comm_ne ℓ hℓ he hbdd hsupp (Ne.symm hij) hX
        have h3 : (fun x => slotProj1 e j (aPC ℓ i (slotProj e U' Ψ)) x)
            =ᵐ[(volume : Measure (Fin N → Sp))]
            (fun x => slotProj1 e j (slotProj e (U'.erase i) (aPC ℓ i Ψ)) x) :=
          slotProj1_ae_eq_congr_aux e j ih
        have h4 : (fun x => slotProj1 e j (slotProj e (U'.erase i) (aPC ℓ i Ψ)) x)
            =ᵐ[(volume : Measure (Fin N → Sp))]
            (fun x => slotProj e (insert j (U'.erase i)) (aPC ℓ i Ψ) x) := by
          have hji' : j ∉ U'.erase i := fun h => hj (Finset.mem_of_mem_erase h)
          exact (slotProj_peel_ae (ℓ := ℓ) hbdd hsupp (U := U'.erase i) (i := j) hji'
            (aPC_memLp_top hℓ i hΨ)).symm
        have hset : insert j (U'.erase i) = (insert j U').erase i :=
          (Finset.erase_insert_of_ne hij).symm
        simpa only [hset] using h1.trans (h2.trans (h3.trans h4))

/-- **The slot mean commutes with every slot projection** (a.e. on the box): the erased
projection of `aPC_slotProj_erase` is put back on the box, where it is absorbed by M1. -/
theorem aPC_slotProj_comm_box {m N : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : Measure Sp), e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (i : Fin N) (U : Finset (Fin N)) {Ψ : (Fin N → Sp) → ℂ} (hΨ : MemLp Ψ ⊤) :
    (fun x => aPC ℓ i (slotProj e U Ψ) x)
      =ᵐ[(volume : Measure (Fin N → Sp)).restrict (Submission.BoseGases.abox N ℓ)]
      (fun x => slotProj e U (aPC ℓ i Ψ) x) := by
  classical
  have hA : MemLp (aPC ℓ i Ψ) ⊤ := aPC_memLp_top hℓ i hΨ
  have hstar := aPC_slotProj_erase (ℓ := ℓ) hℓ he hbdd hsupp hc i U hΨ
  by_cases hiU : i ∈ U
  · -- `i ∈ U`: the erased projection `U \ {i}` is restored on the box
    have hiT : i ∉ U.erase i := Finset.notMem_erase i U
    have hUT : insert i (U.erase i) = U := Finset.insert_erase hiU
    have hZ : MemLp (slotProj e (U.erase i) Ψ) ⊤ :=
      slotProj_memLp_top' hbdd hsupp (U.erase i) hΨ
    have hstarT := aPC_slotProj_erase (ℓ := ℓ) hℓ he hbdd hsupp hc i (U.erase i) hΨ
    have hself : (U.erase i).erase i = U.erase i := Finset.erase_eq_of_notMem hiT
    rw [hself] at hstarT
    have hUTfun : slotProj e U (aPC ℓ i Ψ) = slotProj e (insert i (U.erase i)) (aPC ℓ i Ψ) := by
      rw [hUT]
    have hpeel : (fun x => slotProj e U (aPC ℓ i Ψ) x)
        =ᵐ[(volume : Measure (Fin N → Sp))]
        (fun x => slotProj1 e i (slotProj e (U.erase i) (aPC ℓ i Ψ)) x) := by
      rw [hUTfun]
      exact slotProj_peel_ae (ℓ := ℓ) hbdd hsupp (U := U.erase i) (i := i) hiT hA
    have hcongr : (fun x => slotProj1 e i (slotProj e (U.erase i) (aPC ℓ i Ψ)) x)
        =ᵐ[(volume : Measure (Fin N → Sp))]
        (fun x => slotProj1 e i (aPC ℓ i (slotProj e (U.erase i) Ψ)) x) :=
      slotProj1_ae_eq_congr_aux e i hstarT.symm
    have hM1 : (fun x => slotProj1 e i (aPC ℓ i (slotProj e (U.erase i) Ψ)) x)
        =ᵐ[(volume : Measure (Fin N → Sp)).restrict (Submission.BoseGases.abox N ℓ)]
        (fun x => aPC ℓ i (slotProj e (U.erase i) Ψ) x) :=
      slotProj1_aPC_absorb_self ℓ hℓ he hbdd hsupp hc i hZ
    have hgoal : (fun x => slotProj e U (aPC ℓ i Ψ) x)
        =ᵐ[(volume : Measure (Fin N → Sp)).restrict (Submission.BoseGases.abox N ℓ)]
        (fun x => slotProj e (U.erase i) (aPC ℓ i Ψ) x) :=
      Filter.EventuallyEq.trans (eventuallyEq_restrict_box hpeel)
        (Filter.EventuallyEq.trans (eventuallyEq_restrict_box hcongr)
          (Filter.EventuallyEq.trans hM1 (eventuallyEq_restrict_box hstarT)))
    exact Filter.EventuallyEq.trans (eventuallyEq_restrict_box hstar) hgoal.symm
  · rw [Finset.erase_eq_of_notMem hiU] at hstar
    exact eventuallyEq_restrict_box hstar

/-- **The slot mean commutes with the sector projection** (a.e. on the box): the Möbius sum of
`slotProj` defining `slotExact` is handled by the `aPC`-additivity `aPC_finsetSum_ae` and the
per-slot-set commutation `aPC_slotProj_comm_box`. -/
theorem aPC_slotExact_comm_box {m N : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : Measure Sp), e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (i : Fin N) (S : Finset (Fin N)) {Ψ : (Fin N → Sp) → ℂ} (hΨ : MemLp Ψ ⊤) :
    (fun x => aPC ℓ i (slotExact e S Ψ) x)
      =ᵐ[(volume : Measure (Fin N → Sp)).restrict (Submission.BoseGases.abox N ℓ)]
      (fun x => slotExact e S (aPC ℓ i Ψ) x) := by
  classical
  set sf : Finset (Finset (Fin N)) := Finset.univ.filter (fun T : Finset (Fin N) => S ⊆ T)
    with hsf
  have hmem : ∀ T ∈ sf,
      MemLp (fun y => (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Ψ y) ⊤ :=
    fun T _ => (slotProj_memLp_top' hbdd hsupp T hΨ).const_smul
      ((-1 : ℂ) ^ (T.card - S.card))
  have hlin : (fun x => aPC ℓ i (slotExact e S Ψ) x)
      =ᵐ[(volume : Measure (Fin N → Sp))]
      (fun x => ∑ T ∈ sf, (-1 : ℂ) ^ (T.card - S.card) • aPC ℓ i (slotProj e T Ψ) x) := by
    have h := aPC_finsetSum_ae (ℓ := ℓ) hℓ i sf
      (Θ := fun T => fun y => (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Ψ y) hmem
    have hL : slotExact e S Ψ
        = fun y => ∑ T ∈ sf, (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Ψ y := by
      funext y
      rw [hsf]
      simp only [slotExact, Finset.sum_apply, Pi.smul_apply]
    have hR : (fun x => ∑ T ∈ sf,
          aPC ℓ i (fun y => (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Ψ y) x)
        = fun x => ∑ T ∈ sf, (-1 : ℂ) ^ (T.card - S.card) • aPC ℓ i (slotProj e T Ψ) x := by
      funext x
      exact Finset.sum_congr rfl (fun T _ =>
        aPC_const_smul ℓ i ((-1 : ℂ) ^ (T.card - S.card)) (slotProj e T Ψ) x)
    rw [← hL, hR] at h
    exact h
  have hterm : (fun x => ∑ T ∈ sf, (-1 : ℂ) ^ (T.card - S.card) • aPC ℓ i (slotProj e T Ψ) x)
      =ᵐ[(volume : Measure (Fin N → Sp)).restrict (Submission.BoseGases.abox N ℓ)]
      (fun x => ∑ T ∈ sf, (-1 : ℂ) ^ (T.card - S.card) • slotProj e T (aPC ℓ i Ψ) x) := by
    have hall : ∀ᵐ x ∂((volume : Measure (Fin N → Sp)).restrict
        (Submission.BoseGases.abox N ℓ)),
        ∀ T ∈ sf, aPC ℓ i (slotProj e T Ψ) x = slotProj e T (aPC ℓ i Ψ) x := by
      rw [Finset.eventually_all]
      intro T _
      exact aPC_slotProj_comm_box (ℓ := ℓ) hℓ he hbdd hsupp hc i T hΨ
    filter_upwards [hall] with x hx
    exact Finset.sum_congr rfl (fun T hT => by rw [hx T hT])
  have hRHS : (fun x => ∑ T ∈ sf, (-1 : ℂ) ^ (T.card - S.card) • slotProj e T (aPC ℓ i Ψ) x)
      = fun x => slotExact e S (aPC ℓ i Ψ) x := by
    funext x
    rw [hsf]
    simp only [slotExact, Finset.sum_apply, Pi.smul_apply]
  exact Filter.EventuallyEq.trans (eventuallyEq_restrict_box hlin)
    (hterm.trans (Filter.EventuallyEq.of_eq hRHS))

/-! ## 7. The single-step commutation `XS ∘ slotExact =ᵐ slotExact ∘ XS` -/

/-- **A finite sum of a.e. equal functions is a.e. equal.** -/
lemma eventuallyEq_finsetSum {ι α β : Type*} [AddCommMonoid β] {l : Filter α} {s : Finset ι}
    {f g : ι → α → β} (h : ∀ i ∈ s, f i =ᶠ[l] g i) :
    (fun x => ∑ i ∈ s, f i x) =ᶠ[l] (fun x => ∑ i ∈ s, g i x) := by
  filter_upwards [(Finset.eventually_all (l := l) s (p := fun i x => f i x = g i x)).2 h]
    with x hx
  exact Finset.sum_congr rfl hx

/-- **The sector is additive over differences of `L^∞` states** (a.e. on the box): the sector is
additive over finite sums (`slotExact_finsetSum_ae`), and writing `f = g + (f − g)` turns that
into the difference rule without ever splitting the Bochner integral of a single slot
projection. -/
lemma slotExact_sub_ae {n m : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {f g : (Fin n → Sp) → ℂ} (hf : MemLp f ⊤) (hg : MemLp g ⊤) :
    (fun x => slotExact e S (f - g) x)
      =ᵐ[(volume : Measure (Fin n → Sp)).restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => slotExact e S f x - slotExact e S g x) := by
  classical
  -- the two-term index: `0 ↦ g`, `1 ↦ f − g`
  set Θ : Fin 2 → (Fin n → Sp) → ℂ := fun k => if (k : ℕ) = 0 then g else f - g with hΘ
  have hΘ0 : Θ 0 = g := by rw [hΘ]; simp
  have hΘ1 : Θ 1 = f - g := by rw [hΘ]; simp
  have hΘmem : ∀ k ∈ (Finset.univ : Finset (Fin 2)), MemLp (Θ k) ⊤ := by
    intro k _
    have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    rcases hk with h | h
    · rw [h, hΘ0]; exact hg
    · rw [h, hΘ1]; exact hf.sub hg
  have hadd := slotExact_finsetSum_ae hbdd hsupp S (Finset.univ : Finset (Fin 2)) hΘmem
  -- the summed state is `f`
  have hfun : (fun y : Fin n → Sp => ∑ k ∈ (Finset.univ : Finset (Fin 2)), Θ k y) = f := by
    funext y
    rw [Fin.sum_univ_two]
    rw [hΘ0, hΘ1]
    simp only [Pi.sub_apply]
    ring
  -- the right-hand side is `slotExact f = slotExact g + slotExact (f − g)`
  have hsum : (fun x => ∑ k ∈ (Finset.univ : Finset (Fin 2)), slotExact e S (Θ k) x)
      = (fun x => slotExact e S g x + slotExact e S (f - g) x) := by
    funext x
    rw [Fin.sum_univ_two, hΘ0, hΘ1]
  rw [hfun, hsum] at hadd
  -- `slotExact f =ᵐ slotExact g + slotExact (f − g)`; rearrange
  filter_upwards [hadd] with x hx
  rw [hx]
  ring

/-- **`XS ℓ S` commutes with the sector projection** (a.e. on the box), for an `L^∞` state. -/
theorem XS_slotExact_comm_box {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : Measure Sp), e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (S : Finset (Fin n)) {Φ : (Fin n → Sp) → ℂ} (hΦ : MemLp Φ ⊤) :
    (fun x => XS ℓ S (slotExact e S Φ) x)
      =ᵐ[(volume : Measure (Fin n → Sp)).restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => slotExact e S (XS ℓ S Φ) x) := by
  classical
  have hΘmem : ∀ i ∈ S, MemLp (fun y : Fin n → Sp => Φ y - aPC ℓ i Φ y) ⊤ :=
    fun i _ => hΦ.sub (aPC_memLp_top hℓ i hΦ)
  have hadd := slotExact_finsetSum_ae hbdd hsupp S S hΘmem
  have hL : (fun y : Fin n → Sp => ∑ k ∈ S,
      (fun (i : Fin n) (y : Fin n → Sp) => Φ y - aPC ℓ i Φ y) k y) = XS ℓ S Φ := by
    funext y
    rfl
  rw [hL] at hadd
  have hsum : (fun x => ∑ k ∈ S, slotExact e S (fun y : Fin n → Sp => Φ y - aPC ℓ k Φ y) x)
      =ᵐ[(volume : Measure (Fin n → Sp)).restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => ∑ k ∈ S, (slotExact e S Φ x - aPC ℓ k (slotExact e S Φ) x)) := by
    refine eventuallyEq_finsetSum (fun k _ => ?_)
    have hsub := slotExact_sub_ae hbdd hsupp S hΦ (aPC_memLp_top hℓ k hΦ)
    have hcm := aPC_slotExact_comm_box (ℓ := ℓ) hℓ he hbdd hsupp hc k S hΦ
    refine hsub.trans ?_
    filter_upwards [hcm] with x hx
    rw [← hx]
  have hfin : (fun x => ∑ k ∈ S, (slotExact e S Φ x - aPC ℓ k (slotExact e S Φ) x))
      = XS ℓ S (slotExact e S Φ) := by
    funext x
    rfl
  exact ((Filter.EventuallyEq.of_eq hfin).symm.trans (hsum.symm.trans hadd.symm))

/-- **The sector projection is `XSpow ℓ S j`-equivariant** (a.e. on the box), by induction on `j`
on the single-step commutation `XS_slotExact_comm_box`. -/
theorem XSpow_slotExact_comm_box {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : Measure Sp), e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (S : Finset (Fin n)) (j : ℕ) {Ψ : (Fin n → Sp) → ℂ} (hΨ : MemLp Ψ ⊤) :
    (fun x => XSpow ℓ S j (slotExact e S Ψ) x)
      =ᵐ[(volume : Measure (Fin n → Sp)).restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => slotExact e S (XSpow ℓ S j Ψ) x) := by
  classical
  obtain ⟨C₀, _hC₀0, hC₀b⟩ := exists_ae_bound_of_memLp_top_aux hΨ
  have hXmem : ∀ i : ℕ, MemLp (XSpow ℓ S i Ψ) ⊤ := by
    intro i
    obtain ⟨haesm, C, hCb⟩ :=
      XSpow_aeStronglyMeasurable_ae_bounded ℓ hℓ S hΨ.aestronglyMeasurable ⟨C₀, hC₀b⟩ i
    exact memLp_top_of_bound haesm C hCb
  have hcongr : ∀ {f g : (Fin n → Sp) → ℂ},
      f =ᵐ[(volume : Measure (Fin n → Sp)).restrict (Submission.BoseGases.abox n ℓ)] g →
      XS ℓ S f =ᵐ[(volume : Measure (Fin n → Sp)).restrict (Submission.BoseGases.abox n ℓ)]
        XS ℓ S g := by
    intro f g hfg
    have hall : ∀ᵐ x ∂((volume : Measure (Fin n → Sp)).restrict
        (Submission.BoseGases.abox n ℓ)),
        ∀ i ∈ S, aPC ℓ i f x = aPC ℓ i g x := by
      rw [Finset.eventually_all]
      intro i _
      exact aPC_congr_ae_abox i hfg
    filter_upwards [hfg, hall] with x hx hxall
    simp only [XS]
    exact Finset.sum_congr rfl (fun i hi => by rw [hx, hxall i hi])
  have key : ∀ i : ℕ,
      (fun x => XSpow ℓ S i (slotExact e S Ψ) x)
        =ᵐ[(volume : Measure (Fin n → Sp)).restrict (Submission.BoseGases.abox n ℓ)]
        (fun x => slotExact e S (XSpow ℓ S i Ψ) x) := by
    intro i
    induction i with
    | zero => exact Filter.EventuallyEq.rfl
    | succ i ih =>
        have h1 : (fun x => XS ℓ S (XSpow ℓ S i (slotExact e S Ψ)) x)
            =ᵐ[(volume : Measure (Fin n → Sp)).restrict (Submission.BoseGases.abox n ℓ)]
            (fun x => XS ℓ S (slotExact e S (XSpow ℓ S i Ψ)) x) := hcongr ih
        have h2 := XS_slotExact_comm_box (ℓ := ℓ) hℓ he hbdd hsupp hc S (hXmem i)
        exact h1.trans h2
  exact key j

end Kf

/-- **The width form of the sector spectral bound, in a knot-free import cone.**

`Submission/Work/BoseBoxFock/sector_XSpow_width_holds.lean` already proves this exact statement
(687 lines, `sorry`-free, axiom-clean).  The present result is needed because that module imports
`Work.BoseBoxFock.XSpow_slotExact_comm`, whose cone contains `Work.BoseBoxFock._helpers`; and
`_helpers` imports `Work.BoseBoxFock.sliceBadCoeff_zero`, the single consumer of this result — so
that cone creates a *build cycle* and is unusable here.

The cone of this file must therefore avoid `XSpow_slotExact_comm`, `aPC_slotExact_comm_ae`,
`aPC_slotExact_aux`, `_helpers` and `sliceBadCoeff_zero`.  Concretely: copy the proof of
`sector_XSpow_width_holds` (it is *readable*; only its two forbidden imports must not be
reproduced) — every auxiliary result it uses is available in the cone listed in `depends_on`,
EXCEPT the single call `XSpow_slotExact_comm` in its last paragraph, which must be replaced by a
knot-free derivation of

    (comm)  XSpow ℓ S j (slotExact e S Φc) =ᵐ[(volume : Measure (X n)).restrict (abox n ℓ)]
              slotExact e S (XSpow ℓ S j Φc).

`FINDING_sector_XSpow_le_s11.md` §3 gives the route: `aPC ℓ i` commutes with `slotExact e S`
(equivalently `XSpow ℓ S j` does) by the Möbius expansion of `slotExact`, the finite-sum additivity
`aPC_finsetSum_ae`/`slotExact_finsetSum_ae` and the *per-slot* commutation, which follows from

* `slotProj1_aPC_absorb_self` (M1), `aPC_slotProj1_absorb` (M2) and `aPC_slotProj1_comm_ne`
  (disjoint slots) — the absorption `aPC ℓ i` vs `slotProj1 e i`, which use the pinning `hc`;
* `slotProj_peel_ae` (PEEL) `slotProj e (insert i U) Ψ =ᵐ slotProj1 e i (slotProj e U Ψ)`,
  which lifts the single-slot statement to every `slotProj e T` (with `T ∋ i`).

The `XSpow`-iterate version is then the induction on `j` already written in
`XSpow_slotExact_comm.lean` (copy that part too).  ⚠ Do NOT import
`Submission.Work.BoseBoxFock.XSpow_slotExact_comm`,
`Submission.Work.BoseBoxFock.aPC_slotExact_comm_ae`,
`Submission.Work.BoseBoxFock.aPC_slotExact_aux`,
`Submission.Work.BoseBoxFock._helpers`,
`Submission.Work.BoseBoxFock.sector_XSpow_width_holds`,
`Submission.Work.BoseBoxFock.sliceBadCoeff_zero`, nor
`Submission.Work.BoseBoxFock.slotSum_sectorPointwise` (duplicate `update_pairCoord`). -/
theorem sector_XSpow_width_holds_kf {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n))
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (hΦc : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ)
    {M : ℝ} (hM : 0 ≤ M) (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ)
    {m : ℕ} [NeZero m] {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (he : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x)) (j : ℕ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        ‖Work.BoseBoxFock.XSpow ℓ S j
          (Work.BoseBoxFock.slotExact e S (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2)
      ≤ M ^ (2 * j) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  -- the complexification of the box state is `L^∞`
  have hcs : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset (Submission.BoseGases.abox_compact n hℓ)
      (isClosed_tsupport Φ) hΦc
  obtain ⟨B, hB⟩ := hΦ.bounded_above_of_compact_support hcs
  have hΨbdd : ∀ᵐ x ∂(volume : Measure (Submission.BoseGases.X n)),
      ‖((Φ x : ℝ) : ℂ)‖ ≤ B :=
    Filter.Eventually.of_forall fun x => by
      rw [Complex.norm_real]
      exact hB x
  have hΨaesm : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp hΦ).aestronglyMeasurable
  have hΨmem : MemLp (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)) ⊤ :=
    memLp_top_of_bound hΨaesm B hΨbdd
  refine sector_XSpow_width (ℓ := ℓ) (hℓ := hℓ) (S := S) hΦ (M := M) hM hmom (j := j)
    (Kf.XSpow_slotExact_comm_box (ℓ := ℓ) hℓ he hbdd hsupp hc S j hΨmem) ?_
  -- the contraction, applied to `XSpow ℓ S j` of the complexified state
  obtain ⟨hXaesm, CX, hXbdd⟩ :=
    XSpow_aeStronglyMeasurable_ae_bounded ℓ hℓ S hΨaesm ⟨B, hΨbdd⟩ j
  exact Kf.slotExact_contract_box (ℓ := ℓ) hℓ he hbdd hsupp S
    (memLp_top_of_bound hXaesm CX hXbdd)

end

end Work.BoseBoxFock
