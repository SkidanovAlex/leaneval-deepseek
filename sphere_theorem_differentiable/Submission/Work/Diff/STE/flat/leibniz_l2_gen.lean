import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pdList_mul_sub
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.ENormSq_pairing_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `L²` Leibniz (commutator) estimate, with a split of the smoothness orders

This file proves `Work.Diff.STE.flat.leibniz_l2_gen`.

For a list `l` of `s + 1` directions, `∂^l (F·g) - F · ∂^l g` is the sum of the Leibniz terms
`∂^{p.1}F · ∂^{p.2}g` over the splits `p` of `l` with `p.1 ≠ []`.  The estimate of the file is

`|∑_l L2re (∂^l (F·g) - F·∂^l g) (∂^l v)| ≤ C (HF·EG·EV + EF·HG·EV)`,

where `HF`, `HG` are *sup* bounds for the iterated derivatives of `F` (up to order `MF`),
resp. `g` (up to order `Mg`), while `EF`, `EG`, `EV` are *`L²`* bounds for the iterated
derivatives of `F` (up to order `s+1`), `g` (up to order `s`), resp. `v` (up to order `s+1`),
and `s ≤ MF + Mg`.

The decisive point is *which* factor of a Leibniz term carries the sup bound.  Every term of the
commutator expansion has `|p.1| + |p.2| = s+1`, `p.1 ≠ []`, so
* either `|p.1| ≤ MF`, and then `‖∂^{p.1}F‖` is bounded by `HF` pointwise while `∂^{p.2}g` and
  `∂^l v` are controlled in `L²` (both at order `≤ s`),
* or `|p.1| > MF`, and then `|p.2| = s+1-|p.1| ≤ s - MF ≤ Mg`, so `‖∂^{p.2}g‖ ≤ HG` pointwise
  while `∂^{p.1}F` (order `≤ s+1`) and `∂^l v` are controlled in `L²`.

Both alternatives give the same shape `(sup bound) · √(∫‖·‖²) · √(∫‖·‖²)`, which is the
Cauchy–Schwarz bound `L2re_mul_le_sqrt` of this file.
-/

noncomputable section

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The elementary `L²` term bound -/

/-- The `L²` pairing is symmetric under swapping the two factors of the first argument,
`L2re (fun x => a x * b x) w = L2re (fun x => b x * a x) w`. -/
theorem L2re_mul_comm (a b w : (ι → ℝ) → ℂ) :
    Work.Diff.STE.L2re (fun x => a x * b x) w
      = Work.Diff.STE.L2re (fun x => b x * a x) w := by
  simp only [Work.Diff.STE.L2re]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))

/-- **Cauchy–Schwarz with a pointwise bound on the first factor.**
If `‖u x‖ ≤ M` for all `x`, `∫ ‖w‖² ≤ G` and `∫ ‖h‖² ≤ H`, then
`|L2re (u·w) h| ≤ M √G √H`. -/
theorem L2re_mul_le_sqrt (u w h : (ι → ℝ) → ℂ) (M G H : ℝ)
    (hu : Continuous u) (hw : Continuous w) (hh : Continuous h)
    (hM : 0 ≤ M) (hub : ∀ x, ‖u x‖ ≤ M)
    (hG : ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖w x‖ ^ 2 ≤ G)
    (hH : ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖h x‖ ^ 2 ≤ H)
    (hGn : 0 ≤ G) (hHn : 0 ≤ H) :
    |Work.Diff.STE.L2re (fun x => u x * w x) h| ≤ M * Real.sqrt G * Real.sqrt H := by
  have hIntUW : Integrable (fun x : ι → ℝ => ‖u x * w x‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.cm_integrableOn_unitCube_of_continuous ((hu.mul hw).norm.pow 2)
  have hIntW : Integrable (fun x : ι → ℝ => ‖w x‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.cm_integrableOn_unitCube_of_continuous (hw.norm.pow 2)
  have hIntH : Integrable (fun x : ι → ℝ => ‖h x‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.cm_integrableOn_unitCube_of_continuous (hh.norm.pow 2)
  have hcs := Work.Diff.STE.L2re_abs_le_sqrt (fun x : ι → ℝ => u x * w x) h hIntUW hIntH
  -- the pointwise bound on `‖u‖` is integrated against `‖w‖²`
  have hle : (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖u x * w x‖ ^ 2)
      ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), M ^ 2 * ‖w x‖ ^ 2 := by
    refine integral_mono_ae hIntUW (hIntW.const_mul (M ^ 2))
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 : ‖u x‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (u x), hub x, hM]
    have h2 : 0 ≤ ‖w x‖ ^ 2 := sq_nonneg _
    calc ‖u x * w x‖ ^ 2 = ‖u x‖ ^ 2 * ‖w x‖ ^ 2 := by rw [norm_mul, mul_pow]
      _ ≤ M ^ 2 * ‖w x‖ ^ 2 := by nlinarith
  have hs : Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖u x * w x‖ ^ 2)
      ≤ M * Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖w x‖ ^ 2) := by
    have h := Real.sqrt_le_sqrt hle
    have heq : Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), M ^ 2 * ‖w x‖ ^ 2)
        = M * Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖w x‖ ^ 2) := by
      rw [integral_const_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq hM]
    linarith [h, heq]
  have hA : Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖w x‖ ^ 2)
      ≤ Real.sqrt G := Real.sqrt_le_sqrt hG
  have hB : Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖h x‖ ^ 2)
      ≤ Real.sqrt H := Real.sqrt_le_sqrt hH
  refine hcs.trans ?_
  calc Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖u x * w x‖ ^ 2)
        * Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖h x‖ ^ 2)
      ≤ (M * Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖w x‖ ^ 2))
          * Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖h x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
    _ ≤ M * Real.sqrt G * Real.sqrt H := by
        refine (mul_le_mul (mul_le_mul_of_nonneg_left hA hM) hB
          (Real.sqrt_nonneg _) (mul_nonneg hM (Real.sqrt_nonneg G))).trans (le_of_eq ?_)
        ring

/-! ## Summing the Leibniz terms -/

/-- **The Leibniz expansion of the commutator, estimated term by term.**
If `∂^L(F·g) - F·∂^L g` is the sum of the Leibniz terms `∂^{p.1}F · ∂^{p.2}g` over
`p ∈ (splits L).filter (fun p => p.1 ≠ [])`, and each of these terms is bounded by `C ≥ 0` in the
`L²` pairing against `w`, then the pairing of the full commutator with `w` is bounded by
`(splits L).length * C`. -/
theorem L2re_pdList_mul_sub_le {n : ℕ} (L : List (Fin n)) (F g w : (Fin n → ℝ) → ℂ) (C : ℝ)
    (hC : 0 ≤ C)
    (hleib : (fun y => Work.Diff.STE.pdList L (fun z => F z * g z) y
        - F y * Work.Diff.STE.pdList L g y)
      = fun y => ((List.filter (fun p : List (Fin n) × List (Fin n) => p.1 ≠ [])
          (Work.Diff.STE.splits L)).map
        (fun p => Work.Diff.STE.pdList p.1 F y * Work.Diff.STE.pdList p.2 g y)).sum)
    (hcontF : ∀ p ∈ List.filter (fun p : List (Fin n) × List (Fin n) => p.1 ≠ [])
        (Work.Diff.STE.splits L), Continuous (Work.Diff.STE.pdList p.1 F))
    (hcontg : ∀ p ∈ List.filter (fun p : List (Fin n) × List (Fin n) => p.1 ≠ [])
        (Work.Diff.STE.splits L), Continuous (Work.Diff.STE.pdList p.2 g))
    (hw : Continuous w)
    (hterm : ∀ p ∈ List.filter (fun p : List (Fin n) × List (Fin n) => p.1 ≠ [])
        (Work.Diff.STE.splits L),
      |Work.Diff.STE.L2re (fun y => Work.Diff.STE.pdList p.1 F y * Work.Diff.STE.pdList p.2 g y)
        w| ≤ C) :
    |Work.Diff.STE.L2re (fun y => Work.Diff.STE.pdList L (fun z => F z * g z) y
        - F y * Work.Diff.STE.pdList L g y) w|
      ≤ ((Work.Diff.STE.splits L).length : ℝ) * C := by
  classical
  set Sf : List (List (Fin n) × List (Fin n)) :=
    List.filter (fun p : List (Fin n) × List (Fin n) => p.1 ≠ []) (Work.Diff.STE.splits L)
    with hSf
  have hcont : ∀ p ∈ Sf, Continuous (fun y => Work.Diff.STE.pdList p.1 F y
      * Work.Diff.STE.pdList p.2 g y) :=
    fun p hp => (hcontF p (hSf ▸ hp)).mul (hcontg p (hSf ▸ hp))
  have hlin := Work.Diff.STE.cm_L2re_list_sum Sf
    (fun p y => Work.Diff.STE.pdList p.1 F y * Work.Diff.STE.pdList p.2 g y) w hcont hw
  have hfun : (fun y => (Sf.map (fun p => Work.Diff.STE.pdList p.1 F y
        * Work.Diff.STE.pdList p.2 g y)).sum)
      = (Sf.map (fun p => fun y => Work.Diff.STE.pdList p.1 F y
          * Work.Diff.STE.pdList p.2 g y)).sum :=
    Work.Diff.STE.cm_list_sum_apply Sf
      (fun p y => Work.Diff.STE.pdList p.1 F y * Work.Diff.STE.pdList p.2 g y)
  have hterm' : ∀ p ∈ Sf, |Work.Diff.STE.L2re (fun y => Work.Diff.STE.pdList p.1 F y
      * Work.Diff.STE.pdList p.2 g y) w| ≤ C := fun p hp => hterm p (hSf ▸ hp)
  have hlen : (Sf.length : ℝ) ≤ ((Work.Diff.STE.splits L).length : ℝ) := by
    have h : Sf.length ≤ (Work.Diff.STE.splits L).length := by
      rw [hSf]; exact List.length_filter_le _ _
    exact_mod_cast h
  have hconst : (Sf.map (fun _ => C)).sum = (Sf.length : ℝ) * C := by
    induction Sf with
    | nil => simp
    | cons a t ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
        rw [ih]; push_cast; ring
  have hkey : |Work.Diff.STE.L2re (fun y => Work.Diff.STE.pdList L (fun z => F z * g z) y
      - F y * Work.Diff.STE.pdList L g y) w|
      = |(Sf.map (fun p => Work.Diff.STE.L2re (fun y => Work.Diff.STE.pdList p.1 F y
          * Work.Diff.STE.pdList p.2 g y) w)).sum| := by
    rw [hleib, hfun, hlin]
  rw [hkey]
  have step1 : |(Sf.map (fun p => Work.Diff.STE.L2re (fun y => Work.Diff.STE.pdList p.1 F y
      * Work.Diff.STE.pdList p.2 g y) w)).sum|
      ≤ (Sf.map (fun p => |Work.Diff.STE.L2re (fun y => Work.Diff.STE.pdList p.1 F y
          * Work.Diff.STE.pdList p.2 g y) w|)).sum := Work.Diff.STE.cm_list_abs_sum_le Sf _
  have step2 : (Sf.map (fun p => |Work.Diff.STE.L2re (fun y => Work.Diff.STE.pdList p.1 F y
      * Work.Diff.STE.pdList p.2 g y) w|)).sum ≤ (Sf.map (fun _ => C)).sum :=
    List.sum_le_sum (fun p hp => hterm' p hp)
  have step3 : (Sf.map (fun _ => C)).sum ≤ ((Work.Diff.STE.splits L).length : ℝ) * C := by
    rw [hconst]
    exact mul_le_mul_of_nonneg_right hlen hC
  exact step1.trans (step2.trans step3)

/-! ## The per-term estimate -/

/-- **One Leibniz term.**  If `p` is a split with `p.1 ≠ []` and
`p.1.length + p.2.length = s + 1`, and `s ≤ MF + Mg`, then the Leibniz term
`∂^{p.1}F · ∂^{p.2}g` is bounded in the `L²` pairing against `w` by
`HF·EG·EV + EF·HG·EV`: depending on whether `p.1.length ≤ MF` or not, either the `F`-factor or
the `g`-factor carries the *sup* bound `HF`, resp. `HG`, and the two remaining factors carry the
`L²` bounds. -/
theorem leibniz_term_le {n s MF Mg : ℕ} (hMs : s ≤ MF + Mg)
    (F g w : (Fin n → ℝ) → ℂ) (HF HG EF EG EV : ℝ)
    (hHF : 0 ≤ HF) (hHG : 0 ≤ HG) (hEF : 0 ≤ EF) (hEG : 0 ≤ EG) (hEV : 0 ≤ EV)
    (hFsup : ∀ m ≤ MF, ∀ l : Fin m → Fin n, ∀ x, ‖Work.Diff.STE.pdVec m l F x‖ ≤ HF)
    (hgsup : ∀ m ≤ Mg, ∀ l : Fin m → Fin n, ∀ x, ‖Work.Diff.STE.pdVec m l g x‖ ≤ HG)
    (hFl2 : ∀ m ≤ s + 1, ∀ l : Fin m → Fin n,
      ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m l F x‖ ^ 2 ≤ EF ^ 2)
    (hgl2 : ∀ m ≤ s, ∀ l : Fin m → Fin n,
      ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m l g x‖ ^ 2 ≤ EG ^ 2)
    (hw : Continuous w)
    (hwl2 : ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖w x‖ ^ 2 ≤ EV ^ 2)
    (p : List (Fin n) × List (Fin n)) (hp1 : p.1 ≠ [])
    (hlen : p.1.length + p.2.length = s + 1)
    (hcontF : Continuous (Work.Diff.STE.pdList p.1 F))
    (hcontg : Continuous (Work.Diff.STE.pdList p.2 g)) :
    |Work.Diff.STE.L2re (fun y => Work.Diff.STE.pdList p.1 F y
        * Work.Diff.STE.pdList p.2 g y) w|
      ≤ HF * EG * EV + EF * HG * EV := by
  have hplen : p.1.length ≤ s + 1 := by omega
  have hp2len : p.2.length ≤ s := by
    have hpos : 0 < p.1.length := List.length_pos_of_ne_nil hp1
    omega
  have hgetF : Work.Diff.STE.pdVec p.1.length p.1.get F = Work.Diff.STE.pdList p.1 F := by
    simp [Work.Diff.STE.pdVec, List.ofFn_get]
  have hgetg : Work.Diff.STE.pdVec p.2.length p.2.get g = Work.Diff.STE.pdList p.2 g := by
    simp [Work.Diff.STE.pdVec, List.ofFn_get]
  by_cases hle : p.1.length ≤ MF
  · -- the `F`-factor carries the sup bound
    have hsup1 : ∀ x, ‖Work.Diff.STE.pdList p.1 F x‖ ≤ HF := by
      intro x
      rw [← hgetF]
      exact hFsup p.1.length hle p.1.get x
    have hl2g : (∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdList p.2 g x‖ ^ 2) ≤ EG ^ 2 := by
      rw [← hgetg]
      exact hgl2 p.2.length hp2len p.2.get
    have h := L2re_mul_le_sqrt (Work.Diff.STE.pdList p.1 F) (Work.Diff.STE.pdList p.2 g) w
      HF (EG ^ 2) (EV ^ 2) hcontF hcontg hw hHF hsup1 hl2g hwl2 (by positivity) (by positivity)
    rw [Real.sqrt_sq hEG, Real.sqrt_sq hEV] at h
    linarith [h, mul_nonneg (mul_nonneg hEF hHG) hEV]
  · -- the `g`-factor carries the sup bound
    have hlt : MF < p.1.length := not_le.mp hle
    have hcase2 : p.2.length ≤ Mg := by omega
    have hsup2 : ∀ x, ‖Work.Diff.STE.pdList p.2 g x‖ ≤ HG := by
      intro x
      rw [← hgetg]
      exact hgsup p.2.length hcase2 p.2.get x
    have hl2F : (∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdList p.1 F x‖ ^ 2) ≤ EF ^ 2 := by
      rw [← hgetF]
      exact hFl2 p.1.length hplen p.1.get
    have h := L2re_mul_le_sqrt (Work.Diff.STE.pdList p.2 g) (Work.Diff.STE.pdList p.1 F) w
      HG (EF ^ 2) (EV ^ 2) hcontg hcontF hw hHG hsup2 hl2F hwl2 (by positivity) (by positivity)
    rw [Real.sqrt_sq hEF, Real.sqrt_sq hEV] at h
    rw [L2re_mul_comm] at h
    linarith [h, mul_nonneg (mul_nonneg hHF hEG) hEV]

/-! ## The estimate for one multi-index -/

/-- The general form of `leibniz_l2_gen` at a single multi-index `l : Fin (s+1) → Fin n`. -/
theorem leibniz_one_l2 {n s MF Mg : ℕ} (hMs : s ≤ MF + Mg)
    (F g v : (Fin n → ℝ) → ℂ)
    (hFsm : ContDiff ℝ (⊤ : ℕ∞) F) (hgsm : ContDiff ℝ (⊤ : ℕ∞) g)
    (hvsm : ContDiff ℝ (⊤ : ℕ∞) v)
    (HF HG EF EG EV : ℝ) (hHF : 0 ≤ HF) (hHG : 0 ≤ HG)
    (hEF : 0 ≤ EF) (hEG : 0 ≤ EG) (hEV : 0 ≤ EV)
    (hFsup : ∀ m ≤ MF, ∀ l : Fin m → Fin n, ∀ x, ‖Work.Diff.STE.pdVec m l F x‖ ≤ HF)
    (hgsup : ∀ m ≤ Mg, ∀ l : Fin m → Fin n, ∀ x, ‖Work.Diff.STE.pdVec m l g x‖ ≤ HG)
    (hFl2 : ∀ m ≤ s + 1, ∀ l : Fin m → Fin n,
      ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m l F x‖ ^ 2 ≤ EF ^ 2)
    (hgl2 : ∀ m ≤ s, ∀ l : Fin m → Fin n,
      ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m l g x‖ ^ 2 ≤ EG ^ 2)
    (l : Fin (s + 1) → Fin n)
    (hvl2 : ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
      ‖Work.Diff.STE.pdVec (s + 1) l v x‖ ^ 2 ≤ EV ^ 2) :
    |Work.Diff.STE.L2re
        (fun x => Work.Diff.STE.pdVec (s + 1) l (fun z => F z * g z) x
          - F x * Work.Diff.STE.pdVec (s + 1) l g x)
        (Work.Diff.STE.pdVec (s + 1) l v)|
      ≤ (2 : ℝ) ^ (s + 1) * (HF * EG * EV + EF * HG * EV) := by
  classical
  set L : List (Fin n) := List.ofFn l with hL
  have hLlen : L.length = s + 1 := by simp [hL]
  have hsmF : ∀ (q : List (Fin n)) (m : ℕ),
      ContDiff ℝ (((q.length + m : ℕ)) : WithTop ℕ∞) F :=
    fun q m => hFsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hsmg : ∀ (q : List (Fin n)) (m : ℕ),
      ContDiff ℝ (((q.length + m : ℕ)) : WithTop ℕ∞) g :=
    fun q m => hgsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hsmv : ∀ (q : List (Fin n)) (m : ℕ),
      ContDiff ℝ (((q.length + m : ℕ)) : WithTop ℕ∞) v :=
    fun q m => hvsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdiffF : ∀ q : List (Fin n), q.Sublist L → q.length < L.length →
      Differentiable ℝ (Work.Diff.STE.pdList q F) :=
    fun q _ _ => (Work.Diff.STE.cm_contDiff_pdList q 1 F (hsmF q 1)).differentiable (by norm_num)
  have hdiffg : ∀ q : List (Fin n), q.Sublist L → q.length < L.length →
      Differentiable ℝ (Work.Diff.STE.pdList q g) :=
    fun q _ _ => (Work.Diff.STE.cm_contDiff_pdList q 1 g (hsmg q 1)).differentiable (by norm_num)
  have hleib := Work.Diff.STE.pdList_mul_sub L F g hdiffF hdiffg
  have hcontF : ∀ q : List (Fin n), q.length ≤ L.length →
      Continuous (Work.Diff.STE.pdList q F) :=
    fun q _ => (Work.Diff.STE.cm_contDiff_pdList q 0 F (hsmF q 0)).continuous
  have hcontg : ∀ q : List (Fin n), q.length ≤ L.length →
      Continuous (Work.Diff.STE.pdList q g) :=
    fun q _ => (Work.Diff.STE.cm_contDiff_pdList q 0 g (hsmg q 0)).continuous
  have hcontv : Continuous (Work.Diff.STE.pdVec (s + 1) l v) := by
    have h : Work.Diff.STE.pdVec (s + 1) l v = Work.Diff.STE.pdList L v := rfl
    rw [h]
    exact (Work.Diff.STE.cm_contDiff_pdList L 0 v (hsmv L 0)).continuous
  -- the per-term estimate
  have hterm : ∀ p ∈ List.filter (fun p : List (Fin n) × List (Fin n) => p.1 ≠ [])
      (Work.Diff.STE.splits L),
      |Work.Diff.STE.L2re (fun y => Work.Diff.STE.pdList p.1 F y
        * Work.Diff.STE.pdList p.2 g y) (Work.Diff.STE.pdVec (s + 1) l v)|
      ≤ HF * EG * EV + EF * HG * EV := by
    intro p hp
    obtain ⟨hp', hneBool⟩ := List.mem_filter.mp hp
    have hne : p.1 ≠ [] := of_decide_eq_true hneBool
    have hlen := Work.Diff.STE.cm_splits_mem_length L p hp'
    have hlen1 : p.1.length ≤ L.length := by omega
    have hlen2 : p.2.length ≤ L.length := by omega
    refine leibniz_term_le hMs F g (Work.Diff.STE.pdVec (s + 1) l v) HF HG EF EG EV
      hHF hHG hEF hEG hEV hFsup hgsup hFl2 hgl2 hcontv hvl2 p hne ?_ ?_ ?_
    · rw [hLlen] at hlen; omega
    · exact hcontF p.1 hlen1
    · exact hcontg p.2 hlen2
  have hC0 : 0 ≤ HF * EG * EV + EF * HG * EV := by positivity
  have hmain := L2re_pdList_mul_sub_le L F g (Work.Diff.STE.pdVec (s + 1) l v)
    (HF * EG * EV + EF * HG * EV) hC0 hleib
    (fun p hp => hcontF p.1 (by
      have h := Work.Diff.STE.cm_splits_mem_length L p (List.mem_filter.mp hp).1
      omega))
    (fun p hp => hcontg p.2 (by
      have h := Work.Diff.STE.cm_splits_mem_length L p (List.mem_filter.mp hp).1
      omega))
    hcontv hterm
  have hlen_le : ((Work.Diff.STE.splits L).length : ℝ) ≤ (2 : ℝ) ^ (s + 1) := by
    have h : (Work.Diff.STE.splits L).length ≤ 2 ^ (s + 1) := by
      rw [Work.Diff.STE.cm_splits_length_count, hLlen]
    exact_mod_cast h
  refine hmain.trans ?_
  exact mul_le_mul_of_nonneg_right hlen_le hC0

/-! ## The main theorem -/

theorem leibniz_l2_gen {n s MF Mg : ℕ} (hMs : s ≤ MF + Mg) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F g v : (Fin n → ℝ) → ℂ)
      (hFsm : ContDiff ℝ (⊤ : ℕ∞) F) (hgsm : ContDiff ℝ (⊤ : ℕ∞) g)
      (hvsm : ContDiff ℝ (⊤ : ℕ∞) v)
      (hFper : Work.Diff.STE.Periodic1 F) (hgper : Work.Diff.STE.Periodic1 g)
      (hvper : Work.Diff.STE.Periodic1 v)
      (HF HG EF EG EV : ℝ) (hHF : 0 ≤ HF) (hHG : 0 ≤ HG)
      (hEF : 0 ≤ EF) (hEG : 0 ≤ EG) (hEV : 0 ≤ EV)
      (hFsup : ∀ m ≤ MF, ∀ l : Fin m → Fin n, ∀ x, ‖Work.Diff.STE.pdVec m l F x‖ ≤ HF)
      (hgsup : ∀ m ≤ Mg, ∀ l : Fin m → Fin n, ∀ x, ‖Work.Diff.STE.pdVec m l g x‖ ≤ HG)
      (hFl2 : ∀ m ≤ s + 1, ∀ l : Fin m → Fin n,
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m l F x‖ ^ 2 ≤ EF ^ 2)
      (hgl2 : ∀ m ≤ s, ∀ l : Fin m → Fin n,
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m l g x‖ ^ 2 ≤ EG ^ 2)
      (hvl2 : ∀ l : Fin (s + 1) → Fin n,
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec (s + 1) l v x‖ ^ 2 ≤ EV ^ 2),
      |∑ l : Fin (s + 1) → Fin n,
        Work.Diff.STE.L2re
          (fun x => Work.Diff.STE.pdVec (s + 1) l (fun z => F z * g z) x
            - F x * Work.Diff.STE.pdVec (s + 1) l g x)
          (Work.Diff.STE.pdVec (s + 1) l v)|
        ≤ C * (HF * EG * EV + EF * HG * EV) := by
  classical
  refine ⟨(n : ℝ) ^ (s + 1) * 2 ^ (s + 1) + 1, by positivity, ?_⟩
  intro F g v hFsm hgsm hvsm hFper hgper hvper HF HG EF EG EV
    hHF hHG hEF hEG hEV hFsup hgsup hFl2 hgl2 hvl2
  have hX : 0 ≤ HF * EG * EV + EF * HG * EV := by positivity
  have hper : ∀ l : Fin (s + 1) → Fin n,
      |Work.Diff.STE.L2re
        (fun x => Work.Diff.STE.pdVec (s + 1) l (fun z => F z * g z) x
          - F x * Work.Diff.STE.pdVec (s + 1) l g x)
        (Work.Diff.STE.pdVec (s + 1) l v)|
      ≤ (2 : ℝ) ^ (s + 1) * (HF * EG * EV + EF * HG * EV) :=
    fun l => leibniz_one_l2 hMs F g v hFsm hgsm hvsm HF HG EF EG EV
      hHF hHG hEF hEG hEV hFsup hgsup hFl2 hgl2 l (hvl2 l)
  have hsum : |∑ l : Fin (s + 1) → Fin n,
        Work.Diff.STE.L2re
          (fun x => Work.Diff.STE.pdVec (s + 1) l (fun z => F z * g z) x
            - F x * Work.Diff.STE.pdVec (s + 1) l g x)
          (Work.Diff.STE.pdVec (s + 1) l v)|
      ≤ (n : ℝ) ^ (s + 1) * ((2 : ℝ) ^ (s + 1) * (HF * EG * EV + EF * HG * EV)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun l _ => hper l)).trans ?_
    have hcard : ((Finset.univ : Finset (Fin (s + 1) → Fin n)).card : ℝ) = (n : ℝ) ^ (s + 1) := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      push_cast
      ring
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  refine hsum.trans ?_
  have hEq : (n : ℝ) ^ (s + 1) * ((2 : ℝ) ^ (s + 1) * (HF * EG * EV + EF * HG * EV))
      = ((n : ℝ) ^ (s + 1) * 2 ^ (s + 1)) * (HF * EG * EV + EF * HG * EV) := by ring
  rw [hEq]
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hX

end Work.Diff.STE.flat
