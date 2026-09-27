import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.germGlue
import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm
import Submission.Work.Compat.MFDerivCongrV433

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Gluing a straight germ segment to a middle arc  (WIP: statement frozen, proof open)

Step 1 of the design in `NOTES_S112b_twoLanes_complete_design.md` §2/§9.  The piece of one stage of
the immersed-line recursion is

  `P = [ straight germ segment σ → x in the chart c along u ]  ⊔  [ a middle arc α from x ]`

where `x = c.symm (c σ + L • u)` and the middle is straight from `x` along the *same* chart line.
The two parts agree with that chart line on a neighbourhood of the glue point.

The `φ`-clamp: for `t < 0` the raw chart line leaves `c.target`, so the germ part is written as
`t ↦ c.symm (c σ + φ t • u)` with `φ` smooth, the identity on `(-1, L+1)` (hence on a *neighbourhood*
of every parameter in `[0, L+1]`, which makes the germ part locally the chart line, so the immersion
of the germ half is `isImmersion_chartLine` verbatim) and globally valued so that the chart argument
stays in `c.target`.

Available ingredients (all proved in the workspace):
* `germGlue.contMDiffAt_glue_same_germ` — the junction clause of global `C^∞`;
* `germGlue.mfderiv_sub_eq_id` — `mfderiv (fun s : ℝ => s - c) x = id`, so the past-the-junction
  immersion is `hαimm` transported along the chain rule;
* `immersedArcWithGerm.isImmersion_chartLine` — the germ half;
* `ContMDiff` is `∀ x, ContMDiffAt` (as in `arrivalGlue.contMDiff_cutGlued`), so global smoothness
  is pointwise: `t < L` by `hg_sm.congr_of_eventuallyEq`, `t = L` by the junction lemma, `t > L` by
  the composite with the shift.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology Function
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (MC n) smoothOrder M] [T2Space M]

/-- **The clamped germ map is `C^∞`.**  The chart argument `c σ + φ t • u` is kept inside
`c.target` by `hφtgt`, so `c.symm` composes with the (smooth) inner map everywhere. -/
lemma clampedGerm_contMDiff {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) {σ : M}
    {u : EuclideanSpace ℝ (Fin n)} {φ : ℝ → ℝ}
    (hφsm : ∀ k : ℕ∞, ContDiff ℝ (k : WithTop ℕ∞) φ)
    (hφtgt : ∀ t : ℝ, c σ + φ t • u ∈ c.target) :
    ContMDiff MCreal (MC n) smoothOrder (fun t : ℝ => c.symm (c σ + φ t • u)) := by
  intro t
  have hinner : ContMDiffAt MCreal (MC n) smoothOrder (fun s : ℝ => c σ + φ s • u) t := by
    rw [MCreal, MC, smoothOrder, contMDiffAt_iff_contDiffAt]
    have h1 : ContDiff ℝ (∞ : WithTop ℕ∞) φ := hφsm ⊤
    exact (contDiff_const.add (h1.smul_const u)).contDiffAt
  have hsymm : ContMDiffAt (MC n) (MC n) smoothOrder (⇑c.symm) (c σ + φ t • u) :=
    (contMDiffOn_symm_of_mem_maximalAtlas hc).contMDiffAt (c.open_target.mem_nhds (hφtgt t))
  exact hsymm.comp t hinner

/-- **The glued piece is `C^∞` strictly left of the junction.**  There it *is* the clamped germ
map (the `if` takes its first branch), so this is a congruence. -/
lemma glue_contMDiffAt_left {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) {σ : M}
    {u : EuclideanSpace ℝ (Fin n)} {φ : ℝ → ℝ} {L : ℝ}
    (hφsm : ∀ k : ℕ∞, ContDiff ℝ (k : WithTop ℕ∞) φ)
    (hφtgt : ∀ t : ℝ, c σ + φ t • u ∈ c.target)
    {α : ℝ → M} {t : ℝ} (ht : t < L) :
    ContMDiffAt MCreal (MC n) smoothOrder
      (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) t := by
  refine (clampedGerm_contMDiff hc hφsm hφtgt).contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
  rw [if_pos (le_of_lt hs)]

/-- **The glued piece is `C^∞` strictly right of the junction.**  There it is `α` composed with the
shift `s ↦ s - L`. -/
lemma glue_contMDiffAt_right {α : ℝ → M} (hαsm : ContMDiff MCreal (MC n) smoothOrder α)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {σ : M}
    {u : EuclideanSpace ℝ (Fin n)} {φ : ℝ → ℝ} {L t : ℝ} (ht : L < t) :
    ContMDiffAt MCreal (MC n) smoothOrder
      (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) t := by
  have hshift : ContMDiffAt MCreal MCreal smoothOrder (fun s : ℝ => s - L) t :=
    (contMDiffAt_id (x := t) (n := (∞ : WithTop ℕ∞))).sub
      (contMDiffAt_const (x := t) (n := (∞ : WithTop ℕ∞)))
  have hcomp : ContMDiffAt MCreal (MC n) smoothOrder (fun s : ℝ => α (s - L)) t :=
    (hαsm.contMDiffAt (x := t - L)).comp t hshift
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  rw [if_neg (not_le.mpr hs)]

/-- **The glued piece is `C^∞` at the junction.**  Both branches agree there with the same straight
chart line (through `p`, in the direction `w`), which is exactly the hypothesis of
`germGlue.contMDiffAt_glue_same_germ`; the call site discharges those two obligations. -/
lemma glue_contMDiffAt_junction {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) {δ : ℝ} (hδ : 0 < δ)
    {σ p : M} (hp : p ∈ c.source) {u : EuclideanSpace ℝ (Fin n)} {φ : ℝ → ℝ} {L : ℝ}
    {α : ℝ → M} {w : EuclideanSpace ℝ (Fin n)}
    (hA : ∀ t : ℝ, L - δ ≤ t → t ≤ L →
      c.symm (c σ + φ t • u) = c.symm (c p + (t - L) • w))
    (hB : ∀ t : ℝ, L ≤ t → t ≤ L + δ → α (t - L) = c.symm (c p + (t - L) • w)) :
    ContMDiffAt MCreal (MC n) smoothOrder
      (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) L :=
  contMDiffAt_glue_same_germ (n := n) hc hp (w := w) hδ
    (A := fun s : ℝ => c.symm (c σ + φ s • u)) (B := fun s : ℝ => α (s - L)) (τ := L) hA hB

/-- **The glued piece is `C^∞`.**  Pointwise assembly: strictly left and strictly right of the
junction the two congruences apply, and at the junction `glue_contMDiffAt_junction` does, with the
two branch-agreement obligations produced here from `hφid`, `hα0` (through `c (α 0) = c σ + L • u`)
and `hαgerm`. -/
lemma glue_contMDiff {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) {σ : M} (hσ : σ ∈ c.source)
    {u : EuclideanSpace ℝ (Fin n)} {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hφsm : ∀ k : ℕ∞, ContDiff ℝ (k : WithTop ℕ∞) φ)
    (hφid : ∀ t : ℝ, -1 < t → t < L + 1 → φ t = t)
    (hφtgt : ∀ t : ℝ, c σ + φ t • u ∈ c.target)
    {α : ℝ → M} (hαsm : ContMDiff MCreal (MC n) smoothOrder α)
    {ε : ℝ} (hε : 0 < ε) (hα0 : α 0 = c.symm (c σ + L • u))
    (hαgerm : ∀ s : ℝ, 0 ≤ s → s ≤ ε →
      α s = c.symm (c (α 0) + s • u) ∧ c (α 0) + s • u ∈ c.target) :
    ContMDiff MCreal (MC n) smoothOrder
      (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) := by
  have hφL : φ L = L := hφid L (by linarith) (by linarith)
  have hctgt : c σ + L • u ∈ c.target := by rw [← hφL]; exact hφtgt L
  have hcq : c (α 0) = c σ + L • u := by rw [hα0, c.right_inv hctgt]
  have hα0src : α 0 ∈ c.source := by rw [hα0]; exact (c.symm).map_source hctgt
  intro t
  rcases lt_trichotomy t L with hlt | heq | hgt
  · exact glue_contMDiffAt_left hc hφsm hφtgt hlt
  · rw [heq]
    refine glue_contMDiffAt_junction hc (δ := min 1 ε) (lt_min one_pos hε) hα0src
      (p := α 0) (w := u) ?_ ?_
    · intro s hs1 hs2
      congr 1
      rw [hφid s (by linarith only [hs1, hL, min_le_left (1:ℝ) ε])
        (by linarith only [hs2, hL])]
      rw [hcq, add_assoc, ← add_smul, show L + (s - L) = s from by ring]
    · intro s hs1 hs2
      have h2 : s - L ≤ ε := by
        have h := min_le_right (1:ℝ) ε
        linarith only [hs2, h]
      exact (hαgerm (s - L) (by linarith only [hs1]) h2).1
  · exact glue_contMDiffAt_right hαsm hgt

/-- **The glued piece is injective on `[0, L+1]`.**  Within each half by injectivity of the chart
line resp. of `α`; across the junction by `hsep`, which forces the junction parameter of `α` to be
`0`, hence the junction to be `L`, and then the chart-line argument comparison. -/
lemma glue_injOn {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) {σ : M} (hσ : σ ∈ c.source)
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hφid : ∀ t : ℝ, -1 < t → t < L + 1 → φ t = t)
    (hφtgt : ∀ t : ℝ, c σ + φ t • u ∈ c.target)
    {α : ℝ → M} (hαinj : Set.InjOn α (Set.Icc (0:ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hα0 : α 0 = c.symm (c σ + L • u))
    (hαgerm : ∀ s : ℝ, 0 ≤ s → s ≤ ε →
      α s = c.symm (c (α 0) + s • u) ∧ c (α 0) + s • u ∈ c.target)
    (hsep : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 →
      α s ∈ c.symm '' ((fun t : ℝ => c σ + t • u) '' Set.Icc (0:ℝ) L) → α s = α 0) :
    Set.InjOn (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L))
      (Set.Icc (0:ℝ) (L + 1)) := by
  have htgtL : ∀ t : ℝ, 0 ≤ t → t ≤ L → c σ + t • u ∈ c.target := by
    intro t ht0 htL
    have h := hφtgt t
    rwa [hφid t (by linarith) (by linarith)] at h
  have hval : ∀ s : ℝ, 0 ≤ s → s ≤ L + 1 →
      (if s ≤ L then c.symm (c σ + φ s • u) else α (s - L))
        = (if s ≤ L then c.symm (c σ + s • u) else α (s - L)) := by
    intro s hs0 hs1
    by_cases hsL : s ≤ L
    · rw [if_pos hsL, if_pos hsL]
      congr 1
      have hs_gt : -1 < s := by linarith only [hs0]
      have hs_lt : s < L + 1 := lt_of_le_of_lt hsL (lt_add_one L)
      rw [hφid s hs_gt hs_lt]
    · rw [if_neg hsL, if_neg hsL]
  have hchart : ∀ s t : ℝ, 0 ≤ s → s ≤ L → 0 ≤ t → t ≤ L →
      c.symm (c σ + s • u) = c.symm (c σ + t • u) → s = t := by
    intro s t hs0 hsL' ht0 htL' heq
    have h1 : c σ + s • u = c σ + t • u :=
      c.symm.injOn (htgtL s hs0 hsL') (htgtL t ht0 htL') heq
    have h2 : (s - t) • u = 0 := by
      have h3 : s • u = t • u := add_left_cancel h1
      rw [sub_smul, h3, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · linarith only [h]
    · exact absurd h hu
  intro s hs t ht hst
  change (if s ≤ L then c.symm (c σ + φ s • u) else α (s - L))
      = (if t ≤ L then c.symm (c σ + φ t • u) else α (t - L)) at hst
  rw [hval s hs.1 (by linarith only [hs.2])] at hst
  rw [hval t ht.1 (by linarith only [ht.2])] at hst
  by_cases hsL : s ≤ L
  · by_cases htL : t ≤ L
    · rw [if_pos hsL] at hst
      rw [if_pos htL] at hst
      exact hchart s t hs.1 hsL ht.1 htL hst
    · rw [if_pos hsL] at hst
      rw [if_neg htL] at hst
      have hLt : L < t := not_le.mp htL
      have hmem : c.symm (c σ + s • u) ∈
          c.symm '' ((fun t : ℝ => c σ + t • u) '' Set.Icc (0:ℝ) L) :=
        ⟨c σ + s • u, ⟨s, ⟨hs.1, hsL⟩, rfl⟩, rfl⟩
      have h0 : α (t - L) = α 0 :=
        hsep (t - L) ⟨by linarith only [hLt], by linarith only [ht.2]⟩ (by rw [← hst]; exact hmem)
      have htz : t - L = 0 :=
        hαinj ⟨by linarith only [hLt], by linarith only [ht.2]⟩ ⟨le_rfl, zero_le_one⟩ h0
      have ht_eq : t = L := by linarith only [htz]
      have hs_eq : s = L := hchart s L hs.1 hsL hL.le le_rfl (by rw [hst, h0, hα0])
      rw [hs_eq, ht_eq]
  · by_cases htL : t ≤ L
    · rw [if_neg hsL] at hst
      rw [if_pos htL] at hst
      have hLs : L < s := not_le.mp hsL
      have hmem : c.symm (c σ + t • u) ∈
          c.symm '' ((fun t : ℝ => c σ + t • u) '' Set.Icc (0:ℝ) L) :=
        ⟨c σ + t • u, ⟨t, ⟨ht.1, htL⟩, rfl⟩, rfl⟩
      have h0 : α (s - L) = α 0 :=
        hsep (s - L) ⟨by linarith only [hLs], by linarith only [hs.2]⟩ (by rw [hst]; exact hmem)
      have hsz : s - L = 0 :=
        hαinj ⟨by linarith only [hLs], by linarith only [hs.2]⟩ ⟨le_rfl, zero_le_one⟩ h0
      have hs_eq : s = L := by linarith only [hsz]
      have ht_eq : t = L := hchart t L ht.1 htL hL.le le_rfl (by rw [← hst, h0, hα0])
      rw [hs_eq, ht_eq]
    · rw [if_neg hsL] at hst
      rw [if_neg htL] at hst
      have hLs : L < s := not_le.mp hsL
      have hLt : L < t := not_le.mp htL
      have harg : s - L = t - L :=
        hαinj ⟨by linarith only [hLs], by linarith only [hs.2]⟩
          ⟨by linarith only [hLt], by linarith only [ht.2]⟩ hst
      linarith only [harg]

/-- **The `if` clause of the glued piece past the junction.**  For `t ≥ L` the piece is the middle
arc evaluated at `t - L`; at `t = L` this is `hα0` (and `φ L = L`). -/
lemma glue_value_if {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {σ : M} {u : EuclideanSpace ℝ (Fin n)} {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hφid : ∀ t : ℝ, -1 < t → t < L + 1 → φ t = t)
    {α : ℝ → M} (hα0 : α 0 = c.symm (c σ + L • u)) :
    ∀ t : ℝ, L ≤ t →
      (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) t = α (t - L) := by
  intro t htL
  change (if t ≤ L then c.symm (c σ + φ t • u) else α (t - L)) = α (t - L)
  rcases eq_or_lt_of_le htL with h | h
  · subst h
    rw [if_pos le_rfl, hφid L (by linarith) (by linarith)]
    rw [sub_self]
    exact hα0.symm
  · rw [if_neg (not_le.mpr h)]

/-- **`P 0 = σ`.** -/
lemma glue_value_zero {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {σ : M} (hσ : σ ∈ c.source) {u : EuclideanSpace ℝ (Fin n)} {φ : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hφid : ∀ t : ℝ, -1 < t → t < L + 1 → φ t = t) {α : ℝ → M} :
    (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) 0 = σ := by
  change (if (0:ℝ) ≤ L then c.symm (c σ + φ 0 • u) else α (0 - L)) = σ
  rw [if_pos hL.le]
  rw [show φ 0 = (0:ℝ) from hφid 0 (by norm_num) (by linarith), zero_smul, add_zero]
  exact c.left_inv hσ

/-- **`P L = α 0`.** -/
lemma glue_value_L {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {σ : M} {u : EuclideanSpace ℝ (Fin n)} {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hφid : ∀ t : ℝ, -1 < t → t < L + 1 → φ t = t) {α : ℝ → M}
    (hα0 : α 0 = c.symm (c σ + L • u)) :
    (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) L = α 0 := by
  change (if L ≤ L then c.symm (c σ + φ L • u) else α (L - L)) = α 0
  rw [if_pos le_rfl, hφid L (by linarith) (by linarith)]
  exact hα0.symm

/-- **`P (L + 1) = α 1`.** -/
lemma glue_value_Lp1 {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {σ : M} {u : EuclideanSpace ℝ (Fin n)} {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    {α : ℝ → M} :
    (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) (L + 1) = α 1 := by
  change (if L + 1 ≤ L then c.symm (c σ + φ (L + 1) • u) else α (L + 1 - L)) = α 1
  rw [if_neg (not_le.mpr (lt_add_one L))]
  congr 1
  ring

/-- **The germ clause: on `[0,L]` the piece is the plain chart line** (here `φ` is the identity). -/
lemma glue_value_germ {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {σ : M} {u : EuclideanSpace ℝ (Fin n)} {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hφid : ∀ t : ℝ, -1 < t → t < L + 1 → φ t = t) {α : ℝ → M} :
    ∀ t : ℝ, 0 ≤ t → t ≤ L →
      (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) t
        = c.symm (c σ + t • u) := by
  intro t ht0 htL
  change (if t ≤ L then c.symm (c σ + φ t • u) else α (t - L)) = c.symm (c σ + t • u)
  rw [if_pos htL, hφid t (by linarith only [ht0]) (by linarith only [htL])]

/-- **The image clause.**  On `[0,L]` the piece is the germ segment (`glue_value_germ`), past the
junction it is the middle arc (`glue_value_if`); both are contained in `X` by hypothesis. -/
lemma glue_image_subset {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {σ : M} {u : EuclideanSpace ℝ (Fin n)} {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hφid : ∀ t : ℝ, -1 < t → t < L + 1 → φ t = t) {α : ℝ → M}
    (hα0 : α 0 = c.symm (c σ + L • u))
    {X : Set M} (hXg : c.symm '' ((fun t : ℝ => c σ + t • u) '' Set.Icc (0:ℝ) L) ⊆ X)
    (hXm : α '' Set.Icc (0:ℝ) 1 ⊆ X) :
    ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) (L + 1) →
      (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) t ∈ X := by
  intro t ht
  by_cases htL : t ≤ L
  · change (if t ≤ L then c.symm (c σ + φ t • u) else α (t - L)) ∈ X
    rw [if_pos htL, hφid t (by linarith only [ht.1]) (by linarith only [htL])]
    exact hXg ⟨c σ + t • u, ⟨t, ⟨ht.1, htL⟩, rfl⟩, rfl⟩
  · have hLt : L < t := not_le.mp htL
    change (if t ≤ L then c.symm (c σ + φ t • u) else α (t - L)) ∈ X
    rw [if_neg htL]
    exact hXm ⟨t - L, ⟨by linarith only [hLt], by linarith only [ht.2]⟩, rfl⟩

section GlueImmersionOption

set_option backward.isDefEq.respectTransparency false

/-- **The glued piece is an immersion on `[0, L+1]`.**

Strictly left of the junction the piece agrees with the chart line `s ↦ c.symm (c σ + s • u)` (the
clamp `φ` is the identity there), at the junction with the *same* chart line (two-sided agreement
from `hφid`/`hαgerm`), and past the junction it is the middle arc composed with the shift: the
chain rule with `germGlue.mfderiv_sub_eq_id` transports `hαimm`. -/
lemma glue_immersion {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) {σ : M} (hσ : σ ∈ c.source)
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) {L : ℝ} (hL : 0 < L)
    {φ : ℝ → ℝ} (hφid : ∀ t : ℝ, -1 < t → t < L + 1 → φ t = t)
    (hφtgt : ∀ t : ℝ, c σ + φ t • u ∈ c.target)
    {α : ℝ → M} (hαsm : ContMDiff MCreal (MC n) smoothOrder α)
    (hαimm : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Function.Injective (mfderiv MCreal (MC n) α t))
    {ε : ℝ} (hε : 0 < ε) (hα0 : α 0 = c.symm (c σ + L • u))
    (hαgerm : ∀ s : ℝ, 0 ≤ s → s ≤ ε →
      α s = c.symm (c (α 0) + s • u) ∧ c (α 0) + s • u ∈ c.target) :
    ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) (L + 1) →
      Function.Injective (mfderiv MCreal (MC n)
        (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) t) := by
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hφL : φ L = L := hφid L (by linarith) (by linarith)
  have hctgt : c σ + L • u ∈ c.target := by rw [← hφL]; exact hφtgt L
  have hcq : c (α 0) = c σ + L • u := by rw [hα0, c.right_inv hctgt]
  have hmin : 0 < min (1:ℝ) ε := lt_min one_pos hε
  have hTopen : IsOpen {s : ℝ | c σ + s • u ∈ c.target} := by
    apply IsOpen.preimage _ c.open_target
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hImm : ∀ t : ℝ, c σ + t • u ∈ c.target →
      Function.Injective (mfderiv MCreal (MC n) (fun s : ℝ => c.symm (c σ + s • u)) t) :=
    (isImmersion_chartLine c hc hσ hu hTopen (fun t ht => ht)).2
  have hvalL : ∀ t : ℝ, 0 ≤ t → t < L →
      (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) =ᶠ[𝓝 t]
        (fun s : ℝ => c.symm (c σ + s • u)) := by
    intro t ht0 htL
    filter_upwards [isOpen_Iio.mem_nhds htL,
      isOpen_Ioo.mem_nhds (show t ∈ Set.Ioo (-1:ℝ) (L + 1) from ⟨by linarith, by linarith⟩)]
      with s hs1 hs2
    change (if s ≤ L then c.symm (c σ + φ s • u) else α (s - L))
      = c.symm (c σ + s • u)
    rw [if_pos (le_of_lt hs1), hφid s hs2.1 hs2.2]
  have hvalM : (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) =ᶠ[𝓝 L]
      (fun s : ℝ => c.symm (c σ + s • u)) := by
    filter_upwards [Ioo_mem_nhds (show L - min 1 ε < L by linarith)
      (show L < L + min 1 ε by linarith)] with s hs
    have hs1 : -1 < s := by
      have h := min_le_left (1:ℝ) ε; linarith only [hs.1, h, hL]
    have hs2 : s < L + 1 := by
      have h := min_le_left (1:ℝ) ε; linarith only [hs.2, h]
    change (if s ≤ L then c.symm (c σ + φ s • u) else α (s - L))
      = c.symm (c σ + s • u)
    by_cases hsL : s ≤ L
    · rw [if_pos hsL, hφid s hs1 hs2]
    · rw [if_neg hsL]
      have hsE : s - L ≤ ε := by
        have h := min_le_right (1:ℝ) ε; linarith only [hs.2, h]
      rw [(hαgerm (s - L) (by linarith) hsE).1]
      congr 1
      rw [hcq, add_assoc, ← add_smul, show L + (s - L) = s from by ring]
  have hvalR : ∀ t : ℝ, L < t →
      (fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L)) =ᶠ[𝓝 t]
        (α ∘ (fun s : ℝ => s - L)) := by
    intro t ht
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    change (if s ≤ L then c.symm (c σ + φ s • u) else α (s - L))
      = α ((fun s : ℝ => s - L) s)
    rw [if_neg (not_le.mpr hs)]
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ L + 1 := ht.2
  by_cases htLt : t < L
  · rw [Filter.EventuallyEq.mfderiv_eq_v433 (hvalL t ht0 htLt)]
    exact hImm t (by
      have h := hφtgt t
      rwa [hφid t (by linarith only [ht0]) (by linarith only [htLt, hL])] at h)
  · have hLt : L ≤ t := not_lt.mp htLt
    rcases eq_or_lt_of_le hLt with heq | hgt
    · rw [heq.symm]
      rw [Filter.EventuallyEq.mfderiv_eq_v433 hvalM]
      exact hImm L hctgt
    · have hmdα : MDifferentiableAt MCreal (MC n) α (t - L) :=
        (hαsm (t - L)).mdifferentiableAt hn0
      have hmdsh : MDifferentiableAt MCreal MCreal (fun s : ℝ => s - L) t := by
        have h : ContMDiffAt MCreal MCreal smoothOrder (fun s : ℝ => s - L) t :=
          (contMDiffAt_id (x := t) (n := (∞ : WithTop ℕ∞))).sub
            (contMDiffAt_const (x := t) (n := (∞ : WithTop ℕ∞)))
        exact h.mdifferentiableAt hn0
      have hchain := mfderiv_comp (I := MCreal) (I' := MCreal) (I'' := MC n) t
        (g := α) (f := fun s : ℝ => s - L) hmdα hmdsh
      rw [Filter.EventuallyEq.mfderiv_eq_v433 (hvalR t hgt), hchain]
      exact (hαimm (t - L) ⟨by linarith only [hgt], by linarith only [ht1]⟩).comp
        (injective_mfderiv_sub L t)

end GlueImmersionOption

/-- **The initial germ glued to a middle arc.**  See the module header. -/
theorem germ_middle_glue {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) {σ : M} (hσ : σ ∈ c.source)
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) {L : ℝ} (hL : 0 < L)
    {φ : ℝ → ℝ} (hφsm : ∀ k : ℕ∞, ContDiff ℝ (k : WithTop ℕ∞) φ) (hφid : ∀ t : ℝ, -1 < t → t < L + 1 → φ t = t)
    (hφtgt : ∀ t : ℝ, c σ + φ t • u ∈ c.target)
    {α : ℝ → M} (hαsm : ContMDiff MCreal (MC n) smoothOrder α)
    (hαimm : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Function.Injective (mfderiv MCreal (MC n) α t))
    (hαinj : Set.InjOn α (Set.Icc (0:ℝ) 1))
    (hα0 : α 0 = c.symm (c σ + L • u))
    {ε : ℝ} (hε : 0 < ε)
    (hαgerm : ∀ s : ℝ, 0 ≤ s → s ≤ ε →
      α s = c.symm (c (α 0) + s • u) ∧ c (α 0) + s • u ∈ c.target)
    (hsep : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 →
      α s ∈ c.symm '' ((fun t : ℝ => c σ + t • u) '' Set.Icc (0:ℝ) L) → α s = α 0)
    {X : Set M} (hXg : c.symm '' ((fun t : ℝ => c σ + t • u) '' Set.Icc (0:ℝ) L) ⊆ X)
    (hXm : α '' Set.Icc (0:ℝ) 1 ⊆ X) :
    ∃ P : ℝ → M, ContMDiff MCreal (MC n) smoothOrder P ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) (L + 1) → Function.Injective (mfderiv MCreal (MC n) P t)) ∧
      Set.InjOn P (Set.Icc (0:ℝ) (L + 1)) ∧
      P 0 = σ ∧ P L = α 0 ∧ P (L + 1) = α 1 ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ L → P t = c.symm (c σ + t • u)) ∧
      (∀ t : ℝ, L ≤ t → P t = α (t - L)) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) (L + 1) → P t ∈ X) := by
  refine ⟨fun s : ℝ => if s ≤ L then c.symm (c σ + φ s • u) else α (s - L),
    glue_contMDiff hc hσ hL hφsm hφid hφtgt hαsm hε hα0 hαgerm,
    glue_immersion hc hσ hu hL hφid hφtgt hαsm hαimm hε hα0 hαgerm,
    glue_injOn hc hσ hu hL hφid hφtgt hαinj hε hα0 hαgerm hsep,
    glue_value_zero hσ hL hφid,
    glue_value_L hL hφid hα0,
    glue_value_Lp1 hL,
    glue_value_germ hL hφid,
    glue_value_if hL hφid hα0,
    glue_image_subset hL hφid hα0 hXg hXm⟩

end

end Work.Noncompact.CompressionTube
