import Mathlib
import Submission.Work.Drive.Mono.OneEventNDDefs
import Submission.Work.Drive.Mono.OneEvBadAux
import Submission.Work.Drive.Mono.projectionNull_localDimH_two
import Submission.Work.Drive.Mono.exists_critChart
import Submission.Work.Drive.Mono.exists_faceChart
import Submission.Work.Drive.Mono.exists_cornerChart
import Submission.Work.Drive.Mono.localStructure_opposite
import Submission.Work.Drive.Mono.localStructure_same
import Submission.Work.Drive.Mono.localStructure_one

/-!
# `Work.Drive.Mono.oneEvBad_null3`

The bad set of "one event per level" is null in `ℝ³ = (u, h, τ)`.  The auxiliary vocabulary of the
proof lives in `Submission.Work.Drive.Mono.OneEvBadAux`: the event charts `EvChart` (a `C¹`
parametrisation of the events of one type by the tilt and the slab coordinate) and `CritChart` (the
continuation of a nondegenerate critical point), together with the local structure lemmas
(`localStructure_opposite`, `localStructure_same`, `localStructure_one`) and the measure-theoretic
assembly (`projectionNull_localDimH_two`).
-/

open LeanEval.KnotTheory.PardonDistortion Set Filter
open scoped RealInnerProductSpace ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-! ## The three clauses of `NDEvent`, and the witness space -/

/-- The first clause of `NDEvent` (a nondegenerate critical point inside the slab). -/
def ND1 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3)
    (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (p : ℝ × ℝ) : Prop :=
  Work.Drive.Final.IsEvent ψ s c σ u v h ℓ p ∧
    |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| < h ∧
    Function.Injective (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ)) p)

/-- The second clause of `NDEvent` (a tangency of the level with a slab face). -/
def ND2 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3)
    (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (p : ℝ × ℝ) : Prop :=
  Work.Drive.Final.IsFaceEvent ψ s c σ u v h ℓ p ∧
    fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0 ∧
    fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p ≠ 0 ∧
    ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p =
        t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p →
      ∀ w : ℝ × ℝ, w ≠ 0 → fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p w = 0 →
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
          Work.Drive.EpsForm.sweepHeight ψ ℓ q
            - t * Work.Drive.Final.slabFnPar ψ c u v q)) p) w w ≠ 0

/-- The third clause of `NDEvent` (a corner event on the box sphere). -/
def ND3 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3)
    (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (p : ℝ × ℝ) : Prop :=
  Work.Drive.Final.IsCornerEvent ψ s c σ u v h p ∧
    ∃ i : Fin 3, i ≠ 2 ∧
      (∀ j : Fin 3, j ≠ i →
        |(Work.BoxShrink.Pinch.par ψ p) (σ j) - c (σ j)| < Submission.boxSide j * s) ∧
      (fderiv ℝ (fun q : ℝ × ℝ =>
        ((Work.BoxShrink.Pinch.par ψ q) (σ i), inner ℝ v (Work.BoxShrink.Pinch.par ψ q))) p).IsInvertible ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p

/-- `NDEvent` is the disjunction of its three clauses. -/
theorem ndEvent_iff (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (p : ℝ × ℝ) :
    NDEvent ψ s c σ u v h ℓ p ↔
      ND1 ψ s c σ u v h ℓ p ∨ ND2 ψ s c σ u v h ℓ p ∨ ND3 ψ s c σ u v h ℓ p :=
  Iff.rfl

/-- **The witness predicate**: `w = (u,h,τ,q,q')` is a pair of distinct non-degenerate events of the
swept level `ℓ_τ`, not both critical points. -/
def WitBad (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (w : Wit) : Prop :=
  NDEvent ψ s c σ (wU w) v (wH w) ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf (wT w) a₀ b₀))
      (wQ w) ∧
    NDEvent ψ s c σ (wU w) v (wH w) ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf (wT w) a₀ b₀))
      (wQ' w) ∧
    sH ψ a₀ b₀ (wT w) (wQ w) = sH ψ a₀ b₀ (wT w) (wQ' w) ∧
    Work.BoxShrink.Pinch.par ψ (wQ w) ≠ Work.BoxShrink.Pinch.par ψ (wQ' w) ∧
    ¬ (Work.Drive.Final.IsEvent ψ s c σ (wU w) v (wH w)
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf (wT w) a₀ b₀)) (wQ w) ∧
       Work.Drive.Final.IsEvent ψ s c σ (wU w) v (wH w)
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf (wT w) a₀ b₀)) (wQ' w))

/-- The bad set of `OneEvBad` is the projection of the witness set. -/
theorem oneEvBad_eq_proj (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : R3) :
    {x : ℝ × ℝ × ℝ | OneEvBad ψ s c σ v a₀ b₀ x.1 x.2.1 x.2.2}
      = witProj '' {w : Wit | WitBad ψ s c σ v a₀ b₀ w} := by
  ext x
  constructor
  · rintro ⟨p, p', h1, h2, hlev, hne, hnot⟩
    refine ⟨wit x.1 x.2.1 x.2.2 p p', ⟨h1, h2, ?_, hne, hnot⟩, rfl⟩
    simpa only [sH, innerSL_apply_apply, wT_wit, wQ_wit, wQ'_wit] using hlev
  · rintro ⟨w, hw, rfl⟩
    exact ⟨wQ w, wQ' w, hw.1, hw.2.1,
      by simpa only [sH, innerSL_apply_apply, witProj, wU, wH, wT, wQ, wQ'] using hw.2.2.1,
      hw.2.2.2.1, hw.2.2.2.2⟩

/-! ## The clauses of `NDEvent`, read on the witness space -/

/-- The level functional of the tilt `τ`: `ℓ_τ = ⟪dirOf τ a₀ b₀, ·⟫`. -/
def levOf (a₀ b₀ : R3) (τ : ℝ) : R3 →L[ℝ] ℝ :=
  (innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)

@[simp] theorem levOf_apply (a₀ b₀ : R3) (τ : ℝ) :
    levOf a₀ b₀ τ = (innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀) := rfl

/-- `sH` is the sweep height of the tilt `τ`, in the `levOf` spelling. -/
theorem sH_eq_sweepHeight_levOf (ψ : Submission.Diffeo) (a₀ b₀ : R3) (τ : ℝ) :
    sH ψ a₀ b₀ τ = Work.Drive.EpsForm.sweepHeight ψ (levOf a₀ b₀ τ) :=
  sH_eq_sweepHeight ψ a₀ b₀ τ

/-- The first clause `ND1` of `NDEvent`, read at the first point of a witness. -/
def C1 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (w : Wit) : Prop :=
  ND1 ψ s c σ (wU w) v (wH w) (levOf a₀ b₀ (wT w)) (wQ w)

/-- The second clause `ND2` of `NDEvent`, read at the first point of a witness. -/
def C2 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (w : Wit) : Prop :=
  ND2 ψ s c σ (wU w) v (wH w) (levOf a₀ b₀ (wT w)) (wQ w)

/-- The third clause `ND3` of `NDEvent`, read at the first point of a witness. -/
def C3 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (w : Wit) : Prop :=
  ND3 ψ s c σ (wU w) v (wH w) (levOf a₀ b₀ (wT w)) (wQ w)

/-- The first clause of `NDEvent` at the second point of a witness. -/
def C1' (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (w : Wit) : Prop :=
  ND1 ψ s c σ (wU w) v (wH w) (levOf a₀ b₀ (wT w)) (wQ' w)

/-- The second clause of `NDEvent` at the second point of a witness. -/
def C2' (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (w : Wit) : Prop :=
  ND2 ψ s c σ (wU w) v (wH w) (levOf a₀ b₀ (wT w)) (wQ' w)

/-- The third clause of `NDEvent` at the second point of a witness. -/
def C3' (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (w : Wit) : Prop :=
  ND3 ψ s c σ (wU w) v (wH w) (levOf a₀ b₀ (wT w)) (wQ' w)

/-- The two events of a witness have the same level. -/
def LevW (ψ : Submission.Diffeo) (a₀ b₀ : R3) (w : Wit) : Prop :=
  sH ψ a₀ b₀ (wT w) (wQ w) = sH ψ a₀ b₀ (wT w) (wQ' w)

/-- The two surface points of a witness are distinct. -/
def NeW (ψ : Submission.Diffeo) (w : Wit) : Prop :=
  Work.BoxShrink.Pinch.par ψ (wQ w) ≠ Work.BoxShrink.Pinch.par ψ (wQ' w)

/-- Not both points of the witness are critical points (`IsEvent`). -/
def NotBothW (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (w : Wit) : Prop :=
  ¬ (Work.Drive.Final.IsEvent ψ s c σ (wU w) v (wH w) (levOf a₀ b₀ (wT w)) (wQ w) ∧
     Work.Drive.Final.IsEvent ψ s c σ (wU w) v (wH w) (levOf a₀ b₀ (wT w)) (wQ' w))

/-- `WitBad` is the disjunction of the three clauses at each of the two points. -/
theorem witBad_iff (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : R3) (w : Wit) :
    WitBad ψ s c σ v a₀ b₀ w ↔
      (C1 ψ s c σ v a₀ b₀ w ∨ C2 ψ s c σ v a₀ b₀ w ∨ C3 ψ s c σ v a₀ b₀ w) ∧
      (C1' ψ s c σ v a₀ b₀ w ∨ C2' ψ s c σ v a₀ b₀ w ∨ C3' ψ s c σ v a₀ b₀ w) ∧
      LevW ψ a₀ b₀ w ∧ NeW ψ w ∧ NotBothW ψ s c σ v a₀ b₀ w := by
  unfold WitBad C1 C2 C3 C1' C2' C3' LevW NeW NotBothW NDEvent
  exact Iff.rfl

/-! ## Signs and slab coordinates -/

/-- From `|x| = h` extract a sign: `x = η * h` with `η = ±1`. -/
theorem exists_sign_of_abs_eq {x h : ℝ} (hx : |x| = h) :
    ∃ η : ℝ, (η = 1 ∨ η = -1) ∧ x = η * h := by
  rcases lt_or_ge x 0 with hx0 | hx0
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [abs_of_neg hx0] at hx
    linarith
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [abs_of_nonneg hx0] at hx
    linarith

/-- The slab equation at the first point of a witness. -/
def sEq1 (ψ : Submission.Diffeo) (v c : R3) (η : ℝ) (w : Wit) : Prop :=
  hFn ψ v (wQ w) = (inner ℝ v c + wU w) + η * wH w

/-- The slab equation at the second point of a witness. -/
def sEq2 (ψ : Submission.Diffeo) (v c : R3) (η : ℝ) (w : Wit) : Prop :=
  hFn ψ v (wQ' w) = (inner ℝ v c + wU w) + η * wH w

/-- A clause-2 (face) witness point has a slab sign. -/
theorem exists_eta_of_C2 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {w : Wit} (h : C2 ψ s c σ v a₀ b₀ w) :
    ∃ η : ℝ, (η = 1 ∨ η = -1) ∧ sEq1 ψ v c η w := by
  obtain ⟨hface, -, -, -⟩ := h
  have h1 : |hFn ψ v (wQ w) - (inner ℝ v c + wU w)| = wH w := by
    have h2 := hface.2.1
    simp only [Work.Drive.Final.slabFn, hFn, Work.BoxShrink.Pinch.par_apply] at h2
    exact h2
  obtain ⟨η, hη, hx⟩ := exists_sign_of_abs_eq h1
  refine ⟨η, hη, ?_⟩
  show hFn ψ v (wQ w) = (inner ℝ v c + wU w) + η * wH w
  linarith

/-- A clause-2 (face) witness point satisfies the tangency `Tangent`. -/
theorem tangent_of_C2 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {w : Wit} (h : C2 ψ s c σ v a₀ b₀ w) :
    Tangent ψ v a₀ b₀ (wT w) (wQ w) := by
  obtain ⟨hface, -, -, -⟩ := h
  obtain ⟨t, ht⟩ := hface.2.2
  refine ⟨t, ?_⟩
  show fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ (wT w) x) (wQ w)
    = t • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) (wQ w)
  have hsw : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ (levOf a₀ b₀ (wT w))) (wQ w)
      = fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ (wT w) x) (wQ w) := by
    rw [← sH_eq_sweepHeight_levOf ψ a₀ b₀ (wT w)]
  have hsl : fderiv ℝ (Work.Drive.Final.slabFnPar ψ c (wU w) v) (wQ w)
      = fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) (wQ w) :=
    fderiv_slabFnPar_eq ψ c (wU w) v (wQ w)
  rw [← hsw, ht, hsl]

/-- A clause-1 (critical point) witness point carries a critical-point chart. -/
theorem critChart_of_C1 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) {w : Wit}
    (h : C1 ψ s c σ v a₀ b₀ w) :
    Nonempty (CritChart ψ a₀ b₀ (wT w) (wQ w)) := by
  obtain ⟨hEv, hlt, hinj⟩ := h
  have h2 : (fun x : ℝ × ℝ => sH ψ a₀ b₀ (wT w) x)
      = Work.Drive.EpsForm.sweepHeight ψ (levOf a₀ b₀ (wT w)) :=
    sH_eq_sweepHeight_levOf ψ a₀ b₀ (wT w)
  refine exists_critChart ha hb hab ψ ?_ ?_
  · have h1 : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ (levOf a₀ b₀ (wT w))) (wQ w) = 0 :=
      hEv.2.2
    rw [h2]
    exact h1
  · rw [h2]
    exact hinj

/-- A corner event whose active face is the `σ i`-th has its `σ i`-th coordinate at the box bound. -/
theorem cornerBound {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {p : R3} {i : Fin 3}
    (hnorm : Submission.boxNorm c σ p = s)
    (hstrict : ∀ j : Fin 3, j ≠ i → |p (σ j) - c (σ j)| < Submission.boxSide j * s) :
    |p (σ i) - c (σ i)| = Submission.boxSide i * s := by
  have hle : ∀ j : Fin 3, |p (σ j) - c (σ j)| / Submission.boxSide j ≤ s := by
    intro j
    rw [← hnorm, Submission.boxNorm]
    fin_cases j <;> simp
  have hlt : ∀ j : Fin 3, j ≠ i →
      |p (σ j) - c (σ j)| / Submission.boxSide j < s := by
    intro j hj
    rw [div_lt_iff₀ (Submission.boxSide_pos j), mul_comm]
    exact hstrict j hj
  have hmain : |p (σ i) - c (σ i)| / Submission.boxSide i = s := by
    by_contra hne
    have h0 : |p (σ i) - c (σ i)| / Submission.boxSide i < s :=
      lt_of_le_of_ne (hle i) hne
    have hbox : Submission.boxNorm c σ p < s := by
      rw [Submission.boxNorm]
      fin_cases i
      · exact max_lt (max_lt h0 (hlt 1 (by decide))) (hlt 2 (by decide))
      · exact max_lt (max_lt (hlt 0 (by decide)) h0) (hlt 2 (by decide))
      · exact max_lt (max_lt (hlt 0 (by decide)) (hlt 1 (by decide))) h0
    rw [hnorm] at hbox
    exact lt_irrefl s hbox
  have hfin := (div_eq_iff (Submission.boxSide_pos i).ne').mp hmain
  rw [mul_comm] at hfin
  exact hfin

/-- The corner data at the first point of a witness: the active index `i`, the sign `ε` of the
active coordinate and the whole clause-3 information. -/
def CorW (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (i : Fin 3) (ε : ℝ) (w : Wit) : Prop :=
  i ≠ 2 ∧
  (∀ j : Fin 3, j ≠ i → |(Work.BoxShrink.Pinch.par ψ (wQ w)) (σ j) - c (σ j)|
    < Submission.boxSide j * s) ∧
  (fderiv ℝ (fun q : ℝ × ℝ => ((Work.BoxShrink.Pinch.par ψ q) (σ i),
      inner ℝ v (Work.BoxShrink.Pinch.par ψ q))) (wQ w)).IsInvertible ∧
  (∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ (levOf a₀ b₀ (wT w))) (wQ w) ≠
    t • fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) (wQ w)) ∧
  Work.Drive.Final.IsCornerEvent ψ s c σ (wU w) v (wH w) (wQ w) ∧
  (Work.BoxShrink.Pinch.par ψ (wQ w)) (σ i) = c (σ i) + ε * (Submission.boxSide i * s)

/-- The corner data at the second point of a witness. -/
def CorW' (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (i : Fin 3) (ε : ℝ) (w : Wit) : Prop :=
  i ≠ 2 ∧
  (∀ j : Fin 3, j ≠ i → |(Work.BoxShrink.Pinch.par ψ (wQ' w)) (σ j) - c (σ j)|
    < Submission.boxSide j * s) ∧
  (fderiv ℝ (fun q : ℝ × ℝ => ((Work.BoxShrink.Pinch.par ψ q) (σ i),
      inner ℝ v (Work.BoxShrink.Pinch.par ψ q))) (wQ' w)).IsInvertible ∧
  (∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ (levOf a₀ b₀ (wT w))) (wQ' w) ≠
    t • fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) (wQ' w)) ∧
  Work.Drive.Final.IsCornerEvent ψ s c σ (wU w) v (wH w) (wQ' w) ∧
  (Work.BoxShrink.Pinch.par ψ (wQ' w)) (σ i) = c (σ i) + ε * (Submission.boxSide i * s)

/-- A clause-3 witness point yields corner data with the bound equation. -/
theorem exists_corner_data_of_C3 {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v a₀ b₀ : R3} {w : Wit} (h : C3 ψ s c σ v a₀ b₀ w) :
    ∃ i ε, (ε = 1 ∨ ε = -1) ∧ CorW ψ s c σ v a₀ b₀ i ε w := by
  obtain ⟨hcorner, i, hi2, hstrict, hinv, hnt⟩ := h
  have hnorm := hcorner.2.1
  have hb := cornerBound hnorm hstrict
  obtain ⟨ε, hε, hx⟩ := exists_sign_of_abs_eq hb
  refine ⟨i, ε, hε, hi2, hstrict, hinv, hnt, hcorner, ?_⟩
  linarith

/-- A clause-3 witness point has a slab sign. -/
theorem exists_eta_of_C3 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {w : Wit} (h : C3 ψ s c σ v a₀ b₀ w) :
    ∃ η : ℝ, (η = 1 ∨ η = -1) ∧ sEq1 ψ v c η w := by
  obtain ⟨hcorner, -⟩ := h
  have h1 : |hFn ψ v (wQ w) - (inner ℝ v c + wU w)| = wH w := by
    have h2 := hcorner.2.2
    simp only [Work.Drive.Final.slabFn, hFn, Work.BoxShrink.Pinch.par_apply] at h2
    exact h2
  obtain ⟨η, hη, hx⟩ := exists_sign_of_abs_eq h1
  refine ⟨η, hη, ?_⟩
  show hFn ψ v (wQ w) = (inner ℝ v c + wU w) + η * wH w
  linarith

/-! ## The Hessian of `sweepHeight - t · slabFnPar` -/

/-- The second derivative of `F - t·G` is the difference of the second derivatives. -/
theorem fderiv_fderiv_sub_smul {F G : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (t : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => F q - (t • G) q)) p
      = fderiv ℝ (fderiv ℝ F) p - t • fderiv ℝ (fderiv ℝ G) p := by
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdG : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := (contDiff_succ_iff_fderiv.mp hF).2.2
  have hG1 : ContDiff ℝ 1 (fderiv ℝ G) := (contDiff_succ_iff_fderiv.mp hG).2.2
  have hev : (fun q => fderiv ℝ (fun x : ℝ × ℝ => F x - (t • G) x) q) =ᶠ[𝓝 p]
      fun q => fderiv ℝ F q - t • fderiv ℝ G q := by
    filter_upwards with q
    rw [fderiv_fun_sub hdF.differentiableAt (hdG.differentiableAt.const_smul t),
      fderiv_const_smul hdG.differentiableAt t]
  rw [hev.fderiv_eq]
  have h1 : (fun q : ℝ × ℝ => fderiv ℝ F q - t • fderiv ℝ G q)
      = fun q => fderiv ℝ F q - (t • fderiv ℝ G) q := rfl
  rw [h1, fderiv_fun_sub ((hF1.differentiable (by norm_num)).differentiableAt)
    (((hG1.differentiable (by norm_num)).differentiableAt).const_smul t),
    fderiv_const_smul ((hG1.differentiable (by norm_num)).differentiableAt) t]

/-- Adding a constant does not change the second derivative. -/
theorem fderiv_fderiv_add_const' {F : ℝ × ℝ → ℝ} (c : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => F q + c)) p = fderiv ℝ (fderiv ℝ F) p := by
  have h : (fderiv ℝ (fun q : ℝ × ℝ => F q + c)) = fderiv ℝ F := by
    ext1 q
    exact fderiv_add_const c
  rw [h]

/-- **The Hessian of `sweepHeight - t · slabFnPar` in terms of `sH` and `hFn`.** -/
theorem fderiv_fderiv_sweep_sub {ψ : Submission.Diffeo} {a₀ b₀ v c : R3} {u τ t : ℝ}
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (p : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
        Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) q
          - t * Work.Drive.Final.slabFnPar ψ c u v q)) p
      = fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => sH ψ a₀ b₀ τ q)) p
        - t • fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => hFn ψ v q)) p := by
  have hfun : (fun q : ℝ × ℝ =>
        Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) q
          - t * Work.Drive.Final.slabFnPar ψ c u v q)
      = fun q : ℝ × ℝ => (sH ψ a₀ b₀ τ q - (t • hFn ψ v) q) + t * (inner ℝ v c + u) := by
    funext q
    rw [← sH_eq_sweepHeight ψ a₀ b₀ τ, hFn_eq_slabFnPar_add ψ c u v]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, fderiv_fderiv_add_const']
  exact fderiv_fderiv_sub_smul (contDiff_sH_section ha hb hab ψ τ) (contDiff_hFn_two ψ v) t p

/-! ## From the clauses to the charts -/

/-- A face event (with the tangency data in the `sweepHeight`/`slabFnPar` spelling) carries a face
chart. -/
theorem faceChart_of_faceEvent {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) {ψ : Submission.Diffeo} {v : R3} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u h τ : ℝ} {p : ℝ × ℝ}
    (hface : Work.Drive.Final.IsFaceEvent ψ s c σ u v h ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p)
    (hd1 : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) p ≠ 0)
    (hd2 : fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p ≠ 0)
    (hlag : ∀ t : ℝ,
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) p
        = t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p →
      ∀ w : ℝ × ℝ, w ≠ 0 → fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p w = 0 →
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
          Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) q
            - t * Work.Drive.Final.slabFnPar ψ c u v q)) p) w w ≠ 0) :
    Nonempty (Work.Drive.Mono.EvChart ψ v a₀ b₀ (Work.Drive.Mono.Tangent ψ v a₀ b₀) τ
      (Work.Drive.Mono.hFn ψ v p) p) := by
  obtain ⟨-, -, ht⟩ := hface
  obtain ⟨t, ht'⟩ := ht
  have ht2 : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) (Band.dirOf τ a₀ b₀))) p
      = t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p := ht'
  have hmu : t ≠ 0 := by
    intro h0
    exact hd1 (by rw [ht2, h0, zero_smul])
  have htang : fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ x) p
      = t • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) p := by
    rw [← sH_eq_sweepHeight ψ a₀ b₀ τ] at ht'
    rw [fderiv_slabFnPar_eq ψ c u v p] at ht'
    exact ht'
  have hbne : fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) p ≠ 0 := by
    rw [← fderiv_slabFnPar_eq ψ c u v p]
    exact hd2
  refine exists_faceChart ha hb hab ψ v (mu₀ := t) htang hmu hbne ?_
  intro w hw hzero
  have hraw := hlag t ht2 w hw (by rw [fderiv_slabFnPar_eq ψ c u v p]; exact hzero)
  intro h0
  apply hraw
  rw [fderiv_fderiv_sweep_sub ha hb hab p]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact h0

/-- A clause-2 (face) witness point carries a face event chart. -/
theorem faceChart_of_C2 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) {w : Wit}
    (h : C2 ψ s c σ v a₀ b₀ w) :
    Nonempty (EvChart ψ v a₀ b₀ (Tangent ψ v a₀ b₀) (wT w) (hFn ψ v (wQ w)) (wQ w)) := by
  obtain ⟨hface, hd1, hd2, hlag⟩ := h
  exact faceChart_of_faceEvent ha hb hab hface hd1 hd2 hlag

/-- A clause-3 (corner) witness point carries a corner event chart. -/
theorem cornerChart_of_C3 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) {w : Wit}
    (h : C3 ψ s c σ v a₀ b₀ w) :
    ∃ i : Fin 3, Nonempty (EvChart ψ v a₀ b₀
      (fun _ q => (Work.BoxShrink.Pinch.par ψ q) (σ i)
        = (Work.BoxShrink.Pinch.par ψ (wQ w)) (σ i))
      (wT w) (hFn ψ v (wQ w)) (wQ w)) := by
  obtain ⟨-, i, hi2, hstrict, hinv, hnt⟩ := h
  refine ⟨i, exists_cornerChart ha hb hab ψ v σ i hinv ?_⟩
  intro t ht
  apply hnt t
  have h2 : (fun x : ℝ × ℝ => sH ψ a₀ b₀ (wT w) x)
      = Work.Drive.EpsForm.sweepHeight ψ (levOf a₀ b₀ (wT w)) :=
    sH_eq_sweepHeight_levOf ψ a₀ b₀ (wT w)
  rwa [h2] at ht

/-! ## The two-chart local structure -/

/-- **The local structure of a pair of events parametrised by two charts**: near the base point the
bad witnesses are contained in the image of a `C¹` map of two parameters. -/
theorem localStructure_twoCharts {ψ : Submission.Diffeo} {v a₀ b₀ c : R3}
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    {care₁ care₂ : ℝ → ℝ × ℝ → Prop} {τ₀ σ₁₀ σ₂₀ : ℝ} {p₁ p₂ : ℝ × ℝ}
    (C₁ : EvChart ψ v a₀ b₀ care₁ τ₀ σ₁₀ p₁) (C₂ : EvChart ψ v a₀ b₀ care₂ τ₀ σ₂₀ p₂)
    (hc₁ : care₁ τ₀ p₁) (hc₂ : care₂ τ₀ p₂)
    (hσ₁ : σ₁₀ = hFn ψ v p₁) (hσ₂ : σ₂₀ = hFn ψ v p₂)
    {η₁ η₂ : ℝ} (hη₁ : η₁ = 1 ∨ η₁ = -1) (hη₂ : η₂ = 1 ∨ η₂ = -1)
    (hlev : sH ψ a₀ b₀ τ₀ p₁ = sH ψ a₀ b₀ τ₀ p₂)
    (hne : Work.BoxShrink.Pinch.par ψ p₁ ≠ Work.BoxShrink.Pinch.par ψ p₂)
    {u₀ h₀ : ℝ}
    (hu₁ : hFn ψ v p₁ = (inner ℝ v c + u₀) + η₁ * h₀)
    (hu₂ : hFn ψ v p₂ = (inner ℝ v c + u₀) + η₂ * h₀) :
    ∃ (O : Set Wit) (V : Set (ℝ × ℝ)) (φ : ℝ × ℝ → Wit),
      IsOpen O ∧ wit u₀ h₀ τ₀ p₁ p₂ ∈ O ∧ IsOpen V ∧ ContDiffOn ℝ 1 φ V ∧
      {w : Wit | care₁ (wT w) (wQ w) ∧ care₂ (wT w) (wQ' w) ∧
          hFn ψ v (wQ w) = (inner ℝ v c + wU w) + η₁ * wH w ∧
          hFn ψ v (wQ' w) = (inner ℝ v c + wU w) + η₂ * wH w ∧
          sH ψ a₀ b₀ (wT w) (wQ w) = sH ψ a₀ b₀ (wT w) (wQ' w)} ∩ O ⊆ φ '' V := by
  by_cases hη : η₁ = η₂
  · have hσeq : hFn ψ v p₁ = hFn ψ v p₂ := by rw [hu₁, hu₂, hη]
    have hσ₁₂ : σ₂₀ = σ₁₀ := by rw [hσ₁, hσ₂, hσeq]
    have hσ₂' : σ₁₀ = hFn ψ v p₂ := by rw [hσ₁, hσeq]
    have hu₂' : hFn ψ v p₂ = (inner ℝ v c + u₀) + η₁ * h₀ := by rw [hu₂, hη]
    obtain ⟨O, V, φ, hO, hwit, hV, -, hφ, hsub⟩ :=
      localStructure_same ψ v a₀ b₀ c ha hb hab hva hvb C₁ (hσ₁₂ ▸ C₂) hc₁ hc₂
        hη₁ hlev hne hσ₁ hσ₂' hu₁ hu₂'
    refine ⟨O, V, φ, hO, hwit, hV, hφ, ?_⟩
    intro w hw
    rw [Set.mem_inter_iff] at hw
    obtain ⟨hwS, hwO⟩ := hw
    rw [Set.mem_ofPred_eq] at hwS
    obtain ⟨h1, h2, h3, h4, h5⟩ := hwS
    refine hsub ?_
    rw [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨⟨h1, h2, by rw [h3, h4, hη], h3, h5⟩, hwO⟩
  · have hsum : η₁ + η₂ = 0 := by
      rcases hη₁ with h1 | h1 <;> rcases hη₂ with h2 | h2
      · exact absurd (by rw [h1, h2]) hη
      · rw [h1, h2]; norm_num
      · rw [h1, h2]; norm_num
      · exact absurd (by rw [h1, h2]) hη
    obtain ⟨O, V, φ, hO, hwit, hV, -, hφ, hsub⟩ :=
      localStructure_opposite ψ v a₀ b₀ c ha hb hab hva hvb C₁ C₂ hc₁ hc₂
        hη₁ hη₂ hsum hlev hu₁ hu₂
    exact ⟨O, V, φ, hO, hwit, hV, hφ, hsub⟩

/-! ## Swapping the two points of a witness -/

/-- The witness with its two parameter-plane points exchanged. -/
def swapWit (w : Wit) : Wit := wit (wU w) (wH w) (wT w) (wQ' w) (wQ w)

@[simp] theorem wU_swapWit (w : Wit) : wU (swapWit w) = wU w := rfl
@[simp] theorem wH_swapWit (w : Wit) : wH (swapWit w) = wH w := rfl
@[simp] theorem wT_swapWit (w : Wit) : wT (swapWit w) = wT w := rfl
@[simp] theorem wQ_swapWit (w : Wit) : wQ (swapWit w) = wQ' w := rfl
@[simp] theorem wQ'_swapWit (w : Wit) : wQ' (swapWit w) = wQ w := rfl

@[simp] theorem swapWit_swapWit (w : Wit) : swapWit (swapWit w) = w := by
  obtain ⟨a, b, c, d, e⟩ := w
  rfl

/-- Transporting a local structure across the swapping of the two points. -/
theorem swapWit_image_subset {S : Set Wit} {O : Set Wit} {V : Set (ℝ × ℝ)} {φ : ℝ × ℝ → Wit}
    (hsub : S ∩ O ⊆ φ '' V) :
    (swapWit ⁻¹' S) ∩ (swapWit ⁻¹' O) ⊆ (swapWit ∘ φ) '' V := by
  rintro w ⟨hS, hO⟩
  obtain ⟨y, hyV, hy⟩ := hsub ⟨hS, hO⟩
  exact ⟨y, hyV, by rw [Function.comp_apply, hy, swapWit_swapWit]⟩

/-! ## The measure-theoretic assembly -/

/-- A set of witnesses covered by pieces, each with null projection, has null projection. -/
theorem volume_proj_eq_zero_of_cover {ι : Type*} [Countable ι] {W : Set Wit} (P : ι → Set Wit)
    (hcover : W ⊆ ⋃ i, P i)
    (hnull : ∀ i, (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ × ℝ))
      (witProj '' P i) = 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ × ℝ)) (witProj '' W) = 0 := by
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_iUnion_null hnull)
  rintro x ⟨w, hw, rfl⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hw)
  exact mem_iUnion.mpr ⟨i, w, hi, rfl⟩

/-! ## Two more extraction lemmas, at the second point -/

/-- A clause-2 witness point has a slab sign (second point). -/
theorem exists_eta_of_C2' {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {w : Wit} (h : C2' ψ s c σ v a₀ b₀ w) :
    ∃ η : ℝ, (η = 1 ∨ η = -1) ∧ sEq2 ψ v c η w := by
  have h' : C2 ψ s c σ v a₀ b₀ (swapWit w) := h
  have := exists_eta_of_C2 h'
  simpa only [wU_swapWit, wH_swapWit, wQ_swapWit, sEq2, sEq1] using this

/-- A clause-3 witness point yields corner data (second point). -/
theorem exists_corner_data_of_C3' {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v a₀ b₀ : R3} {w : Wit} (h : C3' ψ s c σ v a₀ b₀ w) :
    ∃ i ε, (ε = 1 ∨ ε = -1) ∧ CorW' ψ s c σ v a₀ b₀ i ε w := by
  have h' : C3 ψ s c σ v a₀ b₀ (swapWit w) := h
  obtain ⟨i, ε, hε, hd⟩ := exists_corner_data_of_C3 h'
  exact ⟨i, ε, hε, hd⟩

/-- A clause-1 (critical point) witness point is critical for the sweep height. -/
theorem crit_of_C1 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {w : Wit} (h : C1 ψ s c σ v a₀ b₀ w) :
    fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ (wT w) x) (wQ w) = 0 := by
  have h1 : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ (levOf a₀ b₀ (wT w))) (wQ w) = 0 :=
    h.1.2.2
  have h2 : (fun x : ℝ × ℝ => sH ψ a₀ b₀ (wT w) x)
      = Work.Drive.EpsForm.sweepHeight ψ (levOf a₀ b₀ (wT w)) :=
    sH_eq_sweepHeight_levOf ψ a₀ b₀ (wT w)
  rw [h2]
  exact h1

/-- A clause-1 (critical point) witness point lies strictly inside the slab. -/
theorem slab_lt_of_C1 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {w : Wit} (h : C1 ψ s c σ v a₀ b₀ w) :
    |hFn ψ v (wQ w) - (inner ℝ v c + wU w)| < wH w := by
  have h1 : |Work.Drive.Final.slabFn c (wU w) v (Work.BoxShrink.Pinch.par ψ (wQ w))| < wH w :=
    h.2.1
  simpa only [Work.Drive.Final.slabFn, hFn, Work.BoxShrink.Pinch.par_apply] using h1

/-- The care predicate of a corner chart: the active coordinate equals its base value. -/
def careCor (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (p : ℝ × ℝ) :
    ℝ → ℝ × ℝ → Prop :=
  fun _ q => (Work.BoxShrink.Pinch.par ψ q) (σ i) = (Work.BoxShrink.Pinch.par ψ p) (σ i)

/-- The corner chart carried by corner data at the first point. -/
theorem cornerChart_of_CorW {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {i : Fin 3} {ε : ℝ} {w : Wit}
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (h : CorW ψ s c σ v a₀ b₀ i ε w) :
    Nonempty (EvChart ψ v a₀ b₀ (careCor ψ σ i (wQ w)) (wT w) (hFn ψ v (wQ w)) (wQ w)) := by
  obtain ⟨hi2, hstrict, hinv, hnt, hcorner, hval⟩ := h
  refine exists_cornerChart ha hb hab ψ v σ i hinv ?_
  intro t ht
  apply hnt t
  rwa [sH_eq_sweepHeight_levOf] at ht

/-- The corner chart carried by corner data at the second point. -/
theorem cornerChart_of_CorW' {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {i : Fin 3} {ε : ℝ} {w : Wit}
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (h : CorW' ψ s c σ v a₀ b₀ i ε w) :
    Nonempty (EvChart ψ v a₀ b₀ (careCor ψ σ i (wQ' w)) (wT w) (hFn ψ v (wQ' w)) (wQ' w)) :=
  cornerChart_of_CorW (w := swapWit w) ha hb hab h

/-! ## The pieces -/

/-- The piece `(1,2)`: a critical point and a face event. -/
def Q12 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (η : ℝ) : Set Wit :=
  {w | C1 ψ s c σ v a₀ b₀ w ∧ C2' ψ s c σ v a₀ b₀ w ∧ sEq2 ψ v c η w ∧
    (η = 1 ∨ η = -1) ∧ LevW ψ a₀ b₀ w ∧ NeW ψ w ∧ NotBothW ψ s c σ v a₀ b₀ w}

/-- The piece `(1,3)`: a critical point and a corner event. -/
def Q13 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (i : Fin 3) (ε : ℝ) (η : ℝ) : Set Wit :=
  {w | C1 ψ s c σ v a₀ b₀ w ∧ CorW' ψ s c σ v a₀ b₀ i ε w ∧ sEq2 ψ v c η w ∧
    (η = 1 ∨ η = -1) ∧ (ε = 1 ∨ ε = -1) ∧ LevW ψ a₀ b₀ w ∧ NeW ψ w ∧
    NotBothW ψ s c σ v a₀ b₀ w}

/-- The piece `(2,2)`: two face events. -/
def Q22 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (η₁ η₂ : ℝ) : Set Wit :=
  {w | C2 ψ s c σ v a₀ b₀ w ∧ C2' ψ s c σ v a₀ b₀ w ∧ sEq1 ψ v c η₁ w ∧ sEq2 ψ v c η₂ w ∧
    (η₁ = 1 ∨ η₁ = -1) ∧ (η₂ = 1 ∨ η₂ = -1) ∧ LevW ψ a₀ b₀ w ∧ NeW ψ w ∧
    NotBothW ψ s c σ v a₀ b₀ w}

/-- The piece `(3,2)`: a corner event and a face event. -/
def Q32 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (i : Fin 3) (ε : ℝ) (η₁ η₂ : ℝ) : Set Wit :=
  {w | CorW ψ s c σ v a₀ b₀ i ε w ∧ C2' ψ s c σ v a₀ b₀ w ∧ sEq1 ψ v c η₁ w ∧
    sEq2 ψ v c η₂ w ∧ (η₁ = 1 ∨ η₁ = -1) ∧ (η₂ = 1 ∨ η₂ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
    LevW ψ a₀ b₀ w ∧ NeW ψ w ∧ NotBothW ψ s c σ v a₀ b₀ w}

/-- The piece `(3,3)`: two corner events. -/
def Q33 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (i₁ : Fin 3) (ε₁ : ℝ) (η₁ : ℝ) (i₂ : Fin 3) (ε₂ : ℝ) (η₂ : ℝ) : Set Wit :=
  {w | CorW ψ s c σ v a₀ b₀ i₁ ε₁ w ∧ CorW' ψ s c σ v a₀ b₀ i₂ ε₂ w ∧ sEq1 ψ v c η₁ w ∧
    sEq2 ψ v c η₂ w ∧ (η₁ = 1 ∨ η₁ = -1) ∧ (η₂ = 1 ∨ η₂ = -1) ∧ (ε₁ = 1 ∨ ε₁ = -1) ∧
    (ε₂ = 1 ∨ ε₂ = -1) ∧ LevW ψ a₀ b₀ w ∧ NeW ψ w ∧ NotBothW ψ s c σ v a₀ b₀ w}

/-- The piece `(2,1)`: a face event and a critical point (the swap of `Q12`). -/
def Q21 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (η : ℝ) : Set Wit :=
  swapWit ⁻¹' Q12 ψ s c σ v a₀ b₀ η

/-- The piece `(3,1)`: a corner event and a critical point (the swap of `Q13`). -/
def Q31 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (i : Fin 3) (ε : ℝ) (η : ℝ) : Set Wit :=
  swapWit ⁻¹' Q13 ψ s c σ v a₀ b₀ i ε η

/-- The piece `(2,3)`: a face event and a corner event (the swap of `Q32`). -/
def Q23 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3)
    (i : Fin 3) (ε : ℝ) (η₁ η₂ : ℝ) : Set Wit :=
  swapWit ⁻¹' Q32 ψ s c σ v a₀ b₀ i ε η₂ η₁

@[simp] theorem mem_Q12 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {η : ℝ} {w : Wit} :
    w ∈ Q12 ψ s c σ v a₀ b₀ η ↔
      (C1 ψ s c σ v a₀ b₀ w ∧ C2' ψ s c σ v a₀ b₀ w ∧ sEq2 ψ v c η w ∧
        (η = 1 ∨ η = -1) ∧ LevW ψ a₀ b₀ w ∧ NeW ψ w ∧
        NotBothW ψ s c σ v a₀ b₀ w) := by
  rw [Q12, Set.mem_ofPred_eq]

@[simp] theorem mem_Q13 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {i : Fin 3} {ε η : ℝ} {w : Wit} :
    w ∈ Q13 ψ s c σ v a₀ b₀ i ε η ↔
      (C1 ψ s c σ v a₀ b₀ w ∧ CorW' ψ s c σ v a₀ b₀ i ε w ∧ sEq2 ψ v c η w ∧
        (η = 1 ∨ η = -1) ∧ (ε = 1 ∨ ε = -1) ∧ LevW ψ a₀ b₀ w ∧ NeW ψ w ∧
        NotBothW ψ s c σ v a₀ b₀ w) := by
  rw [Q13, Set.mem_ofPred_eq]

@[simp] theorem mem_Q22 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {η₁ η₂ : ℝ} {w : Wit} :
    w ∈ Q22 ψ s c σ v a₀ b₀ η₁ η₂ ↔
      (C2 ψ s c σ v a₀ b₀ w ∧ C2' ψ s c σ v a₀ b₀ w ∧ sEq1 ψ v c η₁ w ∧
        sEq2 ψ v c η₂ w ∧ (η₁ = 1 ∨ η₁ = -1) ∧ (η₂ = 1 ∨ η₂ = -1) ∧
        LevW ψ a₀ b₀ w ∧ NeW ψ w ∧ NotBothW ψ s c σ v a₀ b₀ w) := by
  rw [Q22, Set.mem_ofPred_eq]

@[simp] theorem mem_Q32 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {i : Fin 3} {ε η₁ η₂ : ℝ} {w : Wit} :
    w ∈ Q32 ψ s c σ v a₀ b₀ i ε η₁ η₂ ↔
      (CorW ψ s c σ v a₀ b₀ i ε w ∧ C2' ψ s c σ v a₀ b₀ w ∧ sEq1 ψ v c η₁ w ∧
        sEq2 ψ v c η₂ w ∧ (η₁ = 1 ∨ η₁ = -1) ∧ (η₂ = 1 ∨ η₂ = -1) ∧
        (ε = 1 ∨ ε = -1) ∧ LevW ψ a₀ b₀ w ∧ NeW ψ w ∧
        NotBothW ψ s c σ v a₀ b₀ w) := by
  rw [Q32, Set.mem_ofPred_eq]

@[simp] theorem mem_Q33 {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {i₁ : Fin 3} {ε₁ η₁ : ℝ} {i₂ : Fin 3} {ε₂ η₂ : ℝ} {w : Wit} :
    w ∈ Q33 ψ s c σ v a₀ b₀ i₁ ε₁ η₁ i₂ ε₂ η₂ ↔
      (CorW ψ s c σ v a₀ b₀ i₁ ε₁ w ∧ CorW' ψ s c σ v a₀ b₀ i₂ ε₂ w ∧ sEq1 ψ v c η₁ w ∧
        sEq2 ψ v c η₂ w ∧ (η₁ = 1 ∨ η₁ = -1) ∧ (η₂ = 1 ∨ η₂ = -1) ∧
        (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧ LevW ψ a₀ b₀ w ∧ NeW ψ w ∧
        NotBothW ψ s c σ v a₀ b₀ w) := by
  rw [Q33, Set.mem_ofPred_eq]

/-! ## Continuity and smoothness of the swapping -/

theorem continuous_swapWit : Continuous swapWit := by
  have h : swapWit = fun w : Wit => (w.1, w.2.1, w.2.2.1, w.2.2.2.2, w.2.2.2.1) := rfl
  rw [h]
  fun_prop

theorem contDiff_swapWit : ContDiff ℝ 1 swapWit := by
  have h : swapWit = fun w : Wit => (w.1, w.2.1, w.2.2.1, w.2.2.2.2, w.2.2.2.1) := rfl
  rw [h]
  fun_prop

/-! ## The local structure of each piece -/

/-- **The local structure of the piece `(2,2)`** (two face events). -/
theorem localStructure_Q22 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : R3) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) (η₁ η₂ : ℝ) :
    ∀ w ∈ Q22 ψ s c σ v a₀ b₀ η₁ η₂,
      ∃ (O : Set Wit) (V : Set (ℝ × ℝ)) (φ : ℝ × ℝ → Wit),
        IsOpen O ∧ w ∈ O ∧ IsOpen V ∧ ContDiffOn ℝ 1 φ V ∧
        Q22 ψ s c σ v a₀ b₀ η₁ η₂ ∩ O ⊆ φ '' V := by
  intro w hw
  rw [mem_Q22] at hw
  obtain ⟨hC2, hC2', hsq1, hsq2, hηd1, hηd2, hlev, hne, hboth⟩ := hw
  obtain ⟨C₁⟩ := faceChart_of_C2 (ψ := ψ) (s := s) (c := c) (σ := σ) (v := v) (a₀ := a₀)
    (b₀ := b₀) ha hb hab hC2
  obtain ⟨C₂⟩ := faceChart_of_C2 (a₀ := a₀) (b₀ := b₀) ha hb hab (w := swapWit w) hC2'
  have hc₁ : Tangent ψ v a₀ b₀ (wT w) (wQ w) := tangent_of_C2 hC2
  have hc₂ : Tangent ψ v a₀ b₀ (wT w) (wQ' w) := by
    have h := tangent_of_C2 (w := swapWit w) hC2'
    simpa only [wT_swapWit, wQ_swapWit] using h
  obtain ⟨O, V, φ, hO, hwit, hV, hφ, hsub⟩ :=
    localStructure_twoCharts ha hb hab hva hvb C₁ C₂ hc₁ hc₂ rfl rfl hηd1 hηd2 hlev hne
      (u₀ := wU w) (h₀ := wH w) hsq1 hsq2
  refine ⟨O, V, φ, hO, ?_, hV, hφ, ?_⟩
  · exact hwit
  · intro w' hw'
    rw [Set.mem_inter_iff, mem_Q22] at hw'
    obtain ⟨⟨h2a, h2b, hsq1', hsq2', hηd1', hηd2', hlev', hne', hboth'⟩, hw'O⟩ := hw'
    refine hsub ?_
    rw [Set.mem_inter_iff, Set.mem_ofPred_eq]
    refine ⟨⟨tangent_of_C2 h2a, ?_, hsq1', hsq2', hlev'⟩, hw'O⟩
    have h := tangent_of_C2 (w := swapWit w') h2b
    simpa only [wT_swapWit, wQ_swapWit] using h

/-- **The local structure of the piece `(3,2)`** (a corner event and a face event). -/
theorem localStructure_Q32 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : R3) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) (i : Fin 3) (ε η₁ η₂ : ℝ) :
    ∀ w ∈ Q32 ψ s c σ v a₀ b₀ i ε η₁ η₂,
      ∃ (O : Set Wit) (V : Set (ℝ × ℝ)) (φ : ℝ × ℝ → Wit),
        IsOpen O ∧ w ∈ O ∧ IsOpen V ∧ ContDiffOn ℝ 1 φ V ∧
        Q32 ψ s c σ v a₀ b₀ i ε η₁ η₂ ∩ O ⊆ φ '' V := by
  intro w hw
  rw [mem_Q32] at hw
  obtain ⟨hcor, hC2', hsq1, hsq2, hηd1, hηd2, hεd, hlev, hne, hboth⟩ := hw
  obtain ⟨C₁⟩ := cornerChart_of_CorW ha hb hab hcor
  obtain ⟨C₂⟩ := faceChart_of_C2 (a₀ := a₀) (b₀ := b₀) ha hb hab (w := swapWit w) hC2'
  have hc₁ : careCor ψ σ i (wQ w) (wT w) (wQ w) := rfl
  have hc₂ : Tangent ψ v a₀ b₀ (wT w) (wQ' w) := by
    have h := tangent_of_C2 (w := swapWit w) hC2'
    simpa only [wT_swapWit, wQ_swapWit] using h
  obtain ⟨O, V, φ, hO, hwit, hV, hφ, hsub⟩ :=
    localStructure_twoCharts ha hb hab hva hvb C₁ C₂ hc₁ hc₂ rfl rfl hηd1 hηd2 hlev hne
      (u₀ := wU w) (h₀ := wH w) hsq1 hsq2
  refine ⟨O, V, φ, hO, ?_, hV, hφ, ?_⟩
  · exact hwit
  · intro w' hw'
    rw [Set.mem_inter_iff, mem_Q32] at hw'
    obtain ⟨⟨hcor', hC2'', hsq1', hsq2', hηd1', hηd2', hεd', hlev', hne', hboth'⟩, hw'O⟩ := hw'
    refine hsub ?_
    rw [Set.mem_inter_iff, Set.mem_ofPred_eq]
    have hval : (Work.BoxShrink.Pinch.par ψ (wQ w')) (σ i)
        = (Work.BoxShrink.Pinch.par ψ (wQ w)) (σ i) := by
      rw [hcor'.2.2.2.2.2, hcor.2.2.2.2.2]
    refine ⟨⟨show careCor ψ σ i (wQ w) (wT w') (wQ w') from hval, ?_, hsq1', hsq2', hlev'⟩,
      hw'O⟩
    have h := tangent_of_C2 (w := swapWit w') hC2''
    simpa only [wT_swapWit, wQ_swapWit] using h

/-- **The local structure of the piece `(3,3)`** (two corner events). -/
theorem localStructure_Q33 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : R3) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    (i₁ : Fin 3) (ε₁ η₁ : ℝ) (i₂ : Fin 3) (ε₂ η₂ : ℝ) :
    ∀ w ∈ Q33 ψ s c σ v a₀ b₀ i₁ ε₁ η₁ i₂ ε₂ η₂,
      ∃ (O : Set Wit) (V : Set (ℝ × ℝ)) (φ : ℝ × ℝ → Wit),
        IsOpen O ∧ w ∈ O ∧ IsOpen V ∧ ContDiffOn ℝ 1 φ V ∧
        Q33 ψ s c σ v a₀ b₀ i₁ ε₁ η₁ i₂ ε₂ η₂ ∩ O ⊆ φ '' V := by
  intro w hw
  rw [mem_Q33] at hw
  obtain ⟨hcor₁, hcor₂, hsq1, hsq2, hηd1, hηd2, hεd1, hεd2, hlev, hne, hboth⟩ := hw
  obtain ⟨C₁⟩ := cornerChart_of_CorW ha hb hab hcor₁
  obtain ⟨C₂⟩ := cornerChart_of_CorW' ha hb hab hcor₂
  have hc₁ : careCor ψ σ i₁ (wQ w) (wT w) (wQ w) := rfl
  have hc₂ : careCor ψ σ i₂ (wQ' w) (wT w) (wQ' w) := rfl
  obtain ⟨O, V, φ, hO, hwit, hV, hφ, hsub⟩ :=
    localStructure_twoCharts ha hb hab hva hvb C₁ C₂ hc₁ hc₂ rfl rfl hηd1 hηd2 hlev hne
      (u₀ := wU w) (h₀ := wH w) hsq1 hsq2
  refine ⟨O, V, φ, hO, ?_, hV, hφ, ?_⟩
  · exact hwit
  · intro w' hw'
    rw [Set.mem_inter_iff, mem_Q33] at hw'
    obtain ⟨⟨hcor₁', hcor₂', hsq1', hsq2', hηd1', hηd2', hεd1', hεd2', hlev', hne', hboth'⟩,
      hw'O⟩ := hw'
    refine hsub ?_
    rw [Set.mem_inter_iff, Set.mem_ofPred_eq]
    have hval₁ : (Work.BoxShrink.Pinch.par ψ (wQ w')) (σ i₁)
        = (Work.BoxShrink.Pinch.par ψ (wQ w)) (σ i₁) := by
      rw [hcor₁'.2.2.2.2.2, hcor₁.2.2.2.2.2]
    have hval₂ : (Work.BoxShrink.Pinch.par ψ (wQ' w')) (σ i₂)
        = (Work.BoxShrink.Pinch.par ψ (wQ' w)) (σ i₂) := by
      rw [hcor₂'.2.2.2.2.2, hcor₂.2.2.2.2.2]
    exact ⟨⟨show careCor ψ σ i₁ (wQ w) (wT w') (wQ w') from hval₁,
      show careCor ψ σ i₂ (wQ' w) (wT w') (wQ' w') from hval₂, hsq1', hsq2', hlev'⟩, hw'O⟩

/-- **The local structure of the piece `(1,2)`** (a critical point and a face event). -/
theorem localStructure_Q12 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : R3) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) (η : ℝ) :
    ∀ w ∈ Q12 ψ s c σ v a₀ b₀ η,
      ∃ (O : Set Wit) (V : Set (ℝ × ℝ)) (φ : ℝ × ℝ → Wit),
        IsOpen O ∧ w ∈ O ∧ IsOpen V ∧ ContDiffOn ℝ 1 φ V ∧
        Q12 ψ s c σ v a₀ b₀ η ∩ O ⊆ φ '' V := by
  intro w hw
  rw [mem_Q12] at hw
  obtain ⟨hC1, hC2', hsq2, hηd2, hlev, hne, hboth⟩ := hw
  obtain ⟨K⟩ := critChart_of_C1 ha hb hab hC1
  obtain ⟨C⟩ := faceChart_of_C2 (a₀ := a₀) (b₀ := b₀) ha hb hab (w := swapWit w) hC2'
  have hcare : Tangent ψ v a₀ b₀ (wT w) (wQ' w) := by
    have h := tangent_of_C2 (w := swapWit w) hC2'
    simpa only [wT_swapWit, wQ_swapWit] using h
  obtain ⟨O, V, φ, hO, hwit, hV, -, hφ, hsub⟩ :=
    localStructure_one ψ v a₀ b₀ c ha hb hab hva hvb K C hcare hlev
      (η := η) (u₀ := wU w) (h₀ := wH w) hηd2 hsq2 (slab_lt_of_C1 hC1)
  refine ⟨O ∩ (wQ ⁻¹' K.U), V, φ, hO.inter (K.hUopen.preimage continuous_wQ), ?_, hV, hφ, ?_⟩
  · exact ⟨hwit, K.hUmem⟩
  · intro w' hw'
    rw [Set.mem_inter_iff, mem_Q12] at hw'
    obtain ⟨⟨hC1', hC2'', hsq2', hηd2', hlev', hne', hboth'⟩, hw'O'⟩ := hw'
    rw [Set.mem_inter_iff, Set.mem_preimage] at hw'O'
    obtain ⟨hw'O, hw'U⟩ := hw'O'
    refine hsub ?_
    rw [Set.mem_inter_iff, Set.mem_ofPred_eq]
    have h := tangent_of_C2 (w := swapWit w') hC2''
    refine ⟨⟨crit_of_C1 hC1', hw'U, slab_lt_of_C1 hC1', ?_, hsq2', hlev'⟩, hw'O⟩
    simpa only [wT_swapWit, wQ_swapWit] using h

/-- **The local structure of the piece `(1,3)`** (a critical point and a corner event). -/
theorem localStructure_Q13 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : R3) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) (i : Fin 3) (ε η : ℝ) :
    ∀ w ∈ Q13 ψ s c σ v a₀ b₀ i ε η,
      ∃ (O : Set Wit) (V : Set (ℝ × ℝ)) (φ : ℝ × ℝ → Wit),
        IsOpen O ∧ w ∈ O ∧ IsOpen V ∧ ContDiffOn ℝ 1 φ V ∧
        Q13 ψ s c σ v a₀ b₀ i ε η ∩ O ⊆ φ '' V := by
  intro w hw
  rw [mem_Q13] at hw
  obtain ⟨hC1, hcor, hsq2, hηd2, hεd, hlev, hne, hboth⟩ := hw
  obtain ⟨K⟩ := critChart_of_C1 ha hb hab hC1
  obtain ⟨C⟩ := cornerChart_of_CorW' ha hb hab hcor
  have hcare : careCor ψ σ i (wQ' w) (wT w) (wQ' w) := rfl
  obtain ⟨O, V, φ, hO, hwit, hV, -, hφ, hsub⟩ :=
    localStructure_one ψ v a₀ b₀ c ha hb hab hva hvb K C hcare hlev
      (η := η) (u₀ := wU w) (h₀ := wH w) hηd2 hsq2 (slab_lt_of_C1 hC1)
  refine ⟨O ∩ (wQ ⁻¹' K.U), V, φ, hO.inter (K.hUopen.preimage continuous_wQ), ?_, hV, hφ, ?_⟩
  · exact ⟨hwit, K.hUmem⟩
  · intro w' hw'
    rw [Set.mem_inter_iff, mem_Q13] at hw'
    obtain ⟨⟨hC1', hcor', hsq2', hηd2', hεd', hlev', hne', hboth'⟩, hw'O'⟩ := hw'
    rw [Set.mem_inter_iff, Set.mem_preimage] at hw'O'
    obtain ⟨hw'O, hw'U⟩ := hw'O'
    refine hsub ?_
    rw [Set.mem_inter_iff, Set.mem_ofPred_eq]
    have hval : (Work.BoxShrink.Pinch.par ψ (wQ' w')) (σ i)
        = (Work.BoxShrink.Pinch.par ψ (wQ' w)) (σ i) := by
      rw [hcor'.2.2.2.2.2, hcor.2.2.2.2.2]
    exact ⟨⟨crit_of_C1 hC1', hw'U, slab_lt_of_C1 hC1', hval, hsq2', hlev'⟩, hw'O⟩

/-- **The local structure of the piece `(2,1)`** (a face event and a critical point). -/
theorem localStructure_Q21 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : R3) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) (η : ℝ) :
    ∀ w ∈ Q21 ψ s c σ v a₀ b₀ η,
      ∃ (O : Set Wit) (V : Set (ℝ × ℝ)) (φ : ℝ × ℝ → Wit),
        IsOpen O ∧ w ∈ O ∧ IsOpen V ∧ ContDiffOn ℝ 1 φ V ∧
        Q21 ψ s c σ v a₀ b₀ η ∩ O ⊆ φ '' V := by
  intro w hw
  rw [Q21, Set.mem_preimage] at hw
  obtain ⟨O, V, φ, hO, hwit, hV, hφ, hsub⟩ :=
    localStructure_Q12 ψ s c σ v a₀ b₀ ha hb hab hva hvb η (swapWit w) hw
  refine ⟨swapWit ⁻¹' O, V, swapWit ∘ φ, hO.preimage continuous_swapWit, hwit, hV,
    contDiff_swapWit.comp_contDiffOn hφ, ?_⟩
  rw [Q21]
  exact swapWit_image_subset hsub

/-- **The local structure of the piece `(3,1)`** (a corner event and a critical point). -/
theorem localStructure_Q31 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : R3) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) (i : Fin 3) (ε η : ℝ) :
    ∀ w ∈ Q31 ψ s c σ v a₀ b₀ i ε η,
      ∃ (O : Set Wit) (V : Set (ℝ × ℝ)) (φ : ℝ × ℝ → Wit),
        IsOpen O ∧ w ∈ O ∧ IsOpen V ∧ ContDiffOn ℝ 1 φ V ∧
        Q31 ψ s c σ v a₀ b₀ i ε η ∩ O ⊆ φ '' V := by
  intro w hw
  rw [Q31, Set.mem_preimage] at hw
  obtain ⟨O, V, φ, hO, hwit, hV, hφ, hsub⟩ :=
    localStructure_Q13 ψ s c σ v a₀ b₀ ha hb hab hva hvb i ε η (swapWit w) hw
  refine ⟨swapWit ⁻¹' O, V, swapWit ∘ φ, hO.preimage continuous_swapWit, hwit, hV,
    contDiff_swapWit.comp_contDiffOn hφ, ?_⟩
  rw [Q31]
  exact swapWit_image_subset hsub

/-- **The local structure of the piece `(2,3)`** (a face event and a corner event). -/
theorem localStructure_Q23 (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : R3) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) (i : Fin 3) (ε η₁ η₂ : ℝ) :
    ∀ w ∈ Q23 ψ s c σ v a₀ b₀ i ε η₁ η₂,
      ∃ (O : Set Wit) (V : Set (ℝ × ℝ)) (φ : ℝ × ℝ → Wit),
        IsOpen O ∧ w ∈ O ∧ IsOpen V ∧ ContDiffOn ℝ 1 φ V ∧
        Q23 ψ s c σ v a₀ b₀ i ε η₁ η₂ ∩ O ⊆ φ '' V := by
  intro w hw
  rw [Q23, Set.mem_preimage] at hw
  obtain ⟨O, V, φ, hO, hwit, hV, hφ, hsub⟩ :=
    localStructure_Q32 ψ s c σ v a₀ b₀ ha hb hab hva hvb i ε η₂ η₁ (swapWit w) hw
  refine ⟨swapWit ⁻¹' O, V, swapWit ∘ φ, hO.preimage continuous_swapWit, hwit, hV,
    contDiff_swapWit.comp_contDiffOn hφ, ?_⟩
  rw [Q23]
  exact swapWit_image_subset hsub

/-! ## The bridges between the two points of a witness -/

theorem C1_swapWit {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} (w : Wit) :
    C1 ψ s c σ v a₀ b₀ (swapWit w) ↔ C1' ψ s c σ v a₀ b₀ w := by
  simp only [C1, C1', swapWit, wit, wU, wH, wT, wQ, wQ']

theorem C1'_swapWit {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} (w : Wit) :
    C1' ψ s c σ v a₀ b₀ (swapWit w) ↔ C1 ψ s c σ v a₀ b₀ w := by
  simp only [C1, C1', swapWit, wit, wU, wH, wT, wQ, wQ']

theorem C2_swapWit {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} (w : Wit) :
    C2 ψ s c σ v a₀ b₀ (swapWit w) ↔ C2' ψ s c σ v a₀ b₀ w := by
  simp only [C2, C2', swapWit, wit, wU, wH, wT, wQ, wQ']

theorem C2'_swapWit {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} (w : Wit) :
    C2' ψ s c σ v a₀ b₀ (swapWit w) ↔ C2 ψ s c σ v a₀ b₀ w := by
  simp only [C2, C2', swapWit, wit, wU, wH, wT, wQ, wQ']

theorem C3'_swapWit {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} (w : Wit) :
    C3' ψ s c σ v a₀ b₀ (swapWit w) ↔ C3 ψ s c σ v a₀ b₀ w := by
  simp only [C3, C3', swapWit, wit, wU, wH, wT, wQ, wQ']

theorem CorW'_swapWit {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} (i : Fin 3) (ε : ℝ) (w : Wit) :
    CorW' ψ s c σ v a₀ b₀ i ε (swapWit w) ↔ CorW ψ s c σ v a₀ b₀ i ε w := by
  simp only [CorW, CorW', swapWit, wit, wU, wH, wT, wQ, wQ']

theorem CorW_swapWit {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} (i : Fin 3) (ε : ℝ) (w : Wit) :
    CorW ψ s c σ v a₀ b₀ i ε (swapWit w) ↔ CorW' ψ s c σ v a₀ b₀ i ε w := by
  simp only [CorW, CorW', swapWit, wit, wU, wH, wT, wQ, wQ']

theorem sEq1_swapWit {ψ : Submission.Diffeo} {v c : R3} (η : ℝ) (w : Wit) :
    sEq1 ψ v c η (swapWit w) ↔ sEq2 ψ v c η w := by
  simp only [sEq1, sEq2, swapWit, wit, wU, wH, wQ, wQ']

theorem sEq2_swapWit {ψ : Submission.Diffeo} {v c : R3} (η : ℝ) (w : Wit) :
    sEq2 ψ v c η (swapWit w) ↔ sEq1 ψ v c η w := by
  simp only [sEq1, sEq2, swapWit, wit, wU, wH, wQ, wQ']

theorem LevW_swapWit {ψ : Submission.Diffeo} {a₀ b₀ : R3} (w : Wit) :
    LevW ψ a₀ b₀ (swapWit w) ↔ LevW ψ a₀ b₀ w := by
  simp only [LevW, swapWit, wit, wT, wQ, wQ']
  exact eq_comm

theorem NeW_swapWit {ψ : Submission.Diffeo} (w : Wit) :
    NeW ψ (swapWit w) ↔ NeW ψ w := by
  simp only [NeW, swapWit, wit, wQ, wQ']
  exact ne_comm

theorem NotBothW_swapWit {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} (w : Wit) :
    NotBothW ψ s c σ v a₀ b₀ (swapWit w) ↔ NotBothW ψ s c σ v a₀ b₀ w := by
  simp only [NotBothW, swapWit, wit, wU, wH, wT, wQ, wQ']
  exact not_congr and_comm

theorem exists_eta_of_C3' {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v a₀ b₀ : R3} {w : Wit} (h : C3' ψ s c σ v a₀ b₀ w) :
    ∃ η : ℝ, (η = 1 ∨ η = -1) ∧ sEq2 ψ v c η w := by
  have h' : C3 ψ s c σ v a₀ b₀ (swapWit w) := h
  obtain ⟨η, hη, hsq⟩ := exists_eta_of_C3 h'
  exact ⟨η, hη, (sEq1_swapWit η w).mp hsq⟩

/-! ## Encoding the sign data by a finite index -/

/-- The two signs `±1`. -/
def sgnB (b : Bool) : ℝ := if b then 1 else -1

/-- The sign index of a real number known to be `±1`. -/
def indB (η : ℝ) : Bool := if η = 1 then true else false

theorem sgnB_indB {η : ℝ} (h : η = 1 ∨ η = -1) : sgnB (indB η) = η := by
  rcases h with h | h
  · rw [show indB η = true from by unfold indB; exact if_pos h, h]
    rfl
  · have h1 : ¬(η = 1) := by rw [h]; norm_num
    rw [show indB η = false from by unfold indB; exact if_neg h1, h]
    rfl

theorem sgnB_indB_mem {η : ℝ} (h : η = 1 ∨ η = -1) : sgnB (indB η) = 1 ∨ sgnB (indB η) = -1 := by
  rw [sgnB_indB h]
  exact h

/-! ## The finite family of pieces -/

/-- The finite index set of the pieces. -/
inductive PieceIdx : Type
  | p12 (η : Bool)
  | p13 (i : Fin 3) (e : Bool) (η : Bool)
  | p21 (η : Bool)
  | p22 (η₁ η₂ : Bool)
  | p23 (i : Fin 3) (e : Bool) (η₁ η₂ : Bool)
  | p31 (i : Fin 3) (e : Bool) (η : Bool)
  | p32 (i : Fin 3) (e : Bool) (η₁ η₂ : Bool)
  | p33 (i₁ : Fin 3) (e₁ : Bool) (η₁ : Bool) (i₂ : Fin 3) (e₂ : Bool) (η₂ : Bool)
  deriving DecidableEq, Fintype

/-- The piece attached to an index. -/
def piece (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3) :
    PieceIdx → Set Wit
  | PieceIdx.p12 η => Q12 ψ s c σ v a₀ b₀ (sgnB η)
  | PieceIdx.p13 i e η => Q13 ψ s c σ v a₀ b₀ i (sgnB e) (sgnB η)
  | PieceIdx.p21 η => Q21 ψ s c σ v a₀ b₀ (sgnB η)
  | PieceIdx.p22 η₁ η₂ => Q22 ψ s c σ v a₀ b₀ (sgnB η₁) (sgnB η₂)
  | PieceIdx.p23 i e η₁ η₂ => Q23 ψ s c σ v a₀ b₀ i (sgnB e) (sgnB η₁) (sgnB η₂)
  | PieceIdx.p31 i e η => Q31 ψ s c σ v a₀ b₀ i (sgnB e) (sgnB η)
  | PieceIdx.p32 i e η₁ η₂ => Q32 ψ s c σ v a₀ b₀ i (sgnB e) (sgnB η₁) (sgnB η₂)
  | PieceIdx.p33 i₁ e₁ η₁ i₂ e₂ η₂ =>
      Q33 ψ s c σ v a₀ b₀ i₁ (sgnB e₁) (sgnB η₁) i₂ (sgnB e₂) (sgnB η₂)

/-- **Every bad witness lies in one of the pieces.** -/
theorem witBad_subset_pieces (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (v a₀ b₀ : R3) :
    {w | WitBad ψ s c σ v a₀ b₀ w} ⊆ ⋃ d : PieceIdx, piece ψ s c σ v a₀ b₀ d := by
  intro w hw
  rw [Set.mem_ofPred_eq, witBad_iff] at hw
  obtain ⟨hc, hc', hlev, hne, hboth⟩ := hw
  rcases hc with h1 | h2 | h3
  · rcases hc' with h1' | h2' | h3'
    · exact absurd ⟨h1.1, h1'.1⟩ hboth
    · obtain ⟨η₂, hηd2, hsq2⟩ := exists_eta_of_C2' h2'
      refine mem_iUnion.mpr ⟨PieceIdx.p12 (indB η₂), ?_⟩
      simp only [piece, mem_Q12]
      exact ⟨h1, h2', by rw [sgnB_indB hηd2]; exact hsq2, sgnB_indB_mem hηd2, hlev, hne, hboth⟩
    · obtain ⟨i₂, ε₂, hεd2, hcor2⟩ := exists_corner_data_of_C3' h3'
      obtain ⟨η₂, hηd2, hsq2⟩ := exists_eta_of_C3' h3'
      refine mem_iUnion.mpr ⟨PieceIdx.p13 i₂ (indB ε₂) (indB η₂), ?_⟩
      simp only [piece, mem_Q13]
      exact ⟨h1, by rw [sgnB_indB hεd2]; exact hcor2, by rw [sgnB_indB hηd2]; exact hsq2,
        sgnB_indB_mem hηd2, sgnB_indB_mem hεd2, hlev, hne, hboth⟩
  · rcases hc' with h1' | h2' | h3'
    · obtain ⟨η₁, hηd1, hsq1⟩ := exists_eta_of_C2 h2
      refine mem_iUnion.mpr ⟨PieceIdx.p21 (indB η₁), ?_⟩
      rw [piece]
      rw [Q21, Set.mem_preimage, mem_Q12]
      refine ⟨?_, ?_, ?_, sgnB_indB_mem hηd1, ?_, ?_, ?_⟩
      · rw [C1_swapWit]; exact h1'
      · rw [C2'_swapWit]; exact h2
      · rw [sEq2_swapWit, sgnB_indB hηd1]; exact hsq1
      · rw [LevW_swapWit]; exact hlev
      · rw [NeW_swapWit]; exact hne
      · rw [NotBothW_swapWit]; exact hboth
    · obtain ⟨η₁, hηd1, hsq1⟩ := exists_eta_of_C2 h2
      obtain ⟨η₂, hηd2, hsq2⟩ := exists_eta_of_C2' h2'
      refine mem_iUnion.mpr ⟨PieceIdx.p22 (indB η₁) (indB η₂), ?_⟩
      simp only [piece, mem_Q22]
      exact ⟨h2, h2', by rw [sgnB_indB hηd1]; exact hsq1, by rw [sgnB_indB hηd2]; exact hsq2,
        sgnB_indB_mem hηd1, sgnB_indB_mem hηd2, hlev, hne, hboth⟩
    · obtain ⟨i₂, ε₂, hεd2, hcor2⟩ := exists_corner_data_of_C3' h3'
      obtain ⟨η₁, hηd1, hsq1⟩ := exists_eta_of_C2 h2
      obtain ⟨η₂, hηd2, hsq2⟩ := exists_eta_of_C3' h3'
      refine mem_iUnion.mpr ⟨PieceIdx.p23 i₂ (indB ε₂) (indB η₁) (indB η₂), ?_⟩
      rw [piece]
      rw [Q23, Set.mem_preimage, mem_Q32]
      refine ⟨?_, ?_, ?_, ?_, sgnB_indB_mem hηd2, sgnB_indB_mem hηd1, sgnB_indB_mem hεd2,
        ?_, ?_, ?_⟩
      · rw [CorW_swapWit, sgnB_indB hεd2]; exact hcor2
      · rw [C2'_swapWit]; exact h2
      · rw [sEq1_swapWit, sgnB_indB hηd2]; exact hsq2
      · rw [sEq2_swapWit, sgnB_indB hηd1]; exact hsq1
      · rw [LevW_swapWit]; exact hlev
      · rw [NeW_swapWit]; exact hne
      · rw [NotBothW_swapWit]; exact hboth
  · obtain ⟨i₁, ε₁, hεd1, hcor1⟩ := exists_corner_data_of_C3 h3
    obtain ⟨η₁, hηd1, hsq1⟩ := exists_eta_of_C3 h3
    rcases hc' with h1' | h2' | h3'
    · refine mem_iUnion.mpr ⟨PieceIdx.p31 i₁ (indB ε₁) (indB η₁), ?_⟩
      rw [piece]
      rw [Q31, Set.mem_preimage, mem_Q13]
      refine ⟨?_, ?_, ?_, sgnB_indB_mem hηd1, sgnB_indB_mem hεd1, ?_, ?_, ?_⟩
      · rw [C1_swapWit]; exact h1'
      · rw [CorW'_swapWit, sgnB_indB hεd1]; exact hcor1
      · rw [sEq2_swapWit, sgnB_indB hηd1]; exact hsq1
      · rw [LevW_swapWit]; exact hlev
      · rw [NeW_swapWit]; exact hne
      · rw [NotBothW_swapWit]; exact hboth
    · obtain ⟨η₂, hηd2, hsq2⟩ := exists_eta_of_C2' h2'
      refine mem_iUnion.mpr ⟨PieceIdx.p32 i₁ (indB ε₁) (indB η₁) (indB η₂), ?_⟩
      simp only [piece, mem_Q32]
      exact ⟨by rw [sgnB_indB hεd1]; exact hcor1, h2',
        by rw [sgnB_indB hηd1]; exact hsq1, by rw [sgnB_indB hηd2]; exact hsq2,
        sgnB_indB_mem hηd1, sgnB_indB_mem hηd2, sgnB_indB_mem hεd1, hlev, hne, hboth⟩
    · obtain ⟨i₂, ε₂, hεd2, hcor2⟩ := exists_corner_data_of_C3' h3'
      obtain ⟨η₂, hηd2, hsq2⟩ := exists_eta_of_C3' h3'
      refine mem_iUnion.mpr ⟨PieceIdx.p33 i₁ (indB ε₁) (indB η₁) i₂ (indB ε₂) (indB η₂), ?_⟩
      simp only [piece, mem_Q33]
      exact ⟨by rw [sgnB_indB hεd1]; exact hcor1, by rw [sgnB_indB hεd2]; exact hcor2,
        by rw [sgnB_indB hηd1]; exact hsq1, by rw [sgnB_indB hηd2]; exact hsq2,
        sgnB_indB_mem hηd1, sgnB_indB_mem hηd2, sgnB_indB_mem hεd1, sgnB_indB_mem hεd2,
        hlev, hne, hboth⟩

/-- **The bad set of "one event per level" is null in `ℝ³ = (u, h, τ)`.**  For the orthonormal
configuration `(v, a₀, b₀)` (unit, mutually orthogonal, `a₀, b₀ ⊥ v`), the set of triples
`(u, h, τ)` at which the swept level `ℓ_τ = ⟪dirOf τ a₀ b₀, ·⟫` carries two *distinct* non-degenerate
events (`Work.Drive.Mono.NDEvent`) of the same level, not both critical points
(`Work.Drive.Mono.OneEvBad`), is null.

This is the reformulation of route I in `Submission/Work/Drive/Mono/NOTES_LEAD_LD_interface.md` §0.1
and §4: putting the *pointwise non-degeneracy* inside the bad set and varying `u` together with
`(h, τ)` is what makes the statement true without any `BoxGen`/`GammaTransverse`/`TiltedGenericity`
hypothesis (every refutation of the earlier spellings used a degenerate event).  The proof is one
template: split by the pair of event types, continue each event by the inverse function theorem
(type 1: injective Hessian; type 2: the constrained second derivative; type 3: the invertible
derivative of `q ↦ ((par q) (σ i), ⟪v, par q⟫)`), compute the level derivatives by the envelope
(a corner event does not move with `τ`), and observe that the difference `D = L − L'` has a nonzero
partial derivative in `(u, h, τ)` at every incidence point — `∂_u` for `{1, b}` pairs, `(∂_u, ∂_h)`
for opposite faces, `(∂_u, ∂_τ)` for two events on the same face, where `D = 0` forces the two
surface points to coincide; a `C¹` function with a nonzero partial on a box has null zero set, and a
countable Lindelöf cover finishes. -/
theorem oneEvBad_null3 (ψ : Submission.Diffeo) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1)
    (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (hva : inner ℝ v a₀ = 0)
    (hvb : inner ℝ v b₀ = 0) :
    MeasureTheory.volume {x : ℝ × ℝ × ℝ |
      Work.Drive.Mono.OneEvBad ψ s c σ v a₀ b₀ x.1 x.2.1 x.2.2} = 0 := by
  rw [oneEvBad_eq_proj ψ s c σ v a₀ b₀]
  refine volume_proj_eq_zero_of_cover (piece ψ s c σ v a₀ b₀)
    (witBad_subset_pieces ψ s c σ v a₀ b₀) ?_
  intro d
  cases d with
  | p12 η =>
      exact projectionNull_localDimH_two
        (fun w hw => localStructure_Q12 ψ s c σ v a₀ b₀ ha hb hab hva hvb (sgnB η) w hw)
  | p13 i e η =>
      exact projectionNull_localDimH_two
        (fun w hw => localStructure_Q13 ψ s c σ v a₀ b₀ ha hb hab hva hvb i (sgnB e) (sgnB η)
          w hw)
  | p21 η =>
      exact projectionNull_localDimH_two
        (fun w hw => localStructure_Q21 ψ s c σ v a₀ b₀ ha hb hab hva hvb (sgnB η) w hw)
  | p22 η₁ η₂ =>
      exact projectionNull_localDimH_two
        (fun w hw => localStructure_Q22 ψ s c σ v a₀ b₀ ha hb hab hva hvb (sgnB η₁) (sgnB η₂)
          w hw)
  | p23 i e η₁ η₂ =>
      exact projectionNull_localDimH_two
        (fun w hw => localStructure_Q23 ψ s c σ v a₀ b₀ ha hb hab hva hvb i (sgnB e) (sgnB η₁)
          (sgnB η₂) w hw)
  | p31 i e η =>
      exact projectionNull_localDimH_two
        (fun w hw => localStructure_Q31 ψ s c σ v a₀ b₀ ha hb hab hva hvb i (sgnB e) (sgnB η)
          w hw)
  | p32 i e η₁ η₂ =>
      exact projectionNull_localDimH_two
        (fun w hw => localStructure_Q32 ψ s c σ v a₀ b₀ ha hb hab hva hvb i (sgnB e) (sgnB η₁)
          (sgnB η₂) w hw)
  | p33 i₁ e₁ η₁ i₂ e₂ η₂ =>
      exact projectionNull_localDimH_two
        (fun w hw => localStructure_Q33 ψ s c σ v a₀ b₀ ha hb hab hva hvb i₁ (sgnB e₁) (sgnB η₁)
          i₂ (sgnB e₂) (sgnB η₂) w hw)

end

end Work.Drive.Mono
