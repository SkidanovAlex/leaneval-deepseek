import Mathlib
import Submission.Work.Peluse.Concat.gcsRecurse

/-!
# The flat cube sum of a single function is a nonnegative real

For `1 ≤ t`, `X` a finite type and `g : (Fin t → X) → ℂ`, the *flat cube sum*
`Work.Peluse.Concat.cubeSum (fun _ : Fin t → Bool => g)` is a nonnegative real.  This is the
"positivity of the flat cube" used (i) to drop the modulus of the Gowers--Cauchy--Schwarz output in
the phase-elimination chain (`NOTES_lemma75_GCS_route.md` §3) and (ii) to compare the chirped and
unchirped aggregates of Peluse's Lemma 7.5.

It is an **immediate consequence of the workspace's `Concat.gcsRecurse`** (second component):

```
∀ t ≥ 1, ∀ g, cubeSum (fun _ : Fin t → Bool => g) = ↑(NPow t g) ,      NPow t g = ‖cubeSum (fun _ => g)‖ ≥ 0
```

so no new proof is needed — the lemma is a restatement of an already proved identity.  (The case
`t = 0` is false — the sum collapses to the arbitrary complex number `g` — hence the hypothesis
`1 ≤ t`; the same hypothesis is carried by the colleague's stub `flatCubeSum_re_nonneg`.)

The `Finset`-pi version `flatCubeSum_nonneg_finset` is the form needed by the phase-elimination
chain, with `Q : Finset ℤ` the direction set and `W` defined on the tuple type `Fin t → ℤ`.
-/

namespace Work.Peluse.Ulower

noncomputable section

/-- **The flat cube sum of a single function is a nonnegative real** (`1 ≤ t`).  Immediate from
`Concat.gcsRecurse`: the cube sum is the coercion of `NPow t g ≥ 0`. -/
theorem flatCubeSum_nonneg {t : ℕ} (ht : 1 ≤ t) {X : Type} [Fintype X] (g : (Fin t → X) → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ Work.Peluse.Concat.cubeSum (fun _ : Fin t → Bool => g) = (r : ℂ) :=
  ⟨Work.Peluse.Concat.NPow t g, norm_nonneg _, Work.Peluse.Concat.gcsRecurse.2.1 X t ht g⟩

/-- `∑_{v ∈ Fintype.piFinset (fun _ : Fin t => Q)} f v = ∑_{v : Fin t → ↥Q} f (fun i => (v i).1)`. -/
lemma sum_piFinset_eq_sum_subtype' {t : ℕ} (Q : Finset ℤ) {M : Type*} [AddCommMonoid M]
    (F : (Fin t → ℤ) → M) :
    (∑ v ∈ Fintype.piFinset (fun _ : Fin t => Q), F v)
      = ∑ v : Fin t → ↥Q, F (fun i => (v i).1) := by
  classical
  have hπ : Fintype.piFinset (fun _ : Fin t => Q)
      = (Finset.univ : Finset (Fin t → ↥Q)).image (fun v i => (v i).1) := by
    ext u
    simp only [Fintype.mem_piFinset, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hu
      exact ⟨fun i => ⟨u i, hu i⟩, rfl⟩
    · rintro ⟨v, rfl⟩ i
      exact (v i).2
  rw [hπ, Finset.sum_image]
  intro x _ y _ h
  funext i
  exact Subtype.ext (congr_fun h i)

/-- The two-variable form of `sum_piFinset_eq_sum_subtype'`. -/
lemma sum_piFinset₂_eq_sum_subtype' {t : ℕ} (Q : Finset ℤ) {M : Type*} [AddCommMonoid M]
    (F : (Fin t → ℤ) → (Fin t → ℤ) → M) :
    (∑ v0 ∈ Fintype.piFinset (fun _ : Fin t => Q),
      ∑ v1 ∈ Fintype.piFinset (fun _ : Fin t => Q), F v0 v1)
      = ∑ v0 : Fin t → ↥Q, ∑ v1 : Fin t → ↥Q,
          F (fun i => (v0 i).1) (fun i => (v1 i).1) := by
  rw [sum_piFinset_eq_sum_subtype' Q
    (fun v0 : Fin t → ℤ => ∑ v1 ∈ Fintype.piFinset (fun _ : Fin t => Q), F v0 v1)]
  refine Finset.sum_congr rfl (fun v0 _ => ?_)
  exact sum_piFinset_eq_sum_subtype' Q (fun v1 : Fin t → ℤ => F (fun i => (v0 i).1) v1)

/-- **The flat cube sum in the `Finset`-pi form is a nonnegative real** (`1 ≤ t`), for a direction
set `Q : Finset ℤ` and `W : (Fin t → ℤ) → ℂ`. -/
theorem flatCubeSum_nonneg_finset {t : ℕ} (ht : 1 ≤ t) (Q : Finset ℤ) (W : (Fin t → ℤ) → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      (∑ v0 ∈ Fintype.piFinset (fun _ : Fin t => Q),
        ∑ v1 ∈ Fintype.piFinset (fun _ : Fin t => Q),
          ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (W (Work.Peluse.Concat.mix ω v0 v1))) = (r : ℂ) := by
  classical
  obtain ⟨r, hr, hrW⟩ := flatCubeSum_nonneg (t := t) ht
    (X := ↥Q) (fun v : Fin t → ↥Q => W (fun i => (v i).1))
  refine ⟨r, hr, ?_⟩
  have hmix : ∀ (v0 v1 : Fin t → ↥Q) (ω : Fin t → Bool),
      (fun i => (Work.Peluse.Concat.mix ω v0 v1 i).1)
        = Work.Peluse.Concat.mix ω (fun i => (v0 i).1) (fun i => (v1 i).1) := by
    intro v0 v1 ω
    funext i
    by_cases h : ω i = true <;> simp [Work.Peluse.Concat.mix, h]
  have hsum : (∑ v0 : Fin t → ↥Q, ∑ v1 : Fin t → ↥Q,
        ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (W (Work.Peluse.Concat.mix ω (fun i => (v0 i).1) (fun i => (v1 i).1))))
      = Work.Peluse.Concat.cubeSum (fun _ : Fin t → Bool =>
          fun v : Fin t → ↥Q => W (fun i => (v i).1)) := by
    simp only [Work.Peluse.Concat.cubeSum, Work.Peluse.Concat.cubeProd]
    refine Finset.sum_congr rfl (fun v0 _ => Finset.sum_congr rfl (fun v1 _ => ?_))
    refine Finset.prod_congr rfl (fun ω _ => ?_)
    rw [hmix v0 v1 ω]
  rw [sum_piFinset₂_eq_sum_subtype' Q
    (fun v0 v1 : Fin t → ℤ => ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
      (W (Work.Peluse.Concat.mix ω v0 v1))), hsum, hrW]

end

end Work.Peluse.Ulower
