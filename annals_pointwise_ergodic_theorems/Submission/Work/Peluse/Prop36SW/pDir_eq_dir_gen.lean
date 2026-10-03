import Mathlib
import Submission.Work.Peluse.Prop36SW.existsSlotSetEquivI
import Submission.Work.Peluse.ladderBaseDefs

open scoped BigOperators

namespace Work.Peluse.Prop36SW

open Work.Peluse.UControl

/-- **The level-`(j+1)` direction of a subset `ω` is the sum of the level-`j` slot
contributions, with the level-`j` parameters read from a level-`(j+1)` family.**

This is the variant of `Work.Peluse.Prop36SW.sumSlotDir` in which the level-`j` slot coefficients
`(d - j)·dir d c j (par j s) ·` are evaluated on `D.pad (j + 1) al`, so that the level-`j`
coordinates of the parameter family are the *actual* level-`j` parameters `al ⟨j, _⟩` rather than
the junk value `0` produced by `D.pad j`.  Unfolding `IdxDatum.dir` at the level `j+1` expresses the
direction of the level-`(j+1)` index `omega'` as
`∑_{t ∈ omega'.1} (((d - j)·dir d c j (par j t) af)) · af (j+1) t`, with `af` the family whose
levels `≤ j` are `D.pad (j + 1) al` and whose level `j+1` coordinates are `a'`; by
`dir_congr` (`Work.Peluse.dir_congr`) only the levels `≤ j` matter for the inner `dir d c j`, which
is where the two sides meet. -/
theorem sumSlotDir_gen (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (j : ℕ)
    (al : D.Idx (j + 1)) (a' : D.S (j + 1) → ℤ)
    (omega : Finset (Slot (D.S (j + 1)) (fun _ => 1))) (omega' : D.I (j + 1))
    (h : omega'.1 = omega.image (fun s => s.1)) :
    (∑ s ∈ omega, ((d : ℤ) - (j : ℤ)) * D.dir d c j (D.par j s.1) (D.pad (j + 1) al) * a' s.1)
      = D.dir d c (j + 1) omega'
          (fun j' s => if hj : j' = j + 1 then a' (hj ▸ s) else D.pad (j + 1) al j' s) := by
  set af : (j' : ℕ) → D.S j' → ℤ :=
    fun j' s => if hj : j' = j + 1 then a' (hj ▸ s) else D.pad (j + 1) al j' s with haf
  -- the level-`(j+1)` coordinates of `af` are those of `a'`
  have htop : af (j + 1) = a' := by
    funext t
    rw [haf]; simp
  -- the levels `≤ j` of `af` are those of `D.pad (j + 1) al`
  have hlo : ∀ j' ≤ j, af j' = D.pad (j + 1) al j' := by
    intro j' hj'
    have hne : j' ≠ j + 1 := by omega
    funext s
    rw [haf]; simp only [dif_neg hne]
  -- the first projection is injective on the level-`(j+1)` slots
  have hinj : ∀ s t : Slot (D.S (j + 1)) (fun _ => 1), s.1 = t.1 → s = t := by
    intro s t hst
    obtain ⟨s1, s2⟩ := s
    obtain ⟨t1, t2⟩ := t
    simp only [Sigma.mk.injEq]
    refine ⟨hst, ?_⟩
    rw [heq_iff_eq]
    exact Subsingleton.elim _ _
  -- reindex the sum over the slots by the subset they belong to
  have hsum : (∑ s ∈ omega, ((d : ℤ) - (j : ℤ)) * D.dir d c j (D.par j s.1) (D.pad (j + 1) al) * a' s.1)
      = ∑ t ∈ omega'.1, ((d : ℤ) - (j : ℤ)) * D.dir d c j (D.par j t) (D.pad (j + 1) al) * a' t := by
    rw [h]
    exact (Finset.sum_image
      (f := fun t => ((d : ℤ) - (j : ℤ)) * D.dir d c j (D.par j t) (D.pad (j + 1) al) * a' t)
      (g := fun s : Slot (D.S (j + 1)) (fun _ => 1) => s.1) (fun x _ y _ hxy => hinj x y hxy)).symm
  rw [hsum]
  -- unfold the level-`(j+1)` direction
  rw [show D.dir d c (j + 1) omega' af
        = ∑ t ∈ omega'.1, (((d : ℤ) - (j : ℤ)) * D.dir d c j (D.par j t) af) * af (j + 1) t
      from rfl]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [dir_congr D d c j (D.par j t) af (D.pad (j + 1) al) (fun j' hj' s' => by rw [hlo j' hj']),
    htop]

theorem pDir_eq_dir_gen (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (j : ℕ) (al : D.Idx (j + 1))
    (a' : D.S (j + 1) → ℤ) (H : ℕ) :
    ∃ e : Work.Peluse.UControl.SlotSet (D.S (j + 1)) (fun _ => 1) ≃ D.I (j + 1),
      ∀ ω : Work.Peluse.UControl.SlotSet (D.S (j + 1)) (fun _ => 1),
        Work.Peluse.UControl.pDir (p := fun (s : D.S (j + 1)) (_ : Fin 0 → ℤ) =>
            ((d : ℤ) - (j : ℤ)) * D.dir d c j (D.par j s) (D.pad (j + 1) al))
          H (fun _ => (0 : ℤ)) (fun s => a' s.1) ω
          = Work.Peluse.arithIcc (D.dir d c (j + 1) (e ω)
              (fun j' s => if hj : j' = j + 1 then a' (hj ▸ s) else D.pad (j + 1) al j' s)) H := by
  obtain ⟨e, he⟩ := existsSlotSetEquivI D (j + 1)
  refine ⟨e, fun ω => ?_⟩
  rw [Work.Peluse.UControl.pDir, sumSlotDir_gen D d c j al a' ω.1 (e ω) (he ω)]

end Work.Peluse.Prop36SW
