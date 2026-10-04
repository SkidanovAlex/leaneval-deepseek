import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

/-! ## Two elementary facts about periodic matrix-valued functions

`Periodic1` is periodicity by the unit shifts `x ↦ x + eᵢ`; iterating it gives invariance under
translation by an arbitrary integer vector, and this survives applying `reMat` and `det`.  Both are
needed below to reduce the (non-compact) parameter domain `univ ⊆ ℝⁿ` to a fundamental cube. -/

/-- **Invariance under integer translations.**  A function `1`-periodic in every coordinate is
invariant under translation by a vector with integer coordinates. -/
lemma periodic_intVec {n : ℕ} {β : Type*} {g : (Fin n → ℝ) → β} (hg : Work.Diff.STE.Periodic1 g)
    (m : Fin n → ℤ) : Function.Periodic g (fun i => (m i : ℝ)) := by
  have hsingle : ∀ i : Fin n, Function.Periodic g ((m i) • Pi.single i (1 : ℝ)) :=
    fun i => (show Function.Periodic g (Pi.single i (1 : ℝ)) from hg i).zsmul (m i)
  have hbasis : (∑ i : Fin n, (m i) • Pi.single i (1 : ℝ)) = fun i => (m i : ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have key : Function.Periodic g (∑ i : Fin n, (m i) • Pi.single i (1 : ℝ)) := by
    classical
    have hgen : ∀ s : Finset (Fin n),
        Function.Periodic g (∑ i ∈ s, (m i) • Pi.single i (1 : ℝ)) := by
      intro s
      refine Finset.induction ?base ?step s
      · simp
      · intro a s ha ih
        rw [Finset.sum_insert ha]
        exact (hsingle a).add_period ih
    simpa using hgen Finset.univ
  rwa [hbasis] at key

/-- `Periodic1` is preserved by `x ↦ det (reMat (g x))`. -/
lemma periodic1_det_reMat {n : ℕ} {g : (Fin n → ℝ) → Work.Diff.STE.Flat.MatC n}
    (hg : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.Periodic1 (fun x => (Work.Diff.STE.Flat.reMat (g x)).det) := by
  intro i x
  change (Work.Diff.STE.Flat.reMat (g (x + Pi.single i 1))).det
    = (Work.Diff.STE.Flat.reMat (g x)).det
  rw [hg i x]

/-- **A uniform lower bound for the determinant of a pointwise positive definite, jointly
continuous, space-periodic family of matrices.**

If `(t,x) ↦ seriesFunM (c t) x` is continuous and positive definite on the slab `[0,τ) × ℝⁿ` and
`1`-periodic in `x` at every time `t ∈ [0,τ)`, then the determinant of its real part is bounded
below by a positive constant on the smaller slab `[0,T] × ℝⁿ` for every `T < τ`.

Indeed `F := (t,x) ↦ det (reMat (seriesFunM (c t) x))` is continuous and strictly positive on the
slab, and it is periodic in `x` at every time; so its values on the non-compact set
`[0,T] × ℝⁿ` are exactly its values on the compact set `[0,T] × [0,1]ⁿ`, where the extreme value
theorem produces a strictly positive minimum. -/
theorem exists_pos_det_of_posDef {n : ℕ} {τ T : ℝ} (hτ : 0 < τ) (hTτ : T < τ)
    (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hcont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => Work.Diff.STE.Flat.seriesFunM (c p.1) p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ))
    (hpd : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ x : Fin n → ℝ,
      Work.Diff.STE.Flat.PosDefM (Work.Diff.STE.Flat.seriesFunM (c t) x))
    (hper : ∀ t ∈ Set.Ico (0 : ℝ) τ, Work.Diff.STE.Periodic1 (Work.Diff.STE.Flat.seriesFunM (c t))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : Fin n → ℝ,
      δ ≤ (Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x)).det := by
  classical
  by_cases hT : T ≤ 0
  · -- the slab `[0,T)` is empty
    exact ⟨1, one_pos, fun t ht x => absurd ht.2 (not_lt.mpr (le_trans hT ht.1))⟩
  have hTpos : 0 < T := not_le.mp hT
  -- the determinant function on the slab
  set F : ℝ × (Fin n → ℝ) → ℝ :=
    fun p => (Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c p.1) p.2)).det with hF
  have hFcont : ContinuousOn F (Set.Ico 0 τ ×ˢ Set.univ) := by
    -- `det ∘ reMat` is continuous, so it composes with the joint continuity hypothesis
    have hdet : Continuous (fun A : MatC n => (reMat A).det) := by
      refine (continuous_id.matrix_det :
        Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M.det)).comp ?_
      refine continuous_matrix (fun i j => ?_)
      exact Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply i))
    rw [hF]
    exact hdet.comp_continuousOn hcont
  have hFpos : ∀ p ∈ Set.Ico 0 τ ×ˢ Set.univ, 0 < F p := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    rw [hF]
    exact Matrix.PosDef.det_pos (hpd t ht x)
  -- the compact box `[0,T] × [0,1]ⁿ`
  set K : Set (ℝ × (Fin n → ℝ)) :=
    Set.Icc 0 T ×ˢ (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) with hK
  have hKc : IsCompact K := by
    rw [hK]
    exact isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hKsub : K ⊆ Set.Ico 0 τ ×ˢ Set.univ := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ⟨⟨ht.1, lt_of_le_of_lt ht.2 hTτ⟩, trivial⟩
  obtain ⟨δ, hδpos, hδle⟩ :=
    hKc.exists_forall_le' (hFcont.mono hKsub) (fun b hb => hFpos b (hKsub hb))
  refine ⟨δ, hδpos, ?_⟩
  intro t ht x
  have htτ : t ∈ Set.Ico 0 τ := ⟨ht.1, lt_trans ht.2 hTτ⟩
  -- `F (t, ·)` is periodic, so it suffices to control it on the fundamental cube
  have hperF : Work.Diff.STE.Periodic1 (fun x' => F (t, x')) := by
    have := periodic1_det_reMat (hper t htτ)
    simpa [hF] using this
  set m : Fin n → ℤ := fun i => ⌊x i⌋ with hm
  set y : Fin n → ℝ := fun i => x i - (m i : ℝ) with hy
  have hycube : y ∈ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1 := by
    intro i _
    have h1 : (m i : ℝ) ≤ x i := by rw [hm]; exact Int.floor_le (x i)
    have h2 : x i < (m i : ℝ) + 1 := by rw [hm]; exact Int.lt_floor_add_one (x i)
    exact ⟨by simp [hy]; linarith, by simp [hy]; linarith⟩
  have hsub : (fun x' => F (t, x')) (x - fun i => (m i : ℝ)) = (fun x' => F (t, x')) x :=
    (periodic_intVec hperF m).sub_eq x
  simp only at hsub
  have hyx : x - (fun i : Fin n => (m i : ℝ)) = y := by
    funext i; simp [hy]
  rw [hyx] at hsub
  have hfin := hδle (t, y) ⟨⟨ht.1, le_of_lt ht.2⟩, hycube⟩
  simp only [hF] at hsub hfin
  linarith

end Work.Diff.STE.flat
