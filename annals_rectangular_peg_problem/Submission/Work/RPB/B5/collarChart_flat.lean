import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.chartJets_levelPt_contDiff

/-!
# B5: the difference of the collar and the chart is flat at `σ = 0`

`Work.RPB.B5.collarChart_flat` states that the `σ`-profile of the assembled family's *difference*
at the seam `σ = 0`

`σ ↦ collarPt Γc Ac τ σ t - W τ t (ρh τ t σ)`

has vanishing one-sided (`σ ≥ 0`) derivatives of every order `≤ 8` at `σ = 0`.  This is the
`hflat` hypothesis of `Work.RPB.B5.contDiffOn_flat_trunc`, and it is a direct consequence of the
jet hypothesis `LagData.σjet`.

## The proof

Write `F σ = collarPt Γc Ac τ σ t = levelPt (Γc τ σ t) σ (Ac τ σ t)` for the collar profile and
`G σ = W τ t (ρh τ t σ)` for the chart profile.  The argument is short once two structural facts
are in place:

* **Both profiles are `C⁸` at `0`** (`hFcd`, `hGcd` below).
  * `G`: `ρh` is `ContDiffOn` on the open box `Ioo (-κ) κ` in its *third* argument and maps into
    `Ioo (-ρ₀) ρ₀` (`hρhv`), where `W` is `ContDiffOn` (`hWsm`); both slices are extracted with
    `slice_contDiffAt_openBox` (`0` is an interior point of both boxes).
  * `F`: `Γc` and `Ac` are only `ContDiffOn` on the half space `{third argument ≥ 0}`, but they
    are quasi-periodic in the *angle* (the third argument), so shifting the angle by `2πk` into
    `{t ≥ 0}` (`hΓper`, `hAper`) exhibits the `σ`-slice as smooth at `σ = 0` *from both sides*
    (`slice_contDiffAt_halfSpace`); `levelPt` is smooth (`chartJets_levelPt_contDiff`).
* **`0 ∈ Ici 0`**: `iteratedFDerivWithin_insert` says that the `n`-th derivative of `f` within a
  set does not see whether the base point belongs to the set, so the one-sided derivative at
  `0 ∉ Ioi 0` equals the derivative within `Ici 0`, and `Mathlib`'s additivity lemma
  `iteratedDerivWithin_sub` (which wants its base point in the set) becomes applicable:
  ```
  iteratedDerivWithin j (F - G) (Ioi 0) 0
    = iteratedDerivWithin j (F - G) (Ici 0) 0
    = iteratedDerivWithin j F (Ici 0) 0 - iteratedDerivWithin j G (Ici 0) 0
    = iteratedDeriv j F 0 - iteratedDeriv j G 0.
  ```
  Since `0 ∈ Ici 0` and `F`, `G` are `C⁸` (hence `C^j`) at `0`, the last two terms are the honest
  two-sided derivatives.  Finally `iteratedDeriv j F 0 = iteratedDeriv j G 0`, because `σjet`
  identifies the one-sided (`Ioi 0`) derivative of `F` with `iteratedDeriv j G 0`, and the
  one-sided derivative of `F` is the two-sided one by the same `insert` invariance.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Smoothness of one-variable slices of the `ContDiffOn` fields of `LagData` -/

/-- The slice `ρ ↦ F (τ, t, ρ)` at `ρ = 0` of a function smooth on the box
`Icc 0 1 ×ˢ univ ×ˢ Ioo a b` with `a < 0 < b` is smooth at `0`. -/
private theorem slice_contDiffAt_openBox {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × (ℝ × ℝ) → E} {a b τ t : ℝ} {n : ℕ}
    (hF : ContDiffOn ℝ n F (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo a b))
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (ha : a < 0) (hb : 0 < b) :
    ContDiffAt ℝ n (fun ρ : ℝ => F (τ, t, ρ)) 0 := by
  have hglob : ContDiff ℝ n (fun ρ : ℝ => (τ, t, ρ)) := by fun_prop
  have hi : ContDiffWithinAt ℝ n (fun ρ : ℝ => (τ, t, ρ)) (Set.Ioo a b) 0 :=
    hglob.contDiffWithinAt
  have hFW : ContDiffWithinAt ℝ n F (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo a b)
      (τ, t, 0) := hF.contDiffWithinAt (x := (τ, t, 0)) ⟨hτ, Set.mem_univ t, ha, hb⟩
  have hmt : Set.MapsTo (fun ρ : ℝ => (τ, t, ρ)) (Set.Ioo a b)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo a b) :=
    fun ρ hρ => ⟨hτ, Set.mem_univ t, hρ⟩
  exact (hFW.comp (0 : ℝ) hi hmt).contDiffAt (isOpen_Ioo.mem_nhds ⟨ha, hb⟩)

/-- Iterating the quasi-periodicity relation `f τ σ (t + 2π) = f τ σ t + c`. -/
private lemma quasi_periodic_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ → ℝ → E) (c : E)
    (hper : ∀ τ σ t, f τ σ (t + 2 * Real.pi) = f τ σ t + c) (k : ℕ) (τ σ t : ℝ) :
    f τ σ (t + 2 * Real.pi * (k : ℝ)) = f τ σ t + (k : ℝ) • c := by
  induction k generalizing t with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    rw [show t + 2 * Real.pi * ((n : ℝ) + 1)
        = (t + 2 * Real.pi * (n : ℝ)) + 2 * Real.pi by ring]
    rw [hper τ σ (t + 2 * Real.pi * (n : ℝ)), ih t]
    rw [add_smul, one_smul]
    abel

/-- The `σ`-slice `σ ↦ f τ σ t` at `σ = 0` of a family `f` which is `C⁸` on the set where the
*third* argument is `≥ 0` (and the first lies in `Icc 0 1`) and which is quasi-periodic in that
third argument with shift `c`: shifting the third argument by `2πk` into the half line `{· ≥ 0}`
makes the slice smooth at `0` (from both sides). -/
private theorem slice_contDiffAt_halfSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ → ℝ → E) (c : E)
    (hsm : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)))
    (hper : ∀ τ σ t, f τ σ (t + 2 * Real.pi) = f τ σ t + c)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    ContDiffAt ℝ 8 (fun σ : ℝ => f τ σ t) 0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 < t + 2 * Real.pi * (k : ℝ) := by
    obtain ⟨k, hk⟩ := exists_nat_gt (-t / (2 * Real.pi))
    refine ⟨k, ?_⟩
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have h := mul_lt_mul_of_pos_right hk hπ
    rw [div_mul_cancel₀ _ (ne_of_gt hπ)] at h
    linarith
  have hshift : ContDiffAt ℝ 8 (fun σ : ℝ => f τ σ (t + 2 * Real.pi * (k : ℝ))) 0 := by
    have hpt : (τ, (0, t + 2 * Real.pi * (k : ℝ))) ∈
        Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ) :=
      ⟨hτ, Set.mem_univ _, le_of_lt hk⟩
    have hFw : ContDiffWithinAt ℝ 8 (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ))
        (τ, (0, t + 2 * Real.pi * (k : ℝ))) := hsm.contDiffWithinAt hpt
    have hg : ContDiffWithinAt ℝ 8 (fun σ : ℝ => (τ, (σ, t + 2 * Real.pi * (k : ℝ))))
        Set.univ 0 :=
      (by fun_prop : ContDiff ℝ 8
        (fun σ : ℝ => (τ, (σ, t + 2 * Real.pi * (k : ℝ))))).contDiffWithinAt
    have hmt : Set.MapsTo (fun σ : ℝ => (τ, (σ, t + 2 * Real.pi * (k : ℝ)))) Set.univ
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) :=
      fun σ _ => ⟨hτ, Set.mem_univ _, le_of_lt hk⟩
    simpa only [Function.comp_def] using (hFw.comp (0 : ℝ) hg hmt).contDiffAt (by simp)
  have heq : (fun σ : ℝ => f τ σ t)
      = fun σ : ℝ => f τ σ (t + 2 * Real.pi * (k : ℝ)) - (k : ℝ) • c := by
    funext σ
    rw [quasi_periodic_nat f c hper k τ σ t]
    abel
  rw [heq]
  exact hshift.sub contDiffAt_const

/-! ## Moving the base point `0` into the set -/

/-- `Ici 0 = insert 0 (Ioi 0)`. -/
private lemma Ici_zero_eq_insert_Ioi : Set.Ici (0 : ℝ) = insert 0 (Set.Ioi (0 : ℝ)) := by
  ext y
  simp only [Set.mem_Ici, Set.mem_insert_iff, Set.mem_Ioi]
  constructor
  · intro h
    rcases eq_or_lt_of_le h with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'
  · rintro (rfl | h)
    · exact le_refl 0
    · exact le_of_lt h

/-- `iteratedDerivWithin` within a set does not see whether the base point belongs to the set
(`iteratedFDerivWithin_insert`): so the one-sided derivative at `0 ∉ Ioi 0` is the derivative
within `Ici 0`, where the base point *does* belong to the set. -/
private lemma iteratedDerivWithin_Ioi_eq_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (h : ℝ → E) :
    iteratedDerivWithin j h (Set.Ioi (0 : ℝ)) 0 = iteratedDerivWithin j h (Set.Ici (0 : ℝ)) 0 := by
  simp only [iteratedDerivWithin]
  rw [Ici_zero_eq_insert_Ioi, iteratedFDerivWithin_insert]

/-! ## The flatness of the difference at `σ = 0` -/

theorem collarChart_flat (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ j : ℕ, j ≤ 8 →
      iteratedDerivWithin j
        (fun σ : ℝ => Work.RPB.B5.collarPt D.Γc D.Ac τ σ t - D.W τ t (D.ρh τ t σ))
        (Set.Ioi (0 : ℝ)) 0 = 0 := by
  intro τ hτ t j hj
  -- the collar profile `F` and the chart profile `G`
  set F : ℝ → Work.RPV.PS := fun σ => Work.RPB.B5.collarPt D.Γc D.Ac τ σ t with hFdef
  set G : ℝ → Work.RPV.PS := fun σ => D.W τ t (D.ρh τ t σ) with hGdef
  change iteratedDerivWithin j (F - G) (Set.Ioi (0 : ℝ)) 0 = 0
  -- ## smoothness of the chart profile `G` at `0`
  have hGcd : ContDiffAt ℝ 8 G 0 := by
    have hWslice : ContDiffAt ℝ 8 (fun ρ : ℝ => D.W τ t ρ) (D.ρh τ t 0) := by
      rw [D.hρh0 τ hτ t]
      exact slice_contDiffAt_openBox D.hWsm hτ (by linarith [D.hρ₀]) D.hρ₀
    have hρhslice : ContDiffAt ℝ 8 (fun σ : ℝ => D.ρh τ t σ) 0 :=
      slice_contDiffAt_openBox D.hρh hτ (by linarith [D.hκ]) D.hκ
    have h := hWslice.comp (0 : ℝ) hρhslice
    simpa only [Function.comp_def] using h
  -- ## smoothness of the collar profile `F` at `0`
  have hFcd : ContDiffAt ℝ 8 F 0 := by
    have hΓslice : ContDiffAt ℝ 8 (fun σ : ℝ => D.Γc τ σ t) 0 :=
      slice_contDiffAt_halfSpace D.Γc 0 D.hΓsm
        (fun τ σ t => by rw [D.hΓper τ σ t, add_zero]) hτ t
    have hAslice : ContDiffAt ℝ 8 (fun σ : ℝ => D.Ac τ σ t) 0 :=
      slice_contDiffAt_halfSpace D.Ac (2 * Real.pi) D.hAsm
        (fun τ σ t => D.hAper τ σ t) hτ t
    have hinner : ContDiffAt ℝ 8 (fun σ : ℝ => (D.Γc τ σ t, (σ, D.Ac τ σ t))) 0 :=
      hΓslice.prodMk ((contDiffAt_id (x := (0 : ℝ))).prodMk hAslice)
    have houter : ContDiffAt ℝ 8 (fun p : ℂ × (ℝ × ℝ) => Work.RPV.levelPt p.1 p.2.1 p.2.2)
        (D.Γc τ 0 t, (0, D.Ac τ 0 t)) := chartJets_levelPt_contDiff.contDiffAt
    have h := houter.comp (0 : ℝ) hinner
    simpa only [Function.comp_def, hFdef, Work.RPB.B5.collarPt] using h
  -- ## the two profiles have the same `j`-th derivative at `0`
  have hjc : ((j : ℕ) : WithTop ℕ∞) ≤ ((8 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
  have hIF : iteratedDerivWithin j F (Set.Ioi (0 : ℝ)) 0 = iteratedDeriv j F 0 := by
    rw [iteratedDerivWithin_Ioi_eq_Ici,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) (hFcd.of_le hjc) (by simp)]
  have hσjet : iteratedDerivWithin j F (Set.Ioi (0 : ℝ)) 0 = iteratedDeriv j G 0 := by
    simpa only [hFdef, hGdef, Work.RPB.B5.collarPt] using D.σjet τ hτ t j hj
  have hderivs : iteratedDeriv j F 0 = iteratedDeriv j G 0 := by rw [← hIF, hσjet]
  -- ## additivity on `Ici 0`, where the base point `0` belongs to the set
  have hFj : ContDiffWithinAt ℝ ((j : ℕ) : WithTop ℕ∞) F (Set.Ici (0 : ℝ)) 0 :=
    (hFcd.of_le hjc).contDiffWithinAt
  have hGj : ContDiffWithinAt ℝ ((j : ℕ) : WithTop ℕ∞) G (Set.Ici (0 : ℝ)) 0 :=
    (hGcd.of_le hjc).contDiffWithinAt
  have hsub : iteratedDerivWithin j (F - G) (Set.Ici (0 : ℝ)) 0
      = iteratedDerivWithin j F (Set.Ici (0 : ℝ)) 0
        - iteratedDerivWithin j G (Set.Ici (0 : ℝ)) 0 :=
    iteratedDerivWithin_sub (s := Set.Ici (0 : ℝ)) (x := 0) (by simp) (uniqueDiffOn_Ici 0)
      hFj hGj
  have hFval : iteratedDerivWithin j F (Set.Ici (0 : ℝ)) 0 = iteratedDeriv j F 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) (hFcd.of_le hjc) (by simp)
  have hGval : iteratedDerivWithin j G (Set.Ici (0 : ℝ)) 0 = iteratedDeriv j G 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) (hGcd.of_le hjc) (by simp)
  rw [iteratedDerivWithin_Ioi_eq_Ici, hsub, hFval, hGval, hderivs, sub_self]

end Work.RPB.B5
