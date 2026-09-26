import Mathlib
import Submission.Work.TorusCover.Basic

/-!
# The parametrisation is a covering map onto its range

Let `psi : ℝ → ℝ → R3` be continuous, `2π`-periodic in each variable, and injective modulo
`2π` (two parameter values have the same image under `psi` exactly when they differ by integer
multiples of `2π` in each coordinate).  Then `psiMapToRange psi : ℝ × ℝ → range (psiMap psi)` is
a covering map.

The strategy is to exhibit the covering structure through the free, properly discontinuous
action of `ℤ × ℤ` on the parameter plane `ℝ × ℝ` by the period shifts `v +ᵥ p = p + 2π v`:

* `psiMapToRange psi` is a quotient map onto its range.  Indeed, the fundamental box
  `[0, 2π] × [0, 2π]` is compact and maps onto `range (psiMap psi)`, so the restricted map is a
  quotient map between a compact space and a Hausdorff space; quotient-ness is then transported
  back along the continuous inclusion of the box (`IsCoinducing.of_comp`).
* Its fibres are exactly the orbits of the action (`hinj`).
* Every point has a neighbourhood `U` all of whose translates are disjoint: take the ball of
  radius `π`, since a nonzero period shift has norm at least `2π`.

Then `IsQuotientMap.isCoveringMapOn_of_vadd_disjoint` produces the trivialisations, and the
stabilisers are trivial (`2π v = 0` forces `v = 0`).
-/

open LeanEval.KnotTheory.PardonDistortion Set Filter

namespace Work.TorusCover

noncomputable section

/-! ### The period shift as an additive action of `ℤ × ℤ` on `ℝ × ℝ` -/

local instance instVAddPeriodShift : VAdd (ℤ × ℤ) (ℝ × ℝ) := ⟨fun v p => p + periodShift v⟩

lemma periodShift_add (v w : ℤ × ℤ) :
    periodShift (v + w) = periodShift v + periodShift w := by
  ext <;> simp only [periodShift, Prod.fst_add, Prod.snd_add] <;> push_cast <;> ring

lemma periodShift_neg (v : ℤ × ℤ) : periodShift (-v) = -periodShift v := by
  ext <;> simp only [periodShift, Prod.fst_neg, Prod.snd_neg] <;> push_cast <;> ring

local instance instAddActionPeriodShift : AddAction (ℤ × ℤ) (ℝ × ℝ) where
  zero_vadd p := by show p + periodShift 0 = p; simp [periodShift]
  add_vadd v w p := by
    show p + periodShift (v + w) = (p + periodShift w) + periodShift v
    rw [periodShift_add]; abel

local instance instContinuousConstVAddPeriodShift : ContinuousConstVAdd (ℤ × ℤ) (ℝ × ℝ) where
  continuous_const_vadd v := by
    show Continuous fun p : ℝ × ℝ => p + periodShift v
    exact continuous_id.add continuous_const

/-! ### Periodicity and the period lattice, from the raw hypotheses -/

variable {psi : ℝ → ℝ → R3}

lemma psiMap_add_periodShift_of_periodic
    (hper1 : ∀ x y : ℝ, psi (x + 2 * Real.pi) y = psi x y)
    (hper2 : ∀ x y : ℝ, psi x (y + 2 * Real.pi) = psi x y) (p : ℝ × ℝ) (v : ℤ × ℤ) :
    psiMap psi (p + periodShift v) = psiMap psi p := by
  have h2 : Function.Periodic (fun y : ℝ => psi (p.1 + (v.1 : ℝ) * (2 * Real.pi)) y)
      (2 * Real.pi) := fun y => hper2 _ y
  have e2 : psi (p.1 + (v.1 : ℝ) * (2 * Real.pi)) (p.2 + (v.2 : ℝ) * (2 * Real.pi)) =
      psi (p.1 + (v.1 : ℝ) * (2 * Real.pi)) p.2 := by
    simpa using h2.int_mul v.2 p.2
  have h1 : Function.Periodic (fun x : ℝ => psi x p.2) (2 * Real.pi) := fun x => hper1 x p.2
  have e1 : psi (p.1 + (v.1 : ℝ) * (2 * Real.pi)) p.2 = psi p.1 p.2 := by
    simpa using h1.int_mul v.1 p.1
  show psi (p.1 + (v.1 : ℝ) * (2 * Real.pi)) (p.2 + (v.2 : ℝ) * (2 * Real.pi)) = psi p.1 p.2
  rw [e2, e1]

lemma psiMap_eq_iff_sub_mem_lattice_of_inj
    (hinj : ∀ x y x' y' : ℝ, psi x y = psi x' y' ↔
      (∃ k : ℤ, x = x' + k * (2 * Real.pi)) ∧ (∃ k : ℤ, y = y' + k * (2 * Real.pi)))
    {p q : ℝ × ℝ} : psiMap psi p = psiMap psi q ↔ p - q ∈ lattice := by
  rw [psiMap_apply, psiMap_apply, hinj p.1 p.2 q.1 q.2, mem_lattice_iff']
  constructor
  · rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
    refine ⟨k, l, ?_⟩
    have h1 : p.1 - q.1 = (k : ℝ) * (2 * Real.pi) := by linarith
    have h2 : p.2 - q.2 = (l : ℝ) * (2 * Real.pi) := by linarith
    exact Prod.ext h1 h2
  · rintro ⟨k, l, h⟩
    refine ⟨⟨k, ?_⟩, ⟨l, ?_⟩⟩
    · have := congrArg Prod.fst h; simp only [Prod.fst_sub] at this; linarith
    · have := congrArg Prod.snd h; simp only [Prod.snd_sub] at this; linarith

lemma psiMap_eq_iff_exists_periodShift_of_inj
    (hinj : ∀ x y x' y' : ℝ, psi x y = psi x' y' ↔
      (∃ k : ℤ, x = x' + k * (2 * Real.pi)) ∧ (∃ k : ℤ, y = y' + k * (2 * Real.pi)))
    {p q : ℝ × ℝ} : psiMap psi q = psiMap psi p ↔ ∃ v : ℤ × ℤ, q = p + periodShift v := by
  have hiff : psiMap psi q = psiMap psi p ↔ q - p ∈ lattice :=
    psiMap_eq_iff_sub_mem_lattice_of_inj (psi := psi) hinj
  rw [hiff, mem_lattice_iff]
  exact ⟨fun ⟨v, hv⟩ => ⟨v, by rw [hv]; abel⟩, fun ⟨v, hv⟩ => ⟨v, by rw [hv]; abel⟩⟩

/-- Every real number can be shifted into `[0, 2π]` by an integer multiple of `2π`. -/
lemma exists_int_shift_mem_Icc (x : ℝ) :
    ∃ k : ℤ, x + (k : ℝ) * (2 * Real.pi) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨-⌊x / (2 * Real.pi)⌋, ?_⟩
  have hx : x + ((-⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) =
      (2 * Real.pi) * Int.fract (x / (2 * Real.pi)) := by
    rw [Int.fract]; push_cast; field_simp; ring
  rw [Set.mem_Icc, hx]
  constructor
  · exact mul_nonneg (le_of_lt hπ) (Int.fract_nonneg _)
  · have h1 := Int.fract_lt_one (x / (2 * Real.pi))
    have h2 := Int.fract_nonneg (x / (2 * Real.pi))
    nlinarith [Real.pi_pos]

/-! ### The covering map -/

set_option linter.style.haveILetI false in
set_option maxHeartbeats 1000000 in
theorem isCoveringMap_psiMapToRange (psi : ℝ → ℝ → LeanEval.KnotTheory.PardonDistortion.R3)
    (hcont : Continuous (fun p : ℝ × ℝ => psi p.1 p.2))
    (hper1 : ∀ x y : ℝ, psi (x + 2 * Real.pi) y = psi x y)
    (hper2 : ∀ x y : ℝ, psi x (y + 2 * Real.pi) = psi x y)
    (hinj : ∀ x y x' y' : ℝ, psi x y = psi x' y' ↔
      (∃ k : ℤ, x = x' + k * (2 * Real.pi)) ∧ (∃ k : ℤ, y = y' + k * (2 * Real.pi))) :
    IsCoveringMap (Work.TorusCover.psiMapToRange psi) := by
  classical
  have hcontΨ : Continuous (psiMapToRange psi) := by
    have h1 : Continuous (psiMap psi) := hcont
    exact h1.subtype_mk (fun p => Set.mem_range_self p)
  have hsurjΨ : Function.Surjective (psiMapToRange psi) := Set.rangeFactorization_surjective
  -- the fundamental box `[0, 2π] × [0, 2π]`
  set B : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) with hB
  have hBc : IsCompact B := isCompact_Icc.prod isCompact_Icc
  haveI hBcomp : CompactSpace B := isCompact_iff_compactSpace.mp hBc
  -- the box maps onto the range
  have hsurjBox : Function.Surjective ((psiMapToRange psi) ∘ (Subtype.val : B → ℝ × ℝ)) := by
    intro y
    obtain ⟨p, hp⟩ := y.2
    obtain ⟨k, hk⟩ := exists_int_shift_mem_Icc p.1
    obtain ⟨l, hl⟩ := exists_int_shift_mem_Icc p.2
    refine ⟨⟨(p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)), ⟨hk, hl⟩⟩, ?_⟩
    show psiMapToRange psi (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) = y
    have hq : psiMap psi (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) =
        psiMap psi p := by
      simpa [periodShift] using psiMap_add_periodShift_of_periodic (psi := psi) hper1 hper2 p (k, l)
    exact Subtype.ext (hq.trans hp)
  -- hence `psiMapToRange psi` is a quotient map
  have hquotBox : Topology.IsQuotientMap ((psiMapToRange psi) ∘ (Subtype.val : B → ℝ × ℝ)) :=
    Topology.IsQuotientMap.of_surjective_continuous hsurjBox (hcontΨ.comp continuous_subtype_val)
  have hcoind : Topology.IsCoinducing (psiMapToRange psi) :=
    Topology.IsCoinducing.of_comp continuous_subtype_val hcontΨ hquotBox.isCoinducing
  have hquotΨ : Topology.IsQuotientMap (psiMapToRange psi) := ⟨hcoind, hsurjΨ⟩
  -- the fibres are exactly the orbits
  have horbit : ∀ {e₁ e₂ : ℝ × ℝ},
      psiMapToRange psi e₁ = psiMapToRange psi e₂ ↔ e₁ ∈ AddAction.orbit (ℤ × ℤ) e₂ := by
    intro e₁ e₂
    rw [AddAction.mem_orbit_iff]
    have h1 : psiMapToRange psi e₁ = psiMapToRange psi e₂ ↔ psiMap psi e₁ = psiMap psi e₂ :=
      Subtype.ext_iff
    rw [h1]
    constructor
    · intro h
      obtain ⟨v, hv⟩ := (psiMap_eq_iff_exists_periodShift_of_inj (psi := psi) hinj).mp h.symm
      refine ⟨-v, ?_⟩
      show e₂ + periodShift (-v) = e₁
      rw [periodShift_neg, hv]; abel
    · rintro ⟨v, hv⟩
      rw [← hv]
      show psiMap psi (e₂ + periodShift v) = psiMap psi e₂
      exact psiMap_add_periodShift_of_periodic (psi := psi) hper1 hper2 e₂ v
  -- disjointness of translates: the ball of radius `π`
  have hdisj : ∀ e : ℝ × ℝ, ∃ U ∈ nhds e, ∀ g : ℤ × ℤ,
      ((fun x => g +ᵥ x) '' U ∩ U).Nonempty → g +ᵥ e = e := by
    intro e
    refine ⟨Metric.ball e Real.pi, Metric.ball_mem_nhds e Real.pi_pos, ?_⟩
    intro g hne
    by_contra hge
    have hg0 : g ≠ 0 := by
      intro h0
      exact hge (by rw [h0]; exact zero_vadd _ _)
    obtain ⟨x, hx1, hx2⟩ := hne
    obtain ⟨y, hyU, hyx⟩ := hx1
    have hxy : x = y + periodShift g := hyx.symm
    have hlt : ‖periodShift g‖ < 2 * Real.pi := by
      have h1 : periodShift g = x - y := by rw [hxy]; abel
      rw [h1, ← dist_eq_norm]
      have htri := dist_triangle x e y
      have hxe := Metric.mem_ball.mp hx2
      have hye := Metric.mem_ball.mp hyU
      have hye' : dist e y < Real.pi := by rw [dist_comm]; exact hye
      linarith [Real.pi_pos]
    exact absurd (two_pi_le_norm_periodShift hg0) (not_le.mpr hlt)
  -- every stabiliser is trivial
  have hstab : ∀ e : ℝ × ℝ, AddAction.stabilizer (ℤ × ℤ) e = ⊥ := by
    intro e
    rw [AddSubgroup.eq_bot_iff_forall]
    intro g hg
    rw [AddAction.mem_stabilizer_iff] at hg
    have h1 : e + periodShift g = e := hg
    have h0 : periodShift g = 0 := by
      have := congrArg (fun z : ℝ × ℝ => z - e) h1
      simpa using this
    exact periodShift_eq_zero_iff.mp h0
  refine isCoveringMap_iff_isCoveringMapOn_univ.mpr ?_
  have h := Topology.IsQuotientMap.isCoveringMapOn_of_vadd_disjoint (f := psiMapToRange psi)
    (G := ℤ × ℤ) hquotΨ horbit hdisj
  have hsetEq : {e : ℝ × ℝ | AddAction.stabilizer (ℤ × ℤ) e = ⊥} = Set.univ := by
    ext e; simp [hstab e]
  rwa [hsetEq, Set.image_univ_of_surjective hsurjΨ] at h

end

end Work.TorusCover
