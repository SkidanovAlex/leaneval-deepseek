import Mathlib
import Submission.Work.SurgeryInvariance.Defs

/-!
# A loop inside one fundamental square has vanishing winding

If the image of a closed curve `γ` of a parametrised torus `P` lies in the image of a single
*open* fundamental square `(a, a + 2π) × (b, b + 2π)` of the parameter plane, then the winding
vector of `γ` is zero: such a curve lifts into the square, and the lift is then trapped inside
the square, so that its displacement over one period must be a period shift `periodShift w` two
points of the square can only differ by if `w = 0`.

The proof is the standard "clopen partition of the connected line" argument: for a lift `Λ` of
`γ` and each `v : ℤ × ℤ` put

  `piece L a b v = {t | Λ t - periodShift v ∈ (a, a+2π) × (b, b+2π)}`.

Each `piece` is open (`piece_isOpen`), two of them are disjoint (`piece_disjoint`, because two
points of an open square never differ by a nonzero period shift,
`periodShift_eq_zero_of_add_mem_paramSquare`), and they cover `ℝ` (`psi` is injective modulo
`2π`).  A nonempty clopen subset of the connected line is everything
(`IsPreconnected.subset_isClopen`), so one `piece L a b v₀` is all of `ℝ`; evaluating it at
`0` and at `2π` and using `LiftOf.winding_spec` exhibits `L.winding` as a period shift between
two points of the square, hence `L.winding = 0`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- The open fundamental square `(a, a + 2π) × (b, b + 2π)` of the parameter plane. -/
def paramSquare (a b : ℝ) : Set (ℝ × ℝ) :=
  Set.Ioo a (a + 2 * Real.pi) ×ˢ Set.Ioo b (b + 2 * Real.pi)

lemma mem_paramSquare {a b : ℝ} {p : ℝ × ℝ} :
    p ∈ paramSquare a b ↔ p.1 ∈ Set.Ioo a (a + 2 * Real.pi) ∧
      p.2 ∈ Set.Ioo b (b + 2 * Real.pi) :=
  Set.mem_prod

/-- **Two points of an open fundamental square never differ by a nonzero period shift.**  If
`q = p + periodShift v` with `p` and `q` both in the open square `(a, a+2π) × (b, b+2π)`, then
`v = 0`: adding a nonzero multiple of `2π` to a coordinate leaves the interval
`(a, a + 2π)` of length `2π`. -/
lemma periodShift_eq_zero_of_add_mem_paramSquare {a b : ℝ} {p q : ℝ × ℝ}
    (hp : p ∈ paramSquare a b) (hq : q ∈ paramSquare a b) {v : ℤ × ℤ}
    (h : q = p + Work.TorusCover.periodShift v) : v = 0 := by
  rw [mem_paramSquare] at hp hq
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  have hq1' : q.1 = p.1 + (v.1 : ℝ) * (2 * Real.pi) := by
    rw [h]; simp [Work.TorusCover.periodShift]
  have hq2' : q.2 = p.2 + (v.2 : ℝ) * (2 * Real.pi) := by
    rw [h]; simp [Work.TorusCover.periodShift]
  have h1 : v.1 = 0 := by
    have hlt : ((v.1 : ℤ) : ℝ) < 1 := by nlinarith [hp1.1, hq1.2, hq1', Real.pi_pos]
    have hgt : (-1 : ℝ) < ((v.1 : ℤ) : ℝ) := by nlinarith [hp1.2, hq1.1, hq1', Real.pi_pos]
    have hlt' : v.1 < (1 : ℤ) := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < v.1 := by exact_mod_cast hgt
    omega
  have h2 : v.2 = 0 := by
    have hlt : ((v.2 : ℤ) : ℝ) < 1 := by nlinarith [hp2.1, hq2.2, hq2', Real.pi_pos]
    have hgt : (-1 : ℝ) < ((v.2 : ℤ) : ℝ) := by nlinarith [hp2.2, hq2.1, hq2', Real.pi_pos]
    have hlt' : v.2 < (1 : ℤ) := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < v.2 := by exact_mod_cast hgt
    omega
  exact Prod.ext h1 h2

/-- The parameters `t` at which a lift `(Θ, Φ)` of a closed curve, shifted by `-periodShift v`,
lies in the fundamental square `(a, a+2π) × (b, b+2π)`. -/
def piece {P : Work.CoreTopology.ParamTorus} {γ : Work.CoreTopology.ClosedCurve P}
    (L : Work.CoreTopology.LiftOf P γ) (a b : ℝ) (v : ℤ × ℤ) : Set ℝ :=
  {t : ℝ | (L.Θ t, L.Φ t) - Work.TorusCover.periodShift v ∈ paramSquare a b}

lemma mem_piece {P : Work.CoreTopology.ParamTorus} {γ : Work.CoreTopology.ClosedCurve P}
    (L : Work.CoreTopology.LiftOf P γ) (a b : ℝ) (v : ℤ × ℤ) (t : ℝ) :
    t ∈ piece L a b v ↔
      (L.Θ t, L.Φ t) - Work.TorusCover.periodShift v ∈ paramSquare a b :=
  Iff.rfl

/-- Each `piece` is open, being the preimage of the open square under the continuous map
`t ↦ Λ t - periodShift v`. -/
lemma piece_isOpen {P : Work.CoreTopology.ParamTorus} {γ : Work.CoreTopology.ClosedCurve P}
    (L : Work.CoreTopology.LiftOf P γ) (a b : ℝ) (v : ℤ × ℤ) :
    IsOpen (piece L a b v) := by
  have hcont : Continuous fun t : ℝ => (L.Θ t, L.Φ t) - Work.TorusCover.periodShift v :=
    (L.contΘ.prodMk L.contΦ).sub continuous_const
  exact (isOpen_Ioo.prod isOpen_Ioo).preimage hcont

/-- Distinct `piece`s are disjoint: a point of the square shifted by two different period
shifts gives two points of the square differing by a nonzero period shift. -/
lemma piece_disjoint {P : Work.CoreTopology.ParamTorus} {γ : Work.CoreTopology.ClosedCurve P}
    (L : Work.CoreTopology.LiftOf P γ) (a b : ℝ) {v w : ℤ × ℤ} (h : v ≠ w) :
    Disjoint (piece L a b v) (piece L a b w) := by
  rw [Set.disjoint_left]
  intro t ht htw
  have hp : (L.Θ t, L.Φ t) - Work.TorusCover.periodShift w ∈ paramSquare a b := htw
  have hq : (L.Θ t, L.Φ t) - Work.TorusCover.periodShift v ∈ paramSquare a b := ht
  have hEq : (L.Θ t, L.Φ t) - Work.TorusCover.periodShift v
      = ((L.Θ t, L.Φ t) - Work.TorusCover.periodShift w)
        + Work.TorusCover.periodShift (w - v) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Work.TorusCover.periodShift] <;> push_cast <;> ring
  exact h (sub_eq_zero.mp (periodShift_eq_zero_of_add_mem_paramSquare hp hq hEq)).symm

/-- A closed curve of a parametrised torus whose image lies in the image of one open
fundamental square `(a, a+2π) × (b, b+2π)` of the parameter plane has vanishing winding
vector.  Proof route: a lift `Λ = (Θ, Φ)` of `γ` exists; for each `v : ℤ × ℤ` the set
`A v = {t | Λ t - periodShift v ∈ U}` is open, the `A v` are pairwise disjoint (two points of
the open square `U` never differ by a nonzero `2πℤ²`-vector) and cover `ℝ`
(`ψ p = ψ q` implies `p - q ∈ 2πℤ²`); hence each is clopen in `ℝ`, so exactly one is everything.
Then `Λ` minus a lattice vector takes all its values in `U`, and
`Λ (t + 2π) - Λ t = periodShift w` for the winding vector `w`; two points of `U` differing by
`periodShift w` forces `w = 0`. -/
theorem fundamentalSquare_winding_zero
    (P : Work.CoreTopology.ParamTorus) (a b : ℝ)
    (γ : Work.CoreTopology.ClosedCurve P)
    (hγ : ∀ t : ℝ, ∃ p : ℝ × ℝ,
      p.1 ∈ Set.Ioo a (a + 2 * Real.pi) ∧ p.2 ∈ Set.Ioo b (b + 2 * Real.pi) ∧
      P.psi p.1 p.2 = γ t) :
    Work.SurgeryInvariance.windingOf P γ = (0, 0) := by
  classical
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
  rw [Work.SurgeryInvariance.windingOf_eq P γ L]
  -- the pieces `A v` cover `ℝ`: the lift of `γ` can always be brought back into the square
  have hcover : ∀ t : ℝ, ∃ v : ℤ × ℤ, t ∈ piece L a b v := by
    intro t
    obtain ⟨p, hp1, hp2, hppsi⟩ := hγ t
    have hpv : P.psi p.1 p.2 = P.psi (L.Θ t) (L.Φ t) := hppsi.trans (L.lifts t).symm
    obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := (P.psi_eq_iff p.1 p.2 (L.Θ t) (L.Φ t)).mp hpv
    refine ⟨(-k, -l), ?_⟩
    have hpt : (L.Θ t, L.Φ t) - Work.TorusCover.periodShift (-k, -l) = p := by
      ext
      · simp only [Prod.fst_sub, Work.TorusCover.periodShift]
        push_cast
        linarith [hk]
      · simp only [Prod.snd_sub, Work.TorusCover.periodShift]
        push_cast
        linarith [hl]
    show (L.Θ t, L.Φ t) - Work.TorusCover.periodShift (-k, -l) ∈ paramSquare a b
    rw [hpt]
    exact mem_paramSquare.mpr ⟨hp1, hp2⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v : ℤ × ℤ, (0 : ℝ) ∈ piece L a b v := hcover 0
  -- that `piece` is clopen, hence everything (the line is connected)
  have hcompl : IsOpen (piece L a b v₀)ᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨w, hw⟩ := hcover t
    have hwne : w ≠ v₀ := by rintro rfl; exact ht hw
    exact ⟨piece L a b w,
      fun s hs hsv => (Set.disjoint_left.mp (piece_disjoint L a b hwne)) hs hsv,
      piece_isOpen L a b w, hw⟩
  have hclopen : IsClopen (piece L a b v₀) :=
    ⟨IsClosed.mk hcompl, piece_isOpen L a b v₀⟩
  have huniv : (Set.univ : Set ℝ) ⊆ piece L a b v₀ :=
    IsPreconnected.subset_isClopen isPreconnected_univ hclopen ⟨0, Set.mem_univ 0, hv₀⟩
  have hall : ∀ t : ℝ, t ∈ piece L a b v₀ := fun t => huniv (Set.mem_univ t)
  -- the displacement of the lift over one period is then a period shift inside the square
  have hshift : (L.Θ (2 * Real.pi), L.Φ (2 * Real.pi)) - Work.TorusCover.periodShift v₀
      = ((L.Θ 0, L.Φ 0) - Work.TorusCover.periodShift v₀)
        + Work.TorusCover.periodShift L.winding := by
    have hs := L.winding_spec
    ext
    · simp only [Prod.fst_sub, Prod.fst_add, Work.TorusCover.periodShift]
      linarith [hs.1]
    · simp only [Prod.snd_sub, Prod.snd_add, Work.TorusCover.periodShift]
      linarith [hs.2]
  have hzero : L.winding = 0 :=
    periodShift_eq_zero_of_add_mem_paramSquare (hall 0) (hall (2 * Real.pi)) hshift
  rw [hzero]
  rfl

end

end Work.BoxShrink.PinchOff
