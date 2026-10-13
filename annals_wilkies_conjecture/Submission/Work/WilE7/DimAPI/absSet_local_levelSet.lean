import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.Nondrop.FibreCalc
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.DimAPI

open WilkiesDesign WilkiesDesign.E

/-! ## The empty base point: `absPt` agrees with appending the (unique) element of `ℝ⁰`

The statement below concerns an *absolute* stratum `S : Stratum 0 N`, i.e. `p = 0`.  The base
projection `projFirst 0 N z` lives in the one-point space `ℝ⁰ = Fin 0 → ℝ`, so all the base
manipulation reduces to the reindexing `absPt : ℝ^{0+N} → ℝ^N` and the round trips between
`absPt` and `Fin.append`.  These three lemmas are the whole content of that reduction. -/

/-- `absPt z i = z (Fin.natAdd 0 i)`: the `Fin (0 + N)` index of `absPt` is the canonical
`Fin.natAdd` embedding of `Fin N`. -/
lemma absPt_apply_natAdd {N : ℕ} (z : Fin (0 + N) → ℝ) (i : Fin N) :
    MainDesign.absPt z i = z (Fin.natAdd 0 i) :=
  congrArg z (by ext; simp [Fin.natAdd])

/-- Appending the (arbitrary, hence unique) point of `ℝ⁰` and then applying `absPt` recovers the
point: `absPt (Fin.append x w) = w`. -/
lemma absPt_append {N : ℕ} (x : Fin 0 → ℝ) (w : Fin N → ℝ) :
    MainDesign.absPt (Fin.append x w) = w := by
  funext i
  rw [absPt_apply_natAdd, Fin.append_right]

/-- The other round trip: `Fin.append x (absPt z) = z`. -/
lemma append_absPt {N : ℕ} (x : Fin 0 → ℝ) (z : Fin (0 + N) → ℝ) :
    Fin.append x (MainDesign.absPt z) = z := by
  funext i
  refine Fin.addCases (fun j => j.elim0) (fun l => ?_) i
  rw [Fin.append_right, absPt_apply_natAdd]

/-- Continuity of `w ↦ Fin.append x w` for `x : ℝ⁰`: every component is a coordinate
projection. -/
lemma continuous_append_zero {N : ℕ} (x : Fin 0 → ℝ) :
    Continuous (fun w : Fin N → ℝ => Fin.append x w) := by
  refine continuous_pi fun i => ?_
  refine Fin.addCases (motive := fun i => Continuous (fun w : Fin N → ℝ => Fin.append x w i))
    (fun j => j.elim0) (fun l => ?_) i
  simp only [Fin.append_right]
  exact continuous_apply l

/-- **The absolute stratum is locally the level set of the fibre map of `S`.**

For a `Good` absolute stratum `S : Stratum 0 N` and `z ∈ S.X.set`, writing `absSet S ⊆ ℝ^N` for
`S` reindexed by `absPt`:

* every point of `absSet S` is a zero of the fibre map `fnpFibre S (projFirst 0 N z)` (the
  equations of `S` restricted to the fibre over the base point of `z`), and
* the same is *locally* an equivalence: near `absPt z`, a zero of the fibre map necessarily lies
  in `absSet S`.

Both are immediate from `Stratum.Good` (`good_eqs` respectively `good_local`), transported across
the bijection `absPt`. -/
theorem absSet_local_levelSet {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) (hS : S.Good)
    (z : Fin (0 + N) → ℝ) (hz : z ∈ S.X.set) :
    (∀ w ∈ Work.WilE7.MainDesign.absSet S,
        Work.WilE7.Nondrop.fnpFibre S (WilkiesDesign.E.projFirst 0 N z) w = 0) ∧
      (∀ᶠ w in nhds (Work.WilE7.MainDesign.absPt z),
        Work.WilE7.Nondrop.fnpFibre S (WilkiesDesign.E.projFirst 0 N z) w = 0 →
          w ∈ Work.WilE7.MainDesign.absSet S) := by
  constructor
  · -- 1. On the stratum the equations vanish.
    intro w hw
    rw [MainDesign.absSet, Set.mem_image] at hw
    obtain ⟨z', hz', rfl⟩ := hw
    refine Work.WilE7.Nondrop.fnpFibre_eq_zero_of_mem S hS (projFirst 0 N z)
      (MainDesign.absPt z') ?_
    show Fin.append (projFirst 0 N z) (MainDesign.absPt z') ∈ S.X.set
    rw [append_absPt]
    exact hz'
  · -- 2. Locally the level set is the stratum, by `Stratum.Good` transported along `absPt`.
    have hcont : Tendsto (fun w : Fin N → ℝ => Fin.append (projFirst 0 N z) w)
        (nhds (MainDesign.absPt z)) (nhds z) := by
      have h := (continuous_append_zero (projFirst 0 N z)).tendsto (MainDesign.absPt z)
      rwa [append_absPt] at h
    -- the locality clause of `Good`, with the (automatic) base condition dropped
    have hP : ∀ᶠ z' in nhds z, (∀ a, eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set :=
      (Work.WilE5.Stratum.good_local hS hz).mono
        (fun z' h => h (Subsingleton.elim _ _))
    filter_upwards [hcont.eventually hP] with w hw h0
    have hz' : Fin.append (projFirst 0 N z) w ∈ S.X.set := hw (fun a => by
      have hh := congrFun h0 a
      simpa using hh)
    rw [MainDesign.absSet, Set.mem_image]
    exact ⟨Fin.append (projFirst 0 N z) w, hz', absPt_append (projFirst 0 N z) w⟩

end Work.WilE7.DimAPI
