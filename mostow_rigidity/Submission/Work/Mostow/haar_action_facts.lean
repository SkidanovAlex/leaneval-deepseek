import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.nearStabDefs
import Submission.Work.Mostow.isCompact_matBallToPO
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.properAction

/-!
# The compact stabiliser `Ksub` and proper discontinuity of discrete subgroups

The Haar-to-volume bridge of the Besson–Courtois–Gallot route needs two facts about the action
of `PO n 1` on the chart space `E n = ℍⁿ`:

* the stabiliser `Ksub n hA` of the origin is **compact** (it is the image of `O(n)`);
* every **discrete** subgroup `Γ ≤ PO n 1` is countable and closed, acts properly
  discontinuously on `ℍⁿ` (finitely many translates of a compact set meet a compact set), and
  every orbit has closest points to any given point.

The properness input is `Work.Mostow.nearStab_finite` from
`Submission/Work/Mostow/properAction.lean` (the near-stabiliser of the origin in a discrete
subgroup is finite, because the orbit map `g ↦ g • 0` is proper, i.e. bounded in the matrix
model); everything else here is the elementary reduction of the statements above to that input.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Topology

noncomputable section

set_option maxHeartbeats 800000

variable {n : ℕ}

/-! ## `Ksub` is compact -/

/-- The stabiliser of the origin is closed: it is the preimage of `{0}` under the continuous
orbit map `g ↦ g • 0`. -/
private theorem isClosed_Ksub (n : ℕ) (hA : POActionProp n) :
    IsClosed ((Ksub n hA : Subgroup (PO n 1)) : Set (PO n 1)) := by
  have hcont : Continuous (fun g : PO n 1 => g • (0 : E n)) :=
    (POBasic.ofProp hA).continuous_smul.comp
      (Continuous.prodMk continuous_id continuous_const)
  have hset : ((Ksub n hA : Subgroup (PO n 1)) : Set (PO n 1)) =
      (fun g : PO n 1 => g • (0 : E n)) ⁻¹' {0} := by
    ext g
    simp [mem_Ksub]
  rw [hset]
  exact isClosed_singleton.preimage hcont

/-- The stabiliser of the origin is contained in the compact set `matBallToPO n 1`: an element
fixing `0` displaces it by `hdist 0 0 = 0`, so all entries of a representing matrix are at
most `cosh 0 = 1`. -/
private theorem Ksub_subset_matBallToPO (n : ℕ) (hA : POActionProp n) :
    ((Ksub n hA : Subgroup (PO n 1)) : Set (PO n 1)) ⊆ matBallToPO n 1 := by
  intro g hg
  have h0 : g ∈ {g : PO n 1 | hdist (0 : E n) (g • (0 : E n)) ≤ 0} := by
    show hdist (0 : E n) (g • (0 : E n)) ≤ 0
    rw [show g • (0 : E n) = (0 : E n) from hg, hdist_self]
  have h1 := orbitBall_subset n 0 h0
  simpa using h1

/-- **`Ksub` is compact**: it is a closed subset of the compact set `matBallToPO n 1`. -/
private theorem isCompact_Ksub (n : ℕ) (hA : POActionProp n) :
    IsCompact ((Ksub n hA : Subgroup (PO n 1)) : Set (PO n 1)) :=
  (matBallToPO_compact n 1).of_isClosed_subset (isClosed_Ksub n hA)
    (Ksub_subset_matBallToPO n hA)

/-! ## Finiteness of the near-stabiliser of an arbitrary point -/

/-- A compact subset of `ℍⁿ` is contained in a ball around the origin: the continuous function
`u ↦ hdist 0 u` is bounded on it (its image under the compact product `{0} × K` is compact). -/
private theorem exists_hdist_bound_of_isCompact (hI : HypIsometryProp n) {K : Set (E n)}
    (hK : IsCompact K) : ∃ R : ℝ, ∀ u ∈ K, hdist (0 : E n) u ≤ R := by
  have hc : IsCompact (({(0 : E n)} : Set (E n)) ×ˢ K) := isCompact_singleton.prod hK
  obtain ⟨R, hR⟩ := (hc.image (HypIsoData.ofProp hI).continuous).bddAbove
  refine ⟨R, fun u hu => ?_⟩
  have hmem : hdist (0 : E n) u ∈
      (fun p : E n × E n => hdist p.1 p.2) '' (({(0 : E n)} : Set (E n)) ×ˢ K) :=
    ⟨(0, u), by simp [hu], rfl⟩
  exact hR hmem

/-- For a discrete subgroup `Γ ≤ PO n 1` and a point `x`, only finitely many `γ ∈ Γ` bring a
fixed base point `o` within distance `R` of `x`.  Reduced to `nearStab_finite` (the
near-stabiliser of the origin) by the triangle inequality and the fact that `Γ` acts by
isometries. -/
private theorem finite_orbit_ball (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1))
    (hdisc : IsDiscrete (Γ : Set (PO n 1))) (o x : E n) (R : ℝ) :
    {γ : Γ | hdist x ((γ : PO n 1) • o) ≤ R}.Finite := by
  let I := HypIsoData.ofProp hI
  refine (nearStab_finite n Γ hdisc (hdist (0 : E n) x + R + hdist (0 : E n) o)).subset ?_
  intro γ hγ
  have hγ' : hdist x ((γ : PO n 1) • o) ≤ R := hγ
  have hiso : hdist ((γ : PO n 1) • o) ((γ : PO n 1) • (0 : E n)) = hdist (0 : E n) o := by
    rw [I.isom_smul (γ : PO n 1) o (0 : E n), I.symm o (0 : E n)]
  have h1 : hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤
      hdist (0 : E n) x + hdist x ((γ : PO n 1) • (0 : E n)) :=
    I.triangle _ _ _
  have h2 : hdist x ((γ : PO n 1) • (0 : E n)) ≤
      hdist x ((γ : PO n 1) • o) + hdist ((γ : PO n 1) • o) ((γ : PO n 1) • (0 : E n)) :=
    I.triangle _ _ _
  show hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ hdist (0 : E n) x + R + hdist (0 : E n) o
  rw [hiso] at h2
  linarith

/-! ## Proper discontinuity -/

set_option linter.unusedVariables false in
/-- **Proper discontinuity.**  For a discrete subgroup `Γ ≤ PO n 1` and compact subsets
`K₁, K₂ ⊆ ℍⁿ`, only finitely many `γ ∈ Γ` have `γ • K₁` meeting `K₂`. -/
private theorem finite_translates_inter_compact (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (Γ : Set (PO n 1)))
    {K₁ K₂ : Set (E n)} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    {γ : Γ | (((fun u : E n => (γ : PO n 1) • u) '' K₁) ∩ K₂).Nonempty}.Finite := by
  let I := HypIsoData.ofProp hI
  have hset : {γ : Γ | (((fun u : E n => (γ : PO n 1) • u) '' K₁) ∩ K₂).Nonempty} =
      {γ : Γ | ∃ v ∈ K₁, (γ : PO n 1) • v ∈ K₂} := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.Nonempty, Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨u, ⟨v, hv, rfl⟩, hu⟩
      exact ⟨v, hv, hu⟩
    · rintro ⟨v, hv, hu⟩
      exact ⟨(γ : PO n 1) • v, ⟨v, hv, rfl⟩, hu⟩
  rw [hset]
  obtain ⟨R₁, hR₁⟩ := exists_hdist_bound_of_isCompact hI hK₁
  obtain ⟨R₂, hR₂⟩ := exists_hdist_bound_of_isCompact hI hK₂
  refine (finite_orbit_ball hI Γ hdisc 0 0 (R₁ + R₂)).subset ?_
  rintro γ ⟨v, hv, hvK₂⟩
  have hv₁ : hdist (0 : E n) v ≤ R₁ := hR₁ v hv
  have hv₂ : hdist (0 : E n) ((γ : PO n 1) • v) ≤ R₂ := hR₂ _ hvK₂
  have hiso : hdist ((γ : PO n 1) • v) ((γ : PO n 1) • (0 : E n)) = hdist (0 : E n) v := by
    rw [I.isom_smul (γ : PO n 1) v (0 : E n), I.symm v (0 : E n)]
  have htri := I.triangle (0 : E n) ((γ : PO n 1) • v) ((γ : PO n 1) • (0 : E n))
  show hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R₁ + R₂
  rw [hiso] at htri
  linarith

/-! ## Closest points of an orbit -/

set_option linter.unusedVariables false in
/-- **Closest orbit points.**  For a discrete subgroup `Γ ≤ PO n 1` and points `o, x`, some
`γ ∈ Γ` realises the minimal distance from `x` to the orbit `Γ • o`: the set of `γ` for which
that distance is at most `hdist x o` is finite (a near-stabiliser) and nonempty (`γ = 1`). -/
private theorem exists_closest_orbit (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (Γ : Set (PO n 1))) (o x : E n) :
    ∃ γ : Γ, ∀ γ' : Γ,
      hdist x ((γ : PO n 1) • o) ≤ hdist x ((γ' : PO n 1) • o) := by
  set f : Γ → ℝ := fun γ => hdist x ((γ : PO n 1) • o) with hf
  have hfin : {γ : Γ | f γ ≤ f 1}.Finite := finite_orbit_ball hI Γ hdisc o x (f 1)
  have hne : {γ : Γ | f γ ≤ f 1}.Nonempty := ⟨1, by simp⟩
  obtain ⟨γ, hγS, hmin⟩ := Finset.exists_min_image hfin.toFinset f
    (by rw [Set.Finite.toFinset_nonempty]; exact hne)
  refine ⟨γ, fun γ' => ?_⟩
  have hγmem : γ ∈ {γ : Γ | f γ ≤ f 1} := (Set.Finite.mem_toFinset hfin).1 hγS
  have hγf : f γ ≤ f 1 := by simpa using hγmem
  have hgoal : f γ ≤ f γ' := by
    by_cases h : f γ' ≤ f 1
    · have hmem : γ' ∈ {γ : Γ | f γ ≤ f 1} := by simpa using h
      exact hmin γ' ((Set.Finite.mem_toFinset hfin).2 hmem)
    · have h' : f 1 < f γ' := lt_of_not_ge h
      linarith
  exact hgoal

/-! ## The requested statement -/

theorem haar_action_facts (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) :
    IsCompact (Work.Mostow.Ksub n hA : Set (LeanEval.Geometry.MostowRigidity.PO n 1)) ∧
      (∀ Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1),
        IsDiscrete (Γ : Set (LeanEval.Geometry.MostowRigidity.PO n 1)) →
          Countable Γ ∧
          IsClosed (Γ : Set (LeanEval.Geometry.MostowRigidity.PO n 1)) ∧
          (∀ K₀ : Set (Submission.Mostow.E n), IsCompact K₀ →
            {γ : Γ | (((fun u : Submission.Mostow.E n =>
              (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) '' K₀) ∩ K₀).Nonempty}.Finite) ∧
          (∀ o x : Submission.Mostow.E n, ∃ γ : Γ, ∀ γ' : Γ,
            Submission.Mostow.hdist x ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • o) ≤
              Submission.Mostow.hdist x ((γ' : LeanEval.Geometry.MostowRigidity.PO n 1) • o))) := by
  refine ⟨isCompact_Ksub n hA, fun Γ hdisc => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact countable_of_isDiscrete (PO n 1) hdisc
  · exact Γ.isClosed_of_isDiscrete hdisc
  · intro K₀ hK₀
    exact finite_translates_inter_compact hA hI Γ hdisc hK₀ hK₀
  · intro o x
    exact exists_closest_orbit hA hI Γ hdisc o x

end

end Work.Mostow
