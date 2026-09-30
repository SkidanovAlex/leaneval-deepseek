import Mathlib
import Submission.Work.StemsB.SerreSphereCollar

set_option synthInstance.maxHeartbeats 400000

/-!
# The inner cube is contractible to a point of the collar

The affine (straight-line) contraction of the open cube `sphLoopBig n = {|v|_∞ < 3/2}` onto the
point `sphShellPt n = (1,0,…,0)` of the collar, fixing that point.  This is the input that makes the
fibration trivial over the inner piece (through
`Work.StemsB.preimageIncl_homotopyEquiv_of_deformation`).

The construction is carried out on the *chart* `OnePoint.some`: the map

  `G (↑v, t) = ↑((1-t) • v + t • vec)`,

extended by `G (∞, t) = ∞`, is discontinuous at `(∞, 1)`, but the domain of interest
`↥(sphLoopBig n) × I` avoids `∞`, and on the chart the formula is manifestly continuous.  The proof
uses that `OnePoint.some` is an **open embedding** (hence an inducing map) so that continuity on the
subtype can be checked after extracting the chart coordinates.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

/-- The vector of the point `sphShellPt n`: the first standard basis vector. -/
def sphShellVec (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0)

@[simp] theorem sphShellPt_eq (n : ℕ) : sphShellPt n = OnePoint.some (sphShellVec n) := rfl

/-- The straight-line homotopy towards `sphShellVec n`, as a function on the model. -/
def affContr (n : ℕ) (q : SphModel n × unitInterval) : SphModel n :=
  match q.1 with
  | none => OnePoint.infty
  | some v => OnePoint.some ((1 - (q.2 : ℝ)) • v + (q.2 : ℝ) • sphShellVec n)

@[simp] theorem affContr_infty (n : ℕ) (t : unitInterval) :
    affContr n (OnePoint.infty, t) = OnePoint.infty := rfl

@[simp] theorem affContr_some (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : unitInterval) :
    affContr n (OnePoint.some v, t) =
      OnePoint.some ((1 - (t : ℝ)) • v + (t : ℝ) • sphShellVec n) := rfl

theorem coord_le_sphShellVec (n : ℕ) (i : Fin n) :
    |sphShellVec n i| ≤ 1 := by
  rw [sphShellVec]
  by_cases h : (i : ℕ) = 0 <;> simp [h]

/-- The affine combination stays in the open cube. -/
theorem affContr_mem_sphLoopBig (n : ℕ) {x : SphModel n} (hx : x ∈ sphLoopBig n)
    (t : unitInterval) : affContr n (x, t) ∈ sphLoopBig n := by
  obtain ⟨v, hv, hvlt⟩ := hx
  refine ⟨(1 - (t : ℝ)) • v + (t : ℝ) • sphShellVec n, ?_, fun i => ?_⟩
  · rw [show x = OnePoint.some v from hv, affContr_some]
  · have hcoord : ((1 - (t : ℝ)) • v + (t : ℝ) • sphShellVec n) i
        = (1 - (t : ℝ)) * v i + (t : ℝ) * sphShellVec n i := by
      simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hcoord]
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have h3 : (1 - (t : ℝ)) * |v i| + (t : ℝ) * 1 < 3 / 2 := by
      rcases lt_or_eq_of_le ht1 with h | h
      · have hpos : 0 < 1 - (t : ℝ) := by linarith
        nlinarith [mul_lt_mul_of_pos_left (hvlt i) hpos]
      · rw [h]; ring_nf; norm_num
    calc |(1 - (t : ℝ)) * v i + (t : ℝ) * sphShellVec n i|
        ≤ |(1 - (t : ℝ)) * v i| + |(t : ℝ) * sphShellVec n i| := abs_add_le _ _
      _ = (1 - (t : ℝ)) * |v i| + (t : ℝ) * |sphShellVec n i| := by
          rw [abs_mul, abs_mul,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (t : ℝ)), abs_of_nonneg ht0]
      _ ≤ (1 - (t : ℝ)) * |v i| + (t : ℝ) * 1 := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (coord_le_sphShellVec n i) ht0)
      _ < 3 / 2 := h3

/-- Joint continuity of the affine contraction at a finite point (the chart argument). -/
theorem continuousAt_affContr_some (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) (t : unitInterval) :
    ContinuousAt (fun p : SphModel n × unitInterval => affContr n p) (OnePoint.some w, t) := by
  have hchart : Topology.IsOpenEmbedding
      (fun p : EuclideanSpace ℝ (Fin n) × unitInterval => (OnePoint.some p.1, p.2)) :=
    (OnePoint.isOpenEmbedding_coe (X := EuclideanSpace ℝ (Fin n))).prodMap
      Topology.IsOpenEmbedding.id
  have hcomp : ContinuousAt
      (fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
        affContr n (OnePoint.some p.1, p.2)) (w, t) := by
    have hinner : Continuous fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
        (1 - (p.2 : ℝ)) • p.1 + (p.2 : ℝ) • sphShellVec n := by fun_prop
    have h2 : Continuous fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
        OnePoint.some ((1 - (p.2 : ℝ)) • p.1 + (p.2 : ℝ) • sphShellVec n) :=
      (OnePoint.isOpenEmbedding_coe (X := EuclideanSpace ℝ (Fin n))).continuous.comp hinner
    simpa only [affContr_some] using h2.continuousAt
  exact (hchart.continuousAt_iff
    (g := fun p : SphModel n × unitInterval => affContr n p)).mp hcomp

/-- Continuity of the affine contraction on the inner cube. -/
theorem continuous_affContr (n : ℕ) :
    Continuous fun q : ↥(sphLoopBig n) × unitInterval => affContr n (q.1.1, q.2) := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨v, hv, _⟩ := q.1.2
  have hincl : ContinuousAt (fun q : ↥(sphLoopBig n) × unitInterval => (q.1.1, q.2)) q :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousAt
  have h1 : ContinuousAt (fun p : SphModel n × unitInterval => affContr n p) (q.1.1, q.2) := by
    rw [show q.1.1 = OnePoint.some v from hv]
    exact continuousAt_affContr_some n v q.2
  exact ContinuousAt.comp (f := fun q : ↥(sphLoopBig n) × unitInterval => (q.1.1, q.2))
    (g := fun p : SphModel n × unitInterval => affContr n p) h1 hincl

/-- **The inner cube is contractible to the shell point**: the affine contraction, fixing the shell
point. -/
theorem serreSphere_contract_big (n : ℕ) (hn : 1 ≤ n) (hc : sphShellPt n ∈ sphLoopBig n) :
    ∃ c : C(↥(sphLoopBig n) × unitInterval, ↥(sphLoopBig n)),
      (∀ x, c (x, 0) = x) ∧
      (∀ x, c (x, 1) = (⟨sphShellPt n, hc⟩ : ↥(sphLoopBig n))) ∧
      (∀ t, c ((⟨sphShellPt n, hc⟩ : ↥(sphLoopBig n)), t) = ⟨sphShellPt n, hc⟩) := by
  have hmem : ∀ q : ↥(sphLoopBig n) × unitInterval,
      affContr n (q.1.1, q.2) ∈ sphLoopBig n := fun q => affContr_mem_sphLoopBig n q.1.2 q.2
  have hcont := continuous_affContr n
  refine ⟨⟨fun q => ⟨affContr n (q.1.1, q.2), hmem q⟩, hcont.subtype_mk hmem⟩, ?_, ?_, ?_⟩
  · intro u
    apply Subtype.ext
    obtain ⟨v, hv, _⟩ := u.2
    show affContr n (u.1, (0 : unitInterval)) = u.1
    rw [show u.1 = OnePoint.some v from hv, affContr_some]
    simp
  · intro u
    apply Subtype.ext
    obtain ⟨v, hv, _⟩ := u.2
    show affContr n (u.1, (1 : unitInterval)) = sphShellPt n
    rw [show u.1 = OnePoint.some v from hv, affContr_some, sphShellPt_eq]
    norm_num
  · intro t
    apply Subtype.ext
    show affContr n (sphShellPt n, t) = sphShellPt n
    rw [sphShellPt_eq, affContr_some]
    rw [← add_smul]
    simp

end
end Work.StemsB
