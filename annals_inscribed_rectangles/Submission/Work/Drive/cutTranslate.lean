import Mathlib
import Submission.Work.Drive.clampedSweep

/-!
# The dictionary between the engine's counts and the cut data

The counting engine counts **parameter triples**: for a triple of chains `D 0, D 1, D 2` on the cube,
`Work.Drive.topBdryMeet Y D k` is the set of triples `(x 0, x 1, x 2)` of cube points at which the
three chains meet in one point of `Y`, with the `k`-th parameter on its top face.  The paper's `n_P` is
instead a statement about the **cut** `A_c = P ∩ V_c` of the plane `P` by a sweep `V_c` — a `1`-cycle
inside the plane — and the passage between the two is pure bookkeeping; it is this file.

For the radial sweeps `V k = Work.Drive.clampedSweep (c k) ψ (P k)` (so that the `k`-th chain's top
face is the plane `P k`, `Work.Drive.clampedSweep_face_one`), the map

> `x ↦ (mk2 (x 0 0) (x 0 1), x 1, x 2)`   (`x 0 2 = 1` is dropped: it is *determined* by the top face)

is a **bijection** from `topBdryMeet Y V 0` onto the set of *cut triples*: a plane parameter
`u ∈ [0,1]²` and two sweep parameters `y, z ∈ [0,1]³` with `P 0 u = V 1 y` and `P 0 u = V 2 z`.  Hence
the counts agree (`ncard_topBdryMeet_zero_eq_ncard_cutTriples`), and the session-15 bookkeeping
(`Work.Drive.ncard_tripleCart_eq_ncard_cutBase`, `…_of_odd_fibres`) applies verbatim to the
`unitBox`-restricted cut triples: the triple count has the parity of the number of plane parameters
lying on **both** cuts, i.e. of `A_1 ∩ A_2` inside the plane — which is what the mod-2 intersection
form of `ℝP²` (`Work.Surf.odd_chordMeetAll_iff_card_fix`) then evaluates as `ε_1 ε_2`.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

variable {Y : Type*} [TopologicalSpace Y]

/-- **The cut of a plane presentation by a sweep**: the pairs of parameters at which the two chains
give the same point.  For `c ∈ Zc γ` this is a `1`-cycle inside the plane (no boundary). -/
def cutRel (P : EuclideanSpace ℝ (Fin 2) → Y) (V : EuclideanSpace ℝ (Fin 3) → Y) :
    Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3)) :=
  {p | P p.1 = V p.2}

/-- **The cut triples in the box**: a plane parameter `u` and two sweep parameters `y`, `z`, both cuts
being hit at `u`. -/
def cutTriples (P : EuclideanSpace ℝ (Fin 2) → Y)
    (V W : EuclideanSpace ℝ (Fin 3) → Y) :
    Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  {p | p.1 ∈ Submission.Drive.unitBox 1 ∧ p.2.1 ∈ Submission.Drive.unitBox 2 ∧
    p.2.2 ∈ Submission.Drive.unitBox 2 ∧ (p.1, p.2.1) ∈ cutRel P V ∧ (p.1, p.2.2) ∈ cutRel P W}

/-- The plane parameters in the box over which *both* cuts have a sweep parameter in the box. -/
def cutBaseBox (P : EuclideanSpace ℝ (Fin 2) → Y) (V W : EuclideanSpace ℝ (Fin 3) → Y) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {u | u ∈ Submission.Drive.unitBox 1 ∧
    (∃ y ∈ Submission.Drive.unitBox 2, (u, y) ∈ cutRel P V) ∧
    (∃ z ∈ Submission.Drive.unitBox 2, (u, z) ∈ cutRel P W)}

/-- The box-fibre of the cut `cutRel P V` over a plane parameter `u`. -/
def cutFibreBox (P : EuclideanSpace ℝ (Fin 2) → Y) (V : EuclideanSpace ℝ (Fin 3) → Y)
    (u : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {y | y ∈ Submission.Drive.unitBox 2 ∧ (u, y) ∈ cutRel P V}

/-- The plane parameter padded to a sweep parameter, with third coordinate `1` (the top face). -/
def pad3 (u : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![u 0, u 1, 1]

@[simp] lemma pad3_apply_zero (u : EuclideanSpace ℝ (Fin 2)) : pad3 u 0 = u 0 := rfl
@[simp] lemma pad3_apply_one (u : EuclideanSpace ℝ (Fin 2)) : pad3 u 1 = u 1 := rfl
@[simp] lemma pad3_apply_two (u : EuclideanSpace ℝ (Fin 2)) : pad3 u 2 = 1 := rfl

/-- The `3`-dimensional analogue of `Work.Drive.mk2_eta`. -/
lemma mk3_eta (z : EuclideanSpace ℝ (Fin 3)) :
    WithLp.toLp 2 (![z 0, z 1, z 2] : Fin 3 → ℝ) = z := by
  have h : (![z 0, z 1, z 2] : Fin 3 → ℝ) = fun i : Fin 3 => z i := by
    funext i
    fin_cases i <;> simp
  rw [h]

lemma pad3_mem_unitBox {u : EuclideanSpace ℝ (Fin 2)} (hu : u ∈ Submission.Drive.unitBox 1) :
    pad3 u ∈ Submission.Drive.unitBox 2 :=
  fun i => by
    fin_cases i
    · simpa using hu 0
    · simpa using hu 1
    · simpa using (Set.mem_Icc.mpr ⟨le_refl (0:ℝ), zero_le_one⟩)

/-- The projection of a triple of parameters to the cut coordinates: the plane parameter `x 0` (its
first two coordinates) and the two sweep parameters. -/
def cutProj (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  (mk2 (x 0 0) (x 0 1), x 1, x 2)

lemma cutProj_apply (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    cutProj x = (mk2 (x 0 0) (x 0 1), x 1, x 2) := rfl

section Capping

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

/-- **The top count of the first chain is the cut-triple count.**  The image of
`Work.Drive.topBdryMeet Y V 0` under the cut projection is the set of cut triples, using that the top
face of the first radial sweep is the plane itself. -/
theorem image_cutProj_topBdryMeet_zero
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (hψ : ψ 1 = 0) :
    cutProj '' (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0)
      = cutTriples (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)) := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨⟨hbox, h01, h02, -⟩, htop⟩ := hx
    have hV0 : clampedSweep (c 0) ψ (P 0) (x 0) = P 0 (mk2 (x 0 0) (x 0 1)) :=
      clampedSweep_face_one (c 0) ψ (P 0) hψ (x 0) htop
    have hplane : mk2 (x 0 0) (x 0 1) ∈ Submission.Drive.unitBox 1 :=
      fun i => by
        fin_cases i
        · simpa using hbox 0 0
        · simpa using hbox 0 1
    refine ⟨hplane, hbox 1, hbox 2, ?_, ?_⟩
    · show P 0 (mk2 (x 0 0) (x 0 1)) = clampedSweep (c 1) ψ (P 1) (x 1)
      rw [← hV0]
      simpa only using h01
    · show P 0 (mk2 (x 0 0) (x 0 1)) = clampedSweep (c 2) ψ (P 2) (x 2)
      rw [← hV0]
      simpa only using h02
  · rintro ⟨hu, hy, hz, hcut1, hcut2⟩
    set x : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
      fun k => if k = 0 then pad3 p.1 else if k = 1 then p.2.1 else p.2.2 with hxdef
    have hx0 : x 0 = pad3 p.1 := by simp [hxdef]
    have hx1 : x 1 = p.2.1 := by simp [hxdef]
    have hx2 : x 2 = p.2.2 := by simp [hxdef]
    have hmem : ∀ k, x k ∈ Submission.Drive.unitBox 2 := by
      intro k
      rw [hxdef]
      show (if k = 0 then pad3 p.1 else if k = 1 then p.2.1 else p.2.2)
        ∈ Submission.Drive.unitBox 2
      split_ifs with h0 h1
      · exact pad3_mem_unitBox hu
      · exact hy
      · exact hz
    have htop : x 0 2 = 1 := by rw [hx0]; exact pad3_apply_two p.1
    have hbdry : x 0 ∈ Submission.Drive.unitBoxBdry 2 := ⟨hmem 0, 2, Or.inr htop⟩
    have he1 : clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1) := by
      rw [hx0, hx1, clampedSweep_face_one (c 0) ψ (P 0) hψ (pad3 p.1) (pad3_apply_two p.1),
        pad3_apply_zero, pad3_apply_one]
      rw [show mk2 (p.1 0) (p.1 1) = p.1 from mk2_eta p.1]
      exact hcut1
    have he2 : clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2) := by
      rw [hx0, hx2, clampedSweep_face_one (c 0) ψ (P 0) hψ (pad3 p.1) (pad3_apply_two p.1),
        pad3_apply_zero, pad3_apply_one]
      rw [show mk2 (p.1 0) (p.1 1) = p.1 from mk2_eta p.1]
      exact hcut2
    have hproj : cutProj x = p := by
      show (mk2 (x 0 0) (x 0 1), x 1, x 2) = p
      rw [hx0, hx1, hx2, pad3_apply_zero, pad3_apply_one,
        show mk2 (p.1 0) (p.1 1) = p.1 from mk2_eta p.1]
    refine ⟨x, ?_, hproj⟩
    show ((∀ k, x k ∈ Submission.Drive.unitBox 2) ∧
        ((fun k => clampedSweep (c k) ψ (P k)) 0 (x 0)
          = (fun k => clampedSweep (c k) ψ (P k)) 1 (x 1)) ∧
        ((fun k => clampedSweep (c k) ψ (P k)) 0 (x 0)
          = (fun k => clampedSweep (c k) ψ (P k)) 2 (x 2)) ∧
        x 0 ∈ Submission.Drive.unitBoxBdry 2) ∧ (x 0 2 = 1)
    exact ⟨⟨hmem, he1, he2, hbdry⟩, htop⟩

lemma injOn_cutProj_topBdryMeet_zero
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ) :
    Set.InjOn cutProj (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0) := by
  rintro x hx y hy hxy
  simp only [topBdryMeet, Set.mem_setOf_eq] at hx hy
  have h1 : mk2 (x 0 0) (x 0 1) = mk2 (y 0 0) (y 0 1) := by
    simpa only [cutProj] using congrArg Prod.fst hxy
  have h2 : x 1 = y 1 := by
    simpa only [cutProj] using congrArg (fun p => p.2.1) hxy
  have h3 : x 2 = y 2 := by
    simpa only [cutProj] using congrArg (fun p => p.2.2) hxy
  have h11 : x 0 0 = y 0 0 := by
    simpa only [mk2_apply_zero] using congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 0) h1
  have h12 : x 0 1 = y 0 1 := by
    simpa only [mk2_apply_one] using congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 1) h1
  have hx0 : x 0 = WithLp.toLp 2 (![x 0 0, x 0 1, x 0 2] : Fin 3 → ℝ) := (mk3_eta (x 0)).symm
  have hy0 : y 0 = WithLp.toLp 2 (![y 0 0, y 0 1, y 0 2] : Fin 3 → ℝ) := (mk3_eta (y 0)).symm
  have hx0' : x 0 = y 0 := by
    rw [hx0, hy0, h11, h12, hx.2, hy.2]
  funext k
  fin_cases k
  · exact hx0'
  · exact h2
  · exact h3

/-- **The engine's top count for the first chain *is* the cut-triple count.** -/
theorem ncard_topBdryMeet_zero_eq_ncard_cutTriples
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (hψ : ψ 1 = 0) :
    (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
      = (cutTriples (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2))).ncard := by
  rw [← image_cutProj_topBdryMeet_zero P c ψ hψ,
    (injOn_cutProj_topBdryMeet_zero P c ψ).ncard_image]

end Capping

end

end Work.Drive
