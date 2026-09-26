import Mathlib
import Submission.Work.CoreTopology.All
import Submission.Work.SurgeryInvariance.All

/-!
# Descending a path in the parameter plane to a closed curve of the torus

Let `V ⊆ ℝ²` be a set which is invariant under the period lattice `2πℤ²`, and let
`p : [0,1] → ℝ²` be a continuous path with values in `V` whose endpoints differ by a lattice
vector `(2πk, 2πl)`.  Then `p` descends to the torus: there is a closed curve `γ` of `F = P.carrier`
whose image lies in the image of `V` in the surface, and whose winding vector is `(k, l)`.

The construction is the standard one.  The path `p`, extended to the whole line by the periodicity
relation `P̃(x + n) = P̃(x) + n·(2πk, 2πl)`, is the map `pathExt p k l` below; the curve `γ` is
`t ↦ P.psi (Λ t).1 (Λ t).2` with `Λ t = pathExt p k l (t / 2π)`.  The only point which requires
care is the continuity of `pathExt`, which holds because the jump of the "number of periods"
function `⌊x⌋` at an integer is exactly compensated by the endpoint relation
`p 1 = p 0 + (2πk, 2πl)` (`pathExt_add_int`): on each interval `[m, m+1]` the extension agrees with
the manifestly continuous expression `x ↦ p (x - m) + m·(2πk, 2πl)`.
-/

namespace Work.BoxShrink.Bubble.Plane

open Set

noncomputable section

/-- The reduction of a real number to the fundamental interval `[0,1]`: the fractional part. -/
private def wrap (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨Int.fract x, Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

/-- The path `p : [0,1] → ℝ²` extended to the whole line by the relation
`P̃ (x + n) = P̃ x + n · (2πk, 2πl)`.  Concretely, `P̃ x = p (fract x) + ⌊x⌋ · (2πk, 2πl)`. -/
private def pathExt (p : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)) (k l : ℤ) (x : ℝ) : ℝ × ℝ :=
  ((p (wrap x)).1 + (⌊x⌋ : ℝ) * ((k : ℝ) * (2 * Real.pi)),
   (p (wrap x)).2 + (⌊x⌋ : ℝ) * ((l : ℝ) * (2 * Real.pi)))

/-- The defining periodicity of the extended path: shifting the argument by an integer `n` shifts
the value by `n` periods. -/
private theorem pathExt_add_int (p : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)) (k l : ℤ) (x : ℝ) (n : ℤ) :
    pathExt p k l (x + (n : ℝ)) =
      ((pathExt p k l x).1 + (n : ℝ) * ((k : ℝ) * (2 * Real.pi)),
       (pathExt p k l x).2 + (n : ℝ) * ((l : ℝ) * (2 * Real.pi))) := by
  have hf : Int.fract (x + (n : ℝ)) = Int.fract x := Int.fract_add_intCast x n
  have hfl : ⌊x + (n : ℝ)⌋ = ⌊x⌋ + n := Int.floor_add_intCast x n
  have hw : wrap (x + (n : ℝ)) = wrap x := Subtype.ext hf
  simp only [pathExt, hw, hfl]
  push_cast
  ring

/-- The case `n = 1` of `pathExt_add_int`: one period. -/
private theorem pathExt_add_one (p : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)) (k l : ℤ) (x : ℝ) :
    pathExt p k l (x + 1) =
      ((pathExt p k l x).1 + (k : ℝ) * (2 * Real.pi),
       (pathExt p k l x).2 + (l : ℝ) * (2 * Real.pi)) := by
  have h := pathExt_add_int p k l x 1
  simpa using h

/-- On the fundamental interval the extension agrees with the original path.  At the endpoint
`x = 1` this uses the relation `p 1 = p 0 + (2πk, 2πl)`, recorded here in the (proof-irrelevant)
form `hstep`. -/
private theorem pathExt_of_mem_Icc (p : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)) (k l : ℤ)
    (hstep : ∀ (h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1),
      p ⟨1, h1⟩ = ((p ⟨0, h0⟩).1 + (k : ℝ) * (2 * Real.pi),
                   (p ⟨0, h0⟩).2 + (l : ℝ) * (2 * Real.pi)))
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    pathExt p k l x = p ⟨x, hx⟩ := by
  rcases eq_or_lt_of_le hx.2 with hx1 | hx1
  · -- `x = 1`
    have hfx : Int.fract x = 0 := by rw [hx1]; norm_num [Int.fract]
    have hfloor : ⌊x⌋ = 1 := by rw [hx1]; norm_num
    have hwrap : wrap x =
        (⟨0, (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)⟩ : Set.Icc (0 : ℝ) 1) :=
      Subtype.ext hfx
    have hsub : (⟨x, hx⟩ : Set.Icc (0 : ℝ) 1) =
        ⟨1, (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)⟩ :=
      Subtype.ext hx1
    rw [pathExt, hwrap, hfloor, hsub, hstep (by norm_num) (by norm_num)]
    norm_num
  · -- `x < 1`
    have hfloor : ⌊x⌋ = 0 := by
      rw [Int.floor_eq_iff]
      exact ⟨by simpa using hx.1, by simpa using hx1⟩
    have hfx : Int.fract x = x := by rw [Int.fract, hfloor]; ring
    have hwrap : wrap x = (⟨x, hx⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext hfx
    rw [pathExt, hwrap, hfloor]
    norm_num

/-- On each fundamental interval `[m, m+1]` the extension is given by the manifestly continuous
expression `x ↦ p (x - m) + m · (2πk, 2πl)`; hence it is continuous there. -/
private theorem continuousOn_pathExt_Icc (p : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)) (k l : ℤ)
    (hstep : ∀ (h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1),
      p ⟨1, h1⟩ = ((p ⟨0, h0⟩).1 + (k : ℝ) * (2 * Real.pi),
                   (p ⟨0, h0⟩).2 + (l : ℝ) * (2 * Real.pi)))
    (m : ℤ) :
    ContinuousOn (pathExt p k l) (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let σ : Set.Icc (m : ℝ) ((m : ℝ) + 1) → Set.Icc (0 : ℝ) 1 := fun y =>
    ⟨y.1 - (m : ℝ), by have := y.2.1; linarith, by have := y.2.2; linarith⟩
  have hσ : Continuous σ := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.sub continuous_const
  have hval : (Set.domRestrict (Set.Icc (m : ℝ) ((m : ℝ) + 1)) (pathExt p k l)) =
      fun y => ((p (σ y)).1 + (m : ℝ) * ((k : ℝ) * (2 * Real.pi)),
                (p (σ y)).2 + (m : ℝ) * ((l : ℝ) * (2 * Real.pi))) := by
    funext y
    simp only [Set.domRestrict_apply]
    have hmem : y.1 - (m : ℝ) ∈ Set.Icc (0 : ℝ) 1 := (σ y).2
    have hy : (y : ℝ) = (y.1 - (m : ℝ)) + (m : ℝ) := by ring
    rw [hy, pathExt_add_int p k l (y.1 - (m : ℝ)) m,
      pathExt_of_mem_Icc p k l hstep (y.1 - (m : ℝ)) hmem]
  rw [hval]
  exact Continuous.prodMk (((p.continuous.comp hσ).fst).add continuous_const)
    (((p.continuous.comp hσ).snd).add continuous_const)

/-- **The extension `pathExt p k l` is continuous.**  This is the technical heart of the descent: at
a non-integer point `⌊·⌋` is locally constant, and at an integer the discontinuity of `⌊·⌋` (which
jumps by one period) is compensated by the endpoint relation of `p`, so that the two manifestly
continuous branches glue. -/
private theorem continuous_pathExt (p : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)) (k l : ℤ)
    (hstep : ∀ (h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1),
      p ⟨1, h1⟩ = ((p ⟨0, h0⟩).1 + (k : ℝ) * (2 * Real.pi),
                   (p ⟨0, h0⟩).2 + (l : ℝ) * (2 * Real.pi))) :
    Continuous (pathExt p k l) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne (Int.fract x) 0 with hf | hf
  · -- `x` is an integer: glue the two branches at `⌊x⌋`
    have hx : x = (⌊x⌋ : ℝ) := by
      have h := Int.floor_add_fract x
      rw [hf, add_zero] at h
      exact h.symm
    rw [hx]
    have h1 : ContinuousOn (pathExt p k l) (Set.Icc ((⌊x⌋ : ℝ) - 1) ((⌊x⌋ : ℝ))) := by
      convert continuousOn_pathExt_Icc p k l hstep (⌊x⌋ - 1) using 1
      push_cast
      ring
    have h2 : ContinuousOn (pathExt p k l) (Set.Icc ((⌊x⌋ : ℝ)) ((⌊x⌋ : ℝ) + 1)) :=
      continuousOn_pathExt_Icc p k l hstep ⌊x⌋
    have hu : ContinuousOn (pathExt p k l) (Set.Icc ((⌊x⌋ : ℝ) - 1) ((⌊x⌋ : ℝ) + 1)) := by
      rw [← Set.Icc_union_Icc_eq_Icc (show ((⌊x⌋ : ℝ) - 1) ≤ (⌊x⌋ : ℝ) by linarith)
            (show ((⌊x⌋ : ℝ)) ≤ ((⌊x⌋ : ℝ) + 1) by linarith)]
      exact h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    exact hu.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  · -- `x` is not an integer: `⌊·⌋` is locally constant
    have hlt : (⌊x⌋ : ℝ) < x := by
      rcases lt_or_eq_of_le (Int.floor_le x) with h | h
      · exact h
      · exfalso
        apply hf
        rw [Int.fract]
        linarith
    have hup : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    exact (continuousOn_pathExt_Icc p k l hstep ⌊x⌋).continuousAt (Icc_mem_nhds hlt hup)

theorem descent {P : Work.CoreTopology.ParamTorus} {k l : ℤ}
    {V : Set (ℝ × ℝ)}
    (hV : ∀ q ∈ V, ∀ a b : ℤ, (q.1 + a * (2 * Real.pi), q.2 + b * (2 * Real.pi)) ∈ V)
    (p : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ))
    (hpV : ∀ t : Set.Icc (0 : ℝ) 1, p t ∈ V)
    (hp1 : (p ⟨1, by norm_num⟩).1 = (p ⟨0, by norm_num⟩).1 + k * (2 * Real.pi) ∧
      (p ⟨1, by norm_num⟩).2 = (p ⟨0, by norm_num⟩).2 + l * (2 * Real.pi)) :
    ∃ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ t ∈ (fun q : ℝ × ℝ => P.psi q.1 q.2) '' V) ∧
        Work.SurgeryInvariance.windingOf P γ = (k, l) := by
  -- the endpoint relation, in a form independent of the proofs of the membership statements
  have hstep : ∀ (h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1),
      p ⟨1, h1⟩ = ((p ⟨0, h0⟩).1 + (k : ℝ) * (2 * Real.pi),
                   (p ⟨0, h0⟩).2 + (l : ℝ) * (2 * Real.pi)) := by
    intro h1 h0
    have e1 : (⟨1, h1⟩ : Set.Icc (0 : ℝ) 1) = ⟨1, by norm_num⟩ := Subtype.ext rfl
    have e0 : (⟨0, h0⟩ : Set.Icc (0 : ℝ) 1) = ⟨0, by norm_num⟩ := Subtype.ext rfl
    rw [e1, e0]
    exact Prod.ext hp1.1 hp1.2
  -- the extension of the path to the whole line
  let E : ℝ → ℝ × ℝ := pathExt p k l
  have hEcont : Continuous E := continuous_pathExt p k l hstep
  -- every value of the extension lies in `V`
  have hmemV : ∀ x : ℝ, E x ∈ V := by
    intro x
    have h0 : p (wrap x) ∈ V := hpV (wrap x)
    have h1 : ((p (wrap x)).1 + ((⌊x⌋ * k : ℤ) : ℝ) * (2 * Real.pi),
               (p (wrap x)).2 + ((⌊x⌋ * l : ℤ) : ℝ) * (2 * Real.pi)) ∈ V :=
      hV _ h0 (⌊x⌋ * k) (⌊x⌋ * l)
    have h2 : E x = ((p (wrap x)).1 + ((⌊x⌋ * k : ℤ) : ℝ) * (2 * Real.pi),
                     (p (wrap x)).2 + ((⌊x⌋ * l : ℤ) : ℝ) * (2 * Real.pi)) := by
      show pathExt p k l x = _
      simp only [pathExt, Int.cast_mul]
      ring_nf
    rw [h2]
    exact h1
  -- the lift of the descended curve
  let L : ℝ → ℝ × ℝ := fun t => E (t / (2 * Real.pi))
  have hLcont : Continuous L := hEcont.comp (continuous_id.div_const _)
  have hEone : E 1 = ((E 0).1 + (k : ℝ) * (2 * Real.pi),
      (E 0).2 + (l : ℝ) * (2 * Real.pi)) := by
    simpa [E] using pathExt_add_one p k l 0
  have hLper : ∀ t : ℝ, L (t + 2 * Real.pi) =
      ((L t).1 + (k : ℝ) * (2 * Real.pi), (L t).2 + (l : ℝ) * (2 * Real.pi)) := by
    intro t
    have hdiv : (t + 2 * Real.pi) / (2 * Real.pi) = t / (2 * Real.pi) + 1 := by
      rw [add_div, div_self (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
    show E ((t + 2 * Real.pi) / (2 * Real.pi)) = _
    rw [hdiv]
    simpa [E] using pathExt_add_one p k l (t / (2 * Real.pi))
  -- the descended closed curve
  let γ : Work.CoreTopology.ClosedCurve P :=
    { γ := fun t => P.psi (L t).1 (L t).2
      cont := P.cont.comp (hLcont.fst.prodMk hLcont.snd)
      periodic := by
        intro t
        have key := hLper t
        show P.psi (L (t + 2 * Real.pi)).1 (L (t + 2 * Real.pi)).2 =
          P.psi (L t).1 (L t).2
        rw [key]
        exact (P.psi_congr_left ⟨k, rfl⟩ rfl).trans (P.psi_congr_right rfl ⟨l, rfl⟩)
      mem := fun t => P.psi_mem_carrier _ _ }
  refine ⟨γ, ?_, ?_⟩
  · -- the image lies in the image of `V`
    intro t
    exact ⟨L t, hmemV (t / (2 * Real.pi)), rfl⟩
  · -- the winding vector is `(k, l)`
    let Lf : Work.CoreTopology.LiftOf P γ :=
      { Θ := fun t => (L t).1
        Φ := fun t => (L t).2
        contΘ := hLcont.fst
        contΦ := hLcont.snd
        lifts := fun t => rfl }
    rw [Work.SurgeryInvariance.windingOf_eq P γ Lf]
    have hspec := Lf.winding_spec
    have hΘ1 : Lf.Θ (2 * Real.pi) = Lf.Θ 0 + (k : ℝ) * (2 * Real.pi) := by
      have ha : Lf.Θ (2 * Real.pi) = (E 1).1 := by
        show (E ((2 * Real.pi) / (2 * Real.pi))).1 = (E 1).1
        rw [div_self (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
      have hb : Lf.Θ 0 = (E 0).1 := by
        show (E (0 / (2 * Real.pi))).1 = (E 0).1
        rw [zero_div]
      rw [ha, hb, congrArg Prod.fst hEone]
    have hΦ1 : Lf.Φ (2 * Real.pi) = Lf.Φ 0 + (l : ℝ) * (2 * Real.pi) := by
      have ha : Lf.Φ (2 * Real.pi) = (E 1).2 := by
        show (E ((2 * Real.pi) / (2 * Real.pi))).2 = (E 1).2
        rw [div_self (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
      have hb : Lf.Φ 0 = (E 0).2 := by
        show (E (0 / (2 * Real.pi))).2 = (E 0).2
        rw [zero_div]
      rw [ha, hb, congrArg Prod.snd hEone]
    refine Prod.ext ?_ ?_
    · have hmul : ((Lf.winding).1 : ℝ) * (2 * Real.pi) = (k : ℝ) * (2 * Real.pi) := by
        linarith [hspec.1, hΘ1]
      exact_mod_cast mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) hmul
    · have hmul : ((Lf.winding).2 : ℝ) * (2 * Real.pi) = (l : ℝ) * (2 * Real.pi) := by
        linarith [hspec.2, hΦ1]
      exact_mod_cast mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) hmul

end

end Work.BoxShrink.Bubble.Plane
