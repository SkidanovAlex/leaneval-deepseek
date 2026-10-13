/-
# Integration by parts against a compactly supported test function on `ℝ³`

`Work.FTS.PressureOn.integral_div_mul_of_differentiable_off_planes`: for a *continuous* vector
field `ω : ℝ³ → ℝ³` which is differentiable with derivative `fderiv ℝ ω` at every point off the
two planes `x 0 = 0`, `x 2 = 0`, whose `fderiv` is locally integrable, and for a `C¹` compactly
supported scalar test function `ψ`,

  `∫ x, ⟪ω x, ∇ψ x⟫ = -∫ x, div ω x * ψ x`.

Equivalently `∫ x, div (ψ • ω) x = 0`.  The point of the lemma is that the *exceptional set*
(the union of two planes) is only a null set: it is **not** countable, so Mathlib's divergence
theorem `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` — which allows the
field to fail to be differentiable only off a countable set — cannot be applied to a box
straddling the planes.  (Continuity of `ω` is what makes the identity true at all: the jump of
`fderiv ω` across a plane produces no boundary term, because `ω` itself is continuous there.)

## Route

1. `Work.FTS.PressureOn.box_divergence_identity` (Mathlib's divergence theorem on a box, for a
   box whose interior avoids both planes) applied to the four boxes
   `[0,R]×[-R,R]×[0,R]`, `[-R,0]×[-R,R]×[0,R]`, …: the `2×2` grid cut out by the two planes.
   All four boxes meet the ball containing the support of the field, and their interiors avoid
   the exceptional set.
2. Summing the four identities, the six faces of each box either lie outside the support (so
   they vanish) or are matched by a face of a neighbouring box (so they cancel pairwise).  The
   matching is made *syntactic* by normalising the endpoints of the faces
   (`vec3_comp0/1/2`), which is what lets `linarith` finish the job.
3. The four `Icc`-boxes are replaced by the corresponding half-open `Ioc`-boxes (a.e. equal,
   `Measure.univ_pi_Ioc_ae_eq_Icc`) so that the four sub-boxes are *literally* disjoint with
   union the big `Ioc`-box; this gives `∫ = Σ_k ∫_{box k}` via `MeasureTheory.setIntegral_union`.
4. The localised identity is upgraded to the identity on `ℝ³` (the field `ω` being replaced by
   `ψ • ω`, supported in the support of `ψ`), and the a.e. product rule
   `div (ψ • ω) = ψ * div ω + ⟪∇ψ, ω⟫` (valid off the two planes, a null set) converts
   `∫ div (ψ • ω) = 0` into the stated identity.

The file also builds the small "coordinate space" toolkit (`Iocc`, `mem_pi_vals`, the box
splittings) used by the argument.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.box_divergence_identity
import Submission.Work.FTS.PressureOn.ae_coord_ne_zero
import Submission.Work.FTS.PressureOn.div_smul_eq
import Submission.Work.FTS.PressureOn.integrable_inner_gradient
import Submission.Work.FTS.PressureOn.integrable_mul_div
import Submission.Work.FTS.PressureOn.hasCompactSupport_transport

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open FiniteTimeSingularity

namespace Work.FTS.PressureOn

/-! ## Endpoint normalisation for `Fin 3 → ℝ` -/

/-- The `0`-th coordinate of a `3`-vector.  These are the normal forms that make the endpoints
of the faces of the boxes below syntactically equal for neighbouring boxes. -/
@[simp] lemma vec3_0 {c0 c1 c2 : ℝ} : (![c0,c1,c2] : Fin 3 → ℝ) 0 = c0 := rfl
@[simp] lemma vec3_1 {c0 c1 c2 : ℝ} : (![c0,c1,c2] : Fin 3 → ℝ) 1 = c1 := rfl
@[simp] lemma vec3_2 {c0 c1 c2 : ℝ} : (![c0,c1,c2] : Fin 3 → ℝ) 2 = c2 := rfl

/-- The face of a box for the `0`-th coordinate, as a `2`-vector. -/
@[simp] lemma vec3_comp0 {c0 c1 c2 : ℝ} :
    ((![c0,c1,c2] : Fin 3 → ℝ) ∘ Fin.succAbove 0) = ![c1,c2] := by
  funext j; fin_cases j <;> rfl

/-- The face of a box for the `1`-st coordinate, as a `2`-vector. -/
@[simp] lemma vec3_comp1 {c0 c1 c2 : ℝ} :
    ((![c0,c1,c2] : Fin 3 → ℝ) ∘ Fin.succAbove 1) = ![c0,c2] := by
  funext j; fin_cases j <;> rfl

/-- The face of a box for the `2`-nd coordinate, as a `2`-vector. -/
@[simp] lemma vec3_comp2 {c0 c1 c2 : ℝ} :
    ((![c0,c1,c2] : Fin 3 → ℝ) ∘ Fin.succAbove 2) = ![c0,c1] := by
  funext j; fin_cases j <;> rfl

/-- **The sup norm of a `3`-vector is dominated by its `L²` norm.**  Used to transfer the
support radius between the coordinate space `Fin 3 → ℝ` and `ℝ³`. -/
lemma norm_le_norm_toLp (x : Fin 3 → ℝ) : ‖x‖ ≤ ‖(toLpCLM x : R3)‖ := by
  rw [toLpCLM_apply]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    fun i => PiLp.norm_apply_le (WithLp.toLp 2 x) i

/-! ## The two-plane divergence theorem in the coordinate space -/

/-- A face of a box lying outside the ball of radius `ρ` carries a vanishing integral. -/
lemma face_int_zero {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {ρ : ℝ}
    (hF : ∀ x, ρ ≤ ‖x‖ → F x = 0) {c : ℝ} (hc : ρ ≤ |c|) (i : Fin 3) (u v : Fin 2 → ℝ) :
    (∫ x : Fin 2 → ℝ in Set.Icc u v, F (i.insertNth c x) i) = 0 := by
  have h : ∀ x : Fin 2 → ℝ, F (i.insertNth c x) i = 0 := by
    intro x
    have h0 : F (i.insertNth c x) = 0 := by
      refine hF _ ?_
      calc ρ ≤ |c| := hc
        _ = ‖c‖ := (Real.norm_eq_abs c).symm
        _ = ‖(i.insertNth c x : Fin 3 → ℝ) i‖ := by rw [Fin.insertNth_apply_same]
        _ ≤ ‖(i.insertNth c x : Fin 3 → ℝ)‖ := norm_le_pi_norm _ i
    exact congrFun h0 i
  simp [h]

/-- A box in the coordinate space, the `i`-th coordinate running over `Ioc (c i) (d i)`.  The
half-open convention makes boxes that share a face *literally* disjoint. -/
abbrev Iocc (c d : Fin 3 → ℝ) : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun j => Set.Ioc (c j) (d j))

/-- Coordinates of a box with vector-literal endpoints. -/
lemma mem_pi_vals {P : ℝ → ℝ → Set ℝ} {c0 c1 c2 d0 d1 d2 : ℝ} {x : Fin 3 → ℝ} :
    x ∈ Set.pi Set.univ (fun j => P ((![c0,c1,c2] : Fin 3 → ℝ) j) ((![d0,d1,d2] : Fin 3 → ℝ) j)) ↔
      (x 0 ∈ P c0 d0) ∧ (x 1 ∈ P c1 d1) ∧ (x 2 ∈ P c2 d2) := by
  have hg : (fun j : Fin 3 => P ((![c0,c1,c2] : Fin 3 → ℝ) j) ((![d0,d1,d2] : Fin 3 → ℝ) j))
      = (![P c0 d0, P c1 d1, P c2 d2] : Fin 3 → Set ℝ) := by
    funext j
    fin_cases j <;> rfl
  have g0 : (![P c0 d0, P c1 d1, P c2 d2] : Fin 3 → Set ℝ) 0 = P c0 d0 := rfl
  have g1 : (![P c0 d0, P c1 d1, P c2 d2] : Fin 3 → Set ℝ) 1 = P c1 d1 := rfl
  have g2 : (![P c0 d0, P c1 d1, P c2 d2] : Fin 3 → Set ℝ) 2 = P c2 d2 := rfl
  rw [hg]
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun h => ?_⟩
  · simpa only [g0] using Set.mem_pi.mp h 0 trivial
  · simpa only [g1] using Set.mem_pi.mp h 1 trivial
  · simpa only [g2] using Set.mem_pi.mp h 2 trivial
  · refine Set.mem_pi.mpr ?_
    intro j hj
    fin_cases j
    · show x 0 ∈ P c0 d0; exact h.1
    · show x 1 ∈ P c1 d1; exact h.2.1
    · show x 2 ∈ P c2 d2; exact h.2.2

/-- Coordinates of an `Iocc`-box with vector-literal endpoints. -/
lemma mem_Iocc_vals {c0 c1 c2 d0 d1 d2 : ℝ} {x : Fin 3 → ℝ} :
    x ∈ Iocc (![c0,c1,c2] : Fin 3 → ℝ) (![d0,d1,d2] : Fin 3 → ℝ) ↔
      (x 0 ∈ Set.Ioc c0 d0) ∧ (x 1 ∈ Set.Ioc c1 d1) ∧ (x 2 ∈ Set.Ioc c2 d2) :=
  mem_pi_vals (P := Set.Ioc)

/-- `(-R, R] = (-R, 0] ∪ (0, R]`. -/
lemma Ioc_union_Ioc (R : ℝ) (hR : 0 < R) :
    Set.Ioc (-R) 0 ∪ Set.Ioc 0 R = Set.Ioc (-R) R := by
  ext x
  simp only [Set.mem_union, Set.mem_Ioc]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, by linarith⟩
    · exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩
    rcases le_or_gt x 0 with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h, h2⟩

/-- The big half-open box is the union of the two half-boxes cut out by the plane `x 0 = 0`. -/
lemma splitBig (R : ℝ) (hR : 0 < R) :
    Iocc ![(-R),(-R),(-R)] ![R,R,R]
      = Iocc ![0,(-R),(-R)] ![R,R,R] ∪ Iocc ![(-R),(-R),(-R)] ![0,R,R] := by
  ext x
  rw [Set.mem_union, mem_Iocc_vals, mem_Iocc_vals, mem_Iocc_vals]
  constructor
  · rintro ⟨h0, h1, h2⟩
    rw [Set.mem_Ioc] at h0 h1 h2
    rcases le_or_gt (x 0) 0 with h | h
    · exact Or.inr ⟨⟨h0.1, h⟩, h1, h2⟩
    · exact Or.inl ⟨⟨h, h0.2⟩, h1, h2⟩
  · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
    · rw [Set.mem_Ioc] at h0 h1 h2 ⊢
      exact ⟨⟨by linarith, h0.2⟩, h1, h2⟩
    · rw [Set.mem_Ioc] at h0 h1 h2 ⊢
      exact ⟨⟨h0.1, by linarith⟩, h1, h2⟩

/-- The half-box `x 0 ∈ (0,R]` splits along the plane `x 2 = 0`. -/
lemma splitP (R : ℝ) (hR : 0 < R) :
    Iocc ![0,(-R),(-R)] ![R,R,R]
      = Iocc ![0,(-R),0] ![R,R,R] ∪ Iocc ![0,(-R),(-R)] ![R,R,0] := by
  ext x
  rw [Set.mem_union, mem_Iocc_vals, mem_Iocc_vals, mem_Iocc_vals]
  constructor
  · rintro ⟨h0, h1, h2⟩
    rw [Set.mem_Ioc] at h0 h1 h2
    rcases le_or_gt (x 2) 0 with h | h
    · exact Or.inr ⟨h0, h1, ⟨h2.1, h⟩⟩
    · exact Or.inl ⟨h0, h1, ⟨h, h2.2⟩⟩
  · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
    · rw [Set.mem_Ioc] at h0 h1 h2 ⊢
      exact ⟨h0, h1, ⟨by linarith, h2.2⟩⟩
    · rw [Set.mem_Ioc] at h0 h1 h2 ⊢
      exact ⟨h0, h1, ⟨h2.1, by linarith⟩⟩

/-- The half-box `x 0 ∈ (-R,0]` splits along the plane `x 2 = 0`. -/
lemma splitM (R : ℝ) (hR : 0 < R) :
    Iocc ![(-R),(-R),(-R)] ![0,R,R]
      = Iocc ![(-R),(-R),0] ![0,R,R] ∪ Iocc ![(-R),(-R),(-R)] ![0,R,0] := by
  ext x
  rw [Set.mem_union, mem_Iocc_vals, mem_Iocc_vals, mem_Iocc_vals]
  constructor
  · rintro ⟨h0, h1, h2⟩
    rw [Set.mem_Ioc] at h0 h1 h2
    rcases le_or_gt (x 2) 0 with h | h
    · exact Or.inr ⟨h0, h1, ⟨h2.1, h⟩⟩
    · exact Or.inl ⟨h0, h1, ⟨h, h2.2⟩⟩
  · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
    · rw [Set.mem_Ioc] at h0 h1 h2 ⊢
      exact ⟨h0, h1, ⟨by linarith, h2.2⟩⟩
    · rw [Set.mem_Ioc] at h0 h1 h2 ⊢
      exact ⟨h0, h1, ⟨h2.1, by linarith⟩⟩

lemma disjBig (R : ℝ) :
    Disjoint (Iocc ![0,(-R),(-R)] ![R,R,R]) (Iocc ![(-R),(-R),(-R)] ![0,R,R]) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  rw [mem_Iocc_vals] at h1 h2
  rw [Set.mem_Ioc] at h1 h2
  exact absurd h1.1.1 (not_lt.mpr h2.1.2)

lemma disjP (R : ℝ) :
    Disjoint (Iocc ![0,(-R),0] ![R,R,R]) (Iocc ![0,(-R),(-R)] ![R,R,0]) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  rw [mem_Iocc_vals] at h1 h2
  rw [Set.mem_Ioc] at h1 h2
  exact absurd h1.2.2.1 (not_lt.mpr h2.2.2.2)

lemma disjM (R : ℝ) :
    Disjoint (Iocc ![(-R),(-R),0] ![0,R,R]) (Iocc ![(-R),(-R),(-R)] ![0,R,0]) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  rw [mem_Iocc_vals] at h1 h2
  rw [Set.mem_Ioc] at h1 h2
  exact absurd h1.2.2.1 (not_lt.mpr h2.2.2.2)

lemma measurableSet_Iocc (c d : Fin 3 → ℝ) : MeasurableSet (Iocc c d) := by
  rw [Iocc]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)

/-- **The divergence theorem off the two planes, in the coordinate space.**  If a field
`F : (Fin 3 → ℝ) → Fin 3 → ℝ` is continuous, differentiable with derivative `F'` off the
coordinate planes `x 0 = 0` and `x 2 = 0`, has integrable "divergence"
`x ↦ ∑ i, F' x (Pi.single i 1) i`, and both `F` and its divergence vanish outside the ball of
radius `ρ`, then the integral of the divergence vanishes. -/
theorem integral_trace_eq_zero_of_diff_off_planes
    (F : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (F' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (hcont : Continuous F)
    (hdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt F (F' x) x)
    (hint : MeasureTheory.Integrable fun x => ∑ i, F' x (Pi.single i 1) i)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hFsupp : ∀ x, ρ ≤ ‖x‖ → F x = 0)
    (hDsupp : ∀ x, ρ ≤ ‖x‖ → (∑ i, F' x (Pi.single i 1) i) = 0) :
    (∫ x, ∑ i, F' x (Pi.single i 1) i) = 0 := by
  set R : ℝ := ρ + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hρR : ρ ≤ R := by rw [hRdef]; linarith
  let D : (Fin 3 → ℝ) → ℝ := fun x => ∑ i, F' x (Pi.single i 1) i
  have hD0 : ∀ x, ρ ≤ ‖x‖ → D x = 0 := fun x hx => hDsupp x hx
  have hintD : MeasureTheory.Integrable D := hint
  have hRabs : ρ ≤ |R| := by rw [abs_of_pos hRpos]; exact hρR
  have hmRabs : ρ ≤ |-R| := by rw [abs_neg, abs_of_pos hRpos]; exact hρR
  -- the four boxes cut out by the two planes
  have hle1 : (![(0:ℝ),-R,0] : Fin 3 → ℝ) ≤ ![R,R,R] := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hlt1 : ∀ i, (![(0:ℝ),-R,0] : Fin 3 → ℝ) i < ![R,R,R] i := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hgood1 : ∀ x ∈ Set.pi Set.univ (fun i => Set.Ioo
      ((![(0:ℝ),-R,0] : Fin 3 → ℝ) i) ((![R,R,R] : Fin 3 → ℝ) i)), x 0 ≠ 0 ∧ x 2 ≠ 0 := by
    intro x hx
    have h := (mem_pi_vals (P := Set.Ioo)).mp hx
    exact ⟨ne_of_gt h.1.1, ne_of_gt h.2.2.1⟩
  have hbox1 : (∫ x in Set.Icc (![(0:ℝ),-R,0] : Fin 3 → ℝ) (![R,R,R] : Fin 3 → ℝ), D x)
      = ∑ i : Fin 3,
          ((∫ x in Set.Icc (((![(0:ℝ),-R,0] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![R,R,R] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![R,R,R] : Fin 3 → ℝ) i) x) i) -
            (∫ x in Set.Icc (((![(0:ℝ),-R,0] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![R,R,R] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![(0:ℝ),-R,0] : Fin 3 → ℝ) i) x) i)) := by
    exact box_divergence_identity (F := F) (F' := F') _ _ hle1 hlt1 hgood1
      hcont.continuousOn hdiff hint.integrableOn
  have hle2 : (![-R,-R,0] : Fin 3 → ℝ) ≤ ![0,R,R] := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hlt2 : ∀ i, (![-R,-R,0] : Fin 3 → ℝ) i < ![0,R,R] i := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hgood2 : ∀ x ∈ Set.pi Set.univ (fun i => Set.Ioo
      ((![-R,-R,0] : Fin 3 → ℝ) i) ((![0,R,R] : Fin 3 → ℝ) i)), x 0 ≠ 0 ∧ x 2 ≠ 0 := by
    intro x hx
    have h := (mem_pi_vals (P := Set.Ioo)).mp hx
    exact ⟨ne_of_lt h.1.2, ne_of_gt h.2.2.1⟩
  have hbox2 : (∫ x in Set.Icc (![-R,-R,0] : Fin 3 → ℝ) (![0,R,R] : Fin 3 → ℝ), D x)
      = ∑ i : Fin 3,
          ((∫ x in Set.Icc (((![-R,-R,0] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![0,R,R] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![0,R,R] : Fin 3 → ℝ) i) x) i) -
            (∫ x in Set.Icc (((![-R,-R,0] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![0,R,R] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![-R,-R,0] : Fin 3 → ℝ) i) x) i)) := by
    exact box_divergence_identity (F := F) (F' := F') _ _ hle2 hlt2 hgood2
      hcont.continuousOn hdiff hint.integrableOn
  have hle3 : (![(0:ℝ),-R,-R] : Fin 3 → ℝ) ≤ ![R,R,0] := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hlt3 : ∀ i, (![(0:ℝ),-R,-R] : Fin 3 → ℝ) i < ![R,R,0] i := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hgood3 : ∀ x ∈ Set.pi Set.univ (fun i => Set.Ioo
      ((![(0:ℝ),-R,-R] : Fin 3 → ℝ) i) ((![R,R,0] : Fin 3 → ℝ) i)), x 0 ≠ 0 ∧ x 2 ≠ 0 := by
    intro x hx
    have h := (mem_pi_vals (P := Set.Ioo)).mp hx
    exact ⟨ne_of_gt h.1.1, ne_of_lt h.2.2.2⟩
  have hbox3 : (∫ x in Set.Icc (![(0:ℝ),-R,-R] : Fin 3 → ℝ) (![R,R,0] : Fin 3 → ℝ), D x)
      = ∑ i : Fin 3,
          ((∫ x in Set.Icc (((![(0:ℝ),-R,-R] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![R,R,0] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![R,R,0] : Fin 3 → ℝ) i) x) i) -
            (∫ x in Set.Icc (((![(0:ℝ),-R,-R] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![R,R,0] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![(0:ℝ),-R,-R] : Fin 3 → ℝ) i) x) i)) := by
    exact box_divergence_identity (F := F) (F' := F') _ _ hle3 hlt3 hgood3
      hcont.continuousOn hdiff hint.integrableOn
  have hle4 : (![-R,-R,-R] : Fin 3 → ℝ) ≤ ![0,R,0] := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hlt4 : ∀ i, (![-R,-R,-R] : Fin 3 → ℝ) i < ![0,R,0] i := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hgood4 : ∀ x ∈ Set.pi Set.univ (fun i => Set.Ioo
      ((![-R,-R,-R] : Fin 3 → ℝ) i) ((![0,R,0] : Fin 3 → ℝ) i)), x 0 ≠ 0 ∧ x 2 ≠ 0 := by
    intro x hx
    have h := (mem_pi_vals (P := Set.Ioo)).mp hx
    exact ⟨ne_of_lt h.1.2, ne_of_lt h.2.2.2⟩
  have hbox4 : (∫ x in Set.Icc (![-R,-R,-R] : Fin 3 → ℝ) (![0,R,0] : Fin 3 → ℝ), D x)
      = ∑ i : Fin 3,
          ((∫ x in Set.Icc (((![-R,-R,-R] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![0,R,0] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![0,R,0] : Fin 3 → ℝ) i) x) i) -
            (∫ x in Set.Icc (((![-R,-R,-R] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![0,R,0] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![-R,-R,-R] : Fin 3 → ℝ) i) x) i)) := by
    exact box_divergence_identity (F := F) (F' := F') _ _ hle4 hlt4 hgood4
      hcont.continuousOn hdiff hint.integrableOn
  -- all faces at `x i = ±R` vanish, and the remaining faces are matched between neighbours
  rw [Fin.sum_univ_three] at hbox1 hbox2 hbox3 hbox4
  simp only [face_int_zero hFsupp hRabs, face_int_zero hFsupp hmRabs, vec3_0, vec3_1, vec3_2,
    vec3_comp0, vec3_comp1, vec3_comp2] at hbox1 hbox2 hbox3 hbox4
  -- `∫ D` over the big half-open box, and the two-stage splitting
  have hbig : (∫ x in Iocc ![(-R),(-R),(-R)] ![R,R,R], D x) = ∫ x, D x := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    refine hD0 x ?_
    by_contra hcon
    rw [not_le] at hcon
    have h0 : |x 0| < ρ := by
      rw [← Real.norm_eq_abs]
      exact lt_of_le_of_lt (norm_le_pi_norm x 0) hcon
    have h1 : |x 1| < ρ := by
      rw [← Real.norm_eq_abs]
      exact lt_of_le_of_lt (norm_le_pi_norm x 1) hcon
    have h2 : |x 2| < ρ := by
      rw [← Real.norm_eq_abs]
      exact lt_of_le_of_lt (norm_le_pi_norm x 2) hcon
    exact hx (by
      rw [mem_Iocc_vals]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        linarith [h0, h1, h2, neg_abs_le (x 0), le_abs_self (x 0), neg_abs_le (x 1),
          le_abs_self (x 1), neg_abs_le (x 2), le_abs_self (x 2), hρR])
  have hsplit1 : (∫ x in Iocc ![(-R),(-R),(-R)] ![R,R,R], D x)
      = (∫ x in Iocc ![0,(-R),(-R)] ![R,R,R], D x)
        + (∫ x in Iocc ![(-R),(-R),(-R)] ![0,R,R], D x) := by
    rw [splitBig R hRpos]
    exact MeasureTheory.setIntegral_union (disjBig R) (measurableSet_Iocc _ _) hintD.integrableOn
      hintD.integrableOn
  have hsplit2 : (∫ x in Iocc ![0,(-R),(-R)] ![R,R,R], D x)
      = (∫ x in Iocc ![0,(-R),0] ![R,R,R], D x)
        + (∫ x in Iocc ![0,(-R),(-R)] ![R,R,0], D x) := by
    rw [splitP R hRpos]
    exact MeasureTheory.setIntegral_union (disjP R) (measurableSet_Iocc _ _) hintD.integrableOn
      hintD.integrableOn
  have hsplit3 : (∫ x in Iocc ![(-R),(-R),(-R)] ![0,R,R], D x)
      = (∫ x in Iocc ![(-R),(-R),0] ![0,R,R], D x)
        + (∫ x in Iocc ![(-R),(-R),(-R)] ![0,R,0], D x) := by
    rw [splitM R hRpos]
    exact MeasureTheory.setIntegral_union (disjM R) (measurableSet_Iocc _ _) hintD.integrableOn
      hintD.integrableOn
  -- the half-open boxes are a.e. the closed boxes of the divergence theorem
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ))
      = MeasureTheory.Measure.pi (fun _ : Fin 3 => MeasureTheory.volume) :=
    MeasureTheory.volume_pi
  have hS1 : (∫ x in Iocc ![0,(-R),0] ![R,R,R], D x)
      = ∫ x in Set.Icc (![(0:ℝ),-R,0] : Fin 3 → ℝ) (![R,R,R] : Fin 3 → ℝ), D x := by
    refine MeasureTheory.setIntegral_congr_set ?_
    have h := MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc
      (μ := fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := (![(0:ℝ),-R,0] : Fin 3 → ℝ)) (g := (![R,R,R] : Fin 3 → ℝ))
    rw [← hvol] at h
    exact h
  have hS2 : (∫ x in Iocc ![(-R),(-R),0] ![0,R,R], D x)
      = ∫ x in Set.Icc (![-R,-R,0] : Fin 3 → ℝ) (![0,R,R] : Fin 3 → ℝ), D x := by
    refine MeasureTheory.setIntegral_congr_set ?_
    have h := MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc
      (μ := fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := (![-R,-R,0] : Fin 3 → ℝ)) (g := (![0,R,R] : Fin 3 → ℝ))
    rw [← hvol] at h
    exact h
  have hS3 : (∫ x in Iocc ![0,(-R),(-R)] ![R,R,0], D x)
      = ∫ x in Set.Icc (![(0:ℝ),-R,-R] : Fin 3 → ℝ) (![R,R,0] : Fin 3 → ℝ), D x := by
    refine MeasureTheory.setIntegral_congr_set ?_
    have h := MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc
      (μ := fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := (![(0:ℝ),-R,-R] : Fin 3 → ℝ)) (g := (![R,R,0] : Fin 3 → ℝ))
    rw [← hvol] at h
    exact h
  have hS4 : (∫ x in Iocc ![(-R),(-R),(-R)] ![0,R,0], D x)
      = ∫ x in Set.Icc (![-R,-R,-R] : Fin 3 → ℝ) (![0,R,0] : Fin 3 → ℝ), D x := by
    refine MeasureTheory.setIntegral_congr_set ?_
    have h := MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc
      (μ := fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := (![-R,-R,-R] : Fin 3 → ℝ)) (g := (![0,R,0] : Fin 3 → ℝ))
    rw [← hvol] at h
    exact h
  linarith [hbig.symm, hsplit1, hsplit2, hsplit3, hS1, hS2, hS3, hS4,
    hbox1, hbox2, hbox3, hbox4]

/-! ## Integration by parts for `ψ • ω` -/

theorem integral_div_mul_of_differentiable_off_planes {ω : R3 → R3} {ψ : R3 → ℝ}
    (hωcont : Continuous ω)
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x))
    (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    ∫ x, inner ℝ (ω x) (gradient ψ x)
      = -∫ x, FiniteTimeSingularity.div ω x * ψ x := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hGcont : Continuous (ψ • ω) := hψ.continuous.smul hωcont
  have hGcs : HasCompactSupport (ψ • ω) := hψcs.smul_right
  obtain ⟨ρ, hρpos, hρ⟩ := exists_norm_supp_bound (ψ • ω) hGcs
  -- integrability of the two summands whose sum is `div (ψ • ω)`
  have hint1 : MeasureTheory.Integrable (fun y : R3 => inner ℝ (gradient ψ y) (ω y)) := by
    refine (integrable_inner_gradient hωcont hψ hψcs).congr ?_
    filter_upwards with y
    exact (real_inner_comm (ω y) (gradient ψ y)).symm
  have hint2 : MeasureTheory.Integrable (fun y : R3 => ψ y * FiniteTimeSingularity.div ω y) :=
    integrable_mul_div hωint hψ hψcs
  have hae : (fun y : R3 => FiniteTimeSingularity.div (ψ • ω) y)
      =ᵐ[MeasureTheory.volume]
        fun y => ψ y * FiniteTimeSingularity.div ω y + inner ℝ (gradient ψ y) (ω y) := by
    filter_upwards [ae_coord_ne_zero] with y hy
    exact div_smul_eq hψd.differentiableAt ((hωdiff y hy.1 hy.2).differentiableAt)
  have hAdd : MeasureTheory.Integrable
      (fun y : R3 => ψ y * FiniteTimeSingularity.div ω y + inner ℝ (gradient ψ y) (ω y)) :=
    hint2.add hint1
  have hDivInt : MeasureTheory.Integrable
      (fun y : R3 => FiniteTimeSingularity.div (ψ • ω) y) := hAdd.congr hae.symm
  -- the transported field on the coordinate space
  have hHcont : Continuous (transport (ψ • ω)) := continuous_transport _ hGcont
  have hHdiff : ∀ x : Fin 3 → ℝ, x 0 ≠ 0 → x 2 ≠ 0 →
      HasFDerivAt (transport (ψ • ω)) (fderivTransport (ψ • ω) x) x := by
    intro x hx0 hx2
    refine hasFDerivAt_transport ?_
    have hy0 : (toLpCLM x) 0 ≠ 0 := by simpa using hx0
    have hy2 : (toLpCLM x) 2 ≠ 0 := by simpa using hx2
    exact (hψd.differentiableAt.smul
      (hωdiff (toLpCLM x) hy0 hy2).differentiableAt).hasFDerivAt
  have hH'integ : MeasureTheory.Integrable
      (fun x : Fin 3 → ℝ => ∑ i, fderivTransport (ψ • ω) x (Pi.single i 1) i) := by
    have h1 : MeasureTheory.Integrable
        (fun x : Fin 3 → ℝ => FiniteTimeSingularity.div (ψ • ω) (toLpCLM x)) :=
      integrable_div_transport (ψ • ω) hDivInt
    refine h1.congr ?_
    filter_upwards with x
    exact (sum_fderivTransport (ψ • ω) x).symm
  have hHsupp : ∀ x : Fin 3 → ℝ, ρ ≤ ‖x‖ → transport (ψ • ω) x = 0 := by
    intro x hx
    have h1 : ρ ≤ ‖toLpCLM x‖ := le_trans hx (norm_le_norm_toLp x)
    have h2 : (ψ • ω) (toLpCLM x) = 0 := (hρ (toLpCLM x) h1).1
    change WithLp.ofLp ((ψ • ω) (toLpCLM x)) = 0
    rw [h2]
    exact WithLp.ofLp_zero 2
  have hH'supp : ∀ x : Fin 3 → ℝ, ρ ≤ ‖x‖ →
      (∑ i, fderivTransport (ψ • ω) x (Pi.single i 1) i) = 0 := by
    intro x hx
    have h1 : ρ ≤ ‖toLpCLM x‖ := le_trans hx (norm_le_norm_toLp x)
    rw [sum_fderivTransport]
    exact (hρ (toLpCLM x) h1).2
  have hcore := integral_trace_eq_zero_of_diff_off_planes (transport (ψ • ω))
    (fderivTransport (ψ • ω)) hHcont hHdiff hH'integ ρ hρpos hHsupp hH'supp
  -- transport the conclusion back to `ℝ³`
  have hdivG : (∫ y : R3, FiniteTimeSingularity.div (ψ • ω) y) = 0 := by
    rw [← integral_div_transport (ψ • ω)]
    rw [MeasureTheory.integral_congr_ae (Eventually.of_forall
      (fun x : Fin 3 → ℝ => (sum_fderivTransport (ψ • ω) x).symm))]
    exact hcore
  have hzero : (∫ y : R3,
      ψ y * FiniteTimeSingularity.div ω y + inner ℝ (gradient ψ y) (ω y)) = 0 := by
    rw [← MeasureTheory.integral_congr_ae hae]
    exact hdivG
  have hsum : (∫ y : R3, ψ y * FiniteTimeSingularity.div ω y)
      + (∫ y : R3, inner ℝ (gradient ψ y) (ω y)) = 0 := by
    rw [← MeasureTheory.integral_add hint2 hint1]
    exact hzero
  have hflip1 : (∫ y : R3, inner ℝ (ω y) (gradient ψ y))
      = ∫ y : R3, inner ℝ (gradient ψ y) (ω y) :=
    MeasureTheory.integral_congr_ae (Eventually.of_forall
      fun y => (real_inner_comm (ω y) (gradient ψ y)).symm)
  have hflip2 : (∫ y : R3, FiniteTimeSingularity.div ω y * ψ y)
      = ∫ y : R3, ψ y * FiniteTimeSingularity.div ω y :=
    MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  rw [hflip1, hflip2]
  linarith

end Work.FTS.PressureOn
