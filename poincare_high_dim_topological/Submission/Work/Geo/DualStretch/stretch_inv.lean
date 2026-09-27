import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.coord_spec
import Submission.Work.Geo.DualStretch.stretch_defs
import Submission.Work.Geo.DualStretch.massG_api
import Submission.Work.Geo.DualStretch.massG_of_chain_repr
import Submission.Work.Geo.DualStretch.stretch_aux
import Submission.Work.Geo.DualStretch.stretch_relations

/-!
# The stretch is inverted by the stretch with the reciprocal taper

`Work.Geo.DualStretch.stretch P hP β p α M x` rescales the high mass of `x` by the taper
`taperM β p P hP α M x` and renormalises.  The rescaled masses are `wtOf β p P hP α M x τ`
(see `stretch_defs.lean`): low level sets keep their mass divided by `d = denOf … x`, high ones
have it multiplied by `taperM x / d`.  Two consequences (proved in `stretch_aux` and
`stretch_relations`) drive the inverse law:

* the stretched point is the convex combination `∑ wtOf τ • bary τ` on the *same* chain of level
  sets, so `massG` of the stretched point is `wtOf` again (`massG_of_chain_repr`);
* the join segment `segOf` is unchanged, so the taper at the image equals the taper at the source.

Writing `c = taperM … x`, `S = SOf … x`, `d = denOf … x`, `A = AOf … x`, `B = BOf … x`, and
recalling `A + B = x`, `d = (1 - S) + c * S`, `SOf (stretch x) = c * S / d`,
`AOf (stretch x) = d⁻¹ • A` and `BOf (stretch x) = (c / d) • B`, the composition expands to

  `(1 + (c⁻¹ - 1) * (c * S / d))⁻¹ • (d⁻¹ • A + c⁻¹ • ((c / d) • B))`

whose scalar factor is `d⁻¹` while the vector is `d⁻¹ • x`, giving `x` back.
-/
open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open _root_.PL (E Cx)

/-- A subset of the carrier face of a point of `P.space` is a candidate level set. -/
theorem mem_cands_of_subset_carrier {n : ℕ} (P : Cx n) (hP : P.faces.Finite) {y : E n}
    (hy : y ∈ P.space) {τ : Finset (E n)} (h : τ ⊆ carrier P y) : τ ∈ cands P hP := by
  rw [cands, Finset.mem_biUnion]
  exact ⟨carrier P y, (Set.Finite.mem_toFinset hP).mpr (carrier_spec P hP hy).1,
    Finset.mem_powerset.mpr h⟩

/-- The scalar/vector algebra of the inverse law: if `d = 1 + (c - 1) * S` with `c, d ≠ 0`, then
the renormalised affine combination with reciprocal factor `c⁻¹` is the identity on `A + B`. -/
theorem inv_algebra {n : ℕ} {c S d : ℝ} (hd : d = 1 + (c - 1) * S) (hd0 : d ≠ 0) (hc0 : c ≠ 0)
    {A B : E n} :
    (1 + (c⁻¹ - 1) * (c * S / d))⁻¹ • (d⁻¹ • A + c⁻¹ • ((c / d) • B)) = A + B := by
  have hcd : (c⁻¹ - 1) * (c * S / d) = (1 - c) * S / d := by field_simp
  have h1 : 1 + (c⁻¹ - 1) * (c * S / d) = d⁻¹ := by
    have hS : (1 - c) * S = 1 - d := by rw [hd]; ring
    rw [hcd, hS]
    field_simp
    ring
  have h2 : d * c⁻¹ * (c / d) = 1 := by field_simp
  have h3 : d * d⁻¹ = 1 := mul_inv_cancel₀ hd0
  have hdA : d • (d⁻¹ • A) = A := by rw [smul_smul, h3, one_smul]
  have hdB : d • (c⁻¹ • ((c / d) • B)) = B := by rw [smul_smul, smul_smul, h2, one_smul]
  rw [h1, inv_inv, smul_add, hdA, hdB]

theorem stretch_inv {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {β α M : ℝ} (hM : 0 < M) {p : ℕ}
    {x : PL.E n} (hx : x ∈ P.space) :
    Work.Geo.DualStretch.stretchM β p P hP
        (fun y => (Work.Geo.DualStretch.taperM β p P hP α M y)⁻¹)
        (Work.Geo.DualStretch.stretch P hP β p α M x) = x := by
  classical
  -- the bookkeeping of the rescaled mass decomposition
  obtain ⟨hcpos, hS0, hS1, hdpos, hCfaces, hCne, hCchain, hCwtpos, hCwtsum, hy, hydec⟩ :=
    stretch_aux (β := β) (α := α) (M := M) (p := p) (x := x) P hP hM hx
  -- `massG` of the stretched point is the rescaled mass on the same chain of level sets
  obtain ⟨hwtC, hwtOff⟩ :=
    massG_of_chain_repr P hP (posCands P hP x) (fun τ hτ => hCfaces τ hτ) hCne hCchain
      (wtOf β p P hP α M x) hCwtpos hCwtsum (y := stretch P hP β p α M x) hydec
  have hwt : ∀ τ : Finset (PL.E n), massG P hP (stretch P hP β p α M x) τ =
      if τ ∈ posCands P hP x then wtOf β p P hP α M x τ else 0 := by
    intro τ
    by_cases hτ : τ ∈ posCands P hP x
    · rw [ite_eq_left hτ]; exact hwtC τ hτ
    · rw [ite_eq_right hτ]
      by_cases hτc : τ ∈ cands P hP
      · exact hwtOff τ hτc hτ
      · exact (massG_api P hP hy).2.2.2.1 τ
          (fun hsub => hτc (mem_cands_of_subset_carrier P hP hy hsub))
  -- the transformations of `SOf`, `AOf`, `BOf` and of the join segment
  obtain ⟨hBS, hBA, hBB, hBseg⟩ := stretch_relations (β := β) (α := α) (M := M) (p := p) P hP hM hx hwt
  have hcy : taperM β p P hP α M (stretch P hP β p α M x) = taperM β p P hP α M x :=
    taperM_congr hBseg
  have hAB : AOf β p P hP x + BOf β p P hP x = x := AOf_add_BOf P hP hx
  have hc0 : taperM β p P hP α M x ≠ 0 := ne_of_gt hcpos
  have hd0 : denOf β p P hP α M x ≠ 0 := ne_of_gt hdpos
  have hmain : (1 + ((taperM β p P hP α M (stretch P hP β p α M x))⁻¹ - 1) *
        SOf β p P hP (stretch P hP β p α M x))⁻¹ •
        (AOf β p P hP (stretch P hP β p α M x) +
          (taperM β p P hP α M (stretch P hP β p α M x))⁻¹ •
            BOf β p P hP (stretch P hP β p α M x)) = AOf β p P hP x + BOf β p P hP x := by
    rw [hcy, hBS, hBA, hBB]
    exact inv_algebra rfl hd0 hc0
  unfold stretchM
  rw [ite_eq_left hy]
  simp only []
  rw [hmain, hAB]

end Work.Geo.DualStretch
