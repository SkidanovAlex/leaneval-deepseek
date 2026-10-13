/-
  WilG1 / Thin : the left oscillation set `oscL g q` has empty interior.

  This is the left-handed mirror of `Work.WilG1.OneDim.oscillation_empty`, adapted to the
  vocabulary of the thin one-dimensional theory.  The two ingredients are

  * `interval_mem_of_accumulates_left` below: an `Ω`-set of dimension one that accumulates
    at `x` from the *left* contains a whole left-neighbourhood `(β, x)` of `x`
    (a copy of `Work.WilG1.OneDim.interval_mem_of_accumulates`, mirrored across `x`), and

  * `Work.WilG1.OneDim.aboveGraphSet_mem`: the superlevel set `{u | c < g (u 0) - q·(u 0)}`
    is an `Ω`-set of dimension one.

  Writing `h = g - q·id`, left difference quotients of `g` at `x` above `q` correspond to
  `h y < h x`, and below `q` to `h y > h x`.  If `x` were an interior point of `oscL g q`,
  the second half of the oscillation condition says that the `Ω`-set `{h > h x}` accumulates
  at `x` from the left, so it contains `(β, x)`; the first half then exhibits `y ∈ (β, x)`
  with `h y < h x`, a contradiction.
-/
import Mathlib
import Submission.Work.WilG1.OneDim.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.oscillation_empty
import Submission.Work.WilG1.OneDim.interval_of_accumulates

noncomputable section

open Classical

namespace Work.WilG1.Thin

open WilkiesDesign

/-! ## The left-handed interval lemma -/

/-- The left-handed mirror of `Work.WilG1.OneDim.interval_mem_of_accumulates`: an `Ω`-set of
dimension one accumulating at `x` from the left contains a whole left-neighbourhood of `x`.

The proof mirrors the right-handed version: intersect with the left half-line
`{z | z 0 < x}` (an `Ω`-set, being the positivity set of the affine polynomial `C x - X 0`),
decompose into finitely many preconnected pieces via `SOMin.comps`, transport to `ℝ` along
`Homeomorph.funUnique (Fin 1) ℝ`, and use that a preconnected subset of `ℝ` is order-convex
to fill in the interval. -/
theorem interval_mem_of_accumulates_left {S : WilkiesDesign.SOMin} {a d : ℕ} {A : Set (Fin 1 → ℝ)}
    (hA : A ∈ S.Ω a d 1) {x : ℝ}
    (hacc : ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, (fun _ : Fin 1 => y) ∈ A ∧ x - δ < y ∧ y < x) :
    ∃ β : ℝ, β < x ∧ ∀ y : ℝ, β < y → y < x → (fun _ : Fin 1 => y) ∈ A := by
  -- The left half-line `{z | z 0 < x}` is an `Ω`-set, as the positivity set of `C x - X 0`.
  set P : MvPolynomial (Fin 1) ℝ := MvPolynomial.C x - MvPolynomial.X 0 with hP
  set H : Set (Fin 1 → ℝ) := {z | z 0 < x} with hH
  have hHmem : H ∈ S.Ω 5 (P.totalDegree + 3) 1 := by
    have h := Work.WilG4b.posPoly_mem (S := S) (P := P)
    have hset : {z : Fin 1 → ℝ | 0 < MvPolynomial.eval z P} = H := by
      rw [hH]
      ext z
      simp only [Set.mem_ofPred_eq, hP, MvPolynomial.eval_sub, MvPolynomial.eval_X,
        MvPolynomial.eval_C]
      constructor <;> intro hh <;> linarith
    rw [hset] at h
    exact h
  have hAm : A ∈ S.Ω (max a 5) d 1 := Work.WilG1.Omega.mono hA (le_max_left _ _) le_rfl
  have hHm : H ∈ S.Ω (max a 5) (P.totalDegree + 3) 1 :=
    Work.WilG1.Omega.mono hHmem (le_max_right _ _) le_rfl
  have hA1 : A ∩ H ∈ S.Ω (max a 5 + 1) (d + (P.totalDegree + 3)) 1 := by
    have h := S.inter (F := max a 5) (n := 1) (k := 2)
      (D := fun i : Fin 2 => if i = 0 then d else P.totalDegree + 3)
      (A := fun i : Fin 2 => if i = 0 then A else H)
      (by intro i; fin_cases i
          · simpa using hAm
          · simpa using hHm)
    rw [Work.WilG1.Omega.iInter_fin_two] at h
    have hsum : (∑ i : Fin 2, (if i = (0 : Fin 2) then d else P.totalDegree + 3))
        = d + (P.totalDegree + 3) := by
      rw [Fin.sum_univ_two]; simp
    rw [hsum] at h
    exact h
  -- `comps`: `A ∩ H` is a finite union of preconnected pieces.
  obtain ⟨p, hp⟩ := S.comps (max a 5 + 1)
  obtain ⟨s, -, hconn, hA1eq⟩ := hp (d + (P.totalDegree + 3)) (A ∩ H) hA1
  -- Transport to `ℝ`.
  let e : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ
  have heapp : ∀ t : ℝ, e (fun _ : Fin 1 => t) = t := by
    intro t; rw [Homeomorph.funUnique_apply]
  have he0 : ∀ z : Fin 1 → ℝ, e z = z 0 := by
    intro z; rw [Homeomorph.funUnique_apply]
    exact congrArg z (Subsingleton.elim default 0)
  set s' : Finset (Set ℝ) := s.image (fun c => e '' c) with hs'
  have hsub : e '' (A ∩ H) = ⋃₀ (s' : Set (Set ℝ)) := by
    rw [hA1eq, hs', Set.image_sUnion, Finset.coe_image]
  have hxcl : x ∈ closure (e '' (A ∩ H)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨y, hyA, hyx, hyδ⟩ := hacc ε hε
    refine ⟨y, ?_, ?_⟩
    · exact ⟨fun _ : Fin 1 => y,
        ⟨hyA, by simp only [H, Set.mem_ofPred_eq]; exact hyδ⟩, heapp y⟩
    · rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  rw [hsub] at hxcl
  have hfin : ((s' : Set (Set ℝ))).Finite := Finset.finite_toSet s'
  have hcl : closure (⋃₀ (s' : Set (Set ℝ))) = ⋃ I ∈ (s' : Set (Set ℝ)), closure I := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.closure_biUnion id
  rw [hcl, Set.mem_iUnion] at hxcl
  obtain ⟨I, hxclI⟩ := hxcl
  rw [Set.mem_iUnion] at hxclI
  obtain ⟨hIs, hxI⟩ := hxclI
  simp only [Finset.mem_coe] at hIs
  rw [hs', Finset.mem_image] at hIs
  obtain ⟨c, hcs, rfl⟩ := hIs
  have hcc : c ⊆ A ∩ H := by
    intro z hz
    rw [hA1eq]
    exact Set.mem_sUnion.mpr ⟨c, hcs, hz⟩
  have hcconn : IsPreconnected c := hconn c hcs
  have hpre : IsPreconnected (e '' c) := hcconn.image e e.continuous.continuousOn
  have hconv : (e '' c).OrdConnected := isPreconnected_iff_ordConnected.mp hpre
  have hneg : ∀ t ∈ e '' c, t < x := by
    rintro t ⟨z, hz, rfl⟩
    rw [he0 z]
    exact (hcc hz).2
  -- `e '' c ⊆ (-∞, x)` accumulates at `x` from the left, hence is an interval `(y₀, x)`.
  obtain ⟨y0, hy0c, -⟩ := (Metric.mem_closure_iff.mp hxI) 1 one_pos
  have hy0x : y0 < x := hneg y0 hy0c
  refine ⟨y0, hy0x, fun y hy hyx => ?_⟩
  obtain ⟨u, huc, hud⟩ := (Metric.mem_closure_iff.mp hxI) (x - y) (by linarith)
  have huy : y < u := by
    have hux : u < x := hneg u huc
    rw [Real.dist_eq, abs_lt] at hud
    linarith
  have hyc : y ∈ e '' c := hconv.out hy0c huc ⟨le_of_lt hy, le_of_lt huy⟩
  obtain ⟨z, hzc, hzy⟩ := hyc
  have hz_eq : z = fun _ : Fin 1 => y := e.injective (by rw [hzy, heapp y])
  rw [← hz_eq]
  exact (hcc hzc).1

/-! ## The left oscillation set has empty interior -/

theorem oneDim_oscL_empty {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (q : ℝ) :
    interior (Work.WilG1.oscL g q) = ∅ := by
  rw [Work.WilG1.oscL]
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨h1, h2⟩ := interior_subset hx
  -- `h = g - q·id`, so that `dq g x y > q ↔ h y < h x` and `dq g x y < q ↔ h y > h x`
  -- (for `y < x`).
  set c : ℝ := g x - q * x with hc
  -- `A = {h > h x}` is `Ω`-definable (dimension one).
  have hAmem : {u : Fin 1 → ℝ | c < g (u 0) - q * (u 0)} ∈ S.Ω (F + 20) (D + 20) 1 :=
    Work.WilG1.OneDim.aboveGraphSet_mem (S := S) q c g hg
  -- `A` accumulates at `x` from the left, by the second half of the oscillation condition.
  have hacc : ∀ δ : ℝ, 0 < δ → ∃ y : ℝ,
      (fun _ : Fin 1 => y) ∈ {u : Fin 1 → ℝ | c < g (u 0) - q * (u 0)} ∧ x - δ < y ∧ y < x := by
    intro δ hδ
    obtain ⟨y, hy1, hy2, hslope⟩ := h2 δ hδ
    refine ⟨y, ?_, hy1, hy2⟩
    have hgt : q * (y - x) < g y - g x :=
      (div_lt_iff_of_neg (by linarith : y - x < 0)).mp (by simpa only [Work.WilG1.dq] using hslope)
    simp only [Set.mem_ofPred_eq]
    rw [hc]
    linarith
  obtain ⟨α, hαx, hαsub⟩ := interval_mem_of_accumulates_left (S := S) hAmem hacc
  -- The first half exhibits `y ∈ (α, x)` with `h y < h x`, contradicting `y ∈ A`.
  obtain ⟨y, hy1, hy2, hslope⟩ := h1 (x - α) (by linarith)
  have hyα : α < y := by linarith
  have hyA : c < g y - q * y := hαsub y hyα hy2
  have hlt : g y - g x < q * (y - x) :=
    (lt_div_iff_of_neg (by linarith : y - x < 0)).mp (by simpa only [Work.WilG1.dq] using hslope)
  rw [hc] at hyA
  linarith

end Work.WilG1.Thin
