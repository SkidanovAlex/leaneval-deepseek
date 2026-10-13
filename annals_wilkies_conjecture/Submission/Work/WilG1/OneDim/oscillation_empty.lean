/-
  WilG1 / OneDim / oscillation_empty.

  Let `g : ℝ → ℝ` have an `Ω`-definable graph in an abstract sharply o-minimal structure and
  let `q : ℝ`.  Then the set of `x` at which the right difference quotients of `g` take values
  both above and below `q` arbitrarily close to `x` has empty interior.  In fact that set is
  empty.

  Write `h = g - q·id`.  Then `x` lies in the oscillation set iff on every right neighbourhood
  of `x` the function `h` takes values both above and below `h x`.  If `x` is such a point,
  the `Ω`-set `A = {y | h y > h x}` accumulates at `x` from the right; by the
  one-dimensional o-minimality axiom `SOMin.comps` (every `Ω`-set of dimension one is a finite
  union of preconnected sets, i.e. of intervals) `A` then contains a whole right neighbourhood
  of `x`, contradicting the second half of the oscillation condition at `x`.

  The two ingredients are established here:

  * `interval_mem_of_accumulates` — the o-minimality step.  An `Ω`-set of dimension one which
    accumulates at `x` from the right contains an interval `(x, β)`; the preconnected pieces
    given by `comps` are transported to `ℝ` along `Homeomorph.funUnique (Fin 1) ℝ`, where
    preconnected sets are order convex.

  * `aboveGraphSet_mem` — the half-space `{(u, t) | t - q u > c}` over the graph of `g` is an
    `Ω`-set of dimension two, and projecting it out gives the `Ω`-set
    `{u | c < g (u 0) - q * u 0}` of dimension one.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.ChoiceDefs
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG1.Calc.finite_of_interior_empty
import Submission.Work.WilG4b.posPoly_mem

noncomputable section

namespace Work.WilG1.OneDim

open WilkiesDesign

/-! ## 1. An `Ω`-set of dimension one that accumulates from the right contains an interval -/

theorem interval_mem_of_accumulates {S : WilkiesDesign.SOMin} {a d : ℕ} {A : Set (Fin 1 → ℝ)}
    (hA : A ∈ S.Ω a d 1) {x : ℝ}
    (hacc : ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, (fun _ : Fin 1 => y) ∈ A ∧ x < y ∧ y < x + δ) :
    ∃ β : ℝ, x < β ∧ ∀ y : ℝ, x < y → y < β → (fun _ : Fin 1 => y) ∈ A := by
  -- The right half-line `{z | x < z 0}` is an `Ω`-set, as the positivity set of `X₀ - x`.
  set P : MvPolynomial (Fin 1) ℝ := MvPolynomial.X 0 - MvPolynomial.C x with hP
  set H : Set (Fin 1 → ℝ) := {z | x < z 0} with hH
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
        ⟨hyA, by simp only [H, Set.mem_ofPred_eq]; exact hyx⟩, heapp y⟩
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
  have hpos : ∀ t ∈ e '' c, x < t := by
    rintro t ⟨z, hz, rfl⟩
    rw [he0 z]
    exact (hcc hz).2
  -- `e '' c ⊆ (x, ∞)` accumulates at `x` from the right, hence is an interval `(x, y₀)`.
  obtain ⟨y0, hy0c, -⟩ := (Metric.mem_closure_iff.mp hxI) 1 one_pos
  have hxy0 : x < y0 := hpos y0 hy0c
  refine ⟨y0, hxy0, fun y hy hyy0 => ?_⟩
  obtain ⟨u, huc, hud⟩ := (Metric.mem_closure_iff.mp hxI) (y - x) (by linarith)
  have hu_lt : u < y := by
    have hux : x < u := hpos u huc
    rw [Real.dist_eq, abs_lt] at hud
    linarith
  have hyc : y ∈ e '' c := hconv.out huc hy0c ⟨le_of_lt hu_lt, le_of_lt hyy0⟩
  obtain ⟨z, hzc, hzy⟩ := hyc
  have hz_eq : z = fun _ : Fin 1 => y := e.injective (by rw [hzy, heapp y])
  rw [← hz_eq]
  exact (hcc hzc).1

/-! ## 2. The half-space over the graph of `g` is `Ω`-definable in dimension one -/

theorem aboveGraphSet_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (q c : ℝ) (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    {u : Fin 1 → ℝ | c < g (u 0) - q * (u 0)} ∈ S.Ω (F + 20) (D + 20) 1 := by
  -- The polynomial `t - q u - c`, whose positivity cuts out the half-space.
  set P2 : MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.X (Fin.last 1) - MvPolynomial.C q * MvPolynomial.X (Fin.castSucc (0 : Fin 1))
      - MvPolynomial.C c with hP2
  have htd : P2.totalDegree ≤ 2 := by
    rw [hP2]
    refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
    · refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
      · refine le_trans (le_of_eq (MvPolynomial.totalDegree_X (Fin.last 1))) ?_
        norm_num
      · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        rw [show (MvPolynomial.C q : MvPolynomial (Fin 2) ℝ).totalDegree = 0 from
              MvPolynomial.totalDegree_C q,
            show (MvPolynomial.X (Fin.castSucc (0 : Fin 1)) :
                MvPolynomial (Fin 2) ℝ).totalDegree = 1 from MvPolynomial.totalDegree_X _]
        norm_num
    · refine le_trans (le_of_eq (MvPolynomial.totalDegree_C c)) ?_
      norm_num
  set G : Set (Fin 2 → ℝ) := WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) with hG
  set H : Set (Fin 2 → ℝ) := {z | 0 < MvPolynomial.eval z P2} with hH
  have hHmem : H ∈ S.Ω 6 (P2.totalDegree + 3) 2 := by
    rw [hH]
    exact Work.WilG4b.posPoly_mem (S := S) (P := P2)
  have hGm : G ∈ S.Ω (max F 6) D 2 := Work.WilG1.Omega.mono hg (le_max_left _ _) le_rfl
  have hHm : H ∈ S.Ω (max F 6) (P2.totalDegree + 3) 2 :=
    Work.WilG1.Omega.mono hHmem (le_max_right _ _) le_rfl
  have hinter : G ∩ H ∈ S.Ω (max F 6 + 1) (D + (P2.totalDegree + 3)) 2 := by
    have h := S.inter (F := max F 6) (n := 2) (k := 2)
      (D := fun i : Fin 2 => if i = 0 then D else P2.totalDegree + 3)
      (A := fun i : Fin 2 => if i = 0 then G else H)
      (by intro i; fin_cases i
          · simpa using hGm
          · simpa using hHm)
    rw [Work.WilG1.Omega.iInter_fin_two] at h
    have hsum : (∑ i : Fin 2, (if i = (0 : Fin 2) then D else P2.totalDegree + 3))
        = D + (P2.totalDegree + 3) := by
      rw [Fin.sum_univ_two]; simp
    rw [hsum] at h
    exact h
  have hproj : WilkiesDesign.projLast (G ∩ H) ∈
      S.Ω (max F 6 + 1 + 1) (D + (P2.totalDegree + 3)) 1 := S.proj hinter
  have hset : WilkiesDesign.projLast (G ∩ H) =
      {u : Fin 1 → ℝ | c < g (u 0) - q * (u 0)} := by
    ext u
    constructor
    · rintro ⟨t, htG, htH⟩
      have h1 : t = g (u 0) := by
        rw [hG] at htG
        simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq] at htG
        rw [Fin.snoc_last, Fin.init_snoc] at htG
        exact htG
      have h2 : 0 < t - q * (u 0) - c := by
        rw [hH] at htH
        simp only [Set.mem_ofPred_eq] at htH
        rw [hP2] at htH
        simpa only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X,
          MvPolynomial.eval_C, Fin.snoc_last, Fin.snoc_castSucc] using htH
      simp only [Set.mem_ofPred_eq]
      rw [h1] at h2
      linarith
    · intro hu
      simp only [Set.mem_ofPred_eq] at hu
      refine ⟨g (u 0), ?_, ?_⟩
      · rw [hG]
        simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq]
        rw [Fin.snoc_last, Fin.init_snoc]
      · rw [hH]
        simp only [Set.mem_ofPred_eq]
        rw [hP2]
        simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X,
          MvPolynomial.eval_C, Fin.snoc_last, Fin.snoc_castSucc]
        linarith
  rw [hset] at hproj
  exact Work.WilG1.Omega.mono hproj (by omega) (by omega)

/-! ## 3. The oscillation set has empty interior -/

theorem oscillation_empty {S : WilkiesDesign.SOMin} {F D : ℕ} (q : ℝ) (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    interior {x : ℝ | (∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x < y ∧ y < x + δ ∧ q < (g y - g x) / (y - x))
      ∧ (∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x < y ∧ y < x + δ ∧ (g y - g x) / (y - x) < q)} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨h1, h2⟩ := interior_subset hx
  -- `h = g - q·id`, so that `dq g x y > q ↔ h y > h x`.
  set c : ℝ := g x - q * x with hc
  have hac : ∀ δ : ℝ, 0 < δ →
      ∃ y : ℝ, (fun _ : Fin 1 => y) ∈ {u : Fin 1 → ℝ | c < g (u 0) - q * (u 0)} ∧
        x < y ∧ y < x + δ := by
    intro δ hδ
    obtain ⟨y, hyx, hyδ, hslope⟩ := h1 δ hδ
    refine ⟨y, ?_, hyx, hyδ⟩
    have hyx' : 0 < y - x := by linarith
    have h2' : q * (y - x) < g y - g x := (lt_div_iff₀ hyx').mp hslope
    simp only [Set.mem_ofPred_eq]
    rw [hc]
    linarith
  -- The `Ω`-set `{y | h y > h x}` accumulates at `x` from the right, so it contains `(x, β)`.
  obtain ⟨β, hxβ, hβ⟩ :=
    interval_mem_of_accumulates (aboveGraphSet_mem (S := S) q c g hg) (x := x) hac
  -- But the second half of the oscillation condition forbids that.
  obtain ⟨y, hyx, hyβ', hslope2⟩ := h2 (β - x) (by linarith)
  have hyβ : y < β := by linarith
  have hyA : c < g y - q * y := hβ y hyx hyβ
  have hyx' : 0 < y - x := by linarith
  have h2'' : g y - g x < q * (y - x) := (div_lt_iff₀ hyx').mp hslope2
  rw [hc] at hyA
  linarith

end Work.WilG1.OneDim
