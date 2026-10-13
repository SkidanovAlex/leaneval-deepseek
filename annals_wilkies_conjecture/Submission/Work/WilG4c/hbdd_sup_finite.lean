import Mathlib
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.CurveFamDefs
import Submission.Work.WilG4c.hbdd_defs
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG4c.graphOfCompGen
import Submission.Work.WilG4c.IterDirAux
import Submission.Work.WilG4c.iterDir_perm
import Submission.Work.WilG4c.psi_facts
import Submission.Work.WilG4c.psi_contDiffAt
import Submission.Work.WilG4c.hbdd_psi_graph_fb
import Submission.Work.WilG4c.iterDir_slice_transport
import Submission.Work.WilG4c.graphOf_chi_mem
import Submission.Work.WilG4c.chi_ybound
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

open scoped Topology

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

namespace Work.WilG4c

/-! ## Elementary helpers -/

/-- The `C^n`-locus of a function is open (for finite `n`). -/
lemma hbdd_isOpen_locus {N : ℕ} {n : WithTop ℕ∞} (hn : n ≠ ↑(⊤ : ℕ∞))
    (g : (Fin N → ℝ) → ℝ) :
    IsOpen {z : Fin N → ℝ | ContDiffAt ℝ n g z} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hz' : ContDiffAt ℝ n g z := hz
  exact Filter.mem_of_superset (hz'.eventually hn) (fun y hy => hy)

/-- Membership in the interior of the `C^n`-locus. -/
lemma hbdd_mem_interior_locus {N : ℕ} {n : WithTop ℕ∞} (hn : n ≠ ↑(⊤ : ℕ∞))
    (g : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) :
    z ∈ interior {z' : Fin N → ℝ | ContDiffAt ℝ n g z'} ↔ ContDiffAt ℝ n g z := by
  rw [(hbdd_isOpen_locus hn g).interior_eq]
  simp only [Set.mem_setOf_eq]

lemma hbdd_natCast_ne_top {k : ℕ} : ((k : ℕ) : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞) := by
  simp

/-- Membership in the interior of the `C^m`-locus, `m` a natural number. -/
lemma hbdd_mem_interior_locus_nat {N : ℕ} (m : ℕ) (g : (Fin N → ℝ) → ℝ)
    (z : Fin N → ℝ) :
    z ∈ interior {z' : Fin N → ℝ | ContDiffAt ℝ m g z'} ↔ ContDiffAt ℝ m g z :=
  hbdd_mem_interior_locus (n := ((m : ℕ) : WithTop ℕ∞)) hbdd_natCast_ne_top g z

/-- The iterated directional derivative is the `iteratedFDeriv` evaluated on the corresponding
unit coordinate vectors. -/
theorem hbdd_iterDir_jet {m : ℕ} (L : List (Fin m)) (G : (Fin m → ℝ) → ℝ) (z : Fin m → ℝ)
    (hG : ContDiffAt ℝ L.length G z) :
    iterDir L G z = iteratedFDeriv ℝ L.length G z
      (fun k => (Pi.single (L.get k) (1 : ℝ) : Fin m → ℝ)) := by
  revert G z
  induction L with
  | nil =>
    intro G z _
    simp [iterDir_nil, iteratedFDeriv_zero_apply]
  | cons i L' ih =>
    intro G z hG
    simp only [iterDir_cons]
    have hev : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ (L'.length) G w := by
      have hne : ((L'.length + 1 : ℕ) : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
      have h1 := hG.eventually hne
      filter_upwards [show ∀ᶠ y in 𝓝 z, ContDiffAt ℝ (L'.length + 1) G y from by
        simpa using h1] with w hw
      exact hw.of_le (by exact_mod_cast Nat.le_succ L'.length :
        (L'.length : WithTop ℕ∞) ≤ ((L'.length + 1 : ℕ) : WithTop ℕ∞))
    have heq : iterDir L' G =ᶠ[𝓝 z]
        (fun w => iteratedFDeriv ℝ (L'.length) G w
          (fun k => (Pi.single (L'.get k) (1 : ℝ) : Fin m → ℝ))) := by
      filter_upwards [hev] with w hw
      exact ih G w hw
    rw [heq.fderiv_eq]
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ (L'.length) G) z :=
      hG.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self L'.length)
    rw [fderiv_continuousMultilinear_apply_const_apply (c := iteratedFDeriv ℝ (L'.length) G)
          hdiff (fun k => (Pi.single (L'.get k) (1 : ℝ) : Fin m → ℝ)) (Pi.single i 1)]
    change (((fderiv ℝ (iteratedFDeriv ℝ L'.length G) z) (Pi.single i 1))
        (fun k => (Pi.single (L'.get k) (1 : ℝ) : Fin m → ℝ))) =
      (iteratedFDeriv ℝ (L'.length + 1) G z)
        (fun k => (Pi.single ((i :: L').get k) (1 : ℝ) : Fin m → ℝ))
    rw [iteratedFDeriv_succ_apply_left (f := G) (x := z) (n := L'.length)]
    rfl

/-- Smoothness of a slice from smoothness of the function. -/
lemma hbdd_slice_contDiffAt {n m : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ} {x : ℝ}
    {y : Fin n → ℝ} (h : ContDiffAt ℝ m g (Work.WilkG4c.pt x y)) :
    ContDiffAt ℝ m (Work.WilkG4c.slice g x) y := by
  have hmap : ContDiffAt ℝ m (fun y' : Fin n → ℝ => Work.WilkG4c.pt x y') y := by
    rw [contDiffAt_pi]
    intro i
    induction i using Fin.cases with
    | zero =>
      have he : (fun y' : Fin n → ℝ => (Work.WilkG4c.pt x y') 0) = fun _ => x := by
        funext y'; rw [Work.WilkG4c.pt_zero]
      rw [he]; exact contDiffAt_const
    | succ j =>
      have he : (fun y' : Fin n → ℝ => (Work.WilkG4c.pt x y') j.succ) = fun y' => y' j := by
        funext y'; rw [Work.WilkG4c.pt_succ]
      rw [he]
      exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).contDiff.contDiffAt
  have hf : (fun y' : Fin n → ℝ => g (Work.WilkG4c.pt x y')) = Work.WilkG4c.slice g x := rfl
  rw [← hf]
  exact h.comp y hmap

/-! ## `xcount` bookkeeping -/

lemma hbdd_xcount_cons {n : ℕ} (a : Fin (n + 1)) (L : List (Fin (n + 1))) :
    Work.WilkG4c.xcount (a :: L) = Work.WilkG4c.xcount L + (if a = 0 then 1 else 0) := by
  by_cases h : a = 0
  · simp [Work.WilkG4c.xcount, List.filter_cons, h]
  · simp [Work.WilkG4c.xcount, List.filter_cons, h]

lemma hbdd_xcount_append {n : ℕ} (L₁ L₂ : List (Fin (n + 1))) :
    Work.WilkG4c.xcount (L₁ ++ L₂) = Work.WilkG4c.xcount L₁ + Work.WilkG4c.xcount L₂ := by
  simp [Work.WilkG4c.xcount, List.filter_append]

lemma hbdd_xcount_cons_succ {n : ℕ} (i : Fin n) (L : List (Fin (n + 1))) :
    Work.WilkG4c.xcount (i.succ :: L) = Work.WilkG4c.xcount L := by
  rw [hbdd_xcount_cons]
  have : (i.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero i
  simp [this]

/-! ## The base case (no `x`-directions): the `y`-jet hypothesis `hY` -/

/-- For a list `L` of nonzero `Fin (n+1)`-indices, the corresponding list of `Fin n`-indices:
the entry `i ≠ 0` is sent to `i.pred`, the `y`-coordinate it comes from. -/
def hbdd_stripY : {n : ℕ} → (L : List (Fin (n + 1))) → (∀ i ∈ L, i ≠ 0) → List (Fin n)
  | _, [], _ => []
  | _, (i :: L), h => i.pred (h i (by simp)) :: hbdd_stripY L (fun j hj => h j (by simp [hj]))

lemma hbdd_hbdd_stripY_map_succ {n : ℕ} (L : List (Fin (n + 1))) (h : ∀ i ∈ L, i ≠ 0) :
    (hbdd_stripY L h).map Fin.succ = L := by
  induction L with
  | nil => simp [hbdd_stripY]
  | cons i L ih =>
    have hi : i ≠ 0 := h i (by simp)
    have hL : ∀ j ∈ L, j ≠ 0 := fun j hj => h j (by simp [hj])
    simp only [hbdd_stripY, List.map_cons, ih hL, Fin.succ_pred i hi]

lemma hbdd_hbdd_stripY_length {n : ℕ} (L : List (Fin (n + 1))) (h : ∀ i ∈ L, i ≠ 0) :
    (hbdd_stripY L h).length = L.length := by
  induction L with
  | nil => simp [hbdd_stripY]
  | cons i L ih =>
    have hL : ∀ j ∈ L, j ≠ 0 := fun j hj => h j (by simp [hj])
    simp only [hbdd_stripY, List.length_cons, ih hL]

lemma hbdd_base_bound {n r : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ}
    (hY : ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ y ∈ openCube n,
      ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice g x) y‖ ≤ 1)
    {L : List (Fin (n + 1))} (hne : ∀ i ∈ L, i ≠ 0) (hlen : L.length ≤ r)
    {x : ℝ} (hx : x ∈ Work.WilkG4c.I) {y : Fin n → ℝ} (hyc : y ∈ openCube n)
    (hycd : ContDiffAt ℝ L.length g (Work.WilkG4c.pt x y)) :
    |Work.WilkG4c.iterDir L g (Work.WilkG4c.pt x y)| ≤ 1 := by
  have hML : (hbdd_stripY L hne).map Fin.succ = L := hbdd_hbdd_stripY_map_succ L hne
  have hlen' : (hbdd_stripY L hne).length = L.length := hbdd_hbdd_stripY_length L hne
  have hprod : (∏ k : Fin (hbdd_stripY L hne).length,
      ‖(Pi.single ((hbdd_stripY L hne).get k) (1 : ℝ) : Fin n → ℝ)‖ : ℝ) = 1 := by
    refine Finset.prod_eq_one fun k _ => ?_
    rw [Pi.norm_single, norm_one]
  have hjet := hbdd_iterDir_jet (hbdd_stripY L hne) (Work.WilkG4c.slice g x) y (by
    rw [hlen']; exact hbdd_slice_contDiffAt hycd)
  have htr := iterDir_slice_transport g (hbdd_stripY L hne) x y (by rw [hlen']; exact hycd)
  rw [← hML, htr, hjet]
  calc |iteratedFDeriv ℝ (hbdd_stripY L hne).length (Work.WilkG4c.slice g x) y
        (fun k => (Pi.single ((hbdd_stripY L hne).get k) (1 : ℝ) : Fin n → ℝ))|
      = ‖iteratedFDeriv ℝ (hbdd_stripY L hne).length (Work.WilkG4c.slice g x) y
        (fun k => (Pi.single ((hbdd_stripY L hne).get k) (1 : ℝ) : Fin n → ℝ))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖iteratedFDeriv ℝ (hbdd_stripY L hne).length (Work.WilkG4c.slice g x) y‖ *
        (∏ k : Fin (hbdd_stripY L hne).length,
          ‖(Pi.single ((hbdd_stripY L hne).get k) (1 : ℝ) : Fin n → ℝ)‖) :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ (hbdd_stripY L hne).length (Work.WilkG4c.slice g x) y‖ * 1 := by
        rw [hprod]
    _ = ‖iteratedFDeriv ℝ (hbdd_stripY L hne).length (Work.WilkG4c.slice g x) y‖ := mul_one _
    _ ≤ 1 := by rw [hlen']; exact hY x hx L.length hlen y hyc

/-! ## The main induction -/

/-- The fibre supremum of any order-`≤ r` directional derivative of an `Ω`-definable function of
`n+1` variables (with values in `(0,1)` on the cube and with unit `y`-derivative jets) is finite
outside a finite set of `x`.  This is BNZ's "repeatedly applying Lemma 5.6" (our `hbdd`): for a
derivative whose `x`-order is `k`, apply `hbdd` to `ψ ∘ ∂^{(k-1)e₁+α'}g`, where
`ψ(u) = 1/2 + u/(2*sqrt(1+u^2)) : ℝ → (0,1)` is semialgebraic with `0 < ψ' ≤ 1/2`; the
`y`-partials of that function are `ψ'(∂^{...}g)·∂^{(k-1)e₁+α'+e_j}g`, bounded off a finite set by
the induction hypothesis for `x`-order `k-1`, while a superset of the graph of
`ψ ∘ (extension by 0 of ∂^{(k-1)e₁+α'}g off its `C^{k-1}`-locus)` is `Ω`-bounded by `SharpDeriv`
and `GraphOfComp`. -/
theorem hbdd_sup_finite (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (hbdd : Work.WilkG4c.BddDxHyp S) {n r F D : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ)
    (hΩ : WilkiesDesign.graphOf g ∈ S.Ω F D (n + 1 + 1))
    (hI : ∀ z ∈ WilkiesDesign.openCube (n + 1), g z ∈ Set.Ioo (0 : ℝ) 1)
    (hY : ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ y ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice g x) y‖ ≤ 1) :
    ∀ L : List (Fin (n + 1)), L.length ≤ r →
      ∃ s : Finset ℝ, ∀ x ∈ Work.WilkG4c.I, x ∉ (s : Set ℝ) →
        BddAbove ((fun y => |Work.WilkG4c.iterDir L g (Work.WilkG4c.pt x y)|) ''
          {y : Fin n → ℝ | y ∈ WilkiesDesign.openCube n ∧
            Work.WilkG4c.pt x y ∈ interior {z | ContDiffAt ℝ L.length g z}}) := by
  classical
  obtain ⟨hpsi_deriv, hpsi_Ioo, hdpsi_pos, hdpsi_le, hdpsi_ge, hpsi_fderiv⟩ := psi_facts
  have main : ∀ k : ℕ, ∀ L : List (Fin (n + 1)), xcount L ≤ k → L.length ≤ r →
      ∃ s : Finset ℝ, ∀ x ∈ I, x ∉ (s : Set ℝ) →
        BddAbove ((fun y => |iterDir L g (pt x y)|) ''
          {y : Fin n → ℝ | y ∈ openCube n ∧ ContDiffAt ℝ L.length g (pt x y)}) := by
    intro k
    induction k with
    | zero =>
      intro L hx hlen
      have hne : ∀ i ∈ L, i ≠ 0 := by
        intro i hi hi0
        have hmem : i ∈ L.filter (fun i => decide (i = 0)) := by
          rw [List.mem_filter]
          exact ⟨hi, by simp [hi0]⟩
        have hpos : 0 < (L.filter (fun i => decide (i = 0))).length := List.length_pos_of_mem hmem
        simp only [xcount] at hx
        omega
      refine ⟨∅, fun x hxI _ => ⟨1, ?_⟩⟩
      rintro b ⟨y, hy, rfl⟩
      exact hbdd_base_bound hY hne hlen hxI hy.1 hy.2
    | succ k ih =>
      intro L hx hlen
      by_cases hcase : xcount L ≤ k
      · exact ih L hcase hlen
      · have hxk : xcount L = k + 1 := by omega
        have hmem0 : (0 : Fin (n + 1)) ∈ L := by
          by_contra hcon
          have hfilt : L.filter (fun i => decide (i = 0)) = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro a ha
            rw [List.mem_filter] at ha
            have ha0 : a = 0 := by simpa using ha.2
            exact hcon (ha0 ▸ ha.1)
          simp only [xcount, hfilt, List.length_nil] at hxk
          omega
        obtain ⟨A, B, hAB⟩ := List.mem_iff_append.mp hmem0
        set L' : List (Fin (n + 1)) := A ++ B with hL'def
        have hperm : L.Perm ((0 : Fin (n + 1)) :: L') := by
          rw [hAB, hL'def]; exact List.perm_middle
        have hlen_cons : L.length = L'.length + 1 := by
          have h1 : L.length = A.length + (B.length + 1) := by
            rw [hAB]; simp [List.length_append]
          have h2 : L'.length = A.length + B.length := by rw [hL'def, List.length_append]
          omega
        have hxcount' : xcount L' ≤ k := by
          have h1 : xcount L = xcount A + (xcount B + 1) := by
            rw [hAB, hbdd_xcount_append, hbdd_xcount_cons]; simp
          have h2 : xcount L' = xcount A + xcount B := by rw [hL'def, hbdd_xcount_append]
          omega
        have hIH : ∀ i : Fin n, ∃ s : Finset ℝ, ∀ x ∈ I, x ∉ (s : Set ℝ) →
            BddAbove ((fun y => |iterDir (i.succ :: L') g (pt x y)|) ''
              {y : Fin n → ℝ | y ∈ openCube n ∧ ContDiffAt ℝ L.length g (pt x y)}) := by
          intro i
          have hxc : xcount (i.succ :: L') ≤ k := by
            rw [hbdd_xcount_cons_succ]; exact hxcount'
          have hln : (i.succ :: L').length ≤ r := by
            have he : (i.succ :: L').length = L.length := by
              simp only [List.length_cons]; omega
            rw [he]; exact hlen
          obtain ⟨s, hs⟩ := ih (i.succ :: L') hxc hln
          refine ⟨s, fun x hxI hxs => ?_⟩
          have hord : ((i.succ :: L').length : WithTop ℕ∞) = (L.length : WithTop ℕ∞) := by
            have he : (i.succ :: L').length = L.length := by
              simp only [List.length_cons]; omega
            rw [he]
          have hset : {y : Fin n → ℝ | y ∈ openCube n ∧
                ContDiffAt ℝ ((i.succ :: L').length) g (pt x y)}
              = {y : Fin n → ℝ | y ∈ openCube n ∧ ContDiffAt ℝ L.length g (pt x y)} := by
            ext y
            simp only [Set.mem_setOf_eq]
            rw [hord]
          have hs' := hs x hxI hxs
          rw [hset] at hs'
          exact hs'
        obtain ⟨a, b, hpsiΩ⟩ := hbdd_psi_graph_fb S
        obtain ⟨Fc, Dc, hchiΩ⟩ := graphOf_chi_mem S hder g hΩ L' (m := L.length) (by omega)
        obtain ⟨C₁, C₂, hcomp⟩ := graphOfCompGen S 1 (n + 1)
        have hfΩ : graphOf (fun z : Fin (n + 1) → ℝ => psi (chi g L' L.length z))
            ∈ S.Ω (a + Fc + C₁) (b.eval Dc + 1 * Dc + C₂) (n + 1 + 1) := by
          have h := hcomp a Fc (b.eval Dc) Dc (fun v : Fin 1 → ℝ => psi (v 0))
            (fun z : Fin (n + 1) → ℝ => fun _ : Fin 1 => chi g L' L.length z)
            (hpsiΩ Dc) (fun j => by
              have heq : (fun z : Fin (n + 1) → ℝ =>
                  (fun _ : Fin 1 => chi g L' L.length z) j) = fun z => chi g L' L.length z := by
                funext z; simp
              rw [heq]; exact hchiΩ)
          simpa [Function.comp_def] using h
        have hval : ∀ z ∈ openCube (n + 1),
            (fun z : Fin (n + 1) → ℝ => psi (chi g L' L.length z)) z ∈ Set.Ioo (0 : ℝ) 1 :=
          fun z _ => hpsi_Ioo _
        have hc := chi_ybound L' hlen_cons.symm hpsi_deriv hdpsi_le hIH
        obtain ⟨s_hb, hsb⟩ := hbdd
          (fun z : Fin (n + 1) → ℝ => psi (chi g L' L.length z)) hfΩ hval hc
        have hgoal : ∃ s : Finset ℝ, ∀ x ∈ I, x ∉ (s : Set ℝ) →
            BddAbove ((fun y => |iterDir ((0 : Fin (n + 1)) :: L') g (pt x y)|) ''
              {y : Fin n → ℝ | y ∈ openCube n ∧
                ContDiffAt ℝ ((0 : Fin (n + 1)) :: L').length g (pt x y)}) := by
          obtain ⟨sL, hsL⟩ := ih L' hxcount' (show L'.length ≤ r by omega)
          refine ⟨s_hb ∪ sL, fun x hxI hxs => ?_⟩
          have hx1 : x ∉ (s_hb : Set ℝ) := fun h => hxs (Finset.mem_union.mpr (Or.inl h))
          have hx2 : x ∉ (sL : Set ℝ) := fun h => hxs (Finset.mem_union.mpr (Or.inr h))
          obtain ⟨B, hB⟩ := hsb x hxI hx1
          obtain ⟨C, hC⟩ := hsL x hxI hx2
          refine ⟨B / dpsi (max C 0), ?_⟩
          rintro b ⟨y, hy, rfl⟩
          have hord : ((0 : Fin (n + 1)) :: L').length = L.length := by
            simp only [List.length_cons]; omega
          have hord' : (((0 : Fin (n + 1)) :: L').length : WithTop ℕ∞) = (L.length : WithTop ℕ∞) :=
            by rw [hord]
          have hycd : ContDiffAt ℝ L.length g (pt x y) := by
            rw [← hord']
            exact hy.2
          have hev : (fun z : Fin (n + 1) → ℝ => psi (chi g L' L.length z))
              =ᶠ[𝓝 (pt x y)] (fun z => psi (iterDir L' g z)) := by
            filter_upwards [hycd.eventually (by simp)] with z hz
            simp only [chi_of_contDiffAt g L' L.length hz]
          have hiter : ContDiffAt ℝ 1 (fun z : Fin (n + 1) → ℝ => iterDir L' g z) (pt x y) := by
            refine iterDir_contDiffAt g L' 1 (pt x y) ?_
            have hbase : ContDiffAt ℝ (((L'.length + 1 : ℕ)) : WithTop ℕ∞) g (pt x y) := by
              simpa only [List.length_cons] using hy.2
            have hcast : (((L'.length + 1 : ℕ)) : WithTop ℕ∞)
                = ((L'.length : ℕ) : WithTop ℕ∞) + ((1 : ℕ) : WithTop ℕ∞) :=
              Nat.cast_add _ _
            rw [hcast] at hbase
            exact hbase
          have h1 : ContDiffAt ℝ 1 (fun z : Fin (n + 1) → ℝ => psi (iterDir L' g z)) (pt x y) :=
            (psi_contDiffAt (iterDir L' g (pt x y))).comp (pt x y) hiter
          have hf1 : ContDiffAt ℝ 1 (fun z : Fin (n + 1) → ℝ => psi (chi g L' L.length z))
              (pt x y) := ContDiffAt.congr_of_eventuallyEq h1 hev
          have hloc : pt x y ∈ interior {z | ContDiffAt ℝ 1
              (fun z : Fin (n + 1) → ℝ => psi (chi g L' L.length z)) z} := by
            have hopen : IsOpen {z : Fin (n + 1) → ℝ | ContDiffAt ℝ 1
                (fun z : Fin (n + 1) → ℝ => psi (chi g L' L.length z)) z} := by
              rw [isOpen_iff_mem_nhds]
              intro z hz
              have hz' : ContDiffAt ℝ 1
                  (fun z : Fin (n + 1) → ℝ => psi (chi g L' L.length z)) z := hz
              exact Filter.mem_of_superset (hz'.eventually (by simp)) (fun y hy => hy)
            rw [hopen.interior_eq]
            exact hf1
          have hchi_eq : chi g L' L.length (pt x y) = iterDir L' g (pt x y) :=
            chi_of_contDiffAt g L' L.length hycd
          have hchain : (fderiv ℝ (fun z : Fin (n + 1) → ℝ => psi (chi g L' L.length z))
                (pt x y)) (Pi.single (0 : Fin (n + 1)) 1)
              = deriv psi (chi g L' L.length (pt x y)) *
                ((fderiv ℝ (iterDir L' g) (pt x y)) (Pi.single (0 : Fin (n + 1)) 1)) := by
            rw [hev.fderiv_eq]
            rw [show (fun z : Fin (n + 1) → ℝ => psi (iterDir L' g z))
                = psi ∘ (fun z : Fin (n + 1) → ℝ => iterDir L' g z) from rfl]
            rw [fderiv_comp (x := pt x y) (hpsi_deriv _).differentiableAt
              (hiter.differentiableAt one_ne_zero)]
            rw [ContinuousLinearMap.comp_apply, hpsi_fderiv]
            rw [hchi_eq]
          have hin : y ∈ {y' : Fin n → ℝ | y' ∈ openCube n ∧
                ContDiffAt ℝ (L'.length) g (pt x y')} := by
            refine ⟨hy.1, ?_⟩
            exact hycd.of_le (by exact_mod_cast (by omega : L'.length ≤ L.length))
          have hinb : |iterDir L' g (pt x y)| ≤ max C 0 :=
            le_trans (hC (Set.mem_image_of_mem _ hin)) (le_max_left _ _)
          have hd : dpsi (max C 0) ≤ deriv psi (chi g L' L.length (pt x y)) := by
            rw [hchi_eq, (hpsi_deriv (iterDir L' g (pt x y))).deriv]
            exact hdpsi_ge (max C 0) _ (le_max_right _ _) hinb
          have hbnd : |deriv psi (chi g L' L.length (pt x y)) *
              ((fderiv ℝ (iterDir L' g) (pt x y)) (Pi.single (0 : Fin (n + 1)) 1))| ≤ B := by
            rw [← hchain]
            exact hB y hy.1 hloc
          have hpos : 0 < deriv psi (chi g L' L.length (pt x y)) := by
            rw [hchi_eq, (hpsi_deriv _).deriv]
            exact hdpsi_pos _
          have hXb : |(fderiv ℝ (iterDir L' g) (pt x y)) (Pi.single (0 : Fin (n + 1)) 1)| *
              dpsi (max C 0) ≤ B := by
            refine le_trans (mul_le_mul_of_nonneg_left hd (abs_nonneg _)) ?_
            calc |(fderiv ℝ (iterDir L' g) (pt x y)) (Pi.single (0 : Fin (n + 1)) 1)| *
                  deriv psi (chi g L' L.length (pt x y))
                = |(fderiv ℝ (iterDir L' g) (pt x y)) (Pi.single (0 : Fin (n + 1)) 1) *
                    deriv psi (chi g L' L.length (pt x y))| := by
                  rw [abs_mul, abs_of_pos hpos]
              _ = |deriv psi (chi g L' L.length (pt x y)) *
                    ((fderiv ℝ (iterDir L' g) (pt x y)) (Pi.single (0 : Fin (n + 1)) 1))| := by
                  rw [mul_comm]
              _ ≤ B := hbnd
          show |(fderiv ℝ (iterDir L' g) (pt x y)) (Pi.single (0 : Fin (n + 1)) 1)|
            ≤ B / dpsi (max C 0)
          exact (le_div_iff₀ (hdpsi_pos _)).mpr hXb
        obtain ⟨s0, hs0⟩ := hgoal
        refine ⟨s0, fun x hxI hxs => ?_⟩
        obtain ⟨B, hB⟩ := hs0 x hxI hxs
        refine ⟨B, ?_⟩
        rintro b ⟨y, hy, rfl⟩
        show |iterDir L g (pt x y)| ≤ B
        have hy' : y ∈ openCube n ∧ ContDiffAt ℝ ((0 : Fin (n + 1)) :: L').length g (pt x y) := by
          refine ⟨hy.1, ?_⟩
          rw [show ((0 : Fin (n + 1)) :: L').length = L.length from by
            simp only [List.length_cons]; omega]
          exact hy.2
        have hb := hB ⟨y, hy', rfl⟩
        simp only [] at hb
        rw [show iterDir L g (pt x y) = iterDir ((0 : Fin (n + 1)) :: L') g (pt x y) from
          iterDir_perm g hperm (pt x y) hy.2]
        exact hb
  intro L hL
  obtain ⟨s, hs⟩ := main r L (le_trans (xcount_le_length L) hL) hL
  refine ⟨s, fun x hxI hxs => ?_⟩
  have himg : ((fun y => |iterDir L g (pt x y)|) ''
        {y : Fin n → ℝ | y ∈ openCube n ∧ pt x y ∈ interior {z | ContDiffAt ℝ L.length g z}})
      = ((fun y => |iterDir L g (pt x y)|) ''
        {y : Fin n → ℝ | y ∈ openCube n ∧ ContDiffAt ℝ L.length g (pt x y)}) := by
    congr 1
    ext y
    simp only [Set.mem_setOf_eq]
    rw [hbdd_mem_interior_locus_nat L.length g (pt x y)]
  rw [himg]
  exact hs x hxI hxs

end Work.WilG4c
