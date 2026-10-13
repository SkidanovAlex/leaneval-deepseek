/-
  WilG4c — the fibre-supremum lemma for `Ω`-definable functions **without** the
  value hypothesis `g ∈ (0,1)` on the cube.

  `Work.WilkG4c.hbdd_sup_finite` (imported here) proves the same conclusion under the extra
  hypothesis `hI : ∀ z ∈ openCube (n+1), g z ∈ Ioo 0 1`.  That hypothesis is *never used* in
  its proof: the only function the area hypothesis `hbdd` (`BddDxHyp`) is ever applied to is
  `ψ ∘ chi`, whose values lie in `(0,1)` because `0 < ψ < 1` automatically (this is what the
  local `hval` provides, from `psi_facts`).  Consequently the same induction — on the number
  `xcount L` of `x`-directions of `L`, with base case `hY` for the pure `y`-directions and the
  `hbdd` step for `ψ ∘ chi`, exactly as in BNZ's proof of Lemma 5.6 — yields the lemma without
  `hI`.  We reproduce that proof here, with the `hI` hypothesis dropped.

  The lemma is what the higher-step reductions need: there the `Ω`-definable function whose
  fibre-suprema must be finite is only known to be unit-bounded on the cube (via `hY`), not to
  take values in `(0,1)`.
-/
import Mathlib
import Submission.Work.WilG4c.hbdd_sup_finite

set_option autoImplicit false
noncomputable section
open Classical

open scoped Topology

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

namespace Work.WilG4c

/-! ## The lemma -/

/-- The fibre supremum of any order-`≤ r` directional derivative of an `Ω`-definable function
of `n+1` variables whose slices have unit `y`-derivative jets up to order `r` is finite outside
a finite set of `x`.  This is `hbdd_sup_finite` with the value hypothesis `g ∈ (0,1)` removed. -/
theorem BddSupFiniteNoI (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (hbdd : Work.WilkG4c.BddDxHyp S) {n r F D : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ)
    (hΩ : WilkiesDesign.graphOf g ∈ S.Ω F D (n + 1 + 1))
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
