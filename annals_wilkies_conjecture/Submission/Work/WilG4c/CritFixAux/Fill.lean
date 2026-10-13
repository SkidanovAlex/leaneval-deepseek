/-
  WilG4c / `CritFixAux.Fill` — the puncture-filling half of `Work.WilkG4c.CritFixGoodMem`:
  on `AlGood`, the corrected criterion implies that the fibre really is `C^{|L|}` and stores its
  `|L|`-th derivative along `L`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.CritFixDefs
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.JBadMem
import Submission.Work.WilG4c.DensePunctureCriterion
import Submission.Work.WilG4c.CritFixAux.Pre

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilkG4c

open WilkiesDesign

/-- **The value condition, read off.**  A `LimeqP`-membership at the point `(w, s)` unfolded into
the `ε`-`δ` statement with the `Fin.snoc`/`Fin.init` bookkeeping removed. -/
theorem limeqP_apply {p n : ℕ} {A : Set (Fin (p + (n + 1) + 1) → ℝ)}
    {w : Fin (p + (n + 1)) → ℝ} {s : ℝ}
    (hw : (Fin.snoc w s : Fin (p + (n + 1) + 1) → ℝ) ∈ Work.WilG4c.LimeqP p n A) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x : Fin (n + 1) → ℝ, x ≠ cubePt w →
      (∀ j : Fin (n + 1), |x j - cubePt w j| < δ) → ∀ v : ℝ,
      (Fin.snoc (Fin.append (parPt w) x) v : Fin (p + (n + 1) + 1) → ℝ) ∈ A →
      |v - s| ≤ ε := by
  have h := hw
  rw [Work.WilG4c.LimeqP] at h
  have hinit : Fin.init (Fin.snoc w s : Fin (p + (n + 1) + 1) → ℝ) = w :=
    init_snoc_real w s
  have hlast : (Fin.snoc w s : Fin (p + (n + 1) + 1) → ℝ) (Fin.last (p + (n + 1))) = s :=
    snoc_last_real w s
  simpa only [Set.mem_ofPred_eq, hinit, hlast] using h

/-! ## 5. The puncture-filling direction -/

/-- The fibre bad set `{x | (l,x) ∈ jBad p n f k}` is thin on `AlGood`: its complement is dense in
the cube (`AlGood_dense`). -/
theorem interior_fibreJBad_eq_empty {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    {z : Fin (p + (n + 1) + 1) → ℝ} (hz : z ∈ AlGood p n f L) {k : ℕ} (hk : k ≤ L.length) :
    interior {x : Fin (n + 1) → ℝ | fibPt (Fin.init z) x ∈ jBad p n f k} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x₀ hx₀
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx₀)
  obtain ⟨y, hy, hygood⟩ := Work.WilkG4c.AlGood_dense f L hz hk x₀ hε
  have hbady : fibPt (Fin.init z) y ∈ jBad p n f k :=
    hball (by rw [Metric.mem_ball]; exact hy)
  rw [jBad, Set.mem_compl_iff] at hbady
  exact hbady hygood

/-- The fibre bad set `{x | Fin.append l x ∈ jBad p n f k}` is closed: it is the preimage of the
closed set `jBad` under the continuous inclusion `x ↦ Fin.append l x`. -/
theorem isClosed_fibreJBad {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (k : ℕ) (l : Fin p → ℝ) :
    IsClosed {x : Fin (n + 1) → ℝ | Fin.append l x ∈ jBad p n f k} := by
  have hcont : Continuous fun x : Fin (n + 1) → ℝ => Fin.append l x := by
    refine continuous_pi fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
    · simp only [Fin.append_left]
      exact continuous_const
    · simp only [Fin.append_right]
      exact continuous_apply j'
  refine IsClosed.preimage hcont ?_
  rw [jBad]
  exact isClosed_compl_iff.mpr isOpen_interior

/-- **The puncture-filling direction.**  On `AlGood`, the corrected criterion implies that the
fibre really is `C^{|L|}` and stores its `|L|`-th derivative along `L`. -/
theorem critFix_inter_AlGood_subset {p n : ℕ} (S : WilkiesDesign.SOMin)
    (hcd : WilkiesDesign.SOMin.SharpCD S) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (F0 D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    (hf : WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1)) :
    CritFix p n f L ∩ AlGood p n f L ⊆ AlDgListSlice p n f L := by
  rintro z ⟨hzCrit, hzGood⟩
  rw [mem_CritFix_iff] at hzCrit
  obtain ⟨hzLoc, hzLimeq⟩ := hzCrit
  obtain ⟨ρ, hρpos, hρUV⟩ := hzLoc
  -- the fibre bad set over the parameter of `z`
  have hAmem : ∃ (F D' : ℕ),
      {x : Fin (n + 1) → ℝ | Fin.append (parPt (Fin.init z)) x ∈ jBad p n f L.length}
        ∈ S.Ω F D' (n + 1) :=
    fibreJBad_mem S hder p n F0 D L.length f (parPt (Fin.init z)) hf
  obtain ⟨FA, DA, hAmem⟩ := hAmem
  obtain ⟨K, pdeg, hK⟩ := Work.WilG4b.projCoords_mem (S := S) (m := p + (n + 1)) (N := n + 1)
    (Fin.natAdd p)
  -- thinness from `AlGood`
  have hAthin : interior {x : Fin (n + 1) → ℝ | Fin.append (parPt (Fin.init z)) x ∈ jBad p n f L.length}
      = ∅ := by
    have h := interior_fibreJBad_eq_empty f L hzGood (le_refl L.length)
    have hfib : ∀ x : Fin (n + 1) → ℝ,
        fibPt (Fin.init z) x = Fin.append (parPt (Fin.init z)) x := fun x => rfl
    simpa only [hfib] using h
  have hAclosed : IsClosed {x : Fin (n + 1) → ℝ |
      Fin.append (parPt (Fin.init z)) x ∈ jBad p n f L.length} :=
    isClosed_fibreJBad f L.length (parPt (Fin.init z))
  -- continuity of the fibre on the ball
  have hcont : ContinuousOn (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
      (Metric.ball (cubePt (Fin.init z)) ρ) := by
    intro x hx
    have hw' : Fin.append (parPt (Fin.init z)) x ∈ UVFix p n f L.length :=
      hρUV (Fin.append (parPt (Fin.init z)) x) (parPt_append' _ x) (by
        simpa only [cubePt_append', Metric.mem_ball] using hx)
    have hcs : Fin.append (parPt (Fin.init z)) x ∈ contSet p n f := hw'.1
    have hct := (mem_contSet_iff f (Fin.append (parPt (Fin.init z)) x)).mp hcs
    simpa only [parPt_append', cubePt_append'] using hct.continuousWithinAt
  -- the fibre is `C^{|L|}` off the bad set
  have hsm : ∀ x ∈ Metric.ball (cubePt (Fin.init z)) ρ,
      x ∉ {x : Fin (n + 1) → ℝ | Fin.append (parPt (Fin.init z)) x ∈ jBad p n f L.length} →
      ContDiffAt ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) x := by
    intro x hx hxA
    have hxjloc : Fin.append (parPt (Fin.init z)) x ∈ jLoc p n f L.length := by
      by_contra hh
      exact hxA (show Fin.append (parPt (Fin.init z)) x ∈ jBad p n f L.length from by
        rw [jBad, Set.mem_compl_iff]; exact hh)
    have hz' : Fin.init (Fin.snoc (Fin.append (parPt (Fin.init z)) x) (0 : ℝ)
          : Fin (p + (n + 1) + 1) → ℝ)
        ∈ interior {w | ContDiffAt ℝ L.length (famFunHat f) w} := by
      rw [Fin.init_snoc]
      have hcl : ContDiffAt ℝ L.length (famFunHat f) (Fin.append (parPt (Fin.init z)) x) :=
        interior_subset hxjloc
      exact mem_interior_iff_mem_nhds.mpr (hcl.eventually (by simp))
    have hres := (Work.WilG4c.SliceDerivJointSubset f L
      (Fin.snoc (Fin.append (parPt (Fin.init z)) x) (0 : ℝ) : Fin (p + (n + 1) + 1) → ℝ) hz').1
    simpa only [Fin.init_snoc, parPt_append', cubePt_append'] using hres
  -- the limit conditions
  have hlim : ∀ y ∈ Metric.ball (cubePt (Fin.init z)) ρ, ∀ m, 1 ≤ m → m ≤ L.length →
      ∀ c : Fin (n + 1) → Fin (m + 1),
      ∃ s : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Metric.ball (cubePt (Fin.init z)) ρ →
        x ∉ {x : Fin (n + 1) → ℝ | Fin.append (parPt (Fin.init z)) x ∈ jBad p n f L.length} →
        x ≠ y → dist x y < δ →
        |iteratedFDeriv ℝ m (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) x
          (fun i => Pi.single (cntWord n m (fun j => (c j).val) i) 1) - s| < ε := by
    intro y hy m hm1 hmk c
    -- the counts as an element of the `critIdxFix` type
    set c' : Fin (n + 1) → Fin ((m - 1) + 2) :=
      fun j => ⟨(c j).val, by have := (c j).isLt; omega⟩ with hc'def
    have hc'val : ∀ j : Fin (n + 1), (c' j).val = (c j).val := fun j => rfl
    have hord : (⟨m - 1, by omega⟩ : Fin L.length).val + 1 = m := by
      simp only [Fin.val_mk]; omega
    -- the criterion holds at the point `(l, y)`
    have hw' : Fin.append (parPt (Fin.init z)) y ∈ UVFix p n f L.length :=
      hρUV (Fin.append (parPt (Fin.init z)) y) (parPt_append' _ y) (by
        simpa only [cubePt_append', Metric.mem_ball] using hy)
    rw [UVFix, Set.mem_inter_iff] at hw'
    obtain ⟨-, hlimcond⟩ := hw'
    have hi : (⟨⟨m - 1, by omega⟩, c'⟩ :
        Σ m' : Fin L.length, Fin (n + 1) → Fin (m'.val + 2)) ∈ critIdxFix n L.length := by
      simp [critIdxFix]
    have hLC : Fin.append (parPt (Fin.init z)) y ∈
        LimCond p n f ((⟨m - 1, by omega⟩ : Fin L.length).val + 1) (fun j => (c' j).val) := by
      rw [Set.mem_iInter₂] at hlimcond
      exact hlimcond ⟨⟨m - 1, by omega⟩, c'⟩ hi
    rw [LimCond, ProjLim, WilkiesDesign.projLast, Set.mem_ofPred_eq] at hLC
    obtain ⟨s, hs⟩ := hLC
    have hs' := limeqP_apply (p := p) (n := n)
      (A := dgSet p n f ((⟨m - 1, by omega⟩ : Fin L.length).val + 1)
        (cntWord n ((⟨m - 1, by omega⟩ : Fin L.length).val + 1) (fun j => (c' j).val)))
      (w := Fin.append (parPt (Fin.init z)) y) (s := s) hs
    rw [parPt_append' (parPt (Fin.init z)) y, cubePt_append' (parPt (Fin.init z)) y] at hs'
    refine ⟨s, fun ε hε => ?_⟩
    obtain ⟨δ, hδpos, hδ⟩ := hs' (ε / 2) (by linarith)
    refine ⟨δ, hδpos, fun x hxball hxA hxy hxd => ?_⟩
    -- the point `x` is joint-good, hence joint `C^m`
    have hxk : Fin.append (parPt (Fin.init z)) x ∈ jLoc p n f L.length := by
      by_contra hh
      exact hxA (show Fin.append (parPt (Fin.init z)) x ∈ jBad p n f L.length from by
        simp only [jBad, Set.mem_compl_iff]
        exact hh)
    have hxint : Fin.append (parPt (Fin.init z)) x ∈
        interior {w | ContDiffAt ℝ L.length (famFunHat f) w} := hxk
    have hxm : Fin.append (parPt (Fin.init z)) x ∈
        interior {w | ContDiffAt ℝ ((⟨m - 1, by omega⟩ : Fin L.length).val + 1)
          (famFunHat f) w} := by
      refine interior_mono ?_ hxint
      intro w hw
      show ContDiffAt ℝ (((⟨m - 1, by omega⟩ : Fin L.length).val + 1 : ℕ) : WithTop ℕ∞)
        (famFunHat f) w
      exact (show ContDiffAt ℝ ((L.length : ℕ) : WithTop ℕ∞) (famFunHat f) w from hw).of_le
        (by exact_mod_cast (show (⟨m - 1, by omega⟩ : Fin L.length).val + 1 ≤ L.length by omega))
    have hjoint : ContDiffAt ℝ ((⟨m - 1, by omega⟩ : Fin L.length).val + 1) (famFunHat f)
        (Fin.append (parPt (Fin.init z)) x) :=
      interior_subset hxm
    -- the `dgSet`-point carried by the joint derivative at `x`
    have hcomp : ∀ j : Fin (n + 1), |x j - y j| < δ := by
      intro j
      rw [← Real.dist_eq]
      exact (dist_pi_lt_iff hδpos).mp hxd j
    have hdg : (Fin.snoc (Fin.append (parPt (Fin.init z)) x)
          (iteratedFDeriv ℝ ((⟨m - 1, by omega⟩ : Fin L.length).val + 1) (famFunHat f)
            (Fin.append (parPt (Fin.init z)) x)
            (fun i => Pi.single (Fin.natAdd p
              (cntWord n ((⟨m - 1, by omega⟩ : Fin L.length).val + 1)
                (fun j => (c' j).val) i)) 1))
          : Fin (p + (n + 1) + 1) → ℝ)
        ∈ dgSet p n f ((⟨m - 1, by omega⟩ : Fin L.length).val + 1)
            (cntWord n ((⟨m - 1, by omega⟩ : Fin L.length).val + 1)
              (fun j => (c' j).val)) := by
      rw [mem_dgSet]
      refine ⟨?_, ?_⟩
      · rw [Fin.init_snoc]
        exact hxm
      · simp only [Fin.snoc_last, init_snoc_real]
    have hbd := hδ x hxy hcomp
      (iteratedFDeriv ℝ ((⟨m - 1, by omega⟩ : Fin L.length).val + 1) (famFunHat f)
        (Fin.append (parPt (Fin.init z)) x)
        (fun i => Pi.single (Fin.natAdd p
          (cntWord n ((⟨m - 1, by omega⟩ : Fin L.length).val + 1)
            (fun j => (c' j).val) i)) 1)) hdg
    -- the joint value at `x` is the fibre value there
    have hbridge := jointDeriv_eq_fibreDeriv f (parPt (Fin.init z)) x
      (cntWord n ((⟨m - 1, by omega⟩ : Fin L.length).val + 1) (fun j => (c' j).val)) hjoint
    have hfin : iteratedFDeriv ℝ m (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) x
        (fun i => Pi.single (cntWord n m (fun j => (c j).val) i) 1)
        = iteratedFDeriv ℝ ((⟨m - 1, by omega⟩ : Fin L.length).val + 1) (famFunHat f)
            (Fin.append (parPt (Fin.init z)) x)
            (fun i => Pi.single (Fin.natAdd p
              (cntWord n ((⟨m - 1, by omega⟩ : Fin L.length).val + 1)
                (fun j => (c' j).val) i)) 1) := by
      rw [hbridge]
      refine iteratedFDeriv_congr_index hord.symm
        (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) x
        (fun i => Pi.single (cntWord n m (fun j => (c j).val) i) 1)
        (fun i => Pi.single (cntWord n ((⟨m - 1, by omega⟩ : Fin L.length).val + 1)
          (fun j => (c' j).val) i) 1) ?_
      intro i
      congr 1
    rw [hfin]
    linarith [abs_le.mp hbd]
  -- the analytic criterion gives `C^{|L|}` at the centre
  have hCk : ContDiffAt ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
      (cubePt (Fin.init z)) :=
    Work.WilkG4c.DensePunctureCriterion S hcd (A := {x : Fin (n + 1) → ℝ |
        Fin.append (parPt (Fin.init z)) x ∈ jBad p n f L.length}) (F := FA) (D := DA)
      hρpos hAmem hAthin hAclosed hcont hsm hlim
  refine ⟨hCk, ?_⟩
  -- the stored value is the fibre's `|L|`-th derivative along `L`
  have hvaleq : z (Fin.last (p + (n + 1))) = iteratedFDeriv ℝ L.length
      (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) (cubePt (Fin.init z))
      (fun j => Pi.single (L.get j) 1) := by
    by_contra hne
    set A : ℝ := |z (Fin.last (p + (n + 1))) - iteratedFDeriv ℝ L.length
      (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) (cubePt (Fin.init z))
      (fun j => Pi.single (L.get j) 1)| with hA
    have hApos : 0 < A := abs_pos.mpr (sub_ne_zero.mpr hne)
    -- the value condition: the joint `|L|`-th derivative tends to `z`'s last coordinate
    have hδex : ∃ δ : ℝ, 0 < δ ∧ ∀ x : Fin (n + 1) → ℝ, x ≠ cubePt (Fin.init z) →
        (∀ j : Fin (n + 1), |x j - cubePt (Fin.init z) j| < δ) → ∀ v : ℝ,
        (Fin.snoc (Fin.append (parPt (Fin.init z)) x) v : Fin (p + (n + 1) + 1) → ℝ)
          ∈ dgSet p n f L.length (fun j => L.get j) → |v - z (Fin.last (p + (n + 1)))| ≤ A / 4 := by
      have h := hzLimeq
      rw [Work.WilG4c.LimeqP] at h
      exact h (A / 4) (by linarith)
    obtain ⟨δ, hδpos, hδ⟩ := hδex
    -- continuity of the stored fibre derivative at the centre
    obtain ⟨η, hηpos, hη⟩ : ∃ η : ℝ, 0 < η ∧ ∀ y : Fin (n + 1) → ℝ,
        dist y (cubePt (Fin.init z)) < η →
        |iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y
            (fun j => Pi.single (L.get j) 1)
          - iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
            (cubePt (Fin.init z)) (fun j => Pi.single (L.get j) 1)| < A / 4 := by
      have hc := hCk.continuousAt_iteratedFDeriv (k := L.length) le_rfl
      -- continuity of the evaluated iterated derivative
      have hce : ContinuousAt (fun y : Fin (n + 1) → ℝ =>
          iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y
            (fun j => Pi.single (L.get j) 1)) (cubePt (Fin.init z)) := by
        set v : Fin L.length → (Fin (n + 1) → ℝ) :=
          fun j => (Pi.single (L.get j) (1 : ℝ) : Fin (n + 1) → ℝ) with hv
        rw [Metric.continuousAt_iff] at hc ⊢
        intro ε hε
        have hC : (0 : ℝ) ≤ ∏ i : Fin L.length, ‖v i‖ :=
          Finset.prod_nonneg fun i _ => norm_nonneg _
        have hpos : 0 < ∏ i : Fin L.length, ‖v i‖ + 1 := by linarith
        obtain ⟨δ', hδ'pos, hδ'⟩ := hc (ε / (∏ i : Fin L.length, ‖v i‖ + 1)) (by positivity)
        refine ⟨δ', hδ'pos, fun y hy => ?_⟩
        have h1 : ‖iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y
            - iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
              (cubePt (Fin.init z))‖ < ε / (∏ i : Fin L.length, ‖v i‖ + 1) := by
          simpa [dist_eq_norm] using hδ' hy
        have hb := ContinuousMultilinearMap.le_opNorm
          (iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y
            - iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
              (cubePt (Fin.init z))) v
        have h2 : ‖iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y v
            - iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
              (cubePt (Fin.init z)) v‖
            ≤ ‖iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y
              - iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
                (cubePt (Fin.init z))‖ * ∏ i : Fin L.length, ‖v i‖ := by
          rw [sub_apply] at hb; exact hb
        rw [dist_eq_norm]
        calc ‖iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y v
              - iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
                (cubePt (Fin.init z)) v‖
            ≤ ‖iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y
              - iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
                (cubePt (Fin.init z))‖ * (∏ i : Fin L.length, ‖v i‖) := h2
          _ ≤ ‖iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y
              - iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
                (cubePt (Fin.init z))‖ * (∏ i : Fin L.length, ‖v i‖ + 1) := by
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); linarith
          _ < (ε / (∏ i : Fin L.length, ‖v i‖ + 1)) * (∏ i : Fin L.length, ‖v i‖ + 1) :=
              mul_lt_mul_of_pos_right h1 hpos
          _ = ε := by field_simp
      rw [Metric.continuousAt_iff] at hce
      obtain ⟨η, hηpos, hη⟩ := hce (A / 4) (by linarith)
      exact ⟨η, hηpos, fun y hy => by simpa [Real.dist_eq] using hη hy⟩
    -- a joint-good point close to the centre
    -- a joint-good point close to, but different from, the centre
    set e : Fin (n + 1) → ℝ := Pi.single ⟨0, Nat.succ_pos n⟩ 1 with he
    set rr : ℝ := min δ η with hrr
    have hrpos : 0 < rr := lt_min hδpos hηpos
    set cc : Fin (n + 1) → ℝ := cubePt (Fin.init z) with hcc
    obtain ⟨y₀, hy₀, hy₀good⟩ := Work.WilkG4c.AlGood_dense f L hzGood (le_refl L.length)
      (cc + (rr / 4) • e) (ε := rr / 8) (by linarith [hrpos])
    have he1 : ‖e‖ = 1 := by simp [he, Pi.norm_single]
    have hcent : dist (cc + (rr / 4) • e) cc = rr / 4 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, he1, mul_one,
        abs_of_pos (by linarith)]
    have hy₀ne : y₀ ≠ cc := by
      intro hc'
      have h1 : dist cc (cc + (rr / 4) • e) < rr / 8 := by rw [hc'] at hy₀; exact hy₀
      have h2 : rr / 4 ≤ dist cc (cc + (rr / 4) • e) := by
        rw [dist_comm]
        exact le_of_eq hcent.symm
      linarith
    have hy₀r : dist y₀ cc < rr := by
      have h1 : dist y₀ cc ≤ dist y₀ (cc + (rr / 4) • e) + dist (cc + (rr / 4) • e) cc :=
        dist_triangle _ _ _
      rw [hcent] at h1
      have h2 : dist y₀ (cc + (rr / 4) • e) < rr / 8 := hy₀
      linarith
    have hy₀δ : dist y₀ cc < δ := lt_of_lt_of_le hy₀r (min_le_left _ _)
    have hy₀η : dist y₀ cc < η := lt_of_lt_of_le hy₀r (min_le_right _ _)
    have hcomp : ∀ j : Fin (n + 1), |y₀ j - cc j| < δ := fun j => by
      rw [← Real.dist_eq]
      exact (dist_pi_lt_iff hδpos).mp hy₀δ j
    have hne' : y₀ ≠ cc := hy₀ne
    have hyloc : Fin.append (parPt (Fin.init z)) y₀ ∈ jLoc p n f L.length := by
      simpa only [fibPt] using hy₀good
    have hdg : (Fin.snoc (Fin.append (parPt (Fin.init z)) y₀)
          (iteratedFDeriv ℝ L.length (famFunHat f) (Fin.append (parPt (Fin.init z)) y₀)
            (fun j => Pi.single (Fin.natAdd p (L.get j)) 1))
          : Fin (p + (n + 1) + 1) → ℝ)
        ∈ dgSet p n f L.length (fun j => L.get j) := by
      rw [mem_dgSet]
      refine ⟨?_, ?_⟩
      · simpa only [Fin.init_snoc] using hyloc
      · simp only [Fin.snoc_last, init_snoc_real]
    have hbd := hδ y₀ (by rw [hcc]; exact hne') (by rw [hcc]; exact hcomp) _ hdg
    have hbridge := jointDeriv_eq_fibreDeriv f (parPt (Fin.init z)) y₀
      (fun j : Fin L.length => L.get j) (interior_subset hyloc)
    rw [hbridge] at hbd
    -- combine the two bounds
    have hterm := hη y₀ (by rw [hcc]; exact hy₀η)
    have htri : A ≤ |z (Fin.last (p + (n + 1))) - iteratedFDeriv ℝ L.length
          (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y₀ (fun j => Pi.single (L.get j) 1)|
        + |iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y₀
            (fun j => Pi.single (L.get j) 1) - iteratedFDeriv ℝ L.length
          (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) (cubePt (Fin.init z))
          (fun j => Pi.single (L.get j) 1)| := by
      rw [hA]
      calc |z (Fin.last (p + (n + 1))) - iteratedFDeriv ℝ L.length
            (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) (cubePt (Fin.init z))
            (fun j => Pi.single (L.get j) 1)|
          = |(z (Fin.last (p + (n + 1))) - iteratedFDeriv ℝ L.length
                (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y₀
                (fun j => Pi.single (L.get j) 1))
              + (iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y₀
                (fun j => Pi.single (L.get j) 1) - iteratedFDeriv ℝ L.length
                (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) (cubePt (Fin.init z))
                (fun j => Pi.single (L.get j) 1))| := by
            rw [sub_eq_add_neg]; ring_nf
        _ ≤ _ := abs_add_le _ _
    have hfirst : |z (Fin.last (p + (n + 1))) - iteratedFDeriv ℝ L.length
          (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y₀ (fun j => Pi.single (L.get j) 1)|
        ≤ A / 4 := by
      rw [abs_sub_comm]
      exact hbd
    linarith [hterm, htri, hfirst]
  exact hvaleq

end Work.WilkG4c
