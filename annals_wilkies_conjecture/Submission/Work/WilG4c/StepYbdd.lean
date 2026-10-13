/-
  WilG4c / StepYbdd — BNZ §5.2, the reduction to bounded `y`-derivatives.

  Main theorem; the auxiliary `Ω`-machinery (clamping, regrouping, composition of
  `famGraph`s, polynomial bookkeeping) lives in the sibling module `YbddAux`.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.phiPtCoordGraph
import Submission.Work.WilG4c.clampFamGraph
import Submission.Work.WilG4c.vieClampGraph

set_option autoImplicit false

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1
open scoped BigOperators Topology

noncomputable section
open Classical

/-! ## 6. The three Ω-machinery inputs live in sibling modules -/

/-! ## 7. The reduction -/
/-- **BNZ §5.2 — reduction to bounded `y`-derivatives.** -/
theorem StepYbdd (S : SOMin) (n p : ℕ) (hn : 1 ≤ n) (ih : ∀ q, FLem S q n)
    (hP0 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PY p n)) :
    FLem S p (n + 1) := by
  classical
  obtain ⟨acl, ccl, hClamp⟩ := Work.WilG4c.vieClampGraph S p n
  obtain ⟨aclf, cclf, hClampF⟩ := Work.WilG4c.clampFamGraph S p (n + 1)
  obtain ⟨aphi, cphi, hPhi⟩ := Work.WilG4c.phiPtCoordGraph S p n
  obtain ⟨acomp, ccomp, hComp⟩ := famGraph_comp_single S p (n + 1)
  have hihC := (FLemP_iff S (p + 1) n (fun _ _ _ => True)).mp
    ((FLemP_true_iff S (p + 1) n).mpr (ih (p + 1)))
  have hP0C := (FLemP_iff S p (n + 1) (PY p n)).mp hP0
  intro F0
  obtain ⟨a₁, b₁, c₁, hih⟩ := hihC (F0 + acl)
  obtain ⟨aG, bG, cG, hhP0⟩ := hP0C ((F0 + aclf) + (a₁ + aphi) + acomp)
  -- degree bookkeeping
  set b1s : MvPolynomial (Fin 2) ℕ := MvPolynomial.eval₂ MvPolynomial.C
    (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 + MvPolynomial.C ccl
      else MvPolynomial.X 1) b₁ with hb1s
  set bDg : MvPolynomial (Fin 2) ℕ := MvPolynomial.X 0 + MvPolynomial.C cclf
    + MvPolynomial.C (p + (n + 1)) * (b1s + MvPolynomial.C cphi) + MvPolynomial.C ccomp with hbDg
  set bGs : MvPolynomial (Fin 2) ℕ := MvPolynomial.eval₂ MvPolynomial.C
    (fun i : Fin 2 => if i = 0 then bDg else MvPolynomial.X 1) bG with hbGs
  set bfin : MvPolynomial (Fin 2) ℕ := b1s + MvPolynomial.C cphi
    + MvPolynomial.C (p + (n + 1)) * bGs + MvPolynomial.C ccomp with hbfin
  set h24 : Fin 2 → Fin 4 := fun i => ⟨i.val, by omega⟩ with hh24
  set bDgR : MvPolynomial (Fin 4) ℝ :=
    MvPolynomial.map (Nat.castRingHom ℝ) (MvPolynomial.rename h24 bDg) with hbDgR
  set cfin : MvPolynomial (Fin 4) ℝ :=
    MvPolynomial.eval₂ MvPolynomial.C
      (fun i : Fin 4 => if i = 0 then MvPolynomial.X 0 + MvPolynomial.C ((ccl : ℕ) : ℝ)
        else if i = 3 then MvPolynomial.X 3 + MvPolynomial.C (Real.log 2)
        else MvPolynomial.X i) c₁
    * MvPolynomial.eval₂ MvPolynomial.C
      (fun i : Fin 4 => if i = 0 then bDgR
        else if i = 3 then MvPolynomial.X 3 + MvPolynomial.C (Real.log 2)
        else MvPolynomial.X i) cG with hcfin
  refine ⟨(a₁ + aphi) + aG + acomp, bfin, cfin, ?_⟩
  intro D r k ε hε hε1 Λ F hΩ hval
  set Λ'' : Set (Fin (p + 1) → ℝ) := {w | w (Fin.last p) ∈ I} with hΛ''
  set Dg : ℕ := (D + cclf) + (p + (n + 1)) * (MvPolynomial.eval ![D + ccl, r] b₁ + cphi)
    + ccomp with hDg
  have eval_b1s : MvPolynomial.eval ![D, r] b1s = MvPolynomial.eval ![D + ccl, r] b₁ := by
    rw [hb1s, eval_eval₂_C_nat]
    have hfun : (fun i : Fin 2 => MvPolynomial.eval ![D, r]
        (if i = 0 then MvPolynomial.X 0 + MvPolynomial.C ccl else MvPolynomial.X 1))
        = ![D + ccl, r] := by
      funext i
      fin_cases i <;> simp
    rw [hfun]
  have eval_bDg : MvPolynomial.eval ![D, r] bDg = Dg := by
    rw [hbDg, hDg]
    simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C, eval_b1s]
  have eval_bGs : MvPolynomial.eval ![D, r] bGs = MvPolynomial.eval ![Dg, r] bG := by
    rw [hbGs, eval_eval₂_C_nat]
    have hfun : (fun i : Fin 2 => MvPolynomial.eval ![D, r]
        (if i = 0 then bDg else MvPolynomial.X 1)) = ![Dg, r] := by
      funext i
      fin_cases i <;> simp [eval_bDg]
    rw [hfun]
  have eval_bfin : MvPolynomial.eval ![D, r] bfin
      = (MvPolynomial.eval ![D + ccl, r] b₁ + cphi)
        + (p + (n + 1)) * MvPolynomial.eval ![Dg, r] bG + ccomp := by
    rw [hbfin]
    simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C, eval_b1s, eval_bGs]
  have eval_bDgR : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] bDgR
      = (Dg : ℝ) := by
    rw [hbDgR, MvPolynomial.eval_map, MvPolynomial.eval₂_rename]
    change MvPolynomial.eval₂ (Nat.castRingHom ℝ)
      (fun i : Fin 2 => ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] (h24 i)) bDg = (Dg : ℝ)
    have hv : (fun i : Fin 2 => ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] (h24 i))
        = fun i => ((![D, r] i : ℕ) : ℝ) := by
      funext i
      fin_cases i <;> simp [h24]
    rw [hv, eval₂_natCast_comp, eval_bDg]
  have eval_cfin : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cfin
      = MvPolynomial.eval ![(D : ℝ) + (ccl : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c₁
        * MvPolynomial.eval ![(Dg : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] cG := by
    rw [hcfin, MvPolynomial.eval_mul]
    congr 1
    · rw [eval_eval₂_C_real]
      have hfun : (fun i : Fin 4 => MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
          (if i = 0 then MvPolynomial.X 0 + MvPolynomial.C ((ccl : ℕ) : ℝ)
            else if i = 3 then MvPolynomial.X 3 + MvPolynomial.C (Real.log 2)
            else MvPolynomial.X i))
          = ![(D : ℝ) + (ccl : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] := by
        funext i
        fin_cases i <;>
          simp [Real.log_div hε.ne' (by norm_num : (2 : ℝ) ≠ 0)] <;> ring
      rw [hfun]
    · rw [eval_eval₂_C_real]
      have hfun : (fun i : Fin 4 => MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
          (if i = 0 then bDgR
            else if i = 3 then MvPolynomial.X 3 + MvPolynomial.C (Real.log 2)
            else MvPolynomial.X i))
          = ![(Dg : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] := by
        funext i
        fin_cases i <;>
          simp [eval_bDgR, Real.log_div hε.ne' (by norm_num : (2 : ℝ) ≠ 0)] <;> ring
      rw [hfun]
  -- the clamped, regrouped family
  have hΩc : ∀ i, famGraph (clampFam F i) ∈ S.Ω (F0 + aclf) (D + cclf) (p + (n + 1) + 1) :=
    fun i => hClampF (k := k) F0 D F hΩ i
  have hΩv : ∀ i, famGraph (vie (clampFam F) i)
      ∈ S.Ω (F0 + acl) (D + ccl) ((p + 1) + n + 1) := by
    intro i
    have h := hClamp (k := k) F F0 D hΩ i
    rw [vie_clampFam_eq F i]
    exact h
  have hvalv : ValuesIn01 Λ'' (vie (clampFam F)) := by
    intro i w hw y hy
    exact yclamp_mem _
  obtain ⟨Ξ, hΞcard, hΞok, hΞcov⟩ :=
    hih (D + ccl) r k (ε / 2) (by linarith) (by linarith) Λ'' (vie (clampFam F))
      trivial hΩv hvalv
  have hΞne : Ξ.Nonempty := by
    have hw : (fun _ : Fin (p + 1) => (1 / 2 : ℝ)) ∈ Λ'' := by
      rw [hΛ'']
      simp only [Set.mem_ofPred_eq, I]
      norm_num
    have hx : (fun _ : Fin n => (1 / 2 : ℝ)) ∈ openCube n := by
      intro i
      exact ⟨by norm_num, by norm_num⟩
    obtain ⟨φ, hφ, _⟩ := hΞcov _ hw _ hx
    exact ⟨φ, hφ⟩
  -- the pullback families satisfy `PY` and `ValuesIn01`
  have hPY : ∀ φ ∈ Ξ, YBound (pullFam (clampFam F) φ) r := by
    intro φ hφ i l x hx m hm y hy
    have hw : parSnoc l x ∈ Λ'' := by
      rw [hΛ'']
      simp only [Set.mem_ofPred_eq, parSnoc, Fin.snoc_last]
      exact hx
    have h := (hΞok φ hφ).2 (parSnoc l x) hw
    have hnorm := (h.2 i).2 m hm y hy
    rw [slice_pullFam]
    exact hnorm
  have hΩG : ∀ φ ∈ Ξ, ∀ i, famGraph (pullFam (clampFam F) φ i)
      ∈ S.Ω ((F0 + aclf) + (a₁ + aphi) + acomp) Dg (p + (n + 1) + 1) := by
    intro φ hφ i
    have hχ : ∀ j, famGraph (fun l z => phiPt φ l z j)
        ∈ S.Ω (a₁ + aphi) (MvPolynomial.eval ![D + ccl, r] b₁ + cphi) (p + (n + 1) + 1) :=
      fun j => hPhi a₁ (MvPolynomial.eval ![D + ccl, r] b₁) φ (fun j => (hΞok φ hφ).1 j) j
    have hmain := hComp (F0 + aclf) (a₁ + aphi) (D + cclf)
      (MvPolynomial.eval ![D + ccl, r] b₁ + cphi) (clampFam F i) (fun j l z => phiPt φ l z j)
      (hΩc i) hχ
    rw [hDg]
    exact hmain
  have hValG : ∀ φ ∈ Ξ, ValuesIn01 Λ (pullFam (clampFam F) φ) := by
    intro φ hφ i l hl z hz
    exact yclamp_mem _
  have hGdata : ∀ φ ∈ Ξ, ∃ Ψ : Finset (ChartTuple p (n + 1)),
      (Ψ.card : ℝ) ≤ MvPolynomial.eval ![(Dg : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] cG ∧
      ChartsOK S aG (MvPolynomial.eval ![Dg, r] bG) r Λ (pullFam (clampFam F) φ) Ψ ∧
      Covers Λ (pullFam (clampFam F) φ) Ψ (ε / 2) := by
    intro φ hφ
    exact hhP0 Dg r k (ε / 2) (by linarith) (by linarith) Λ (pullFam (clampFam F) φ)
      (hPY φ hφ) (hΩG φ hφ) (hValG φ hφ)
  set Ψ : ChartTuple (p + 1) n → Finset (ChartTuple p (n + 1)) :=
    fun φ => if h : φ ∈ Ξ then (hGdata φ h).choose else ∅ with hΨ
  have hΨspec : ∀ φ (hφ : φ ∈ Ξ),
      ((Ψ φ).card : ℝ) ≤ MvPolynomial.eval ![(Dg : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] cG
        ∧ ChartsOK S aG (MvPolynomial.eval ![Dg, r] bG) r Λ (pullFam (clampFam F) φ) (Ψ φ)
        ∧ Covers Λ (pullFam (clampFam F) φ) (Ψ φ) (ε / 2) := by
    intro φ hφ
    have hΨeq : Ψ φ = (hGdata φ hφ).choose := by
      rw [hΨ]
      show (if h : φ ∈ Ξ then (hGdata φ h).choose else ∅)
        = (hGdata φ hφ).choose
      rw [dif_pos hφ]
    rw [hΨeq]
    exact (hGdata φ hφ).choose_spec
  have hEvalGnn : 0 ≤ MvPolynomial.eval ![(Dg : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] cG := by
    obtain ⟨φ0, hφ0⟩ := hΞne
    exact le_trans (Nat.cast_nonneg _) (hΨspec φ0 hφ0).1
  refine ⟨Ξ.biUnion (fun φ => (Ψ φ).image (fun ψ => chartComp φ ψ)), ?_, ?_, ?_⟩
  · -- cardinality
    have h1 : ((Ξ.biUnion (fun φ => (Ψ φ).image (fun ψ => chartComp φ ψ))).card : ℝ)
        ≤ ∑ φ ∈ Ξ, (((Ψ φ).image (fun ψ => chartComp φ ψ)).card : ℝ) := by
      have h := Finset.card_biUnion_le (s := Ξ)
        (t := fun φ => (Ψ φ).image (fun ψ => chartComp φ ψ))
      exact_mod_cast h
    have h2 : ∑ φ ∈ Ξ, (((Ψ φ).image (fun ψ => chartComp φ ψ)).card : ℝ)
        ≤ ∑ φ ∈ Ξ, ((Ψ φ).card : ℝ) := by
      refine Finset.sum_le_sum fun φ _ => ?_
      exact_mod_cast Finset.card_image_le
    have h3 : ∑ φ ∈ Ξ, ((Ψ φ).card : ℝ)
        ≤ ∑ _φ ∈ Ξ, MvPolynomial.eval ![(Dg : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] cG :=
      Finset.sum_le_sum fun φ hφ => (hΨspec φ hφ).1
    have h4 : ∑ _φ ∈ Ξ, MvPolynomial.eval ![(Dg : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] cG
        = (Ξ.card : ℝ)
          * MvPolynomial.eval ![(Dg : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] cG := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h5 : (Ξ.card : ℝ)
          * MvPolynomial.eval ![(Dg : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] cG
        ≤ MvPolynomial.eval ![(D : ℝ) + (ccl : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c₁
          * MvPolynomial.eval ![(Dg : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] cG :=
      mul_le_mul_of_nonneg_right (by simpa using hΞcard) hEvalGnn
    rw [eval_cfin]
    exact h1.trans (h2.trans (h3.trans (h4.trans_le h5)))
  · -- per-chart conditions
    intro φfin hφfin
    rw [Finset.mem_biUnion] at hφfin
    obtain ⟨φ, hφΞ, hmem⟩ := hφfin
    rw [Finset.mem_image] at hmem
    obtain ⟨ψ, hψ, rfl⟩ := hmem
    obtain ⟨hΨcard, hΨok, hΨcov⟩ := hΨspec φ hφΞ
    obtain ⟨hΨgraph, hΨrest⟩ := hΨok ψ hψ
    refine ⟨?_, ?_⟩
    · intro j
      have hf : famGraph (fun l z => phiPt φ l z j)
          ∈ S.Ω (a₁ + aphi) (MvPolynomial.eval ![D + ccl, r] b₁ + cphi) (p + (n + 1) + 1) :=
        hPhi a₁ (MvPolynomial.eval ![D + ccl, r] b₁) φ (fun j => (hΞok φ hφΞ).1 j) j
      have hmain := hComp (a₁ + aphi) aG (MvPolynomial.eval ![D + ccl, r] b₁ + cphi)
        (MvPolynomial.eval ![Dg, r] bG) (fun l z => phiPt φ l z j) ψ hf hΨgraph
      rw [eval_bfin]
      exact hmain
    · intro l hl
      have hφcube := (hΞok φ hφΞ).2
      have hψcube := (hΨrest l hl).1
      have hucube : ∀ t ∈ openCube (n + 1), phiPt φ l (toPt ψ l t) ∈ openCube (n + 1) := by
        intro t ht
        have hw : toPt ψ l t ∈ openCube (n + 1) := hψcube t ht
        have hφc := hφcube (parSnoc l ((toPt ψ l t) 0)) (by
          rw [hΛ'', Set.mem_ofPred_eq]
          simpa only [parSnoc_last, I] using hw 0)
        have h0 : (toPt ψ l t) 0 ∈ Set.Ioo (0 : ℝ) 1 := hw 0
        intro j
        refine Fin.cases ?_ ?_ j
        · show (toPt ψ l t) 0 ∈ Set.Ioo (0 : ℝ) 1
          exact h0
        · intro i
          exact hφc.1 (Fin.tail (toPt ψ l t)) (fun k => hw k.succ) i
      refine ⟨?_, ?_⟩
      · intro t ht
        rw [show (fun j => chartComp φ ψ j l t) = phiPt φ l (toPt ψ l t)
              from funext (fun j => rfl)]
        exact hucube t ht
      · intro i
        refine ⟨?_, ?_⟩
        · have hg : ContDiffOn ℝ r
              (fun t => pullFam (clampFam F) φ i l (toPt ψ l t)) (openCube (n + 1)) :=
            ((hΨrest l hl).2 i).1
          refine hg.congr (fun t ht => ?_)
          have hu := hucube t ht
          have h2 : pullFam (clampFam F) φ i l (toPt ψ l t)
              = F i l (phiPt φ l (toPt ψ l t)) := by
            simp only [pullFam, clampFam_eq_of_mem F i l _ (hval i l hl _ hu)]
          rw [show (fun j => chartComp φ ψ j l t) = phiPt φ l (toPt ψ l t)
                from funext (fun j => rfl), h2]
        · intro m hm t ht
          have hg : ‖iteratedFDeriv ℝ m (fun t => pullFam (clampFam F) φ i l
              (toPt ψ l t)) t‖ ≤ 1 := ((hΨrest l hl).2 i).2 m hm t ht
          have hev : (fun t => F i l (fun j => chartComp φ ψ j l t))
              =ᶠ[𝓝 t] (fun t => pullFam (clampFam F) φ i l (toPt ψ l t)) := by
            refine Filter.eventually_of_mem ((openCube_isOpen (n + 1)).mem_nhds ht)
              (fun s hs => ?_)
            show F i l (fun j => chartComp φ ψ j l s) = pullFam (clampFam F) φ i l (toPt ψ l s)
            have hu := hucube s hs
            have h2 : pullFam (clampFam F) φ i l (toPt ψ l s)
                = F i l (phiPt φ l (toPt ψ l s)) := by
              simp only [pullFam, clampFam_eq_of_mem F i l _ (hval i l hl _ hu)]
            rw [show (fun j => chartComp φ ψ j l s) = phiPt φ l (toPt ψ l s)
                  from funext (fun j => rfl), h2]
          rw [(hev.iteratedFDeriv ℝ m).eq_of_nhds]
          exact hg
  · -- the cover
    intro l hl x hx
    have hw : parSnoc l (x 0) ∈ Λ'' := by
      rw [hΛ'', Set.mem_ofPred_eq]
      simpa only [parSnoc, Fin.snoc_last, I] using hx 0
    have hy0 : Fin.tail x ∈ openCube n := fun k => hx k.succ
    obtain ⟨φ, hφΞ, t₀, ht₀, hcov1⟩ := hΞcov (parSnoc l (x 0)) hw (Fin.tail x) hy0
    obtain ⟨-, hΨok, hΨcov⟩ := hΨspec φ hφΞ
    have hu0 : phiPt φ l (pt (x 0) t₀) ∈ openCube (n + 1) := by
      have hφc := (hΞok φ hφΞ).2 (parSnoc l (x 0)) hw
      have h0 : x 0 ∈ Set.Ioo (0 : ℝ) 1 := hx 0
      intro j
      refine Fin.cases ?_ ?_ j
      · show (pt (x 0) t₀) 0 ∈ Set.Ioo (0 : ℝ) 1
        exact h0
      · intro i
        exact hφc.1 t₀ ht₀ i
    have hcov1' : ∀ i, |F i l (phiPt φ l (pt (x 0) t₀)) - F i l x| < ε / 2 := by
      intro i
      have h1 : vie (clampFam F) i (parSnoc l (x 0)) (fun j => φ j (parSnoc l (x 0)) t₀)
          = F i l (phiPt φ l (pt (x 0) t₀)) := by
        rw [vie_parSnoc, ← phiPt_pt φ l (x 0) t₀]
        exact clampFam_eq_of_mem F i l _ (hval i l hl _ hu0)
      have h2 : vie (clampFam F) i (parSnoc l (x 0)) (Fin.tail x) = F i l x := by
        rw [vie_parSnoc]
        rw [Fin.cons_self_tail x]
        exact clampFam_eq_of_mem F i l x (hval i l hl x hx)
      have hc1 := hcov1 i
      rw [h1, h2] at hc1
      exact hc1
    have hp0 : pt (x 0) t₀ ∈ openCube (n + 1) := by
      intro j
      refine Fin.cases ?_ ?_ j
      · exact hx 0
      · intro i
        exact ht₀ i
    obtain ⟨ψ, hψ, t₁, ht₁, hcov2⟩ := hΨcov l hl (pt (x 0) t₀) hp0
    have hΨrest := (hΨok ψ hψ).2
    refine ⟨chartComp φ ψ, ?_, t₁, ht₁, ?_⟩
    · rw [Finset.mem_biUnion]
      exact ⟨φ, hφΞ, Finset.mem_image.mpr ⟨ψ, hψ, rfl⟩⟩
    · intro i
      have h2 : pullFam (clampFam F) φ i l (pt (x 0) t₀)
          = F i l (phiPt φ l (pt (x 0) t₀)) := by
        simp only [pullFam, clampFam_eq_of_mem F i l _ (hval i l hl _ hu0)]
      have h3 : pullFam (clampFam F) φ i l (toPt ψ l t₁)
          = F i l (phiPt φ l (toPt ψ l t₁)) := by
        have hwψ : toPt ψ l t₁ ∈ openCube (n + 1) := (hΨrest l hl).1 t₁ ht₁
        have hu1 : phiPt φ l (toPt ψ l t₁) ∈ openCube (n + 1) := by
          have hφc := (hΞok φ hφΞ).2 (parSnoc l ((toPt ψ l t₁) 0)) (by
            rw [hΛ'', Set.mem_ofPred_eq]
            simpa only [parSnoc_last, I] using hwψ 0)
          have h0 : (toPt ψ l t₁) 0 ∈ Set.Ioo (0 : ℝ) 1 := hwψ 0
          intro j
          refine Fin.cases ?_ ?_ j
          · show (toPt ψ l t₁) 0 ∈ Set.Ioo (0 : ℝ) 1
            exact h0
          · intro i
            exact hφc.1 (Fin.tail (toPt ψ l t₁)) (fun k => hwψ k.succ) i
        simp only [pullFam, clampFam_eq_of_mem F i l _ (hval i l hl _ hu1)]
      have hc2 : |F i l (phiPt φ l (toPt ψ l t₁)) - F i l (phiPt φ l (pt (x 0) t₀))| < ε / 2 := by
        have h' : |pullFam (clampFam F) φ i l (toPt ψ l t₁)
            - pullFam (clampFam F) φ i l (pt (x 0) t₀)| < ε / 2 := hcov2 i
        rw [h2, h3] at h'
        exact h'
      have hcomp : (fun j => chartComp φ ψ j l t₁) = phiPt φ l (toPt ψ l t₁) :=
        funext (fun j => rfl)
      rw [hcomp]
      have htri : |F i l (phiPt φ l (toPt ψ l t₁)) - F i l (phiPt φ l (pt (x 0) t₀))|
          + |F i l (phiPt φ l (pt (x 0) t₀)) - F i l x| < ε := by
        linarith [hc2, hcov1' i]
      calc |F i l (phiPt φ l (toPt ψ l t₁)) - F i l x|
          ≤ |F i l (phiPt φ l (toPt ψ l t₁)) - F i l (phiPt φ l (pt (x 0) t₀))|
            + |F i l (phiPt φ l (pt (x 0) t₀)) - F i l x| := by
            rw [← Real.dist_eq]
            exact dist_triangle _ _ _
        _ < ε := htri

end

end Work.WilkG4c

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- Alias of `Work.WilkG4c.StepYbdd` under the path-derived namespace (the area writes its
files in the namespace `Work.WilkG4c`, which differs from the directory name `WilG4c`). -/
theorem StepYbdd (S : SOMin) (n p : ℕ) (hn : 1 ≤ n) (ih : ∀ q, FLem S q n)
    (hP0 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PY p n)) :
    FLem S p (n + 1) :=
  Work.WilkG4c.StepYbdd S n p hn ih hP0

end Work.WilG4c
