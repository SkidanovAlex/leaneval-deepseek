import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG5.Defs
import Submission.Work.WilG5.Cell.cell_par
import Submission.Work.WilG5.Cell.cell_dim
import Submission.Work.WilG5.Rel.padRel_mem
import Submission.Work.WilG5.Rel.pad_par
import Submission.Work.WilG5.Rel.graphOf_RelSel_mem
import Submission.Work.WilG5.Rel.norm_iteratedFDeriv_pi_le
import Submission.Work.WilG5.Count.dominate
import Submission.Work.WilG5.Interior.famGraph_param_mem
import Submission.Work.WilG5.Interior.sv_rel
import Submission.Work.WilG5.Interior.famgraph_uniform

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilG5.Interior

open WilkiesDesign WilkiesConjecture

theorem cell_charts (S : WilkiesDesign.SOMin) (hF : ∀ p n, WilkiesDesign.CG.FLem S p n)
    (n : ℕ) (F₀ : ℕ) (μ : ℕ) (hμ : μ ≤ n) :
    ∃ c : MvPolynomial (Fin 4) ℝ,
      ∀ (D₀ r : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (κ : Set (Fin n → ℝ)), WilkiesDesign.IsCell n κ → κ.Nonempty →
        κ ⊆ WilkiesDesign.cube01 n → κ ⊆ WilkiesDesign.openCube n →
        κ ∈ S.Ω F₀ D₀ n → WilkiesDesign.DimLE κ μ →
        ∃ Ψ : Finset ((Fin μ → ℝ) → (Fin n → ℝ)),
          (Ψ.card : ℝ) ≤ MvPolynomial.eval ![(D₀ : ℝ), (r : ℝ), (n : ℝ), -Real.log ε] c ∧
          (∀ φ ∈ Ψ, (∀ t ∈ WilkiesDesign.openCube μ, φ t ∈ κ) ∧
            ContDiffOn ℝ r φ (WilkiesDesign.openCube μ) ∧
            ∀ k ≤ r, ∀ t ∈ WilkiesDesign.openCube μ, ‖iteratedFDeriv ℝ k φ t‖ ≤ 1) ∧
          ∀ x ∈ κ, x ∈ WilkiesDesign.openCube n →
            ∃ φ ∈ Ψ, ∃ t ∈ WilkiesDesign.openCube μ, dist (φ t) x < ε := by
  classical
  obtain ⟨Apar, Cpar, Lpar, hcellpar⟩ := Work.WilG5.Cell.cell_par S n F₀
  choose Agr Cgr Lgr hgr using fun (i : Fin n) =>
    Work.WilG5.Rel.graphOf_RelSel_mem (S := S) (d := μ) (n := n) i (1 : ℝ) (0 : ℝ)
  obtain ⟨Asv, Lsv, hsv⟩ := Work.WilG5.Interior.svRel_mem (S := S) (d := μ) (n := n)
  obtain ⟨Agf, Lgf, hgf⟩ := Work.WilG5.Interior.famGraph_param_mem_uniform S μ
  set AgrM : ℕ := Finset.univ.sup Agr with hAgrM
  set CgrM : ℕ := Finset.univ.sup Cgr with hCgrM
  set LgrM : ℕ := Finset.univ.sup Lgr with hLgrM
  have hAgr_le : ∀ i : Fin n, Agr i ≤ AgrM := fun i => by
    rw [hAgrM]; exact Finset.le_sup (Finset.mem_univ i)
  have hCgr_le : ∀ i : Fin n, Cgr i ≤ CgrM := fun i => by
    rw [hCgrM]; exact Finset.le_sup (Finset.mem_univ i)
  have hLgr_le : ∀ i : Fin n, Lgr i ≤ LgrM := fun i => by
    rw [hLgrM]; exact Finset.le_sup (Finset.mem_univ i)
  set LpadM : ℕ := 32 * ((μ + n) + (μ + n)) + 32 with hLpadM
  set ApadM : ℕ := 64 * ((μ + n) + (μ + n)) + 64 with hApadM
  set cD : Polynomial ℕ := Polynomial.C Cpar * Polynomial.X + Polynomial.C (Lpar + LpadM + Lsv) with hcD
  set Ffam : ℕ := Agf + (AgrM + (Asv + (ApadM + Apar))) with hFfam
  obtain ⟨aF, bF, cF, hFmain⟩ := hF 1 μ Ffam
  set L0 : ℕ := LgrM + Lgf with hL0
  obtain ⟨p, hpnn, hpbound⟩ := Work.WilG5.Count.dominate cF cD CgrM L0 0 n
  set cc : MvPolynomial (Fin 4) ℝ := MvPolynomial.rename (fun i : Fin 3 => ![(0 : Fin 4), 1, 3] i) p with hcc
  refine ⟨cc, ?_⟩
  intro D₀ r ε hε0 hε1 κ hcell hne hsub01 hsubopen hΩ hdim
  obtain ⟨d, e, R, hd, hR, hpar⟩ := hcellpar D₀ κ hcell hne hsub01 hΩ
  have hdμ : d ≤ μ := Work.WilG5.Cell.cell_dim hpar hne (le_refl κ) hdim
  set Br : ℕ := Cpar * D₀ + (Lpar + LpadM) with hBr
  have hR' : Work.WilG5.padRel hdμ R ∈ S.Ω (ApadM + Apar) Br (μ + n) := by
    refine Work.WilG5.mem_mono
      (Work.WilG5.Interior.padRel_mem_explicit (S := S) (μ := μ) hdμ Apar (Cpar * D₀ + Lpar) R hR)
      (ApadM + Apar) Br ?_ ?_
    · rw [hApadM]; omega
    · rw [hBr, hLpadM]; omega
  set Bsv : ℕ := Br + Lsv with hBsv
  have hR'' : Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R) ∈
      S.Ω (Asv + (ApadM + Apar)) Bsv (μ + n) := by
    refine Work.WilG5.mem_mono (hsv (ApadM + Apar) Br (Work.WilG5.padRel hdμ R) hR')
      (Asv + (ApadM + Apar)) Bsv ?_ ?_
    · omega
    · rw [hBsv]
  obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := Work.WilG5.Rel.pad_par hdμ hpar
  have hsingle : ∀ u : Fin μ → ℝ,
      (∃ x : Fin n → ℝ, Fin.append u x ∈ Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R)) →
      ∀ x y : Fin n → ℝ, Fin.append u x ∈ Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R) →
        Fin.append u y ∈ Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R) → x = y :=
    Work.WilG5.Interior.svRel_single (d := μ) (n := n) (R := Work.WilG5.padRel hdμ R) hp2
  set Bg : ℕ := CgrM * Bsv + LgrM with hBg
  have hgraph : ∀ i : Fin n,
      WilkiesDesign.graphOf (fun u : Fin μ → ℝ =>
        Work.WilG5.RelSel (Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R)) u i) ∈
        S.Ω (AgrM + (Asv + (ApadM + Apar))) Bg (μ + 1) := by
    intro i
    have h0 := hgr i (Asv + (ApadM + Apar)) Bsv
      (Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R)) hR'' hsingle
    have h0' : WilkiesDesign.graphOf (fun u : Fin μ → ℝ =>
        Work.WilG5.RelSel (Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R)) u i) ∈
        S.Ω (Agr i + (Asv + (ApadM + Apar))) (Cgr i * Bsv + Lgr i) (μ + 1) := by
      simpa only [one_mul, add_zero] using h0
    refine Work.WilG5.mem_mono h0' (AgrM + (Asv + (ApadM + Apar))) Bg ?_ ?_
    · have h1 : Agr i ≤ AgrM := hAgr_le i; omega
    · have h1 : Cgr i * Bsv ≤ CgrM * Bsv := Nat.mul_le_mul_right Bsv (hCgr_le i)
      have h2 : Lgr i ≤ LgrM := hLgr_le i
      rw [hBg]; omega
  set Dfam : ℕ := CgrM * Bsv + (LgrM + Lgf) with hDfam
  have hfam : ∀ i : Fin n,
      WilkiesDesign.CG.famGraph (fun (_ : Fin 1 → ℝ) (u : Fin μ → ℝ) =>
        Work.WilG5.RelSel (Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R)) u i) ∈
        S.Ω Ffam Dfam (1 + μ + 1) := by
    intro i
    have h0 := hgf (fun u : Fin μ → ℝ =>
      Work.WilG5.RelSel (Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R)) u i)
      (AgrM + (Asv + (ApadM + Apar))) Bg (hgraph i)
    refine Work.WilG5.mem_mono h0 Ffam Dfam ?_ ?_
    · rw [hFfam]
    · rw [hDfam, hBg]; omega
  let l0 : Fin 1 → ℝ := 0
  let Ff : Fin n → (Fin 1 → ℝ) → (Fin μ → ℝ) → ℝ := fun i _ x =>
    Work.WilG5.RelSel (Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R)) x i
  have hval : ∀ i : Fin n, ∀ l ∈ (Set.univ : Set (Fin 1 → ℝ)), ∀ x ∈ WilkiesDesign.openCube μ,
      Ff i l x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i l _ x hx
    have hsel : Work.WilG5.RelSel (Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R)) x =
        Work.WilG5.RelSel (Work.WilG5.padRel hdμ R) x :=
      Work.WilG5.Interior.svRel_RelSel (d := μ) (n := n) hp3 hp2 hx
    have hspec : Fin.append x (Work.WilG5.RelSel (Work.WilG5.padRel hdμ R) x) ∈
        Work.WilG5.padRel hdμ R := Work.WilG5.RelSel_spec (hp3 x hx)
    have hink : Work.WilG5.RelSel (Work.WilG5.padRel hdμ R) x ∈ κ := hp1 x hx _ hspec
    have h2 : Work.WilG5.RelSel (Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R)) x ∈ κ := by
      rw [hsel]; exact hink
    have h3 : Work.WilG5.RelSel (Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R)) x ∈
        WilkiesDesign.openCube n := hsubopen h2
    exact h3 i
  obtain ⟨Φ, hΦcard, hΦprop, hΦcover⟩ :=
    hFmain Dfam r n ε hε0 hε1 (Set.univ : Set (Fin 1 → ℝ)) Ff hfam hval
  let ψ : (Fin μ → (Fin 1 → ℝ) → (Fin μ → ℝ) → ℝ) → (Fin μ → ℝ) → (Fin n → ℝ) :=
    fun φ t => fun i => Ff i l0 (fun j => φ j l0 t)
  refine ⟨Φ.image ψ, ?_, ?_, ?_⟩
  · have h1 : ((Φ.image ψ).card : ℝ) ≤ (Φ.card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    have hs : 0 ≤ -Real.log ε := by
      have := Real.log_nonpos (le_of_lt hε0) (le_of_lt hε1)
      linarith
    have h3 := hpbound D₀ r (-Real.log ε) hs
    have hcDeq : cD.eval D₀ = Bsv := by
      rw [hcD, hBsv, hBr, hLpadM]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
      omega
    have hDeq : CgrM * cD.eval D₀ + L0 = Dfam := by
      rw [hcDeq, hDfam, hL0]
    have h4 : |cF.eval ![(Dfam : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]| ≤
        p.eval ![(D₀ : ℝ), (r : ℝ), -Real.log ε] := by
      have hh := h3
      rw [hDeq] at hh
      simpa using hh
    calc ((Φ.image ψ).card : ℝ)
        ≤ (Φ.card : ℝ) := h1
      _ ≤ cF.eval ![(Dfam : ℝ), (r : ℝ), (n : ℝ), -Real.log ε] := hΦcard
      _ ≤ |cF.eval ![(Dfam : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]| := le_abs_self _
      _ ≤ p.eval ![(D₀ : ℝ), (r : ℝ), -Real.log ε] := h4
      _ = cc.eval ![(D₀ : ℝ), (r : ℝ), (n : ℝ), -Real.log ε] := by
            rw [hcc, MvPolynomial.eval_rename]
            have hass : ((![(D₀ : ℝ), (r : ℝ), (n : ℝ), -Real.log ε] : Fin 4 → ℝ) ∘
                (fun i : Fin 3 => ![(0 : Fin 4), 1, 3] i)) =
                ![(D₀ : ℝ), (r : ℝ), -Real.log ε] := by
              funext i
              fin_cases i <;> simp
            rw [hass]
  · intro ψ0 hψ0
    rcases Finset.mem_image.mp hψ0 with ⟨φ, hφΦ, rfl⟩
    obtain ⟨_, hφ2⟩ := hΦprop φ hφΦ
    obtain ⟨hcube, hrest⟩ := hφ2 l0 (Set.mem_univ ())
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      have harg : (fun j : Fin μ => φ j l0 t) ∈ WilkiesDesign.openCube μ := hcube t ht
      have hsel : Work.WilG5.RelSel (Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R))
            (fun j : Fin μ => φ j l0 t) =
          Work.WilG5.RelSel (Work.WilG5.padRel hdμ R) (fun j : Fin μ => φ j l0 t) :=
        Work.WilG5.Interior.svRel_RelSel (d := μ) (n := n) hp3 hp2 harg
      have hspec := Work.WilG5.RelSel_spec (R := Work.WilG5.padRel hdμ R) (hp3 _ harg)
      have hink : Work.WilG5.RelSel (Work.WilG5.padRel hdμ R) (fun j : Fin μ => φ j l0 t) ∈ κ :=
        hp1 _ harg _ hspec
      show (fun i : Fin n => Ff i l0 (fun j : Fin μ => φ j l0 t)) ∈ κ
      have heqf : (fun i : Fin n => Ff i l0 (fun j : Fin μ => φ j l0 t)) =
          Work.WilG5.RelSel (Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R))
            (fun j : Fin μ => φ j l0 t) := rfl
      rw [heqf, hsel]; exact hink
    · show ContDiffOn ℝ r
          (fun t : Fin μ → ℝ => fun i : Fin n => Ff i l0 (fun j : Fin μ => φ j l0 t))
          (WilkiesDesign.openCube μ)
      exact contDiffOn_pi.mpr (fun i => (hrest i).1)
    · intro k hk t ht
      refine Work.WilG5.Rel.norm_iteratedFDeriv_pi_le _ _ ?_ ?_
      · have hopen : WilkiesDesign.openCube μ ∈ nhds t :=
          (Work.WilG5.Cell.isOpen_openCube μ).mem_nhds ht
        have hcd : ContDiffOn ℝ r
            (fun t : Fin μ → ℝ => fun i : Fin n => Ff i l0 (fun j : Fin μ => φ j l0 t))
            (WilkiesDesign.openCube μ) := contDiffOn_pi.mpr (fun i => (hrest i).1)
        exact (hcd.contDiffAt hopen).of_le (by exact_mod_cast hk)
      · intro i
        exact (hrest i).2 k hk t ht
  · intro x hxκ hxopen
    obtain ⟨u, hu, huR⟩ := hp4 x hxκ
    have hx_eq : Work.WilG5.RelSel (Work.WilG5.padRel hdμ R) u = x :=
      Work.WilG5.RelSel_eq huR (fun y hy => hp2 u hu y x hy huR)
    obtain ⟨φ, hφΦ, t, ht, hφc⟩ := hΦcover l0 (Set.mem_univ ()) u hu
    refine ⟨ψ φ, Finset.mem_image.mpr ⟨φ, hφΦ, rfl⟩, t, ht, ?_⟩
    rw [dist_pi_lt_iff hε0]
    intro i
    have h1 : Ff i l0 u = x i := by
      show Work.WilG5.RelSel (Work.WilG5.Interior.svRel (Work.WilG5.padRel hdμ R)) u i = x i
      rw [Work.WilG5.Interior.svRel_RelSel (d := μ) (n := n) hp3 hp2 hu, hx_eq]
    have h2 := hφc i
    rw [h1] at h2
    rw [Real.dist_eq]
    exact h2

end Work.WilG5.Interior
