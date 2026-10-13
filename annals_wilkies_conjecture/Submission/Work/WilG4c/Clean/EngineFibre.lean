import Mathlib
import Submission.Work.WilG4c.Clean.Engine

set_option maxHeartbeats 4000000

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

-- Identical to `StepCellEngine`, except that the differentiability data is not read off the
-- bad locus: it is assumed directly on the fibre of the cell `κ` over `Λ`.  Consequently the
-- proof is the proof of `StepCellEngine` with `PYLipDef`'s `NormLeOneDef` and
-- `contDiffAt_of_mem_cell_disjoint_badLoc` replaced by the two components of the fibre
-- hypothesis.  (The `YBound` and `LipOnCube` components of `PYLipDef` were never used.)

theorem StepCellEngineFibre (S : WilkiesDesign.SOMin) (n p : ℕ) (hn : 1 ≤ n)
    (ih : ∀ q, WilkiesDesign.CG.FLem S q n) (F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (Λ : Set (Fin p → ℝ))
        (F : Work.WilkG4c.Family k p (n + 1))
        (C : Finset (Set (Fin (p + (n + 1)) → ℝ)))
        (κ : Set (Fin (p + (n + 1)) → ℝ)),
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        (∀ i, ∀ l ∈ Λ, ∀ x ∈ WilkiesDesign.openCube (n + 1), F i l x ∈ Set.Ioo (0 : ℝ) 1) →
        Work.WilkG4c.LipOnCube F 1 →
        WilkiesDesign.IsCylDecomp (p + (n + 1)) C →
        (∀ κ' ∈ C, κ' ∈ S.Ω F0 D (p + (n + 1))) →
        κ ∈ C → κ ⊆ Work.WilG4c.inCubeSet p (n + 1) →
        (∀ i, ∀ l ∈ Λ, ∀ y : Fin (n + 1) → ℝ, Fin.append l y ∈ κ →
          ContDiffAt ℝ r (F i l) y ∧
            ∀ m, m ≤ r → ‖iteratedFDeriv ℝ m (F i l) y‖ ≤ 1) →
        (∀ l ∈ Λ, ∃ y : Fin (n + 1) → ℝ, Fin.append l y ∈ κ) →
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          ∃ Ψ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
            (Ψ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (1 : ℝ), -Real.log ε] c ∧
            Work.WilkG4c.ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Ψ ∧
            (∀ l ∈ Λ, ∀ y : Fin (n + 1) → ℝ, Fin.append l y ∈ κ →
              ∃ φ ∈ Ψ, ∃ t ∈ WilkiesDesign.openCube (n + 1),
                ∀ j : Fin (n + 1), |φ j l t - y j| < ε) := by
  classical
  -- ================================================================ constants
  obtain ⟨a_fe, b_fe, hFE⟩ := StepFiberEnds S (p + n) F0
  obtain ⟨a_cp, b_cp, hCP⟩ := CellParamMain S p n (F0 + 1)
  obtain ⟨S₀, hS₀1, hJet⟩ := ChartJetBoundC p n
  obtain ⟨c_nm, hc_nm_pos, hNorm⟩ :=
    chart_norms_rescale_grid (n + 1) (by omega) S₀ (le_trans zero_le_one hS₀1)
  obtain ⟨A_mw, C_mw, hMW⟩ := MidWidMem S p n (max a_cp a_fe)
  set F_fam : ℕ := max a_cp a_fe + A_mw with hF_fam
  obtain ⟨a_ih, b_ih, c_ih, IH⟩ := ih p F_fam
  obtain ⟨A_eng, C_eng, hENG⟩ := EngineChartMem S p n (max F_fam a_ih)
  obtain ⟨A_sub, C_sub, hSUB⟩ := WilkG4c.ChartSubstMem S p (n + 1)
  obtain ⟨Dfp, b, c, hbk⟩ :=
    EngineBookkeeping n c_nm (le_of_lt hc_nm_pos) b_cp b_fe b_ih C_mw C_eng C_sub c_ih
  refine ⟨max F_fam a_ih + A_eng + A_sub, b, c, ?_⟩
  intro D r k Λ F C κ hΩF h01 hLip hdec hκΩ hκC hcube hFib hne ε hε0 hε1
  -- ================================================================ setup
  obtain ⟨hdec', hC₀mem, hC₀Ω, hC₀cube, hne₀, hκI, hκcell, hprojLast⟩ :=
    EngineSetup S n p F0 D Λ C κ hdec hκΩ hκC hcube hne
  -- The fibre hypothesis supplies, at every point of `κ` over `Λ`, both the `C^r`-ness of
  -- the member and the unit bound on its iterated derivatives — exactly the two facts that
  -- `PYLipDef` plus disjointness from the bad locus provided in `StepCellEngine`.
  have hcd : ∀ (i : Fin k) (l : Fin p → ℝ), l ∈ Λ → ∀ y : Fin (n + 1) → ℝ,
      Fin.append l y ∈ κ → ContDiffAt ℝ r (F i l) y :=
    fun i l hl y hy => (hFib i l hl y hy).1
  have hnorm : ∀ (i : Fin k) (l : Fin p → ℝ), l ∈ Λ → ∀ y : Fin (n + 1) → ℝ,
      Fin.append l y ∈ κ → ∀ m, m ≤ r → ‖iteratedFDeriv ℝ m (F i l) y‖ ≤ 1 :=
    fun i l hl y hy => (hFib i l hl y hy).2
  obtain ⟨χ, hχΩ, hχcube, hχfib, hχsurj⟩ :=
    hCP D (C.image (fun c => Fin.init '' c)) hdec' hC₀Ω (Fin.init '' κ) hC₀mem hC₀cube Λ hne₀
  obtain ⟨lo, hi, hloG, hhiG, hlo⟩ := hFE D r κ (hκΩ κ hκC) hκI
  -- degrees and formats
  set D_mw : ℕ := max (MvPolynomial.eval ![D, 1] b_cp) (MvPolynomial.eval ![D, r] b_fe) with hD_mw
  set D_fam : ℕ := MvPolynomial.eval ![D, r] Dfp with hD_fam
  set D_all : ℕ := max D_fam (MvPolynomial.eval ![D_fam, r] b_ih) with hD_all
  have hbmw1 : MvPolynomial.eval ![D, 1] b_cp ≤ D_fam := by
    rw [hD_fam]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hbk D r).1
  have hbmwc : C_mw * D_mw + C_mw ≤ D_fam := by
    rw [hD_fam, hD_mw]
    exact le_trans (le_max_right _ _) (hbk D r).1
  have hDmw_le : D_mw ≤ D_fam := by
    rw [hD_fam, hD_mw]
    exact le_trans (le_max_left _ _) (hbk D r).1
  have hFfam1 : a_cp ≤ F_fam := by
    rw [hF_fam]; exact le_trans (le_max_left _ _) (Nat.le_add_right _ _)
  have hFfam2 : max a_cp a_fe ≤ F_fam := by
    rw [hF_fam]; exact Nat.le_add_right _ _
  have hFfam3 : F_fam ≤ max F_fam a_ih := le_max_left _ _
  have haih3 : a_ih ≤ max F_fam a_ih := le_max_right _ _
  have hloΩ : graphOf lo ∈ S.Ω (max a_cp a_fe) D_mw (p + n + 1) :=
    WilkG4c.Omega_mono_le S (le_max_right a_cp a_fe) (by rw [hD_mw]; exact le_max_right _ _) hloG
  have hhiΩ : graphOf hi ∈ S.Ω (max a_cp a_fe) D_mw (p + n + 1) :=
    WilkG4c.Omega_mono_le S (le_max_right a_cp a_fe) (by rw [hD_mw]; exact le_max_right _ _) hhiG
  have hχΩ' : ∀ j : Fin n, famGraph (fun l u => χ l u j) ∈
      S.Ω (max a_cp a_fe) D_mw (p + n + 1) := fun j =>
    WilkG4c.Omega_mono_le S (le_max_left a_cp a_fe) (by rw [hD_mw]; exact le_max_left _ _) (hχΩ j)
  obtain ⟨hMW1, hMW2⟩ := hMW D_mw lo hi χ hloΩ hhiΩ hχΩ'
  have hMΩ : famGraph (midFun lo hi χ) ∈ S.Ω F_fam (C_mw * D_mw + C_mw) (p + n + 1) := by
    rw [hF_fam]; exact hMW1
  have hWΩ : famGraph (widFun lo hi χ) ∈ S.Ω F_fam (C_mw * D_mw + C_mw) (p + n + 1) := by
    rw [hF_fam]; exact hMW2
  -- ================================================================ the family
  have hfamΩ : ∀ i : Fin (n + 2),
      famGraph (engFam χ (midFun lo hi χ) (widFun lo hi χ) i) ∈ S.Ω F_fam D_fam (p + n + 1) := by
    intro i
    by_cases h1 : (i : ℕ) < n
    · have heq : engFam χ (midFun lo hi χ) (widFun lo hi χ) i = fun l u => χ l u ⟨(i : ℕ), h1⟩ := by
        funext l u; simp only [engFam, dif_pos h1]
      rw [heq]
      exact WilkG4c.Omega_mono_le S hFfam2 hDmw_le (hχΩ' ⟨(i : ℕ), h1⟩)
    · by_cases h2 : (i : ℕ) = n
      · have heq : engFam χ (midFun lo hi χ) (widFun lo hi χ) i = (midFun lo hi χ) := by
          funext l u; simp only [engFam]; rw [dif_neg h1, if_pos h2]
        rw [heq]
        exact WilkG4c.Omega_mono_le S le_rfl hbmwc hMΩ
      · have heq : engFam χ (midFun lo hi χ) (widFun lo hi χ) i = (widFun lo hi χ) := by
          funext l u; simp only [engFam]; rw [dif_neg h1, if_neg h2]
        rw [heq]
        exact WilkG4c.Omega_mono_le S le_rfl hbmwc hWΩ
  have hbase_ne : ∀ l ∈ Λ, ∀ x ∈ openCube n,
      ∃ c : ℝ, Fin.snoc (Fin.append l (χ l x)) c ∈ κ := by
    intro l hl x hx
    have h := hχfib l hl x hx
    rw [hprojLast] at h
    exact h
  have hfam01 : ∀ i : Fin (n + 2), ∀ l ∈ Λ, ∀ x ∈ openCube n,
      engFam χ (midFun lo hi χ) (widFun lo hi χ) i l x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i l hl x hx
    obtain ⟨c, hc⟩ := hbase_ne l hl x hx
    obtain ⟨hlo0, hlo1, hhi0, hhi1, hmid0, hmid1, hwid0, hwid1, hIoo, hsweep⟩ :=
      FibreEndsInterval κ hκcell hκI lo hi hlo (Fin.append l (χ l x)) ⟨c, hc⟩
    by_cases h1 : (i : ℕ) < n
    · have heq : engFam χ (midFun lo hi χ) (widFun lo hi χ) i l x = χ l x ⟨(i : ℕ), h1⟩ := by
        simp only [engFam, dif_pos h1]
      rw [heq]
      exact hχcube l hl x hx ⟨(i : ℕ), h1⟩
    · by_cases h2 : (i : ℕ) = n
      · have heq : engFam χ (midFun lo hi χ) (widFun lo hi χ) i l x = (midFun lo hi χ) l x := by
          simp only [engFam]; rw [dif_neg h1, if_pos h2]
        rw [heq]
        simp only [midFun]
        exact ⟨hmid0, hmid1⟩
      · have heq : engFam χ (midFun lo hi χ) (widFun lo hi χ) i l x = (widFun lo hi χ) l x := by
          simp only [engFam]; rw [dif_neg h1, if_neg h2]
        rw [heq]
        simp only [widFun]
        exact ⟨by linarith, by linarith⟩
  -- ============================================ the inductive hypothesis at `ε/4`
  obtain ⟨Ψ_ih, hΨcard, hΨOK, hΨcov⟩ :=
    IH D_fam r (n + 2) (ε / 4) (by linarith) (by linarith) Λ (engFam χ (midFun lo hi χ) (widFun lo hi χ)) hfamΩ hfam01
  -- ================================================================ the grid
  set lam : ℝ := max 1 (c_nm * (r + 1)) with hlamdef
  set Kg : ℕ := Nat.ceil (2 * (lam - 1)) + 2 with hKgdef
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hlamc : c_nm * (r + 1) ≤ lam := le_max_right _ _
  have hKg : 2 * (lam - 1) + 2 ≤ (Kg : ℝ) := by
    rw [hKgdef]
    have h1 : 2 * (lam - 1) ≤ (Nat.ceil (2 * (lam - 1)) : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  have hKgb : (Kg : ℝ) ≤ (2 * c_nm + 3) * (r + 1) + 3 := by
    rw [hKgdef]
    have h1 : (Nat.ceil (2 * (lam - 1)) : ℝ) < 2 * (lam - 1) + 1 := Nat.ceil_lt_add_one (by linarith [hlam1] : (0 : ℝ) ≤ 2 * (lam - 1))
    have h2 : lam ≤ 1 + c_nm * (r + 1) := by
      rw [hlamdef]
      exact max_le (le_add_of_nonneg_right (mul_nonneg hc_nm_pos.le (by positivity)))
        (le_add_of_nonneg_left (by norm_num))
    push_cast
    nlinarith [h1, h2, hc_nm_pos.le]
  -- ================================================================ the chart family
  set Ψ_fin : Finset (WilkG4c.ChartTuple p (n + 1)) := engFinset χ lo hi Ψ_ih lam Kg with hΨfin
  -- ------------------------------------------------------------------ cardinality
  have hcard : (Ψ_fin.card : ℝ) ≤
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (1 : ℝ), -Real.log ε] c := by
    have h1 : Ψ_fin.card ≤ Ψ_ih.card * Kg ^ (n + 1) := by
      have h2 : (Finset.univ : Finset (Fin (n + 1) → Fin Kg)).card = Kg ^ (n + 1) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      calc Ψ_fin.card
          ≤ (Ψ_ih.product (Finset.univ : Finset (Fin (n + 1) → Fin Kg))).card := by
            rw [hΨfin, engFinset]; exact Finset.card_image_le
        _ = Ψ_ih.card * (Finset.univ : Finset (Fin (n + 1) → Fin Kg)).card :=
            Finset.card_product _ _
        _ = Ψ_ih.card * Kg ^ (n + 1) := by rw [h2]
    have h2 : (Ψ_ih.card : ℝ) * (Kg : ℝ) ^ (n + 1) ≤
        |MvPolynomial.eval ![(D_fam : ℝ), (r : ℝ), ((n + 2 : ℕ) : ℝ),
            -Real.log (ε / 4)] c_ih| * (((2 * c_nm + 3) * (r + 1) + 3) ^ (n + 1)) := by
      have h3 : (MvPolynomial.eval ![(D_fam : ℝ), (r : ℝ), ((n + 2 : ℕ) : ℝ),
            -Real.log (ε / 4)] c_ih) ≤
          |MvPolynomial.eval ![(D_fam : ℝ), (r : ℝ), ((n + 2 : ℕ) : ℝ),
            -Real.log (ε / 4)] c_ih| := le_abs_self _
      have h4 : (Kg : ℝ) ^ (n + 1) ≤ (((2 * c_nm + 3) * (r + 1) + 3) ^ (n + 1)) :=
        pow_le_pow_left₀ (by positivity) hKgb (n + 1)
      exact mul_le_mul (le_trans hΨcard h3) h4 (by positivity) (abs_nonneg _)
    calc (Ψ_fin.card : ℝ)
        ≤ ((Ψ_ih.card * Kg ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (Ψ_ih.card : ℝ) * (Kg : ℝ) ^ (n + 1) := by push_cast; ring
      _ ≤ _ := h2
      _ ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (1 : ℝ), -Real.log ε] c := by
          rw [hD_fam]; exact (hbk D r).2.2 ε hε0 hε1
  -- ------------------------------------------------------------------ `ChartsOK`
  have hdegineq : (C_eng * D_all + C_eng) + C_sub ≤ MvPolynomial.eval ![D, r] b := by
    rw [hD_all]; exact (hbk D r).2.1
  have hOK : WilkG4c.ChartsOK S (max F_fam a_ih + A_eng + A_sub)
      (MvPolynomial.eval ![D, r] b) r Λ F Ψ_fin := by
    intro φ hφ
    rw [hΨfin, engFinset] at hφ
    obtain ⟨⟨ψ, kk⟩, hmem, hfk⟩ := Finset.mem_image.mp hφ
    obtain ⟨hψmem, -⟩ := Finset.mem_product.mp hmem
    rw [← hfk]
    simp only [engChart]
    set ψp : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) := fun l u => fun j => ψ j l u with hψp
    obtain ⟨hψΩ, hψrest⟩ := hΨOK ψ hψmem
    have hvbd : ∀ i : Fin (n + 1), 0 ≤ gridPt lam kk i ∧ gridPt lam kk i ≤ lam - 1 :=
      gridPt_bounds lam hlam1 kk
    refine ⟨?_, ?_⟩
    · -- `Ω`-bounded coordinate graphs
      intro j
      have hχΩ'' : ∀ j' : Fin n, famGraph (fun l u => χ l u j') ∈
          S.Ω (max F_fam a_ih) D_all (p + n + 1) := fun j' =>
        WilkG4c.Omega_mono_le S (le_trans hFfam2 hFfam3)
          (le_trans hDmw_le (le_max_left _ _)) (hχΩ' j')
      have hMΩ'' : famGraph (midFun lo hi χ) ∈ S.Ω (max F_fam a_ih) D_all (p + n + 1) :=
        WilkG4c.Omega_mono_le S hFfam3 (le_trans hbmwc (le_max_left _ _)) hMΩ
      have hWΩ'' : famGraph (widFun lo hi χ) ∈ S.Ω (max F_fam a_ih) D_all (p + n + 1) :=
        WilkG4c.Omega_mono_le S hFfam3 (le_trans hbmwc (le_max_left _ _)) hWΩ
      have hψΩ'' : ∀ j' : Fin n, famGraph (fun l u => ψp l u j') ∈
          S.Ω (max F_fam a_ih) D_all (p + n + 1) := by
        intro j'
        have heq : (fun l u => ψp l u j') = (fun l u => ψ j' l u) := by
          funext l u; rw [hψp]
        rw [heq]
        exact WilkG4c.Omega_mono_le S haih3 (by rw [hD_all]; exact le_max_right _ _) (hψΩ j')
      have hchartΩ := hENG D_all χ ψp (midFun lo hi χ) (widFun lo hi χ) hχΩ'' hMΩ'' hWΩ'' hψΩ'' j
      have hsub := hSUB ((max F_fam a_ih) + A_eng) (C_eng * D_all + C_eng)
        (fun l z => cellChart χ (midFun lo hi χ) (widFun lo hi χ) ψp l z j) (gridPt lam kk) lam hchartΩ
      exact WilkG4c.Omega_mono_le S le_rfl hdegineq hsub
    · intro l hl
      obtain ⟨hψcube, hψcr⟩ := hψrest l hl
      have hχcr : ∀ j' : Fin n, ContDiffOn ℝ r (fun u : Fin n → ℝ => χ l (ψp l u) j')
          (openCube n) := fun j' => by
        simpa [engFam, hψp] using (hψcr ⟨(j' : ℕ), by omega⟩).1
      have hMcr : ContDiffOn ℝ r (fun u : Fin n → ℝ => (midFun lo hi χ) l (ψp l u)) (openCube n) := by
        simpa [engFam, hψp] using (hψcr ⟨n, by omega⟩).1
      have hWcr : ContDiffOn ℝ r (fun u : Fin n → ℝ => (widFun lo hi χ) l (ψp l u)) (openCube n) := by
        simpa [engFam, hψp] using (hψcr ⟨n + 1, by omega⟩).1
      have hχnm : ∀ j' : Fin n, ∀ m, m ≤ r → ∀ t ∈ openCube n,
          ‖iteratedFDeriv ℝ m (fun u : Fin n → ℝ => χ l (ψp l u) j') t‖ ≤ 1 := by
        intro j' m hm t ht
        simpa [engFam, hψp] using (hψcr ⟨(j' : ℕ), by omega⟩).2 m hm t ht
      have hMnm : ∀ m, m ≤ r → ∀ t ∈ openCube n,
          ‖iteratedFDeriv ℝ m (fun u : Fin n → ℝ => (midFun lo hi χ) l (ψp l u)) t‖ ≤ 1 := by
        intro m hm t ht
        simpa [engFam, hψp] using (hψcr ⟨n, by omega⟩).2 m hm t ht
      have hWnm : ∀ m, m ≤ r → ∀ t ∈ openCube n,
          ‖iteratedFDeriv ℝ m (fun u : Fin n → ℝ => (widFun lo hi χ) l (ψp l u)) t‖ ≤ 1 := by
        intro m hm t ht
        simpa [engFam, hψp] using (hψcr ⟨n + 1, by omega⟩).2 m hm t ht
      have hΦcd : ContDiffOn ℝ r
          (fun z : Fin (n + 1) → ℝ => cellChart χ (midFun lo hi χ) (widFun lo hi χ) ψp l z) (openCube (n + 1)) :=
        cellChart_contDiffOn χ ψp (midFun lo hi χ) (widFun lo hi χ) l hχcr hMcr hWcr
      have hopen : IsOpen (openCube (n + 1)) := isOpen_openCube_engine (n + 1)
      have hchartmem : ∀ x ∈ openCube (n + 1),
          (fun j => cellChart χ (midFun lo hi χ) (widFun lo hi χ) ψp l x j) ∈ openCube (n + 1) := by
        intro x hx
        have hinit : Fin.init x ∈ openCube n := fun i => hx i.castSucc
        have hψcube' : ψp l (Fin.init x) ∈ openCube n := hψcube (Fin.init x) hinit
        have hb : Fin.append l (χ l (ψp l (Fin.init x))) ∈ Fin.init '' κ :=
          hχfib l hl (ψp l (Fin.init x)) hψcube'
        obtain ⟨c, hc⟩ := (show ∃ c : ℝ,
            Fin.snoc (Fin.append l (χ l (ψp l (Fin.init x)))) c ∈ κ from by
          have h := hb; rw [hprojLast] at h; exact h)
        obtain ⟨hlo0, hlo1, hhi0, hhi1, hmid0, hmid1, hwid0, hwid1, hIoo, hsweep⟩ :=
          FibreEndsInterval κ hκcell hκI lo hi hlo (Fin.append l (χ l (ψp l (Fin.init x))))
            ⟨c, hc⟩
        refine cellChart_mem_openCube χ ψp (midFun lo hi χ) (widFun lo hi χ) l x hx
          (hχcube l hl (ψp l (Fin.init x)) hψcube')
          (lo (Fin.append l (χ l (ψp l (Fin.init x)))))
          (hi (Fin.append l (χ l (ψp l (Fin.init x))))) hlo0 hhi1 ?_ hmid0 hmid1 ?_ ?_
        · have hle : lo (Fin.append l (χ l (ψp l (Fin.init x)))) ≤ hi (Fin.append l (χ l (ψp l (Fin.init x)))) :=
            le_trans ((hlo (Fin.append l (χ l (ψp l (Fin.init x)))) ⟨c, hc⟩).1 c hc).1
              ((hlo (Fin.append l (χ l (ψp l (Fin.init x)))) ⟨c, hc⟩).1 c hc).2
          exact hle
        · simp only [midFun]
        · simp only [widFun]; ring
      have himage : ∀ x ∈ openCube (n + 1),
          Fin.append l (fun j => cellChart χ (midFun lo hi χ) (widFun lo hi χ) ψp l x j) ∈ κ := by
        intro x hx
        have hinit : Fin.init x ∈ openCube n := fun i => hx i.castSucc
        have hψcube' : ψp l (Fin.init x) ∈ openCube n := hψcube (Fin.init x) hinit
        have hb : Fin.append l (χ l (ψp l (Fin.init x))) ∈ Fin.init '' κ :=
          hχfib l hl (ψp l (Fin.init x)) hψcube'
        refine cellChart_mem_cell hκcell hκI lo hi hlo χ ψp (midFun lo hi χ) (widFun lo hi χ) l x hx hb ?_ ?_
        · simp only [midFun]
        · simp only [widFun]; ring
      refine ⟨?_, ?_⟩
      · intro t ht
        have hx'' : (fun i => (gridPt lam kk i + t i) / lam) ∈ openCube (n + 1) := by
          intro i
          have hki := hvbd i
          have hti := ht i
          constructor
          · apply div_pos _ (by linarith [hlam1])
            linarith [hki.1, hti.1]
          · rw [div_lt_one (by linarith [hlam1])]
            linarith [hki.2, hti.2]
        exact hchartmem _ hx''
      · intro i
        refine ⟨?_, ?_⟩
        · refine (hopen.contDiffOn_iff).mpr fun x hx => ?_
          have hx' : (fun i => (gridPt lam kk i + x i) / lam) ∈ openCube (n + 1) := by
            intro i
            have hki := hvbd i
            have hxi := hx i
            constructor
            · apply div_pos _ (by linarith [hlam1])
              linarith [hki.1, hxi.1]
            · rw [div_lt_one (by linarith [hlam1])]
              linarith [hki.2, hxi.2]
          have haff : ContDiffAt ℝ r
              (fun y : Fin (n + 1) → ℝ => fun i => (gridPt lam kk i + y i) / lam) x := by
            have hfun : (fun y : Fin (n + 1) → ℝ => fun i => (gridPt lam kk i + y i) / lam)
                = (fun y : Fin (n + 1) → ℝ => lam⁻¹ • (y + fun i => gridPt lam kk i)) := by
              funext y; ext i
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
              ring
            rw [hfun]
            fun_prop
          have hg : ContDiffAt ℝ r
              (fun z : Fin (n + 1) → ℝ => cellChart χ (midFun lo hi χ) (widFun lo hi χ) ψp l z)
              (fun i => (gridPt lam kk i + x i) / lam) :=
            hΦcd.contDiffAt (hopen.mem_nhds hx')
          have hinner : ContDiffAt ℝ r
              (fun y : Fin (n + 1) → ℝ =>
                cellChart χ (midFun lo hi χ) (widFun lo hi χ) ψp l (fun i => (gridPt lam kk i + y i) / lam)) x := by
            fun_prop
          have hFc : ContDiffAt ℝ r (F i l) (cellChart χ (midFun lo hi χ) (widFun lo hi χ) ψp l
              (fun i => (gridPt lam kk i + x i) / lam)) :=
            hcd i l hl _ (himage _ hx')
          exact ContDiffAt.comp x hFc hinner
        · intro m hm t ht
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · subst h0
            rw [norm_iteratedFDeriv_zero]
            have hx' : (fun i => (gridPt lam kk i + t i) / lam) ∈ openCube (n + 1) := by
              intro i
              have hki := hvbd i
              have hti := ht i
              constructor
              · apply div_pos _ (by linarith [hlam1])
                linarith [hki.1, hti.1]
              · rw [div_lt_one (by linarith [hlam1])]
                linarith [hki.2, hti.2]
            have hmem := hchartmem _ hx'
            rw [Real.norm_eq_abs, abs_of_pos (h01 i l hl _ hmem).1]
            exact le_of_lt (h01 i l hl _ hmem).2
          · have hr : 1 ≤ r := le_trans (Nat.succ_le_of_lt hpos) hm
            have hjet := hJet r χ ψp (midFun lo hi χ) (widFun lo hi χ) l hχcr hMcr hWcr hχnm hMnm hWnm
            have hvals : ∀ x ∈ openCube (n + 1), ∀ m', m' ≤ r →
                ‖iteratedFDeriv ℝ m' (F i l) (cellChart χ (midFun lo hi χ) (widFun lo hi χ) ψp l x)‖ ≤ 1 := by
              intro x hx m' hm'
              rcases Nat.eq_zero_or_pos m' with h0 | hpos'
              · subst h0
                rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
                  abs_of_pos (h01 i l hl _ (hchartmem x hx)).1]
                exact le_of_lt (h01 i l hl _ (hchartmem x hx)).2
              · exact hnorm i l hl (cellChart χ (midFun lo hi χ) (widFun lo hi χ) ψp l x)
                  (himage x hx) m' hm'
            exact hNorm r hr (F i l) (fun z : Fin (n + 1) → ℝ => cellChart χ (midFun lo hi χ) (widFun lo hi χ) ψp l z)
              lam (gridPt lam kk) (le_trans hlamc le_rfl)
              (fun x hx => hcd i l hl _ (himage x hx))
              (fun x hx => hΦcd.contDiffAt (hopen.mem_nhds hx))
              hchartmem hvals hjet hvbd m hm t ht
  -- ------------------------------------------------------------------ cover
  have hψdata : ∀ l ∈ Λ, ∀ t ∈ openCube n, ∃ ψ ∈ Ψ_ih, ∃ t' ∈ openCube n,
      ((fun j => ψ j l t') ∈ openCube n) ∧
      (∀ j : Fin n, |χ l (fun j' => ψ j' l t') j - χ l t j| < ε / 4) ∧
      |midFun lo hi χ l (fun j' => ψ j' l t') - midFun lo hi χ l t| < ε / 4 ∧
      |widFun lo hi χ l (fun j' => ψ j' l t') - widFun lo hi χ l t| < ε / 4 := by
    intro l hl t ht
    obtain ⟨ψ, hψmem, t', ht', hcov⟩ := hΨcov l hl t ht
    obtain ⟨hψΩ, hψrest⟩ := hΨOK ψ hψmem
    obtain ⟨hψcube, hψcr⟩ := hψrest l hl
    refine ⟨ψ, hψmem, t', ht', hψcube t' ht', ?_, ?_, ?_⟩
    · intro j
      have h := hcov ⟨(j : ℕ), by omega⟩
      have h3 : (engFam χ (midFun lo hi χ) (widFun lo hi χ) ⟨(j : ℕ), by omega⟩ l
          (fun j'' => ψ j'' l t')) = χ l (fun j'' => ψ j'' l t') j := by simp [engFam]
      have h4 : (engFam χ (midFun lo hi χ) (widFun lo hi χ) ⟨(j : ℕ), by omega⟩ l t) = χ l t j := by
        simp [engFam]
      rw [h3, h4] at h
      exact h
    · have h := hcov ⟨n, by omega⟩
      have h3 : (engFam χ (midFun lo hi χ) (widFun lo hi χ) ⟨n, by omega⟩ l
          (fun j'' => ψ j'' l t')) = (midFun lo hi χ) l (fun j'' => ψ j'' l t') := by simp [engFam]
      have h4 : (engFam χ (midFun lo hi χ) (widFun lo hi χ) ⟨n, by omega⟩ l t) = (midFun lo hi χ) l t := by
        simp [engFam]
      rw [h3, h4] at h
      exact h
    · have h := hcov ⟨n + 1, by omega⟩
      have h3 : (engFam χ (midFun lo hi χ) (widFun lo hi χ) ⟨n + 1, by omega⟩ l
          (fun j'' => ψ j'' l t')) = (widFun lo hi χ) l (fun j'' => ψ j'' l t') := by simp [engFam]
      have h4 : (engFam χ (midFun lo hi χ) (widFun lo hi χ) ⟨n + 1, by omega⟩ l t) = (widFun lo hi χ) l t := by
        simp [engFam]
      rw [h3, h4] at h
      exact h
  have hcover : ∀ l ∈ Λ, ∀ y : Fin (n + 1) → ℝ, Fin.append l y ∈ κ →
      ∃ φ ∈ Ψ_fin, ∃ t ∈ openCube (n + 1), ∀ j : Fin (n + 1), |φ j l t - y j| < ε := by
    rw [hΨfin]
    exact engineCover n p k Λ κ χ lo hi Ψ_ih lam Kg ε hε0 hε1 hlam1 hKg hκcell hκI hlo
      hχsurj hψdata
  exact ⟨Ψ_fin, hcard, hOK, hcover⟩

end Work.WilG4c
