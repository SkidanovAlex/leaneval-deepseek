import Mathlib
import Submission.Work.Diff.STE.flat.torus_uniqueness

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open MeasureTheory Set Filter
open scoped Topology Matrix

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ## Continuity of the spatial slice of the difference of the two nonlinearities -/

/-- The spatial jet of a smooth solution is continuous. -/
lemma continuous_jetM_slice {n : ℕ} {Φ : (Fin n → ℝ) × Jet n → MatC n}
    {T : ℝ} {u : ℝ → Torus n} (hu : SolvesOn Φ T u) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) :
    Continuous (fun x : Fin n → ℝ => jetM (u t) x) := by
  have h0 : Continuous (fun x : Fin n → ℝ => u t x) := by
    refine continuous_pi (fun i => continuous_pi (fun j => ?_))
    exact (contDiff_slice_of_contDiffOn (F := fun τ y => u τ y i j)
      (contDiffOn_entry_of_contDiffOn hu.1 i j) ht).continuous
  have h1 : Continuous (fun x : Fin n → ℝ => fun c : Fin n => pdM c (u t) x) := by
    refine continuous_pi (fun c => continuous_pi (fun i => continuous_pi (fun j => ?_)))
    exact (contDiff_slice_of_contDiffOn
      (F := fun τ y => pd c (fun z : Fin n → ℝ => u τ z i j) y)
      (contDiffOn_pd_slice (F := fun τ y => u τ y i j)
        (contDiffOn_entry_of_contDiffOn hu.1 i j) c) ht).continuous
  have h2 : Continuous (fun x : Fin n → ℝ => fun c d : Fin n =>
      pdM c (pdM d (u t)) x) := by
    refine continuous_pi (fun c => continuous_pi (fun d => continuous_pi (fun i =>
      continuous_pi (fun j => ?_))))
    exact (contDiff_slice_of_contDiffOn
      (F := fun τ y => pd c (fun z : Fin n → ℝ => pdM d (u τ) z i j) y)
      (contDiffOn_pd_slice (F := fun τ y => pdM d (u τ) y i j)
        (contDiffOn_pd_slice (F := fun τ y => u τ y i j)
          (contDiffOn_entry_of_contDiffOn hu.1 i j) d) c) ht).continuous
  simpa only [jetM] using h0.prodMk (h1.prodMk h2)

/-- The `x`-slice of `Φ (·, jet u)` is continuous where the metric matrix is positive definite. -/
lemma continuous_slice_Phi {n : ℕ} {Φ : (Fin n → ℝ) × Jet n → MatC n}
    (hshape : IsDeTurckNonlin Φ) {T : ℝ} {u : ℝ → Torus n} (hu : SolvesOn Φ T u)
    (hellu : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, PosDefM (u t x))
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) :
    Continuous (fun x : Fin n → ℝ => Φ (x, jetM (u t) x)) := by
  obtain ⟨hΦsm, -, -, -⟩ := hshape
  have hjet : Continuous (fun x : Fin n → ℝ => jetM (u t) x) := continuous_jetM_slice hu ht
  have hmap : Set.MapsTo (fun x : Fin n → ℝ => (x, jetM (u t) x)) Set.univ
      (Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0}) :=
    fun x _ => ⟨Set.mem_univ _, (Matrix.PosDef.det_pos (hellu t ht x)).ne'⟩
  have hc : ContinuousOn (fun x : Fin n → ℝ => Φ (x, jetM (u t) x)) Set.univ :=
    hΦsm.continuousOn.comp (continuous_id.prodMk hjet).continuousOn hmap
  exact continuousOn_univ.mp hc

/-- The spatial slice of the difference of the two nonlinearities is continuous. -/
lemma continuous_slice_PhiDiff_aux {n : ℕ}
    (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hshape : IsDeTurckNonlin Φ)
    {T : ℝ} (u v : ℝ → Torus n)
    (hu : SolvesOn Φ T u) (hv : SolvesOn Φ T v)
    (hellu : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, PosDefM (u t x))
    (hellv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, PosDefM (v t x))
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) (i j : Fin n) :
    Continuous (fun x : Fin n → ℝ =>
      (Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j) := by
  have hdiff : Continuous (fun x : Fin n → ℝ =>
      Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) :=
    (continuous_slice_Phi hshape hu hellu ht).sub (continuous_slice_Phi hshape hv hellv ht)
  exact (continuous_apply j).comp ((continuous_apply i).comp hdiff)

/-! ## Auxiliary facts about the `L²` pairing -/

/-- The `L²` pairing is bounded by the integral of the product of the norms. -/
lemma L2re_le_integral_norm_mul {ι : Type*} [Fintype ι] (f g : (ι → ℝ) → ℂ) :
    L2re f g ≤ ∫ x in unitCube (ι := ι), ‖f x‖ * ‖g x‖ := by
  have h1 : L2re f g ≤ ‖∫ x in unitCube (ι := ι), f x * star (g x)‖ := by
    simp only [L2re]
    exact Complex.re_le_norm _
  have h2 : ‖∫ x in unitCube (ι := ι), f x * star (g x)‖
      ≤ ∫ x in unitCube (ι := ι), ‖f x * star (g x)‖ := norm_integral_le_integral_norm _
  have h3 : (∫ x in unitCube (ι := ι), ‖f x * star (g x)‖)
      = ∫ x in unitCube (ι := ι), ‖f x‖ * ‖g x‖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, norm_star]
  linarith [h1, h2, h3]

/-- The `L²` pairing is additive in its first argument. -/
lemma L2re_add_slice {ι : Type*} [Fintype ι] {f₁ f₂ g : (ι → ℝ) → ℂ}
    (h1 : Integrable (fun x => f₁ x * star (g x)) (volume.restrict (unitCube (ι := ι))))
    (h2 : Integrable (fun x => f₂ x * star (g x)) (volume.restrict (unitCube (ι := ι)))) :
    L2re (fun x => f₁ x + f₂ x) g = L2re f₁ g + L2re f₂ g := by
  have hpt : (fun x : ι → ℝ => (f₁ x + f₂ x) * star (g x))
      = fun x => f₁ x * star (g x) + f₂ x * star (g x) := by
    funext x; rw [add_mul]
  have h3 : (∫ x in unitCube (ι := ι), (f₁ x + f₂ x) * star (g x))
      = (∫ x in unitCube (ι := ι), f₁ x * star (g x))
        + ∫ x in unitCube (ι := ι), f₂ x * star (g x) := by
    rw [hpt, integral_add h1 h2]
  simp only [L2re]
  rw [h3, Complex.add_re]

/-! ## The energy inequality -/

theorem uniqueness_energy_ineq {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    {T tstar : ℝ} (u v : ℝ → Work.Diff.STE.Flat.Torus n)
    (hu : Work.Diff.STE.Flat.SolvesOn Φ T u) (hv : Work.Diff.STE.Flat.SolvesOn Φ T v)
    (hellu : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, Work.Diff.STE.Flat.PosDefM (u t x))
    (hellv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, Work.Diff.STE.Flat.PosDefM (v t x))
    (htstarT : tstar < T)
    (M lamu K₁ CR : ℝ) (hM : 0 ≤ M) (hlamu : 0 < lamu) (hCR : 0 ≤ CR)
    (hbu : ∀ t ∈ Set.Ico (0 : ℝ) tstar,
      ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      (∀ i j, ‖u t x i j‖ ≤ M) ∧ (∀ c i j, ‖Work.Diff.STE.Flat.pdM c (u t) x i j‖ ≤ M) ∧
      (∀ c d i j, ‖Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u t)) x i j‖ ≤ M) ∧
      (∀ i j, ‖((Work.Diff.STE.Flat.reMat (u t x))⁻¹) i j‖ ≤ M))
    (hbv : ∀ t ∈ Set.Ico (0 : ℝ) tstar,
      ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      (∀ i j, ‖v t x i j‖ ≤ M) ∧ (∀ c i j, ‖Work.Diff.STE.Flat.pdM c (v t) x i j‖ ≤ M) ∧
      (∀ c d i j, ‖Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v t)) x i j‖ ≤ M) ∧
      (∀ i j, ‖((Work.Diff.STE.Flat.reMat (v t x))⁻¹) i j‖ ≤ M))
    (hellMu : ∀ t ∈ Set.Ico (0 : ℝ) tstar, ∀ x, ∀ ξ : Fin n → ℝ,
      lamu * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, Work.Diff.STE.Flat.reMat (u t x) i j * ξ i * ξ j)
    (hellMv : ∀ t ∈ Set.Ico (0 : ℝ) tstar, ∀ x, ∀ ξ : Fin n → ℝ,
      lamu * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, Work.Diff.STE.Flat.reMat (v t x) i j * ξ i * ξ j)
    (hellIu : ∀ t ∈ Set.Ico (0 : ℝ) tstar, ∀ x, ∀ ξ : Fin n → ℝ,
      lamu * ∑ i, (ξ i) ^ 2 ≤
        ∑ i, ∑ j, ((Work.Diff.STE.Flat.reMat (u t x))⁻¹) i j * ξ i * ξ j)
    (hK₁u : ∀ t ∈ Set.Ico (0 : ℝ) tstar, ∀ (c d i : Fin n) (x : Fin n → ℝ),
      |Work.Diff.STE.pdR i (fun y => ((Work.Diff.STE.Flat.reMat (u t y))⁻¹) c d) x| ≤ K₁)
    (hres : ∀ t ∈ Set.Ico (0 : ℝ) tstar,
      ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      ‖Φ (x, Work.Diff.STE.Flat.jetM (u t) x) - Φ (x, Work.Diff.STE.Flat.jetM (v t) x) -
          Work.Diff.STE.Flat.secOpFlat (u t x)
            (fun c d => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u t)) x -
              Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v t)) x)‖ ≤
        CR * ((∑ i, ∑ j, ‖u t x i j - v t x i j‖) +
          (∑ c, ∑ i, ∑ j,
            ‖Work.Diff.STE.Flat.pdM c (u t) x i j - Work.Diff.STE.Flat.pdM c (v t) x i j‖))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Ioo (0 : ℝ) tstar,
      (∑ i : Fin n, ∑ j : Fin n, 2 * ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ((Φ (x, Work.Diff.STE.Flat.jetM (u t) x) - Φ (x, Work.Diff.STE.Flat.jetM (v t) x)) i j
            * star (u t x i j - v t x i j)).re)
        ≤ K * (∑ i : Fin n, ∑ j : Fin n, ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
            ‖u t x i j - v t x i j‖ ^ 2) := by
  -- ## 1. the Gårding estimate for the inverse metric matrix of `u`
  have hmatu : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => reMat (u p.1 p.2) i j) (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun i j => contDiffOn_reMat_entry hu.1 i j
  have hdetu : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x, (reMat (u t x)).det ≠ 0 :=
    fun t ht x => (Matrix.PosDef.det_pos (hellu t ht x)).ne'
  have hinvu : ∀ c d, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => ((reMat (u p.1 p.2))⁻¹) c d)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun c d => contDiffOn_matrixInv_entry hmatu hdetu c d
  have hperRe : ∀ t ∈ Set.Ico (0:ℝ) tstar,
      Periodic1 (fun x : Fin n → ℝ => reMat (u t x)) := by
    intro t ht i x
    have h : u t (x + Pi.single i 1) = u t x :=
      hu.2.1 t ⟨ht.1, lt_trans ht.2 htstarT⟩ i x
    show reMat (u t (x + Pi.single i 1)) = reMat (u t x)
    rw [h]
  obtain ⟨Cg, hCg, hgard⟩ := garding_param
      (A := fun (b : {τ : ℝ // τ ∈ Set.Ico (0:ℝ) tstar}) (c d : Fin n) (x : Fin n → ℝ) =>
        ((reMat (u b.1 x))⁻¹) c d)
      (fun b c d => contDiff_slice_of_contDiffOn_real
        (F := fun τ y => ((reMat (u τ y))⁻¹) c d)
        (hinvu c d) ⟨b.2.1, lt_trans b.2.2 htstarT⟩)
      (fun b c d => Periodic1.matrixInv_entry (hperRe b.1 b.2) c d)
      (fun b c d x => by
        have h := (hellu b.1 ⟨b.2.1, lt_trans b.2.2 htstarT⟩ x).inv.isHermitian.apply c d
        simpa using h.symm)
      lamu hlamu (fun b x ξ => hellIu b.1 b.2 x ξ) K₁
      (fun b c d i x => hK₁u b.1 b.2 c d i x)
  -- ## 2. the numerical constants
  set N : ℝ := (n : ℝ) with hNdef
  have hNnn : (0:ℝ) ≤ N := by rw [hNdef]; positivity
  set dlt : ℝ := lamu / (8 * (N * N * N * N * N * CR + 1)) with hdltdef
  have hdltpos : 0 < dlt := by
    rw [hdltdef]; exact div_pos hlamu (by positivity)
  have hdltineq : 2 * (N * N * CR) * dlt * (N * N * N) ≤ lamu / 2 := by
    have h1 : 2 * (N * N * CR) * dlt * (N * N * N)
        = lamu * (N * N * N * N * N * CR / (4 * (N * N * N * N * N * CR + 1))) := by
      rw [hdltdef]; field_simp; ring
    rw [h1]
    have hnn : (0:ℝ) ≤ N * N * N * N * N * CR := by positivity
    have h2 : N * N * N * N * N * CR / (4 * (N * N * N * N * N * CR + 1)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (N * N * N * N * N * CR + 1))]
      linarith
    have h3 : lamu * (N * N * N * N * N * CR / (4 * (N * N * N * N * N * CR + 1)))
        ≤ lamu * (1 / 4) := mul_le_mul_of_nonneg_left h2 hlamu.le
    linarith [h3]
  set Kk : ℝ := 2 * Cg + 2 * (N * N * CR) * (1 + 1 / (4 * dlt)) * (N * N) with hKkdef
  refine ⟨Kk, ?_, ?_⟩
  · rw [hKkdef]
    have h1 : (0:ℝ) ≤ 2 * (N * N * CR) * (1 + 1 / (4 * dlt)) * (N * N) := by positivity
    linarith
  · -- ## 3. the estimate at a fixed time
    intro t ht
    have htT : t ∈ Set.Ico (0:ℝ) T := ⟨ht.1.le, lt_trans ht.2 htstarT⟩
    have htI : t ∈ Set.Ico (0:ℝ) tstar := ⟨ht.1.le, ht.2⟩
    -- abbreviations
    set W : Fin n → Fin n → (Fin n → ℝ) → ℂ := fun i j x => u t x i j - v t x i j with hWdef
    set P : Fin n → Fin n → (Fin n → ℝ) → ℂ := fun i j x =>
      (Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j with hPdef
    set secG : Fin n → Fin n → (Fin n → ℝ) → ℂ := fun i j x =>
      ∑ c : Fin n, ∑ d : Fin n, (((reMat (u t x))⁻¹) c d : ℂ) * pd c (pd d (W i j)) x
      with hsecGdef
    set Rf : Fin n → Fin n → (Fin n → ℝ) → ℂ := fun i j x => P i j x - secG i j x with hRfdef
    set A : (Fin n → ℝ) → ℝ := fun x => ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ with hAdef
    set B : (Fin n → ℝ) → ℝ := fun x => ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
      ‖pdM c (u t) x i j - pdM c (v t) x i j‖ with hBdef
    set Em : ℝ := ∑ i : Fin n, ∑ j : Fin n, ∫ x in unitCube, ‖W i j x‖ ^ 2 with hEmdef
    set Gr : ℝ := ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
      ∫ x in unitCube, ‖pd c (W i j) x‖ ^ 2 with hGrdef
    set IAB : ℝ := ∫ x in unitCube, (A x + B x) * A x with hIABdef
    have hmeas : MeasurableSet (unitCube (ι := Fin n)) :=
      MeasurableSet.pi Set.finite_univ.countable (fun i _ => measurableSet_Ioc)
    -- smoothness / continuity of the slices
    have hWd : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (W i j) := by
      intro i j
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2 i j - v p.1 p.2 i j)
          (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
        (contDiffOn_entry_of_contDiffOn hu.1 i j).sub
          (contDiffOn_entry_of_contDiffOn hv.1 i j)
      have hs := contDiff_slice_of_contDiffOn (F := fun τ y => u τ y i j - v τ y i j) h1 htT
      have heq : W i j = fun y : Fin n → ℝ => u t y i j - v t y i j := by
        funext x; simp only [hWdef]
      rw [heq]; exact hs
    have hsliceu : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => u t x i j) :=
      fun i j => contDiff_slice_of_contDiffOn (F := fun τ y => u τ y i j)
        (contDiffOn_entry_of_contDiffOn hu.1 i j) htT
    have hslicev : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => v t x i j) :=
      fun i j => contDiff_slice_of_contDiffOn (F := fun τ y => v τ y i j)
        (contDiffOn_entry_of_contDiffOn hv.1 i j) htT
    have hpdWd1 : ∀ (c i j : Fin n),
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => pd c (W i j) x) :=
      fun c i j => contDiff_pd (hWd i j) c
    have hpdWd2 : ∀ (c d i j : Fin n),
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => pd c (pd d (W i j)) x) :=
      fun c d i j => contDiff_pd (contDiff_pd (hWd i j) d) c
    have hpdu : ∀ (c i j : Fin n),
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => pdM c (u t) x i j) := by
      intro c i j
      have h := contDiff_slice_of_contDiffOn
        (F := fun τ y => pd c (fun z : Fin n → ℝ => u τ z i j) y)
        (contDiffOn_pd_slice (F := fun τ y => u τ y i j)
          (contDiffOn_entry_of_contDiffOn hu.1 i j) c) htT
      simpa only [pdM] using h
    have hpdv : ∀ (c i j : Fin n),
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => pdM c (v t) x i j) := by
      intro c i j
      have h := contDiff_slice_of_contDiffOn
        (F := fun τ y => pd c (fun z : Fin n → ℝ => v τ z i j) y)
        (contDiffOn_pd_slice (F := fun τ y => v τ y i j)
          (contDiffOn_entry_of_contDiffOn hv.1 i j) c) htT
      simpa only [pdM] using h
    have hWcont : ∀ i j, Continuous (W i j) := fun i j => (hWd i j).continuous
    have hAcont : Continuous A := by
      have hAeq : A = fun x : Fin n → ℝ => ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ := by
        funext x; simp only [hAdef]
      rw [hAeq]
      refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
      exact (hWcont i j).norm
    have hBcont : Continuous B := by
      have hBeq : B = fun x : Fin n → ℝ => ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          ‖pdM c (u t) x i j - pdM c (v t) x i j‖ := by
        funext x; simp only [hBdef]
      rw [hBeq]
      refine continuous_finsetSum _ (fun c _ => continuous_finsetSum _ (fun i _ =>
        continuous_finsetSum _ (fun j _ => ?_)))
      exact (((hpdu c i j).continuous).sub ((hpdv c i j).continuous)).norm
    have hPcont : ∀ i j, Continuous (P i j) := by
      intro i j
      have h := continuous_slice_PhiDiff_aux Φ hshape u v hu hv hellu hellv htT i j
      have hPeq : P i j = fun x : Fin n → ℝ =>
          (Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j := by
        funext x; simp only [hPdef]
      rw [hPeq]; exact h
    have hsecGcont : ∀ i j, Continuous (secG i j) := by
      intro i j
      have hseq : secG i j = fun x : Fin n → ℝ =>
          ∑ c : Fin n, ∑ d : Fin n,
            (((reMat (u t x))⁻¹) c d : ℂ) * pd c (pd d (W i j)) x := by
        funext x; simp only [hsecGdef]
      rw [hseq]
      refine continuous_finsetSum _ (fun c _ => continuous_finsetSum _ (fun d _ => ?_))
      refine Continuous.mul ?_ ?_
      · refine Complex.continuous_ofReal.comp ?_
        exact (contDiff_slice_of_contDiffOn_real
          (F := fun τ y => ((reMat (u τ y))⁻¹) c d) (hinvu c d) htT).continuous
      · exact (hpdWd2 c d i j).continuous
    have hRfcont : ∀ i j, Continuous (Rf i j) := by
      intro i j
      have hReq : Rf i j = fun x : Fin n → ℝ => P i j x - secG i j x := by
        funext x; simp only [hRfdef]
      rw [hReq]
      exact (hPcont i j).sub (hsecGcont i j)
    -- ## 3a. the Gårding sum
    have hgard_sum : (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (secG i j) (W i j))
        ≤ -lamu * Gr + 2 * Cg * Em := by
      have hpt : ∀ i j : Fin n, 2 * L2re (secG i j) (W i j)
          ≤ -(lamu * (∑ c : Fin n, ∫ x in unitCube, ‖pd c (W i j) x‖ ^ 2))
            + 2 * Cg * (∫ x in unitCube, ‖W i j x‖ ^ 2) := by
        intro i j
        have hsm : ContDiff ℝ 2 (W i j) := (hWd i j).of_le (by simp)
        have hper : Periodic1 (W i j) := by
          intro k y
          have h1 : u t (y + Pi.single k 1) i j = u t y i j :=
            Periodic1.entry (hu.2.1 t htT) i j k y
          have h2 : v t (y + Pi.single k 1) i j = v t y i j :=
            Periodic1.entry (hv.2.1 t htT) i j k y
          show W i j (y + Pi.single k 1) = W i j y
          simp only [hWdef]
          rw [h1, h2]
        have h := hgard ⟨t, htI⟩ (W i j) hsm hper
        have hseq : secG i j = fun x : Fin n → ℝ =>
            ∑ c : Fin n, ∑ d : Fin n,
              (((reMat (u t x))⁻¹) c d : ℂ) * pd c (pd d (W i j)) x := by
          funext x; simp only [hsecGdef]
        rw [hseq]
        linarith [h]
      calc (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (secG i j) (W i j))
          ≤ ∑ i : Fin n, ∑ j : Fin n,
              (-(lamu * (∑ c : Fin n, ∫ x in unitCube, ‖pd c (W i j) x‖ ^ 2))
                + 2 * Cg * (∫ x in unitCube, ‖W i j x‖ ^ 2)) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpt i j))
        _ = -lamu * Gr + 2 * Cg * Em := by
            rw [hGrdef, hEmdef]
            simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum, neg_mul]
    -- ## 3b. the residual
    have hsecPeq : ∀ i j x, secG i j x
        = secOpFlat (u t x)
            (fun c d => pdM c (pdM d (u t)) x - pdM c (pdM d (v t)) x) i j := by
      intro i j x
      have hpdW : ∀ (c d : Fin n), pd c (pd d (W i j)) x
          = pdM c (pdM d (u t)) x i j - pdM c (pdM d (v t)) x i j := by
        intro c d
        have h := congrFun (pd_pd_sub_fun c d
          (contDiff_slice_of_contDiffOn (F := fun τ y => u τ y i j)
            (contDiffOn_entry_of_contDiffOn hu.1 i j) htT)
          (contDiff_slice_of_contDiffOn (F := fun τ y => v τ y i j)
            (contDiffOn_entry_of_contDiffOn hv.1 i j) htT)) x
        simpa only [hWdef, pdM] using h
      have hseq : secG i j x = ∑ c : Fin n, ∑ d : Fin n,
          (((reMat (u t x))⁻¹) c d : ℂ) * pd c (pd d (W i j)) x := by
        simp only [hsecGdef]
      rw [hseq]
      simp only [secOpFlat, Pi.sub_apply]
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
      rw [hpdW c d]
    have hPeq : ∀ i j, P i j = fun x => secG i j x + Rf i j x := by
      intro i j
      funext x
      have hRfeq : Rf i j x = P i j x - secG i j x := by simp only [hRfdef]
      rw [hRfeq]; ring
    have hRpt : ∀ i j x, x ∈ unitCube (ι := Fin n) →
        ‖Rf i j x‖ ≤ CR * (A x + B x) := by
      intro i j x hx
      have hxIcc : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1) :=
        fun k _ => ⟨le_of_lt (Set.mem_pi.mp hx k (Set.mem_univ k)).1,
          (Set.mem_pi.mp hx k (Set.mem_univ k)).2⟩
      have hresx := hres t htI x hxIcc
      have hmati : (Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x) -
            secOpFlat (u t x)
              (fun c d => pdM c (pdM d (u t)) x - pdM c (pdM d (v t)) x)) i j
          = Rf i j x := by
        have hthis : Rf i j x = (Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j
            - secG i j x := by
          simp only [hRfdef, hPdef]
        rw [hthis, hsecPeq i j x]
        simp only [Pi.sub_apply]
      rw [← hmati]
      refine le_trans (norm_entry_le_norm_matC _ i j) ?_
      have hAeq : (∑ i : Fin n, ∑ j : Fin n, ‖u t x i j - v t x i j‖) = A x := by
        simp only [hAdef, hWdef]
      have hBeq : (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
            ‖pdM c (u t) x i j - pdM c (v t) x i j‖) = B x := by
        simp only [hBdef]
      rw [hAeq, hBeq] at hresx
      exact hresx
    have hRsum : (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (Rf i j) (W i j))
        ≤ 2 * (N * N * CR) * IAB := by
      have hkey : ∀ i j : Fin n, 2 * L2re (Rf i j) (W i j) ≤ 2 * (CR * IAB) := by
        intro i j
        have h1 : L2re (Rf i j) (W i j) ≤ ∫ x in unitCube, ‖Rf i j x‖ * ‖W i j x‖ :=
          L2re_le_integral_norm_mul _ _
        have h2 : (∫ x in unitCube, ‖Rf i j x‖ * ‖W i j x‖)
            ≤ ∫ x in unitCube, CR * (A x + B x) * A x := by
          refine setIntegral_mono_on
            (integrableOn_unitCube_of_continuous_real ((hRfcont i j).norm.mul (hWcont i j).norm))
            (integrableOn_unitCube_of_continuous_real
              ((continuous_const.mul (hAcont.add hBcont)).mul hAcont))
            hmeas (fun x hx => ?_)
          have hRx := hRpt i j x hx
          have hWx : ‖W i j x‖ ≤ A x := by
            have h1 : ‖W i j x‖ ≤ ∑ j' : Fin n, ‖W i j' x‖ :=
              single_le_sum_univ (f := fun j' : Fin n => ‖W i j' x‖) (fun j' => norm_nonneg _) j
            have h2 : (∑ j' : Fin n, ‖W i j' x‖)
                ≤ ∑ i' : Fin n, ∑ j' : Fin n, ‖W i' j' x‖ :=
              single_le_sum_univ (f := fun i' : Fin n => ∑ j' : Fin n, ‖W i' j' x‖)
                (fun i' => Finset.sum_nonneg (fun j' _ => norm_nonneg _)) i
            have hAeq : A x = ∑ i' : Fin n, ∑ j' : Fin n, ‖W i' j' x‖ := by
              simp only [hAdef]
            rw [hAeq]
            exact le_trans h1 h2
          have hA0 : 0 ≤ A x := by
            have hAeq : A x = ∑ i' : Fin n, ∑ j' : Fin n, ‖W i' j' x‖ := by
              simp only [hAdef]
            rw [hAeq]
            exact Finset.sum_nonneg (fun i' _ => Finset.sum_nonneg (fun j' _ => norm_nonneg _))
          have hB0 : 0 ≤ B x := by
            have hBeq : B x = ∑ c : Fin n, ∑ i' : Fin n, ∑ j' : Fin n,
                ‖pdM c (u t) x i' j' - pdM c (v t) x i' j'‖ := by
              simp only [hBdef]
            rw [hBeq]
            exact Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun i' _ =>
              Finset.sum_nonneg (fun j' _ => norm_nonneg _)))
          have hCRAB : 0 ≤ CR * (A x + B x) := mul_nonneg hCR (by linarith)
          calc ‖Rf i j x‖ * ‖W i j x‖
              ≤ (CR * (A x + B x)) * A x := mul_le_mul hRx hWx (norm_nonneg _) hCRAB
            _ = CR * (A x + B x) * A x := by ring
        have h3 : (∫ x in unitCube, CR * (A x + B x) * A x) = CR * IAB := by
          rw [hIABdef]
          rw [show (fun x : Fin n → ℝ => CR * (A x + B x) * A x)
              = fun x => CR * ((A x + B x) * A x) from funext (fun x => by ring)]
          rw [integral_const_mul]
        linarith [h1, h2, h3]
      calc (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (Rf i j) (W i j))
          ≤ ∑ i : Fin n, ∑ j : Fin n, 2 * (CR * IAB) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hkey i j))
        _ = 2 * (N * N * CR) * IAB := by
            rw [sum_sum_const (n := n), hNdef]
            ring
    -- ## 3c. the pointwise Cauchy-Schwarz bounds and the Young inequality
    have hEcont : Continuous (fun x : Fin n → ℝ =>
        ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ ^ 2) := by
      refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
      exact (hWcont i j).norm.pow 2
    have hGcont : Continuous (fun x : Fin n → ℝ =>
        ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n, ‖pd c (W i j) x‖ ^ 2) := by
      refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        continuous_finsetSum _ (fun c _ => ?_)))
      exact (hpdWd1 c i j).continuous.norm.pow 2
    have hcard : (Fintype.card (Fin n) : ℝ) = N := by rw [Fintype.card_fin, hNdef]
    have hA2pt : ∀ x, A x ^ 2 ≤ N * (N * (∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ ^ 2)) := by
      intro x
      have h1 : (∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖) ^ 2
          ≤ N * ∑ i : Fin n, (∑ j : Fin n, ‖W i j x‖) ^ 2 := by
        have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun i : Fin n => ∑ j : Fin n, ‖W i j x‖)
        rw [Finset.card_univ, hcard] at hh
        exact hh
      have h2 : ∀ i : Fin n, (∑ j : Fin n, ‖W i j x‖) ^ 2
          ≤ N * ∑ j : Fin n, ‖W i j x‖ ^ 2 := by
        intro i
        have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun j : Fin n => ‖W i j x‖)
        rw [Finset.card_univ, hcard] at hh
        exact hh
      have hAeq : A x = ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ := by simp only [hAdef]
      rw [hAeq]
      calc (∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖) ^ 2
          ≤ N * ∑ i : Fin n, (∑ j : Fin n, ‖W i j x‖) ^ 2 := h1
        _ ≤ N * ∑ i : Fin n, (N * ∑ j : Fin n, ‖W i j x‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h2 i)) hNnn
        _ = N * (N * ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ ^ 2) := by
            simp only [Finset.mul_sum]
    have hB2pt : ∀ x, B x ^ 2
        ≤ N * (N * (N * ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
            ‖pd c (W i j) x‖ ^ 2)) := by
      intro x
      have hcomm : (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖ ^ 2)
          = ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n, ‖pd c (W i j) x‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
      have hpd : ∀ (c i j : Fin n), ‖pdM c (u t) x i j - pdM c (v t) x i j‖
          = ‖pd c (W i j) x‖ := by
        intro c i j
        have hdu : Differentiable ℝ (fun y : Fin n → ℝ => u t y i j) :=
          (hsliceu i j).differentiable (by simp)
        have hdv : Differentiable ℝ (fun y : Fin n → ℝ => v t y i j) :=
          (hslicev i j).differentiable (by simp)
        have h := congrFun (pd_sub_fun c hdu hdv) x
        have h2 : pdM c (u t) x i j - pdM c (v t) x i j
            = pd c (fun y : Fin n → ℝ => u t y i j - v t y i j) x := by
          simpa only [pdM] using h.symm
        have h3 : pd c (W i j) x = pd c (fun y : Fin n → ℝ => u t y i j - v t y i j) x := by
          simp only [hWdef]
        rw [h2, h3]
      have h1 : (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2
          ≤ N * ∑ c : Fin n, (∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2 := by
        have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun c : Fin n => ∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖)
        rw [Finset.card_univ, hcard] at hh
        exact hh
      have h2 : ∀ c : Fin n, (∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2
          ≤ N * ∑ i : Fin n, (∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2 := by
        intro c
        have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun i : Fin n => ∑ j : Fin n, ‖pd c (W i j) x‖)
        rw [Finset.card_univ, hcard] at hh
        exact hh
      have h3 : ∀ (c i : Fin n), (∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2
          ≤ N * ∑ j : Fin n, ‖pd c (W i j) x‖ ^ 2 := by
        intro c i
        have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun j : Fin n => ‖pd c (W i j) x‖)
        rw [Finset.card_univ, hcard] at hh
        exact hh
      have hBeq : B x = ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖ := by
        rw [hBdef]
        refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ =>
          Finset.sum_congr rfl (fun j _ => hpd c i j)))
      rw [hBeq]
      calc (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2
          ≤ N * ∑ c : Fin n, (∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2 := h1
        _ ≤ N * ∑ c : Fin n, (N * ∑ i : Fin n, (∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => h2 c)) hNnn
        _ ≤ N * ∑ c : Fin n, (N * ∑ i : Fin n, (N * ∑ j : Fin n,
              ‖pd c (W i j) x‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => ?_)) hNnn
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h3 c i)) hNnn
        _ = N * (N * (N * ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              ‖pd c (W i j) x‖ ^ 2)) := by
            simp only [Finset.mul_sum]
        _ = N * (N * (N * ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
              ‖pd c (W i j) x‖ ^ 2)) := by
            rw [hcomm]
    have hIntW : ∀ i j : Fin n, Integrable (fun x : Fin n → ℝ => ‖W i j x‖ ^ 2)
        (volume.restrict (unitCube (ι := Fin n))) :=
      fun i j => integrableOn_unitCube_of_continuous_real ((hWcont i j).norm.pow 2)
    have hIntpdW : ∀ (c i j : Fin n),
        Integrable (fun x : Fin n → ℝ => ‖pd c (W i j) x‖ ^ 2)
          (volume.restrict (unitCube (ι := Fin n))) :=
      fun c i j => integrableOn_unitCube_of_continuous_real ((hpdWd1 c i j).continuous.norm.pow 2)
    have hEint : (∫ x in unitCube, ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ ^ 2) = Em := by
      rw [hEmdef]
      have hI1 : ∀ i : Fin n, Integrable (fun x : Fin n → ℝ => ∑ j : Fin n, ‖W i j x‖ ^ 2)
          (volume.restrict (unitCube (ι := Fin n))) := fun i =>
        integrableOn_unitCube_of_continuous_real
          (continuous_finsetSum Finset.univ (fun j _ => (hWcont i j).norm.pow 2))
      rw [integral_finset_sum Finset.univ (fun i _ => hI1 i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finset_sum Finset.univ (fun j _ => hIntW i j)]
    have hGrint : (∫ x in unitCube, ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
        ‖pd c (W i j) x‖ ^ 2) = Gr := by
      rw [hGrdef]
      have hI1 : ∀ i : Fin n, Integrable (fun x : Fin n → ℝ =>
          ∑ j : Fin n, ∑ c : Fin n, ‖pd c (W i j) x‖ ^ 2)
          (volume.restrict (unitCube (ι := Fin n))) := fun i =>
        integrableOn_unitCube_of_continuous_real
          (continuous_finsetSum Finset.univ (fun j _ =>
            continuous_finsetSum Finset.univ (fun c _ => (hpdWd1 c i j).continuous.norm.pow 2)))
      rw [integral_finset_sum Finset.univ (fun i _ => hI1 i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hI2 : ∀ j : Fin n, Integrable (fun x : Fin n → ℝ =>
          ∑ c : Fin n, ‖pd c (W i j) x‖ ^ 2)
          (volume.restrict (unitCube (ι := Fin n))) := fun j =>
        integrableOn_unitCube_of_continuous_real
          (continuous_finsetSum Finset.univ (fun c _ => (hpdWd1 c i j).continuous.norm.pow 2))
      rw [integral_finset_sum Finset.univ (fun j _ => hI2 j)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [integral_finset_sum Finset.univ (fun c _ => hIntpdW c i j)]
    have hA2int : (∫ x in unitCube, A x ^ 2) ≤ N * (N * Em) := by
      have hstep : (∫ x in unitCube, A x ^ 2)
          ≤ ∫ x in unitCube, N * (N * (∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ ^ 2)) := by
        refine setIntegral_mono_on (integrableOn_unitCube_of_continuous_real (hAcont.pow 2))
          (integrableOn_unitCube_of_continuous_real
            (continuous_const.mul (continuous_const.mul hEcont))) hmeas
          (fun x _ => hA2pt x)
      calc (∫ x in unitCube, A x ^ 2)
          ≤ ∫ x in unitCube, N * (N * (∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ ^ 2)) := hstep
        _ = N * (N * Em) := by
            rw [integral_const_mul, integral_const_mul, hEint]
    have hB2int : (∫ x in unitCube, B x ^ 2) ≤ N * (N * (N * Gr)) := by
      have hstep : (∫ x in unitCube, B x ^ 2)
          ≤ ∫ x in unitCube, N * (N * (N * (∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
              ‖pd c (W i j) x‖ ^ 2))) := by
        refine setIntegral_mono_on (integrableOn_unitCube_of_continuous_real (hBcont.pow 2))
          (integrableOn_unitCube_of_continuous_real
            (continuous_const.mul (continuous_const.mul (continuous_const.mul hGcont))))
          hmeas (fun x _ => hB2pt x)
      calc (∫ x in unitCube, B x ^ 2)
          ≤ ∫ x in unitCube, N * (N * (N * (∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
              ‖pd c (W i j) x‖ ^ 2))) := hstep
        _ = N * (N * (N * Gr)) := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul, hGrint]
    have hYoung : ∀ x, A x * B x ≤ A x ^ 2 / (4 * dlt) + dlt * B x ^ 2 := by
      intro x
      have h1 : 0 < 4 * dlt := by linarith [hdltpos]
      have h2 : 4 * dlt * (A x * B x) ≤ A x ^ 2 + 4 * dlt * (dlt * B x ^ 2) := by
        nlinarith [sq_nonneg (A x - 2 * dlt * B x)]
      calc A x * B x ≤ (A x ^ 2 + 4 * dlt * (dlt * B x ^ 2)) / (4 * dlt) :=
            (le_div_iff₀ h1).mpr (by nlinarith [h2])
        _ = A x ^ 2 / (4 * dlt) + dlt * B x ^ 2 := by
            have hne : (4 * dlt) ≠ 0 := ne_of_gt h1
            field_simp
    have hAB_int : IAB ≤ (1 + 1 / (4 * dlt)) * (N * (N * Em))
        + dlt * (N * (N * (N * Gr))) := by
      rw [hIABdef]
      have hpt : ∀ x, (A x + B x) * A x
          ≤ (1 + 1 / (4 * dlt)) * A x ^ 2 + dlt * B x ^ 2 := by
        intro x
        have h1 : (A x + B x) * A x = A x ^ 2 + A x * B x := by ring
        rw [h1]
        have h2 : (1 + 1 / (4 * dlt)) * A x ^ 2 = A x ^ 2 + A x ^ 2 / (4 * dlt) := by
          have hne : (4 * dlt) ≠ 0 := ne_of_gt (by linarith [hdltpos])
          field_simp
        rw [h2]
        linarith [hYoung x]
      have hstep : (∫ x in unitCube, (A x + B x) * A x)
          ≤ ∫ x in unitCube, ((1 + 1 / (4 * dlt)) * A x ^ 2 + dlt * B x ^ 2) := by
        refine setIntegral_mono_on
          (integrableOn_unitCube_of_continuous_real ((hAcont.add hBcont).mul hAcont))
          (integrableOn_unitCube_of_continuous_real
            ((continuous_const.mul (hAcont.pow 2)).add (continuous_const.mul (hBcont.pow 2))))
          hmeas (fun x _ => hpt x)
      have hsplit : (∫ x in unitCube, ((1 + 1 / (4 * dlt)) * A x ^ 2 + dlt * B x ^ 2))
          = (1 + 1 / (4 * dlt)) * (∫ x in unitCube, A x ^ 2)
            + dlt * (∫ x in unitCube, B x ^ 2) := by
        rw [integral_add
            (f := fun x : Fin n → ℝ => (1 + 1 / (4 * dlt)) * A x ^ 2)
            (g := fun x : Fin n → ℝ => dlt * B x ^ 2)
            (integrableOn_unitCube_of_continuous_real (continuous_const.mul (hAcont.pow 2)))
            (integrableOn_unitCube_of_continuous_real (continuous_const.mul (hBcont.pow 2))),
          integral_const_mul, integral_const_mul]
      rw [hsplit] at hstep
      have h3 : (1 + 1 / (4 * dlt)) * (∫ x in unitCube, A x ^ 2)
          ≤ (1 + 1 / (4 * dlt)) * (N * (N * Em)) :=
        mul_le_mul_of_nonneg_left hA2int (by positivity)
      have h4 : dlt * (∫ x in unitCube, B x ^ 2) ≤ dlt * (N * (N * (N * Gr))) :=
        mul_le_mul_of_nonneg_left hB2int hdltpos.le
      linarith [hstep, h3, h4]
    -- ## 3d. assembly
    have hsplit2 : (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (P i j) (W i j))
        = (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (secG i j) (W i j))
          + (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (Rf i j) (W i j)) := by
      have h1 : ∀ i j : Fin n, 2 * L2re (P i j) (W i j)
          = 2 * L2re (secG i j) (W i j) + 2 * L2re (Rf i j) (W i j) := by
        intro i j
        have hint1 : Integrable (fun x : Fin n → ℝ => secG i j x * star (W i j x))
            (volume.restrict (unitCube (ι := Fin n))) :=
          integrableOn_unitCube_of_continuous ((hsecGcont i j).mul (hWcont i j).star)
        have hint2 : Integrable (fun x : Fin n → ℝ => Rf i j x * star (W i j x))
            (volume.restrict (unitCube (ι := Fin n))) :=
          integrableOn_unitCube_of_continuous ((hRfcont i j).mul (hWcont i j).star)
        have hadd := L2re_add_slice (f₁ := secG i j) (f₂ := Rf i j) (g := W i j) hint1 hint2
        rw [hPeq i j, hadd]
        ring
      calc (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (P i j) (W i j))
          = ∑ i : Fin n, ∑ j : Fin n, (2 * L2re (secG i j) (W i j)
              + 2 * L2re (Rf i j) (W i j)) :=
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h1 i j))
        _ = _ := by simp only [Finset.sum_add_distrib]
    have hmain : (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (P i j) (W i j)) ≤ Kk * Em := by
      rw [hsplit2]
      have hGrnn : 0 ≤ Gr := by
        have hGeq : Gr = ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
            ∫ x in unitCube, ‖pd c (W i j) x‖ ^ 2 := hGrdef
        rw [hGeq]
        exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
          Finset.sum_nonneg (fun c _ => integral_nonneg (fun x => by positivity))))
      have hstep : 2 * (N * N * CR) * IAB
          ≤ 2 * (N * N * CR) * ((1 + 1 / (4 * dlt)) * (N * (N * Em))
              + dlt * (N * (N * (N * Gr)))) :=
        mul_le_mul_of_nonneg_left hAB_int (by positivity)
      nlinarith [hgard_sum, hRsum, hstep, hGrnn, hdltineq, hKkdef, hNnn]
    -- ## 3e. identification with the goal
    have hconv : ∀ i j : Fin n,
        (∫ x in unitCube, (((Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j)
          * star (u t x i j - v t x i j)).re) = L2re (P i j) (W i j) := by
      intro i j
      have heq : (fun x : Fin n → ℝ => (((Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j)
            * star (u t x i j - v t x i j)).re)
          = fun x => (P i j x * star (W i j x)).re := by
        funext x; simp only [hPdef, hWdef]
      rw [heq]
      have hint : Integrable (fun x : Fin n → ℝ => P i j x * star (W i j x))
          (volume.restrict (unitCube (ι := Fin n))) :=
        integrableOn_unitCube_of_continuous ((hPcont i j).mul (hWcont i j).star)
      have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM hint
      simpa only [L2re, Complex.reCLM_apply] using h
    have hEmeq : Em = ∑ i : Fin n, ∑ j : Fin n,
        ∫ x in unitCube, ‖u t x i j - v t x i j‖ ^ 2 := by
      simp only [hEmdef, hWdef]
    calc (∑ i : Fin n, ∑ j : Fin n, 2 * ∫ x in unitCube,
          ((Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j
            * star (u t x i j - v t x i j)).re)
        = ∑ i : Fin n, ∑ j : Fin n, 2 * L2re (P i j) (W i j) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [hconv i j]
      _ ≤ Kk * Em := hmain
      _ = Kk * (∑ i : Fin n, ∑ j : Fin n, ∫ x in unitCube,
            ‖u t x i j - v t x i j‖ ^ 2) := by rw [hEmeq]

end Work.Diff.STE.flat
