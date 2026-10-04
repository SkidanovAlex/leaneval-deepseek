import Mathlib
import Submission.Work.Diff.STE.flat.uniqueness_energy_ineq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

/-!
## Roadmap (for the prover)

This is the energy/Grönwall argument for a *linear* parabolic system on the flat torus: a
symmetric uniformly elliptic coefficient family `a` and a residual `r := P - (a-part)` obeying a
Lipschitz bound in the `L¹`-type norms `A x = Σ_{ij} ‖w t x i j‖`, `B x = Σ_{cij} ‖pdM c (w t) x i j‖`
of `w` and its first derivatives imply `w ≡ 0` on `Ico 0 tstar`, given the zero initial datum and
the equation `∂_t w = P`.

Adapt the proof of `Work.Diff.STE.flat.uniqueness_energy_ineq`
(`Submission/Work/Diff/STE/flat/uniqueness_energy_ineq.lean`, sorry-free, importable) and the tail
of `Work.Diff.STE.flat.torus_uniqueness` (`Submission/Work/Diff/STE/flat/torus_uniqueness.lean`):

1. Set `W i j x := w t x i j`, `Em := Σ_{ij} ∫ ‖W i j‖²`, `Gr := Σ_{ij} Σ_c ∫ ‖pd c (W i j)‖²`,
   `secG i j x := Σ_{cd} ((a t x c d : ℂ) * pd c (pd d (W i j)) x)` and `Rf := (P t) - secG`.
   Copy the estimates 3a (Gårding), 3b (residual), 3c (Cauchy–Schwarz/Young) verbatim, with
   `P` in place of `Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)` and `w` in place of `u - v`;
   the identity `P = secG + Rf` is definitional, and `hres` is the only new input
   (use `norm_entry_le_norm_matC` to pass from the matrix norm to entries).
   For Gårding use `Work.Diff.STE.flat.garding_param` with parameter `β := {t // t ∈ Ico 0 tstar}`,
   coefficient family `A b c d x := a b.1 x c d`; its hypotheses are `ha_entry` (via
   `contDiff_slice_of_contDiffOn_real`), `haper` (use `Periodic1` for entries), `hasym`, `hell`,
   `hK₁` (this is `hdK`).
   Conclusion: `∃ K ≥ 0, ∀ t ∈ Ioo 0 tstar, Σ_{ij} 2 * L2re (P t x i j) (W i j) ≤ K * Em t`.
2. Differentiating the energy: use the proved
   `Work.Diff.STE.flat.hasDerivAt_integral_normSq_slice` (from `torus_uniqueness.lean`) applied to
   `W := fun s x => w s x i j`, `W' := fun s x => P s x i j`, with `hderiv` (restricted to `Ioo 0 T`)
   to obtain `HasDerivWithinAt E (Ed t) (Icc 0 tstar) t` for `t ∈ Ioo 0 tstar` with
   `E t := Σ_{ij} ∫ ‖w t x i j‖²`, `Ed t := Σ_{ij} 2 * ∫ (P t x i j * star (w t x i j)).re`;
   `hPcont` (joint continuity of `P` on the strip, as needed by
   `hasDerivAt_integral_normSq_slice`) gives the continuity of `P t` for each `t`.
3. Grönwall: `Work.Diff.STE.flat.eq_zero_of_deriv_le` (from `torus_uniqueness.lean`) with
   `hE0 : E 0 = 0` (from `hw0`) and `E ≥ 0` gives `E t₀ = 0` for all `t₀ ∈ Ico 0 tstar`.
4. Pointwise conclusion: for `t₀ ∈ Ico 0 tstar` and each `(i,j)` the slice
   `x ↦ w t₀ x i j` is continuous (from `hwsmooth` via `contDiff_slice_of_contDiffOn`) and
   `∫ ‖·‖² = 0` over the cube, so it vanishes on the closed cube
   (`Work.Diff.STE.flat.eq_zero_on_closedCube_of_integral_normSq_eq_zero`); `hwper` makes it
   `1`-periodic, so it vanishes everywhere (`Work.Diff.STE.eq_zero_of_eq_zero_on_closedCube`).
-/

open Work.Diff.STE.Flat
open MeasureTheory Set Filter
open scoped Topology Matrix

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ## Differentiating the energy -/

/-- The time derivative of the `L²` energy of a solution of the linear parabolic system. -/
lemma linEnergyDeriv {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (w : ℝ → Torus n) (P : ℝ → (Fin n → ℝ) → MatC n)
    (hwsmooth : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => w p.1 p.2 i j) (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (hPcont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => P p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (hderiv : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Fin n → ℝ,
      HasDerivWithinAt (fun s : ℝ => w s x) (P t x) (Set.Ico (0:ℝ) T) t)
    {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) T) :
    HasDerivAt (fun s : ℝ => ∑ i : Fin n, ∑ j : Fin n,
        ∫ x in unitCube (ι := Fin n), ‖w s x i j‖ ^ 2)
      (∑ i : Fin n, ∑ j : Fin n, 2 * ∫ x in unitCube (ι := Fin n),
        (P t x i j * star (w t x i j)).re) t := by
  have hW : ∀ i j, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => w p.1 p.2 i j)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := fun i j => (hwsmooth i j).continuousOn
  have hW' : ∀ i j, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => P p.1 p.2 i j)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
    intro i j
    have hc : Continuous (fun z : MatC n => z i j) := by fun_prop
    exact hc.comp_continuousOn hPcont
  have hd : ∀ s ∈ Set.Ico (0:ℝ) T, ∀ x : Fin n → ℝ, ∀ i j : Fin n,
      HasDerivWithinAt (fun r : ℝ => w r x i j) (P s x i j) (Set.Ico (0:ℝ) T) s := by
    intro s hs x i j
    have h4 := hasDerivWithinAt_pi.mp (hderiv s hs x) i
    have h5 := hasDerivWithinAt_pi.mp h4 j
    simpa using h5
  have hentry : ∀ i j : Fin n, HasDerivAt
      (fun s : ℝ => ∫ x in unitCube (ι := Fin n), ‖w s x i j‖ ^ 2)
      (2 * ∫ x in unitCube (ι := Fin n), (P t x i j * star (w t x i j)).re) t :=
    fun i j => hasDerivAt_integral_normSq_slice (n := n) hn
      (W := fun r x => w r x i j) (W' := fun r x => P r x i j) T
      (hW i j) (hW' i j) (fun s hs x => hd s hs x i j) ht
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ => hentry i j))
  have hfun : (∑ i : Fin n, ∑ j : Fin n,
      fun s => ∫ x in unitCube (ι := Fin n), ‖w s x i j‖ ^ 2)
        = fun s => ∑ i : Fin n, ∑ j : Fin n,
          ∫ x in unitCube (ι := Fin n), ‖w s x i j‖ ^ 2 := by
    funext s
    simp only [Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum

/-! ## Continuity of the energy at `0⁺` -/

/-- The energy of a solution of the linear system is continuous at `0⁺`. -/
lemma linEnergyCont0 {n : ℕ} (hn : 1 ≤ n)
    {T tstar : ℝ} (htstarT : tstar < T)
    (w : ℝ → Torus n) (P : ℝ → (Fin n → ℝ) → MatC n)
    (hwsmooth : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => w p.1 p.2 i j) (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (hPcont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => P p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (hderiv : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Fin n → ℝ,
      HasDerivWithinAt (fun s : ℝ => w s x) (P t x) (Set.Ico (0:ℝ) T) t)
    (hw0 : ∀ x i j, w 0 x i j = 0) :
    ContinuousWithinAt (fun s : ℝ => ∑ i : Fin n, ∑ j : Fin n,
        ∫ x in unitCube (ι := Fin n), ‖w s x i j‖ ^ 2)
      (Set.Icc (0:ℝ) tstar) 0 := by
  set E : ℝ → ℝ := fun s => ∑ i : Fin n, ∑ j : Fin n,
      ∫ x in unitCube (ι := Fin n), ‖w s x i j‖ ^ 2 with hEdef
  have hE0 : E 0 = 0 := by
    simp only [hEdef]
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    have hzero : (fun x : Fin n → ℝ => ‖w 0 x i j‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext x; rw [hw0 x i j]; simp
    rw [hzero]; simp
  have hEnn : ∀ s : ℝ, 0 ≤ E s := by
    intro s
    simp only [hEdef]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      integral_nonneg (fun x => sq_nonneg _)))
  -- the uniform bound on `P` on the closed strip `[0, tstar] × cube`
  obtain ⟨BP, hBP⟩ := (isCompact_Icc.prod
      (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc))).exists_bound_of_continuousOn
    (hPcont.mono (fun p hp => ⟨⟨hp.1.1, lt_of_le_of_lt hp.1.2 htstarT⟩,
      Set.mem_univ p.2⟩))
  set BL : ℝ := max BP 0 with hBLdef
  have hBLnn : 0 ≤ BL := by rw [hBLdef]; exact le_max_right _ _
  have hBLEP : BP ≤ BL := by rw [hBLdef]; exact le_max_left _ _
  -- the pointwise Lipschitz bound on the cube
  have hptw : ∀ s ∈ Set.Icc (0:ℝ) tstar, ∀ x : Fin n → ℝ,
      (∀ k, x k ∈ Set.Icc (0:ℝ) 1) → ∀ i j, ‖w s x i j‖ ≤ BL * s := by
    intro s hs x hx i j
    have hder : ∀ r ∈ Set.Icc (0:ℝ) s,
        HasDerivWithinAt (fun ρ : ℝ => w ρ x i j) (P r x i j) (Set.Icc (0:ℝ) s) r := by
      intro r hr
      have hrT : r ∈ Set.Ico (0:ℝ) T :=
        ⟨hr.1, lt_of_le_of_lt (le_trans hr.2 hs.2) htstarT⟩
      have h5 : HasDerivWithinAt (fun ρ : ℝ => w ρ x i j) (P r x i j) (Set.Ico (0:ℝ) T) r := by
        have h4 := hasDerivWithinAt_pi.mp (hderiv r hrT x) i
        have h6 := hasDerivWithinAt_pi.mp h4 j
        simpa using h6
      exact h5.mono (fun y hy => ⟨hy.1, lt_of_le_of_lt (le_trans hy.2 hs.2) htstarT⟩)
    have hbd : ∀ r ∈ Set.Ico (0:ℝ) s, ‖P r x i j‖ ≤ BL := by
      intro r hr
      have h1 : ‖P r x i j‖ ≤ ‖P r x‖ := norm_entry_le_norm_matC _ i j
      have h2 : ‖P r x‖ ≤ BP := hBP (r, x) ⟨⟨hr.1, le_trans (le_of_lt hr.2) hs.2⟩,
        fun k _ => hx k⟩
      linarith
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun ρ : ℝ => w ρ x i j) (f' := fun ρ : ℝ => P ρ x i j)
      (a := 0) (b := s) (C := BL) hder hbd s ⟨hs.1, le_rfl⟩
    have h0eq : w 0 x i j = 0 := hw0 x i j
    rw [h0eq, sub_zero, sub_zero] at hmvt
    exact hmvt
  -- hence the energy bound
  have hEmem : ∀ s ∈ Set.Icc (0:ℝ) tstar, E s ≤ (n : ℝ) * ((n : ℝ) * (BL * s) ^ 2) := by
    intro s hs
    have h1 : E s ≤ ∑ i : Fin n, ∑ j : Fin n, (BL * s) ^ 2 := by
      simp only [hEdef]
      refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
      have hcontc : Continuous (fun x : Fin n → ℝ => ‖w s x i j‖ ^ 2) := by
        have h1' : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => w s x i j) :=
          contDiff_slice_of_contDiffOn (F := fun ρ y => w ρ y i j) (hwsmooth i j)
            ⟨hs.1, lt_of_le_of_lt hs.2 htstarT⟩
        exact (h1'.continuous.norm.pow 2)
      have hvol : (volume : Measure (Fin n → ℝ)).real (unitCube (ι := Fin n)) = 1 := by
        show (((volume : Measure (Fin n → ℝ)) (unitCube (ι := Fin n))).toReal) = 1
        rw [unitCube, Real.volume_pi_Ioc]; simp
      have hcmp := setIntegral_mono_on (f := fun x : Fin n → ℝ => ‖w s x i j‖ ^ 2)
        (g := fun _ : Fin n → ℝ => (BL * s) ^ 2)
        (integrableOn_unitCube_of_continuous_real hcontc)
        (integrableOn_unitCube_of_continuous_real continuous_const)
        (MeasurableSet.pi Set.finite_univ.countable (fun i _ => measurableSet_Ioc))
        (fun x hx => by
          have hle := hptw s hs x (fun k => ⟨le_of_lt (hx k (Set.mem_univ k)).1,
            (hx k (Set.mem_univ k)).2⟩) i j
          have hBs : 0 ≤ BL * s := mul_nonneg hBLnn hs.1
          nlinarith [hle, norm_nonneg (w s x i j), hBs])
      calc (∫ x in unitCube (ι := Fin n), ‖w s x i j‖ ^ 2)
          ≤ ∫ x in unitCube (ι := Fin n), (BL * s) ^ 2 := hcmp
        _ = (BL * s) ^ 2 := by rw [setIntegral_const, hvol, one_smul]
    calc E s ≤ ∑ i : Fin n, ∑ j : Fin n, (BL * s) ^ 2 := h1
      _ = (n : ℝ) * ((n : ℝ) * (BL * s) ^ 2) := by rw [sum_sum_const]
  -- squeeze
  have hsq : Tendsto (fun s : ℝ => (n : ℝ) * ((n : ℝ) * (BL * s) ^ 2))
      (𝓝[Set.Icc (0:ℝ) tstar] 0) (𝓝 0) := by
    have hcont : Continuous (fun s : ℝ => (n : ℝ) * ((n : ℝ) * (BL * s) ^ 2)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have htend : Tendsto E (𝓝[Set.Icc (0:ℝ) tstar] 0) (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall hEnn)
      (Filter.eventually_of_mem self_mem_nhdsWithin hEmem) hsq
  rw [ContinuousWithinAt, hE0]
  exact htend

/-! ## The fixed-time energy inequality -/

/-- The fixed-time energy inequality for the linear parabolic system. -/
lemma linEnergyStep {n : ℕ} (hn : 1 ≤ n)
    {T tstar : ℝ} (htstarT : tstar < T)
    (a : ℝ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (w : ℝ → Torus n)
    (P : ℝ → (Fin n → ℝ) → MatC n)
    (ha_entry : ∀ c d, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => a p.1 p.2 c d) (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (haper : ∀ t ∈ Set.Ico (0:ℝ) T, Periodic1 (a t))
    (hasym : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x (c d : Fin n), a t x c d = a t x d c)
    (hwsmooth : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => w p.1 p.2 i j) (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (hwper : ∀ t ∈ Set.Ico (0:ℝ) T, Periodic1 (w t))
    (hPcont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => P p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (lam K₁ CR : ℝ) (hlam : 0 < lam) (hK₁ : 0 ≤ K₁) (hCR : 0 ≤ CR)
    (hell : ∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ x : Fin n → ℝ, ∀ ξ : Fin n → ℝ,
      lam * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, a t x c d * ξ c * ξ d)
    (hdK : ∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ (c d i : Fin n) (x : Fin n → ℝ),
      |pdR i (fun y => a t y c d) x| ≤ K₁)
    (hres : ∀ t ∈ Set.Ico (0:ℝ) tstar,
      ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1),
      ‖P t x - (fun i j => ∑ c, ∑ d,
          ((a t x c d : ℂ) * pd c (pd d (fun y => w t y i j)) x))‖
        ≤ CR * ((∑ i, ∑ j, ‖w t x i j‖) + (∑ c, ∑ i, ∑ j,
            ‖pdM c (w t) x i j‖))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Ioo (0:ℝ) tstar,
      (∑ i : Fin n, ∑ j : Fin n, 2 * ∫ x in unitCube (ι := Fin n),
          (P t x i j * star (w t x i j)).re)
        ≤ K * (∑ i : Fin n, ∑ j : Fin n, ∫ x in unitCube (ι := Fin n),
            ‖w t x i j‖ ^ 2) := by
  -- ## 1. the Gårding estimate for the coefficient family `a`
  obtain ⟨Cg, hCg, hgard⟩ := garding_param
      (A := fun (b : {τ : ℝ // τ ∈ Set.Ico (0:ℝ) tstar}) (c d : Fin n) (x : Fin n → ℝ) =>
        a b.1 x c d)
      (fun b c d => contDiff_slice_of_contDiffOn_real
        (F := fun τ y => a τ y c d) (ha_entry c d) ⟨b.2.1, lt_trans b.2.2 htstarT⟩)
      (fun b c d i x => by
        have h := haper b.1 ⟨b.2.1, lt_trans b.2.2 htstarT⟩ i x
        exact congrFun (congrFun h c) d)
      (fun b c d x => hasym b.1 ⟨b.2.1, lt_trans b.2.2 htstarT⟩ x c d)
      lam hlam (fun b x ξ => hell b.1 b.2 x ξ) K₁
      (fun b c d i x => hdK b.1 b.2 c d i x)
  -- ## 2. the numerical constants
  set N : ℝ := (n : ℝ) with hNdef
  have hNnn : (0:ℝ) ≤ N := by rw [hNdef]; positivity
  set dlt : ℝ := lam / (8 * (N * N * N * N * N * CR + 1)) with hdltdef
  have hdltpos : 0 < dlt := by
    rw [hdltdef]; exact div_pos hlam (by positivity)
  have hdltineq : 2 * (N * N * CR) * dlt * (N * N * N) ≤ lam / 2 := by
    have h1 : 2 * (N * N * CR) * dlt * (N * N * N)
        = lam * (N * N * N * N * N * CR / (4 * (N * N * N * N * N * CR + 1))) := by
      rw [hdltdef]; field_simp; ring
    rw [h1]
    have hnn : (0:ℝ) ≤ N * N * N * N * N * CR := by positivity
    have h2 : N * N * N * N * N * CR / (4 * (N * N * N * N * N * CR + 1)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (N * N * N * N * N * CR + 1))]
      linarith
    have h3 : lam * (N * N * N * N * N * CR / (4 * (N * N * N * N * N * CR + 1)))
        ≤ lam * (1 / 4) := mul_le_mul_of_nonneg_left h2 hlam.le
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
    set W : Fin n → Fin n → (Fin n → ℝ) → ℂ := fun i j x => w t x i j with hWdef
    set Q : Fin n → Fin n → (Fin n → ℝ) → ℂ := fun i j x => P t x i j with hQdef
    set secG : Fin n → Fin n → (Fin n → ℝ) → ℂ := fun i j x =>
      ∑ c : Fin n, ∑ d : Fin n, ((a t x c d : ℂ) * pd c (pd d (W i j)) x) with hsecGdef
    set Rf : Fin n → Fin n → (Fin n → ℝ) → ℂ := fun i j x => Q i j x - secG i j x with hRfdef
    set A : (Fin n → ℝ) → ℝ := fun x => ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ with hAdef
    set B : (Fin n → ℝ) → ℝ := fun x => ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
      ‖pdM c (w t) x i j‖ with hBdef
    set Em : ℝ := ∑ i : Fin n, ∑ j : Fin n, ∫ x in unitCube, ‖W i j x‖ ^ 2 with hEmdef
    set Gr : ℝ := ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
      ∫ x in unitCube, ‖pd c (W i j) x‖ ^ 2 with hGrdef
    set IAB : ℝ := ∫ x in unitCube, (A x + B x) * A x with hIABdef
    have hmeas : MeasurableSet (unitCube (ι := Fin n)) :=
      MeasurableSet.pi Set.finite_univ.countable (fun i _ => measurableSet_Ioc)
    -- smoothness / continuity of the slices
    have hWd : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (W i j) := by
      intro i j
      have hs := contDiff_slice_of_contDiffOn (F := fun τ y => w τ y i j) (hwsmooth i j) htT
      have heq : W i j = fun y : Fin n → ℝ => w t y i j := by
        funext x; simp only [hWdef]
      rw [heq]; exact hs
    have hpdWd1 : ∀ (c i j : Fin n),
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => pd c (W i j) x) :=
      fun c i j => contDiff_pd (hWd i j) c
    have hpdWd2 : ∀ (c d i j : Fin n),
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => pd c (pd d (W i j)) x) :=
      fun c d i j => contDiff_pd (contDiff_pd (hWd i j) d) c
    have hWcont : ∀ i j, Continuous (W i j) := fun i j => (hWd i j).continuous
    have hpdw : ∀ (c i j : Fin n),
        Continuous (fun x : Fin n → ℝ => pdM c (w t) x i j) := by
      intro c i j
      have h := contDiff_slice_of_contDiffOn
        (F := fun τ y => pd c (fun z : Fin n → ℝ => w τ z i j) y)
        (contDiffOn_pd_slice (F := fun τ y => w τ y i j) (hwsmooth i j) c) htT
      have heq : (fun x : Fin n → ℝ => pdM c (w t) x i j)
          = fun x => pd c (fun z : Fin n → ℝ => w t z i j) x := by
        funext x; rfl
      rw [heq]; exact h.continuous
    have hAcont : Continuous A := by
      have hAeq : A = fun x : Fin n → ℝ => ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ := by
        funext x; simp only [hAdef]
      rw [hAeq]
      refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
      exact (hWcont i j).norm
    have hBcont : Continuous B := by
      have hBeq : B = fun x : Fin n → ℝ => ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          ‖pdM c (w t) x i j‖ := by
        funext x; simp only [hBdef]
      rw [hBeq]
      refine continuous_finsetSum _ (fun c _ => continuous_finsetSum _ (fun i _ =>
        continuous_finsetSum _ (fun j _ => ?_)))
      exact (hpdw c i j).norm
    have hQcont : ∀ i j, Continuous (Q i j) := by
      intro i j
      have hslice : Continuous (fun x : Fin n → ℝ => P t x i j) := by
        have hc : Continuous (fun z : MatC n => z i j) := by fun_prop
        have hproj : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => P p.1 p.2 i j)
            (Set.Ico (0:ℝ) T ×ˢ Set.univ) := hc.comp_continuousOn hPcont
        have h2 := hproj.comp (s := Set.univ) (t := Set.Ico (0:ℝ) T ×ˢ Set.univ)
          (f := fun y : Fin n → ℝ => (t, y))
          (continuousOn_const.prodMk continuousOn_id)
          (fun y _ => ⟨htT, Set.mem_univ y⟩)
        have h3 : ((fun p : ℝ × (Fin n → ℝ) => P p.1 p.2 i j) ∘ fun y : Fin n → ℝ => (t, y))
            = fun y => P t y i j := rfl
        rw [h3, continuousOn_univ] at h2
        exact h2
      have hQeq : Q i j = fun x : Fin n → ℝ => P t x i j := by
        funext x; simp only [hQdef]
      rw [hQeq]; exact hslice
    have hsecGcont : ∀ i j, Continuous (secG i j) := by
      intro i j
      have hseq : secG i j = fun x : Fin n → ℝ =>
          ∑ c : Fin n, ∑ d : Fin n, ((a t x c d : ℂ) * pd c (pd d (W i j)) x) := by
        funext x; simp only [hsecGdef]
      rw [hseq]
      refine continuous_finsetSum _ (fun c _ => continuous_finsetSum _ (fun d _ => ?_))
      refine Continuous.mul ?_ ?_
      · refine Complex.continuous_ofReal.comp ?_
        exact (contDiff_slice_of_contDiffOn_real
          (F := fun τ y => a τ y c d) (ha_entry c d) htT).continuous
      · exact (hpdWd2 c d i j).continuous
    have hRfcont : ∀ i j, Continuous (Rf i j) := by
      intro i j
      have hReq : Rf i j = fun x : Fin n → ℝ => Q i j x - secG i j x := by
        funext x; simp only [hRfdef]
      rw [hReq]
      exact (hQcont i j).sub (hsecGcont i j)
    -- ## 3a. the Gårding sum
    have hgard_sum : (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (secG i j) (W i j))
        ≤ -lam * Gr + 2 * Cg * Em := by
      have hpt : ∀ i j : Fin n, 2 * L2re (secG i j) (W i j)
          ≤ -(lam * (∑ c : Fin n, ∫ x in unitCube, ‖pd c (W i j) x‖ ^ 2))
            + 2 * Cg * (∫ x in unitCube, ‖W i j x‖ ^ 2) := by
        intro i j
        have hsm : ContDiff ℝ 2 (W i j) := (hWd i j).of_le (by simp)
        have hper : Periodic1 (W i j) := by
          intro k y
          have h := hwper t htT k y
          simpa only [hWdef] using congrFun (congrFun h i) j
        have h := hgard ⟨t, htI⟩ (W i j) hsm hper
        have hseq : secG i j = fun x : Fin n → ℝ =>
            ∑ c : Fin n, ∑ d : Fin n, ((a t x c d : ℂ) * pd c (pd d (W i j)) x) := by
          funext x; simp only [hsecGdef]
        rw [hseq]
        linarith [h]
      calc (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (secG i j) (W i j))
          ≤ ∑ i : Fin n, ∑ j : Fin n,
              (-(lam * (∑ c : Fin n, ∫ x in unitCube, ‖pd c (W i j) x‖ ^ 2))
                + 2 * Cg * (∫ x in unitCube, ‖W i j x‖ ^ 2)) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpt i j))
        _ = -lam * Gr + 2 * Cg * Em := by
            rw [hGrdef, hEmdef]
            simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum, neg_mul]
    -- ## 3b. the residual
    have hQsum : ∀ i j, Q i j = fun x => secG i j x + Rf i j x := by
      intro i j
      funext x
      have hRfeq : Rf i j x = Q i j x - secG i j x := by simp only [hRfdef]
      rw [hRfeq]; ring
    have hRpt : ∀ i j x, x ∈ unitCube (ι := Fin n) → ‖Rf i j x‖ ≤ CR * (A x + B x) := by
      intro i j x hx
      have hxIcc : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1) :=
        fun k _ => ⟨le_of_lt (Set.mem_pi.mp hx k (Set.mem_univ k)).1,
          (Set.mem_pi.mp hx k (Set.mem_univ k)).2⟩
      have hresx := hres t htI x hxIcc
      have hmati : (P t x - (fun i j => ∑ c : Fin n, ∑ d : Fin n,
            ((a t x c d : ℂ) * pd c (pd d (fun y => w t y i j)) x))) i j = Rf i j x := by
        simp only [hRfdef, hQdef, hsecGdef, hWdef, Pi.sub_apply]
      rw [← hmati]
      refine le_trans (norm_entry_le_norm_matC _ i j) ?_
      have hAeq : (∑ i : Fin n, ∑ j : Fin n, ‖w t x i j‖) = A x := by
        simp only [hAdef, hWdef]
      have hBeq : (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
            ‖pdM c (w t) x i j‖) = B x := by
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
            have hAeq : A x = ∑ i' : Fin n, ∑ j' : Fin n, ‖W i' j' x‖ := by
              simp only [hAdef]
            rw [hAeq]
            refine le_trans (single_le_sum_univ (f := fun j' : Fin n => ‖W i j' x‖)
              (fun j' => norm_nonneg _) j) ?_
            exact single_le_sum_univ (f := fun i' : Fin n => ∑ j' : Fin n, ‖W i' j' x‖)
              (fun i' => Finset.sum_nonneg (fun j' _ => norm_nonneg _)) i
          have hA0 : 0 ≤ A x := by
            have hAeq : A x = ∑ i' : Fin n, ∑ j' : Fin n, ‖W i' j' x‖ := by
              simp only [hAdef]
            rw [hAeq]
            exact Finset.sum_nonneg (fun i' _ => Finset.sum_nonneg (fun j' _ => norm_nonneg _))
          have hB0 : 0 ≤ B x := by
            have hBeq : B x = ∑ c : Fin n, ∑ i' : Fin n, ∑ j' : Fin n,
                ‖pdM c (w t) x i' j'‖ := by
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
      have hpd : ∀ (c i j : Fin n), ‖pdM c (w t) x i j‖ = ‖pd c (W i j) x‖ := by
        intro c i j
        have h1 : pdM c (w t) x i j = pd c (fun y : Fin n → ℝ => w t y i j) x := rfl
        have h2 : pd c (W i j) x = pd c (fun y : Fin n → ℝ => w t y i j) x := by
          simp only [hWdef]
        rw [h1, h2]
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
    have hsplit2 : (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (Q i j) (W i j))
        = (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (secG i j) (W i j))
          + (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (Rf i j) (W i j)) := by
      have h1 : ∀ i j : Fin n, 2 * L2re (Q i j) (W i j)
          = 2 * L2re (secG i j) (W i j) + 2 * L2re (Rf i j) (W i j) := by
        intro i j
        have hint1 : Integrable (fun x : Fin n → ℝ => secG i j x * star (W i j x))
            (volume.restrict (unitCube (ι := Fin n))) :=
          integrableOn_unitCube_of_continuous ((hsecGcont i j).mul (hWcont i j).star)
        have hint2 : Integrable (fun x : Fin n → ℝ => Rf i j x * star (W i j x))
            (volume.restrict (unitCube (ι := Fin n))) :=
          integrableOn_unitCube_of_continuous ((hRfcont i j).mul (hWcont i j).star)
        have hadd := L2re_add_slice (f₁ := secG i j) (f₂ := Rf i j) (g := W i j) hint1 hint2
        rw [hQsum i j, hadd]
        ring
      calc (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (Q i j) (W i j))
          = ∑ i : Fin n, ∑ j : Fin n, (2 * L2re (secG i j) (W i j)
              + 2 * L2re (Rf i j) (W i j)) :=
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h1 i j))
        _ = _ := by simp only [Finset.sum_add_distrib]
    have hmain : (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (Q i j) (W i j)) ≤ Kk * Em := by
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
        (∫ x in unitCube, (P t x i j * star (w t x i j)).re) = L2re (Q i j) (W i j) := by
      intro i j
      have heq : (fun x : Fin n → ℝ => (P t x i j * star (w t x i j)).re)
          = fun x => (Q i j x * star (W i j x)).re := by
        funext x; simp only [hQdef, hWdef]
      rw [heq]
      have hint : Integrable (fun x : Fin n → ℝ => Q i j x * star (W i j x))
          (volume.restrict (unitCube (ι := Fin n))) :=
        integrableOn_unitCube_of_continuous ((hQcont i j).mul (hWcont i j).star)
      have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM hint
      simpa only [L2re, Complex.reCLM_apply] using h
    have hEmeq : Em = ∑ i : Fin n, ∑ j : Fin n,
        ∫ x in unitCube, ‖w t x i j‖ ^ 2 := by
      simp only [hEmdef, hWdef]
    calc (∑ i : Fin n, ∑ j : Fin n, 2 * ∫ x in unitCube,
          (P t x i j * star (w t x i j)).re)
        = ∑ i : Fin n, ∑ j : Fin n, 2 * L2re (Q i j) (W i j) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [hconv i j]
      _ ≤ Kk * Em := hmain
      _ = Kk * (∑ i : Fin n, ∑ j : Fin n, ∫ x in unitCube, ‖w t x i j‖ ^ 2) := by rw [hEmeq]

theorem linEnergyZero {n : ℕ} (hn : 1 ≤ n)
    {T tstar : ℝ} (htstarT : tstar < T)
    (a : ℝ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (w : ℝ → Work.Diff.STE.Flat.Torus n)
    (P : ℝ → (Fin n → ℝ) → Work.Diff.STE.Flat.MatC n)
    (ha_entry : ∀ c d, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => a p.1 p.2 c d) (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (haper : ∀ t ∈ Set.Ico (0:ℝ) T, Work.Diff.STE.Periodic1 (a t))
    (hasym : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x (c d : Fin n), a t x c d = a t x d c)
    (hwsmooth : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => w p.1 p.2 i j) (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (hwper : ∀ t ∈ Set.Ico (0:ℝ) T, Work.Diff.STE.Periodic1 (w t))
    (hPcont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => P p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (hderiv : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Fin n → ℝ,
      HasDerivWithinAt (fun s : ℝ => w s x) (P t x) (Set.Ico (0:ℝ) T) t)
    (hw0 : ∀ x i j, w 0 x i j = 0)
    (lam K₁ CR : ℝ) (hlam : 0 < lam) (hK₁ : 0 ≤ K₁) (hCR : 0 ≤ CR)
    (hell : ∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ x : Fin n → ℝ, ∀ ξ : Fin n → ℝ,
      lam * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, a t x c d * ξ c * ξ d)
    (hdK : ∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ (c d i : Fin n) (x : Fin n → ℝ),
      |Work.Diff.STE.pdR i (fun y => a t y c d) x| ≤ K₁)
    (hres : ∀ t ∈ Set.Ico (0:ℝ) tstar,
      ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1),
      ‖P t x - (fun i j => ∑ c, ∑ d,
          ((a t x c d : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d (fun y => w t y i j)) x))‖
        ≤ CR * ((∑ i, ∑ j, ‖w t x i j‖) + (∑ c, ∑ i, ∑ j,
            ‖Work.Diff.STE.Flat.pdM c (w t) x i j‖))) :
    ∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ (x : Fin n → ℝ) (i j : Fin n), w t x i j = 0 := by
  obtain ⟨K, hK, hineq⟩ := linEnergyStep hn htstarT a w P ha_entry haper hasym hwsmooth hwper
    hPcont lam K₁ CR hlam hK₁ hCR hell hdK hres
  set E : ℝ → ℝ := fun s => ∑ i : Fin n, ∑ j : Fin n,
      ∫ x in unitCube (ι := Fin n), ‖w s x i j‖ ^ 2 with hEdef
  set Ed : ℝ → ℝ := fun s => ∑ i : Fin n, ∑ j : Fin n, 2 *
      ∫ x in unitCube (ι := Fin n), (P s x i j * star (w s x i j)).re with hEddef
  have hEnn : ∀ s : ℝ, 0 ≤ E s := by
    intro s
    simp only [hEdef]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      integral_nonneg (fun x => sq_nonneg _)))
  have hE0 : E 0 = 0 := by
    simp only [hEdef]
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    have hzero : (fun x : Fin n → ℝ => ‖w 0 x i j‖ ^ 2) = fun _ => (0:ℝ) := by
      funext x; rw [hw0 x i j]; simp
    rw [hzero]; simp
  have hEderiv : ∀ t ∈ Set.Ioo (0:ℝ) tstar, HasDerivAt E (Ed t) t := by
    intro t ht
    have htT : t ∈ Set.Ioo (0:ℝ) T := ⟨ht.1, lt_trans ht.2 htstarT⟩
    exact linEnergyDeriv hn w P hwsmooth hPcont hderiv htT
  have hcont0 : ContinuousWithinAt E (Set.Icc (0:ℝ) tstar) 0 :=
    linEnergyCont0 hn htstarT w P hwsmooth hPcont hderiv hw0
  intro t₀ ht₀ x i j
  have ht₀T : t₀ ∈ Set.Ico (0:ℝ) T := ⟨ht₀.1, lt_trans ht₀.2 htstarT⟩
  have hEt₀ : E t₀ = 0 := by
    have hcont : ContinuousOn E (Set.Icc 0 t₀) := by
      intro s hs
      by_cases h0s : s = 0
      · rw [h0s]
        exact hcont0.mono (Set.Icc_subset_Icc_right ht₀.2.le)
      · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm h0s)
        have hslt : s < tstar := lt_of_le_of_lt hs.2 ht₀.2
        exact ((hEderiv s ⟨hspos, hslt⟩).continuousAt).continuousWithinAt
    have hder : ∀ t ∈ Set.Ioo (0:ℝ) t₀, HasDerivWithinAt E (Ed t) (Set.Ioo (0:ℝ) t₀) t :=
      fun t ht => (hEderiv t ⟨ht.1, lt_trans ht.2 ht₀.2⟩).hasDerivWithinAt
    have hineq' : ∀ t ∈ Set.Ioo (0:ℝ) t₀, Ed t ≤ K * E t :=
      fun t ht => hineq t ⟨ht.1, lt_trans ht.2 ht₀.2⟩
    exact eq_zero_of_deriv_le (C := K) hcont hder hineq' (fun t _ => hEnn t) hE0 t₀
      ⟨ht₀.1, le_rfl⟩
  have hterm : (∫ x in unitCube, ‖w t₀ x i j‖ ^ 2) = 0 := by
    have h1 : (∑ i : Fin n, ∑ j : Fin n,
        ∫ x in unitCube, ‖w t₀ x i j‖ ^ 2) = 0 := by
      simpa only [hEdef] using hEt₀
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      integral_nonneg (fun x => sq_nonneg _)))).mp h1
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      integral_nonneg (fun x => sq_nonneg _))).mp (h2 i (Finset.mem_univ i))
    exact h3 j (Finset.mem_univ j)
  have hcontij : Continuous (fun x : Fin n → ℝ => w t₀ x i j) :=
    (contDiff_slice_of_contDiffOn (F := fun s x => w s x i j) (hwsmooth i j) ht₀T).continuous
  have hclosed := eq_zero_on_closedCube_of_integral_normSq_eq_zero
    (fun x : Fin n → ℝ => w t₀ x i j) hcontij hterm
  exact eq_zero_of_eq_zero_on_closedCube (fun y : Fin n → ℝ => w t₀ y i j)
    (Periodic1.entry (hwper t₀ ht₀T) i j) hclosed x

end Work.Diff.STE.flat
