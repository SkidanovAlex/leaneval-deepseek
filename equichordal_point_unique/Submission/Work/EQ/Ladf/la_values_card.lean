import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.Defs
import Submission.Work.EQ.LAFree
import Submission.Work.EQ.bwdP_fan_degenerate_countable
import Submission.Work.EQ.bwdFanDefs
import Submission.Work.EQ.isPreconnected_ball_diff_countable
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.Ladf.wsec_descent
import Submission.Work.EQ.Ladf.wsec_defs
import Submission.Work.EQ.H0_structure

/-!
# Only finitely many values are realised by a fixed reading datum

`Work.EQ.Ladf.la_values_card`: for a fixed reading datum `(f, [], b, M)` over a small annulus
`Ann r₁ r₂`, only finitely many values `c` admit a regular component `S` with `(c,S)` in
`LAFree.DatumSet` (a witness chain over the annulus whose reading is the datum and whose two tails
are the germs from depth `M` on).

See the end of this file for the outline of the argument.
-/

namespace Work.EQ.Ladf

open Work.EQ Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-! ## Auxiliary complex analysis -/

/-- **Propagation of the vanishing of a function that is analytic off a thin set.**  If `f`
vanishes on an open set `A ⊆ U` and is analytic at every point of `U \ D`, and `U \ D` is
preconnected, then `f` vanishes on all of `U \ D`.  (The usual clopen argument.) -/
theorem eq_zero_of_analyticAt_off_countable {U D : Set ℂ} (hUpc : IsPreconnected (U \ D))
    {f : ℂ → ℂ} {A : Set ℂ} (hAo : IsOpen A) (hAU : A ⊆ U) (hAz : ∀ z ∈ A, f z = 0)
    (hAne : (A \ D).Nonempty) (han : ∀ z ∈ U \ D, AnalyticAt ℂ f z) :
    ∀ z ∈ U \ D, f z = 0 := by
  obtain ⟨z₀, hz₀A, hz₀D⟩ := hAne
  have hz₀ : z₀ ∈ U \ D := ⟨hAU hz₀A, hz₀D⟩
  have hev : f =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hAo.mem_nhds hz₀A] with z hz
    exact hAz z hz
  have hAn : AnalyticOnNhd ℂ f (U \ D) := fun z hz => han z hz
  exact hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUpc hz₀ hev

/-- **The labelled sheet product is analytic off the degenerate locus.**  The product over all
sign lists `σ` of length `N` of the differences `F w − (bwdP a σ (fan a h τ w)).2` is analytic at
`w₀`, provided `F` is and all the labelled radicands of level `≤ N` are non-zero at `w₀`.  The
individual labelled maps are *not* analytic (the principal square root jumps across its cut), but
the product is symmetric in the sheets, so the local analytic sheets of `bwdFanSheets` may be
substituted: the multiset of sheet values equals the multiset of labelled values
(`sheet_claim`). -/
theorem analyticAt_labelled_snd_prod {a : ℝ} {h : ℂ → ℂ} {τ : List Bool} {N : ℕ} {w₀ : ℂ}
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F w₀)
    (hfan : ∀ τ' : List Bool, AnalyticAt ℂ (fan a h τ') w₀)
    (hgood : ∀ σ : List Bool, σ.length ≤ N →
      bsq (subO1 a (bwdP a σ (fan a h τ w₀))) ≠ 0) :
    AnalyticAt ℂ
      (fun w => ((fanWords N).map (fun σ => F w - (bwdP a σ (fan a h τ w)).2)).prod) w₀ := by
  obtain ⟨hA, -, hC⟩ :=
    sheet_claim (a := a) (h := h) (ε := τ) (w₀ := w₀) (n := N) hfan hgood N (by omega)
  have hbase : AnalyticAt ℂ
      (fun w => ((fanWords N).map (fun σ => F w - (sheetU a h τ w₀ σ w).2)).prod) w₀ :=
    analyticAt_list_prod fun σ hσ =>
      hF.sub (analyticAt_snd.comp (hA σ (le_of_eq (mem_fanWords.mp hσ))))
  refine hbase.congr ?_
  filter_upwards with w
  refine List.Perm.prod_eq ?_
  simpa [List.map_map, Function.comp_def] using
    ((hC N le_rfl w).map fun Q : ℂ × ℂ => F w - Q.2)

/-- **The open annulus with a countable set removed is preconnected.**  A continuous surjection of
the plane onto the annulus `{α < ‖z‖ < R}` with countable fibres is
`z ↦ exp (a + (b-a)(1/2 + arctan (Re z)/π) + i·Im z)` (`a = log α`, `b = log R`); the complement of
its (countable) preimage of `D` is path connected by `Mathlib`'s theorem that the complement of a
countable set in a real vector space of rank `> 1` is path connected. -/
theorem isPreconnected_openAnnulus_diff_countable {α R : ℝ} (hα : 0 < α) (hαR : α < R)
    {D : Set ℂ} (hD : D.Countable) :
    IsPreconnected ({z : ℂ | α < ‖z‖ ∧ ‖z‖ < R} \ D) := by
  set a : ℝ := Real.log α with ha
  set b : ℝ := Real.log R with hb
  have hab : a < b := Real.log_lt_log hα hαR
  have hba : (0 : ℝ) < b - a := by linarith
  -- the squashing map onto the strip `{a < re < b}`
  let Φ : ℂ → ℂ := fun z =>
    ((a + (b - a) * (1 / 2 + Real.arctan z.re / Real.pi) : ℝ) : ℂ) +
      ((z.im : ℝ) : ℂ) * Complex.I
  have hΦre : ∀ z : ℂ, (Φ z).re = a + (b - a) * (1 / 2 + Real.arctan z.re / Real.pi) := by
    intro z
    simp only [Φ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      sub_zero, Complex.ofReal_im, Complex.I_im, mul_one, add_zero]
  have hΦim : ∀ z : ℂ, (Φ z).im = z.im := by
    intro z
    simp only [Φ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  have hΦmem : ∀ z : ℂ, a < (Φ z).re ∧ (Φ z).re < b := by
    intro z
    have h3 : -(1 / 2 : ℝ) < Real.arctan z.re / Real.pi := by
      rw [lt_div_iff₀ Real.pi_pos]
      have h := Real.neg_pi_div_two_lt_arctan z.re
      have he : -(1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) := by ring
      rw [he]; exact h
    have h4 : Real.arctan z.re / Real.pi < 1 / 2 := by
      rw [div_lt_iff₀ Real.pi_pos]
      have h := Real.arctan_lt_pi_div_two z.re
      have he : (1 / 2 : ℝ) * Real.pi = Real.pi / 2 := by ring
      rw [he]; exact h
    have h5 : 0 < 1 / 2 + Real.arctan z.re / Real.pi := by linarith
    have h6 : 1 / 2 + Real.arctan z.re / Real.pi < 1 := by linarith
    have h7 : 0 < (b - a) * (1 / 2 + Real.arctan z.re / Real.pi) := mul_pos hba h5
    have h8 : (b - a) * (1 / 2 + Real.arctan z.re / Real.pi) < (b - a) * 1 :=
      mul_lt_mul_of_pos_left h6 hba
    rw [hΦre]
    constructor <;> linarith
  have hΦinj : ∀ z w : ℂ, Φ z = Φ w → z = w := by
    intro z w h
    have hre : Real.arctan z.re = Real.arctan w.re := by
      have h1 := congrArg Complex.re h
      rw [hΦre, hΦre] at h1
      have h2 : (b - a) * (Real.arctan z.re / Real.pi)
          = (b - a) * (Real.arctan w.re / Real.pi) := by linarith
      have h3 : Real.arctan z.re / Real.pi = Real.arctan w.re / Real.pi :=
        mul_left_cancel₀ (ne_of_gt hba) h2
      have h4 : Real.arctan z.re / Real.pi * Real.pi
          = Real.arctan w.re / Real.pi * Real.pi := congrArg (fun t => t * Real.pi) h3
      rwa [div_mul_cancel₀ _ Real.pi_ne_zero, div_mul_cancel₀ _ Real.pi_ne_zero] at h4
    have hzr : z.re = w.re := Real.arctan_inj.mp hre
    have him : z.im = w.im := by
      have h1 := congrArg Complex.im h
      rwa [hΦim, hΦim] at h1
    exact Complex.ext hzr him
  have hΦsurj : ∀ s : ℂ, a < s.re → s.re < b → ∃ z : ℂ, Φ z = s := by
    intro s h1 h2
    set u : ℝ := (s.re - a) / (b - a) - 1 / 2 with hu
    have hu1 : -(1 / 2 : ℝ) < u := by
      have h : 0 < (s.re - a) / (b - a) := div_pos (by linarith) hba
      rw [hu]; linarith
    have hu2 : u < 1 / 2 := by
      have h : (s.re - a) / (b - a) < 1 := by
        rw [div_lt_one hba]; linarith
      rw [hu]; linarith
    have htπ : -(Real.pi / 2) < Real.pi * u ∧ Real.pi * u < Real.pi / 2 := by
      refine ⟨?_, ?_⟩ <;> nlinarith [Real.pi_pos]
    have harctan : Real.arctan (Real.tan (Real.pi * u)) = Real.pi * u :=
      Real.arctan_tan htπ.1 htπ.2
    refine ⟨((Real.tan (Real.pi * u) : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I, ?_⟩
    refine Complex.ext ?_ ?_
    · show (Φ (((Real.tan (Real.pi * u) : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I)).re = s.re
      rw [hΦre]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        sub_zero, Complex.ofReal_im, Complex.I_im, mul_one, add_zero]
      rw [harctan, hu]
      field_simp
      ring
    · show (Φ (((Real.tan (Real.pi * u) : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I)).im = s.im
      rw [hΦim]
      show (↑(Real.tan (Real.pi * u)) + (↑s.im : ℂ) * Complex.I).im = s.im
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  have hΦrange : Set.range Φ = {s : ℂ | a < s.re ∧ s.re < b} := by
    ext s
    constructor
    · rintro ⟨z, rfl⟩
      exact hΦmem z
    · rintro ⟨h1, h2⟩
      exact hΦsurj s h1 h2
  -- the composite `Ψ = exp ∘ Φ` has range the annulus
  let Ψ : ℂ → ℂ := fun z => Complex.exp (Φ z)
  have hΨcont : Continuous Ψ := by
    refine Complex.continuous_exp.comp ?_
    unfold Φ
    fun_prop
  have hΨrange : Set.range Ψ = {z : ℂ | α < ‖z‖ ∧ ‖z‖ < R} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      have h := hΦmem w
      have hv : Ψ w = Complex.exp (Φ w) := rfl
      have hαeq : Real.exp a = α := by rw [ha]; exact Real.exp_log hα
      have hReq : Real.exp b = R := by rw [hb]; exact Real.exp_log (lt_trans hα hαR)
      rw [Set.mem_ofPred_eq, hv, Complex.norm_exp, ← hαeq, ← hReq]
      exact ⟨Real.exp_lt_exp.mpr h.1, Real.exp_lt_exp.mpr h.2⟩
    · intro hz
      have hz' := hz
      rw [Set.mem_ofPred_eq] at hz'
      have hzne : z ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hz'
        linarith [hz'.1]
      have hlog1 : a < (Complex.log z).re := by
        rw [Complex.log_re]; exact Real.log_lt_log hα hz'.1
      have hlog2 : (Complex.log z).re < b := by
        rw [Complex.log_re]; exact Real.log_lt_log (lt_trans hα hz'.1) hz'.2
      obtain ⟨w, hw⟩ := hΦsurj (Complex.log z) hlog1 hlog2
      refine ⟨w, ?_⟩
      have hv : Ψ w = Complex.exp (Φ w) := rfl
      rw [hv, hw, Complex.exp_log hzne]
  -- the fibres of `Ψ` are countable
  have hexpFib : ∀ d : ℂ, (Complex.exp ⁻¹' {d}).Countable := by
    intro d
    by_cases hd : d = 0
    · have hempty : Complex.exp ⁻¹' ({0} : Set ℂ) = ∅ := by
        ext z
        simp [Complex.exp_ne_zero]
      rw [hd, hempty]
      exact Set.countable_empty
    · have hsub : Complex.exp ⁻¹' {d} ⊆
          (fun k : ℤ => Complex.log d + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) '' Set.univ := by
        intro z hz
        have hz' : Complex.exp z = d := hz
        have h1 : Complex.exp (z - Complex.log d) = 1 := by
          rw [Complex.exp_sub, hz', Complex.exp_log hd]
          exact div_self hd
        obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
        refine ⟨k, Set.mem_univ _, ?_⟩
        show Complex.log d + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = z
        rw [← hk]
        ring
      exact Set.Countable.mono hsub
        (Set.countable_univ.image fun k : ℤ => Complex.log d + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
  have hexpPre : (Complex.exp ⁻¹' D).Countable := by
    rw [← Set.biUnion_preimage_singleton Complex.exp D]
    exact Set.Countable.biUnion hD fun d _ => hexpFib d
  have hpre : (Ψ ⁻¹' D).Countable := by
    have hinj : Set.InjOn Φ (Φ ⁻¹' (Complex.exp ⁻¹' D)) := fun z _ w _ h => hΦinj z w h
    have himage : (Φ '' (Φ ⁻¹' (Complex.exp ⁻¹' D))).Countable :=
      hexpPre.mono (by rintro _ ⟨z, hz, rfl⟩; exact hz)
    have hthis := Set.countable_of_injective_of_countable_image
      (s := Φ ⁻¹' (Complex.exp ⁻¹' D)) hinj himage
    have heq : Ψ ⁻¹' D = Φ ⁻¹' (Complex.exp ⁻¹' D) := rfl
    rw [heq]
    exact hthis
  -- Mathlib: the complement of a countable set in a rank-`> 1` space is path connected
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hpath : IsPathConnected ((Ψ ⁻¹' D)ᶜ) :=
    Set.Countable.isPathConnected_compl_of_one_lt_rank hrank hpre
  have himg : Ψ '' ((Ψ ⁻¹' D)ᶜ) = {z : ℂ | α < ‖z‖ ∧ ‖z‖ < R} \ D := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨by rw [← hΨrange]; exact ⟨w, rfl⟩, hw⟩
    · rintro ⟨hz, hzD⟩
      obtain ⟨w, hw⟩ : z ∈ Set.range Ψ := by rw [hΨrange]; exact hz
      refine ⟨w, ?_, hw⟩
      intro hwD
      exact hzD (by rwa [Set.mem_preimage, hw] at hwD)
  rw [← himg]
  exact (hpath.isConnected.isPreconnected).image _ hΨcont.continuousOn

theorem la_values_card {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r₁ r₂ : ℝ) (M : ℕ) (f b : List Bool),
      0 < r₁ → r₁ < r₂ → r₂ < δ → 1 / eqLam a < r₂ / r₁ → f.length = M → b.length = M →
      (eqLam a : ℝ) ^ M * r₂ < δ →
      (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁ < δ →
      {c : ℂ | ∃ S : Set ChainData, (c, S) ∈ LAFree.DatumSet a h r₁ r₂ M f b}.Finite := by
  obtain ⟨δF, hδFpos, hfan_an⟩ := fan_estimates (a := a) ha0 ha1 (h := h) (r := r) hh
  obtain ⟨δG, hδGpos, hgerm_an, -, -, hginj, -⟩ :=
    germC_facts (a := a) ha0 ha1 (h := h) (r := r) hh
  obtain ⟨δW, hδWpos, hwsec⟩ := wsec_tails_ball (a := a) ha0 ha1 (h := h) (r := r) hh
  obtain ⟨δD, hδDpos, hdeg⟩ := bwdP_fan_degenerate_countable (a := a) ha0 ha1 (h := h) (r := r) hh
  set ρ : ℝ := min (min δF δW) (min δD (δG / 2)) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact lt_min (lt_min hδFpos hδWpos) (lt_min hδDpos (by linarith))
  have hρF : ρ ≤ δF := by rw [hρdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρW : ρ ≤ δW := by rw [hρdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρD : ρ ≤ δD := by rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρG2 : ρ ≤ δG / 2 := by rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hρG : ρ ≤ δG := by linarith
  refine ⟨ρ, hρpos, ?_⟩
  intro r₁ r₂ M f b h1 h12 h2 h3 hf hb h4 h5
  have hlem_pos : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlem_nn : (0 : ℝ) ≤ eqLam a := le_of_lt hlem_pos
  have hθpos : 0 < r₁ / 2 := by linarith
  have hθρ : r₁ / 2 < ρ := by linarith
  -- ## the degenerate locus
  set Dset : Set ℂ := ({0} : Set ℂ) ∪ ⋃ τ ∈ {σ : List Bool | σ ∈ fanWords M},
      {w : ℂ | ‖w‖ < δD ∧ ∃ σ : List Bool, σ.length ≤ M ∧
        bsq (subO1 a (bwdP a σ (fan a h τ w))) = 0} with hDsetdef
  have hDcount : Dset.Countable := by
    rw [hDsetdef]
    refine (Set.countable_singleton (0 : ℂ)).union ?_
    refine Set.Countable.biUnion (List.finite_toSet (fanWords M)).countable ?_
    intro τ hτ
    exact hdeg τ M
  have hgoodD : ∀ w : ℂ, ‖w‖ < ρ → w ∉ Dset → ∀ τ ∈ {σ : List Bool | σ ∈ fanWords M},
      ∀ σ : List Bool, σ.length ≤ M →
        bsq (subO1 a (bwdP a σ (fan a h τ w))) ≠ 0 := by
    intro w hw hwD τ hτ σ hσ hzero
    refine hwD (by
      rw [hDsetdef]
      exact Or.inr (Set.mem_iUnion.mpr ⟨τ, Set.mem_iUnion.mpr
        ⟨hτ, ⟨lt_of_lt_of_le hw hρD, σ, hσ, hzero⟩⟩⟩))
  -- ## a comparison point
  have hzstar : ∃ zstar : ℂ, r₁ / 2 < ‖zstar‖ ∧ ‖zstar‖ < ρ ∧ zstar ∉ Dset := by
    by_contra hcon
    push_neg at hcon
    have hsub : ((fun t : ℝ => (t : ℂ) * Complex.I) '' (Set.Ioo (r₁ / 2) ρ)) ⊆ Dset := by
      rintro z ⟨t, ht, rfl⟩
      refine hcon _ ?_ ?_
      · rw [norm_mul, Complex.norm_I, mul_one,
          Complex.norm_of_nonneg (le_of_lt (lt_trans hθpos ht.1))]
        exact ht.1
      · rw [norm_mul, Complex.norm_I, mul_one,
          Complex.norm_of_nonneg (le_of_lt (lt_trans hθpos ht.1))]
        exact ht.2
    have hcount : (Set.Ioo (r₁ / 2) ρ).Countable := by
      have hinj : Set.InjOn (fun t : ℝ => (t : ℂ) * Complex.I) (Set.Ioo (r₁ / 2) ρ) := by
        intro s _ t _ hst
        have h := congrArg Complex.im hst
        simpa using h
      exact Set.countable_of_injective_of_countable_image hinj (hDcount.mono hsub)
    exact absurd (Cardinal.Real.Ioo_countable_iff.mp hcount) (by linarith)
  obtain ⟨zstar, hzθ, hzρ, hzD⟩ := hzstar
  -- ## the main counting
  have hkey : ∀ c : ℂ, (∃ S : Set ChainData, (c, S) ∈ LAFree.DatumSet a h r₁ r₂ M f b) →
      ∃ σ τ : List Bool, σ ∈ fanWords M ∧ τ ∈ fanWords M ∧
        (germC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / zstar))).2 =
          (bwdP a σ (fan a h τ zstar)).2 := by
    intro c hc
    obtain ⟨S, hSdat⟩ := hc
    rw [LAFree.DatumSet, Set.mem_ofPred_eq] at hSdat
    obtain ⟨hSreg, hcnorm, q, hqS, hqann, hqeq, -, hqbwd⟩ := hSdat
    set u : ℂ := q.2.1 with hu
    have hqH0 : q ∈ H0 a h := hSreg.1 hqS
    have hu_ne : u ≠ 0 := by
      intro h0
      have h := hqann.1
      rw [h0, norm_zero] at h
      linarith
    have hq2 : q.2.2 = c / u := by
      rw [hqeq, candChain_psi2]
    have hJ : bwdP a b (fan a h f u) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / u)) := by
      have h1 := hqbwd M le_rfl
      rw [hq2] at h1
      have h2 : q.1 (-(M : ℤ)) = bwdP a b (fan a h f u) := by
        rw [hqeq]
        have h3 := candChain_fst_neg a h f [] b M c u (j := M) le_rfl
        rwa [List.take_of_length_le (le_of_eq hb)] at h3
      rw [h2] at h1
      exact h1
    -- the local analytic section through the witness
    obtain ⟨-, hsect, -, -⟩ := H0_structure (a := a) ha0 ha1 (h := h) (r := r) hh
    obtain ⟨ρs, hρspos, g, hg0, hgmem, hgan, hgψ2, -⟩ := hsect q hqH0
    have hcontg : ContinuousOn g (Metric.ball u ρs) := by
      have hc1 : ContinuousOn (fun z => (g z).1) (Metric.ball u ρs) := by
        rw [continuousOn_pi]
        intro n
        exact (hgan n).continuousOn
      have hc2 : ContinuousOn (fun z => (g z).2.1) (Metric.ball u ρs) := by
        refine continuousOn_id.congr ?_
        intro z hz
        exact (hgmem z hz).2
      have hc3 : ContinuousOn (fun z => (g z).2.2) (Metric.ball u ρs) := hgψ2.continuousOn
      exact hc1.prodMk (hc2.prodMk hc3)
    have hvalg : ∀ z ∈ Metric.ball u ρs, (g z).2.1 * (g z).2.2 = c := by
      have himg : IsPreconnected (g '' Metric.ball u ρs) :=
        (Metric.isPreconnected_ball (x := u) (r := ρs)).image _ hcontg
      have hScomp : S = connectedComponentIn (H0 a h) q := by
        obtain ⟨p, -, hSp⟩ := hSreg.2.1
        have hqcomp : q ∈ connectedComponentIn (H0 a h) p := by rw [← hSp]; exact hqS
        calc S = connectedComponentIn (H0 a h) p := hSp
          _ = connectedComponentIn (H0 a h) q := connectedComponentIn_eq hqcomp
      have hsub : g '' Metric.ball u ρs ⊆ S := by
        rw [hScomp]
        refine IsPreconnected.subset_connectedComponentIn himg ⟨u, ?_, hg0⟩ ?_
        · exact Metric.mem_ball_self hρspos
        · rintro x ⟨y, hy, rfl⟩
          exact (hgmem y hy).1
      intro z hz
      exact hSreg.2.2 (g z) (hsub ⟨z, hz, rfl⟩)
    have hsectat : IsSectAt a h g u ρs :=
      ⟨hρspos, by rw [hg0]; exact hqH0,
        fun z hz => ⟨(hgmem z hz).1, (hgmem z hz).2⟩, hgan, hgψ2⟩
    have hlem_u : (eqLam a : ℝ) ^ M * ‖u‖ < ρ := by
      have hle : (eqLam a : ℝ) ^ M * ‖u‖ ≤ (eqLam a : ℝ) ^ M * r₂ :=
        mul_le_mul_of_nonneg_left hqann.2 (by positivity)
      linarith
    have hlem_c : (eqLam a : ℝ) ^ M * ‖c / u‖ < ρ := by
      have hcu : ‖c / u‖ ≤ 2 * rhoStar a h / r₁ := by
        rw [norm_div]
        exact div_le_div₀ (by positivity) hcnorm h1 hqann.1
      have hle : (eqLam a : ℝ) ^ M * ‖c / u‖ ≤
          (eqLam a : ℝ) ^ M * (2 * rhoStar a h / r₁) :=
        mul_le_mul_of_nonneg_left hcu (by positivity)
      have heq : (eqLam a : ℝ) ^ M * (2 * rhoStar a h / r₁) =
          (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁ := by ring
      linarith
    obtain ⟨ρt, hρtpos, hρtle, htails⟩ := hwsec M f b hf hb hu_ne hsectat
      (hg0.trans hqeq) hvalg hJ (lt_of_lt_of_le hlem_u hρW) (lt_of_lt_of_le hlem_c hρW)
    -- ## the sheet product
    set F : ℂ → ℂ := fun w => (germC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / w))).2 with hFdef
    set Pc : ℂ → ℂ := fun w => ((fanWords M).map (fun τ =>
        ((fanWords M).map (fun σ => F w - (bwdP a σ (fan a h τ w)).2)).prod)).prod with hPcdef
    have hPczero : ∀ z ∈ Metric.ball u ρt, Pc z = 0 := by
      intro z hz
      have hzs : z ∈ Metric.ball u ρs := lt_of_lt_of_le hz hρtle
      have hchain : IsChain a h (g z) := isChain_of_mem_H0 (hgmem z hzs).1
      have hψ1 : (g z).2.1 = z := (hgmem z hzs).2
      have hread : (g z).1 (-(M : ℤ)) = bwdP a (LAFree.bwdWord a M (g z))
          (fan a h (LAFree.fanWord a M (g z)) z) := by
        have h1 := LAFree.bwdP_bwdWord_take (a := a) (h := h) hchain M le_rfl
        rw [List.take_of_length_le (le_of_eq (LAFree.bwdWord_length a M (g z)))] at h1
        have htail' : ∀ n : ℕ, M ≤ n →
            (g z).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (g z).2.1) := by
          intro n hn
          rw [hψ1]
          exact (htails z hz).1 n hn
        have h2 := LAFree.fanWord_eq_fan (a := a) ha0 ha1 hchain htail'
        rw [h1, h2, hψ1]
      have heq : F z = (bwdP a (LAFree.bwdWord a M (g z))
          (fan a h (LAFree.fanWord a M (g z)) z)).2 := by
        have h3 := (htails z hz).2 M le_rfl
        rw [hread] at h3
        have h4 : (germC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / z))).2 =
            (ugermC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / z))).2 := by
          simp [ugermC, eqMirror]
        have hFz : F z = (germC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / z))).2 := by
          rw [hFdef]
        rw [hFz, h4, ← h3]
      have hmemτ : LAFree.fanWord a M (g z) ∈ fanWords M :=
        mem_fanWords.mpr (LAFree.fanWord_length a M (g z))
      have hmemσ : LAFree.bwdWord a M (g z) ∈ fanWords M :=
        mem_fanWords.mpr (LAFree.bwdWord_length a M (g z))
      have hinner : ((fanWords M).map (fun σ =>
          F z - (bwdP a σ (fan a h (LAFree.fanWord a M (g z)) z)).2)).prod = 0 := by
        refine List.prod_eq_zero_iff.mpr (List.mem_map.mpr ⟨LAFree.bwdWord a M (g z), hmemσ, ?_⟩)
        rw [heq]; ring
      rw [hPcdef]
      exact List.prod_eq_zero_iff.mpr (List.mem_map.mpr ⟨LAFree.fanWord a M (g z), hmemτ, hinner⟩)
    have hPcan : ∀ w : ℂ, r₁ / 2 < ‖w‖ → ‖w‖ < ρ → w ∉ Dset → AnalyticAt ℂ Pc w := by
      intro w hwθ hw hwD
      have hw0 : w ≠ 0 := fun h0 => hwD (by rw [hDsetdef]; exact Or.inl h0)
      have harg : ‖((eqLam a : ℝ) : ℂ) ^ M * (c / w)‖ < δG := by
        have hcw : ‖c / w‖ ≤ 2 * rhoStar a h / (r₁ / 2) := by
          rw [norm_div]
          exact div_le_div₀ (by positivity) hcnorm (by linarith) (le_of_lt hwθ)
        have hle : (eqLam a : ℝ) ^ M * ‖c / w‖ ≤
            (eqLam a : ℝ) ^ M * (2 * rhoStar a h / (r₁ / 2)) :=
          mul_le_mul_of_nonneg_left hcw (by positivity)
        have heq : (eqLam a : ℝ) ^ M * (2 * rhoStar a h / (r₁ / 2)) =
            (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / (r₁ / 2) := by ring
        rw [norm_mul, norm_pow, Complex.norm_of_nonneg hlem_nn]
        have h2 : (eqLam a : ℝ) ^ M * (2 * rhoStar a h / (r₁ / 2)) =
            2 * ((eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁) := by ring
        have h3 : (eqLam a : ℝ) ^ M * ‖c / w‖ ≤
            (eqLam a : ℝ) ^ M * (2 * rhoStar a h / (r₁ / 2)) := hle
        have h4 : 2 * ((eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁) < 2 * ρ := by linarith
        linarith [hρG2]
      have hFw : AnalyticAt ℂ F w := by
        have hinner : AnalyticAt ℂ (fun w : ℂ => ((eqLam a : ℝ) : ℂ) ^ M * (c / w)) w :=
          (analyticAt_const (v := ((eqLam a : ℝ) : ℂ) ^ M)).mul
            ((analyticAt_const (v := c)).div analyticAt_id hw0)
        have hgerm : AnalyticAt ℂ (germC a h) (((eqLam a : ℝ) : ℂ) ^ M * (c / w)) :=
          hgerm_an _ (by rw [Metric.mem_ball, dist_zero_right]; exact harg)
        have hcomp : AnalyticAt ℂ
            (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / w))) w :=
          hgerm.comp (f := fun w : ℂ => ((eqLam a : ℝ) : ℂ) ^ M * (c / w)) hinner
        have h2 : AnalyticAt ℂ
            (fun w : ℂ => (germC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / w))).2) w :=
          analyticAt_snd.comp hcomp
        rw [hFdef]
        exact h2
      have hfanw : ∀ τ' : List Bool, AnalyticAt ℂ (fan a h τ') w := fun τ' =>
        (hfan_an τ').1 w (by
          rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hw hρF)
      have hgdz : ∀ τ ∈ {σ : List Bool | σ ∈ fanWords M}, ∀ σ : List Bool, σ.length ≤ M →
          bsq (subO1 a (bwdP a σ (fan a h τ w))) ≠ 0 :=
        hgoodD w hw hwD
      rw [hPcdef]
      exact analyticAt_list_prod (fun τ hτ =>
        analyticAt_labelled_snd_prod (a := a) (h := h) (τ := τ) (N := M) (w₀ := w) (F := F)
          hFw hfanw (hgdz τ hτ))
    -- ## propagation to the comparison point
    have hUpc : IsPreconnected
        ({z : ℂ | r₁ / 2 < ‖z‖ ∧ ‖z‖ < ρ} \ Dset) :=
      isPreconnected_openAnnulus_diff_countable hθpos hθρ hDcount
    have huA : u ∈ Metric.ball u ρt ∩ {z : ℂ | r₁ / 2 < ‖z‖ ∧ ‖z‖ < ρ} :=
      ⟨Metric.mem_ball_self hρtpos, by
        rw [Set.mem_ofPred_eq]
        exact ⟨by linarith [hqann.1], lt_of_le_of_lt hqann.2 h2⟩⟩
    have hAopen : IsOpen (Metric.ball u ρt ∩ {z : ℂ | r₁ / 2 < ‖z‖ ∧ ‖z‖ < ρ}) :=
      Metric.isOpen_ball.inter
        ((isOpen_lt continuous_const continuous_norm).inter
          (isOpen_lt continuous_norm continuous_const))
    obtain ⟨zA, hzA⟩ : ∃ z : ℂ,
        z ∈ (Metric.ball u ρt ∩ {z : ℂ | r₁ / 2 < ‖z‖ ∧ ‖z‖ < ρ}) \ Dset := by
      by_contra hcon
      push_neg at hcon
      have hAcnt : (Metric.ball u ρt ∩ {z : ℂ | r₁ / 2 < ‖z‖ ∧ ‖z‖ < ρ}).Countable := by
        refine hDcount.mono ?_
        intro z hz
        by_contra hzD
        exact hcon z ⟨hz, hzD⟩
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hAopen u huA
      have hinjimg : ((fun t : ℝ => u + (t : ℂ) * Complex.I) '' Set.Ioo 0 ε) ⊆
          Metric.ball u ρt ∩ {z : ℂ | r₁ / 2 < ‖z‖ ∧ ‖z‖ < ρ} := by
        rintro z ⟨t, ht, rfl⟩
        refine hεsub ?_
        rw [Metric.mem_ball, dist_eq_norm]
        have h1 : ‖(fun t : ℝ => u + (t : ℂ) * Complex.I) t - u‖ = t := by
          rw [show (fun t : ℝ => u + (t : ℂ) * Complex.I) t = u + (t : ℂ) * Complex.I from rfl,
            add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_of_nonneg (le_of_lt ht.1)]
        rw [h1]
        exact ht.2
      have hcnt' : (Set.Ioo (0 : ℝ) ε).Countable := by
        have hinj : Set.InjOn (fun t : ℝ => u + (t : ℂ) * Complex.I) (Set.Ioo 0 ε) := by
          intro s _ t _ hst
          have h := congrArg Complex.im hst
          simpa using h
        exact Set.countable_of_injective_of_countable_image hinj (hAcnt.mono hinjimg)
      exact absurd (Cardinal.Real.Ioo_countable_iff.mp hcnt') (by linarith)
    have hPcall : ∀ z ∈ ({z : ℂ | r₁ / 2 < ‖z‖ ∧ ‖z‖ < ρ} \ Dset), Pc z = 0 :=
      eq_zero_of_analyticAt_off_countable (U := {z : ℂ | r₁ / 2 < ‖z‖ ∧ ‖z‖ < ρ}) (D := Dset)
        hUpc (f := Pc) (A := Metric.ball u ρt ∩ {z : ℂ | r₁ / 2 < ‖z‖ ∧ ‖z‖ < ρ})
        hAopen (by intro z hz; exact hz.2) (fun z hz => hPczero z hz.1)
        ⟨zA, hzA⟩ (fun z hz => hPcan z hz.1.1 hz.1.2 hz.2)
    have hPczstar : Pc zstar = 0 := hPcall zstar ⟨⟨hzθ, hzρ⟩, hzD⟩
    rw [hPcdef] at hPczstar
    rw [List.prod_eq_zero_iff] at hPczstar
    obtain ⟨τ, hτ, hinner⟩ := List.mem_map.mp hPczstar
    rw [List.prod_eq_zero_iff] at hinner
    obtain ⟨σ, hσ, hzero⟩ := List.mem_map.mp hinner
    refine ⟨σ, τ, hσ, hτ, ?_⟩
    have := sub_eq_zero.mp hzero
    rw [hFdef] at this
    exact this
  -- ## finiteness
  set Ψ : ℂ → ℂ := fun c => (germC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / zstar))).2 with hΨdef
  set T : Set ℂ := (fun p : List Bool × List Bool =>
      (bwdP a p.1 (fan a h p.2 zstar)).2) ''
      ({σ : List Bool | σ ∈ fanWords M} ×ˢ {τ : List Bool | τ ∈ fanWords M}) with hTdef
  have hTfin : T.Finite := by
    have h1 : ({σ : List Bool | σ ∈ fanWords M} ×ˢ
        {τ : List Bool | τ ∈ fanWords M}).Finite :=
      (List.finite_toSet (fanWords M)).prod (List.finite_toSet (fanWords M))
    rw [hTdef]
    exact h1.image _
  refine Set.Finite.of_finite_image (s := {c : ℂ | ∃ S : Set ChainData,
      (c, S) ∈ LAFree.DatumSet a h r₁ r₂ M f b}) (f := Ψ) ?_ ?_
  · refine hTfin.subset ?_
    rintro v ⟨c, hc, rfl⟩
    obtain ⟨σ, τ, hσ, hτ, heq⟩ := hkey c hc
    refine ⟨(σ, τ), ⟨hσ, hτ⟩, ?_⟩
    show (bwdP a σ (fan a h τ zstar)).2 = Ψ c
    exact heq.symm
  · intro c₁ hc₁ c₂ hc₂ heq
    obtain ⟨S₁, hS₁⟩ := hc₁
    obtain ⟨S₂, hS₂⟩ := hc₂
    rw [LAFree.DatumSet, Set.mem_ofPred_eq] at hS₁ hS₂
    have hb₁ : ‖c₁‖ ≤ 2 * rhoStar a h := hS₁.2.1
    have hb₂ : ‖c₂‖ ≤ 2 * rhoStar a h := hS₂.2.1
    have harg : ∀ c : ℂ, ‖c‖ ≤ 2 * rhoStar a h →
        ‖((eqLam a : ℝ) : ℂ) ^ M * (c / zstar)‖ < δG := by
      intro c hc
      have hcw : ‖c / zstar‖ ≤ 2 * rhoStar a h / (r₁ / 2) := by
        rw [norm_div]
        exact div_le_div₀ (by positivity) hc (by linarith) (le_of_lt hzθ)
      have hle : (eqLam a : ℝ) ^ M * ‖c / zstar‖ ≤
          (eqLam a : ℝ) ^ M * (2 * rhoStar a h / (r₁ / 2)) :=
        mul_le_mul_of_nonneg_left hcw (by positivity)
      have h2 : (eqLam a : ℝ) ^ M * (2 * rhoStar a h / (r₁ / 2)) =
          2 * ((eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁) := by ring
      have h4 : 2 * ((eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁) < 2 * ρ := by linarith
      rw [norm_mul, norm_pow, Complex.norm_of_nonneg hlem_nn]
      linarith [hρG2]
    have hw₁ : ((eqLam a : ℝ) : ℂ) ^ M * (c₁ / zstar) ∈ Metric.ball 0 δG := by
      rw [Metric.mem_ball, dist_zero_right]; exact harg c₁ hb₁
    have hw₂ : ((eqLam a : ℝ) : ℂ) ^ M * (c₂ / zstar) ∈ Metric.ball 0 δG := by
      rw [Metric.mem_ball, dist_zero_right]; exact harg c₂ hb₂
    have heq' : (germC a h (((eqLam a : ℝ) : ℂ) ^ M * (c₁ / zstar))).2 =
        (germC a h (((eqLam a : ℝ) : ℂ) ^ M * (c₂ / zstar))).2 := heq
    have h12 : ((eqLam a : ℝ) : ℂ) ^ M * (c₁ / zstar) = ((eqLam a : ℝ) : ℂ) ^ M * (c₂ / zstar) :=
      hginj hw₁ hw₂ heq'
    have hlem_ne : ((eqLam a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlem_pos)
    have hzne : zstar ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hzθ; linarith
    have h1' : c₁ / zstar = c₂ / zstar :=
      mul_left_cancel₀ (pow_ne_zero M hlem_ne) h12
    have h2' : c₁ / zstar * zstar = c₂ / zstar * zstar := by rw [h1']
    rwa [div_mul_cancel₀ _ hzne, div_mul_cancel₀ _ hzne] at h2'



end

end Work.EQ.Ladf
