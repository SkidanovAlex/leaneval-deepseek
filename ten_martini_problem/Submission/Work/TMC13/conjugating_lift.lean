import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.RotBasics.Defs
import Submission.Work.TMC13.Defs
import Submission.Work.TMC13.fourier_amp
import Submission.Work.TMC13.log_lift_deriv
import Submission.Work.TMC13.analytic_lipschitz
import Submission.Work.TMC13.ref_lift
import Submission.Work.TMC13.firstcol_lift

namespace Work.TMC13

open Work.TMComp.RotBasics
open Filter Topology Set

noncomputable section

/-- The matrix–vector product is the real/imaginary part of the complex action of `smul`. -/
theorem mulVec_vc (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    A.mulVec ![Real.cos (Real.pi * t), Real.sin (Real.pi * t)] =
      ![(smul A (vc t)).re, (smul A (vc t)).im] := by
  rw [Matrix.mulVec_fin_two]
  ext i
  fin_cases i <;> simp [smul, vc]

/-- `vc s` is the exponential of `i π s`. -/
theorem vc_eq_exp (s : ℝ) : vc s = Complex.exp ((↑(Real.pi * s) : ℂ) * Complex.I) := by
  apply Complex.ext <;>
    simp only [vc, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- `smul A (vc t)` is never `0` when `det A = 1`. -/
theorem smul_vc_ne_zero {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det = 1) (t : ℝ) :
    smul A (vc t) ≠ 0 := by
  have hfa := fourier_amp A
  have hfa2 := hfa.2
  rw [hA] at hfa2
  have hns : ‖c1 A‖ ^ 2 - ‖c2 A‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    nlinarith [hfa2]
  have hlt : ‖c2 A‖ < ‖c1 A‖ := by
    nlinarith [norm_nonneg (c1 A), norm_nonneg (c2 A), hns]
  rw [hfa.1 t]
  intro hzero
  have h1 : ‖c1 A * vc t‖ = ‖c1 A‖ := by rw [norm_mul, vc_norm, mul_one]
  have h2 : ‖c2 A * (starRingEnd ℂ (vc t))‖ = ‖c2 A‖ := by
    rw [norm_mul, Complex.norm_conj, vc_norm, mul_one]
  have hsub : ‖c1 A‖ - ‖c2 A‖ ≤ ‖c1 A * vc t + c2 A * (starRingEnd ℂ (vc t))‖ := by
    have h := abs_norm_sub_norm_le (c1 A * vc t) (-(c2 A * (starRingEnd ℂ (vc t))))
    rw [norm_neg, h1, h2,
      show c1 A * vc t - -(c2 A * (starRingEnd ℂ (vc t)))
        = c1 A * vc t + c2 A * (starRingEnd ℂ (vc t)) by ring] at h
    exact le_trans (le_abs_self _) h
  rw [hzero, norm_zero] at hsub
  linarith

/-- A continuous function on a preconnected space all of whose values are even integers
is constant. -/
theorem eq_const_of_two_int {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) (hval : ∀ x, ∃ n : ℤ, f x = 2 * (n : ℝ)) :
    ∃ c : ℝ, ∀ x, f x = c := by
  have hT : IsDiscrete (Set.range ((↑) : ℤ → ℝ)) :=
    Topology.IsInducing.isDiscrete_range
      (f := ((↑) : ℤ → ℝ)) Real.isClosedEmbedding_intCast.isInducing
  have hmaps : MapsTo f Set.univ (Set.range ((↑) : ℤ → ℝ)) := by
    intro x _
    obtain ⟨n, hn⟩ := hval x
    exact ⟨2 * n, by push_cast; linarith [hn]⟩
  obtain ⟨c, -, hc⟩ := IsPreconnected.eqOn_const_of_mapsTo (S := Set.univ)
    isPreconnected_univ hT hf.continuousOn hmaps (Set.range_nonempty _)
  exact ⟨c, fun x => hc (Set.mem_univ x)⟩

theorem conjugating_lift {a b a' b' : ℝ} (ha : a < a') (hb : b' < b) (hab : a' ≤ b')
    {C : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hper : ∀ E x : ℝ, C E (x + 1) = C E x) (hdet : ∀ E x : ℝ, (C E x).det = 1)
    (hana : ∀ i j : Fin 2, AnalyticOnNhd ℝ (fun p : ℝ × ℝ => C p.1 p.2 i j)
        (Set.Ioo a b ×ˢ Set.univ))
    (hdeg : ∀ E : ℝ, Work.TMContract.HasDegree (C E) 0) :
    ∃ h : ℝ → ℝ → ℝ → ℝ,
      (∀ E ∈ Set.Icc a' b', Continuous (fun p : ℝ × ℝ => h E p.1 p.2)) ∧
      (∀ E ∈ Set.Icc a' b', ∀ y t : ℝ, h E y (t + 1) = h E y t + 1) ∧
      (∀ E ∈ Set.Icc a' b', ∀ y t : ℝ, ∃ c : ℝ, c ≠ 0 ∧
        Matrix.mulVec (C E y)
          ![Real.cos (Real.pi * t), Real.sin (Real.pi * t)] =
          c • ![Real.cos (Real.pi * h E y t), Real.sin (Real.pi * h E y t)]) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ E ∈ Set.Icc a' b', ∀ y t : ℝ, |h E y t - t| ≤ M) ∧
      (∃ L : ℝ, 0 ≤ L ∧ ∀ E ∈ Set.Icc a' b', ∀ y s β : ℝ, |β| ≤ 1 →
        |h E y s - h E (y + β) s| ≤ L * |β|) := by
  have hab' : a < b := lt_trans (lt_of_lt_of_le ha hab) hb
  let U : Set (ℝ × ℝ × ℝ) := Set.Ioo a b ×ˢ (Set.univ ×ˢ Set.univ)
  let Z : ℝ × ℝ × ℝ → ℂ := fun p => smul (C p.1 p.2.1) (vc p.2.2)
  have hproj : Continuous (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) := by fun_prop
  have hC3 : ∀ i j : Fin 2, ContinuousOn (fun p : ℝ × ℝ × ℝ => C p.1 p.2.1 i j) U := by
    intro i j
    refine ContinuousOn.comp ((hana i j).continuousOn) hproj.continuousOn ?_
    intro p hp
    simpa only [U, Set.mem_prod, Set.mem_univ, Set.mem_Ioo, and_true, true_and] using hp
  have hZpos : ∀ p ∈ U, 0 < ‖Z p‖ := by
    intro p hp
    have heq : Z p = smul (C p.1 p.2.1) (vc p.2.2) := rfl
    rw [heq]
    exact norm_pos_iff.mpr (smul_vc_ne_zero (hdet p.1 p.2.1) p.2.2)
  have hZne : 0 ∉ Z '' U := by
    rintro ⟨p, hp, h0⟩
    have h := hZpos p hp
    rw [h0, norm_zero] at h
    exact lt_irrefl 0 h
  have hZcont : ContinuousOn Z U := by
    have hcos : Continuous (fun p : ℝ × ℝ × ℝ => Real.cos (Real.pi * p.2.2)) := by fun_prop
    have hsin : Continuous (fun p : ℝ × ℝ × ℝ => Real.sin (Real.pi * p.2.2)) := by fun_prop
    have hre : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        C p.1 p.2.1 0 0 * Real.cos (Real.pi * p.2.2) +
          C p.1 p.2.1 0 1 * Real.sin (Real.pi * p.2.2)) U :=
      ((hC3 0 0).mul hcos.continuousOn).add ((hC3 0 1).mul hsin.continuousOn)
    have him : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        C p.1 p.2.1 1 0 * Real.cos (Real.pi * p.2.2) +
          C p.1 p.2.1 1 1 * Real.sin (Real.pi * p.2.2)) U :=
      ((hC3 1 0).mul hcos.continuousOn).add ((hC3 1 1).mul hsin.continuousOn)
    have hW : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        ((C p.1 p.2.1 0 0 * Real.cos (Real.pi * p.2.2) +
          C p.1 p.2.1 0 1 * Real.sin (Real.pi * p.2.2) : ℝ) : ℂ)
        + ((C p.1 p.2.1 1 0 * Real.cos (Real.pi * p.2.2) +
          C p.1 p.2.1 1 1 * Real.sin (Real.pi * p.2.2) : ℝ) : ℂ) * Complex.I) U :=
      (Complex.continuous_ofReal.comp_continuousOn hre).add
        ((Complex.continuous_ofReal.comp_continuousOn him).mul continuous_const.continuousOn)
    exact hW.congr (fun p hp => by
      apply Complex.ext <;>
        simp only [Z, smul, vc, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          add_zero, sub_zero, zero_add])
  have hUopen : IsOpen U := by
    change IsOpen (Set.Ioo a b ×ˢ (Set.univ ×ˢ Set.univ))
    exact isOpen_Ioo.prod (isOpen_univ.prod isOpen_univ)
  have hUsc : IsSimplyConnected U := by
    change IsSimplyConnected (Set.Ioo a b ×ˢ (Set.univ ×ˢ Set.univ) : Set (ℝ × ℝ × ℝ))
    have hconv : Convex ℝ (Set.Ioo a b ×ˢ (Set.univ ×ˢ Set.univ) : Set (ℝ × ℝ × ℝ)) :=
      (convex_Ioo a b).prod (convex_univ.prod convex_univ)
    have hne : (Set.Ioo a b ×ˢ (Set.univ ×ˢ Set.univ) : Set (ℝ × ℝ × ℝ)).Nonempty :=
      ⟨((a + b) / 2, 0, 0), ⟨⟨by linarith, by linarith⟩, trivial, trivial⟩⟩
    haveI : ContractibleSpace ↥(Set.Ioo a b ×ˢ (Set.univ ×ˢ Set.univ) : Set (ℝ × ℝ × ℝ)) :=
      hconv.contractibleSpace hne
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨ell, hell_cont, hell_exp⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp (X := ℝ × ℝ × ℝ) hUsc hUopen hZcont hZne
  let h : ℝ → ℝ → ℝ → ℝ := fun E y t => (ell (E, y, t)).im / Real.pi
  have hell_E : ∀ E ∈ Set.Ioo a b, Continuous (fun p : ℝ × ℝ => ell (E, p.1, p.2)) := by
    intro E hE
    have hf : Continuous (fun p : ℝ × ℝ => (E, p.1, p.2)) := by fun_prop
    refine hell_cont.comp_continuous hf (fun p => ?_)
    simpa only [U, Set.mem_prod, Set.mem_univ, Set.mem_Ioo, and_true, true_and] using hE
  have hmemIoo : ∀ E ∈ Set.Icc a' b', E ∈ Set.Ioo a b := fun E hE =>
    ⟨lt_of_lt_of_le ha hE.1, lt_of_le_of_lt hE.2 hb⟩
  -- the two-parameter identity `Z = ‖Z‖ · vc(h)`
  have hmain : ∀ p ∈ U, Z p = (↑‖Z p‖ : ℂ) * vc (h p.1 p.2.1 p.2.2) := by
    intro p hp
    have he : Complex.exp (ell p) = Z p := hell_exp hp
    have hnorm : ‖Z p‖ = Real.exp (ell p).re := by rw [← he, Complex.norm_exp]
    have h1 : Complex.exp (ell p)
        = Complex.exp (↑(ell p).re) * Complex.exp (↑(ell p).im * Complex.I) := by
      conv_lhs => rw [← Complex.re_add_im (ell p)]
      rw [Complex.exp_add]
    have h2 : Complex.exp (↑(ell p).re) = (↑‖Z p‖ : ℂ) := by
      rw [← Complex.ofReal_exp, hnorm]
    have hZex : Z p = (↑‖Z p‖ : ℂ) * Complex.exp (↑(ell p).im * Complex.I) :=
      calc Z p = Complex.exp (ell p) := he.symm
        _ = Complex.exp (↑(ell p).re) * Complex.exp (↑(ell p).im * Complex.I) := h1
        _ = (↑‖Z p‖ : ℂ) * Complex.exp (↑(ell p).im * Complex.I) := by rw [h2]
    have hvc : Complex.exp (↑(ell p).im * Complex.I) = vc (h p.1 p.2.1 p.2.2) := by
      have hpi : Real.pi * ((ell p).im / Real.pi) = (ell p).im := by field_simp
      apply Complex.ext <;>
        simp only [vc, h, hpi, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    exact hZex.trans (by rw [hvc])
  have hvc_unit : ∀ p ∈ U, vc (h p.1 p.2.1 p.2.2) = Z p / (↑‖Z p‖ : ℂ) := by
    intro p hp
    have hne : (↑‖Z p‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hZpos p hp)
    rw [eq_div_iff hne]
    conv_rhs => rw [hmain p hp]
    ring
  -- the periodic angle of `hdeg`
  let η : ℝ → ℝ → ℝ := fun E => (hdeg E).2.choose
  have hη_cont : ∀ E, Continuous (η E) := fun E => (hdeg E).2.choose_spec.1
  have hη_per : ∀ E y, η E (y + 1) = η E y := fun E y => by
    have := (hdeg E).2.choose_spec.2.1 y
    simpa using this
  have hη_pol : ∀ E y, ∃ r : ℝ, 0 < r ∧ C E y 0 0 = r * Real.cos (2 * Real.pi * η E y) ∧
      C E y 1 0 = r * Real.sin (2 * Real.pi * η E y) := fun E y => (hdeg E).2.choose_spec.2.2 y
  -- y-periodicity (period `1` in `y`)
  have hk0 : ∀ E ∈ Set.Ioo a b, ∀ y t : ℝ, h E (y + 1) t = h E y t := by
    intro E hE y t
    have hstep : ∀ z : ℝ, h E (z + 1) 0 = h E z 0 := by
      intro z
      have hgconst : ∀ a b : ℝ, h E a 0 - 2 * η E a = h E b 0 - 2 * η E b := by
        have hgcont : Continuous (fun z : ℝ => h E z 0 - 2 * η E z) := by
          have h1 : Continuous (fun z : ℝ => h E z 0) := by
            have hzc : Continuous (fun z : ℝ => (z, (0 : ℝ))) :=
              continuous_id.prodMk continuous_const
            have hc : Continuous (fun z : ℝ => ell (E, z, 0)) := by
              show Continuous ((fun p : ℝ × ℝ => ell (E, p.1, p.2)) ∘ (fun z : ℝ => (z, (0:ℝ))))
              exact (hell_E E hE).comp hzc
            exact (Complex.continuous_im.comp hc).div_const Real.pi
          exact h1.sub (continuous_const.mul (hη_cont E))
        have hgval : ∀ z : ℝ, ∃ n : ℤ, h E z 0 - 2 * η E z = 2 * (n : ℝ) := by
          intro z
          have hpU : (E, z, 0) ∈ U := by
            simp only [U, Set.mem_prod, Set.mem_univ, Set.mem_Ioo, and_true, true_and]
            exact hE
          have hv := hvc_unit (E, z, 0) hpU
          obtain ⟨r, hr, hp1, hp2⟩ := hη_pol E z
          have hfl := firstcol_lift (A := C E z) hr hp1 hp2
          have hvceq : vc (h E z 0) = vc (2 * η E z) := by rw [hv]; exact hfl
          obtain ⟨m, hm⟩ := vc_eq_iff hvceq
          exact ⟨m, by linarith⟩
        obtain ⟨c, hc⟩ := eq_const_of_two_int hgcont hgval
        intro a b; rw [hc a, hc b]
      have h1 := hgconst z (z + 1)
      have h2 := hη_per E z
      linarith [h1, h2]
    have hFconst : ∀ y t : ℝ, h E (y + 1) t - h E y t = 0 := by
      have hgcont : Continuous (fun p : ℝ × ℝ => h E (p.1 + 1) p.2 - h E p.1 p.2) := by
        have hpc1 : Continuous (fun p : ℝ × ℝ => (p.1 + 1, p.2)) :=
          (continuous_fst.add continuous_const).prodMk continuous_snd
        have hpc0 : Continuous (fun p : ℝ × ℝ => (p.1, p.2)) :=
          continuous_fst.prodMk continuous_snd
        have hc1 : Continuous (fun p : ℝ × ℝ => ell (E, p.1 + 1, p.2)) := by
          show Continuous ((fun p : ℝ × ℝ => ell (E, p.1, p.2)) ∘ (fun p : ℝ × ℝ => (p.1 + 1, p.2)))
          exact (hell_E E hE).comp hpc1
        have hc0 : Continuous (fun p : ℝ × ℝ => ell (E, p.1, p.2)) := hell_E E hE
        exact ((Complex.continuous_im.comp hc1).div_const Real.pi).sub
          ((Complex.continuous_im.comp hc0).div_const Real.pi)
      have hgval : ∀ p : ℝ × ℝ, ∃ n : ℤ,
          h E (p.1 + 1) p.2 - h E p.1 p.2 = 2 * (n : ℝ) := by
        intro p
        have hp1 : (E, p.1 + 1, p.2) ∈ U := by
          simp only [U, Set.mem_prod, Set.mem_univ, Set.mem_Ioo, and_true, true_and]
          exact hE
        have hp0 : (E, p.1, p.2) ∈ U := by
          simp only [U, Set.mem_prod, Set.mem_univ, Set.mem_Ioo, and_true, true_and]
          exact hE
        have hv1 := hvc_unit (E, p.1 + 1, p.2) hp1
        have hv0 := hvc_unit (E, p.1, p.2) hp0
        have hZeq : Z (E, p.1 + 1, p.2) = Z (E, p.1, p.2) := by
          show smul (C E (p.1 + 1)) (vc p.2) = smul (C E p.1) (vc p.2)
          rw [hper E p.1]
        have hvceq : vc (h E (p.1 + 1) p.2) = vc (h E p.1 p.2) := by rw [hv1, hv0, hZeq]
        obtain ⟨m, hm⟩ := vc_eq_iff hvceq
        exact ⟨m, by linarith⟩
      obtain ⟨c, hc⟩ := eq_const_of_two_int hgcont hgval
      have hc0 : c = 0 := by
        have h00 := hc (0, 0)
        have hs00 := hstep 0
        linarith
      intro y t
      have hyt := hc (y, t)
      rw [hc0] at hyt
      linarith
    have h := hFconst y t
    linarith
  -- t-periodicity (period `1` in `t`), via the explicit reference lift
  have hd1 : ∀ E ∈ Set.Ioo a b, ∀ y t : ℝ, h E y (t + 1) = h E y t + 1 := by
    intro E hE y t
    obtain ⟨G, hGcont, hGper, hGvc⟩ := ref_lift (hdet E y)
    have hvcG : ∀ s : ℝ, vc (h E y s) = vc (G s) := by
      intro s
      have hpU : (E, y, s) ∈ U := by
        simp only [U, Set.mem_prod, Set.mem_univ, Set.mem_Ioo, and_true, true_and]; exact hE
      rw [hvc_unit (E, y, s) hpU, hGvc s]
    have hconst : ∀ s : ℝ, h E y s - G s = h E y 0 - G 0 := by
      have hcont : Continuous (fun s : ℝ => h E y s - G s) := by
        have hyc : Continuous (fun s : ℝ => (y, s)) :=
          continuous_const.prodMk continuous_id
        have hc : Continuous (fun s : ℝ => ell (E, y, s)) := by
          show Continuous ((fun p : ℝ × ℝ => ell (E, p.1, p.2)) ∘ (fun s : ℝ => (y, s)))
          exact (hell_E E hE).comp hyc
        exact ((Complex.continuous_im.comp hc).div_const Real.pi).sub hGcont
      have hval : ∀ s : ℝ, ∃ n : ℤ, h E y s - G s = 2 * (n : ℝ) := by
        intro s
        obtain ⟨m, hm⟩ := vc_eq_iff (hvcG s)
        exact ⟨m, by linarith⟩
      obtain ⟨c, hc⟩ := eq_const_of_two_int hcont hval
      intro s; rw [hc s, hc 0]
    linarith [hconst (t + 1), hconst t, hGper t]
  -- integer forms of the two periodicities
  have hpery : ∀ E ∈ Set.Ioo a b, ∀ (m : ℤ) (y t : ℝ), h E (y + m) t = h E y t := by
    intro E hE m
    have hpnat : ∀ n : ℕ, ∀ y t : ℝ, h E (y + n) t = h E y t := by
      intro n
      induction n with
      | zero => intro y t; simp
      | succ k ih =>
          intro y t
          have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
          rw [hcast, show y + ((k : ℝ) + 1) = (y + (k : ℝ)) + 1 by ring, hk0 E hE, ih]
    have hnneg : ∀ n : ℕ, ∀ y t : ℝ, h E (y - n) t = h E y t := by
      intro n
      induction n with
      | zero => intro y t; simp
      | succ k ih =>
          intro y t
          have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
          rw [hcast, show y - ((k : ℝ) + 1) = y - (k : ℝ) - 1 by ring]
          have h2 : h E (y - (k:ℝ)) t = h E (y - (k:ℝ) - 1) t := by
            have hh := hk0 E hE (y - (k:ℝ) - 1) t
            rw [show y - (k:ℝ) - 1 + 1 = y - (k:ℝ) by ring] at hh
            exact hh
          rw [← h2, ih]
    intro y t
    obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg m
    · rw [hn]; exact hpnat n y t
    · rw [hn]
      push_cast
      exact hnneg n y t
  have hpert : ∀ E ∈ Set.Ioo a b, ∀ (n : ℤ) (y t : ℝ), h E y (t + n) = h E y t + n := by
    intro E hE n
    have hpnat : ∀ k : ℕ, ∀ y t : ℝ, h E y (t + k) = h E y t + k := by
      intro k
      induction k with
      | zero => intro y t; simp
      | succ j ih =>
          intro y t
          have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
          rw [hcast, show t + ((j : ℝ) + 1) = (t + (j : ℝ)) + 1 by ring, hd1 E hE, ih]
          ring
    have hnneg : ∀ k : ℕ, ∀ y t : ℝ, h E y (t - k) = h E y t - k := by
      intro k
      induction k with
      | zero => intro y t; simp
      | succ j ih =>
          intro y t
          have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
          rw [hcast, show t - ((j : ℝ) + 1) = t - (j : ℝ) - 1 by ring]
          have h2 : h E y (t - (j:ℝ) - 1) = h E y (t - (j:ℝ)) - 1 := by
            have hh := hd1 E hE y (t - (j:ℝ) - 1)
            rw [show t - (j:ℝ) - 1 + 1 = t - (j:ℝ) by ring] at hh
            linarith [hh]
          rw [h2, ih]
          ring
    intro y t
    obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
    · rw [hk]; exact hpnat k y t
    · rw [hk]
      push_cast
      exact hnneg k y t
  refine ⟨h, ?_, ?_, ?_, ?_, ?_⟩
  · intro E hE
    have hcont := hell_E E (hmemIoo E hE)
    change Continuous (fun p : ℝ × ℝ => (ell (E, p.1, p.2)).im / Real.pi)
    exact (Complex.continuous_im.comp hcont).div_const Real.pi
  · intro E hE y t
    exact hd1 E (hmemIoo E hE) y t
  · intro E hE y t
    have hE' : E ∈ Set.Ioo a b := hmemIoo E hE
    have hpU : (E, y, t) ∈ U := by
      simp only [U, Set.mem_prod, Set.mem_univ, Set.mem_Ioo, and_true, true_and]
      exact hE'
    have hm := hmain (E, y, t) hpU
    have hre : (Z (E, y, t)).re = ‖Z (E, y, t)‖ * Real.cos (Real.pi * h E y t) := by
      conv_lhs => rw [hm]
      simp only [vc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
        sub_zero]
    have him : (Z (E, y, t)).im = ‖Z (E, y, t)‖ * Real.sin (Real.pi * h E y t) := by
      conv_lhs => rw [hm]
      simp only [vc, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
        add_zero]
    have hZeq : Z (E, y, t) = smul (C E y) (vc t) := rfl
    refine ⟨‖Z (E, y, t)‖, ?_, ?_⟩
    · exact ne_of_gt (hZpos (E, y, t) hpU)
    · rw [mulVec_vc]
      show (![(smul (C E y) (vc t)).re, (smul (C E y) (vc t)).im] : Fin 2 → ℝ)
          = ‖Z (E, y, t)‖ • ![Real.cos (Real.pi * h E y t), Real.sin (Real.pi * h E y t)]
      rw [← hZeq, hre, him]
      ext i
      fin_cases i <;> simp
  · -- condition 4 : boundedness of `h - t`
    have hK4 : IsCompact (Set.Icc a' b' ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) :
        Set (ℝ × ℝ × ℝ)) := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have hK4U : (Set.Icc a' b' ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) :
        Set (ℝ × ℝ × ℝ)) ⊆ U := by
      intro p hp
      rw [Set.mem_prod] at hp
      obtain ⟨hpE, hp2⟩ := hp
      exact ⟨⟨lt_of_lt_of_le ha hpE.1, lt_of_le_of_lt hpE.2 hb⟩, trivial, trivial⟩
    have hFK4 : ContinuousOn (fun p : ℝ × ℝ × ℝ => h p.1 p.2.1 p.2.2 - p.2.2)
        (Set.Icc a' b' ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ × ℝ => ell p)
          (Set.Icc a' b' ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)) := hell_cont.mono hK4U
      have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => (ell p).im / Real.pi)
          (Set.Icc a' b' ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)) :=
        (Complex.continuous_im.comp_continuousOn h1).div_const Real.pi
      have h3 : ContinuousOn (fun p : ℝ × ℝ × ℝ => p.2.2)
          (Set.Icc a' b' ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)) := by fun_prop
      exact h2.sub h3
    obtain ⟨Cb, hCb⟩ := hK4.exists_bound_of_continuousOn hFK4
    refine ⟨max Cb 0, le_max_right _ _, ?_⟩
    intro E hE y t
    have hE' : E ∈ Set.Ioo a b := hmemIoo E hE
    have hred : h E y t - t = h E (y - ⌊y⌋) (t - ⌊t⌋) - (t - ⌊t⌋) := by
      have h1 : h E y t = h E (y - ⌊y⌋) t := by
        have hh := hpery E hE' ⌊y⌋ (y - ⌊y⌋) t
        rwa [show (y - (⌊y⌋ : ℝ)) + (⌊y⌋ : ℝ) = y by ring] at hh
      have h2 : h E (y - ⌊y⌋) t = h E (y - ⌊y⌋) (t - ⌊t⌋) + (⌊t⌋ : ℝ) := by
        have hh := hpert E hE' ⌊t⌋ (y - ⌊y⌋) (t - ⌊t⌋)
        rwa [show (t - (⌊t⌋ : ℝ)) + (⌊t⌋ : ℝ) = t by ring] at hh
      rw [h1, h2]; ring
    rw [hred]
    have hmem : (E, y - ⌊y⌋, t - ⌊t⌋) ∈
        (Set.Icc a' b' ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)) :=
      ⟨hE, ⟨by linarith [Int.floor_le y], by linarith [Int.lt_floor_add_one y]⟩,
        ⟨by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩⟩
    have hb := hCb (E, y - ⌊y⌋, t - ⌊t⌋) hmem
    rw [Real.norm_eq_abs] at hb
    exact le_trans hb (le_max_left _ _)
  · -- condition 5 : Lipschitz in `y`
    have hui : UniqueDiffOn ℝ U := hUopen.uniqueDiffOn
    let gproj : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ :=
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
    have hcontEntry : ∀ i j, ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => C p.1 p.2.1 i j) U := by
      intro i j
      have h2 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => C p.1 p.2 i j) (Set.Ioo a b ×ˢ Set.univ) :=
        (hana i j).contDiffOn (isOpen_Ioo.prod isOpen_univ).uniqueDiffOn
      have h3 := h2.comp_continuousLinearMap gproj
      refine h3.mono ?_
      intro p hp
      exact ⟨hp.1, trivial⟩
    have hcos : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => Real.cos (Real.pi * p.2.2)) U := by fun_prop
    have hsin : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => Real.sin (Real.pi * p.2.2)) U := by fun_prop
    have hZcd : ContDiffOn ℝ 1 Z U := by
      have hreC : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ =>
          C p.1 p.2.1 0 0 * Real.cos (Real.pi * p.2.2) +
            C p.1 p.2.1 0 1 * Real.sin (Real.pi * p.2.2)) U :=
        ((hcontEntry 0 0).mul hcos).add ((hcontEntry 0 1).mul hsin)
      have himC : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ =>
          C p.1 p.2.1 1 0 * Real.cos (Real.pi * p.2.2) +
            C p.1 p.2.1 1 1 * Real.sin (Real.pi * p.2.2)) U :=
        ((hcontEntry 1 0).mul hcos).add ((hcontEntry 1 1).mul hsin)
      have h1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ =>
          (((C p.1 p.2.1 0 0 * Real.cos (Real.pi * p.2.2) +
            C p.1 p.2.1 0 1 * Real.sin (Real.pi * p.2.2) : ℝ)) : ℂ)) U :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn hreC
      have h2 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ =>
          (((C p.1 p.2.1 1 0 * Real.cos (Real.pi * p.2.2) +
            C p.1 p.2.1 1 1 * Real.sin (Real.pi * p.2.2) : ℝ)) : ℂ)) U :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn himC
      have h3 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ =>
          (((C p.1 p.2.1 0 0 * Real.cos (Real.pi * p.2.2) +
            C p.1 p.2.1 0 1 * Real.sin (Real.pi * p.2.2) : ℝ)) : ℂ)
          + (((C p.1 p.2.1 1 0 * Real.cos (Real.pi * p.2.2) +
            C p.1 p.2.1 1 1 * Real.sin (Real.pi * p.2.2) : ℝ)) : ℂ) * Complex.I) U :=
        h1.add (h2.mul contDiffOn_const)
      exact h3.congr (fun p hp => by
        apply Complex.ext <;>
          simp only [Z, smul, vc, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
            add_zero, sub_zero, zero_add])
    have hfdc : ContinuousOn (fderiv ℝ Z) U := hZcd.continuousOn_fderiv_of_isOpen hUopen le_rfl
    set K : Set (ℝ × ℝ × ℝ) := Set.Icc a' b' ×ˢ (Set.Icc (-1:ℝ) 2 ×ˢ Set.Icc (0:ℝ) 1) with hKdef
    have hKcomp : IsCompact K := by
      rw [hKdef]
      exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have hKne : K.Nonempty := by
      rw [hKdef]
      exact ⟨(a', (0:ℝ), (0:ℝ)), left_mem_Icc.mpr hab,
        ⟨by norm_num, by norm_num⟩, ⟨le_refl (0:ℝ), by norm_num⟩⟩
    have hKU : K ⊆ U := by
      intro p hp
      rw [hKdef] at hp
      obtain ⟨hpE, hp1, hp2⟩ := hp
      exact ⟨⟨lt_of_lt_of_le ha hpE.1, lt_of_le_of_lt hpE.2 hb⟩, trivial, trivial⟩
    obtain ⟨Kf, hKf⟩ := hKcomp.exists_bound_of_continuousOn (hfdc.mono hKU)
    obtain ⟨pmin, hpminK, hpmin⟩ :=
      hKcomp.exists_isMinOn hKne ((hZcont.mono hKU).norm)
    have hδpos : 0 < ‖Z pmin‖ := hZpos pmin (hKU hpminK)
    set δ : ℝ := ‖Z pmin‖ with hδdef
    have hδle : ∀ p ∈ K, δ ≤ ‖Z p‖ := by
      intro p hp
      rw [hδdef]
      exact hpmin hp
    set L : ℝ := max (Kf / (Real.pi * δ)) 0 with hLdef
    have hdB : ∀ E ∈ Set.Icc a' b', ∀ y ∈ Set.Icc (-1:ℝ) 2, ∀ s ∈ Set.Icc (0:ℝ) 1,
        ∃ g : ℝ, HasDerivAt (fun y' => h E y' s) g y ∧ ‖g‖ ≤ L := by
      intro E hE y hy s hs
      have hE' : E ∈ Set.Ioo a b := hmemIoo E hE
      have hpU : (E, y, s) ∈ U := by
        simp only [U, Set.mem_prod, Set.mem_univ, Set.mem_Ioo, and_true, true_and]
        exact hE'
      have hpK : (E, y, s) ∈ K := by
        rw [hKdef]
        exact ⟨hE, hy, hs⟩
      have hZfd : HasFDerivAt Z (fderiv ℝ Z (E,y,s)) (E,y,s) :=
        ((hZcd.differentiableOn (by norm_num)).differentiableAt (hUopen.mem_nhds hpU)).hasFDerivAt
      have hcurve : HasDerivAt (fun y' : ℝ => (E, y', s)) ((0, (1, 0)) : ℝ × ℝ × ℝ) y := by
        have h1 : HasDerivAt (fun _ : ℝ => E) 0 y := hasDerivAt_const y E
        have h2 : HasDerivAt (fun y' : ℝ => y') 1 y := hasDerivAt_id y
        have h3 : HasDerivAt (fun _ : ℝ => s) 0 y := hasDerivAt_const y s
        exact h1.prodMk (h2.prodMk h3)
      have hslice : HasDerivAt (fun y' : ℝ => Z (E, y', s))
          ((fderiv ℝ Z (E,y,s)) (0,1,0)) y := by
        have hh := hZfd.comp_hasDerivAt y hcurve
        exact hh
      have hZne' : Z (E,y,s) ≠ 0 := norm_pos_iff.mp (hZpos (E,y,s) hpU)
      have hℓcont : ContinuousAt (fun y' : ℝ => ell (E, y', s)) y := by
        have hpc : Continuous (fun y' : ℝ => (y', s)) := continuous_id.prodMk continuous_const
        have hcont : Continuous (fun y' : ℝ => ell (E, y', s)) := by
          show Continuous ((fun p : ℝ × ℝ => ell (E, p.1, p.2)) ∘ (fun y' : ℝ => (y', s)))
          exact (hell_E E hE').comp hpc
        exact hcont.continuousAt
      have hexp : ∀ y' : ℝ, Complex.exp (ell (E, y', s)) = Z (E, y', s) := by
        intro y'
        have hp' : (E, y', s) ∈ U := by
          simp only [U, Set.mem_prod, Set.mem_univ, Set.mem_Ioo, and_true, true_and]
          exact hE'
        exact hell_exp hp'
      have hℓderiv := log_lift_deriv hslice hZne' hℓcont hexp
      refine ⟨((fderiv ℝ Z (E,y,s)) (0,1,0) / Z (E,y,s)).im / Real.pi, ?_, ?_⟩
      · have him : HasDerivAt (fun y' => (ell (E, y', s)).im)
            ((fderiv ℝ Z (E,y,s)) (0,1,0) / Z (E,y,s)).im y := by
          have hh := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y hℓderiv
          exact hh
        have hh := him.div_const Real.pi
        simpa only [h] using hh
      · have hfdb : ‖fderiv ℝ Z (E,y,s)‖ ≤ Kf := hKf (E,y,s) hpK
        have hZlb : δ ≤ ‖Z (E,y,s)‖ := hδle (E,y,s) hpK
        have h01 : ‖((0:ℝ), (1:ℝ), (0:ℝ))‖ = 1 := by
          simp [Prod.norm_def, Real.norm_eq_abs]
        have hnum : ‖(fderiv ℝ Z (E,y,s)) (0,1,0)‖ ≤ Kf := by
          calc ‖(fderiv ℝ Z (E,y,s)) (0,1,0)‖
              ≤ ‖fderiv ℝ Z (E,y,s)‖ * ‖((0:ℝ), (1:ℝ), (0:ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
            _ = ‖fderiv ℝ Z (E,y,s)‖ * 1 := by rw [h01]
            _ = ‖fderiv ℝ Z (E,y,s)‖ := mul_one _
            _ ≤ Kf := hfdb
        have hg : ‖(fderiv ℝ Z (E,y,s)) (0,1,0) / Z (E,y,s)‖ ≤ Kf / δ := by
          rw [norm_div]
          exact div_le_div₀ (le_trans (norm_nonneg _) hnum) hnum hδpos hZlb
        calc ‖((fderiv ℝ Z (E,y,s)) (0,1,0) / Z (E,y,s)).im / Real.pi‖
            = |((fderiv ℝ Z (E,y,s)) (0,1,0) / Z (E,y,s)).im| / Real.pi := by
              rw [Real.norm_eq_abs, abs_div, abs_of_pos Real.pi_pos]
          _ ≤ ‖(fderiv ℝ Z (E,y,s)) (0,1,0) / Z (E,y,s)‖ / Real.pi :=
              div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) Real.pi_pos.le
          _ ≤ (Kf / δ) / Real.pi := div_le_div_of_nonneg_right hg Real.pi_pos.le
          _ = Kf / (Real.pi * δ) := by rw [div_div, mul_comm δ Real.pi]
          _ ≤ L := le_max_left _ _
    refine ⟨L, le_max_right _ _, ?_⟩
    intro E hE y s β hβ
    have hE' : E ∈ Set.Ioo a b := hmemIoo E hE
    set s0 : ℝ := s - ⌊s⌋ with hs0def
    have hs0mem : s0 ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by linarith [Int.floor_le s], by linarith [Int.lt_floor_add_one s]⟩
    have hsdiff : h E y s - h E (y + β) s = h E y s0 - h E (y + β) s0 := by
      have h1 : h E y s = h E y s0 + (⌊s⌋ : ℝ) := by
        have hh := hpert E hE' ⌊s⌋ y s0
        rwa [show s0 + ((⌊s⌋ : ℤ) : ℝ) = s by rw [hs0def]; ring] at hh
      have h2 : h E (y + β) s = h E (y + β) s0 + (⌊s⌋ : ℝ) := by
        have hh := hpert E hE' ⌊s⌋ (y + β) s0
        rwa [show s0 + ((⌊s⌋ : ℤ) : ℝ) = s by rw [hs0def]; ring] at hh
      rw [h1, h2]; ring
    rw [hsdiff]
    set y0 : ℝ := y - ⌊y⌋ with hy0def
    have hy0mem : y0 ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by linarith [Int.floor_le y], by linarith [Int.lt_floor_add_one y]⟩
    have hydiff1 : h E y s0 = h E y0 s0 := by
      have hh := hpery E hE' ⌊y⌋ y0 s0
      rwa [show y0 + ((⌊y⌋ : ℤ) : ℝ) = y by rw [hy0def]; ring] at hh
    have hydiff2 : h E (y + β) s0 = h E (y0 + β) s0 := by
      have hh := hpery E hE' ⌊y⌋ (y0 + β) s0
      rwa [show (y0 + β) + ((⌊y⌋ : ℤ) : ℝ) = y + β by rw [hy0def]; ring] at hh
    rw [hydiff1, hydiff2]
    have hβ1 : -(1:ℝ) ≤ β := (abs_le.mp hβ).1
    have hβ2 : β ≤ 1 := (abs_le.mp hβ).2
    have hy0β : y0 + β ∈ Set.Icc (-1:ℝ) 2 := ⟨by linarith [hy0mem.1], by linarith [hy0mem.2]⟩
    have hseg : (Set.Icc (min y0 (y0 + β)) (max y0 (y0 + β)) : Set ℝ) ⊆ Set.Icc (-1:ℝ) 2 := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      constructor
      · have h1 : (-1:ℝ) ≤ min y0 (y0+β) :=
          le_min (by linarith [hy0mem.1, hβ1]) (by linarith [hy0mem.1, hβ1])
        linarith
      · have h1 : max y0 (y0+β) ≤ 2 :=
          max_le (by linarith [hy0mem.2, hβ2]) (by linarith [hy0β.2])
        linarith
    have hdAt : ∀ x ∈ Set.Icc (min y0 (y0 + β)) (max y0 (y0 + β)),
        HasDerivAt (fun y' => h E y' s0) (deriv (fun y' => h E y' s0) x) x := by
      intro x hx
      obtain ⟨g, hg, -⟩ := hdB E hE x (hseg hx) s0 hs0mem
      rw [hg.deriv]
      exact hg
    have hbound : ∀ x ∈ Set.Icc (min y0 (y0 + β)) (max y0 (y0 + β)),
        ‖deriv (fun y' => h E y' s0) x‖ ≤ L := by
      intro x hx
      obtain ⟨g, hg, hgb⟩ := hdB E hE x (hseg hx) s0 hs0mem
      rw [hg.deriv]; exact hgb
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun y' => h E y' s0) (s := Set.Icc (min y0 (y0 + β)) (max y0 (y0 + β)))
      (x := y0) (y := y0 + β) (C := L)
      (fun x hx => (hdAt x hx).differentiableAt) hbound (convex_Icc _ _)
      ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
    rw [Real.norm_eq_abs, show (y0 + β) - y0 = β by ring] at hmvt
    calc |h E y0 s0 - h E (y0 + β) s0| = |h E (y0 + β) s0 - h E y0 s0| := abs_sub_comm _ _
      _ ≤ L * |β| := hmvt

end

end Work.TMC13
