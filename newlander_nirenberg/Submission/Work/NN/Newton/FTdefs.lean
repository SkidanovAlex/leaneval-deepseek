import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Final.flatTwoTunableLinear
import Submission.Work.NN.Core.TelTwoDF.Setup
import Submission.Work.NN.Core.TelTwoDF.S2_smooth
import Submission.Work.NN.Core.TelTwoDF.S2Bound
import Submission.Work.NN.Core.bmRow_holder
import Submission.Work.NN.Core.bmPotential_gain
import Submission.Work.NN.Core.sharpCut
import Submission.Work.NN.Final.iterDerivNorm_comp_smul


namespace Work.NN.Newton

open scoped ENNReal ContDiff

open Set

/-- Chain rule for `∂̄` under a real dilation. -/
lemma dbarCoord_comp_smul {n : ℕ} (j : Fin n) (c : ℝ) (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord j (fun y => g (c • y)) z
      = (c : ℂ) * Work.CR.Flat.dbarCoord j g (c • z) := by
  simp only [Work.CR.Flat.dbarCoord]
  rw [fderiv_comp_smul]
  simp only [smul_apply, Complex.real_smul]
  ring

/-- A dilation carries the polydisc of radius `ρ/c` onto that of radius `ρ`. -/
lemma smul_mem_polydisc_iff {n : ℕ} {c : ℝ} (hc : 0 < c) (ρ : Fin n → ℝ) (z : Fin n → ℂ) :
    c • z ∈ Work.CR.Flat.polydisc 0 ρ ↔ z ∈ Work.CR.Flat.polydisc 0 (fun j => ρ j / c) := by
  simp only [Work.NN.Final.tun_mem_polydisc_zero]
  constructor <;> intro h j
  · have h1 : c * ‖z j‖ < ρ j := by
      have h2 := h j
      rwa [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc.le] at h2
    have h2 : ρ j / c * c = ρ j := div_mul_cancel₀ _ (ne_of_gt hc)
    nlinarith [hc, h1, h2]
  · have h1 : ‖z j‖ < ρ j / c := h j
    have h2 : ρ j / c * c = ρ j := div_mul_cancel₀ _ (ne_of_gt hc)
    have h3 : c * ‖z j‖ < ρ j := by nlinarith [hc, h1, h2]
    show ‖(c • z) j‖ < ρ j
    rwa [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc.le]

/-- Pulling a function back along a dilation multiplies the `C^{k,α}` norm by at most
`max 1 |c| ^ (k+α)`. -/
lemma holderNorm_comp_smul_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ℕ) {α : ℝ} (hα0 : 0 ≤ α) {c : ℝ} (hc : c ≠ 0) {Ω : Set X} (hΩ : IsOpen Ω)
    (f : X → ℂ) :
    Work.CR.Flat.holderNorm k α (fun z => f (c • z)) {z | c • z ∈ Ω}
      ≤ ENNReal.ofReal (max 1 (|c| ^ ((k : ℝ) + α))) * Work.CR.Flat.holderNorm k α f Ω := by
  set M : ℝ≥0∞ := ENNReal.ofReal (max 1 (|c| ^ ((k : ℝ) + α))) with hMdef
  have hkey1 : ∀ i ≤ k, ENNReal.ofReal (|c| ^ i) * Work.CR.Flat.iterDerivNorm i f Ω
      ≤ M * Work.CR.Flat.iterDerivNorm i f Ω := by
    intro i hi
    refine mul_le_mul_left ?_ _
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_or_gt 1 |c| with hc1 | hc1
    · have h : |c| ^ (i : ℝ) ≤ |c| ^ ((k : ℝ) + α) :=
        Real.rpow_le_rpow_of_exponent_le hc1 (by
          have : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hi
          linarith)
      rw [Real.rpow_natCast] at h
      exact h.trans (le_max_right _ _)
    · calc |c| ^ i ≤ 1 ^ i := pow_le_pow_left₀ (abs_nonneg c) hc1.le i
        _ = 1 := one_pow i
        _ ≤ _ := le_max_left _ _
  have hkey2 : ∀ i ≤ k, ENNReal.ofReal (|c| ^ ((i : ℝ) + α)) * Work.CR.Flat.holderSeminorm i α f Ω
      ≤ M * Work.CR.Flat.holderSeminorm i α f Ω := by
    intro i hi
    refine mul_le_mul_left ?_ _
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_or_gt 1 |c| with hc1 | hc1
    · exact (Real.rpow_le_rpow_of_exponent_le hc1 (by
        have : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hi
        linarith)).trans (le_max_right _ _)
    · calc |c| ^ ((i : ℝ) + α) ≤ 1 ^ ((i : ℝ) + α) :=
            Real.rpow_le_rpow (abs_nonneg c) hc1.le (by positivity)
        _ = 1 := Real.one_rpow _
        _ ≤ _ := le_max_left _ _
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  obtain ⟨h1, h2⟩ := Work.NN.Final.iterDerivNorm_comp_smul c hc i α f hΩ
  rw [h1, h2, mul_add]
  exact add_le_add (hkey1 i hik) (hkey2 i hik)


/-- The dilation-pullback bound on a polydisc: `z ↦ f (c • z)` on the polydisc of radius `ρ/c`. -/
lemma holderNorm_comp_smul_polydisc_le {n : ℕ} {k : ℕ} {α : ℝ} (hα0 : 0 ≤ α)
    {c : ℝ} (hc : 0 < c) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (f : (Fin n → ℂ) → ℂ) :
    Work.CR.Flat.holderNorm k α (fun z => f (c • z))
        (Work.CR.Flat.polydisc 0 (fun j => ρ j / c))
      ≤ ENNReal.ofReal (max 1 (|c| ^ ((k : ℝ) + α)))
          * Work.CR.Flat.holderNorm k α f (Work.CR.Flat.polydisc 0 ρ) := by
  have hset : {z : Fin n → ℂ | c • z ∈ Work.CR.Flat.polydisc 0 ρ}
      = Work.CR.Flat.polydisc 0 (fun j => ρ j / c) := by
    ext z
    exact smul_mem_polydisc_iff hc ρ z
  rw [← hset]
  exact holderNorm_comp_smul_le k hα0 (ne_of_gt hc) (Work.CR.Flat.isOpen_polydisc 0 ρ) f

variable {n : ℕ}

/-- The product cutoff on `ℂⁿ`: `1` on the polydisc of radius `a`, vanishing outside the (closed)
polydisc of radius `b`. -/
noncomputable def ftCut (n : ℕ) (a b : ℝ) (z : Fin n → ℂ) : ℂ :=
  ∏ j : Fin n, Work.NN.Core.sharpCut a b (z j)

@[simp] lemma ftCut_apply (a b : ℝ) (z : Fin n → ℂ) :
    ftCut n a b z = ∏ j : Fin n, Work.NN.Core.sharpCut a b (z j) := rfl

lemma contDiff_ftCut (a b : ℝ) : ContDiff ℝ ∞ (ftCut n a b) :=
  contDiff_prod fun j _ => (Work.NN.Core.contDiff_sharpCut (a := a) (b := b)).comp
    (contDiff_apply ℝ ℂ j)

lemma ftCut_eq_one {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {z : Fin n → ℂ} (h : ∀ j, ‖z j‖ ≤ a) :
    ftCut n a b z = 1 := by
  rw [ftCut_apply]
  exact Finset.prod_eq_one fun j _ => Work.NN.Core.sharpCut_eq_one ha hab (h j)

lemma ftCut_eq_zero {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {z : Fin n → ℂ} {j : Fin n}
    (h : b ≤ ‖z j‖) : ftCut n a b z = 0 := by
  rw [ftCut_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (Work.NN.Core.sharpCut_eq_zero ha hab h)

lemma norm_ftCut_le_one (a b : ℝ) (z : Fin n → ℂ) : ‖ftCut n a b z‖ ≤ 1 := by
  have h : ‖ftCut n a b z‖₊ ≤ 1 := by
    rw [ftCut_apply, nnnorm_prod]
    refine Finset.prod_le_one (fun j _ => ?_)
    rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm]
    exact Work.NN.Core.norm_sharpCut_le_one a b (z j)
  exact_mod_cast h

lemma closedPolydisc_isCompact (b : ℝ) :
    IsCompact {z : Fin n → ℂ | ∀ j, ‖z j‖ ≤ b} := by
  have h : {z : Fin n → ℂ | ∀ j, ‖z j‖ ≤ b}
      = Set.univ.pi (fun _ : Fin n => Metric.closedBall (0 : ℂ) b) := by
    ext z; simp [Metric.mem_closedBall, dist_eq_norm]
  rw [h]
  exact isCompact_univ_pi fun _ => isCompact_closedBall 0 b

lemma hasCompactSupport_ftCut {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    HasCompactSupport (ftCut n a b) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := {z : Fin n → ℂ | ∀ j, ‖z j‖ ≤ b}) (closedPolydisc_isCompact b) ?_
  intro z hz
  by_contra hcon
  simp only [mem_setOf_eq, not_forall, not_le] at hcon
  obtain ⟨j, hj⟩ := hcon
  exact hz (ftCut_eq_zero ha hab (le_of_lt hj))

lemma tsupport_ftCut {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    tsupport (ftCut n a b) ⊆ {z : Fin n → ℂ | ∀ j, ‖z j‖ ≤ b} := by
  refine closure_minimal (fun z hz => ?_) (isClosed_le (continuous_pi fun j =>
    (continuous_norm.comp (continuous_apply j))) continuous_const)
  intro j
  by_contra hcon
  simp only [mem_setOf_eq, not_le] at hcon
  exact hz (ftCut_eq_zero ha hab (le_of_lt hcon))

/-- The telescope geometry for a gap `δ`: target radius `1 - δ`, data radius `1 - 7δ/8`. -/
noncomputable def ftG (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    Work.NN.Core.TelTwoDF.Geom n :=
  { e := fun _ => 1 - δ
    a := fun _ => 1 - 15 * δ / 16
    b := fun _ => 1 - 7 * δ / 8
    r := fun _ => 2 * (1 - 7 * δ / 8)
    he := fun _ => by linarith
    hea := fun _ => by linarith
    ha := fun _ => by linarith
    hab := fun _ => by linarith
    hr := fun _ => by linarith
    hbr := fun _ => by linarith }

lemma ftG_e (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (k : Fin n) :
    (ftG (n := n) δ hδ0 hδ4).e k = 1 - δ := rfl

lemma ftG_a (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (k : Fin n) :
    (ftG (n := n) δ hδ0 hδ4).a k = 1 - 15 * δ / 16 := rfl

lemma ftG_b (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (k : Fin n) :
    (ftG (n := n) δ hδ0 hδ4).b k = 1 - 7 * δ / 8 := rfl

lemma ftG_r (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (k : Fin n) :
    (ftG (n := n) δ hδ0 hδ4).r k = 2 * (1 - 7 * δ / 8) := rfl



/-- The cutoff of the thin-gap construction. -/
noncomputable def ftChi (n : ℕ) (δ : ℝ) : (Fin n → ℂ) → ℂ :=
  ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8)

@[simp] lemma ftChi_apply (δ : ℝ) (z : Fin n → ℂ) :
    ftChi n δ z = ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8) z := rfl

lemma contDiff_ftChi (δ : ℝ) : ContDiff ℝ ∞ (ftChi n δ) := contDiff_ftCut _ _

lemma ftChi_eq_one {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) {z : Fin n → ℂ}
    (h : ∀ j, ‖z j‖ ≤ 1 - 3 * δ / 4) : ftChi n δ z = 1 :=
  ftCut_eq_one (by linarith) (by linarith) h

lemma hasCompactSupport_ftChi {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    HasCompactSupport (ftChi n δ) :=
  hasCompactSupport_ftCut (a := 1 - 3 * δ / 4) (b := 1 - 5 * δ / 8) (by linarith) (by linarith)

lemma tsupport_ftChi {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    tsupport (ftChi n δ) ⊆ Work.CR.Flat.polydisc 0 (fun _ => 1 - δ / 2) := by
  intro z hz
  rw [Work.NN.Final.tun_mem_polydisc_zero]
  intro j
  have h2 : ‖z j‖ ≤ 1 - 5 * δ / 8 :=
    tsupport_ftCut (a := 1 - 3 * δ / 4) (b := 1 - 5 * δ / 8) (by linarith) (by linarith) hz j
  linarith

lemma ftChi_eq_one_of_mem {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) {z : Fin n → ℂ}
    (hz : z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1 - 3 * δ / 4)) : ftChi n δ z = 1 := by
  refine ftChi_eq_one hδ0 hδ4 fun j => ?_
  rw [Work.NN.Final.tun_mem_polydisc_zero] at hz
  exact le_of_lt (hz j)

lemma polydisc_const_mono {a b : ℝ} (h : a ≤ b) :
    Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => a)
      ⊆ Work.CR.Flat.polydisc 0 (fun _ => b) :=
  Work.CR.Flat.polydisc_mono fun _ => h

/-- The Bochner–Martinelli row potential of `χ η`. -/
noncomputable def ftPsi1 (n : ℕ) (δ : ℝ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    Fin n → (Fin n → ℂ) → ℂ :=
  Work.NN.Core.bmRow (fun a b w => ftChi n δ w * η a b w)

/-- The `(0,2)`-defect of one Bochner–Martinelli step with the thin cutoff. -/
noncomputable def ftEdat (n : ℕ) (δ : ℝ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    Fin n → Fin n → (Fin n → ℂ) → ℂ :=
  Work.NN.Assemble.FT.Edat (ftChi n δ) η

/-- The telescoping solution of the defect. -/
noncomputable def ftPsi2 (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) : Fin n → (Fin n → ℂ) → ℂ :=
  Work.NN.Core.TelTwoDF.S2 (ftG (n := n) δ hδ0 hδ4) (ftEdat n δ η)

lemma ftPsi1_apply (δ : ℝ) (η : _) (j : Fin n) :
    ftPsi1 n δ η j = Work.NN.Core.bmRow (fun a b w => ftChi n δ w * η a b w) j := rfl

lemma ftPsi2_apply {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (η : _) (j : Fin n) :
    ftPsi2 n δ hδ0 hδ4 η j
      = Work.NN.Core.TelTwoDF.S2 (ftG (n := n) δ hδ0 hδ4) (ftEdat n δ η) j := rfl

lemma ftEdat_apply (δ : ℝ) (η : _) (i m : Fin n) :
    ftEdat n δ η i m = Work.NN.Assemble.FT.Edat (ftChi n δ) η i m := rfl

/-- Smoothness of the Bochner–Martinelli part. -/
lemma contDiff_ftPsi1 {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ j l (m : ℕ), ContDiffOn ℝ m (η j l) (Work.CR.Flat.polydisc 0 (fun _ => 1)))
    (hn : 0 < n) (m : ℕ) (j : Fin n) : ContDiff ℝ m (ftPsi1 n δ η j) := by
  refine Work.NN.Assemble.FT.contDiff_bmRow hn (m := m) (fun i l => ?_) (fun i l => ?_) j
  · exact Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport
      (Work.CR.Flat.isOpen_polydisc 0 (fun _ => 1))
      (contDiff_ftChi δ) ((tsupport_ftChi hδ0 hδ4).trans (polydisc_const_mono (by linarith)))
      (hη i l m)
  · exact (hasCompactSupport_ftChi (n := n) hδ0 hδ4).mul_right

/-- Smoothness of the defect. -/
lemma contDiff_ftEdat {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ j l (m : ℕ), ContDiffOn ℝ m (η j l) (Work.CR.Flat.polydisc 0 (fun _ => 1)))
    (hn : 0 < n) (N : ℕ) (i m : Fin n) : ContDiff ℝ N (ftEdat n δ η i m) := by
  have hts : ∀ a : Fin n, tsupport (fun w => Work.CR.Flat.dbarCoord a (ftChi n δ) w)
      ⊆ Work.CR.Flat.polydisc 0 (fun _ => 1) := fun a =>
    (Work.NN.Assemble.FT.tsupport_dbarCoord_subset a).trans
      ((tsupport_ftChi hδ0 hδ4).trans (polydisc_const_mono (by linarith)))
  have hb : ∀ (a b c : Fin n),
      ContDiff ℝ N (fun w => Work.CR.Flat.dbarCoord a (ftChi n δ) w * η b c w) := fun a b c =>
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport
      (Work.CR.Flat.isOpen_polydisc 0 (fun _ => 1))
      (Work.NN.Assemble.FT.contDiff_dbarCoord_of (contDiff_ftChi δ) a) (hts a) (hη b c N)
  rw [ftEdat_apply,
    show Work.NN.Assemble.FT.Edat (ftChi n δ) η i m = fun z =>
      (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
        Work.CR.Flat.Cauchy.bmPot (fun j => Work.NN.Core.bmH (ftChi n δ) η i m j) z from rfl]
  refine contDiff_const.mul (Work.NN.Assemble.FT.contDiff_bmPot hn (m := N) (fun j => ?_)
    (fun j => ?_))
  · show ContDiff ℝ N (fun w => Work.CR.Flat.dbarCoord j (ftChi n δ) w * η i m w
        + Work.CR.Flat.dbarCoord i (ftChi n δ) w * η m j w
        - Work.CR.Flat.dbarCoord m (ftChi n δ) w * η i j w)
    exact ((hb j i m).add (hb i m j)).sub (hb m i j)
  · exact Work.NN.Assemble.FT.bmH_hasCompactSupport (hasCompactSupport_ftChi hδ0 hδ4) i m j

/-- Smoothness of the telescoping part. -/
lemma contDiffOn_ftPsi2 {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ j l (m : ℕ), ContDiffOn ℝ m (η j l) (Work.CR.Flat.polydisc 0 (fun _ => 1)))
    (hn : 0 < n) (m : ℕ) (j : Fin n) :
    ContDiffOn ℝ m (ftPsi2 n δ hδ0 hδ4 η j)
      (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ)) := by
  refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
  have hx' : ∀ k : Fin n, ‖x k‖ < 1 - δ := by
    rw [Work.NN.Final.tun_mem_polydisc_zero] at hx; exact hx
  set ρ' : Fin n → ℝ := fun k => (‖x k‖ + (1 - δ)) / 2 with hρ'
  have hρ'pos : ∀ k, 0 < ρ' k := fun k => by
    have hk := hx' k; simp only [hρ']; linarith [norm_nonneg (x k)]
  have hρ'lt : ∀ k, ρ' k < (ftG (n := n) δ hδ0 hδ4).e k := fun k => by
    rw [ftG_e]; have hk := hx' k; simp only [hρ']; linarith [norm_nonneg (x k)]
  have hxmem : x ∈ Work.CR.Flat.polydisc 0 ρ' := by
    rw [Work.NN.Final.tun_mem_polydisc_zero]; intro k; simp only [hρ']
    have hk := hx' k
    linarith [norm_nonneg (x k)]
  refine ⟨Work.CR.Flat.polydisc 0 ρ', Work.CR.Flat.isOpen_polydisc 0 ρ', hxmem, ?_⟩
  have hsm : ContDiffOn ℝ m (ftPsi2 n δ hδ0 hδ4 η j)
      (Work.CR.Flat.polydisc 0 ρ') := by
    rw [ftPsi2_apply]
    exact Work.NN.Core.TelTwoDF.S2_smooth (ftG (n := n) δ hδ0 hδ4) hρ'pos hρ'lt
      (fun N i l => contDiff_ftEdat hδ0 hδ4 hη hn N i l) j m
  exact hsm.mono Set.inter_subset_right



/-- **Assembly of the thin-gap `(0,2)`-Poincaré on the unit polydisc.**  Given the three
quantitative estimates (Bochner–Martinelli row potential, telescoping solution, defect), the
constructive solution satisfies the equation, is smooth, and obeys the polynomial bound. -/
theorem flatTwoThin_assembly {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hBm : ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
      (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiffOn ℝ 1 (η i l) (Work.CR.Flat.polydisc 0 (fun _ => 1))) → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (ftPsi1 n δ η j)
          (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))
        ≤ ENNReal.ofReal (K / δ ^ N) * ∑ a : Fin n, ∑ b : Fin n,
            Work.CR.Flat.holderNorm 0 α (η a b) (Work.CR.Flat.polydisc 0 (fun _ => 1)))
    (hTel : ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
      (E : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiff ℝ 1 (E i l)) → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α
          (Work.NN.Core.TelTwoDF.S2 (ftG (n := n) δ hδ0 hδ4) E j)
          (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))
        ≤ ENNReal.ofReal (K / δ ^ N) * ∑ a : Fin n, ∑ b : Fin n,
            Work.CR.Flat.holderNorm 1 α (E a b)
              (Work.CR.Flat.polydisc 0 (fun _ => 1 - 7 * δ / 8)))
    (hEd : ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
      (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiffOn ℝ 1 (η i l) (Work.CR.Flat.polydisc 0 (fun _ => 1))) →
      ∀ (T : ℝ), 1 / 2 ≤ T → T ≤ 1 →
      (∑ a : Fin n, ∑ b : Fin n,
          Work.CR.Flat.holderNorm 1 α (ftEdat n δ η a b)
            (Work.CR.Flat.polydisc 0 (fun _ => T)))
        ≤ ENNReal.ofReal (K / δ ^ N) * ∑ a : Fin n, ∑ b : Fin n,
            Work.CR.Flat.holderNorm 0 α (η a b) (Work.CR.Flat.polydisc 0 (fun _ => 1))) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
      (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ j l (m : ℕ), ContDiffOn ℝ m (η j l) (Work.CR.Flat.polydisc 0 (fun _ => 1))) →
      (∀ j l z, η j l z = - η l j z) →
      (∀ j l k z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1) →
        Work.CR.Flat.dbarCoord j (η l k) z - Work.CR.Flat.dbarCoord l (η j k) z
          + Work.CR.Flat.dbarCoord k (η j l) z = 0) →
      ∃ ψ : Fin n → (Fin n → ℂ) → ℂ,
        (∀ j (m : ℕ), ContDiffOn ℝ m (ψ j) (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))) ∧
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1 - δ) →
          Work.CR.Flat.dbarCoord j (ψ l) z - Work.CR.Flat.dbarCoord l (ψ j) z = η j l z) ∧
        (∀ j, Work.CR.Flat.holderNorm 1 α (ψ j) (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))
          ≤ ENNReal.ofReal (C / δ ^ N) * ∑ j, ∑ l,
              Work.CR.Flat.holderNorm 0 α (η j l) (Work.CR.Flat.polydisc 0 (fun _ => 1))) := by
  obtain ⟨KB, hKB0, NB, hBm⟩ := hBm
  obtain ⟨KT, hKT0, NT, hTel⟩ := hTel
  obtain ⟨KE, hKE0, NE, hEd⟩ := hEd
  refine ⟨KB + KT * KE + 1, by positivity, NB + NT + NE, ?_⟩
  intro δ hδ0 hδ4 η hη hanti hcl
  have hδ1 : δ < 1 := by linarith
  -- smoothness of `η` on the smaller polydisc
  have hη1 : ∀ i l, ContDiffOn ℝ 1 (η i l) (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ / 2)) :=
    fun i l => (hη i l 1).mono (polydisc_const_mono (by linarith))
  -- the Bochner–Martinelli defect identity
  have hbmDef : ∀ j l z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1 - δ) →
      Work.CR.Flat.dbarCoord j (ftPsi1 n δ η l) z
        - Work.CR.Flat.dbarCoord l (ftPsi1 n δ η j) z
        = η j l z + Work.NN.Core.bmDefect (ftChi n δ) η j l z := by
    intro j l z hz
    have h := Work.NN.Final.tun_bmDefect (n := n) hn
      (r := fun _ => 1 - δ / 2) (r₁ := fun _ => 1 - δ) (R := fun _ => 1)
      (by intro j; norm_num) (by intro j; linarith) (by intro j; linarith)
      (contDiff_ftChi (n := n) δ) (hasCompactSupport_ftChi (n := n) hδ0 hδ4)
      (tsupport_ftChi (n := n) hδ0 hδ4)
      (V := Work.CR.Flat.polydisc 0 (fun _ => 1 - 3 * δ / 4))
      (Work.CR.Flat.isOpen_polydisc _ _)
      (by
        intro y hy
        rw [Work.NN.Final.tun_mem_polydisc_zero]
        intro k
        have h1 : y k ∈ Metric.closedBall (0 : ℂ) (1 - δ) := Set.mem_univ_pi.mp hy k
        rw [Metric.mem_closedBall, dist_eq_norm] at h1
        simp only [sub_zero] at h1
        linarith)
      (fun y hy => ftChi_eq_one_of_mem hδ0 hδ4 hy)
      (fun i l => hη i l 1)
      (fun i l m z hz => hcl i l m z hz)
      j l z hz
    simpa only [ftPsi1_apply] using h
  -- the defect is minus the Edat term
  have hψ₁eq : ∀ j l z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1 - δ) →
      Work.CR.Flat.dbarCoord j (ftPsi1 n δ η l) z
        - Work.CR.Flat.dbarCoord l (ftPsi1 n δ η j) z = η j l z - ftEdat n δ η j l z := by
    intro j l z hz
    rw [hbmDef j l z hz]
    have hχz : ftChi n δ z = 1 :=
      ftChi_eq_one_of_mem hδ0 hδ4 (polydisc_const_mono (by linarith) hz)
    rw [Work.NN.Core.bmDefect_apply, ftEdat_apply, Work.NN.Assemble.FT.Edat_apply, hχz]
    ring
  -- the telescope solves the equation for the defect
  have hE1 : ∀ i m, ContDiff ℝ 1 (ftEdat n δ η i m) :=
    fun i m => contDiff_ftEdat hδ0 hδ4 hη hn 1 i m
  have hEanti : ∀ i m z, ftEdat n δ η i m z = - ftEdat n δ η m i z := by
    intro i m z
    rw [ftEdat_apply, ftEdat_apply]
    exact Work.NN.Final.tun_Edat_antisymm hn (contDiff_ftChi (n := n) δ)
      (hasCompactSupport_ftChi (n := n) hδ0 hδ4) (tsupport_ftChi (n := n) hδ0 hδ4) hη1
      (fun i l z hz => hanti i l z) i m z
  have hEcl : ∀ i l m' z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1 - 7 * δ / 8) →
      Work.CR.Flat.dbarCoord i (ftEdat n δ η l m') z
        - Work.CR.Flat.dbarCoord l (ftEdat n δ η i m') z
        + Work.CR.Flat.dbarCoord m' (ftEdat n δ η i l) z = 0 := by
    intro i l m' z hz
    exact Work.NN.Final.tun_Edat_closed (n := n) hn (r := fun _ => 1 - δ / 2)
      (R := fun _ => 1) (S := fun _ => 1 - 7 * δ / 8)
      (by intro j; linarith) (by intro j; linarith)
      (contDiff_ftChi (n := n) δ) (hasCompactSupport_ftChi (n := n) hδ0 hδ4)
      (tsupport_ftChi (n := n) hδ0 hδ4)
      (V := Work.CR.Flat.polydisc 0 (fun _ => 1 - 3 * δ / 4)) (Work.CR.Flat.isOpen_polydisc _ _)
      (by
        intro y hy
        rw [Work.NN.Final.tun_mem_polydisc_zero]
        intro k
        have h1 : y k ∈ Metric.closedBall (0 : ℂ) (1 - 7 * δ / 8) := Set.mem_univ_pi.mp hy k
        rw [Metric.mem_closedBall, dist_eq_norm] at h1
        simp only [sub_zero] at h1
        linarith)
      (fun y hy => ftChi_eq_one_of_mem hδ0 hδ4 hy)
      (fun i l => (hη i l 1).mono (polydisc_const_mono (by linarith)))
      (fun j l m z hz => hcl j l m z hz)
      i l m' z hz
  have hEcl' : ∀ i l m' z, (∀ k : Fin n, ‖z k‖ < (ftG (n := n) δ hδ0 hδ4).b k) →
      Work.CR.Flat.dbarCoord i (ftEdat n δ η l m') z
        - Work.CR.Flat.dbarCoord l (ftEdat n δ η i m') z
        + Work.CR.Flat.dbarCoord m' (ftEdat n δ η i l) z = 0 := by
    intro i l m' z hz
    refine hEcl i l m' z ?_
    rw [Work.NN.Final.tun_mem_polydisc_zero]
    intro k
    have hk := hz k
    rwa [ftG_b] at hk
  have hTelSolves := Work.NN.Core.TelTwoDF.S2_solves (ftG (n := n) δ hδ0 hδ4) hE1 hEanti hEcl'
  have hψ₂eq : ∀ j l z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1 - δ) →
      Work.CR.Flat.dbarCoord j (ftPsi2 n δ hδ0 hδ4 η l) z
        - Work.CR.Flat.dbarCoord l (ftPsi2 n δ hδ0 hδ4 η j) z = ftEdat n δ η j l z := by
    intro j l z hz
    have hz' : ∀ k : Fin n, ‖z k‖ < 1 - δ := by
      rw [Work.NN.Final.tun_mem_polydisc_zero] at hz; exact hz
    refine hTelSolves j l z ?_
    intro k
    rw [ftG_e]
    exact hz' k
  -- the candidate
  refine ⟨fun j z => ftPsi1 n δ η j z + ftPsi2 n δ hδ0 hδ4 η j z, ?_, ?_, ?_⟩
  · -- smoothness
    intro j m
    exact (contDiff_ftPsi1 hδ0 hδ4 hη hn m j).contDiffOn.add
      (contDiffOn_ftPsi2 hδ0 hδ4 hη hn m j)
  · -- the equation
    intro j l z hz
    change Work.CR.Flat.dbarCoord j (ftPsi1 n δ η l + ftPsi2 n δ hδ0 hδ4 η l) z
      - Work.CR.Flat.dbarCoord l (ftPsi1 n δ η j + ftPsi2 n δ hδ0 hδ4 η j) z = η j l z
    have h1 := hψ₁eq j l z hz
    have h2 := hψ₂eq j l z hz
    have hd1 : DifferentiableAt ℝ (ftPsi1 n δ η l) z :=
      ((contDiff_ftPsi1 hδ0 hδ4 hη hn 1 l).differentiable one_ne_zero).differentiableAt
    have hd2 : DifferentiableAt ℝ (ftPsi2 n δ hδ0 hδ4 η l) z := by
      have hco := contDiffOn_ftPsi2 hδ0 hδ4 hη hn 1 l
      exact ((hco.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 _).mem_nhds hz)).differentiableAt
        one_ne_zero)
    have hd3 : DifferentiableAt ℝ (ftPsi1 n δ η j) z :=
      ((contDiff_ftPsi1 hδ0 hδ4 hη hn 1 j).differentiable one_ne_zero).differentiableAt
    have hd4 : DifferentiableAt ℝ (ftPsi2 n δ hδ0 hδ4 η j) z := by
      have hco := contDiffOn_ftPsi2 hδ0 hδ4 hη hn 1 j
      exact ((hco.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 _).mem_nhds hz)).differentiableAt
        one_ne_zero)
    rw [Work.NN.Assemble.FT.dbarCoord_add_pi j hd1 hd2,
      Work.NN.Assemble.FT.dbarCoord_add_pi l hd3 hd4]
    linear_combination h1 + h2
  · -- the bound
    intro j
    set S : ℝ≥0∞ := ∑ j, ∑ l, Work.CR.Flat.holderNorm 0 α (η j l)
      (Work.CR.Flat.polydisc 0 (fun _ => 1)) with hS
    have h1 := hBm δ hδ0 hδ4 η (fun i l => hη i l 1) j
    have h2 := hTel δ hδ0 hδ4 (ftEdat n δ η) hE1 j
    have h3 : (∑ a : Fin n, ∑ b : Fin n,
        Work.CR.Flat.holderNorm 1 α (ftEdat n δ η a b)
          (Work.CR.Flat.polydisc 0 (fun _ => 1 - 7 * δ / 8)))
        ≤ ENNReal.ofReal (KE / δ ^ NE) * S := by
      refine (hEd δ hδ0 hδ4 η (fun i l => hη i l 1) (1 - 7 * δ / 8) (by linarith)
        (by linarith)).trans ?_
      rw [hS]
    calc Work.CR.Flat.holderNorm 1 α
          (fun z => ftPsi1 n δ η j z + ftPsi2 n δ hδ0 hδ4 η j z)
          (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))
        ≤ Work.CR.Flat.holderNorm 1 α (ftPsi1 n δ η j)
              (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))
            + Work.CR.Flat.holderNorm 1 α (ftPsi2 n δ hδ0 hδ4 η j)
              (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ)) := by
          refine Work.CR.Flat.Holder.holderNorm_add_le (f := ftPsi1 n δ η j)
            (g := ftPsi2 n δ hδ0 hδ4 η j) (Ω := Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))
            ((contDiff_ftPsi1 hδ0 hδ4 hη hn 1 j).contDiffOn)
            (contDiffOn_ftPsi2 hδ0 hδ4 hη hn 1 j)
            (Work.CR.Flat.isOpen_polydisc 0 _).uniqueDiffOn
      _ ≤ ENNReal.ofReal (KB / δ ^ NB) * S
            + ENNReal.ofReal (KT / δ ^ NT) * (ENNReal.ofReal (KE / δ ^ NE) * S) := by
          refine add_le_add ?_ ?_
          · rw [hS]; exact h1
          · simpa only [ftPsi2_apply] using
              h2.trans (mul_le_mul_right h3 (ENNReal.ofReal (KT / δ ^ NT)))
      _ = ENNReal.ofReal (KB / δ ^ NB + (KT / δ ^ NT) * (KE / δ ^ NE)) * S := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← add_mul,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal ((KB + KT * KE + 1) / δ ^ (NB + NT + NE)) * S := by
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) S
          have hδ1 : δ ≤ 1 := by linarith
          have hN : δ ^ (NB + NT + NE) ≤ δ ^ NB :=
            pow_le_pow_of_le_one hδ0.le hδ1 (by omega)
          have hN' : δ ^ (NB + NT + NE) ≤ δ ^ (NT + NE) :=
            pow_le_pow_of_le_one hδ0.le hδ1 (by omega)
          have hA : KB / δ ^ NB ≤ KB / δ ^ (NB + NT + NE) :=
            div_le_div_of_nonneg_left hKB0.le (by positivity) hN
          have hB : (KT / δ ^ NT) * (KE / δ ^ NE) = KT * KE / δ ^ (NT + NE) := by
            rw [div_mul_div_comm, ← pow_add]
          have hB' : KT * KE / δ ^ (NT + NE) ≤ KT * KE / δ ^ (NB + NT + NE) :=
            div_le_div_of_nonneg_left (mul_nonneg hKT0.le hKE0.le) (by positivity) hN'
          have hsum : KB / δ ^ (NB + NT + NE) + KT * KE / δ ^ (NB + NT + NE)
              = (KB + KT * KE) / δ ^ (NB + NT + NE) := by rw [← add_div]
          have hfin : (KB + KT * KE) / δ ^ (NB + NT + NE)
              ≤ (KB + KT * KE + 1) / δ ^ (NB + NT + NE) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
          linarith [hA, hB, hB', hsum, hfin]
      _ = ENNReal.ofReal ((KB + KT * KE + 1) / δ ^ (NB + NT + NE))
            * ∑ j, ∑ l, Work.CR.Flat.holderNorm 0 α (η j l)
                (Work.CR.Flat.polydisc 0 (fun _ => 1)) := by rw [hS]

end Work.NN.Newton
