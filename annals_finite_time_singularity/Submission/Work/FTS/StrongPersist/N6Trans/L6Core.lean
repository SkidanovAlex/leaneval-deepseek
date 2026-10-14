import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Joint continuity on the open quadrant -/

/-- The uncurried mixed derivative of an open-smooth function is continuous on the open
quadrant.  (Open twin of `continuousOn_mixed_Qd`.) -/
theorem continuousOn_mixed_Qd_open {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2) Work.FTS.LocData.Qd :=
  (hsg.mixed j i).continuousOn

/-- The uncurried hard slot `Thard g k` is continuous on the open quadrant. -/
theorem continuousOn_Thard_Qd_open {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.Thard g k p.1 p.2) Work.FTS.LocData.Qd := by
  refine (continuousOn_mixed_Qd_open hsg (4 - k.val) k.val).congr fun p _ => ?_
  simp only [Work.FTS.H2.Thard_eq_mixed]

/-- The uncurried weighted slot `Xz α g k` is continuous on the open quadrant. -/
theorem continuousOn_Xz_Qd_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.Xz α g k p.1 p.2)
      Work.FTS.LocData.Qd := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    refine ((continuousOn_mixed_Qd_open hsg 4 0).mul
      Work.FTS.TransportS.continuousOn_wdivsin_Qd).congr fun p _ => ?_
    simp only [Work.FTS.TransportS.Xz_apply_zero, Work.Spaces.mixed_zero_right, Pi.mul_apply]
  · refine ((continuousOn_mixed_Qd_open hsg (4 - k.val) k.val).mul
      (Work.FTS.TransportS.continuousOn_Wt_Qd α)).congr fun p _ => ?_
    simp only [Work.FTS.TransportS.Xz_apply_ne hk, Pi.mul_apply]

/-- The uncurried weighted slot `Yz α g k` is continuous on the open quadrant. -/
theorem continuousOn_Yz_Qd_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.Yz α g k p.1 p.2)
      Work.FTS.LocData.Qd := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    refine ((continuousOn_mixed_Qd_open hsg 5 0).mul
      Work.FTS.TransportS.continuousOn_wdivsin_Qd).congr fun p _ => ?_
    simp only [Work.FTS.TransportS.Yz_apply_zero, Work.Spaces.mixed_zero_right, Pi.mul_apply]
  · refine ((continuousOn_mixed_Qd_open hsg (5 - k.val) k.val).mul
      (Work.FTS.TransportS.continuousOn_Wt_Qd α)).congr fun p _ => ?_
    simp only [Work.FTS.TransportS.Yz_apply_ne hk, Pi.mul_apply]

/-- The uncurried `k`-th hard summand `gK α f g k` is continuous on the open quadrant. -/
theorem continuousOn_gK_Qd_open {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.gK α f g k p.1 p.2)
      Work.FTS.LocData.Qd := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.LocData.Qd :=
    (hsf.continuousOn).mono fun p hp => hp
  refine (hf.mul ((continuousOn_Xz_Qd_open (α := α) hsg k).mul
    (continuousOn_Yz_Qd_open (α := α) hsg k))).congr fun p hp => ?_
  have hp' := Set.mem_prod.mp hp
  rw [Work.FTS.TransportS.gK_eq_mul α f g k p.1 p.2 ⟨le_of_lt hp'.2.1, le_of_lt hp'.2.2⟩]
  simp only [Pi.mul_apply]

/-- The uncurried integration-by-parts integrand `gK' α f g k` is continuous on the open
quadrant. -/
theorem continuousOn_gK'_Qd_open {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.gK' α f g k p.1 p.2)
      Work.FTS.LocData.Qd := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.LocData.Qd :=
    (hsf.continuousOn).mono fun p hp => hp
  have hpf : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2) Work.FTS.LocData.Qd :=
    (hsf.pz.continuousOn).mono fun p hp => hp
  have hratio : ContinuousOn (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1)) Work.FTS.LocData.Qd :=
    ContinuousOn.div (continuousOn_fst.sub continuousOn_const)
      (continuousOn_const.add continuousOn_fst) (fun p hp => by
        have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
        linarith)
  refine ((((hpf.mul continuousOn_fst).mul Work.FTS.TransportS.continuousOn_w_sq_Qd).add
    (hf.mul (Work.FTS.TransportS.continuousOn_w_sq_Qd.mul hratio))).mul
      ((continuousOn_Thard_Qd_open hsg k).pow 2)).congr fun p _ => ?_
  simp only [Work.FTS.TransportS.gK', Pi.mul_apply, Pi.add_apply, Pi.pow_apply]

/-- The rewritten `H1`-slice integrand of the radial integration by parts is continuous on the
open quadrant.  (Open twin of `T3BadAux.continuousOn_slotH1_Qd`.) -/
theorem continuousOn_slotH1_Qd_open {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * Work.Spaces.mixed (5 - k.val) k.val g p.1 p.2
      * (Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.Thard g k p.1 p.2) Work.FTS.LocData.Qd :=
  ((((hsf.continuousOn).mono fun p hp => hp).mul
      (continuousOn_mixed_Qd_open hsg (5 - k.val) k.val)).mul
    (Work.FTS.TransportS.continuousOn_w_sq_Qd.mul
      (continuousOn_Thard_Qd_open hsg k))).congr fun p _ => by
    simp only [Pi.mul_apply]
    rw [show Function.uncurry f p = f p.1 p.2 from rfl]
    ring

/-! ## Product-integrability -/

/-- The `ℋ^k`-integrand of `g` is product-integrable, and its product integral is
`HkSq α k g`, for `g` smooth on the open quadrant.  (Open twin of
`integrable_HkIntegrand_prod`.) -/
theorem integrable_HkIntegrand_prod_open {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      ∧ (∫ p, Work.Spaces.HkIntegrand α k g p.1 p.2
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        = Work.Spaces.HkSq α k g := by
  have h := Work.Spaces.integrable_prod_of_iterated
    (μ := volume.restrict Work.Spaces.Iz) (ν := volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => Work.Spaces.HkIntegrand α k g z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
    (aesm_HkIntegrand_prod_open (k := k) hg)
    ((MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iz from
      measurableSet_Ici)).mpr (Filter.Eventually.of_forall fun z hz => hmem.1 z hz))
    hmem.2
  exact ⟨h.1, by rw [h.2]; rfl⟩

/-- A single order-`4` weighted factor is a summand of `HkIntegrand α 4 g`, hence
product-integrable, for `g` smooth on the open quadrant. -/
theorem integrable_Xz_sq_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hmg4 : Work.Spaces.HkMem α 4 g) (k : Fin 5) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono' (integrable_HkIntegrand_prod_open hsg hmg4).1
    (Work.Spaces.aesm_of_continuousOn_Qd _ ((continuousOn_Xz_Qd_open hsg k).pow 2)) ?_
  filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
    (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g p.1 p.2)
    fun z θ hz hθ hθ' => Work.FTS.TransportS.Xz_sq_le_HkIntegrand4 α g k z θ] with p hp
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hp

/-- The `k`-th hard summand `gK α f g k` is product-integrable, for `g` smooth on the open
quadrant and `g ∈ ℋ⁵`.  (Open twin of `integrable_gK`.) -/
theorem integrable_gK_open {α Mf : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmg5 : Work.Spaces.HkMem α 5 g) (hMf : 0 ≤ Mf)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf) (k : Fin 5) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.gK α f g k p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono'
    ((integrable_HkIntegrand_prod_open hsg hmg5).1.const_mul Mf)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_gK_Qd_open hsf hsg k)) ?_
  filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
    |Work.FTS.TransportS.gK α f g k p.1 p.2| ≤ Mf * Work.Spaces.HkIntegrand α 5 g p.1 p.2)
    fun z θ hz hθ hθ' => Work.FTS.TransportS.abs_gK_le hMf hf k hz ⟨hθ, hθ'⟩] with p hp
  simpa only [Real.norm_eq_abs, mul_comm] using hp

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.L6Core =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- `|a b| ≤ (a² + b²)/2`. -/
theorem abs_mul_le_half_sq_add6 (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]

/-! ## The Bell-number bound at level six -/

/-- The Bell numbers of the rows `0 ≤ n ≤ 6` are `1, 1, 2, 5, 15, 52, 203`, all below `1000`. -/
theorem bell_le_six (n : ℕ) (hn : n ≤ 6) : Work.Spaces.bell n ≤ 1000 := by
  interval_cases n <;> decide

/-! ## The `𝒲^{6,∞}`-bounds on the radial derivatives -/

/-- `|z^j ∂_z^j f| ≤ |f|_{𝒲^{6,∞}}` for `j ≤ 6`, on the domain. -/
theorem zpz_le_WlInf6 {α : ℝ} {f : ℝ → ℝ → ℝ} (hfm : Work.Spaces.WlInfMem α 6 f)
    {j : ℕ} (hj : j ≤ 6) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |z ^ j * Work.Spaces.pzIter j f z θ| ≤ Work.Spaces.WlInf α 6 f := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have h := Work.Spaces.pz_sup_bound α 6 f hfm j hj z θ hz hθ
  have hW := Work.Spaces.WlInf_nonneg α 6 f hfm
  rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
  calc z ^ j * |Work.Spaces.pzIter j f z θ|
      ≤ z ^ j * (Work.Spaces.WlInf α 6 f / (z + 1) ^ j) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hz0 j)
    _ = Work.Spaces.WlInf α 6 f * (z / (z + 1)) ^ j := by rw [div_pow]; ring
    _ ≤ Work.Spaces.WlInf α 6 f * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hW
        exact pow_le_one₀ (div_nonneg hz0 (by linarith)) (by rw [div_le_one hz1]; linarith)
    _ = Work.Spaces.WlInf α 6 f := mul_one _

/-- `|D_z^b f| ≤ 1000 |f|_{𝒲^{6,∞}}` on the open quadrant, for `b ≤ 6`. -/
theorem dzIter_le_WlInf6 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 6 f)
    {b : ℕ} (hb : b ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.DzIter b f z θ| ≤ 1000 * Work.Spaces.WlInf α 6 f := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hz' : z ∈ Set.Ioi (0 : ℝ) := hz
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => f z' θ) (Set.Ioi 0) :=
    Work.FTS.OpenPkg.smoothOpen_slice_z hf hθ
  have hDz : Work.Spaces.DzIter b f z θ
      = ∑ k ∈ Finset.range (b + 1),
          (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k f z θ) :=
    Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open hslice b z hz'
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (Work.Spaces.WlInf α 6 f)
    (fun k => z ^ k * Work.Spaces.pzIter k f z θ)
    (fun k hk => zpz_le_WlInf6 hfm (le_trans hk hb) hzI hθI)
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 1000 := by
    exact_mod_cast bell_le_six b hb
  have hW : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
  calc |Work.Spaces.DzIter b f z θ|
      = |∑ k ∈ Finset.range (b + 1),
          (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k f z θ)| := by rw [hDz]
    _ ≤ (Work.Spaces.bell b : ℝ) * Work.Spaces.WlInf α 6 f := hsum
    _ ≤ 1000 * Work.Spaces.WlInf α 6 f := mul_le_mul_of_nonneg_right hbell hW

/-! ## The single-slot domination at level six -/

/-- A single canonical slot is dominated by `HkIntegrand α 6 g`. -/
theorem canonW_slot_le_Hk6 {α : ℝ} {g : ℝ → ℝ → ℝ} {q : ℝ} (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {j i : ℕ} (hi : i = 0 → q ≤ Work.Spaces.eta)
    (hij : i + j ≤ 6) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  rcases eq_or_ne i 0 with hi0 | hine
  · subst hi0
    simpa only [Work.Spaces.mixed_zero_right] using
      Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_z_le6 α g hq0 (hi rfl) hθ j
        (by omega)
  · exact Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_mixed_le6 α g hq0 hqγ hθ j i
      (Nat.one_le_iff_ne_zero.mpr hine) hij


/-! ## The two-factor AM–GM form -/

/-- **The two-factor `ℋ⁶` AM–GM estimate.**  For two slots `D_z^jD_θ^ig`, `D_z^bD_θ^ag` whose
weight classes both dominate the canonical exponent `q` (`q ≤ η` whenever the angular index
vanishes, `q ≤ γ` always), the product of the canonical weight with the two absolute values is
dominated by `HkIntegrand α 6 g`. -/
theorem canonW_pair_le6 {α : ℝ} {g : ℝ → ℝ → ℝ} {q : ℝ} (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {j i b a : ℕ} (hi : i = 0 → q ≤ Work.Spaces.eta)
    (ha : a = 0 → q ≤ Work.Spaces.eta) (hij : i + j ≤ 6) (hab : a + b ≤ 6)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i g z θ|
        * |Work.Spaces.mixed b a g z θ| ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  have hX := canonW_slot_le_Hk6 (α := α) (g := g) hq0 hqγ hi hij hz hθ
  have hY := canonW_slot_le_Hk6 (α := α) (g := g) hq0 hqγ ha hab hz hθ
  have hnn : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
    Work.FTS.TransportS.SlotT2.canonW_nonneg hθ
  have habs : |Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b a g z θ|
      ≤ ((Work.Spaces.mixed j i g z θ) ^ 2 + (Work.Spaces.mixed b a g z θ) ^ 2) / 2 := by
    simpa only [abs_mul] using abs_mul_le_half_sq_add6 _ _
  have hkey : Work.FTS.TransportS.SlotT2.canonW q z θ
        * (|Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b a g z θ|)
      ≤ Work.FTS.TransportS.SlotT2.canonW q z θ
        * (((Work.Spaces.mixed j i g z θ) ^ 2 + (Work.Spaces.mixed b a g z θ) ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left habs hnn
  have hsplit : Work.FTS.TransportS.SlotT2.canonW q z θ
        * (((Work.Spaces.mixed j i g z θ) ^ 2 + (Work.Spaces.mixed b a g z θ) ^ 2) / 2)
      = (Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2) / 2
        + (Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) / 2 := by
    ring
  calc Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i g z θ|
        * |Work.Spaces.mixed b a g z θ|
      = Work.FTS.TransportS.SlotT2.canonW q z θ
        * (|Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b a g z θ|) := by ring
    _ ≤ Work.FTS.TransportS.SlotT2.canonW q z θ
        * (((Work.Spaces.mixed j i g z θ) ^ 2 + (Work.Spaces.mixed b a g z θ) ^ 2) / 2) := hkey
    _ = (Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2) / 2
        + (Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) / 2 :=
        hsplit
    _ ≤ Work.Spaces.HkIntegrand α 6 g z θ := by linarith

end Work.FTS.StrongPersist.N6Trans
end
end
